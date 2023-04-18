use std::collections::HashSet;
use std::convert::TryFrom;
use std::fmt::Write as _;
use std::fs::File;
use std::io::Read;
use std::iter;
use std::mem;
use std::path::Path;
use std::slice;
use cheesecloth::micro_ram::feature::{self, Version, Feature};
use cheesecloth::micro_ram::fetch;
use cheesecloth::micro_ram::parse;
use cheesecloth::micro_ram::types::{ExecBody, RamInstr, Commitment};
use cheesecloth::mode::if_mode::{Mode, with_mode};
use clap::{App, AppSettings, SubCommand, Arg, ArgMatches};
use getrandom;
use serde::Serialize;
use serde::de::DeserializeOwned;
use sha2::{Sha256, Digest};


fn parse_args() -> ArgMatches<'static> {
    App::new("commitment_tool")
        .about("manipulate commitments to secret programs")
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .subcommand(SubCommand::with_name("calc")
            .about("calculate the commitment and related data for a CBOR file")
            .arg(Arg::with_name("trace")
                 .takes_value(true)
                 .value_name("TRACE.CBOR")
                 .help("MicroRAM execution trace")
                 .required(true))
            .arg(Arg::with_name("keep-randomness")
                 .long("keep-randomness")
                 .help("keep the existing __commitment_randomness__ values \
                       instead of generating new ones"))
        )
        .subcommand(SubCommand::with_name("update-cbor")
            .about("update a CBOR file by adding a commitment")
            .arg(Arg::with_name("trace")
                 .takes_value(true)
                 .value_name("TRACE.CBOR")
                 .help("MicroRAM execution trace")
                 .required(true))
            .arg(Arg::with_name("output")
                 .short("o")
                 .long("output")
                 .takes_value(true)
                 .value_name("OUT.CBOR")
                 .help("where to write the new trace including the commitment"))
            .arg(Arg::with_name("set-commitment")
                 .long("set-commitment")
                 .takes_value(true)
                 .value_name("COMMITMENT")
                 .help("set the value of params.commitment"))
            .arg(Arg::with_name("set-randomness")
                 .long("set-randomness")
                 .takes_value(true)
                 .value_name("HEX")
                 .help("set the values of any __commitment_randomness__ memory segments"))
        )
        .get_matches()
}


type Error = String;

trait Value: Sized + Serialize {
    fn from_reader<R: Read>(r: R) -> Result<Self, Error>;
    fn new_u64(x: u64) -> Self;
    fn new_string(s: String) -> Self;
    fn new_array(v: Vec<Self>) -> Self;
    fn new_map() -> Self;
    fn get_index(&self, i: usize) -> Option<&Self>;
    fn get_key(&self, k: &str) -> Option<&Self>;
    fn get_index_mut(&mut self, i: usize) -> Option<&mut Self>;
    fn get_key_mut(&mut self, k: &str) -> Option<&mut Self>;
    fn insert_key(&mut self, k: &str, v: Self);
    fn parse<T: DeserializeOwned>(&self) -> Result<T, Error>;
}

impl Value for serde_cbor::Value {
    fn from_reader<R: Read>(r: R) -> Result<Self, Error> {
        serde_cbor::from_reader(r)
            .map_err(|e| e.to_string())
    }

    fn new_u64(x: u64) -> Self {
        x.into()
    }

    fn new_string(s: String) -> Self {
        s.into()
    }

    fn new_array(v: Vec<Self>) -> Self {
        v.into()
    }

    fn new_map() -> Self {
        serde_cbor::Value::Map(Default::default())
    }

    fn get_index(&self, i: usize) -> Option<&Self> {
        match *self {
            serde_cbor::Value::Array(ref a) => a.get(i),
            serde_cbor::Value::Map(ref m) => m.get(&(i as u64).into()),
            _ => panic!("expected array or map"),
        }
    }

    fn get_key(&self, k: &str) -> Option<&Self> {
        match *self {
            serde_cbor::Value::Map(ref m) => m.get(&k.to_owned().into()),
            _ => panic!("expected map"),
        }
    }

    fn get_index_mut(&mut self, i: usize) -> Option<&mut Self> {
        match *self {
            serde_cbor::Value::Array(ref mut a) => a.get_mut(i),
            serde_cbor::Value::Map(ref mut m) => m.get_mut(&(i as u64).into()),
            _ => panic!("expected array or map"),
        }
    }

    fn get_key_mut(&mut self, k: &str) -> Option<&mut Self> {
        match *self {
            serde_cbor::Value::Map(ref mut m) => m.get_mut(&k.to_owned().into()),
            _ => panic!("expected map"),
        }
    }

    fn insert_key(&mut self, k: &str, v: Self) {
        match *self {
            serde_cbor::Value::Map(ref mut m) => { m.insert(k.to_owned().into(), v); },
            _ => panic!("expected map"),
        }
    }

    fn parse<T: DeserializeOwned>(&self) -> Result<T, Error> {
        serde_cbor::value::from_value(self.clone())
            .map_err(|e| e.to_string())
    }
}

impl Value for serde_yaml::Value {
    fn from_reader<R: Read>(r: R) -> Result<Self, Error> {
        serde_yaml::from_reader(r)
            .map_err(|e| e.to_string())
    }

    fn new_u64(x: u64) -> Self {
        x.into()
    }

    fn new_string(s: String) -> Self {
        s.into()
    }

    fn new_array(v: Vec<Self>) -> Self {
        v.into()
    }

    fn new_map() -> Self {
        serde_yaml::Value::Mapping(Default::default())
    }

    fn get_index(&self, i: usize) -> Option<&Self> {
        match *self {
            serde_yaml::Value::Sequence(ref s) => s.get(i),
            serde_yaml::Value::Mapping(ref m) => m.get(&i.into()),
            _ => panic!("expected sequence or mapping"),
        }
    }

    fn get_key(&self, k: &str) -> Option<&Self> {
        match *self {
            serde_yaml::Value::Mapping(ref m) => m.get(&k.into()),
            _ => panic!("expected mapping"),
        }
    }

    fn get_index_mut(&mut self, i: usize) -> Option<&mut Self> {
        match *self {
            serde_yaml::Value::Sequence(ref mut s) => s.get_mut(i),
            serde_yaml::Value::Mapping(ref mut m) => m.get_mut(&i.into()),
            _ => panic!("expected sequence or mapping"),
        }
    }

    fn get_key_mut(&mut self, k: &str) -> Option<&mut Self> {
        match *self {
            serde_yaml::Value::Mapping(ref mut m) => m.get_mut(&k.into()),
            _ => panic!("expected mapping"),
        }
    }

    fn insert_key(&mut self, k: &str, v: Self) {
        match *self {
            serde_yaml::Value::Mapping(ref mut m) => { m.insert(k.to_owned().into(), v); },
            _ => panic!("expected map"),
        }
    }

    fn parse<T: DeserializeOwned>(&self) -> Result<T, Error> {
        serde_yaml::from_value(self.clone())
            .map_err(|e| e.to_string())
    }
}


fn add_commitment<V: Value>(exec: &mut V, commitment: String) {
    if let Some(params) = exec.get_key_mut("params") {
        params.insert_key("commitment", V::new_string(commitment));
    } else {
        let mut m = V::new_map();
        m.insert_key("commitment", V::new_string(commitment));
        exec.insert_key("params", m);
    }
}

fn write_output<V: Value>(out_path: &Path, v: &V) -> Result<(), String> {
    let f = File::create(out_path).map_err(|e| e.to_string())?;
    match Format::from_path(out_path) {
        Format::Yaml => serde_yaml::to_writer(f, v).map_err(|e| e.to_string())?,
        Format::Cbor => serde_cbor::to_writer(f, v).map_err(|e| e.to_string())?,
        Format::Json => serde_json::to_writer(f, v).map_err(|e| e.to_string())?,
    }
    Ok(())
}

fn run_verifier<V: Value>(
    in_path: &Path,
    out_path: Option<&Path>,
    commitment: String,
) -> Result<(), String> {
    let f = File::open(in_path).map_err(|e| e.to_string())?;
    let mut v = V::from_reader(f)?;

    let exec = v.get_index_mut(2).ok_or("missing execution")?;
    add_commitment(exec, commitment);

    if let Some(out_path) = out_path {
        write_output(out_path, &v)?;
    } else {
        return Err("must specify an output path with -o for verifier mode".into());
    }

    Ok(())
}

fn parse_file<V: Value>(path: &Path) -> Result<V, String> {
    let f = File::open(path).map_err(|e| e.to_string())?;
    V::from_reader(f)
}

fn check_version<V: Value>(v: &V) -> Result<HashSet<Feature>, String> {
    let version = v.get_index(0).ok_or("missing version")?.parse::<Version>()?;
    let mut features = v.get_index(1).ok_or("missing features")?.parse::<HashSet<Feature>>()?;
    let version_features = feature::lookup_version(version)
        .unwrap_or_else(|| panic!("unknown version {:?}", version));
    features.extend(version_features);

    if features.contains(&Feature::MultiExec) {
        return Err("multi-exec feature is not supported by this tool".into());
    }

    Ok(features)
}

fn get_exec<V: Value>(v: &V) -> Result<(ExecBody, &V), String> {
    let features = check_version(v)?;
    let v_exec = v.get_index(2).ok_or("missing execution")?;
    let mut exec = parse::with_features(features, || v_exec.parse::<ExecBody>())?;
    Ok((exec, v_exec))
}

fn get_exec_mut<V: Value>(v: &mut V) -> Result<(ExecBody, &mut V), String> {
    let features = check_version(v)?;
    let v_exec = v.get_index_mut(2).ok_or("missing execution")?;
    let mut exec = parse::with_features(features, || v_exec.parse::<ExecBody>())?;
    Ok((exec, v_exec))
}

const RANDOMNESS_NAME: &str = "__commitment_randomness__";

/// Count the total number of words in all `__commitment_randomness__` memory segments.
fn count_randomness_words(exec: &ExecBody) -> usize {
    let mut sum = 0;
    for ms in &exec.init_mem {
        if !ms.name.contains(RANDOMNESS_NAME) {
            continue;
        }
        if !ms.secret {
            eprintln!("warning: skipping non-secret segment {:?}", ms.name);
            continue;
        }
        if ms.uncommitted {
            eprintln!("warning: skipping non-secret segment {:?}", ms.name);
            continue;
        }
        sum += ms.len as usize;
    }
    sum
}

/// Count the total number of steps in all secret and public PC segments.
fn count_steps(exec: &ExecBody) -> usize {
    let mut sum = 0;
    for seg in &exec.segments {
        sum += seg.len;
    }
    sum
}

fn gather_randomness(exec: &ExecBody) -> Result<Vec<u8>, String> {
    let mut bytes = Vec::new();

    for ms in &exec.init_mem {
        if !ms.name.contains(RANDOMNESS_NAME) {
            continue;
        }
        if !ms.secret || ms.uncommitted {
            continue;
        }

        let words = ms.data.iter().cloned()
            .chain(iter::repeat(0).take(ms.len as usize - ms.data.len()));
        for word in words {
            bytes.extend_from_slice(&u64::to_le_bytes(word));
        }
    }

    Ok(bytes)
}

const RNG_SEED_NAME: &str = "__rng_seed__";

fn find_rng_seed(exec: &ExecBody) -> Result<Option<Vec<u8>>, String> {
    let mut seed = None;

    for ms in &exec.init_mem {
        if !ms.name.contains(RNG_SEED_NAME) {
            continue;
        }
        if ms.secret {
            eprintln!("warning: rng seed {:?} should not be secret", ms.secret);
        }

        if seed.is_some() {
            return Err("found multiple __rng_seed__ memory segments".into());
        }

        let mut bytes = Vec::with_capacity(ms.len as usize * 8);
        let words = ms.data.iter().cloned()
            .chain(iter::repeat(0).take(ms.len as usize - ms.data.len()));
        for word in words {
            bytes.extend_from_slice(&u64::to_le_bytes(word));
        }
        seed = Some(bytes);
    }

    Ok(seed)
}

fn calc_commitment(
    exec: &ExecBody,
    randomness: Option<impl IntoIterator<Item = u64>>,
) -> Result<[u8; 32], String> {
    let mut randomness = randomness.map(|it| it.into_iter());

    let mut h = Sha256::new();

    let mut code_count = 0;
    for cs in &exec.program {
        if !cs.secret || cs.uncommitted {
            continue;
        }
        let instrs = cs.instrs.iter().cloned()
            .chain(iter::repeat(fetch::PADDING_INSTR).take(cs.len as usize - cs.instrs.len()));
        for instr in instrs {
            let RamInstr { opcode, dest, op1, op2, imm } = instr;
            h.update(&u8::to_le_bytes(opcode));
            h.update(&u8::to_le_bytes(dest));
            h.update(&u8::to_le_bytes(op1));
            h.update(&u64::to_le_bytes(op2));
            h.update(&u8::to_le_bytes(imm as u8));
        }
        code_count += 1;
    }
    eprintln!("hashed {} secret code segments", code_count);

    let mut mem_count = 0;
    for ms in &exec.init_mem {
        if !ms.secret || ms.uncommitted {
            continue;
        }

        // Special case: if this is a `__commitment_randomness__` segment, and a randomness
        // iterator is available, use the words it provides instead of the ones actually present in
        // `ms.data`.
        if ms.name.contains(RANDOMNESS_NAME) {
            if let Some(ref mut it) = randomness {
                for _ in 0 .. ms.len {
                    let word = it.next()
                        .ok_or("ran out of randomness")?;
                    h.update(&u64::to_le_bytes(word));
                }
                continue;
            }
        }

        let words = ms.data.iter().cloned()
            .chain(iter::repeat(0).take(ms.len as usize - ms.data.len()));
        for word in words {
            h.update(&u64::to_le_bytes(word));
        }
        mem_count += 1;
    }
    eprintln!("hashed {} secret memory segments", mem_count);

    let hash = h.finalize();

    if let Some(ref mut it) = randomness {
        if it.next().is_some() {
            return Err("got too much randomness".into());
        }
    }

    let mut hash_arr = [0_u8; 32];
    hash_arr.copy_from_slice(&hash);
    Ok(hash_arr)
}

fn calc_rng_seed(commitment: &[u8; 32], steps: usize) -> [u8; 32] {
    let mut hash = *commitment;
    for _ in 0 .. steps {
        let mut h = Sha256::new();
        h.update(&hash);
        hash.copy_from_slice(&h.finalize());
    }
    hash
}

fn set_randomness_value<V: Value>(
    v_exec: &mut V,
    parsed_exec: &ExecBody,
    randomness: impl IntoIterator<Item = u64>,
) -> Result<(), String> {
    let mut it = randomness.into_iter();

    // Find `__commitment_randomness__` memory segment(s) and fill them with random data.
    for (i, parsed_ms) in parsed_exec.init_mem.iter().enumerate() {
        if !parsed_ms.name.contains("__commitment_randomness__") {
            continue;
        }
        if !parsed_ms.secret {
            eprintln!("warning: skipping non-secret segment {:?}", parsed_ms.name);
            continue;
        }

        let mut words = Vec::with_capacity(parsed_ms.len as usize);
        for _ in 0 .. parsed_ms.len {
            let word = it.next()
                .ok_or("ran out of randomness")?;
            words.push(word);
        }
        eprintln!("set init_mem[{}] ({:?}) data = {:?}", i, parsed_ms.name, words);

        let init_mem = v_exec.get_key_mut("init_mem").unwrap();
        let ms = init_mem.get_index_mut(i).unwrap();
        let data = V::new_array(words.into_iter().map(V::new_u64).collect());
        ms.insert_key("data", data);
    }

    Ok(())
}

fn set_commitment_value<V: Value>(exec: &mut V, commitment: String) -> Result<(), String> {
    if let Some(params) = exec.get_key_mut("params") {
        params.insert_key("commitment", V::new_string(commitment));
    } else {
        let mut m = V::new_map();
        m.insert_key("commitment", V::new_string(commitment));
        exec.insert_key("params", m);
    }

    Ok(())
}

/*
fn run<V: Value>(in_path: &Path, out_path: Option<&Path>) -> Result<(), String> {
    let f = File::open(in_path).map_err(|e| e.to_string())?;
    let mut v = V::from_reader(f)?;


    let version = v.get_index(0).ok_or("missing version")?.parse::<Version>()?;
    let mut features = v.get_index(1).ok_or("missing features")?.parse::<HashSet<Feature>>()?;
    let version_features = feature::lookup_version(version)
        .unwrap_or_else(|| panic!("unknown version {:?}", version));
    features.extend(version_features);

    if features.contains(&Feature::MultiExec) {
        return Err("multi-exec feature is not supported by this tool".into());
    }

    let v_exec = v.get_index_mut(2).ok_or("missing execution")?;
    let mut exec = parse::with_features(features, || v_exec.parse::<ExecBody>())?;


    // Find `__commitment_randomness__` memory segment(s) and fill them with random data.
    let mut randomness_count = 0;
    let mut randomness_words = 0;
    for (i, parsed_ms) in exec.init_mem.iter_mut().enumerate() {
        if !parsed_ms.name.contains("__commitment_randomness__") {
            continue;
        }
        if !parsed_ms.secret {
            eprintln!("warning: skipping non-secret segment {:?}", parsed_ms.name);
            continue;
        }

        randomness_count += 1;
        randomness_words += parsed_ms.len;

        let len = parsed_ms.len as usize;
        let mut bytes = vec![0; len * 8];
        getrandom::getrandom(&mut bytes).map_err(|e| e.to_string())?;

        let mut words = Vec::with_capacity(len);
        for i in 0..len {
            let mut word_bytes = [0; 8];
            word_bytes.copy_from_slice(&bytes[i * 8 .. (i + 1) * 8]);
            words.push(u64::from_le_bytes(word_bytes));
        }
        eprintln!("init_mem[{}] ({:?}) data = {:?}", i, parsed_ms.name, words);
        parsed_ms.data = words.clone();

        let init_mem = v_exec.get_key_mut("init_mem").unwrap();
        let ms = init_mem.get_index_mut(i).unwrap();
        let data = V::new_array(words.into_iter().map(V::new_u64).collect());
        ms.insert_key("data", data);
    }

    if randomness_words < 2 {
        eprintln!("warning: not enough secret __commitment_randomness__ bits: \
            found {} segments containing {} total bits, but expected >= 128 bits",
            randomness_count, randomness_words * 64);
    }


    // Hash the secret code and memory.

    let mut h = Sha256::new();

    let mut code_count = 0;
    for cs in &exec.program {
        if !cs.secret || cs.uncommitted {
            continue;
        }
        let instrs = cs.instrs.iter().cloned()
            .chain(iter::repeat(fetch::PADDING_INSTR).take(cs.len as usize - cs.instrs.len()));
        for instr in instrs {
            let RamInstr { opcode, dest, op1, op2, imm } = instr;
            h.update(&u8::to_le_bytes(opcode));
            h.update(&u8::to_le_bytes(dest));
            h.update(&u8::to_le_bytes(op1));
            h.update(&u64::to_le_bytes(op2));
            h.update(&u8::to_le_bytes(imm as u8));
        }
        code_count += 1;
    }
    eprintln!("hashed {} secret code segments", code_count);

    let mut mem_count = 0;
    for ms in &exec.init_mem {
        if !ms.secret || ms.uncommitted {
            continue;
        }
        let words = ms.data.iter().cloned()
            .chain(iter::repeat(0).take(ms.len as usize - ms.data.len()));
        for word in words {
            h.update(&u64::to_le_bytes(word));
        }
        mem_count += 1;
    }
    eprintln!("hashed {} secret memory segments", mem_count);

    let hash = h.finalize();

    // Set `params.commitment` to the computed hash.

    let mut commitment = String::from("sha256:");
    commitment.reserve(64);
    for &b in &hash {
        write!(commitment, "{:02x}", b)
            .map_err(|e| e.to_string())?;
    }
    debug_assert_eq!(commitment.len(), "sha256:".len() + 64);

    eprintln!("commitment = {:?}", commitment);

    add_commitment(v_exec, commitment);


    // Write the output file, if needed.

    if let Some(out_path) = out_path {
        write_output(out_path, &v)?;
    }

    Ok(())
}
*/


enum Format {
    Yaml,
    Cbor,
    Json,
}

impl Format {
    fn from_path(path: &Path) -> Format {
        match path.extension().and_then(|os| os.to_str()) {
            Some("yaml") => Format::Yaml,
            Some("cbor") => Format::Cbor,
            Some("json") => Format::Json,
            _ => Format::Cbor,
        }
    }
}


fn to_hex_string(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        write!(s, "{:02x}", b).unwrap();
    }
    s
}

fn parse_hex_string(s: &str) -> Result<Vec<u8>, String> {
    if s.len() % 2 != 0 {
        return Err("bad input length (odd number of hex digits)".into());
    }

    let mut bytes = Vec::with_capacity(s.len() / 2);
    for i in (0 .. s.len()).step_by(2) {
        let byte_hex = s.get(i .. i + 2)
            .ok_or("invalid unicode characters in hex string")?;
        let byte = u8::from_str_radix(byte_hex, 16)
            .map_err(|e| format!("error parsing hex byte {:?}: {}", byte_hex, e))?;
        bytes.push(byte);
    }
    Ok(bytes)
}

fn to_byte_array_string(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 5);
    s.push_str("[");

    for (i, &b) in bytes.iter().enumerate() {
        if i % 16 == 0 {
            s.push_str("\n    ");
        } else {
            s.push_str(" ");
        }
        write!(s, "{},", b).unwrap();
    }

    s.push_str("\n]");
    s
}

fn to_word_array_string(words: impl IntoIterator<Item = u64>) -> String {
    let mut s = String::new();
    s.push_str("[");

    for (i, w) in words.into_iter().enumerate() {
        if i % 8 == 0 {
            s.push_str("\n    ");
        } else {
            s.push_str(" ");
        }
        write!(s, "{},", w).unwrap();
    }

    s.push_str("\n]");
    s
}

fn iter_words<'a>(bytes: &'a [u8]) -> impl Iterator<Item = u64> + 'a {
    (0 .. bytes.len()).step_by(8).map(move |i| {
        let slice = &bytes[i .. i + 8];
        let arr = <[u8; 8]>::try_from(slice).unwrap();
        u64::from_le_bytes(arr)
    })
}

fn sha256_bytes_to_words(x: [u8; 32]) -> [u32; 8] {
    let mut out = [0; 8];
    for i in 0 .. 8 {
        let mut buf = [0_u8; 4];
        buf.copy_from_slice(&x[i * 4 .. (i + 1) * 4]);
        out[i] = u32::from_be_bytes(buf);
    }
    out
}


fn run_calc(args: &ArgMatches) -> Result<(), String> {
    let in_path = Path::new(args.value_of_os("trace")
        .ok_or("cbor path is required")?);
    let exec = match Format::from_path(in_path) {
        Format::Yaml => get_exec(&parse_file::<serde_yaml::Value>(in_path)?)?.0,
        Format::Cbor => get_exec(&parse_file::<serde_cbor::Value>(in_path)?)?.0,
        Format::Json => todo!("json support"),
    };

    // Sample randomness.
    let randomness_len = count_randomness_words(&exec);
    let randomness = if args.is_present("keep-randomness") {
        gather_randomness(&exec)?
    } else {
        let mut bytes = vec![0_u8; randomness_len * 8];
        getrandom::getrandom(&mut bytes).map_err(|e| e.to_string())?;
        bytes
    };
    assert_eq!(randomness.len(), randomness_len * 8);

    // Compute commitment.
    let commitment = calc_commitment(&exec, Some(iter_words(&randomness)))?;

    // Compute RNG seed.
    let steps = count_steps(&exec);
    let seed = calc_rng_seed(&commitment, steps);

    // Print output
    println!("randomness hex = {}", to_hex_string(&randomness));
    println!("randomness bytes = {}", to_byte_array_string(&randomness));
    println!("randomness words = {}", to_word_array_string(iter_words(&randomness)));
    println!("commitment = sha256:{}", to_hex_string(&commitment));
    println!("steps = {}", steps);
    println!("rng seed hex = {}", to_hex_string(&seed));
    println!("rng seed bytes = {}", to_byte_array_string(&seed));
    println!("rng seed words = {}", to_word_array_string(iter_words(&seed)));

    Ok(())
}


fn run_update_cbor(args: &ArgMatches) -> Result<(), String> {
    let in_path = Path::new(args.value_of_os("trace")
        .ok_or("cbor path is required")?);
    match Format::from_path(in_path) {
        Format::Yaml => run_update_cbor_typed::<serde_yaml::Value>(args, in_path),
        Format::Cbor => run_update_cbor_typed::<serde_cbor::Value>(args, in_path),
        Format::Json => todo!("json support"),
    }
}

fn run_update_cbor_typed<V: Value>(args: &ArgMatches, in_path: &Path) -> Result<(), String> {
    let mut v = parse_file::<V>(in_path)?;
    let (exec, v_exec) = get_exec_mut(&mut v)?;

    let randomness: Vec<u8>;
    if let Some(randomness_str) = args.value_of("set-randomness") {
        randomness = parse_hex_string(randomness_str)
            .map_err(|e| format!("error parsing --set-randomness argument: {}", e))?;
        set_randomness_value(v_exec, &exec, iter_words(&randomness))?;
    } else {
        randomness = gather_randomness(&exec)?;
    }

    let commitment: Commitment;
    if let Some(commitment_str) = args.value_of("set-commitment") {
        let commitment_value = V::new_string(commitment_str.to_owned());
        commitment = commitment_value.parse::<Commitment>().map_err(|e| e.to_string())?;
        set_commitment_value(v_exec, commitment_str.to_owned())?;
    } else {
        commitment = exec.params.commitment
            .ok_or("expected input file to contain params.commitment")?;
    }

    let expect_commitment_bytes = calc_commitment(&exec, Some(iter_words(&randomness)))?;
    let expect_commitment = Commitment::Sha256(sha256_bytes_to_words(expect_commitment_bytes));
    if commitment != expect_commitment {
        return Err(format!("invalid commitment: expected {:?}, but got {:?}",
            expect_commitment, commitment));
    } else {
        println!("commitment OK");
    }

    let steps = count_steps(&exec);
    let expect_seed = calc_rng_seed(&expect_commitment_bytes, steps);
    if let Some(seed) = find_rng_seed(&exec)? {
        if &seed as &[_] != &expect_seed {
            return Err(format!("invalid rng seed: expected {:?}, but got {:?}",
                expect_seed, seed));
        }
        println!("rng seed OK");
    } else {
        println!("rng seed OK (not present)");
    }

    if let Some(out_path) = args.value_of_os("output") {
        write_output(Path::new(out_path), &v)?;
    }

    Ok(())
}


fn real_main() -> Result<(), String> {
    let args = parse_args();

    let (cmd, opt_sub_args) = args.subcommand();
    let sub_args = opt_sub_args.ok_or("missing subcommand")?;
    match cmd {
        "calc" => run_calc(sub_args),
        "update-cbor" => run_update_cbor(sub_args),
        _ => unreachable!("bad command {:?}", cmd),
    }

    /*
    let in_path = Path::new(args.value_of_os("trace")
        .ok_or("cbor path is required")?);
    let out_path = args.value_of_os("output").map(Path::new);

    if let Some(commitment) = args.value_of("verifier-commitment") {
        // Run in verifier mode, with a fixed commitment.
        let commitment = commitment.to_owned();
        match Format::from_path(in_path) {
            Format::Yaml => run_verifier::<serde_yaml::Value>(in_path, out_path, commitment)?,
            Format::Cbor => run_verifier::<serde_cbor::Value>(in_path, out_path, commitment)?,
            Format::Json => todo!("json support"),
        }
    } else {
        match Format::from_path(in_path) {
            Format::Yaml => run::<serde_yaml::Value>(in_path, out_path)?,
            Format::Cbor => run::<serde_cbor::Value>(in_path, out_path)?,
            Format::Json => todo!("json support"),
        }
    }

    Ok(())
    */
}

fn main() -> Result<(), String> {
    let mode = Mode::MemorySafety;
    unsafe { with_mode(mode, || real_main()) }
}