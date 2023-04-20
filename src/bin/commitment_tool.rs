use std::cmp;
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
use cheesecloth::micro_ram::types::{ExecBody, RamInstr, Commitment, WORD_BYTES};
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
            .arg(Arg::with_name("randomness-symbol")
                 .long("randomness-symbol")
                 .takes_value(true)
                 .value_name("NAME")
                 .help("symbol/label where randomness starts in memory; useful \
                        when randomness is not in its own memory segment"))
            .arg(Arg::with_name("randomness-length")
                 .long("randomness-length")
                 .takes_value(true)
                 .value_name("N")
                 .help("length of randomness in memory; useful when randomness \
                        is not in its own memory segment"))
            .arg(Arg::with_name("machine-readable")
                 .long("machine-readable")
                 .help("produce machine-readable output"))
            .arg(Arg::with_name("uncommitted")
                 .long("uncommitted")
                 .takes_value(true)
                 .value_name("NAME")
                 .multiple(true)
                 .number_of_values(1)
                 .help("treat the named secret memory segments as uncommitted"))
        )
        .subcommand(SubCommand::with_name("check")
            .about("check that the commitment in a CBOR file is valid")
            .arg(Arg::with_name("trace")
                 .takes_value(true)
                 .value_name("TRACE.CBOR")
                 .help("MicroRAM execution trace")
                 .required(true))
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
            .arg(Arg::with_name("randomness-symbol")
                 .long("randomness-symbol")
                 .takes_value(true)
                 .value_name("NAME")
                 .help("symbol/label where randomness starts in memory; useful \
                        when randomness is not in its own memory segment"))
            .arg(Arg::with_name("randomness-length")
                 .long("randomness-length")
                 .takes_value(true)
                 .value_name("N")
                 .help("length of randomness in memory; useful when randomness \
                        is not in its own memory segment"))
            .arg(Arg::with_name("set-uncommitted")
                 .long("set-uncommitted")
                 .takes_value(true)
                 .value_name("NAME")
                 .multiple(true)
                 .number_of_values(1)
                 .help("mark the named secret memory segments as uncommitted in the output CBOR"))
        )
        .get_matches()
}


type Error = String;

trait Value: Sized + Serialize {
    fn from_reader<R: Read>(r: R) -> Result<Self, Error>;
    fn new_bool(b: bool) -> Self;
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

    fn new_bool(x: bool) -> Self {
        x.into()
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

    fn new_bool(x: bool) -> Self {
        x.into()
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

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
struct MemRange {
    pub segment_idx: usize,
    pub start: u64,
    pub end: u64,
}

impl MemRange {
    pub fn len(&self) -> usize {
        (self.end - self.start) as usize
    }
}

fn find_randomness(exec: &ExecBody, args: &ArgMatches) -> Result<MemRange, String> {
    if let Some(sym) = args.value_of("randomness-symbol") {
        let start = {
            let mut found_addr: Option<u64> = None;
            for (name, &addr) in exec.labels.iter() {
                if let Some((name, _)) = name.split_once('#') {
                    if name == sym {
                        if found_addr.is_some() {
                            return Err(format!(
                                "found multiple symbols named {:?} in exec.labels", sym));
                        }
                        found_addr = Some(addr);
                    }
                }
            }
            found_addr.ok_or_else(|| format!("symbol {:?} not found in exec.labels", sym))?
        };

        let len_str = args.value_of("randomness-length")
            .ok_or_else(|| {
                "must set --randomness-length when using --randomness-symbol".to_owned()
            })?;
        let len = len_str.parse::<u64>()
            .map_err(|e| format!("failed to parse randomness length {:?}: {}", len_str, e))?;

        let end = start.checked_add(len)
            .ok_or_else(|| "overflow when calculating randomness end".to_owned())?;

        let mut found: Option<usize> = None;
        for (i, ms) in exec.init_mem.iter().enumerate() {
            let ms_start_addr = ms.start * WORD_BYTES as u64;
            let ms_end_addr = ms_start_addr + ms.len * WORD_BYTES as u64;
            if ms_start_addr <= start && start < ms_end_addr {
                if !(end <= ms_end_addr) {
                    return Err(format!(
                        "randomness 0x{:x}..0x{:x} overflows memory segment {} {:?}",
                        start, end, i, ms.name,
                    ));
                }
                if found.is_some() {
                    return Err(format!(
                        "found multiple segments containing randomness 0x{:x}..0x{:x}: \
                            {} {:?}, {} {:?}",
                        start, end, i, ms.name,
                        found.unwrap(), exec.init_mem[found.unwrap()].name,
                    ));
                }
                found = Some(i);
            }
        }
        let segment_idx = found
            .ok_or_else(|| format!("no segment contains randomness 0x{:x}..0x{:x}", start, end))?;

        Ok(MemRange { segment_idx, start, end })

    } else {
        let mut found: Option<usize> = None;
        for (i, ms) in exec.init_mem.iter().enumerate() {
            if ms.name.contains(RANDOMNESS_NAME) {
                if found.is_some() {
                    return Err(format!(
                        "found multiple segments containing randomness: {} {:?}, {} {:?}",
                        i, ms.name, found.unwrap(), exec.init_mem[found.unwrap()].name,
                    ));
                }
                found = Some(i);
            }
        }
        let segment_idx = found
            .ok_or_else(|| format!("found no segment named {:?}", RANDOMNESS_NAME))?;

        let start = 0;
        let end = exec.init_mem[segment_idx].len * WORD_BYTES as u64;
        Ok(MemRange { segment_idx, start, end })
    }
}

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
            eprintln!("warning: skipping uncommitted segment {:?}", ms.name);
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

fn gather_randomness(exec: &ExecBody, range: MemRange) -> Result<Vec<u8>, String> {
    let ms = &exec.init_mem[range.segment_idx];
    let bytes = word_bytes(&ms.data);

    let start_offset = (range.start - ms.start * WORD_BYTES as u64) as usize;
    let end_offset = start_offset + range.len();
    Ok((start_offset .. end_offset).map(|i| bytes.get(i).copied().unwrap_or(0)).collect())
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

/// Calculate a commitment for `exec`.  `randomness_range` gives the range of bytes that make up
/// the commitment randomness; when calculating the commitment, we replace those bytes with the
/// values in `randomness`.
fn calc_commitment(
    exec: &ExecBody,
    randomness: &[u8],
    randomness_range: MemRange,
    uncommitted_names: &HashSet<String>,
) -> Result<[u8; 32], String> {
    let mut h = Sha256::new();

    let mut code_count = 0;
    for cs in &exec.program {
        if !cs.secret || cs.uncommitted {
            continue;
        }
        eprintln!("hashing secret code segment {:?} (at {:x})", cs.name, cs.start * 8);
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
    for (i, ms) in exec.init_mem.iter().enumerate() {
        if !ms.secret || ms.uncommitted || uncommitted_names.contains(&ms.name) {
            continue;
        }
        eprintln!("hashing secret memory segment {:?} (at {:x})", ms.name, ms.start * 8);

        let mut words = ms.data.iter().cloned()
            .chain(iter::repeat(0).take(ms.len as usize - ms.data.len()))
            .collect::<Vec<_>>();

        if i == randomness_range.segment_idx && randomness_range.len() > 0 {
            let bytes = word_bytes_mut(&mut words);
            let start_offset = (randomness_range.start - ms.start * WORD_BYTES as u64) as usize;
            let end_offset = start_offset + randomness_range.len();
            bytes[start_offset .. end_offset].copy_from_slice(randomness);
        }

        for word in words {
            h.update(&u64::to_le_bytes(word));
        }
        mem_count += 1;
    }
    eprintln!("hashed {} secret memory segments", mem_count);

    let hash = h.finalize();

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
    randomness: &[u8],
    randomness_range: MemRange,
) -> Result<(), String> {
    let mut it = randomness.into_iter();

    let parsed_ms = &parsed_exec.init_mem[randomness_range.segment_idx];

    let mut words = parsed_ms.data.clone();
    let start_offset = (randomness_range.start - parsed_ms.start * WORD_BYTES as u64) as usize;
    let end_offset = start_offset + randomness_range.len();
    let end_offset_word = (end_offset + WORD_BYTES - 1) / WORD_BYTES;
    if words.len() < end_offset_word + 1 {
        words.resize(end_offset_word + 1, 0);
    }

    let bytes = word_bytes_mut(&mut words);
    bytes[start_offset .. end_offset].copy_from_slice(randomness);

    let init_mem = v_exec.get_key_mut("init_mem").unwrap();
    let ms = init_mem.get_index_mut(randomness_range.segment_idx).unwrap();
    let data = V::new_array(words.into_iter().map(V::new_u64).collect());
    ms.insert_key("data", data);

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

fn get_uncommitted_names(args: &ArgMatches, key: &str) -> HashSet<String> {
    let mut names = HashSet::new();
    if let Some(vals) = args.values_of(key) {
        for name in vals {
            names.insert(name.to_owned());
        }
    }
    names
}

fn set_uncommitted_flags<V: Value>(
    v_exec: &mut V,
    parsed_exec: &ExecBody,
    uncommitted_names: &HashSet<String>,
) -> Result<(), String> {
    for (i, parsed_ms) in parsed_exec.init_mem.iter().enumerate() {
        if !uncommitted_names.contains(&parsed_ms.name) {
            continue;
        }

        let init_mem = v_exec.get_key_mut("init_mem").unwrap();
        let ms = init_mem.get_index_mut(i).unwrap();
        let data = V::new_bool(true);
        ms.insert_key("uncommitted", data);
    }

    Ok(())

}


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
        let mut arr = [0; 8];
        let n = cmp::min(arr.len(), bytes.len() - i);
        arr[..n].copy_from_slice(&bytes[i .. i + n]);
        u64::from_le_bytes(arr)
    })
}

fn word_bytes<'a>(words: &'a [u64]) -> &'a [u8] {
    unsafe { slice::from_raw_parts(words.as_ptr() as *const u8, words.len() * 8) }
}

fn word_bytes_mut<'a>(words: &'a mut [u64]) -> &'a mut [u8] {
    unsafe { slice::from_raw_parts_mut(words.as_mut_ptr() as *mut u8, words.len() * 8) }
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
    let randomness_range = find_randomness(&exec, args)?;
    let randomness = if args.is_present("keep-randomness") {
        gather_randomness(&exec, randomness_range)?
    } else {
        let mut bytes = vec![0_u8; randomness_range.len()];
        getrandom::getrandom(&mut bytes).map_err(|e| e.to_string())?;
        bytes
    };

    // Compute commitment.
    let uncommitted_names = get_uncommitted_names(args, "uncommitted");
    let commitment = calc_commitment(
        &exec,
        &randomness,
        randomness_range,
        &uncommitted_names,
    )?;

    // Compute RNG seed.
    let steps = count_steps(&exec);
    let seed = calc_rng_seed(&commitment, steps);

    // Print output
    if !args.is_present("machine-readable") {
        println!("randomness hex = {}", to_hex_string(&randomness));
        println!("randomness bytes = {}", to_byte_array_string(&randomness));
        println!("randomness words = {}", to_word_array_string(iter_words(&randomness)));
        println!("commitment = sha256:{}", to_hex_string(&commitment));
        println!("steps = {}", steps);
        println!("rng seed hex = {}", to_hex_string(&seed));
        println!("rng seed bytes = {}", to_byte_array_string(&seed));
        println!("rng seed words = {}", to_word_array_string(iter_words(&seed)));
    } else {
        println!("randomness={}", to_hex_string(&randomness));
        println!("commitment={}", to_hex_string(&commitment));
        println!("rng_seed={}", to_hex_string(&seed));
    }

    Ok(())
}


fn run_check(args: &ArgMatches) -> Result<(), String> {
    let in_path = Path::new(args.value_of_os("trace")
        .ok_or("cbor path is required")?);
    let exec = match Format::from_path(in_path) {
        Format::Yaml => get_exec(&parse_file::<serde_yaml::Value>(in_path)?)?.0,
        Format::Cbor => get_exec(&parse_file::<serde_cbor::Value>(in_path)?)?.0,
        Format::Json => todo!("json support"),
    };

    // Get commitment from file
    let commitment = exec.params.commitment
        .ok_or("expected input file to contain params.commitment")?;

    // Compute commitment.
    let expect_commitment_bytes = calc_commitment(
        &exec,
        &[],
        MemRange { segment_idx: 0, start: 0, end: 0 },
        &HashSet::new(),
    )?;
    let expect_commitment = Commitment::Sha256(sha256_bytes_to_words(expect_commitment_bytes));
    if commitment != expect_commitment {
        return Err(format!("invalid commitment: expected {:?}, but got {:?}",
            expect_commitment, commitment));
    } else {
        println!("commitment OK");
    }

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

    let randomness_range = find_randomness(&exec, args)?;
    let randomness: Vec<u8>;
    if let Some(randomness_str) = args.value_of("set-randomness") {
        randomness = parse_hex_string(randomness_str)
            .map_err(|e| format!("error parsing --set-randomness argument: {}", e))?;
        set_randomness_value(v_exec, &exec, &randomness, randomness_range)?;
    } else {
        randomness = gather_randomness(&exec, randomness_range)?;
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

    let uncommitted_names = get_uncommitted_names(args, "set-uncommitted");
    if uncommitted_names.len() > 0 {
        set_uncommitted_flags(v_exec, &exec, &uncommitted_names)?;
    }

    let expect_commitment_bytes = calc_commitment(
        &exec,
        &randomness,
        randomness_range,
        &uncommitted_names,
    )?;
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
        "check" => run_check(sub_args),
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
