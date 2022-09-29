use std::collections::HashSet;
use std::fmt::Write as _;
use std::fs::File;
use std::io::Read;
use std::iter;
use std::path::Path;
use cheesecloth::micro_ram::feature::{self, Version, Feature};
use cheesecloth::micro_ram::fetch;
use cheesecloth::micro_ram::parse;
use cheesecloth::micro_ram::types::{ExecBody, RamInstr};
use cheesecloth::mode::if_mode::{Mode, with_mode};
use clap::{App, Arg, ArgMatches};
use getrandom;
use serde::Serialize;
use serde::de::DeserializeOwned;
use sha2::{Sha256, Digest};


fn parse_args() -> ArgMatches<'static> {
    App::new("add_commitment")
        .about("add a commitment to a MicroRAM CBOR file")
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
        .arg(Arg::with_name("verifier-commitment")
             .long("verifier-commitment")
             .takes_value(true)
             .value_name("COMMITMENT")
             .help("run in verifier mode, setting params.commitment to COMMITMENT"))
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

    for cs in &exec.program {
        if !cs.secret {
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
    }

    for ms in &exec.init_mem {
        if !ms.secret {
            continue;
        }
        let words = ms.data.iter().cloned()
            .chain(iter::repeat(0).take(ms.len as usize - ms.data.len()));
        for word in words {
            h.update(&u64::to_le_bytes(word));
        }
    }

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

fn real_main() -> Result<(), String> {
    let args = parse_args();

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
}

fn main() -> Result<(), String> {
    let mode = Mode::MemorySafety;
    unsafe { with_mode(mode, || real_main()) }
}
