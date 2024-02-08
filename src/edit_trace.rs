//! Helpers for editing trace files in CBOR or YAML format.
use std::collections::HashSet;
use std::fs::File;
use std::io::Read;
use std::path::Path;
use serde::Serialize;
use serde::de::DeserializeOwned;
use crate::micro_ram::feature::{self, Feature, Version};
use crate::micro_ram::parse;
use crate::micro_ram::types::ExecBody;

pub type Error = String;

pub trait Value: Sized + Serialize + Clone + PartialEq {
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
    fn get_key_any(&self, k: &Self) -> Option<&Self>;
    fn get_key_any_mut(&mut self, k: &Self) -> Option<&mut Self>;
    fn len(&self) -> usize;
    fn push_array(&mut self, x: Self);
    fn keys(&self) -> Vec<Self>;
    fn insert_key(&mut self, k: &str, v: Self);
    fn remove_key(&mut self, k: &str);
    fn insert_key_any(&mut self, k: Self, v: Self);
    fn remove_key_any(&mut self, k: &Self);
    fn parse<T: DeserializeOwned>(&self) -> Result<T, Error>;
    fn from_serialize<T: Serialize>(x: &T) -> Result<Self, Error>;
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

    fn get_key_any(&self, k: &Self) -> Option<&Self> {
        match *self {
            serde_cbor::Value::Map(ref m) => m.get(k),
            _ => panic!("expected map"),
        }
    }

    fn get_key_any_mut(&mut self, k: &Self) -> Option<&mut Self> {
        match *self {
            serde_cbor::Value::Map(ref mut m) => m.get_mut(k),
            _ => panic!("expected map"),
        }
    }

    fn len(&self) -> usize {
        match *self {
            serde_cbor::Value::Array(ref a) => a.len(),
            serde_cbor::Value::Map(ref m) => m.len(),
            _ => panic!("expected array or map"),
        }
    }

    fn push_array(&mut self, v: Self) {
        match *self {
            serde_cbor::Value::Array(ref mut a) => { a.push(v); },
            _ => panic!("expected array"),
        }
    }

    fn keys(&self) -> Vec<Self> {
        match *self {
            serde_cbor::Value::Map(ref m) => {
                m.keys().cloned().collect()
            },
            _ => panic!("expected map"),
        }
    }

    fn insert_key(&mut self, k: &str, v: Self) {
        match *self {
            serde_cbor::Value::Map(ref mut m) => { m.insert(k.to_owned().into(), v); },
            _ => panic!("expected map"),
        }
    }

    fn remove_key(&mut self, k: &str) {
        match *self {
            serde_cbor::Value::Map(ref mut m) => { m.remove(&k.to_owned().into()); },
            _ => panic!("expected map"),
        }
    }

    fn insert_key_any(&mut self, k: Self, v: Self) {
        match *self {
            serde_cbor::Value::Map(ref mut m) => { m.insert(k, v); },
            _ => panic!("expected map"),
        }
    }

    fn remove_key_any(&mut self, k: &Self) {
        match *self {
            serde_cbor::Value::Map(ref mut m) => { m.remove(k); },
            _ => panic!("expected map"),
        }
    }

    fn parse<T: DeserializeOwned>(&self) -> Result<T, Error> {
        serde_cbor::value::from_value(self.clone())
            .map_err(|e| e.to_string())
    }

    fn from_serialize<T: Serialize>(x: &T) -> Result<Self, Error> {
        serde_cbor::value::to_value(&x)
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

    fn get_key_any(&self, k: &Self) -> Option<&Self> {
        match *self {
            serde_yaml::Value::Mapping(ref m) => m.get(k),
            _ => panic!("expected mapping"),
        }
    }

    fn get_key_any_mut(&mut self, k: &Self) -> Option<&mut Self> {
        match *self {
            serde_yaml::Value::Mapping(ref mut m) => m.get_mut(k),
            _ => panic!("expected mapping"),
        }
    }

    fn len(&self) -> usize {
        match *self {
            serde_yaml::Value::Sequence(ref s) => s.len(),
            serde_yaml::Value::Mapping(ref m) => m.len(),
            _ => panic!("expected sequence or mapping"),
        }
    }

    fn push_array(&mut self, v: Self) {
        match *self {
            serde_yaml::Value::Sequence(ref mut s) => { s.push(v); },
            _ => panic!("expected array"),
        }
    }

    fn keys(&self) -> Vec<Self> {
        match *self {
            serde_yaml::Value::Mapping(ref m) => {
                m.iter().map(|(k, _)| k.clone()).collect()
            },
            _ => panic!("expected mapping"),
        }
    }

    fn insert_key(&mut self, k: &str, v: Self) {
        match *self {
            serde_yaml::Value::Mapping(ref mut m) => { m.insert(k.to_owned().into(), v); },
            _ => panic!("expected mapping"),
        }
    }

    fn remove_key(&mut self, k: &str) {
        match *self {
            serde_yaml::Value::Mapping(ref mut m) => { m.remove(&k.to_owned().into()); },
            _ => panic!("expected mapping"),
        }
    }

    fn insert_key_any(&mut self, k: Self, v: Self) {
        match *self {
            serde_yaml::Value::Mapping(ref mut m) => { m.insert(k, v); },
            _ => panic!("expected mapping"),
        }
    }

    fn remove_key_any(&mut self, k: &Self) {
        match *self {
            serde_yaml::Value::Mapping(ref mut m) => { m.remove(k); },
            _ => panic!("expected mapping"),
        }
    }

    fn parse<T: DeserializeOwned>(&self) -> Result<T, Error> {
        serde_yaml::from_value(self.clone())
            .map_err(|e| e.to_string())
    }

    fn from_serialize<T: Serialize>(x: &T) -> Result<Self, Error> {
        serde_yaml::to_value(&x)
            .map_err(|e| e.to_string())
    }
}


pub fn set_param<V: Value>(exec: &mut V, key: &str, value: V) {
    if let Some(params) = exec.get_key_mut("params") {
        params.insert_key(key, value);
    } else {
        let mut m = V::new_map();
        m.insert_key(key, value);
        exec.insert_key("params", m);
    }
}

pub fn parse_file<V: Value>(path: &Path) -> Result<V, String> {
    let f = File::open(path).map_err(|e| e.to_string())?;
    V::from_reader(f)
}

pub fn write_output<V: Value>(out_path: &Path, v: &V) -> Result<(), String> {
    let f = File::create(out_path).map_err(|e| e.to_string())?;
    match Format::from_path(out_path) {
        Format::Yaml => serde_yaml::to_writer(f, v).map_err(|e| e.to_string())?,
        Format::Cbor => serde_cbor::to_writer(f, v).map_err(|e| e.to_string())?,
        Format::Json => serde_json::to_writer(f, v).map_err(|e| e.to_string())?,
    }
    Ok(())
}

pub fn check_version<V: Value>(v: &V) -> Result<HashSet<Feature>, String> {
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

pub fn get_exec<V: Value>(v: &V) -> Result<(ExecBody, &V), String> {
    let features = check_version(v)?;
    let v_exec = v.get_index(2).ok_or("missing execution")?;
    let mut exec = parse::with_features(features, || v_exec.parse::<ExecBody>())?;
    Ok((exec, v_exec))
}

pub fn get_exec_mut<V: Value>(v: &mut V) -> Result<(ExecBody, &mut V), String> {
    let features = check_version(v)?;
    let v_exec = v.get_index_mut(2).ok_or("missing execution")?;
    let mut exec = parse::with_features(features, || v_exec.parse::<ExecBody>())?;
    Ok((exec, v_exec))
}


pub enum Format {
    Yaml,
    Cbor,
    Json,
}

impl Format {
    pub fn from_path(path: &Path) -> Format {
        match path.extension().and_then(|os| os.to_str()) {
            Some("yaml") => Format::Yaml,
            Some("cbor") => Format::Cbor,
            Some("json") => Format::Json,
            _ => Format::Cbor,
        }
    }
}


