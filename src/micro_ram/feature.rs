use std::collections::HashSet;
use serde::{Deserialize, Deserializer};

macro_rules! define_features {
    (
        $( $Variant:ident = $str:expr, )*
    ) => {
        #[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
        pub enum Feature {
            $($Variant,)*
        }

        impl<'de> Deserialize<'de> for Feature {
            fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
                let s = String::deserialize(d)?;
                match &s as &str {
                    $( $str => Ok(Feature::$Variant), )*
                    _ => return Err(serde::de::Error::custom(format_args!(
                        "unknown feature string {:?}", s,
                    ))),
                }
            }
        }
    };
}

define_features! {
    PublicPc = "public-pc",
}


#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Default)]
pub struct Version(pub u8, pub u8, pub u8, pub u8);

impl<'de> Deserialize<'de> for Version {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let (a, b, c, d) = Deserialize::deserialize(d)?;
        Ok(Version(a, b, c, d))
    }
}

macro_rules! define_versions {
    (
        $( ($($v:expr),*) = { $($variants:tt)* }, )*
    ) => {
        pub static VERSIONS: &[(Version, &[Feature])] = &[
            $( (Version($($v),*), &[ $(Feature::$variants)* ]), )*
        ];
    };
}

define_versions! {
    (0,1,0,0) = {},
}

pub fn lookup_version(v: Version) -> Option<HashSet<Feature>> {
    for &(vv, fs) in VERSIONS {
        if v == vv {
            return Some(fs.iter().cloned().collect::<HashSet<_>>());
        }
    }
    None
}
