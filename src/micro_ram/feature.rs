use std::collections::HashSet;
use std::fmt;
use serde::{Deserialize, Deserializer};

macro_rules! define_features {
    (
        $( $(#[$attr:meta])* $Variant:ident = $str:expr, )*
    ) => {
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
        pub enum Feature {
            $( $(#[$attr])* $Variant,)*
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
    /// Pseudo-feature used to indicate MicroRAM versions that are known to produce buggy/invalid
    /// CBOR files.
    Buggy = "buggy",

    PublicPc = "public-pc",
    /// The keys of the `advice` dict are the index of the pre-state of the step that uses the
    /// advice, rather than the index of the post-state.  For example, the advice for the first
    /// step is placed at index 0 with this feature, rather than index 1.
    PreAdvice = "pre-advice",
    /// Initialized heap.
    HeapInit = "heap_init",
    LeakTainted = "leak-tainted",
    /// `advise` instruction takes an upper bound, and the circuit includes an assertion that the
    /// advice value is in bounds.
    AdviseMaxBound = "advise-max-bound",

    /// Multiple executions are provided. Also adds names to memory segments.
    MultiExec = "multi-exec",

    /// If present, the `program` is split into multiple code segments, similar to the way
    /// `init_mem` is broken into segments.
    CodeSegments = "code-segments",
}


#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Default)]
pub struct Version(pub u8, pub u8, pub u8, pub u8);

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}.{}.{}", self.0, self.1, self.2, self.3)
    }
}

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
            $( (Version($($v),*), &[ $(Feature::$variants,)* ]), )*
        ];
    };
}

define_versions! {
    (0,1,0,0) = {},
    (0,1,1,0) = { PublicPc PreAdvice },
    // 0.1.2.0 removes `params.trace_len`, which we already ignore in all public-pc traces, and
    // also removes `flag` from states, which we ignore always.
    (0,1,2,0) = { PublicPc PreAdvice },
    // 0.1.3.0 adds the heap init feature.
    (0,1,3,0) = { PublicPc PreAdvice HeapInit },
    // 0.1.4.0 adds the `labels` map, which we ignore.
    (0,1,4,0) = { PublicPc PreAdvice HeapInit Buggy },
    (0,1,4,1) = { PublicPc PreAdvice HeapInit },
    // 0.1.5.0 adds an upper-bound operand to the `advise` instruction.
    (0,1,5,0) = { PublicPc PreAdvice HeapInit AdviseMaxBound },
    // 0.1.6.0 adds multiple executions and named memory segments. 
    (0,1,6,0) = { PublicPc PreAdvice HeapInit AdviseMaxBound},
    // 0.1.7.0 adds code segments and `params.commitment`.
    (0,1,7,0) = { PublicPc PreAdvice HeapInit AdviseMaxBound CodeSegments },
}

pub fn lookup_version(v: Version) -> Option<HashSet<Feature>> {
    for &(vv, fs) in VERSIONS {
        if v == vv {
            return Some(fs.iter().cloned().collect::<HashSet<_>>());
        }
    }
    None
}
