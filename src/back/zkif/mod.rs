pub mod backend;
mod zkif_cs;
mod representer;
mod num;
mod bit_width;
mod int;
mod uint32;

//mod gadget_specs;
//mod prototype_backend;
//mod mem;
//mod debug;

#[cfg(feature = "libsnark")]
mod gadgetlib;
#[cfg(feature = "libsnark")]
mod machine;

use zkinterface::{
    statement::{StatementBuilder, Store, FileStore},
    Result,
    CircuitOwned, VariablesOwned, KeyValueOwned,
};
