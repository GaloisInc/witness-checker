use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use num_bigint::BigUint;
use crate::eval::{self, CachingEvaluator};
use crate::ir::circuit::{CircuitBase, Wire, EraseVisitor, MigrateVisitor};
use crate::ir::migrate;
use crate::stats::Stats;


/// Trait for abstracting over backends.  `post_erase` and `post_migrate` are callbacks to be
/// invoked during `MigrateHandle::erase_and_migrate`.  `finish` is used to finish writing the
/// low-level circuit.
///
/// This trait is unsafe because `MigrateHandle` places special requirements on the behavior of
/// `post_migrate` for memory safety.
pub unsafe trait Backend<'a> {
    /// Called at the end of the `erase` step, after the `EraseVisitor` has been applied to all
    /// other objects in the program.
    fn post_erase(&mut self, v: &mut EraseVisitor<'a, '_>);

    /// Called at the end of the `migrate` step, after the `MigrateVisitor` has been applied to all
    /// other objects in the program.
    ///
    /// Safety: This method must migrate all wires stored within the backend.  Any wires not
    /// migrated will be left dangling when `MigrateHandle::erase_and_migrate` is called.
    fn post_migrate(&mut self, v: &mut MigrateVisitor<'a, 'a, '_>);

    /// Assert that `accepted` is true, and finish writing out the circuit.  If `validate` is set,
    /// a validation pass will be run on the output afterward.
    fn finish(
        self: Box<Self>,
        c: &CircuitBase<'a>,
        ev: &mut CachingEvaluator<'a, '_, eval::RevealSecrets>,
        accepted: Wire<'a>,
        validate: bool,
    );
}


macro_rules! declare_use_plugins {
    ($($plugin:ident),*) => {
        #[derive(Clone, Copy, PartialEq, Eq, Debug)]
        pub struct UsePlugins {
            $(pub $plugin: bool,)*
        }

        impl UsePlugins {
            pub fn none() -> UsePlugins {
                UsePlugins {
                    $($plugin: false,)*
                }
            }

            pub fn all() -> UsePlugins {
                UsePlugins {
                    $($plugin: true,)*
                }
            }

            pub fn set(&mut self, name: &str, value: bool) {
                let UsePlugins { $(ref mut $plugin,)* } = *self;
                match name {
                    $(stringify!($plugin) => { *$plugin = value; },)*
                    // Ignore unknown plugins
                    _ => {},
                }
            }

            /// Parse a comma-separated list of plugin names into an `UsePlugins` set that
            /// contains only those plugins.
            pub fn from_str(x: &str) -> UsePlugins {
                let mut ap = UsePlugins::none();
                for name in x.split(",") {
                    ap.set(name.trim(), true);
                }
                ap
            }
        }
    };
}
declare_use_plugins!(mux_v0);


#[cfg(feature = "bellman")]
pub mod zkif;

pub fn new_zkif<'a>(dest: &OsStr) -> Box<dyn Backend<'a> + 'a> {
    #[cfg(feature = "bellman")]
    {
        use self::zkif::backend::Backend;
        use zkinterface::{cli::{cli, Options}, clean_workspace};


        struct BackendWrapper<'a> {
            backend: Backend<'a>,
            workspace: PathBuf,
        }


        // Clean workspace.
        let workspace = Path::new(dest);
        clean_workspace(workspace).unwrap();

        // Generate the circuit and witness.
        let backend = Backend::new(workspace, true);
        return Box::new(BackendWrapper {
            backend,
            workspace: workspace.to_owned(),
        });


        unsafe impl<'w> self::Backend<'w> for BackendWrapper<'w> {
            fn post_erase(&mut self, v: &mut EraseVisitor<'w, '_>) {
                self.backend.post_erase(v);
            }

            fn post_migrate(&mut self, v: &mut MigrateVisitor<'w, 'w, '_>) {
                self.backend.post_migrate(v);
            }

            fn finish(
                mut self: Box<Self>,
                c: &CircuitBase<'w>,
                ev: &mut CachingEvaluator<'w, '_, eval::RevealSecrets>,
                accepted: Wire<'w>,
                validate: bool,
            ) {
                self.backend.enforce_true(c, accepted);

                // Write files.
                self.backend.finish().unwrap();

                eprintln!("validating zkif...");

                if validate {
                    // Validate the circuit and witness.
                    cli(&Options {
                        tool: "simulate".to_string(),
                        paths: vec![self.workspace.clone()],
                        field_order: Default::default(),
                    }).unwrap();
                }

                // Print statistics.
                cli(&Options {
                    tool: "stats".to_string(),
                    paths: vec![self.workspace.clone()],
                    field_order: Default::default(),
                }).unwrap();
            }
        }
    }
    #[cfg(not(feature = "bellman"))]
    {
        panic!("zkinterface output is not enabled - build with `--features bellman`");
    }
}


#[cfg(feature = "sieve_ir")]
pub mod sieve_ir;

pub fn new_sieve_ir<'a>(workspace: &str, dedup: bool) -> Box<dyn Backend<'a> + 'a> {
    #[cfg(feature = "sieve_ir")]
    {
        use self::sieve_ir::{
            backend::{Backend, Scalar},
            ir_builder::IRBuilder,
        };
        use zki_sieve::{
            cli::{cli, Options, StructOpt},
            FilesSink,
        };

        struct BackendWrapper<'w> {
            backend: Backend<'w, IRBuilder<FilesSink>>,
            workspace: String,
        }


        let sink = FilesSink::new_clean(&workspace).unwrap();
        sink.print_filenames();
        let mut ir_builder = IRBuilder::new::<Scalar>(sink);
        // ir_builder.enable_profiler();
        if !dedup {
            ir_builder.disable_dedup();
        }

        let backend = Backend::new(ir_builder);
        return Box::new(BackendWrapper {
            backend,
            workspace: workspace.to_owned(),
        });


        unsafe impl<'w> self::Backend<'w> for BackendWrapper<'w> {
            fn post_erase(&mut self, v: &mut EraseVisitor<'w, '_>) {
                self.backend.post_erase(v);
            }

            fn post_migrate(&mut self, v: &mut MigrateVisitor<'w, 'w, '_>) {
                self.backend.post_migrate(v);
            }

            fn finish(
                mut self: Box<Self>,
                c: &CircuitBase<'w>,
                ev: &mut CachingEvaluator<'w, '_, eval::RevealSecrets>,
                accepted: Wire<'w>,
                validate: bool,
            ) {
                let workspace = self.workspace.clone();

                self.backend.enforce_true(c, accepted);
                let ir_builder = self.backend.finish();

                eprintln!();
                ir_builder.prof.as_ref().map(|p| p.print_report());
                ir_builder.dedup.as_ref().map(|p| p.print_report());
                ir_builder.finish();

                // Validate the circuit and witness.
                if validate {
                    eprintln!("\nValidating SIEVE IR files...");
                    cli(&Options::from_iter(&["zki_sieve", "validate", &workspace])).unwrap();
                    cli(&Options::from_iter(&["zki_sieve", "evaluate", &workspace])).unwrap();
                }
                cli(&Options::from_iter(&["zki_sieve", "metrics", &workspace])).unwrap();
            }
        }
    }
    #[cfg(not(feature = "sieve_ir"))]
    {
        panic!("SIEVE IR output is not enabled - build with `--features sieve_ir`");
    }
}


#[cfg(feature = "sieve_ir")]
pub mod sieve_ir_v2;

pub fn new_sieve_ir_v2<'a>(
    workspace: &str,
    modulus: Option<BigUint>,
    dedup: bool,
) -> Box<dyn Backend<'a> + 'a> {
    #[cfg(feature = "sieve_ir")]
    {
        use self::sieve_ir_v2::{
            backend::{Backend, Scalar},
            ir_builder::IRBuilder,
        };
        use zki_sieve_v3::{
            cli::{cli, Options, StructOpt},
            FilesSink,
        };

        struct BackendWrapper<'w> {
            backend: Backend<'w, IRBuilder<FilesSink>>,
            workspace: String,
        }


        let sink = FilesSink::new_clean(&workspace).unwrap();
        sink.print_filenames();
        let mut ir_builder = IRBuilder::new::<Scalar>(sink, modulus);
        // ir_builder.enable_profiler();
        if !dedup {
            ir_builder.disable_dedup();
        }

        let backend = Backend::new(ir_builder);
        return Box::new(BackendWrapper {
            backend,
            workspace: workspace.to_owned(),
        });


        unsafe impl<'w> self::Backend<'w> for BackendWrapper<'w> {
            fn post_erase(&mut self, v: &mut EraseVisitor<'w, '_>) {
                self.backend.post_erase(v);
            }

            fn post_migrate(&mut self, v: &mut MigrateVisitor<'w, 'w, '_>) {
                self.backend.post_migrate(v);
            }

            fn finish(
                mut self: Box<Self>,
                c: &CircuitBase<'w>,
                ev: &mut CachingEvaluator<'w, '_, eval::RevealSecrets>,
                accepted: Wire<'w>,
                validate: bool,
            ) {
                let workspace = self.workspace.clone();

                self.backend.enforce_true(c, accepted);
                let ir_builder = self.backend.finish();

                eprintln!();
                ir_builder.prof.as_ref().map(|p| p.print_report());
                ir_builder.dedup.as_ref().map(|p| p.print_report());
                ir_builder.finish();

                // Validate the circuit and witness.
                if validate {
                    eprintln!("\nValidating SIEVE IR files...");
                    cli(&Options::from_iter(&["zki_sieve", "validate", &workspace])).unwrap();
                    cli(&Options::from_iter(&["zki_sieve", "evaluate", &workspace])).unwrap();
                }
                cli(&Options::from_iter(&["zki_sieve", "metrics", &workspace])).unwrap();
            }
        }
    }
    #[cfg(not(feature = "sieve_ir"))]
    {
        panic!("SIEVE IR0+ output is not enabled - build with `--features sieve_ir`");
    }
}


pub mod boolean;

pub fn new_boolean_sieve_ir<'a>(workspace: &str) -> Box<dyn Backend<'a> + 'a> {
    #[cfg(feature = "sieve_ir")]
    {
        use self::boolean::Backend;
        use self::boolean::sink_sieve_ir_function::SieveIrV1Sink;
        use zki_sieve::{
            cli::{cli, Options, StructOpt},
            FilesSink,
        };

        struct BackendWrapper<'w> {
            backend: Backend<'w, SieveIrV1Sink<FilesSink>>,
            workspace: String,
        }


        let sink = FilesSink::new_clean(&workspace).unwrap();
        sink.print_filenames();
        let bool_sink = SieveIrV1Sink::new(sink, UsePlugins::none());
        let backend = Backend::new(bool_sink);
        return Box::new(BackendWrapper {
            backend,
            workspace: workspace.to_owned(),
        });


        unsafe impl<'w> self::Backend<'w> for BackendWrapper<'w> {
            fn post_erase(&mut self, v: &mut EraseVisitor<'w, '_>) {
                self.backend.post_erase(v);
            }

            fn post_migrate(&mut self, v: &mut MigrateVisitor<'w, 'w, '_>) {
                self.backend.post_migrate(v);
            }

            fn finish(
                mut self: Box<Self>,
                c: &CircuitBase<'w>,
                ev: &mut CachingEvaluator<'w, '_, eval::RevealSecrets>,
                accepted: Wire<'w>,
                validate: bool,
            ) {
                let workspace = self.workspace.clone();

                self.backend.enforce_true(c, accepted);
                let bool_sink = self.backend.finish();
                let sink = bool_sink.finish();

                eprintln!();

                // Validate the circuit and witness.
                if validate {
                    eprintln!("\nValidating SIEVE IR files...");
                    cli(&Options::from_iter(&["zki_sieve", "validate", &workspace])).unwrap();
                    cli(&Options::from_iter(&["zki_sieve", "evaluate", &workspace])).unwrap();
                }
                cli(&Options::from_iter(&["zki_sieve", "metrics", &workspace])).unwrap();
            }
        }
    }
    #[cfg(not(feature = "sieve_ir"))]
    {
        panic!("SIEVE IR output is not enabled - build with `--features sieve_ir`");
    }
}

pub fn new_boolean_sieve_ir_v2<'a>(
    workspace: &str,
    use_plugins: UsePlugins,
) -> Box<dyn Backend<'a> + 'a> {
    #[cfg(feature = "sieve_ir")]
    {
        use self::boolean::Backend;
        use self::boolean::sink_sieve_ir_function::SieveIrV2Sink;
        use zki_sieve_v3::{
            cli::{cli, Options, StructOpt},
            FilesSink,
        };

        struct BackendWrapper<'w> {
            backend: Backend<'w, SieveIrV2Sink<FilesSink>>,
            workspace: String,
        }


        let sink = FilesSink::new_clean(&workspace).unwrap();
        sink.print_filenames();
        let bool_sink = SieveIrV2Sink::new(sink, use_plugins);
        let backend = Backend::new(bool_sink);
        return Box::new(BackendWrapper {
            backend,
            workspace: workspace.to_owned(),
        });


        unsafe impl<'w> self::Backend<'w> for BackendWrapper<'w> {
            fn post_erase(&mut self, v: &mut EraseVisitor<'w, '_>) {
                self.backend.post_erase(v);
            }

            fn post_migrate(&mut self, v: &mut MigrateVisitor<'w, 'w, '_>) {
                self.backend.post_migrate(v);
            }

            fn finish(
                mut self: Box<Self>,
                c: &CircuitBase<'w>,
                ev: &mut CachingEvaluator<'w, '_, eval::RevealSecrets>,
                accepted: Wire<'w>,
                validate: bool,
            ) {
                let workspace = self.workspace.clone();

                self.backend.enforce_true(c, accepted);
                let bool_sink = self.backend.finish();
                let sink = bool_sink.finish();

                eprintln!();

                // Validate the circuit and witness.
                if validate {
                    eprintln!("\nValidating SIEVE IR files...");
                    cli(&Options::from_iter(&["zki_sieve", "validate", &workspace])).unwrap();
                    cli(&Options::from_iter(&["zki_sieve", "evaluate", &workspace])).unwrap();
                }
                cli(&Options::from_iter(&["zki_sieve", "metrics", &workspace])).unwrap();
            }
        }
    }
    #[cfg(not(feature = "sieve_ir"))]
    {
        panic!("SIEVE IR0+ output is not enabled - build with `--features sieve_ir`");
    }
}


pub fn new_dummy<'a>() -> Box<dyn Backend<'a> + 'a> {
    Box::new(())
}

#[allow(unused)]
unsafe impl<'a> Backend<'a> for () {
    fn post_erase(&mut self, v: &mut EraseVisitor<'a, '_>) {}
    fn post_migrate(&mut self, v: &mut MigrateVisitor<'a, 'a, '_>) {}
    fn finish(
        self: Box<Self>,
        c: &CircuitBase<'a>,
        ev: &mut CachingEvaluator<'a, '_, eval::RevealSecrets>,
        accepted: Wire<'a>,
        validate: bool,
    ) {}
}


pub fn new_stats<'a>() -> Box<dyn Backend<'a> + 'a> {
    #[derive(Default)]
    struct BackendWrapper<'a> {
        stats: Stats<'a>,
    }

    return Box::new(BackendWrapper::default());


    unsafe impl<'a> Backend<'a> for BackendWrapper<'a> {
        fn post_erase(&mut self, v: &mut EraseVisitor<'a, '_>) {
            self.stats.add_iter(v.erased().iter().map(|&(w, _)| w));
            migrate::migrate_in_place(v, &mut self.stats);
        }

        fn post_migrate(&mut self, v: &mut MigrateVisitor<'a, 'a, '_>) {
            migrate::migrate_in_place(v, &mut self.stats);
        }

        fn finish(
            mut self: Box<Self>,
            _c: &CircuitBase<'a>,
            _ev: &mut CachingEvaluator<'a, '_, eval::RevealSecrets>,
            accepted: Wire<'a>,
            _validate: bool,
        ) {
            self.stats.add(&[accepted]);
            eprintln!(" ===== stats =====");
            self.stats.print();
            eprintln!(" ===== end stats =====");
        }
    }
}
