use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use crate::ir::circuit::{Wire, EraseVisitor, MigrateVisitor};
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
    fn post_erase(&mut self, v: &mut EraseVisitor<'a>);

    /// Called at the end of the `migrate` step, after the `MigrateVisitor` has been applied to all
    /// other objects in the program.
    ///
    /// Safety: This method must migrate all wires stored within the backend.  Any wires not
    /// migrated will be left dangling when `MigrateHandle::erase_and_migrate` is called.
    fn post_migrate(&mut self, v: &mut MigrateVisitor<'a, 'a>);

    /// Assert that `accepted` is true, and finish writing out the circuit.  If `validate` is set,
    /// a validation pass will be run on the output afterward.
    fn finish(self: Box<Self>, accepted: Wire<'a>, validate: bool);
}


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
            fn post_erase(&mut self, v: &mut EraseVisitor<'w>) {
                self.backend.post_erase(v);
            }

            fn post_migrate(&mut self, v: &mut MigrateVisitor<'w, 'w>) {
                self.backend.post_migrate(v);
            }

            fn finish(mut self: Box<Self>, accepted: Wire<'w>, validate: bool) {
                self.backend.enforce_true(accepted);

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
        panic!("zkinterface output is not supported - build with `--features bellman`");
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
            fn post_erase(&mut self, v: &mut EraseVisitor<'w>) {
                self.backend.post_erase(v);
            }

            fn post_migrate(&mut self, v: &mut MigrateVisitor<'w, 'w>) {
                self.backend.post_migrate(v);
            }

            fn finish(mut self: Box<Self>, accepted: Wire<'w>, validate: bool) {
                let workspace = self.workspace.clone();

                self.backend.enforce_true(accepted);
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
        panic!("SIEVE IR output is not supported - build with `--features sieve_ir`");
    }
}


pub fn new_dummy<'a>() -> Box<dyn Backend<'a> + 'a> {
    Box::new(())
}

#[allow(unused)]
unsafe impl<'a> Backend<'a> for () {
    fn post_erase(&mut self, v: &mut EraseVisitor<'a>) {}
    fn post_migrate(&mut self, v: &mut MigrateVisitor<'a, 'a>) {}
    fn finish(self: Box<Self>, accepted: Wire<'a>, validate: bool) {}
}


pub fn new_stats<'a>() -> Box<dyn Backend<'a> + 'a> {
    #[derive(Default)]
    struct BackendWrapper<'a> {
        stats: Stats<'a>,
    }

    return Box::new(BackendWrapper::default());


    unsafe impl<'a> Backend<'a> for BackendWrapper<'a> {
        fn post_erase(&mut self, v: &mut EraseVisitor<'a>) {
            self.stats.add_iter(v.erased().iter().map(|&(w, _)| w));
            migrate::migrate_in_place(v, &mut self.stats);
        }

        fn post_migrate(&mut self, v: &mut MigrateVisitor<'a, 'a>) {
            migrate::migrate_in_place(v, &mut self.stats);
        }

        fn finish(mut self: Box<Self>, accepted: Wire<'a>, _validate: bool) {
            self.stats.add(&[accepted]);
            eprintln!(" ===== stats =====");
            self.stats.print();
            eprintln!(" ===== end stats =====");
        }
    }
}
