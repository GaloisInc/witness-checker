use std::fs;
use std::io;
use std::iter;
use std::path::Path;
use clap::{App, Arg, ArgMatches};
use env_logger;
use num_traits::One;

use cheesecloth::wire_assert;
use cheesecloth::debug;
use cheesecloth::eval::{self, Evaluator, CachingEvaluator};
use cheesecloth::gadget;
use cheesecloth::ir::circuit::{
    Circuit, Arenas, CircuitTrait, CircuitExt, DynCircuit, CircuitFilter, FilterNil, GadgetKindRef,
};
use cheesecloth::ir::typed::{Builder, TWire};
use cheesecloth::lower;
use cheesecloth::micro_ram::context::Context;
use cheesecloth::micro_ram::exec::ExecBuilder;
use cheesecloth::micro_ram::feature::Feature;
use cheesecloth::micro_ram::mem::EquivSegments;
use cheesecloth::micro_ram::types::{VersionedMultiExec, RamState, Segment, TraceChunk, WORD_UNTAINTED};
use cheesecloth::mode::if_mode::{AnyTainted, IfMode, Mode, is_mode, with_mode};
use cheesecloth::mode::tainted;


fn parse_args() -> ArgMatches<'static> {
    App::new("witness-checker")
        .about("generate a witness checker circuit for a given MicroRAM execution trace")
        .arg(Arg::with_name("trace")
             .takes_value(true)
             .value_name("TRACE.CBOR")
             .help("MicroRAM execution trace")
             .required(true))
        .arg(Arg::with_name("zkif-out")
             .long("zkif-out")
             .takes_value(true)
             .value_name("DIR/")
             .help("output zkinterface circuit representation in this directory"))
        .arg(Arg::with_name("sieve-ir-out")
             .long("sieve-ir-out")
             .takes_value(true)
             .value_name("DIR/")
             .help("output SIEVE IR circuit representation in this directory"))
        .arg(Arg::with_name("validate-only")
             .long("validate-only")
             .help("check only that the trace is valid; don't require it to demonstrate a bug"))
        .arg(Arg::with_name("expect-zero")
             .long("expect-zero")
             .help("check that r0 == 0 in the final state"))
        .arg(Arg::with_name("stats")
             .long("stats")
             .help("print info about the size of the circuit"))
        .arg(Arg::with_name("mode")
             .long("mode")
             .takes_value(true)
             .help("Mode to run the checker in. Valid options include:\n    leak-uninitialized - Detect an information leak when uninitialized memory is output.\n    leak-tainted - Detect an information leak when a tainted value is output."))
        .arg(Arg::with_name("check-steps")
             .long("check-steps")
             .takes_value(true)
             .value_name("1")
             .help("check state against the trace every D steps"))
        .arg(Arg::with_name("verifier-mode")
             .long("verifier-mode")
             .help("run in verifier mode, constructing the circuit but not the secret witness"))
        .arg(Arg::with_name("sieve-ir-dedup")
             .long("sieve-ir-dedup")
             .help("in SIEVE IR mode, deduplicate gates produced by the backend"))
        .arg(Arg::with_name("skip-backend-validation")
             .long("skip-backend-validation")
             .help("don't validate the circuit constructed by the backend"))

        // Debug flags
        .arg(Arg::with_name("debug-segment-graph")
             .long("debug-segment-graph")
             .takes_value(true)
             .value_name("OUT.DOT")
             .help("dump the segment graph to a file for debugging"))
        .arg(Arg::with_name("test-gadget-eval")
             .long("test-gadget-eval")
             .help("test GadgetKind::eval behavior for all gadgets in the circuit"))

        .after_help("With no output options, prints the result of evaluating the circuit.")
        .get_matches()
}


fn check_first<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    s: &TWire<'a, RamState>,
) {
    let _g = b.scoped_label("check_first");
    let pc = s.pc;
    wire_assert!(
        cx, b.eq(pc, b.lit(0)),
        "initial pc is {} (expected {})",
        cx.eval(pc), 0,
    );
    for (i, &r) in s.regs.iter().enumerate().skip(1) {
        wire_assert!(
            cx, b.eq(r, b.lit(0)),
            "initial r{} has value {} (expected {})",
            i, cx.eval(r), 0,
        );
    }

    tainted::check_first(cx, b, &s.tainted_regs);
}


fn real_main(args: ArgMatches<'static>) -> io::Result<()> {
    #[cfg(not(feature = "bellman"))]
    if args.is_present("zkif-out") {
        eprintln!("error: zkinterface output is not supported - build with `--features bellman`");
        std::process::exit(1);
    }

    #[cfg(not(feature = "sieve_ir"))]
    if args.is_present("sieve-ir-out") {
        eprintln!("error: sieve_ir output is not supported - build with `--features sieve_ir`");
        std::process::exit(1);
    }

    let is_prover = !args.is_present("verifier-mode");

    let arenas = Arenas::new();

    let arg_test_gadget_eval = args.is_present("test-gadget-eval");
    let arg_zkif_out = args.is_present("zkif-out");
    let arg_sieve_out = args.is_present("sieve-out");
    let gadget_supported = move |g: GadgetKindRef| {
        use cheesecloth::gadget::bit_pack::{ConcatBits, ExtractBits};
        let mut ok = false;
        if arg_test_gadget_eval {
            return true;
        }
        if arg_zkif_out || arg_sieve_out {
            ok = ok || g.cast::<ConcatBits>().is_some();
            ok = ok || g.cast::<ExtractBits>().is_some();
        }
        ok
    };

    let cf = FilterNil;
    //let cf = lower::const_fold::ConstFold(c);
    let cf = cf.add_pass(lower::bool_::not_to_xor);
    let cf = cf.add_pass(lower::bool_::compare_to_logic);
    let cf = cf.add_pass(lower::bool_::mux);
    let cf = cf.add_opt_pass(args.is_present("zkif-out") || args.is_present("sieve-ir-out"),
        lower::int::compare_to_greater_or_equal_to_zero);
    let cf = cf.add_pass(lower::int::non_constant_shift);
    let cf = lower::const_fold::ConstFold(cf);
    let cf = cf.add_pass(lower::bundle::simplify);
    let cf = cf.add_pass(lower::bundle::unbundle_mux);
    let cf = lower::gadget::DecomposeGadgets::new(cf, move |g| !gadget_supported(g));
    let cf = cf.add_pass(lower::bit_pack::concat_bits_flat);
    let c = Circuit::new(&arenas, is_prover, cf);
    let c = &c as &DynCircuit;

    let b = Builder::new(c);
    let mut cx = Context::new(c);

    // Load the program and trace from files
    let trace_path = Path::new(args.value_of_os("trace").unwrap());
    let content = fs::read(trace_path).unwrap();
    let parse_exec: VersionedMultiExec = match trace_path.extension().and_then(|os| os.to_str()) {
        Some("yaml") => serde_yaml::from_slice(&content).unwrap(),
        Some("cbor") => serde_cbor::from_slice(&content).unwrap(),
        Some("json") => serde_json::from_slice(&content).unwrap(),
        _ => serde_cbor::from_slice(&content).unwrap(),
    };
    parse_exec.validate().unwrap();
    let mut multi_exec = parse_exec;
    // Check that --mode leak-tainted is provided iff the feature is present.
    assert!(is_mode::<AnyTainted>() == multi_exec.has_feature(Feature::LeakTainted), "--mode leak-tainted must only be provided when the feature is set in the input file.");

    // Adjust non-public-pc traces to fit the public-pc format.
    // In non-public-PC mode, the prover can provide an initial state, with some restrictions.
    let mut provided_init_state = None;
    if !multi_exec.has_feature(Feature::PublicPc) {
        for (_name,exec) in multi_exec.inner.execs.iter_mut(){
            assert!(exec.segments.len() == 0);
            assert!(exec.trace.len() == 1);
            let chunk = &exec.trace[0];
            
            let new_segment = Segment {
                constraints: vec![],
                len: exec.params.trace_len.unwrap() - 1,
                successors: vec![],
                enter_from_network: false,
                exit_to_network: false,
            };
            
            provided_init_state = Some(chunk.states[0].clone());
            let new_chunk = TraceChunk {
                segment: 0,
                states: chunk.states[1..].to_owned(),
                debug: None,
            };
            
            exec.segments = vec![new_segment];
            exec.trace = vec![new_chunk];
            
        }
    }

    let mut equiv_segments = EquivSegments::new(&multi_exec.inner.mem_equiv);

    // Build Circuit for each execution,
    // using the memequivalences to use the same wire
    // for equivalent mem segments. 
    for (name,exec) in multi_exec.inner.execs.iter(){
        // Generate IR code to check the trace.
        let init_state = provided_init_state.clone().unwrap_or_else(|| {
            let mut regs = vec![0; exec.params.num_regs];
            regs[0] = exec.init_mem.iter()
                .filter(|ms| ms.heap_init == false)
                .map(|ms| ms.start + ms.len)
                .max().unwrap_or(0);
            let tainted_regs = IfMode::new(|_| vec![WORD_UNTAINTED; exec.params.num_regs]);
            RamState { cycle: 0, pc: 0, regs, live: true, tainted_regs }
        });
        if provided_init_state.is_some() {
            let init_state_wire = b.lit(init_state.clone());
            check_first(&cx, &b, &init_state_wire);
        }

        let check_steps = args.value_of("check-steps")
            .and_then(|c| c.parse::<usize>().ok()).unwrap_or(0);

        let expect_zero = args.is_present("expect-zero");
        let debug_segment_graph_path = args.value_of("debug-segment-graph")
            .map(|s| s.to_owned());

        let (new_cx, new_equiv_segments) = ExecBuilder::build(
            &b, cx, &exec, name, equiv_segments, init_state,
            check_steps, expect_zero, debug_segment_graph_path);
        cx = new_cx;
        equiv_segments = new_equiv_segments;
    }
        
    // Collect assertions and bugs.
    drop(b);
    let (asserts, bugs) = cx.finish();
    let asserts = asserts.into_iter().map(|tw| tw.repr).collect::<Vec<_>>();
    let bugs = bugs.into_iter().map(|tw| tw.repr).collect::<Vec<_>>();

    // The statement is accepted if all assertions hold.
    let accepted = if args.is_present("validate-only") {
        c.all_true(asserts.iter().cloned())
    } else {
        c.and(
            c.all_true(asserts.iter().cloned()),
            c.any_true(bugs.iter().cloned()),
        )
    };

    // Concatenate accepted, asserts, bugs.
    let num_asserts = asserts.len();
    let flags =
        iter::once(accepted)
        .chain(asserts.into_iter())
        .chain(bugs.into_iter())
        .collect::<Vec<_>>();

    if args.is_present("stats") {
        eprintln!(" ===== stats: after lowering =====");
        debug::count_gates::count_gates(&flags);
        eprintln!(" ===== end stats (after lowering) =====");
    }

    {
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(c);
        let flag_vals = flags.iter().map(|&w| {
            ev.eval_wire(w).ok().as_ref().and_then(|v| v.as_single()).unwrap().is_one()
        }).collect::<Vec<_>>();

        let asserts_ok: u32 = flag_vals[1 .. 1 + num_asserts].iter().map(|&ok| ok as u32).sum();
        let bugs_ok: u32 = flag_vals[1 + num_asserts ..].iter().map(|&ok| ok as u32).sum();

        eprintln!(
            "internal evaluator: {} asserts passed, {} failed; found {} bugs; overall status: {}",
            asserts_ok, num_asserts as u32 - asserts_ok, bugs_ok,
            if flag_vals[0] { "GOOD" } else { "BAD" },
        );
    }

    if args.is_present("test-gadget-eval") {
        let count = gadget::test_gadget_eval(c.as_base(), [accepted].iter().cloned());
        eprintln!("all {} gadgets passed", count);
        return Ok(());
    }

    #[cfg(feature = "bellman")]
    if let Some(dest) = args.value_of_os("zkif-out") {
        use cheesecloth::back::zkif::backend::Backend;
        use zkinterface::{cli::{cli, Options}, clean_workspace};

        let accepted = flags[0];

        // Clean workspace.
        let workspace = Path::new(dest);
        clean_workspace(workspace).unwrap();

        // Generate the circuit and witness.
        let mut backend = Backend::new(workspace, true);

        backend.enforce_true(accepted);

        // Write files.
        backend.finish().unwrap();

        eprintln!("validating zkif...");

        if !args.is_present("skip-backend-validation") {
            // Validate the circuit and witness.
            cli(&Options {
                tool: "simulate".to_string(),
                paths: vec![workspace.to_path_buf()],
                field_order: Default::default(),
            }).unwrap();
        }

        // Print statistics.
        cli(&Options {
            tool: "stats".to_string(),
            paths: vec![workspace.to_path_buf()],
            field_order: Default::default(),
        }).unwrap();
    }

    #[cfg(feature = "sieve_ir")]
    if let Some(workspace) = args.value_of("sieve-ir-out") {
        use cheesecloth::back::sieve_ir::{
            backend::{Backend, Scalar},
            ir_builder::IRBuilder,
        };
        use zki_sieve::{
            cli::{cli, Options, StructOpt},
            FilesSink,
        };

        { // restrict ir_builder to its own scope
            // Generate the circuit and witness.
            let sink = FilesSink::new_clean(&workspace).unwrap();
            sink.print_filenames();
            let mut ir_builder = IRBuilder::new::<Scalar>(sink);
            // ir_builder.enable_profiler();
            if !args.is_present("sieve-ir-dedup") {
                ir_builder.disable_dedup();
            }

            { // restrict backend to its own scope to save memory
                let mut backend = Backend::new(&mut ir_builder);

                let accepted = flags[0];
                backend.enforce_true(accepted);
                backend.finish();
            }
            eprintln!();
            ir_builder.prof.as_ref().map(|p| p.print_report());
            ir_builder.dedup.as_ref().map(|p| p.print_report());
            ir_builder.finish();
        }

        // Validate the circuit and witness.
        eprintln!("\nValidating SIEVE IR files...");
        if !args.is_present("skip-backend-validation") {
            cli(&Options::from_iter(&["zki_sieve", "validate", workspace])).unwrap();
            cli(&Options::from_iter(&["zki_sieve", "evaluate", workspace])).unwrap();
        }
        cli(&Options::from_iter(&["zki_sieve", "metrics", workspace])).unwrap();
    }

    // Unused in some configurations.
    let _ = num_asserts;

    Ok(())
}

fn main() -> io::Result<()> {
    env_logger::init();
    let args = parse_args();

    let mode = match args.value_of("mode") {
        Some("leak-uninitialized") => Mode::LeakUninit1,
        Some("leak-tainted") => Mode::LeakTainted,
        None => Mode::MemorySafety,
        Some(m) => {
            eprintln!("error: unknown mode `{}`", m);
            std::process::exit(1);
        },
    };

    unsafe { with_mode(mode, || real_main(args)) }
}

