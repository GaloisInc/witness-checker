use std::fs;
use std::io;
use std::iter;
use std::path::Path;
use std::str::FromStr;
use clap::{App, Arg, ArgMatches};
use env_logger;
use num_bigint::BigUint;
use num_traits::One;

use zk_circuit_builder::back::{self, UsePlugins};
use zk_circuit_builder::eval::{self, Evaluator, CachingEvaluator};
use zk_circuit_builder::gadget;
use zk_circuit_builder::ir::circuit::{
    Circuit, Arenas, CircuitTrait, CircuitExt, CircuitFilter, FilterNil, GadgetKindRef,
};
use zk_circuit_builder::ir::typed::{Builder, BuilderExt, BuilderImpl, TWire};
use zk_circuit_builder::lower;

use cheesecloth::wire_assert;
use cheesecloth::micro_ram::context::Context;
use cheesecloth::micro_ram::exec::ExecBuilder;
use cheesecloth::micro_ram::feature::Feature;
use cheesecloth::micro_ram::mem::EquivSegments;
use cheesecloth::micro_ram::types::{VersionedMultiExec, RamState, Segment, TraceChunk, WORD_BOTTOM};
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
        .arg(Arg::with_name("sieve-ir-v2-out")
             .long("sieve-ir-v2-out")
             .takes_value(true)
             .value_name("DIR/")
             .help("output SIEVE IR v2 (IR0+) circuit representation in this directory"))
        .arg(Arg::with_name("boolean-sieve-ir-out")
             .long("boolean-sieve-ir-out")
             .takes_value(true)
             .value_name("DIR/")
             .help("output boolean SIEVE IR v1 (IR1) circuit representation in this directory"))
        .arg(Arg::with_name("boolean-sieve-ir-v2-out")
             .long("boolean-sieve-ir-v2-out")
             .takes_value(true)
             .value_name("DIR/")
             .help("output boolean SIEVE IR v2 (IR0+) circuit representation in this directory"))
        .arg(Arg::with_name("field-modulus")
             .long("field-modulus")
             .takes_value(true)
             .value_name("P")
             .help("generate a circuit in the field modulo P"))
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
        .arg(Arg::with_name("available-plugins")
             .long("available-plugins")
             .takes_value(true)
             .value_name("NAMES")
             .help("enable only the listed IR0+ plugins (default: enable all plugins)"))

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
    b: &impl Builder<'a>,
    s: &TWire<'a, RamState>,
) {
    let _g = b.scoped_label("check_first");
    let pc = s.pc;
    wire_assert!(
        cx, b, b.eq(pc, b.lit(0)),
        "initial pc is {} (expected {})",
        cx.eval(pc), 0,
    );
    for (i, &r) in s.regs.iter().enumerate().skip(1) {
        wire_assert!(
            cx, b, b.eq(r, b.lit(0)),
            "initial r{} has value {} (expected {})",
            i, cx.eval(r), 0,
        );
    }

    tainted::check_first(cx, b, &s.tainted_regs);
}


fn real_main(args: ArgMatches<'static>) -> io::Result<()> {
    let is_prover = !args.is_present("verifier-mode");

    let arenas = Arenas::new();
    let mcx = zk_circuit_builder::ir::migrate::handle::MigrateContext::new();

    let arg_test_gadget_eval = args.is_present("test-gadget-eval");
    let arg_zkif_out = args.is_present("zkif-out");
    let arg_sieve_out = args.is_present("sieve-out");
    let gadget_supported = move |g: GadgetKindRef| {
        use zk_circuit_builder::gadget::bit_pack::{ConcatBits, ExtractBits};
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
    let cf = cf.add_opt_pass(
        args.is_present("zkif-out") ||
            args.is_present("sieve-ir-out") ||
            args.is_present("sieve-ir-v2-out") ||
            args.is_present("boolean-sieve-ir-out") ||
            args.is_present("boolean-sieve-ir-v2-out"),
        lower::int::compare_to_greater_or_equal_to_zero);
    let cf = cf.add_pass(lower::int::non_constant_shift);
    let cf = lower::const_fold::ConstFold(cf);
    let cf = cf.add_pass(lower::bundle::simplify);
    let cf = cf.add_pass(lower::bundle::unbundle_mux);
    let cf = lower::gadget::DecomposeGadgets::new(cf, move |g| !gadget_supported(g));
    let cf = cf.add_pass(lower::bit_pack::concat_bits_flat);
    let c = Circuit::new::<()>(&arenas, is_prover, cf);
    let c = &c;

    let b = BuilderImpl::from_ref(c);
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

    // Set up the backend.
    let modulus = args.value_of("field-modulus").map(|s| {
        BigUint::from_str(s).unwrap_or_else(|e| {
            panic!("invalid --field-modulus {:?}: {}", s, e);
        })
    });
    let use_plugins = args.value_of("available-plugins")
        .map(UsePlugins::from_str)
        .unwrap_or_else(UsePlugins::all);
    let mut backend =
        if let Some(workspace) = args.value_of("sieve-ir-out") {
            assert!(modulus.is_none(),
                "--field-modulus is not supported with --sieve-ir-out");
            let dedup = args.is_present("sieve-ir-dedup");
            back::new_sieve_ir(workspace, dedup)
        } else if let Some(workspace) = args.value_of("sieve-ir-v2-out") {
            let dedup = args.is_present("sieve-ir-dedup");
            back::new_sieve_ir_v2(workspace, modulus, dedup)
        } else if let Some(workspace) = args.value_of("boolean-sieve-ir-out") {
            assert!(modulus.is_none(),
                "--field-modulus is not supported with --boolean-sieve-ir-out");
            back::new_boolean_sieve_ir(workspace)
        } else if let Some(workspace) = args.value_of("boolean-sieve-ir-v2-out") {
            assert!(modulus.is_none(),
                "--field-modulus is not supported with --boolean-sieve-ir-v2-out");
            back::new_boolean_sieve_ir_v2(workspace, use_plugins)
        } else if let Some(dest) = args.value_of_os("zkif-out") {
            assert!(modulus.is_none(), "--field-modulus is not supported with --zkif-out");
            back::new_zkif(dest)
        } else if args.is_present("stats") {
            // --field-modulus is accepted but ignored here.
            back::new_stats()
        } else {
            // --field-modulus is accepted but ignored here.
            back::new_dummy()
        };
    let mcx_backend_guard = mcx.set_backend(&mut *backend);


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
            let tainted_regs = IfMode::new(|_| vec![WORD_BOTTOM; exec.params.num_regs]);
            RamState { cycle: 0, pc: 0, regs, live: true, tainted_regs }
        });
        if provided_init_state.is_some() {
            let init_state_wire = b.lit(init_state.clone());
            check_first(&cx, b, &init_state_wire);
        }

        let check_steps = args.value_of("check-steps")
            .and_then(|c| c.parse::<usize>().ok()).unwrap_or(0);

        let expect_zero = args.is_present("expect-zero");
        let debug_segment_graph_path = args.value_of("debug-segment-graph")
            .map(|s| s.to_owned());

        let (new_cx, new_equiv_segments) = ExecBuilder::build(
            b, &mcx, cx, &exec, name, equiv_segments, init_state,
            check_steps, expect_zero, debug_segment_graph_path);
        cx = new_cx;
        equiv_segments = new_equiv_segments;
    }

    // Collect assertions and bugs.
    drop(b);
    let (asserts, bugs) = cx.finish(c);
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

    {
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new();
        let flag_vals = flags.iter().map(|&w| {
            ev.eval_wire(c, w).ok().as_ref().and_then(|v| v.as_single()).unwrap().is_one()
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

    drop(mcx_backend_guard);
    let accepted = flags[0];
    let validate = !args.is_present("skip-backend-validation");
    let mut ev = CachingEvaluator::new();
    backend.finish(c.as_base(), &mut ev, accepted, validate);

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

