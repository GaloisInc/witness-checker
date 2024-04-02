use std::fs;
use std::io;
use std::iter;
use std::num::ParseIntError;
use std::path::Path;
use std::ptr;
use std::str::FromStr;
use clap::{App, Arg, ArgMatches};
use env_logger;
use num_bigint::BigUint;
use num_traits::One;

use zk_circuit_builder::back::{self, UsePlugins, BackendFeature};
use zk_circuit_builder::eval::{self, EvalWire, CachingEvaluator};
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
use cheesecloth::micro_ram::types::{
    VersionedMultiExec, MultiExec, RamState, Segment, TraceChunk, WORD_BOTTOM,
};
use cheesecloth::micro_ram::witness::MultiExecWitness;
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
             .help("output arithmetic zkinterface (R1CS) circuit representation in this directory"))
        .arg(Arg::with_name("sieve-ir-out")
             .long("sieve-ir-out")
             .takes_value(true)
             .value_name("DIR/")
             .help("output arithmetic SIEVE IR circuit representation in this directory"))
        .arg(Arg::with_name("sieve-ir-v2-out")
             .long("sieve-ir-v2-out")
             .takes_value(true)
             .value_name("DIR/")
             .help("output arithmetic SIEVE IR v2 (IR0+) circuit representation in this directory"))
        .arg(Arg::with_name("sieve-ir-v3-out")
             .long("sieve-ir-v3-out")
             .takes_value(true)
             .value_name("DIR/")
             .help("output arithmetic SIEVE IR v3 (Phase 3 Circuit IR) circuit representation in this directory"))
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
        .arg(Arg::with_name("boolean-sieve-ir-v3-out")
             .long("boolean-sieve-ir-v3-out")
             .takes_value(true)
             .value_name("DIR/")
             .help("output boolean SIEVE IR v3 (Phaes 3 Circuit IR) circuit representation in this directory"))
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
             .help("check that r0 == 0 in the final state \
                (WARNING: this leaks information about the trace!)"))
        .arg(Arg::with_name("expect-write")
             .long("expect-write")
             .takes_value(true)
             .value_name("ADDR")
             .help("check that the program writes the value 1 to ADDR before terminating"))
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
             .help("check state against the trace every D steps \
                (WARNING: this leaks information about the trace!)"))
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
             .help(&format!("enable only the listed IR0+ plugins (default: enable all plugins)\navailable plugins: {}", UsePlugins::list_plugins())))
        .arg(Arg::with_name("no-functions")
             .long("no-functions")
             .help("Do not generate functions in the output circuit"))

        // Special flag for T&E, used by generate_statements.py
        .arg(Arg::with_name("test-expand-trace")
             .long("test-expand-trace")
             .takes_value(true)
             .value_name("FACTOR")
             .help("add extra segments to multiply the max trace length by FACTOR"))

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

fn expand_trace(multi_exec: &mut MultiExec, factor: usize) {
    eprintln!("expanding trace by a factor of {}", factor);
    if factor <= 1 {
        return;
    }

    for exec in multi_exec.execs.values_mut() {
        let orig_len = exec.segments.len();
        exec.segments.reserve((factor - 1) * orig_len);
        for mut seg in exec.segments.clone() {
            for _ in 1 .. factor {
                for succ in &mut seg.successors {
                    *succ += orig_len;
                }
                exec.segments.push(seg.clone());
            }
        }

        // Add a dummy edge from segment 0 to each copy of segment 0 so that they aren't dropped
        // for being unreachable in the segment graph.
        for i in 1 .. factor {
            exec.segments[0].successors.push(i * orig_len);
        }

        assert_eq!(exec.segments.len(), orig_len * factor);
        eprintln!("expanded execution: {} -> {}", orig_len, orig_len * factor);
    }
}

fn parse_address(s: &str) -> Result<u64, ParseIntError> {
    if s.starts_with("0x") {
        u64::from_str_radix(&s[2..], 16)
    } else if s.starts_with("0o") {
        u64::from_str_radix(&s[2..], 8)
    } else if s.starts_with("0b") {
        u64::from_str_radix(&s[2..], 2)
    } else {
        u64::from_str_radix(s, 10)
    }
}

fn real_main(args: ArgMatches<'static>) -> io::Result<()> {
    let is_prover = !args.is_present("verifier-mode");


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

    if let Some(factor_str) = args.value_of("test-expand-trace") {
        let factor = factor_str.parse::<usize>().unwrap_or_else(|e| {
            panic!("bad --test-expand-trace argument {:?}: {}", factor_str, e);
        });
        expand_trace(&mut multi_exec.inner, factor);
    }

    let multi_exec_witness = MultiExecWitness::from_raw(&multi_exec.inner);

    let mut equiv_segments = EquivSegments::new(&multi_exec.inner.mem_equiv);

    // `arenas` and `mcx` must outlive both the circuit and the backend.
    let arenas = Arenas::new();
    let mcx = zk_circuit_builder::ir::migrate::handle::MigrateContext::new(&multi_exec_witness);

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
        } else if let Some(workspace) = args.value_of("sieve-ir-v3-out") {
            let dedup = args.is_present("sieve-ir-dedup");
            back::new_sieve_ir_v3(workspace, modulus, dedup)
        } else if let Some(workspace) = args.value_of("boolean-sieve-ir-out") {
            assert!(modulus.is_none(),
                "--field-modulus is not supported with --boolean-sieve-ir-out");
            back::new_boolean_sieve_ir(workspace)
        } else if let Some(workspace) = args.value_of("boolean-sieve-ir-v2-out") {
            assert!(modulus.is_none(),
                "--field-modulus is not supported with --boolean-sieve-ir-v2-out");
            back::new_boolean_sieve_ir_v2(workspace, use_plugins)
        } else if let Some(workspace) = args.value_of("boolean-sieve-ir-v3-out") {
            assert!(modulus.is_none(),
                "--field-modulus is not supported with --boolean-sieve-ir-v3-out");
            back::new_boolean_sieve_ir_v3(workspace, use_plugins)
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

    // Set up the circuit and builder
    let arg_test_gadget_eval = args.is_present("test-gadget-eval");

    let has_concat_extract_bits = backend.has_feature(BackendFeature::ConcatExtractBits);
    let has_wide_mul = backend.has_feature(BackendFeature::WideMul);
    let has_permute = backend.has_feature(BackendFeature::Permute);
    let gadget_supported = move |g: GadgetKindRef| {
        use zk_circuit_builder::gadget::arith::WideMul;
        use zk_circuit_builder::gadget::bit_pack::{ConcatBits, ExtractBits};
        use zk_circuit_builder::routing::gadget::Permute;
        let mut ok = false;
        if arg_test_gadget_eval {
            return true;
        }
        if has_concat_extract_bits {
            ok = ok || g.cast::<ConcatBits>().is_some();
            ok = ok || g.cast::<ExtractBits>().is_some();
        }
        if has_wide_mul {
            ok = ok || g.cast::<WideMul>().is_some();
        }
        if has_permute {
            ok = ok || g.cast::<Permute>().is_some();
        }
        ok
    };

    let cf = FilterNil;
    let cf = cf.add_pass(|c, gk| lower::bool_::not_to_xor(c, gk));
    let cf = cf.add_pass(|c, gk| lower::bool_::compare_to_logic(c, gk));
    let cf = cf.add_pass(|c, gk| lower::bool_::mux(c, gk));
    let cf = cf.add_opt_pass(
        !backend.has_feature(BackendFeature::CompareNonZero),
        |c, gk| lower::int::compare_to_greater_or_equal_to_zero(c, gk));
    let cf = cf.add_pass(|c, gk| lower::int::non_constant_shift(c, gk));
    let cf = lower::const_fold::ConstFold(cf);
    let cf = cf.add_pass(|c, gk| lower::bundle::simplify(c, gk));
    let cf = cf.add_pass(|c, gk| lower::bundle::unbundle_mux(c, gk));
    let cf = lower::gadget::DecomposeGadgets::new(cf, move |g| !gadget_supported(g));
    let cf = cf.add_pass(|c, gk| lower::bit_pack::concat_bits_flat(c, gk));
    let use_functions = !args.is_present("no-functions") && backend.has_feature(BackendFeature::Function);
    let c = Circuit::new::<MultiExecWitness>(&arenas, is_prover, cf)
        .set_allow_functions(use_functions)
        .set_allow_switches(backend.has_feature(BackendFeature::Switch));
    let c = &c;

    let b = BuilderImpl::from_ref(c);
    let mut cx = Context::new(c);

    let mcx_backend_guard = mcx.set_backend(&mut *backend);


    // Hack: cast away the lifetime of the `MultiExec`, pretending it's `'static`.   We do this to
    // allow lazy secret callbacks to include `&'static str` names for executions.  This is okay as
    // long as the value outlives the circuit, which we ensure below.
    let multi_exec: &'static _ = unsafe { &*ptr::addr_of!(multi_exec) };

    // Build Circuit for each execution,
    // using the memequivalences to use the same wire
    // for equivalent mem segments. 
    for (name,exec) in multi_exec.inner.execs.iter(){
        // Generate IR code to check the trace.
        let init_state = exec.provided_init_state.clone().unwrap_or_else(|| exec.initial_state());
        if exec.provided_init_state.is_some() {
            let init_state_wire = b.lit(init_state.clone());
            check_first(&cx, b, &init_state_wire);
        }

        let check_steps = args.value_of("check-steps")
            .and_then(|c| c.parse::<usize>().ok()).unwrap_or(0);

        let expect_zero = args.is_present("expect-zero");
        let expect_write = args.value_of("expect-write").map(|s| {
            parse_address(s).expect("failed to parse --expect-write address")
        });
        let debug_segment_graph_path = args.value_of("debug-segment-graph")
            .map(|s| s.to_owned());

        // Get a `&'static str` version of `name` from the witness.
        let (new_cx, new_equiv_segments) = ExecBuilder::build(
            b, &mcx, cx, &exec, name, equiv_segments, init_state,
            check_steps, expect_zero, expect_write, debug_segment_graph_path);
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

    let mut ev = CachingEvaluator::<eval::RevealSecrets>::with_witness(&multi_exec_witness);
    {
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
    backend.finish(c.as_base(), &mut ev, accepted, validate);

    // Unused in some configurations.
    let _ = num_asserts;

    // Ensure `multi_exec` is still valid.
    let _ = &*multi_exec;

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

