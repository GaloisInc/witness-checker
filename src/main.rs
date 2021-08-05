use std::collections::HashMap;
use std::fs;
use std::io;
use std::iter;
use std::mem::{self, MaybeUninit};
use std::path::Path;
use std::ptr;
use bumpalo::Bump;
use clap::{App, Arg, ArgMatches};
use num_traits::One;

use cheesecloth::wire_assert;
use cheesecloth::debug;
use cheesecloth::eval::{self, Evaluator, CachingEvaluator};
use cheesecloth::ir::circuit::{Circuit, Wire, GateKind, GadgetKindRef};
use cheesecloth::ir::typed::{Builder, TWire};
use cheesecloth::lower::{self, run_pass, run_pass_debug};
use cheesecloth::micro_ram::context::Context;
use cheesecloth::micro_ram::feature::Feature;
use cheesecloth::micro_ram::fetch::Fetch;
use cheesecloth::micro_ram::mem::Memory;
use cheesecloth::micro_ram::parse::ParseExecution;
use cheesecloth::micro_ram::seg_graph::{SegGraphBuilder, SegGraphItem};
use cheesecloth::micro_ram::trace::SegmentBuilder;
use cheesecloth::micro_ram::types::{RamState, Segment, TraceChunk};


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
}

fn check_last<'a>(
    cx: &Context<'a>,
    b: &Builder<'a>,
    s: &TWire<'a, RamState>,
    expect_zero: bool,
) {
    let _g = b.scoped_label("check_last");
    let r0 = s.regs[0];
    if expect_zero {
        wire_assert!(
            cx, b.eq(r0, b.lit(0)),
            "final r0 is {} (expected {})",
            cx.eval(r0), 0,
        );
    }
}


struct PassRunner<'a> {
    // Wrap everything in `MaybeUninit` to prevent the compiler from realizing that we have
    // overlapping `&` and `&mut` references.
    cur: MaybeUninit<&'a mut Bump>,
    next: MaybeUninit<&'a mut Bump>,
    /// Invariant: the underlying `Gate` of every wire in `wires` is allocated from the `cur`
    /// arena.
    wires: MaybeUninit<Vec<Wire<'a>>>,
    is_prover: bool,
}

const DEBUG_PASSES: bool = false;

impl<'a> PassRunner<'a> {
    pub fn new(
        a: &'a mut Bump,
        b: &'a mut Bump,
        wires: Vec<Wire>,
        is_prover: bool,
    ) -> PassRunner<'a> {
        a.reset();
        b.reset();
        let cur = MaybeUninit::new(a);
        let next = MaybeUninit::new(b);
        let wires = unsafe {
            // Transfer all wires into the `cur` arena.
            let arena: &Bump = &**cur.as_ptr();
            let c = Circuit::new(arena, is_prover);
            let wires = run_pass(&c, wires, |c, _old, gk| c.gate(gk));
            MaybeUninit::new(wires)
        };

        PassRunner { cur, next, wires, is_prover }
    }

    // FIXME: using `'a` instead of a fresh lifetime (`for <'b>`) potentially allows the closure to
    // stash a `GateKind` or `Wire` somewhere and use it after the arena has been `reset`.
    // However, this also makes it hard to apply stateful transformation passes (`const_fold`).
    pub fn run(&mut self, f: impl FnMut(&Circuit<'a>, Wire, GateKind<'a>) -> Wire<'a>) {
        unsafe {
            {
                let arena: &Bump = &**self.next.as_ptr();
                let c = Circuit::new(arena, self.is_prover);
                let wires = mem::replace(&mut *self.wires.as_mut_ptr(), Vec::new());
                let wires = if DEBUG_PASSES {
                    run_pass_debug(&c, wires, f)
                } else {
                    run_pass(&c, wires, f)
                };
                *self.wires.as_mut_ptr() = wires;
            }
            // All `wires` are now allocated from `self.next`, leaving `self.cur` unused.
            (*self.cur.as_mut_ptr()).reset();
            ptr::swap(self.cur.as_mut_ptr(), self.next.as_mut_ptr());
        }
    }

    pub fn finish(self) -> (Circuit<'a>, Vec<Wire<'a>>) {
        unsafe {
            let arena: &Bump = &**self.cur.as_ptr();
            let c = Circuit::new(arena, self.is_prover);
            let wires = ptr::read(self.wires.as_ptr());
            (c, wires)
        }
    }
}

fn main() -> io::Result<()> {
    let args = parse_args();

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

    let arena = Bump::new();
    let c = Circuit::new(&arena, is_prover);
    let b = Builder::new(&c);
    let cx = Context::new(&c);

    // Load the program and trace from files
    let trace_path = Path::new(args.value_of_os("trace").unwrap());
    let content = fs::read(trace_path).unwrap();
    let parse_exec: ParseExecution = match trace_path.extension().and_then(|os| os.to_str()) {
        Some("yaml") => serde_yaml::from_slice(&content).unwrap(),
        Some("cbor") => serde_cbor::from_slice(&content).unwrap(),
        Some("json") => serde_json::from_slice(&content).unwrap(),
        _ => serde_cbor::from_slice(&content).unwrap(),
    };
    let mut exec = parse_exec.into_inner().validate().unwrap();

    // Adjust non-public-pc traces to fit the public-pc format.
    // In non-public-PC mode, the prover can provide an initial state, with some restrictions.
    let mut provided_init_state = None;
    if !exec.has_feature(Feature::PublicPc) {
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


    // Set up memory ports and check consistency.
    let mut mem = Memory::new();
    for seg in &exec.init_mem {
        mem.init_segment(&b, seg);
    }

    // Set up instruction-fetch ports and check consistency.
    let mut fetch = Fetch::new(&b, &exec.program);

    // Generate IR code to check the trace.
    let check_steps = args.value_of("check-steps")
        .and_then(|c| c.parse::<usize>().ok()).unwrap_or(0);
    let mut segments_map = HashMap::new();
    let mut segment_builder = SegmentBuilder {
        cx: &cx,
        b: &b,
        mem: &mut mem,
        fetch: &mut fetch,
        params: &exec.params,
        prog: &exec.program,
        check_steps,
    };

    let init_state = provided_init_state.clone().unwrap_or_else(|| {
        let mut regs = vec![0; exec.params.num_regs];
        regs[0] = exec.init_mem.iter().filter(|ms| ms.heap_init == false).map(|ms| ms.start + ms.len).max().unwrap_or(0);
        RamState { cycle: 0, pc: 0, regs, live: true }
    });
    if provided_init_state.is_some() {
        let init_state_wire = b.lit(init_state.clone());
        check_first(&cx, &b, &init_state_wire);
    }

    let mut seg_graph_builder = SegGraphBuilder::new(
        &b, &exec.segments, &exec.params, init_state.clone());

    for item in seg_graph_builder.get_order() {
        let idx = match item {
            SegGraphItem::Segment(idx) => idx,
            SegGraphItem::Network => {
                seg_graph_builder.build_network(&b);
                continue;
            },
        };

        let seg_def = &exec.segments[idx];
        let prev_state = seg_graph_builder.get_initial(&b, idx).clone();
        let seg = segment_builder.run(idx, seg_def, prev_state);
        seg_graph_builder.set_final(idx, seg.final_state().clone());
        assert!(!segments_map.contains_key(&idx));
        segments_map.insert(idx, seg);
    }

    let mut seg_graph = seg_graph_builder.finish(&cx, &b);

    let mut segments = (0 .. exec.segments.len()).map(|i| {
        segments_map.remove(&i)
            .unwrap_or_else(|| panic!("seg_graph omitted segment {}", i))
    }).collect::<Vec<_>>();
    drop(segments_map);

    check_last(&cx, &b, segments.last().unwrap().final_state(), args.is_present("expect-zero"));

    // Fill in advice and other secrets.
    let mut cycle = 0;
    let mut prev_state = init_state.clone();
    let mut prev_segment = None;
    for chunk in &exec.trace {
        if let Some(ref debug) = chunk.debug {
            if let Some(c) = debug.cycle {
                cycle = c;
            }
            if let Some(ref s) = debug.prev_state {
                prev_state = s.clone();
            }
            if debug.clear_prev_segment {
                prev_segment = None;
            }
            if let Some(idx) = debug.prev_segment {
                prev_segment = Some(idx);
            }
        }

        let seg = &mut segments[chunk.segment];
        assert_eq!(seg.idx, chunk.segment);
        seg.set_states(&b, &exec.program, cycle, &prev_state, &chunk.states, &exec.advice);
        seg.check_states(&cx, &b, cycle, check_steps, &chunk.states);

        if let Some(prev_segment) = prev_segment {
            seg_graph.make_edge_live(&b, prev_segment, chunk.segment, &prev_state);
        }
        prev_segment = Some(chunk.segment);

        cycle += chunk.states.len() as u32;
        if chunk.states.len() > 0 {
            prev_state = chunk.states.last().unwrap().clone();
            prev_state.cycle = cycle;
        }
    }

    seg_graph.finish(&b);

    // Explicitly drop anything that contains a `SecretHandle`, ensuring that defaults are set
    // before we move on.
    drop(segments);

    // Some consistency checks involve sorting, which requires that all the relevant secrets be
    // initialized first.
    mem.assert_consistent(&cx, &b);
    fetch.assert_consistent(&cx, &b);

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
        eprintln!(" ===== stats: before lowering =====");
        debug::count_gates::count_gates(&flags);
        eprintln!(" ===== end stats (before lowering) =====");
    }

    let mut arena1 = Bump::new();
    let mut arena2 = Bump::new();
    let mut passes = PassRunner::new(&mut arena1, &mut arena2, flags, is_prover);

    let gadget_supported = |g: GadgetKindRef| {
        use cheesecloth::gadget::bit_pack::{ConcatBits, ExtractBits};
        let mut ok = false;
        if args.is_present("zkif-out") || args.is_present("sieve-ir-out") {
            ok = ok || g.cast::<ConcatBits>().is_some();
            ok = ok || g.cast::<ExtractBits>().is_some();
        }
        if args.is_present("scale-out") {
        }
        ok
    };

    passes.run(lower::bit_pack::concat_bits_flat);
    // TODO: need a better way to handle passes that must be run to fixpoint
    passes.run(lower::gadget::decompose_gadgets(|g| !gadget_supported(g)));
    passes.run(lower::gadget::decompose_gadgets(|g| !gadget_supported(g)));
    passes.run(lower::bundle::unbundle_mux);
    passes.run(lower::bundle::simplify);
    passes.run(lower::const_fold::const_fold(&c));
    passes.run(lower::int::non_constant_shift);
    if args.is_present("zkif-out") || args.is_present("sieve-ir-out") {
        passes.run(lower::int::compare_to_greater_or_equal_to_zero);
    }
    passes.run(lower::bool_::mux);
    passes.run(lower::bool_::compare_to_logic);
    passes.run(lower::bool_::not_to_xor);
    let (c, flags) = passes.finish();

    if args.is_present("stats") {
        eprintln!(" ===== stats: after lowering =====");
        debug::count_gates::count_gates(&flags);
        eprintln!(" ===== end stats (after lowering) =====");
    }

    {
        let mut ev = CachingEvaluator::<eval::RevealSecrets>::new(&c);
        let flag_vals = flags.iter().map(|&w| {
            ev.eval_wire(w).as_ref().and_then(|v| v.as_single()).unwrap().is_one()
        }).collect::<Vec<_>>();

        let asserts_ok: u32 = flag_vals[1 .. 1 + num_asserts].iter().map(|&ok| ok as u32).sum();
        let bugs_ok: u32 = flag_vals[1 + num_asserts ..].iter().map(|&ok| ok as u32).sum();

        eprintln!(
            "internal evaluator: {} asserts passed, {} failed; found {} bugs; overall status: {}",
            asserts_ok, num_asserts as u32 - asserts_ok, bugs_ok,
            if flag_vals[0] { "GOOD" } else { "BAD" },
        );
    }

    #[cfg(feature = "bellman")]
    if let Some(dest) = args.value_of_os("zkif-out") {
        use cheesecloth::back::zkif::backend::{Backend, Scalar};
        use std::fs::remove_file;
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

        // Validate the circuit and witness.
        cli(&Options {
            tool: "simulate".to_string(),
            paths: vec![workspace.to_path_buf()],
            field_order: Default::default(),
        }).unwrap();

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
        cli(&Options::from_iter(&["zki_sieve", "validate", workspace])).unwrap();
        cli(&Options::from_iter(&["zki_sieve", "evaluate", workspace])).unwrap();
        cli(&Options::from_iter(&["zki_sieve", "metrics", workspace])).unwrap();
    }

    // Unused in some configurations.
    let _ = num_asserts;

    Ok(())
}
