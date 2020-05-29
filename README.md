# Cheesecloth witness checker prototype

This tool generates a witness/trace checker, which checks that a (secret) trace
represents a valid execution of a (public) program.  The output program is
SCALE bytecode and can be run using the SCALE engine.

To generate the witness checker:

    cargo run

Currently the input program and trace are hardcoded - see `main` in
`src/main.rs`.  The bytecode output path is also hardcoded as `out.bc`.

To run the checker using the SCALE engine:

    scripts/run_scale.py path/to/SCALE-MAMBA/Player.x out.bc

The script will run `out.bc` with three players, printing player 0's output to
the screen.  Near the end of the output, player 0 will print a line of digits
(1 or 0) indicating outcome of each check applied to the trace.  If the trace
is valid, then all digits should be 1.

To set up the SCALE engine, first clone [the SCALE-MAMBA
repository](https://github.com/KULeuven-COSIC/SCALE-MAMBA/).  Then follow the
installation instructions in the [SCALE
manual](https://homes.esat.kuleuven.be/~nsmart/SCALE/Documentation-SCALE.pdf),
specifically sections 3.1 (building the SCALE engine) and 3.4 (setting up
certificates for local use).
