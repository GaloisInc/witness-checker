# Cheesecloth witness checker prototype

This tool constructs a witness/trace checking circuit, which checks that a
(secret) trace represents a valid execution of a (public) program.  The output
can be saved in zkInterface format and evaluated using other tools.

To generate the witness checking circuit:

    cargo run --release -- examples/memory-3.yaml

The input is a program and trace in the CBOR format produced by MicroRAM.
(YAML and JSON representations are also accepted, allowing for human-readable
input.)  The tool will build and evaluate the circuit and print some output
about the status of its various validity assertions and bug checks.

By default, the trace is expected to exhibit a memory safety error.  If you
only want to check that the trace is valid, use the `--validate-only` flag:

    cargo run --release -- examples/memory-1.yaml --validate-only

To save the circuit in ZKIF format:

    cargo run --release --features bellman -- examples/memory-3.yaml --zkif-out zkif

This will produce zkInterface files in the `zkif/` directory, which you can
later evaluate using `mac-n-cheese` or a similar tool.

You may need to add `CARGO_NET_GIT_FETCH_WITH_CLI=true` to `cargo` commands to
clone dependencies.
