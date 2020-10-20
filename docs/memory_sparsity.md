## Consistency checking

The goal of these checks is to prevent the prover from introducing a fictitious
memory op into the memory checker that does not actually arise from any step in
the execution trace.

The `mem` module constructs roughly `num_steps / sparsity` secret `MemPort`s,
each shared by a block of `sparsity` consecutive steps.
We start by ensuring that:

 1. Every active `MemPort` (`cycle != MEM_PORT_UNUSED_CYCLE`) must be passed to
    some call to `calc_step`/`check_step`.
 2. `calc_step`/`check_step` must enforce that the fields of the `MemPort` it
    receives match the memory operation performed in that step (if any).

Enforcing (2) is relatively straightforward:

* If `mem_port.cycle` is the current cycle, then the step must perform a
  memory op, and the `MemPort`'s `addr`, `value`, and `op` fields must match
  the details of that memory op.
* If `mem_port.cycle == MEM_PORT_UNUSED_CYCLE`, then the step must not
  perform a memory op.
* If `mem_port.cycle` has any other value, then the trace is invalid.

These checks happen in `check_step`.

Then, to enforce (1):

* We keep a secret `user` index for each sparse `MemPort`, indicating which
  step within the block uses that `MemPort`.  If the `MemPort` is unused,
  then we set `user` to an out-of-range value (`user >= sparsity`).
* If `user >= sparsity`, then the corresponding `MemPort` must be inactive
  (`cycle == MEM_PORT_UNUSED_CYCLE`).  Now we need only show that every
  `MemPort` with `user < sparsity` is passed to some call to
  `calc_step`/`check_step`.
* The `MemPort`s passed to `calc_step`/`check_step` are produced by calling
  `mem::CyclePorts::get(i)` for every `i` in `0 .. num_steps`.  `get(i)`
  returns the `MemPort` for block `i / sparsity` if `i % sparsity == user`
  for that block.  We rely on `get` being called on every valid `i` to ensure
  that every active `MemPort` gets returned at least once.
* For all but the last block, `get` is called with each `i % sparsity` value,
  so if `user < sparsity`, then the `MemPort` is returned once.
* The last block may have fewer than `sparsity` steps in it (for example, if
  `sparsity` is 2 but `num_steps` is odd).  We assert that either `user <
  num_steps % sparsity` or `user >= sparsity` (i.e., `user` is not the index
  of a nonexistent step near the end of the block).  In the last block, `i %
  sparsity` takes on each value in the range `0 .. num_steps % sparsity`, so
  if `user < sparsity`, then `user < num_steps % sparsity` and `get` will
  return the `MemPort` once.

These checks happen in `Memory::add_cycles`, before the construction of the
`mem::CyclePorts`.
