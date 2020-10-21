## Consistency checking

The goal of these checks is to prevent the prover from introducing a fictitious
memory op into the memory checker that does not actually arise from any step in
the execution trace.

The `mem` module constructs roughly `num_steps / sparsity` secret `MemPort`s,
each shared by a block of `sparsity` consecutive steps.
We start by ensuring that:

 1. Every `MemPort` must be passed to some call to `calc_step`/`check_step`.
 2. `calc_step`/`check_step` must enforce that the fields of the `MemPort` it
    receives match the memory operation performed in that step, if any.

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
  then we arbitrarily set `user` to zero.  In all cases, we require that `user
  < sparsity`.
* The `MemPort`s passed to `calc_step`/`check_step` are produced by calling
  `mem::CyclePorts::get(i)` for every `i` in `0 .. num_steps`.  `get(i)`
  returns the `MemPort` for block `i / sparsity` if `i % sparsity == user`
  for that block.  We rely on `get` being called on every valid `i` to ensure
  that every active `MemPort` gets returned at least once.
* For all but the last block, `get` is called with each `i % sparsity` value.
  Since `user < sparsity`, the `MemPort` is returned by one such `get` calls.
* The last block may have fewer than `sparsity` steps in it (for example, if
  `sparsity` is 2 but `num_steps` is odd).  In this case, we assert that `user
  < num_steps % sparsity` to ensure that `user` is not the index of a
  nonexistent step near the end of the block.  In a truncated last block, `i %
  sparsity` takes on each value in the range `0 .. num_steps % sparsity`.
  Since `user < num_steps % sparsity`, `get` will return the `MemPort` once.

These checks happen in `Memory::add_cycles`, before the construction of the
`mem::CyclePorts`.

Under this scheme,

* If a block contains a memory op, then its `user` must refer to the step
  that performs the memory op, and its `MemPort` must match the parameters of
  the memory op.  If the step receives a bad `MemPort` (either because the
  parameters in the block's `MemPort` are wrong, or because `user` is set
  incorrectly and the step receives an unused placeholder `MemPort`), then the
  checks in (2) will fail.
* If a block does not contain a memory op, then its `MemPort` must be unused.
  Some step in the block will receive the `MemPort`; no step in the block is a
  memory op, so that step will check that the `MemPort` is unused.
* If a block contains multiple memory ops, then the trace is invalid.  Only the
  single step identified by `user` will receive an active `MemPort`.  The other
  step will receive an unused placeholder `MemPort`, and the checks in (2) will
  fail.


## Fractional sparsity

We may eventually wish to extend the memory sparsity system to support
*fractional sparsity*, in which there are `N` memory ports shared by each block
of `D` steps, for an average of `N/D` memory ports per step.  (In the current
design, `N` is always 1.)  This would require a few adjustments to preserve the
central property that every `MemPort` is passed to some step:

* We would need to track a separate `user` for each `MemPort`, and require that
  all `user` indices are distinct.  The least expensive way to do this would be
  to require that they be sorted: `user0 < user1 < sparsity`.
* We would need a slightly more clever scheme for setting the `user` index for
  unused `MemPort`s.  With multiple `MemPort`s in a block, they can't all have
  `user == 0`.
* The last block could have fewer than `N` steps in it, in which case it would
  need to have fewer than `N` `MemPort`s as well.
