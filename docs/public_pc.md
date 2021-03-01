## Liveness

Some public-PC segments are present in the circuit but unused in the execution.
We must ensure that these "dead" segments cannot perform memory operations, as
otherwise the prover might be able to use them to inject fake memory ops that
alter the behavior of the program.

We track "liveness" via a new `live` flag within `RamState`.  If `live` is set,
this indicates that the following step is part of a live segment, and memory
ops in that step are valid (assuming all other memory-op validity conditions
are satisfied).  The `live` flag is `true` in the initial state, and its value
is preserved by every step.  The only way to obtain a non-`live` state is as
the initial state of a segment where all incoming edges are non-`live` (see the
"one live path" section for details).

Specifically, we assert that

* If a step's pre-state is non-`live`, then that step's `MemPort` must have
  `cycle == MEM_PORT_UNUSED_CYCLE`, so that the `MemPort` has no effect on the
  state of memory.  (Note that, when sparsity is enabled, states that do not
  perform memory ops will be given a dummy `MemPort` that always has `cycle ==
  MEM_PORT_UNUSED_CYCLE`.)

### One live path

We have so far ensured that all live (non-`UNUSED`) memory ops originate in
`live` segments; we wish to show that all live memory ops originate in a valid
execution.  So we must show that all `live` segments are part of a valid
execution.  To enforce this, we check that there is only *one live path*, which
originates at the initial state and does not fork, and we check that all
segments outside the live path are non-`live`.

To track the live path, we add a `live` flag to each edge between segments,
including edges leading to and from the routing network.  If the edge's `live`
flag is `true`, then its output state is the same as its input state; if the
edge's `live` flag is `false`, then the output state has `live == false`.  (The
other values of non-`live` states, such as PC and register values, don't
matter.  Some edges will copy these values from the input state, while others
may set them to hardcoded values, such as zero.)

To check the one-live-path property, we make the following assertions:

* If a segment's initial state is live, then at least one of its incoming edges
  is live; and if an edge is live, then its input state is live.  In other
  words, each live segment must have a live predecessor.  This check is
  implicit in the calculation of the segment's initial state: the initial state
  is computed by copying one of the predecessor states and `and`ing the state's
  `live` flag with the edge's `live` flag.

* If a segment's final state is live, it must have at most one live outgoing
  edge.  This check prevents "forking" the live path to create two live paths
  that run with parallel cycle counts; if the prover could do this, it might
  cause the two forks to diverge by giving them different advice, and then
  interleave their two unequal streams of memory accesses to produce program
  behavior that would otherwise be impossible.  Note that this check is "at
  most one" and not "exactly one" because the last segment used in the
  execution will have a live final state but no live outgoing edges.

There are two interesting cases that we don't assert against:

* A live segment may have multiple live incoming edges.  This can happen when
  the live path proceeds outward from the CPU initial state as normal, but
  eventually loops back to a previously used segment.  Only one of the incoming
  edges can "win" and provide the actual initial state of the segment; the
  behavior otherwise is exactly as if all the "losing" edges were actually
  non-`live`.

* The prover may construct a loop of live segments not connected to the initial
  state.  Non-empty loops are prevented by the cycle counter, which increases
  after every step, including stutter steps.  If segment `S` is its own
  ancestor and contains at least one step, then its initial cycle counter must
  be strictly greater than itself, a contradiction.  And empty loops, where all
  segments in the loop contain zero steps, perform no steps at all and thus
  have no side effects on memory.


## Cycle breaking

The segment graph may contain cycles (and, in fact, it very often does, since
the entire routing network is treated as a single node for the purposes of
circuit building), but the circuit itself must be acyclic.  We would like for
each segment to directly compute its initial state from the final states of its
possible predecessors, but when the segment graph contains cycles, this is not
always possible.  We handle the cyclic case by inserting "cycle-break nodes"
whose final state is a fresh secret value, explicitly constrained to match the
node's predecessors rather than computed directly from them.

We specifically assert the following for each cycle-break node:

* For each incoming edge, if the edge is `live`, then the cycle-break's secret
  state is equal to the edge's input state, which is the final state of the
  corresponding predecessor.

* If no incoming edge is live, then the cycle-break node's secret state must
  not be live.

The result is that the cycle-break node's secret state is equal to the initial
state that would be computed directly for an ordinary segment node.

Note this breaks the property described above in which each node has a single
"winning" predecessor that determines the node's initial state.  A cycle-break
node might have two live incoming edges where the two corresponding predecessor
nodes have equal final states.  However, if the predecessors have equal cycle
counters for their final states, then the path from the cycle-break node that
leads to the back edge must contain no steps, not even stutter steps, as in the
empty loop case.


## Routing network padding

The routing network can be unbalanced: it can have more or fewer inputs than it
has outputs.  In such cases, the shorter side will be padded out to the length
of the longer side.  Padding elements on the output side are discarded, but
padding values on the input side can be routed (and, in fact, must be routed)
to valid outputs.  We therefore must use non-`live` states for the input
padding to ensure that the number of live outputs matches the number of live
and valid (non-padding) inputs.
