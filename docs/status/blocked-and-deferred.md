# Blocked And Deferred Items

This page records work that is not hidden but also not claimed as complete.

## Deferred Implementation

### Union-Find Correctness

- Related section: Section 23.2 - Kruskal and Prim
- Status: `deferred-implementation`
- Current decision: do not prove it in the first CLRS-lean phase.

The current MST proof uses `ComponentOracle` and `CycleTestImplementation` as
interfaces.  A future union-find implementation can refine this interface
without changing the mathematical Kruskal proof.

## Blocked Design

### Concrete MST Exchange Edge

- Related section: Section 23.1 - Growing a minimum spanning tree
- Status: `blocked-design`

The current theorem assumes a cut exchange certificate.  To remove that
assumption, we need a stable finite path or walk representation and a boundary
edge lemma for paths crossing a cut.

### Sorted-Order Lightness

- Related section: Section 23.2 - Kruskal and Prim
- Status: `partial`

Kruskal's textbook proof relies on processing edges in nondecreasing weight.
The Lean proof still needs a processed-prefix invariant showing that any lighter
crossing edge would already have been considered and rejected.

## Future Work

### CLRS Exercises

- Related scope: all chapters
- Status: `future-work`

Exercises should be recorded after the main theorem interface for a section is
stable.  This keeps the first pass focused on core textbook claims while still
leaving a clear path for a richer companion project.

### Chapter-End Problems

- Related scope: all chapters
- Status: `future-work`

Chapter-end Problems should become a separate track with explicit priority and
difficulty labels.  Some Problems are small theorem variations; others are
mini-projects and should not block the main chapter workflow.

### Full RAM Semantics

- Related scope: analysis-of-algorithms chapters
- Status: `future-work`

A full RAM semantics would model CLRS-style imperative pseudocode with machine
states, arrays or memory, variables/registers, control flow, primitive
operations, and per-step costs.  It is stronger than the current lightweight
cost models, which prove mathematical recurrences and bounds directly.

### General Merge-Sort Recurrence

- Related section: Section 2.3 - Designing algorithms
- Status: `future-work`

The power-of-two recurrence is proved.  The arbitrary-size recurrence
`T(n) = T(⌈n / 2⌉) + T(⌊n / 2⌋) + n` remains future work because it needs
floor/ceiling arithmetic, monotonicity, and a clean asymptotic theorem for all
input sizes.
