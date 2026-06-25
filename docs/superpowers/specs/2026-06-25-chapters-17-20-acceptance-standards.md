# CLRS Chapters 17-20 Acceptance Standards

Date: 2026-06-25
Status: accepted for first-pass implementation planning

This spec fixes the first-pass acceptance standards for CLRS-Lean Chapters 17
through 20 under the repository's current chapter numbering:

- Chapter 17: Amortized Analysis
- Chapter 18: B-Trees
- Chapter 19: Fibonacci Heaps
- Chapter 20: van Emde Boas Trees

The goal is not a line-by-line RAM or pointer semantics translation.  The first
pass is accepted when the chapter has a stable Lean mathematical model, a small
public theorem interface, proved textbook-facing main theorems, honest
deferred-refinement notes, and synchronized project status documents.

## Global Acceptance Contract

Every accepted chapter pass must satisfy the following project-level criteria.

1. Lean structure is present and navigable:
   - `CLRSLean/Chapter_XX.lean` exists.
   - Section files live under `CLRSLean/Chapter_XX/`.
   - The chapter is imported from `CLRSLean.lean`.
   - `literate.toml` lists the chapter and its represented sections.

2. Public theorem interface is small and CLRS-facing:
   - The main theorem names are stable enough for future `#check` tests.
   - Helper lemmas are local unless at least two sections need them.
   - Low-level implementation refinements are explicit strengthening targets,
     not hidden inside the main theorem.

3. Proof status is honest:
   - A chapter can be `proved` only when its advertised target theorems are
     sorry-free and do not rely on `axiom` or `admit`.
   - If theorem statements exist but proofs are not complete, the status is
     `statement` or `partial`.
   - Build success alone is not proof completion, because this project disables
     sorry warnings in Lake.

4. Reader-facing documentation is synchronized:
   - `docs/proof-map.md` records the theorem names, proof pattern, and gaps.
   - `docs/chapters/chapter-XX.md` records the chapter-level acceptance state
     once the chapter has a planned or implemented Lean surface.
   - `docs/clrs-proof-progress.csv` records status/count changes.
   - `CLRSLean/Progress.lean` is regenerated when the CSV changes.
   - `CLRSLean/Status.lean` is updated when public status wording changes.

5. Verification is fresh:
   - Run the narrow section check, for example
     `lake env lean CLRSLean/Chapter_17/Section_17_1_Aggregate_Analysis.lean`.
   - Run a chapter interface check with `#check` entries for the public names.
   - Run `lake build CLRSLean`.
   - Run `lake build :literateHtml` for website/navigation changes.

## Chapter 17 - Amortized Analysis

### First-Pass Goal

Chapter 17 should become the reusable amortized-analysis layer for later data
structure chapters.  The accepted first pass proves the common aggregate,
accounting, and potential-method facts and instantiates them on the textbook
stack, binary-counter, and dynamic-table examples.

### Required Lean Surface

The first pass should introduce:

- an actual-cost sequence model;
- aggregate amortized cost bounds over finite prefixes;
- an accounting model with nonnegative stored credit;
- a potential model with nonnegative potential and telescoping total-cost
  theorem;
- concrete models for `MULTIPOP`, binary-counter `INCREMENT`, and dynamic
  tables.

### Required Main Theorems

The chapter is first-pass accepted only when the following theorem groups are
proved.

- Generic aggregate theorem: if every prefix total actual cost is bounded by a
  simple expression, each operation has the corresponding amortized average.
- Generic accounting theorem: if per-operation charges preserve nonnegative
  credit, total actual cost is bounded by total charged cost plus initial credit.
- Generic potential theorem: if amortized cost is
  `actual + potential_after - potential_before`, finite sums telescope.
- `MULTIPOP` stack theorem: any sequence of stack operations has linear total
  cost in the number of pushes plus pops/multipops, yielding constant amortized
  cost for the standard CLRS operation set.
- Binary counter theorem: `n` increments on a `k`-bit counter flip at most
  `2 * n + k` bits, or an equivalent constant-amortized bound.
- Dynamic table theorem: the abstract expansion/shrink policy preserves the
  load-factor invariant and has constant amortized update cost.

### Deferred Refinements

The following are not required for first-pass completion:

- mutable-array copying semantics for table resizing;
- exact allocator or memory model;
- line-by-line RAM cost constants;
- randomized or cache-aware variants.

## Chapter 18 - B-Trees

### First-Pass Goal

Chapter 18 should formalize B-trees as mathematical search trees with bounded
node occupancy, separator invariants, same-depth leaves, search correctness,
insertion correctness, and a CLRS height bound.  Deletion can be included in the
first pass if the representation supports it cleanly, but an insertion-plus-height
pass may be accepted as `partial`.

### Required Lean Surface

The first pass should introduce:

- minimum degree `t` with assumption `2 <= t`;
- node key-count bounds, with root and non-root cases separated;
- sorted keys within a node;
- child-count invariant for internal nodes;
- separator invariant connecting child subtrees to parent keys;
- same-depth leaf invariant;
- membership and multiset/specification views of keys;
- abstract versions of `B-TREE-SEARCH`, `B-TREE-SPLIT-CHILD`,
  `B-TREE-INSERT-NONFULL`, and `B-TREE-INSERT`.

### Required Main Theorems

The chapter is first-pass accepted as `proved` only when these theorem groups
are proved.

- B-tree height theorem: for an `n`-key B-tree of height `h` and minimum degree
  `t >= 2`, the minimal-key argument gives `n >= 2 * t^h - 1`, packaged as the
  CLRS logarithmic height bound.
- Search theorem: `B-TREE-SEARCH` returns a position containing `x` exactly
  when `x` occurs in the B-tree.
- Split-child theorem: splitting a full child preserves key membership/multiset
  and the B-tree invariants required by insertion.
- Insert-nonfull theorem: insertion into a nonfull node preserves B-tree
  invariants and adds exactly the inserted key.
- Insert theorem: top-level insertion preserves B-tree invariants and has the
  expected membership/multiset specification.
- Delete theorem, if claimed complete: deletion preserves B-tree invariants and
  removes exactly the requested key occurrence.

### Deferred Refinements

The following are not required for first-pass completion:

- disk-page read/write semantics;
- buffer-cache behavior;
- pointer-level node mutation;
- satellite-data movement;
- exact CPU and I/O cost constants.

## Chapter 19 - Fibonacci Heaps

### First-Pass Goal

Chapter 19 should provide an abstract Fibonacci-heap forest model with
heap-ordering, minimum correctness, operation specifications, potential-method
amortized bounds, and the Fibonacci degree bound that turns extract-min and
delete into logarithmic-amortized operations.

### Required Lean Surface

The first pass should introduce:

- heap nodes as a finite forest or equivalent tree collection;
- root set, child relation, marks, ranks/degrees, and key membership;
- heap-order invariant;
- minimum pointer/specification invariant;
- operation-level specifications for `MAKE-HEAP`, `INSERT`, `MINIMUM`,
  `UNION`, `EXTRACT-MIN`, `DECREASE-KEY`, and `DELETE`;
- potential function `Phi = number_of_roots + 2 * number_of_marked_nodes`;
- a consolidation model sufficient to state and prove root-degree uniqueness
  after extract-min;
- subtree-size lower bound by Fibonacci numbers.

### Required Main Theorems

The chapter is first-pass accepted only when these theorem groups are proved.

- Basic operation correctness: `MAKE-HEAP`, `INSERT`, `MINIMUM`, and `UNION`
  preserve heap invariants and satisfy their membership/minimum specs.
- Extract-min correctness: returned key is the old minimum, the output contains
  exactly the remaining keys, and heap invariants are restored after
  consolidation.
- Decrease-key correctness: decreasing a key preserves membership with the
  updated key, preserves heap-order via cuts/cascading cuts, and restores the
  minimum spec.
- Delete correctness: delete is specified via decrease-to-minus-infinity plus
  extract-min or an equivalent abstract operation, and removes exactly the
  target key/handle.
- Potential theorem instantiation: using Chapter 17's generic potential theorem,
  insert/union/decrease-key have constant amortized cost, while extract-min and
  delete have cost bounded by a function of the maximum degree.
- Degree theorem: a node of degree `d` has subtree size at least the `d`th
  Fibonacci lower bound, yielding maximum degree `O(log n)`.

### Deferred Refinements

The following are not required for first-pass completion:

- circular doubly linked-list representation;
- pointer handles and memory safety;
- exact CLRS constant costs for every pointer update;
- destructive in-place implementation refinement.

## Chapter 20 - van Emde Boas Trees

### First-Pass Goal

Chapter 20 should formalize a recursively split universe model, prove that the
tree represents a finite set exactly, prove correctness of the main queries and
updates, and package the `O(log log u)` recurrence over the chosen universe
family.

### Required Lean Surface

The first pass should introduce:

- a Lean-friendly universe family, preferably `u = 2^(2^k)` or an equivalent
  recursive universe parameter;
- `high`, `low`, and `index` functions with reconstruction and bounds lemmas;
- base cases for small universes;
- abstract vEB state with `min`, `max`, summary, and clusters;
- representation invariant: `min`/`max` are correct, summary tracks nonempty
  clusters, and each cluster represents exactly the corresponding low parts;
- set semantics `Represents tree S`;
- operation models for `MEMBER`, `MINIMUM`, `MAXIMUM`, `SUCCESSOR`,
  `PREDECESSOR`, `INSERT`, and `DELETE`.

### Required Main Theorems

The chapter is first-pass accepted only when these theorem groups are proved.

- Decomposition theorem: `index (high x) (low x) = x`, with range bounds for
  `high` and `low`.
- Representation theorem: each operation preserves the vEB representation
  invariant.
- Member/min/max correctness: the returned values match the represented set.
- Successor/predecessor correctness: returned values are respectively the least
  represented key greater than the query and the greatest represented key less
  than the query.
- Insert/delete correctness: insertion adds exactly the key, deletion removes
  exactly the key, and all auxiliary summary/cluster invariants remain valid.
- Runtime recurrence theorem: under the selected universe family, the recursive
  operation-depth recurrence is linear in `k`, packaged as `O(log log u)` for
  the original universe size.

### Deferred Refinements

The following are not required for first-pass completion:

- bit-vector base-case optimization;
- word-RAM instruction semantics;
- space optimization and lazy cluster allocation;
- imperative memory layout.

## Initial Scheduling Recommendation

The implementation order should be:

1. Chapter 17 generic potential framework and small examples.
2. Chapter 18 B-tree height/search/insert model.
3. Chapter 20 vEB universe decomposition and query/update correctness.
4. Chapter 19 Fibonacci heaps, after Chapter 17's potential framework is
   available.

This order builds reusable proof infrastructure before relying on it.  Chapter
19 is intentionally after Chapter 17 because its cleanest acceptance path uses
the generic potential theorem.
