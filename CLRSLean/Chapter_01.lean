import Mathlib

/-!
# Chapter 1. Algorithms

This chapter is the doorway.  CLRS introduces what an algorithm is, why
correctness and efficiency matter, and how to think about algorithm design.
We do not repeat the original text; instead we show what those ideas look
like in Lean.

## An algorithm is a function … with a proof

In CLRS-Lean, *algorithm* means two things that live side by side:

1. A Lean function that computes something — the executable part.
2. A theorem that states what the function guarantees — the proof part.

For example, insertion sort is a pair `(f, P)` where `f` sorts a list and
`P` says that the result is ordered and permutes the input — see
Chapter 2 for the real Lean version.

Every section in later chapters follows this pattern: define the computation,
then prove the claim.

## Why formalize algorithm proofs?

Algorithm textbooks use pseudocode and loop invariants.  Lean can express
the same invariants as types, and the same inductive reasoning as dependent
pattern matching.  The gain is **machine-checked certainty**:

* No off-by-one errors in the invariant.
* No hand-waving about "and so forth" in an induction.
* The proof object can be inspected, reused, and composed.

The cost is precision: every case must be handled, every inequality justified.

## How to read the rest

| Chapter | What you'll find |
|---------|-----------------|
| 2 | Sorting correctness, a runtime bound, and a merge-sort recurrence |
| 16 | Huffman optimality — the flagship greedy proof |
| 23 | The MST cut property and Kruskal's induction |

To build and browse the site locally:

* `lake build` compiles everything.
* `lake build :literateHtml` generates this website.

## Conventions

* **0-indexed**: lists and sequences start at 0, for Mathlib compatibility.
* **Total functions**: partial operations return junk values, not `Option`.
* **Unfinished proofs**: marked `sorry` with a comment explaining the gap.
  Each chapter page lists exactly what is missing.

## Repository

[TankTechnology/CLRS-Lean](https://github.com/TankTechnology/CLRS-Lean)
-/

namespace CLRS
namespace Chapter01
end Chapter01
end CLRS