# CLRS-lean

`CLRS-lean` is a chapter-by-chapter Lean companion project for CLRS-style
algorithm correctness proofs.

The project is organized by the book order, not by implementation topic.  A
section file is named with both its CLRS number and a short human-readable
suffix:

```text
CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean
CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean
CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean
CLRSLean/Chapter_02/Section_02_1_Insertion_Sort.lean
CLRSLean/Chapter_02/Section_02_2_Analyzing_Algorithms.lean
CLRSLean/Chapter_02/Section_02_3_Designing_Algorithms.lean
```

In prose and on the future website, these appear as:

- Section 16.3 - Huffman codes
- Section 23.1 - Growing a minimum spanning tree
- Section 23.2 - Kruskal and Prim
- Section 2.1 - Insertion sort
- Section 2.2 - Analyzing algorithms
- Section 2.3 - Designing algorithms

The Lean filenames use underscores instead of hyphens because Lean module names
should remain import-friendly.

## Current Sections

| CLRS section | Lean source | Status | Main result |
| --- | --- | --- | --- |
| Section 2.1 - Insertion sort | `CLRSLean/Chapter_02/Section_02_1_Insertion_Sort.lean` | `proved` | `CLRS.Chapter02.insertionSort_sorted`, `CLRS.Chapter02.insertionSort_perm` |
| Section 2.2 - Analyzing algorithms | `CLRSLean/Chapter_02/Section_02_2_Analyzing_Algorithms.lean` | `proved` | `CLRS.Chapter02.insertionSortWorstComparisons_quadratic` |
| Section 2.3 - Designing algorithms | `CLRSLean/Chapter_02/Section_02_3_Designing_Algorithms.lean` | `proved` | `CLRS.Chapter02.mergeSort_sortedLE`, `CLRS.Chapter02.mergeSort_perm`, `CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm` |
| Section 16.3 - Huffman codes | `CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean` | `proved` | `HuffmanV2.optimum_huffman_freqs` |
| Section 23.1 - Growing a minimum spanning tree | `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean` | `partial` | `CLRS.MST.safe_edge_of_lightest_crossing` |
| Section 23.2 - Kruskal and Prim | `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean` | `partial` | `CLRS.MST.kruskal_optimal` |

See [`proof-map.md`](proof-map.md) for the full status ledger.

Static preview:

```text
docs/site/index.html
```

## Status Labels

- `proved`: the main theorem for this section is sorry-free.
- `partial`: important Lean theorems exist, but the full CLRS section is not
  complete.
- `statement`: theorem interfaces exist, but proofs have not started.
- `blocked-design`: progress depends on choosing a representation, such as
  graph paths, heaps, arrays, or probability spaces.
- `blocked-mathlib`: progress depends on missing or inconvenient Mathlib
  infrastructure.
- `deferred-implementation`: the mathematical proof is in scope, but a low-level
  implementation proof is intentionally postponed.
- `future-work`: useful extension work, such as exercises or chapter-end
  Problems, that is intentionally outside the first main-theorem pass.
- `out-of-scope`: the section is not a current project target.

## Near-Term Rule

For early CLRS work, implementation-level data structure proofs are optional.
For example, union-find correctness is recorded as
`deferred-implementation`; the main MST target is the mathematical CLRS proof
via cut certificates and Kruskal's safe-edge induction.
