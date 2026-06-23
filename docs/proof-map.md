# CLRS-lean Proof Map

This ledger records what is proved, what is partial, and what is currently
deferred.  It is intended to become the website's main navigation table.

## Chapter 2 - Getting Started

### Section 2.1 - Insertion sort

- Lean source: `CLRSLean/Chapter_02/Section_02_1_Insertion_Sort.lean`
- Status: `proved`
- Main theorems:
  - `CLRS.Chapter02.insertionSort_sorted`
  - `CLRS.Chapter02.insertionSort_perm`
- Proof pattern: induction, sortedness preservation, permutation preservation
- Current gap: none for the current functional-list theorem statement

The section proves functional correctness for insertion sort over lists of
natural numbers.  The proof mirrors the textbook loop invariant by separating
orderedness from element preservation.

### Section 2.2 - Analyzing algorithms

- Lean source: `CLRSLean/Chapter_02/Section_02_2_Analyzing_Algorithms.lean`
- Status: `proved`
- Main theorems:
  - `CLRS.Chapter02.insertionSortWorstComparisons_quadratic`
  - `CLRS.Chapter02.insertionSortWorstComparisons_eventually_quadratic`
- Proof pattern: triangular sum, natural-number inequalities, asymptotic wrapper
- Current gap: full RAM semantics and exact line-by-line pseudocode cost are
  future strengthening targets

The section proves that the standard insertion-sort worst-case comparison count
is bounded by a quadratic function.

### Section 2.3 - Designing algorithms

- Lean source: `CLRSLean/Chapter_02/Section_02_3_Designing_Algorithms.lean`
- Status: `proved`
- Main theorems:
  - `CLRS.Chapter02.mergeSort_sortedLE`
  - `CLRS.Chapter02.mergeSort_perm`
  - `CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm`
- Proof pattern: divide and conquer, sortedness, permutation preservation,
  recurrence solving
- Current gap: arbitrary-size floor/ceiling recurrence and full RAM execution
  cost are future strengthening targets

The section proves functional correctness for merge sort using Lean's verified
`List.mergeSort` implementation.  It also proves the exact closed form of the
standard recurrence on input sizes `2^k`.

## Chapter 16 - Greedy Algorithms

### Section 16.3 - Huffman codes

- Lean source: `CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean`
- Status: `proved`
- Main theorem: `HuffmanV2.optimum_huffman_freqs`
- Proof pattern: greedy exchange argument, split-leaf transformation
- Current gap: none for the current theorem statement

The section proves that Huffman coding produces an optimal prefix tree for a
nonempty frequency table with distinct symbols and positive frequencies.

## Chapter 23 - Minimum Spanning Trees

### Section 23.1 - Growing a minimum spanning tree

- Lean source:
  `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean`
- Status: `partial`
- Main proved theorem: `CLRS.MST.safe_edge_of_lightest_crossing`
- Supporting theorem: `CLRS.MST.mst_exchange_step`
- Proof pattern: cut property, safe edge, exchange argument
- Current gap: the concrete path/cycle lemma that constructs the exchange edge
  from a finite graph spanning tree is still an explicit certificate.

This section contains the mathematical core of the CLRS MST proof.  It proves
that a light edge crossing a cut is safe once the graph-specific exchange
certificate is supplied.

### Section 23.2 - Kruskal and Prim

- Lean source: `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean`
- Status: `partial`
- Main proved theorem: `CLRS.MST.kruskal_optimal`
- Supporting theorem: `CLRS.MST.FiniteGraph.kruskal_optimal`
- Proof pattern: safe-edge induction over an edge list
- Deferred implementation: union-find correctness
- Current gaps:
  - derive lightness automatically from a sorted edge order;
  - prove the final selected edge set is a spanning tree from connectedness and
    complete edge scan;
  - add Prim's algorithm theorem interface.

The section currently proves a mathematical Kruskal skeleton: if accepted edges
come with safe-edge certificates and the final selected set is a spanning tree,
then the result is optimal.

## Deferred And Blocked Items

| Item | Status | Reason |
| --- | --- | --- |
| Union-find implementation correctness | `deferred-implementation` | Not needed for the mathematical MST correctness theorem. |
| Sorted-order lightness for Kruskal | `partial` | Needs a list-order invariant over processed edges. |
| Concrete MST exchange edge from paths | `blocked-design` | Needs a stable finite path/walk representation. |
| Prim's algorithm | `statement` | Section file exists only through the Chapter 23.2 target; theorem interface has not been added yet. |
| CLRS exercises | `future-work` | Keep the first pass focused on main textbook claims; add exercises after section interfaces stabilize. |
| Chapter-end problems | `future-work` | Treat as a second track with explicit priority and difficulty labels. |
| Full RAM semantics | `future-work` | Requires an imperative machine/cost semantics rather than only mathematical functions and recurrences. |
| General merge-sort recurrence | `future-work` | Needs floor/ceiling arithmetic and an asymptotic theorem for all input sizes. |

## Publication Value

The proof map is intentionally honest.  Completed sections show theorem names
that compile.  Partial sections expose the exact missing mathematical or
representation layer.  This lets future contributors pick a section without
reverse-engineering the project state.
