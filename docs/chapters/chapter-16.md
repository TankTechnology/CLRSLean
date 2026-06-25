# Chapter 16 - Greedy Algorithms

## Section 16.1 - Activity Selection

- Lean source: `CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean`
- Status: `proved` for the finite sorted-list model
- Main theorems:
  - `CLRS.ActivitySelection.earliest_finish_minFinish`
  - `CLRS.ActivitySelection.finishSorted_head_minFinish`
  - `CLRS.ActivitySelection.finishSorted_greedyChoiceCertificate`
  - `CLRS.ActivitySelection.activitySelection`
  - `CLRS.ActivitySelection.activitySelection_cons_eq`
  - `CLRS.ActivitySelection.greedySelect_cons_eq`
  - `CLRS.ActivitySelection.greedySelect_sublist`
  - `CLRS.ActivitySelection.greedySelect_feasible`
  - `CLRS.ActivitySelection.greedy_choice_optimal_from_certificate`
  - `CLRS.ActivitySelection.greedySelect_after_maxCardinality`
  - `CLRS.ActivitySelection.greedySelect_cons_maxCardinality`
  - `CLRS.ActivitySelection.greedySelect_maxCardinality`
  - `CLRS.ActivitySelection.activitySelection_cons_maxCardinality`
  - `CLRS.ActivitySelection.activitySelection_maxCardinality`
  - `CLRS.ActivitySelection.greedySelect_optimal_length`
  - `CLRS.ActivitySelection.greedySelect_cons_recursive_correct`
  - `CLRS.ActivitySelection.activitySelection_cons_recursive_correct`
  - `CLRS.ActivitySelection.activitySelection_cons_correct`
  - `CLRS.ActivitySelection.activitySelection_correct`

This section formalizes the finite activity model, feasibility of selected
activity lists, finish-time ordering, the executable earliest-finish selector,
and the recursive greedy selector.  On finish-time-sorted inputs,
`greedySelect` is proved to return a feasible sublist with maximum cardinality
among all feasible sublists of the input.  The recursion theorem
`greedySelect_cons_maxCardinality` exposes the nonempty step directly: take the
first finish-sorted activity, filter to the compatible tail, and solve that
subproblem recursively.  The public wrapper `activitySelection` exposes the same
recursion and maximum-cardinality certificates under the CLRS-facing algorithm
name.  The bundled theorem `activitySelection_cons_recursive_correct` combines
the exact recursion equation, optimal recursive tail, optimal full solution,
feasibility, sublist membership, and the optimal-length inequality in one
reader-facing statement.  The theorem
`activitySelection_correct` gives the direct CLRS-facing theorem bundle: the
greedy output is a feasible sublist and every feasible sublist has length at
most the greedy output.  `activitySelection_cons_correct` gives the same bundle
for the nonempty recursive step.  Lower-level
array/pseudocode execution refinement remains outside this finite-list theorem
statement.

## Section 16.3 - Huffman Codes

- Lean source: `CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean`
- Status: `proved`
- Main theorems:
  - `CLRS.HuffmanV2.optimum_huffman_freqs`
  - `CLRS.HuffmanV2.huffmanOfFreqs_correct`
  - `CLRS.HuffmanV2.huffmanOfFreqs_cost_le`

This is currently the strongest completed CLRS-style case study in the project.
The proof uses a split-leaf exchange argument:

1. merge the two least frequent symbols;
2. use the inductive optimum for the merged instance;
3. split the merged leaf back into the two original leaves;
4. show no competing tree can have smaller cost.

The public interface is frequency-table based.  Users can cite
`huffmanOfFreqs_correct` for frequency preservation plus optimality, or
`huffmanOfFreqs_cost_le` for the direct theorem that no consistent tree with
the same frequencies has smaller cost.

## Greedy Proof Pattern

Both Section 16.1 and Section 16.3 use the same proof shape: package the
exchange step as a small certificate, prove the recursive subproblem, then
consume the certificate to lift the recursive optimum back to the original
problem.  See `docs/proof-patterns/greedy-exchange-certificates.md` for the
reader-facing version of this pattern.
