# Chapter 7 - Quicksort

Chapter 7 now has a first compiler-clean correctness spine for quicksort.

## Section 7.1 - Description of quicksort

- Lean source: `CLRSLean/Chapter_07/Section_07_1_Description_Of_Quicksort.lean`
- Status: `proved` for the current functional-list model
- Main theorems: `CLRS.Chapter07.partitionAround_correct` and
  `CLRS.Chapter07.quickSort_correct`

The model uses a stable pivot partition rather than the CLRS in-place array
partition loop.  The proved partition facts are:

- `CLRS.Chapter07.partitionAround_left_eq_filter`: the left partition is
  exactly the stable filter of elements at most the pivot.
- `CLRS.Chapter07.partitionAround_right_eq_filter`: the right partition is
  exactly the stable filter of elements greater than the pivot.
- `CLRS.Chapter07.mem_partitionAround_left_iff`: membership in the left
  partition is equivalent to input membership plus `≤ pivot`.
- `CLRS.Chapter07.mem_partitionAround_right_iff`: membership in the right
  partition is equivalent to input membership plus `> pivot`.
- `CLRS.Chapter07.partitionAround_perm`: the two partition lists contain exactly
  the original tail elements.
- `CLRS.Chapter07.partitionAround_left_allLeUpper`: every left-partition element
  is at most the pivot.
- `CLRS.Chapter07.partitionAround_right_allGt`: every right-partition element is
  greater than the pivot.
- `CLRS.Chapter07.partitionAround_correct`: the reader-facing bundle of the
  partition classification, bounds, and permutation facts.

The quicksort theorem layer proves:

- `CLRS.Chapter07.quickSort_perm`: quicksort preserves the input elements up to
  permutation.
- `CLRS.Chapter07.quickSort_ordered`: quicksort returns an ordered list.
- `CLRS.Chapter07.quickSort_correct`: the reader-facing conjunction of
  sortedness and permutation preservation.

## Hard Follow-Up Work

- In-place `PARTITION` loop correctness: requires an array-segment invariant
  for the less/equal and greater regions.
- Deterministic performance analysis: requires a cost recurrence tied to the
  partition sizes.
- Randomized quicksort expected time: requires a probability model for random
  pivots or random permutations plus a recurrence or indicator-variable proof.
