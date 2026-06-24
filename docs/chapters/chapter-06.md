# Chapter 6 - Heapsort

Chapter 6 is currently formalized through a functional max-heap interface.
A heap is represented by a descending list, which lets the first Lean pass prove
the mathematical correctness facts without committing to an imperative array
semantics.

## Completed

- Sections 6.1-6.4, heaps and heapsort:
  - `CLRS.Chapter06.buildMaxHeap_orderedDesc`
  - `CLRS.Chapter06.buildMaxHeap_perm`
  - `CLRS.Chapter06.buildMaxHeap_max`
  - `CLRS.Chapter06.heapExtractMax?_orderedDesc`
  - `CLRS.Chapter06.heapExtractMax?_max`
  - `CLRS.Chapter06.heapSort_orderedAsc`
  - `CLRS.Chapter06.heapSort_perm`
- Section 6.5, priority queues:
  - `CLRS.Chapter06.heapInsert_orderedDesc`
  - `CLRS.Chapter06.heapInsert_perm`
  - `CLRS.Chapter06.heapInsert_max`
  - `CLRS.Chapter06.heapIncreaseKey_orderedDesc`
  - `CLRS.Chapter06.heapIncreaseKey_perm`
  - `CLRS.Chapter06.heapDelete_orderedDesc`
  - `CLRS.Chapter06.heapDelete_perm`

## Open Refinements

- Prove an array-backed heap predicate with CLRS parent/left/right index
  arithmetic.
- Prove `MAX-HEAPIFY` preserves the heap property below the repaired node and
  preserves the multiset of array entries.
- Prove `BUILD-MAX-HEAP` refines the functional `buildMaxHeap` specification.
- Prove the in-place heapsort loop produces the same sorted permutation.
- Add RAM-cost bounds after the project has a shared imperative cost model.
