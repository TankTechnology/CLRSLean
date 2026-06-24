# Chapter 6 - Heapsort

Chapter 6 now has one public file per CLRS section.  The implementation still
has a compact functional heap scaffold, but the reader-facing layer separates
the array heap predicate, `MAX-HEAPIFY` facts, heap construction wrapper,
heapsort wrapper, and priority-queue operations.

## Completed

- Section 6.1, heaps:
  - `CLRS.Chapter06.parent_lt_self`
  - `CLRS.Chapter06.eq_left_or_right_parent`
  - `CLRS.Chapter06.ArrayMaxHeap.getElem_le_root`
  - `CLRS.Chapter06.orderedDesc_arrayMaxHeap`
- Section 6.2, maintaining the heap property:
  - `CLRS.Chapter06.swapAt_perm`
  - `CLRS.Chapter06.maxHeapifyFuel_perm`
  - `CLRS.Chapter06.valAt_i_le_maxChildIndex`
  - `CLRS.Chapter06.arrayMaxHeap_of_except_of_maxChildIndex_self`
- Section 6.3, building a heap:
  - `CLRS.Chapter06.arrayBuildMaxHeap_isMaxHeap`
  - `CLRS.Chapter06.arrayBuildMaxHeap_perm`
- Section 6.4, the heapsort algorithm:
  - `CLRS.Chapter06.arrayHeapSort_orderedAsc`
  - `CLRS.Chapter06.arrayHeapSort_perm`
- Section 6.5, priority queues:
  - `CLRS.Chapter06.heapInsert_orderedDesc`
  - `CLRS.Chapter06.heapInsert_perm`
  - `CLRS.Chapter06.heapInsert_max`
  - `CLRS.Chapter06.heapIncreaseKey_orderedDesc`
  - `CLRS.Chapter06.heapIncreaseKey_perm`
  - `CLRS.Chapter06.heapDelete_orderedDesc`
  - `CLRS.Chapter06.heapDelete_perm`

## Open Refinements

- Prove the recursive swap-branch repair theorem for `MAX-HEAPIFY`.
- Prove bottom-up `BUILD-MAX-HEAP` as repeated heapify.
- Prove the in-place heapsort loop over a shrinking heap prefix and growing
  sorted suffix.
- Refine the priority-queue operations to index-based array updates.
- Add RAM-cost bounds after the project has a shared imperative cost model.
