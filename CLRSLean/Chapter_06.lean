import CLRSLean.Chapter_06.Section_06_1_Heapsort
import CLRSLean.Chapter_06.Section_06_5_Priority_Queues

/-!
# Chapter 6 - Heapsort

Chapter 6 introduces heaps, the heapsort algorithm, and max-priority queues.
The current CLRS-Lean pass proves a functional heap interface: a max-heap is
represented by a descending list, heap construction preserves the input
elements, the heap maximum is genuinely maximal, heapsort returns an ascending
permutation of its input, and priority-queue operations preserve the heap
invariant.

## Sections

* 6.1-6.4 Heaps and heapsort: {lit}`proved` for the functional descending-list
  model.  Main results: {lit}`CLRS.Chapter06.buildMaxHeap_orderedDesc`,
  {lit}`CLRS.Chapter06.buildMaxHeap_perm`,
  {lit}`CLRS.Chapter06.buildMaxHeap_max`,
  {lit}`CLRS.Chapter06.heapSort_orderedAsc`, and
  {lit}`CLRS.Chapter06.heapSort_perm`.
* 6.5 Priority queues: {lit}`proved` for the functional heap interface.  Main
  results: {lit}`CLRS.Chapter06.heapInsert_orderedDesc`,
  {lit}`CLRS.Chapter06.heapInsert_perm`,
  {lit}`CLRS.Chapter06.heapIncreaseKey_orderedDesc`, and
  {lit}`CLRS.Chapter06.heapDelete_orderedDesc`.

## Current Gaps

The array representation used in the CLRS pseudocode, {lit}`MAX-HEAPIFY`,
{lit}`BUILD-MAX-HEAP`, in-place heapsort swaps, and index-based priority-queue
updates remain refinement targets.  Runtime bounds and RAM semantics are
deferred to the project-level cost model.
-/

namespace CLRS
namespace Chapter06
end Chapter06
end CLRS
