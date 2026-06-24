import CLRSLean.Chapter_06.Section_06_1_Heaps
import CLRSLean.Chapter_06.Section_06_2_Maintaining_Heap_Property
import CLRSLean.Chapter_06.Section_06_3_Building_A_Heap
import CLRSLean.Chapter_06.Section_06_4_Heapsort
import CLRSLean.Chapter_06.Section_06_5_Priority_Queues

/-!
# Chapter 6 - Heapsort

Chapter 6 introduces heaps, the heapsort algorithm, and max-priority queues.
The current CLRS-Lean pass has two layers.  The compact functional layer proves
the mathematical heapsort specification: heap construction preserves elements,
the heap maximum is genuinely maximal, and heapsort returns an ascending
permutation.  The array layer adds the zero-based CLRS child/parent formulas,
an indexed heap predicate, {lit}`MAX-HEAPIFY`'s {lit}`largest` choice facts,
no-swap repair, swap permutation/read lemmas, and the array-level
{lit}`HEAP-MAXIMUM`
theorem.

## Sections

* 6.1 Heaps: {lit}`partial` for the CLRS array refinement.  Main results:
  {lit}`CLRS.Chapter06.parent_lt_self`,
  {lit}`CLRS.Chapter06.eq_left_or_right_parent`,
  {lit}`CLRS.Chapter06.ArrayMaxHeap.getElem_le_root`, and
  {lit}`CLRS.Chapter06.orderedDesc_arrayMaxHeap`.
* 6.2 Maintaining the heap property: {lit}`partial`.  Main results:
  {lit}`CLRS.Chapter06.swapAt_perm`,
  {lit}`CLRS.Chapter06.maxHeapifyFuel_perm`, and
  {lit}`CLRS.Chapter06.arrayMaxHeap_of_except_of_maxChildIndex_self`.
* 6.3 Building a heap: {lit}`partial`, using the functional builder as the
  current executable model.  Main results:
  {lit}`CLRS.Chapter06.arrayBuildMaxHeap_isMaxHeap` and
  {lit}`CLRS.Chapter06.arrayBuildMaxHeap_perm`.
* 6.4 The heapsort algorithm: {lit}`proved` for the functional heapsort model,
  and {lit}`partial` for the in-place CLRS loop refinement.  Main results:
  {lit}`CLRS.Chapter06.arrayHeapSort_orderedAsc` and
  {lit}`CLRS.Chapter06.arrayHeapSort_perm`.
* 6.5 Priority queues: {lit}`proved` for the functional heap interface, with an
  array-level maximum theorem.  Main results:
  {lit}`CLRS.Chapter06.heapInsert_orderedDesc`,
  {lit}`CLRS.Chapter06.heapInsert_perm`,
  {lit}`CLRS.Chapter06.heapIncreaseKey_orderedDesc`, and
  {lit}`CLRS.Chapter06.heapDelete_orderedDesc`; array result:
  {lit}`CLRS.Chapter06.arrayHeapMaximum?_max`.

## Current Gaps

The full recursive repair theorem for the swap branch of {lit}`MAX-HEAPIFY`,
bottom-up {lit}`BUILD-MAX-HEAP` as repeated heapify, the in-place heapsort loop
with shrinking heap prefix and sorted suffix, index-based {lit}`HEAP-INCREASE-KEY`
and {lit}`HEAP-DELETE`, and runtime/RAM semantics remain refinement targets.
-/

namespace CLRS
namespace Chapter06
end Chapter06
end CLRS
