import CLRSLean.Chapter_06.Section_06_3_Building_A_Heap

/-!
# CLRS Section 6.4 - The Heapsort Algorithm

This section exposes the Chapter 6 heapsort correctness theorem through the
array-facing names used by the rest of the project.

Main results:

- Theorem {lit}`arrayHeapSort_orderedAsc`: heapsort returns ascending output.
- Theorem {lit}`arrayHeapSort_perm`: heapsort preserves the multiset of input
  elements.

Current gap:

- The theorem currently wraps the functional heapsort model.  A line-by-line
  refinement of the CLRS in-place loop over a shrinking heap prefix and growing
  sorted suffix remains future work.
-/

namespace CLRS
namespace Chapter06

/-! ## Array-level heapsort refinement theorems -/

/-- Array-facing name for the current heapsort implementation. -/
def arrayHeapSort (xs : List Nat) : List Nat :=
  heapSort xs

/-- Array-facing heapsort returns ascending output. -/
theorem arrayHeapSort_orderedAsc (xs : List Nat) :
    OrderedAsc (arrayHeapSort xs) := by
  simpa [arrayHeapSort] using heapSort_orderedAsc xs

/-- Array-facing heapsort preserves the input elements. -/
theorem arrayHeapSort_perm (xs : List Nat) :
    (arrayHeapSort xs).Perm xs := by
  simpa [arrayHeapSort] using heapSort_perm xs

end Chapter06
end CLRS
