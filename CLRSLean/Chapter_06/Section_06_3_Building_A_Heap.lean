import CLRSLean.Chapter_06.Section_06_2_Maintaining_Heap_Property

/-!
# CLRS Section 6.3 - Building a Heap

This section connects the current functional heap builder to the indexed heap
predicate introduced in Section 6.1.

Main results:

- Theorem {lit}`arrayBuildMaxHeap_isMaxHeap`: the array-facing builder returns
  an indexed max-heap over the whole list.
- Theorem {lit}`arrayBuildMaxHeap_perm`: the builder preserves the multiset of
  input elements.

Current gap:

- CLRS builds a heap bottom-up by repeated {lit}`MAX-HEAPIFY`.  The present theorem
  proves the same heap predicate for the compact functional builder; the
  bottom-up loop refinement depends on the remaining Section 6.2 swap-branch
  repair theorem.
-/

namespace CLRS
namespace Chapter06

/-! ## Array-level build refinement theorems -/

/-- Array-facing name for the current heap builder. -/
def arrayBuildMaxHeap (xs : List Nat) : List Nat :=
  buildMaxHeap xs

/-- The array-facing heap builder returns an indexed max-heap. -/
theorem arrayBuildMaxHeap_isMaxHeap (xs : List Nat) :
    ArrayMaxHeap (arrayBuildMaxHeap xs) (arrayBuildMaxHeap xs).length := by
  exact orderedDesc_arrayMaxHeap (Nat.le_refl _)
    (by simpa [arrayBuildMaxHeap] using buildMaxHeap_orderedDesc xs)

/-- The array-facing heap builder preserves the input elements. -/
theorem arrayBuildMaxHeap_perm (xs : List Nat) :
    (arrayBuildMaxHeap xs).Perm xs := by
  simpa [arrayBuildMaxHeap] using buildMaxHeap_perm xs

end Chapter06
end CLRS
