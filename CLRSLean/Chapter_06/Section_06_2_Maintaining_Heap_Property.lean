import CLRSLean.Chapter_06.Section_06_1_Heaps

/-!
# CLRS Section 6.2 - Maintaining the Heap Property

This section isolates the executable pieces around CLRS {lit}`MAX-HEAPIFY`.

Main results:

- Theorem {lit}`swapAt_perm`: swapping two array cells preserves the multiset
  of elements.
- Theorems {lit}`valAt_swapAt_left` and {lit}`valAt_swapAt_right`: after an
  in-bounds swap, the two exchanged cells contain each other's old values.
- Theorem {lit}`maxHeapifyFuel_perm`: the fuelled executable heapify loop
  preserves the multiset of elements.
- Theorems {lit}`valAt_i_le_maxChildIndex`,
  {lit}`valAt_left_le_maxChildIndex`, and
  {lit}`valAt_right_le_maxChildIndex`: the CLRS {lit}`largest` choice is locally
  maximal among the root and in-heap children.
- Theorem {lit}`arrayMaxHeap_of_except_of_maxChildIndex_self`: the no-swap
  branch of {lit}`MAX-HEAPIFY` repairs the only potentially bad parent.

Current gap:

- The swap branch of recursive {lit}`MAX-HEAPIFY` is still a refinement target:
  after swapping with the larger child, the child subtree must be shown to be
  recursively repaired.
-/

namespace CLRS
namespace Chapter06

/-! ## Swaps and fuelled {lit}`MAX-HEAPIFY` -/

/-- Read an array cell with fallback zero outside the list. -/
def valAt (a : List Nat) (i : Nat) : Nat :=
  a.getD i 0

/-- Inside bounds, {lit}`valAt` is the ordinary list-backed array read. -/
theorem valAt_eq_getElem (a : List Nat) {i : Nat} (hi : i < a.length) :
    valAt a i = a[i] := by
  simp [valAt, List.getElem?_eq_getElem hi]

/-- Swap two array cells when both indices are in bounds; otherwise leave the list unchanged. -/
def swapAt (a : List Nat) (i j : Nat) : List Nat :=
  match a[i]?, a[j]? with
  | some ai, some aj => (a.set i aj).set j ai
  | _, _ => a

/-- Auxiliary permutation lemma for swapping the head with a later cell. -/
theorem cons_set_perm_of_get? {xs : List Nat} {j x y : Nat}
    (h : xs[j]? = some y) : (y :: xs.set j x).Perm (x :: xs) := by
  induction xs generalizing j with
  | nil =>
      simp at h
  | cons z zs ih =>
      cases j with
      | zero =>
          simp at h
          subst y
          simp [List.set]
          exact List.Perm.swap x z zs
      | succ j =>
          simp at h
          have ih' := ih h
          simp [List.set]
          exact ((List.Perm.swap y z (zs.set j x)).symm.trans
            (List.Perm.cons z ih')).trans (List.Perm.swap z x zs).symm

/-- Swapping two cells preserves list length. -/
theorem swapAt_length (a : List Nat) (i j : Nat) :
    (swapAt a i j).length = a.length := by
  unfold swapAt
  cases a[i]? <;> cases a[j]? <;> simp

/-- Swapping two cells preserves the multiset of elements. -/
theorem swapAt_perm (a : List Nat) (i j : Nat) :
    (swapAt a i j).Perm a := by
  induction a generalizing i j with
  | nil =>
      simp [swapAt]
  | cons x xs ih =>
      cases i with
      | zero =>
          cases j with
          | zero =>
              simp [swapAt]
          | succ j =>
              unfold swapAt
              simp
              cases h : xs[j]? with
              | none =>
                  simp
              | some y =>
                  simpa [h, List.set] using
                    cons_set_perm_of_get? (xs := xs) (j := j) (x := x) h
      | succ i =>
          cases j with
          | zero =>
              unfold swapAt
              simp
              cases h : xs[i]? with
              | none =>
                  simp
              | some y =>
                  simpa [h, List.set] using
                    cons_set_perm_of_get? (xs := xs) (j := i) (x := x) h
          | succ j =>
              cases hi : xs[i]? with
              | none =>
                  simp [swapAt, hi]
              | some ai =>
                  cases hj : xs[j]? with
                  | none =>
                      simp [swapAt, hi, hj]
                  | some aj =>
                      simpa [swapAt, hi, hj, List.set] using ih i j

/-- After an in-bounds swap, the first index contains the old value at the second. -/
theorem valAt_swapAt_left {a : List Nat} {i j : Nat}
    (hi : i < a.length) (hj : j < a.length) :
    valAt (swapAt a i j) i = valAt a j := by
  by_cases hij : i = j
  · subst j
    simp [swapAt, valAt, List.getElem?_eq_getElem hi]
  · unfold swapAt
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    simp [valAt, Ne.symm hij]
    rw [List.getElem?_set_self']
    simp [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]

/-- After an in-bounds swap, the second index contains the old value at the first. -/
theorem valAt_swapAt_right {a : List Nat} {i j : Nat}
    (hi : i < a.length) (hj : j < a.length) :
    valAt (swapAt a i j) j = valAt a i := by
  by_cases hij : i = j
  · subst j
    simp [swapAt, valAt, List.getElem?_eq_getElem hi]
  · unfold swapAt
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    simp [valAt]
    rw [List.getElem?_set_self']
    have hjset : j < (a.set i a[j]).length := by
      simpa [List.length_set] using hj
    simp [List.getElem?_eq_getElem hjset, List.getElem?_eq_getElem hi]

/-- Choose between a current largest index and a candidate child. -/
def largerIndex (a : List Nat) (heapSize current candidate : Nat) : Nat :=
  if candidate < heapSize then
    if valAt a current < valAt a candidate then candidate else current
  else
    current

/-- The CLRS choice of the largest among {lit}`i`, {lit}`left i`, and {lit}`right i`. -/
def maxChildIndex (a : List Nat) (heapSize i : Nat) : Nat :=
  largerIndex a heapSize (largerIndex a heapSize i (left i)) (right i)

/-- A {lit}`largerIndex` result is at least the current index's key. -/
theorem valAt_current_le_largerIndex (a : List Nat)
    (heapSize current candidate : Nat) :
    valAt a current ≤ valAt a (largerIndex a heapSize current candidate) := by
  unfold largerIndex
  by_cases hc : candidate < heapSize
  · simp [hc]
    by_cases hlt : valAt a current < valAt a candidate
    · simp [hlt]
      exact Nat.le_of_lt hlt
    · simp [hlt]
  · simp [hc]

/-- If the candidate is in the heap, a {lit}`largerIndex` result is at least it. -/
theorem valAt_candidate_le_largerIndex {a : List Nat}
    {heapSize current candidate : Nat} (hcandidate : candidate < heapSize) :
    valAt a candidate ≤ valAt a (largerIndex a heapSize current candidate) := by
  unfold largerIndex
  simp [hcandidate]
  by_cases hlt : valAt a current < valAt a candidate
  · simp [hlt]
  · simp [hlt]
    exact Nat.le_of_not_gt hlt

/-- If the current index is inside the heap, the selected larger index is too. -/
theorem largerIndex_lt_heapSize {a : List Nat}
    {heapSize current candidate : Nat} (hcurrent : current < heapSize) :
    largerIndex a heapSize current candidate < heapSize := by
  unfold largerIndex
  by_cases hc : candidate < heapSize
  · simp [hc]
    by_cases hlt : valAt a current < valAt a candidate
    · simp [hlt, hc]
    · simp [hlt, hcurrent]
  · simp [hc, hcurrent]

/-- If the root is inside the heap, the CLRS {lit}`largest` index is inside too. -/
theorem maxChildIndex_lt_heapSize {a : List Nat} {heapSize i : Nat}
    (hi : i < heapSize) : maxChildIndex a heapSize i < heapSize := by
  unfold maxChildIndex
  exact largerIndex_lt_heapSize (largerIndex_lt_heapSize hi)

/-- The selected CLRS {lit}`largest` key is at least the original root key. -/
theorem valAt_i_le_maxChildIndex (a : List Nat) (heapSize i : Nat) :
    valAt a i ≤ valAt a (maxChildIndex a heapSize i) := by
  unfold maxChildIndex
  exact Nat.le_trans (valAt_current_le_largerIndex a heapSize i (left i))
    (valAt_current_le_largerIndex a heapSize
      (largerIndex a heapSize i (left i)) (right i))

/-- The selected CLRS {lit}`largest` key is at least the left child's key. -/
theorem valAt_left_le_maxChildIndex {a : List Nat} {heapSize i : Nat}
    (hl : left i < heapSize) :
    valAt a (left i) ≤ valAt a (maxChildIndex a heapSize i) := by
  unfold maxChildIndex
  exact Nat.le_trans (valAt_candidate_le_largerIndex (a := a) (current := i) hl)
    (valAt_current_le_largerIndex a heapSize
      (largerIndex a heapSize i (left i)) (right i))

/-- The selected CLRS {lit}`largest` key is at least the right child's key. -/
theorem valAt_right_le_maxChildIndex {a : List Nat} {heapSize i : Nat}
    (hr : right i < heapSize) :
    valAt a (right i) ≤ valAt a (maxChildIndex a heapSize i) := by
  unfold maxChildIndex
  exact valAt_candidate_le_largerIndex (a := a)
    (current := largerIndex a heapSize i (left i)) hr

/-- A left child index is strictly different from its parent index. -/
theorem left_ne_self (i : Nat) : left i ≠ i := by
  unfold left
  omega

/-- A right child index is strictly different from its parent index. -/
theorem right_ne_self (i : Nat) : right i ≠ i := by
  unfold right
  omega

/--
Fuelled executable version of {lit}`MAX-HEAPIFY`.  Each recursive call swaps the
current root with its largest in-heap child and continues at that child.
-/
def maxHeapifyFuel : Nat → List Nat → Nat → Nat → List Nat
  | 0, a, _, _ => a
  | fuel + 1, a, heapSize, i =>
      let largest := maxChildIndex a heapSize i
      if largest = i then
        a
      else
        maxHeapifyFuel fuel (swapAt a i largest) heapSize largest

/-- Fuelled heapify preserves list length. -/
theorem maxHeapifyFuel_length (fuel : Nat) (a : List Nat)
    (heapSize i : Nat) :
    (maxHeapifyFuel fuel a heapSize i).length = a.length := by
  induction fuel generalizing a i with
  | zero =>
      simp [maxHeapifyFuel]
  | succ fuel ih =>
      simp [maxHeapifyFuel]
      split
      · rfl
      · trans (swapAt a i (maxChildIndex a heapSize i)).length
        · exact ih (swapAt a i (maxChildIndex a heapSize i))
            (maxChildIndex a heapSize i)
        · exact swapAt_length a i (maxChildIndex a heapSize i)

/-- Fuelled heapify preserves the multiset of elements. -/
theorem maxHeapifyFuel_perm (fuel : Nat) (a : List Nat)
    (heapSize i : Nat) :
    (maxHeapifyFuel fuel a heapSize i).Perm a := by
  induction fuel generalizing a i with
  | zero =>
      simp [maxHeapifyFuel]
  | succ fuel ih =>
      simp [maxHeapifyFuel]
      split
      · rfl
      · exact (ih (swapAt a i (maxChildIndex a heapSize i))
          (maxChildIndex a heapSize i)).trans
          (swapAt_perm a i (maxChildIndex a heapSize i))

/--
If a {lit}`largerIndex` call returns a target different from its candidate, then the
target must have been the current index.  CLRS uses the same case split when
reasoning about the variable {lit}`largest`.
-/
theorem largerIndex_eq_target_forces_current {a : List Nat}
    {heapSize current candidate target : Nat}
    (h : largerIndex a heapSize current candidate = target)
    (hcandidate : candidate ≠ target) : current = target := by
  unfold largerIndex at h
  by_cases hin : candidate < heapSize
  · simp [hin] at h
    by_cases hlt : valAt a current < valAt a candidate
    · simp [hlt] at h
      exact False.elim (hcandidate h)
    · simpa [hlt] using h
  · simpa [hin] using h

/--
If {lit}`largerIndex` keeps the current index and the candidate is in the heap, then
the candidate's key is no larger than the current key.
-/
theorem largerIndex_eq_current_le {a : List Nat}
    {heapSize current candidate : Nat}
    (h : largerIndex a heapSize current candidate = current)
    (hcandidate : candidate < heapSize) :
    valAt a candidate ≤ valAt a current := by
  unfold largerIndex at h
  simp [hcandidate] at h
  by_cases hlt : valAt a current < valAt a candidate
  · simp [hlt] at h
    subst candidate
    exact Nat.le_refl _
  · exact Nat.le_of_not_gt hlt

/--
If {lit}`MAX-HEAPIFY` chooses not to swap, the left-child inequality at {lit}`i` holds.
-/
theorem maxChildIndex_eq_self_left_le {a : List Nat} {heapSize i : Nat}
    (hmax : maxChildIndex a heapSize i = i) (hl : left i < heapSize) :
    valAt a (left i) ≤ valAt a i := by
  have hleft : largerIndex a heapSize i (left i) = i :=
    largerIndex_eq_target_forces_current
      (by simpa [maxChildIndex] using hmax) (right_ne_self i)
  exact largerIndex_eq_current_le hleft hl

/--
If {lit}`MAX-HEAPIFY` chooses not to swap, the right-child inequality at {lit}`i` holds.
-/
theorem maxChildIndex_eq_self_right_le {a : List Nat} {heapSize i : Nat}
    (hmax : maxChildIndex a heapSize i = i) (hr : right i < heapSize) :
    valAt a (right i) ≤ valAt a i := by
  have hleft : largerIndex a heapSize i (left i) = i :=
    largerIndex_eq_target_forces_current
      (by simpa [maxChildIndex] using hmax) (right_ne_self i)
  have hright : largerIndex a heapSize i (right i) = i := by
    simpa [maxChildIndex, hleft] using hmax
  exact largerIndex_eq_current_le hright hr

/--
No-swap correctness for {lit}`MAX-HEAPIFY`: if all heap edges except those outgoing
from {lit}`i` are already valid, and {lit}`MAX-HEAPIFY` leaves {lit}`i` in place, the entire
prefix is a max-heap.
-/
theorem arrayMaxHeap_of_except_of_maxChildIndex_self {a : List Nat}
    {heapSize i : Nat} (hexcept : ArrayMaxHeapExcept a heapSize i)
    (hmax : maxChildIndex a heapSize i = i) : ArrayMaxHeap a heapSize := by
  refine ⟨hexcept.heapSize_le_length, ?_, ?_⟩
  · intro j hj hl
    by_cases hji : j = i
    · subst j
      have hval := maxChildIndex_eq_self_left_le hmax hl
      rw [valAt_eq_getElem a (Nat.lt_of_lt_of_le hl hexcept.heapSize_le_length),
        valAt_eq_getElem a (Nat.lt_of_lt_of_le hj hexcept.heapSize_le_length)] at hval
      exact hval
    · exact hexcept.left_le hj hji hl
  · intro j hj hr
    by_cases hji : j = i
    · subst j
      have hval := maxChildIndex_eq_self_right_le hmax hr
      rw [valAt_eq_getElem a (Nat.lt_of_lt_of_le hr hexcept.heapSize_le_length),
        valAt_eq_getElem a (Nat.lt_of_lt_of_le hj hexcept.heapSize_le_length)] at hval
      exact hval
    · exact hexcept.right_le hj hji hr

end Chapter06
end CLRS
