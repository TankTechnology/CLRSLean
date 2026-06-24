import Mathlib

/-!
# CLRS Chapter 6.1-6.4 - Heaps and Heapsort

This file gives the first Lean model for Chapter 6's heap proof.  Instead of
starting with the array indices and in-place swaps of the CLRS pseudocode, it
models a max-heap as a list sorted in descending order.  This keeps the first
formal layer focused on the mathematical facts used by heapsort:

- inserting into a heap preserves the heap order and the multiset of elements;
- building a heap preserves all input elements;
- the heap maximum really is maximal;
- heapsort returns the same elements in ascending order.

Current gaps:

- The array representation, {lit}`MAX-HEAPIFY`, {lit}`BUILD-MAX-HEAP`, and the in-place
  swap loop are refinement targets.  The current file proves the functional
  heap interface that those implementations should refine.
- Runtime bounds and full RAM semantics are deferred to the project-level cost
  model.
-/

namespace CLRS
namespace Chapter06

/-! ## Ordered lists as functional heaps -/

/-- Ascending sortedness, used for the final heapsort output. -/
def OrderedAsc (xs : List Nat) : Prop :=
  xs.Pairwise (fun a b => a ≤ b)

/-- Descending sortedness, used as the abstract max-heap invariant. -/
def OrderedDesc (xs : List Nat) : Prop :=
  xs.Pairwise (fun a b => b ≤ a)

/-- Every element of {lit}`xs` is at most {lit}`upper`. -/
def AllLe (upper : Nat) (xs : List Nat) : Prop :=
  ∀ x ∈ xs, x ≤ upper

/-- Insert an element into a descending list. -/
def insertDesc (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
      if y ≤ x then
        x :: y :: ys
      else
        y :: insertDesc x ys

/-- Build a functional max-heap by repeated descending insertion. -/
def buildMaxHeap : List Nat → List Nat
  | [] => []
  | x :: xs => insertDesc x (buildMaxHeap xs)

/--
Functional heapsort: build a max-heap, then read it from smallest to largest.
For a descending-list heap this is just {lit}`reverse`.
-/
def heapSort (xs : List Nat) : List Nat :=
  (buildMaxHeap xs).reverse

/-! ## Insertion and heap construction -/

theorem allLe_insertDesc {upper x : Nat} {xs : List Nat}
    (hx : x ≤ upper) (hxs : AllLe upper xs) :
    AllLe upper (insertDesc x xs) := by
  induction xs with
  | nil =>
      intro z hz
      simp [insertDesc] at hz
      exact hz ▸ hx
  | cons y ys ih =>
      by_cases hyx : y ≤ x
      · intro w hw
        simp [insertDesc, hyx] at hw
        rcases hw with rfl | hwy
        · exact hx
        · exact hxs w (by simp [hwy])
      · intro w hw
        simp [insertDesc, hyx] at hw
        rcases hw with rfl | hwin
        · exact hxs w (by simp)
        · exact ih (fun z hz => hxs z (by simp [hz])) w hwin

/-- Inserting into a descending list preserves descending order. -/
theorem insertDesc_orderedDesc {x : Nat} {xs : List Nat}
    (hxs : OrderedDesc xs) : OrderedDesc (insertDesc x xs) := by
  induction xs with
  | nil =>
      simp [OrderedDesc, insertDesc]
  | cons y ys ih =>
      by_cases hyx : y ≤ x
      · rcases List.pairwise_cons.mp hxs with ⟨hy_all, htail⟩
        have hx_all : AllLe x (y :: ys) := by
          intro z hz
          simp at hz
          rcases hz with rfl | hzy
          · exact hyx
          · exact Nat.le_trans (hy_all z hzy) hyx
        simpa [OrderedDesc, insertDesc, hyx, AllLe] using
          List.Pairwise.cons (show ∀ z ∈ y :: ys, z ≤ x from hx_all) hxs
      · have hxy : x ≤ y := Nat.le_of_lt (Nat.lt_of_not_ge hyx)
        rcases List.pairwise_cons.mp hxs with ⟨hy_all, htail⟩
        have hinsert : OrderedDesc (insertDesc x ys) := ih htail
        have hy_insert : AllLe y (insertDesc x ys) :=
          allLe_insertDesc hxy hy_all
        simpa [OrderedDesc, insertDesc, hyx, AllLe] using
          List.Pairwise.cons
            (show ∀ z ∈ insertDesc x ys, z ≤ y from hy_insert) hinsert

/-- Descending insertion preserves the elements up to permutation. -/
theorem insertDesc_perm (x : Nat) (xs : List Nat) :
    (insertDesc x xs).Perm (x :: xs) := by
  induction xs with
  | nil =>
      simp [insertDesc]
  | cons y ys ih =>
      by_cases hyx : y ≤ x
      · simp [insertDesc, hyx]
      · simpa [insertDesc, hyx] using
          (List.Perm.cons y ih).trans (List.Perm.swap y x ys).symm

/-- Repeated insertion builds a descending heap. -/
theorem buildMaxHeap_orderedDesc (xs : List Nat) :
    OrderedDesc (buildMaxHeap xs) := by
  induction xs with
  | nil =>
      simp [OrderedDesc, buildMaxHeap]
  | cons x xs ih =>
      exact insertDesc_orderedDesc ih

/-- Building the heap preserves the input elements up to permutation. -/
theorem buildMaxHeap_perm (xs : List Nat) :
    (buildMaxHeap xs).Perm xs := by
  induction xs with
  | nil =>
      simp [buildMaxHeap]
  | cons x xs ih =>
      exact (insertDesc_perm x (buildMaxHeap xs)).trans (List.Perm.cons x ih)

/-! ## Heap maximum and heapsort correctness -/

/-- Return the maximum element of a functional max-heap, if any. -/
def heapMaximum? : List Nat → Option Nat
  | [] => none
  | x :: _ => some x

/-- Extract the maximum element and the remaining heap spine, if nonempty. -/
def heapExtractMax? : List Nat → Option (Nat × List Nat)
  | [] => none
  | x :: xs => some (x, xs)

/-- The head of a nonempty descending heap bounds every element in the heap. -/
theorem heapMaximum?_max {h : List Nat} {m : Nat}
    (hord : OrderedDesc h) (hmax : heapMaximum? h = some m) :
    ∀ x ∈ h, x ≤ m := by
  cases h with
  | nil =>
      simp [heapMaximum?] at hmax
  | cons y ys =>
      simp [heapMaximum?] at hmax
      subst m
      intro x hx
      simp at hx
      rcases hx with rfl | htail
      · exact Nat.le_refl _
      · exact (List.pairwise_cons.mp hord).1 x htail

/--
The maximum of a built heap is maximal among the original input elements.
-/
theorem buildMaxHeap_max {xs : List Nat} {m : Nat}
    (hmax : heapMaximum? (buildMaxHeap xs) = some m) :
    ∀ x ∈ xs, x ≤ m := by
  intro x hx
  have hxheap : x ∈ buildMaxHeap xs :=
    (List.Perm.mem_iff (buildMaxHeap_perm xs)).2 hx
  exact heapMaximum?_max (buildMaxHeap_orderedDesc xs) hmax x hxheap

/-- Extracting from a descending heap leaves a descending heap. -/
theorem heapExtractMax?_orderedDesc {h rest : List Nat} {m : Nat}
    (hord : OrderedDesc h) (hextract : heapExtractMax? h = some (m, rest)) :
    OrderedDesc rest := by
  cases h with
  | nil =>
      simp [heapExtractMax?] at hextract
  | cons y ys =>
      simp [heapExtractMax?] at hextract
      rcases hextract with ⟨rfl, rfl⟩
      exact (List.pairwise_cons.mp hord).2

/-- Extracting the maximum only decomposes the original heap into head and tail. -/
theorem heapExtractMax?_perm {h rest : List Nat} {m : Nat}
    (hextract : heapExtractMax? h = some (m, rest)) :
    h.Perm (m :: rest) := by
  cases h with
  | nil =>
      simp [heapExtractMax?] at hextract
  | cons y ys =>
      simp [heapExtractMax?] at hextract
      rcases hextract with ⟨rfl, rfl⟩
      rfl

/-- The element extracted from a descending heap bounds every remaining element. -/
theorem heapExtractMax?_max {h rest : List Nat} {m : Nat}
    (hord : OrderedDesc h) (hextract : heapExtractMax? h = some (m, rest)) :
    ∀ x ∈ rest, x ≤ m := by
  cases h with
  | nil =>
      simp [heapExtractMax?] at hextract
  | cons y ys =>
      simp [heapExtractMax?] at hextract
      rcases hextract with ⟨rfl, rfl⟩
      exact (List.pairwise_cons.mp hord).1

/-- Heapsort returns an ascending list. -/
theorem heapSort_orderedAsc (xs : List Nat) :
    OrderedAsc (heapSort xs) := by
  simpa [heapSort, OrderedAsc, OrderedDesc] using
    (buildMaxHeap_orderedDesc xs).reverse

/-- Heapsort preserves the input elements up to permutation. -/
theorem heapSort_perm (xs : List Nat) :
    (heapSort xs).Perm xs := by
  exact (List.reverse_perm (buildMaxHeap xs)).trans (buildMaxHeap_perm xs)

end Chapter06
end CLRS
