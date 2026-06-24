import Mathlib

/-!
# CLRS Section 6.1 - Heaps

This section introduces the heap layer used by the rest of Chapter 6.  It first
records a compact functional heap scaffold based on descending lists, then
introduces the array-indexed heap predicate and CLRS parent/child arithmetic.
Lists play the role of arrays, and the CLRS indices use the ordinary zero-based
formulas:

- left child: {lit}`2 * i + 1`;
- right child: {lit}`2 * i + 2`;
- parent: {lit}`(i - 1) / 2`.

Main results:

- Theorem {lit}`parent_lt_self`: every positive heap index has a smaller
  parent.
- Theorem {lit}`eq_left_or_right_parent`: every positive index is either the
  left or right child of its parent.
- Theorem {lit}`ArrayMaxHeap.getElem_le_root`: every element in an indexed
  max-heap prefix is bounded by the root.
- Theorem {lit}`orderedDesc_arrayMaxHeap`: the functional descending-list heap
  model refines the indexed max-heap predicate.
- Theorems {lit}`buildMaxHeap_orderedDesc`, {lit}`buildMaxHeap_perm`,
  {lit}`buildMaxHeap_max`, {lit}`heapSort_orderedAsc`, and
  {lit}`heapSort_perm`: the compact functional heap scaffold used by later
  refinement wrappers.

Current gap:

- This section proves the mathematical heap predicate and root-maximum fact.
  The executable {lit}`MAX-HEAPIFY`, {lit}`BUILD-MAX-HEAP`, and {lit}`HEAPSORT`
  refinements
  appear in Sections 6.2--6.4.
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

/-!
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

/-! ## CLRS array indices and heap predicate -/

/-- Zero-based left-child index. -/
def left (i : Nat) : Nat :=
  2 * i + 1

/-- Zero-based right-child index. -/
def right (i : Nat) : Nat :=
  2 * i + 2

/-- Zero-based parent index, with {lit}`parent 0 = 0` by natural subtraction. -/
def parent (i : Nat) : Nat :=
  (i - 1) / 2

/-- Every positive zero-based heap index has a strictly smaller parent. -/
theorem parent_lt_self {i : Nat} (hi : 0 < i) : parent i < i := by
  unfold parent
  omega

/-- Every positive index is either the left or right child of its parent. -/
theorem eq_left_or_right_parent {i : Nat} (hi : 0 < i) :
    i = left (parent i) ∨ i = right (parent i) := by
  unfold parent left right
  omega

/--
Indexed max-heap predicate over the prefix {lit}`0 ..< heapSize` of a list-backed
array.  Every in-heap parent is at least each in-heap child.
-/
structure ArrayMaxHeap (a : List Nat) (heapSize : Nat) : Prop where
  heapSize_le_length : heapSize ≤ a.length
  left_le : ∀ {i : Nat}, (hi : i < heapSize) → (hl : left i < heapSize) →
    a[left i]'(Nat.lt_of_lt_of_le hl heapSize_le_length) ≤
    a[i]'(Nat.lt_of_lt_of_le hi heapSize_le_length)
  right_le : ∀ {i : Nat}, (hi : i < heapSize) → (hr : right i < heapSize) →
    a[right i]'(Nat.lt_of_lt_of_le hr heapSize_le_length) ≤
    a[i]'(Nat.lt_of_lt_of_le hi heapSize_le_length)

/--
The same heap predicate with one possible bad parent.  This is the CLRS
precondition for {lit}`MAX-HEAPIFY`: both child subtrees are already heaps, so every
edge except the two outgoing edges from the root under repair is valid.
-/
structure ArrayMaxHeapExcept (a : List Nat) (heapSize bad : Nat) : Prop where
  heapSize_le_length : heapSize ≤ a.length
  left_le : ∀ {i : Nat}, (hi : i < heapSize) → i ≠ bad →
    (hl : left i < heapSize) →
    a[left i]'(Nat.lt_of_lt_of_le hl heapSize_le_length) ≤
    a[i]'(Nat.lt_of_lt_of_le hi heapSize_le_length)
  right_le : ∀ {i : Nat}, (hi : i < heapSize) → i ≠ bad →
    (hr : right i < heapSize) →
    a[right i]'(Nat.lt_of_lt_of_le hr heapSize_le_length) ≤
    a[i]'(Nat.lt_of_lt_of_le hi heapSize_le_length)

/-- A heap remains a heap after forgetting the obligations at one parent. -/
theorem ArrayMaxHeap.except {a : List Nat} {heapSize bad : Nat}
    (h : ArrayMaxHeap a heapSize) : ArrayMaxHeapExcept a heapSize bad := by
  refine ⟨h.heapSize_le_length, ?_, ?_⟩
  · intro i hi _ hl
    exact h.left_le hi hl
  · intro i hi _ hr
    exact h.right_le hi hr

/--
In an indexed max-heap, the root bounds every element in the heap prefix.  This
is the array-level proof behind CLRS {lit}`HEAP-MAXIMUM`.
-/
theorem ArrayMaxHeap.getElem_le_root {a : List Nat} {heapSize : Nat}
    (h : ArrayMaxHeap a heapSize) {i : Nat} (hi : i < heapSize) :
    a[i]'(Nat.lt_of_lt_of_le hi h.heapSize_le_length) ≤
      a[0]'(Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hi) h.heapSize_le_length) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simp
      | succ k =>
          let p := parent (Nat.succ k)
          have hpos : 0 < Nat.succ k := Nat.succ_pos k
          have hplt : p < Nat.succ k := parent_lt_self hpos
          have hpheap : p < heapSize := Nat.lt_trans hplt hi
          have hedge :
              a[Nat.succ k]'(Nat.lt_of_lt_of_le hi h.heapSize_le_length) ≤
                a[p]'(Nat.lt_of_lt_of_le hpheap h.heapSize_le_length) := by
            rcases eq_left_or_right_parent hpos with hleft | hright
            · have hchildEq : left p = Nat.succ k := hleft.symm
              have hchild : left p < heapSize := by simpa [hchildEq] using hi
              have hle := h.left_le hpheap hchild
              simpa [p, hchildEq] using hle
            · have hchildEq : right p = Nat.succ k := hright.symm
              have hchild : right p < heapSize := by simpa [hchildEq] using hi
              have hle := h.right_le hpheap hchild
              simpa [p, hchildEq] using hle
          have hparent := ih p hplt hpheap
          exact Nat.le_trans hedge (by simpa using hparent)

/--
In a descending list, a smaller index contains a value at least as large as any
larger index.  This bridges the first functional heap model to the indexed heap
predicate used by the CLRS array layer.
-/
theorem orderedDesc_getElem_le {xs : List Nat} (hxs : OrderedDesc xs)
    {i j : Nat} (hij : i < j) (hj : j < xs.length) : xs[j] ≤ xs[i] := by
  induction xs generalizing i j with
  | nil =>
      simp at hj
  | cons x xs ih =>
      cases j with
      | zero =>
          omega
      | succ j =>
          cases i with
          | zero =>
              have hj' : j < xs.length := by simpa using hj
              have htailmem : xs[j] ∈ xs := List.getElem_mem hj'
              have hx := (List.pairwise_cons.mp hxs).1 (xs[j]'hj') htailmem
              simpa using hx
          | succ i =>
              have htail : OrderedDesc xs := (List.pairwise_cons.mp hxs).2
              have hij' : i < j := by omega
              have hj' : j < xs.length := by simpa using hj
              simpa using ih htail hij' hj'

/-- A descending list is an indexed max-heap on any prefix. -/
theorem orderedDesc_arrayMaxHeap {a : List Nat} {heapSize : Nat}
    (hlen : heapSize ≤ a.length) (h : OrderedDesc a) :
    ArrayMaxHeap a heapSize := by
  refine ⟨hlen, ?_, ?_⟩
  · intro i hi hl
    exact orderedDesc_getElem_le h (by simp [left]; omega)
      (Nat.lt_of_lt_of_le hl hlen)
  · intro i hi hr
    exact orderedDesc_getElem_le h (by simp [right]; omega)
      (Nat.lt_of_lt_of_le hr hlen)

end Chapter06
end CLRS
