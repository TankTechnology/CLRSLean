import Mathlib

/-!
# CLRS Section 14.1 - Order-statistic trees

This section gives the first augmentation proof for CLRS-Lean.  An
order-statistic tree stores, at every node, a size field intended to equal the
number of nodes in that subtree.  The operation {lit}`osSelect?` uses the
stored size of the left child to implement rank selection.

The file separates the executable augmented operation from its ideal
mathematical specification:

* {lit}`storedSize` reads the cached field;
* {lit}`realSize` recomputes the mathematical subtree size;
* {lit}`WellSized` says every cached field is correct;
* {lit}`rankSelect?` is the ideal selector using recomputed sizes;
* {lit}`osSelect?` is the augmented selector using cached sizes.

Main results:

* Theorem {lit}`storedSize_eq_realSize_of_wellSized`: a well-sized tree has a
  correct root size field.
* Theorem {lit}`recomputeSizes_wellSized`: recomputing size fields establishes
  the augmentation invariant.
* Theorem {lit}`keys_recomputeSizes`: recomputing size fields preserves the
  inorder key sequence.
* Theorems {lit}`keys_rotateLeft` and {lit}`keys_rotateRight`: rotations
  preserve the inorder key sequence.
* Theorems {lit}`rotateLeft_wellSized` and {lit}`rotateRight_wellSized`:
  rotations with local size recomputation preserve the size augmentation
  invariant.
* Theorem {lit}`osSelect?_eq_rankSelect?_of_wellSized`: on a well-sized tree,
  the augmented selector agrees with the ideal rank selector.

Current gaps:

* The size-preserving rotation layer is functional; it is not yet connected to
  the Chapter 13 red-black insertion/deletion fixup procedures.
* Interval trees and the general augmentation theorem remain future targets.
-/

namespace CLRS
namespace Chapter14

/-! ## Augmented tree model -/

/-- A binary tree whose internal nodes cache their subtree size. -/
inductive OSTree where
  | empty : OSTree
  | node : OSTree → Nat → Nat → OSTree → OSTree
  deriving Repr, DecidableEq

namespace OSTree

/-- Mathematical inorder traversal of the keys, ignoring cached sizes. -/
def keys : OSTree → List Nat
  | empty => []
  | node left key _size right => keys left ++ [key] ++ keys right

/-- The cached size stored at the root.  Empty trees have cached size zero. -/
def storedSize : OSTree → Nat
  | empty => 0
  | node _left _key size _right => size

/-- The mathematical size obtained by recursively counting nodes. -/
def realSize : OSTree → Nat
  | empty => 0
  | node left _key _size right => realSize left + realSize right + 1

/-- Every cached size field agrees with the mathematical subtree size. -/
def WellSized : OSTree → Prop
  | empty => True
  | node left _key size right =>
      WellSized left ∧ WellSized right ∧
        size = realSize left + realSize right + 1

/-- Recompute every cached size field from the children upward. -/
def recomputeSizes : OSTree → OSTree
  | empty => empty
  | node left key _size right =>
      let left' := recomputeSizes left
      let right' := recomputeSizes right
      node left' key (realSize left' + realSize right' + 1) right'

/-! ## Local rotations -/

/--
Left rotation with local size recomputation.  If the right child is empty, the
tree is left unchanged.
-/
def rotateLeft : OSTree → OSTree
  | node a x _ (node b y _ c) =>
      let left' := node a x (realSize a + realSize b + 1) b
      node left' y (realSize left' + realSize c + 1) c
  | t => t

/--
Right rotation with local size recomputation.  If the left child is empty, the
tree is left unchanged.
-/
def rotateRight : OSTree → OSTree
  | node (node a x _ b) y _ c =>
      let right' := node b y (realSize b + realSize c + 1) c
      node a x (realSize a + realSize right' + 1) right'
  | t => t

/-! ## Selectors -/

/--
The ideal rank selector, using mathematically recomputed subtree sizes.
Ranks are zero-based: rank zero returns the first inorder key.
-/
def rankSelect? : OSTree → Nat → Option Nat
  | empty, _ => none
  | node left key _size right, i =>
      if i < realSize left then
        rankSelect? left i
      else if i = realSize left then
        some key
      else
        rankSelect? right (i - realSize left - 1)

/--
The augmented order-statistic selector, using cached subtree sizes rather than
recomputing them.  The main theorem states that this agrees with
{lit}`rankSelect?` whenever the cached fields are well-sized.
-/
def osSelect? : OSTree → Nat → Option Nat
  | empty, _ => none
  | node left key _size right, i =>
      if i < storedSize left then
        osSelect? left i
      else if i = storedSize left then
        some key
      else
        osSelect? right (i - storedSize left - 1)

/-! ## Augmentation correctness -/

/-- A well-sized tree has a correct root size field. -/
theorem storedSize_eq_realSize_of_wellSized {t : OSTree}
    (h : WellSized t) : storedSize t = realSize t := by
  cases t with
  | empty =>
      rfl
  | node left key size right =>
      exact h.2.2

/-- Recomputing cached size fields preserves the inorder key sequence. -/
theorem keys_recomputeSizes (t : OSTree) :
    keys (recomputeSizes t) = keys t := by
  induction t with
  | empty =>
      rfl
  | node left key size right ihLeft ihRight =>
      simp [recomputeSizes, keys, ihLeft, ihRight]

/-- Recomputing cached size fields establishes the size augmentation invariant. -/
theorem recomputeSizes_wellSized (t : OSTree) :
    WellSized (recomputeSizes t) := by
  induction t with
  | empty =>
      trivial
  | node left key size right ihLeft ihRight =>
      simp [recomputeSizes, WellSized, ihLeft, ihRight]

/-! ## Rotation correctness for the size augmentation -/

/-- Left rotation preserves the inorder key sequence. -/
theorem keys_rotateLeft (t : OSTree) :
    keys (rotateLeft t) = keys t := by
  cases t with
  | empty =>
      rfl
  | node a x sx right =>
      cases right with
      | empty =>
          rfl
      | node b y sy c =>
          simp [rotateLeft, keys, List.append_assoc]

/-- Right rotation preserves the inorder key sequence. -/
theorem keys_rotateRight (t : OSTree) :
    keys (rotateRight t) = keys t := by
  cases t with
  | empty =>
      rfl
  | node left y sy c =>
      cases left with
      | empty =>
          rfl
      | node a x sx b =>
          simp [rotateRight, keys, List.append_assoc]

/-- Left rotation preserves the mathematical subtree size. -/
theorem realSize_rotateLeft (t : OSTree) :
    realSize (rotateLeft t) = realSize t := by
  cases t with
  | empty =>
      rfl
  | node a x sx right =>
      cases right with
      | empty =>
          rfl
      | node b y sy c =>
          simp [rotateLeft, realSize]
          omega

/-- Right rotation preserves the mathematical subtree size. -/
theorem realSize_rotateRight (t : OSTree) :
    realSize (rotateRight t) = realSize t := by
  cases t with
  | empty =>
      rfl
  | node left y sy c =>
      cases left with
      | empty =>
          rfl
      | node a x sx b =>
          simp [rotateRight, realSize]
          omega

/-- Left rotation with local size recomputation preserves {lit}`WellSized`. -/
theorem rotateLeft_wellSized {t : OSTree}
    (h : WellSized t) : WellSized (rotateLeft t) := by
  cases t with
  | empty =>
      trivial
  | node a x sx right =>
      cases right with
      | empty =>
          simpa [rotateLeft] using h
      | node b y sy c =>
          rcases h with ⟨ha, hRight, _hSize⟩
          rcases hRight with ⟨hb, hc, _hRightSize⟩
          simp [rotateLeft, WellSized, realSize, ha, hb, hc]

/-- Right rotation with local size recomputation preserves {lit}`WellSized`. -/
theorem rotateRight_wellSized {t : OSTree}
    (h : WellSized t) : WellSized (rotateRight t) := by
  cases t with
  | empty =>
      trivial
  | node left y sy c =>
      cases left with
      | empty =>
          simpa [rotateRight] using h
      | node a x sx b =>
          rcases h with ⟨hLeft, hc, _hSize⟩
          rcases hLeft with ⟨ha, hb, _hLeftSize⟩
          simp [rotateRight, WellSized, realSize, ha, hb, hc]

/-- The augmented selector agrees with the ideal selector on well-sized trees. -/
theorem osSelect?_eq_rankSelect?_of_wellSized {t : OSTree} {i : Nat}
    (h : WellSized t) : osSelect? t i = rankSelect? t i := by
  induction t generalizing i with
  | empty =>
      rfl
  | node left key size right ihLeft ihRight =>
      rcases h with ⟨hLeft, hRight, hSize⟩
      have hLeftSize : storedSize left = realSize left :=
        storedSize_eq_realSize_of_wellSized hLeft
      by_cases hlt : i < realSize left
      · simp [osSelect?, rankSelect?, hLeftSize, hlt, ihLeft hLeft]
      · by_cases heq : i = realSize left
        · simp [osSelect?, rankSelect?, hLeftSize, heq]
        · simp [osSelect?, rankSelect?, hLeftSize, hlt, heq, ihRight hRight]

/--
Recomputing size fields makes the augmented selector agree with the ideal
selector without requiring an external invariant proof.
-/
theorem osSelect?_recomputeSizes_eq_rankSelect? (t : OSTree) (i : Nat) :
    osSelect? (recomputeSizes t) i = rankSelect? (recomputeSizes t) i := by
  exact osSelect?_eq_rankSelect?_of_wellSized (recomputeSizes_wellSized t)

end OSTree

end Chapter14
end CLRS
