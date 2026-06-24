import Mathlib

/-!
# CLRS Section 12.1 - Binary search trees

This section gives a first Lean model of binary search trees as inductive trees
of natural-number keys.  It proves the fundamental search and insertion facts
used by the textbook invariant argument: search is correct on ordered trees,
minimum and maximum return genuine extremal keys, insertion adds exactly the
inserted key to the membership set, and insertion preserves the BST ordering
invariant.

Main results:

- Theorem {lit}`search_eq_true_iff`: Boolean search is equivalent to tree
  membership on ordered trees.
- Theorem {lit}`minimum?_inTree`: a returned minimum key occurs in the tree.
- Theorem {lit}`minimum?_le_of_ordered`: a returned minimum key is a lower bound
  on an ordered tree.
- Theorem {lit}`maximum?_inTree`: a returned maximum key occurs in the tree.
- Theorem {lit}`le_maximum?_of_ordered`: a returned maximum key is an upper
  bound on an ordered tree.
- Theorem {lit}`inTree_insert_iff`: membership after insertion is exactly the
  old membership relation plus the inserted key.
- Theorem {lit}`insert_ordered`: insertion preserves the BST ordering invariant.

Current gaps:

- Successor/predecessor, transplant, deletion, and pointer-level tree mutation
  are future section targets.
-/

namespace CLRS
namespace Chapter12

/-! ## Tree model and invariant -/

/-- A binary tree of natural-number keys. -/
inductive BSTree where
  | empty : BSTree
  | node : BSTree → Nat → BSTree → BSTree
  deriving Repr, DecidableEq

namespace BSTree

/-- Membership of a key in a binary tree. -/
def InTree (x : Nat) : BSTree → Prop
  | empty => False
  | node left key right => x = key ∨ InTree x left ∨ InTree x right

/-- Every key in the tree is strictly less than {lit}`bound`. -/
def AllLt (bound : Nat) (t : BSTree) : Prop :=
  ∀ x, InTree x t → x < bound

/-- Every key in the tree is strictly greater than {lit}`bound`. -/
def AllGt (bound : Nat) (t : BSTree) : Prop :=
  ∀ x, InTree x t → bound < x

/-- The binary-search-tree ordering invariant. -/
def Ordered : BSTree → Prop
  | empty => True
  | node left key right =>
      Ordered left ∧ Ordered right ∧ AllLt key left ∧ AllGt key right

/-- Functional insertion into a binary search tree. -/
def insert (x : Nat) : BSTree → BSTree
  | empty => node empty x empty
  | node left key right =>
      if x < key then
        node (insert x left) key right
      else if key < x then
        node left key (insert x right)
      else
        node left key right

/-! ## Search, minimum, and maximum operations -/

/-- Search for a key using the binary-search-tree ordering decisions. -/
def search (x : Nat) : BSTree → Bool
  | empty => false
  | node left key right =>
      if x = key then
        true
      else if x < key then
        search x left
      else
        search x right

/-- The minimum key of a nonempty tree, found by following left children. -/
def minimum? : BSTree → Option Nat
  | empty => none
  | node empty key _right => some key
  | node left@(node _ _ _) _key _right => minimum? left

/-- The maximum key of a nonempty tree, found by following right children. -/
def maximum? : BSTree → Option Nat
  | empty => none
  | node _left key empty => some key
  | node _left _key right@(node _ _ _) => maximum? right

/-! ## Search correctness -/

/-- On an ordered tree, Boolean search is equivalent to tree membership. -/
theorem search_eq_true_iff {x : Nat} {t : BSTree}
    (ht : Ordered t) : search x t = true ↔ InTree x t := by
  induction t with
  | empty =>
      simp [search, InTree]
  | node left key right ihLeft ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
      by_cases hxkey : x = key
      · simp [search, InTree, hxkey]
      · by_cases hxlt : x < key
        · have hnotRight : ¬ InTree x right := by
            intro hxRight
            exact (Nat.lt_asymm hxlt (hGt x hxRight)).elim
          simp [search, InTree, hxkey, hxlt, ihLeft hLeft, hnotRight]
        · have hnotLeft : ¬ InTree x left := by
            intro hxLeft
            exact hxlt (hLt x hxLeft)
          simp [search, InTree, hxkey, hxlt, ihRight hRight, hnotLeft]

/-! ## Minimum and maximum correctness -/

/-- If {lit}`minimum?` returns a key, that key occurs in the tree. -/
theorem minimum?_inTree {t : BSTree} {m : Nat}
    (hmin : minimum? t = some m) : InTree m t := by
  induction t with
  | empty =>
      simp [minimum?] at hmin
  | node left key right ihLeft _ihRight =>
      cases left with
      | empty =>
          simp [minimum?, InTree] at hmin ⊢
          exact Or.inl hmin.symm
      | node ll lk lr =>
          have hminLeft : (node ll lk lr).minimum? = some m := by
            simpa [minimum?] using hmin
          have hLeft : InTree m (node ll lk lr) := ihLeft hminLeft
          exact Or.inr (Or.inl hLeft)

/-- On an ordered tree, the result returned by {lit}`minimum?` is a lower bound. -/
theorem minimum?_le_of_ordered {t : BSTree} {m : Nat}
    (ht : Ordered t) (hmin : minimum? t = some m) :
    ∀ x, InTree x t → m ≤ x := by
  induction t generalizing m with
  | empty =>
      simp [minimum?] at hmin
  | node left key right ihLeft _ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
      cases left with
      | empty =>
          simp [minimum?] at hmin
          subst m
          intro x hx
          simp [InTree] at hx
          rcases hx with rfl | hxRight
          · exact le_rfl
          · exact Nat.le_of_lt (hGt x hxRight)
      | node ll lk lr =>
          have hminLeft : (node ll lk lr).minimum? = some m := by
            simpa [minimum?] using hmin
          have hMinLeft : InTree m (node ll lk lr) := minimum?_inTree hminLeft
          have hm_lt_key : m < key := hLt m hMinLeft
          intro x hx
          simp [InTree] at hx
          rcases hx with rfl | hxLeft | hxRight
          · exact Nat.le_of_lt hm_lt_key
          · exact ihLeft hLeft hminLeft x hxLeft
          · exact Nat.le_trans (Nat.le_of_lt hm_lt_key) (Nat.le_of_lt (hGt x hxRight))

/-- If {lit}`maximum?` returns a key, that key occurs in the tree. -/
theorem maximum?_inTree {t : BSTree} {m : Nat}
    (hmax : maximum? t = some m) : InTree m t := by
  induction t with
  | empty =>
      simp [maximum?] at hmax
  | node left key right _ihLeft ihRight =>
      cases right with
      | empty =>
          simp [maximum?, InTree] at hmax ⊢
          exact Or.inl hmax.symm
      | node rl rk rr =>
          have hmaxRight : (node rl rk rr).maximum? = some m := by
            simpa [maximum?] using hmax
          have hRight : InTree m (node rl rk rr) := ihRight hmaxRight
          exact Or.inr (Or.inr hRight)

/-- On an ordered tree, the result returned by {lit}`maximum?` is an upper bound. -/
theorem le_maximum?_of_ordered {t : BSTree} {m : Nat}
    (ht : Ordered t) (hmax : maximum? t = some m) :
    ∀ x, InTree x t → x ≤ m := by
  induction t generalizing m with
  | empty =>
      simp [maximum?] at hmax
  | node left key right _ihLeft ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
      cases right with
      | empty =>
          simp [maximum?] at hmax
          subst m
          intro x hx
          simp [InTree] at hx
          rcases hx with rfl | hxLeft
          · exact le_rfl
          · exact Nat.le_of_lt (hLt x hxLeft)
      | node rl rk rr =>
          have hmaxRight : (node rl rk rr).maximum? = some m := by
            simpa [maximum?] using hmax
          have hMaxRight : InTree m (node rl rk rr) := maximum?_inTree hmaxRight
          have hkey_lt_m : key < m := hGt m hMaxRight
          intro x hx
          simp [InTree] at hx
          rcases hx with rfl | hxLeft | hxRight
          · exact Nat.le_of_lt hkey_lt_m
          · exact Nat.le_trans (Nat.le_of_lt (hLt x hxLeft)) (Nat.le_of_lt hkey_lt_m)
          · exact ihRight hRight hmaxRight x hxRight

/-! ## Membership after insertion -/

/-- Insertion adds exactly the inserted key to the tree membership relation. -/
theorem inTree_insert_iff (x y : Nat) (t : BSTree) :
    InTree y (insert x t) ↔ y = x ∨ InTree y t := by
  induction t with
  | empty =>
      simp [insert, InTree]
  | node left key right ihLeft ihRight =>
      by_cases hxkey : x < key
      · simp [insert, InTree, hxkey, ihLeft, or_assoc, or_left_comm]
      · by_cases hkeyx : key < x
        · simp [insert, InTree, hxkey, hkeyx, ihRight, or_left_comm]
        · have hxeq : x = key := by
            exact Nat.le_antisymm (Nat.le_of_not_gt hkeyx) (Nat.le_of_not_gt hxkey)
          subst x
          simp [insert, InTree]

/-- The inserted key is a member of the resulting tree. -/
theorem inTree_insert_self (x : Nat) (t : BSTree) :
    InTree x (insert x t) := by
  exact (inTree_insert_iff x x t).mpr (Or.inl rfl)

/-- Existing members remain members after insertion. -/
theorem inTree_insert_of_inTree {x y : Nat} {t : BSTree}
    (h : InTree y t) : InTree y (insert x t) := by
  exact (inTree_insert_iff x y t).mpr (Or.inr h)

/-! ## Ordering after insertion -/

/-- Insertion preserves an upper-bound invariant when the inserted key satisfies it. -/
theorem allLt_insert {x bound : Nat} {t : BSTree}
    (hx : x < bound) (ht : AllLt bound t) :
    AllLt bound (insert x t) := by
  intro y hy
  rcases (inTree_insert_iff x y t).mp hy with rfl | hyold
  · exact hx
  · exact ht y hyold

/-- Insertion preserves a lower-bound invariant when the inserted key satisfies it. -/
theorem allGt_insert {x bound : Nat} {t : BSTree}
    (hx : bound < x) (ht : AllGt bound t) :
    AllGt bound (insert x t) := by
  intro y hy
  rcases (inTree_insert_iff x y t).mp hy with rfl | hyold
  · exact hx
  · exact ht y hyold

/-- Functional BST insertion preserves the binary-search-tree ordering invariant. -/
theorem insert_ordered {x : Nat} {t : BSTree}
    (ht : Ordered t) : Ordered (insert x t) := by
  induction t with
  | empty =>
      simp [insert, Ordered, AllLt, AllGt, InTree]
  | node left key right ihLeft ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
      by_cases hxkey : x < key
      · simp [insert, Ordered, hxkey]
        exact ⟨ihLeft hLeft, hRight, allLt_insert hxkey hLt, hGt⟩
      · by_cases hkeyx : key < x
        · simp [insert, Ordered, hxkey, hkeyx]
          exact ⟨hLeft, ihRight hRight, hLt, allGt_insert hkeyx hGt⟩
        · simp [insert, Ordered, hxkey, hkeyx, hLeft, hRight, hLt, hGt]

end BSTree

end Chapter12
end CLRS
