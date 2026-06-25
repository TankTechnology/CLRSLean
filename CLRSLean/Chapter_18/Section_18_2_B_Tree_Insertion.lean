import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model

/-!
# CLRS Section 18.2 - B-tree insertion

This first-pass section gives specification-level split and insertion wrappers
over the mathematical B-tree model from Section 18.1.  The goal is a stable
public theorem surface before introducing full node occupancy and separator
repair proofs.

Main results:

- Theorem {lit}`BTree.splitChild_preserves_model`: the first-pass split wrapper
  preserves validity and membership.
- Theorem {lit}`BTree.insert_preserves_model`: specification insertion preserves
  the first-pass validity predicate.
- Theorem {lit}`BTree.insert_mem_iff`: insertion adds exactly the inserted key
  to the membership specification.

Current gaps:

- This is not yet the full CLRS in-node split and insert-nonfull proof.  It is a
  specification layer that fixes the public theorem names and membership
  behavior for the later structural refinement.
-/

namespace CLRS
namespace Chapter18
namespace BTree

/-- First-pass split-child wrapper.  Structural split refinement is future work. -/
def splitChild (t : BTree) : BTree :=
  t

/-- The first-pass split wrapper preserves validity and membership. -/
theorem splitChild_preserves_model {minDegree : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    Valid minDegree (splitChild t) ∧
      forall x, mem x (splitChild t) <-> mem x t := by
  exact ⟨hvalid, by intro x; rfl⟩

/-- Specification-level B-tree insertion: add the key at a fresh root. -/
def insert (x : Nat) (t : BTree) : BTree :=
  node (x :: keysOf t) []

/-- Specification insertion preserves the first-pass validity predicate. -/
theorem insert_preserves_model {minDegree x : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    Valid minDegree (insert x t) := by
  exact hvalid

/-- Specification insertion adds exactly the inserted key to membership. -/
theorem insert_mem_iff (x y : Nat) (t : BTree) :
    mem y (insert x t) <-> y = x ∨ mem y t := by
  simp [insert, mem, keysOf]

end BTree
end Chapter18
end CLRS
