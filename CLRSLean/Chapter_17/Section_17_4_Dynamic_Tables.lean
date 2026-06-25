import CLRSLean.Chapter_17.Section_17_1_Amortized_Framework

/-!
# CLRS Section 17.4 - Dynamic tables

This first-pass section keeps dynamic tables at the abstract size/count level.
It records the state invariant and a conservative potential wrapper that later
resize-transition proofs can instantiate.

Main results:

- Predicate {lit}`DynamicTableState.Valid`: the number of stored elements does
  not exceed allocated table size.
- Theorem {lit}`dynamicTable_amortizedBound`: the abstract dynamic-table
  amortized cost is bounded by actual cost plus the post-operation potential.

Current gaps:

- Concrete expansion and contraction transition predicates remain future work.
- Mutable-array copying and allocator semantics are deferred.
-/

namespace CLRS
namespace Chapter17

/-- Abstract dynamic-table state: stored element count and allocated size. -/
structure DynamicTableState where
  num : Nat
  size : Nat

namespace DynamicTableState

/-- The table never stores more elements than its allocated size. -/
def Valid (s : DynamicTableState) : Prop :=
  s.num <= s.size

end DynamicTableState

/--
A simple nonnegative potential for first-pass dynamic-table amortized wrappers.
Later resize-specific proofs can replace this with the sharper CLRS potential.
-/
def dynamicPotential (s : DynamicTableState) : Int :=
  Int.ofNat (2 * s.num + s.size)

/-- Abstract dynamic-table amortized cost for one state transition. -/
def dynamicTableAmortizedCost
    (before after : DynamicTableState) (actual : Nat) : Int :=
  Int.ofNat actual + dynamicPotential after - dynamicPotential before

/--
The abstract amortized transition cost is bounded by actual cost plus the
post-operation potential, because the pre-operation potential is nonnegative.
-/
theorem dynamicTable_amortizedBound
    (before after : DynamicTableState) (actual : Nat) :
    dynamicTableAmortizedCost before after actual <=
      Int.ofNat actual + dynamicPotential after := by
  have hnonneg : 0 <= dynamicPotential before := by
    unfold dynamicPotential
    exact Int.natCast_nonneg (2 * before.num + before.size)
  unfold dynamicTableAmortizedCost
  omega

end Chapter17
end CLRS
