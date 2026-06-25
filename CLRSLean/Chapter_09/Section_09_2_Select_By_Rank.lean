import Mathlib

/-!
# CLRS Section 9.2 - Selection by rank

This file gives the first Chapter 9 correctness interface: a selector returns
an element with the requested zero-based order statistic.  The implementation is
the simple specification program obtained by sorting and indexing; randomized
or deterministic linear-time SELECT can later refine to this interface.

The public certificate is phrased by counts, so duplicates are handled in the
usual order-statistic way: if the selected value is {lit}`x`, then at most
{lit}`k` elements are strictly smaller than {lit}`x`, and more than {lit}`k`
elements are at most {lit}`x`.
-/

namespace CLRS
namespace Chapter09

/-! ## Specification selector and rank certificate -/

/-- A sorted copy of the input, used as the executable specification. -/
def sortedCopy (xs : List Nat) : List Nat :=
  xs.mergeSort (fun x y => decide (x ≤ y))

/-- Number of input elements strictly smaller than {lit}`x`. -/
def ltCount (x : Nat) (xs : List Nat) : Nat :=
  (xs.filter (fun y => decide (y < x))).length

/-- Number of input elements at most {lit}`x`. -/
def leCount (x : Nat) (xs : List Nat) : Nat :=
  (xs.filter (fun y => decide (y ≤ x))).length

/-- Select the zero-based rank {lit}`k`, if the input has that many elements. -/
def selectByRank? (k : Nat) (xs : List Nat) : Option Nat :=
  (sortedCopy xs)[k]?

/--
Rank certificate for order statistics with duplicates.  The selected value
{lit}`x` is present in the input, the number of values below it is at most
{lit}`k`, and the number of values at most it is greater than {lit}`k`.
-/
def RankCertificate (xs : List Nat) (k x : Nat) : Prop :=
  x ∈ xs ∧ ltCount x xs ≤ k ∧ k < leCount x xs

theorem sortedCopy_perm (xs : List Nat) :
    (sortedCopy xs).Perm xs := by
  simpa [sortedCopy] using
    List.mergeSort_perm xs (fun x y => decide (x ≤ y))

theorem sortedCopy_pairwise (xs : List Nat) :
    (sortedCopy xs).Pairwise (fun x y => x ≤ y) := by
  simpa [sortedCopy] using
    List.pairwise_mergeSort' (r := fun x y : Nat => x ≤ y) xs

/-! ## List lemmas for the rank proof -/

theorem getElem?_eq_some_iff_split {α : Type u} :
    ∀ {xs : List α} {k : Nat} {x : α},
      xs[k]? = some x ↔
        ∃ lo hi, xs = lo ++ x :: hi ∧ lo.length = k := by
  intro xs k x
  constructor
  · intro h
    induction k generalizing xs with
    | zero =>
        cases xs with
        | nil =>
            simp at h
        | cons y ys =>
            simp at h
            subst y
            exact ⟨[], ys, by simp, rfl⟩
    | succ k ih =>
        cases xs with
        | nil =>
            simp at h
        | cons y ys =>
            simp at h
            rcases ih h with ⟨lo, hi, hys, hlen⟩
            refine ⟨y :: lo, hi, ?_, ?_⟩
            · simp [hys]
            · simp [hlen]
  · rintro ⟨lo, hi, rfl, hlen⟩
    have hget : (lo ++ x :: hi)[lo.length]? = some x := by
      induction lo with
      | nil =>
          simp
      | cons _ lo ih =>
          simp
    rw [← hlen]
    exact hget

theorem pairwise_split_bounds {lo hi : List Nat} {x : Nat}
    (h : (lo ++ x :: hi).Pairwise (fun x y => x ≤ y)) :
    (∀ y ∈ lo, y ≤ x) ∧ (∀ y ∈ hi, x ≤ y) := by
  rcases (List.pairwise_append.mp h) with ⟨_, hxhi, hcross⟩
  constructor
  · intro y hy
    exact hcross y hy x (by simp)
  · cases hxhi with
    | cons hhead _ =>
        intro y hy
        exact hhead y hy

theorem ltCount_eq_of_perm {xs ys : List Nat} {x : Nat}
    (h : xs.Perm ys) :
    ltCount x xs = ltCount x ys := by
  unfold ltCount
  exact (h.filter (fun y => decide (y < x))).length_eq

theorem leCount_eq_of_perm {xs ys : List Nat} {x : Nat}
    (h : xs.Perm ys) :
    leCount x xs = leCount x ys := by
  unfold leCount
  exact (h.filter (fun y => decide (y ≤ x))).length_eq

theorem ltCount_le_of_sorted_split {ys lo hi : List Nat} {x : Nat}
    (hsplit : ys = lo ++ x :: hi)
    (_hlo : ∀ y ∈ lo, y ≤ x)
    (hhi : ∀ y ∈ hi, x ≤ y) :
    ltCount x ys ≤ lo.length := by
  subst ys
  unfold ltCount
  have hhi_empty :
      hi.filter (fun y => decide (y < x)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro y hy
    simp [not_lt_of_ge (hhi y hy)]
  have hfilter :
      (lo ++ x :: hi).filter (fun y => decide (y < x)) =
        lo.filter (fun y => decide (y < x)) := by
    rw [List.filter_append]
    simp [hhi_empty]
  rw [hfilter]
  exact List.length_filter_le (fun y => decide (y < x)) lo

theorem lt_length_leCount_of_sorted_split {ys lo hi : List Nat} {x : Nat}
    (hsplit : ys = lo ++ x :: hi)
    (hlo : ∀ y ∈ lo, y ≤ x)
    (_hhi : ∀ y ∈ hi, x ≤ y) :
    lo.length < leCount x ys := by
  subst ys
  unfold leCount
  have hlo_self :
      lo.filter (fun y => decide (y ≤ x)) = lo := by
    rw [List.filter_eq_self]
    intro y hy
    simp [hlo y hy]
  have hfilter :
      (lo ++ x :: hi).filter (fun y => decide (y ≤ x)) =
        lo ++ x :: hi.filter (fun y => decide (y ≤ x)) := by
    rw [List.filter_append]
    simp [hlo_self]
  rw [hfilter]
  simp

/-! ## Selection correctness -/

theorem selectByRank?_rankCorrect {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : selectByRank? k xs = some x) :
    RankCertificate xs k x := by
  unfold selectByRank? at hsel
  rcases (getElem?_eq_some_iff_split.mp hsel) with
    ⟨lo, hi, hsplit, hlen⟩
  have hpair :
      (lo ++ x :: hi).Pairwise (fun x y => x ≤ y) := by
    rw [← hsplit]
    exact sortedCopy_pairwise xs
  rcases pairwise_split_bounds hpair with ⟨hlo, hhi⟩
  have hxSorted : x ∈ sortedCopy xs := by
    rw [hsplit]
    simp
  have hperm : (sortedCopy xs).Perm xs := sortedCopy_perm xs
  refine ⟨(hperm.mem_iff.mp hxSorted), ?_, ?_⟩
  · have hltSorted :
        ltCount x (sortedCopy xs) ≤ lo.length :=
      ltCount_le_of_sorted_split hsplit hlo hhi
    have hltEq : ltCount x (sortedCopy xs) = ltCount x xs :=
      ltCount_eq_of_perm hperm
    rw [← hltEq, ← hlen]
    exact hltSorted
  · have hleSorted :
        lo.length < leCount x (sortedCopy xs) :=
      lt_length_leCount_of_sorted_split hsplit hlo hhi
    have hleEq : leCount x (sortedCopy xs) = leCount x xs :=
      leCount_eq_of_perm hperm
    rw [← hleEq, ← hlen]
    exact hleSorted

theorem selectByRank?_mem {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : selectByRank? k xs = some x) :
    x ∈ xs :=
  (selectByRank?_rankCorrect hsel).1

/-- Reader-facing correctness wrapper for the specification selector. -/
theorem selectByRank?_correct {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : selectByRank? k xs = some x) :
    RankCertificate xs k x :=
  selectByRank?_rankCorrect hsel

end Chapter09
end CLRS
