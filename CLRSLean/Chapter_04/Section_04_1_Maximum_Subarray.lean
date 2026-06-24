import Mathlib.Tactic

/-!
# 4.1. The Maximum-Subarray Problem

This file gives the first Lean model for CLRS Section 4.1.  The textbook
problem asks for a nonempty contiguous subarray of maximum sum.  We model the
input as a list of integer daily changes, enumerate all nonempty contiguous
subarrays, and choose a candidate with maximum sum.

The current executable selector is intentionally simple: it is an exhaustive
finite search, not yet the divide-and-conquer implementation from the
pseudocode.  This gives a clean specification and proof target for later
refinement: a future divide-and-conquer implementation should return the same
kind of optimal certificate.

Main results:

- Theorem {lit}`mem_nonemptySubarrays_iff`: the candidate enumerator contains
  exactly the nonempty contiguous subarrays.
- Theorem {lit}`bestCandidate_correct`: the generic finite argmax selector
  returns a member whose sum is at least every listed candidate.
- Theorem {lit}`maxSubarray_exists_of_ne_nil`: nonempty inputs have a selected
  maximum-subarray candidate.
- Theorem {lit}`maxSubarray_correct`: the executable maximum-subarray selector
  returns a nonempty contiguous subarray whose sum is maximal among all
  nonempty contiguous subarrays.

Current gaps:

- The divide-and-conquer CLRS pseudocode is not yet proved as an implementation
  refinement of this specification.
- Runtime and RAM-cost analysis are future strengthening targets.
-/

namespace CLRS
namespace Chapter04

/-! ## Contiguous subarrays -/

/-- The sum of a candidate subarray. -/
def subarraySum (xs : List Int) : Int := xs.sum

/--
{lit}`pre` is a nonempty prefix of {lit}`xs`.

This is a specification predicate; the executable enumerator below is proved
equivalent to it.
-/
def IsNonemptyPrefix (pre xs : List Int) : Prop :=
  pre ≠ [] ∧ ∃ rest, xs = pre ++ rest

/--
{lit}`sub` is a nonempty contiguous subarray of {lit}`xs`.

The witnesses are the elements before and after the contiguous segment.
-/
def IsNonemptySubarray (sub xs : List Int) : Prop :=
  sub ≠ [] ∧ ∃ before after, xs = before ++ sub ++ after

/-- Enumerate all nonempty prefixes of a list. -/
def nonemptyPrefixes : List Int → List (List Int)
  | [] => []
  | x :: xs => [x] :: (nonemptyPrefixes xs).map (fun pre => x :: pre)

/-- Enumerate all nonempty contiguous subarrays of a list. -/
def nonemptySubarrays : List Int → List (List Int)
  | [] => []
  | x :: xs => nonemptyPrefixes (x :: xs) ++ nonemptySubarrays xs

/-- The prefix enumerator is exact. -/
theorem mem_nonemptyPrefixes_iff {pre xs : List Int} :
    pre ∈ nonemptyPrefixes xs ↔ IsNonemptyPrefix pre xs := by
  induction xs generalizing pre with
  | nil =>
      simp [nonemptyPrefixes, IsNonemptyPrefix]
  | cons x xs ih =>
      constructor
      · intro h
        simp [nonemptyPrefixes] at h
        rcases h with hSingle | hMap
        · subst pre
          exact ⟨by simp, ⟨xs, rfl⟩⟩
        · rcases hMap with ⟨tail, htail, rfl⟩
          rcases ih.mp htail with ⟨_htailNonempty, rest, htailEq⟩
          exact ⟨by simp, ⟨rest, by simp [htailEq]⟩⟩
      · intro h
        rcases h with ⟨hpreNonempty, rest, hEq⟩
        cases pre with
        | nil =>
            exact False.elim (hpreNonempty rfl)
        | cons y ys =>
            simp [List.cons_append] at hEq
            rcases hEq with ⟨hxy, htail⟩
            subst y
            cases ys with
            | nil =>
                simp [nonemptyPrefixes]
            | cons z zs =>
                have htailMem : (z :: zs) ∈ nonemptyPrefixes xs := by
                  exact ih.mpr ⟨by simp, ⟨rest, htail⟩⟩
                simp [nonemptyPrefixes, htailMem]

/-- The contiguous-subarray enumerator is exact. -/
theorem mem_nonemptySubarrays_iff {sub xs : List Int} :
    sub ∈ nonemptySubarrays xs ↔ IsNonemptySubarray sub xs := by
  induction xs generalizing sub with
  | nil =>
      simp [nonemptySubarrays, IsNonemptySubarray]
  | cons x xs ih =>
      constructor
      · intro h
        simp [nonemptySubarrays] at h
        rcases h with hPrefix | hTail
        · rcases mem_nonemptyPrefixes_iff.mp hPrefix with
            ⟨hsubNonempty, rest, hPrefixEq⟩
          exact ⟨hsubNonempty, ⟨[], rest, by simp [hPrefixEq]⟩⟩
        · rcases ih.mp hTail with ⟨hsubNonempty, before, after, hEq⟩
          exact ⟨hsubNonempty, ⟨x :: before, after, by simp [hEq]⟩⟩
      · intro h
        rcases h with ⟨hsubNonempty, before, after, hEq⟩
        simp [nonemptySubarrays]
        cases before with
        | nil =>
            left
            exact mem_nonemptyPrefixes_iff.mpr
              ⟨hsubNonempty, ⟨after, by simpa using hEq⟩⟩
        | cons y beforeTail =>
            right
            simp [List.cons_append] at hEq
            rcases hEq with ⟨_hy, htail⟩
            exact ih.mpr
              ⟨hsubNonempty, ⟨beforeTail, after, by
                simpa [List.append_assoc] using htail⟩⟩

/-! ## Finite argmax -/

/-- Choose the candidate with greater sum, breaking ties toward the first one. -/
def betterCandidate (a b : List Int) : List Int :=
  if subarraySum a < subarraySum b then b else a

/-- A finite maximum-by-sum selector for a list of candidates. -/
def bestCandidate : List (List Int) → Option (List Int)
  | [] => none
  | cand :: rest =>
      match bestCandidate rest with
      | none => some cand
      | some best => some (betterCandidate cand best)

/--
The finite selector returns an element of the candidate list whose sum is at
least every candidate sum.
-/
theorem bestCandidate_correct {candidates : List (List Int)} {best : List Int}
    (hbest : bestCandidate candidates = some best) :
    best ∈ candidates ∧
      ∀ cand, cand ∈ candidates → subarraySum cand ≤ subarraySum best := by
  induction candidates generalizing best with
  | nil =>
      simp [bestCandidate] at hbest
  | cons cand rest ih =>
      simp [bestCandidate] at hbest
      cases hrest : bestCandidate rest with
      | none =>
          have hrestNil : rest = [] := by
            cases rest with
            | nil => rfl
            | cons restCand restTail =>
                cases htail : bestCandidate restTail <;>
                  simp [bestCandidate, htail] at hrest
          simp [hrest] at hbest
          subst best
          subst rest
          constructor
          · simp
          · intro other hother
            simp at hother
            subst other
            exact le_rfl
      | some restBest =>
          simp [hrest] at hbest
          have hrestCorrect := ih hrest
          by_cases hlt : subarraySum cand < subarraySum restBest
          · simp [betterCandidate, hlt] at hbest
            subst best
            constructor
            · simp [hrestCorrect.1]
            · intro other hother
              simp at hother
              rcases hother with hsame | hinRest
              · subst other
                exact le_of_lt hlt
              · exact hrestCorrect.2 other hinRest
          · simp [betterCandidate, hlt] at hbest
            subst best
            constructor
            · simp
            · intro other hother
              simp at hother
              rcases hother with hsame | hinRest
              · subst other
                exact le_rfl
              · exact le_trans (hrestCorrect.2 other hinRest) (le_of_not_gt hlt)

/-- Every nonempty candidate list has a selected best candidate. -/
theorem bestCandidate_exists_of_ne_nil {candidates : List (List Int)}
    (hcandidates : candidates ≠ []) :
    ∃ best, bestCandidate candidates = some best := by
  cases candidates with
  | nil =>
      exact False.elim (hcandidates rfl)
  | cons cand rest =>
      simp [bestCandidate]
      cases hrest : bestCandidate rest with
      | none =>
          exact ⟨cand, rfl⟩
      | some restBest =>
          exact ⟨betterCandidate cand restBest, rfl⟩

/-! ## Maximum-subarray selector -/

/--
Exhaustively choose a maximum-sum nonempty contiguous subarray.  Empty inputs
have no nonempty candidate and therefore return {lit}`none`.
-/
def maxSubarray (xs : List Int) : Option (List Int) :=
  bestCandidate (nonemptySubarrays xs)

/-- The selector returns {lit}`none` on the empty input. -/
theorem maxSubarray_nil :
    maxSubarray [] = none := by
  rfl

/-- Nonempty inputs have at least one nonempty contiguous-subarray candidate. -/
theorem maxSubarray_exists_of_ne_nil {xs : List Int} (hxs : xs ≠ []) :
    ∃ best, maxSubarray xs = some best := by
  cases xs with
  | nil =>
      exact False.elim (hxs rfl)
  | cons x xs =>
      unfold maxSubarray
      apply bestCandidate_exists_of_ne_nil
      simp [nonemptySubarrays, nonemptyPrefixes]

/--
Correctness of the maximum-subarray selector: whenever it returns a candidate,
that candidate is a nonempty contiguous subarray and has maximum sum among all
nonempty contiguous subarrays of the input.
-/
theorem maxSubarray_correct {xs best : List Int}
    (hbest : maxSubarray xs = some best) :
    IsNonemptySubarray best xs ∧
      ∀ cand, IsNonemptySubarray cand xs →
        subarraySum cand ≤ subarraySum best := by
  unfold maxSubarray at hbest
  rcases bestCandidate_correct hbest with ⟨hbestMem, hbestOptimal⟩
  constructor
  · exact mem_nonemptySubarrays_iff.mp hbestMem
  · intro cand hcand
    exact hbestOptimal cand (mem_nonemptySubarrays_iff.mpr hcand)

end Chapter04
end CLRS
