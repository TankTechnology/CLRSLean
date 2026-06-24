import Mathlib

open Finset
open scoped BigOperators

/-!
# 5.1. The Hiring Problem

This file proves the finite symmetry calculation behind the CLRS hiring
problem.  At step `n+1`, the new candidate is hired exactly when the best among
the first `n+1` candidates is in the new candidate's position.  Under the
uniform rank model, that event has probability `1/(n+1)`.  Summing these
indicator expectations gives the harmonic number.

Main result:

- Theorem {lit}`CLRS.Chapter05.uniformAverage_indicator_singleton`: a singleton
  event in a finite uniform space has probability `1/m`.
- Theorem {lit}`CLRS.Chapter05.hireProbability_eq`: the hire probability at
  step `n+1` is `1/(n+1)`.
- Theorem {lit}`CLRS.Chapter05.expectedHiresByIndicators_eq_harmonic`: summing
  the indicator expectations gives the harmonic number.
- Theorem {lit}`CLRS.Chapter05.expectedHires_eq_harmonic`: the equivalent
  recurrence solution equals the harmonic number.

Current gaps:

- The logarithmic asymptotic bounds for harmonic numbers are future work for a
  stronger Chapter 5 pass.
-/

namespace CLRS
namespace Chapter05

/-! ## Finite uniform expectation model -/

/-- Uniform average over the finite sample space `{0, ..., m-1}`. -/
noncomputable def uniformAverageRange (m : ℕ) (X : ℕ → ℝ) : ℝ :=
  (∑ i ∈ range m, X i) / (m : ℝ)

/-- A `0/1` indicator as a real-valued random variable. -/
def indicator (P : Prop) [Decidable P] : ℝ :=
  if P then 1 else 0

/-- In a finite uniform space of size `m`, a singleton event has probability `1/m`. -/
theorem uniformAverage_indicator_singleton {m j : ℕ} (hj : j ∈ range m) :
    uniformAverageRange m (fun i => indicator (i = j)) = 1 / (m : ℝ) := by
  classical
  have hsum : (∑ i ∈ range m, indicator (i = j)) = (1 : ℝ) := by
    rw [Finset.sum_eq_single j]
    · simp [indicator]
    · intro b _hb hbj
      simp [indicator, hbj]
    · intro hj_not
      exact (hj_not hj).elim
  simp [uniformAverageRange, hsum]

/-! ## Hiring probabilities from symmetry -/

/--
At step `n+1`, index `n` is the new candidate's position in a rank-symmetry
sample space of size `n+1`.
-/
def newCandidateIsBest (n rankOfBest : ℕ) : Prop :=
  rankOfBest = n

instance newCandidateIsBestDecidable (n rankOfBest : ℕ) :
    Decidable (newCandidateIsBest n rankOfBest) :=
  inferInstanceAs (Decidable (rankOfBest = n))

/-- The probability that the new candidate is the best among the first `n+1`. -/
noncomputable def hireProbability (n : ℕ) : ℝ :=
  uniformAverageRange (n + 1) (fun rankOfBest => indicator (rankOfBest = n))

/-- The single-step hiring probability is `1/(n+1)` by finite symmetry. -/
theorem hireProbability_eq (n : ℕ) :
    hireProbability n = 1 / ((n : ℝ) + 1) := by
  classical
  have hn_mem : n ∈ range (n + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_self n
  have hsingleton :=
    uniformAverage_indicator_singleton (m := n + 1) (j := n) hn_mem
  simpa [hireProbability, Nat.cast_add, Nat.cast_one] using hsingleton

/-! ## Harmonic numbers -/

/-- The {lit}`n`-th harmonic number, written as `Σ_{i=0}^{n-1} 1/(i+1)`. -/
noncomputable def harmonic (n : ℕ) : ℝ :=
  ∑ i ∈ range n, 1 / ((i : ℝ) + 1)

@[simp] lemma harmonic_zero : harmonic 0 = 0 := by
  simp [harmonic]

/-- Successor recurrence for harmonic numbers. -/
lemma harmonic_succ (n : ℕ) :
    harmonic (n + 1) = harmonic n + 1 / ((n : ℝ) + 1) := by
  simp [harmonic, sum_range_succ]

/-- Harmonic numbers are positive once the index is positive. -/
lemma harmonic_pos {n : ℕ} (hn : 0 < n) : 0 < harmonic n := by
  refine Finset.sum_pos (fun i _ => div_pos (by norm_num) (by positivity)) ?_
  rw [Finset.nonempty_range_iff]
  exact Nat.ne_of_gt hn

/-! ## Expected number of hires -/

/-- Expected hires as a sum of indicator expectations. -/
noncomputable def expectedHiresByIndicators (n : ℕ) : ℝ :=
  ∑ i ∈ range n, hireProbability i

/-- Linearity of expectation reduces the hiring problem to the harmonic sum. -/
theorem expectedHiresByIndicators_eq_harmonic (n : ℕ) :
    expectedHiresByIndicators n = harmonic n := by
  unfold expectedHiresByIndicators harmonic
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact hireProbability_eq i

/--
Expected number of hires from {lit}`n` candidates, assuming the CLRS recurrence
obtained from the finite rank-symmetry argument.
-/
noncomputable def expectedHires : ℕ → ℝ
  | 0 => 0
  | n + 1 => expectedHires n + 1 / ((n : ℝ) + 1)

/-- The expected-hire recurrence has the harmonic-number closed form. -/
theorem expectedHires_eq_harmonic (n : ℕ) : expectedHires n = harmonic n := by
  induction' n with n ih
  · simp [expectedHires]
  · rw [expectedHires, harmonic_succ, ih]

/-- The recurrence and indicator-sum views of the expected hires agree. -/
theorem expectedHires_eq_expectedHiresByIndicators (n : ℕ) :
    expectedHires n = expectedHiresByIndicators n := by
  rw [expectedHires_eq_harmonic, expectedHiresByIndicators_eq_harmonic]

end Chapter05
end CLRS
