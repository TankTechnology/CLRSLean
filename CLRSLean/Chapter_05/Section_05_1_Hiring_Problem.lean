import Mathlib

open Finset
open scoped BigOperators

/-!
# 5.1. The Hiring Problem

This file contains the compiler-clean deterministic recurrence layer for the
CLRS hiring problem.  If {lit}`h(n)` denotes the expected number of hires after {lit}`n`
candidates and the probabilistic symmetry argument gives
`h(n+1) = h(n) + 1/(n+1)`, then the unique recurrence solution is the harmonic
number.

Main result:

- Theorem {lit}`CLRS.Chapter05.expectedHires_eq_harmonic`: the recurrence
  solution equals the harmonic number.

Current gaps:

- The probability space over random permutations and the indicator-variable
  expectation proof are not yet formalized.
- The logarithmic asymptotic bounds for harmonic numbers are future work for a
  stronger Chapter 5 pass.
-/

namespace CLRS
namespace Chapter05

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

/--
Expected number of hires from {lit}`n` candidates, assuming the CLRS recurrence
obtained from the permutation-symmetry argument.
-/
noncomputable def expectedHires : ℕ → ℝ
  | 0 => 0
  | n + 1 => expectedHires n + 1 / ((n : ℝ) + 1)

/-- The expected-hire recurrence has the harmonic-number closed form. -/
theorem expectedHires_eq_harmonic (n : ℕ) : expectedHires n = harmonic n := by
  induction' n with n ih
  · simp [expectedHires]
  · rw [expectedHires, harmonic_succ, ih]

end Chapter05
end CLRS
