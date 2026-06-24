import Mathlib.Tactic

open Finset
open scoped BigOperators

/-!
# 4.5. The Master Method - Exact Powers

This file keeps the compiler-clean core of the Chapter 4 Master Theorem track.
For recurrences on exact powers,
`T(b^(i+1)) = a * T(b^i) + f(b^(i+1))`, the normalized quantity
`T(b^i) / a^i` unfolds into the initial value plus a finite sum of normalized
forcing terms.

Main result:

- Theorem {lit}`CLRS.Chapter04.h_formula`: the normalized exact-power
  recurrence expansion.

Current gaps:

- The three full Master Theorem cases are not yet mechanized.  They need a
  cleaner asymptotic bridge from `f(n) = Θ(n^d)` to finite sums over powers and
  a robust geometric-sum library layer.  Until those proofs compile, this
  section remains `partial`.
-/

namespace CLRS
namespace Chapter04

/-! ## Exact-power recurrences -/

/-- Exact-power form of the CLRS Master Theorem recurrence. -/
structure ExactPowerRecurrence (a b : ℕ) (f T : ℕ → ℝ) : Prop where
  step : ∀ i : ℕ, T (b ^ (i + 1)) = (a : ℝ) * T (b ^ i) + f (b ^ (i + 1))

/-! ## Public theorem -/

/--
Unroll the exact-power recurrence after dividing by {lit}`a^i`.

This is the algebraic spine of the Master Theorem proof: the remaining CLRS
case analysis is a question about bounding the finite sum on the right-hand
side.
-/
theorem h_formula (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : ExactPowerRecurrence a b f T) (ha_ne_zero : (a : ℝ) ≠ 0)
    (i : ℕ) :
    T (b ^ i) / ((a : ℝ) ^ i) =
      T (b ^ 0) / ((a : ℝ) ^ 0) +
        (∑ k ∈ range i, f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1))) := by
  induction' i with i ih
  · simp
  · rw [show
        T (b ^ (i + 1)) / ((a : ℝ) ^ (i + 1)) =
          T (b ^ i) / ((a : ℝ) ^ i) +
            f (b ^ (i + 1)) / ((a : ℝ) ^ (i + 1)) by
        field_simp [ha_ne_zero, pow_succ]
        rw [h_rec.step i]
        ring]
    rw [ih]
    simp [sum_range_succ, add_assoc]

end Chapter04
end CLRS
