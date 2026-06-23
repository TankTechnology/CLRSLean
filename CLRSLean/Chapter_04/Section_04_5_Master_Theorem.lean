import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import Mathlib.Tactic

open Real Filter Asymptotics Finset

/-!
# 4.5. The Master Method — Exact Powers, Case 1

Proves Case 1 of the Master Theorem for `T(bⁱ⁺¹) = a·T(bⁱ) + f(bⁱ⁺¹)`:

**Case 1** (`b^d < a`).  If `f(n) = Θ(n^d)`, then `T(bⁱ) = Θ(aⁱ)`.
(equivalently, `T(n) = Θ(n^{log_b(a)})` when `n = bⁱ`).

Cases 2 (`b^d = a`) and 3 (`b^d > a`) are analogous, using harmonic-series
and dominant-term estimates respectively.  The method — divide by `aⁱ` and
bound the resulting sum — works uniformly for all three cases.
-/

namespace CLRS
namespace Chapter04

open Chapter03

structure ExactPowerRecurrence (a b : ℕ) (f T : ℕ → ℝ) : Prop where
  step : ∀ i : ℕ, T (b ^ (i + 1)) = (a : ℝ) * T (b ^ i) + f (b ^ (i + 1))

lemma h_formula (a b : ℕ) (f T : ℕ → ℝ) (h_rec : ExactPowerRecurrence a b f T)
    (ha_pos : (a : ℝ) ≠ 0) (i : ℕ) :
    T (b ^ i) / ((a : ℝ) ^ i) = T (b ^ 0) / ((a : ℝ) ^ 0) +
      (∑ k in range i, f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1))) := by
  induction' i with i IH
  · simp
  · rw [show T (b ^ (i + 1)) / ((a : ℝ) ^ (i + 1))
        = (T (b ^ i) / ((a : ℝ) ^ i)) + f (b ^ (i + 1)) / ((a : ℝ) ^ (i + 1)) by
      field_simp [ha_pos, pow_succ]; rw [h_rec.step i]; ring]
    rw [IH]; simp [sum_range_succ, add_assoc]

/--
**Case 1 of the Master Theorem (exact powers).**

Assumptions:
* `a ≥ 1`, `b > 1`, `d ≥ 0` are integers
* `T(bⁱ⁺¹) = a·T(bⁱ) + f(bⁱ⁺¹)`  (exact-powers recurrence)
* `f(n) = Θ(n^d)`  (for `n = bⁱ`)
* `b^d < a`  (the Case 1 condition)

Conclusion:  `T(bⁱ) = Θ(aⁱ)`.

**Proof.**  Set `r := b^d / a < 1`.  From the recurrence divided by `aⁱ⁺¹`:
`h(i) := T(bⁱ)/aⁱ` satisfies `h(i+1) = h(i) + f(bⁱ⁺¹)/aⁱ⁺¹`.

Since `f(bⁱ⁺¹) = Θ((bⁱ⁺¹)^d)` and `(bⁱ⁺¹)^d/aⁱ⁺¹ = rⁱ⁺¹`, we have
`f(bⁱ⁺¹)/aⁱ⁺¹ = Θ(rⁱ⁺¹)`.  Because `r < 1`, the series `Σ rᵏ` converges.
Hence `h(i) = h(0) + Σ_{k=1}^i Θ(rᵏ) = Θ(1)`.  Multiplying by `aⁱ` gives
`T(bⁱ) = Θ(aⁱ)`.

The formal proof constructs a uniform constant `K` such that
`h(i) ≤ K` for all `i` (O-bound) and `c > 0` such that `h(i) ≥ c` (Ω-bound),
using the `Θ(n^d)` bounds on `f`.
-/
theorem master_case1 (a b d : ℕ) (ha : 1 ≤ a) (hb : 1 < b)
    (f T : ℕ → ℝ) (h_rec : ExactPowerRecurrence a b f T)
    (h_f_theta : isBigTheta f (fun n : ℕ => (n : ℝ) ^ (d : ℕ)))
    (h_nonneg_T : ∀ i, 0 ≤ T (b ^ i))
    (h_nonneg_f : ∀ n, 0 ≤ f n)
    (h_T0_pos : 0 < T (b ^ 0))
    (h_cond : (b : ℕ) ^ d < a) :
    isBigTheta (fun i : ℕ => T (b ^ i)) (fun i : ℕ => ((a : ℝ) ^ i)) := by
  have ha_pos : (a : ℝ) > 0 := by exact_mod_cast (Nat.one_le_of_lt (by omega : 0 < a))
  have ha_ne_zero : (a : ℝ) ≠ 0 := by linarith
  let r := ((b : ℝ) ^ (d : ℕ)) / (a : ℝ)
  have hr_lt_one : r < 1 := (div_lt_one ha_pos).mpr (by exact mod_cast h_cond)
  have hr_nonneg : 0 ≤ r := div_nonneg (by positivity) (by positivity)
  have h_geom_sum : (∑' k : ℕ, r ^ (k + 1)) = r / (1 - r) := by
    calc
      (∑' k : ℕ, r ^ (k + 1)) = (∑' k : ℕ, r ^ k * r) := by
        refine tsum_congr (fun k => ?_); rw [pow_succ]
      _ = (∑' k : ℕ, r ^ k) * r := by rw [tsum_mul_right]
      _ = (1 / (1 - r)) * r := by
        rw [tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr_nonneg])]
      _ = r / (1 - r) := by ring

  -- From f = Θ(n^d), get both upper and lower bounds:
  -- ∃ C₁, C₂ > 0, N, such that ∀ n ≥ N: C₁·n^d ≤ f(n) ≤ C₂·n^d
  rcases h_f_theta with ⟨h_f_O, h_f_Omega⟩
  rcases h_f_O.exists_pos with ⟨C2, hC2_pos, hC2⟩
  rcases h_f_Omega.exists_pos with ⟨C1, hC1_pos, hC1⟩
  have hC1_uniform : ∀ᶠ (n : ℕ) in atTop, C1 * ((n : ℝ) ^ (d : ℕ)) ≤ f n := by
    filter_upwards [hC1] with n hn
    have h0 : 0 ≤ (n : ℝ) ^ (d : ℕ) := pow_nonneg (Nat.cast_nonneg _) _
    simpa [abs_of_nonneg (h_nonneg_f n), abs_of_nonneg h0, mul_comm] using hn
  rw [Filter.eventually_atTop] at hC1_uniform
  rcases hC1_uniform with ⟨N1, hN1⟩
  have hC2_uniform : ∀ᶠ (n : ℕ) in atTop, f n ≤ C2 * ((n : ℝ) ^ (d : ℕ)) := by
    filter_upwards [hC2] with n hn
    have h0 : 0 ≤ (n : ℝ) ^ (d : ℕ) := pow_nonneg (Nat.cast_nonneg _) _
    simpa [abs_of_nonneg (h_nonneg_f n), abs_of_nonneg h0] using hn
  rw [Filter.eventually_atTop] at hC2_uniform
  rcases hC2_uniform with ⟨N2, hN2⟩
  let N := max N1 N2

  -- Construct a universal constant C' such that ∀k, f(b^{k+1})/a^{k+1} ≤ C'·r^{k+1}
  -- For k < N: use the finite max of f(b^{k+1})/(a^{k+1}·r^{k+1}).
  -- For k ≥ N: C2 suffices since f(b^{k+1}) ≤ C2·(b^{k+1})^d = C2·a^{k+1}·r^{k+1}
  let C' := max C2 ((range N).sup' (by simp)
    (fun k => f (b ^ (k + 1)) / (((a : ℝ) ^ (k + 1)) * (r ^ (k + 1)))))
  have hC'_ge_C2 : C2 ≤ C' := le_max_left _ _
  have hC'_universal : ∀ k : ℕ, f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1)) ≤ C' * (r ^ (k + 1)) := by
    intro k
    by_cases hk : k < N
    · -- k < N: use the finite supremum
      have hk' := Finset.le_sup' (fun j =>
          f (b ^ (j + 1)) / (((a : ℝ) ^ (j + 1)) * (r ^ (j + 1)))) (mem_range.2 hk)
      have hk_bound : f (b ^ (k + 1)) / (((a : ℝ) ^ (k + 1)) * (r ^ (k + 1))) ≤ C' :=
        le_trans hk' (le_max_right _ _)
      -- Rearrange: f/(a^{k+1}·r^{k+1}) ≤ C' → f/a^{k+1} ≤ C'·r^{k+1}
      rcases eq_or_ne (r ^ (k + 1)) 0 with (hz | hnz)
      · -- r^{k+1} = 0 implies r = 0, so r < 1 holds trivially
        have hzz : f (b ^ (k + 1)) = 0 := by
          -- from hC2_bound, if b^{k+1} ≥ N2 then 0 ≤ f ≤ C2·(b^{k+1})^d
          -- If r = 0 then b^d = 0, impossible since b > 0
          -- Actually if b^d / a = 0 then b^d = 0 which is impossible for b > 0
          have : (b : ℝ) ^ (d : ℕ) > 0 := pow_pos (by exact_mod_cast (Nat.zero_lt_of_lt hb)) _
          linarith [hr_nonneg, hr_lt_one, this]
        simp [hzz, hz]
      · -- r^{k+1} > 0, can multiply through
        have hpos : 0 < r ^ (k + 1) := by
          apply pow_pos
          -- r ≠ 0, since r^{k+1} ≠ 0.  Also hr_nonneg ≥ 0, so r > 0
          have hr_pos : 0 < r := by
            by_contra! H
            have : r = 0 := by linarith
            subst this
            simp at hnz
          exact hr_pos
        have hk_bound' : f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1)) ≤ C' * (r ^ (k + 1)) := by
          -- From hk_bound: f/(a^{k+1}·r^{k+1}) ≤ C'
          -- Multiply both sides by r^{k+1}: f/a^{k+1} ≤ C'·r^{k+1}
          field_simp [hpos.ne']
          nlinarith [hk_bound, hpos]
        exact hk_bound'
    · -- k ≥ N: use the O(n^d) bound hN2
      have h_bpow_ge_N2 : N2 ≤ b ^ (k + 1) := by
        -- b ≥ 2, so b^{k+1} ≥ 2^{k+1} ≥ k+1 ≥ N (since k ≥ N ≥ N2)
        have hk_succ_le_2pow : (k + 1 : ℕ) ≤ 2 ^ (k + 1) := by
          induction' k with j IH; · norm_num
          rw [Nat.pow_succ]; omega
        have h2_b : 2 ≤ b := by omega
        calc
          N2 ≤ N := le_max_right _ _
          _ ≤ k := by omega
          _ < k + 1 := by omega
          _ ≤ 2 ^ (k + 1) := hk_succ_le_2pow
          _ ≤ b ^ (k + 1) := Nat.pow_le_pow_right (by omega) h2_b
      have h_fb := hN2 (b ^ (k + 1)) h_bpow_ge_N2
      calc
        f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1))
            ≤ (C2 * (((b : ℝ) ^ (k + 1)) ^ (d : ℕ))) / ((a : ℝ) ^ (k + 1)) := by
          refine (div_le_div_right (by positivity)).mpr h_fb
        _ = C2 * ((((b : ℝ) ^ (d : ℕ)) / (a : ℝ)) ^ (k + 1)) := by
          simp [div_pow, mul_div_assoc, pow_mul]
        _ = C2 * (r ^ (k + 1)) := rfl
        _ ≤ C' * (r ^ (k + 1)) := by gcongr

  -- Now the universal bound: ∀ i, h(i) = T(bⁱ)/aⁱ ≤ T(1) + C'·r/(1-r) =: K
  have h_O : isBigO (fun i : ℕ => T (b ^ i)) (fun i : ℕ => ((a : ℝ) ^ i)) := by
    let K := T (b ^ 0) / ((a : ℝ) ^ 0) + C' * (r / (1 - r))
    have hK : ∀ i : ℕ, T (b ^ i) / ((a : ℝ) ^ i) ≤ K := by
      intro i
      rw [h_formula a b f T h_rec ha_ne_zero i, div_one]
      -- Need: T(b^0) + Σ_{k< i} f(b^{k+1})/a^{k+1} ≤ T(b^0) + C'·r/(1-r)
      -- Cancel T(b^0): Σ_{k< i} f(b^{k+1})/a^{k+1} ≤ C'·r/(1-r)
      -- From universal bound: each term ≤ C'·r^{k+1}
      -- So Σ ≤ C'·Σ_{k< i} r^{k+1} ≤ C'·Σ_{k} r^{k+1} = C'·r/(1-r)
      calc
        T (b ^ 0) + (∑ k in range i, f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1)))
            ≤ T (b ^ 0) + (∑ k in range i, C' * (r ^ (k + 1))) := by
          gcongr; exact hC'_universal k
        _ = T (b ^ 0) + C' * (∑ k in range i, r ^ (k + 1)) := by simp [Finset.mul_sum]
        _ ≤ T (b ^ 0) + C' * (∑' k : ℕ, r ^ (k + 1)) := by
          gcongr
          refine sum_le_tsum _ (fun _ _ => pow_nonneg hr_nonneg _) ?_
          -- The series converges because r < 1
          exact summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr_nonneg])
        _ = T (b ^ 0) + C' * (r / (1 - r)) := by rw [h_geom_sum]
    refine Asymptotics.isBigO_of_le' atTop (fun i => ?_)
    have h := hK i
    calc
      T (b ^ i) = ((a : ℝ) ^ i) * (T (b ^ i) / ((a : ℝ) ^ i)) := by field_simp [ha_ne_zero]
      _ ≤ ((a : ℝ) ^ i) * K := by gcongr

  -- Ω-bound: T(bⁱ) = Ω(aⁱ).
  -- From the recurrence and nonnegativity of f:
  --   T(b^{i+1}) = a·T(bⁱ) + f(b^{i+1}) ≥ a·T(bⁱ)
  -- Hence T(bⁱ) ≥ aⁱ·T(b⁰).  Since T(b⁰) > 0, we get T(bⁱ) = Ω(aⁱ).
  have h_Omega : isBigOmega (fun i : ℕ => T (b ^ i)) (fun i : ℕ => ((a : ℝ) ^ i)) := by
    have h_ge : ∀ i, T (b ^ i) ≥ ((a : ℝ) ^ i) * T (b ^ 0) := by
      intro i
      induction' i with k IH
      · simp
      · rw [h_rec.step k]
        have : T (b ^ (k + 1)) = (a : ℝ) * T (b ^ k) + f (b ^ (k + 1)) := h_rec.step k
        nlinarith [h_nonneg_f (b ^ (k + 1)), IH]
    refine Asymptotics.isBigO_of_le' atTop (fun i => ?_)
    have h := h_ge i
    -- h: T(bⁱ) ≥ aⁱ·T(b⁰)
    -- Need: T(bⁱ) ≥ c·aⁱ for some c > 0.  Take c = T(b⁰)/2 (or just T(b⁰))
    -- Actually the definition of isBigOmega uses ∃ c>0, eventually |f| ≥ c·|g|
    -- With f = T(bⁱ), g = aⁱ.  Since both are nonnegative:
    -- T(bⁱ) ≥ T(b⁰)·aⁱ, and T(b⁰) > 0, so we can take c = T(b⁰).
    -- But the definition wants: ∃ c>0, ∀ᶠ i in atTop, T(bⁱ) ≥ c·aⁱ
    -- That's exactly h with c = T(b⁰) > 0, for ALL i.
    -- So we just need to massage h into the right shape.
    rcases h_T0_pos with hpos
    -- Actually h_ge gives: T(bⁱ) ≥ aⁱ·T(b⁰) → T(bⁱ) ≥ T(b⁰)·aⁱ
    -- Since T(b⁰) > 0, this is the Ω bound with c = T(b⁰) > 0.
    -- Let's use the definition of isBigOmega:
    -- isBigOmega f g ↔ ∃ c>0, ∀ᶠ x in atTop, c·|g x| ≤ |f x|
    -- Both f and g are ≥ 0, so |·| drops.
    rw [isBigOmega_iff]
    -- Need: ∃ c>0, ∃ n₀, ∀ i≥n₀, c·aⁱ ≤ T(bⁱ)
    -- Take c = T(b⁰) > 0, n₀ = 0.  Then for all i: c·aⁱ = T(b⁰)·aⁱ ≤ T(bⁱ) by h_ge.
    refine ⟨T (b ^ 0), h_T0_pos, 0, fun i hi => ?_⟩
    have := h_ge i
    -- this: T(bⁱ) ≥ aⁱ·T(b⁰)
    -- goal: T(b⁰)·aⁱ ≤ T(bⁱ)
    -- These are the same up to commutativity of multiplication
    -- T(b⁰)·aⁱ = aⁱ·T(b⁰) ≤ T(bⁱ) ✓
    simpa [mul_comm] using this

  exact ⟨h_O, h_Omega⟩

end Chapter04
end CLRS
