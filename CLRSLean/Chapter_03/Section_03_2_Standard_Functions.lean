import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open Filter
open Asymptotics
open scoped Topology

/-!
# 3.2. Standard Notations and Common Functions

Concrete asymptotic comparisons for algorithm analysis.

* `nᵃ = o(nᵇ)` when `a < b`
* `nᵃ = o(cⁿ)` when `1 < c`
* `log n = o(nʳ)` when `0 < r`
* `aⁿ = o(bⁿ)` when `0 ≤ a < b`
* the harmonic numbers satisfy `Hₙ ~ log n` and `Hₙ = Θ(log n)`
* `⌊n⌋ = Θ(n)` and `⌈n⌉ = Θ(n)` on ℕ
* `⌊n/2⌋ = Θ(n)` and `⌈n/2⌉ = Θ(n)` on ℕ
* lower and upper factorial bounds
* `aⁿ = o(n!)` and `n! = o(nⁿ)`
-/

namespace CLRS
namespace Chapter03

/-! ## Polynomial comparisons -/

/-- `nᵃ = o(nᵇ)` when `a < b`. -/
theorem isLittleO_pow_pow {a b : ℕ} (h : a < b) :
    isLittleO (fun n : ℕ => (n : ℝ) ^ a) (fun n : ℕ => (n : ℝ) ^ b) := by
  unfold isLittleO
  have h_ℝ : (fun x : ℝ => x ^ a) =o[atTop] (fun x : ℝ => x ^ b) :=
    Asymptotics.isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) h
  exact (h_ℝ.comp_tendsto tendsto_natCast_atTop_atTop).congr
    (by simp) (by simp)

/-- `nᵃ = O(nᵇ)` when `a ≤ b`. -/
theorem isBigO_pow_pow {a b : ℕ} (h : a ≤ b) :
    isBigO (fun n : ℕ => (n : ℝ) ^ a) (fun n : ℕ => (n : ℝ) ^ b) := by
  rcases Nat.eq_or_lt_of_le h with (rfl | hlt)
  · exact isBigO_refl _
  · exact (isLittleO_pow_pow hlt).isBigO

/-! ## Polynomial, logarithmic, and exponential comparisons -/

/-- For any natural exponent `a` and real base `c > 1`, `nᵃ = o(cⁿ)`. -/
theorem isLittleO_pow_const_exp {a : ℕ} {c : ℝ} (hc : 1 < c) :
    isLittleO (fun n : ℕ => (n : ℝ) ^ a) (fun n : ℕ => c ^ n) := by
  unfold isLittleO
  exact isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) a hc

/-- For every positive real exponent `r`, `log n = o(nʳ)`. -/
theorem isLittleO_log_rpow {r : ℝ} (hr : 0 < r) :
    isLittleO (fun n : ℕ => Real.log (n : ℝ)) (fun n : ℕ => (n : ℝ) ^ r) := by
  unfold isLittleO
  exact (isLittleO_log_rpow_atTop hr).comp_tendsto tendsto_natCast_atTop_atTop

/-- If `0 ≤ a < b`, then `aⁿ = o(bⁿ)`. -/
theorem isLittleO_exp_exp_of_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    isLittleO (fun n : ℕ => a ^ n) (fun n : ℕ => b ^ n) := by
  unfold isLittleO
  exact isLittleO_pow_pow_of_lt_left ha hab

/-! ## Harmonic numbers -/

/-- The harmonic numbers are asymptotic to `log n`. -/
theorem isEquivalent_harmonic_log :
    (fun n : ℕ => (harmonic n : ℝ)) ~[atTop] (fun n : ℕ => Real.log (n : ℝ)) := by
  have hdiffO :
      (fun n : ℕ => (harmonic n : ℝ) - Real.log (n : ℝ)) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
    exact Filter.Tendsto.isBigO_one (F := ℝ) Real.tendsto_harmonic_sub_log
  have hconst :
      (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n : ℕ => Real.log (n : ℝ)) := by
    exact Real.isLittleO_const_log_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  exact hdiffO.trans_isLittleO hconst

/-- The harmonic numbers have logarithmic growth, `Hₙ = Θ(log n)`. -/
theorem isBigTheta_harmonic_log :
    isBigTheta (fun n : ℕ => (harmonic n : ℝ)) (fun n : ℕ => Real.log (n : ℝ)) := by
  have htheta :
      (fun n : ℕ => (harmonic n : ℝ)) =Θ[atTop]
        (fun n : ℕ => Real.log (n : ℝ)) :=
    isEquivalent_harmonic_log.isTheta
  exact ⟨by unfold isBigO; exact htheta.1, by unfold isBigOmega; exact htheta.2⟩

/-! ## Floor and ceiling are Θ(id) on ℕ -/

theorem isBigTheta_nat_floor_coerce : isBigTheta (fun n : ℕ => (⌊(n : ℝ)⌋₊ : ℝ)) (fun n : ℕ => (n : ℝ)) := by
  have h_equiv : (fun x : ℝ => (⌊x⌋₊ : ℝ)) ~[atTop] (fun x : ℝ => x) := isEquivalent_nat_floor
  have hO : (fun n : ℕ => (⌊(n : ℝ)⌋₊ : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) :=
    (h_equiv.isBigO.comp_tendsto tendsto_natCast_atTop_atTop).congr (by simp) (by simp)
  have hΩ : (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (⌊(n : ℝ)⌋₊ : ℝ)) :=
    (h_equiv.symm.isBigO.comp_tendsto tendsto_natCast_atTop_atTop).congr (by simp) (by simp)
  exact ⟨by unfold isBigO; exact hO, by unfold isBigOmega; exact hΩ⟩

theorem isBigTheta_nat_ceil_coerce : isBigTheta (fun n : ℕ => (⌈(n : ℝ)⌉₊ : ℝ)) (fun n : ℕ => (n : ℝ)) := by
  have h_equiv : (fun x : ℝ => (⌈x⌉₊ : ℝ)) ~[atTop] (fun x : ℝ => x) := isEquivalent_nat_ceil
  have hO : (fun n : ℕ => (⌈(n : ℝ)⌉₊ : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) :=
    (h_equiv.isBigO.comp_tendsto tendsto_natCast_atTop_atTop).congr (by simp) (by simp)
  have hΩ : (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (⌈(n : ℝ)⌉₊ : ℝ)) :=
    (h_equiv.symm.isBigO.comp_tendsto tendsto_natCast_atTop_atTop).congr (by simp) (by simp)
  exact ⟨by unfold isBigO; exact hO, by unfold isBigOmega; exact hΩ⟩

private theorem self_le_four_mul_div_two_nat {n : ℕ} (hn : 2 ≤ n) :
    n ≤ 4 * (n / 2) := by
  have hpos : 0 < n / 2 := Nat.div_pos hn (by decide)
  have hmod_lt : n % 2 < 2 := Nat.mod_lt n (by decide)
  have hdecomp : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
  omega

private theorem ceil_half_le_self_nat {n : ℕ} (hn : 1 ≤ n) :
    (n + 1) / 2 ≤ n := by
  omega

private theorem self_le_two_mul_ceil_half_nat (n : ℕ) :
    n ≤ 2 * ((n + 1) / 2) := by
  have hmod_lt : (n + 1) % 2 < 2 := Nat.mod_lt (n + 1) (by decide)
  have hdecomp : 2 * ((n + 1) / 2) + (n + 1) % 2 = n + 1 :=
    Nat.div_add_mod (n + 1) 2
  omega

/-- Natural-number floor half-scale: `⌊n/2⌋ = Θ(n)`. -/
theorem isBigTheta_nat_floor_half_coerce :
    isBigTheta (fun n : ℕ => ((n / 2 : ℕ) : ℝ)) (fun n : ℕ => (n : ℝ)) := by
  constructor
  · rw [isBigO_iff]
    refine ⟨1, by norm_num, 0, ?_⟩
    intro n _hn
    have hnat : n / 2 ≤ n := Nat.div_le_self n 2
    have hreal : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnat
    simpa using hreal
  · change isBigO (fun n : ℕ => (n : ℝ)) (fun n : ℕ => ((n / 2 : ℕ) : ℝ))
    rw [isBigO_iff]
    refine ⟨4, by norm_num, 2, ?_⟩
    intro n hn
    have hnat : n ≤ 4 * (n / 2) := self_le_four_mul_div_two_nat hn
    have hreal : (n : ℝ) ≤ 4 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa using hreal

/-- Natural-number ceiling half-scale, represented as `(n+1)/2`: `⌈n/2⌉ = Θ(n)`. -/
theorem isBigTheta_nat_ceil_half_coerce :
    isBigTheta (fun n : ℕ => (((n + 1) / 2 : ℕ) : ℝ)) (fun n : ℕ => (n : ℝ)) := by
  constructor
  · rw [isBigO_iff]
    refine ⟨1, by norm_num, 1, ?_⟩
    intro n hn
    have hnat : (n + 1) / 2 ≤ n := ceil_half_le_self_nat hn
    have hreal : (((n + 1) / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnat
    simpa using hreal
  · change isBigO (fun n : ℕ => (n : ℝ)) (fun n : ℕ => (((n + 1) / 2 : ℕ) : ℝ))
    rw [isBigO_iff]
    refine ⟨2, by norm_num, 0, ?_⟩
    intro n _hn
    have hnat : n ≤ 2 * ((n + 1) / 2) := self_le_two_mul_ceil_half_nat n
    have hreal : (n : ℝ) ≤ 2 * ((((n + 1) / 2 : ℕ) : ℝ)) := by exact_mod_cast hnat
    simpa using hreal

/-! ## Factorial bound -/

/-- `n! ≤ nⁿ` for all `n`.  Proof on `ℕ`: each factor 1..n ≤ n. -/
theorem factorial_upper_bound_nat (n : ℕ) : Nat.factorial n ≤ n ^ n := by
  exact Nat.factorial_le_pow n

/-- `n! ≤ nⁿ` for all `n`, real version. -/
theorem factorial_upper_bound (n : ℕ) : (Nat.factorial n : ℝ) ≤ (n : ℝ) ^ n := by
  exact_mod_cast factorial_upper_bound_nat n

/--
For any offset `m`, the last `k` factors in `(m+k)!` are each at least `m+1`,
so `(m+1)^k ≤ (m+k)!`.
-/
theorem factorial_lower_bound_offset_nat (m k : ℕ) :
    (m + 1) ^ k ≤ Nat.factorial (m + k) := by
  have h := Nat.factorial_mul_pow_le_factorial (m := m) (n := k)
  have hle : (m + 1) ^ k ≤ Nat.factorial m * (m + 1) ^ k :=
    Nat.le_mul_of_pos_left ((m + 1) ^ k) (Nat.factorial_pos m)
  exact le_trans hle h

/-- Real-valued version of `factorial_lower_bound_offset_nat`. -/
theorem factorial_lower_bound_offset (m k : ℕ) :
    ((m + 1 : ℕ) : ℝ) ^ k ≤ (Nat.factorial (m + k) : ℝ) := by
  exact_mod_cast factorial_lower_bound_offset_nat m k

/--
A CLRS-style half-scale lower bound: the upper half of the factors in `n!`
contributes at least `(⌊n/2⌋+1)^(n-⌊n/2⌋)`.
-/
theorem factorial_lower_bound_half_pow_nat (n : ℕ) :
    (n / 2 + 1) ^ (n - n / 2) ≤ Nat.factorial n := by
  have h := factorial_lower_bound_offset_nat (m := n / 2) (k := n - n / 2)
  have hsum : n / 2 + (n - n / 2) = n :=
    Nat.add_sub_of_le (Nat.div_le_self n 2)
  simpa [hsum] using h

/-- Real-valued version of `factorial_lower_bound_half_pow_nat`. -/
theorem factorial_lower_bound_half_pow (n : ℕ) :
    (((n / 2 + 1 : ℕ) : ℝ) ^ (n - n / 2)) ≤ (Nat.factorial n : ℝ) := by
  exact_mod_cast factorial_lower_bound_half_pow_nat n

/-! ## Exponential vs factorial -/

/-- `aⁿ = o(n!)` as `n → ∞`.  Follows from `FloorSemiring.tendsto_pow_div_factorial_atTop`,
the standard lemma that `cⁿ / n! → 0` for any real `c`. -/
theorem isLittleO_exp_vs_factorial (a : ℝ) :
    isLittleO (fun n : ℕ => a ^ n) (fun n : ℕ => (Nat.factorial n : ℝ)) := by
  -- The key lemma: a^n / n! → 0 as n → ∞ (standard result in mathlib)
  have h_tendsto : Tendsto (fun n : ℕ => a ^ n / ((Nat.factorial n : ℕ) : ℝ)) atTop (𝓝 0) := by
    -- FloorSemiring.tendsto_pow_div_factorial_atTop gives a^n / n! → 0 in ℝ
    -- where n! is the ℝ factorial via the factorial notation `n !`
    simpa using FloorSemiring.tendsto_pow_div_factorial_atTop (K := ℝ) a
  -- Use isLittleO_iff_tendsto: f =o[atTop] g  ↔  f/g → 0  (when g=0 → f=0)
  have h_cond : ∀ n : ℕ, ((Nat.factorial n : ℝ) = 0) → a ^ n = 0 := by
    intro n hn
    have hpos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    linarith
  unfold isLittleO
  rw [isLittleO_iff_tendsto h_cond]
  exact h_tendsto

/--
CLRS standard growth-table fact: `n! = o(nⁿ)`.
-/
theorem isLittleO_factorial_pow_self :
    isLittleO (fun n : ℕ => (Nat.factorial n : ℝ)) (fun n : ℕ => (n : ℝ) ^ n) := by
  have h_tendsto :
      Tendsto (fun n : ℕ => (Nat.factorial n : ℝ) / ((n : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa using tendsto_factorial_div_pow_self_atTop
  have h_cond : ∀ n : ℕ, ((n : ℝ) ^ n = 0) → (Nat.factorial n : ℝ) = 0 := by
    intro n hn
    exfalso
    have hpow_pos : 0 < (n : ℝ) ^ n := by
      cases n with
      | zero => norm_num
      | succ k => positivity
    exact (ne_of_gt hpow_pos) hn
  unfold isLittleO
  rw [isLittleO_iff_tendsto h_cond]
  exact h_tendsto

end Chapter03
end CLRS
