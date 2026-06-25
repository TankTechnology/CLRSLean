import CLRSLean.Chapter_09.Section_09_2_Select_By_Rank

/-!
# CLRS Section 9.3 - Deterministic selection

This file factors the Chapter 9 selection proof through a pivot-parametric
interface.  The key point is pure correctness rather than running time: any
pivot rule that returns an element of the current input list yields a selector
whose successful result satisfies the same count-based rank certificate used in
Section 9.2.

Main results:

* Theorem {lit}`selectWithPivot?_correct`: a pivot-parametric SELECT is rank
  correct whenever the pivot rule returns members of the current list.
* Theorem {lit}`medianOfFive?_certificate`: the median selected from a
  five-element group has at least three elements below it weakly and at least
  three elements above it weakly.
* Theorem {lit}`deterministicSelect?_correct`: a deterministic median-pivot
  instance is rank correct.

Current gaps:

* This is not yet the CLRS linear-time median-of-medians cost theorem.  The
  local five-element median certificate is proved below; the remaining hard
  proof is the global split-size inequality for the grouped medians and the
  associated linear recurrence.
-/

namespace CLRS
namespace Chapter09

/-! ## Pivot-parametric selection -/

/--
A pivot function is membership-safe when every pivot it returns is an element
of the current input list.
-/
def PivotMembership (choosePivot? : List Nat → Option Nat) : Prop :=
  ∀ {xs : List Nat} {pivot : Nat}, choosePivot? xs = some pivot → pivot ∈ xs

/--
Fuelled SELECT with an abstract deterministic pivot rule.

The algorithm mirrors the CLRS three-way partition around the chosen pivot:
recurse on elements below the pivot, return the pivot block when the requested
rank falls inside it, or recurse on elements above the pivot after shifting the
rank by the number of elements at most the pivot.
-/
def selectWithPivotFuel? (choosePivot? : List Nat → Option Nat) :
    Nat → Nat → List Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, k, xs =>
      match choosePivot? xs with
      | none => none
      | some pivot =>
          if k < ltCount pivot xs then
            selectWithPivotFuel? choosePivot? fuel k
              (xs.filter fun y => decide (y < pivot))
          else if k < leCount pivot xs then
            some pivot
          else
            selectWithPivotFuel? choosePivot? fuel (k - leCount pivot xs)
              (xs.filter fun y => decide (pivot < y))

/-- Public SELECT wrapper using one unit of fuel per input element. -/
def selectWithPivot? (choosePivot? : List Nat → Option Nat)
    (k : Nat) (xs : List Nat) : Option Nat :=
  selectWithPivotFuel? choosePivot? xs.length k xs

/--
Correctness of the fuelled pivot-parametric SELECT.

If the pivot function is membership-safe and the computation returns {lit}`x`,
then {lit}`x` is a valid zero-based order statistic certificate for the
original input.
-/
theorem selectWithPivotFuel?_rankCorrect
    (choosePivot? : List Nat → Option Nat)
    (hpivot : PivotMembership choosePivot?) :
    ∀ (fuel k : Nat) (xs : List Nat) {x : Nat}, xs.length ≤ fuel →
      selectWithPivotFuel? choosePivot? fuel k xs = some x →
        RankCertificate xs k x := by
  intro fuel
  induction fuel with
  | zero =>
      intro k xs selected _hlen hsel
      simp [selectWithPivotFuel?] at hsel
  | succ fuel ih =>
      intro k xs selected hlen hsel
      cases hchoose : choosePivot? xs with
      | none =>
          simp [selectWithPivotFuel?, hchoose] at hsel
      | some pivot =>
          have hpivot_mem : pivot ∈ xs := hpivot hchoose
          have hlow_len :
              (xs.filter fun y => decide (y < pivot)).length ≤ fuel := by
            have hstrict :
                (xs.filter fun y => decide (y < pivot)).length < xs.length :=
              filter_length_lt_of_mem_false (fun y => decide (y < pivot))
                (xs := xs) (x := pivot) hpivot_mem (by simp)
            have hlt_fuel :
                (xs.filter fun y => decide (y < pivot)).length < fuel + 1 :=
              Nat.lt_of_lt_of_le hstrict hlen
            exact Nat.lt_succ_iff.mp hlt_fuel
          have hhigh_len :
              (xs.filter fun y => decide (pivot < y)).length ≤ fuel := by
            have hstrict :
                (xs.filter fun y => decide (pivot < y)).length < xs.length :=
              filter_length_lt_of_mem_false (fun y => decide (pivot < y))
                (xs := xs) (x := pivot) hpivot_mem (by simp)
            have hlt_fuel :
                (xs.filter fun y => decide (pivot < y)).length < fuel + 1 :=
              Nat.lt_of_lt_of_le hstrict hlen
            exact Nat.lt_succ_iff.mp hlt_fuel
          by_cases hlo : k < ltCount pivot xs
          · have hsel_low :
                selectWithPivotFuel? choosePivot? fuel k
                    (xs.filter fun y => decide (y < pivot)) =
                  some selected := by
              simpa [selectWithPivotFuel?, hchoose, hlo] using hsel
            exact rankCertificate_low_lift
              (ih k (xs.filter fun y => decide (y < pivot))
                hlow_len hsel_low)
          · by_cases hle : k < leCount pivot xs
            · have hx : selected = pivot := by
                exact Eq.symm
                  (by
                    simpa [selectWithPivotFuel?, hchoose, hlo, hle] using hsel)
              subst selected
              exact rankCertificate_pivot (xs := xs) (pivot := pivot)
                hpivot_mem hlo hle
            · have hsel_high :
                  selectWithPivotFuel? choosePivot? fuel
                      (k - leCount pivot xs)
                      (xs.filter fun y => decide (pivot < y)) =
                    some selected := by
                simpa [selectWithPivotFuel?, hchoose, hlo, hle] using hsel
              have hge : leCount pivot xs ≤ k := Nat.le_of_not_gt hle
              exact rankCertificate_high_lift hge
                (ih (k - leCount pivot xs)
                  (xs.filter fun y => decide (pivot < y))
                  hhigh_len hsel_high)

/-- Rank-correctness theorem for the public pivot-parametric SELECT wrapper. -/
theorem selectWithPivot?_rankCorrect
    (choosePivot? : List Nat → Option Nat)
    (hpivot : PivotMembership choosePivot?) {k : Nat} {xs : List Nat}
    {x : Nat} (hsel : selectWithPivot? choosePivot? k xs = some x) :
    RankCertificate xs k x := by
  exact selectWithPivotFuel?_rankCorrect choosePivot? hpivot xs.length k xs
    (Nat.le_refl xs.length) hsel

/-- Membership projection for pivot-parametric SELECT. -/
theorem selectWithPivot?_mem
    (choosePivot? : List Nat → Option Nat)
    (hpivot : PivotMembership choosePivot?) {k : Nat} {xs : List Nat}
    {x : Nat} (hsel : selectWithPivot? choosePivot? k xs = some x) :
    x ∈ xs :=
  (selectWithPivot?_rankCorrect choosePivot? hpivot hsel).1

/-- Reader-facing correctness wrapper for pivot-parametric SELECT. -/
theorem selectWithPivot?_correct
    (choosePivot? : List Nat → Option Nat)
    (hpivot : PivotMembership choosePivot?) {k : Nat} {xs : List Nat}
    {x : Nat} (hsel : selectWithPivot? choosePivot? k xs = some x) :
    RankCertificate xs k x :=
  selectWithPivot?_rankCorrect choosePivot? hpivot hsel

/-! ## Five-element median certificate -/

/-- Correctness-oriented median selector for a five-element group. -/
def medianOfFive? (xs : List Nat) : Option Nat :=
  selectByRank? 2 xs

/--
Local certificate used by the CLRS median-of-medians split argument.

For a five-element group, the selected median is an input member, at least
three group elements are at most it, and at least three group elements are at
least it.
-/
def MedianFiveCertificate (xs : List Nat) (median : Nat) : Prop :=
  xs.length = 5 ∧ median ∈ xs ∧ 3 ≤ leCount median xs ∧ 3 ≤ geCount median xs

/--
The rank-2 selector on a five-element group supplies the local 3/3 median
certificate needed by the deterministic SELECT split-size proof.
-/
theorem medianOfFive?_certificate {xs : List Nat} {median : Nat}
    (hlen : xs.length = 5) (hsel : medianOfFive? xs = some median) :
    MedianFiveCertificate xs median := by
  have hrank : RankCertificate xs 2 median := by
    exact selectByRank?_rankCorrect (by simpa [medianOfFive?] using hsel)
  refine ⟨hlen, hrank.1, ?_, ?_⟩
  · exact Nat.succ_le_of_lt hrank.2.2
  · have hlt : ltCount median xs ≤ 2 := hrank.2.1
    rw [geCount_eq_length_sub_ltCount, hlen]
    omega

/-! ## Deterministic median-pivot instance -/

/--
Deterministic pivot rule that chooses the median of the current list according
to the specification selector.

This is a correctness-oriented pivot rule.  It deliberately separates the rank
proof from the harder CLRS median-of-medians running-time argument.
-/
def deterministicPivot? (xs : List Nat) : Option Nat :=
  selectByRank? (xs.length / 2) xs

/-- The deterministic median-pivot rule returns only members of its input. -/
theorem deterministicPivot?_mem :
    PivotMembership deterministicPivot? := by
  intro xs pivot hsel
  exact selectByRank?_mem (by simpa [deterministicPivot?] using hsel)

/-- Deterministic SELECT using the specification median as its pivot rule. -/
def deterministicSelect? (k : Nat) (xs : List Nat) : Option Nat :=
  selectWithPivot? deterministicPivot? k xs

/-- Rank-correctness theorem for deterministic median-pivot SELECT. -/
theorem deterministicSelect?_rankCorrect {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : deterministicSelect? k xs = some x) :
    RankCertificate xs k x := by
  exact selectWithPivot?_rankCorrect deterministicPivot? deterministicPivot?_mem
    (by simpa [deterministicSelect?] using hsel)

/-- Membership projection for deterministic median-pivot SELECT. -/
theorem deterministicSelect?_mem {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : deterministicSelect? k xs = some x) :
    x ∈ xs :=
  (deterministicSelect?_rankCorrect hsel).1

/-- Reader-facing correctness wrapper for deterministic median-pivot SELECT. -/
theorem deterministicSelect?_correct {k : Nat} {xs : List Nat} {x : Nat}
    (hsel : deterministicSelect? k xs = some x) :
    RankCertificate xs k x :=
  deterministicSelect?_rankCorrect hsel

end Chapter09
end CLRS
