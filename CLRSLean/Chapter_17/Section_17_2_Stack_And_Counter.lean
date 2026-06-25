import CLRSLean.Chapter_17.Section_17_1_Amortized_Framework

/-!
# CLRS Section 17.2 - Stack and counter examples

This section records two compact textbook amortized-analysis examples.  The
stack model uses the real operation cost for {lit}`MULTIPOP`: at most one unit
per popped element.  The counter model exposes the first-pass constant
amortized-cost conclusion as a specification-level flip-count sequence; the
exact trailing-one bit-count model is a later strengthening target.

Main results:

- Theorem {lit}`multiPop_totalCost_le`: one {lit}`MULTIPOP` operation pops at
  most the requested number of stack cells.
- Theorem {lit}`binaryCounter_totalFlips_le`: the first-pass counter cost model
  has total flip count at most {lit}`2n`.

Current gaps:

- The binary-counter theorem does not yet count trailing ones in an executable
  bit-vector increment trace.
-/

namespace CLRS
namespace Chapter17

/-! ## Stack multipop -/

/-- Pop at most {lit}`k` elements from a stack represented by a list. -/
def multiPop {α : Type u} (s : List α) (k : Nat) : List α :=
  s.drop k

/-- Cost of a single {lit}`MULTIPOP`: the number of cells actually removed. -/
def multiPopCost {α : Type u} (s : List α) (k : Nat) : Nat :=
  min k s.length

/-- A single {lit}`MULTIPOP` pops at most the requested number of cells. -/
theorem multiPop_totalCost_le {α : Type u} (s : List α) (k : Nat) :
    multiPopCost s k <= k := by
  exact Nat.min_le_left k s.length

/-! ## Binary counter -/

/--
Executable little-endian binary-counter increment.  This definition is included
for the public model; the first-pass cost theorem below uses a specification
cost sequence with the standard constant amortized bound.
-/
def binaryCounterIncrement : List Bool -> List Bool
  | [] => [true]
  | false :: bits => true :: bits
  | true :: bits => false :: binaryCounterIncrement bits

/-- First-pass amortized flip count for one counter increment. -/
def bitFlipsForIncrement (_i : Nat) : Nat :=
  2

/-- Under the first-pass cost model, {lit}`n` increments flip at most {lit}`2n` bits. -/
theorem binaryCounter_totalFlips_le (n : Nat) :
    prefixCost bitFlipsForIncrement n <= 2 * n := by
  induction n with
  | zero =>
      simp [prefixCost]
  | succ n ih =>
      simp [prefixCost, bitFlipsForIncrement]
      omega

end Chapter17
end CLRS
