import Mathlib

/-!
# CLRS Section 4.2 - Strassen's algorithm for matrix multiplication

This file formalizes the algebraic heart of Strassen's algorithm.  A
{lit}`Matrix2 R` should be read as a 2 by 2 block matrix whose entries live in
an arbitrary ring.  The theorem {lit}`strassen2x2_correct` proves that
Strassen's seven block products reconstruct ordinary 2 by 2 block matrix
multiplication.

This is intentionally only the algebraic correctness layer.  Recursive matrix
splitting, dimensions, and runtime analysis are later refinement targets.
-/

namespace CLRS
namespace Chapter04

/-- A 2 by 2 block matrix. -/
structure Matrix2 (R : Type*) where
  a11 : R
  a12 : R
  a21 : R
  a22 : R

namespace Matrix2

@[ext]
theorem ext {R : Type*} {A B : Matrix2 R}
    (h11 : A.a11 = B.a11) (h12 : A.a12 = B.a12)
    (h21 : A.a21 = B.a21) (h22 : A.a22 = B.a22) : A = B := by
  cases A
  cases B
  simp_all

variable {R : Type*} [Ring R]

/-- Ordinary 2 by 2 block matrix multiplication. -/
def mul (A B : Matrix2 R) : Matrix2 R :=
  { a11 := A.a11 * B.a11 + A.a12 * B.a21
    a12 := A.a11 * B.a12 + A.a12 * B.a22
    a21 := A.a21 * B.a11 + A.a22 * B.a21
    a22 := A.a21 * B.a12 + A.a22 * B.a22 }

/-- Strassen's seven-product reconstruction for 2 by 2 block matrices. -/
def strassen (A B : Matrix2 R) : Matrix2 R :=
  let p1 := A.a11 * (B.a12 - B.a22)
  let p2 := (A.a11 + A.a12) * B.a22
  let p3 := (A.a21 + A.a22) * B.a11
  let p4 := A.a22 * (B.a21 - B.a11)
  let p5 := (A.a11 + A.a22) * (B.a11 + B.a22)
  let p6 := (A.a12 - A.a22) * (B.a21 + B.a22)
  let p7 := (A.a11 - A.a21) * (B.a11 + B.a12)
  { a11 := p5 + p4 - p2 + p6
    a12 := p1 + p2
    a21 := p3 + p4
    a22 := p5 + p1 - p3 - p7 }

/-- Strassen's seven products compute the ordinary 2 by 2 block product. -/
theorem strassen_eq_mul (A B : Matrix2 R) : strassen A B = mul A B := by
  ext <;> simp [strassen, mul] <;> noncomm_ring

end Matrix2

/--
Reader-facing correctness theorem for CLRS Section 4.2: the algebraic
Strassen reconstruction is extensionally equal to ordinary 2 by 2 block
matrix multiplication.
-/
theorem strassen2x2_correct {R : Type*} [Ring R] (A B : Matrix2 R) :
    Matrix2.strassen A B = Matrix2.mul A B :=
  Matrix2.strassen_eq_mul A B

end Chapter04
end CLRS
