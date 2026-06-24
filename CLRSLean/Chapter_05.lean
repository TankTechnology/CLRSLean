import CLRSLean.Chapter_05.Section_05_1_Hiring_Problem

/-!
# Chapter 5. Probabilistic Analysis and Randomized Algorithms

The hiring problem studies the expected number of times a new best candidate is
hired in a random interview order.  The current file proves the deterministic
recurrence solution: once the CLRS symmetry argument gives
`h(n+1) = h(n) + 1/(n+1)`, the solution is the harmonic number.

* Section 5.1: `partial`; recurrence solution, with the probability-space proof
  still future work.
-/

namespace CLRS
namespace Chapter05
end Chapter05
end CLRS
