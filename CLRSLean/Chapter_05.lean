import CLRSLean.Chapter_05.Section_05_1_Hiring_Problem

/-!
# Chapter 5. Probabilistic Analysis and Randomized Algorithms

The hiring problem studies the expected number of times a new best candidate is
hired in a random interview order.  The current file proves the finite
rank-symmetry calculation that the step probability is {lit}`1/(n+1)`, sums the
indicator expectations, proves the equivalent recurrence solution, and derives
the logarithmic asymptotic growth of the expected number of hires.

* Section 5.1: {lit}`proved` for the finite rank-symmetry model, including
  {lit}`CLRS.Chapter05.expectedHires_isBigTheta_log`.
-/

namespace CLRS
namespace Chapter05
end Chapter05
end CLRS
