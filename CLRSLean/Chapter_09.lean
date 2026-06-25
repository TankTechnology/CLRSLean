import CLRSLean.Chapter_09.Section_09_2_Select_By_Rank

/-!
# Chapter 9 - Medians and Order Statistics

Chapter 9 now has a first correctness interface for selection: a specification
selector obtains the zero-based rank by sorting and indexing, and its public
theorem proves the returned value satisfies the usual order-statistic count
certificate.

## Sections

* 9.2 Selection by rank: {lit}`proved` for the specification selector.  Main
  results:
  {lit}`CLRS.Chapter09.selectByRank?_mem`,
  {lit}`CLRS.Chapter09.selectByRank?_rankCorrect`, and
  {lit}`CLRS.Chapter09.selectByRank?_correct`.

## Current Gaps

* Randomized SELECT and expected running time require a probability model.
* Deterministic linear-time SELECT needs a refinement theorem from the
  median-of-medians algorithm to the rank certificate.
-/

namespace CLRS
namespace Chapter09
end Chapter09
end CLRS
