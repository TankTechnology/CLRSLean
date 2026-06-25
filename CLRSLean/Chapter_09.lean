import CLRSLean.Chapter_09.Section_09_2_Select_By_Rank

/-!
# Chapter 9 - Medians and Order Statistics

Chapter 9 now has two compiler-clean correctness interfaces for selection: a
specification selector obtains the zero-based rank by sorting and indexing, and
a pivot-style quickselect model recursively partitions around the first
element.  Both public theorem layers prove that any returned value satisfies
the usual order-statistic count certificate.

## Sections

* 9.2 Selection by rank: {lit}`proved` for the specification selector and the
  pivot-style quickselect model.  Main results:
  {lit}`CLRS.Chapter09.selectByRank?_mem`,
  {lit}`CLRS.Chapter09.selectByRank?_rankCorrect`, and
  {lit}`CLRS.Chapter09.selectByRank?_correct`;
  {lit}`CLRS.Chapter09.quickSelect?_mem`,
  {lit}`CLRS.Chapter09.quickSelect?_rankCorrect`, and
  {lit}`CLRS.Chapter09.quickSelect?_correct`.

## Current Gaps

* Randomized SELECT and expected running time require a probability model.
* Deterministic linear-time SELECT still needs the median-of-medians split-size
  theorem and recurrence analysis.
-/

namespace CLRS
namespace Chapter09
end Chapter09
end CLRS
