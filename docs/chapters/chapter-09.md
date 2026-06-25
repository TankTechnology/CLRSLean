# Chapter 9 - Medians and Order Statistics

Chapter 9 now has a first compiler-clean correctness interface for selection.

## Section 9.2 - Selection by rank

- Lean source: `CLRSLean/Chapter_09/Section_09_2_Select_By_Rank.lean`
- Status: `proved` for the specification selector
- Main theorem: `CLRS.Chapter09.selectByRank?_correct`

The model uses a simple specification selector: sort the input list and read
the zero-based rank `k`.  This is intentionally not the final linear-time
algorithm, but it gives the stable theorem target that later SELECT
implementations should refine.

The theorem layer proves:

- `CLRS.Chapter09.sortedCopy_perm`: sorting preserves exactly the input
  elements.
- `CLRS.Chapter09.sortedCopy_pairwise`: the sorted copy is pairwise ordered.
- `CLRS.Chapter09.selectByRank?_mem`: any returned value came from the input.
- `CLRS.Chapter09.selectByRank?_rankCorrect`: the returned value satisfies the
  order-statistic count certificate.
- `CLRS.Chapter09.selectByRank?_correct`: the reader-facing correctness wrapper.

The rank certificate handles duplicates in the standard way.  If the returned
value is `x`, then the number of input elements strictly smaller than `x` is at
most `k`, and the number of input elements at most `x` is greater than `k`.

## Hard Follow-Up Work

- Randomized SELECT expected time: requires a probability model for randomized
  pivots and a cost recurrence or indicator argument.
- Deterministic linear-time SELECT: requires median-of-medians partition
  bounds and a refinement proof from the executable algorithm to the same rank
  certificate.
