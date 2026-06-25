# Chapter 9 - Medians and Order Statistics

Chapter 9 now has compiler-clean correctness interfaces for both the
specification selector and a pivot-style quickselect model.

## Section 9.2 - Selection by rank

- Lean source: `CLRSLean/Chapter_09/Section_09_2_Select_By_Rank.lean`
- Status: `proved` for the specification selector and pivot-style quickselect
- Main theorem: `CLRS.Chapter09.quickSelect?_correct`

The section keeps the simple specification selector: sort the input list and
read the zero-based rank `k`.  It also proves a fuelled quickselect model that
uses the first element as a pivot and recursively keeps the `< pivot` or
`> pivot` side, with the middle pivot block represented by the interval
`ltCount pivot xs ≤ k < leCount pivot xs`.

The theorem layer proves:

- `CLRS.Chapter09.sortedCopy_perm`: sorting preserves exactly the input
  elements.
- `CLRS.Chapter09.sortedCopy_pairwise`: the sorted copy is pairwise ordered.
- `CLRS.Chapter09.selectByRank?_mem`: any returned value came from the input.
- `CLRS.Chapter09.selectByRank?_rankCorrect`: the returned value satisfies the
  order-statistic count certificate.
- `CLRS.Chapter09.selectByRank?_correct`: the reader-facing correctness wrapper.
- `CLRS.Chapter09.quickSelect?_mem`: any quickselect result came from the input.
- `CLRS.Chapter09.quickSelect?_rankCorrect`: pivot-style quickselect satisfies
  the same rank certificate.
- `CLRS.Chapter09.quickSelect?_correct`: the reader-facing quickselect wrapper.

The rank certificate handles duplicates in the standard way.  If the returned
value is `x`, then the number of input elements strictly smaller than `x` is at
most `k`, and the number of input elements at most `x` is greater than `k`.

## Hard Follow-Up Work

- Randomized SELECT expected time: requires a probability model for randomized
  pivots and a cost recurrence or indicator argument.
- Deterministic linear-time SELECT: requires median-of-medians partition
  bounds and recurrence analysis.
