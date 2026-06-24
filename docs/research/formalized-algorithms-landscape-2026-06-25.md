# Formalized Algorithms Landscape - 2026-06-25

This note records a short literature scan for positioning CLRS-Lean.

## Established Baseline

- `Verified Textbook Algorithms: A Biased Survey` surveys machine-checked
  textbook-algorithm verification with a strong CLRS focus, considering both
  correctness and running-time complexity:
  <https://www21.in.tum.de/~nipkow/pubs/atva20.pdf>.
- The survey emphasizes that many proofs target functional versions of textbook
  algorithms, and it calls out imperative proofs explicitly.  This distinction
  matches the main design pressure in CLRS-Lean: prove the mathematical theorem
  first, then refine to arrays, mutation, and cost models where needed.
- Coq has mature textbook-style teaching material in `Verified Functional
  Algorithms`, part of Software Foundations:
  <https://softwarefoundations.cis.upenn.edu/vfa-current/index.html>.
- Isabelle/HOL has a mature publication-style ecosystem through the Archive of
  Formal Proofs:
  <https://isa-afp.org/>.

## Strong Reference Points

- Isabelle AFP's Kruskal entry proves an abstract greedy algorithm for minimum
  weight basis, instantiates it to graph forests, and refines it to imperative
  executable code using efficient union-find:
  <https://isa-afp.org/entries/Kruskal.html>.
- This is substantially stronger than CLRS-Lean's current MST layer, which has
  cut-property and Kruskal skeleton theorems but intentionally defers union-find
  and low-level implementation refinement.
- `Functional Algorithms Design` is a Lean adaptation of `Algorithm Design with
  Haskell`; it reimplements algorithm-design examples in Lean and makes
  informal equational reasoning machine checked:
  <https://github.com/arademaker/fad>.
- Lean also has exploratory graph-algorithm work, notably Peter Kementzey's
  2021 graph-library thesis, covering graph representations and algorithms
  including Dijkstra, Kruskal, topological sorting, and push-relabel:
  <https://lean-forward.github.io/pubs/kementzey_bsc_thesis.pdf>.

## Positioning CLRS-Lean

CLRS-Lean is currently best described as an early-to-mid-stage Lean textbook
companion and proof atlas:

- It already has a public Verso site, chapter/section structure, a proof-status
  ledger, and multiple sorry-free theorem clusters.
- Its strongest current assets are the complete Huffman optimality proof, the
  growing greedy/MST infrastructure, and a broad first pass over early CLRS
  chapters.
- It is not yet at AFP/VFA maturity.  Coverage is incomplete, several sections
  use compact functional models rather than line-by-line imperative pseudocode,
  running-time/RAM semantics are not yet systematic, and some major CLRS
  algorithms remain partial.

## Publication Implication

The most plausible near-term research claim is not "we have fully formalized
CLRS"; it is:

- a Lean-native, website-first workflow for turning textbook algorithms into
  checked theorem interfaces;
- a transparent proof map distinguishing proved, partial, deferred, and blocked
  targets;
- several chapter-scale case studies, with at least one flagship complete proof;
- an agent-assisted workflow that gradually converts textbook prose into stable
  Lean statements, proofs, and readable public pages.

For a stronger conference or journal target, CLRS-Lean should next prioritize:

- one or two deeper complete chapters or sections, especially Chapter 6
  in-place heapsort, Chapter 16 greedy algorithms, and Chapter 23 MST;
- reusable libraries for arrays, finite graphs, exchange arguments, and cost
  recurrences;
- stable theorem names and honest proof-gap labels;
- reproducible build/site metrics such as proof lines, generated page size, and
  optimization impact.
