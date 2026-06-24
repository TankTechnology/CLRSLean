# Chapter 23 - Minimum Spanning Trees

## Section 23.1 - Growing A Minimum Spanning Tree

- Lean source:
  `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean`
- Status: `partial`
- Main theorem: `CLRS.MST.safe_edge_of_lightest_crossing`

This section contains the cut-property core.  It proves the safe-edge theorem
from a bundled cut certificate.  The remaining work is the concrete graph lemma
that constructs the exchange edge from a spanning-tree path or cycle.

## Section 23.2 - Kruskal And Prim

- Lean source: `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean`
- Status: `partial`
- Main theorems:
  `CLRS.MST.processed_prefix_excludes_of_exact_component_kruskal`,
  `CLRS.MST.cut_certificate_of_exact_component_kruskal_prefix`,
  `CLRS.MST.FiniteGraph.kruskal_spanning_tree_of_complete_exact_component`, and
  `CLRS.MST.FiniteGraph.kruskal_optimal_of_complete_exact_component_empty`

The current Kruskal proof is mathematical rather than implementation-level.  It
uses an exact component oracle, sorted edge order, and safe-edge certificates.
For finite connected graphs with a complete edge scan, Lean now proves that the
exact-component Kruskal output preserves forests, spans all vertices, contains
only graph edges, and therefore is a spanning tree when started from a forest.
Union-find correctness is intentionally deferred.

Open tasks:

- construct the concrete exchange edge from finite graph paths or cycles;
- discharge prefix-local sorted lightness inside the full recursive optimality
  wrapper, rather than requiring a global lightness hypothesis;
- add the Prim theorem interface after Kruskal's mathematical version is stable.
