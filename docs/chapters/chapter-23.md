# Chapter 23 - Minimum Spanning Trees

## Section 23.1 - Growing A Minimum Spanning Tree

- Lean source:
  `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean`
- Status: `partial`
- Main theorems:
  `CLRS.MST.Graph.connected_crosses_cut`,
  `CLRS.MST.FiniteGraph.minimumSpanningTree_of_mstExtending_empty`,
  `CLRS.MST.FiniteGraph.mstExtending_empty_of_minimumSpanningTree`,
  `CLRS.MST.FiniteGraph.minimumSpanningTree_iff_mstExtending_empty`,
  `CLRS.MST.FiniteGraph.exists_crossing_tree_edge_of_cut`,
  `CLRS.MST.FiniteGraph.exists_crossing_tree_edge_preserving_prefix`, and
  `CLRS.MST.safe_edge_of_lightest_crossing`

This section contains the cut-property core.  It proves the safe-edge theorem
from a bundled cut certificate and now derives a crossing tree edge from the
spanning-tree path between the endpoints of a cut-crossing edge.  It also proves
that the abstract empty-prefix `IsMSTExtending` specification is equivalent to
the concrete finite-graph `IsMinimumSpanningTree` specification.

## Section 23.2 - Kruskal And Prim

- Lean source: `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean`
- Status: `partial`
- Main theorems:
  `CLRS.MST.Graph.ExchangePath`,
  `CLRS.MST.Graph.InsertedEdgeConnection`,
  `CLRS.MST.Graph.exchangePath_connected_insert`,
  `CLRS.MST.Graph.insertedEdgeConnection_of_exchangePath`,
  `CLRS.MST.Graph.exchangePath_of_insert_connected`,
  `CLRS.MST.Graph.exchangePath_iff_insertedEdgeConnection`,
  `CLRS.MST.FiniteGraph.exchangePath_of_insert_connects_erased_edge`,
  `CLRS.MST.FiniteGraph.exchangePath_iff_insertedEdgeConnection_of_spanningTree`,
  `CLRS.MST.FiniteGraph.spanningTree_exchange_of_path_certificate`,
  `CLRS.MST.FiniteGraph.exists_replacement_spanning_tree_of_cut`,
  `CLRS.MST.FiniteGraph.cutCertificate_of_lightest_crossing`,
  `CLRS.MST.processed_prefix_excludes_of_exact_component_kruskal`,
  `CLRS.MST.cut_certificate_of_exact_component_kruskal_prefix`,
  `CLRS.MST.FiniteGraph.kruskal_spanning_tree_of_complete_exact_component`,
  `CLRS.MST.FiniteGraph.kruskal_minimum_spanning_tree_of_cycle_test`, and
  `CLRS.MST.FiniteGraph.kruskal_minimum_spanning_tree_of_complete_exact_component_empty`

The current Kruskal proof is mathematical rather than implementation-level.  It
uses an exact component oracle, sorted edge order, and safe-edge certificates.
For finite connected graphs with a complete edge scan, Lean now proves that the
exact-component Kruskal output preserves forests, spans all vertices, contains
only graph edges, and therefore is a spanning tree when started from a forest.
It also packages the empty-prefix and cycle-test optimality statements as
concrete `IsMinimumSpanningTree` theorems for finite graphs.
The exchange side is now certificate-based: an explicit `ExchangePath`
decomposition proves that adding the accepted edge and deleting a tree edge
preserves the spanning-tree property.  The new exchange-path bridge converts
between `ExchangePath` and the named cycle-style
`InsertedEdgeConnection`: inserting the new edge reconnects the endpoints of
the erased tree edge.
Union-find correctness is intentionally deferred.

Open tasks:

- derive `InsertedEdgeConnection` automatically from a canonical finite
  simple path or cycle representation;
- discharge prefix-local sorted lightness inside the full recursive optimality
  wrapper, rather than requiring a global lightness hypothesis;
- add the Prim theorem interface after Kruskal's mathematical version is stable.
