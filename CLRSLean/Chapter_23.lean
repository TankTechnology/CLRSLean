import CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim

/-!
# Chapter 23 - Minimum Spanning Trees

Chapter 23 tracks the minimum-spanning-tree proof stack.  The current focus is
the mathematical CLRS argument: safe edges, cut certificates, and Kruskal's
safe-edge induction.

## Sections

* 23.1 Growing a minimum spanning tree: `partial`.
  Main result: `CLRS.MST.safe_edge_of_lightest_crossing`.
* 23.2 Kruskal and Prim: `partial`.
  Main results: `CLRS.MST.processed_prefix_excludes_of_exact_component_kruskal`,
  `CLRS.MST.cut_certificate_of_exact_component_kruskal_prefix`,
  `CLRS.MST.FiniteGraph.kruskal_spanning_tree_of_complete_exact_component`,
  and `CLRS.MST.FiniteGraph.kruskal_optimal_of_complete_exact_component_empty`.

## Current Shape

Section 23.1 contains the cut-property core.  It proves that a light edge
crossing a cut is safe once the graph-specific exchange certificate is supplied.
The finite graph definitions, spanning-tree specification, and safe-edge
interface are already present.

Section 23.2 contains the sorted-order lightness layer, exact-component prefix
accounting, and a mathematical Kruskal skeleton.  It proves that an exact
component oracle accounts for every previously processed edge, derives the
processed-prefix exclusion invariant, and then uses sorted edge order to make
the current edge light.  For finite connected graphs with a complete edge scan,
it proves that an exact-component Kruskal pass preserves forests and returns a
spanning tree from an initial forest.  It also proves finite-graph optimality
wrappers that discharge the final spanning-tree side condition from those
structural facts.

## Deferred Work

The project intentionally defers union-find correctness in the first phase.  The
mathematical proof should stabilize before adding an implementation refinement
for the cycle test.

The main strengthening targets are:

* refine exact components to an executable union-find implementation if that
  implementation proof becomes in scope;
* construct the concrete exchange edge automatically from finite graph paths;
* discharge prefix-local sorted lightness inside the full recursive optimality
  wrapper, rather than requiring a global lightness hypothesis;
* add Prim's theorem interface after the Kruskal skeleton is complete.
-/
