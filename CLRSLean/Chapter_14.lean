import CLRSLean.Chapter_14.Section_14_1_Order_Statistic_Trees

/-!
# Chapter 14 - Augmenting Data Structures

Chapter 14 explains how to attach auxiliary information to a data structure and
maintain enough local consistency to support stronger queries.  The first
CLRS-Lean pass formalizes the mathematical core of order-statistic trees: each
node stores a subtree size, and rank selection uses the left-subtree size to
choose a branch.  The rotation layer now exposes cached-root-size preservation,
ideal rank-selection preservation, and the corresponding augmented-selector
wrapper for well-sized trees.

## Sections

* 14.1 Order-statistic trees: {lit}`partial`.
  Main results: {lit}`CLRS.Chapter14.OSTree.storedSize_eq_realSize_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.recomputeSizes_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.keys_recomputeSizes`, and
  {lit}`CLRS.Chapter14.OSTree.keys_rotateLeft`,
  {lit}`CLRS.Chapter14.OSTree.keys_rotateRight`,
  {lit}`CLRS.Chapter14.OSTree.realSize_rotateLeft`,
  {lit}`CLRS.Chapter14.OSTree.realSize_rotateRight`,
  {lit}`CLRS.Chapter14.OSTree.storedSize_rotateLeft_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.storedSize_rotateRight_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.rankSelect?_rotateLeft`,
  {lit}`CLRS.Chapter14.OSTree.rankSelect?_rotateRight`,
  {lit}`CLRS.Chapter14.OSTree.rotateLeft_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.rotateRight_wellSized`, and
  {lit}`CLRS.Chapter14.OSTree.osSelect?_eq_rankSelect?_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.osSelect?_rotateLeft_eq_rankSelect?_of_wellSized`,
  and {lit}`CLRS.Chapter14.OSTree.osSelect?_rotateRight_eq_rankSelect?_of_wellSized`.

## Current Gaps

The current model proves the augmentation invariant and rank-selection
correctness for a functional tree, including size-preserving local rotations.
It does not yet connect those rotations to red-black balancing, interval trees,
or the full augmentation theorem from the textbook.
-/

namespace CLRS
namespace Chapter14
end Chapter14
end CLRS
