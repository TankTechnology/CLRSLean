# Chapter 18 - B-Trees

- Status: `partial`
- Lean entry: `CLRSLean/Chapter_18.lean`
- Interface test: `Tests/Chapter_18_Interface.lean`

## Proved First-Pass Surface

- `CLRS.Chapter18.BTree.search_correct`
- `CLRS.Chapter18.BTree.minKeys_lower_bound`
- `CLRS.Chapter18.BTree.splitChild_preserves_model`
- `CLRS.Chapter18.BTree.insert_preserves_model`
- `CLRS.Chapter18.BTree.insert_mem_iff`

## Remaining Work

The current chapter uses a mathematical key-membership model and specification
wrappers for split/insert.  Full separator ordering, same-depth leaves, deletion,
disk-page I/O, and pointer-level mutation remain future refinements.
