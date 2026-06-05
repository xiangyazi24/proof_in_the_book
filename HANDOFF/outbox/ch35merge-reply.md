## Ch35 merge reply

Read `HANDOFF/TASK_Ch35merge.md`.  `HANDOFF/EULER_DESIGN_r3.md` is not present in this checkout; `find` under the repo did not locate it.

Updated `ProofsInTheBook/PlanarMapDelete.lean`.

Verified:

```bash
/data/home/xhuan5/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lake env lean ProofsInTheBook/PlanarMapDelete.lean
```

Result: passes with no warnings.  `grep` finds no `sorry`, `axiom`, or `native_decide` in `PlanarMapDelete.lean`.

What was proved:

- `deleteVertexFacesMerge_iff_face_card_eq`: the current quotient-level `DeleteVertexFacesMerge` is equivalent to equality of the actual deleted face quotient cardinal and the face model cardinal.
- `deleteVertexFacesMerge_of_F_eq`: once the deleted face count is known to be `F - deg(v) + 1` and `VertexFacesDistinct` holds, `DeleteVertexFacesMerge` follows.

Important blocker found and formalized:

- The requested unconditional deleted-star merge from `IsSphereMap`/`NoLoopAt` is false for the current dart-only closed-star deletion.
- Formal counterexample in the file: `twoEdgePathMap`, the 4-dart two-edge path.
- Proved `twoEdgePathMap_isSphereMap` and `twoEdgePathMap_noLoopAt_middle`.
- Proved the middle closed-star deletion removes every dart: `twoEdgePathMap_deleteVertexSet_middle`.
- Proved all three hoped-for automatic hypotheses fail:
  - `twoEdgePathMap_not_vertexFacesDistinct_middle`
  - `twoEdgePathMap_not_deleteVertex_vertexQuotient_middle`
  - `twoEdgePathMap_not_deleteVertexFacesMerge_middle`

Precise missing input:

The current `CombMap` model has no isolated vertices, so closed-star deletion can erase neighboring degree-1 vertices.  Therefore the vertex quotient `hQ` is not derivable from `IsSphereMap`.  Separately, bridges/cut behavior makes `VertexFacesDistinct` and the one-boundary face merge fail.  A valid theorem needs extra hypotheses excluding this, or a graph-layer deletion model that retains isolated vertices plus a topological/local boundary-cycle theorem.
