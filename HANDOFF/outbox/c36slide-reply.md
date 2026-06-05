2026-06-05 08:52 CDT

Created `ProofsInTheBook/PolygonDiagonal.lean`, importing only
`ProofsInTheBook.PolygonSubstrate`.

Lean checks run:

```text
/home/xhuan5/.elan/bin/lake build ProofsInTheBook.PolygonSubstrate
/home/xhuan5/.elan/bin/lake build ProofsInTheBook.PolygonDiagonal
/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/PolygonDiagonal.lean
```

All passed.  `grep -n "sorry\|axiom\|admit"` on `PolygonDiagonal.lean` and
`PolygonSubstrate.lean` returns nothing.

What is in the new file:

- A3 definitions:
  - `IsConvexVertex` as adjacent closed-triangle containment in `ClosedRegion`.
  - `adjacentTriangle`.
  - `verticesInAdjacentTriangle`.
  - `heightTowardA`.
- Proved A3 finite/linear facts:
  - `convex_vertex_triangle_subset_closedRegion`.
  - `mem_verticesInAdjacentTriangle_iff`.
  - `orient_base_left`, `orient_base_right`.
  - `heightTowardA_base_left`, `heightTowardA_base_right`,
    `heightTowardA_apex`.
  - `slide_last_vertex_exists` from `Finset.exists_max_image`.
- Exact A3 target statements:
  - `exists_convex_vertex_statement`.
  - `convex_vertex_empty_triangle_gives_ear_statement`.
  - `slide_last_vertex_gives_diagonal_statement`.
  - `exists_diagonal_statement`.
  - bundled as `A3GeometryFacts`, with projection lemmas.
- A4 tuple/index layer:
  - `leftLength`, `rightLength`.
  - `leftIndex`, `rightIndex`.
  - `subpolygonLeftTuple`, `subpolygonRightTuple`, `deleteVertexTuple`.
  - length lemmas `leftLength_add_rightLength`,
    `leftLength_add_rightLength_of_diagonal`,
    `leftLength_le_total_of_diagonal`,
    `rightLength_le_total_of_diagonal`.
- Exact A4 target statements and conditional API:
  - `diagonal_split_left_strict_statement`.
  - `diagonal_split_right_strict_statement`.
  - `ear_delete_strict_statement`.
  - `diagonal_split_region_union_statement`.
  - `diagonal_split_region_intersection_statement`.
  - `ear_delete_region_union_statement`.
  - bundled as `A4CuttingFacts`, with `subpolygonLeft`,
    `subpolygonRight`, `deleteVertex`, and region projection lemmas.
  - The handoff names also exist as conditional aliases taking the relevant
    facts bundle, e.g. `exists_diagonal G hn`,
    `diagonal_split_left_strict G hdiag`,
    `diagonal_split_region_union G hdiag ...`, and
    `ear_delete_region_union G hdiag ...`.

Important limitation:

The current `PolygonSubstrate` API does not contain enough planar topology or
ray-crossing invariance to prove the full A3/A4 geometry unconditionally.  In
particular, `exists_convex_vertex`, the empty-triangle-to-ear diagonal theorem,
`slide_last_vertex_gives_diagonal`, `exists_diagonal`, strictness of the
constructed subpolygons, and the region split equalities all require new
geometric lemmas beyond the A0-A2 substrate.  I therefore did not introduce
global axioms/constants or fake proofs.  The missing goals are isolated as
exact named statement definitions and bundled evidence structures, so later
work can fill them without changing downstream signatures.
