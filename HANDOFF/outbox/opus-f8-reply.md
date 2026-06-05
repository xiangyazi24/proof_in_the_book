# File 8 reply: `ProofsInTheBook/PlanarMapBoundaryDelete.lean`

## Status

Compiles clean (`lake env lean` + full `lake build ProofsInTheBook.PlanarMapBoundaryDelete`,
8426 jobs, no error). 0 `sorry` / `axiom` / `admit`. `#print axioms` on every public
result returns exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx`,
no custom axiom, no `ofReduceBool`/`native_decide`.

Imports: `ProofsInTheBook.PlanarMapBoundaryFan`, `ProofsInTheBook.PlanarMapDelete`.
Reuses `CombMap.deleteVertex` and friends; defines **no** parallel deletion.

## What is proved UNCONDITIONALLY (no certificate)

* `NearTriangulation.noLoopAt_of_simpleGraph (hNT) (d0 : D) : M.NoLoopAt d0`
  — the deletion edge-count hypothesis, straight from `IsSimpleGraph` via
  `noLoopAt_dart_of_isSimpleGraph`.
* `NearTriangulation.deleteVertex_isSimpleGraph (hNT) (d0 : D) :
  (M.deleteVertex d0).IsSimpleGraph` — deleting darts/reverses cannot create a
  loop or parallel edge. Both `no_loop` and `no_parallel` are transported from
  `M` through `deleteVertex_sigma_sameCycle_iff` / `deleteVertex_alpha_apply_coe`
  (helpers `deleted_tail_eq_iff`, `deleted_alpha_sameCycle_of_M`). This needs no
  deletion certificate.
* `deleteBoundaryVertex_fan_nonempty (fan) (hchordless) (hbig : 3 < M.V) :
  1 ≤ fan.t` — the mandatory non-base-case fact (single triangle `t=0` would
  leave a degenerate length-2 boundary), forwarded from
  `fan_nonempty_of_chordless_of_not_triangle`.

## The two certificates (the genuine dart-rotation surgery)

The hypotheses of `deleteVertex_isSphereMap` that `PlanarMapDelete.lean` itself
flags as **not** following from `Equiv.Perm.deleteSet` (see its
`deleteVertex_V_of_orbitEquiv` docstring and the `TwoEdgePathObstruction`
section), and that the current fan layer exposes no dart-level reconstruction
for, are packaged honestly rather than faked:

```
structure BoundaryDeletionData (hNT : NearTriangulation M) (d0 : D) where
  vertexFacesDistinct : M.VertexFacesDistinct d0
  vertexQuotient : Quotient (cycleSetoid (M.deleteVertex d0).σ)
                     ≃ {Q : M.Vertex // Q ≠ ⟦d0⟧}
  facesMerge : M.DeleteVertexFacesMerge d0
  connected : (M.deleteVertex d0).Connected

structure DeletedBoundaryData (hNT : NearTriangulation M) (d0 : D) where
  outerFace : (M.deleteVertex d0).Face
  outerCycle : BoundaryCycle (M.deleteVertex d0) outerFace
  outer_simple : outerCycle.VertexNodup
  outer_len_ge_three : 3 ≤ outerCycle.length
  inner_tri : ∀ f, f ≠ outerFace → (M.deleteVertex d0).faceLen f = 3
```

These fields are all TRUE for a genuine chordless boundary-vertex deletion of a
near-triangulation (Thomassen's construction; the tetrahedron `t=1` deletion is
a concrete witness), so the conditional theorems are NOT vacuous.

## Derived from `BoundaryDeletionData` (reusing the existing machinery)

* `BoundaryDeletionData.isSphereMap : (M.deleteVertex d0).IsSphereMap`
  — `deleteVertex_isSphereMap hNT.sphere (noLoopAt …) vertexQuotient
    vertexFacesDistinct facesMerge connected`.
* `BoundaryDeletionData.smaller : (M.deleteVertex d0).V = M.V - 1`
  — `deleteVertex_V_of_orbitEquiv`.
* `BoundaryDeletionData.eulerChar_eq_two`, `deleteVertex_connected`,
  `deleteVertex_isSimpleGraph`.
* `BoundaryDeletionData.face_count : (M.deleteVertex d0).F = M.F - dartVertexDegree d0 + 1`
  — exactly the "Euler count for deletion" item, via the existing
  `deleteVertex_F_of_facesMerge` (no new arithmetic).
* `BoundaryDeletionData.edge_count : (M.deleteVertex d0).E = M.E - dartVertexDegree d0`.

## Headline bundles

* `deleteBoundaryVertex_nearTriangulation (data : BoundaryDeletionData hNT d0)
  (bdy : DeletedBoundaryData hNT d0) : NearTriangulation (M.deleteVertex d0)`
  — `sphere` and `simpleGraph` fields are DERIVED; only the outer-boundary cycle
  and inner-face triangularity come from `bdy`.
* `deleteBoundaryVertex_smaller (data) : (M.deleteVertex d0).V = M.V - 1`.

## Honest faithfulness verdict (Group C)

**CONDITIONAL-honest.** The dart-level `deleteSet` surgery — (a) surviving
`σ`-orbits = old orbits minus `⟦d0⟧`, (b) the fan triangles + old outer face
merge to one face, (c) connectivity via the fan path
`x,z_1,…,z_t,w`, (d) construction of the new outer `BoundaryCycle` (fan path
concatenated with the surviving old boundary arc, with its `VertexNodup`,
`outer_len ≥ 3`, and `inner_tri` classification) — is **real mathematical
content that this file assumes via the two certificates, not discharged.** It is
the same design discipline `BoundaryVertexFan` (file 7) already uses for data
the underlying layer does not expose. Everything the fan/simplicity layer *can*
supply (`NoLoopAt`, full simplicity of the deleted map, Euler edge/face counts,
sphere assembly, vertex decrease) is proved with no extra assumption.

## Recommended follow-up (to close the certificates)

To make the deletion theorem unconditional one must build, at the dart level:
the `deleteSet` σ-orbit equivalence, the φ-orbit face-merge equivalence, deleted
connectivity from the fan path, and the new `BoundaryCycle` enumeration. These
need a fan API that exposes `fan.rotation_order.darts = vertexDarts d0` as a set
and a normalized vertex-rotation list (file 7 notes File 3 does not yet expose
this). That is a separate surgery file, not derivable from the current
quotient-level fan certificate.

## Public API (all under `…PlanarMap.CombMap.NearTriangulation`)

```
noLoopAt_of_simpleGraph
deleteVertex_isSimpleGraph                      -- (hNT) (d0), unconditional
deleteBoundaryVertex_fan_nonempty
structure BoundaryDeletionData
  .isSphereMap .smaller .eulerChar_eq_two
  .deleteVertex_connected .deleteVertex_isSimpleGraph
  .face_count .edge_count
structure DeletedBoundaryData
deleteBoundaryVertex_nearTriangulation
deleteBoundaryVertex_smaller
```
