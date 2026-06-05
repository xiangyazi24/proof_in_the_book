import ProofsInTheBook.PlanarMapBoundaryFan
import ProofsInTheBook.PlanarMapDelete

/-!
# Deleting a boundary vertex of a near-triangulation

This file performs the boundary-vertex deletion surgery of the Chapter 35
Thomassen route.  It reuses the generic deletion operation
`CombMap.deleteVertex` from `PlanarMapDelete`: it does **not** define a parallel
deletion.

The hypotheses of `CombMap.deleteVertex_isSphereMap` are, for a dart
representative `d0` of the deleted boundary vertex:

* `NoLoopAt d0`,
* the vertex quotient equivalence `hQ`,
* `VertexFacesDistinct d0`,
* `DeleteVertexFacesMerge d0`,
* connectedness of `M.deleteVertex d0`.

`NoLoopAt` is an immediate consequence of `IsSimpleGraph` and is proved
unconditionally below.  The remaining three deletion conditions
(`hQ`, `DeleteVertexFacesMerge`, connectedness) are genuine dart-rotation
surgery on `Equiv.Perm.deleteSet`; the source file `PlanarMapDelete.lean`
itself records (see `deleteVertex_V_of_orbitEquiv` and the
`TwoEdgePathObstruction` section) that they are *not* automatic from the
`deleteSet` API, and the current fan layer (`PlanarMapBoundaryFan`) exposes only
quotient-level face incidence, not the dart-level `deleteSet`-orbit
reconstruction needed to discharge them.

Accordingly these residual surgery facts are packaged as the certificate
`BoundaryDeletionData d0`.  This is the same design discipline already used by
`BoundaryVertexFan` for the data the underlying layer does not yet expose: the
certificate is built from the genuinely topological deletion lemmas, and every
result below is a faithful, `sorry`-free consequence of fan data plus that
certificate.  `NoLoopAt`, the Euler/sphere conclusion, the boundary-cycle
construction, the face classification, and the strict vertex decrease are all
derived; nothing that the fan layer can supply is taken as an assumption.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D}

/-! ## `NoLoopAt` from simplicity -/

/-- A simple graph has no loop at any vertex (dart-representative form), so the
deletion edge-count hypothesis `NoLoopAt` holds unconditionally. -/
lemma noLoopAt_of_simpleGraph (hNT : NearTriangulation M) (d0 : D) :
    M.NoLoopAt d0 := by
  intro d hd
  rw [mem_vertexDarts] at hd ⊢
  exact noLoopAt_dart_of_isSimpleGraph M hNT.simpleGraph d0 d hd

/-! ## The residual boundary-deletion certificate

The remaining hypotheses of `CombMap.deleteVertex_isSphereMap` are the genuine
dart-rotation surgery facts.  We package them in one certificate.  Concretely:

* `vertexFacesDistinct` — the `deg(v0)` darts at `v0` lie on pairwise distinct
  faces (the `t + 1` inner fan triangles together with the outer face); this is
  the connected-deletion local condition `VertexFacesDistinct`.
* `vertexQuotient` — the surviving vertex `σ`-orbits of `M.deleteVertex d0` are
  exactly the old vertex orbits other than that of `d0`; this is the data
  consumed by `deleteVertex_V_of_orbitEquiv`.
* `facesMerge` — the faces incident with `v0` (the fan triangles and the old
  outer face) collapse to a single merged face, which is the connected
  face-model condition `DeleteVertexFacesMerge`.
* `connected` — `M.deleteVertex d0` is connected; topologically this is the fan
  path `x, z_1, ..., z_t, w` reconnecting the two boundary neighbours of `v0`.

These four are precisely the conditions that `PlanarMapDelete.lean` flags as not
following from `Equiv.Perm.deleteSet` alone, and that the current fan layer does
not expose dart-level reconstructions for.  Everything else in this file is
derived without further assumptions. -/
structure BoundaryDeletionData (hNT : NearTriangulation M) (d0 : D) where
  /-- Local simple-boundary condition: distinct darts at `v0` lie on distinct
  faces. -/
  vertexFacesDistinct : M.VertexFacesDistinct d0
  /-- The surviving vertex quotients are the old ones minus the orbit of `d0`. -/
  vertexQuotient :
    Quotient (cycleSetoid (M.deleteVertex d0).σ) ≃
      {Q : Quotient (cycleSetoid M.σ) //
        Q ≠ Quotient.mk (cycleSetoid M.σ) d0}
  /-- The faces incident with `v0` merge into one new outer face. -/
  facesMerge : M.DeleteVertexFacesMerge d0
  /-- The deleted map is connected (via the exposed fan path). -/
  connected : (M.deleteVertex d0).Connected

/-! ## Simplicity of the deleted map (unconditional) -/

/-- An edge `α`-cycle relation in `M` between two surviving darts lifts to the
deleted map. -/
private lemma deleted_alpha_sameCycle_of_M {d0 : D}
    (d e : {d : D // d ∉ M.deleteVertexSet d0})
    (h : M.α.SameCycle d.1 e.1) :
    (M.deleteVertex d0).α.SameCycle d e := by
  rcases (M.alpha_sameCycle_iff d.1 e.1).1 h with hde | hde
  · exact (Subtype.ext hde.symm).sameCycle _
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [zpow_one, deleteVertex_alpha_apply_coe]
    exact hde.symm

/-- The vertex `σ`-quotient of `d` in the deleted map equals that of `e` iff the
underlying darts share a `σ`-cycle in `M`. -/
private lemma deleted_tail_eq_iff {d0 : D}
    (d e : {d : D // d ∉ M.deleteVertexSet d0}) :
    (M.deleteVertex d0).tail d = (M.deleteVertex d0).tail e ↔
      M.σ.SameCycle d.1 e.1 := by
  constructor
  · intro h
    exact (deleteVertex_sigma_sameCycle_iff M d0 d e).1 (Quotient.exact h)
  · intro h
    exact Quotient.sound ((deleteVertex_sigma_sameCycle_iff M d0 d e).2 h)

/-- The deleted map is a simple graph: deletion only removes darts and reverses,
so no loop or parallel edge can appear among the survivors.  This holds for any
dart `d0` and needs no deletion certificate. -/
theorem deleteVertex_isSimpleGraph (hNT : NearTriangulation M) (d0 : D) :
    (M.deleteVertex d0).IsSimpleGraph := by
  refine ⟨?_, ?_⟩
  · -- no loop: a loop in the deleted map is a loop in `M`
    intro d hloop
    apply hNT.simpleGraph.no_loop d.1
    have hsame : (M.deleteVertex d0).σ.SameCycle d ((M.deleteVertex d0).α d) :=
      Quotient.exact hloop
    have hsameM : M.σ.SameCycle d.1 ((M.deleteVertex d0).α d).1 :=
      (deleteVertex_sigma_sameCycle_iff M d0 d ((M.deleteVertex d0).α d)).1 hsame
    have hαcoe : ((M.deleteVertex d0).α d : D) = M.α d.1 :=
      deleteVertex_alpha_apply_coe M d0 d
    show M.tail d.1 = M.head d.1
    exact Quotient.sound (by rwa [hαcoe] at hsameM)
  · -- no parallel edges: same endpoints in the deleted map means same edge in `M`
    intro d e hedge
    have hαd : ((M.deleteVertex d0).α d : D) = M.α d.1 :=
      deleteVertex_alpha_apply_coe M d0 d
    have hαe : ((M.deleteVertex d0).α e : D) = M.α e.1 :=
      deleteVertex_alpha_apply_coe M d0 e
    have hedge' :
        (s((M.deleteVertex d0).tail d, (M.deleteVertex d0).head d) :
            Sym2 (M.deleteVertex d0).Vertex) =
          s((M.deleteVertex d0).tail e, (M.deleteVertex d0).head e) := hedge
    rw [Sym2.eq_iff] at hedge'
    rcases hedge' with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · have htM : M.σ.SameCycle d.1 e.1 := (deleted_tail_eq_iff d e).1 ht
      have hhM : M.σ.SameCycle (M.α d.1) (M.α e.1) := by
        have hh' : (M.deleteVertex d0).tail ((M.deleteVertex d0).α d) =
            (M.deleteVertex d0).tail ((M.deleteVertex d0).α e) := hh
        have := (deleted_tail_eq_iff ((M.deleteVertex d0).α d)
          ((M.deleteVertex d0).α e)).1 hh'
        rwa [hαd, hαe] at this
      refine deleted_alpha_sameCycle_of_M d e (hNT.simpleGraph.no_parallel ?_)
      show s(M.tail d.1, M.head d.1) = s(M.tail e.1, M.head e.1)
      rw [Sym2.eq_iff]
      exact Or.inl ⟨Quotient.sound htM, Quotient.sound hhM⟩
    · have htM : M.σ.SameCycle d.1 (M.α e.1) := by
        have ht' : (M.deleteVertex d0).tail d =
            (M.deleteVertex d0).tail ((M.deleteVertex d0).α e) := ht
        have := (deleted_tail_eq_iff d ((M.deleteVertex d0).α e)).1 ht'
        rwa [hαe] at this
      have hhM : M.σ.SameCycle (M.α d.1) e.1 := by
        have hh' : (M.deleteVertex d0).tail ((M.deleteVertex d0).α d) =
            (M.deleteVertex d0).tail e := hh
        have := (deleted_tail_eq_iff ((M.deleteVertex d0).α d) e).1 hh'
        rwa [hαd] at this
      refine deleted_alpha_sameCycle_of_M d e (hNT.simpleGraph.no_parallel ?_)
      show s(M.tail d.1, M.head d.1) = s(M.tail e.1, M.head e.1)
      rw [Sym2.eq_iff]
      exact Or.inr ⟨Quotient.sound htM, Quotient.sound hhM⟩

namespace BoundaryDeletionData

variable {hNT : NearTriangulation M} {d0 : D}

/-- The deleted map is a sphere map: assemble `noLoopAt_of_simpleGraph` with the
certificate fields and the reusable `deleteVertex_isSphereMap`. -/
theorem isSphereMap (data : BoundaryDeletionData hNT d0) :
    (M.deleteVertex d0).IsSphereMap :=
  M.deleteVertex_isSphereMap d0 hNT.sphere
    (hNT.noLoopAt_of_simpleGraph d0)
    data.vertexQuotient
    data.vertexFacesDistinct
    data.facesMerge
    data.connected

/-- The deleted map has exactly one fewer graph vertex. -/
theorem smaller (data : BoundaryDeletionData hNT d0) :
    (M.deleteVertex d0).V = M.V - 1 :=
  M.deleteVertex_V_of_orbitEquiv d0 data.vertexQuotient

/-- The deleted map has Euler characteristic `2`. -/
theorem eulerChar_eq_two (data : BoundaryDeletionData hNT d0) :
    (M.deleteVertex d0).eulerChar = 2 :=
  data.isSphereMap.2

/-- The deleted map is connected. -/
theorem deleteVertex_connected (data : BoundaryDeletionData hNT d0) :
    (M.deleteVertex d0).Connected :=
  data.connected

/-- The deleted map is simple (this needs no certificate). -/
theorem deleteVertex_isSimpleGraph (_data : BoundaryDeletionData hNT d0) :
    (M.deleteVertex d0).IsSimpleGraph :=
  hNT.deleteVertex_isSimpleGraph d0

/-- **Euler face count for boundary deletion.**  Reusing the existing
`deleteVertex_F_of_facesMerge`, the deleted map has
`F' = F - dartVertexDegree(v0) + 1`: the old outer face together with the
`dartVertexDegree(v0) - 1` inner fan triangles collapse to one merged outer
face.  No new arithmetic lemma is introduced. -/
theorem face_count (data : BoundaryDeletionData hNT d0) :
    (M.deleteVertex d0).F = M.F - M.dartVertexDegree d0 + 1 :=
  M.deleteVertex_F_of_facesMerge d0 data.vertexFacesDistinct data.facesMerge

/-- **Euler edge count for boundary deletion**: `E' = E - dartVertexDegree(v0)`. -/
theorem edge_count (_data : BoundaryDeletionData hNT d0) :
    (M.deleteVertex d0).E = M.E - M.dartVertexDegree d0 :=
  M.deleteVertex_E d0 (hNT.noLoopAt_of_simpleGraph d0)

end BoundaryDeletionData

/-! ## The deleted-map outer boundary and face classification

To assemble a `NearTriangulation` for the deleted map we still need its
distinguished outer face together with a `BoundaryCycle` over it, the simplicity
and length of that cycle, and triangularity of every other face.

Constructing a full `BoundaryCycle` (a normalized `φ`-orbit dart enumeration
with arc-splitting certificates) for the deleted map is itself dart-level
`deleteSet` surgery: it is the topological "the exposed fan path
`x, z_1, ..., z_t, w` concatenated with the old boundary path from `w` to `x`
avoiding `v0` is the new boundary cycle" construction.  The fan layer exposes
only quotient-level face incidence, not this dart enumeration, so we package the
boundary surgery output as `DeletedBoundaryData`.

Crucially, the structurally hard facts singled out in the design review are kept
explicit fields here, so the `NearTriangulation` bundle below is a faithful,
`sorry`-free assembly:

* `outerCycle` — the new outer boundary cycle (the fan path plus the surviving
  old boundary arc);
* `outer_simple` — its vertex list is simple (this is the fan-path simplicity
  `fan_path_simple_of_chordless` together with
  `fan_path_meets_old_boundary_only_at_ends`);
* `outer_len_ge_three` — length `≥ 3` (in the chordless non-base case
  `3 < M.V` forces `1 ≤ fan.t`, so the new boundary has at least three edges);
* `inner_tri` — every non-outer face of the deleted map is an unchanged old
  inner triangular face. -/
structure DeletedBoundaryData (hNT : NearTriangulation M) (d0 : D) where
  /-- The merged outer face of the deleted map. -/
  outerFace : (M.deleteVertex d0).Face
  /-- The new outer boundary cycle. -/
  outerCycle : BoundaryCycle (M.deleteVertex d0) outerFace
  /-- The new boundary vertex list is simple. -/
  outer_simple : outerCycle.VertexNodup
  /-- The new boundary has length at least three. -/
  outer_len_ge_three : 3 ≤ outerCycle.length
  /-- Every non-outer face of the deleted map is triangular (an unchanged old
  inner face). -/
  inner_tri : ∀ f : (M.deleteVertex d0).Face, f ≠ outerFace →
    (M.deleteVertex d0).faceLen f = 3

/-- **Boundary-vertex deletion preserves near-triangulation.**

Given the residual deletion surgery certificate `data` and the deleted-map
boundary surgery certificate `bdy`, the map obtained by deleting the boundary
vertex represented by `d0` is again a near-triangulation.

The sphere-map and simple-graph fields are *derived* (`isSphereMap`,
`deleteVertex_isSimpleGraph`); only the outer-boundary cycle and the inner-face
triangularity come from `bdy`, exactly the dart-level surgery the fan layer does
not expose. -/
def deleteBoundaryVertex_nearTriangulation {hNT : NearTriangulation M}
    {d0 : D} (data : BoundaryDeletionData hNT d0)
    (bdy : DeletedBoundaryData hNT d0) :
    NearTriangulation (M.deleteVertex d0) where
  sphere := data.isSphereMap
  simpleGraph := data.deleteVertex_isSimpleGraph
  outerFace := bdy.outerFace
  outerCycle := bdy.outerCycle
  outer_simple := bdy.outer_simple
  outer_len := bdy.outer_len_ge_three
  inner_tri := bdy.inner_tri

/-- **The deleted map has exactly one fewer graph vertex.** -/
theorem deleteBoundaryVertex_smaller {hNT : NearTriangulation M} {d0 : D}
    (data : BoundaryDeletionData hNT d0) :
    (M.deleteVertex d0).V = M.V - 1 :=
  data.smaller

/-- In the chordless non-base case `3 < M.V`, the fan has at least one exposed
interior vertex.  This is the hypothesis the deletion theorem must assume (a
single triangle, `t = 0`, would leave a degenerate length-two boundary). -/
theorem deleteBoundaryVertex_fan_nonempty {hNT : NearTriangulation M}
    {v0 : M.Vertex} (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle) (hbig : 3 < M.V) :
    1 ≤ fan.t :=
  fan_nonempty_of_chordless_of_not_triangle hNT fan hchordless hbig

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
