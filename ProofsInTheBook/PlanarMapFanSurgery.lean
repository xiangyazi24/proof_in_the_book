import ProofsInTheBook.PlanarMapBoundaryDelete

/-!
# Fan surgery: discharging the boundary-deletion certificates

This file sits on top of `PlanarMapBoundaryDelete`.  Its purpose is to reduce the
two boundary-deletion certificates (`BoundaryDeletionData`, `DeletedBoundaryData`)
of that file to the single genuinely dart-level reconstruction step, and to make
the deletion theorem unconditional *modulo that step*.

## What is at stake

`PlanarMapDelete.lean` proves (see its `TwoEdgePathObstruction` section) that the
quotient hypotheses of `deleteVertex_isSphereMap` do **not** follow from
`IsSphereMap` and `NoLoopAt` alone: the two-edge path is a connected sphere map,
loop-free at its middle vertex, yet its closed-star deletion erases every dart, so
the surviving σ-orbit equivalence, the φ-orbit face merge, and connectivity all
fail.  The missing ingredient is exactly the *boundary-vertex fan* local geometry:
in a near-triangulation a boundary vertex `v0` is surrounded by `t + 1` triangular
faces between its two boundary neighbours, and each neighbour still carries darts
after the star of `v0` is removed.

This file therefore packages the dart-level reconstruction as one explicit
structure `FanSurgeryReconstruction`, whose fields are precisely the four outputs
of the dart-walking surgery (the σ-orbit equivalence, the face-merge equivalence,
the deleted-map connectivity, and the new outer boundary cycle with its
combinatorial certificates).  Everything downstream — the assembly of both
`BoundaryDeletionData` and `DeletedBoundaryData`, the sphere/Euler conclusions,
the vertex-count decrease, and the final near-triangulation endpoint — is then
*derived* with no further assumption.

Several certificate fields that the boundary-deletion layer kept as black boxes are
discharged here directly from the fan and the near-triangulation invariant, namely
the `NoLoopAt` edge condition (already unconditional upstream) and the
`VertexFacesDistinct` local face-injectivity.  The remaining fields are the genuine
dart-level surgery and are honestly isolated in the reconstruction structure.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D}

/-! ## Discharging `VertexFacesDistinct` from the near-triangulation invariant

Around any vertex of a near-triangulation, two darts on the *same* face must
coincide: an inner face is a triangle whose three darts have pairwise distinct
tails (so at most one of them is based at a given vertex), and the outer face is a
simple cycle whose darts have distinct tails as well.  This discharges the local
`VertexFacesDistinct` condition with no fan or surgery input. -/

/-- In a near-triangulation, a dart whose face is an inner (triangular) face lies
in the `φ`-orbit `{d, φ d, φ² d}`, and these three darts have distinct tails. -/
lemma inner_face_dart_eq_of_same_tail (hNT : NearTriangulation M) {d e : D}
    (hd : M.dartFace d ≠ hNT.outerFace)
    (hface : M.dartFace e = M.dartFace d) (htail : M.tail e = M.tail d) :
    e = d := by
  classical
  -- The triangular face: support of the `φ`-cycle of `d` has size 3.
  have hφ : M.φ d ≠ d := phi_ne_self_of_isSimpleGraph M hNT.simpleGraph d
  have hlen : M.faceLen (M.dartFace d) = 3 := hNT.inner_tri (M.dartFace d) hd
  have hcard : (M.φ.cycleOf d).support.card = 3 := by
    rw [← faceLen_dartFace_eq_card_support_cycleOf M hφ, hlen]
  -- `e` shares the `φ`-cycle with `d`.
  have hcycle : M.φ.SameCycle d e := Quotient.exact hface.symm
  have hsupport : d ∈ M.φ.support := by simpa [Equiv.Perm.mem_support] using hφ
  obtain ⟨i, hi, hipow⟩ := hcycle.exists_pow_eq_of_mem_support hsupport
  rw [hcard] at hi
  -- The three tails are pairwise distinct.
  have hverts := faceLen_three_vertices_pairwiseDistinct M hNT.simpleGraph hlen
  interval_cases i
  · simpa using hipow.symm
  · exfalso
    have he1 : M.φ d = e := by simpa using hipow
    have : M.tail (M.φ d) = M.tail d := by rw [he1, htail]
    exact hverts.1 this.symm
  · exfalso
    have he2 : M.φ (M.φ d) = e := by
      simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hipow
    have : M.tail (M.φ (M.φ d)) = M.tail d := by rw [he2, htail]
    exact hverts.2.2 this

/-- Two darts of a near-triangulation that share the same face and the same tail
are equal.  This is the dart-level statement underlying `VertexFacesDistinct`. -/
lemma dart_eq_of_same_face_same_tail (hNT : NearTriangulation M) {d e : D}
    (hface : M.dartFace d = M.dartFace e) (htail : M.tail d = M.tail e) :
    d = e := by
  classical
  by_cases houter : M.dartFace d = hNT.outerFace
  · -- Both darts lie on the simple outer cycle; its tails are injective.
    have hdmem : d ∈ hNT.outerCycle.darts :=
      (hNT.outerCycle.mem_darts_iff d).mpr houter
    have hemem : e ∈ hNT.outerCycle.darts :=
      (hNT.outerCycle.mem_darts_iff e).mpr (hface ▸ houter)
    exact hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hdmem hemem htail
  · exact (inner_face_dart_eq_of_same_tail hNT houter hface.symm htail.symm).symm

/-- **`VertexFacesDistinct` discharged.**  In a near-triangulation, the darts at a
vertex represented by `d0` lie on pairwise distinct faces. -/
theorem vertexFacesDistinct_of_nearTriangulation (hNT : NearTriangulation M)
    (d0 : D) : M.VertexFacesDistinct d0 := by
  intro d hd e he hface
  -- `hd, he : same σ-cycle as d0`, so `tail d = tail e = tail d0`.
  have hdtail : M.tail d = M.tail d0 := by
    have : M.σ.SameCycle d0 d := by simpa [vertexDarts] using hd
    exact (Quotient.sound this.symm)
  have hetail : M.tail e = M.tail d0 := by
    have : M.σ.SameCycle d0 e := by simpa [vertexDarts] using he
    exact (Quotient.sound this.symm)
  exact dart_eq_of_same_face_same_tail hNT hface (hdtail.trans hetail.symm)

/-! ## The fan rotation enumerates the vertex dart set

The neighbor-rotation list of a fan is a complete `σ`-orbit: it is closed under
`σ` (its `consecutive_sigma` field) and nodup, so it equals the `σ`-orbit of any
of its elements.  Since every listed dart has tail `v0`, that orbit is exactly the
star of `v0`.  Hence the vertex degree of `v0` is the rotation length `= t + 2`,
the bridge from the fan to the Euler face count `F' = F - deg + 1`. -/

namespace NeighborRotationOrder

variable {v0 : M.Vertex} {neighbors : List M.Vertex}

/-- Each listed rotation dart has tail `v0`. -/
lemma tail_get (rot : NeighborRotationOrder M v0 neighbors)
    (i : Fin rot.darts.length) : M.tail (rot.darts.get i) = v0 := by
  have hmem : M.tail (rot.darts.get i) ∈ rot.darts.map M.tail :=
    List.mem_map_of_mem (List.get_mem _ _)
  rw [rot.tails_eq] at hmem
  exact List.eq_of_mem_replicate hmem

/-- Every listed rotation dart lies in the `σ`-orbit of any other (they share the
tail `v0`). -/
lemma sameCycle_get (rot : NeighborRotationOrder M v0 neighbors)
    (i j : Fin rot.darts.length) :
    M.σ.SameCycle (rot.darts.get i) (rot.darts.get j) := by
  have hi := rot.tail_get i
  have hj := rot.tail_get j
  exact Quotient.exact (hi.trans hj.symm)

/-- The rotation dart set is closed under `σ`. -/
lemma sigma_mem (rot : NeighborRotationOrder M v0 neighbors)
    {d : D} (hd : d ∈ rot.darts) : M.σ d ∈ rot.darts := by
  rw [List.mem_iff_get] at hd
  obtain ⟨i, hi⟩ := hd
  rw [← hi, ← rot.consecutive_sigma i]
  exact List.get_mem _ _

/-- The rotation list enumerates exactly the `σ`-orbit of a dart `d0` with tail
`v0`: it is closed under `σ`, nonempty, nodup, and shares the orbit of `d0`. -/
lemma vertexDarts_eq (rot : NeighborRotationOrder M v0 neighbors)
    {d0 : D} (htail : M.tail d0 = v0) :
    M.vertexDarts d0 = rot.darts.toFinset := by
  classical
  -- A representative dart of the list.
  set d1 : D := rot.darts.get ⟨0, rot.darts_nonempty⟩ with hd1
  have hd1_mem : d1 ∈ rot.darts := List.get_mem _ _
  have hd1_tail : M.tail d1 = v0 := rot.tail_get ⟨0, rot.darts_nonempty⟩
  have hsame01 : M.σ.SameCycle d0 d1 := Quotient.exact (htail.trans hd1_tail.symm)
  ext e
  rw [mem_vertexDarts, List.mem_toFinset]
  constructor
  · -- `σ.SameCycle d0 e → e ∈ list`.  Move along the orbit from `d1` to `e`.
    intro he
    have hse : M.σ.SameCycle d1 e := hsame01.symm.trans he
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (M.σ ^ n) d1 = e :=
      Equiv.Perm.SameCycle.exists_nat_pow_eq hse
    -- climb `n` steps of `σ` from `d1`, staying inside the σ-closed list.
    have hclosed : ∀ m : ℕ, (M.σ ^ m) d1 ∈ rot.darts := by
      intro m
      induction m with
      | zero => simpa using hd1_mem
      | succ m ih =>
          have hstep : (M.σ ^ (m + 1)) d1 = M.σ ((M.σ ^ m) d1) := by
            rw [pow_succ']; rfl
          rw [hstep]
          exact rot.sigma_mem ih
    rw [← hn]; exact hclosed n
  · -- `e ∈ list → σ.SameCycle d0 e`.
    intro he
    rw [List.mem_iff_get] at he
    obtain ⟨j, hj⟩ := he
    have hetail : M.tail (rot.darts.get j) = v0 := rot.tail_get j
    rw [← hj]
    exact Quotient.exact (htail.trans hetail.symm)

/-- The vertex degree of `v0` equals the rotation length. -/
lemma dartVertexDegree_eq (rot : NeighborRotationOrder M v0 neighbors)
    {d0 : D} (htail : M.tail d0 = v0) :
    M.dartVertexDegree d0 = rot.darts.length := by
  classical
  rw [dartVertexDegree, rot.vertexDarts_eq htail,
    List.toFinset_card_of_nodup rot.darts_nodup]

/-- The rotation length equals the neighbor-list length. -/
lemma length_eq_neighbors_length (rot : NeighborRotationOrder M v0 neighbors) :
    rot.darts.length = neighbors.length := by
  have := congrArg List.length rot.heads_eq
  simpa using this

end NeighborRotationOrder

/-- The vertex degree of `v0` equals `t + 2`, where `t` is the number of interior
fan vertices: the fan rotation has one dart per neighbor, and the neighbour list
`x, z₁, …, z_t, w` has `t + 2` entries.  This is the fan-to-degree bridge feeding
the Euler face count `F' = F - (t + 2) + 1` for the deletion. -/
theorem dartVertexDegree_eq_fan_t_add_two {hNT : NearTriangulation M}
    {v0 : M.Vertex} (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail : M.tail d0 = v0) :
    M.dartVertexDegree d0 = fan.t + 2 := by
  have hdeg := fan.rotation_order.dartVertexDegree_eq htail
  have hlen := fan.rotation_order.length_eq_neighbors_length
  rw [hdeg, hlen]
  -- `neighbors = fanPath x interior w = x :: interior ++ [w]`, length `t + 2`.
  show (fanPath fan.x fan.interior fan.w).length = fan.t + 2
  simp only [fanPath, BoundaryVertexFan.t, List.length_cons, List.length_append,
    List.length_nil]

/-! ## The irreducible dart-level reconstruction

The remaining content of a boundary-vertex deletion is the genuine dart-rotation
surgery on `Equiv.Perm.deleteSet` that `PlanarMapDelete.lean` flags as not
following from the `deleteSet` API.  Concretely, after removing the closed star of
`v0`:

* every surviving `σ`-orbit is one of the old vertex orbits other than `⟦d0⟧`, and
  each such orbit keeps a representative (this is where the boundary-fan geometry
  is needed: the two boundary neighbours and each interior fan vertex retain darts
  — contrast the two-edge-path obstruction, where a degree-one neighbour loses all
  of its darts);
* the faces incident with `v0` (the `t + 1` fan triangles together with the old
  outer face) collapse to a single new outer face, while every other face survives
  unchanged;
* the deleted map is connected, the fan path `x, z₁, …, z_t, w` reconnecting the
  two boundary neighbours of `v0`;
* that fan path concatenated with the surviving old boundary arc is the new outer
  boundary cycle.

These are bundled as the explicit reconstruction below, together with the
triangularity of the surviving (non-outer) faces, which is part of the same
face-correspondence surgery output.  Two of the original deletion-certificate
fields are **not** included because they are now proved directly here: `NoLoopAt`
(unconditional, upstream `noLoopAt_of_simpleGraph`) and `VertexFacesDistinct`
(`vertexFacesDistinct_of_nearTriangulation`, above).  Everything else in this file
— both deletion certificates, the sphere/Euler conclusions, the vertex-count
decrease, the fan-to-degree bridge, and the near-triangulation endpoint — is a
`sorry`-free consequence of this reconstruction together with the
near-triangulation invariant. -/

/-- The dart-level output of the boundary-vertex deletion surgery at the boundary
vertex represented by `d0`.  Its fields are exactly the equivalences /
connectivity / boundary cycle that the `deleteSet`-based `deleteVertex` operation
does not produce automatically (see the `TwoEdgePathObstruction` section of
`PlanarMapDelete`), specialized to a chordless boundary vertex via the fan. -/
structure FanSurgeryReconstruction (hNT : NearTriangulation M) (d0 : D) where
  /-- The surviving vertex `σ`-orbits are the old ones minus `⟦d0⟧`. -/
  vertexQuotient :
    Quotient (cycleSetoid (M.deleteVertex d0).σ) ≃
      {Q : Quotient (cycleSetoid M.σ) //
        Q ≠ Quotient.mk (cycleSetoid M.σ) d0}
  /-- The faces incident with `v0` merge into one new outer face. -/
  facesMerge : M.DeleteVertexFacesMerge d0
  /-- The deleted map is connected. -/
  connected : (M.deleteVertex d0).Connected
  /-- The merged outer face of the deleted map. -/
  outerFace : (M.deleteVertex d0).Face
  /-- The new outer boundary cycle (fan path plus surviving old boundary arc). -/
  outerCycle : BoundaryCycle (M.deleteVertex d0) outerFace
  /-- The new boundary vertex list is simple. -/
  outer_simple : outerCycle.VertexNodup
  /-- The new boundary has length at least three. -/
  outer_len_ge_three : 3 ≤ outerCycle.length
  /-- Every non-outer face of the deleted map is an unchanged old inner triangle. -/
  inner_tri : ∀ f : (M.deleteVertex d0).Face, f ≠ outerFace →
    (M.deleteVertex d0).faceLen f = 3

namespace FanSurgeryReconstruction

variable {hNT : NearTriangulation M} {d0 : D}

/-- Assemble the `BoundaryDeletionData` certificate of `PlanarMapBoundaryDelete`
from the reconstruction.  The two locally-provable fields (`VertexFacesDistinct`)
are supplied by `vertexFacesDistinct_of_nearTriangulation`; the genuinely
dart-level fields come from the reconstruction. -/
def toBoundaryDeletionData (R : FanSurgeryReconstruction hNT d0) :
    BoundaryDeletionData hNT d0 where
  vertexFacesDistinct := hNT.vertexFacesDistinct_of_nearTriangulation d0
  vertexQuotient := R.vertexQuotient
  facesMerge := R.facesMerge
  connected := R.connected

/-- Assemble the `DeletedBoundaryData` certificate from the reconstruction. -/
def toDeletedBoundaryData (R : FanSurgeryReconstruction hNT d0) :
    DeletedBoundaryData hNT d0 where
  outerFace := R.outerFace
  outerCycle := R.outerCycle
  outer_simple := R.outer_simple
  outer_len_ge_three := R.outer_len_ge_three
  inner_tri := R.inner_tri

/-- **The deleted map is a near-triangulation, derived from the reconstruction.**

This is the headline endpoint: given the dart-level reconstruction `R`, deleting
the boundary vertex represented by `d0` again yields a near-triangulation.  Every
hypothesis of `deleteBoundaryVertex_nearTriangulation` is supplied — the locally
provable ones (`NoLoopAt`, `VertexFacesDistinct`) discharged here, the genuinely
dart-level ones taken from `R`. -/
def nearTriangulation (R : FanSurgeryReconstruction hNT d0) :
    NearTriangulation (M.deleteVertex d0) :=
  deleteBoundaryVertex_nearTriangulation R.toBoundaryDeletionData R.toDeletedBoundaryData

/-- The deleted map has exactly one fewer graph vertex. -/
theorem smaller (R : FanSurgeryReconstruction hNT d0) :
    (M.deleteVertex d0).V = M.V - 1 :=
  R.toBoundaryDeletionData.smaller

/-- Euler face count for the deletion: `F' = F - deg(v0) + 1`. -/
theorem face_count (R : FanSurgeryReconstruction hNT d0) :
    (M.deleteVertex d0).F = M.F - M.dartVertexDegree d0 + 1 :=
  R.toBoundaryDeletionData.face_count

/-- Euler edge count for the deletion: `E' = E - deg(v0)`. -/
theorem edge_count (R : FanSurgeryReconstruction hNT d0) :
    (M.deleteVertex d0).E = M.E - M.dartVertexDegree d0 :=
  R.toBoundaryDeletionData.edge_count

/-- Euler face count in fan terms: `F' = F - (t + 2) + 1`. -/
theorem face_count_fan {v0 : M.Vertex} (fan : BoundaryVertexFan hNT v0)
    (R : FanSurgeryReconstruction hNT d0) (htail : M.tail d0 = v0) :
    (M.deleteVertex d0).F = M.F - (fan.t + 2) + 1 := by
  rw [R.face_count, dartVertexDegree_eq_fan_t_add_two fan htail]

/-- Euler edge count in fan terms: `E' = E - (t + 2)`. -/
theorem edge_count_fan {v0 : M.Vertex} (fan : BoundaryVertexFan hNT v0)
    (R : FanSurgeryReconstruction hNT d0) (htail : M.tail d0 = v0) :
    (M.deleteVertex d0).E = M.E - (fan.t + 2) := by
  rw [R.edge_count, dartVertexDegree_eq_fan_t_add_two fan htail]

end FanSurgeryReconstruction

/-! ## The unconditional endpoint modulo the dart-level reconstruction

Combining the discharged local conditions with the reconstruction, the boundary
deletion theorem holds with `BoundaryDeletionData` and `DeletedBoundaryData`
eliminated as separate inputs: a single `FanSurgeryReconstruction` (plus the
near-triangulation and the chordless / large-vertex-count hypotheses of the
inductive step) suffices. -/

/-- **Boundary-vertex deletion preserves near-triangulation (reconstruction
form).**  Given only the dart-level reconstruction `R` at the boundary vertex
represented by `d0`, the deleted map is again a near-triangulation.  Both
deletion certificates of `PlanarMapBoundaryDelete` are eliminated as separate
inputs; the locally-provable `NoLoopAt` and `VertexFacesDistinct` conditions are
discharged internally. -/
def deleteBoundaryVertex_nearTriangulation_unconditional
    {hNT : NearTriangulation M} {d0 : D}
    (R : FanSurgeryReconstruction hNT d0) :
    NearTriangulation (M.deleteVertex d0) :=
  R.nearTriangulation

/-- **Strict vertex decrease for the deletion.** -/
theorem deleteBoundaryVertex_smaller_unconditional
    {hNT : NearTriangulation M} {d0 : D}
    (R : FanSurgeryReconstruction hNT d0) :
    (M.deleteVertex d0).V = M.V - 1 :=
  R.smaller

/-- **Fan-driven inductive step.**  Packaging the deletion together with the fan
and the chordless / large-vertex hypotheses: the deleted map is a
near-triangulation *and* the fan is genuinely nonempty (`1 ≤ fan.t`), so the
boundary has strictly shrunk and the Thomassen induction can proceed. -/
def deleteBoundaryVertex_inductiveStep
    {hNT : NearTriangulation M} {v0 : M.Vertex} {d0 : D}
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle) (hbig : 3 < M.V)
    (R : FanSurgeryReconstruction hNT d0) :
    NearTriangulation (M.deleteVertex d0) ×' (1 ≤ fan.t) :=
  ⟨R.nearTriangulation,
    deleteBoundaryVertex_fan_nonempty fan hchordless hbig⟩

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
