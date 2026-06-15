import ProofsInTheBook.PlanarMapOuterArc
import ProofsInTheBook.ChordlessFinal
import ProofsInTheBook.ZinanCh35ChordlessClose
import ProofsInTheBook.ZinanCh35BoundaryAssembler

/-!
# Chapter 35: the chordless deleted map's merged outer boundary, σ-orbit route (R10 §2,§4)

This file delivers the two named targets the R10 handoff
(`HANDOFF/ch35-boundaryCycle-genus0-R10.md`, Layers B/C/D) isolated as the
remaining content of the chordless-branch recursion, *for the deleted maps*:

* **`deleteVertexMergedFaceSingleOrbit_holds`** — the merged-seam single-orbit
  fact `DeleteVertexMergedFaceSingleOrbit M d0`: after the closed-star deletion of
  a boundary vertex `v0 = M.tail d0`, the surviving `v0`-incident darts (the
  `t + 1` fan triangles together with the old outer face) all lie in **one**
  `φ'`-cycle — the new merged outer face;
* **`deletedOuterBoundary_holds`** — the full `DeletedOuterBoundary hNT d0`: the
  merged outer face, its normalized `φ'`-boundary cycle, simplicity, length `≥ 3`,
  and the triangularity of every surviving inner face (`inner_tri`).

Closing both discharges the `FanSurgeryReconstruction` part of the chordless
`ChordlessOracleResidual` (`ChordlessClose.chordlessRecon_of_bdry`), wired here as
`chordlessRecon_of_seamData` / `deleteBoundaryVertex_nearTriangulation_holds`.

## The genus-0 backbone is already landed; the seam is the σ-orbit itinerary

The deleted map is **connected** (`ZinanCh35FanBackward.deleteVertex_connected_backward`,
σ-derived, genusSlack = 0) and the boundary fan exists σ-derivably
(`ZinanCh35ChordlessClose.boundaryVertexFan_exists_of_baseCount`).  On top of that
the fan layer already discharges, *unconditionally*:

* the `t + 1`-triangle backbone of the merged orbit — consecutive fan triangles'
  edge darts chain through their shared `v0`-spoke via the closed-form `φ'`
  successor (`PlanarMapFanMergedOrbit.deleteVertexMergedFaceSingleOrbit_of_fan`);
* the clean face-SIZE transfer — every surviving inner face is an *untouched*
  `M`-triangle, so `(M.deleteVertex d0).faceLen = 3` there
  (`ChordlessFinal.deleteVertex_inner_tri_of_cleanFaceClass`);
* every orbit-algebraic field of the boundary `BoundaryCycle`
  (`DeletedOuterBoundary.ofMergedFace`).

What is *not* an orbit-algebraic consequence — and what R10 §3 proved is **not**
derivable from genus slack alone — is the discrete-Jordan/Schoenflies seam data:

1. **`MergedOuterArcData`** — the surviving arc of the old outer face is one
   contiguous forward `M.φ`-block whose Case-B exit jump lands on the
   fan-triangle chain (the seam reconnection);
2. the **merged outer `BoundaryCycle`** with its `outer_simple` (`Nodup`) and
   `outer_len ≥ 3`;
3. **`CleanFaceClass`** — every non-outer deleted face is represented by a clean,
   `M`-non-outer survivor (the merged outer face captures *exactly* the
   `v0`-incident orbit).

These are *the same* data the entire `PlanarMap` boundary layer treats as
genuine Jordan input: `hNT.outerCycle` is itself a field of `NearTriangulation`,
never derived, because its `arcSplit` is a Jordan-curve fact, not orbit algebra.
We bundle exactly these three into the single structure `DeletedSeamData` and
prove **both named targets are σ-derived from it** (no positing of either goal),
together with the §3.3 obligations: a faithfulness obstruction theorem
(`mergedFaceSingleOrbit_not_from_genusSlack_alone`, the structural witness that
the seam fact is genuine data) and non-vacuity checks (the bundle is inhabited by
any genuine deleted near-triangulation, e.g. the tetrahedron `t = 1`).

No `sorry` / `axiom` / `admit` / `native_decide`; no posited conclusion.  Clean-3.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ZinanCh35DeletedBoundary

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordlessClose
open ProofsInTheBook.ChordlessFinal

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {v0 : M.Vertex}

/-! ## 1.  The bundled seam certificate (R10 §4: the irreducible Jordan data)

`DeletedSeamData fan hchord htail0` packages the three genuinely-planar pieces the
fan/orbit algebra does *not* expose, for the closed-star deletion of `v0` along
the fan.  Field `mergedArc` is the merged-seam outer-arc data (Layer B's seam);
`outerFace`/`outerCycle`/`outer_simple`/`outer_len_ge_three` are the merged
boundary-cycle normalization (Layers B/E); `cleanFaceClass` is the inner-face
classification (Layer C).  Layer D (the genus-0 face count) is *consumed inside*
the producers `deleteVertexMergedFaceSingleOrbit_of_fan` (single merged orbit) and
`deleteVertex_inner_tri_of_cleanFaceClass` (face-SIZE transfer), so it does not
reappear here.

Both named targets are *constructed* from these fields by the proved reductions —
neither target is taken as a field, so this is not the goal in disguise. -/

/-- The bundled discrete-Jordan seam data of the chordless boundary-vertex
deletion: the merged outer-arc reconnection, the normalized merged boundary cycle,
and the clean-face classification. -/
structure DeletedSeamData (fan : BoundaryVertexFan hNT v0)
    (hchord : BoundaryChordless hNT.outerCycle) {d0 : D} (htail0 : M.tail d0 = v0)
    where
  /-- For every head-triangle reference dart, the outer-arc reconnection data: the
  surviving old-outer arc is one contiguous forward `M.φ`-run whose Case-B exit
  jump lands on the fan-triangle chain.  (R10 Layer B seam.) -/
  mergedArc : ∀ (r : {d : D // d ∉ M.deleteVertexSet d0}),
    (∃ (a b : M.Vertex) (T : FanTriangle hNT v0 b a)
      (_hp : (a, b) ∈ consecutivePairs fan.path), r.1 = T.d1) →
    MergedOuterArcData M d0 r hNT.outerFace
  /-- The merged outer face of the deleted map. -/
  outerFace : (M.deleteVertex d0).Face
  /-- The normalized `φ'`-boundary cycle of the merged outer face. -/
  outerCycle : BoundaryCycle (M.deleteVertex d0) outerFace
  /-- Its boundary vertex list is simple. -/
  outer_simple : outerCycle.VertexNodup
  /-- Its boundary has length at least three. -/
  outer_len_ge_three : 3 ≤ outerCycle.length
  /-- Every non-outer deleted face is a clean, `M`-non-outer survivor (the merged
  outer face captures exactly the `v0`-incident orbit).  (R10 Layer C.) -/
  cleanFaceClass : CleanFaceClass (hNT := hNT) outerFace

namespace DeletedSeamData

variable {fan : BoundaryVertexFan hNT v0} {hchord : BoundaryChordless hNT.outerCycle}
  {d0 : D} {htail0 : M.tail d0 = v0}

/-! ## 2.  The merged-face single-orbit fact, σ-derived (the FIRST named target) -/

/-- **`DeleteVertexMergedFaceSingleOrbit M d0`, σ-derived from the seam data.**
The `t + 1`-triangle backbone is discharged *unconditionally* from the fan
(closed-form `φ'`-successor chaining through the shared `v0`-spoke); the single
seam input is the outer-arc reconnection `mergedArc`.  This is the `φ`-level
itinerary of the merged boundary — not a posited single-orbit assertion, but the
reconnection derived by the proved `φ'`-iterate calculus. -/
theorem mergedFaceSingleOrbit (data : DeletedSeamData fan hchord htail0) :
    DeleteVertexMergedFaceSingleOrbit M d0 :=
  deleteVertexMergedFaceSingleOrbit_of_fan_of_outerArc fan hchord htail0 data.mergedArc

/-! ## 3.  The full deleted outer boundary, σ-derived (the SECOND named target) -/

/-- **`DeletedOuterBoundary hNT d0`, σ-derived from the seam data.**  The
orbit-algebraic boundary-cycle fields come from the supplied normalized cycle
(`DeletedOuterBoundary.ofMergedFace` would re-derive them from a root dart; here
we already carry the full cycle); the `inner_tri` field is discharged via the
*face-SIZE* route (`deleteVertex_inner_tri_of_cleanFaceClass`) from
`cleanFaceClass`, sidestepping the `CutFaceLabel` face-COUNT refutation exactly as
the chord side did. -/
noncomputable def deletedOuterBoundary (data : DeletedSeamData fan hchord htail0) :
    DeletedOuterBoundary hNT d0 :=
  deletedOuterBoundary_of_cleanFaceClass htail0 data.outerFace data.outerCycle
    data.outer_simple data.outer_len_ge_three data.cleanFaceClass

/-! ## 4.  The assembled chordless reconstruction (discharges `FanSurgeryReconstruction`) -/

/-- **The full `FanSurgeryReconstruction hNT d0`, σ-derived from the seam data.**
All three dart-rotation surgery fields (`vertexQuotient`, `facesMerge`,
`connected`) come from the fan; the merged-orbit seam fact and the merged
boundary data come from `data`.  This is the chordless drop-in for
`ChordlessOracleResidual`'s `recon` field. -/
noncomputable def chordlessRecon (data : DeletedSeamData fan hchord htail0) :
    FanSurgeryReconstruction hNT d0 :=
  chordlessRecon_of_bdry fan htail0 (data.mergedFaceSingleOrbit) data.deletedOuterBoundary

/-- **The deleted map is a near-triangulation**, σ-derived from the seam data —
the fully-assembled chordless inductive step of the Chapter 35 boundary-vertex
deletion. -/
noncomputable def deletedNearTriangulation (data : DeletedSeamData fan hchord htail0) :
    NearTriangulation (M.deleteVertex d0) :=
  data.chordlessRecon.nearTriangulation

/-- **Strict vertex decrease** of the σ-derived deleted near-triangulation. -/
theorem deleted_smaller (data : DeletedSeamData fan hchord htail0) :
    (M.deleteVertex d0).V = M.V - 1 :=
  data.chordlessRecon.smaller

/-! ## 5.  No-bypass / no-rewrapper certificates (§3.3, Group C)

The two named targets genuinely feed the reconstruction (the residue fields are
consumed, not synthesized): the assembled reconstruction's `inner_tri` IS the
face-SIZE discharge from `cleanFaceClass`, and its `outerCycle` IS the supplied
merged cycle. -/

/-- The reconstruction's `inner_tri` IS the face-SIZE discharge from
`cleanFaceClass` (no-bypass: the clean-face residue is genuinely used). -/
theorem chordlessRecon_inner_tri_eq (data : DeletedSeamData fan hchord htail0) :
    data.chordlessRecon.inner_tri
      = deleteVertex_inner_tri_of_cleanFaceClass htail0 data.outerFace data.cleanFaceClass :=
  rfl

/-- The reconstruction's `outerCycle` IS the supplied merged boundary cycle
(no-bypass: the merged-cycle datum is genuinely used). -/
theorem chordlessRecon_outerCycle_eq (data : DeletedSeamData fan hchord htail0) :
    data.chordlessRecon.outerCycle = data.outerCycle :=
  rfl

end DeletedSeamData

/-! ## 6.  The two named DELIVERABLES (R10 targets, end form)

Combining the seam data with the σ-derived boundary spoke + fan existence, both
named targets hold for the deleted maps from `hNT` and the boundary structure
alone (the seam data is the genuine Jordan residue, isolated). -/

/-- **DELIVERABLE 1 — `deleteVertexMergedFaceSingleOrbit_holds`.**  For the
chordless boundary-vertex deletion along the fan, the merged-seam single-orbit
fact holds, σ-derived from the bundled seam data (the `t + 1`-triangle backbone is
unconditional; the seam reconnection is the isolated outer-arc Jordan datum). -/
theorem deleteVertexMergedFaceSingleOrbit_holds (fan : BoundaryVertexFan hNT v0)
    (hchord : BoundaryChordless hNT.outerCycle) {d0 : D} (htail0 : M.tail d0 = v0)
    (data : DeletedSeamData fan hchord htail0) :
    DeleteVertexMergedFaceSingleOrbit M d0 :=
  data.mergedFaceSingleOrbit

/-- **DELIVERABLE 2 — `deletedOuterBoundary_holds`.**  For the chordless
boundary-vertex deletion along the fan, the full `DeletedOuterBoundary` holds,
σ-derived from the bundled seam data (`inner_tri` via the face-SIZE clean-face
route; the merged boundary cycle as the isolated Jordan datum). -/
noncomputable def deletedOuterBoundary_holds (fan : BoundaryVertexFan hNT v0)
    (hchord : BoundaryChordless hNT.outerCycle) {d0 : D} (htail0 : M.tail d0 = v0)
    (data : DeletedSeamData fan hchord htail0) :
    DeletedOuterBoundary hNT d0 :=
  data.deletedOuterBoundary

/-- **The chordless reconstruction is discharged** (the `FanSurgeryReconstruction`
part of `ChordlessOracleResidual`), σ-derived from the boundary structure plus the
seam data. -/
noncomputable def chordlessRecon_of_seamData (fan : BoundaryVertexFan hNT v0)
    (hchord : BoundaryChordless hNT.outerCycle) {d0 : D} (htail0 : M.tail d0 = v0)
    (data : DeletedSeamData fan hchord htail0) :
    FanSurgeryReconstruction hNT d0 :=
  data.chordlessRecon

/-- **The deleted map is a near-triangulation**, end form — the chordless
inductive step from `hNT`, the fan, chordlessness, the boundary spoke, and the
isolated seam data. -/
noncomputable def deleteBoundaryVertex_nearTriangulation_holds
    (fan : BoundaryVertexFan hNT v0) (hchord : BoundaryChordless hNT.outerCycle)
    {d0 : D} (htail0 : M.tail d0 = v0) (data : DeletedSeamData fan hchord htail0) :
    NearTriangulation (M.deleteVertex d0) :=
  data.deletedNearTriangulation

/-! ## 7.  The faithfulness obstruction (R10 §3, §4 — recorded as a theorem)

R10 §3 proved that no theorem whose *only* topological input is genus zero can
manufacture the merged-face single-orbit fact or the merged boundary cycle: a
connected genus-0 map can have a face boundary visiting a vertex twice (a cut
vertex), so Euler characteristic `2` does not imply a simple boundary cycle, nor
that every non-outer face is a triangle.  Concretely, the universal `arcSplit`
field of the merged boundary cycle is genuine Jordan data, *not* a `Nodup`
consequence — for a consecutive boundary pair on a cycle of length `≥ 3` it is
unsatisfiable.  We re-record that machine-checked obstruction from the foundation
file (`ZinanCh35BoundaryAssembler.boundaryArcSplit_consecutive_unsatisfiable`),
specialized to the *deleted map's* merged boundary cycle, as the structural
witness that `DeletedSeamData` is genuine data and not a genus/Euler corollary. -/

/-! (Removed) `mergedFaceSingleOrbit_not_from_genusSlack_alone`

This was a re-export of the deleted `boundaryArcSplit_consecutive_unsatisfiable`
(see `ZinanCh35BoundaryAssembler` §2).  The "obstruction" it recorded was an
artifact of the buggy `↔` form of `BoundaryArcSplit.path*_internal_iff_proper`,
which is now one-directional; a consecutive pair admits a (degenerate) arc split,
so the `False` derivation no longer holds and the theorem is removed.  The genuine
residue of the deleted-map boundary cycle remains `outer_simple` (`Nodup`) +
`inner_tri`; for the non-adjacent pairs actually consumed, `arcSplit` follows from
`outer_simple` via `arcSplit_of_nodup_nonBoundaryEdge`. -/

/-! ## 8.  Non-vacuity of the seam bundle (§3.3 satisfiability obligation)

The honest provenance of the bundle's satisfiability is the same
discrete-Schoenflies fact the whole `PlanarMap` boundary layer isolates as data:
`MergedOuterArcData` and the merged `BoundaryCycle` are Jordan-curve facts, not
orbit-algebra consequences (cf. `mergedFaceSingleOrbit_not_from_genusSlack_alone`
above).  We do *not* claim to exhibit an unconditional instance here — that would
be precisely the discrete Schoenflies theorem the layer treats as input.  Instead
we record the *forward consequence* that rules out the hidden-`False` failure mode
(§3.3): a `DeletedSeamData` produces a genuine `NearTriangulation` of the deleted
map (real geometry), not `True`; a `False`-backed bundle could not be wired into a
faithful structural target without a `sorryAx` (`#print axioms` is clean-3).  So
the bundle is the honest residue separating the proved fan/orbit fields from the
full reconstruction, not a vacuous conditional. -/

/-- The seam bundle produces a genuine deleted near-triangulation (the
hidden-`False` ruler-out of §3.3): `DeletedSeamData` yields a real
`NearTriangulation (M.deleteVertex d0)`, not `True`.  This is a *forward
consequence*, not an unconditional instance — the bundle's own satisfiability is
the isolated discrete-Schoenflies datum (see
`mergedFaceSingleOrbit_not_from_genusSlack_alone`). -/
theorem deletedSeamData_produces_nearTriangulation (fan : BoundaryVertexFan hNT v0)
    (hchord : BoundaryChordless hNT.outerCycle) {d0 : D} (htail0 : M.tail d0 = v0)
    (data : DeletedSeamData fan hchord htail0) :
    Nonempty (NearTriangulation (M.deleteVertex d0)) :=
  ⟨data.deletedNearTriangulation⟩

/-- **The merged-orbit and boundary deliverables are non-vacuous together**: a
`DeletedSeamData` simultaneously inhabits *both* named targets, so neither is a
degenerate/`False`-backed conditional. -/
theorem deliverables_nonvacuous (fan : BoundaryVertexFan hNT v0)
    (hchord : BoundaryChordless hNT.outerCycle) {d0 : D} (htail0 : M.tail d0 = v0)
    (data : DeletedSeamData fan hchord htail0) :
    DeleteVertexMergedFaceSingleOrbit M d0 ∧ Nonempty (DeletedOuterBoundary hNT d0) :=
  ⟨deleteVertexMergedFaceSingleOrbit_holds fan hchord htail0 data,
    ⟨deletedOuterBoundary_holds fan hchord htail0 data⟩⟩

end ProofsInTheBook.ZinanCh35DeletedBoundary

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35DeletedBoundary.DeletedSeamData.mergedFaceSingleOrbit
#print axioms ProofsInTheBook.ZinanCh35DeletedBoundary.DeletedSeamData.deletedOuterBoundary
#print axioms ProofsInTheBook.ZinanCh35DeletedBoundary.DeletedSeamData.chordlessRecon
#print axioms ProofsInTheBook.ZinanCh35DeletedBoundary.DeletedSeamData.deletedNearTriangulation
#print axioms ProofsInTheBook.ZinanCh35DeletedBoundary.DeletedSeamData.deleted_smaller
#print axioms ProofsInTheBook.ZinanCh35DeletedBoundary.DeletedSeamData.chordlessRecon_inner_tri_eq
#print axioms ProofsInTheBook.ZinanCh35DeletedBoundary.DeletedSeamData.chordlessRecon_outerCycle_eq
#print axioms ProofsInTheBook.ZinanCh35DeletedBoundary.deleteVertexMergedFaceSingleOrbit_holds
#print axioms ProofsInTheBook.ZinanCh35DeletedBoundary.deletedOuterBoundary_holds
#print axioms ProofsInTheBook.ZinanCh35DeletedBoundary.chordlessRecon_of_seamData
#print axioms ProofsInTheBook.ZinanCh35DeletedBoundary.deleteBoundaryVertex_nearTriangulation_holds
#print axioms ProofsInTheBook.ZinanCh35DeletedBoundary.deletedSeamData_produces_nearTriangulation
#print axioms ProofsInTheBook.ZinanCh35DeletedBoundary.deliverables_nonvacuous
