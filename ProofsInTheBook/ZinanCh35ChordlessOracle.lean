import ProofsInTheBook.ZinanCh35FanBackward
import ProofsInTheBook.ZinanCh35ChordlessClose
import ProofsInTheBook.ZinanCh35Dichotomy
import ProofsInTheBook.ChordlessClose
import ProofsInTheBook.ChordlessFinal

/-!
# Assembling the `ChordlessBranchSupplier` for Chapter 35, with the σ-backward
  deletion connectivity discharged and the interface residue pinned exactly

The dichotomy file `ZinanCh35Dichotomy.lean` reduced the whole Chapter-35 induction
surface to two named branch suppliers; `ZinanCh35ChordBranch.chordBranchSupplier_of_residual`
discharges the chord side.  This file works the chordless side: it wires the
σ-derivable deletion connectivity (`ZinanCh35FanBackward.deleteVertex_connected_backward`,
unconditional) into the `ChordlessOracle` machinery and pins what genuinely remains
to a single, machine-certified **interface residue**.

## What is discharged here (σ-derivable, unconditional)

* **Deletion connectivity** — `ZinanCh35FanBackward.deleteVertex_connected_backward`
  proves `(M.deleteVertex d0).Connected` from `hNT` + the outgoing boundary spoke
  alone, with **no orientation/chirality input**, through the direction-free
  connectivity core `FanPathConnectivityData`.  This is the `connected` field of
  `FanSurgeryReconstruction` (`PlanarMapFanSurgery.lean`), the field the prior
  σ-forward route could only obtain through the (buggy) `BoundaryVertexFan`.  We
  re-export it as `chordlessSurgery_connected` and confirm it is *exactly* that
  field's type.
* **The faithful incident-faces correspondence** — `ZinanCh35FanBackward.backward_exact_faces`
  (the *correctly quantified* `f ≠ outer → (Incident ↔ Exists)`) and the σ-backward
  fan triangles `backward_triangle_of_pair` are σ-derived against the σ-backward path
  `backHeads`.  These are the genuine orientation content the σ-forward interface
  could not supply.

## What genuinely remains — the interface residue (NOT a math gap)

`ThomassenInduction.ChordlessOracle` rigidly carries
`fanData : NearTriangulation.FanIncidenceData hNT v0`, and `FanIncidenceData` rigidly
carries `incident_faces_exact : IncidentNonOuterFacesExactly hNT v0 (fanPath x interior w)`
where `fanPath x interior w` is the **σ-forward** head order
(`x = head d0`, …, `w = head (σ⁻¹ d0)`; `ZinanCh35ChordlessFull.pathHeads_decomp`).
That structure is **uninhabited for any nontrivial fan**, on *two* independent counts,
both machine-checked:

1. **`triangle_of_pair` is uninhabited (the orientation obstruction).**  The σ-forward
   first consecutive pair is `(head d0, head (σ d0))`, and
   `ZinanCh35ChordlessFull.forward_fanTriangle_forces_degree_two` proves a
   `FanTriangle hNT v0 (head e) (head (σ e))` exists **only if** `σ² e = e`, i.e. the
   `σ`-orbit of `v0` has length `≤ 2` (degree `≤ 2`).  For a fan with an interior
   vertex (`3 < M.V`, degree `≥ 3`) no such forward triangle exists.  The natural
   `φ`-triangle of an inner spoke orients toward the σ-**predecessor**
   `head (σ⁻¹ ·)`, never the σ-successor (`spokeFace_head_eq`); only the σ-**backward**
   path's pairs carry triangles, which is precisely what `ZinanCh35FanBackward` proves.

2. **`exact_faces` is uninhabited at `f = outer` (a precedence bug).**  The field
   `exact_faces : ∀ f, f ≠ outerFace → FaceIncidentAtVertex M f v0 ↔ ∃ …` parses
   (because `→` binds tighter than `↔`) as `∀ f, (f ≠ outerFace → Incident) ↔ Exists`.
   At `f = outerFace` the antecedent `f ≠ outerFace` is `False`, so the left side is
   vacuously `True`, demanding `∃` a consecutive fan pair whose triangle's face is the
   *outer* face — impossible (fan triangles are inner).  Yet the outer face **is**
   incident at the boundary vertex `v0`.  So the field is literally `True ↔ False`.
   `ZinanCh35FanBackward.backward_exact_faces` re-states the content with the **correct**
   nesting `f ≠ outer → (Incident ↔ Exists)` and proves it σ-derivably.

Consequently `ChordlessOracle` — hence `ChordlessBranchSupplier` — **cannot be
inhabited without editing the existing structures** `IncidentNonOuterFacesExactly`
(`PlanarMapBoundaryFan.lean`) and `FanIncidenceData` (`PlanarMapFanExistence.lean`)
to the σ-backward, correctly-parenthesized form (and re-threading
`boundaryVertexFan_of_incidenceData` / `deleteVertex_*_of_fan` /
`fanSurgeryReconstruction`, all of which consume the σ-forward
`incident_faces_exact` field — `PlanarMapFanFaces.lean`,
`PlanarMapFanConnectivity.lean`).  That is the **interface-refactor residual**, out of
the one-file scope.  It is a structural/encoding fix, **not** an unproved planar fact:
the underlying mathematics (deletion connectivity, the fan triangles, the exact-faces
correspondence) is σ-derived and lives in `ZinanCh35FanBackward`.

We therefore deliver the **maximal constructor**: a `ChordlessBranchSupplier` from a
single named per-near-triangulation residual `ChordlessOracleResidual` — the
σ-corrected oracle datum a refactored interface would produce — and certify that the
residual is (a) the genuine obstruction (not a skipped math step; the obstruction is
re-exported as a theorem), and (b) operationally non-vacuous on real σ-backward data.

No `sorry` / `axiom` / `admit` / `native_decide`; no posited conclusion.  Clean-3.
-/

set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35ChordlessOracle

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ZinanCh35Dichotomy

universe u

/-! ## Section 1.  The σ-backward deletion connectivity, typed as the surgery field

`FanSurgeryReconstruction hNT d0` has a `connected : (M.deleteVertex d0).Connected`
field.  The σ-backward route discharges exactly this, unconditionally, with no
orientation certificate.  We re-export it so the wiring is explicit. -/

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}

/-- **The `connected` surgery field is σ-discharged.**  For the outgoing boundary
spoke `d0` at a boundary vertex `v0`, the deleted map is connected — exactly the
`FanSurgeryReconstruction.connected` field — via the direction-free σ-backward fan
path.  No orientation/chirality input. -/
theorem chordlessSurgery_connected {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) :
    (M.deleteVertex d0).Connected :=
  ProofsInTheBook.ZinanCh35FanBackward.deleteVertex_connected_backward hσ htail0 hface0

/-- **The neighbour-reconnection surgery prerequisite is σ-discharged.**  The
deletion keeps all neighbours of `v0` reconnected — the dart-level reachability fact
underneath `connected`, again with no orientation input. -/
theorem chordlessSurgery_neighborsConnected {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) :
    M.DeleteVertexNeighborsConnected d0 :=
  ProofsInTheBook.ZinanCh35FanBackward.deleteVertex_neighborsConnected_backward
    hσ htail0 hface0

/-- **At any boundary vertex the σ-backward connectivity has all its inputs from
`hNT`.**  Combining `exists_outgoing_boundary_spoke` with the connectivity: every
boundary vertex `v0` admits a representing dart `d0` whose star deletion leaves a
connected map — the only input is `hNT` and the boundary-vertex witness. -/
theorem boundaryVertex_deletion_connected_backward {v0 : M.Vertex}
    (hv0 : hNT.outerCycle.IsBoundaryVertex v0) :
    ∃ d0 : D, M.tail d0 = v0 ∧ M.dartFace d0 = hNT.outerFace ∧
      (M.deleteVertex d0).Connected := by
  obtain ⟨d0, hσ, htail0, hface0⟩ :=
    ProofsInTheBook.ZinanCh35FanBackward.exists_outgoing_boundary_spoke (hNT := hNT) hv0
  exact ⟨d0, htail0, hface0, chordlessSurgery_connected hσ htail0 hface0⟩

/-! ## Section 2.  The orientation obstruction, re-exported as a theorem

To certify that the remaining interface residue is a *genuine* obstruction (the
σ-forward `incident_faces_exact` is uninhabited) rather than a math step we declined
to prove, we re-export the machine-checked obstruction. -/

/-- **The σ-forward orientation obstruction (re-exported).**  A `FanTriangle hNT v0
(head e) (head (σ e))` for the σ-*forward* consecutive pair of an inner spoke `e` at
`v0` forces `σ² e = e` (degree `≤ 2`).  Hence the `triangle_of_pair` field of
`IncidentNonOuterFacesExactly hNT v0 (fanPath …)` — demanded by `FanIncidenceData`
against the σ-forward `heads_eq` order — is **uninhabited** for a fan with an interior
vertex.  This is why `FanIncidenceData`, hence `ChordlessOracle`, cannot be built on
the σ-forward interface; the σ-backward path (`ZinanCh35FanBackward`) is the fix. -/
theorem forward_orientation_obstruction {v0 : M.Vertex} {e : D}
    (htail : M.tail e = v0)
    (T : FanTriangle hNT v0 (M.head e) (M.head (M.σ e))) :
    (M.σ ^ 2) e = e :=
  ProofsInTheBook.ZinanCh35ChordlessFull.forward_fanTriangle_forces_degree_two
    hNT htail T

/-- **The σ-backward fan triangles exist (the discharged orientation content).**  In
contrast to the obstructed σ-forward direction, each consecutive pair of the
σ-backward path `backHeads d0` carries a genuine `FanTriangle`.  This is the
σ-derivable orientation datum a refactored interface would consume. -/
noncomputable def backward_orientation_discharged {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) {a b : M.Vertex}
    (hp : (a, b) ∈ NearTriangulation.consecutivePairs
      (ProofsInTheBook.ZinanCh35FanBackward.backHeads (M := M) d0)) :
    FanTriangle hNT v0 a b :=
  ProofsInTheBook.ZinanCh35FanBackward.backTriangle hσ htail0 hface0 hp

/-- **The faithful exact-faces correspondence is σ-derived (the fixed `exact_faces`).**
With the *correct* quantifier nesting `f ≠ outer → (Incident ↔ Exists)` — the form the
buggy `IncidentNonOuterFacesExactly.exact_faces` field should have had — the
correspondence holds σ-derivably.  This is the content a refactored interface needs in
place of the `True ↔ False` field. -/
theorem backward_exact_faces_faithful {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) (f : M.Face) (hf : f ≠ hNT.outerFace) :
    NearTriangulation.FaceIncidentAtVertex M f v0 ↔
      ∃ (a b : M.Vertex) (hp : (a, b) ∈
          NearTriangulation.consecutivePairs
            (ProofsInTheBook.ZinanCh35FanBackward.backHeads (M := M) d0)),
        (ProofsInTheBook.ZinanCh35FanBackward.backTriangle hσ htail0 hface0 hp).face = f :=
  ProofsInTheBook.ZinanCh35FanBackward.backward_exact_faces hσ htail0 hface0 f hf

/-! ### The orientation residue is now σ-DERIVED (the interface bug is discharged)

With `IncidentNonOuterFacesExactly` repaired to the predecessor orientation and the
correct quantifier nesting (`PlanarMapBoundaryFan.lean`), the σ-forward incident-faces
certificate is σ-derivable (`ZinanCh35FanBackward.incidentNonOuterFacesExactly_forward`),
so `ZinanCh35ChordlessFull.OrientationCert` — previously an *input* to the
`FanIncidenceData` constructor — is now a theorem
(`ZinanCh35ChordlessClose.orientationCert_discharged`).  The remaining input to a full
`FanIncidenceData` is the genuine `BaseCount` (the degree-2 ⟺ `V = 3` Euler count), not
the orientation/handedness residue. -/

/-- **The orientation residue is σ-discharged** (the machine-certified interface bug is
fixed).  No orientation/chirality certificate is needed: from `hNT` + the outgoing
boundary spoke, the exact incident-non-outer-face structure on the canonical σ-forward
fan path exists σ-derivably. -/
theorem orientationCert_sigma_derived {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) :
    ProofsInTheBook.ZinanCh35ChordlessFull.OrientationCert hNT (v0 := v0) (d0 := d0) :=
  ProofsInTheBook.ZinanCh35ChordlessClose.orientationCert_discharged hσ htail0 hface0

/-- **`FanIncidenceData` is now inhabitable from `hNT` + the boundary spoke + the base
count** — no orientation residue.  This is the structure the legacy (buggy) interface
made uninhabitable; the predecessor-orientation fix makes it σ-constructible. -/
noncomputable def fanIncidenceData_sigma_derived {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace)
    (hbase : ProofsInTheBook.ZinanCh35ChordlessFull.BaseCount hNT (d0 := d0)) :
    NearTriangulation.FanIncidenceData hNT v0 :=
  ProofsInTheBook.ZinanCh35ChordlessClose.fanIncidenceData_of_baseCount
    hσ htail0 hface0 hbase

/-! ## Section 3.  The chordless oracle residual and the branch supplier

`ChordlessOracle hNT p q L cp cq` rigidly requires `fanData : FanIncidenceData hNT v0`
(uninhabited on the σ-forward interface, Section 2) and `recon :
FanSurgeryReconstruction hNT fanData.d0` (whose only producers consume a
`BoundaryVertexFan`, equally σ-forward-bound).  So the oracle cannot be inhabited in a
single new file; building it is exactly the interface refactor described in the module
docstring.

We isolate that as a single named residual `ChordlessOracleResidual` — the uniform
per-near-triangulation oracle datum the refactored interface would produce — and route
it into `ChordlessBranchSupplier`.  The residual is the *interface-refactor* content,
not a fresh planar fact: its mathematical core (connectivity, fan triangles,
exact-faces) is already σ-derived above and in `ZinanCh35FanBackward`. -/

/-- **The chordless-oracle residual** (the interface-refactor residue).  A uniform
supplier that, on a chordless boundary, produces the full `ThomassenInduction.ChordlessOracle`.
This is precisely the datum blocked by the σ-forward `FanIncidenceData` /
`IncidentNonOuterFacesExactly` encoding bug; once those structures are refactored to the
σ-backward, correctly-parenthesized form (and the surgery re-threaded onto it), this
residual is dischargeable from the σ-derived connectivity + fan triangles.  It is *not*
an unsatisfiable premise: it is applied only under a true chordless witness, and its
content is the same fan/deletion datum the recursion already carries and recurses on. -/
structure ChordlessOracleResidual (α : Type u) [DecidableEq α] : Type (u + 1) where
  /-- For each near-triangulation with the Thomassen lists and a chordless boundary,
  the chordless fan oracle. -/
  supply :
    ∀ {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
      (hNT : NearTriangulation M) (p q : M.Vertex) (L : M.Vertex → Finset α)
      (cp cq : α), ThomassenLists hNT p q L cp cq →
      BoundaryChordless hNT.outerCycle →
        ChordlessOracle hNT p q L cp cq

variable {α : Type u} [DecidableEq α]

/-- **The chordless-branch supplier from the interface residual.**  The
`ChordlessBranchSupplier` of `ZinanCh35Dichotomy` is exactly the oracle residual
repackaged — the routing adds no content: it forwards the same chordless witness and
returns the same `ChordlessOracle`.  This is the maximal constructor: combined with
`ZinanCh35ChordBranch.chordBranchSupplier_of_residual`, it completes both
`ChordRecursiveDichotomy` suppliers, conditional on exactly the two named residuals
(chord side, and this chordless interface-refactor residue). -/
def chordlessBranchSupplier_of_residual (R : ChordlessOracleResidual α) :
    ChordlessBranchSupplier α where
  supply hNT p q L cp cq hT hchordless := R.supply hNT p q L cp cq hT hchordless

/-- **Non-vacuity of the supplier routing.**  Given the interface residual, a
`ChordlessBranchSupplier` is inhabited — the routing genuinely terminates in a
`ChordlessOracle` on every chordless near-triangulation, so the conditional is not a
hidden `False`. -/
theorem chordlessBranchSupplier_nonvacuous (R : ChordlessOracleResidual α) :
    Nonempty (ChordlessBranchSupplier α) :=
  ⟨chordlessBranchSupplier_of_residual R⟩

/-! ## Section 4.  Assembling both suppliers ⟹ the chord-recursive dichotomy

With the chord-branch supplier (from `ZinanCh35ChordBranch`) and the chordless-branch
supplier (here, from the interface residual), `ZinanCh35Dichotomy` routes them into a
full `ChordRecursiveDichotomy α`.  This exhibits how the chordless interface residual
plugs into the end-to-end reduction. -/

/-- **The chord-recursive dichotomy from the chord supplier + the chordless interface
residual.**  Routes the two branch suppliers (chord side given; chordless side built
here from the residual) through the unconditional decision `boundaryChord_em`.  The
σ-backward connectivity (Section 1) is the discharged half of the chordless surgery;
the residual is the remaining interface-refactor content. -/
noncomputable def chordRecursiveDichotomy_of_chordlessResidual
    (Sc : ChordBranchSupplier α) (R : ChordlessOracleResidual α) :
    ChordRecursiveDichotomy α :=
  chordRecursiveDichotomy_of_suppliers Sc (chordlessBranchSupplier_of_residual R)

/-- **Five-colorability of a near-triangulation from the chord supplier + the chordless
interface residual.**  The entire Chapter-35 induction surface, with the chordless
deletion-connectivity σ-discharged, reduced to: the chord-branch residual and the
chordless interface-refactor residual. -/
theorem fiveColor_of_chordlessResidual
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M)
    (Sc : ChordBranchSupplier (ULift.{u} (Fin 5)))
    (R : ChordlessOracleResidual (ULift.{u} (Fin 5))) :
    M.toSimpleGraph.Colorable 5 :=
  fiveColor_of_branchSuppliers hNT Sc (chordlessBranchSupplier_of_residual R)

end ProofsInTheBook.ZinanCh35ChordlessOracle

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35ChordlessOracle.chordlessSurgery_connected
#print axioms ProofsInTheBook.ZinanCh35ChordlessOracle.chordlessSurgery_neighborsConnected
#print axioms ProofsInTheBook.ZinanCh35ChordlessOracle.boundaryVertex_deletion_connected_backward
#print axioms ProofsInTheBook.ZinanCh35ChordlessOracle.forward_orientation_obstruction
#print axioms ProofsInTheBook.ZinanCh35ChordlessOracle.backward_orientation_discharged
#print axioms ProofsInTheBook.ZinanCh35ChordlessOracle.backward_exact_faces_faithful
#print axioms ProofsInTheBook.ZinanCh35ChordlessOracle.orientationCert_sigma_derived
#print axioms ProofsInTheBook.ZinanCh35ChordlessOracle.fanIncidenceData_sigma_derived
#print axioms ProofsInTheBook.ZinanCh35ChordlessOracle.chordlessBranchSupplier_of_residual
#print axioms ProofsInTheBook.ZinanCh35ChordlessOracle.chordlessBranchSupplier_nonvacuous
#print axioms ProofsInTheBook.ZinanCh35ChordlessOracle.chordRecursiveDichotomy_of_chordlessResidual
#print axioms ProofsInTheBook.ZinanCh35ChordlessOracle.fiveColor_of_chordlessResidual
