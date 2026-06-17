import ProofsInTheBook.ZinanCh35FanBackward
import ProofsInTheBook.ZinanCh35ChordlessFull

/-!
# Discharging the σ-forward orientation residue (Chapter 35 chordless fan)

The machine-certified interface bug (commit `15bd7a6`) made
`NearTriangulation.IncidentNonOuterFacesExactly` **uninhabitable** for any nontrivial
fan, on two counts:

1. its `triangle_of_pair` field demanded a σ-**forward** `FanTriangle hNT v0 a b` for a
   forward consecutive pair `(a, b)`, which `forward_fanTriangle_forces_degree_two`
   proves forces degree `≤ 2`; the genuine `φ`-triangle of an inner spoke points to the
   σ-**predecessor**, giving the *reverse* labelling `FanTriangle hNT v0 b a`;
2. its `exact_faces` field parsed (because `→` binds tighter than `↔`) as
   `(f ≠ outer → Incident) ↔ Exists`, i.e. `True ↔ False` at `f = outerFace`.

`PlanarMapBoundaryFan.lean` now states the field in the **predecessor orientation**
`(a, b) ↦ FanTriangle hNT v0 b a` with the **correct** nesting
`f ≠ outer → (Incident ↔ Exists)`, and `ZinanCh35FanBackward.incidentNonOuterFacesExactly_forward`
inhabits it σ-derivably on the σ-forward head list `forwardHeads d0`.

This file performs the last wiring step: it transports that certificate along the
canonical decomposition `pathHeads_decomp`
(`(vertexDartList d0).map head = fanPath (head d0) canonInterior (head (σ⁻¹ d0))`) to
**discharge** `ZinanCh35ChordlessFull.OrientationCert` — the planar/handedness residue
the σ-forward `FanIncidenceData` constructor previously took as an *input*.  The
orientation obstruction is therefore resolved with no orientation/chirality input: it is
σ-derived end to end.

No `sorry` / `axiom` / `admit` / `native_decide`; no posited conclusion.  Clean-3.
-/

set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35ChordlessClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open Equiv

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}

/-- `forwardHeads d0` is exactly the canonical fan path `fanPath (head d0)
canonInterior (head (σ⁻¹ d0))` used by `OrientationCert`. -/
lemma forwardHeads_eq_canon {d0 : D} (hσ : M.σ d0 ≠ d0) :
    ProofsInTheBook.ZinanCh35FanBackward.forwardHeads (M := M) d0 =
      fanPath (M.head d0)
        (ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior (M := M) (d0 := d0))
        (M.head (M.σ.symm d0)) := by
  rw [ProofsInTheBook.ZinanCh35FanBackward.forwardHeads]
  have h := ProofsInTheBook.ZinanCh35ChordlessFull.pathHeads_decomp (M := M) hσ
  simpa only [ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior] using h

/-- **The σ-forward orientation residue is σ-derived (discharged).**  From `hNT` and
the outgoing boundary spoke `d0` at `v0` (`σ d0 ≠ d0`, `tail d0 = v0`,
`dartFace d0 = outerFace`), the `OrientationCert` — `Nonempty
(IncidentNonOuterFacesExactly hNT v0 (fanPath (head d0) canonInterior (head (σ⁻¹ d0))))`
— holds, with no orientation/chirality input.  This is the planar residue the previous
σ-forward `FanIncidenceData` constructor took as an input; the interface fix makes it a
σ-derivable theorem. -/
theorem orientationCert_discharged {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) :
    ProofsInTheBook.ZinanCh35ChordlessFull.OrientationCert hNT (v0 := v0) (d0 := d0) := by
  refine ⟨?_⟩
  rw [← forwardHeads_eq_canon hσ]
  exact ProofsInTheBook.ZinanCh35FanBackward.incidentNonOuterFacesExactly_forward
    hσ htail0 hface0

/-- **The full `FanIncidenceData` is σ-derived from `hNT` + the boundary spoke + the
base-triangle count.**  With the orientation residue discharged, the only remaining
input to `fanIncidenceData_of_orientation` is the genuine `BaseCount` (the degree-2 ⟺
`V = 3` Euler count). -/
noncomputable def fanIncidenceData_of_baseCount {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace)
    (hbase : ProofsInTheBook.ZinanCh35ChordlessFull.BaseCount hNT (d0 := d0)) :
    NearTriangulation.FanIncidenceData hNT v0 :=
  ProofsInTheBook.ZinanCh35ChordlessFull.fanIncidenceData_of_orientation hNT
    hσ htail0 hface0 (orientationCert_discharged hσ htail0 hface0) hbase

/-- **Boundary-vertex fan existence, σ-derived in the orientation residue.**  The
keystone `BoundaryVertexFan hNT v0` exists from `hNT`, the outgoing boundary spoke, and
the base-triangle count alone — the orientation/handedness residue is now σ-derived. -/
theorem boundaryVertexFan_exists_of_baseCount {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace)
    (hbase : ProofsInTheBook.ZinanCh35ChordlessFull.BaseCount hNT (d0 := d0)) :
    Nonempty (NearTriangulation.BoundaryVertexFan hNT v0) :=
  NearTriangulation.boundaryVertexFan_exists
    (fanIncidenceData_of_baseCount hσ htail0 hface0 hbase)

end ProofsInTheBook.ZinanCh35ChordlessClose

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35ChordlessClose.forwardHeads_eq_canon
#print axioms ProofsInTheBook.ZinanCh35ChordlessClose.orientationCert_discharged
#print axioms ProofsInTheBook.ZinanCh35ChordlessClose.fanIncidenceData_of_baseCount
#print axioms ProofsInTheBook.ZinanCh35ChordlessClose.boundaryVertexFan_exists_of_baseCount
