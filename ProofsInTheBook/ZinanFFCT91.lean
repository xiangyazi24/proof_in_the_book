import ProofsInTheBook.ZinanFFCT90

/-!
# `ZinanFFCT91` -- face-contiguity surface for bounded simplicity

This file isolates the exact geometric face-contiguity input needed to close
`ZinanFFCT90.BoundedFaceRunPropagation`, and proves the downstream assembly
from that input.

The new content here is intentionally non-circular:

* `face_run_consecutive_flat_at` proves the algebraic endpoint of the
  face-contiguity route: if all vertices in a run lie on the support great
  circle of the edge `(r,r+1)`, then every consecutive triple inside the run is
  coplanar, hence its `det3` vanishes.
* `FaceContiguityPropagation` is the remaining geometric statement, stated as
  a `Prop`, not introduced as a declaration.
* `boundedFaceRunPropagation_of_faceContiguity` shows that this face statement
  supplies FFCT90's exact residue, so the existing FFCT88/89/90 composition
  gives bounded simplicity and the Chapter 13 headline from it.

No proof placeholders or unsafe declarations.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT86
open ProofsInTheBook.ZinanFFCT89
open ProofsInTheBook.ZinanFFCT90

namespace ProofsInTheBook.ZinanFFCT91

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## The algebraic endpoint of face-contiguity. -/

/-- If a whole sub-run lies on the support great circle of the edge
`(r,r+1)`, then any consecutive triple contained in that run is coplanar.

The hypothesis `hface` is the determinant form of "on the support great
circle": every `P m` in `[r+1,s]` has
`det3 (P r) (P (r+1)) (P m) = 0`.  The edge `(r,r+1)` is a short arc by weak
convexity, so the two support vertices form a nondegenerate plane basis; each
of `P t`, `P(t+1)`, `P(t+2)` is a real linear combination of that basis, and
`coplanar_triple_det3_zero` closes the determinant. -/
theorem face_run_consecutive_flat_at
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hweak : WeakConvexSphArm P)
    {r s t : ℕ} (hr : r < n + 1) (hs : s < n + 1)
    (hrt : r + 1 ≤ t) (ht2s : t + 2 ≤ s)
    (hface :
      ∀ {m : ℕ} (hm : m < n + 1), r + 1 ≤ m → m ≤ s →
        det3 (P ⟨r, hr⟩ : E3) (P ⟨r + 1, by omega⟩ : E3)
          (P ⟨m, hm⟩ : E3) = 0) :
    det3 (P ⟨t, by omega⟩ : E3)
      (P ⟨t + 1, by omega⟩ : E3)
      (P ⟨t + 2, by omega⟩ : E3) = 0 := by
  have hr1 : r + 1 < n + 1 := by omega
  have hedge : ShortArc (P ⟨r, hr⟩) (P ⟨r + 1, hr1⟩) := by
    have h := hweak.closed_convex.edge_short ⟨r, hr⟩
    have hsucc :
        ((⟨r, hr⟩ : Fin (n + 1)) + 1) =
          (⟨r + 1, hr1⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (by omega)]
    simpa [hsucc] using h
  have hrepr :
      ∀ {m : ℕ} (hm : m < n + 1), r + 1 ≤ m → m ≤ s →
        ∃ a b : ℝ,
          a • (P ⟨r, hr⟩ : E3) + b • (P ⟨r + 1, hr1⟩ : E3) =
            (P ⟨m, hm⟩ : E3) := by
    intro m hm hmlo hmhi
    have hdet :
        det3 (P ⟨r, hr⟩ : E3) (P ⟨r + 1, hr1⟩ : E3)
          (P ⟨m, hm⟩ : E3) = 0 := by
      simpa using hface hm hmlo hmhi
    obtain ⟨a, b, hab⟩ :=
      lin_indep_span_of_det3_zero (P ⟨r, hr⟩).2 (P ⟨r + 1, hr1⟩).2
        (fun h => hedge.1 (S2.ext h)) hedge.2 hdet
    exact ⟨a, b, hab.symm⟩
  exact coplanar_triple_det3_zero
    (hrepr (m := t) (by omega) (by omega) (by omega))
    (hrepr (m := t + 1) (by omega) (by omega) (by omega))
    (hrepr (m := t + 2) (by omega) (by omega) (by omega))

/-- A face-contiguous run contains a consecutive flat triple.  We choose the
first fully interior triple `(r+1,r+2,r+3)`, which exists because `r+3 ≤ s`. -/
theorem face_run_consecutive_flat
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hweak : WeakConvexSphArm P)
    {r s : ℕ} (hr : r < n + 1) (hs : s < n + 1)
    (hgap : r + 3 ≤ s)
    (hface :
      ∀ {m : ℕ} (hm : m < n + 1), r + 1 ≤ m → m ≤ s →
        det3 (P ⟨r, hr⟩ : E3) (P ⟨r + 1, by omega⟩ : E3)
          (P ⟨m, hm⟩ : E3) = 0) :
    ∃ t : ℕ, ∃ ht2 : t + 2 < n + 1,
      det3 (P ⟨t, by omega⟩ : E3)
        (P ⟨t + 1, by omega⟩ : E3)
        (P ⟨t + 2, ht2⟩ : E3) = 0 := by
  refine ⟨r + 1, by omega, ?_⟩
  have hflat := face_run_consecutive_flat_at hweak hr hs
    (t := r + 1) (by omega) (by omega) hface
  simpa using hflat

/-! ## The remaining face-contiguity surface. -/

/-- The precise face-contiguity statement needed by FFCT90.

For a repeated nonadjacent pair `P r = P s` with `r+3 ≤ s`, every vertex in
the run `[r+1,s]` lies on the support great circle of the edge `(r,r+1)`.
This is the geometric face fact described in the handoff. -/
def FaceContiguityPropagation : Prop :=
  ∀ {n : ℕ} {P : Fin (n + 1) → S2},
    WeakConvexSphArm P →
    PositiveJoints P →
    (∀ i : Fin (n - 1), jointAngle P i < Real.pi) →
    ∀ {r s : ℕ} (hr : r < n + 1) (hs : s < n + 1),
      (hgap : r + 3 ≤ s) →
      P ⟨r, hr⟩ = P ⟨s, hs⟩ →
      ∀ {m : ℕ} (hm : m < n + 1), r + 1 ≤ m → m ≤ s →
        det3 (P ⟨r, hr⟩ : E3) (P ⟨r + 1, by omega⟩ : E3)
          (P ⟨m, hm⟩ : E3) = 0

/-- The gap-three endpoint of the face route, kept as a named partial target:
if the face-contiguity statement is supplied, the smallest non-digon repeated
run already has a flat consecutive triple. -/
theorem gap_three_flat_of_faceContiguity
    (hface : FaceContiguityPropagation)
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hweak : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hlt : ∀ i : Fin (n - 1), jointAngle P i < Real.pi)
    {r s : ℕ} (hr : r < n + 1) (hs : s < n + 1)
    (hgap3 : s = r + 3)
    (hrep : P ⟨r, hr⟩ = P ⟨s, hs⟩) :
    det3 (P ⟨r + 1, by omega⟩ : E3)
      (P ⟨r + 2, by omega⟩ : E3)
      (P ⟨r + 3, by omega⟩ : E3) = 0 := by
  have hgap : r + 3 ≤ s := by omega
  have hrun :
      ∀ {m : ℕ} (hm : m < n + 1), r + 1 ≤ m → m ≤ s →
        det3 (P ⟨r, hr⟩ : E3) (P ⟨r + 1, by omega⟩ : E3)
          (P ⟨m, hm⟩ : E3) = 0 :=
    hface hweak hpos hlt hr hs hgap hrep
  simpa [hgap3] using
    face_run_consecutive_flat_at hweak hr hs
      (t := r + 1) (by omega) (by omega) hrun

/-! ## FFCT90 residue and Chapter 13 composition from face-contiguity. -/

/-- Face-contiguity supplies the exact propagation surface isolated in
`ZinanFFCT90`. -/
theorem boundedFaceRunPropagation_of_faceContiguity
    (hface : FaceContiguityPropagation) :
    BoundedFaceRunPropagation := by
  intro n P hweak hpos hlt r s hr hs hgap hrep
  exact face_run_consecutive_flat hweak hr hs hgap
    (hface hweak hpos hlt hr hs hgap hrep)

/-- Bounded weak-positive simplicity follows from the face-contiguity theorem. -/
theorem boundedWeakPositiveSimplicity_of_faceContiguity
    (hface : FaceContiguityPropagation) :
    BoundedWeakPositiveSimplicity :=
  boundedWeakPositiveSimplicity_of_faceRunPropagation
    (boundedFaceRunPropagation_of_faceContiguity hface)

/-- The no-repeat theorem follows from the face-contiguity theorem. -/
theorem weakConvex_boundedJoints_noNonadjacentRepeat_of_faceContiguity
    (hface : FaceContiguityPropagation)
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hweak : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hlt : ∀ i : Fin (n - 1), jointAngle P i < Real.pi) :
    NoNonadjacentRepeat P :=
  weakConvex_boundedJoints_noNonadjacentRepeat_of_faceRunPropagation
    (boundedFaceRunPropagation_of_faceContiguity hface) hweak hpos hlt

/-- The collision endpoint branch closes from face-contiguity. -/
theorem crossPieceCollisionEndpointAtSup_of_faceContiguity
    (hface : FaceContiguityPropagation) :
    CrossPieceCollisionEndpointAtSup :=
  crossPieceCollisionEndpointAtSup_of_faceRunPropagation
    (boundedFaceRunPropagation_of_faceContiguity hface)

/-- Conditional Chapter 13 headline with the remaining input phrased as the
geometric face-contiguity theorem rather than FFCT90's coarser propagation
surface. -/
theorem spherical_arm_mono_ch13_of_faceContiguity
    (hface : FaceContiguityPropagation) :
    SphericalArmMonotone :=
  spherical_arm_mono_ch13_of_faceRunPropagation
    (boundedFaceRunPropagation_of_faceContiguity hface)

/-! ## Guards. -/

#check face_run_consecutive_flat_at
#check face_run_consecutive_flat
#check gap_three_flat_of_faceContiguity
#check boundedFaceRunPropagation_of_faceContiguity
#check boundedWeakPositiveSimplicity_of_faceContiguity
#check weakConvex_boundedJoints_noNonadjacentRepeat_of_faceContiguity
#check crossPieceCollisionEndpointAtSup_of_faceContiguity
#check spherical_arm_mono_ch13_of_faceContiguity

end ProofsInTheBook.ZinanFFCT91
