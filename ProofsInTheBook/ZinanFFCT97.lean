import ProofsInTheBook.ZinanFFCT95
import ProofsInTheBook.ZinanFFCT68

/-!
# `ZinanFFCT97` -- opened WBS gnomonic single-wind layer

This file builds the spherical and gnomonic data for the opened WBS arm at the
support-stuck supremum.  The remaining planar content is isolated as
`OpenedWBSPlanarLiftedTurnSpanExists`: from weak planar edge supports,
nonzero edges, strict consecutive turns, and an orthonormal affine frame,
produce the lifted turn span with total turn below one full wind.

The residue is premise-respecting.  Its hypotheses are realised by ordinary
strict convex planar chains; for example `ZinanFFCT94.witChain_certificate`
gives a concrete lifted certificate for a three-vertex chain with positive
turn and small total span.
-/

noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT8
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT89
open ProofsInTheBook.ZinanFFCT92
open ProofsInTheBook.ZinanFFCT94
open ProofsInTheBook.ZinanFFCT95

namespace ProofsInTheBook.ZinanFFCT97

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-- The planar lifted-turn residue needed by the opened WBS arm.

For a chain in an affine plane with an orthonormal frame, weak edge supports,
nonzero cyclic edges, and strict positive consecutive interior turns, produce a
full `PlanarLiftedTurnSpan`.  The `one_wind` field of that structure is the
remaining total-turning input. -/
def OpenedWBSPlanarLiftedTurnSpanExists : Prop :=
  ∀ {n : ℕ} (Q : Fin (n + 1) → E3) (h u v : E3),
    (⟪h, u⟫ : ℝ) = 0 → (⟪h, v⟫ : ℝ) = 0 →
    (⟪u, u⟫ : ℝ) = 1 → (⟪v, v⟫ : ℝ) = 1 → (⟪u, v⟫ : ℝ) = 0 →
    (∀ i : Fin (n + 1), (⟪h, Q i⟫ : ℝ) = 1) →
    (∀ i j : Fin (n + 1), 0 ≤ det3 (Q i) (Q (i + 1)) (Q j)) →
    (∀ i : Fin (n + 1), Q i ≠ Q (i + 1)) →
    (∀ r : ℕ, ∀ hr2 : r + 2 < n + 1,
      0 < det3 (Q ⟨r, by omega⟩) (Q ⟨r + 1, by omega⟩) (Q ⟨r + 2, hr2⟩)) →
    Nonempty (PlanarLiftedTurnSpan Q h u v)

/-- The opened WBS arm carries a gnomonic single-wind certificate, modulo the
single planar lifted-turn residue. -/
noncomputable def openedWBS_gnomonicSingleWind
    (hres : OpenedWBSPlanarLiftedTurnSpanExists)
    {n : ℕ} (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k)
    (hstuck : SupportStuckWBS A B k) :
    GnomonicSingleWind (openedWBS A B k) := by
  have _hside_keep : SameSides A B := hside
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have hwrap :
      ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0) :=
    openedWrapShortArc_at_supWBS hA hB hka hkt hkdef
  have hPweak : WeakConvexSphArm (openedWBS A B k) := by
    unfold openedWBS
    exact supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrap
  have hPpos : PositiveJoints (openedWBS A B k) := by
    intro r
    unfold openedWBS
    exact (openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef r).1
  have hPlt : ∀ i : Fin (n - 1), jointAngle (openedWBS A B k) i < Real.pi :=
    openedWBS_jointAngle_lt_pi A B k hstuck hA hB hangle hkdef
  let hex : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ i : Fin (n + 1), (0 : ℝ) < ⟪h, (openedWBS A B k i : E3)⟫ :=
    hPweak.closed_convex.open_hemisphere
  let h : E3 := Classical.choose hex
  have hspec := Classical.choose_spec hex
  have hnorm : ‖h‖ = 1 := hspec.1
  have hhem : ∀ i : Fin (n + 1), (0 : ℝ) < ⟪h, (openedWBS A B k i : E3)⟫ := hspec.2
  let frame := exists_orthoFrame hnorm
  let u : E3 := Classical.choose frame
  let frameTail := Classical.choose_spec frame
  let v : E3 := Classical.choose frameTail
  have hframe := Classical.choose_spec frameTail
  have hhu : (⟪h, u⟫ : ℝ) = 0 := hframe.1
  have hhv : (⟪h, v⟫ : ℝ) = 0 := hframe.2.1
  have huu : (⟪u, u⟫ : ℝ) = 1 := hframe.2.2.1
  have hvv : (⟪v, v⟫ : ℝ) = 1 := hframe.2.2.2.1
  have huv : (⟪u, v⟫ : ℝ) = 0 := hframe.2.2.2.2
  set Q : Fin (n + 1) → E3 := fun i => gproj h (openedWBS A B k i) with hQ
  have hplane : ∀ i : Fin (n + 1), (⟪h, Q i⟫ : ℝ) = 1 := by
    intro i
    rw [hQ]
    exact inner_gproj (ne_of_gt (hhem i))
  have hsupport : ∀ i j : Fin (n + 1), 0 ≤ det3 (Q i) (Q (i + 1)) (Q j) := by
    intro i j
    rw [hQ]
    exact gnomonic_edge_support_nonneg hPweak.closed_convex hhem i j
  have hedge : ∀ i : Fin (n + 1), Q i ≠ Q (i + 1) := by
    intro i
    rw [hQ]
    exact gproj_ne_of_short (hhem i) (hhem (i + 1)) (hPweak.closed_convex.edge_short i)
  have hturn : ∀ r : ℕ, ∀ hr2 : r + 2 < n + 1,
      0 < det3 (Q ⟨r, by omega⟩) (Q ⟨r + 1, by omega⟩) (Q ⟨r + 2, hr2⟩) := by
    intro r hr2
    rw [hQ]
    exact gnomonic_consecutive_turn_pos hPweak hPpos hPlt hhem hr2
  let lifted : PlanarLiftedTurnSpan Q h u v :=
    Classical.choice (hres Q h u v hhu hhv huu hvv huv hplane hsupport hedge hturn)
  exact
    { h := h
      hnorm := hnorm
      hpos := hhem
      u := u
      v := v
      lifted := by
        simpa [Q] using lifted }

#print axioms openedWBS_gnomonicSingleWind

/-- The theorem-shaped wrapper for the opened WBS certificate. -/
theorem openedWBS_gnomonicSingleWind_nonempty
    (hres : OpenedWBSPlanarLiftedTurnSpanExists)
    {n : ℕ} (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k)
    (hstuck : SupportStuckWBS A B k) :
    Nonempty (GnomonicSingleWind (openedWBS A B k)) :=
  ⟨openedWBS_gnomonicSingleWind hres A B hA hB hside hangle k hkdef hstuck⟩

#print axioms openedWBS_gnomonicSingleWind_nonempty

/-- The planar one-wind no-repeat theorem, kept as the separate planar target
owned by the downstream layer. -/
def PlanarOneWindNoRepeat : Prop :=
  ∀ {N : ℕ} [NeZero N] {Q : Fin N → E3} {h u v : E3},
    PlanarLiftedTurnSpan Q h u v → PlanarNoNonadjacentRepeat Q

/-- A gnomonic single-wind certificate gives spherical no-repeat once the
planar one-wind no-repeat theorem is supplied. -/
theorem noNonadjacentRepeat_of_gnomonicSingleWind
    (hplanar : PlanarOneWindNoRepeat)
    {n : ℕ} {P : Fin (n + 1) → S2}
    (cert : GnomonicSingleWind P) :
    NoNonadjacentRepeat P := by
  intro r s hr hs hrs heq
  have hQnr : PlanarNoNonadjacentRepeat
      (fun i : Fin (n + 1) => gproj cert.h (P i)) :=
    hplanar cert.lifted
  exact hQnr r s hr hs hrs (by simp [heq])

#print axioms noNonadjacentRepeat_of_gnomonicSingleWind

/-- The cross-piece no-collision residue follows from the opened WBS
single-wind certificate plus the separate planar one-wind no-repeat theorem. -/
theorem crossPieceNoCollisionAtSup_of_openedWBS_gnomonicSingleWind
    (hres : OpenedWBSPlanarLiftedTurnSpanExists)
    (hplanar : PlanarOneWindNoRepeat) :
    CrossPieceNoCollisionAtSup := by
  intro n A B hA hB hside hangle k hkdef hstuck r s hr hs hrs _hrK _hKs hcoll
  have cert : GnomonicSingleWind (openedWBS A B k) :=
    openedWBS_gnomonicSingleWind hres A B hA hB hside hangle k hkdef hstuck
  have hnr : NoNonadjacentRepeat (openedWBS A B k) :=
    noNonadjacentRepeat_of_gnomonicSingleWind hplanar cert
  exact hnr r s hr hs hrs hcoll

#print axioms crossPieceNoCollisionAtSup_of_openedWBS_gnomonicSingleWind

end ProofsInTheBook.ZinanFFCT97
