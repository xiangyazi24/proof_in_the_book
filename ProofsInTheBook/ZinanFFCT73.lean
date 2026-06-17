import ProofsInTheBook.ZinanFFCT72

/-!
# `ZinanFFCT73` -- merging the v5/v6 routes at the strict WBS step

This file removes the arbitrary weak-entry `WeakPositiveCutReady` dependency from the
WBS support-stuck branch.  The resulting local step is strict-entry only: the opened
weak WBS arm is consumed directly by the folded-flat forward transport, and the
`b > 0, a > 0` branch derives its diagonal inequality at the live induction level.

The full `SZOpeningStepPlus` weak-entry branch is intentionally not rebuilt here: an
arbitrary weak positive input with a vanishing support still needs the unresolved
`WeakPositiveCutReady` bridge.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT72

namespace ProofsInTheBook.ZinanFFCT73

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Refutation-check guard for `WeakPositiveCutReady`. -/

/-- At level `2`, `CutReadyPlus` is impossible: its only normalized cut has a
one-edge ear, while the `WeakConvexSphArm` certificate inside `CutReadyPlus`
requires an ear of size at least `2`.  This does not by itself refute
`WeakPositiveCutReady`, because a matching level-`2` weak-positive premise with
a strict comparison arm is still needed; it records the concrete obstruction
found by the refutation pass. -/
theorem cutReadyPlus_level_two_false {A B : Fin (2 + 1) → S2} :
    ¬ CutReadyPlus A B := by
  intro hcr
  obtain ⟨i, j, hsk, hAe, _hBe⟩ := hcr
  have hm : 2 ≤ j - (i + 1) := hAe.two_le
  have hij := hsk.hij1
  have hj := hsk.hj
  omega

/-! ## Diagonal production for the positive-positive branch. -/

/-- Row expansion at the parent edge `(Ai, Aip1)`: if
`Ai = a • Aip1 + b • Aj`, then the support of the diagonal `(Aj, Aip1)`
multiplied by `b` is the parent edge support. -/
theorem det3_rowExpand_edge {a b : ℝ} {Ai Aip1 Aj V : E3}
    (hspan : Ai = a • Aip1 + b • Aj) :
    b * det3 Aj Aip1 V = det3 Ai Aip1 V := by
  rw [hspan, det3_add_fst, det3_smul_fst, det3_smul_fst]
  have hself : det3 Aip1 Aip1 V = 0 := by
    simp only [det3]
    ring
  rw [hself]
  ring

/-- A positive real span relation gives the NNReal betweenness consumed by the
folded-flat forward transport. -/
theorem span_mem_of_positive_coeffs {n : ℕ} {P : Fin (n + 1) → S2}
    {i j : ℕ} (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hbpos : 0 < b) (hapos : 0 < a) :
    (P ⟨i, hi⟩ : E3) ∈
      Submodule.span NNReal
        ({(P ⟨i + 1, hi1⟩ : E3), (P ⟨j, hj⟩ : E3)} : Set E3) := by
  rw [Submodule.mem_span_pair]
  refine ⟨⟨a, le_of_lt hapos⟩, ⟨b, le_of_lt hbpos⟩, ?_⟩
  rw [NNReal.smul_def, NNReal.smul_def]
  exact hspan.symm

/-- The A-side interval wrap data for `P[i+1..j]`, derived from the positive
span relation and the parent weak convexity. -/
theorem intervalWrapData_of_positive_span {n : ℕ} {P : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hnr : NoNonadjacentRepeat P)
    {i j : ℕ} (hij : i + 1 < j) (hfar : i + 2 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hbpos : 0 < b) :
    IntervalWrapData P (i + 1) (j - (i + 1)) (by omega) := by
  have hidxj :
      (⟨(i + 1) + (j - (i + 1)), by omega⟩ : Fin (n + 1)) = ⟨j, hj⟩ :=
    Fin.ext (by simp; omega)
  refine
    { wrap_short := ?_
      wrap_support := ?_ }
  · rw [hidxj]
    have hdist0 : P ⟨i + 1, by omega⟩ ≠ P ⟨j, by omega⟩ :=
      distinctNormalized_of_noRepeat hP hnr hij (by omega)
    obtain ⟨h, _hnorm, hhem⟩ := hP.closed_convex.open_hemisphere
    refine ⟨?_, ?_⟩
    · intro heq
      exact hdist0 (by simpa using heq.symm)
    · exact hemisphere_nonAntipodal hhem ⟨j, hj⟩ ⟨i + 1, hi1⟩
  · intro v hv
    rw [hidxj]
    have hsucc : ((⟨i, hi⟩ : Fin (n + 1)) + 1) = (⟨i + 1, hi1⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show i + 1 < n + 1 by omega)]
    have hpar :
        0 ≤ sOrient (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩)
          (P ⟨i + 1 + v, by have := hv; omega⟩) := by
      have hs := hP.closed_convex.edge_support ⟨i, hi⟩
        ⟨i + 1 + v, by have := hv; omega⟩
      rwa [hsucc] at hs
    have hrow := det3_rowExpand_edge (a := a) (b := b)
      (Ai := (P ⟨i, hi⟩ : E3)) (Aip1 := (P ⟨i + 1, hi1⟩ : E3))
      (Aj := (P ⟨j, hj⟩ : E3))
      (V := (P ⟨i + 1 + v, by have := hv; omega⟩ : E3)) hspan
    have hge :
        0 ≤ b * det3 (P ⟨j, hj⟩ : E3) (P ⟨i + 1, hi1⟩ : E3)
          (P ⟨i + 1 + v, by have := hv; omega⟩ : E3) := by
      rw [hrow]
      exact hpar
    have hdiag :
        0 ≤ det3 (P ⟨j, hj⟩ : E3) (P ⟨i + 1, hi1⟩ : E3)
          (P ⟨i + 1 + v, by have := hv; omega⟩ : E3) :=
      (mul_nonneg_iff_of_pos_left hbpos).mp hge
    simpa [sOrient]
      using hdiag

/-- Strict interval wrap data for `B[i+1..j]`, from the unconditional cyclic
triple theorem for strict spherical polygons. -/
theorem intervalWrapDataStrict_of_cyclicTriple {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B)
    {i j : ℕ} (_hij : i + 1 < j) (hfar : i + 2 < j) (hj : j < n + 1) :
    IntervalWrapDataStrict B (i + 1) (j - (i + 1)) (by omega) := by
  have hcyc :
      ProofsInTheBook.SphericalCyclicTriple.CyclicTriplePos (n := n + 1) B :=
    ProofsInTheBook.PlanarConvexDiag.cyclicTriplePos_unconditional hB.closed_convex
  have hidxj :
      (⟨(i + 1) + (j - (i + 1)), by omega⟩ : Fin (n + 1)) = ⟨j, hj⟩ :=
    Fin.ext (by simp; omega)
  refine
    { toWeak :=
        { wrap_short := ?_
          wrap_support := ?_ }
      wrap_strict := ?_ }
  · rw [hidxj]
    have hpos :
        0 < sOrient (B ⟨i + 1, by omega⟩) (B ⟨i + 2, by omega⟩) (B ⟨j, hj⟩) :=
      hcyc ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩ ⟨j, hj⟩
        (by exact_mod_cast (show i + 1 < i + 2 by omega))
        (by exact_mod_cast (show i + 2 < j by omega))
    obtain ⟨h, _hnorm, hhem⟩ := hB.closed_convex.open_hemisphere
    refine ⟨?_, ?_⟩
    · intro heq
      rw [heq] at hpos
      have hz :
          sOrient (B ⟨i + 1, by omega⟩) (B ⟨i + 2, by omega⟩)
            (B ⟨i + 1, by omega⟩) = 0 := by
        simp only [sOrient, det3]
        ring
      rw [hz] at hpos
      exact lt_irrefl 0 hpos
    · exact hemisphere_nonAntipodal hhem ⟨j, hj⟩ ⟨i + 1, by omega⟩
  · intro v hv
    rw [hidxj]
    by_cases hv0 : v = 0
    · subst hv0
      have hidx0 :
          (⟨i + 1 + 0, by omega⟩ : Fin (n + 1)) =
            (⟨i + 1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
      rw [hidx0, sOrient]
      have hz :
          det3 (B ⟨j, hj⟩ : E3) (B ⟨i + 1, by omega⟩ : E3)
            (B ⟨i + 1, by omega⟩ : E3) = 0 := by
        simp only [det3]
        ring
      rw [hz]
    · by_cases hvm : v = j - (i + 1)
      · subst hvm
        have hidxv :
            (⟨i + 1 + (j - (i + 1)), by omega⟩ : Fin (n + 1)) = ⟨j, hj⟩ :=
          Fin.ext (by omega)
        rw [hidxv, sOrient]
        have hz :
            det3 (B ⟨j, hj⟩ : E3) (B ⟨i + 1, by omega⟩ : E3)
              (B ⟨j, hj⟩ : E3) = 0 := by
          simp only [det3]
          ring
        rw [hz]
      · have hmid_lt : i + 1 < i + 1 + v := by omega
        have hmid_j : i + 1 + v < j := by omega
        have hpos :
            0 < sOrient (B ⟨i + 1, by omega⟩)
              (B ⟨i + 1 + v, by have := hv; omega⟩) (B ⟨j, hj⟩) :=
          hcyc ⟨i + 1, by omega⟩ ⟨i + 1 + v, by have := hv; omega⟩ ⟨j, hj⟩
            (by exact_mod_cast hmid_lt) (by exact_mod_cast hmid_j)
        rw [sOrient_cyclic (B ⟨j, hj⟩) (B ⟨i + 1, by omega⟩)
          (B ⟨i + 1 + v, by have := hv; omega⟩)]
        exact le_of_lt hpos
  · intro v hv hvm hv0
    rw [hidxj]
    have hmid_lt : i + 1 < i + 1 + v := by omega
    have hmid_j : i + 1 + v < j := by omega
    have hpos :
        0 < sOrient (B ⟨i + 1, by omega⟩)
          (B ⟨i + 1 + v, by have := hv; omega⟩) (B ⟨j, hj⟩) :=
      hcyc ⟨i + 1, by omega⟩ ⟨i + 1 + v, by have := hv; omega⟩ ⟨j, hj⟩
        (by exact_mod_cast hmid_lt) (by exact_mod_cast hmid_j)
    rw [sOrient_cyclic (B ⟨j, hj⟩) (B ⟨i + 1, by omega⟩)
      (B ⟨i + 1 + v, by have := hv; omega⟩)]
    exact hpos

/-- The diagonal inequality for the non-adjacent positive-positive branch. -/
theorem diag_le_of_positive_span_at_level
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B) (hnr : NoNonadjacentRepeat P)
    (ihdim : ∀ m : ℕ, m < n → MainPlus m)
    {i j : ℕ} (hij : i + 1 < j) (hfar : i + 2 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hbpos : 0 < b) (hapos : 0 < a) :
    sDist (P ⟨i, hi⟩) (P ⟨j, hj⟩) ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩) := by
  have hcol := span_mem_of_positive_coeffs hi hi1 hj hspan hbpos hapos
  have hm : 2 ≤ j - (i + 1) := by omega
  have hbnd : (i + 1) + (j - (i + 1)) ≤ n := by omega
  have hAe : WeakConvexSphArm (intervalArm P (i + 1) (j - (i + 1)) hbnd) :=
    weakConvex_intervalArm_of_wrap hP hm hbnd
      (intervalWrapData_of_positive_span hP hnr hij hfar hi hi1 hj hspan hbpos)
  have hBe : StrictConvexSphArm (intervalArm B (i + 1) (j - (i + 1)) hbnd) :=
    strictConvex_intervalArm_of_wrap hB hm hbnd
      (intervalWrapDataStrict_of_cyclicTriple hB hij hfar hj)
  have hMm : MainPlus (j - (i + 1)) := ihdim (j - (i + 1)) (by omega)
  have hear0 := ear_chord_le_of_MainPlus (A := P) (B := B)
    (a := i + 1) (m := j - (i + 1)) hbnd hMm hpos hAe hBe hside hangle
  have hear : sDist (P ⟨i + 1, hi1⟩) (P ⟨j, hj⟩)
      ≤ sDist (B ⟨i + 1, by omega⟩) (B ⟨j, hj⟩) := by
    have hidx1 : (⟨i + 1, by omega⟩ : Fin (n + 1)) = ⟨i + 1, hi1⟩ := rfl
    have hidxj :
        (⟨i + 1 + (j - (i + 1)), by omega⟩ : Fin (n + 1)) = ⟨j, hj⟩ :=
      Fin.ext (by simp; omega)
    rwa [hidx1, hidxj] at hear0
  have hfirst : sDist (B ⟨i + 1, by omega⟩) (B ⟨i, by omega⟩)
      = sDist (P ⟨i + 1, hi1⟩) (P ⟨i, hi⟩) := by
    simpa using (hside_of_sameSides (A' := P) (B := B) hside hij (by omega))
  have hdiag := diag_le_of_foldedFlat hcol hear hfirst
  simpa using hdiag

/-- The normalized positive-positive branch closes through the forward folded-flat
transport, with the adjacent case killed directly and the non-adjacent case using
the live dimension IH to derive the diagonal inequality. -/
theorem bpos_apos_endpoint_at_level_v7
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B) (hnr : NoNonadjacentRepeat P)
    (ihdim : ∀ m : ℕ, m < n → MainPlus m)
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hbpos : 0 < b) (hapos : 0 < a) :
    endpt P ≤ endpt B := by
  have hcol := span_mem_of_positive_coeffs hi hi1 hj hspan hbpos hapos
  by_cases hfar : i + 2 < j
  · have hdiag := diag_le_of_positive_span_at_level hP hpos hB hside hangle hnr ihdim
      hij hfar hi hi1 hj hspan hbpos hapos
    exact bpos_apos_endpointConsumer_forward_holds foldedFlatCutTransportPlusForward_v3
      hP hpos hB hside hangle hnr ihdim hij hi hi1 hj hspan hbpos hapos hdiag
  · have hjeq : j = i + 2 := by omega
    subst hjeq
    have hcol2 : (P ⟨i, hi⟩ : E3) ∈
        Submodule.span NNReal
          ({(P ⟨i + 1, hi1⟩ : E3), (P ⟨i + 2, hj⟩ : E3)} : Set E3) := by
      simpa using hcol
    exact False.elim (foldedFlat_adjacent_contradiction (i := i) hP hpos (by omega) hcol2)

/-! ## WBS support-stuck step with the exact v7 public surface. -/

structure Ch13FinalSurface73 : Prop where
  /-- Raw WBS wrap seed residue; non-wrap seeds are normalized by FFCT71. -/
  hwrapSeed : SupportStuckWBSWrapSeedResidue
  /-- Cross-piece no-collision, used to get opened-arm no-repeat. -/
  hcross : CrossPieceNoCollisionAtSup
  /-- The remaining `b > 0, a < 0` tail endpoint. -/
  hbpos_aneg_tail : BPosANegTailCornerResidue

/-- Coefficient dispatch at a fixed induction level, with no weak-entry cut-ready
bridge and no folded-flat transport Prop on the surface. -/
theorem endpoint_of_span_at_level_v7
    (htail : BPosANegTailCornerResidue)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B) (hnr : NoNonadjacentRepeat P)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlus m)
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3)) :
    endpt P ≤ endpt B := by
  rcases lt_trichotomy b 0 with hbneg | hb0 | hbpos
  · by_cases hi2 : i + 2 < n + 1
    · exact False.elim (midFold_bneg_false hP hpos hB hangle hi hi1 hi2 hj hhem hspan hbneg)
    · exact bneg_tail_closed_by_normalization hP hpos hB hside hangle hnr hhem
        hij hi hi1 hj hspan hbneg hi2
  · exact False.elim (span_bzero_false_of_weak hP hi hi1 hj hspan hb0)
  · rcases lt_trichotomy a 0 with haneg | ha0 | hapos
    · exact bpos_aneg_endpointConsumer_of_tail htail hP hpos hB hside hangle hnr hhem
        hij hi hi1 hj hspan hbpos haneg
    · have hij2 : i + 2 ≤ j := by omega
      exact False.elim (span_azero_bpos_false_of_noRepeat hnr hi hi1 hj hij2 hspan hbpos ha0)
    · exact bpos_apos_endpoint_at_level_v7 hP hpos hB hside hangle hnr ihdim
        hij hi hi1 hj hspan hbpos hapos

/-- A normalized vanishing support on a weak-positive opened WBS arm closes at a
fixed induction level. -/
theorem endpoint_of_normalized_vanishing_support_at_level_v7
    (htail : BPosANegTailCornerResidue)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B) (hnr : NoNonadjacentRepeat P)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlus m)
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hzero : sOrient (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨j, hj⟩) = 0) :
    endpt P ≤ endpt B := by
  obtain ⟨h, hnorm, hhemPos⟩ := hhem
  have hdist : P ⟨i + 1, hi1⟩ ≠ P ⟨j, hj⟩ := by
    have hdist0 : P ⟨i + 1, by omega⟩ ≠ P ⟨j, by omega⟩ :=
      distinctNormalized_of_noRepeat hP hnr hij (by omega)
    simpa using hdist0
  have hanti : (P ⟨i + 1, hi1⟩ : E3) ≠ -(P ⟨j, hj⟩ : E3) :=
    hemisphere_nonAntipodal hhemPos ⟨i + 1, hi1⟩ ⟨j, hj⟩
  have hdet : det3 (P ⟨i + 1, hi1⟩ : E3) (P ⟨j, hj⟩ : E3)
      (P ⟨i, hi⟩ : E3) = 0 := by
    rw [sOrient] at hzero
    rwa [ProofsInTheBook.ZinanFFCT12.det3_cyclic (P ⟨i, hi⟩ : E3) (P ⟨i + 1, hi1⟩ : E3)
      (P ⟨j, hj⟩ : E3)] at hzero
  obtain ⟨a, b, hspan⟩ :=
    lin_indep_span_of_det3_zero (P ⟨i + 1, hi1⟩).2 (P ⟨j, hj⟩).2
      (fun h => hdist (S2.ext h)) hanti hdet
  exact endpoint_of_span_at_level_v7 htail hP hpos hB hside hangle hnr
    ⟨h, hnorm, hhemPos⟩ ihdim hij hi hi1 hj hspan

/-- The v7 support-stuck endpoint dispatch at a live induction level. -/
theorem supportStuckWBS_endpoint_dispatch_at_level_v7
    (res : Ch13FinalSurface73)
    {n : ℕ} (ihdim : ∀ m : ℕ, m < n → MainPlus m)
    (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k)
    (hstuck : SupportStuckWBS A B k) :
    endpt (openedWBS A B k) ≤ endpt B := by
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have hwrapArc :
      ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0) :=
    openedWrapShortArc_at_supWBS hA hB hka hkt hkdef
  have hPweak : WeakConvexSphArm (openedWBS A B k) := by
    unfold openedWBS
    exact supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrapArc
  have hPpos : PositiveJoints (openedWBS A B k) := by
    intro r
    unfold openedWBS
    exact (openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef r).1
  have hedge := openedEdges_short_at_supWBS_of_wrap (A := A) (B := B) hA hwrapArc
  have hjopen := openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef
  have hhem0 := openHemisphere_at_WBS_sup hA hka hkt hkdef hedge hjopen
  have hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ) := by
    simpa [openedWBS] using hhem0
  have hside' : SameSides (openedWBS A B k) B := by
    intro r
    unfold openedWBS
    rw [openTail_preserves_sides A (openingAxis k) (-(monitoredSupWBS A B k)) r]
    exact hside r
  have hjointk : jointAngle (openedWBS A B k) k =
      openedInteriorJointAngle A k (-(monitoredSupWBS A B k)) := by
    unfold openedWBS
    exact jointAngle_openTail_eq_openedInterior A k (-(monitoredSupWBS A B k))
  have hslack : openedInteriorJointAngle A k (-(monitoredSupWBS A B k)) ≤ jointAngle B k :=
    openedInteriorJoint_le_at_supWBS hA hka hkt hkdef
  have hangle' : JointLe (openedWBS A B k) B := by
    intro r
    by_cases hrk : r = k
    · rw [hrk, hjointk]
      exact hslack
    · unfold openedWBS
      rw [jointAngle_openTail_eq_of_ne A k (-(monitoredSupWBS A B k)) hrk]
      exact hangle r
  have hnr : NoNonadjacentRepeat (openedWBS A B k) :=
    openedWBS_noNonadjacentRepeat_of_crossPiece res.hcross A B hA hB hside hangle k hkdef hstuck
  rcases (mirrorSeed_of_wrapSeedResidue res.hwrapSeed) A B hA hB hside hangle k hkdef hstuck with hdir | hmir
  · obtain ⟨i, j, hi, hi1, hj, hij, hzero⟩ := hdir
    exact endpoint_of_normalized_vanishing_support_at_level_v7 res.hbpos_aneg_tail
      hPweak hPpos hB hside' hangle' hnr hhem ihdim hij hi hi1 hj hzero
  · obtain ⟨i, j, hi, hi1, hj, hij, hzero⟩ := hmir
    have hmirror : endpt (mirrorArm (openedWBS A B k)) ≤ endpt (mirrorArm B) :=
      endpoint_of_normalized_vanishing_support_at_level_v7 res.hbpos_aneg_tail
        (weakConvex_mirrorArm hPweak) (positiveJoints_mirrorArm hPpos)
        (strictConvex_mirrorArm hB) (sameSides_mirrorArm hside') (jointLe_mirrorArm hangle')
        (noNonadjacentRepeat_mirrorArm hnr)
        (weakConvex_mirrorArm hPweak).closed_convex.open_hemisphere ihdim
        hij hi hi1 hj hzero
    simpa [endpt_mirrorArm] using hmirror

/-- The strict-entry WBS opening step with the v7 surface. -/
theorem open_step_wbs_v7 (res : Ch13FinalSurface73)
    {n : ℕ} (_hn : 2 ≤ n) (ihdim : ∀ m : ℕ, m < n → MainPlus m)
    {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (ihdef : ∀ A' B' : Fin (n + 1) → S2,
      WeakConvexSphArm A' → PositiveJoints A' →
      StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
      deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B')
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k) :
    endpt A ≤ endpt B := by
  set K : Fin (n + 1) := openingAxis k with hK
  set δ : ℝ := monitoredSupWBS A B k with hδ
  set A' : Fin (n + 1) → S2 := openTail A K (-δ) with hA'
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have hjointk : jointAngle A' k = openedInteriorJointAngle A k (-δ) := by
    rw [hA']; exact jointAngle_openTail_eq_openedInterior A k (-δ)
  have hslack : openedInteriorJointAngle A k (-δ) ≤ jointAngle B k :=
    openedInteriorJoint_le_at_supWBS hA hka hkt hkdef
  have hside' : SameSides A' B := by
    intro i; rw [hA', openTail_preserves_sides A K (-δ) i]; exact hside i
  have hangle' : JointLe A' B := by
    intro r
    by_cases hrk : r = k
    · rw [hrk, hjointk]; exact hslack
    · rw [hA', jointAngle_openTail_eq_of_ne A k (-δ) hrk]; exact hangle r
  have hmono : endpt A ≤ endpt A' := glueWBS_clause_i hA hka hkt hkdef
  by_cases hstuck : SupportStuckWBS A B k
  · have hAB0 : endpt (openedWBS A B k) ≤ endpt B :=
      supportStuckWBS_endpoint_dispatch_at_level_v7 res ihdim A B hA hB hside hangle k hkdef hstuck
    have hAB : endpt A' ≤ endpt B := by
      rw [hA']
      exact hAB0
    exact le_trans hmono hAB
  · have hreach : ReachWBS A B k := by
      rcases glueWBS_clause_ii hA hB hka hkt hkdef hstuck with hr | hbase
      · exact hr
      · rcases BaseStuckProgressWBS_holds n A B hA hB k hkdef hbase with hr | hvan
        · exact hr
        · exfalso
          obtain ⟨i, j, hji, hji1, heq⟩ := hvan
          exact hstuck ⟨⟨(i, j), ⟨hji, hji1⟩⟩, by rw [supportConstraint_apply]; exact heq⟩
    have hstrict : StrictConvexSphArm A' := by
      rw [hA']; exact reachWBS_strictConvex hA hB hka hkt hkdef hstuck
    have hreach_k : jointAngle A' k = jointAngle B k := by rw [hjointk]; exact hreach
    have hdrop : deficitCount A' B < deficitCount A B := by
      rw [hA']; exact deficitCount_openTail_reach_lt A B k (-δ) hkdef hreach_k
    have hAB : endpt A' ≤ endpt B :=
      ihdef A' B (strictConvexSphArm_toWeak hstrict)
        (strictConvexSphArm_positiveJoints hstrict) hB hside' hangle' hdrop
    exact le_trans hmono hAB

/-- Guard: the v7 local strict step's conclusion is a real endpoint inequality. -/
theorem open_step_wbs_v7_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

#print axioms cutReadyPlus_level_two_false
#print axioms det3_rowExpand_edge
#print axioms intervalWrapData_of_positive_span
#print axioms intervalWrapDataStrict_of_cyclicTriple
#print axioms diag_le_of_positive_span_at_level
#print axioms bpos_apos_endpoint_at_level_v7
#print axioms supportStuckWBS_endpoint_dispatch_at_level_v7
#print axioms open_step_wbs_v7

end ProofsInTheBook.ZinanFFCT73
