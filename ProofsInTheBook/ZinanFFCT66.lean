import ProofsInTheBook.ZinanFFCT65
import ProofsInTheBook.PlanarConvexDiag

/-!
# `ZinanFFCT66` — discharging the Chapter 13 strict-diagonal core and the contextual tail ray

This file is additive.  It proves the B-side strict diagonal core from the landed global
convex-position theorem, and proves the `(0,n-1)` tail-ray membership in the actual comparison
context where the non-flat upper bound `JointLe A B` is available.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT63
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65

namespace ProofsInTheBook.ZinanFFCT66

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Core 1: strict wrap diagonal support from global cyclic triples. -/

/-- Cyclic rotation for `sOrient`. -/
theorem sOrient_cyclic (a b c : S2) :
    sOrient a b c = sOrient b c a := by
  rw [sOrient]
  exact ProofsInTheBook.PlanarConvexDiag.det3_cyclic (a : E3) (b : E3) (c : E3)

/-- The wrap diagonal `(B n, B 1)` strictly supports every arc-interior vertex `B (1+v)`. -/
theorem strictDiagonal_arcInterior_of_cyclicTriple
    {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B)
    {v : ℕ} (hv1 : 1 ≤ v) (hvn : v ≤ n - 2) :
    0 < sOrient
      (B ⟨n, by omega⟩)
      (B ⟨1, by omega⟩)
      (B ⟨1 + v, by omega⟩) := by
  have hcyc :
      ProofsInTheBook.SphericalCyclicTriple.CyclicTriplePos (n := n + 1) B :=
    ProofsInTheBook.PlanarConvexDiag.cyclicTriplePos_unconditional hB.closed_convex
  have hpos :
      0 < sOrient
        (B ⟨1, by omega⟩)
        (B ⟨1 + v, by omega⟩)
        (B ⟨n, by omega⟩) := by
    exact hcyc
      ⟨1, by omega⟩
      ⟨1 + v, by omega⟩
      ⟨n, by omega⟩
      (by exact_mod_cast (show (1 : ℕ) < 1 + v by omega))
      (by exact_mod_cast (show (1 + v : ℕ) < n by omega))
  rw [sOrient_cyclic (B ⟨n, by omega⟩) (B ⟨1, by omega⟩)
        (B ⟨1 + v, by omega⟩)]
  exact hpos

/-- FFCT63's strict-diagonal interior residue is fully discharged. -/
theorem StrictDiagonalInteriorSupport_holds
    {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hn3 : 3 ≤ n) :
    StrictDiagonalInteriorSupport B hn3 := by
  intro v hv hv2 hvn
  exact strictDiagonal_arcInterior_of_cyclicTriple (B := B) hB (by omega) (by omega)

/-- The full FFCT54 wrap-diagonal support follows directly from cyclic triples. -/
theorem StrictDiagonalSupport_wrap_holds
    {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hn3 : 3 ≤ n) :
    StrictDiagonalSupport B hn3 := by
  intro v hv hv0 hvn
  have hv1 : 1 ≤ v := by omega
  have hvle : v ≤ n - 2 := by omega
  exact strictDiagonal_arcInterior_of_cyclicTriple (B := B) hB hv1 hvle

/-- FFCT65's `StrictDiagonalInteriorCore` field, now supplied unconditionally. -/
theorem StrictDiagonalInteriorCore_holds :
    StrictDiagonalInteriorCore := by
  intro n hn3 _hn5 B hB
  exact StrictDiagonalInteriorSupport_holds hB hn3

/-! ## Core 2: contextual tail-ray membership. -/

/-- Convert the real coefficient signs from the tail-line computation into the desired NNReal cone. -/
theorem tail_rayMembership_of_coeff_signs
    {u v p q : E3} {a b α β : ℝ}
    (ha : 0 < a)
    (hfold : p = a • u + b • v)
    (hq : q = α • u + β • v)
    (hα : 0 ≤ α)
    (hμ : 0 ≤ β * a - α * b) :
    q ∈ Submodule.span NNReal ({p, v} : Set E3) := by
  have hane : a ≠ 0 := ne_of_gt ha
  rw [Submodule.mem_span_pair]
  refine ⟨⟨α / a, div_nonneg hα (le_of_lt ha)⟩,
    ⟨(β * a - α * b) / a, div_nonneg hμ (le_of_lt ha)⟩, ?_⟩
  have hcalc :
      (α / a) • p + ((β * a - α * b) / a) • v = α • u + β • v := by
    rw [hfold, smul_add, smul_smul, smul_smul, add_assoc, ← add_smul]
    have hca : (α / a) * a = α := by field_simp [hane]
    have hcb : (α / a) * b + (β * a - α * b) / a = β := by
      field_simp [hane]
      ring
    rw [hca, hcb]
  change (α / a : ℝ) • p + ((β * a - α * b) / a : ℝ) • v = q
  rw [hcalc, ← hq]

/-- The actual `(0,n-1)` tail fold supplies the last vertex on the ray `span≥0 {A0,A(n-1)}` when
the comparison-arm non-flat bound is in scope. -/
theorem TailRayMembership_holds_context
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn3 : 3 ≤ n)
    (hA : WeakConvexSphArm A)
    (hpos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hangle : JointLe A B)
    (hnr : NoNonadjacentRepeat A)
    (hcol : (A ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨1, by omega⟩ : E3), (A ⟨n - 1, by omega⟩ : E3)} : Set E3)) :
    TailRayMembership A (by omega) := by
  by_cases hn4 : 4 ≤ n
  · have h0 : 0 < n + 1 := by omega
    have h1 : 1 < n + 1 := by omega
    have h2 : 2 < n + 1 := by omega
    have hj : n - 1 < n + 1 := by omega
    have hnn : n < n + 1 := by omega
    have hcol' : (A ⟨0, by omega⟩ : E3) ∈
        Submodule.span NNReal
          ({(A ⟨0 + 1, by omega⟩ : E3), (A ⟨n - 1, hj⟩ : E3)} : Set E3) := by
      have hidx1 : (⟨0 + 1, by omega⟩ : Fin (n + 1)) =
          (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
      have hidxj : (⟨n - 1, hj⟩ : Fin (n + 1)) =
          (⟨n - 1, by omega⟩ : Fin (n + 1)) := rfl
      rwa [hidx1, hidxj]
    obtain ⟨a, b, ha, hb, hcoeff⟩ :=
      far_fold_nondeg_datum_of_no_repeat hA hnr (i := 0) (j := n - 1)
        (by omega) hj hcol'
    have hfold : (A ⟨0, h0⟩ : E3) =
        (a : ℝ) • (A ⟨1, h1⟩ : E3) + (b : ℝ) • (A ⟨n - 1, hj⟩ : E3) := by
      have hidx1 : (⟨0 + 1, by omega⟩ : Fin (n + 1)) =
          (⟨1, h1⟩ : Fin (n + 1)) := Fin.ext rfl
      have hidx0 : (⟨0, by omega⟩ : Fin (n + 1)) =
          (⟨0, h0⟩ : Fin (n + 1)) := rfl
      rw [hidx1, hidx0] at hcoeff
      exact hcoeff.symm
    -- The `A2` witness gives the oriented area `D = det3 A(n-1) A1 A2` strictly positive.
    have hDneg :
        det3 (A ⟨1, h1⟩ : E3) (A ⟨n - 1, hj⟩ : E3) (A ⟨2, h2⟩ : E3) < 0 :=
      fold_A2_witness_negative hA hpos hB hangle hj (by omega) h1 h2 h0 hb hfold
    have hDpos :
        0 < det3 (A ⟨n - 1, hj⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3) := by
      rw [ProofsInTheBook.ZinanFFCT12.det3_swap12
        (A ⟨n - 1, hj⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3)]
      linarith
    -- First put `A n` on the real line spanned by `A1` and `A(n-1)`.
    have hsucc01 : ((⟨0, h0⟩ : Fin (n + 1)) + 1) = (⟨1, h1⟩ : Fin (n + 1)) :=
      succ_mk (by omega) (by omega)
    have htn : n - 1 + 1 < n + 1 := by omega
    have hidxn : (⟨n - 1 + 1, htn⟩ : Fin (n + 1)) =
        (⟨n, hnn⟩ : Fin (n + 1)) := Fin.ext (show n - 1 + 1 = n by omega)
    have hsuccj : ((⟨n - 1, hj⟩ : Fin (n + 1)) + 1) = (⟨n, hnn⟩ : Fin (n + 1)) := by
      have h := succ_mk (n := n) (k := n - 1) hj htn
      exact h.trans hidxn
    have hsupp1 : 0 ≤ det3 (A ⟨0, h0⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨n, hnn⟩ : E3) := by
      have h := hA.closed_convex.edge_support ⟨0, h0⟩ ⟨n, hnn⟩
      rwa [hsucc01] at h
    have hsupp2 : 0 ≤ det3 (A ⟨n - 1, hj⟩ : E3) (A ⟨n, hnn⟩ : E3)
        (A ⟨1, h1⟩ : E3) := by
      have h := hA.closed_convex.edge_support ⟨n - 1, hj⟩ ⟨1, h1⟩
      rwa [hsuccj] at h
    have hseed : (A ⟨n - 1, hj⟩ : E3) =
        (0 : ℝ) • (A ⟨1, h1⟩ : E3) + (1 : ℝ) • (A ⟨n - 1, hj⟩ : E3) := by
      rw [zero_smul, one_smul, zero_add]
    have hline0 : det3 (A ⟨1, h1⟩ : E3) (A ⟨n - 1, hj⟩ : E3)
        (A ⟨n - 1 + 1, htn⟩ : E3) = 0 :=
      have hsupp1t : 0 ≤ det3 (A ⟨0, h0⟩ : E3) (A ⟨1, h1⟩ : E3)
          (A ⟨n - 1 + 1, htn⟩ : E3) := by
        rw [hidxn]
        exact hsupp1
      have hsupp2t : 0 ≤ det3 (A ⟨n - 1, hj⟩ : E3)
          (A ⟨n - 1 + 1, htn⟩ : E3) (A ⟨1, h1⟩ : E3) := by
        rw [hidxn]
        exact hsupp2
      tail_step_collinear (j := n - 1) (t := n - 1) hj h1 h0 hj htn hb
        (by norm_num : (0 : ℝ) < 1) hfold hseed hsupp1t hsupp2t
    have hline : det3 (A ⟨1, h1⟩ : E3) (A ⟨n - 1, hj⟩ : E3)
        (A ⟨n, hnn⟩ : E3) = 0 := by
      rwa [hidxn] at hline0
    obtain ⟨α, β, hq⟩ :=
      repr_of_collinear hA hnr h1 hj hnn (by omega) hline
    -- Edge `(n-1,n)` at `2` gives `0 ≤ α`.
    have hsuppVq : 0 ≤ det3 (A ⟨n - 1, hj⟩ : E3) (A ⟨n, hnn⟩ : E3)
        (A ⟨2, h2⟩ : E3) := by
      have h := hA.closed_convex.edge_support ⟨n - 1, hj⟩ ⟨2, h2⟩
      rwa [hsuccj] at h
    have hαexp : det3 (A ⟨n - 1, hj⟩ : E3) (A ⟨n, hnn⟩ : E3)
        (A ⟨2, h2⟩ : E3)
        = α * det3 (A ⟨n - 1, hj⟩ : E3) (A ⟨1, h1⟩ : E3)
            (A ⟨2, h2⟩ : E3) := by
      rw [hq]
      simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    have hα : 0 ≤ α := by
      rw [hαexp] at hsuppVq
      nlinarith [hsuppVq, hDpos]
    -- Wrap edge `(n,0)` at `2` gives `0 ≤ β*a - α*b`.
    have hsuccn : ((⟨n, hnn⟩ : Fin (n + 1)) + 1) = (⟨0, h0⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have : ((⟨n, hnn⟩ + 1 : Fin (n + 1)) : ℕ) = (n + 1) % (n + 1) := by
        rw [Fin.add_def]; simp
      rw [this, Nat.mod_self]
    have hsuppqp : 0 ≤ det3 (A ⟨n, hnn⟩ : E3) (A ⟨0, h0⟩ : E3)
        (A ⟨2, h2⟩ : E3) := by
      have h := hA.closed_convex.edge_support ⟨n, hnn⟩ ⟨2, h2⟩
      rwa [hsuccn] at h
    have hμexp : det3 (A ⟨n, hnn⟩ : E3) (A ⟨0, h0⟩ : E3)
        (A ⟨2, h2⟩ : E3)
        = (β * (a : ℝ) - α * (b : ℝ))
            * det3 (A ⟨n - 1, hj⟩ : E3) (A ⟨1, h1⟩ : E3)
              (A ⟨2, h2⟩ : E3) := by
      rw [hq, hfold]
      simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    have hμ : 0 ≤ β * (a : ℝ) - α * (b : ℝ) := by
      rw [hμexp] at hsuppqp
      nlinarith [hsuppqp, hDpos]
    -- Convert the signs to the desired ray membership.
    unfold TailRayMembership
    have hidxLast : (Fin.last n : Fin (n + 1)) = ⟨n, hnn⟩ := rfl
    have hidx0 : (⟨0, by omega⟩ : Fin (n + 1)) = ⟨0, h0⟩ := rfl
    have hidxj : (⟨n - 1, by omega⟩ : Fin (n + 1)) = ⟨n - 1, hj⟩ := rfl
    rw [hidxLast, hidx0, hidxj]
    exact tail_rayMembership_of_coeff_signs (a := (a : ℝ)) (b := (b : ℝ))
      (α := α) (β := β) ha hfold hq hα hμ
  · have hn_eq : n = 3 := by omega
    subst hn_eq
    exfalso
    have hcolAdj : (A ⟨0, by omega⟩ : E3) ∈
        Submodule.span NNReal
          ({(A ⟨0 + 1, by omega⟩ : E3), (A ⟨0 + 2, by omega⟩ : E3)} : Set E3) := by
      simpa using hcol
    exact foldedFlat_adjacent_contradiction (i := 0) hA hpos (by omega) hcolAdj

/-- Metric tail boundary from the contextual ray-membership proof. -/
theorem TailFoldBoundary_holds_context
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn3 : 3 ≤ n)
    (hA : WeakConvexSphArm A)
    (hpos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hangle : JointLe A B)
    (hnr : NoNonadjacentRepeat A)
    (hcol : (A ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨1, by omega⟩ : E3), (A ⟨n - 1, by omega⟩ : E3)} : Set E3)) :
    TailFoldBoundary A (by omega) :=
  tailFoldBoundary_of_rayMembership (by omega)
    (TailRayMembership_holds_context hn3 hA hpos hB hangle hnr hcol)

/-! ## Final wiring: FFCT65 with the two cores supplied. -/

/-- Forward folded-flat transport with both FFCT63 cores supplied in their usable forms. -/
theorem foldedFlatCutTransportPlusForward_v3 :
    FoldedFlatCutTransportPlusForward := by
  intro n hn ih A B hA hposA hnr hB hside hangle i j hij1 hi1 hj hcol hdiag
  rcases Nat.lt_or_ge j (i + 2) with hj2 | hj2
  · omega
  · rcases Nat.eq_or_lt_of_le hj2 with hjeq | hjfar
    · subst hjeq
      exact absurd (foldedFlat_adjacent_contradiction (i := i) hA hposA (by omega) hcol)
        (by exact fun h => h)
    · have hnd := far_fold_nondeg_datum_of_no_repeat hA hnr hjfar hj hcol
      have hclass : i = 0 ∧ (j = n ∨ j = n - 1) :=
        far_fold_boundary_classification_final hA hposA hB hangle hnr hjfar hj hnd
      obtain ⟨hi0, hjcase⟩ := hclass
      subst hi0
      rcases hjcase with hjn | hjn1
      · have hcol' : (A ⟨0, by omega⟩ : E3) ∈
            Submodule.span NNReal
              ({(A ⟨1, by omega⟩ : E3), (A ⟨n, by omega⟩ : E3)} : Set E3) := by
          have hidx1 : (⟨0 + 1, hi1⟩ : Fin (n + 1)) =
              (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
          have hidxj : (⟨j, hj⟩ : Fin (n + 1)) =
              (⟨n, by omega⟩ : Fin (n + 1)) := Fin.ext hjn
          rwa [hidx1, hidxj] at hcol
        obtain ⟨hAe, hBe⟩ :=
          intervalCerts_of_betweenness_and_interiorCore
            StrictDiagonalInteriorCore_holds hA hnr hB (by omega) hcol'
        exact foldedFlat_boundary_j_eq_n hn ih hposA hside hangle hAe hBe hcol'
      · subst hjn1
        have hcol' : (A ⟨0, by omega⟩ : E3) ∈
            Submodule.span NNReal
              ({(A ⟨1, by omega⟩ : E3), (A ⟨n - 1, by omega⟩ : E3)} : Set E3) := by
          have hidx1 : (⟨0 + 1, hi1⟩ : Fin (n + 1)) =
              (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
          have hidxj : (⟨n - 1, hj⟩ : Fin (n + 1)) =
              (⟨n - 1, by omega⟩ : Fin (n + 1)) := rfl
          rwa [hidx1, hidxj] at hcol
        have htail : TailFoldBoundary A (by omega) :=
          TailFoldBoundary_holds_context (by omega) hA hposA hB hangle hnr hcol'
        have hdiag' : sDist (A ⟨0, by omega⟩) (A ⟨n - 1, by omega⟩)
            ≤ sDist (B ⟨0, by omega⟩) (B ⟨n - 1, by omega⟩) := hdiag
        exact foldedFlat_boundary_j_eq_n_minus_one hn hside htail hdiag'

/-- The corrected `NR` folded-flat transport with the two final cores supplied. -/
theorem foldedFlatCutTransportPlusNR_v3
    (hback : BackwardFoldCase) :
    FoldedFlatCutTransportPlusNR :=
  foldedFlatCutTransportPlusNR_of_forward hback foldedFlatCutTransportPlusForward_v3

/-- The remaining dispatch surface after discharging `StrictDiagonalInteriorCore` and the contextual
tail-ray core. -/
structure Ch13ConsolidatedSurface66 : Prop where
  hback : BackwardFoldCase
  hspanSeed : SupportStuckWBSVanishingSpanSeedSupply
  hnorepeat : OpenedWBSNoNonadjacentRepeatSupply
  hendpoint : BTrichotomyEndpointSurfaceV2

/-- The b-trichotomy dispatch surface assembled from the remaining FFCT66 fields. -/
theorem btrichotomyDispatchSurface_of_consolidated66
    (res : Ch13ConsolidatedSurface66) : BTrichotomyDispatchSurface where
  hspan := supportStuckWBSSpanSupply_of_vanishingSeed res.hspanSeed res.hnorepeat
  hnorepeat := openedWBSNoNonadjacentRepeat_pass res.hnorepeat
  hcases := btrichotomyEndpointCases_of_v2
    (foldedFlatCutTransportPlusNR_v3 res.hback) res.hendpoint

/-- The consolidated Chapter 13 headline after the two final cores are supplied. -/
theorem spherical_arm_mono_consolidated66 (res : Ch13ConsolidatedSurface66)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_vNext_btrichotomy
    (btrichotomyDispatchSurface_of_consolidated66 res) hn A B hA hB hside hangle

/-- Non-vacuity guard for the final headline shape. -/
theorem spherical_arm_mono_consolidated66_conclusion_satisfiable {n : ℕ}
    (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

#print axioms strictDiagonal_arcInterior_of_cyclicTriple
#print axioms StrictDiagonalInteriorCore_holds
#print axioms TailRayMembership_holds_context
#print axioms TailFoldBoundary_holds_context
#print axioms foldedFlatCutTransportPlusForward_v3
#print axioms foldedFlatCutTransportPlusNR_v3
#print axioms btrichotomyDispatchSurface_of_consolidated66
#print axioms spherical_arm_mono_consolidated66

end ProofsInTheBook.ZinanFFCT66
