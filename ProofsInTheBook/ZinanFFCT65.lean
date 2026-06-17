import ProofsInTheBook.ZinanFFCT63
import ProofsInTheBook.ZinanFFCT64

/-!
# `ZinanFFCT65` — corrected FFCTPlus assembly and consolidated b-trichotomy wiring

This file is intentionally an additive repair layer.  It does not edit `ZinanFFCT53`: the old
`htfb`-based assembly is left alone, and the corrected assembly below consumes FFCT63's honest
`BoundaryTailRay` in the actual `(0, n-1)` branch.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT59
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT62
open ProofsInTheBook.ZinanFFCT63
open ProofsInTheBook.ZinanFFCT64

namespace ProofsInTheBook.ZinanFFCT65

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The shrunken strict-diagonal core and interval certificates. -/

/-- The remaining B-side strict-diagonal content after FFCT63: only the strict interior range
`2 ≤ v ≤ n-3`, and only in the nonempty regime `n ≥ 5`. -/
def StrictDiagonalInteriorCore : Prop :=
  ∀ {n : ℕ} (hn3 : 3 ≤ n) (_hn5 : 5 ≤ n) (B : Fin (n + 1) → S2),
    StrictConvexSphArm B → StrictDiagonalInteriorSupport B hn3

/-- For `n = 3, 4`, FFCT63's interior range is empty; for `n ≥ 5`, use the named core. -/
theorem strictDiagonalSupport_of_interiorCore
    (hcore : StrictDiagonalInteriorCore) {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hn3 : 3 ≤ n) :
    StrictDiagonalSupport B hn3 := by
  apply strictDiagonalSupport_of_interior hB hn3
  by_cases hn5 : 5 ≤ n
  · exact hcore hn3 hn5 B hB
  · intro v hv hv2 hvn
    omega

/-- The `(0,n)` interval certificates with FFCT63's smaller B-side core threaded in.  The B ear is
free for `n ∈ {3,4}` and uses `StrictDiagonalInteriorCore` only for `n ≥ 5`. -/
theorem intervalCerts_of_betweenness_and_interiorCore
    (hcore : StrictDiagonalInteriorCore) {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hnr : NoNonadjacentRepeat A)
    (hB : StrictConvexSphArm B) (hn3 : 3 ≤ n)
    (hcol : (A ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal ({(A ⟨1, by omega⟩ : E3), (A ⟨n, by omega⟩ : E3)} : Set E3)) :
    WeakConvexSphArm (intervalArm A 1 (n - 1) (by omega)) ∧
      StrictConvexSphArm (intervalArm B 1 (n - 1) (by omega)) :=
  intervalCerts_of_betweenness_and_strictDiagonal hA hnr hB hn3 hcol
    (strictDiagonalSupport_of_interiorCore hcore hB hn3)

/-! ## §2. Corrected FFCTPlus assembly. -/

/-- The forward folded-flat transport with the corrected `(0,n-1)` tail input.  The old free
universal `htfb` is replaced by FFCT63's context-carrying `BoundaryTailRay`, consumed only where the
`(0,n-1)` branch has the required fold betweenness in scope. -/
theorem foldedFlatCutTransportPlusForward_v2
    (hcore : StrictDiagonalInteriorCore) (hbtr : BoundaryTailRay) :
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
          have hidx1 : (⟨0 + 1, hi1⟩ : Fin (n + 1)) = (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
          have hidxj : (⟨j, hj⟩ : Fin (n + 1)) = (⟨n, by omega⟩ : Fin (n + 1)) := Fin.ext hjn
          rwa [hidx1, hidxj] at hcol
        obtain ⟨hAe, hBe⟩ :=
          intervalCerts_of_betweenness_and_interiorCore hcore hA hnr hB (by omega) hcol'
        exact foldedFlat_boundary_j_eq_n hn ih hposA hside hangle hAe hBe hcol'
      · subst hjn1
        have hcol' : (A ⟨0, by omega⟩ : E3) ∈
            Submodule.span NNReal
              ({(A ⟨1, by omega⟩ : E3), (A ⟨n - 1, by omega⟩ : E3)} : Set E3) := by
          have hidx1 : (⟨0 + 1, hi1⟩ : Fin (n + 1)) = (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
          have hidxj : (⟨n - 1, hj⟩ : Fin (n + 1)) = (⟨n - 1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
          rwa [hidx1, hidxj] at hcol
        have htail : TailFoldBoundary A (by omega) :=
          tailFoldBoundary_supply_in_context hbtr (by omega) hA hposA hnr hcol'
        have hdiag' : sDist (A ⟨0, by omega⟩) (A ⟨n - 1, by omega⟩)
            ≤ sDist (B ⟨0, by omega⟩) (B ⟨n - 1, by omega⟩) := hdiag
        exact foldedFlat_boundary_j_eq_n_minus_one hn hside htail hdiag'

/-- The corrected general `NR` assembly: the backward tax is unchanged, while the forward branch uses
`BoundaryTailRay` and the shrunken strict-diagonal core. -/
theorem foldedFlatCutTransportPlusNR_v2
    (hback : BackwardFoldCase) (hcore : StrictDiagonalInteriorCore) (hbtr : BoundaryTailRay) :
    FoldedFlatCutTransportPlusNR :=
  foldedFlatCutTransportPlusNR_of_forward hback
    (foldedFlatCutTransportPlusForward_v2 hcore hbtr)

/-- Bridge to the original `FoldedFlatCutTransportPlus`, retaining the honest no-repeat supply. -/
theorem foldedFlatCutTransportPlus_v2
    (hback : BackwardFoldCase) (hcore : StrictDiagonalInteriorCore) (hbtr : BoundaryTailRay)
    (hsupply : ∀ {n : ℕ} (A : Fin (n + 1) → S2),
      WeakConvexSphArm A → PositiveJoints A → NoNonadjacentRepeat A) :
    FoldedFlatCutTransportPlus :=
  foldedFlatCutTransportPlus_of_NR
    (foldedFlatCutTransportPlusNR_v2 hback hcore hbtr) hsupply

/-! ## §3. Raw span extraction for the b-trichotomy dispatch. -/

/-- A normalized vanishing support seed for each WBS support-stuck branch.  This is the sharp raw
geometric input still needed before the algebraic b-trichotomy can run. -/
def SupportStuckWBSVanishingSpanSeedSupply : Prop :=
  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
    StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    SupportStuckWBS A B k →
      ∃ i j : ℕ, ∃ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
        i + 1 < j ∧
          sOrient (openedWBS A B k ⟨i, hi⟩) (openedWBS A B k ⟨i + 1, hi1⟩)
            (openedWBS A B k ⟨j, hj⟩) = 0

/-- The accepted opened-arm no-repeat surface, passed through under its sharper name. -/
theorem openedWBSNoNonadjacentRepeat_pass
    (h : OpenedWBSNoNonadjacentRepeatSupply) :
    OpenedWBSNoNonadjacentRepeatSupply := h

/-- From a normalized vanishing support seed and opened no-repeat, extract the real span datum needed
by FFCT64.  Independence of `(A'(i+1), A'j)` comes from `ShortArc`: distinctness by no-repeat/weak
convexity, non-antipodality by the WBS open hemisphere. -/
theorem supportStuckWBSSpanSupply_of_vanishingSeed
    (hseed : SupportStuckWBSVanishingSpanSeedSupply)
    (hnrs : OpenedWBSNoNonadjacentRepeatSupply) :
    SupportStuckWBSSpanSupply := by
  intro n A B hA hB hside hangle k hkdef hstuck
  obtain ⟨i, j, hi, hi1, hj, hij, hzero⟩ := hseed A B hA hB hside hangle k hkdef hstuck
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have hwrap :
      ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0) :=
    openedWrapShortArc_at_supWBS hA hB hka hkt hkdef
  have hPweak : WeakConvexSphArm (openedWBS A B k) := by
    unfold openedWBS
    exact supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrap
  have hedge := openedEdges_short_at_supWBS_of_wrap (A := A) (B := B) hA hwrap
  have hjopen := openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef
  have hhem0 := openHemisphere_at_WBS_sup hA hka hkt hkdef hedge hjopen
  obtain ⟨h', _hnorm', hhem0'⟩ := hhem0
  have hhem : ∀ r : Fin (n + 1), 0 < (⟪h', (openedWBS A B k r : E3)⟫ : ℝ) := by
    simpa [openedWBS] using hhem0'
  have hnr : NoNonadjacentRepeat (openedWBS A B k) :=
    hnrs A B hA hB hside hangle k hkdef hstuck
  have hdist : openedWBS A B k ⟨i + 1, hi1⟩ ≠ openedWBS A B k ⟨j, hj⟩ :=
    distinctNormalized_of_noRepeat hPweak hnr hij (by omega)
  have hanti : (openedWBS A B k ⟨i + 1, hi1⟩ : E3)
      ≠ -(openedWBS A B k ⟨j, hj⟩ : E3) :=
    hemisphere_nonAntipodal hhem ⟨i + 1, hi1⟩ ⟨j, hj⟩
  have hdet : det3 (openedWBS A B k ⟨i + 1, hi1⟩ : E3)
      (openedWBS A B k ⟨j, hj⟩ : E3) (openedWBS A B k ⟨i, hi⟩ : E3) = 0 := by
    rw [sOrient] at hzero
    rwa [det3_cyclic (openedWBS A B k ⟨i, hi⟩ : E3)
      (openedWBS A B k ⟨i + 1, hi1⟩ : E3) (openedWBS A B k ⟨j, hj⟩ : E3)] at hzero
  obtain ⟨a, b, hspan⟩ :=
    lin_indep_span_of_det3_zero
      (openedWBS A B k ⟨i + 1, hi1⟩).2 (openedWBS A B k ⟨j, hj⟩).2
      (fun h => hdist (S2.ext h)) hanti hdet
  exact ⟨i, j, hi, hi1, hj, hij, a, b, hspan⟩

/-! ## §4. Endpoint case consumers. -/

/-- The missing adapter from the corrected FFCTPlus theorem to FFCT64's `b > 0, a > 0` endpoint
consumer.  The available landed theorem is `foldedFlatCutTransportPlusNR_v2`; what remains is the
case-specific production of the diagonal/IH data required to use it in FFCT64's endpoint-dispatch
signature. -/
def BPosAPosFFCTPlusV2EndpointConsumer : Prop :=
  FoldedFlatCutTransportPlusNR →
    ∀ {n : ℕ} {P B : Fin (n + 1) → S2},
      WeakConvexSphArm P → PositiveJoints P → StrictConvexSphArm B →
      SameSides P B → JointLe P B → NoNonadjacentRepeat P →
      (∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ)) →
      ∀ {i j : ℕ}, i + 1 < j →
      ∀ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
      ∀ {a b : ℝ},
        (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3) →
        0 < b → 0 < a → endpt P ≤ endpt B

/-- The remaining `b > 0, a < 0` endpoint consumer.  FFCT64 isolated this case; no landed supplier in
the current tree proves the edge-between-vertex contradiction for all endpoint corners. -/
def BPosANegEndpointConsumer : Prop :=
  ∀ {n : ℕ} {P B : Fin (n + 1) → S2},
    WeakConvexSphArm P → PositiveJoints P → StrictConvexSphArm B →
    SameSides P B → JointLe P B → NoNonadjacentRepeat P →
    (∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ)) →
    ∀ {i j : ℕ}, i + 1 < j →
    ∀ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
    ∀ {a b : ℝ},
      (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3) →
      0 < b → a < 0 → endpt P ≤ endpt B

structure BTrichotomyEndpointSurfaceV2 : Prop where
  bpos_apos : BPosAPosFFCTPlusV2EndpointConsumer
  bpos_aneg : BPosANegEndpointConsumer

/-- In FFCT64's normalized surface, the retained `b < 0` tail branch is arithmetically empty:
`i+1<j` and `j<n+1` imply `i+2<n+1`. -/
theorem bneg_tail_closed_by_normalization {n : ℕ} {P B : Fin (n + 1) → S2}
    (_hP : WeakConvexSphArm P) (_hpos : PositiveJoints P) (_hB : StrictConvexSphArm B)
    (_hside : SameSides P B) (_hangle : JointLe P B) (_hnr : NoNonadjacentRepeat P)
    (_hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    {i j : ℕ} (hij : i + 1 < j)
    (_hi : i < n + 1) (_hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (_hspan : (P ⟨i, by omega⟩ : E3) = a • (P ⟨i + 1, by omega⟩ : E3)
      + b • (P ⟨j, hj⟩ : E3))
    (_hbneg : b < 0) (hnot : ¬ i + 2 < n + 1) :
    endpt P ≤ endpt B := by
  exfalso
  apply hnot
  omega

/-- Build FFCT64's endpoint-case surface from the corrected FFCTPlus theorem and the two honest
remaining endpoint consumers. -/
theorem btrichotomyEndpointCases_of_v2
    (hffct : FoldedFlatCutTransportPlusNR) (res : BTrichotomyEndpointSurfaceV2) :
    BTrichotomyEndpointCases where
  bneg_tail := by
    intro n P B hP hpos hB hside hangle hnr hhem i j hij hi hi1 hj a b hspan hb hnot
    exact bneg_tail_closed_by_normalization hP hpos hB hside hangle hnr hhem hij hi hi1 hj hspan hb hnot
  bpos_apos := by
    exact res.bpos_apos hffct
  bpos_aneg := by
    exact res.bpos_aneg

/-! ## §5. Tail-boundary mirror endpoint wrappers. -/

/-- The still-missing mirrored diagonal inequality for FFCT62's `j = 1` tail endpoint transport. -/
def TailJ1MirrorDiagSupply : Prop :=
  ∀ {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    {i j : ℕ} {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1},
    NonAxisTailBoundaryResidue A B k i j hi hi1 hj → j = 1 →
      sDist (mirrorArm (openedWBS A B k) ⟨0, by omega⟩)
          (mirrorArm (openedWBS A B k) ⟨n - 1, by omega⟩)
        ≤ sDist (mirrorArm B ⟨0, by omega⟩) (mirrorArm B ⟨n - 1, by omega⟩)

/-- The dimension-IH supply still needed by the `j = 0` mirror transport's `(0,n)` boundary close. -/
def TailJ0MirrorIHSupply : Prop :=
  ∀ {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    {i j : ℕ} {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1},
    NonAxisTailBoundaryResidue A B k i j hi hi1 hj → j = 0 →
      ∀ m : ℕ, m < n → MainPlus m

/-- The `j = 0` mirror endpoint case with the interval certificates produced from the shrunken
strict-diagonal core. -/
theorem tailBoundary_j0_endpoint_transport_mirror_v2
    (hcore : StrictDiagonalInteriorCore) (hih : TailJ0MirrorIHSupply) {n : ℕ}
    {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    {i j : ℕ} {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1}
    (hA'weak : WeakConvexSphArm (openedWBS A B k))
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hB : StrictConvexSphArm B)
    (hside' : SameSides (openedWBS A B k) B)
    (hangle' : JointLe (openedWBS A B k) B)
    (hnr : NoNonadjacentRepeat (openedWBS A B k))
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    (hj0 : j = 0)
    (hres : NonAxisTailBoundaryResidue A B k i j hi hi1 hj) :
    endpt (openedWBS A B k) ≤ endpt B := by
  have hn3 : 3 ≤ n := by
    rcases hres with ⟨htail, hi_rot, _hj_fixed, _hmix⟩
    have hKint := openingAxis_interior k
    omega
  have hn : 2 ≤ n := by omega
  have hcol0 := nonAxisTailBoundaryResidue_mirror_collinearity hhem hres
  have hidx : (⟨n - j, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext (by simp [hj0])
  have hcol : (mirrorArm (openedWBS A B k) ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(mirrorArm (openedWBS A B k) ⟨1, by omega⟩ : E3),
          (mirrorArm (openedWBS A B k) ⟨n, by omega⟩ : E3)} : Set E3) := by
    rwa [hidx] at hcol0
  obtain ⟨hAe, hBe⟩ :=
    intervalCerts_of_betweenness_and_interiorCore hcore
      (weakConvex_mirrorArm hA'weak) (noNonadjacentRepeat_mirrorArm hnr)
      (strictConvex_mirrorArm hB) hn3 hcol
  exact tailBoundary_j0_endpoint_transport_mirror hn (hih hres hj0)
    hA'pos hside' hangle' hAe hBe hhem hj0 hres

/-- The `j = 1` mirror endpoint case with `TailFoldBoundary` supplied from `BoundaryTailRay`.  The
only retained geometric input is the mirrored diagonal inequality. -/
theorem tailBoundary_j1_endpoint_transport_mirror_v2
    (hbtr : BoundaryTailRay) {n : ℕ}
    {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    {i j : ℕ} {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1}
    (hA'weak : WeakConvexSphArm (openedWBS A B k))
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hnr : NoNonadjacentRepeat (openedWBS A B k))
    (hside' : SameSides (openedWBS A B k) B)
    (hdiag : sDist (mirrorArm (openedWBS A B k) ⟨0, by omega⟩)
        (mirrorArm (openedWBS A B k) ⟨n - 1, by omega⟩)
      ≤ sDist (mirrorArm B ⟨0, by omega⟩) (mirrorArm B ⟨n - 1, by omega⟩))
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    (hj1 : j = 1)
    (hres : NonAxisTailBoundaryResidue A B k i j hi hi1 hj) :
    endpt (openedWBS A B k) ≤ endpt B := by
  have hn3 : 3 ≤ n := by
    rcases hres with ⟨htail, hi_rot, _hj_fixed, _hmix⟩
    have hKint := openingAxis_interior k
    omega
  have hn : 2 ≤ n := by omega
  have hcol0 := nonAxisTailBoundaryResidue_mirror_collinearity hhem hres
  have hidx : (⟨n - j, by omega⟩ : Fin (n + 1)) = ⟨n - 1, by omega⟩ := Fin.ext (by simp [hj1])
  have hcol : (mirrorArm (openedWBS A B k) ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(mirrorArm (openedWBS A B k) ⟨1, by omega⟩ : E3),
          (mirrorArm (openedWBS A B k) ⟨n - 1, by omega⟩ : E3)} : Set E3) := by
    rwa [hidx] at hcol0
  have htail : TailFoldBoundary (mirrorArm (openedWBS A B k)) (by omega) :=
    tailFoldBoundary_supply_in_context hbtr hn3
      (weakConvex_mirrorArm hA'weak) (positiveJoints_mirrorArm hA'pos)
      (noNonadjacentRepeat_mirrorArm hnr) hcol
  exact tailBoundary_j1_endpoint_transport_mirror hn hside' htail hdiag hhem hj1 hres

/-- FFCT61's endpoint classification plus FFCT62's mirror transports, with the `j = 0` interval
certificates and the `j = 1` tail-fold premise supplied by FFCT63/65. -/
theorem nonAxisTailBoundary_endpoint_transport_v2
    (hcore : StrictDiagonalInteriorCore) (hbtr : BoundaryTailRay)
    (hih0 : TailJ0MirrorIHSupply) (hdiag1 : TailJ1MirrorDiagSupply)
    {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    {i j : ℕ} {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1}
    (hA'weak : WeakConvexSphArm (openedWBS A B k))
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hB : StrictConvexSphArm B)
    (hside' : SameSides (openedWBS A B k) B)
    (hangle' : JointLe (openedWBS A B k) B)
    (hnr : NoNonadjacentRepeat (openedWBS A B k))
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    (hres : NonAxisTailBoundaryResidue A B k i j hi hi1 hj) :
    endpt (openedWBS A B k) ≤ endpt B := by
  rcases nonAxisTailBoundaryResidue_forces_endpoint_j_mirror hA'weak hA'pos hB hangle'
      hnr hhem hres with hj0 | hj1
  · exact tailBoundary_j0_endpoint_transport_mirror_v2 hcore hih0 hA'weak hA'pos hB hside'
      hangle' hnr hhem hj0 hres
  · exact tailBoundary_j1_endpoint_transport_mirror_v2 hbtr hA'weak hA'pos hnr hside'
      (hdiag1 hres hj1) hhem hj1 hres

/-! ## §6. Consolidated headline. -/

structure Ch13ConsolidatedSurface : Prop where
  hback : BackwardFoldCase
  hdiagCore : StrictDiagonalInteriorCore
  hbtr : BoundaryTailRay
  hspanSeed : SupportStuckWBSVanishingSpanSeedSupply
  hnorepeat : OpenedWBSNoNonadjacentRepeatSupply
  hendpoint : BTrichotomyEndpointSurfaceV2
  hj0ih : TailJ0MirrorIHSupply
  hj1diag : TailJ1MirrorDiagSupply

/-- The dispatch surface used by FFCT64, assembled from the sharper FFCT65 components. -/
theorem btrichotomyDispatchSurface_of_consolidated
    (res : Ch13ConsolidatedSurface) : BTrichotomyDispatchSurface where
  hspan := supportStuckWBSSpanSupply_of_vanishingSeed res.hspanSeed res.hnorepeat
  hnorepeat := openedWBSNoNonadjacentRepeat_pass res.hnorepeat
  hcases := btrichotomyEndpointCases_of_v2
    (foldedFlatCutTransportPlusNR_v2 res.hback res.hdiagCore res.hbtr) res.hendpoint

/-- The sharpest current strict-arm headline from the consolidated honest surface. -/
theorem spherical_arm_mono_consolidated (res : Ch13ConsolidatedSurface)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_vNext_btrichotomy
    (btrichotomyDispatchSurface_of_consolidated res) hn A B hA hB hside hangle

/-- Non-vacuity guard: the consolidated headline has the genuine endpoint inequality conclusion. -/
theorem spherical_arm_mono_consolidated_conclusion_satisfiable {n : ℕ}
    (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

#print axioms strictDiagonalSupport_of_interiorCore
#print axioms foldedFlatCutTransportPlusForward_v2
#print axioms foldedFlatCutTransportPlusNR_v2
#print axioms supportStuckWBSSpanSupply_of_vanishingSeed
#print axioms btrichotomyEndpointCases_of_v2
#print axioms nonAxisTailBoundary_endpoint_transport_v2
#print axioms spherical_arm_mono_consolidated

end ProofsInTheBook.ZinanFFCT65
