import ProofsInTheBook.ZinanFFCT73

/-!
# `ZinanFFCT74` -- NR-threaded static weak entry

This additive layer threads `NoNonadjacentRepeat` through the weak-entry recursion.  The
old unqualified `WeakPositiveCutReady` is not recovered: the `a = 0, b > 0`
coefficient branch is exactly a nonadjacent repeat.  The honest replacement is the
`NR` motive below, together with a normalized/mirror seed for the raw weak
vanishing support.
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
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
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
open ProofsInTheBook.ZinanFFCT73

namespace ProofsInTheBook.ZinanFFCT74

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## NR-threaded recursion. -/

/-- `MainPlus` with `NoNonadjacentRepeat` threaded on the weak left arm. -/
def MainPlusNR (n : ℕ) : Prop :=
  ∀ A B : Fin (n + 1) → S2,
    WeakConvexSphArm A → PositiveJoints A → NoNonadjacentRepeat A →
    StrictConvexSphArm B → SameSides A B → JointLe A B →
    endpt A ≤ endpt B

/-- The opening step consumed by the `MainPlusNR` recursion. -/
def SZOpeningStepPlusNR : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ m : ℕ, m < n → MainPlusNR m) →
    (∀ A B : Fin (n + 1) → S2,
      WeakConvexSphArm A → PositiveJoints A → NoNonadjacentRepeat A →
      StrictConvexSphArm B → SameSides A B → JointLe A B →
      (∀ A' B' : Fin (n + 1) → S2,
        WeakConvexSphArm A' → PositiveJoints A' → NoNonadjacentRepeat A' →
        StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
        deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B') →
      endpt A ≤ endpt B)

theorem mainPlusNR_of_lt_two {m : ℕ} (hm : m < 2) : MainPlusNR m :=
  fun A B hA _ _ hB hside hangle => main_of_lt_two hm A B hA hB hside hangle

theorem mainPlusNR_two : MainPlusNR 2 :=
  fun A B hA _ _ hB hside hangle => main_two A B hA hB hside hangle

/-- Interval subarms inherit no nonadjacent repeats. -/
theorem intervalArm_noNonadjacentRepeat {N : ℕ} {A : Fin (N + 1) → S2}
    (hnr : NoNonadjacentRepeat A) {a m : ℕ} (hb : a + m ≤ N) :
    NoNonadjacentRepeat (intervalArm A a m hb) := by
  intro r s hr hs hrs heq
  have hAeq : A ⟨a + r, by omega⟩ = A ⟨a + s, by omega⟩ := by
    simpa [intervalArm_apply] using heq
  exact hnr (a + r) (a + s) (by omega) (by omega) (by omega) hAeq

/-- Ear chord comparison from the `MainPlusNR` IH. -/
theorem ear_chord_le_of_MainPlusNR {N : ℕ} {A B : Fin (N + 1) → S2} {a m : ℕ}
    (hb : a + m ≤ N)
    (hMm : MainPlusNR m)
    (hposA : PositiveJoints A)
    (hnrA : NoNonadjacentRepeat A)
    (hAe : WeakConvexSphArm (intervalArm A a m hb))
    (hBe : StrictConvexSphArm (intervalArm B a m hb))
    (hside : ∀ i : Fin N, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (N - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A ⟨a, by omega⟩) (A ⟨a + m, by omega⟩)
      ≤ sDist (B ⟨a, by omega⟩) (B ⟨a + m, by omega⟩) := by
  have hposEar : PositiveJoints (intervalArm A a m hb) :=
    intervalArm_positiveJoints a m hb hposA
  have hnrEar : NoNonadjacentRepeat (intervalArm A a m hb) :=
    intervalArm_noNonadjacentRepeat hnrA hb
  have hcmp : endpt (intervalArm A a m hb) ≤ endpt (intervalArm B a m hb) :=
    hMm (intervalArm A a m hb) (intervalArm B a m hb) hAe hposEar hnrEar hBe
      (intervalArm_sameSides hb hside) (intervalArm_jointLe hb hangle)
  rwa [intervalArm_endpt A a m hb, intervalArm_endpt B a m hb] at hcmp

/-- `(0,n)` folded-flat boundary close with the NR induction hypothesis. -/
theorem foldedFlat_boundary_j_eq_n_nr {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (ih : ∀ m : ℕ, m < n → MainPlusNR m)
    (hposA : PositiveJoints A)
    (hnrA : NoNonadjacentRepeat A)
    (hside : SameSides A B)
    (hangle : JointLe A B)
    (hAe : WeakConvexSphArm (intervalArm A 1 (n - 1) (by omega)))
    (hBe : StrictConvexSphArm (intervalArm B 1 (n - 1) (by omega)))
    (hcol : (A ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨1, by omega⟩ : E3), (A ⟨n, by omega⟩ : E3)} : Set E3)) :
    endpt A ≤ endpt B := by
  have h1n : 1 + (n - 1) = n := by omega
  have hbtw : sDist (A ⟨1, by omega⟩) (A ⟨n, by omega⟩)
      = sDist (A ⟨1, by omega⟩) (A ⟨0, by omega⟩)
        + sDist (A ⟨0, by omega⟩) (A ⟨n, by omega⟩) :=
    sDist_betweenness_of_collinear (p := A ⟨1, by omega⟩) (q := A ⟨0, by omega⟩)
      (r := A ⟨n, by omega⟩) hcol
  have hMm : MainPlusNR (n - 1) := ih (n - 1) (by omega)
  have hear0 := ear_chord_le_of_MainPlusNR (A := A) (B := B) (a := 1) (m := n - 1)
    (by omega) hMm hposA hnrA hAe hBe hside hangle
  have hidx : (⟨1 + (n - 1), by omega⟩ : Fin (n + 1)) = (⟨n, by omega⟩ : Fin (n + 1)) :=
    Fin.ext h1n
  rw [hidx] at hear0
  have hear : sDist (A ⟨1, by omega⟩) (A ⟨n, by omega⟩)
      ≤ sDist (B ⟨1, by omega⟩) (B ⟨n, by omega⟩) := hear0
  have hs0 := hside ⟨0, by omega⟩
  have hsA : sideLen A (⟨0, by omega⟩ : Fin n) =
      sDist (A ⟨0, by omega⟩) (A ⟨1, by omega⟩) := by
    rw [sideLen]; rfl
  have hsB : sideLen B (⟨0, by omega⟩ : Fin n) =
      sDist (B ⟨0, by omega⟩) (B ⟨1, by omega⟩) := by
    rw [sideLen]; rfl
  rw [hsA, hsB] at hs0
  have htriB : sDist (B ⟨1, by omega⟩) (B ⟨n, by omega⟩)
      ≤ sDist (B ⟨1, by omega⟩) (B ⟨0, by omega⟩)
        + sDist (B ⟨0, by omega⟩) (B ⟨n, by omega⟩) :=
    sDist_triangle (B ⟨1, by omega⟩) (B ⟨0, by omega⟩) (B ⟨n, by omega⟩)
  have hsymmA : sDist (A ⟨1, by omega⟩) (A ⟨0, by omega⟩) =
      sDist (A ⟨0, by omega⟩) (A ⟨1, by omega⟩) := sDist_comm _ _
  have hsymmB : sDist (B ⟨1, by omega⟩) (B ⟨0, by omega⟩) =
      sDist (B ⟨0, by omega⟩) (B ⟨1, by omega⟩) := sDist_comm _ _
  have heA : endpt A = sDist (A ⟨0, by omega⟩) (A ⟨n, by omega⟩) := by
    rw [endpt]; congr 1
  have heB : endpt B = sDist (B ⟨0, by omega⟩) (B ⟨n, by omega⟩) := by
    rw [endpt]; congr 1
  rw [heA, heB]
  linarith [hbtw, hear, hs0, htriB, hsymmA, hsymmB]

/-- Forward folded-flat transport with the NR dimension IH. -/
theorem foldedFlatCutTransportPlusForwardNR_holds :
    ∀ n : ℕ, 2 ≤ n →
      (∀ m : ℕ, m < n → MainPlusNR m) →
      ∀ A B : Fin (n + 1) → S2,
        WeakConvexSphArm A → PositiveJoints A → NoNonadjacentRepeat A →
        StrictConvexSphArm B → SameSides A B → JointLe A B →
        ∀ i j : ℕ, i + 1 < j →
          ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
          (A ⟨i, by omega⟩ : E3) ∈
            Submodule.span NNReal ({(A ⟨i + 1, hi1⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3) →
          sDist (A ⟨i, by omega⟩) (A ⟨j, hj⟩) ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩) →
          endpt A ≤ endpt B := by
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
        exact foldedFlat_boundary_j_eq_n_nr hn ih hposA hnr hside hangle hAe hBe hcol'
      · subst hjn1
        have hcol' : (A ⟨0, by omega⟩ : E3) ∈
            Submodule.span NNReal
              ({(A ⟨1, by omega⟩ : E3), (A ⟨n - 1, by omega⟩ : E3)} : Set E3) := by
          have hidx1 : (⟨0 + 1, hi1⟩ : Fin (n + 1)) =
              (⟨1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
          have hidxj : (⟨n - 1, hj⟩ : Fin (n + 1)) =
              (⟨n - 1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
          rwa [hidx1, hidxj] at hcol
        have htail : TailFoldBoundary A (by omega) :=
          TailFoldBoundary_holds_context (by omega) hA hposA hB hangle hnr hcol'
        have hdiag' : sDist (A ⟨0, by omega⟩) (A ⟨n - 1, by omega⟩)
            ≤ sDist (B ⟨0, by omega⟩) (B ⟨n - 1, by omega⟩) := hdiag
        exact foldedFlat_boundary_j_eq_n_minus_one hn hside htail hdiag'

/-! ## Static b-trichotomy with NR. -/

/-- Diagonal inequality for the positive-positive branch using the NR dimension IH. -/
theorem diag_le_of_positive_span_at_level_nr
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
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
  have hMm : MainPlusNR (j - (i + 1)) := ihdim (j - (i + 1)) (by omega)
  have hear0 := ear_chord_le_of_MainPlusNR (A := P) (B := B)
    (a := i + 1) (m := j - (i + 1)) hbnd hMm hpos hnr hAe hBe hside hangle
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

/-- Positive-positive coefficient branch at a live NR induction level. -/
theorem bpos_apos_endpoint_at_level_nr
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    {i j : ℕ} (hij : i + 1 < j)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hbpos : 0 < b) (hapos : 0 < a) :
    endpt P ≤ endpt B := by
  have hcol := span_mem_of_positive_coeffs hi hi1 hj hspan hbpos hapos
  by_cases hfar : i + 2 < j
  · have hdiag := diag_le_of_positive_span_at_level_nr hP hpos hnr hB hside hangle ihdim
      hij hfar hi hi1 hj hspan hbpos hapos
    exact foldedFlatCutTransportPlusForwardNR_holds n hP.two_le ihdim P B hP hpos hnr hB
      hside hangle i j hij hi1 hj hcol hdiag
  · have hjeq : j = i + 2 := by omega
    subst hjeq
    have hcol2 : (P ⟨i, hi⟩ : E3) ∈
        Submodule.span NNReal
          ({(P ⟨i + 1, hi1⟩ : E3), (P ⟨i + 2, hj⟩ : E3)} : Set E3) := by
      simpa using hcol
    exact False.elim (foldedFlat_adjacent_contradiction (i := i) hP hpos (by omega) hcol2)

/-- Coefficient dispatch at a fixed NR induction level. -/
theorem endpoint_of_span_at_level_nr
    (htail : BPosANegTailCornerResidue)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
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
    · exact bpos_apos_endpoint_at_level_nr hP hpos hnr hB hside hangle ihdim
        hij hi hi1 hj hspan hbpos hapos

/-- A normalized zero support on a weak-positive NR arm closes at a fixed NR level. -/
theorem endpoint_of_normalized_vanishing_support_at_level_nr
    (htail : BPosANegTailCornerResidue)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B)
    (hside : SameSides P B) (hangle : JointLe P B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
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
    rwa [ProofsInTheBook.ZinanFFCT12.det3_cyclic (P ⟨i, hi⟩ : E3)
      (P ⟨i + 1, hi1⟩ : E3) (P ⟨j, hj⟩ : E3)] at hzero
  obtain ⟨a, b, hspan⟩ :=
    lin_indep_span_of_det3_zero (P ⟨i + 1, hi1⟩).2 (P ⟨j, hj⟩).2
      (fun h => hdist (S2.ext h)) hanti hdet
  exact endpoint_of_span_at_level_nr htail hP hpos hnr hB hside hangle
    ⟨h, hnorm, hhemPos⟩ ihdim hij hi hi1 hj hspan

/-! ## Normalized weak-entry seed. -/

/-- The remaining static wrap-edge seed for a raw weak-entry vanishing support. -/
def WeakVanishingWrapSeedResidue : Prop :=
  ∀ {n : ℕ} (P B : Fin (n + 1) → S2),
    WeakConvexSphArm P → PositiveJoints P → NoNonadjacentRepeat P →
    StrictConvexSphArm B → SameSides P B → JointLe P B →
    ∀ a b : Fin (n + 1),
      b ≠ a → b ≠ a + 1 → ¬ a.val + 1 < n + 1 →
      sOrient (P a) (P (a + 1)) (P b) = 0 →
        (∃ i j : ℕ, ∃ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
          i + 1 < j ∧
            sOrient (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨j, hj⟩) = 0)
        ∨
        (∃ i j : ℕ, ∃ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
          i + 1 < j ∧
            sOrient (mirrorArm P ⟨i, hi⟩) (mirrorArm P ⟨i + 1, hi1⟩)
              (mirrorArm P ⟨j, hj⟩) = 0)

/-- Raw weak-entry vanishing support normalized up to mirror, modulo only the wrap-edge residue. -/
theorem weakMirrorSeed_of_wrapSeedResidue
    (hwrap : WeakVanishingWrapSeedResidue)
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hpos : PositiveJoints P) (hnr : NoNonadjacentRepeat P)
    (hB : StrictConvexSphArm B) (hside : SameSides P B) (hangle : JointLe P B)
    (hvanish : ∃ a b : Fin (n + 1), b ≠ a ∧ b ≠ a + 1 ∧
      sOrient (P a) (P (a + 1)) (P b) = 0) :
      (∃ i j : ℕ, ∃ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
        i + 1 < j ∧
          sOrient (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨j, hj⟩) = 0)
      ∨
      (∃ i j : ℕ, ∃ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
        i + 1 < j ∧
          sOrient (mirrorArm P ⟨i, hi⟩) (mirrorArm P ⟨i + 1, hi1⟩)
            (mirrorArm P ⟨j, hj⟩) = 0) := by
  obtain ⟨a, b, hne, hne1, hsupp⟩ := hvanish
  by_cases hadj : a.val + 1 < n + 1
  · rcases orientationNormalized P hne hne1 hsupp hadj with hdir | hrev
    · obtain ⟨i, j, hij, hj, hzero⟩ := hdir
      left
      refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
      simpa using hzero
    · obtain ⟨i, j, hij, hj, hzero⟩ := hrev
      right
      refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
      exact mirrorArm_sOrient_zero_of_revArm_zero P (by omega) (by omega) (by omega) hzero
  · exact hwrap P B hP hpos hnr hB hside hangle a b hne hne1 hadj hsupp

/-- Static weak-entry endpoint closure under NR. -/
def WeakPositiveCutReadyNR : Prop :=
  WeakVanishingWrapSeedResidue → BPosANegTailCornerResidue →
    ∀ {n : ℕ} {P B : Fin (n + 1) → S2},
      WeakConvexSphArm P → PositiveJoints P → NoNonadjacentRepeat P →
      StrictConvexSphArm B → SameSides P B → JointLe P B →
      (∀ m : ℕ, m < n → MainPlusNR m) →
      (∃ a b : Fin (n + 1), b ≠ a ∧ b ≠ a + 1 ∧
        sOrient (P a) (P (a + 1)) (P b) = 0) →
      endpt P ≤ endpt B

theorem weakPositiveCutReadyNR_holds : WeakPositiveCutReadyNR := by
  intro hwrap htail n P B hP hpos hnr hB hside hangle ihdim hvanish
  rcases weakMirrorSeed_of_wrapSeedResidue hwrap hP hpos hnr hB hside hangle hvanish with hdir | hmir
  · obtain ⟨i, j, hi, hi1, hj, hij, hzero⟩ := hdir
    exact endpoint_of_normalized_vanishing_support_at_level_nr htail hP hpos hnr hB
      hside hangle hP.closed_convex.open_hemisphere ihdim hij hi hi1 hj hzero
  · obtain ⟨i, j, hi, hi1, hj, hij, hzero⟩ := hmir
    have hmirror : endpt (mirrorArm P) ≤ endpt (mirrorArm B) :=
      endpoint_of_normalized_vanishing_support_at_level_nr htail
        (weakConvex_mirrorArm hP) (positiveJoints_mirrorArm hpos)
        (noNonadjacentRepeat_mirrorArm hnr)
        (strictConvex_mirrorArm hB) (sameSides_mirrorArm hside) (jointLe_mirrorArm hangle)
        (weakConvex_mirrorArm hP).closed_convex.open_hemisphere ihdim hij hi hi1 hj hzero
    simpa [endpt_mirrorArm] using hmirror

/-! ## WBS support-stuck dispatch with the NR IH. -/

structure Ch13FinalSurface74 : Prop where
  hweakWrapSeed : WeakVanishingWrapSeedResidue
  hwrapSeed : SupportStuckWBSWrapSeedResidue
  hcross : CrossPieceNoCollisionAtSup
  hbpos_aneg_tail : BPosANegTailCornerResidue

theorem supportStuckWBS_endpoint_dispatch_at_level_nr
    (res : Ch13FinalSurface74)
    {n : ℕ} (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
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
    exact endpoint_of_normalized_vanishing_support_at_level_nr res.hbpos_aneg_tail
      hPweak hPpos hnr hB hside' hangle' hhem ihdim hij hi hi1 hj hzero
  · obtain ⟨i, j, hi, hi1, hj, hij, hzero⟩ := hmir
    have hmirror : endpt (mirrorArm (openedWBS A B k)) ≤ endpt (mirrorArm B) :=
      endpoint_of_normalized_vanishing_support_at_level_nr res.hbpos_aneg_tail
        (weakConvex_mirrorArm hPweak) (positiveJoints_mirrorArm hPpos)
        (noNonadjacentRepeat_mirrorArm hnr)
        (strictConvex_mirrorArm hB) (sameSides_mirrorArm hside') (jointLe_mirrorArm hangle')
        (weakConvex_mirrorArm hPweak).closed_convex.open_hemisphere ihdim
        hij hi hi1 hj hzero
    simpa [endpt_mirrorArm] using hmirror

theorem open_step_wbs_nr (res : Ch13FinalSurface74)
    {n : ℕ} (_hn : 2 ≤ n) (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (ihdef : ∀ A' B' : Fin (n + 1) → S2,
      WeakConvexSphArm A' → PositiveJoints A' → NoNonadjacentRepeat A' →
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
      supportStuckWBS_endpoint_dispatch_at_level_nr res ihdim A B hA hB hside hangle k hkdef hstuck
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
        (strictConvexSphArm_positiveJoints hstrict) (strictConvex_noNonadjacentRepeat hstrict)
        hB hside' hangle' hdrop
    exact le_trans hmono hAB

/-- The NR opening step. -/
theorem szOpeningStepPlusNR_v8 (res : Ch13FinalSurface74) : SZOpeningStepPlusNR := by
  intro n hn ihdim A B hA hposA hnrA hB hside hangle ihdef
  rcases strict_or_vanishing hA with hvanish | hAstrict
  · exact weakPositiveCutReadyNR_holds res.hweakWrapSeed res.hbpos_aneg_tail
      hA hposA hnrA hB hside hangle ihdim hvanish
  · by_cases hnd : deficitCount A B = 0
    · exact congruence_step hAstrict hB hside hangle hnd
    · have hpos : 0 < deficitCount A B := Nat.pos_of_ne_zero hnd
      obtain ⟨k, hkdef⟩ := exists_deficit_of_pos hpos
      exact open_step_wbs_nr res hn ihdim hAstrict hB hside hangle ihdef k hkdef

theorem mainPlusNR_at_level (res : Ch13FinalSurface74) {n : ℕ} (hn : 2 ≤ n)
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m) : MainPlusNR n := by
  intro A B hA hposA hnrA hB hside hangle
  let hstep := szOpeningStepPlusNR_v8 res
  have hrec :
      ∀ d : ℕ, ∀ A B : Fin (n + 1) → S2,
        WeakConvexSphArm A → PositiveJoints A → NoNonadjacentRepeat A →
        StrictConvexSphArm B → SameSides A B → JointLe A B →
        deficitCount A B = d → endpt A ≤ endpt B := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
      intro A B hA hposA hnrA hB hside hangle hdef
      refine hstep n hn ihdim A B hA hposA hnrA hB hside hangle ?_
      intro A' B' hA' hposA' hnrA' hB' hside' hangle' hlt
      exact IH (deficitCount A' B') (hdef ▸ hlt) A' B' hA' hposA' hnrA'
        hB' hside' hangle' rfl
  exact hrec (deficitCount A B) A B hA hposA hnrA hB hside hangle rfl

theorem mainPlusNR_all (res : Ch13FinalSurface74) : ∀ n : ℕ, 2 ≤ n → MainPlusNR n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn A B hA hposA hnrA hB hside hangle
    have ihdim : ∀ m : ℕ, m < n → MainPlusNR m := by
      intro m hm
      rcases Nat.lt_or_ge m 2 with h2 | h2
      · exact mainPlusNR_of_lt_two h2
      · exact IH m hm h2
    exact mainPlusNR_at_level res hn ihdim A B hA hposA hnrA hB hside hangle

/-- Final strict-arm headline through the NR recursion. -/
theorem spherical_arm_mono_final_ch13_v8 (res : Ch13FinalSurface74)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  (mainPlusNR_all res n hn) A B (strictConvexSphArm_toWeak hA)
    (strictConvexSphArm_positiveJoints hA) (strictConvex_noNonadjacentRepeat hA)
    hB hside hangle

/-! ## Guards. -/

theorem weakPositiveCutReadyNR_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

theorem spherical_arm_mono_final_ch13_v8_conclusion_satisfiable {n : ℕ}
    (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

#print axioms intervalArm_noNonadjacentRepeat
#print axioms ear_chord_le_of_MainPlusNR
#print axioms foldedFlatCutTransportPlusForwardNR_holds
#print axioms endpoint_of_normalized_vanishing_support_at_level_nr
#print axioms weakPositiveCutReadyNR_holds
#print axioms supportStuckWBS_endpoint_dispatch_at_level_nr
#print axioms szOpeningStepPlusNR_v8
#print axioms mainPlusNR_all
#print axioms spherical_arm_mono_final_ch13_v8

end ProofsInTheBook.ZinanFFCT74
