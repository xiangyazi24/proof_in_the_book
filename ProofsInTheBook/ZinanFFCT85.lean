import ProofsInTheBook.ZinanFFCT84

/-!
# `ZinanFFCT85` -- first-step wrap residue closure

This layer closes the two v9 wrap-boundary residues by the same first-step
trick used in `ZinanFFCT84`: a cone holder at one endpoint, plus the adjacent
ordinary edge supports at the two cone anchors, forces the adjacent vertex into
the anchor plane.  The resulting coplanar ordinary edge gives the endpoint-aware
wrap payload consumed by the v10 assembly.

No proof placeholders or unsafe declarations.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
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
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82
open ProofsInTheBook.ZinanFFCT83
open ProofsInTheBook.ZinanFFCT84

namespace ProofsInTheBook.ZinanFFCT85

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## Local first-step algebra. -/

/-- If `C` is the first endpoint of an ordinary edge and lies in the open cone
of anchors `P,Q`, then weak supports of the edge `(C,Y)` at both anchors force
`Y` into the anchor plane. -/
theorem edgeAnchor_next_plane_of_prev_openCone
    {P Q C Y : S2}
    (hC : OpenCone P Q C)
    (hCP : 0 ≤ sOrient C Y P)
    (hCQ : 0 ≤ sOrient C Y Q) :
    sOrient P Q Y = 0 := by
  rcases hC with ⟨c, d, hc, hd, hrep⟩
  set D : ℝ := det3 (P : E3) (Q : E3) (Y : E3)
  have hCP' : 0 ≤ d * D := by
    have hid :
        det3 (c • (P : E3) + d • (Q : E3)) (Y : E3) (P : E3) =
          d * D := by
      simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [sOrient, hrep] at hCP
    simpa [hid] using hCP
  have hCQ' : 0 ≤ -c * D := by
    have hid :
        det3 (c • (P : E3) + d • (Q : E3)) (Y : E3) (Q : E3) =
          -c * D := by
      simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [sOrient, hrep] at hCQ
    simpa [hid] using hCQ
  have hDge : 0 ≤ D := by nlinarith [hCP', hd]
  have hDle : D ≤ 0 := by nlinarith [hCQ', hc]
  have hD : D = 0 := by linarith
  simpa [sOrient, D] using hD

/-- Coplanarity with the cone anchors turns the predecessor edge `(Y,C)` into
a zero support with the left anchor as probe. -/
theorem openCone_prevEdge_left_zero_of_plane
    {P Q C Y : S2}
    (hC : OpenCone P Q C)
    (hplane : sOrient P Q Y = 0) :
    sOrient Y C P = 0 := by
  rcases hC with ⟨c, d, _hc, _hd, hrep⟩
  rw [sOrient] at hplane ⊢
  set D : ℝ := det3 (P : E3) (Q : E3) (Y : E3)
  have hD : D = 0 := by simpa [D] using hplane
  have hid :
      det3 (Y : E3) (c • (P : E3) + d • (Q : E3)) (P : E3) =
        -d * D := by
    simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hrep, hid, hD, mul_zero]

/-- Coplanarity with the cone anchors turns the predecessor edge `(Y,C)` into
a zero support with the right anchor as probe. -/
theorem openCone_prevEdge_right_zero_of_plane
    {P Q C Y : S2}
    (hC : OpenCone P Q C)
    (hplane : sOrient P Q Y = 0) :
    sOrient Y C Q = 0 := by
  rcases hC with ⟨c, d, _hc, _hd, hrep⟩
  rw [sOrient] at hplane ⊢
  set D : ℝ := det3 (P : E3) (Q : E3) (Y : E3)
  have hD : D = 0 := by simpa [D] using hplane
  have hid :
      det3 (Y : E3) (c • (P : E3) + d • (Q : E3)) (Q : E3) =
        c * D := by
    simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hrep, hid, hD, mul_zero]

/-- Coplanarity with the cone anchors turns the successor edge `(C,Y)` into
a zero support with the left anchor as probe. -/
theorem openCone_nextEdge_left_zero_of_plane
    {P Q C Y : S2}
    (hC : OpenCone P Q C)
    (hplane : sOrient P Q Y = 0) :
    sOrient C Y P = 0 := by
  rcases hC with ⟨c, d, _hc, _hd, hrep⟩
  rw [sOrient] at hplane ⊢
  set D : ℝ := det3 (P : E3) (Q : E3) (Y : E3)
  have hD : D = 0 := by simpa [D] using hplane
  have hid :
      det3 (c • (P : E3) + d • (Q : E3)) (Y : E3) (P : E3) =
        d * D := by
    simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hrep, hid, hD, mul_zero]

/-! ## Packaging ordinary support zeroes as mirror-aware boundary progress. -/

/-- Any ordinary raw zero support can be packaged as the v9 mirror-aware
boundary-progress payload by the landed orientation normalizer. -/
theorem mirrorBoundaryProgress_of_raw_ordinary_zero
    {n : ℕ} (P B : Fin (n + 1) → S2) {a b : Fin (n + 1)}
    (hne : b ≠ a) (hne1 : b ≠ a + 1)
    (hadj : a.val + 1 < n + 1)
    (hsupp : sOrient (P a) (P (a + 1)) (P b) = 0) :
    MirrorBoundaryZeroProgress P B := by
  rcases orientationNormalized P hne hne1 hsupp hadj with hdir | hrev
  · left
    left
    obtain ⟨i, j, hij, hj, hzero⟩ := hdir
    refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
    simpa using hzero
  · right
    left
    obtain ⟨i, j, hij, hj, hzero⟩ := hrev
    refine ⟨i, j, by omega, by omega, by omega, hij, ?_⟩
    exact mirrorArm_sOrient_zero_of_revArm_zero P (by omega) (by omega) (by omega) hzero

/-! ## The first-step wrap theorem used by both residues. -/

theorem openCone_last_of_head_span_opposite
    {n : ℕ} {P : Fin (n + 1) → S2} {j : Fin (n + 1)}
    {c d : ℝ}
    (hspan :
      (P 0 : E3) =
        c • (P (Fin.last n) : E3) + d • (P j : E3))
    (hc : 0 < c) (hd : d < 0) :
    OpenCone (P 0) (P j) (P (Fin.last n)) := by
  refine ⟨1 / c, (-d) / c, div_pos zero_lt_one hc,
    div_pos (neg_pos.mpr hd) hc, ?_⟩
  have hcne : c ≠ 0 := ne_of_gt hc
  have hcvec :
      c • (P (Fin.last n) : E3) =
        (P 0 : E3) - d • (P j : E3) := by
    rw [hspan]
    module
  calc
    (P (Fin.last n) : E3)
        = (1 / c) • (c • (P (Fin.last n) : E3)) := by
            rw [smul_smul, div_mul_cancel₀ _ hcne, one_smul]
    _ = (1 / c) • ((P 0 : E3) - d • (P j : E3)) := by
            rw [hcvec]
    _ = (1 / c) • (P 0 : E3) + ((-d) / c) • (P j : E3) := by
            rw [smul_sub, smul_smul]
            module

theorem openCone_probe_of_head_span_opposite
    {n : ℕ} {P : Fin (n + 1) → S2} {j : Fin (n + 1)}
    {c d : ℝ}
    (hspan :
      (P 0 : E3) =
        c • (P (Fin.last n) : E3) + d • (P j : E3))
    (hc : c < 0) (hd : 0 < d) :
    OpenCone (P 0) (P (Fin.last n)) (P j) := by
  refine ⟨1 / d, (-c) / d, div_pos zero_lt_one hd,
    div_pos (neg_pos.mpr hc) hd, ?_⟩
  have hdne : d ≠ 0 := ne_of_gt hd
  have hdvec :
      d • (P j : E3) =
        (P 0 : E3) - c • (P (Fin.last n) : E3) := by
    rw [hspan]
    module
  calc
    (P j : E3)
        = (1 / d) • (d • (P j : E3)) := by
            rw [smul_smul, div_mul_cancel₀ _ hdne, one_smul]
    _ = (1 / d) • ((P 0 : E3) - c • (P (Fin.last n) : E3)) := by
            rw [hdvec]
    _ = (1 / d) • (P 0 : E3) + ((-c) / d) • (P (Fin.last n) : E3) := by
            rw [smul_sub, smul_smul]
            module

/-- A wrap zero at `(n,0,j)` gives v9 mirror-aware boundary progress by one
adjacent-edge step from whichever vertex is the open-cone holder. -/
theorem mirrorBoundaryProgress_of_wrap_firstStep
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (hP : WeakConvexSphArm P)
    (hnr : NoNonadjacentRepeat P)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    {j : Fin (n + 1)}
    (hj_ne_last : j ≠ Fin.last n)
    (hj_ne_zero : j ≠ 0)
    (hzero : sOrient (P (Fin.last n)) (P 0) (P j) = 0) :
    MirrorBoundaryZeroProgress P B := by
  obtain ⟨c, d, hspan⟩ :=
    wrap_zero_real_span_of_context hP hnr hhem hj_ne_last hzero
  rcases lt_trichotomy c 0 with hcneg | hc0 | hcpos
  · rcases lt_trichotomy d 0 with hdneg | hd0 | hdpos
    · exact False.elim (wrap_initial_both_negative_absurd hhem hspan hcneg hdneg)
    · exact False.elim (wrap_initial_probe_coeff_zero_absurd hP hhem hspan hd0)
    · have hcone : OpenCone (P 0) (P (Fin.last n)) (P j) :=
        openCone_probe_of_head_span_opposite hspan hcneg hdpos
      have hjpos : 0 < j.val := by
        have hj0 : j.val ≠ 0 := by
          intro hj0
          exact hj_ne_zero (Fin.ext (by simpa using hj0))
        omega
      have hjlt : j.val < n := by
        have hjn : j.val ≠ n := by
          intro hjn
          exact hj_ne_last (Fin.ext (by simpa using hjn))
        omega
      let r : ℕ := j.val - 1
      have hr : r < n + 1 := by
        dsimp [r]
        omega
      have hsucc : ((⟨r, hr⟩ : Fin (n + 1)) + 1) = j := by
        apply Fin.ext
        have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
          rw [Fin.val_one']
          exact Nat.mod_eq_of_lt (by omega)
        rw [Fin.val_add, Fin.val_mk, hone,
          Nat.mod_eq_of_lt (show r + 1 < n + 1 by dsimp [r]; omega)]
        dsimp [r]
        omega
      have hY0 :
          0 ≤ sOrient (P ⟨r, hr⟩) (P j) (P 0) := by
        have h := hP.closed_convex.edge_support ⟨r, hr⟩ 0
        simpa [hsucc] using h
      have hYn :
          0 ≤ sOrient (P ⟨r, hr⟩) (P j) (P (Fin.last n)) := by
        have h := hP.closed_convex.edge_support ⟨r, hr⟩ (Fin.last n)
        simpa [hsucc] using h
      have hplane :
          sOrient (P 0) (P (Fin.last n)) (P ⟨r, hr⟩) = 0 :=
        edgeAnchor_prev_plane_of_next_openCone hcone hY0 hYn
      have hraw :
          sOrient (P ⟨r, hr⟩) (P j) (P (Fin.last n)) = 0 :=
        openCone_prevEdge_right_zero_of_plane hcone hplane
      left
      left
      refine ⟨r, n, by omega, by omega, by omega, ?_, ?_⟩
      · dsimp [r]
        omega
      · have hjidx : (⟨r + 1, by omega⟩ : Fin (n + 1)) = j := by
          apply Fin.ext
          dsimp [r]
          omega
        have hlast : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n :=
          Fin.ext (by simp)
        simpa [hjidx, hlast] using hraw
  · exact False.elim (wrap_initial_last_coeff_zero_absurd hP hnr hhem hj_ne_zero hspan hc0)
  · rcases lt_trichotomy d 0 with hdneg | hd0 | hdpos
    · have hcone : OpenCone (P 0) (P j) (P (Fin.last n)) :=
        openCone_last_of_head_span_opposite hspan hcpos hdneg
      have hprev : n - 1 < n + 1 := by omega
      have hsucc :
          ((⟨n - 1, hprev⟩ : Fin (n + 1)) + 1) = Fin.last n := by
        apply Fin.ext
        have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
          rw [Fin.val_one']
          exact Nat.mod_eq_of_lt (by omega)
        rw [Fin.val_add, Fin.val_mk, hone,
          Nat.mod_eq_of_lt (show n - 1 + 1 < n + 1 by omega)]
        simp
        omega
      have hY0 :
          0 ≤ sOrient (P ⟨n - 1, hprev⟩) (P (Fin.last n)) (P 0) := by
        have h := hP.closed_convex.edge_support ⟨n - 1, hprev⟩ 0
        simpa [hsucc] using h
      have hYj :
          0 ≤ sOrient (P ⟨n - 1, hprev⟩) (P (Fin.last n)) (P j) := by
        have h := hP.closed_convex.edge_support ⟨n - 1, hprev⟩ j
        simpa [hsucc] using h
      have hplane :
          sOrient (P 0) (P j) (P ⟨n - 1, hprev⟩) = 0 :=
        edgeAnchor_prev_plane_of_next_openCone hcone hY0 hYj
      have hraw0 :
          sOrient (P ⟨n - 1, hprev⟩) (P (Fin.last n)) (P 0) = 0 :=
        openCone_prevEdge_left_zero_of_plane hcone hplane
      let a : Fin (n + 1) := ⟨n - 1, hprev⟩
      let b : Fin (n + 1) := 0
      have hsucc_a : a + 1 = Fin.last n := by simpa [a] using hsucc
      have hne : b ≠ a := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [a, b] at hv
        omega
      have hne1 : b ≠ a + 1 := by
        rw [hsucc_a]
        intro h
        have hv := congrArg Fin.val h
        dsimp [b] at hv
        change (0 : ℕ) = n at hv
        omega
      have hadj : a.val + 1 < n + 1 := by
        dsimp [a]
        omega
      have hraw :
          sOrient (P a) (P (a + 1)) (P b) = 0 := by
        simpa [a, b, hsucc_a] using hraw0
      exact mirrorBoundaryProgress_of_raw_ordinary_zero P B hne hne1 hadj hraw
    · exact False.elim (wrap_initial_probe_coeff_zero_absurd hP hhem hspan hd0)
    · have hcone : OpenCone (P (Fin.last n)) (P j) (P 0) :=
        ⟨c, d, hcpos, hdpos, hspan⟩
      have h1 : 1 < n + 1 := by omega
      have hsucc0 : ((0 : Fin (n + 1)) + 1) = ⟨1, h1⟩ := by
        apply Fin.ext
        have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
          rw [Fin.val_one']
          exact Nat.mod_eq_of_lt (by omega)
        rw [Fin.val_add, Fin.val_zero, hone,
          Nat.mod_eq_of_lt (show 0 + 1 < n + 1 by omega)]
      have h0n :
          0 ≤ sOrient (P 0) (P ⟨1, h1⟩) (P (Fin.last n)) := by
        have h := hP.closed_convex.edge_support (0 : Fin (n + 1)) (Fin.last n)
        simpa [hsucc0] using h
      have h0j :
          0 ≤ sOrient (P 0) (P ⟨1, h1⟩) (P j) := by
        have h := hP.closed_convex.edge_support (0 : Fin (n + 1)) j
        simpa [hsucc0] using h
      have hplane :
          sOrient (P (Fin.last n)) (P j) (P ⟨1, h1⟩) = 0 :=
        edgeAnchor_next_plane_of_prev_openCone hcone h0n h0j
      have hraw :
          sOrient (P 0) (P ⟨1, h1⟩) (P (Fin.last n)) = 0 :=
        openCone_nextEdge_left_zero_of_plane hcone hplane
      left
      left
      refine ⟨0, n, by omega, by omega, by omega, by omega, ?_⟩
      have hzero : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
      have hlast : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n :=
        Fin.ext (by simp)
      simpa [hzero, hlast] using hraw

/-! ## The two v9 wrap residues. -/

theorem weakWrapSeed_v9_of_firstStep :
    WeakVanishingWrapSeedResidueV9 := by
  intro n P B hP _hpos hnr _hB _hside _hangle a b hne hne1 hwrapBase hsupp
  have ha_val : a.val = n := weak_wrap_base_is_last hwrapBase
  have ha : a = Fin.last n := Fin.ext (by simpa using ha_val)
  have hsucc : a + 1 = (0 : Fin (n + 1)) :=
    weak_wrap_successor_is_zero hwrapBase
  have hb_ne_last : b ≠ Fin.last n := by
    intro hb
    exact hne (hb.trans ha.symm)
  have hb_ne_zero : b ≠ 0 := by
    intro hb
    exact hne1 (hb.trans hsucc.symm)
  have hzero :
      sOrient (P (Fin.last n)) (P 0) (P b) = 0 := by
    simpa [ha, hsucc] using hsupp
  exact mirrorBoundaryProgress_of_wrap_firstStep hP.two_le hP hnr
    hP.closed_convex.open_hemisphere hb_ne_last hb_ne_zero hzero

theorem supportStuckWBSWrapSeed_v9_of_firstStep
    (hcross : CrossPieceNoCollisionAtSup) :
    SupportStuckWBSWrapSeedResidueV9 := by
  intro n A B hA hB hside hangle k hkdef hstuck a b hne hne1 hwrapBase hsupp
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have hwrapArc :
      ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0) :=
    openedWrapShortArc_at_supWBS hA hB hka hkt hkdef
  have hPweak : WeakConvexSphArm (openedWBS A B k) := by
    unfold openedWBS
    exact supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrapArc
  have hedge := openedEdges_short_at_supWBS_of_wrap (A := A) (B := B) hA hwrapArc
  have hjopen := openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef
  have hhem0 := openHemisphere_at_WBS_sup hA hka hkt hkdef hedge hjopen
  have hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ) := by
    simpa [openedWBS] using hhem0
  have hnr : NoNonadjacentRepeat (openedWBS A B k) :=
    openedWBS_noNonadjacentRepeat_of_crossPiece hcross A B hA hB hside hangle k hkdef hstuck
  have ha_val : a.val = n := weak_wrap_base_is_last hwrapBase
  have ha : a = Fin.last n := Fin.ext (by simpa using ha_val)
  have hsucc : a + 1 = (0 : Fin (n + 1)) :=
    weak_wrap_successor_is_zero hwrapBase
  have hb_ne_last : b ≠ Fin.last n := by
    intro hb
    exact hne (hb.trans ha.symm)
  have hb_ne_zero : b ≠ 0 := by
    intro hb
    exact hne1 (hb.trans hsucc.symm)
  have hzero :
      sOrient (openedWBS A B k (Fin.last n)) (openedWBS A B k 0)
        (openedWBS A B k b) = 0 := by
    simpa [ha, hsucc] using hsupp
  exact mirrorBoundaryProgress_of_wrap_firstStep hPweak.two_le hPweak hnr hhem
    hb_ne_last hb_ne_zero hzero

/-! ## Final v10 assembly. -/

theorem spherical_arm_mono_final_ch13_v10
    (hcross : CrossPieceNoCollisionAtSup) :
    SphericalArmMonotone :=
  spherical_arm_mono_final_ch13_v10_of_hcross_and_boundaryResidues hcross
    { hweakWrapSeed := weakWrapSeed_v9_of_firstStep
      hwrapSeed := supportStuckWBSWrapSeed_v9_of_firstStep hcross
      hbpos_aneg_tail := bpos_aneg_tailCornerResidueV9_of_firstStepInteriorZero }

/-! ## Guards. -/

#print axioms edgeAnchor_next_plane_of_prev_openCone
#print axioms mirrorBoundaryProgress_of_wrap_firstStep
#print axioms weakWrapSeed_v9_of_firstStep
#print axioms supportStuckWBSWrapSeed_v9_of_firstStep
#print axioms spherical_arm_mono_final_ch13_v10

end ProofsInTheBook.ZinanFFCT85
