import ProofsInTheBook.ZinanFFCT100

/-!
# `ZinanFFCT111` -- DIRECT subarm-induction route for cross-piece no-collision

This file rebuilds the FFCT86 WBS support-stuck dispatch / recursion / headline as a
`v12` family that DROPS the cross-piece collision residue `CrossPieceCollisionEndpointAtSup`.
The collision branch of the dispatch is proven INLINE using the induction hypothesis
`ihdim : ∀ m < n → MainPlusNR m`, by a direct subarm argument:

* **full closure** `r = 0 ∧ s = n`: `endpt (openedWBS) = sDist self = 0 ≤ endpt B`;
* **`δ = 0`**: `openedWBS = A`, so the collision is a nonadjacent repeat of `A` — refuted;
* **`r = K` (`δ > 0`)**: the opened tail is a rigid rotation about `A K`; the `sDist_rotS2`
  isometry turns the collision into `A K = A s`, a nonadjacent repeat — refuted;
* **`r < K` (`δ > 0`)**: the genuine subarm-induction case — isolated as `SubarmIHContra`,
  which takes `ihdim` and is the single remaining residue (the weak-target / limit core).

Composing the `v12` recursion gives the Chapter-13 headline `SphericalArmMonotone` with the
`hcollision` residue replaced by the sharper `SubarmIHContra`.

## Route status (numerically verified TRUE; two false routes killed — see HANDOFF notes)
The cap route (`endpt_openTail_interior_mono_neg`) is DEAD: the subarm base angle exceeds the
full base angle (155497/155497), so the subarm cap `δ + sphAngle(A_r,A_K,A_s) ≤ π` is false —
the collision is a genuine over-opening.  The TRUE route is subarm-IH + weak-target via a limit
from below (`endpt A_sub ≤ endpt O_τ` for `τ < δ`, continuity sends `endpt O_τ → 0`).

No proof placeholders or unsafe declarations.
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
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalCyclicTriple
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
open ProofsInTheBook.ZinanFFCT66
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
open ProofsInTheBook.ZinanFFCT85
open ProofsInTheBook.ZinanFFCT86
open ProofsInTheBook.ZinanFFCT100

namespace ProofsInTheBook.ZinanFFCT111

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## Subarm strict convexity (general start index, including `r = 0`). -/

/-- Strict interval wrap data for `A[a..a+m]`, for an arbitrary start `a` (not just `a ≥ 1`).
Mirrors `intervalWrapDataStrict_of_cyclicTriple` but is valid at `a = 0` too. -/
theorem wrapDataStrict_general {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {a m : ℕ} (hm : 2 ≤ m) (hb : a + m ≤ n) :
    IntervalWrapDataStrict A a m hb := by
  have hcyc : CyclicTriplePos (n := n + 1) A := cyclicTriplePos_unconditional hA.closed_convex
  obtain ⟨h, _hnorm, hhem⟩ := hA.closed_convex.open_hemisphere
  have hbase : NoNonadjacentRepeat A := strictConvex_noNonadjacentRepeat hA
  refine { toWeak := { wrap_short := ?_, wrap_support := ?_ }, wrap_strict := ?_ }
  · refine ⟨?_, hemisphere_nonAntipodal hhem ⟨a + m, by omega⟩ ⟨a, by omega⟩⟩
    intro heq
    exact hbase a (a + m) (by omega) (by omega) (by omega) heq.symm
  · intro v hv
    by_cases hv0 : v = 0
    · subst hv0
      have : sOrient (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩) (A ⟨a + 0, by omega⟩) = 0 := by
        simp only [sOrient, det3]; ring
      rw [this]
    · by_cases hvm : v = m
      · have hav : a + v = a + m := by omega
        have hidx : (⟨a + v, by omega⟩ : Fin (n + 1)) = ⟨a + m, by omega⟩ := Fin.ext hav
        rw [hidx]
        have : sOrient (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩) (A ⟨a + m, by omega⟩) = 0 := by
          simp only [sOrient, det3]; ring
        rw [this]
      · have hpos : 0 < sOrient (A ⟨a, by omega⟩) (A ⟨a + v, by omega⟩) (A ⟨a + m, by omega⟩) :=
          hcyc ⟨a, by omega⟩ ⟨a + v, by omega⟩ ⟨a + m, by omega⟩
            (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
        rw [sOrient_cyclic (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩) (A ⟨a + v, by omega⟩)]
        exact le_of_lt hpos
  · intro v hv hvm hv0
    have hpos : 0 < sOrient (A ⟨a, by omega⟩) (A ⟨a + v, by omega⟩) (A ⟨a + m, by omega⟩) :=
      hcyc ⟨a, by omega⟩ ⟨a + v, by omega⟩ ⟨a + m, by omega⟩
        (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
    rw [sOrient_cyclic (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩) (A ⟨a + v, by omega⟩)]
    exact hpos

/-- The subarm `A[a..a+m]` of a strictly convex arm is strictly convex (for `2 ≤ m`). -/
theorem strictConvex_subarm {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {a m : ℕ} (hm : 2 ≤ m) (hb : a + m ≤ n) :
    StrictConvexSphArm (intervalArm A a m hb) :=
  strictConvex_intervalArm_of_wrap hA hm hb (wrapDataStrict_general hA hm hb)

/-! ## The isolated subarm-induction residue (`r < K`, `δ > 0`). -/

/-- The genuine subarm-induction residue: with the IH `MainPlusNR` for all smaller dimensions,
a proper cross collision whose opening axis is strictly interior to the pair (`r < K < s`) and
with positive opening (`0 < δ*`) is impossible.  This is the weak-target / limit core. -/
def SubarmIHContra : Prop :=
  ∀ {n : ℕ}, (∀ m : ℕ, m < n → MainPlusNR m) →
    ∀ (A B : Fin (n + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
      ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k → SupportStuckWBS A B k →
        ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1),
          r + 2 ≤ s →
          r < (openingAxis k).val → (openingAxis k).val < s →
          (0 < r ∨ s < n) →
          0 < monitoredSupWBS A B k →
          openedWBS A B k ⟨r, hr⟩ = openedWBS A B k ⟨s, hs⟩ → False

/-! ## v12 dispatch (collision branch proven inline via the IH). -/

/-- WBS support-stuck endpoint dispatch with the cross-piece collision residue removed.
Collision-free branches reconstruct opened no-repeat locally (verbatim from v11); collision
branches are discharged inline (full closure / `δ = 0` / `r = K`), with the `r < K` case routed
to the subarm-induction residue `SubarmIHContra`. -/
theorem supportStuckWBS_endpoint_dispatch_at_level_nr_v12
    (hSub : SubarmIHContra)
    {n : ℕ} (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k)
    (hstuck : SupportStuckWBS A B k) :
    endpt (openedWBS A B k) ≤ endpt B := by
  by_cases hnocross :
      ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1),
        r + 2 ≤ s →
        r ≤ (openingAxis k).val → (openingAxis k).val < s →
          openedWBS A B k ⟨r, hr⟩ ≠ openedWBS A B k ⟨s, hs⟩
  · obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
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
      openedWBS_noNonadjacentRepeat_of_localNoCross A B hA hB hside hangle
        k hkdef hstuck hnocross
    have hprog : MirrorBoundaryZeroProgress (openedWBS A B k) B :=
      supportStuckWBS_boundaryProgress_of_noRepeat_firstStep A B hA hB hside hangle
        k hkdef hstuck hPweak hnr hhem
    exact endpoint_of_mirrorBoundaryZeroProgress_at_level_nr
      bpos_aneg_tailCornerResidueV9_of_firstStepInteriorZero
      hPweak hPpos hnr hB hside' hangle' hhem ihdim hprog
  · push Not at hnocross
    obtain ⟨r, s, hr, hs, hrs, hrK, hKs, heq⟩ := hnocross
    have hbase : NoNonadjacentRepeat A := strictConvex_noNonadjacentRepeat hA
    by_cases hfull : r = 0 ∧ s = n
    · -- full-arm closure: `endpt (openedWBS) = sDist self = 0 ≤ endpt B`.
      obtain ⟨hr0, hsn⟩ := hfull
      have e0 : (0 : Fin (n + 1)) = ⟨r, hr⟩ := Fin.ext (by simp [hr0])
      have en : (Fin.last n) = ⟨s, hs⟩ := Fin.ext (by simp [hsn])
      have hzero : endpt (openedWBS A B k) = 0 := by
        unfold endpt
        rw [e0, en, heq]
        unfold sDist sInner
        rw [S2.inner_self]
        exact Real.arccos_one
      rw [hzero]
      unfold endpt
      exact sDist_nonneg _ _
    · -- proper collision: derive `False`.
      exfalso
      have hproper : 0 < r ∨ s < n := by
        rcases Nat.eq_zero_or_pos r with hr0 | hrpos
        · refine Or.inr ?_
          rcases Nat.lt_or_ge s n with hlt | hge
          · exact hlt
          · exact absurd ⟨hr0, le_antisymm (by omega) hge⟩ hfull
        · exact Or.inl hrpos
      set δ : ℝ := monitoredSupWBS A B k with hδdef
      by_cases hδ0 : δ = 0
      · have hO : openedWBS A B k = A := by
          simp only [openedWBS, ← hδdef, hδ0, neg_zero]
          exact openTail_zero_angle A (openingAxis k)
        rw [hO] at heq
        exact hbase r s hr hs hrs heq
      · have hδpos : 0 < δ := lt_of_le_of_ne (hδdef ▸ (monitoredSupWBS_mem_Icc hA
          (shortArcs_of_strict hA k).1 (shortArcs_of_strict hA k).2 hkdef).1) (Ne.symm hδ0)
        by_cases hrKeq : r = (openingAxis k).val
        · -- `r = K`: rigid rotation about `A K`; `heq` becomes `A K = A s`.
          have hrleK : r ≤ (openingAxis k).val := le_of_eq hrKeq
          have hrw_r : openedWBS A B k ⟨r, hr⟩ = A (openingAxis k) := by
            have h1 : openedWBS A B k ⟨r, hr⟩ = A ⟨r, hr⟩ := by
              simp only [openedWBS, ← hδdef]
              exact openTail_fixed A (openingAxis k) (-δ) hrleK
            rw [h1]
            congr 1
            exact Fin.ext (by simp [hrKeq])
          have hrw_s : openedWBS A B k ⟨s, hs⟩ = rotS2 (A (openingAxis k)) (-δ) (A ⟨s, hs⟩) := by
            simp only [openedWBS, ← hδdef]
            exact openTail_rot A (openingAxis k) (-δ) hKs
          rw [hrw_r, hrw_s] at heq
          have hzero : sDist (A (openingAxis k)) (A ⟨s, hs⟩) = 0 := by
            have hiso : sDist (A (openingAxis k)) (A ⟨s, hs⟩)
                = sDist (rotS2 (A (openingAxis k)) (-δ) (A (openingAxis k)))
                    (rotS2 (A (openingAxis k)) (-δ) (A ⟨s, hs⟩)) :=
              (sDist_rotS2 (A (openingAxis k)) (-δ) (A (openingAxis k)) (A ⟨s, hs⟩)).symm
            rw [hiso, rotS2_axis_fixed, ← heq, sDist_eq_zero_iff]
          have hKs2 : A (openingAxis k) = A ⟨s, hs⟩ := sDist_eq_zero_iff.mp hzero
          have hKlt : (openingAxis k).val + 2 ≤ s := by omega
          refine hbase (openingAxis k).val s (openingAxis k).isLt hs hKlt ?_
          rw [← hKs2]
        · -- `r < K`: the genuine subarm-induction residue.
          have hrK_lt : r < (openingAxis k).val := lt_of_le_of_ne hrK hrKeq
          exact hSub ihdim A B hA hB hside hangle k hkdef hstuck
            r s hr hs hrs hrK_lt hKs hproper hδpos heq

/-! ## v12 recursion and headline (mirroring FFCT86 v11, dropping `hcollision`). -/

theorem open_step_wbs_nr_v12
    (hSub : SubarmIHContra)
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
      supportStuckWBS_endpoint_dispatch_at_level_nr_v12 hSub ihdim
        A B hA hB hside hangle k hkdef hstuck
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

theorem szOpeningStepPlusNR_v12
    (hSub : SubarmIHContra) :
    SZOpeningStepPlusNR := by
  intro n hn ihdim A B hA hposA hnrA hB hside hangle ihdef
  rcases strict_or_vanishing hA with hvanish | hAstrict
  · exact weakPositiveCutReadyNR_v9_holds weakWrapSeed_v9_of_firstStep
      bpos_aneg_tailCornerResidueV9_of_firstStepInteriorZero
      hA hposA hnrA hB hside hangle ihdim hvanish
  · by_cases hnd : deficitCount A B = 0
    · exact congruence_step hAstrict hB hside hangle hnd
    · have hpos : 0 < deficitCount A B := Nat.pos_of_ne_zero hnd
      obtain ⟨k, hkdef⟩ := exists_deficit_of_pos hpos
      exact open_step_wbs_nr_v12 hSub hn ihdim hAstrict hB hside hangle ihdef k hkdef

theorem mainPlusNR_at_level_v12
    (hSub : SubarmIHContra)
    {n : ℕ} (hn : 2 ≤ n)
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m) : MainPlusNR n := by
  intro A B hA hposA hnrA hB hside hangle
  let hstep := szOpeningStepPlusNR_v12 hSub
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

theorem mainPlusNR_all_v12
    (hSub : SubarmIHContra) :
    ∀ n : ℕ, 2 ≤ n → MainPlusNR n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn A B hA hposA hnrA hB hside hangle
    have ihdim : ∀ m : ℕ, m < n → MainPlusNR m := by
      intro m hm
      rcases Nat.lt_or_ge m 2 with h2 | h2
      · exact mainPlusNR_of_lt_two h2
      · exact IH m hm h2
    exact mainPlusNR_at_level_v12 hSub hn ihdim
      A B hA hposA hnrA hB hside hangle

/-- Chapter-13 strict-arm monotonicity, with the cross-piece collision residue replaced by the
genuine subarm-induction residue `SubarmIHContra`. -/
theorem spherical_arm_mono_final_ch13_v12
    (hSub : SubarmIHContra) :
    SphericalArmMonotone := by
  intro n hn A B hA hB hside hangle
  exact (mainPlusNR_all_v12 hSub n hn) A B
    (strictConvexSphArm_toWeak hA) (strictConvexSphArm_positiveJoints hA)
    (strictConvex_noNonadjacentRepeat hA) hB hside hangle

/-! ## Guards. -/

#print axioms supportStuckWBS_endpoint_dispatch_at_level_nr_v12
#print axioms mainPlusNR_all_v12
#print axioms spherical_arm_mono_final_ch13_v12

end ProofsInTheBook.ZinanFFCT111
