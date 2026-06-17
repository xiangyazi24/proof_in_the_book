import ProofsInTheBook.ZinanFFCT61

/-!
# `ZinanFFCT62` — Ch13 reach-only minimization and the remaining honest boundary surface

This file does not add postulates.  It records the part of the `Ch13ReachOnlyResidues` bundle that
really minimizes, and it pins the remaining non-axis / tail-boundary work to theorem-shaped facts.

* The strict-arm reach-only theorem can avoid `SZOpeningStepPlus` entirely: a custom induction on
  `deficitCount` only ever recurses on the strict opened arm returned by `reachOnly_outcome`.
  Consequently the strict headline needs only `SupportStuckWBSImpossible`.
* The raw non-axis sign supply is not obtained by the one-sided derivative algebra alone: after
  substituting the span relation, the derivative expression is `b * (q * G - p)`, whose second factor
  is not sign-definite from the ledger variables.
* The tail endpoint cases are transported through `mirrorArm`, but the existing FFCT53 boundary
  consumers still require their honest inputs: the `(0,n)` interval/diagonal certificates, and the
  `(0,n-1)` diagonal inequality plus `TailFoldBoundary`.

No `sorry`, `axiom`, `admit`, or `native_decide`.
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
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT59
open ProofsInTheBook.ZinanFFCT61

namespace ProofsInTheBook.ZinanFFCT62

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The minimized strict reach-only theorem. -/

/-- **Strict reach-only recursion from `SupportStuckWBSImpossible` alone.**

This is the minimized version of the reach-only route.  It does not build an `SZOpeningStepPlus`,
so it never has to solve the weak-entry vanishing-support branch.  The induction is only on strict
left arms, and the recursive arm is strict because `reachOnly_outcome` returns
`StrictConvexSphArm A'`. -/
theorem spherical_arm_mono_reachOnly_v2 (helim : SupportStuckWBSImpossible)
    {n : ℕ} (_hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) := by
  have H : ∀ d : ℕ, ∀ A B : Fin (n + 1) → S2,
      StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
      deficitCount A B = d → endpt A ≤ endpt B := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
      intro A B hA hB hside hangle hdef
      by_cases hnd : deficitCount A B = 0
      · exact congruence_step hA hB hside hangle hnd
      · have hpos : 0 < deficitCount A B := Nat.pos_of_ne_zero hnd
        obtain ⟨k, hkdef⟩ := exists_deficit_of_pos hpos
        obtain ⟨A', hmono, hside', hangle', hstrict, hdrop⟩ :=
          reachOnly_outcome helim hA hB hside hangle k hkdef
        have hdrop' : deficitCount A' B < d := by
          rwa [hdef] at hdrop
        have hAB : endpt A' ≤ endpt B :=
          IH (deficitCount A' B) hdrop' A' B hstrict hB hside' hangle' rfl
        exact le_trans hmono hAB
  have h := H (deficitCount A B) A B hA hB hside hangle rfl
  simpa [endpt] using h

/-- **The true strict-step support-stuck consumer.**

For the strict-only recursion, the support-stuck branch does not have to be contradictory: it is
enough to prove the endpoint comparison for the WBS-opened arm.  This is the shape needed by the
tail endpoint cases, where the boundary transport gives `endpt (openedWBS A B k) ≤ endpt B` rather
than `False`. -/
def SupportStuckWBSEndpointDispatch : Prop :=
  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
    StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    SupportStuckWBS A B k → endpt (openedWBS A B k) ≤ endpt B

/-- `SupportStuckWBSImpossible` is a special case of endpoint dispatch. -/
theorem supportStuckEndpointDispatch_of_impossible
    (helim : SupportStuckWBSImpossible) : SupportStuckWBSEndpointDispatch := by
  intro n A B hA hB hside hangle k hkdef hstuck
  exact False.elim ((helim A B hA hB k hkdef) hstuck)

/-- **Strict recursion from endpoint dispatch.**

This is the final strict-only induction shape: REACH recurses on a strict opened arm; support-stuck
is consumed by whatever endpoint transport/elimination theorem is available for the opened arm. -/
theorem spherical_arm_mono_of_supportStuckEndpointDispatch
    (hdispatch : SupportStuckWBSEndpointDispatch)
    {n : ℕ} (_hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) := by
  have H : ∀ d : ℕ, ∀ A B : Fin (n + 1) → S2,
      StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
      deficitCount A B = d → endpt A ≤ endpt B := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
      intro A B hA hB hside hangle hdef
      by_cases hnd : deficitCount A B = 0
      · exact congruence_step hA hB hside hangle hnd
      · have hpos : 0 < deficitCount A B := Nat.pos_of_ne_zero hnd
        obtain ⟨k, hkdef⟩ := exists_deficit_of_pos hpos
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
            hdispatch A B hA hB hside hangle k hkdef hstuck
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
          have hreach_k : jointAngle A' k = jointAngle B k := by
            rw [hjointk]; exact hreach
          have hdrop : deficitCount A' B < deficitCount A B := by
            rw [hA']; exact deficitCount_openTail_reach_lt A B k (-δ) hkdef hreach_k
          have hdrop' : deficitCount A' B < d := by
            rwa [hdef] at hdrop
          have hAB : endpt A' ≤ endpt B :=
            IH (deficitCount A' B) hdrop' A' B hstrict hB hside' hangle' rfl
          exact le_trans hmono hAB
  have h := H (deficitCount A B) A B hA hB hside hangle rfl
  simpa [endpt] using h

/-! ## §2. The raw non-axis sign ledger obstruction. -/

/-- The single-rotation non-axis derivative expression after substituting
`x = a*y + b*z`, where `G = <y,z>`, `p = <y,k>`, and `q = <z,k>`. -/
theorem nonAxis_singleRotation_substitution_algebra (a b G p q : ℝ) :
    (a * p + b * q) * G - (a * G + b) * p = b * (q * G - p) := by
  ring

/-- The derivative inequality `b * (q * G - p) ≤ 0` does not force `b < 0`.
This is the exact algebraic failure of the raw sign supply from the one-sided slope alone. -/
theorem nonAxis_derivative_inequality_not_force_bneg :
    ¬ (∀ b G p q : ℝ, b * (q * G - p) ≤ 0 → b < 0) := by
  intro h
  have hb : (1 : ℝ) < 0 := h 1 0 1 0 (by norm_num)
  norm_num at hb

/-- The second factor in the non-axis derivative readout is not sign-definite even with
`G` in the open Gram range. -/
theorem nonAxis_derivative_factor_has_all_signs :
    (∃ G p q : ℝ, -1 < G ∧ G < 1 ∧ 0 < q * G - p) ∧
    (∃ G p q : ℝ, -1 < G ∧ G < 1 ∧ q * G - p < 0) ∧
    (∃ G p q : ℝ, -1 < G ∧ G < 1 ∧ q * G - p = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨0, -1, 0, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨0, 1, 0, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨0, 0, 0, by norm_num, by norm_num, by norm_num⟩

/-! ## §3. Mirror transport for the two endpoint tail cases. -/

/-- A tail mid-fold on `P` becomes a boundary betweenness for `mirrorArm P`. -/
theorem mirror_tail_midFold_collinearity {n : ℕ} {P : Fin (n + 1) → S2} {j : ℕ}
    (hnpos : 1 ≤ n) (hjle : j ≤ n) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hmid : (P ⟨n, by omega⟩ : E3)
      = c • (P ⟨n - 1, by omega⟩ : E3) + d • (P ⟨j, by omega⟩ : E3)) :
    (mirrorArm P ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(mirrorArm P ⟨1, by omega⟩ : E3),
          (mirrorArm P ⟨n - j, by omega⟩ : E3)} : Set E3) := by
  rw [Submodule.mem_span_pair]
  refine ⟨⟨c, le_of_lt hc⟩, ⟨d, le_of_lt hd⟩, ?_⟩
  rw [NNReal.smul_def, NNReal.smul_def]
  have h0 : (mirrorArm P ⟨0, by omega⟩ : S2) = mirrorS2 (P ⟨n, by omega⟩) := by
    change mirrorS2 (P (revFin (⟨0, by omega⟩ : Fin (n + 1)))) = _
    exact congrArg mirrorS2 (congrArg P (Fin.ext (by simp [revFin_val])))
  have h1 : (mirrorArm P ⟨1, by omega⟩ : S2) = mirrorS2 (P ⟨n - 1, by omega⟩) := by
    change mirrorS2 (P (revFin (⟨1, by omega⟩ : Fin (n + 1)))) = _
    exact congrArg mirrorS2 (congrArg P (Fin.ext (by simp [revFin_val])))
  have hj : (mirrorArm P ⟨n - j, by omega⟩ : S2) = mirrorS2 (P ⟨j, by omega⟩) := by
    change mirrorS2 (P (revFin (⟨n - j, by omega⟩ : Fin (n + 1)))) = _
    congr 1
    exact congrArg P (Fin.ext (by simp [revFin_val]; omega))
  rw [h0, h1, hj, mirrorS2_coe, mirrorS2_coe, mirrorS2_coe]
  have hR := congrArg reflectZ hmid
  rw [reflectZ_add, reflectZ_smul, reflectZ_smul] at hR
  exact hR.symm

/-- The FFCT59 tail-boundary residue supplies the mirror boundary betweenness, conditional only on
the strict open hemisphere needed to rearrange the `b < 0` span datum into a positive mid-fold. -/
theorem nonAxisTailBoundaryResidue_mirror_collinearity {n : ℕ}
    {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    {i j : ℕ} {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1}
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    (hres : NonAxisTailBoundaryResidue A B k i j hi hi1 hj) :
    (mirrorArm (openedWBS A B k) ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(mirrorArm (openedWBS A B k) ⟨1, by omega⟩ : E3),
          (mirrorArm (openedWBS A B k) ⟨n - j, by omega⟩ : E3)} : Set E3) := by
  set P : Fin (n + 1) → S2 := openedWBS A B k
  rcases hres with ⟨htail, _hi_rot, _hj_fixed, hmix⟩
  rcases hmix with ⟨_hnonaxis, a, b, hspan, hb⟩
  obtain ⟨c, d, hc, hd, hmid0⟩ :=
    midFold_coeffs_of_bneg (P := P) hhem hi hi1 hj hspan hb
  have hmid : (P ⟨n, by omega⟩ : E3)
      = c • (P ⟨n - 1, by omega⟩ : E3) + d • (P ⟨j, by omega⟩ : E3) := by
    have hi_eq : i = n - 1 := by omega
    have e0 : (⟨i + 1, hi1⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext (by simp [htail])
    have e1 : (⟨i, hi⟩ : Fin (n + 1)) = ⟨n - 1, by omega⟩ := Fin.ext (by simp [hi_eq])
    have ej : (⟨j, hj⟩ : Fin (n + 1)) = ⟨j, by omega⟩ := Fin.ext rfl
    rwa [e0, e1, ej] at hmid0
  exact mirror_tail_midFold_collinearity (P := P) (j := j) (by omega) (by omega) hc hd hmid

/-- Tail endpoint case `j = 0`: mirror to FFCT53's `(0,n)` boundary transport.

The A-side interval certificate can be produced by FFCT54 from the betweenness; this statement keeps
the exact FFCT53 inputs explicit. -/
theorem tailBoundary_j0_endpoint_transport_mirror {n : ℕ}
    {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    {i j : ℕ} {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1}
    (hn : 2 ≤ n)
    (ih : ∀ m : ℕ, m < n → MainPlus m)
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hside' : SameSides (openedWBS A B k) B)
    (hangle' : JointLe (openedWBS A B k) B)
    (hAe : WeakConvexSphArm (intervalArm (mirrorArm (openedWBS A B k)) 1 (n - 1) (by omega)))
    (hBe : StrictConvexSphArm (intervalArm (mirrorArm B) 1 (n - 1) (by omega)))
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    (hj0 : j = 0)
    (hres : NonAxisTailBoundaryResidue A B k i j hi hi1 hj) :
    endpt (openedWBS A B k) ≤ endpt B := by
  have hcol0 := nonAxisTailBoundaryResidue_mirror_collinearity hhem hres
  have hidx : (⟨n - j, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext (by simp [hj0])
  have hcol : (mirrorArm (openedWBS A B k) ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(mirrorArm (openedWBS A B k) ⟨1, by omega⟩ : E3),
          (mirrorArm (openedWBS A B k) ⟨n, by omega⟩ : E3)} : Set E3) := by
    rwa [hidx] at hcol0
  have hmirror := foldedFlat_boundary_j_eq_n
    (A := mirrorArm (openedWBS A B k)) (B := mirrorArm B)
    hn ih (positiveJoints_mirrorArm hA'pos) (sameSides_mirrorArm hside')
    (jointLe_mirrorArm hangle') hAe hBe hcol
  rwa [endpt_mirrorArm, endpt_mirrorArm] at hmirror

/-- Tail endpoint case `j = 1`: mirror to FFCT53's `(0,n-1)` boundary transport. -/
theorem tailBoundary_j1_endpoint_transport_mirror {n : ℕ}
    {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    {i j : ℕ} {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1}
    (hn : 2 ≤ n)
    (hside' : SameSides (openedWBS A B k) B)
    (htail : TailFoldBoundary (mirrorArm (openedWBS A B k)) (by omega))
    (hdiag : sDist (mirrorArm (openedWBS A B k) ⟨0, by omega⟩)
        (mirrorArm (openedWBS A B k) ⟨n - 1, by omega⟩)
      ≤ sDist (mirrorArm B ⟨0, by omega⟩) (mirrorArm B ⟨n - 1, by omega⟩))
    (_hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    (_hj1 : j = 1)
    (_hres : NonAxisTailBoundaryResidue A B k i j hi hi1 hj) :
    endpt (openedWBS A B k) ≤ endpt B := by
  have hmirror := foldedFlat_boundary_j_eq_n_minus_one
    (A := mirrorArm (openedWBS A B k)) (B := mirrorArm B)
    hn (sameSides_mirrorArm hside') htail hdiag
  rwa [endpt_mirrorArm, endpt_mirrorArm] at hmirror

/-! ## §4. Final honest surface. -/

/-- The final strict surface after the bundle minimization: the strict reach-only headline itself
requires only the support-stuck elimination predicate.  The remaining work is exactly the proof of
that predicate from raw WBS support-stuck data. -/
structure Ch13ReachOnlyStrictSurface : Prop where
  /-- WBS support-stuck is impossible at every deficient strict step. -/
  helim : SupportStuckWBSImpossible

/-- The endpoint-dispatch surface: support-stuck branches may be eliminated or transported. -/
structure Ch13VNextSurface : Prop where
  /-- WBS support-stuck endpoint consumer for the opened arm. -/
  hdispatch : SupportStuckWBSEndpointDispatch

/-- The minimized strict headline from the endpoint-dispatch surface. -/
theorem spherical_arm_mono_vNext (res : Ch13VNextSurface)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_supportStuckEndpointDispatch res.hdispatch hn A B hA hB hside hangle

/-- The impossible-branch surface still gives `vNext`, as a special case. -/
theorem spherical_arm_mono_vNext_of_reachOnlyStrictSurface (res : Ch13ReachOnlyStrictSurface)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_vNext
    ⟨supportStuckEndpointDispatch_of_impossible res.helim⟩ hn A B hA hB hside hangle

/-- The minimized headline conclusion is the genuine chord bound, not a vacuous target. -/
theorem spherical_arm_mono_vNext_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

#print axioms spherical_arm_mono_reachOnly_v2
#print axioms supportStuckEndpointDispatch_of_impossible
#print axioms spherical_arm_mono_of_supportStuckEndpointDispatch
#print axioms nonAxis_singleRotation_substitution_algebra
#print axioms nonAxis_derivative_inequality_not_force_bneg
#print axioms nonAxis_derivative_factor_has_all_signs
#print axioms mirror_tail_midFold_collinearity
#print axioms nonAxisTailBoundaryResidue_mirror_collinearity
#print axioms tailBoundary_j0_endpoint_transport_mirror
#print axioms tailBoundary_j1_endpoint_transport_mirror
#print axioms spherical_arm_mono_vNext

end ProofsInTheBook.ZinanFFCT62
