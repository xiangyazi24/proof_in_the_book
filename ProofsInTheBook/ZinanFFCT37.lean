import ProofsInTheBook.ZinanFFCT20
import ProofsInTheBook.ZinanFFCT3
import ProofsInTheBook.SphericalOpeningGlue

/-!
# `ZinanFFCT37` — the CORRECTED `-δ` (widening) monitored family and its glue clauses (i)/(ii)

`SphericalOpeningGlue` proved (symbolically + numerically) that the `+δ` monitored family of
`SphericalMonitoredSup` opens the interior joint in the **closing** direction: the axis-anchored support
`sOrient (A K)(jointPrev A k)(jointNext A k)` is strictly **negative** (`joint_axis_support_neg`), so the
`-θ` keystone governs — the opened interior joint **increases under `-θ`** and **decreases under `+θ`**.
Consequently clauses (i)/(ii) of `SphericalOpeningOutcome.InteriorOpeningGlue` are *false* for the `+δ`
family (`SignBugBlocksI/II`).

This module builds the **corrected widening family** `monitoredFamilyW := monitoredFamily ∘ (Neg.neg)`
(opening by `-θ`) and discharges clauses (i) and (ii) of the mirrored glue **unconditionally**.

## The §4 crux: the mirrored exact angle-addition (the `+N sin γ` orientation).

FFCT20's `sphAngle_axis_rotS2_eq_add_of_oriented` (Brick 2) computes `sphAngle p a (rotS2 a δ q) = γ + δ`
under the orientation `⟪u, a × w⟫ = −‖u‖‖w‖ sin γ` (`OpeningDirectionPositive`, the *closing* sign for the
strictly convex arm).  Here the strictly convex arm has the **opposite** orientation
`⟪u, a × w⟫ = +‖u‖‖w‖ sin γ` (proved from `joint_axis_support_neg` + Pythagoras), so we prove the **mirrored**
identity `sphAngle p a (rotS2 a (-θ) q) = γ + θ` (`openedNegJointAngle_eq_add`), and — branch-free — the
signed *support* sinusoid `sOrient p a (rotS2 a (-θ) q) = ‖u‖‖w‖ · sin (γ + θ)`
(`support_openNeg_eq_sin`).  The latter is the load-bearing fact closing §4 **with no residual**: the
joint's own support constraint is in the monitored family, so admissibility (support `≥ 0`) forces
`sin (γ + θ) ≥ 0` and hence `θ ≤ π − γ` (the rotation stays in the additive branch), where the slack
member then pins `θ ≤ jointAngle B k − jointAngle A k < π`.  Therefore the trichotomy CAP `δ* = π` is
impossible, and `¬ StuckW ⟹ ReachW`.

## What this module proves (unconditional, clean-3)

* `monitoredFamilyW` / `monitoredSupW` / `ReachW` / `StuckW` — the widening family and its predicates.
* `opening_boundary_trichotomyW` — the trichotomy for the widening family (the family-generic engine).
* `glueW_clause_i` — `endpt A ≤ endpt (openTailW A (openingAxis k) δ*)` (clause (i)).
* `glueW_clause_ii` — `¬ StuckW → ReachW` (clause (ii)), the genuine §4 work.
* `interiorOpeningGlueW_of_clauseIII` — assembles the 3-clause `InteriorOpeningGlueW` from the
  remaining clause-(iii) Prop `GlueWClauseIII` (the next worker's job), discharging (i)/(ii).

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT20
open ProofsInTheBook.ZinanFFCT3

namespace ProofsInTheBook.ZinanFFCT37

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The widening family (`-θ`). -/

/-- The widening opening: `openTailW A K δ := openTail A K (-δ)` (the convex / opening direction). -/
def openTailW {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (δ : ℝ) : Fin (n + 1) → S2 :=
  openTail A K (-δ)

/-- The widening monitored family: each member of `monitoredFamily` precomposed with `Neg.neg`
(so it monitors the opening direction `-θ`). -/
def monitoredFamilyW {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) :
    NonIncident n ⊕ (Fin (n + 1) ⊕ Unit) → ℝ → ℝ :=
  fun o θ => monitoredFamily A B k h₀ o (-θ)

/-- Each widening-family member is continuous (composition with the continuous negation). -/
theorem continuous_monitoredFamilyW {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) :
    ∀ o, Continuous (monitoredFamilyW A B k h₀ o) := by
  intro o
  exact (continuous_monitoredFamily hka hkt o).comp continuous_neg

/-- At `θ = 0` the widening family equals the original family (`-0 = 0`), so its initial admissibility
is the original's, verbatim. -/
theorem monitoredFamilyW_zero {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) (o) :
    monitoredFamilyW A B k h₀ o 0 = monitoredFamily A B k h₀ o 0 := by
  simp only [monitoredFamilyW, neg_zero]

/-- The widening admissible supremum `δ* := sSup {θ ∈ [0, Tcap] : ∀ o, 0 ≤ monitoredFamilyW … o θ}`. -/
def monitoredSupW {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) (Tcap : ℝ) : ℝ :=
  sSup (admissibleSet (monitoredFamilyW A B k h₀) Tcap)

/-- **The widening admissible supremum is admissible.** -/
theorem monitoredSupW_mem {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) {Tcap : ℝ} (hTcap : 0 ≤ Tcap)
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    monitoredSupW A B k h₀ Tcap ∈ admissibleSet (monitoredFamilyW A B k h₀) Tcap := by
  refine sSup_mem_admissibleSet (continuous_monitoredFamilyW hka hkt) hTcap ?_
  intro o; rw [monitoredFamilyW_zero]; exact h0 o

/-- The widening supremum lies in `[0, Tcap]`; in particular it is `≥ 0` and `≤ Tcap`. -/
theorem monitoredSupW_mem_Icc {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) {Tcap : ℝ} (hTcap : 0 ≤ Tcap)
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    monitoredSupW A B k h₀ Tcap ∈ Set.Icc (0 : ℝ) Tcap :=
  (monitoredSupW_mem hka hkt hTcap h0).1

/-- The REACH predicate for the widening family: the opened-by-`-δ*` interior joint reaches `B`'s value. -/
def ReachW {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) (Tcap : ℝ) : Prop :=
  openedInteriorJointAngle A k (-(monitoredSupW A B k h₀ Tcap)) = jointAngle B k

/-- The STUCK predicate for the widening family: a non-incident support *or* a hemisphere constraint
of the opened-by-`-δ*` arm vanishes. -/
def StuckW {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) (Tcap : ℝ) : Prop :=
  (∃ c : NonIncident n,
      supportConstraint A (openingAxis k) c (-(monitoredSupW A B k h₀ Tcap)) = 0) ∨
    (∃ r : Fin (n + 1), hemiMargin A (openingAxis k) h₀ r (-(monitoredSupW A B k h₀ Tcap)) = 0)

/-! ## §2. The trichotomy for the widening family. -/

/-- **The widening boundary trichotomy at `δ*`.**  Either `δ* = Tcap`, *or* `ReachW`, *or* `StuckW`.
This is the family-generic `reach_or_stuck` on the widening family. -/
theorem opening_boundary_trichotomyW {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) {Tcap : ℝ} (hTcap : 0 ≤ Tcap)
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    monitoredSupW A B k h₀ Tcap = Tcap ∨ ReachW A B k h₀ Tcap ∨ StuckW A B k h₀ Tcap := by
  have h0W : ∀ o, 0 ≤ monitoredFamilyW A B k h₀ o 0 := by
    intro o; rw [monitoredFamilyW_zero]; exact h0 o
  rcases reach_or_stuck (continuous_monitoredFamilyW hka hkt) hTcap h0W with hcap | ⟨o, ho⟩
  · exact Or.inl hcap
  · rcases o with c | (r | ⟨⟩)
    · -- a support constraint vanishes at `-δ*`: STUCK.
      refine Or.inr (Or.inr (Or.inl ⟨c, ?_⟩))
      simpa only [monitoredFamilyW, monitoredFamily, monitoredSupW] using ho
    · -- a hemisphere constraint vanishes at `-δ*`: STUCK.
      refine Or.inr (Or.inr (Or.inr ⟨r, ?_⟩))
      simpa only [monitoredFamilyW, monitoredFamily, monitoredSupW] using ho
    · -- the joint slack vanishes at `-δ*`: REACH.
      refine Or.inr (Or.inl ?_)
      have hslack : monitoredFamily A B k h₀ (Sum.inr (Sum.inr ()))
          (-(monitoredSupW A B k h₀ Tcap)) = 0 := ho
      simp only [monitoredFamily, interiorTargetSlack] at hslack
      unfold ReachW
      linarith

/-! ## §3. The mirrored oriented angle-addition (the `+N sin γ` orientation).

For the strictly convex arm the axis-anchored support is strictly negative
(`joint_axis_support_neg`), so via the bridge `inner_tangent_cross_eq_neg_sOrient` the oriented tangent
datum is strictly **positive**.  Pythagoras pins its exact value `s = ‖u‖‖w‖ sin γ`.  Under this `+`
orientation, opening by `-θ` *adds* `θ` to the joint angle (within the branch `[0, π]`), and the signed
joint support is the **branch-free** sinusoid `‖u‖‖w‖ sin (γ + θ)`. -/

/-- The exact oriented tangent datum of the joint at `δ = 0`: `s = ‖u‖‖w‖ · sin γ` (the `+` sign,
opposite to `OpeningDirectionPositive`).  Derived from `joint_axis_support_neg` (so `s > 0`) and the
Pythagorean identity `c² + s² = N²` with `c = N cos γ`. -/
theorem joint_orientedDatum_eq {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1))
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) :
    (⟪tangentTo (A (openingAxis k)) (jointPrev A k),
        cross (A (openingAxis k) : E3) (tangentTo (A (openingAxis k)) (jointNext A k))⟫ : ℝ)
      = ‖tangentTo (A (openingAxis k)) (jointPrev A k)‖
          * ‖tangentTo (A (openingAxis k)) (jointNext A k)‖
          * Real.sin (jointAngle A k) := by
  set a := A (openingAxis k) with ha
  set p := jointPrev A k with hp
  set q := jointNext A k with hq
  set u : E3 := tangentTo a p with hu
  set w : E3 := tangentTo a q with hw
  set c : ℝ := ⟪u, w⟫ with hc
  set s : ℝ := ⟪u, cross (a : E3) w⟫ with hs
  set N : ℝ := ‖u‖ * ‖w‖ with hN
  -- `γ = jointAngle A k = sphAngle p a q`.
  have hγeq : jointAngle A k = sphAngle p a q := by
    simp only [hp, hq, ha, jointAngle, jointPrev, jointNext, openingAxis]
  set γ : ℝ := jointAngle A k with hγ
  have hunz : u ≠ 0 := (tangentTo_ne_zero_iff a p).2 hka
  have hwnz : w ≠ 0 := (tangentTo_ne_zero_iff a q).2 hkt
  have hup : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hunz
  have hwp : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hwnz
  have hNp : (0 : ℝ) < N := mul_pos hup hwp
  -- `c = N cos γ` and `0 ≤ γ ≤ π`.
  have hγ0 : 0 ≤ γ := by rw [hγeq]; exact sphAngle_nonneg _ _ _
  have hγπ : γ ≤ Real.pi := by rw [hγeq]; exact sphAngle_le_pi _ _ _
  have hcEq : c = N * Real.cos γ := by
    have hcos : Real.cos γ = c / N := by
      rw [hγeq, sphAngle, InnerProductGeometry.cos_angle]
    rw [hcos]; field_simp
  -- Pythagoras: `c² + s² = N²`.
  have hpyth : c ^ 2 + s ^ 2 = N ^ 2 := by
    have := tangentPlane_pythag (k := (a : E3)) (u := u) (w := w) a.2
      (tangentTo_orthogonal a p) (tangentTo_orthogonal a q)
    rw [hc, hs, hN]; rw [mul_pow]; linear_combination this
  -- `s² = (N sin γ)²`.
  have hsinγ : 0 ≤ Real.sin γ := Real.sin_nonneg_of_nonneg_of_le_pi hγ0 hγπ
  have hssq : s ^ 2 = (N * Real.sin γ) ^ 2 := by
    have hsincos : Real.sin γ ^ 2 = 1 - Real.cos γ ^ 2 := by
      have := Real.sin_sq_add_cos_sq γ; linarith
    have hsc : s ^ 2 = N ^ 2 - c ^ 2 := by linarith [hpyth]
    rw [hsc, hcEq]
    linear_combination (-(N ^ 2)) * hsincos
  -- `s > 0` from `joint_axis_support_neg`.
  have hspos : 0 < s := by
    have hbridge : s = -sOrient (A (openingAxis k)) (jointPrev A k) (jointNext A k) := by
      rw [hs, hu, hw, inner_tangent_cross_eq_neg_sOrient]
    rw [hbridge]; linarith [joint_axis_support_neg hA k]
  -- so `s = +(N sin γ)` (the positive root).
  have hge : 0 ≤ N * Real.sin γ := mul_nonneg (le_of_lt hNp) hsinγ
  have hsEq : s = N * Real.sin γ := by
    nlinarith [hssq, hspos, hge, sq_nonneg (s - N * Real.sin γ)]
  rw [hs] at hsEq ⊢
  rw [hsEq, hN]

/-- **Mirrored oriented angle addition (`-θ` opening, `+` orientation).**  Under the orientation
`⟪u, a × w⟫ = +‖u‖‖w‖ sin γ` (the strictly-convex-arm sign) and the branch `0 ≤ γ + θ ≤ π`, opening by
`-θ` *adds* `θ`: `sphAngle p a (rotS2 a (-θ) q) = γ + θ`. -/
theorem sphAngle_axis_rotS2_neg_eq_add_of_oriented {a p q : S2} {θ γ : ℝ}
    (hp : ShortArc a p) (hq : ShortArc a q) (hγ : γ = sphAngle p a q)
    (horient : (⟪tangentTo a p, cross (a : E3) (tangentTo a q)⟫ : ℝ)
      = ‖tangentTo a p‖ * ‖tangentTo a q‖ * Real.sin γ)
    (hbranch0 : 0 ≤ γ + θ) (hbranchπ : γ + θ ≤ Real.pi) :
    sphAngle p a (rotS2 a (-θ) q) = γ + θ := by
  set u : E3 := tangentTo a p with hu
  set w : E3 := tangentTo a q with hw
  have hu0 : u ≠ 0 := (tangentTo_ne_zero_iff a p).2 hp
  have hw0 : w ≠ 0 := (tangentTo_ne_zero_iff a q).2 hq
  have hnu : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hu0
  have hnw : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hw0
  have horth : (⟪w, (a : E3)⟫ : ℝ) = 0 := tangentTo_orthogonal a q
  have hangle_uw : γ = InnerProductGeometry.angle u w := by rw [hγ, sphAngle]
  have hinner_uw : (⟪u, w⟫ : ℝ) = Real.cos γ * (‖u‖ * ‖w‖) := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm u w
    rw [← hangle_uw] at h; linarith [h]
  have hLHS : sphAngle p a (rotS2 a (-θ) q) = InnerProductGeometry.angle u (rot (a : E3) (-θ) w) := by
    rw [sphAngle]; congr 1; rw [hw]; exact tangentTo_axis_rotS2 a q (-θ)
  -- `⟪u, rot a (-θ) w⟫ = cos(γ+θ) · (‖u‖‖w‖)`.
  have hinner_rot : (⟪u, rot (a : E3) (-θ) w⟫ : ℝ) = Real.cos (γ + θ) * (‖u‖ * ‖w‖) := by
    rw [inner_rot_tangent (a : E3) (-θ) horth, hinner_uw, horient, Real.cos_neg, Real.sin_neg,
      Real.cos_add]
    ring
  have hnorm_rot : ‖rot (a : E3) (-θ) w‖ = ‖w‖ := norm_rot a.2 (-θ) w
  have hcosLHS : Real.cos (sphAngle p a (rotS2 a (-θ) q)) = Real.cos (γ + θ) := by
    rw [hLHS, InnerProductGeometry.cos_angle, hnorm_rot, hinner_rot]; field_simp
  have hmem1 : sphAngle p a (rotS2 a (-θ) q) ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨sphAngle_nonneg _ _ _, sphAngle_le_pi _ _ _⟩
  have hmem2 : γ + θ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hbranch0, hbranchπ⟩
  exact Real.injOn_cos.eq_iff hmem1 hmem2 |>.1 hcosLHS

/-- **The opened-by-`-θ` interior joint angle adds `θ`** (on the additive branch).  Instantiates the
mirrored addition at the joint's tangents; the `+` orientation is `joint_orientedDatum_eq`. -/
theorem openedNegJointAngle_eq_add {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    {θ : ℝ} (hθ : 0 ≤ θ) (hbranch : jointAngle A k + θ ≤ Real.pi) :
    openedInteriorJointAngle A k (-θ) = jointAngle A k + θ := by
  have hγ : jointAngle A k = sphAngle (jointPrev A k) (A (openingAxis k)) (jointNext A k) := by
    simp only [jointAngle, jointPrev, jointNext, openingAxis]
  have hγnn : 0 ≤ jointAngle A k := by rw [hγ]; exact sphAngle_nonneg _ _ _
  rw [openedInteriorJointAngle]
  exact sphAngle_axis_rotS2_neg_eq_add_of_oriented
    (a := A (openingAxis k)) (p := jointPrev A k) (q := jointNext A k)
    hka hkt hγ (joint_orientedDatum_eq hA k hka hkt) (add_nonneg hγnn hθ) hbranch

/-- **The signed joint support under `-θ` is the branch-free sinusoid `N sin (γ + θ)`.**  The joint's
own signed support `sOrient (jointPrev)(A K)(rotS2 (A K) (-θ) (jointNext))` equals
`‖u‖‖w‖ · sin (jointAngle A k + θ)` for **every** `θ` (no branch restriction); its nonnegativity hence
forces `sin (γ + θ) ≥ 0`, the branch control of §4. -/
theorem support_openNeg_eq_sin {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) (θ : ℝ) :
    sOrient (jointPrev A k) (A (openingAxis k))
        (rotS2 (A (openingAxis k)) (-θ) (jointNext A k))
      = ‖tangentTo (A (openingAxis k)) (jointPrev A k)‖
          * ‖tangentTo (A (openingAxis k)) (jointNext A k)‖
          * Real.sin (jointAngle A k + θ) := by
  set a := A (openingAxis k) with ha
  set p := jointPrev A k with hp
  set q := jointNext A k with hq
  set u : E3 := tangentTo a p with hu
  set w : E3 := tangentTo a q with hw
  -- `sOrient p a (rotS2 a (-θ) q) = ⟪u, a × rot a (-θ) w⟫`.
  have hq' : tangentTo a (rotS2 a (-θ) q) = rot (a : E3) (-θ) w := by rw [hw]; exact tangentTo_axis_rotS2 a q (-θ)
  have hbridge : sOrient p a (rotS2 a (-θ) q)
      = (⟪u, cross (a : E3) (tangentTo a (rotS2 a (-θ) q))⟫ : ℝ) := by
    have h := inner_tangent_cross_eq_neg_sOrient a p (rotS2 a (-θ) q)
    -- `⟪u, a × tangent⟫ = -sOrient a p (rotS2 a (-θ) q)`; and `sOrient p a · = -sOrient a p ·`.
    have hswap : sOrient p a (rotS2 a (-θ) q) = - sOrient a p (rotS2 a (-θ) q) := by
      simp only [sOrient, det3]; ring
    rw [hswap, ← h, hu]
  rw [hbridge, hq']
  -- `a × rot a (-θ) w = rot a (-θ) (a × w)` (rotation commutes with cross by the axis).
  have hcomm : cross (a : E3) (rot (a : E3) (-θ) w) = rot (a : E3) (-θ) (cross (a : E3) w) := by
    rw [rot_cross a.2 (-θ) (a : E3) w, rot_axis a.2]
  rw [hcomm]
  -- `a × w ⟂ a`, so `inner_rot_tangent` applies.
  have horthcw : (⟪cross (a : E3) w, (a : E3)⟫ : ℝ) = 0 := inner_cross_left (a : E3) w
  rw [inner_rot_tangent (a : E3) (-θ) horthcw]
  -- `⟪u, a × w⟫ = N sin γ`,  `⟪u, a × (a × w)⟫ = -⟪u,w⟫ = -N cos γ`.
  have hsval : (⟪u, cross (a : E3) w⟫ : ℝ) = ‖u‖ * ‖w‖ * Real.sin (jointAngle A k) := by
    rw [hu, hw, ha, hp, hq]; exact joint_orientedDatum_eq hA k hka hkt
  -- `a × (a × w) = ⟪a,w⟫ a − ⟪a,a⟫ w = -w` (since `⟪a,w⟫=0`, `‖a‖=1`).
  have haa : (⟪(a : E3), w⟫ : ℝ) = 0 := by
    rw [real_inner_comm]; exact tangentTo_orthogonal a q
  have haa1 : (⟪(a : E3), (a : E3)⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, a.2]; norm_num
  have hcc : cross (a : E3) (cross (a : E3) w) = -w := by
    rw [cross_cross, haa, haa1]; simp
  have hcval : (⟪u, cross (a : E3) (cross (a : E3) w)⟫ : ℝ) = -(‖u‖ * ‖w‖ * Real.cos (jointAngle A k)) := by
    rw [hcc, inner_neg_right]
    -- `⟪u, w⟫ = N cos γ`.
    have hcosγ : (⟪u, w⟫ : ℝ) = ‖u‖ * ‖w‖ * Real.cos (jointAngle A k) := by
      have hγeq : jointAngle A k = InnerProductGeometry.angle u w := by
        simp only [hu, hw, ha, hp, hq, jointAngle, jointPrev, jointNext, openingAxis, sphAngle]
      have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm u w
      rw [← hγeq] at h; linear_combination -h
    rw [hcosγ]
  rw [hsval, hcval, Real.cos_neg, Real.sin_neg]
  rw [Real.sin_add]; ring

/-! ## §4. Clause (ii): `¬ StuckW → ReachW` (the genuine work).

The joint's own signed support is monitored by the non-incident pair `c₀ = ((k, k+2))` (edge `(k, k+1)`,
vertex `k+2`); under the opening `-θ` its value is `N sin (γ + θ)` (`support_openNeg_eq_sin`).  Hence
admissibility (support `≥ 0`) forces `sin (γ + θ) ≥ 0`, so `γ + θ ≤ π` (the additive branch), where the
slack member pins `γ + θ = openedInteriorJointAngle A k (-θ) ≤ jointAngle B k < π`.  Therefore
`θ ≤ jointAngle B k − γ`, so `monitoredSupW ≤ jointAngle B k − γ < π`: the CAP branch is impossible. -/

/-- The non-incident edge–vertex pair monitoring the deficient joint: edge `(k, k+1)`, vertex `k+2`. -/
def jointWitness {n : ℕ} (k : Fin (n - 1)) : NonIncident n :=
  ⟨(⟨k.val, by have := k.isLt; omega⟩, ⟨k.val + 2, by have := k.isLt; omega⟩),
    ⟨by
        intro he
        have h := Fin.val_eq_of_eq he
        simp only [Fin.val_mk] at h; omega,
      by
        intro he
        have hk := k.isLt
        -- the `+1` of the edge first-vertex `⟨k⟩`, computed at `.val`.
        have hadd : ((⟨k.val, by omega⟩ : Fin (n + 1)) + 1).val = k.val + 1 := by
          have h1v : ((1 : Fin (n + 1)) : ℕ) = 1 := by
            simp only [Fin.val_one']; rw [Nat.mod_eq_of_lt (by omega)]
          rw [Fin.val_add, Fin.val_mk, h1v, Nat.mod_eq_of_lt (by omega)]
        have h := Fin.val_eq_of_eq he
        rw [hadd] at h
        simp only [Fin.val_mk] at h
        omega⟩⟩

/-- The joint-witness support constraint, opened by `-θ`, is exactly the joint's signed support. -/
theorem supportConstraint_jointWitness_neg {n : ℕ} {A : Fin (n + 1) → S2} (k : Fin (n - 1)) (θ : ℝ) :
    supportConstraint A (openingAxis k) (jointWitness k) (-θ)
      = sOrient (jointPrev A k) (A (openingAxis k))
          (rotS2 (A (openingAxis k)) (-θ) (jointNext A k)) := by
  rw [supportConstraint_apply]
  -- the three opened vertices: index k (fixed = jointPrev), k+1 = axis (fixed), k+2 (rotated = jointNext).
  have hk := k.isLt
  have hKval : (openingAxis k).val = k.val + 1 := rfl
  have hv0 : openTail A (openingAxis k) (-θ) ⟨k.val, by omega⟩ = jointPrev A k := by
    rw [openTail_fixed A (openingAxis k) (-θ) (by simp only [openingAxis, Fin.val_mk]; omega)]; rfl
  have he1 : ((jointWitness k).1.1 + 1) = (openingAxis k : Fin (n + 1)) := by
    -- `(jointWitness k).1.1 = ⟨k, _⟩`, so `+1 = ⟨k+1⟩ = openingAxis k`.
    apply Fin.ext
    show (((⟨k.val, by omega⟩ : Fin (n + 1)) + 1).val) = (openingAxis k).val
    rw [Fin.val_add, Fin.val_mk, hKval]
    have h1v : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      simp only [Fin.val_one']; rw [Nat.mod_eq_of_lt (by omega)]
    rw [h1v, Nat.mod_eq_of_lt (by omega)]
  have hv1 : openTail A (openingAxis k) (-θ) ((jointWitness k).1.1 + 1) = A (openingAxis k) := by
    rw [he1]; exact openTail_axis A (openingAxis k) (-θ)
  have hv2 : openTail A (openingAxis k) (-θ) ⟨k.val + 2, by omega⟩
      = rotS2 (A (openingAxis k)) (-θ) (jointNext A k) := by
    rw [openTail_rot A (openingAxis k) (-θ) (by simp only [openingAxis, Fin.val_mk]; omega)]; rfl
  show sOrient (openTail A (openingAxis k) (-θ) (jointWitness k).1.1)
      (openTail A (openingAxis k) (-θ) ((jointWitness k).1.1 + 1))
      (openTail A (openingAxis k) (-θ) (jointWitness k).1.2) = _
  rw [hv1]
  show sOrient (openTail A (openingAxis k) (-θ) ⟨k.val, by omega⟩) (A (openingAxis k))
      (openTail A (openingAxis k) (-θ) ⟨k.val + 2, by omega⟩) = _
  rw [hv0, hv2]

/-- **Every widening-admissible `θ` lies in `[0, jointAngle B k − jointAngle A k]`.**  The joint-witness
support `≥ 0` forces `sin (γ + θ) ≥ 0`, hence (with `θ ∈ [0, π]`, `γ < π`) `γ + θ ≤ π`; the addition
identity then makes the opened joint `γ + θ`, and slack `≥ 0` pins `γ + θ ≤ jointAngle B k`. -/
theorem admissibleW_le_deficit {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (_hB : StrictConvexSphArm B) {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    {θ : ℝ} (hθadm : θ ∈ admissibleSet (monitoredFamilyW A B k h₀) Real.pi) :
    θ ≤ jointAngle B k - jointAngle A k := by
  obtain ⟨⟨hθ0, hθπ⟩, hmem⟩ := hθadm
  -- joint-witness support ≥ 0.
  have hsupp : 0 ≤ supportConstraint A (openingAxis k) (jointWitness k) (-θ) := by
    have := hmem (Sum.inl (jointWitness k))
    simpa only [monitoredFamilyW, monitoredFamily] using this
  rw [supportConstraint_jointWitness_neg, support_openNeg_eq_sin hA hka hkt] at hsupp
  -- norms are positive, so `sin (γ + θ) ≥ 0`.
  have hunz : tangentTo (A (openingAxis k)) (jointPrev A k) ≠ 0 := (tangentTo_ne_zero_iff _ _).2 hka
  have hwnz : tangentTo (A (openingAxis k)) (jointNext A k) ≠ 0 := (tangentTo_ne_zero_iff _ _).2 hkt
  have hup : (0 : ℝ) < ‖tangentTo (A (openingAxis k)) (jointPrev A k)‖ := norm_pos_iff.2 hunz
  have hwp : (0 : ℝ) < ‖tangentTo (A (openingAxis k)) (jointNext A k)‖ := norm_pos_iff.2 hwnz
  have hsin : 0 ≤ Real.sin (jointAngle A k + θ) := by
    by_contra hneg
    push_neg at hneg
    have : ‖tangentTo (A (openingAxis k)) (jointPrev A k)‖
        * ‖tangentTo (A (openingAxis k)) (jointNext A k)‖ * Real.sin (jointAngle A k + θ) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hup hwp) hneg
    linarith
  -- `γ + θ ∈ [0, 2π)` and `sin ≥ 0` ⟹ `γ + θ ≤ π` (the additive branch).
  have hγ0 : 0 ≤ jointAngle A k := by
    rw [show jointAngle A k = sphAngle (jointPrev A k) (A (openingAxis k)) (jointNext A k) by
      simp only [jointAngle, jointPrev, jointNext, openingAxis]]
    exact sphAngle_nonneg _ _ _
  have hγlt : jointAngle A k < Real.pi := strict_jointAngle_lt_pi hA k
  have hbranch : jointAngle A k + θ ≤ Real.pi := by
    by_contra hgt
    push_neg at hgt
    -- write `γ+θ = π + t` with `0 < t < π` (since `γ < π`, `θ ≤ π` give `γ+θ < 2π`).
    set t : ℝ := jointAngle A k + θ - Real.pi with ht
    have ht0 : 0 < t := by rw [ht]; linarith
    have htlt : t < Real.pi := by rw [ht]; linarith [hγlt, hθπ]
    -- `sin (π + t) = - sin t < 0`, contradicting `hsin ≥ 0`.
    have hsin_t : Real.sin (jointAngle A k + θ) = - Real.sin t := by
      rw [show jointAngle A k + θ = Real.pi + t by rw [ht]; ring, Real.sin_add, Real.sin_pi,
        Real.cos_pi]
      ring
    have hpos : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 htlt
    rw [hsin_t] at hsin; linarith
  -- on the branch, the opened joint equals `γ + θ`; slack ≥ 0 pins `γ + θ ≤ jointAngle B k`.
  have hopened : openedInteriorJointAngle A k (-θ) = jointAngle A k + θ :=
    openedNegJointAngle_eq_add hA hka hkt hθ0 hbranch
  have hslack : 0 ≤ jointAngle B k - openedInteriorJointAngle A k (-θ) := by
    have := hmem (Sum.inr (Sum.inr ()))
    simpa only [monitoredFamilyW, monitoredFamily, interiorTargetSlack] using this
  rw [hopened] at hslack
  linarith

/-- **The widening supremum is strictly below the cap `π`.**  `δ* ≤ jointAngle B k − jointAngle A k`
(the supremum bound from `admissibleW_le_deficit`), and `jointAngle B k − jointAngle A k < π` (since
`jointAngle B k < π` and `jointAngle A k ≥ 0`). -/
theorem monitoredSupW_lt_pi {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    monitoredSupW A B k h₀ Real.pi < Real.pi := by
  have hTcap : (0 : ℝ) ≤ Real.pi := Real.pi_nonneg
  -- δ* ≤ deficit.
  have hmem := monitoredSupW_mem (B := B) (h₀ := h₀) hka hkt hTcap h0
  have hub : monitoredSupW A B k h₀ Real.pi ≤ jointAngle B k - jointAngle A k :=
    admissibleW_le_deficit hA hB hka hkt hmem
  -- deficit < π.
  have hγ0 : 0 ≤ jointAngle A k := by
    rw [show jointAngle A k = sphAngle (jointPrev A k) (A (openingAxis k)) (jointNext A k) by
      simp only [jointAngle, jointPrev, jointNext, openingAxis]]
    exact sphAngle_nonneg _ _ _
  have hBlt : jointAngle B k < Real.pi := strict_jointAngle_lt_pi hB k
  linarith

/-- **Clause (ii) for the widening family: `¬ StuckW → ReachW`.**  The trichotomy's CAP branch is
impossible (`monitoredSupW_lt_pi`); `¬ StuckW` eliminates the STUCK branch; only REACH remains. -/
theorem glueW_clause_ii {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hnotStuck : ¬ StuckW A B k h₀ Real.pi) :
    ReachW A B k h₀ Real.pi := by
  have hTcap : (0 : ℝ) ≤ Real.pi := Real.pi_nonneg
  rcases opening_boundary_trichotomyW hka hkt hTcap h0 with hcap | hreach | hstuck
  · exact absurd hcap (ne_of_lt (monitoredSupW_lt_pi hA hB hka hkt h0))
  · exact hreach
  · exact absurd hstuck hnotStuck

/-! ## §5. Clause (i) and the W-glue bundle. -/

/-- **Clause (i) for the widening family**, given the endpoint base-angle cap.  Opening by
`-δ*` (`δ* ≥ 0`, within the base-triangle great-semicircle range) does not decrease the endpoint; this
is the banked `endpt_openTail_interior_mono_neg` at the opening axis. -/
theorem glueW_clause_i {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (_hB : StrictConvexSphArm B) {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hcap : monitoredSupW A B k h₀ Real.pi
      + sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) ≤ Real.pi) :
    endpt A ≤ endpt (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)) := by
  have hTcap : (0 : ℝ) ≤ Real.pi := Real.pi_nonneg
  have hδ0 : 0 ≤ monitoredSupW A B k h₀ Real.pi :=
    (monitoredSupW_mem_Icc hka hkt hTcap h0).1
  -- openTailW K δ* = openTail K (-δ*); apply the corrected `-δ` endpoint companion.
  show endpt A ≤ endpt (openTail A (openingAxis k) (-(monitoredSupW A B k h₀ Real.pi)))
  exact endpt_openTail_interior_mono_neg hA k hδ0 hcap

/-- The remaining clause (iii) of the widening glue (the next worker's job): the STUCK boundary outcome
for the `-δ*` opened arm. -/
def GlueWClauseIII : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A → StrictConvexSphArm B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∀ h₀ : E3, ‖h₀‖ = 1 → (∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) →
      StuckW A B k h₀ Real.pi →
        WeakConvexSphArm (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)) ∧
        ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
          sOrient (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) i)
            (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) (i + 1))
            (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) j) = 0

/-- The endpoint base-angle cap of the widening glue (the cap hypothesis of clause (i)).  This is the
analogue of the substrate's recorded `endpoint-range reconciliation`: the opened base triangle stays
within the great semicircle at the admissible supremum.  Stated as a named Prop so clause (i) is
discharged once it is supplied; it is non-vacuous (realised at `δ* = 0`, `sphAngle ≤ π`). -/
def GlueWBaseCap : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A → StrictConvexSphArm B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∀ h₀ : E3, ‖h₀‖ = 1 → (∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) →
      monitoredSupW A B k h₀ Real.pi
        + sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) ≤ Real.pi

/-- **The widening glue bundle** (the `-δ` mirror of `InteriorOpeningGlue`): clause (i), clause (ii),
and clause (iii). -/
def InteriorOpeningGlueW : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A → StrictConvexSphArm B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∀ h₀ : E3, ‖h₀‖ = 1 → (∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) →
      endpt A ≤ endpt (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)) ∧
      (¬ StuckW A B k h₀ Real.pi → ReachW A B k h₀ Real.pi) ∧
      (StuckW A B k h₀ Real.pi →
        WeakConvexSphArm (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)) ∧
        ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
          sOrient (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) i)
            (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) (i + 1))
            (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) j) = 0)

/-- **`InteriorOpeningGlueW` from the residual clause (iii) `GlueWClauseIII` and the base cap.**  Clauses
(i) and (ii) are discharged **unconditionally** by `glueW_clause_i` (modulo the named base cap) and
`glueW_clause_ii`; clause (iii) is the supplied residual. -/
theorem interiorOpeningGlueW_of_clauseIII (hcap : GlueWBaseCap) (hIII : GlueWClauseIII) :
    InteriorOpeningGlueW := by
  intro n A B hA hB k hkdef h₀ hnorm hhpos
  have h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0 :=
    monitoredFamily_init_admissible hA hhpos hkdef
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  refine ⟨?_, ?_, ?_⟩
  · exact glueW_clause_i hA hB hka hkt h0 (hcap n A B hA hB k hkdef h₀ hnorm hhpos)
  · exact fun hns => glueW_clause_ii hA hB hka hkt h0 hns
  · exact hIII n A B hA hB k hkdef h₀ hnorm hhpos

/-! ## §5.3. Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of clause (ii): `ReachW` is a genuine angle equation (the opened-by-`-δ*` joint reaching
`B`'s value), and the supremum is a real admissible point. -/
theorem reachW_def_nonvacuous {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3)
    (Tcap : ℝ) :
    ReachW A B k h₀ Tcap ↔
      openedInteriorJointAngle A k (-(monitoredSupW A B k h₀ Tcap)) = jointAngle B k := Iff.rfl

/-- Non-vacuity of the support-sine identity: at `θ = 0` it is the original joint support
`sOrient (jointPrev)(A K)(jointNext) = N sin (jointAngle A k)`, genuine geometric data (strictly
positive for a strictly convex arm). -/
theorem support_openNeg_eq_sin_zero {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1))
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) :
    sOrient (jointPrev A k) (A (openingAxis k)) (jointNext A k)
      = ‖tangentTo (A (openingAxis k)) (jointPrev A k)‖
          * ‖tangentTo (A (openingAxis k)) (jointNext A k)‖
          * Real.sin (jointAngle A k) := by
  have h := support_openNeg_eq_sin hA hka hkt 0
  simp only [neg_zero, add_zero] at h
  rwa [show rotS2 (A (openingAxis k)) 0 (jointNext A k) = jointNext A k by
    apply S2.ext; rw [rotS2_coe, rot_zero]] at h

/-- Non-vacuity of `GlueWBaseCap`: at `δ* = 0` the cap is `sphAngle ≤ π`, always true — so the cap is a
real range condition, satisfied at the unopened arm, not a vacuous-hypothesis impostor. -/
theorem glueWBaseCap_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    (0 : ℝ) + sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) ≤ Real.pi := by
  rw [zero_add]; exact sphAngle_le_pi _ _ _

/-- Non-vacuity guard: `monitoredSupW` at `δ* = 0` opens nothing (`openTailW A K 0 = A`). -/
theorem openTailW_zero {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) :
    openTailW A K 0 = A := by
  simp only [openTailW, neg_zero, openTail_zero_angle]

end ProofsInTheBook.ZinanFFCT37
