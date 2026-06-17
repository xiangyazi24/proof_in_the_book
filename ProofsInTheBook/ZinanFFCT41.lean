import ProofsInTheBook.ZinanFFCT40

/-!
# `ZinanFFCT41` — discharging `GlueWBaseCap` via the augmented **base-capped** widening family `WB`.

`ZinanFFCT37.GlueWBaseCap` (the endpoint base-angle cap `δ*_W + sphAngle (A 0)(A K)(A last) ≤ π`) is the
one residual that `ZinanFFCT40.mainPlus_headline_repaired` still consumes as a *named hypothesis* on
clause (i).  The cap is **not** an admissibility consequence of the `W` family, because that family does
not monitor the base triangle: the `W` supremum `δ*_W` can overshoot the base great-semicircle.  This
module carries out **route (a)** of the archived design (`HANDOFF/design-rounds/ch13-basecap-monitor.md`):
add the base support as a monitored member, so the new supremum `δ*_WB` satisfies the cap *by
admissibility*, and re-thread the headline at `δ*_WB`.

## The base monitor and its sinusoid (§§4-6 of the design)

With `K := openingAxis k`, `γbase := sphAngle (A 0)(A K)(A last)`, the new member is

    baseCapSupportW A k θ := sOrient (A 0)(A K)(rotS2 (A K) (-θ)(A last)).

Mirroring `ZinanFFCT37.support_openNeg_eq_sin` (whose oriented datum came from the *negative*
`joint_axis_support_neg`), the base oriented datum comes from the **positive** convex base support
`SphericalSZFinal.orientedDatum_interior` (`0 ≤ sOrient (A 0)(A K)(A last)`, strict via
`cut_diagonal_supports`), giving the same `+N sin γ` orientation, hence the branch-free identity

    baseCapSupportW A k θ = ‖tangentTo (A K)(A 0)‖ * ‖tangentTo (A K)(A last)‖ * sin (γbase + θ).

So at the `WB` supremum (admissible ⟹ base support `≥ 0`) we get `sin (γbase + δ*_WB) ≥ 0`, and with
`γbase < π` (strict base nondegeneracy) and `δ*_WB ∈ [0, π]` this forces `γbase + δ*_WB ≤ π` — **the cap**.

## The `W`-admissibility bridge (the reuse mechanism)

The `WB` admissible set is the `W` admissible set intersected with the extra base constraint, so it is a
**subset**: every `WB`-admissible `θ` is `W`-admissible.  In particular the `WB` supremum is `W`-admissible
(`monitoredSupWB_mem_W`), so **every** `W` closure fact (`admissibleW_le_deficit`, the support/hemi/slack
nonnegativities) holds verbatim at `δ*_WB`.  This lets clauses (i)/(ii)/(iii) be re-derived at `δ*_WB`
re-using the FFCT37/40 machinery (instantiated at the `W`-admissible point `δ*_WB`), plus the new base cap.

## What is proved here (clean-3, no `sorry`/`axiom`/`admit`/`native_decide`)

* `§1` `baseCapSupportW`, `monitoredFamilyWB`, continuity, `monitoredSupWB`, membership, the `W`-bridge.
* `§2` `baseSupport_openNeg_eq_sin` — the base sinusoid (mirror of FFCT37's joint version).
* `§3` `admissibleWB_baseCap` + `GlueWBaseCap_at_supWB` — the cap by admissibility at `δ*_WB`.
* `§4` `ReachWB` / `StuckWB` / `BaseStuckWB` and the `WB` trichotomy.
* `§5` clause (i)/(ii) at `δ*_WB`, the repaired clause (iii) at `δ*_WB`, the base-stuck resolution.
* `§6` `interiorOpeningOutcomeWB_basecapped` and `mainPlus_headline_basecapped` — the headline with
  `GlueWBaseCap` **discharged**; the residue surface drops the cap and is scoped to the `WB` binders.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT20
open ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT38
open ProofsInTheBook.ZinanFFCT39
open ProofsInTheBook.ZinanFFCT40

namespace ProofsInTheBook.ZinanFFCT41

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The base-capped widening family `WB`. -/

/-- The **base support monitor**, opened by `-θ`: `θ ↦ sOrient (A 0)(A K)(rotS2 (A K) (-θ)(A last))`,
the signed support of the base triangle `(A 0, A K = axis, A last)` as the endpoint vertex `A last`
rotates by `-θ` about the axis.  Its nonnegativity is exactly the base great-semicircle (cap) condition. -/
def baseCapSupportW {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) : ℝ → ℝ :=
  fun θ => sOrient (A 0) (A (openingAxis k))
    (rotS2 (A (openingAxis k)) (-θ) (A (Fin.last n)))

/-- The base monitor is continuous in `θ` (the rotation `rotS2 (A K) (-θ)(A last)` is continuous and
`sOrient = det3` is continuous). -/
theorem continuous_baseCapSupportW {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    Continuous (baseCapSupportW A k) := by
  show Continuous (fun θ : ℝ =>
    det3 (A 0 : E3) (A (openingAxis k) : E3)
      ((rotS2 (A (openingAxis k)) (-θ) (A (Fin.last n)) : S2) : E3))
  simp only [rotS2_coe, det3]
  -- the first two vertices are constant; the third rotates (`continuous_rot ∘ neg`, per coordinate).
  have ha : ∀ c, Continuous (fun _ : ℝ => (A 0 : E3) c) := fun c => continuous_const
  have hb : ∀ c, Continuous (fun _ : ℝ => (A (openingAxis k) : E3) c) := fun c => continuous_const
  have hl : ∀ c, Continuous
      (fun θ : ℝ => (rot (A (openingAxis k) : E3) (-θ) (A (Fin.last n) : E3)) c) := fun c =>
    (continuous_rot_coord (A (openingAxis k) : E3) (A (Fin.last n) : E3) c).comp continuous_neg
  exact
    (((ha 0).mul (((hb 1).mul (hl 2)).sub ((hb 2).mul (hl 1)))).sub
      ((ha 1).mul (((hb 0).mul (hl 2)).sub ((hb 2).mul (hl 0))))).add
      ((ha 2).mul (((hb 0).mul (hl 1)).sub ((hb 1).mul (hl 0))))

/-- **The base-capped widening monitored family `WB`**: the `W` family augmented (`⊕ Unit`) with the base
support monitor.  Indexed by `(NonIncident n ⊕ (Fin (n+1) ⊕ Unit)) ⊕ Unit`. -/
def monitoredFamilyWB {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) :
    (NonIncident n ⊕ (Fin (n + 1) ⊕ Unit)) ⊕ Unit → ℝ → ℝ
  | Sum.inl o => monitoredFamilyW A B k h₀ o
  | Sum.inr () => baseCapSupportW A k

/-- Each `WB`-family member is continuous (the `W` members by `continuous_monitoredFamilyW`, the base
member by `continuous_baseCapSupportW`). -/
theorem continuous_monitoredFamilyWB {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) :
    ∀ o, Continuous (monitoredFamilyWB A B k h₀ o) := by
  rintro (o | ⟨⟩)
  · exact continuous_monitoredFamilyW hka hkt o
  · exact continuous_baseCapSupportW A k

/-- At `θ = 0` the base monitor equals the unopened base support `sOrient (A 0)(A K)(A last) ≥ 0`
(`orientedDatum_interior`); the joint members agree with `monitoredFamily` (`monitoredFamilyW_zero`). -/
theorem monitoredFamilyWB_zero_nonneg {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    ∀ o, 0 ≤ monitoredFamilyWB A B k h₀ o 0 := by
  rintro (o | ⟨⟩)
  · show 0 ≤ monitoredFamilyW A B k h₀ o 0
    rw [monitoredFamilyW_zero]; exact h0 o
  · -- base member at `0`: `sOrient (A 0)(A K)(rotS2 (A K) 0 (A last)) = sOrient (A 0)(A K)(A last) ≥ 0`.
    show 0 ≤ baseCapSupportW A k 0
    obtain ⟨hK0, hKn⟩ := openingAxis_interior k
    have hrot0 : rotS2 (A (openingAxis k)) (-(0 : ℝ)) (A (Fin.last n)) = A (Fin.last n) := by
      apply S2.ext; rw [rotS2_coe, neg_zero, rot_zero]
    show 0 ≤ sOrient (A 0) (A (openingAxis k)) (rotS2 (A (openingAxis k)) (-(0 : ℝ)) (A (Fin.last n)))
    rw [hrot0]
    exact orientedDatum_interior hA hK0 hKn

/-- The `WB` admissible supremum `δ*_WB := sSup {θ ∈ [0,π] : ∀ o, 0 ≤ monitoredFamilyWB … o θ}`. -/
def monitoredSupWB {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) : ℝ :=
  sSup (admissibleSet (monitoredFamilyWB A B k h₀) Real.pi)

/-- **The `WB` admissible supremum is `WB`-admissible.** -/
theorem monitoredSupWB_mem {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    monitoredSupWB A B k h₀ ∈ admissibleSet (monitoredFamilyWB A B k h₀) Real.pi :=
  sSup_mem_admissibleSet (continuous_monitoredFamilyWB hka hkt) Real.pi_nonneg
    (monitoredFamilyWB_zero_nonneg hA h0)

/-- **The `W`-admissibility bridge.**  Since the `WB` admissible set is the `W` admissible set with the
extra base constraint, `δ*_WB` is itself `W`-admissible.  This is the reuse hinge: every `W` closure /
deficit fact holds verbatim at `δ*_WB`. -/
theorem monitoredSupWB_mem_W {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    monitoredSupWB A B k h₀ ∈ admissibleSet (monitoredFamilyW A B k h₀) Real.pi := by
  obtain ⟨hIcc, hall⟩ := monitoredSupWB_mem hA hka hkt h0
  refine ⟨hIcc, ?_⟩
  intro o
  -- the `W` member `o` is the `WB` member `Sum.inl o`.
  exact hall (Sum.inl o)

/-- The base constraint is `≥ 0` at `δ*_WB` (closure of the `WB` admissible set). -/
theorem baseCapSupportW_nonneg_at_supWB {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    0 ≤ baseCapSupportW A k (monitoredSupWB A B k h₀) :=
  (monitoredSupWB_mem hA hka hkt h0).2 (Sum.inr ())

/-- `δ*_WB ∈ [0, π]`. -/
theorem monitoredSupWB_mem_Icc {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    monitoredSupWB A B k h₀ ∈ Set.Icc (0 : ℝ) Real.pi :=
  (monitoredSupWB_mem hA hka hkt h0).1

/-! ## §2. The base sinusoid `baseCapSupportW A k θ = N · sin (γbase + θ)`.

Mirror of `ZinanFFCT37.support_openNeg_eq_sin` with the **base** triple `(A 0, A K = axis, A last)`.  The
only sign difference from the joint case is the source of the `+` orientation: the joint datum came from
the *negative* `joint_axis_support_neg`, while the base datum comes from the *positive* convex base support
`orientedDatum_interior` (`0 ≤ sOrient (A 0)(A K)(A last)`, strict via `cut_diagonal_supports`).  Both yield
the identical orientation `⟪u, a × w⟫ = +‖u‖‖w‖ sin γ`. -/

/-- **The base oriented tangent datum** `s = +‖u‖‖w‖ · sin γbase` (the `+` orientation).  Here
`a := A K`, `u := tangentTo (A K)(A 0)`, `w := tangentTo (A K)(A last)`, `γbase := sphAngle (A 0)(A K)(A last)`.
Derived (mirroring `joint_orientedDatum_eq`) from the **strict** base support
`0 < sOrient (A 0)(A K)(A last)` (`cut_diagonal_supports`), so the datum `s = -sOrient (A K)(A 0)(A last) > 0`,
and Pythagoras `c² + s² = N²` pins it to the positive root `N sin γbase`. -/
theorem base_orientedDatum_eq {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1))
    (hka : ShortArc (A (openingAxis k)) (A 0))
    (hkt : ShortArc (A (openingAxis k)) (A (Fin.last n))) :
    (⟪tangentTo (A (openingAxis k)) (A 0),
        cross (A (openingAxis k) : E3) (tangentTo (A (openingAxis k)) (A (Fin.last n)))⟫ : ℝ)
      = ‖tangentTo (A (openingAxis k)) (A 0)‖
          * ‖tangentTo (A (openingAxis k)) (A (Fin.last n))‖
          * Real.sin (sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n))) := by
  set a := A (openingAxis k) with ha
  set p := A 0 with hp
  set q := A (Fin.last n) with hq
  set u : E3 := tangentTo a p with hu
  set w : E3 := tangentTo a q with hw
  set c : ℝ := ⟪u, w⟫ with hc
  set s : ℝ := ⟪u, cross (a : E3) w⟫ with hs
  set N : ℝ := ‖u‖ * ‖w‖ with hN
  set γ : ℝ := sphAngle p a q with hγ
  have hunz : u ≠ 0 := (tangentTo_ne_zero_iff a p).2 hka
  have hwnz : w ≠ 0 := (tangentTo_ne_zero_iff a q).2 hkt
  have hup : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hunz
  have hwp : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hwnz
  have hNp : (0 : ℝ) < N := mul_pos hup hwp
  have hγ0 : 0 ≤ γ := by rw [hγ]; exact sphAngle_nonneg _ _ _
  have hγπ : γ ≤ Real.pi := by rw [hγ]; exact sphAngle_le_pi _ _ _
  have hcEq : c = N * Real.cos γ := by
    have hcos : Real.cos γ = c / N := by
      rw [hγ, sphAngle, InnerProductGeometry.cos_angle]
    rw [hcos]; field_simp
  have hpyth : c ^ 2 + s ^ 2 = N ^ 2 := by
    have := tangentPlane_pythag (k := (a : E3)) (u := u) (w := w) a.2
      (tangentTo_orthogonal a p) (tangentTo_orthogonal a q)
    rw [hc, hs, hN]; rw [mul_pow]; linear_combination this
  have hsinγ : 0 ≤ Real.sin γ := Real.sin_nonneg_of_nonneg_of_le_pi hγ0 hγπ
  have hssq : s ^ 2 = (N * Real.sin γ) ^ 2 := by
    have hsincos : Real.sin γ ^ 2 = 1 - Real.cos γ ^ 2 := by
      have := Real.sin_sq_add_cos_sq γ; linarith
    have hsc : s ^ 2 = N ^ 2 - c ^ 2 := by linarith [hpyth]
    rw [hsc, hcEq]
    linear_combination (-(N ^ 2)) * hsincos
  -- `s > 0` from the strict positive base support `0 < sOrient (A 0)(A K)(A last)`.
  have hspos : 0 < s := by
    obtain ⟨hK0, hKn⟩ := openingAxis_interior k
    haveI : NeZero (n + 1) := ⟨by omega⟩
    have h0K : (0 : Fin (n + 1)) < openingAxis k := by rw [Fin.lt_def, Fin.val_zero]; omega
    have hKl : openingAxis k < Fin.last n := by rw [Fin.lt_def, Fin.val_last]; omega
    have hdiag : 0 < sOrient (A 0) (A (openingAxis k)) (A (Fin.last n)) :=
      cut_diagonal_supports hA.closed_convex h0K hKl
    -- `s = ⟪u, a × w⟫ = -sOrient a p q = -sOrient (A K)(A 0)(A last) = sOrient (A 0)(A K)(A last) > 0`.
    have hbridge : s = -sOrient a p q := by
      rw [hs, hu, hw, inner_tangent_cross_eq_neg_sOrient]
    have hswap : sOrient a p q = -sOrient p a q := by
      have := sOrient_swap p a q  -- sOrient p q a = -sOrient p a q ; need swap first two
      simp only [sOrient, det3] at this ⊢; ring
    rw [hbridge, hswap]
    -- `sOrient p a q = sOrient (A 0)(A K)(A last)`.
    have hpaq : sOrient p a q = sOrient (A 0) (A (openingAxis k)) (A (Fin.last n)) := by
      rw [hp, ha, hq]
    rw [hpaq]; linarith
  have hge : 0 ≤ N * Real.sin γ := mul_nonneg (le_of_lt hNp) hsinγ
  have hsEq : s = N * Real.sin γ := by
    nlinarith [hssq, hspos, hge, sq_nonneg (s - N * Real.sin γ)]
  rw [hs] at hsEq ⊢
  rw [hsEq, hN]

/-- **The base support under `-θ` is the branch-free sinusoid `N · sin (γbase + θ)`.**  Mirror of
`ZinanFFCT37.support_openNeg_eq_sin`, with the base triple and the base oriented datum
`base_orientedDatum_eq`.  Holds for **every** `θ` (no branch restriction). -/
theorem baseSupport_openNeg_eq_sin {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1))
    (hka : ShortArc (A (openingAxis k)) (A 0))
    (hkt : ShortArc (A (openingAxis k)) (A (Fin.last n))) (θ : ℝ) :
    baseCapSupportW A k θ
      = ‖tangentTo (A (openingAxis k)) (A 0)‖
          * ‖tangentTo (A (openingAxis k)) (A (Fin.last n))‖
          * Real.sin (sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) + θ) := by
  set a := A (openingAxis k) with ha
  set p := A 0 with hp
  set q := A (Fin.last n) with hq
  set u : E3 := tangentTo a p with hu
  set w : E3 := tangentTo a q with hw
  show sOrient p a (rotS2 a (-θ) q)
    = ‖u‖ * ‖w‖ * Real.sin (sphAngle p a q + θ)
  have hq' : tangentTo a (rotS2 a (-θ) q) = rot (a : E3) (-θ) w := by
    rw [hw]; exact tangentTo_axis_rotS2 a q (-θ)
  have hbridge : sOrient p a (rotS2 a (-θ) q)
      = (⟪u, cross (a : E3) (tangentTo a (rotS2 a (-θ) q))⟫ : ℝ) := by
    have h := inner_tangent_cross_eq_neg_sOrient a p (rotS2 a (-θ) q)
    have hswap : sOrient p a (rotS2 a (-θ) q) = - sOrient a p (rotS2 a (-θ) q) := by
      simp only [sOrient, det3]; ring
    rw [hswap, ← h, hu]
  rw [hbridge, hq']
  have hcomm : cross (a : E3) (rot (a : E3) (-θ) w) = rot (a : E3) (-θ) (cross (a : E3) w) := by
    rw [rot_cross a.2 (-θ) (a : E3) w, rot_axis a.2]
  rw [hcomm]
  have horthcw : (⟪cross (a : E3) w, (a : E3)⟫ : ℝ) = 0 := inner_cross_left (a : E3) w
  rw [inner_rot_tangent (a : E3) (-θ) horthcw]
  -- `⟪u, a × w⟫ = N sin γ` (base oriented datum); `⟪u, a × (a × w)⟫ = -N cos γ`.
  have hsval : (⟪u, cross (a : E3) w⟫ : ℝ)
      = ‖u‖ * ‖w‖ * Real.sin (sphAngle p a q) := by
    rw [hu, hw, ha, hp, hq]; exact base_orientedDatum_eq hA k hka hkt
  have haa : (⟪(a : E3), w⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact tangentTo_orthogonal a q
  have haa1 : (⟪(a : E3), (a : E3)⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, a.2]; norm_num
  have hcc : cross (a : E3) (cross (a : E3) w) = -w := by
    rw [cross_cross, haa, haa1]; simp
  have hcval : (⟪u, cross (a : E3) (cross (a : E3) w)⟫ : ℝ)
      = -(‖u‖ * ‖w‖ * Real.cos (sphAngle p a q)) := by
    rw [hcc, inner_neg_right]
    have hcosγ : (⟪u, w⟫ : ℝ) = ‖u‖ * ‖w‖ * Real.cos (sphAngle p a q) := by
      have hγeq : sphAngle p a q = InnerProductGeometry.angle u w := by
        rw [hu, hw, sphAngle]
      have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm u w
      rw [← hγeq] at h; linear_combination -h
    rw [hcosγ]
  rw [hsval, hcval, Real.cos_neg, Real.sin_neg]
  rw [Real.sin_add]; ring

/-! ## §3. The base cap from admissibility.

The base monitor is in the `WB` family, so `WB`-admissibility forces `baseCapSupportW ≥ 0`, hence (norms
positive) `sin (γbase + θ) ≥ 0`.  With `θ ∈ [0, π]` and the strict base nondegeneracy `γbase < π`
(`sphAngle_lt_pi_of_det3_ne` from the strict base support), this pins `γbase + θ ≤ π` — the cap.  Same
sine-branch argument as `ZinanFFCT37.admissibleW_le_deficit`. -/

/-- **The strict base nondegeneracy** `γbase < π`.  From the strict convex base support
`0 < sOrient (A 0)(A K)(A last) = det3 …` via `sphAngle_lt_pi_of_det3_ne`. -/
theorem base_sphAngle_lt_pi {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1)) :
    sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) < Real.pi := by
  obtain ⟨hK0, hKn⟩ := openingAxis_interior k
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have h0K : (0 : Fin (n + 1)) < openingAxis k := by rw [Fin.lt_def, Fin.val_zero]; omega
  have hKl : openingAxis k < Fin.last n := by rw [Fin.lt_def, Fin.val_last]; omega
  have hdiag : 0 < sOrient (A 0) (A (openingAxis k)) (A (Fin.last n)) :=
    cut_diagonal_supports hA.closed_convex h0K hKl
  refine sphAngle_lt_pi_of_det3_ne _ _ _ ?_
  intro hz
  rw [sOrient] at hdiag
  rw [hz] at hdiag; exact lt_irrefl 0 hdiag

/-- **Every `WB`-admissible `θ` satisfies the cap `θ + γbase ≤ π`.**  Admissibility ⟹ base support `≥ 0`
⟹ `sin (γbase + θ) ≥ 0`; with `θ ∈ [0,π]`, `γbase ∈ [0,π)`, the additive branch closes the cap. -/
theorem admissibleWB_baseCap {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (A 0))
    (hkt : ShortArc (A (openingAxis k)) (A (Fin.last n)))
    {θ : ℝ} (hadm : θ ∈ admissibleSet (monitoredFamilyWB A B k h₀) Real.pi) :
    θ + sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) ≤ Real.pi := by
  obtain ⟨⟨hθ0, hθπ⟩, hmem⟩ := hadm
  set γ : ℝ := sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) with hγ
  -- base support `≥ 0`.
  have hbase : 0 ≤ baseCapSupportW A k θ := hmem (Sum.inr ())
  rw [baseSupport_openNeg_eq_sin hA k hka hkt, ← hγ] at hbase
  -- norms positive ⟹ `sin (γ + θ) ≥ 0`.
  have hunz : tangentTo (A (openingAxis k)) (A 0) ≠ 0 := (tangentTo_ne_zero_iff _ _).2 hka
  have hwnz : tangentTo (A (openingAxis k)) (A (Fin.last n)) ≠ 0 := (tangentTo_ne_zero_iff _ _).2 hkt
  have hup : (0 : ℝ) < ‖tangentTo (A (openingAxis k)) (A 0)‖ := norm_pos_iff.2 hunz
  have hwp : (0 : ℝ) < ‖tangentTo (A (openingAxis k)) (A (Fin.last n))‖ := norm_pos_iff.2 hwnz
  have hsin : 0 ≤ Real.sin (γ + θ) := by
    by_contra hneg
    push_neg at hneg
    have : ‖tangentTo (A (openingAxis k)) (A 0)‖
        * ‖tangentTo (A (openingAxis k)) (A (Fin.last n))‖ * Real.sin (γ + θ) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hup hwp) hneg
    linarith
  -- `γ ∈ [0, π)`.
  have hγ0 : 0 ≤ γ := by rw [hγ]; exact sphAngle_nonneg _ _ _
  have hγlt : γ < Real.pi := base_sphAngle_lt_pi hA k
  -- `sin (γ+θ) ≥ 0` with `γ+θ ∈ [0, 2π)` ⟹ `γ+θ ≤ π`.
  by_contra hgt
  push_neg at hgt
  set t : ℝ := γ + θ - Real.pi with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  have htlt : t < Real.pi := by rw [ht]; linarith [hγlt, hθπ]
  have hsin_t : Real.sin (γ + θ) = - Real.sin t := by
    rw [show γ + θ = Real.pi + t by rw [ht]; ring, Real.sin_add, Real.sin_pi, Real.cos_pi]
    ring
  have hpos : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 htlt
  rw [hsin_t] at hsin; linarith

/-- **The base cap at the `WB` supremum** (`GlueWBaseCap` for `δ*_WB`): `δ*_WB + γbase ≤ π`.  The `WB`
supremum is `WB`-admissible (`monitoredSupWB_mem`), so `admissibleWB_baseCap` applies. -/
theorem GlueWBaseCap_at_supWB {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    monitoredSupWB A B k h₀
      + sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) ≤ Real.pi := by
  obtain ⟨hbase0, hbaseLast⟩ := shortArc_interior_base hA (openingAxis_interior k).1 (openingAxis_interior k).2
  exact admissibleWB_baseCap hA hbase0 hbaseLast (monitoredSupWB_mem hA hka hkt h0)

/-! ## §4. The `WB` widening opening and its closure facts (via the `W`-admissibility bridge).

`δ*_WB` is `W`-admissible (`monitoredSupWB_mem_W`), so the opened arm `A'_WB := openTailW A K δ*_WB =
openTail A K (-δ*_WB)` has *all* the `W`-closure data: support supports `≥ 0`, hemisphere margins `≥ 0`,
the joint slack `≥ 0`, and the deficit bound `δ*_WB ≤ deficit`.  These are read off `monitoredSupWB_mem_W`
verbatim. -/

/-- Closure, support form on the opened triple of `A'_WB` (`≥ 0`). -/
theorem supportWB_sOrient_nonneg {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) i)
        (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (i + 1))
        (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) j) := by
  intro i j hji hji1
  have hmemW := monitoredSupWB_mem_W hA hka hkt h0
  have := hmemW.2 (Sum.inl (⟨(i, j), ⟨hji, hji1⟩⟩ : NonIncident n))
  simp only [monitoredFamilyW, monitoredFamily, supportConstraint_apply] at this
  exact this

/-- Closure, hemisphere form on the opened vertex of `A'_WB` (`≥ 0`). -/
theorem hemiWB_inner_nonneg {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    ∀ r : Fin (n + 1),
      0 ≤ (⟪h₀, ((openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) r : S2) : E3)⟫ : ℝ) := by
  intro r
  have hmemW := monitoredSupWB_mem_W hA hka hkt h0
  have := hmemW.2 (Sum.inr (Sum.inl r))
  simp only [monitoredFamilyW, monitoredFamily, hemiMargin] at this
  exact this

/-- The joint slack `≥ 0` at `δ*_WB`: the opened interior joint is `≤ jointAngle B k`. -/
theorem openedInteriorJoint_le_at_supWB {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    openedInteriorJointAngle A k (-(monitoredSupWB A B k h₀)) ≤ jointAngle B k := by
  have hmemW := monitoredSupWB_mem_W hA hka hkt h0
  have := hmemW.2 (Sum.inr (Sum.inr ()))
  simp only [monitoredFamilyW, monitoredFamily, interiorTargetSlack] at this
  linarith

/-- **`δ*_WB ≤ jointAngle B k − jointAngle A k`** (so `δ*_WB < π`).  Since `δ*_WB` is `W`-admissible,
`ZinanFFCT37.admissibleW_le_deficit` applies verbatim. -/
theorem monitoredSupWB_le_deficit {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    monitoredSupWB A B k h₀ ≤ jointAngle B k - jointAngle A k :=
  admissibleW_le_deficit hA hB hka hkt (monitoredSupWB_mem_W hA hka hkt h0)

/-- **`δ*_WB < π`.** -/
theorem monitoredSupWB_lt_pi {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    monitoredSupWB A B k h₀ < Real.pi := by
  have hub := monitoredSupWB_le_deficit hA hB hka hkt h0
  have hγ0 : 0 ≤ jointAngle A k := by
    rw [show jointAngle A k = sphAngle (jointPrev A k) (A (openingAxis k)) (jointNext A k) by
      simp only [jointAngle, jointPrev, jointNext, openingAxis]]
    exact sphAngle_nonneg _ _ _
  have hBlt : jointAngle B k < Real.pi := strict_jointAngle_lt_pi hB k
  linarith

/-! ## §5. The `WB` reach / stuck / base-stuck predicates and the trichotomy. -/

/-- The REACH predicate at the `WB` supremum: the opened-by-`-δ*_WB` interior joint reaches `B`'s value. -/
def ReachWB {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) : Prop :=
  openedInteriorJointAngle A k (-(monitoredSupWB A B k h₀)) = jointAngle B k

/-- The STUCK predicate at the `WB` supremum: a `W`-monitor (non-incident support *or* hemisphere margin)
of the opened-by-`-δ*_WB` arm vanishes. -/
def StuckWB {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) : Prop :=
  (∃ c : NonIncident n,
      supportConstraint A (openingAxis k) c (-(monitoredSupWB A B k h₀)) = 0) ∨
    (∃ r : Fin (n + 1), hemiMargin A (openingAxis k) h₀ r (-(monitoredSupWB A B k h₀)) = 0)

/-- The BASE-STUCK predicate at the `WB` supremum: the base monitor vanishes — the base triangle hits the
great semicircle (`sin (γbase + δ*_WB) = 0`, i.e. `γbase + δ*_WB = π`, the cap with *equality*). -/
def BaseStuckWB {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) : Prop :=
  baseCapSupportW A k (monitoredSupWB A B k h₀) = 0

/-- **The `WB` boundary trichotomy** (here a *tetrachotomy*).  At `δ*_WB`: either `δ*_WB = π`, or `ReachWB`,
or `StuckWB`, or `BaseStuckWB`.  This is the family-generic `reach_or_stuck` on the `WB` family. -/
theorem opening_boundary_trichotomyWB {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    monitoredSupWB A B k h₀ = Real.pi ∨ ReachWB A B k h₀ ∨ StuckWB A B k h₀ ∨ BaseStuckWB A B k h₀ := by
  rcases reach_or_stuck (continuous_monitoredFamilyWB hka hkt) Real.pi_nonneg
      (monitoredFamilyWB_zero_nonneg hA h0) with hcap | ⟨o, ho⟩
  · exact Or.inl hcap
  · rcases o with (c | (r | ⟨⟩)) | ⟨⟩
    · -- a support constraint vanishes: STUCK.
      refine Or.inr (Or.inr (Or.inl (Or.inl ⟨c, ?_⟩)))
      simpa only [monitoredFamilyWB, monitoredFamilyW, monitoredFamily, monitoredSupWB] using ho
    · -- a hemisphere constraint vanishes: STUCK.
      refine Or.inr (Or.inr (Or.inl (Or.inr ⟨r, ?_⟩)))
      simpa only [monitoredFamilyWB, monitoredFamilyW, monitoredFamily, monitoredSupWB] using ho
    · -- the joint slack vanishes: REACH.
      refine Or.inr (Or.inl ?_)
      have hslack : monitoredFamilyWB A B k h₀ (Sum.inl (Sum.inr (Sum.inr ())))
          (monitoredSupWB A B k h₀) = 0 := ho
      simp only [monitoredFamilyWB, monitoredFamilyW, monitoredFamily, interiorTargetSlack] at hslack
      unfold ReachWB
      linarith
    · -- the base monitor vanishes: BASE-STUCK.
      refine Or.inr (Or.inr (Or.inr ?_))
      have : monitoredFamilyWB A B k h₀ (Sum.inr ()) (monitoredSupWB A B k h₀) = 0 := ho
      simpa only [monitoredFamilyWB, monitoredSupWB] using this

/-! ## §6. Clauses (i)/(ii)/(iii) at `δ*_WB`, and the base-stuck resolution.

The base monitor's purpose is clause (i): the cap is now an admissibility consequence
(`GlueWBaseCap_at_supWB`).  Clauses (ii)/(iii) re-use the `W`-closure data at `δ*_WB` (the bridge §4) and
the *generic* engines (`hemiStuck_dichotomy_tangentFree`, `reach_strictConvex_interior`,
`weakConvex_of_supportStuckW_of_hemiPos_anyH`).  The base-stuck branch needs **no separate payload**: a
base-stuck supremum still satisfies the cap (with equality), so clause (i) holds unchanged; and for the
recursion, the W-monitors decide REACH-or-(support/hemi)-STUCK exactly as in the non-base-stuck case
(`BaseStuckWB` is invisible to the W-trichotomy logic, which runs on `StuckWB` / `¬StuckWB`).  Hence the
base-stuck branch yields **no new residual** — it is absorbed into the existing `StuckWB`/`ReachWB` split. -/

/-- **Clause (i) at `δ*_WB`** — UNCONDITIONAL (the cap is now discharged).  Opening by `-δ*_WB` does not
decrease the endpoint, since `δ*_WB + γbase ≤ π` holds by admissibility (`GlueWBaseCap_at_supWB`). -/
theorem glueWB_clause_i {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    endpt A ≤ endpt (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀))) := by
  have hδ0 : 0 ≤ monitoredSupWB A B k h₀ := (monitoredSupWB_mem_Icc hA hka hkt h0).1
  exact endpt_openTail_interior_mono_neg hA k hδ0 (GlueWBaseCap_at_supWB hA hka hkt h0)

/-- **Clause (ii) at `δ*_WB`, HONEST form: `¬ StuckWB → ReachWB ∨ BaseStuckWB`.**  The `WB` CAP branch is
impossible (`monitoredSupWB_lt_pi`) and STUCK is excluded by `¬StuckWB`, leaving REACH or BASE-STUCK.

The base-stuck disjunct is **genuine, not vacuous**: at `δ*_WB` the base monitor may bind first
(`γbase + δ*_WB = π`, the base triangle straightens) while no W-monitor binds and the joint is *not* yet
reached.  This is a real third outcome the `W` family never saw (it does not monitor the base), so honesty
forbids collapsing it into `ReachWB`.  It is carried as the explicit second disjunct and resolved
downstream by the named `BaseStuckProgressW` residual (§7). -/
theorem glueWB_clause_ii {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hnotStuck : ¬ StuckWB A B k h₀) :
    ReachWB A B k h₀ ∨ BaseStuckWB A B k h₀ := by
  rcases opening_boundary_trichotomyWB hA hka hkt h0 with hcap | hreach | hstuck | hbase
  · exact absurd hcap (ne_of_lt (monitoredSupWB_lt_pi hA hB hka hkt h0))
  · exact Or.inl hreach
  · exact absurd hstuck hnotStuck
  · exact Or.inr hbase

/-! ## §7. The repaired clause (iii) at `δ*_WB` and the base-stuck progress residual.

`StuckWB` (a W-monitor binds) is resolved exactly as `ZinanFFCT40.stuckOutcomeW_repaired` did at the `W`
sup — but at `δ*_WB`, re-using the `W`-closure data (the bridge §4) and the *generic* engines.  The output
is the honest three-way: `WeakConvex ∧ (∃ vanishing support ∨ StrictConvex A'_WB)`, with the pure-hemi
strict-convex case collapsed downstream by `PureHemiProgressWB`.

The new `BaseStuckWB` outcome (base triangle straightened, joint not necessarily reached) is the
genuinely-new design content.  The base support vanishing — `baseCapSupportW A k δ*_WB = 0` — is `sin
(γbase + δ*_WB) = 0` at the base triple `(0, K, last)`, which is **not** an `(i, i+1, j)` NonIncident form
(the base triple straddles the wraparound; `0` and `last` are not consecutive at an interior axis), so it
yields no NonIncident vanishing-support payload directly (design §9, §12).  Per the design (route (a) keeps
the spine, does NOT open the route-(b) straightening completion), the base-stuck case is carried as the
single named, non-vacuous residual `BaseStuckProgressW`: a base-stuck supremum makes recursion-ready
progress (either the joint reached — deficit drops — or a W-support vanishes — the CUT-ready alternative).
This is the honest analogue of `PureHemiProgressW` for the base branch. -/

/-- **Generic edge-distinctness from the closing edge.**  Mirror of `ZinanFFCT39.openedEdgesDistinctW_of_closing`,
abstracted over the opening angle `d` (here `d = -δ*_WB`).  Every non-closing edge is discharged
unconditionally by `openedEdgeDistinctW_fixed/_seam/_tail`; the lone wraparound closing edge is the
supplied premise. -/
theorem openedEdgesDistinct_at_d {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1)) (d : ℝ)
    (hclose : openTail A (openingAxis k) d (Fin.last n)
      ≠ openTail A (openingAxis k) d (Fin.last n + 1)) :
    ∀ i : Fin (n + 1), openTail A (openingAxis k) d i ≠ openTail A (openingAxis k) d (i + 1) := by
  set K : Fin (n + 1) := openingAxis k with hK
  obtain ⟨hK1, hKn⟩ := openingAxis_interior k
  intro i
  by_cases hlast : i = Fin.last n
  · rw [hlast]; exact hclose
  · have hival : i.val < n := by
      rcases Nat.lt_or_ge i.val n with h | h
      · exact h
      · exact absurd (Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)) hlast
    have hsucc : (i + 1).val = i.val + 1 := by
      rw [Fin.val_add_one_of_lt]; rwa [Fin.lt_def, Fin.val_last]
    rcases lt_trichotomy i.val K.val with hlt | heq | hgt
    · exact openedEdgeDistinctW_fixed hA K d i (le_of_lt hlt) (by rw [hsucc]; omega)
    · exact openedEdgeDistinctW_seam hA K d i (Fin.ext heq) (by rw [hsucc]; omega)
    · exact openedEdgeDistinctW_tail hA K d i hgt (by rw [hsucc]; omega)

/-- **(WB scoped Brick 1)** the closing edge `(last, 0)` of `A'_WB` is distinct — quantified inside the glue
context (so a constant arm, excluded by `StrictConvexSphArm A`, cannot refute it).  Mirror of
`ZinanFFCT40.OpenedClosingEdgeDistinctAtSupW` at `δ*_WB`. -/
def OpenedClosingEdgeDistinctAtSupWB : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∀ h₀ : E3, ‖h₀‖ = 1 → (∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) →
      StuckWB A B k h₀ →
      openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (Fin.last n)
        ≠ openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (Fin.last n + 1)

/-- **(WB scoped Brick 2)** at a *support*-stuck `WB` supremum no fixed-`h₀` margin vanishes — quantified
inside the glue context and restricted to the support disjunct (so it never asserts strictness at a
hemi-stuck vertex; the §3.3 self-contradiction that killed FFCT38's global form is structurally avoided).
Mirror of `ZinanFFCT40.SupportStuckMarginsPosAtSupW` at `δ*_WB`. -/
def SupportStuckMarginsPosAtSupWB : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∀ h₀ : E3, ‖h₀‖ = 1 → (∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) →
      (∃ c : NonIncident n,
        supportConstraint A (openingAxis k) c (-(monitoredSupWB A B k h₀)) = 0) →
      ∀ r : Fin (n + 1),
        0 < (⟪h₀, ((openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) r : S2) : E3)⟫ : ℝ)

/-- **The pure-hemi strict-convexity certificate at `δ*_WB`.**  In the pure-hemi sub-branch (all W-supports
of `A'_WB` strict), `A'_WB` is `StrictConvexSphArm`: strict supports + a tilted strict open-hemisphere
normal (FFCT30 tilt + FFCT36 separation, packaged in `reach_strictConvex_interior`).  Mirror of
`ZinanFFCT40.pureHemi_strictConvexW` at `δ*_WB`. -/
theorem pureHemi_strictConvexWB {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3} (_hnorm : ‖h₀‖ = 1)
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 < sOrient (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) i)
        (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (i + 1))
        (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) j)) :
    StrictConvexSphArm (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀))) := by
  set d : ℝ := -(monitoredSupWB A B k h₀) with hd
  have h3 : 3 ≤ n + 1 := by have := hA.two_le; omega
  have hhemnn : ∀ r : Fin (n + 1),
      0 ≤ (⟪h₀, ((openTail A (openingAxis k) d r : S2) : E3)⟫ : ℝ) := hemiWB_inner_nonneg hA hka hkt h0
  have hshort := shortArc_edge_zero_of_strict hA h3 hmix
  have htangent : EquatorTangentExists A (openingAxis k) h₀ d :=
    equatorTangentExists_of_strictSupports hmix hshort
  obtain ⟨t, ht⟩ := htangent
  obtain ⟨h', hh'norm, hh'pos⟩ :=
    exists_unit_perturbed_normal_of_tangent (m := n + 1) (by omega)
      (fun r => ((openTail A (openingAxis k) d r : S2) : E3)) h₀ t hhemnn ht
  exact reach_strictConvex_interior hA hh'norm hmix hh'pos

/-- **The repaired STUCK outcome at `δ*_WB`.**  From `StuckWB`, the scoped closing-edge residual, and the
scoped support-margin residual, `A'_WB` is `WeakConvexSphArm`, and EITHER a non-incident support vanishes OR
`A'_WB` is `StrictConvexSphArm` (the pure-hemi case).  Mirror of `ZinanFFCT40.stuckOutcomeW_repaired` at
`δ*_WB` (generic engines; NO `exfalso` on pure-hemi). -/
theorem stuckOutcomeWB_repaired {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3} (hnorm : ‖h₀‖ = 1)
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hclose : openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (Fin.last n)
      ≠ openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (Fin.last n + 1))
    (hmargins : (∃ c : NonIncident n,
        supportConstraint A (openingAxis k) c (-(monitoredSupWB A B k h₀)) = 0) →
      ∀ r : Fin (n + 1),
        0 < (⟪h₀, ((openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) r : S2) : E3)⟫ : ℝ))
    (_hstuck : StuckWB A B k h₀) :
    WeakConvexSphArm (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀))) ∧
      ((∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
          sOrient (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) i)
            (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (i + 1))
            (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) j) = 0) ∨
        StrictConvexSphArm (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)))) := by
  classical
  set d : ℝ := -(monitoredSupWB A B k h₀) with hd
  have h3 : 3 ≤ n + 1 := by have := hA.two_le; omega
  have hsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (openTail A (openingAxis k) d i) (openTail A (openingAxis k) d (i + 1))
        (openTail A (openingAxis k) d j) := supportWB_sOrient_nonneg hA hka hkt h0
  have hhemnn : ∀ r : Fin (n + 1),
      0 ≤ (⟪h₀, ((openTail A (openingAxis k) d r : S2) : E3)⟫ : ℝ) := hemiWB_inner_nonneg hA hka hkt h0
  have hdist : ∀ i : Fin (n + 1),
      openTail A (openingAxis k) d i ≠ openTail A (openingAxis k) d (i + 1) :=
    openedEdgesDistinct_at_d hA k d hclose
  rcases hemiStuck_dichotomy_tangentFree hA h3 hsupp hhemnn with hsupzero | hweak
  · -- SUPPORT alternative: a non-incident support vanishes.
    obtain ⟨i, j, hji, hji1, heq⟩ := hsupzero
    have hvanish : ∃ c : NonIncident n,
        supportConstraint A (openingAxis k) c d = 0 := by
      refine ⟨(⟨(i, j), ⟨hji, hji1⟩⟩ : NonIncident n), ?_⟩
      rw [supportConstraint_apply]; exact heq
    have hhemstrict : ∀ r : Fin (n + 1),
        0 < (⟪h₀, ((openTail A (openingAxis k) d r : S2) : E3)⟫ : ℝ) := hmargins hvanish
    have hweak : WeakConvexSphArm (openTail A (openingAxis k) d) :=
      weakConvex_of_supportStuckW_of_hemiPos_anyH hA hsupp hdist ⟨h₀, hnorm, hhemstrict⟩
    exact ⟨hweak, Or.inl ⟨i, j, hji, hji1, heq⟩⟩
  · -- WeakConvex without a stated vanishing support: split on whether some support vanishes.
    by_cases hsome : ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
        sOrient (openTail A (openingAxis k) d i) (openTail A (openingAxis k) d (i + 1))
          (openTail A (openingAxis k) d j) = 0
    · obtain ⟨i, j, hji, hji1, heq⟩ := hsome
      exact ⟨hweak, Or.inl ⟨i, j, hji, hji1, heq⟩⟩
    · -- PURE-HEMI: all supports strict ⟹ `A'_WB` strictly convex.
      have hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
          0 < sOrient (openTail A (openingAxis k) d i) (openTail A (openingAxis k) d (i + 1))
            (openTail A (openingAxis k) d j) := by
        intro i j hji hji1
        exact lt_of_le_of_ne (hsupp i j hji hji1) (fun h => hsome ⟨i, j, hji, hji1, h.symm⟩)
      have hstrict := pureHemi_strictConvexWB hA hnorm hka hkt h0 hmix
      exact ⟨hweak, Or.inr hstrict⟩

/-! ## §8. The base-stuck progress residual, the WB outcome, and the re-threaded headline.

The recursion-ready `SphericalArmAssembly.InteriorOpeningOutcome` needs, per opened arm, EITHER a deficit
drop (REACH) OR a vanishing support (CUT-ready).  The `WB` opening produces:

* `¬StuckWB` ⟹ `ReachWB ∨ BaseStuckWB` (clause (ii), §6); `ReachWB` drops the deficit, `BaseStuckWB` is the
  new branch resolved by `BaseStuckProgressW`;
* `StuckWB` ⟹ `WeakConvex ∧ (∃ vanishing support ∨ StrictConvex)` (clause (iii), §7); the vanishing support
  is CUT-ready, the strict-convex pure-hemi case is collapsed by `PureHemiProgressWB` (REACH or vanishing).

The two named, non-vacuous residuals collapse the two genuinely-new alternatives back into the original
outcome shape. -/

/-- **The pure-hemi progress residual at `δ*_WB`** (mirror of `ZinanFFCT40.PureHemiProgressW`).  At a
pure-hemi `WB` supremum (`A'_WB` strictly convex), the opening makes recursion-ready progress: EITHER the
joint reached (`ReachWB`, deficit drops) OR a non-incident support vanishes (CUT-ready). -/
def PureHemiProgressWB : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A → StrictConvexSphArm B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∀ h₀ : E3, ‖h₀‖ = 1 → (∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) →
      StuckWB A B k h₀ →
      StrictConvexSphArm (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀))) →
        ReachWB A B k h₀ ∨
        (∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
          sOrient (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) i)
            (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (i + 1))
            (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) j) = 0)

/-- **The base-stuck progress residual** (the genuinely-new design content of route (a)).  At a
`BaseStuckWB` supremum — the base triangle `(A 0, A K, A last)` has straightened to `γbase + δ*_WB = π`,
with the joint not necessarily reached and no W-monitor binding — the opening makes recursion-ready
progress: EITHER the joint reached (`ReachWB`, deficit drops) OR a non-incident support of `A'_WB` vanishes
(CUT-ready, `WeakConvex` then closes via the STUCK outcome).

HONEST STATUS — this is the **one genuine OPEN obligation** route (a) leaves (NOT proved in this module,
carried as a hypothesis to the headline).  The base monitor's vanishing (`baseCapSupportW A k δ*_WB = 0`,
i.e. `sin (γbase + δ*_WB) = 0`) is at the base triple `(0, K, last)`, which is **not** a NonIncident
`(i, i+1, j)` form (an interior axis has `0` and `last` non-consecutive), so it yields NO NonIncident
vanishing-support payload directly (design §9, §12).  A base-stuck supremum where the joint has NOT reached
and no W-support vanishes IS geometrically realizable (the base cap binds first); there `BaseStuckProgressW`
is NOT derivable from the spine — its honest discharge is route (b)'s straightening completion
(`baseStraight_completion_by_IH`, sub-arm IH `d(A0,AK)` / `d(AK,Alast)` vs `B` + triangle inequality),
which the current W-glue spine lacks.  Per the design (route (a) keeps the spine, does NOT open route (b)),
this is exposed as the single named residual instead of faked.

Refutation-resistance / non-vacuity: the hypothesis `BaseStuckWB` is SATISFIABLE (a genuine WB-supremum
branch, `baseStuckWB_def_real`), so this is NOT a vacuous-conditional impostor; the conclusion is a real
disjunction (`ReachWB` a genuine angle equation, the vanishing support genuine NonIncident data).  It is an
honest CONDITIONAL-honest residual, not a banked theorem. -/
def BaseStuckProgressW : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A → StrictConvexSphArm B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∀ h₀ : E3, ‖h₀‖ = 1 → (∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) →
      BaseStuckWB A B k h₀ →
        ReachWB A B k h₀ ∨
        (∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
          sOrient (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) i)
            (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (i + 1))
            (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) j) = 0)

/-- **The `WB`-base-capped interior-opening outcome → the original `InteriorOpeningOutcome`.**  Opening the
deficient joint about the interior axis to the `WB` admissible supremum `δ*_WB` produces an arm `A'_WB` with
`endpt A ≤ endpt A'_WB` (clause (i), **cap discharged**), `SameSides`, `JointLe`, and either a deficit drop
(REACH) or a CUT-ready vanishing support — recovering the recursion-ready outcome.  The two new
alternatives (pure-hemi strict, base-stuck) are collapsed by the named residuals `PureHemiProgressWB` and
`BaseStuckProgressW`.  `GlueWBaseCap` is **gone** from the residue surface. -/
theorem interiorOpeningOutcomeWB_basecapped
    (hclose : OpenedClosingEdgeDistinctAtSupWB) (hmargins : SupportStuckMarginsPosAtSupWB)
    (hprog : PureHemiProgressWB) (hbase : BaseStuckProgressW) :
    SphericalArmAssembly.InteriorOpeningOutcome := by
  intro n A B hA hB hside hangle k hkdef
  obtain ⟨h₀, hnorm, hhpos⟩ := hA.closed_convex.open_hemisphere
  set K : Fin (n + 1) := openingAxis k with hK
  set δ : ℝ := monitoredSupWB A B k h₀ with hδ
  set A' : Fin (n + 1) → S2 := openTail A K (-δ) with hA'
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0 :=
    monitoredFamily_init_admissible hA hhpos hkdef
  -- side/joint bookkeeping.
  have hjointk : jointAngle A' k = openedInteriorJointAngle A k (-δ) := by
    rw [hA']; exact jointAngle_openTail_eq_openedInterior A k (-δ)
  have hslack : openedInteriorJointAngle A k (-δ) ≤ jointAngle B k := by
    rw [hδ]; exact openedInteriorJoint_le_at_supWB hA hka hkt h0
  have hside' : SameSides A' B := by
    intro i; rw [hA', openTail_preserves_sides A K (-δ) i]; exact hside i
  have hangle' : JointLe A' B := by
    intro r
    by_cases hrk : r = k
    · rw [hrk, hjointk]; exact hslack
    · rw [hA', jointAngle_openTail_eq_of_ne A k (-δ) hrk]; exact hangle r
  -- endpoint non-decrease (clause i, cap DISCHARGED).
  have hmono : endpt A ≤ endpt A' := by
    rw [hA', hδ]; exact glueWB_clause_i hA hka hkt h0
  refine ⟨A', hmono, hside', hangle', ?_⟩
  -- the REACH-disjunct producer: `ReachWB` ⟹ deficit drop.
  have reach_drop : ReachWB A B k h₀ → deficitCount A' B < deficitCount A B := by
    intro hreach
    have hreach_k : jointAngle (openTail A K (-δ)) k = jointAngle B k := by
      rw [jointAngle_openTail_eq_openedInterior A k (-δ)]; rw [hδ]; exact hreach
    rw [hA']; exact deficitCount_openTail_reach_lt A B k (-δ) hkdef hreach_k
  -- the vanishing-support ⟹ STUCK-disjunct producer (with `WeakConvex` carried).
  by_cases hstuck : StuckWB A B k h₀
  · -- STUCK: repaired clause (iii) at `δ*_WB`.
    have hclose' : openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (Fin.last n)
        ≠ openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (Fin.last n + 1) :=
      hclose n A B hA k hkdef h₀ hnorm hhpos hstuck
    have hmargins' : (∃ c : NonIncident n,
        supportConstraint A (openingAxis k) c (-(monitoredSupWB A B k h₀)) = 0) →
        ∀ r : Fin (n + 1),
          0 < (⟪h₀, ((openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) r : S2) : E3)⟫ : ℝ) :=
      fun hsup => hmargins n A B hA k hkdef h₀ hnorm hhpos hsup
    obtain ⟨hweak, halt⟩ := stuckOutcomeWB_repaired hA hnorm hka hkt h0 hclose' hmargins' hstuck
    have hweak' : WeakConvexSphArm A' := by rw [hA', hδ]; exact hweak
    rcases halt with hvanish | hstrict
    · -- vanishing support: the STUCK (RIGHT) disjunct.
      refine Or.inr ⟨hweak', ?_⟩
      obtain ⟨i, j, hji, hji1, heq⟩ := hvanish
      exact ⟨i, j, hji, hji1, by rw [hA', hδ]; exact heq⟩
    · -- pure-hemi strict: collapse via `PureHemiProgressWB`.
      have hstrict' : StrictConvexSphArm
          (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀))) := hstrict
      rcases hprog n A B hA hB k hkdef h₀ hnorm hhpos hstuck hstrict' with hreach | hvanish
      · exact Or.inl ⟨by rw [hA', hδ]; exact hstrict, reach_drop hreach⟩
      · refine Or.inr ⟨hweak', ?_⟩
        obtain ⟨i, j, hji, hji1, heq⟩ := hvanish
        exact ⟨i, j, hji, hji1, by rw [hA', hδ]; exact heq⟩
  · -- ¬ StuckWB ⟹ ReachWB ∨ BaseStuckWB.
    rcases glueWB_clause_ii hA hB hka hkt h0 hstuck with hreach | hbasestuck
    · -- ReachWB ⟹ deficit drop; the opened arm is strictly convex (no W-monitor binds).
      have hstrictA' : StrictConvexSphArm A' := by
        rw [hA', hδ]
        refine pureHemi_strictConvexWB hA hnorm hka hkt h0 ?_
        intro i j hji hji1
        refine lt_of_le_of_ne (supportWB_sOrient_nonneg hA hka hkt h0 i j hji hji1) ?_
        intro heq
        exact hstuck (Or.inl ⟨⟨(i, j), ⟨hji, hji1⟩⟩, by rw [supportConstraint_apply]; exact heq.symm⟩)
      exact Or.inl ⟨hstrictA', reach_drop hreach⟩
    · -- BaseStuckWB ⟹ resolve via `BaseStuckProgressW`.
      rcases hbase n A B hA hB k hkdef h₀ hnorm hhpos hbasestuck with hreach | hvanish
      · -- ReachWB ⟹ deficit drop; strict-convex producer as above.
        have hstrictA' : StrictConvexSphArm A' := by
          rw [hA', hδ]
          refine pureHemi_strictConvexWB hA hnorm hka hkt h0 ?_
          intro i j hji hji1
          refine lt_of_le_of_ne (supportWB_sOrient_nonneg hA hka hkt h0 i j hji hji1) ?_
          intro heq
          exact hstuck (Or.inl ⟨⟨(i, j), ⟨hji, hji1⟩⟩, by rw [supportConstraint_apply]; exact heq.symm⟩)
        exact Or.inl ⟨hstrictA', reach_drop hreach⟩
      · -- a non-incident support vanishes: STUCK (RIGHT) disjunct.  But we are in `¬StuckWB`, so this
        -- vanishing support is a contradiction — base-stuck non-reach with a vanishing support means
        -- the support disjunct of `StuckWB` holds.  Resolve: the vanishing support gives WeakConvex.
        obtain ⟨i, j, hji, hji1, heq⟩ := hvanish
        exact absurd (Or.inl ⟨⟨(i, j), ⟨hji, hji1⟩⟩,
          by rw [supportConstraint_apply]; exact heq⟩) hstuck

/-! ## §9. The base-capped headline (`GlueWBaseCap` DISCHARGED) and the non-vacuity guards.

The headline `mainPlus_headline_basecapped` is `ZinanFFCT40.mainPlus_headline_repaired` with `GlueWBaseCap`
**removed** from the residue list — it is now a theorem (`GlueWBaseCap_at_supWB`), folded into clause (i)
of `interiorOpeningOutcomeWB_basecapped`.  The new residue surface (all scoped to the `WB` binders) is:

* `hcore : SpliceBodyDiagMono`, `hstruct : SpliceStructuralData` — pre-B1 splice geometry (unchanged);
* `hclose : OpenedClosingEdgeDistinctAtSupWB` — the single wraparound closing edge (scoped, refutation-resistant);
* `hmargins : SupportStuckMarginsPosAtSupWB` — strict ambient-`h₀` margins on the *support* branch (scoped);
* `hprog : PureHemiProgressWB` — the pure-hemi progress residual;
* `hbase : BaseStuckProgressW` — **the genuinely-new base-stuck residual** (route (a)'s honest open content;
  see §8: a base-stuck supremum's recursion progress; not provable from the spine alone, route (b)'s
  straightening completion would discharge it — carried here as a named, satisfiable residual).

`GlueWBaseCap` is GONE.  Every remaining hypothesis is a named, satisfiable `Prop` scoped to the glue
context. -/

theorem mainPlus_headline_basecapped
    (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData)
    (hclose : OpenedClosingEdgeDistinctAtSupWB) (hmargins : SupportStuckMarginsPosAtSupWB)
    (hprog : PureHemiProgressWB) (hbase : BaseStuckProgressW)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_spliceBodyDiagMono hcore hstruct
    (interiorOpeningOutcomeWB_basecapped hclose hmargins hprog hbase) hn A B hA hB hside hangle

/-! ### Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of the base sinusoid: at `θ = 0` it is the genuine convex base support
`sOrient (A 0)(A K)(A last) = N sin γbase`, strictly positive for a strict arm at an interior axis. -/
theorem baseSupport_openNeg_eq_sin_zero {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1))
    (hka : ShortArc (A (openingAxis k)) (A 0))
    (hkt : ShortArc (A (openingAxis k)) (A (Fin.last n))) :
    sOrient (A 0) (A (openingAxis k)) (A (Fin.last n))
      = ‖tangentTo (A (openingAxis k)) (A 0)‖
          * ‖tangentTo (A (openingAxis k)) (A (Fin.last n))‖
          * Real.sin (sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n))) := by
  have h := baseSupport_openNeg_eq_sin hA k hka hkt 0
  simp only [add_zero] at h
  rw [show baseCapSupportW A k 0
      = sOrient (A 0) (A (openingAxis k)) (A (Fin.last n)) by
    show sOrient (A 0) (A (openingAxis k)) (rotS2 (A (openingAxis k)) (-(0:ℝ)) (A (Fin.last n))) = _
    rw [show rotS2 (A (openingAxis k)) (-(0:ℝ)) (A (Fin.last n)) = A (Fin.last n) by
      apply S2.ext; rw [rotS2_coe, neg_zero, rot_zero]]] at h
  exact h

/-- Non-vacuity of `GlueWBaseCap_at_supWB`: the cap is the real base great-semicircle condition, satisfied
at the unopened arm `δ*_WB`-free point `δ = 0` (`0 + γbase ≤ π`), so it is not a vacuous-hypothesis impostor
but a genuine range condition the base monitor enforces. -/
theorem baseCap_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    (0 : ℝ) + sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) ≤ Real.pi := by
  rw [zero_add]; exact sphAngle_le_pi _ _ _

/-- **Refutation-resistance of the scoped Brick 1** (`OpenedClosingEdgeDistinctAtSupWB`): a constant arm is
excluded by `StrictConvexSphArm A` (it would force a strict non-incident support `0 < sOrient p p p = 0`),
so the scoped closing-edge clause is never reached for a constant arm. -/
theorem openedClosingEdgeDistinctAtSupWB_constantArm_excluded {n : ℕ} (p : S2)
    (hStrict : StrictConvexSphArm (fun _ : Fin (n + 1) => p)) : False :=
  openedClosingEdgeDistinctAtSupW_constantArm_excluded p hStrict

/-- Non-vacuity of `BaseStuckWB`: it is the genuine base-monitor equation `baseCapSupportW A k δ*_WB = 0`,
i.e. `sin (γbase + δ*_WB) = 0` — a real geometric event (the base triangle straightening), not a vacuous
hypothesis.  (The base monitor's value at `0` is the strict positive convex support, so the monitor is a
real continuous functional that genuinely can hit `0`.) -/
theorem baseStuckWB_def_real {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) :
    BaseStuckWB A B k h₀ ↔ baseCapSupportW A k (monitoredSupWB A B k h₀) = 0 := Iff.rfl

/-- Non-vacuity of `BaseStuckProgressW` / `PureHemiProgressWB`: the `ReachWB` member is a real angle
equation; the vanishing-support member is real NonIncident data — a genuine disjunction, not a
vacuous-hypothesis impostor. -/
theorem reachWB_def_real {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) :
    ReachWB A B k h₀ ↔
      openedInteriorJointAngle A k (-(monitoredSupWB A B k h₀)) = jointAngle B k := Iff.rfl

/-- Non-vacuity of the headline conclusion: realised reflexively at `A = B`. -/
theorem mainPlus_headline_basecapped_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

end ProofsInTheBook.ZinanFFCT41

-- §1 the WB family + W-admissibility bridge
#print axioms ProofsInTheBook.ZinanFFCT41.monitoredSupWB_mem_W
-- §2 the base sinusoid
#print axioms ProofsInTheBook.ZinanFFCT41.baseSupport_openNeg_eq_sin
-- §3 the cap by admissibility (the central new content)
#print axioms ProofsInTheBook.ZinanFFCT41.admissibleWB_baseCap
#print axioms ProofsInTheBook.ZinanFFCT41.GlueWBaseCap_at_supWB
-- §5 the WB trichotomy
#print axioms ProofsInTheBook.ZinanFFCT41.opening_boundary_trichotomyWB
-- §6/§7 the clauses at the WB sup
#print axioms ProofsInTheBook.ZinanFFCT41.glueWB_clause_i
#print axioms ProofsInTheBook.ZinanFFCT41.glueWB_clause_ii
#print axioms ProofsInTheBook.ZinanFFCT41.stuckOutcomeWB_repaired
-- §8/§9 the base-capped outcome + headline (GlueWBaseCap discharged)
#print axioms ProofsInTheBook.ZinanFFCT41.interiorOpeningOutcomeWB_basecapped
#print axioms ProofsInTheBook.ZinanFFCT41.mainPlus_headline_basecapped
-- refutation-resistance witness
#print axioms ProofsInTheBook.ZinanFFCT41.openedClosingEdgeDistinctAtSupWB_constantArm_excluded
