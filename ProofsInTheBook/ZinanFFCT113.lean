import ProofsInTheBook.SphericalReachStuck
import ProofsInTheBook.SphericalSZFinal
import ProofsInTheBook.SphericalSZClose
import ProofsInTheBook.ZinanFFCT111

/-!
# `ZinanFFCT113` — discharging `StuckWitnessExists` via the strict arm lemma (right disjunct)

This file proves the chapter-13 residue
`SphericalOpeningProcess.StuckWitnessExists` **unconditionally** (0 sorry, clean-3).

## The route (verified TRUE; the first-corner left disjunct is the substrate's machine-refuted target)

`StuckWitnessExists` is a *disjunction*:
either a first-corner stuck witness `qstar` (`A 0 ∈ span≥0 {A 1, qstar}` + bounds) **or** the strict
endpoint bound `endpt A < endpt B`.  The substrate proves (`SphericalStuckGeneral`,
`SphericalStuckWitness.closing_not_first`, `SphericalTerminalVis.terminalVisibility_false`) that the
first-corner left disjunct is FALSE on the configurations the last-joint opening produces — so the only
viable route is the **right disjunct** `endpt A < endpt B`.

We prove the right disjunct unconditionally by the classical *tiny-opening* bootstrap.  Let `i₀` be a
strictly wider joint (`jointAngle A i₀ < jointAngle B i₀`).  Set `K = A (i₀+1)` (the vertex carrying
joint `i₀`).  For a small `θ > 0`, open the tail beyond `K` by `-θ` about `K` (`openTail A K (-θ)`):

* the base triangle `(A 0, K, A last)` has the forward-diagonal support strictly positive
  (`cut_diagonal_supports`), so opening by `-θ` STRICTLY increases the base angle
  (`openedAngle_gt_of_oriented_neg`, built here), hence the endpoint strictly increases
  `endpt A < endpt (openTail A K (-θ))` (`reach_base_endpoint_strict`);
* for `θ` small the opened arm stays a `StrictConvexSphArm` (every defining strict inequality —
  edge `ShortArc`, non-incident `sOrient > 0`, hemisphere `⟪h,·⟫ > 0` — is continuous in `θ` and
  strictly satisfied at `θ = 0`; finitely many, so a uniform `θ₀ > 0` works);
* the opening fixes every side length (`openTail_sideLen`) and every joint except `i₀`; joint `i₀`
  varies continuously with `θ` and is `< jointAngle B i₀` at `θ = 0`, so stays `<` for small `θ`;
  all other joints are unchanged `≤ B`.

Then the UNCONDITIONAL weak arm lemma `ZinanFFCT111.spherical_arm_mono_final_ch13` gives
`endpt (openTail A K (-θ)) ≤ endpt B`, and chaining yields `endpt A < endpt B`.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalHinge ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalFinish ProofsInTheBook.SphericalSZStep
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.ZinanFFCT78 ProofsInTheBook.ZinanFFCT111

namespace ProofsInTheBook.ZinanFFCT113

set_option maxHeartbeats 1600000

/-! ## §1. The strict mirrored base-angle increase. -/

/-- **Strict mirrored cosine bound.**  Companion of `cos_open_le_cos_orig_neg`: a *strict* opening
`0 < θ` (within the great-semicircle range, `θ + φ₀ < π`) and a strict oriented datum
`0 < ⟪tangentTo axis a0, axis × tangentTo axis tail⟫`... actually we only need the strict-angle
output, derived below. -/
theorem cos_open_lt_cos_orig_neg (axis a0 tail : S2)
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail)
    (hsign : (0 : ℝ) ≤ (⟪tangentTo axis a0, cross (axis : E3) (tangentTo axis tail)⟫ : ℝ))
    {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ + sphAngle a0 axis tail < Real.pi) :
    Real.cos (sphAngle a0 axis (rotS2 axis (-θ) tail)) < Real.cos (sphAngle a0 axis tail) := by
  set u := tangentTo axis a0 with hu
  set w := tangentTo axis tail with hw
  set c : ℝ := ⟪u, w⟫ with hc
  set s : ℝ := ⟪u, cross (axis : E3) w⟫ with hsdef
  have hunz : u ≠ 0 := (tangentTo_ne_zero_iff axis a0).2 hka
  have hwnz : w ≠ 0 := (tangentTo_ne_zero_iff axis tail).2 hkt
  have hup : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hunz
  have hwp : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hwnz
  set N : ℝ := ‖u‖ * ‖w‖ with hN
  have hNp : (0 : ℝ) < N := mul_pos hup hwp
  set φ₀ : ℝ := sphAngle a0 axis tail with hφ
  have hcosopen : Real.cos (sphAngle a0 axis (rotS2 axis (-θ) tail))
      = (Real.cos (-θ) * c + Real.sin (-θ) * s) / N := by
    rw [cos_openedJointAngle, norm_tangentTo_open]
  have hcosorig : Real.cos φ₀ = c / N := by
    rw [hφ, sphAngle, InnerProductGeometry.cos_angle]
  have hφ0 : 0 ≤ φ₀ := sphAngle_nonneg _ _ _
  have hφπ : φ₀ ≤ Real.pi := sphAngle_le_pi _ _ _
  have hpyth : c ^ 2 + s ^ 2 = N ^ 2 := by
    have := tangentPlane_pythag (k := (axis : E3)) (u := u) (w := w) axis.2
      (tangentTo_orthogonal axis a0) (tangentTo_orthogonal axis tail)
    rw [hc, hsdef, hN]; rw [mul_pow]; linear_combination this
  have hcEq : c = N * Real.cos φ₀ := by
    rw [hcosorig]; field_simp
  have hsinφ : 0 ≤ Real.sin φ₀ := Real.sin_nonneg_of_nonneg_of_le_pi hφ0 hφπ
  have hssq : s ^ 2 = (N * Real.sin φ₀) ^ 2 := by
    have hsincos : Real.sin φ₀ ^ 2 = 1 - Real.cos φ₀ ^ 2 := by
      have := Real.sin_sq_add_cos_sq φ₀; linarith
    rw [mul_pow, hsincos]
    have : s ^ 2 = N ^ 2 - c ^ 2 := by linarith [hpyth]
    rw [this, hcEq]; ring
  have hsEq : s = N * Real.sin φ₀ := by
    have hge : 0 ≤ N * Real.sin φ₀ := mul_nonneg (le_of_lt hNp) hsinφ
    nlinarith [hssq, hsign, hge, sq_nonneg (s - N * Real.sin φ₀)]
  have hsinusoid : Real.cos (-θ) * c + Real.sin (-θ) * s = N * Real.cos (φ₀ + θ) := by
    rw [hcEq, hsEq, Real.cos_neg, Real.sin_neg, Real.cos_add]; ring
  rw [hcosopen, hcosorig, hsinusoid]
  rw [div_lt_div_iff_of_pos_right hNp]
  have hcos : Real.cos (φ₀ + θ) < Real.cos φ₀ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hφ0 (by linarith) (by linarith)
  rw [hcEq]
  exact mul_lt_mul_of_pos_left hcos hNp

/-- **Strict mirrored base-angle increase.**  Opening the joint at `axis` by `-θ` (`0 < θ`, strictly
within range) strictly increases the base angle, given the convex oriented datum. -/
theorem openedAngle_gt_of_oriented_neg (axis a0 tail : S2)
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail)
    (hsign : (0 : ℝ) ≤ (⟪tangentTo axis a0, cross (axis : E3) (tangentTo axis tail)⟫ : ℝ))
    {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ + sphAngle a0 axis tail < Real.pi) :
    sphAngle a0 axis tail < sphAngle a0 axis (rotS2 axis (-θ) tail) := by
  have hcos := cos_open_lt_cos_orig_neg axis a0 tail hka hkt hsign hθ0 hθπ
  by_contra hle
  rw [not_lt] at hle
  have : Real.cos (sphAngle a0 axis (rotS2 axis (-θ) tail)) ≥ Real.cos (sphAngle a0 axis tail) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (sphAngle_nonneg _ _ _) (sphAngle_le_pi _ _ _) hle
  linarith [hcos]

/-! ## §2. The strict interior-axis endpoint increase. -/

/-- **Interior-axis endpoint STRICT increase.**  For a strictly convex arm `A`, interior axis `K`
(`1 ≤ K.val`, `K.val < n`), opening the tail by `-θ` with `0 < θ` strictly within the great-semicircle
range strictly increases the arm endpoint. -/
theorem endpt_openTail_interior_strict {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {K : Fin (n + 1)} (hK0 : 1 ≤ K.val) (hKn : K.val < n) {θ : ℝ} (hθ0 : 0 < θ)
    (hθπ : θ + sphAngle (A 0) (A K) (A (Fin.last n)) < Real.pi) :
    endpt A < endpt (openTail A K (-θ)) := by
  obtain ⟨hka, hkt⟩ := shortArc_interior_base hA hK0 hKn
  have hsign : (0 : ℝ) ≤
      (⟪tangentTo (A K) (A 0), cross (A K : E3) (tangentTo (A K) (A (Fin.last n)))⟫ : ℝ) :=
    orientedSign_neg_of_support (orientedDatum_interior hA hK0 hKn)
  have hangle : sphAngle (A 0) (A K) (A (Fin.last n))
      < sphAngle (A 0) (A K) (rotS2 (A K) (-θ) (A (Fin.last n))) :=
    openedAngle_gt_of_oriented_neg (A K) (A 0) (A (Fin.last n)) hka hkt hsign hθ0 hθπ
  have hstr : sDist (A 0) (A (Fin.last n))
      < sDist (A 0) (rotS2 (A K) (-θ) (A (Fin.last n))) :=
    reach_base_endpoint_strict (A K) (A 0) (A (Fin.last n)) hka hkt hangle
  rw [endpt_openTail_interior A (-θ) hK0 hKn]
  exact hstr

/-! ## §3. Strict convexity persists for small `θ`. -/

/-- Continuity of `tangentTo` of two `θ`-continuous unit-vector families. -/
theorem continuousAt_tangentTo_openTail {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (p q : Fin (n + 1)) (θ₀ : ℝ) :
    ContinuousAt (fun θ : ℝ => tangentTo (openTail A K θ p) (openTail A K θ q)) θ₀ := by
  have hp := (continuous_openTail_vec A K p).continuousAt (x := θ₀)
  have hq := (continuous_openTail_vec A K q).continuousAt (x := θ₀)
  have heq : (fun θ : ℝ => tangentTo (openTail A K θ p) (openTail A K θ q))
      = (fun θ : ℝ => ((openTail A K θ q : S2) : E3)
          - (⟪((openTail A K θ q : S2) : E3), ((openTail A K θ p : S2) : E3)⟫ : ℝ)
            • ((openTail A K θ p : S2) : E3)) := by
    funext θ; rw [tangentTo_eq]; rfl
  rw [heq]
  exact hq.sub ((hq.inner hp).smul hp)

/-- The generic `openTail` strict-convexity assembler (mirrors `reach_strictConvex_at_sup`). -/
theorem strictConvex_openTail_of_constraints {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) {K : Fin (n + 1)} {θ : ℝ} {h : E3} (hnorm : ‖h‖ = 1)
    (hedge : ∀ i : Fin (n + 1), ShortArc (openTail A K θ i) (openTail A K θ (i + 1)))
    (hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 < sOrient (openTail A K θ i) (openTail A K θ (i + 1)) (openTail A K θ j))
    (hhem : ∀ k : Fin (n + 1), 0 < (⟪h, (openTail A K θ k : E3)⟫ : ℝ)) :
    StrictConvexSphArm (openTail A K θ) := by
  refine { two_le := hA.two_le, closed_convex := ?_ }
  refine { three_le := by have := hA.two_le; omega
           edge_short := hedge
           edge_support := ?_
           strict_nonincident := hmix
           open_hemisphere := ⟨h, hnorm, hhem⟩ }
  intro i j
  by_cases hji : j = i
  · subst hji; rw [sOrient, ProofsInTheBook.SphericalDiagCut.det3_self_right]
  · by_cases hji1 : j = i + 1
    · subst hji1; rw [sOrient, ProofsInTheBook.SphericalDiagCut.det3_self_mid]
    · exact le_of_lt (hmix i j hji hji1)

/-- **Strict convexity persistence for small opening.**  There is a `θ₀ > 0` such that for all `θ`
with `|θ| < θ₀`, `openTail A K θ` is a `StrictConvexSphArm`. -/
theorem strictConvex_openTail_of_small {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (K : Fin (n + 1)) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, |θ| < θ₀ → StrictConvexSphArm (openTail A K θ) := by
  classical
  obtain ⟨h, hnorm, hhpos0⟩ := hA.closed_convex.open_hemisphere
  -- at θ = 0, openTail A K 0 = A, so every constraint is strictly satisfied.
  have h0 : openTail A K 0 = A := openTail_zero_angle A K
  -- Build the conjunction of all (finitely many) strict constraints as an eventually-true statement.
  -- edge family: 0 < ‖tangentTo (P i)(P (i+1))‖
  have hedge_ev : ∀ i : Fin (n + 1),
      ∀ᶠ θ : ℝ in nhds 0,
        0 < ‖tangentTo (openTail A K θ i) (openTail A K θ (i + 1))‖ := by
    intro i
    have hcont : ContinuousAt
        (fun θ : ℝ => ‖tangentTo (openTail A K θ i) (openTail A K θ (i + 1))‖) 0 :=
      (continuousAt_tangentTo_openTail A K i (i + 1) 0).norm
    have hpos0 : 0 < ‖tangentTo (openTail A K 0 i) (openTail A K 0 (i + 1))‖ := by
      rw [h0]
      have hsa : ShortArc (A i) (A (i + 1)) := hA.closed_convex.edge_short i
      exact norm_pos_iff.2 ((tangentTo_ne_zero_iff _ _).2 hsa)
    exact continuousAt_const.eventually_lt hcont hpos0
  -- mixed support family
  have hmix_ev : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      ∀ᶠ θ : ℝ in nhds 0,
        0 < sOrient (openTail A K θ i) (openTail A K θ (i + 1)) (openTail A K θ j) := by
    intro i j hji hji1
    have hcont : ContinuousAt
        (fun θ : ℝ => sOrient (openTail A K θ i) (openTail A K θ (i + 1)) (openTail A K θ j)) 0 :=
      (continuous_interiorSupport A K (i, i + 1, j)).continuousAt
    have hpos0 : 0 < sOrient (openTail A K 0 i) (openTail A K 0 (i + 1)) (openTail A K 0 j) := by
      rw [h0]; exact hA.closed_convex.strict_nonincident i j hji hji1
    exact continuousAt_const.eventually_lt hcont hpos0
  -- hemisphere family
  have hhem_ev : ∀ k : Fin (n + 1),
      ∀ᶠ θ : ℝ in nhds 0, 0 < (⟪h, (openTail A K θ k : E3)⟫ : ℝ) := by
    intro k
    have hcont : ContinuousAt (fun θ : ℝ => (⟪h, (openTail A K θ k : E3)⟫ : ℝ)) 0 :=
      (continuous_const.inner (continuous_openTail_vec A K k)).continuousAt
    have hpos0 : 0 < (⟪h, (openTail A K 0 k : E3)⟫ : ℝ) := by rw [h0]; exact hhpos0 k
    exact continuousAt_const.eventually_lt hcont hpos0
  -- combine: all three finite families eventually hold together.
  have hmix_all : ∀ᶠ θ : ℝ in nhds 0,
      (∀ p : Fin (n + 1) × Fin (n + 1), p.2 ≠ p.1 → p.2 ≠ p.1 + 1 →
        0 < sOrient (openTail A K θ p.1) (openTail A K θ (p.1 + 1)) (openTail A K θ p.2)) := by
    refine Filter.eventually_all.2 ?_
    intro p
    by_cases hp1 : p.2 = p.1
    · exact Filter.Eventually.of_forall (fun θ hc => absurd hp1 hc)
    · by_cases hp2 : p.2 = p.1 + 1
      · exact Filter.Eventually.of_forall (fun θ _ hc => absurd hp2 hc)
      · exact (hmix_ev p.1 p.2 hp1 hp2).mono (fun θ hθ _ _ => hθ)
  have hall : ∀ᶠ θ : ℝ in nhds 0,
      (∀ i : Fin (n + 1), 0 < ‖tangentTo (openTail A K θ i) (openTail A K θ (i + 1))‖) ∧
      (∀ p : Fin (n + 1) × Fin (n + 1), p.2 ≠ p.1 → p.2 ≠ p.1 + 1 →
        0 < sOrient (openTail A K θ p.1) (openTail A K θ (p.1 + 1)) (openTail A K θ p.2)) ∧
      (∀ k : Fin (n + 1), 0 < (⟪h, (openTail A K θ k : E3)⟫ : ℝ)) :=
    ((Filter.eventually_all.2 hedge_ev).and hmix_all).and (Filter.eventually_all.2 hhem_ev) |>.mono
      (fun θ hθ => ⟨hθ.1.1, hθ.1.2, hθ.2⟩)
  -- extract a metric ball.
  rw [Metric.eventually_nhds_iff] at hall
  obtain ⟨θ₀, hθ₀pos, hθ₀⟩ := hall
  refine ⟨θ₀, hθ₀pos, ?_⟩
  intro θ hθ
  have hdist : dist θ 0 < θ₀ := by rw [Real.dist_eq, sub_zero]; exact hθ
  obtain ⟨hE, hM, hH⟩ := hθ₀ hdist
  refine strictConvex_openTail_of_constraints hA hnorm ?_ ?_ hH
  · intro i; exact (tangentTo_ne_zero_iff _ _).1 (norm_pos_iff.1 (hE i))
  · intro i j hji hji1; exact hM (i, j) hji hji1

/-! ## §4. Continuity of the joint angle in the opening (at `θ = 0`). -/

/-- **Joint-angle continuity at `θ₀`** when the two joint tangents are nonzero there. -/
theorem continuousAt_jointAngle_openTail {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (i : Fin (n - 1)) (θ₀ : ℝ)
    (hp : tangentTo (openTail A K θ₀ ⟨i.val + 1, by have := i.isLt; omega⟩)
            (openTail A K θ₀ ⟨i.val, by have := i.isLt; omega⟩) ≠ 0)
    (hq : tangentTo (openTail A K θ₀ ⟨i.val + 1, by have := i.isLt; omega⟩)
            (openTail A K θ₀ ⟨i.val + 2, by have := i.isLt; omega⟩) ≠ 0) :
    ContinuousAt (fun θ : ℝ => jointAngle (openTail A K θ) i) θ₀ := by
  set a : Fin (n + 1) := ⟨i.val, by have := i.isLt; omega⟩
  set b : Fin (n + 1) := ⟨i.val + 1, by have := i.isLt; omega⟩
  set c : Fin (n + 1) := ⟨i.val + 2, by have := i.isLt; omega⟩
  have hangle :
      ContinuousAt (fun y : E3 × E3 => InnerProductGeometry.angle y.1 y.2)
        (tangentTo (openTail A K θ₀ b) (openTail A K θ₀ a),
          tangentTo (openTail A K θ₀ b) (openTail A K θ₀ c)) :=
    InnerProductGeometry.continuousAt_angle hp hq
  have hpair :
      ContinuousAt (fun θ : ℝ =>
        ((tangentTo (openTail A K θ b) (openTail A K θ a),
          tangentTo (openTail A K θ b) (openTail A K θ c)) : E3 × E3)) θ₀ :=
    (continuousAt_tangentTo_openTail A K b a θ₀).prodMk
      (continuousAt_tangentTo_openTail A K b c θ₀)
  have hcomp :
      ContinuousAt
        ((fun y : E3 × E3 => InnerProductGeometry.angle y.1 y.2) ∘
          (fun θ : ℝ =>
            ((tangentTo (openTail A K θ b) (openTail A K θ a),
              tangentTo (openTail A K θ b) (openTail A K θ c)) : E3 × E3))) θ₀ :=
    ContinuousAt.comp
      (g := fun y : E3 × E3 => InnerProductGeometry.angle y.1 y.2)
      (f := fun θ : ℝ =>
        ((tangentTo (openTail A K θ b) (openTail A K θ a),
          tangentTo (openTail A K θ b) (openTail A K θ c)) : E3 × E3))
      hangle hpair
  have heq : (fun θ : ℝ => jointAngle (openTail A K θ) i)
      = ((fun y : E3 × E3 => InnerProductGeometry.angle y.1 y.2) ∘
          (fun θ : ℝ =>
            ((tangentTo (openTail A K θ b) (openTail A K θ a),
              tangentTo (openTail A K θ b) (openTail A K θ c)) : E3 × E3))) := by
    funext θ; rfl
  rw [heq]; exact hcomp

/-! ## §5. The assembly: `StuckWitnessExists`. -/

theorem stuckWitnessExists_holds : StuckWitnessExists := by
  intro n hn A B hA hB hside hangle _ih hwider
  -- We always take the right disjunct `endpt A < endpt B`.
  refine Or.inr ?_
  obtain ⟨i₀, hi₀⟩ := hwider
  -- the opening axis = apex of the deficient joint i₀.
  set K : Fin (n + 1 + 1) := openingAxis i₀ with hK
  obtain ⟨hK0, hKn⟩ := ProofsInTheBook.SphericalOpeningOutcome.openingAxis_interior i₀
  -- base angle is strictly below π, so there is room to open.
  have hbaseπ : sphAngle (A 0) (A K) (A (Fin.last (n + 1))) < Real.pi :=
    ProofsInTheBook.ZinanFFCT41.base_sphAngle_lt_pi hA i₀
  -- §3: strict convexity persists on |θ| < θc.
  obtain ⟨θc, hθcpos, hθc⟩ := strictConvex_openTail_of_small hA K
  -- §4: joint i₀ stays < B's joint i₀ on a neighbourhood of 0.
  have hjcont : ContinuousAt (fun θ : ℝ => jointAngle (openTail A K θ) i₀) 0 := by
    have h0 : openTail A K 0 = A := openTail_zero_angle A K
    refine continuousAt_jointAngle_openTail A K i₀ 0 ?_ ?_
    · rw [h0]
      have hsa : ShortArc (A ⟨i₀.val + 1, by have := i₀.isLt; omega⟩)
          (A ⟨i₀.val, by have := i₀.isLt; omega⟩) := by
        have := hA.closed_convex.edge_short ⟨i₀.val, by have := i₀.isLt; omega⟩
        -- edge from ⟨i₀⟩ to ⟨i₀+1⟩ is a short arc; symmetrize.
        have hsucc : (⟨i₀.val, by have := i₀.isLt; omega⟩ + 1 : Fin (n + 1 + 1))
            = ⟨i₀.val + 1, by have := i₀.isLt; omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_add, Fin.val_one]
          rw [Nat.mod_eq_of_lt (by have := i₀.isLt; omega)]
        rw [hsucc] at this; exact this.symm
      exact (tangentTo_ne_zero_iff _ _).2 hsa
    · rw [h0]
      have hsa : ShortArc (A ⟨i₀.val + 1, by have := i₀.isLt; omega⟩)
          (A ⟨i₀.val + 2, by have := i₀.isLt; omega⟩) := by
        have := hA.closed_convex.edge_short ⟨i₀.val + 1, by have := i₀.isLt; omega⟩
        have hsucc : (⟨i₀.val + 1, by have := i₀.isLt; omega⟩ + 1 : Fin (n + 1 + 1))
            = ⟨i₀.val + 2, by have := i₀.isLt; omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_add, Fin.val_one]
          rw [Nat.mod_eq_of_lt (by have := i₀.isLt; omega)]
        rw [hsucc] at this; exact this
      exact (tangentTo_ne_zero_iff _ _).2 hsa
  have hjev : ∀ᶠ θ : ℝ in nhds 0, jointAngle (openTail A K θ) i₀ < jointAngle B i₀ := by
    have hval0 : (fun θ : ℝ => jointAngle (openTail A K θ) i₀) 0 < jointAngle B i₀ := by
      simp only [openTail_zero_angle]; exact hi₀
    exact hjcont.eventually_lt continuousAt_const hval0
  rw [Metric.eventually_nhds_iff] at hjev
  obtain ⟨θj, hθjpos, hθj⟩ := hjev
  -- choose θ small enough (strictly) for: convexity, joint slack, and angle range.
  have hπgap : 0 < Real.pi - sphAngle (A 0) (A K) (A (Fin.last (n + 1))) := by linarith
  set m : ℝ := min (min θc θj) (Real.pi - sphAngle (A 0) (A K) (A (Fin.last (n + 1)))) with hm
  have hmpos : 0 < m := lt_min (lt_min hθcpos hθjpos) hπgap
  set θ : ℝ := m / 2 with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; linarith
  have hθm : θ < m := by rw [hθdef]; linarith
  have hθ_c : θ < θc := lt_of_lt_of_le hθm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hθ_j : θ < θj := lt_of_lt_of_le hθm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hθ_π : θ + sphAngle (A 0) (A K) (A (Fin.last (n + 1))) < Real.pi := by
    have : θ < Real.pi - sphAngle (A 0) (A K) (A (Fin.last (n + 1))) :=
      lt_of_lt_of_le hθm (min_le_right _ _)
    linarith
  -- the opened arm at -θ.
  have habs : |(-θ)| < θc := by rw [abs_neg, abs_of_pos hθpos]; exact hθ_c
  have hAsharp : StrictConvexSphArm (openTail A K (-θ)) := hθc (-θ) habs
  -- (1) strict endpoint increase.
  have hendpt_str : endpt A < endpt (openTail A K (-θ)) :=
    endpt_openTail_interior_strict hA hK0 hKn hθpos hθ_π
  -- (2) the opened arm has the same sides as B.
  have hside' : ∀ i : Fin (n + 1), sideLen (openTail A K (-θ)) i = sideLen B i := by
    intro i; rw [openTail_preserves_sides A K (-θ) i]; exact hside i
  -- (3) the opened arm has joints ≤ B.
  have hangle' : ∀ i : Fin (n + 1 - 1), jointAngle (openTail A K (-θ)) i ≤ jointAngle B i := by
    intro i
    by_cases hii : i = i₀
    · subst hii
      have hdist : dist (-θ) 0 < θj := by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hθpos]; exact hθ_j
      exact le_of_lt (hθj hdist)
    · rw [jointAngle_openTail_eq_of_ne A i₀ (-θ) hii]; exact hangle i
  -- (4) the unconditional weak arm lemma at level n+1.
  have hweak : endpt (openTail A K (-θ)) ≤ endpt B := by
    have := spherical_arm_mono_final_ch13 (n := n + 1) (by omega)
      (openTail A K (-θ)) B hAsharp hB hside' hangle'
    simpa [endpt] using this
  exact lt_of_lt_of_le hendpt_str hweak

/-! ## Guard. -/

#print axioms stuckWitnessExists_holds

end ProofsInTheBook.ZinanFFCT113
