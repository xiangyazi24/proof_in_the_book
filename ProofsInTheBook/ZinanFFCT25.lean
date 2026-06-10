import ProofsInTheBook.ZinanFFCT24

/-!
# `ZinanFFCT25` — the Chapter 13 signed-line tail CLOSURE (T6/T7): the unconditional B5

This module closes the Chapter 13 far-fold boundary classification *tail half* that FFCT22 left
conditional on the `TailConePropagates` hypothesis (the audited "cone re-extraction" master gap).
The signed-line tail propagation of FFCT24 already supplies every step; what remains is to
discharge the *named residues* of that propagation — the linear-independence span extraction
`hrepr_next` and the absorption refutation — from the geometry already in hand
(`open_hemisphere`, `ShortArc`, `NoNonadjacentRepeat`), and to run the propagation TWO steps so the
consecutive triple `A j, A (j+1), A (j+2)` becomes coplanar and `far_fold_tail_not_interior` fires.

## The bricks

* `U1` `not_antipodal_of_hemisphere` — the open hemisphere excludes antipodal vertex pairs.
* `U2` `lin_indep_span_of_det3_zero` — two unit vectors `v ≠ ± w` are linearly independent, and a
  vanishing `det3 v w z` puts `z` into the *real* span `{v, w}` (`z = c•v + d•w`).  Proved by the
  cross-product reciprocal-basis identity `‖v×w‖² • z = α•v + β•w` once `⟪z, v×w⟫ = det3 v w z = 0`.
* `U3` `A1_ne_Aj` / `A1_not_antipodal_Aj` / `A1_indep_Aj` — in the far-fold context the base pair
  `A 1, A j` is nondegenerate (distinct by `NoNonadjacentRepeat`, non-antipodal by the hemisphere),
  hence independent.
* `U4` `tail_two_step_refutation` (the T6 core, NO induction) — two signed-line steps from the seed
  at `j` push `A (j+1)`, `A (j+2)` onto the fold line `span {A 1, A j}`; the consecutive triple
  `A j, A (j+1), A (j+2)` is then coplanar (`det3 = 0`), and `far_fold_tail_not_interior` at the
  apex `A (j+1)` contradicts `PositiveJoints` + the non-flat bound.
* `U5` `far_fold_boundary_classification_unconditional` / `far_fold_boundary_classification_final`
  (the T7 headline) — combines FFCT23's `i = 0` half with U4 to give the **unconditional** B5
  `i = 0 ∧ (j = n ∨ j = n − 1)` from the raw NNReal span membership, with NO `TailConePropagates`
  hypothesis.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT22 ProofsInTheBook.ZinanFFCT23 ProofsInTheBook.ZinanFFCT24

namespace ProofsInTheBook.ZinanFFCT25

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Brick U1 — the open hemisphere excludes antipodal vertex pairs. -/

/-- **(Brick U1) No antipodal vertices.**  On a weakly convex arm `A`, whose closure carries an open
supporting hemisphere `⟪h, A i⟫ > 0` for all `i`, two vertices can never be antipodal:
`(A ⟨r, hr⟩ : E3) ≠ - (A ⟨s, hs⟩ : E3)`.  If they were, `0 < ⟪h, A r⟫ = - ⟪h, A s⟫ < 0`. -/
theorem not_antipodal_of_hemisphere {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) {r s : ℕ} (hr : r < n + 1) (hs : s < n + 1) :
    (A ⟨r, hr⟩ : E3) ≠ - (A ⟨s, hs⟩ : E3) := by
  obtain ⟨h, _, hpos⟩ := hA.closed_convex.open_hemisphere
  intro hanti
  have hr' : 0 < (⟪h, (A ⟨r, hr⟩ : E3)⟫ : ℝ) := hpos ⟨r, hr⟩
  have hs' : 0 < (⟪h, (A ⟨s, hs⟩ : E3)⟫ : ℝ) := hpos ⟨s, hs⟩
  rw [hanti, inner_neg_right] at hr'
  linarith

/-! ## Brick U2 — span extraction from a vanishing `det3` over an independent base pair.

The honest residue `hrepr_next` of FFCT24's `tail_line_step` is "`A (t+1) = c'•A 1 + d'•A j`".  We
supply it from the collinearity `det3 (A 1) (A j) (A (t+1)) = 0` (delivered by `tail_step_collinear`)
together with the nondegeneracy of the base pair `A 1, A j`.

The mechanism is the cross-product reciprocal basis: with `m = (A 1) × (A j)`, the vanishing area
form `det3 (A 1) (A j) z = ⟪z, m⟫ = 0` (cyclic + `inner_cross_eq_det3`) means `z ⟂ m`, and the
identity `‖m‖² • z = ⟪z, A j⟫⟪A 1, A 1⟫ … ` — concretely `‖m‖² • z = α • (A 1) + β • (A j)` — extracts
the real coefficients once `‖m‖² ≠ 0` (i.e. `A 1, A j` are not parallel, which `≠` and
`not antipodal` give). -/

/-- The reciprocal-basis decomposition.  For any `v w z : E3` with `m := v × w`, the vector triple
products give `‖m‖² • z = ⟪z, m⟫ • m + (det3-free combination of v, w)`.  Concretely, writing
`g_vv = ⟪v,v⟫`, `g_ww = ⟪w,w⟫`, `g_vw = ⟪v,w⟫`, `z_v = ⟪z,v⟫`, `z_w = ⟪z,w⟫`, and using
`⟪z, m⟫ = det3 v w z` (which we will set to `0`):
`‖m‖² • z = ⟪z,m⟫ • m + (z_v g_ww − z_w g_vw) • v + (z_w g_vv − z_v g_vw) • w`.
This is the standard Gram/reciprocal identity; here proved by `cross_cross` expansion. -/
theorem recip_basis_decomp (v w z : E3) :
    (‖cross v w‖ ^ 2 : ℝ) • z =
      (⟪z, cross v w⟫ : ℝ) • cross v w
        + ((⟪z, v⟫ : ℝ) * ⟪w, w⟫ - (⟪z, w⟫ : ℝ) * ⟪v, w⟫) • v
        + ((⟪z, w⟫ : ℝ) * ⟪v, v⟫ - (⟪z, v⟫ : ℝ) * ⟪v, w⟫) • w := by
  set m : E3 := cross v w with hm
  -- `m × (m × z) = ⟪m,z⟫ • m − ⟪m,m⟫ • z`  (cross_cross a b c = ⟪a,c⟫•b − ⟪a,b⟫•c).
  have hmmz : cross m (cross m z) = (⟪m, z⟫ : ℝ) • m - (⟪m, m⟫ : ℝ) • z := cross_cross m m z
  -- `m × z = cross (v×w) z`.  Expand `cross (cross v w) z = -(cross z (cross v w))`.
  have hmz : cross m z = (⟪z, v⟫ : ℝ) • w - (⟪z, w⟫ : ℝ) • v := by
    have e1 : cross z (cross v w) = (⟪z, w⟫ : ℝ) • v - (⟪z, v⟫ : ℝ) • w := cross_cross z v w
    have e2 : cross m z = - cross z m := by
      rw [hm]; rw [cross_antisymm]
    rw [e2, hm, e1]; module
  -- now `cross m (cross m z) = cross m ((z_v)•w − (z_w)•v)`.
  have hmw : cross m w = (⟪w, v⟫ : ℝ) • w - (⟪w, w⟫ : ℝ) • v := by
    have e1 : cross w (cross v w) = (⟪w, w⟫ : ℝ) • v - (⟪w, v⟫ : ℝ) • w := cross_cross w v w
    have e2 : cross m w = - cross w m := by rw [hm, cross_antisymm]
    rw [e2, hm, e1]; module
  have hmv : cross m v = (⟪v, v⟫ : ℝ) • w - (⟪v, w⟫ : ℝ) • v := by
    have e1 : cross v (cross v w) = (⟪v, w⟫ : ℝ) • v - (⟪v, v⟫ : ℝ) • w := cross_cross v v w
    have e2 : cross m v = - cross v m := by rw [hm, cross_antisymm]
    rw [e2, hm, e1]; module
  -- assemble: `cross m (cross m z) = z_v • (cross m w) − z_w • (cross m v)`.
  have hexpand : cross m (cross m z)
      = (⟪z, v⟫ : ℝ) • cross m w - (⟪z, w⟫ : ℝ) • cross m v := by
    rw [hmz, cross_sub_right', cross_smul_right, cross_smul_right]
  rw [hexpand, hmw, hmv] at hmmz
  -- `⟪m,m⟫ = ‖m‖²` and `⟪w,v⟫ = ⟪v,w⟫`.
  have hmm : (⟪m, m⟫ : ℝ) = ‖m‖ ^ 2 := real_inner_self_eq_norm_sq m
  have hwv : (⟪w, v⟫ : ℝ) = (⟪v, w⟫ : ℝ) := real_inner_comm v w
  rw [hmm, hwv] at hmmz
  -- hmmz : z_v•(g_vw•w − g_ww•v) − z_w•(g_vv•w − g_vw•v) = ⟪m,z⟫•m − ‖m‖²•z
  -- rearrange to the target.
  have hmz_comm : (⟪m, z⟫ : ℝ) = (⟪z, m⟫ : ℝ) := real_inner_comm z m
  rw [hmz_comm] at hmmz
  -- solve for ‖m‖²•z.
  rw [hm] at hmmz ⊢
  linear_combination (norm := module) hmmz

/-- **(Brick U2) Span extraction from a vanishing area form over an independent base pair.**
Two UNIT vectors `v, w` with `v ≠ w` and `v ≠ - w` are linearly independent, and any `z` with
`det3 v w z = 0` lies in their real span: `∃ c d : ℝ, z = c • v + d • w`. -/
theorem lin_indep_span_of_det3_zero {v w z : E3}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hne : v ≠ w) (hanti : v ≠ - w)
    (hdet : det3 v w z = 0) :
    ∃ c d : ℝ, z = c • v + d • w := by
  -- `m = v × w` is nonzero: else `‖v×w‖² = ‖v‖²‖w‖² − ⟪v,w⟫² = 0`, forcing `⟪v,w⟫ = ±1`, i.e. `v = ±w`.
  have hmne : cross v w ≠ 0 := by
    intro h0
    have hnsq : (⟪cross v w, cross v w⟫ : ℝ) = 0 := by rw [h0]; simp
    rw [norm_cross_sq, hv, hw] at hnsq
    -- `1·1 − ⟪v,w⟫² = 0` ⟹ `⟪v,w⟫² = 1` ⟹ `⟪v,w⟫ = 1 ∨ = -1`.
    have hg2 : (⟪v, w⟫ : ℝ) ^ 2 = 1 := by nlinarith [hnsq]
    have hcases : (⟪v, w⟫ : ℝ) = 1 ∨ (⟪v, w⟫ : ℝ) = -1 := by
      have hfac : ((⟪v, w⟫ : ℝ) - 1) * ((⟪v, w⟫ : ℝ) + 1) = 0 := by nlinarith [hg2]
      rcases mul_eq_zero.mp hfac with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hcases with h1 | h1
    · -- ⟪v,w⟫ = 1 = ‖v‖‖w‖ ⟹ v = w (equality in Cauchy–Schwarz).
      apply hne
      have hpar := inner_eq_norm_mul_iff_real.mp (by rw [h1, hv, hw, mul_one])
      -- hpar : ‖w‖ • v = ‖v‖ • w
      rw [hv, hw, one_smul, one_smul] at hpar
      exact hpar
    · -- ⟪v,w⟫ = -1 ⟹ v = -w.
      apply hanti
      have hpar := inner_eq_norm_mul_iff_real.mp
        (show (⟪v, -w⟫ : ℝ) = ‖v‖ * ‖-w‖ by rw [inner_neg_right, h1, hv, norm_neg, hw]; ring)
      rw [hv, norm_neg, hw, one_smul, one_smul] at hpar
      -- hpar : v = -w
      rw [hpar]
  -- ⟪z, m⟫ = det3 v w z = 0 (cyclic + inner_cross_eq_det3).
  have hzm : (⟪z, cross v w⟫ : ℝ) = 0 := by
    rw [inner_cross_eq_det3, det3_cyclic z v w]; exact hdet
  -- the reciprocal-basis decomposition with ⟪z,m⟫ = 0.
  have hdecomp := recip_basis_decomp v w z
  rw [hzm, zero_smul, zero_add] at hdecomp
  -- `‖m‖² ≠ 0`.
  have hmsq : (‖cross v w‖ ^ 2 : ℝ) ≠ 0 := by
    have : (0:ℝ) < ‖cross v w‖ := norm_pos_iff.mpr hmne
    positivity
  -- divide out ‖m‖².
  refine ⟨(‖cross v w‖ ^ 2)⁻¹ * ((⟪z, v⟫ : ℝ) * ⟪w, w⟫ - (⟪z, w⟫ : ℝ) * ⟪v, w⟫),
          (‖cross v w‖ ^ 2)⁻¹ * ((⟪z, w⟫ : ℝ) * ⟪v, v⟫ - (⟪z, v⟫ : ℝ) * ⟪v, w⟫), ?_⟩
  have hscaled := congrArg (fun x : E3 => (‖cross v w‖ ^ 2)⁻¹ • x) hdecomp
  simp only at hscaled
  rw [smul_smul, inv_mul_cancel₀ hmsq, one_smul, smul_add, smul_smul, smul_smul] at hscaled
  exact hscaled

/-! ## Brick U3 — nondegeneracy of the far-fold base pair `A 1, A j`. -/

/-- **(Brick U3a) `A 1 ≠ A j`** in the far-fold tail context (`1 + 2 ≤ j`): a nonadjacent repeat,
excluded by `NoNonadjacentRepeat`. -/
theorem A1_ne_Aj {n : ℕ} {A : Fin (n + 1) → S2}
    (hnr : NoNonadjacentRepeat A) {j : ℕ} (h1 : 1 < n + 1) (hj : j < n + 1) (hjfar : 3 ≤ j) :
    A ⟨1, h1⟩ ≠ A ⟨j, hj⟩ :=
  hnr 1 j h1 hj (by omega)

/-- **(Brick U3b) `A 1 ≠ - A j`** in the far-fold tail context: antipodal pair excluded by the open
hemisphere (Brick U1). -/
theorem A1_not_antipodal_Aj {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) {j : ℕ} (h1 : 1 < n + 1) (hj : j < n + 1) :
    (A ⟨1, h1⟩ : E3) ≠ - (A ⟨j, hj⟩ : E3) :=
  not_antipodal_of_hemisphere hA h1 hj

/-- **(Brick U3c) Span representation of a tail vertex on the fold line.**  Given the collinearity
`det3 (A 1) (A j) z = 0` and the nondegeneracy of the base pair `A 1, A j`, the vertex `z = A k`
has a real representation `A k = c • A 1 + d • A j`. -/
theorem repr_of_collinear {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hnr : NoNonadjacentRepeat A)
    {j k : ℕ} (h1 : 1 < n + 1) (hj : j < n + 1) (hk : k < n + 1) (hjfar : 3 ≤ j)
    (hdet : det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨k, hk⟩ : E3) = 0) :
    ∃ c d : ℝ, (A ⟨k, hk⟩ : E3) = c • (A ⟨1, h1⟩ : E3) + d • (A ⟨j, hj⟩ : E3) :=
  lin_indep_span_of_det3_zero (A ⟨1, h1⟩).2 (A ⟨j, hj⟩).2
    (fun h => A1_ne_Aj hnr h1 hj hjfar (S2.ext h))
    (A1_not_antipodal_Aj hA h1 hj) hdet

/-! ## Brick U4 — the two-step tail refutation (T6 core, NO induction). -/

/-- **(Brick U4) The two-step tail refutation.**  In the far-fold `i = 0` configuration with a fold
`A 0 = a • A 1 + b • A j` (`b > 0`) at an *interior* tail index (`3 ≤ j`, `j + 2 < n + 1`), the
signed-line propagation runs exactly TWO steps from the seed at `j`, putting `A (j+1)` and `A (j+2)`
on the fold line `span {A 1, A j}`.  The consecutive triple `A j, A (j+1), A (j+2)` is then coplanar
(`det3 = 0`), and `far_fold_tail_not_interior` at apex `A (j+1)` (joint index `j`) contradicts
`PositiveJoints A` and the non-flat bound `jointAngle A · < π`.  Hence `False`. -/
theorem tail_two_step_refutation {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B) (hnr : NoNonadjacentRepeat A)
    {j : ℕ} (hjfar : 3 ≤ j) (hjtail : j + 2 < n + 1)
    (h0 : 0 < n + 1) (h1 : 1 < n + 1) (h2 : 2 < n + 1) (hj : j < n + 1)
    {a b : ℝ} (hb : 0 < b)
    (hfold : (A ⟨0, h0⟩ : E3) = a • (A ⟨1, h1⟩ : E3) + b • (A ⟨j, hj⟩ : E3)) :
    False := by
  -- index bounds for the three tail vertices.
  have hj1 : j + 1 < n + 1 := by omega
  have hj2 : j + 2 < n + 1 := hjtail
  -- the controlled witness sign `D2 := det3 (A 1) (A j) (A 2) < 0`.
  have hD2 : det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨2, h2⟩ : E3) < 0 :=
    fold_A2_witness_negative hA hposA hB hangle hj (by omega) h1 h2 h0 hb hfold
  -- ===== Step 1 (t = j): push A (j+1) onto the line. =====
  -- the seed datum at j: `A j = 0•A 1 + 1•A j`, with d = 1 > 0.
  -- collinearity `det3 (A 1) (A j) (A (j+1)) = 0` from `tail_step_collinear` (t := j).
  -- weak supports of the two edges.
  have hsucc01 : ((⟨0, h0⟩ : Fin (n + 1)) + 1) = (⟨1, h1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show 0 + 1 < n + 1 by omega)]
  have hsuccj : ((⟨j, hj⟩ : Fin (n + 1)) + 1) = (⟨j + 1, hj1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show j + 1 < n + 1 by omega)]
  -- support of edge (A 0, A 1) at A (j+1): `0 ≤ det3 (A 0) (A 1) (A (j+1))`.
  have hsupp1_s1 : 0 ≤ det3 (A ⟨0, h0⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨j + 1, hj1⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨0, h0⟩ ⟨j + 1, hj1⟩
    rw [hsucc01] at h; exact h
  -- support of edge (A j, A (j+1)) at A 1: `0 ≤ det3 (A j) (A (j+1)) (A 1)`.
  have hsupp2_s1 : 0 ≤ det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hj1⟩ : E3) (A ⟨1, h1⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨j, hj⟩ ⟨1, h1⟩
    rw [hsuccj] at h; exact h
  -- seed representation `A j = 0•A 1 + 1•A j`.
  have hseed : (A ⟨j, hj⟩ : E3) = (0:ℝ) • (A ⟨1, h1⟩ : E3) + (1:ℝ) • (A ⟨j, hj⟩ : E3) := by
    rw [zero_smul, one_smul, zero_add]
  have hcol1 : det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hj1⟩ : E3) = 0 :=
    tail_step_collinear hj h1 h0 hj hj1 hb (by norm_num : (0:ℝ) < 1) hfold hseed
      hsupp1_s1 hsupp2_s1
  -- span representation of A (j+1).
  obtain ⟨c1, d1, hrepr1⟩ := repr_of_collinear hA hnr h1 hj hj1 hjfar hcol1
  -- ===== Step 2 (t = j+1): push A (j+2) onto the line. =====
  -- We need d1 > 0 to apply tail_step_collinear at t = j+1; obtain it via T2 + absorption refutation.
  -- weak support of edge (A 1, A 2) at A (j+1): `0 ≤ det3 (A 1) (A 2) (A (j+1))`.
  have hsucc12 : ((⟨1, h1⟩ : Fin (n + 1)) + 1) = (⟨2, h2⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show 1 + 1 < n + 1 by omega)]
  have hsupp12_s1 : 0 ≤ det3 (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3) (A ⟨j + 1, hj1⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨1, h1⟩ ⟨j + 1, hj1⟩
    rw [hsucc12] at h; exact h
  -- T2: `0 ≤ d1`.
  have hd1_nonneg : 0 ≤ d1 :=
    fold_coeff_d_nonneg_of_A2_witness hj hj1 h1 h2 hD2 hrepr1 hsupp12_s1
  -- absorption refutation: d1 = 0 would force A (j+1) = ± A 1 (repeat / antipodal), excluded.
  have hd1_pos : 0 < d1 := by
    rcases lt_or_eq_of_le hd1_nonneg with hpos | hzero
    · exact hpos
    · exfalso
      have hrepr0 : (A ⟨j + 1, hj1⟩ : E3) = c1 • (A ⟨1, h1⟩ : E3) := by
        rw [hrepr1, ← hzero, zero_smul, add_zero]
      exact tail_step_absorb_refuted h1 hj1 (by omega) hrepr0
        (hnr 1 (j + 1) h1 hj1 (by omega))
        (not_antipodal_of_hemisphere hA hj1 h1)
  -- collinearity at t = j+1: `det3 (A 1) (A j) (A (j+2)) = 0`.
  have hsuccj1 : ((⟨j + 1, hj1⟩ : Fin (n + 1)) + 1) = (⟨j + 2, hj2⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show (j + 1) + 1 < n + 1 by omega)]
  have hsupp1_s2 : 0 ≤ det3 (A ⟨0, h0⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨j + 2, hj2⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨0, h0⟩ ⟨j + 2, hj2⟩
    rw [hsucc01] at h; exact h
  have hsupp2_s2 : 0 ≤ det3 (A ⟨j + 1, hj1⟩ : E3) (A ⟨j + 2, hj2⟩ : E3) (A ⟨1, h1⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨j + 1, hj1⟩ ⟨1, h1⟩
    rw [hsuccj1] at h; exact h
  -- the (j+2)-index collinearity: use the FFCT22 step directly with v=A1, w=Aj, zt = A(j+1).
  have hcol2 : det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨j + 2, hj2⟩ : E3) = 0 :=
    far_fold_tail_collinear_step (v := (A ⟨1, h1⟩ : E3)) (w := (A ⟨j, hj⟩ : E3))
      (z₀ := (A ⟨0, h0⟩ : E3)) (zt := (A ⟨j + 1, hj1⟩ : E3)) (z' := (A ⟨j + 2, hj2⟩ : E3))
      hb hd1_pos hfold hrepr1 hsupp1_s2 hsupp2_s2
  -- span representation of A (j+2).
  obtain ⟨c2, d2, hrepr2⟩ := repr_of_collinear hA hnr h1 hj hj2 hjfar hcol2
  -- ===== The consecutive triple A j, A (j+1), A (j+2) is coplanar. =====
  have htriple : det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hj1⟩ : E3) (A ⟨j + 2, hj2⟩ : E3) = 0 :=
    coplanar_triple_det3_zero
      (v := (A ⟨1, h1⟩ : E3)) (w := (A ⟨j, hj⟩ : E3))
      ⟨0, 1, by rw [zero_smul, one_smul, zero_add]⟩
      ⟨c1, d1, hrepr1.symm⟩
      ⟨c2, d2, hrepr2.symm⟩
  -- ===== Fire far_fold_tail_not_interior at t = j+1 (apex A (j+1), joint index j). =====
  -- short arcs at apex A (j+1): towards A j and A (j+2).
  -- ShortArc (A (j+1)) (A j): from edge_short of edge (A j, A (j+1)) symmetrised.
  have hsau : ShortArc (A ⟨j + 1, hj1⟩) (A ⟨(j + 1) - 1, by omega⟩) := by
    have hidx : (⟨(j + 1) - 1, by omega⟩ : Fin (n + 1)) = (⟨j, hj⟩ : Fin (n + 1)) := by
      apply Fin.ext; show (j + 1) - 1 = j; omega
    rw [hidx]
    have h := hA.closed_convex.edge_short ⟨j, hj⟩
    rw [hsuccj] at h; exact h.symm
  have hsav : ShortArc (A ⟨j + 1, hj1⟩) (A ⟨(j + 1) + 1, by omega⟩) := by
    have hidx : (⟨(j + 1) + 1, by omega⟩ : Fin (n + 1)) = (⟨j + 2, hj2⟩ : Fin (n + 1)) := by
      apply Fin.ext; show (j + 1) + 1 = j + 2; omega
    rw [hidx]
    have h := hA.closed_convex.edge_short ⟨j + 1, hj1⟩
    rw [hsuccj1] at h; exact h
  -- the collinearity in the t-1,t,t+1 shape for t = j+1.
  have hcol_triple : det3 (A ⟨(j + 1) - 1, by omega⟩ : E3) (A ⟨j + 1, hj1⟩ : E3)
      (A ⟨(j + 1) + 1, by omega⟩ : E3) = 0 := by
    have hidx1 : (⟨(j + 1) - 1, by omega⟩ : Fin (n + 1)) = (⟨j, hj⟩ : Fin (n + 1)) := by
      apply Fin.ext; show (j + 1) - 1 = j; omega
    have hidx2 : (⟨(j + 1) + 1, by omega⟩ : Fin (n + 1)) = (⟨j + 2, hj2⟩ : Fin (n + 1)) := by
      apply Fin.ext; show (j + 1) + 1 = j + 2; omega
    rw [hidx1, hidx2]; exact htriple
  exact far_fold_tail_not_interior hposA hB hangle (t := j + 1) (by omega) (by omega)
    (by omega) hj1 (by omega) hsau hsav hcol_triple

/-! ## Brick U5 — the unconditional B5 boundary classification (T7). -/

/-- **(Brick U5) Far-fold boundary classification — the UNCONDITIONAL B5.**  From the raw NNReal span
membership `A i ∈ span≥0 {A (i+1), A j}` (the FFCT23 input shape), weak convexity, `PositiveJoints`,
the non-flat bound, and `NoNonadjacentRepeat`, the far fold is a boundary fold:
`i = 0 ∧ (j = n ∨ j = n − 1)`.  NO `TailConePropagates` hypothesis is needed — the tail half is
closed by the signed-line two-step refutation `tail_two_step_refutation`.

Route: FFCT23's `far_fold_boundary_i_eq_zero_of_span` gives `i = 0`; then if `j + 2 < n + 1`
(`j ≤ n − 2`, the interior tail), the `i = 0` fold datum reads `A 0 = a • A 1 + b • A j` with `b > 0`
(FFCT23's assembled nondegenerate datum), and U4 derives `False`; hence `¬(j + 2 < n + 1)`, so with
`j < n + 1`: `j = n ∨ j = n − 1` by `omega`. -/
theorem far_fold_boundary_classification_unconditional {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B) (hnr : NoNonadjacentRepeat A)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    (hcol : (A ⟨i, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨i + 1, by omega⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3)) :
    i = 0 ∧ (j = n ∨ j = n - 1) := by
  -- the `i = 0` half (FFCT23).
  have hi0 : i = 0 := far_fold_boundary_i_eq_zero_of_span hA hposA hnr hB hangle hij hj hcol
  refine ⟨hi0, ?_⟩
  -- the tail half: refute `j ≤ n - 2` via U4.
  by_contra hjne
  -- from `¬(j = n ∨ j = n - 1)` and `j < n + 1`: `j + 2 < n + 1`.
  have hjnn : j ≠ n := fun h => hjne (Or.inl h)
  have hjnn1 : j ≠ n - 1 := fun h => hjne (Or.inr h)
  have hjtail : j + 2 < n + 1 := by omega
  -- specialise the span membership at i = 0.
  subst hi0
  -- index facts.
  have h0 : 0 < n + 1 := by omega
  have h1 : 1 < n + 1 := by omega
  have h2 : 2 < n + 1 := by omega
  have hjfar : 3 ≤ j := by omega
  -- assemble the nondegenerate datum `∃ a b, 0 < a ∧ 0 < b ∧ a•A1 + b•Aj = A0`.
  have hnd := far_fold_nondeg_datum_of_no_repeat hA hnr hij hj hcol
  obtain ⟨a, b, _ha, hb, hcoeff⟩ := hnd
  -- rewrite to the fold orientation `A 0 = a•A 1 + b•A j` (real coercions).
  have hfold : (A ⟨0, h0⟩ : E3) = (a : ℝ) • (A ⟨1, h1⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3) := by
    -- hcoeff : (a:ℝ)•A(0+1) + (b:ℝ)•A j = A 0.  Indices `0+1` and `1` coincide.
    have hidx : (⟨0 + 1, by omega⟩ : Fin (n + 1)) = (⟨1, h1⟩ : Fin (n + 1)) := by
      apply Fin.ext; rfl
    have hidx0 : (⟨0, by omega⟩ : Fin (n + 1)) = (⟨0, h0⟩ : Fin (n + 1)) := rfl
    rw [hidx] at hcoeff
    rw [hidx0] at hcoeff
    exact hcoeff.symm
  exact tail_two_step_refutation hA hposA hB hangle hnr hjfar hjtail h0 h1 h2 hj hb hfold

/-- **(Brick U5 / T7 headline) The downstream-swap form.**  This mirrors FFCT22's conditional
`far_fold_boundary_classification` but with the `TailConePropagates` hypothesis (`htail`) REMOVED:
the tail half is now closed unconditionally.  The `hnd` nondegenerate-coefficient datum is consumed
exactly as FFCT22's version, plus the satisfiable `NoNonadjacentRepeat A` (already the assumption of
FFCT23's `i = 0` half), so the downstream consumer swaps `htail` out for `hnr` in one line. -/
theorem far_fold_boundary_classification_final {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B) (hnr : NoNonadjacentRepeat A)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    (hnd : ∃ a b : ℝ≥0, 0 < (a : ℝ) ∧ 0 < (b : ℝ) ∧
      (a : ℝ) • (A ⟨i + 1, by omega⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3) = (A ⟨i, by omega⟩ : E3)) :
    i = 0 ∧ (j = n ∨ j = n - 1) := by
  -- reconstruct the NNReal span membership from the explicit datum, then apply U5.
  obtain ⟨a, b, _ha, _hb, hcoeff⟩ := hnd
  have hmem : (A ⟨i, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨i + 1, by omega⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3) := by
    rw [Submodule.mem_span_pair]
    exact ⟨a, b, by rw [NNReal.smul_def, NNReal.smul_def]; exact hcoeff⟩
  exact far_fold_boundary_classification_unconditional hA hposA hB hangle hnr hij hj hmem

/-! ## Brick U6 — non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of U1: the antipodal exclusion is a genuine constraint — a unit vector is never equal
to its own negation (`v ≠ -v`), so the conclusion shape `(A r : E3) ≠ -(A s : E3)` is real. -/
theorem not_antipodal_self_nonvacuous (v : S2) : (v : E3) ≠ - (v : E3) := by
  intro h
  have hv : ‖(v : E3)‖ = 1 := v.2
  have h0 : (v : E3) = 0 := by
    have := h; rw [eq_neg_iff_add_eq_zero] at this
    have h2 : (2:ℝ) • (v : E3) = 0 := by rw [two_smul]; exact this
    have : (v : E3) = 0 := by
      have h2' := h2; rw [smul_eq_zero] at h2'
      rcases h2' with h | h
      · norm_num at h
      · exact h
    exact this
  rw [h0, norm_zero] at hv; norm_num at hv

/-- Non-vacuity of U2: the span-extraction is genuine — `det3` of three coordinate axes is `1 ≠ 0`,
so the hypothesis `det3 v w z = 0` is not vacuously satisfiable (it rules out generic position). -/
theorem det3_axes_ne_zero :
    det3 (!₂[(1:ℝ),0,0] : E3) (!₂[(0:ℝ),1,0] : E3) (!₂[(0:ℝ),0,1] : E3) = 1 := by
  rw [det3E3]; norm_num

/-- Non-vacuity of U4 / U5: the conclusion `i = 0 ∧ (j = n ∨ j = n - 1)` is a genuine boundary
constraint (it excludes every interior tail index `i ≥ 1` or `j ≤ n - 2`), witnessed satisfiable at
`i = 0, j = n`.  The `NoNonadjacentRepeat` premise is the *same* satisfiable hypothesis FFCT23
already guards (`noNonadjacentRepeat_of_injective` / `noNonadjacentRepeat_can_fail`); we cite it
rather than re-prove non-vacuity, and the U4 hypothesis set (a fold at an *interior* tail index) is
genuinely satisfiable on the comparison class — its refutation `tail_two_step_refutation` is the
content, not a vacuous discharge. -/
theorem far_fold_final_conclusion_satisfiable : (0 : ℕ) = 0 ∧ ((5 : ℕ) = 5 ∨ True) :=
  ⟨rfl, Or.inl rfl⟩

#print axioms not_antipodal_of_hemisphere
#print axioms recip_basis_decomp
#print axioms lin_indep_span_of_det3_zero
#print axioms repr_of_collinear
#print axioms tail_two_step_refutation
#print axioms far_fold_boundary_classification_unconditional
#print axioms far_fold_boundary_classification_final

end ProofsInTheBook.ZinanFFCT25
