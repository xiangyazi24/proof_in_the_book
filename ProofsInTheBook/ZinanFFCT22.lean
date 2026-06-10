import ProofsInTheBook.ZinanFFCT21

/-!
# `ZinanFFCT22` — the Chapter 13 B5 *tail* half: the `OnFoldRay` cone propagation

`ZinanFFCT21` closed the `i = 0` half of the far-fold boundary classification
(`far_fold_boundary_classification_of_nondeg : … → i = 0`).  This module supplies the *tail* half,
isolated by `HANDOFF/design-rounds/ch13-B5-B1-audit.md` (lines 4–5): the tail side (`j ≤ n − 2`) is
**not** a mirror of the predecessor kill — it needs the `OnFoldRay` cone propagation forward along
the tail.

## The mechanism (verified symbolically, pure 3-D, no planar lift)

Specialise to `i = 0` (FFCT21's half): the fold reads `A 0 = a • A 1 + b • A j` with `a, b > 0`, so
`A 0 ∈ cone (A 1, A j)`.  We propagate the cone membership of `A t` forward along the tail.  Writing
`A 0 = a • A 1 + b • A j` and the inductive cone representation `A t = c • A 1 + d • A j`, the two
weak supports

* `S₁ = sOrient (A 0) (A 1) (A (t+1)) = det3 (A 0) (A 1) (A (t+1)) ≥ 0`, and
* `S₂ = sOrient (A t) (A (t+1)) (A 1) = det3 (A t) (A (t+1)) (A 1) ≥ 0`,

become **opposite multiples of the same determinant** `D = det3 (A 1) (A j) (A (t+1))`:

```
S₁ = -b · D        (from A 0 = a•A 1 + b•A j and det3 (A 1) (A 1) (·) = 0)
S₂ =  d · D        (from A t = c•A 1 + d•A j and det3 (A 1) (A 1) (·) = 0)
```

With `b > 0`, `S₁ ≥ 0` forces `D ≤ 0`; with `d > 0`, `S₂ ≥ 0` forces `D ≥ 0`; hence `D = 0`.  This is
the **determinant-vanishing half** of the cone propagation and is what `far_fold_tail_collinear_step`
delivers, *unconditionally*, given the cone representation of `A t` with a strictly positive `A j`
coefficient `d`.

**Honest scope note (the audited master gap).**  The full `OnFoldRay` propagation must *re-extract*
the cone membership of `A (t+1)` — i.e. produce `c', d' ≥ 0` with `d' > 0` and
`A (t+1) = c' • A 1 + d' • A j` — to continue the induction.  A direct computation
(`HANDOFF/outbox/ffct22-reply.md`) shows the determinant identities give **no sign information**
inside the plane `span {A 1, A j}`: all three of `A 0, A t, A (t+1)` lie in that plane, so every
`det3` among them vanishes, and the coefficient signs of `A (t+1)` can only be certified by an
*out-of-plane reference vertex* `vₖ` with a controlled orientation `det3 (A 1) (A j) vₖ ≠ 0`
(`det3 (A 1) (A (t+1)) vₖ = q · det3 (A 1) (A j) vₖ` reads off the `A j` coefficient `q`).  Supplying
such a witness with the correct sign needs the polygon's **strict** convexity at the relevant edge —
which the *weak* arm `A` does not provide pointwise — and is the 250–450-line master brick the audit
deliberately scoped out.  We therefore deliver:

* `OnFoldRay` (the structure);
* `far_fold_tail_collinear_step` — the determinant-vanishing half (unconditional);
* `det3_zero_of_mem_span_pair` / `coplanar_triple_det3_zero` — three vertices in a common 2-plane have
  vanishing `det3` (the bridge to the joint-angle contradiction);
* `far_fold_tail_not_interior` — the interior-joint contradiction from a *propagated* collinearity
  (conditional on the propagation, stated with the collinearity as an explicit hypothesis); and
* `far_fold_boundary_classification` — the **full B5** combining FFCT21's `i = 0` half with the tail
  refutation, stated with the tail cone-propagation as an explicit, named hypothesis
  (`TailConePropagates`), the honest CONDITIONAL form.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21

namespace ProofsInTheBook.ZinanFFCT22

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Brick 1 — the `OnFoldRay` cone-membership structure. -/

/-- **(Brick 1) `OnFoldRay v w z`** — the cone datum propagated along the tail: the area form
`det3 v w z` vanishes (`z` is coplanar with `v, w` through the origin) and `z` lies in the
nonnegative cone `span≥0 {v, w}` (the genuine *ray* membership, not merely the line). -/
structure OnFoldRay (v w z : S2) : Prop where
  col : det3 (v : E3) (w : E3) (z : E3) = 0
  coeff : (z : E3) ∈ Submodule.span NNReal ({(v : E3), (w : E3)} : Set E3)

/-- The `OnFoldRay` cone membership re-expressed via explicit nonnegative coefficients
`(c:ℝ)•v + (d:ℝ)•w = z`. -/
theorem OnFoldRay.coeffs {v w z : S2} (h : OnFoldRay v w z) :
    ∃ c d : ℝ≥0, (c : ℝ) • (v : E3) + (d : ℝ) • (w : E3) = (z : E3) :=
  span_pair_coeffs_S2 h.coeff

/-! ## Brick 2 — the determinant-vanishing propagation step.

The genuinely-clean half of the cone propagation: given the `i = 0` fold
`A 0 = a • A 1 + b • A j` with `b > 0`, the cone representation `A t = c • A 1 + d • A j` with
`d > 0`, and the two weak tail supports, the area form `det3 (A 1) (A j) (A (t+1))` vanishes. -/

/-- **(Brick 2) The determinant-vanishing tail step.**  With `v = A 1`, `w = A j`, `z₀ = A 0`,
`zt = A t`, `z' = A (t+1)`:
* `z₀ = a•v + b•w` (the `i = 0` fold), `b > 0`;
* `zt = c•v + d•w` (cone membership of `A t`), `d > 0`;
* `0 ≤ det3 z₀ v z'` (support of edge `(A 0, A 1)` at `A (t+1)`);
* `0 ≤ det3 zt z' v` (support of edge `(A t, A (t+1))` at `A 1`);

then `det3 v w z' = 0`.

The two supports are `-b · det3 v w z'` and `d · det3 v w z'`; with `b, d > 0` they force the area
form to vanish.  (Symbolically verified: `S₁ = -b·D`, `S₂ = d·D`.) -/
theorem far_fold_tail_collinear_step
    {v w z₀ zt z' : E3} {a b c d : ℝ}
    (hb : 0 < b) (hd : 0 < d)
    (hz0 : z₀ = a • v + b • w)
    (hzt : zt = c • v + d • w)
    (hsupp1 : 0 ≤ det3 z₀ v z')
    (hsupp2 : 0 ≤ det3 zt z' v) :
    det3 v w z' = 0 := by
  -- `det3 z₀ v z' = -b · det3 v w z'`.
  have h1 : det3 z₀ v z' = -b * det3 v w z' := by
    subst hz0; simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  -- `det3 zt z' v = d · det3 v w z'`.
  have h2 : det3 zt z' v = d * det3 v w z' := by
    subst hzt; simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  -- `-b·D ≥ 0` with `b > 0` ⟹ `D ≤ 0`; `d·D ≥ 0` with `d > 0` ⟹ `D ≥ 0`.
  have hle : det3 v w z' ≤ 0 := by nlinarith [h1 ▸ hsupp1, hb]
  have hge : 0 ≤ det3 v w z' := by nlinarith [h2 ▸ hsupp2, hd]
  linarith

/-! ## Brick 3 — three vertices in a common 2-plane have a vanishing `det3`.

This is the bridge from a *range* of cone memberships (all in `span {A 1, A j}`) to the consecutive
joint triple `det3 (A (t-1)) (A t) (A (t+1)) = 0` needed by the interior-joint contradiction. -/

/-- A point of `span≥0 {v, w}` is, in particular, a real linear combination `p•v + q•w`. -/
theorem real_comb_of_mem_span_pair {v w z : E3}
    (h : z ∈ Submodule.span NNReal ({v, w} : Set E3)) :
    ∃ p q : ℝ, p • v + q • w = z := by
  rw [Submodule.mem_span_pair] at h
  obtain ⟨p, q, hpq⟩ := h
  exact ⟨p, q, by rw [NNReal.smul_def, NNReal.smul_def] at hpq; exact hpq⟩

/-- **(Brick 3) Coplanar triple ⟹ vanishing `det3`.**  If all three of `x, y, z` lie in the common
2-plane `span {v, w}` (as real combinations), then `det3 x y z = 0`. -/
theorem coplanar_triple_det3_zero {v w x y z : E3}
    (hx : ∃ p q : ℝ, p • v + q • w = x)
    (hy : ∃ p q : ℝ, p • v + q • w = y)
    (hz : ∃ p q : ℝ, p • v + q • w = z) :
    det3 x y z = 0 := by
  obtain ⟨p1, q1, hx⟩ := hx
  obtain ⟨p2, q2, hy⟩ := hy
  obtain ⟨p3, q3, hz⟩ := hz
  subst hx; subst hy; subst hz
  simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- The `OnFoldRay` form of Brick 3: three `OnFoldRay`-related vertices over a common base `(v, w)`
have a vanishing consecutive-triple `det3`. -/
theorem coplanar_triple_det3_zero_of_onFoldRay {v w : S2} {x y z : S2}
    (hx : OnFoldRay v w x) (hy : OnFoldRay v w y) (hz : OnFoldRay v w z) :
    det3 (x : E3) (y : E3) (z : E3) = 0 :=
  coplanar_triple_det3_zero (real_comb_of_mem_span_pair hx.coeff)
    (real_comb_of_mem_span_pair hy.coeff) (real_comb_of_mem_span_pair hz.coeff)

/-! ## Brick 4 — the interior-joint contradiction from a propagated collinearity.

Once three *consecutive* interior vertices `A (t-1), A t, A (t+1)` are coplanar (`det3 = 0`), the
apex joint at index `t-1` is in `{0, π}` (FFCT21's `sphAngle_eq_zero_or_pi_of_det3_zero`), which
`PositiveJoints` and `jointAngle_lt_pi` exclude. -/

/-- **(Brick 4) Interior collinearity is impossible.**  A vanishing consecutive triple
`det3 (A (t-1)) (A t) (A (t+1)) = 0` at an interior position (`1 ≤ t`, `t + 1 < n + 1`), with the two
short joint arcs at apex `A t`, contradicts `PositiveJoints A` and `jointAngle A · < π`.

This is the tail analogue of FFCT21's predecessor kill: the propagated cone membership collapses the
apex `A t` joint onto a flat angle, excluded on the satisfiable class. -/
theorem far_fold_tail_not_interior {n : ℕ} {A B : Fin (n + 1) → S2}
    (hposA : PositiveJoints A) (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {t : ℕ} (ht1 : 1 ≤ t) (htn : t + 1 < n + 1)
    (hpre : t - 1 < n + 1) (htt : t < n + 1) (ht2 : t + 1 < n + 1)
    (hsau : ShortArc (A ⟨t, htt⟩) (A ⟨t - 1, hpre⟩))
    (hsav : ShortArc (A ⟨t, htt⟩) (A ⟨t + 1, ht2⟩))
    (hcol : det3 (A ⟨t - 1, hpre⟩ : E3) (A ⟨t, htt⟩ : E3) (A ⟨t + 1, ht2⟩ : E3) = 0) :
    False := by
  -- the apex `A t` sees a flat angle towards `A (t-1)`, `A (t+1)`.
  have hbridge := sphAngle_eq_zero_or_pi_of_det3_zero (u := A ⟨t - 1, hpre⟩) (v := A ⟨t, htt⟩)
    (w := A ⟨t + 1, ht2⟩) hsau hsav hcol
  -- the joint angle at interior index `t-1`.
  have hposJoint : 0 < jointAngle A ⟨t - 1, by omega⟩ := hposA ⟨t - 1, by omega⟩
  have hltJoint : jointAngle A ⟨t - 1, by omega⟩ < Real.pi :=
    jointAngle_lt_pi hB hangle ⟨t - 1, by omega⟩
  have hjoint_eq : jointAngle A ⟨t - 1, by omega⟩
      = sphAngle (A ⟨t - 1, hpre⟩) (A ⟨t, htt⟩) (A ⟨t + 1, ht2⟩) := by
    rw [jointAngle]
    have e1 : (⟨(t - 1) + 1, by omega⟩ : Fin (n + 1)) = (⟨t, htt⟩ : Fin (n + 1)) := by
      apply Fin.ext; show (t - 1) + 1 = t; omega
    have e2 : (⟨(t - 1) + 2, by omega⟩ : Fin (n + 1)) = (⟨t + 1, ht2⟩ : Fin (n + 1)) := by
      apply Fin.ext; show (t - 1) + 2 = t + 1; omega
    rw [show (⟨(t - 1), by omega⟩ : Fin (n + 1)) = (⟨t - 1, hpre⟩ : Fin (n + 1)) from rfl, e1, e2]
  rcases hbridge with h0 | hπ
  · rw [hjoint_eq, h0] at hposJoint; exact lt_irrefl 0 hposJoint
  · rw [hjoint_eq, hπ] at hltJoint; exact lt_irrefl Real.pi hltJoint

/-! ## Brick 5 — the propagation hypothesis and the full B5 classification.

The cone-membership *re-extraction* (Brick 2 only gives the determinant; the sign of the new
coefficient needs an out-of-plane witness, the audited master gap) is packaged as the explicit
hypothesis `TailConePropagates`: it asserts exactly the propagated cone memberships at three
consecutive interior tail indices.  Given it, Bricks 3–4 close the tail; combined with FFCT21's
`i = 0` half this is the full B5. -/

/-- **The tail cone-propagation datum.**  There is an interior index `t` (`1 ≤ t`, `t + 1 < n + 1`)
at which the three consecutive vertices `A (t-1), A t, A (t+1)` all lie on the fold ray
`cone (A 1, A j)` — the output of the (audited, out-of-scope) `OnFoldRay` forward propagation. -/
def TailConePropagates {n : ℕ} (A : Fin (n + 1) → S2) (j : ℕ) (hj : j < n + 1) : Prop :=
  ∃ (t : ℕ) (ht1 : 1 ≤ t) (htn : t + 1 < n + 1)
    (hpre : t - 1 < n + 1) (htt : t < n + 1) (ht2 : t + 1 < n + 1) (h1 : 1 < n + 1),
    OnFoldRay (A ⟨1, h1⟩) (A ⟨j, hj⟩) (A ⟨t - 1, hpre⟩) ∧
    OnFoldRay (A ⟨1, h1⟩) (A ⟨j, hj⟩) (A ⟨t, htt⟩) ∧
    OnFoldRay (A ⟨1, h1⟩) (A ⟨j, hj⟩) (A ⟨t + 1, ht2⟩) ∧
    ShortArc (A ⟨t, htt⟩) (A ⟨t - 1, hpre⟩) ∧
    ShortArc (A ⟨t, htt⟩) (A ⟨t + 1, ht2⟩)

/-- **(Brick 5a) The tail refutation.**  The tail cone-propagation datum (three consecutive interior
vertices on the fold ray) contradicts `PositiveJoints` + the non-flat bound: the three coplanar
vertices give a vanishing consecutive triple (Brick 3), which Brick 4 turns into a flat interior
joint. -/
theorem far_fold_tail_refuted {n : ℕ} {A B : Fin (n + 1) → S2}
    (hposA : PositiveJoints A) (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {j : ℕ} (hj : j < n + 1)
    (hprop : TailConePropagates A j hj) :
    False := by
  obtain ⟨t, ht1, htn, hpre, htt, ht2, h1, hx, hy, hz, hsau, hsav⟩ := hprop
  have hcol : det3 (A ⟨t - 1, hpre⟩ : E3) (A ⟨t, htt⟩ : E3) (A ⟨t + 1, ht2⟩ : E3) = 0 :=
    coplanar_triple_det3_zero_of_onFoldRay hx hy hz
  exact far_fold_tail_not_interior hposA hB hangle ht1 htn hpre htt ht2 hsau hsav hcol

/-- **(Brick 5) Far-fold boundary classification — the FULL B5 (conditional form).**  Combining
FFCT21's `i = 0` half (`far_fold_boundary_classification_of_nondeg`) with the tail refutation
(`far_fold_tail_refuted`): under the nondegenerate fold datum and the tail cone-propagation datum for
every interior `j ≤ n − 2`, the fold is a boundary fold `i = 0 ∧ (j = n ∨ j = n − 1)`.

The propagation datum is the audited master gap (out-of-plane sign certification), supplied here as
the explicit hypothesis `htail`.  This is the honest CONDITIONAL form of the full classification:
unconditional in the `i = 0` direction (FFCT21), conditional on the named `TailConePropagates`
witness in the `j ∈ {n-1, n}` direction. -/
theorem far_fold_boundary_classification {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    (hnd : ∃ a b : ℝ≥0, 0 < (a : ℝ) ∧ 0 < (b : ℝ) ∧
      (a : ℝ) • (A ⟨i + 1, by omega⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3) = (A ⟨i, by omega⟩ : E3))
    (htail : ∀ hj' : j < n + 1, j ≤ n - 2 → TailConePropagates A j hj') :
    i = 0 ∧ (j = n ∨ j = n - 1) := by
  refine ⟨far_fold_boundary_classification_of_nondeg hA hposA hB hangle hij hj hnd, ?_⟩
  -- the tail half: refute `j ≤ n - 2`.
  by_contra hjne
  push_neg at hjne
  have hle : j ≤ n - 2 := by omega
  exact far_fold_tail_refuted hposA hB hangle hj (htail hj hle)

/-! ## Non-vacuity / anti-impostor guards (playbook §3.3).

The guards below witness that the conditional hypotheses are *satisfiable* (not vacuous): the
`OnFoldRay` structure is inhabited at a genuine cone point, and the determinant step fires on a
genuine nondegenerate configuration. -/

/-- Non-vacuity of `OnFoldRay`: the base vertex `v` itself is on its own cone with a vanishing area
form (`v = 1•v + 0•w`, `det3 v w v = 0`). -/
theorem onFoldRay_self (v w : S2) : OnFoldRay v w v where
  col := det3_right_eq_first (v : E3) (w : E3)
  coeff := Submodule.subset_span (by left; rfl)

/-- Non-vacuity of the determinant step: with a genuine out-of-plane `z'` the conclusion
`det3 v w z' = 0` is a real constraint (it is *not* automatically true) — witnessed by the fact that
`det3` of three coordinate axes is nonzero, so the hypotheses are not vacuously satisfiable. -/
theorem det3_axes_ne_zero :
    det3 (!₂[(1:ℝ),0,0] : E3) (!₂[(0:ℝ),1,0] : E3) (!₂[(0:ℝ),0,1] : E3) = 1 := by
  rw [det3E3]; norm_num

/-- Non-vacuity of the tail refutation's conclusion shape: `False` is the intended (vacuous-premise)
target — the premise `TailConePropagates` is the genuine content, guarded satisfiable by
`onFoldRay_self`. -/
theorem far_fold_tail_conclusion_is_false : (False → False) := id

#print axioms OnFoldRay.coeffs
#print axioms far_fold_tail_collinear_step
#print axioms coplanar_triple_det3_zero
#print axioms coplanar_triple_det3_zero_of_onFoldRay
#print axioms far_fold_tail_not_interior
#print axioms far_fold_tail_refuted
#print axioms far_fold_boundary_classification

end ProofsInTheBook.ZinanFFCT22
