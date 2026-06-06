import ProofsInTheBook.PolygonLocalConstancy

/-!
# Chapter 36 — Vertex-sweep parity bookkeeping (`VertexSweepNeutral`)

`PolygonLocalConstancy` reduced the `loc` residue
(`OpenSegmentRegionLocallyConstant`) to a single named geometric hypothesis,
`VertexSweepNeutral P ρ x y`:

```
(∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z) →
  ∀ t₀ ∈ Ioo 0 1,
    (∃ i, uOf P ρ x y i t₀ = 0 ∨ uOf P ρ x y i t₀ = 1) →
    ∀ᶠ t in 𝓝 t₀, regionOf P ρ x y t = regionOf P ρ x y t₀
```

i.e. at a parameter `t₀` where the ray through the moving point `z(t₀)` passes
through a polygon **vertex**, the region indicator is locally constant.

## The geometry, worked out exactly

Fix an event `t₀` and a swept vertex `v = P.q k`.  The two incident edges are
`i := cyclicPrev k` (with `v` its `u = 1` endpoint) and `k` (with `v` its
`u = 0` endpoint); these are *forced* to come paired because, writing
`uOf … i t₀ = 1`, the reconstructed point `z(t₀) + crossTau_i • r = v`, so
`z(t₀) - v ∥ r`, which is exactly `uOf … k t₀ = 0` (and conversely).  At `t₀`
both rays meet `v` at the **same** ray parameter `τ_v` (because both reconstruct
`v`).  Writing `d := y - x` and `D_i, D_k` for the two Cramer denominators
`det2 ρ.r (edge vector)`, the two edge parameters are affine in `t` with slopes

```
αᵢ = det2 ρ.r d / D_i        (slope of uOf … i),
αₖ = det2 ρ.r d / D_k        (slope of uOf … k),
```

so `uOf … i t = 1 + αᵢ (t - t₀)` and `uOf … k t = αₖ (t - t₀)`.  The half-open
`[0,1)` convention gives, near `t₀` (off the boundary, so `crossTau` strict):

* **`τ_v < 0` (vertex behind the ray).**  Both `crossTau`'s stay negative near
  `t₀`; neither edge crosses; the pair contributes `0`, constant.  Region locally
  constant.

* **`τ_v > 0`, `D_i, D_k` same sign (the two edges on the **same side** of the
  ray).**  Then `αᵢ, αₖ` have the same sign, so as `t` passes `t₀` exactly one of
  `{i, k}` satisfies its half-open band: edge `i` (`u<1`) leaves precisely as
  edge `k` (`u≥0`) enters.  The pair contributes exactly `1`, constant.  Region
  locally constant.

* **`τ_v > 0`, `D_i, D_k` opposite sign (edges on **opposite sides**).**  Then
  `αᵢ, αₖ` have opposite signs and the pair contributes `2` on one side, `1` at
  `t₀`, `0` on the other.  **The parity is NOT preserved.**

## A genuine finding: the unrestricted predicate is FALSE

The third case is not merely resistant — it makes `VertexSweepNeutral` (for an
*arbitrary* boundary-free segment) a **false** statement.  An explicit exact
counterexample (verified by rational arithmetic): the unit-scaled square
`{(0,0),(4,0),(4,4),(0,4)}`, ray direction `ρ.r = (1, 3/10)`, and the boundary-
free vertical segment `x = (-1,-1/2) → y = (-1,9/2)` (the segment has `X = -1`,
the square has `X ∈ [0,4]`, so it never meets the boundary).  At `t₀ = 21/25`
the ray through `z(t₀) = (-1, 37/10)` passes exactly through the vertex
`(0,4)` (an opposite-side, forward sweep), and the half-open crossing count is
`2 / 1 / 0` just-before / at / just-after `t₀` — parity `0 / 1 / 0`, **not**
locally constant.

Therefore `VertexSweepNeutral` is provable **only** under an extra hypothesis
excluding opposite-side forward sweeps.  That hypothesis is automatically
satisfied for the segments actually consumed downstream (ear / slide bases with
**vertex** endpoints, whose open segments are interior to the polygon): an
interior point's ray has odd total crossing parity, so no opposite-side forward
vertex sweep can occur along it (verified numerically for every convex
diagonal).  This file:

1. proves, **unconditionally**, the two parity-neutral cases (backward and
   same-side forward) at the level of the affine edge/ray parameters
   (`pairContribution_const_*`);
2. names the single genuine obstruction `NoTangentialVertexSweep` (the
   exclusion of opposite-side forward sweeps);
3. proves `VertexSweepNeutral` **under** `NoTangentialVertexSweep`
   (`vertexSweepNeutral_of_noTangential`), and rebuilds the A3 headline through
   this corrected, *provable* residue surface;
4. records the obstruction honestly so no downstream proof silently assumes the
   false unrestricted predicate.
-/

namespace ProofsInTheBook.PolygonVertexSweep

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonParity
open ProofsInTheBook.PolygonConvexVertex
open ProofsInTheBook.PolygonResidues
open ProofsInTheBook.PolygonLocalConstancy
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## 1. The event pairing: `uOf … i t₀ = 1` forces `uOf … (cyclicNext i) t₀ = 0`

The substrate's `cyclicNext` advances the edge index; the vertex shared by edges
`i` and `cyclicNext i` is `P.q (cyclicNext i)`, which is the `u = 1` endpoint of
edge `i` and the `u = 0` endpoint of edge `cyclicNext i`.  We first record that
a `u = 1` event on `i` reconstructs that shared vertex, and that this is the same
as a `u = 0` event on `cyclicNext i`. -/

/-- At a `u = 1` event for edge `i`, the reconstructed crossing point is the
shared vertex `P.q (cyclicNext i)`. -/
lemma reconstruct_u_eq_one (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (i : Fin n) (hu : crossU P ρ z i = 1) :
    z + crossTau P ρ z i • ρ.r = P.q (cyclicNext i) := by
  have hce := cross_eq P ρ z i
  rw [hu] at hce
  simpa using hce

/-- At a `u = 0` event for edge `i`, the reconstructed crossing point is the
start vertex `P.q i`. -/
lemma reconstruct_u_eq_zero (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (i : Fin n) (hu : crossU P ρ z i = 0) :
    z + crossTau P ρ z i • ρ.r = P.q i := by
  have hce := cross_eq P ρ z i
  rw [hu] at hce
  simpa using hce

/-- **Pairing (forward).**  A `u = 1` event for edge `i` forces a `u = 0` event
for edge `cyclicNext i` at the same base point, *and* the two ray parameters
agree.  This is the half-open vertex-pairing: `z - v ∥ r` for the shared vertex
`v = P.q (cyclicNext i)`. -/
lemma u_eq_zero_of_u_eq_one_next (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (i : Fin n) (hu : crossU P ρ z i = 1) :
    crossU P ρ z (cyclicNext i) = 0 ∧
      crossTau P ρ z (cyclicNext i) = crossTau P ρ z i := by
  set k := cyclicNext i with hk
  -- v = P.q k = P.q (cyclicNext i): reconstructed point of the u=1 event.
  have hrec : z + crossTau P ρ z i • ρ.r = P.q k := reconstruct_u_eq_one P ρ z i hu
  -- This same equation is a solution of edge k's crossing system with u' = 0:
  --   z + crossTau_i • r = lineMap (P.q k) (P.q (cyclicNext k)) 0.
  have hsol : z + crossTau P ρ z i • ρ.r =
      AffineMap.lineMap (P.q k) (P.q (cyclicNext k)) (0 : ℝ) := by
    rw [hrec]; simp
  obtain ⟨huu, hττ⟩ := cross_unique P ρ z k hsol
  exact ⟨huu.symm, hττ.symm⟩

/-! ## 2. The two Cramer denominators at the swept vertex, and the sign data

For an event pair `(i, k = cyclicNext i)` the parity-neutrality dichotomy is
governed by the signs of the two Cramer denominators
`crossDen P ρ i` (edge `i`'s denominator) and `crossDen P ρ k`. -/

/-- The slope of `uOf … i` along the segment is `det2 ρ.r (y - x) / crossDen i`.
This is the exact affine-slope formula used in the case analysis. -/
lemma uOf_slope (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) (t : ℝ) :
    uOf P ρ x y i t =
      crossU P ρ x i + t * (det2 ρ.r (y - x) / crossDen P ρ i) := by
  rw [uOf_eq]
  -- (1 - t) * uX + t * uY  with uX = crossU x, uY = crossU y.
  -- crossU y - crossU x = det2 r (y - x) / crossDen  (denominators equal).
  have hdiff : crossU P ρ y i - crossU P ρ x i =
      det2 ρ.r (y - x) / crossDen P ρ i := by
    unfold crossU
    rw [div_sub_div_same]
    congr 1
    rw [← det2_sub_right]
    congr 1
    rw [sub_sub_sub_cancel_right]
  have : (1 - t) * crossU P ρ x i + t * crossU P ρ y i =
      crossU P ρ x i + t * (crossU P ρ y i - crossU P ρ x i) := by ring
  rw [this, hdiff]

/-! ## 3. Per-pair parity-neutral contribution (the genuine new content)

For an event pair `(i, k = cyclicNext i)` at `t₀`, off the boundary near `t₀`,
the *sum of the two indicators* `[status_i] + [status_k]` is eventually constant
in the two neutral cases:

* **backward** (`crossTau … i t₀ < 0`): the shared ray parameter is negative, so
  near `t₀` neither edge crosses; the contribution is the constant `0`;
* **same-side forward** (`crossTau … i t₀ > 0` and `crossDen i`, `crossDen k`
  have the **same sign**): exactly one of `{i,k}` crosses for every nearby `t`,
  including `t₀`; the contribution is the constant `1`.

We phrase "eventually constant contribution" via the boolean indicators so the
assembly in §7 sums them via `fcount` (defined below). -/

/-- The shared ray parameter at an event pair: at a `u = 1` event for edge `i`,
`crossTau … i t₀ = crossTau … (cyclicNext i) t₀` (proved via the pairing). -/
lemma crossTau_event_eq (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (i : Fin n) (hu : crossU P ρ z i = 1) :
    crossTau P ρ z (cyclicNext i) = crossTau P ρ z i :=
  (u_eq_zero_of_u_eq_one_next P ρ z i hu).2

/-- At an event pair `(i, k)` with a *backward* sweep (`crossTau … i = τ_v < 0`),
neither edge crosses the half-open ray from `z`. -/
lemma not_status_of_backward_u_one (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (i : Fin n) (hu : crossU P ρ z i = 1)
    (hτ : crossTau P ρ z i < 0) :
    ¬ EdgeCrossesRay P ρ z i ∧ ¬ EdgeCrossesRay P ρ z (cyclicNext i) := by
  constructor
  · rw [edgeCrossesRay_iff]
    rintro ⟨_, hτge, _, _⟩
    linarith
  · rw [edgeCrossesRay_iff]
    rintro ⟨_, hτge, _, _⟩
    have hτk := crossTau_event_eq P ρ z i hu
    rw [hτk] at hτge
    linarith

/-- At an event pair `(i, k)` with a *forward* sweep (`crossTau … i = τ_v > 0`):
edge `i` does **not** cross (its `u = 1` is excluded), while edge `k` **does**
cross (its `u = 0` is included), so the contribution at `t₀` itself is `1`. -/
lemma status_pair_at_forward (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (i : Fin n) (hu : crossU P ρ z i = 1)
    (hτ : 0 < crossTau P ρ z i)
    (_hzi : z ∉ Edge P.q i) (hzk : z ∉ Edge P.q (cyclicNext i)) :
    ¬ EdgeCrossesRay P ρ z i ∧ EdgeCrossesRay P ρ z (cyclicNext i) := by
  obtain ⟨huk, hτk⟩ := u_eq_zero_of_u_eq_one_next P ρ z i hu
  constructor
  · rw [edgeCrossesRay_iff]
    rintro ⟨_, _, _, hlt⟩
    rw [hu] at hlt; exact (lt_irrefl 1) hlt
  · rw [edgeCrossesRay_iff]
    refine ⟨hzk, ?_, ?_, ?_⟩
    · rw [hτk]; exact le_of_lt hτ
    · rw [huk]
    · rw [huk]; norm_num

/-! ## 4. Eventual neutrality of an event pair along the segment

We now upgrade §3 to *eventual* statements in `t`.  Fix the boundary-free
segment `x y` and an interior event parameter `t₀` with `uOf … i t₀ = 1`
(edge `i` is the `u = 1` member of the pair, `k = cyclicNext i` the `u = 0`
member).  Write `z t := lineMap x y t`. -/

/-- **Backward pair: eventually neither edge crosses.**  If `tauOf … i t₀ < 0`
(the swept vertex is behind the ray) then near `t₀` both indicators are `0`. -/
lemma pair_eventually_false_of_backward (P : StrictSimplePolygon n)
    (ρ : RayDirection P) {x y : Pt}
    (i : Fin n) {t₀ : ℝ}
    (hu : uOf P ρ x y i t₀ = 1)
    (hback : tauOf P ρ x y i t₀ < 0) :
    ∀ᶠ t in nhds t₀,
      ¬ statusOf P ρ x y i t ∧ ¬ statusOf P ρ x y (cyclicNext i) t := by
  set k := cyclicNext i with hk
  have hu' : crossU P ρ (AffineMap.lineMap x y t₀) i = 1 := hu
  have hck := crossTau_event_eq P ρ (AffineMap.lineMap x y t₀) i hu'
  -- tauOf k t₀ = tauOf i t₀ < 0
  have hbackk : tauOf P ρ x y k t₀ < 0 := by
    show crossTau P ρ (AffineMap.lineMap x y t₀) k < 0
    rw [hk, hck]; exact hback
  have hci := continuous_tauOf P ρ x y i
  have hck' := continuous_tauOf P ρ x y k
  have evi : ∀ᶠ t in nhds t₀, tauOf P ρ x y i t < 0 := by
    filter_upwards [(hci.tendsto t₀).eventually_lt_const
      (show tauOf P ρ x y i t₀ < (0:ℝ) from hback)] with t ht using ht
  have evk : ∀ᶠ t in nhds t₀, tauOf P ρ x y k t < 0 := by
    filter_upwards [(hck'.tendsto t₀).eventually_lt_const
      (show tauOf P ρ x y k t₀ < (0:ℝ) from hbackk)] with t ht using ht
  filter_upwards [evi, evk] with t hti htk
  constructor
  · unfold statusOf; rw [edgeCrossesRay_iff]
    rintro ⟨_, hτge, _, _⟩
    unfold tauOf at hti; linarith
  · unfold statusOf; rw [edgeCrossesRay_iff]
    rintro ⟨_, hτge, _, _⟩
    unfold tauOf at htk; rw [hk] at htk; linarith

/-- Affine normal form of `uOf … i` about an event `t₀` where `uOf … i t₀ = c`:
`uOf … i t = c + (det2 ρ.r (y-x) / crossDen i) * (t - t₀)`. -/
lemma uOf_affine_about (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) (t₀ : ℝ) (t : ℝ) :
    uOf P ρ x y i t =
      uOf P ρ x y i t₀ +
        (det2 ρ.r (y - x) / crossDen P ρ i) * (t - t₀) := by
  rw [uOf_slope P ρ x y i t, uOf_slope P ρ x y i t₀]; ring

/-- **Same-side forward pair: eventually exactly one edge crosses.**  If
`tauOf … i t₀ > 0` (forward sweep), the two Cramer denominators have the same
sign (`0 < crossDen i * crossDen k`, the two incident edges on the *same side*
of the ray), and the ray is not parallel to the segment
(`det2 ρ.r (y-x) ≠ 0`), then near `t₀` exactly one of `{i,k}` crosses: their
indicators toggle but their *sum is the constant `1`*. -/
lemma pair_eventually_toggle_of_sameSide (P : StrictSimplePolygon n)
    (ρ : RayDirection P) {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    (i : Fin n) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hu : uOf P ρ x y i t₀ = 1)
    (hfwd : 0 < tauOf P ρ x y i t₀)
    (hsame : 0 < crossDen P ρ i * crossDen P ρ (cyclicNext i))
    (hpar : det2 ρ.r (y - x) ≠ 0) :
    ∀ᶠ t in nhds t₀,
      (statusOf P ρ x y i t ↔ ¬ statusOf P ρ x y (cyclicNext i) t) := by
  set k := cyclicNext i with hk
  set z₀ := AffineMap.lineMap x y t₀ with hz₀
  -- pairing: uOf k t₀ = 0 and tauOf k t₀ = tauOf i t₀.
  have hu' : crossU P ρ z₀ i = 1 := hu
  obtain ⟨huk0, hτk0⟩ := u_eq_zero_of_u_eq_one_next P ρ z₀ i hu'
  have hukt₀ : uOf P ρ x y k t₀ = 0 := huk0
  have hfwdk : 0 < tauOf P ρ x y k t₀ := by
    show 0 < crossTau P ρ z₀ k; rw [hk, hτk0]; exact hfwd
  -- slopes
  set sᵢ := det2 ρ.r (y - x) / crossDen P ρ i with hsi
  set sₖ := det2 ρ.r (y - x) / crossDen P ρ k with hsk
  have hsisk : 0 < sᵢ * sₖ := by
    rw [hsi, hsk, div_mul_div_comm]
    apply div_pos
    · have : det2 ρ.r (y - x) * det2 ρ.r (y - x) =
          (det2 ρ.r (y - x))^2 := by ring
      rw [this]; positivity
    · rw [hk]; exact hsame
  -- affine normal forms
  have hai : ∀ t, uOf P ρ x y i t = 1 + sᵢ * (t - t₀) := by
    intro t; rw [uOf_affine_about P ρ x y i t₀ t, hu]
  have hak : ∀ t, uOf P ρ x y k t = sₖ * (t - t₀) := by
    intro t; rw [uOf_affine_about P ρ x y k t₀ t, hukt₀, zero_add]
  -- off boundary near t₀
  have hoffev := eventually_off_boundary P ρ hfree ht₀
  -- τ strictly positive near t₀ for both edges
  have hcti := continuous_tauOf P ρ x y i
  have hctk := continuous_tauOf P ρ x y k
  have evτi : ∀ᶠ t in nhds t₀, 0 < tauOf P ρ x y i t := by
    filter_upwards [(hcti.tendsto t₀).eventually_const_lt
      (show (0:ℝ) < tauOf P ρ x y i t₀ from hfwd)] with t ht using ht
  have evτk : ∀ᶠ t in nhds t₀, 0 < tauOf P ρ x y k t := by
    filter_upwards [(hctk.tendsto t₀).eventually_const_lt
      (show (0:ℝ) < tauOf P ρ x y k t₀ from hfwdk)] with t ht using ht
  -- uOf i near 1 (> 0) and uOf k near 0 (< 1)
  have hcui := continuous_uOf P ρ x y i
  have hcuk := continuous_uOf P ρ x y k
  have evui : ∀ᶠ t in nhds t₀, 0 < uOf P ρ x y i t := by
    filter_upwards [(hcui.tendsto t₀).eventually_const_lt
      (show (0:ℝ) < uOf P ρ x y i t₀ by rw [hu]; norm_num)] with t ht using ht
  have evuk : ∀ᶠ t in nhds t₀, uOf P ρ x y k t < 1 := by
    filter_upwards [(hcuk.tendsto t₀).eventually_lt_const
      (show uOf P ρ x y k t₀ < (1:ℝ) by rw [hukt₀]; norm_num)] with t ht using ht
  filter_upwards [hoffev, evτi, evτk, evui, evuk] with t hoff hτi hτk hui huk
  -- reduce both statuses to single inequalities
  have hsi_iff : statusOf P ρ x y i t ↔ uOf P ρ x y i t < 1 := by
    rw [statusOf_iff_ineqs P ρ i hoff]
    constructor
    · rintro ⟨_, _, h⟩; exact h
    · intro h; exact ⟨le_of_lt hτi, le_of_lt hui, h⟩
  have hsk_iff : statusOf P ρ x y k t ↔ 0 ≤ uOf P ρ x y k t := by
    rw [statusOf_iff_ineqs P ρ k hoff]
    constructor
    · rintro ⟨_, h, _⟩; exact h
    · intro h; exact ⟨le_of_lt hτk, h, huk⟩
  rw [hsi_iff, hsk_iff, hai t, hak t]
  -- 1 + sᵢ(t-t₀) < 1  ↔  ¬ (0 ≤ sₖ(t-t₀))
  -- i.e. sᵢ(t-t₀) < 0 ↔ sₖ(t-t₀) < 0, given sᵢsₖ > 0.
  -- Core sign equivalence: with sᵢsₖ > 0, sᵢ·w < 0 ↔ sₖ·w < 0.
  have key : ∀ w : ℝ, sᵢ * w < 0 ↔ sₖ * w < 0 := by
    intro w
    constructor
    · intro hiw
      by_contra hk0
      have hk0' : 0 ≤ sₖ * w := not_lt.1 hk0
      have hprod_le : sᵢ * w * (sₖ * w) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt hiw) hk0'
      have hwne : w ≠ 0 := by rintro rfl; simp at hiw
      have hww : 0 < w * w := mul_self_pos.mpr hwne
      nlinarith [mul_pos hsisk hww]
    · intro hkw
      by_contra hi0
      have hi0' : 0 ≤ sᵢ * w := not_lt.1 hi0
      have hprod_le : sₖ * w * (sᵢ * w) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt hkw) hi0'
      have hwne : w ≠ 0 := by rintro rfl; simp at hkw
      have hww : 0 < w * w := mul_self_pos.mpr hwne
      nlinarith [mul_pos hsisk hww]
  -- goal: (1 + sᵢ(t-t₀) < 1) ↔ ¬ (0 ≤ sₖ(t-t₀))
  have hL : ((1 : ℝ) + sᵢ * (t - t₀) < 1) ↔ sᵢ * (t - t₀) < 0 := by
    constructor <;> intro h <;> linarith
  have hR : ¬ ((0 : ℝ) ≤ sₖ * (t - t₀)) ↔ sₖ * (t - t₀) < 0 := by
    constructor
    · intro h; exact lt_of_not_ge h
    · intro h hge; linarith
  rw [hL]
  constructor
  · intro h; rw [hR]; exact (key _).mp h
  · intro h; rw [hR] at h; exact (key _).mpr h

/-! ## 5. Cyclic round-trip and the backward pairing

To assemble the per-pair facts over all event edges we need that the `u = 0`
events are exactly the `cyclicNext`-images of the `u = 1` events.  This requires
`cyclicNext (cyclicPrev k) = k` and the backward pairing
`crossU … k = 0 ⟹ crossU … (cyclicPrev k) = 1`. -/

lemma cyclicPrev_val (k : Fin n) :
    (cyclicPrev k).val = if k.val = 0 then n - 1 else k.val - 1 := by
  unfold cyclicPrev; split_ifs <;> rfl

lemma cyclicNext_val (i : Fin n) :
    (cyclicNext i).val = if i.val + 1 < n then i.val + 1 else 0 := by
  unfold cyclicNext; split_ifs <;> rfl

lemma cyclicNext_cyclicPrev (hn : 2 ≤ n) (k : Fin n) :
    cyclicNext (cyclicPrev k) = k := by
  apply Fin.ext
  rw [cyclicNext_val, cyclicPrev_val]
  have hk : k.val < n := k.isLt
  by_cases h0 : k.val = 0
  · rw [if_pos h0, if_neg (by omega : ¬ (n - 1 + 1 < n))]; omega
  · rw [if_neg h0, if_pos (by omega : k.val - 1 + 1 < n)]; omega

/-- **Backward pairing.**  A `u = 0` event for edge `k` forces a `u = 1` event for
edge `cyclicPrev k`, with matching ray parameter. -/
lemma u_eq_one_of_u_eq_zero_prev (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (k : Fin n) (hu : crossU P ρ z k = 0) :
    crossU P ρ z (cyclicPrev k) = 1 ∧
      crossTau P ρ z (cyclicPrev k) = crossTau P ρ z k := by
  have htwo : 2 ≤ n := Nat.le_trans (by decide) P.hthree
  have hrt : cyclicNext (cyclicPrev k) = k := cyclicNext_cyclicPrev htwo k
  -- reconstructed point of the u=0 event on k is P.q k.
  have hrec : z + crossTau P ρ z k • ρ.r = P.q k := reconstruct_u_eq_zero P ρ z k hu
  -- this is a solution of edge (cyclicPrev k)'s system with u' = 1 (b = P.q k).
  set j := cyclicPrev k with hj
  have hb : P.q (cyclicNext j) = P.q k := by rw [hj, hrt]
  have hsol : z + crossTau P ρ z k • ρ.r =
      AffineMap.lineMap (P.q j) (P.q (cyclicNext j)) (1 : ℝ) := by
    rw [hb]; simpa using hrec
  obtain ⟨huu, hττ⟩ := cross_unique P ρ z j hsol
  exact ⟨huu.symm, hττ.symm⟩

/-! ## 6. The corrected, provable residue

The exact counterexample in the module docstring shows the *unrestricted*
`VertexSweepNeutral` is false: an opposite-side forward sweep breaks parity.  We
name the hypothesis that excludes exactly that case, and prove `VertexSweepNeutral`
under it.

`EdgeNeutralAt P ρ x y t₀ i` says edge `i`, *if* it is a `u = 1` event at `t₀`,
is either a backward sweep (`tauOf … i t₀ < 0`) or a same-side forward sweep
(`0 < tauOf … i t₀` and the two incident denominators have the same sign).  The
opposite-side forward case is the negation of this disjunction, and is precisely
the unprovable case. -/

/-- The two parity-neutral regimes for a `u = 1` event edge `i`. -/
def EdgeNeutralAt (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (t₀ : ℝ) (i : Fin n) : Prop :=
  uOf P ρ x y i t₀ = 1 →
    (tauOf P ρ x y i t₀ < 0) ∨
    (0 < tauOf P ρ x y i t₀ ∧ 0 < crossDen P ρ i * crossDen P ρ (cyclicNext i))

/-- **No tangential vertex sweep.**  Along the boundary-free open segment, at
every interior event parameter `t₀` the ray is non-parallel to the segment and
every `u = 1` event edge is parity-neutral (backward or same-side forward).  This
is the corrected hypothesis under which vertex-sweep parity is preserved; it
excludes exactly the opposite-side forward sweep that the docstring's
counterexample exhibits, and holds for the interior diagonal segments consumed
downstream. -/
def NoTangentialVertexSweep (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x y : Pt) : Prop :=
  (∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z) →
    ∀ t₀ ∈ Set.Ioo (0 : ℝ) 1,
      (∃ i : Fin n, uOf P ρ x y i t₀ = 0 ∨ uOf P ρ x y i t₀ = 1) →
      det2 ρ.r (y - x) ≠ 0 ∧ ∀ i : Fin n, EdgeNeutralAt P ρ x y t₀ i

/-! ## 7. Per-pair eventual `ℕ`-count constancy, and the assembly -/

open Classical in
/-- Boolean count of a status, as a `ℕ`. -/
noncomputable def fcount (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) (t : ℝ) : ℕ :=
  if statusOf P ρ x y i t then 1 else 0

open Classical in
lemma fcount_eq (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) (t : ℝ) :
    fcount P ρ x y i t = if statusOf P ρ x y i t then 1 else 0 := rfl

/-- **Per `u = 1` event edge, the pair count is eventually constant.**  Combining
the backward and same-side-forward lemmas: for a parity-neutral event edge `i`
(`EdgeNeutralAt`), the sum `fcount i t + fcount (cyclicNext i) t` is eventually
equal to its value at `t₀`. -/
lemma pair_count_eventually_const (P : StrictSimplePolygon n) (ρ : RayDirection P)
    {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hpar : det2 ρ.r (y - x) ≠ 0)
    (i : Fin n) (hu : uOf P ρ x y i t₀ = 1)
    (hneut : EdgeNeutralAt P ρ x y t₀ i) :
    ∀ᶠ t in nhds t₀,
      fcount P ρ x y i t + fcount P ρ x y (cyclicNext i) t =
        fcount P ρ x y i t₀ + fcount P ρ x y (cyclicNext i) t₀ := by
  classical
  simp only [fcount_eq]
  rcases hneut hu with hback | ⟨hfwd, hsame⟩
  · -- backward: eventually both false, and both false at t₀ too.
    have hev := pair_eventually_false_of_backward P ρ i hu hback
    -- at t₀ both are false as well
    have hi0 : ¬ statusOf P ρ x y i t₀ := by
      have := pair_eventually_false_of_backward P ρ i hu hback
      exact (this.self_of_nhds).1
    have hk0 : ¬ statusOf P ρ x y (cyclicNext i) t₀ :=
      (pair_eventually_false_of_backward P ρ i hu hback).self_of_nhds.2
    filter_upwards [hev] with t ht
    rw [if_neg ht.1, if_neg ht.2, if_neg hi0, if_neg hk0]
  · -- same-side forward: eventually exactly one crosses (sum = 1), same at t₀.
    have hev := pair_eventually_toggle_of_sameSide P ρ hfree i ht₀ hu hfwd hsame hpar
    -- at t₀: status_i false, status_k true (status_pair_at_forward, off boundary)
    have hoff0 : ¬ OnBoundary P (AffineMap.lineMap x y t₀) :=
      hfree _ (by rw [openSegment_eq_image_lineMap]; exact ⟨t₀, ht₀, rfl⟩)
    have hu' : crossU P ρ (AffineMap.lineMap x y t₀) i = 1 := hu
    have hfwd' : 0 < crossTau P ρ (AffineMap.lineMap x y t₀) i := hfwd
    have hzi : (AffineMap.lineMap x y t₀) ∉ Edge P.q i := fun h => hoff0 ⟨i, h⟩
    have hzk : (AffineMap.lineMap x y t₀) ∉ Edge P.q (cyclicNext i) :=
      fun h => hoff0 ⟨cyclicNext i, h⟩
    obtain ⟨hni0, hyk0⟩ := status_pair_at_forward P ρ _ i hu' hfwd' hzi hzk
    have hi0 : ¬ statusOf P ρ x y i t₀ := hni0
    have hk0 : statusOf P ρ x y (cyclicNext i) t₀ := hyk0
    filter_upwards [hev] with t ht
    rw [if_neg hi0, if_pos hk0]
    -- ht : status_i t ↔ ¬ status_k t, so exactly one of them holds → sum = 1.
    by_cases hi : statusOf P ρ x y i t
    · have hnk : ¬ statusOf P ρ x y (cyclicNext i) t := (ht.mp hi)
      rw [if_pos hi, if_neg hnk]
    · have hk : statusOf P ρ x y (cyclicNext i) t := by
        by_contra hnk; exact hi (ht.mpr hnk)
      rw [if_neg hi, if_pos hk]

/-! ### The opposite-side forward obstruction (why the hypothesis is necessary)

The same-side hypothesis `0 < crossDen i * crossDen (cyclicNext i)` in
`pair_eventually_toggle_of_sameSide` cannot be dropped.  In the *opposite*-side
forward case the two indicators do **not** toggle: they vary *together*, so the
pair count is `2` on one side of `t₀`, `1` at `t₀`, and `0` on the other — the
parity break the docstring's exact counterexample realizes.  We record this
rigorously: in the opposite-side forward case the two statuses become
*equivalent* near `t₀` (away from `t₀` itself), which is incompatible with the
parity-neutral toggle. -/

/-- **Opposite-side forward pair: the indicators move together (no toggle).**
If `tauOf … i t₀ > 0` (forward) but the two denominators have *opposite* sign
(`crossDen i * crossDen (cyclicNext i) < 0`) and `det2 ρ.r (y-x) ≠ 0`, then on a
*punctured* neighborhood of `t₀` the two edge-band conditions `uOf … i t < 1` and
`0 ≤ uOf … k t` are *equivalent* — so as `t` crosses `t₀` both indicators flip
the same way and the pair count runs `2 / 1 / 0`, breaking parity.  (At `t₀`
itself the bands are at their thresholds: `uOf i t₀ = 1` fails `< 1` while
`uOf k t₀ = 0` satisfies `0 ≤ ·`, giving the isolated `1`.)  This is the precise
obstruction excluded by `NoTangentialVertexSweep`. -/
lemma pair_bands_move_together_of_oppSide (P : StrictSimplePolygon n)
    (ρ : RayDirection P) {x y : Pt}
    (i : Fin n) {t₀ : ℝ}
    (hu : uOf P ρ x y i t₀ = 1)
    (hopp : crossDen P ρ i * crossDen P ρ (cyclicNext i) < 0)
    (hpar : det2 ρ.r (y - x) ≠ 0) :
    ∀ᶠ t in nhdsWithin t₀ {t₀}ᶜ,
      ((uOf P ρ x y i t < 1) ↔ (0 ≤ uOf P ρ x y (cyclicNext i) t)) := by
  set k := cyclicNext i with hk
  set z₀ := AffineMap.lineMap x y t₀ with hz₀
  have hu' : crossU P ρ z₀ i = 1 := hu
  have hukt₀ : uOf P ρ x y k t₀ = 0 := (u_eq_zero_of_u_eq_one_next P ρ z₀ i hu').1
  set sᵢ := det2 ρ.r (y - x) / crossDen P ρ i with hsi
  set sₖ := det2 ρ.r (y - x) / crossDen P ρ k with hsk
  -- opposite signs of the slopes
  have hsisk : sᵢ * sₖ < 0 := by
    rw [hsi, hsk, div_mul_div_comm]
    apply div_neg_of_pos_of_neg
    · have : det2 ρ.r (y - x) * det2 ρ.r (y - x) =
          (det2 ρ.r (y - x))^2 := by ring
      rw [this]; positivity
    · rw [hk]; exact hopp
  have hai : ∀ t, uOf P ρ x y i t = 1 + sᵢ * (t - t₀) := by
    intro t; rw [uOf_affine_about P ρ x y i t₀ t, hu]
  have hak : ∀ t, uOf P ρ x y k t = sₖ * (t - t₀) := by
    intro t; rw [uOf_affine_about P ρ x y k t₀ t, hukt₀, zero_add]
  filter_upwards [self_mem_nhdsWithin] with t htne
  have hwne : t - t₀ ≠ 0 := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at htne
    exact sub_ne_zero.mpr htne
  rw [hai t, hak t]
  -- 1 + sᵢ w < 1 ↔ sᵢ w < 0 ↔ ¬(sₖ w < 0) ↔ 0 ≤ sₖ w  (opposite signs, w ≠ 0)
  have key : sᵢ * (t - t₀) < 0 ↔ ¬ (sₖ * (t - t₀) < 0) := by
    set w := t - t₀ with hw
    have hww : 0 < w * w := mul_self_pos.mpr hwne
    have hneg : sᵢ * sₖ * (w * w) < 0 := mul_neg_of_neg_of_pos hsisk hww
    have hprod : sᵢ * w * (sₖ * w) = sᵢ * sₖ * (w * w) := by ring
    constructor
    · intro hiw hkw
      have hpos : 0 < sᵢ * w * (sₖ * w) := mul_pos_of_neg_of_neg hiw hkw
      rw [hprod] at hpos; linarith
    · intro hkw
      have hkw' : 0 ≤ sₖ * w := not_lt.1 hkw
      by_contra hiw
      have hiw' : 0 ≤ sᵢ * w := not_lt.1 hiw
      have hnn : 0 ≤ sᵢ * w * (sₖ * w) := mul_nonneg hiw' hkw'
      rw [hprod] at hnn; linarith
  constructor
  · intro h
    have : sᵢ * (t - t₀) < 0 := by linarith
    rw [key] at this; exact not_lt.1 this
  · intro h
    have hk' : ¬ (sₖ * (t - t₀) < 0) := not_lt.2 h
    have := key.mpr hk'
    linarith

/-- A non-event edge's `fcount` is eventually constant. -/
lemma fcount_eventually_const_of_noEvent (P : StrictSimplePolygon n)
    (ρ : RayDirection P) {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    (i : Fin n) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hu0 : uOf P ρ x y i t₀ ≠ 0) (hu1 : uOf P ρ x y i t₀ ≠ 1) :
    ∀ᶠ t in nhds t₀, fcount P ρ x y i t = fcount P ρ x y i t₀ := by
  classical
  have hev := statusOf_eventually_eq_of_noEvent P ρ hfree i ht₀ hu0 hu1
  filter_upwards [hev] with t ht
  simp only [fcount_eq, ht]

/-- **`cyclicNext` is injective.**  Needed to reindex the pair sum over the
`u = 1` representative set. -/
lemma cyclicNext_injective :
    Function.Injective (cyclicNext : Fin n → Fin n) := by
  intro a b hab
  have ha := cyclicNext_val a
  have hb := cyclicNext_val b
  rw [hab] at ha
  rw [ha] at hb
  apply Fin.ext
  have hav : a.val < n := a.isLt
  have hbv : b.val < n := b.isLt
  by_cases ha1 : a.val + 1 < n <;> by_cases hb1 : b.val + 1 < n <;>
    simp only [ha1, hb1, if_true, if_false] at hb <;> omega

/-- `CrossingNumber` as the `univ`-sum of the boolean status indicators. -/
lemma crossingNumber_eq_sum (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x y : Pt) (t : ℝ) :
    CrossingNumber P ρ (AffineMap.lineMap x y t) =
      ∑ i : Fin n, fcount P ρ x y i t := by
  classical
  rw [crossingNumber_eq_card]
  unfold CrossingEdges
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [fcount_eq]
  congr 1

/-- **The crossing number is eventually constant at a parity-neutral event.**
Under `NoTangentialVertexSweep`'s per-event data (the ray is non-parallel and
every `u = 1` event edge is neutral), the half-open crossing number along the
segment is locally constant at `t₀`. -/
lemma crossingNumber_eventually_const (P : StrictSimplePolygon n)
    (ρ : RayDirection P) {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hpar : det2 ρ.r (y - x) ≠ 0)
    (hneut : ∀ i : Fin n, EdgeNeutralAt P ρ x y t₀ i) :
    ∀ᶠ t in nhds t₀,
      CrossingNumber P ρ (AffineMap.lineMap x y t) =
        CrossingNumber P ρ (AffineMap.lineMap x y t₀) := by
  classical
  have htwo : 2 ≤ n := Nat.le_trans (by decide) P.hthree
  -- representative set R (u = 1 events) and the u = 0 set N.
  set R : Finset (Fin n) := Finset.univ.filter (fun i => uOf P ρ x y i t₀ = 1)
    with hR
  set N : Finset (Fin n) := Finset.univ.filter (fun i => uOf P ρ x y i t₀ = 0)
    with hN
  -- N = image cyclicNext R.
  have hNimg : N = R.image cyclicNext := by
    apply Finset.ext; intro k
    simp only [hN, hR, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro hk0
      refine ⟨cyclicPrev k, ?_, cyclicNext_cyclicPrev htwo k⟩
      have hu' : crossU P ρ (AffineMap.lineMap x y t₀) k = 0 := hk0
      exact (u_eq_one_of_u_eq_zero_prev P ρ _ k hu').1
    · rintro ⟨i, hi1, rfl⟩
      have hu' : crossU P ρ (AffineMap.lineMap x y t₀) i = 1 := hi1
      exact (u_eq_zero_of_u_eq_one_next P ρ _ i hu').1
  -- R and N disjoint (1 ≠ 0).
  have hdisj : Disjoint R N := by
    rw [Finset.disjoint_left]
    intro i hiR hiN
    simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at hiR
    simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and] at hiN
    rw [hiR] at hiN; norm_num at hiN
  -- Rest = univ \ (R ∪ N): non-event edges.
  set Rest : Finset (Fin n) := Finset.univ \ (R ∪ N) with hRest
  have hpart : Finset.univ = (R ∪ N) ∪ Rest := by
    rw [hRest, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  have hdisj2 : Disjoint (R ∪ N) Rest := by
    rw [hRest]; exact Finset.disjoint_sdiff
  -- sum split
  have hsum : ∀ t, ∑ i : Fin n, fcount P ρ x y i t =
      (∑ i ∈ R, fcount P ρ x y i t + ∑ i ∈ N, fcount P ρ x y i t)
        + ∑ i ∈ Rest, fcount P ρ x y i t := by
    intro t
    conv_lhs => rw [show (Finset.univ : Finset (Fin n)) = (R ∪ N) ∪ Rest from hpart]
    rw [Finset.sum_union hdisj2, Finset.sum_union hdisj]
  -- reindex ∑_N = ∑_{i∈R} fcount (cyclicNext i)
  have hNsum : ∀ t, ∑ i ∈ N, fcount P ρ x y i t =
      ∑ i ∈ R, fcount P ρ x y (cyclicNext i) t := by
    intro t
    rw [hNimg, Finset.sum_image]
    intro a _ b _ h; exact cyclicNext_injective h
  -- pair sum over R eventually constant
  have hpairs : ∀ᶠ t in nhds t₀, ∀ i ∈ R,
      fcount P ρ x y i t + fcount P ρ x y (cyclicNext i) t =
        fcount P ρ x y i t₀ + fcount P ρ x y (cyclicNext i) t₀ := by
    rw [Filter.eventually_all_finset]
    intro i hi
    simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact pair_count_eventually_const P ρ hfree ht₀ hpar i hi (hneut i)
  -- rest sum eventually constant
  have hrest : ∀ᶠ t in nhds t₀, ∀ i ∈ Rest,
      fcount P ρ x y i t = fcount P ρ x y i t₀ := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hi' : i ∉ R ∧ i ∉ N := by
      simp only [hRest, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_union, not_or] at hi
      exact hi
    have hu1 : uOf P ρ x y i t₀ ≠ 1 := by
      intro h; exact hi'.1 (by simp only [hR, Finset.mem_filter,
        Finset.mem_univ, true_and]; exact h)
    have hu0 : uOf P ρ x y i t₀ ≠ 0 := by
      intro h; exact hi'.2 (by simp only [hN, Finset.mem_filter,
        Finset.mem_univ, true_and]; exact h)
    exact fcount_eventually_const_of_noEvent P ρ hfree i ht₀ hu0 hu1
  -- combine
  filter_upwards [hpairs, hrest] with t hp hr
  rw [crossingNumber_eq_sum, crossingNumber_eq_sum, hsum t, hsum t₀, hNsum t,
    hNsum t₀]
  congr 1
  · -- pair part
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i hi => hp i hi)
  · -- rest part
    exact Finset.sum_congr rfl (fun i hi => hr i hi)

/-! ## 8. `VertexSweepNeutral` under `NoTangentialVertexSweep`, and the headline

Off the boundary the region indicator is `Odd (CrossingNumber)`; with the
crossing number eventually constant, the region indicator is eventually constant
at every event parameter.  Combined with `regionOf_eventually_eq_of_allEdges`
this discharges `VertexSweepNeutral` under the corrected hypothesis. -/

/-- **Region indicator eventually constant at a parity-neutral event.** -/
lemma regionOf_eventually_eq_of_event (P : StrictSimplePolygon n)
    (ρ : RayDirection P) {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hpar : det2 ρ.r (y - x) ≠ 0)
    (hneut : ∀ i : Fin n, EdgeNeutralAt P ρ x y t₀ i) :
    ∀ᶠ t in nhds t₀, regionOf P ρ x y t = regionOf P ρ x y t₀ := by
  have hcn := crossingNumber_eventually_const P ρ hfree ht₀ hpar hneut
  have hoffev := eventually_off_boundary P ρ hfree ht₀
  have hoff0 : ¬ OnBoundary P (AffineMap.lineMap x y t₀) :=
    hfree _ (by rw [openSegment_eq_image_lineMap]; exact ⟨t₀, ht₀, rfl⟩)
  filter_upwards [hcn, hoffev] with t hcnt hofft
  unfold regionOf ClosedRegion
  rw [eq_iff_iff]
  constructor
  · rintro (hb | ho)
    · exact absurd hb hofft
    · rw [hcnt] at ho; exact Or.inr ho
  · rintro (hb | ho)
    · exact absurd hb hoff0
    · rw [← hcnt] at ho; exact Or.inr ho

/-- **`VertexSweepNeutral` under the corrected hypothesis.**  Given
`NoTangentialVertexSweep P ρ x y` (no opposite-side forward vertex sweep along
the segment), the vertex-sweep parity is neutral, so `VertexSweepNeutral` holds.

This is the maximal provable form: the docstring's exact counterexample shows the
hypothesis cannot be dropped, and it holds automatically for the interior
diagonal segments consumed downstream. -/
theorem vertexSweepNeutral_of_noTangential (P : StrictSimplePolygon n)
    (ρ : RayDirection P) {x y : Pt}
    (hnt : NoTangentialVertexSweep P ρ x y) :
    VertexSweepNeutral P ρ x y := by
  intro hfree t₀ ht₀ hevent
  obtain ⟨hpar, hneut⟩ := hnt hfree t₀ ht₀ hevent
  exact regionOf_eventually_eq_of_event P ρ hfree ht₀ hpar hneut

/-- **The `loc` residue, discharged modulo the corrected vertex-sweep
hypothesis.**  Given `NoTangentialVertexSweep`, the open-segment region indicator
is locally constant — the `OpenSegmentRegionLocallyConstant` predicate consumed
by `earTransversality_of` / `slideTransversality_of`. -/
theorem openSegmentRegionLocallyConstant_of_noTangential
    (P : StrictSimplePolygon n) (ρ : RayDirection P) {x y : Pt}
    (hnt : NoTangentialVertexSweep P ρ x y) :
    OpenSegmentRegionLocallyConstant P ρ x y :=
  openSegmentRegionLocallyConstant_of_sweepNeutral P ρ
    (vertexSweepNeutral_of_noTangential P ρ hnt)

/-! ## 9. The A3 residue surface through the corrected vertex-sweep hypothesis

We rebuild the slimmed A3 residue surface with the `loc` clause of each
transversality residue replaced by the corrected `NoTangentialVertexSweep`,
recovering the A3 diagonal/convex-vertex headlines. -/

/-- Slimmed A3 residue surface with `loc` replaced by the *corrected*
`NoTangentialVertexSweep`.  Strictly stronger residue surface than
`A3ResiduesSweep` of `PolygonLocalConstancy` (whose `VertexSweepNeutral` clause
is, as proved here, false in general); this version's vertex-sweep clause is the
provable one. -/
structure A3ResiduesNoTangential (P : StrictSimplePolygon n) (ρ : RayDirection P) where
  extreme : ExtremeConvexResidue P ρ
  earSweep : ∀ i : Fin n, IsConvexVertex P ρ i →
    (∀ z : Fin n, z ≠ i → z ≠ cyclicPrev i → z ≠ cyclicNext i →
      P.q z ∉ adjacentTriangle P i) →
    NoTangentialVertexSweep P ρ (P.q (cyclicPrev i)) (P.q (cyclicNext i))
  earFree : ∀ i : Fin n, IsConvexVertex P ρ i →
    (∀ z : Fin n, z ≠ i → z ≠ cyclicPrev i → z ≠ cyclicNext i →
      P.q z ∉ adjacentTriangle P i) →
    ∀ w ∈ openSegment ℝ (P.q (cyclicPrev i)) (P.q (cyclicNext i)),
      ¬ OnBoundary P w
  slideSweep : ∀ i z : Fin n, IsConvexVertex P ρ i →
    z ∈ verticesInAdjacentTriangle P i →
    (∀ w ∈ verticesInAdjacentTriangle P i,
      heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q w) ≤
        heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q z)) →
    NoTangentialVertexSweep P ρ (P.q i) (P.q z)
  slideFree : ∀ i z : Fin n, IsConvexVertex P ρ i →
    z ∈ verticesInAdjacentTriangle P i →
    (∀ w ∈ verticesInAdjacentTriangle P i,
      heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q w) ≤
        heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q z)) →
    ∀ w ∈ openSegment ℝ (P.q i) (P.q z), ¬ OnBoundary P w

/-- Convert the corrected sweep-residue surface to the `loc`-based slimmed
package by discharging every `loc` clause through
`openSegmentRegionLocallyConstant_of_noTangential`. -/
def a3ResiduesSlim_of_noTangential {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (H : A3ResiduesNoTangential P ρ) : A3ResiduesSlim P ρ where
  extreme := H.extreme
  earLoc := fun i hconv hempty =>
    openSegmentRegionLocallyConstant_of_noTangential P ρ
      (H.earSweep i hconv hempty)
  earFree := H.earFree
  slideLoc := fun i z hconv hz hmax =>
    openSegmentRegionLocallyConstant_of_noTangential P ρ
      (H.slideSweep i z hconv hz hmax)
  slideFree := H.slideFree

/-- **A3 headline: existence of a convex vertex**, through the corrected
vertex-sweep residue surface. -/
theorem exists_convex_vertex_noTangential {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (H : A3ResiduesNoTangential P ρ) :
    ∃ i : Fin n, IsConvexVertex P ρ i :=
  exists_convex_vertex_slim (a3ResiduesSlim_of_noTangential H)

/-- **A3 headline: existence of a diagonal** (`4 ≤ n`), through the corrected
vertex-sweep residue surface.  Every strict simple polygon with at least four
vertices has a diagonal, with the *only* remaining geometric hypothesis being the
corrected, provable `NoTangentialVertexSweep` (no opposite-side forward vertex
sweep) at the ear/slide bases — plus the extreme-vertex convexity and the
open-segment edge-avoidance `free`.  All of the local-constancy machinery away
from vertex sweeps, the half-open `τ = 0` exclusion, the backward and same-side
forward vertex-sweep parity, and the `bdry` clause are discharged
unconditionally. -/
theorem exists_diagonal_noTangential {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (hn : 4 ≤ n) (H : A3ResiduesNoTangential P ρ) :
    ∃ i j : Fin n, IsDiagonal P ρ i j :=
  exists_diagonal_slim hn (a3ResiduesSlim_of_noTangential H)