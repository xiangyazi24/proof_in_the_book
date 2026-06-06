import ProofsInTheBook.PolygonSeparation

/-!
# Chapter 36 — parity transport across edge-parallel direction walls (`PolygonWall`)

`PolygonIccEngine` proves crossing-parity is constant along a direction *segment*
that stays a genuine ray direction throughout `[0,1]` (`ValidDirPathSeg`).  For two
*arbitrary* valid directions `ρ`, `σ` the connecting segment `r(t) = dirAt ρ.r σ.r t`
generally meets **edge-parallel walls**: parameters `t₀` where some edge `i` has
`dirDen P ρ.r σ.r i t₀ = det2 (r(t₀)) (edgeVec i) = 0`.  At such a `t₀` the segment
engine breaks (`dirTau i` blows up), so `SegmentChain` cannot cross the wall — the
honest residual `PolygonFinish` and `PolygonSeparation` carry.

This module closes that residue **directly**, by analysing the crossing parity as
`r` crosses a wall, with **no** segment-chain hypothesis.  The whole point is that
the *raw* per-edge statistics `rstatusOf` / `rfcount` / `ds0Of` / `ds1Of` /
`dirTau` / `dirDen` of `PolygonIccEngine`/`PolygonRayIndep` are defined for **every**
`t` (no validity proof attached), so we may run the local-constancy assembly at a
wall parameter too — provided we replace the segment engine's `dirTau`-continuity
step (which fails at a wall) by a wall-specific argument.

## The wall analysis (per edge `i`, off-boundary `x`)

Write `f(t) = side r(t) x a`, `g(t) = side r(t) x b` for `a = P.q i`,
`b = P.q (cyclicNext i)`; both are **affine** in `t`, and `g − f = dirDen i`
(also affine), the *wall function* of edge `i`.  Cases at a wall `t₀`
(`dirDen i t₀ = 0`, i.e. `f t₀ = g t₀`):

* **Generic wall** (`x` off edge `i`'s line): `f t₀ = g t₀ ≠ 0`, same sign, so
  `Span (f ·) (g ·)` is **false** in a whole neighbourhood of `t₀` — the edge
  contributes `0` to the crossing count on both sides of the wall.  Locally
  constant, no `dirTau` needed.  (`rfcount_eventually_zero_of_genericWall`.)

* **Degenerate wall** (`x` on edge `i`'s line, off the segment): `f t₀ = g t₀ = 0`.
  Both side functions are affine with a common zero at `t₀`, so `f t = α(t−t₀)`,
  `g t = β(t−t₀)`.  `Span (f t) (g t)` holds iff `f t · g t < 0`, i.e.
  `αβ(t−t₀)² < 0`, i.e. `αβ < 0` — **independent of the side of the wall**.  The
  forward guard `dirTau` flips sign across `t₀`, but the contributions on the two
  sides still match (the span itself is symmetric); we trace the exact statuses.
  (`rfcount_eventually_const_of_degenerateWall`.)

* **Non-wall** (`dirDen i t₀ ≠ 0`): the segment engine's `dirTau`-continuity runs
  verbatim (no validity of the *whole* direction is needed for edge `i` alone, only
  `dirDen i t₀ ≠ 0`); reused as `rfcount_eventually_const_of_noWall_noEvent` and the
  raw vertex-event pairing.

Assembling per-edge / per-pair local constancy over the preconnected `Icc 0 1`
gives `crossingNumber'_wall_parity_const`: the parity at `ρ` equals the parity at
`σ`, hence the fully unconditional `UnconditionalRayIndepInput`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PolygonWall

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonRayIndep
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonIccEngine
open ProofsInTheBook.PolygonFinish
open Filter Topology

noncomputable section

variable {n : ℕ}

/-! ## Part 0: affine side functions and the wall function

`ds0Of`, `ds1Of` are affine in `t`; their difference is `dirDen`. -/

/-- `det2 u (lineMap P Q t)` is affine in `t` (local copy). -/
lemma det2_lineMap (u P Q : Pt) (t : ℝ) :
    det2 u (AffineMap.lineMap P Q t) =
      (1 - t) * det2 u P + t * det2 u Q := by
  rw [AffineMap.lineMap_apply_module]
  unfold det2
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The end-minus-start side difference is the wall function `dirDen` (pointwise). -/
lemma ds1Of_sub_ds0Of (P : StrictSimplePolygon n) (r₁ r₂ x : Pt) (i : Fin n) (t : ℝ) :
    ds1Of P r₁ r₂ x i t - ds0Of P r₁ r₂ x i t = dirDen P r₁ r₂ i t := by
  unfold ds1Of ds0Of dirSide dirDen dirAt side
  rw [← det2_sub_right]
  congr 1
  ext k
  fin_cases k <;> simp [PiLp.sub_apply]

/-- At a wall (`dirDen i t₀ = 0`) the two endpoint side values coincide. -/
lemma ds_eq_at_wall {P : StrictSimplePolygon n} {r₁ r₂ x : Pt} {i : Fin n} {t₀ : ℝ}
    (hwall : dirDen P r₁ r₂ i t₀ = 0) :
    ds0Of P r₁ r₂ x i t₀ = ds1Of P r₁ r₂ x i t₀ := by
  have := ds1Of_sub_ds0Of P r₁ r₂ x i t₀
  rw [hwall] at this
  linarith

/-! ## Part 1: the generic wall (`x` off edge `i`'s line)

At a wall `t₀` with `ds0Of i t₀ ≠ 0`, the two endpoint side values are equal and
nonzero (same sign), so `Span` is false near `t₀`, and edge `i` does not cross —
the count contribution is `0` in a whole neighbourhood. -/

/-- If the span of the two endpoint side values is false at `t`, the raw status is
false (regardless of the forward guard). -/
lemma not_rstatusOf_of_not_span {P : StrictSimplePolygon n} {r₁ r₂ x : Pt}
    {i : Fin n} {t : ℝ}
    (hns : ¬ Span (ds0Of P r₁ r₂ x i t) (ds1Of P r₁ r₂ x i t)) :
    ¬ rstatusOf P r₁ r₂ x i t := by
  rw [rstatusOf_iff]
  rintro ⟨hsp, _⟩
  exact hns hsp

/-- **Generic wall ⟹ no crossing near the wall.**  At a wall `t₀`
(`dirDen i t₀ = 0`) where the start side value is nonzero, the two endpoint side
values are equal and nonzero, hence the same strict sign, so `Span` fails in a
whole neighbourhood and `rfcount i` is eventually `0` at `t₀`. -/
lemma rfcount_eventually_zero_of_genericWall {P : StrictSimplePolygon n} {r₁ r₂ x : Pt}
    {i : Fin n} {t₀ : ℝ}
    (hwall : dirDen P r₁ r₂ i t₀ = 0)
    (h0 : ds0Of P r₁ r₂ x i t₀ ≠ 0) :
    ∀ᶠ t in nhds t₀, rfcount P r₁ r₂ x i t = 0 := by
  classical
  have heq : ds0Of P r₁ r₂ x i t₀ = ds1Of P r₁ r₂ x i t₀ := ds_eq_at_wall hwall
  have h1 : ds1Of P r₁ r₂ x i t₀ ≠ 0 := heq ▸ h0
  -- Span is locally constant near t₀ (both functions nonzero there) and false at t₀.
  have hns0 : ¬ Span (ds0Of P r₁ r₂ x i t₀) (ds1Of P r₁ r₂ x i t₀) := by
    rw [← heq]
    rcases lt_or_gt_of_ne h0 with hlt | hgt
    · exact span_false_same_nonpos hlt.le hlt.le
    · exact span_false_same_pos hgt hgt
  have hspanev := span_const_two_sides (continuous_ds0Of P r₁ r₂ x i)
    (continuous_ds1Of P r₁ r₂ x i) h0 h1
  filter_upwards [hspanev] with t ht
  have hnst : ¬ Span (ds0Of P r₁ r₂ x i t) (ds1Of P r₁ r₂ x i t) := fun hh =>
    hns0 (ht.mp hh)
  rw [rfcount_eq, if_neg (not_rstatusOf_of_not_span hnst)]

/-! ## Part 2: the non-wall boundary obstruction (raw, single-edge)

At a non-wall parameter (`dirDen i t₀ ≠ 0`) the segment engine's
`crossTau = 0 ∧ span ⟹ x ∈ Edge i` obstruction holds for edge `i` *alone*, with no
need for the *whole* direction to be a valid `RayDirection`.  We restate it on the
bare direction vector `r`. -/

/-- Raw edge parameter `u` of the ray/edge intersection on a bare direction `r`
(denominator `det2 r (edgeVec i)`). -/
def rU (P : StrictSimplePolygon n) (r x : Pt) (i : Fin n) : ℝ :=
  det2 r (x - P.q i) / det2 r (P.q (cyclicNext i) - P.q i)

/-- Raw ray parameter `τ` on a bare direction `r`. -/
def rTau (P : StrictSimplePolygon n) (r x : Pt) (i : Fin n) : ℝ :=
  det2 (P.q i - x) (P.q (cyclicNext i) - P.q i) / det2 r (P.q (cyclicNext i) - P.q i)

/-- Raw reconstruction: `x + τ•r = lineMap a b u` when `det2 r (edgeVec i) ≠ 0`.
A copy of `cross_eq` on a bare direction `r` (only `det2 r (edgeVec) ≠ 0` used). -/
lemma r_cross_eq (P : StrictSimplePolygon n) (r x : Pt) (i : Fin n)
    (hDne : det2 r (P.q (cyclicNext i) - P.q i) ≠ 0) :
    x + rTau P r x i • r =
      AffineMap.lineMap (P.q i) (P.q (cyclicNext i)) (rU P r x i) := by
  set a := P.q i
  set b := P.q (cyclicNext i)
  set D := det2 r (b - a) with hD
  set u := rU P r x i with hu
  set τ := rTau P r x i with hτ
  set L : Pt := AffineMap.lineMap a b u with hL
  set w : Pt := (x + τ • r) - L with hw
  have hgoal : x + τ • r = L ↔ w = 0 := by
    rw [hw]; constructor
    · intro h; rw [h]; simp
    · intro h; rw [sub_eq_zero] at h; exact h
  rw [hgoal]
  apply eq_zero_of_det2_eq_zero (u := r) (v := b - a) (w := w)
  · show det2 r (b - a) ≠ 0; rw [← hD]; exact hDne
  · rw [hw, det2_sub_right, det2_add_right, det2_smul_right,
        PolygonLocalConstancy.det2_self, hL, det2_lineMap]
    have hden : det2 r (b - a) = D := hD.symm
    have huD : u * det2 r (b - a) = det2 r (x - a) := by
      rw [hden, hu, rU]; rw [← hD, div_mul_cancel₀]; exact hDne
    rw [det2_sub_right, det2_sub_right] at huD
    linarith [huD]
  · rw [hw, det2_sub_right, det2_add_right, det2_smul_right, hL, det2_lineMap]
    have hbab : det2 (b - a) b = det2 (b - a) a := by
      unfold det2; simp only [PiLp.sub_apply]; ring
    have hdenτ : det2 (b - a) r = -D := by
      rw [hD, det2_antisymm r (b - a), neg_neg]
    have hτval : τ = det2 (a - x) (b - a) / D := by rw [hτ, rTau, ← hD]
    have hτD : τ * det2 (b - a) r = det2 (b - a) (a - x) := by
      rw [hτval, hdenτ]
      have hnum : det2 (a - x) (b - a) = - det2 (b - a) (a - x) := by
        unfold det2; simp only [PiLp.sub_apply]; ring
      rw [hnum, neg_div]; field_simp
    rw [det2_sub_right] at hτD
    rw [hbab]
    linarith [hτD]

/-- `dirTau` is `rTau` at the direction `dirAt r₁ r₂ t`. -/
lemma dirTau_eq_rTau (P : StrictSimplePolygon n) (r₁ r₂ x : Pt) (i : Fin n) (t : ℝ) :
    dirTau P r₁ r₂ x i t = rTau P (dirAt r₁ r₂ t) x i := by
  unfold dirTau rTau dirDen; rfl

/-- `ds0Of` is `side (dirAt r₁ r₂ t) x (P.q i)`. -/
lemma ds0Of_eq_side (P : StrictSimplePolygon n) (r₁ r₂ x : Pt) (i : Fin n) (t : ℝ) :
    ds0Of P r₁ r₂ x i t = side (dirAt r₁ r₂ t) x (P.q i) := rfl

/-- `ds1Of` is `side (dirAt r₁ r₂ t) x (P.q (cyclicNext i))`. -/
lemma ds1Of_eq_side (P : StrictSimplePolygon n) (r₁ r₂ x : Pt) (i : Fin n) (t : ℝ) :
    ds1Of P r₁ r₂ x i t = side (dirAt r₁ r₂ t) x (P.q (cyclicNext i)) := rfl

/-- **Raw boundary obstruction.**  If at a non-wall parameter (`dirDen i t₀ ≠ 0`) the
endpoint sides span the ray line and the forward parameter vanishes, then `x` lies
on edge `i`, hence on the boundary.  Copy of `crossTau_eq_zero_span_imp_onEdge` on a
bare direction. -/
lemma onEdge_of_span_dirTau_zero {P : StrictSimplePolygon n} {r₁ r₂ x : Pt}
    {i : Fin n} {t₀ : ℝ}
    (hDne : dirDen P r₁ r₂ i t₀ ≠ 0)
    (hspan : Span (ds0Of P r₁ r₂ x i t₀) (ds1Of P r₁ r₂ x i t₀))
    (hτ : dirTau P r₁ r₂ x i t₀ = 0) :
    x ∈ Edge P.q i := by
  set r := dirAt r₁ r₂ t₀ with hr
  have hDne' : det2 r (P.q (cyclicNext i) - P.q i) ≠ 0 := by
    rw [hr]; exact hDne
  -- reconstruction at τ = 0: x = lineMap a b u.
  have hce := r_cross_eq P r x i hDne'
  have hτr : rTau P r x i = 0 := by rw [hr, ← dirTau_eq_rTau]; exact hτ
  rw [hτr, zero_smul, add_zero] at hce
  rw [Edge, seg, segment_eq_image_lineMap]
  refine ⟨rU P r x i, ?_, hce.symm⟩
  set D := det2 r (P.q (cyclicNext i) - P.q i) with hD
  have hsa : side r x (P.q i) = - (rU P r x i * D) := by
    rw [rU, ← hD, div_mul_cancel₀ _ hDne']
    unfold side det2
    simp only [PiLp.sub_apply]; ring
  have hsb : side r x (P.q (cyclicNext i)) = (1 - rU P r x i) * D := by
    have hdiff : side r x (P.q (cyclicNext i)) - side r x (P.q i) = D := by
      rw [hD]; unfold side; rw [← det2_sub_right]; congr 1
      ext k; fin_cases k <;> simp [PiLp.sub_apply]
    rw [hsa] at hdiff; linarith [hdiff]
  have hspan' : Span (side r x (P.q i)) (side r x (P.q (cyclicNext i))) := by
    rw [hr]; rw [ds0Of_eq_side, ds1Of_eq_side] at hspan; exact hspan
  rw [hsa, hsb] at hspan'
  unfold Span at hspan'
  set u := rU P r x i with hu
  rcases lt_or_gt_of_ne hDne' with hDneg | hDpos
  · rcases hspan' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> nlinarith
  · rcases hspan' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> nlinarith

/-! ## Part 3: the non-wall local constancy

At a non-wall parameter (`dirDen i t₀ ≠ 0`) the segment engine's `dirTau`-continuity
argument runs in the full `nhds` filter (no `Icc` restriction, since `dirDen i` is
continuous and nonzero at `t₀`).  Two sub-cases: no vertex event (both side functions
nonzero) — single-edge local constancy; vertex event (`ds1Of i t₀ = 0`) — the raw pair
count is parity-constant. -/

/-- `dirTau i` is continuous at a non-wall parameter. -/
lemma continuousAt_dirTau_of_noWall {P : StrictSimplePolygon n} {r₁ r₂ x : Pt}
    {i : Fin n} {t₀ : ℝ} (hDne : dirDen P r₁ r₂ i t₀ ≠ 0) :
    ContinuousAt (dirTau P r₁ r₂ x i) t₀ := by
  unfold dirTau
  exact continuousAt_const.div (continuous_dirDen P r₁ r₂ i).continuousAt hDne

/-- **Non-wall no-event single-edge local constancy.**  At a non-wall parameter
where neither endpoint side function vanishes, the raw status of edge `i` is locally
constant (full `nhds`). -/
lemma rstatusOf_eventually_eq_of_noWall_noEvent {P : StrictSimplePolygon n}
    {r₁ r₂ : Pt} {x : Pt} (hoff : ¬ OnBoundary P x) {i : Fin n} {t₀ : ℝ}
    (hDne : dirDen P r₁ r₂ i t₀ ≠ 0)
    (h0 : ds0Of P r₁ r₂ x i t₀ ≠ 0) (h1 : ds1Of P r₁ r₂ x i t₀ ≠ 0) :
    ∀ᶠ t in nhds t₀, rstatusOf P r₁ r₂ x i t = rstatusOf P r₁ r₂ x i t₀ := by
  classical
  have hspanev := span_const_two_sides (continuous_ds0Of P r₁ r₂ x i)
    (continuous_ds1Of P r₁ r₂ x i) h0 h1
  have hctau := continuousAt_dirTau_of_noWall (P := P) (x := x) hDne
  by_cases hcross : rstatusOf P r₁ r₂ x i t₀
  · obtain ⟨hspan0, hτ0⟩ := (rstatusOf_iff P r₁ r₂ x i t₀).mp hcross
    have hτpos : 0 < dirTau P r₁ r₂ x i t₀ := by
      rcases lt_or_eq_of_le hτ0 with hlt | heq
      · exact hlt
      · exact absurd (onEdge_of_span_dirTau_zero hDne hspan0 heq.symm)
          (fun he => hoff ⟨i, he⟩)
    have evτ : ∀ᶠ t in nhds t₀, 0 < dirTau P r₁ r₂ x i t := by
      filter_upwards [(hctau.tendsto).eventually_const_lt hτpos] with t ht using ht
    filter_upwards [hspanev, evτ] with t hspant hτt
    rw [eq_iff_iff, rstatusOf_iff]
    exact ⟨fun _ => (rstatusOf_iff P r₁ r₂ x i t₀).mp hcross,
      fun _ => ⟨hspant.mpr hspan0, le_of_lt hτt⟩⟩
  · have hcross' : ¬ (Span (ds0Of P r₁ r₂ x i t₀) (ds1Of P r₁ r₂ x i t₀) ∧
        0 ≤ dirTau P r₁ r₂ x i t₀) := fun hh => hcross ((rstatusOf_iff P r₁ r₂ x i t₀).mpr hh)
    by_cases hspan0 : Span (ds0Of P r₁ r₂ x i t₀) (ds1Of P r₁ r₂ x i t₀)
    · have hτneg : dirTau P r₁ r₂ x i t₀ < 0 := by
        by_contra hge; exact hcross' ⟨hspan0, not_lt.1 hge⟩
      have evτ : ∀ᶠ t in nhds t₀, dirTau P r₁ r₂ x i t < 0 := by
        filter_upwards [(hctau.tendsto).eventually_lt_const hτneg] with t ht using ht
      filter_upwards [hspanev, evτ] with t hspant hτt
      rw [eq_iff_iff, rstatusOf_iff]
      exact ⟨fun hh => by exact absurd hh.2 (not_le.2 hτt),
        fun hh => absurd ((rstatusOf_iff P r₁ r₂ x i t₀).mp hh) hcross'⟩
    · filter_upwards [hspanev] with t hspant
      rw [eq_iff_iff, rstatusOf_iff]
      exact ⟨fun hh => absurd (hspant.mp hh.1) hspan0,
        fun hh => absurd ((rstatusOf_iff P r₁ r₂ x i t₀).mp hh) hcross'⟩

/-- Single-edge no-wall no-event `rfcount` local constancy. -/
lemma rfcount_eventually_eq_of_noWall_noEvent {P : StrictSimplePolygon n}
    {r₁ r₂ : Pt} {x : Pt} (hoff : ¬ OnBoundary P x) {i : Fin n} {t₀ : ℝ}
    (hDne : dirDen P r₁ r₂ i t₀ ≠ 0)
    (h0 : ds0Of P r₁ r₂ x i t₀ ≠ 0) (h1 : ds1Of P r₁ r₂ x i t₀ ≠ 0) :
    ∀ᶠ t in nhds t₀, rfcount P r₁ r₂ x i t = rfcount P r₁ r₂ x i t₀ := by
  filter_upwards [rstatusOf_eventually_eq_of_noWall_noEvent hoff hDne h0 h1] with t ht
  rw [rfcount_eq, rfcount_eq, ht]

/-! ### Vertex events at non-wall parameters

At a vertex event (`ds1Of i t₀ = 0`, the shared vertex `c = P.q (cyclicNext i)` on
the ray line) where both incident edges `i` and `k = cyclicNext i` are non-wall, the
raw forward parameters agree and equal the ray parameter `λ` to the shared vertex.
We trace this via the raw reconstruction. -/

/-- At a vertex event for edge `i` (`ds1Of i t₀ = 0`) the raw edge parameter
`rU (dir t₀) x i = 1`. -/
lemma rU_eq_one_of_event {P : StrictSimplePolygon n} {r₁ r₂ x : Pt} {i : Fin n}
    {t₀ : ℝ} (hDne : dirDen P r₁ r₂ i t₀ ≠ 0)
    (hs : ds1Of P r₁ r₂ x i t₀ = 0) :
    rU P (dirAt r₁ r₂ t₀) x i = 1 := by
  set r := dirAt r₁ r₂ t₀ with hr
  have hsc : det2 r (P.q (cyclicNext i) - x) = 0 := by
    have : ds1Of P r₁ r₂ x i t₀ = det2 r (P.q (cyclicNext i) - x) := rfl
    rw [this] at hs; exact hs
  rw [rU]
  have hDne' : det2 r (P.q (cyclicNext i) - P.q i) ≠ 0 := hDne
  rw [div_eq_one_iff_eq hDne']
  -- det2 r (x - a) = det2 r (c - a), since det2 r (c - x) = 0.
  have h1 : det2 r (x - P.q i) = det2 r x - det2 r (P.q i) := det2_sub_right r x (P.q i)
  have h2 : det2 r (P.q (cyclicNext i) - P.q i) =
      det2 r (P.q (cyclicNext i)) - det2 r (P.q i) := det2_sub_right r _ _
  have h3 : det2 r (P.q (cyclicNext i) - x) =
      det2 r (P.q (cyclicNext i)) - det2 r x := det2_sub_right r _ _
  rw [h3] at hsc
  rw [h1, h2]; linarith

/-- At a vertex event for edge `i`, the next edge `k = cyclicNext i` has raw edge
parameter `rU (dir t₀) x k = 0`. -/
lemma rU_eq_zero_of_event_next {P : StrictSimplePolygon n} {r₁ r₂ x : Pt} {i : Fin n}
    {t₀ : ℝ} (hDk : dirDen P r₁ r₂ (cyclicNext i) t₀ ≠ 0)
    (hs : ds1Of P r₁ r₂ x i t₀ = 0) :
    rU P (dirAt r₁ r₂ t₀) x (cyclicNext i) = 0 := by
  set r := dirAt r₁ r₂ t₀ with hr
  have hsc : det2 r (P.q (cyclicNext i) - x) = 0 := by
    have : ds1Of P r₁ r₂ x i t₀ = det2 r (P.q (cyclicNext i) - x) := rfl
    rw [this] at hs; exact hs
  rw [rU]
  have hDne' : det2 r (P.q (cyclicNext (cyclicNext i)) - P.q (cyclicNext i)) ≠ 0 := hDk
  rw [div_eq_zero_iff]; left
  -- det2 r (x - c) = -det2 r (c - x) = 0.
  have hneg : det2 r (x - P.q (cyclicNext i)) = - det2 r (P.q (cyclicNext i) - x) := by
    unfold det2; simp only [PiLp.sub_apply]; ring
  rw [hneg, hsc, neg_zero]

/-- `dirAt r₁ r₂ t₀ ≠ 0` at a non-wall parameter (the wall function is `det2 dir ev`,
which would vanish if `dir = 0`). -/
lemma dirAt_ne_zero_of_noWall {P : StrictSimplePolygon n} {r₁ r₂ : Pt} {i : Fin n}
    {t₀ : ℝ} (hDne : dirDen P r₁ r₂ i t₀ ≠ 0) : dirAt r₁ r₂ t₀ ≠ 0 := by
  intro hz
  apply hDne
  unfold dirDen
  rw [hz, det2_zero_left]

/-- **Event reconstruction at the shared vertex.**  At a vertex event for edge `i`
(`ds1Of i t₀ = 0`) with both incident edges non-wall, the ray from `x` reaches the
shared vertex `c = P.q (cyclicNext i)` at the common parameter `rTau i = rTau k`, and
`x + (rTau i)•dir = c`. -/
lemma event_reaches_vertex {P : StrictSimplePolygon n} {r₁ r₂ x : Pt} {i : Fin n}
    {t₀ : ℝ} (hDi : dirDen P r₁ r₂ i t₀ ≠ 0)
    (hDk : dirDen P r₁ r₂ (cyclicNext i) t₀ ≠ 0)
    (hs : ds1Of P r₁ r₂ x i t₀ = 0) :
    x + rTau P (dirAt r₁ r₂ t₀) x i • (dirAt r₁ r₂ t₀) = P.q (cyclicNext i) ∧
    x + rTau P (dirAt r₁ r₂ t₀) x (cyclicNext i) • (dirAt r₁ r₂ t₀)
      = P.q (cyclicNext i) := by
  set r := dirAt r₁ r₂ t₀ with hr
  have hDi' : det2 r (P.q (cyclicNext i) - P.q i) ≠ 0 := hDi
  have hDk' : det2 r (P.q (cyclicNext (cyclicNext i)) - P.q (cyclicNext i)) ≠ 0 := hDk
  have hcei := r_cross_eq P r x i hDi'
  have hcek := r_cross_eq P r x (cyclicNext i) hDk'
  rw [rU_eq_one_of_event hDi hs] at hcei
  rw [rU_eq_zero_of_event_next hDk hs] at hcek
  simp only [AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero] at hcei hcek
  exact ⟨hcei, hcek⟩

/-- At a vertex event (both edges non-wall) the two raw forward parameters agree. -/
lemma dirTau_event_eq {P : StrictSimplePolygon n} {r₁ r₂ x : Pt} {i : Fin n}
    {t₀ : ℝ} (hDi : dirDen P r₁ r₂ i t₀ ≠ 0)
    (hDk : dirDen P r₁ r₂ (cyclicNext i) t₀ ≠ 0)
    (hs : ds1Of P r₁ r₂ x i t₀ = 0) :
    dirTau P r₁ r₂ x i t₀ = dirTau P r₁ r₂ x (cyclicNext i) t₀ := by
  obtain ⟨hi, hk⟩ := event_reaches_vertex hDi hDk hs
  have hrne : dirAt r₁ r₂ t₀ ≠ 0 := dirAt_ne_zero_of_noWall hDi
  rw [dirTau_eq_rTau, dirTau_eq_rTau]
  -- (rTau i - rTau k) • dir = 0 ⟹ rTau i = rTau k.
  have hsub : (rTau P (dirAt r₁ r₂ t₀) x i -
      rTau P (dirAt r₁ r₂ t₀) x (cyclicNext i)) • (dirAt r₁ r₂ t₀) = 0 := by
    rw [sub_smul]
    have : rTau P (dirAt r₁ r₂ t₀) x i • dirAt r₁ r₂ t₀ =
        rTau P (dirAt r₁ r₂ t₀) x (cyclicNext i) • dirAt r₁ r₂ t₀ := by
      have e1 : rTau P (dirAt r₁ r₂ t₀) x i • dirAt r₁ r₂ t₀ = P.q (cyclicNext i) - x := by
        rw [← hi]; abel
      have e2 : rTau P (dirAt r₁ r₂ t₀) x (cyclicNext i) • dirAt r₁ r₂ t₀
          = P.q (cyclicNext i) - x := by rw [← hk]; abel
      rw [e1, e2]
    rw [this]; abel
  rcases smul_eq_zero.mp hsub with hc | hc
  · linarith [hc]
  · exact absurd hc hrne

/-- At a vertex event (edge `i` non-wall) the forward parameter is nonzero off the
boundary (else the ray reaches the vertex at `τ = 0`, i.e. `x` is that vertex). -/
lemma dirTau_event_ne_zero {P : StrictSimplePolygon n} {r₁ r₂ x : Pt}
    (hoff : ¬ OnBoundary P x) {i : Fin n} {t₀ : ℝ}
    (hDi : dirDen P r₁ r₂ i t₀ ≠ 0)
    (hDk : dirDen P r₁ r₂ (cyclicNext i) t₀ ≠ 0)
    (hs : ds1Of P r₁ r₂ x i t₀ = 0) :
    dirTau P r₁ r₂ x i t₀ ≠ 0 := by
  intro h0
  obtain ⟨hi, _⟩ := event_reaches_vertex hDi hDk hs
  rw [dirTau_eq_rTau] at h0
  rw [h0, zero_smul, add_zero] at hi
  apply hoff
  refine ⟨cyclicNext i, ?_⟩
  rw [hi, Edge]; exact left_mem_segment ℝ _ _

/-- The far endpoints at a non-wall vertex event are off the ray line. -/
lemma noWall_event_far_ne {P : StrictSimplePolygon n} {r₁ r₂ x : Pt} {i : Fin n}
    {t₀ : ℝ} (hDi : dirDen P r₁ r₂ i t₀ ≠ 0)
    (hDk : dirDen P r₁ r₂ (cyclicNext i) t₀ ≠ 0)
    (hs : ds1Of P r₁ r₂ x i t₀ = 0) :
    ds0Of P r₁ r₂ x i t₀ ≠ 0 ∧ ds1Of P r₁ r₂ x (cyclicNext i) t₀ ≠ 0 := by
  constructor
  · -- dirDen i = ds1Of i - ds0Of i = -ds0Of i, nonzero ⟹ ds0Of i ≠ 0.
    intro h0
    apply hDi
    have := ds1Of_sub_ds0Of P r₁ r₂ x i t₀
    rw [hs, h0] at this; linarith
  · -- dirDen k = ds1Of k - ds0Of k, ds0Of k = ds1Of i = 0 ⟹ ds1Of k = dirDen k ≠ 0.
    intro hk
    apply hDk
    have hshare : ds0Of P r₁ r₂ x (cyclicNext i) t₀ = ds1Of P r₁ r₂ x i t₀ := rfl
    have := ds1Of_sub_ds0Of P r₁ r₂ x (cyclicNext i) t₀
    rw [hk, hshare, hs] at this; linarith

/-- **Non-wall vertex-event pair-count parity constancy.**  At a vertex event for
edge `i` (both incident edges non-wall, `x` off boundary), the raw pair count
`rfcount i + rfcount k` has eventually-constant parity at `t₀` (full `nhds`). -/
lemma rpair_count_eventually_const_noWall {P : StrictSimplePolygon n} {r₁ r₂ : Pt}
    {x : Pt} (hoff : ¬ OnBoundary P x) {t₀ : ℝ} {i : Fin n}
    (hDi : dirDen P r₁ r₂ i t₀ ≠ 0)
    (hDk : dirDen P r₁ r₂ (cyclicNext i) t₀ ≠ 0)
    (hs : ds1Of P r₁ r₂ x i t₀ = 0) :
    ∀ᶠ t in nhds t₀,
      (rfcount P r₁ r₂ x i t + rfcount P r₁ r₂ x (cyclicNext i) t) % 2 =
        (rfcount P r₁ r₂ x i t₀ + rfcount P r₁ r₂ x (cyclicNext i) t₀) % 2 := by
  classical
  simp only [rfcount_eq]
  set k := cyclicNext i with hk
  obtain ⟨ha, hb⟩ := noWall_event_far_ne hDi hDk hs
  have hτeq := dirTau_event_eq hDi hDk hs
  have hτvne := dirTau_event_ne_zero hoff hDi hDk hs
  have hctau_i := continuousAt_dirTau_of_noWall (P := P) (x := x) hDi
  have hctau_k := continuousAt_dirTau_of_noWall (P := P) (x := x) hDk
  have hshare : ∀ t, ds1Of P r₁ r₂ x i t = ds0Of P r₁ r₂ x k t := fun _ => rfl
  have hca := (continuous_ds0Of P r₁ r₂ x i).continuousAt (x := t₀)
  have hcb := (continuous_ds1Of P r₁ r₂ x k).continuousAt (x := t₀)
  have eva : ∀ᶠ t in nhds t₀, ds0Of P r₁ r₂ x i t ≠ 0 := by
    rcases lt_or_gt_of_ne ha with hlt | hgt
    · filter_upwards [hca.tendsto.eventually_lt_const hlt] with t ht using ne_of_lt ht
    · filter_upwards [hca.tendsto.eventually_const_lt hgt] with t ht using ne_of_gt ht
  have evb : ∀ᶠ t in nhds t₀, ds1Of P r₁ r₂ x k t ≠ 0 := by
    rcases lt_or_gt_of_ne hb with hlt | hgt
    · filter_upwards [hcb.tendsto.eventually_lt_const hlt] with t ht using ne_of_lt ht
    · filter_upwards [hcb.tendsto.eventually_const_lt hgt] with t ht using ne_of_gt ht
  rcases lt_or_gt_of_ne hτvne with hback | hfwd
  · -- backward: both forward guards fail near t₀.
    have hτi0 : dirTau P r₁ r₂ x i t₀ < 0 := hback
    have hτk0 : dirTau P r₁ r₂ x k t₀ < 0 := by rw [← hτeq]; exact hback
    have evτi : ∀ᶠ t in nhds t₀, dirTau P r₁ r₂ x i t < 0 := by
      filter_upwards [hctau_i.tendsto.eventually_lt_const hτi0] with t ht using ht
    have evτk : ∀ᶠ t in nhds t₀, dirTau P r₁ r₂ x k t < 0 := by
      filter_upwards [hctau_k.tendsto.eventually_lt_const hτk0] with t ht using ht
    have hfalse : ∀ t, dirTau P r₁ r₂ x i t < 0 → ¬ rstatusOf P r₁ r₂ x i t := by
      intro t hτ hst; rw [rstatusOf_iff] at hst; linarith [hst.2]
    have hfalsek : ∀ t, dirTau P r₁ r₂ x k t < 0 → ¬ rstatusOf P r₁ r₂ x k t := by
      intro t hτ hst; rw [rstatusOf_iff] at hst; linarith [hst.2]
    filter_upwards [evτi, evτk] with t hτi hτk
    rw [if_neg (hfalse t hτi), if_neg (hfalsek t hτk),
        if_neg (hfalse t₀ hτi0), if_neg (hfalsek t₀ hτk0)]
  · -- forward: span_mod_two_through_vertex neutralizes the event.
    have hτi0 : 0 < dirTau P r₁ r₂ x i t₀ := hfwd
    have hτk0 : 0 < dirTau P r₁ r₂ x k t₀ := by rw [← hτeq]; exact hfwd
    have evτi : ∀ᶠ t in nhds t₀, 0 < dirTau P r₁ r₂ x i t := by
      filter_upwards [hctau_i.tendsto.eventually_const_lt hτi0] with t ht using ht
    have evτk : ∀ᶠ t in nhds t₀, 0 < dirTau P r₁ r₂ x k t := by
      filter_upwards [hctau_k.tendsto.eventually_const_lt hτk0] with t ht using ht
    have hstatus_i : ∀ t, 0 < dirTau P r₁ r₂ x i t →
        (if rstatusOf P r₁ r₂ x i t then 1 else 0) =
          (if Span (ds0Of P r₁ r₂ x i t) (ds1Of P r₁ r₂ x i t) then 1 else 0) := by
      intro t hτ
      by_cases hsp : Span (ds0Of P r₁ r₂ x i t) (ds1Of P r₁ r₂ x i t)
      · rw [if_pos hsp, if_pos (by rw [rstatusOf_iff]; exact ⟨hsp, le_of_lt hτ⟩)]
      · rw [if_neg hsp, if_neg (by rw [rstatusOf_iff]; rintro ⟨hh, _⟩; exact hsp hh)]
    have hstatus_k : ∀ t, 0 < dirTau P r₁ r₂ x k t →
        (if rstatusOf P r₁ r₂ x k t then 1 else 0) =
          (if Span (ds0Of P r₁ r₂ x k t) (ds1Of P r₁ r₂ x k t) then 1 else 0) := by
      intro t hτ
      by_cases hsp : Span (ds0Of P r₁ r₂ x k t) (ds1Of P r₁ r₂ x k t)
      · rw [if_pos hsp, if_pos (by rw [rstatusOf_iff]; exact ⟨hsp, le_of_lt hτ⟩)]
      · rw [if_neg hsp, if_neg (by rw [rstatusOf_iff]; rintro ⟨hh, _⟩; exact hsp hh)]
    have hAB_iff : ∀ t, ds0Of P r₁ r₂ x i t ≠ 0 → ds1Of P r₁ r₂ x k t ≠ 0 →
        ((if Span (ds0Of P r₁ r₂ x i t) (ds1Of P r₁ r₂ x i t) then 1 else 0) +
          (if Span (ds0Of P r₁ r₂ x k t) (ds1Of P r₁ r₂ x k t) then 1 else 0)) % 2 =
          (if Span (ds0Of P r₁ r₂ x i t) (ds1Of P r₁ r₂ x k t) then 1 else 0) := by
      intro t hat hbt
      rw [← hshare t]
      exact span_mod_two_through_vertex hat hbt
    have hABev : ∀ᶠ t in nhds t₀,
        (Span (ds0Of P r₁ r₂ x i t) (ds1Of P r₁ r₂ x k t) ↔
          Span (ds0Of P r₁ r₂ x i t₀) (ds1Of P r₁ r₂ x k t₀)) :=
      span_const_two_sides
        (continuous_ds0Of P r₁ r₂ x i) (continuous_ds1Of P r₁ r₂ x k) ha hb
    filter_upwards [evτi, evτk, eva, evb, hABev] with t hτi hτk hat hbt hABt
    have key : ((if rstatusOf P r₁ r₂ x i t then 1 else 0) +
        (if rstatusOf P r₁ r₂ x k t then 1 else 0)) % 2 =
        (if Span (ds0Of P r₁ r₂ x i t₀) (ds1Of P r₁ r₂ x k t₀) then 1 else 0) := by
      rw [hstatus_i t hτi, hstatus_k t hτk, hAB_iff t hat hbt]
      by_cases hsp : Span (ds0Of P r₁ r₂ x i t) (ds1Of P r₁ r₂ x k t)
      · rw [if_pos hsp, if_pos (hABt.mp hsp)]
      · rw [if_neg hsp, if_neg (fun hc => hsp (hABt.mpr hc))]
    have key0 : ((if rstatusOf P r₁ r₂ x i t₀ then 1 else 0) +
        (if rstatusOf P r₁ r₂ x k t₀ then 1 else 0)) % 2 =
        (if Span (ds0Of P r₁ r₂ x i t₀) (ds1Of P r₁ r₂ x k t₀) then 1 else 0) := by
      rw [hstatus_i t₀ hτi0, hstatus_k t₀ hτk0, hAB_iff t₀ ha hb]
    rw [key, key0]

/-! ## Part 4: the degenerate wall (`x` on edge `i`'s line)

At a wall `t₀` where BOTH endpoint side values vanish (`ds0Of i t₀ = ds1Of i t₀ = 0`),
the direction `dir(t₀)` is parallel to both `a − x` and `b − x`, so `a, b, x` are
collinear: `x` is on edge `i`'s line.  Off the boundary, `x` is outside the segment
`[a,b]`, so writing `a − x = μ • (b − x)` we have `μ > 0` (else `x ∈ [a,b]` is on the
boundary).  The two side functions then satisfy `ds0Of i = μ • ds1Of i` pointwise with
`μ > 0`, hence never straddle: `Span` is false everywhere and `rfcount i ≡ 0`. -/

/-- Two vectors both `det2`-orthogonal to a nonzero `r` are parallel: there is `μ`
with `u = μ • w'` provided `det2 r u = 0`, `det2 r w' = 0`, `r ≠ 0`, `w' ≠ 0`. -/
lemma exists_smul_of_det2_zero {r u w' : Pt} (hr : r ≠ 0)
    (hu : det2 r u = 0) (hw : det2 r w' = 0) (hw' : w' ≠ 0) :
    ∃ μ : ℝ, u = μ • w' := by
  -- r 0 * u 1 = r 1 * u 0 and r 0 * w'1 = r 1 * w'0; r ≠ 0 and w' ≠ 0.
  have hu' : r 0 * u 1 - r 1 * u 0 = 0 := hu
  have hw0 : r 0 * w' 1 - r 1 * w' 0 = 0 := hw
  -- the parallel cross-relation u1 w'0 = u0 w'1.
  have hpar : u 1 * w' 0 = u 0 * w' 1 := by
    by_cases hr0 : r 0 = 0
    · have hr1 : r 1 ≠ 0 := fun h => hr (pt_ext_zero_one hr0 h)
      have hu0' : r 1 * u 0 = 0 := by rw [hr0] at hu'; linarith
      have hw0' : r 1 * w' 0 = 0 := by rw [hr0] at hw0; linarith
      have hu0 : u 0 = 0 := by
        rcases mul_eq_zero.mp hu0' with h | h
        · exact absurd h hr1
        · exact h
      have hw'0 : w' 0 = 0 := by
        rcases mul_eq_zero.mp hw0' with h | h
        · exact absurd h hr1
        · exact h
      rw [hu0, hw'0]; ring
    · have e1 : r 0 * u 1 = r 1 * u 0 := by linarith [hu']
      have e2 : r 0 * w' 1 = r 1 * w' 0 := by linarith [hw0]
      have hkey : r 0 * (u 1 * w' 0) = r 0 * (u 0 * w' 1) := by
        calc r 0 * (u 1 * w' 0) = (r 0 * u 1) * w' 0 := by ring
          _ = (r 1 * u 0) * w' 0 := by rw [e1]
          _ = u 0 * (r 1 * w' 0) := by ring
          _ = u 0 * (r 0 * w' 1) := by rw [e2]
          _ = r 0 * (u 0 * w' 1) := by ring
      exact mul_left_cancel₀ hr0 hkey
  -- pick the nonzero coordinate of w'.
  by_cases hw'0 : w' 0 = 0
  · -- then w' 1 ≠ 0, and u 0 * w'1 = u1 * w'0 = 0 ⟹ u 0 = 0.
    have hw'1 : w' 1 ≠ 0 := fun h => hw' (pt_ext_zero_one hw'0 h)
    have hu0 : u 0 = 0 := by
      rw [hw'0, mul_zero] at hpar
      rcases mul_eq_zero.mp hpar.symm with h | h
      · exact h
      · exact absurd h hw'1
    refine ⟨u 1 / w' 1, ?_⟩
    set μ := u 1 / w' 1 with hμ
    have c0 : u 0 = μ * w' 0 := by rw [hw'0, mul_zero, hu0]
    have c1 : u 1 = μ * w' 1 := by rw [hμ, div_mul_cancel₀ _ hw'1]
    ext k; fin_cases k <;> simp only [PiLp.smul_apply, smul_eq_mul] <;> assumption
  · -- w' 0 ≠ 0: μ = u 0 / w' 0.
    refine ⟨u 0 / w' 0, ?_⟩
    set μ := u 0 / w' 0 with hμ
    have c0 : u 0 = μ * w' 0 := by rw [hμ, div_mul_cancel₀ _ hw'0]
    have c1 : u 1 = μ * w' 1 := by
      rw [hμ, div_mul_eq_mul_div, eq_div_iff hw'0]; exact hpar
    ext k; fin_cases k <;> simp only [PiLp.smul_apply, smul_eq_mul] <;> assumption

/-- `¬ Span (μ • v) v` for `μ > 0` (the two values never straddle the origin). -/
lemma not_span_pos_smul {μ v : ℝ} (hμ : 0 < μ) : ¬ Span (μ * v) v := by
  unfold Span
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · nlinarith
  · nlinarith

/-- **Degenerate wall ⟹ no crossing.**  At a wall where both endpoint side values
vanish (`x` on edge `i`'s line) and `x` is off the boundary, the two side functions
are positively proportional (`ds0Of i = μ • ds1Of i`, `μ > 0`), so `Span` is false
everywhere and `rfcount i ≡ 0`. -/
lemma rfcount_eventually_zero_of_degenerateWall {P : StrictSimplePolygon n}
    {r₁ r₂ : Pt} {x : Pt} (hoff : ¬ OnBoundary P x) {i : Fin n} {t₀ : ℝ}
    (hrne : dirAt r₁ r₂ t₀ ≠ 0)
    (hDi : dirDen P r₁ r₂ i t₀ = 0)
    (h0 : ds0Of P r₁ r₂ x i t₀ = 0) :
    ∀ᶠ t in nhds t₀, rfcount P r₁ r₂ x i t = 0 := by
  classical
  set a := P.q i with ha
  set b := P.q (cyclicNext i) with hb
  set r := dirAt r₁ r₂ t₀ with hr
  have h1 : ds1Of P r₁ r₂ x i t₀ = 0 := by rw [← ds_eq_at_wall hDi]; exact h0
  -- det2 r (a - x) = 0 and det2 r (b - x) = 0.
  have hda : det2 r (a - x) = 0 := h0
  have hdb : det2 r (b - x) = 0 := h1
  -- b ≠ x (else x = b on boundary).
  have hbx : b - x ≠ 0 := by
    intro hz
    have hxb : x = b := by rw [sub_eq_zero] at hz; exact hz.symm
    apply hoff
    exact ⟨i, by rw [hxb, hb, Edge]; exact right_mem_segment ℝ _ _⟩
  -- a - x = μ • (b - x).
  obtain ⟨μ, hμeq⟩ := exists_smul_of_det2_zero hrne hda hdb hbx
  -- pointwise: ds0Of i t = μ * ds1Of i t.
  have hprop : ∀ t, ds0Of P r₁ r₂ x i t = μ * ds1Of P r₁ r₂ x i t := by
    intro t
    have e0 : ds0Of P r₁ r₂ x i t = det2 (dirAt r₁ r₂ t) (a - x) := rfl
    have e1 : ds1Of P r₁ r₂ x i t = det2 (dirAt r₁ r₂ t) (b - x) := rfl
    rw [e0, e1, hμeq, det2_smul_right]
  -- b - a = (1 - μ) • (b - x).
  have hedge : b - a = (1 - μ) • (b - x) := by
    have : b - a = (b - x) - (a - x) := by abel
    rw [this, hμeq, sub_smul, one_smul]
  -- 1 - μ ≠ 0 (else edge vector zero).
  have h1μ : (1 : ℝ) - μ ≠ 0 := by
    intro hz
    apply edgeVec_ne_zero P i
    rw [edgeVec, ← hb, ← ha, hedge, hz, zero_smul]
  -- μ > 0 (else x ∈ Edge i with λ = -μ/(1-μ) ∈ [0,1]).
  have hμpos : 0 < μ := by
    by_contra hle
    push_neg at hle
    apply hoff
    refine ⟨i, ?_⟩
    set lam := -μ / (1 - μ) with hlam
    -- x - a = lam • (b - a).
    have hxa : x - a = lam • (b - a) := by
      rw [hlam, hedge]
      rw [smul_smul]
      rw [div_mul_cancel₀ _ h1μ]
      -- x - a = -μ • (b - x); and a - x = μ(b-x) ⟹ x - a = -μ(b-x).
      have : x - a = -(a - x) := by abel
      rw [this, hμeq, neg_smul]
    have hxeq : x = AffineMap.lineMap a b lam := by
      rw [AffineMap.lineMap_apply_module]
      have : (1 - lam) • a + lam • b = a + lam • (b - a) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [this, ← hxa]; abel
    -- 0 ≤ lam ≤ 1.
    have hnum : 0 ≤ -μ := by linarith
    have hden : 0 < 1 - μ := by linarith
    have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
    have hlam1 : lam ≤ 1 := by
      rw [hlam, div_le_one hden]; linarith
    rw [Edge, seg, segment_eq_image_lineMap]
    exact ⟨lam, ⟨hlam0, hlam1⟩, hxeq.symm⟩
  -- now Span is false everywhere ⟹ rfcount ≡ 0.
  filter_upwards with t
  rw [rfcount_eq]
  apply if_neg
  apply not_rstatusOf_of_not_span
  rw [hprop t]
  exact not_span_pos_smul hμpos

/-- **Any wall edge contributes `0` near the wall.**  At a wall (`dirDen i t₀ = 0`),
off the boundary, `rfcount i ≡ 0` in a neighbourhood of `t₀` — whether the wall is
generic (`x` off edge `i`'s line) or degenerate (`x` on the line). -/
lemma rfcount_eventually_zero_of_wall {P : StrictSimplePolygon n}
    {r₁ r₂ : Pt} {x : Pt} (hoff : ¬ OnBoundary P x) {i : Fin n} {t₀ : ℝ}
    (hrne : dirAt r₁ r₂ t₀ ≠ 0)
    (hwall : dirDen P r₁ r₂ i t₀ = 0) :
    ∀ᶠ t in nhds t₀, rfcount P r₁ r₂ x i t = 0 := by
  by_cases h0 : ds0Of P r₁ r₂ x i t₀ = 0
  · exact rfcount_eventually_zero_of_degenerateWall hoff hrne hwall h0
  · exact rfcount_eventually_zero_of_genericWall hwall h0

end

end ProofsInTheBook.PolygonWall
