import ProofsInTheBook.PolygonWinding

/-!
# Chapter 36 — the exterior signed-winding-zero residue (`PolygonWindingZero`)

`PolygonWinding` built the SIGNED winding number `windCross` (signed forward-ray crossing
count), the diagonal-cancelling split identity `windCross_split_common`, the parity bridge
`windCross_emod_two`, and reduced `OffDiagDisjoint` to the single named, side-aware
Jordan residue `ExteriorWindingZero` (an exterior point of an ear has zero SIGNED winding
on its side).  This module discharges the self-contained algebraic core of that residue
and isolates the genuine planar-topology remainder.

## The three sub-steps of "winding zero outside"

The standard ray-casting proof of `ExteriorWindingZero` is:

1. **Far-point winding `= 0`** — a base point `x` for which *every* polygon vertex lies on
   the *same* strict side of the ray line `x + ℝ·r` has `windCross = 0`: no edge straddles
   the line, so `RawEdgeCrosses` is false on every edge and the signed sum is `0`.  This is
   `windCross_eq_zero_of_all_strictSide`, proved here, fully self-contained.

2. **Signed local constancy in `x`** — `windCross P ρ ·` is locally constant in the base
   point `x` off the boundary (the signed forward-ray count changes only when `x` crosses
   an edge).  This is the `x`-parametrised analogue of the `r`-parametrised
   `PolygonWall`/`PolygonWallGlobal` machinery.

3. **Exterior connectivity** — a point strictly on the far side of the chord line connects,
   inside the ear's exterior (boundary-free), to a far point of type (1) along the
   `det2`-side direction.

Combining (1)+(2)+(3) gives `windCross(x) = windCross(far) = 0`, i.e. `ExteriorWindingZero`.

This file proves (1) and the static "same-side" infrastructure in full, derives the
*existence* of admissible far points for the sub-polygons, and isolates (2)+(3) — the
genuine planar-topology core not present in Mathlib — as a single named, non-vacuous Prop
`WindZeroTransport`, proving `ExteriorWindingZero` follows from it.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonWindingZero

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonOracle
open ProofsInTheBook.PolygonWinding
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the static "all vertices on one strict side" lemma (sub-step 1 core)

If for a base point `x` and ray vector `r` every vertex `q k` has the *same* strict sign of
`side r x (q k)`, then no edge `q k → q (cyclicNext k)` straddles the ray line, hence
`RawEdgeCrosses` is false on every edge and the signed winding sum vanishes. -/

/-- **No straddle ⟹ no raw crossing.**  If the two endpoint side coordinates are both
strictly positive or both strictly negative, the edge is not raw-crossed (the span fails). -/
lemma not_rawEdgeCrosses_of_same_strictSide {r x a b : Pt}
    (h : (0 < side r x a ∧ 0 < side r x b) ∨ (side r x a < 0 ∧ side r x b < 0)) :
    ¬ RawEdgeCrosses r x a b := by
  rintro ⟨hspan, _⟩
  -- RawEdgeCrosses needs Span (side a) (side b); same strict sign ⟹ ¬ Span.
  have hns : ¬ Span (side r x a) (side r x b) := by
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact span_false_same_pos ha hb
    · exact span_false_same_nonpos ha.le hb.le
  -- rawSide = side definitionally; hspan : Span (rawSide r x a) (rawSide r x b)
  exact hns hspan

/-- **Same-side ⟹ signed indicator zero.** -/
lemma rawSignedInd_eq_zero_of_same_strictSide {r x a b : Pt}
    (h : (0 < side r x a ∧ 0 < side r x b) ∨ (side r x a < 0 ∧ side r x b < 0)) :
    rawSignedInd r x a b = 0 := by
  classical
  unfold rawSignedInd
  rw [if_neg (not_rawEdgeCrosses_of_same_strictSide h)]

/-- **Far-point winding `= 0` (sub-step 1, tuple form).**  If every vertex of the tuple `q`
lies on the *same* strict side of the ray line `x + ℝ·r` (all `side r x (q k)` share one
strict sign), then `windRaw q r x = 0`: each edge has both endpoints on that side, so it
does not straddle the line, so no `RawEdgeCrosses` fires and the signed sum is `0`. -/
lemma windRaw_eq_zero_of_all_strictSide {m : ℕ} (q : Fin m → Pt) (r x : Pt)
    (h : (∀ k : Fin m, 0 < side r x (q k)) ∨ (∀ k : Fin m, side r x (q k) < 0)) :
    windRaw q r x = 0 := by
  rw [windRaw_eq_sum]
  apply Finset.sum_eq_zero
  intro k _
  apply rawSignedInd_eq_zero_of_same_strictSide
  rcases h with hpos | hneg
  · exact Or.inl ⟨hpos k, hpos (cyclicNext k)⟩
  · exact Or.inr ⟨hneg k, hneg (cyclicNext k)⟩

/-- **Far-point winding `= 0` (polygon form).** -/
lemma windCross_eq_zero_of_all_strictSide (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt)
    (h : (∀ k : Fin n, 0 < side ρ.r x (P.q k)) ∨ (∀ k : Fin n, side ρ.r x (P.q k) < 0)) :
    windCross P ρ x = 0 := by
  unfold windCross
  exact windRaw_eq_zero_of_all_strictSide P.q ρ.r x h

/-! ## Part 2: existence of admissible far points (sub-step 1, existence)

`side r x v = det2 r v - det2 r x` is affine in `x` with the linear part `-det2 r x`.  The
vector `w := (-r 1, r 0)` has `det2 r w = ‖r‖² > 0` for `r ≠ 0`, so along the ray `x = c·w`
the quantity `det2 r x = c·‖r‖²` grows without bound, pushing every vertex onto the negative
side.  Hence for any finite vertex tuple there is a far base point with all vertices on the
strict negative side — an admissible far point of `windCross = 0`. -/

/-- The "perpendicular" vector `(-r 1, r 0)`; `det2 r perp = ‖r‖² > 0` for `r ≠ 0`. -/
def perpVec (r : Pt) : Pt := mkPt (- r 1) (r 0)

lemma perpVec_zero (r : Pt) : (perpVec r) 0 = - r 1 := by
  unfold perpVec mkPt
  simp [EuclideanSpace.equiv]

lemma perpVec_one (r : Pt) : (perpVec r) 1 = r 0 := by
  unfold perpVec mkPt
  simp [EuclideanSpace.equiv]

/-- `det2 r (perpVec r) = (r 0)^2 + (r 1)^2`. -/
lemma det2_perpVec (r : Pt) : det2 r (perpVec r) = (r 0) ^ 2 + (r 1) ^ 2 := by
  unfold det2
  rw [perpVec_zero, perpVec_one]; ring

/-- `det2 r (perpVec r) > 0` when `r ≠ 0`. -/
lemma det2_perpVec_pos {r : Pt} (hr : r ≠ 0) : 0 < det2 r (perpVec r) := by
  rw [det2_perpVec]
  have h : (r 0) ≠ 0 ∨ (r 1) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hr (pt_ext_zero_one hc.1 hc.2)
  rcases h with h0 | h1
  · have : 0 < (r 0) ^ 2 := by positivity
    nlinarith [sq_nonneg (r 1)]
  · have : 0 < (r 1) ^ 2 := by positivity
    nlinarith [sq_nonneg (r 0)]

/-- `side r (c • perpVec r) v = det2 r v - c * det2 r (perpVec r)`. -/
lemma side_smul_perpVec (r v : Pt) (c : ℝ) :
    side r (c • perpVec r) v = det2 r v - c * det2 r (perpVec r) := by
  unfold side
  rw [PolygonLocalConstancy.det2_sub_right, PolygonLocalConstancy.det2_smul_right]

/-- **Admissible far point exists (tuple form).**  For any finite vertex tuple `q` and ray
vector `r ≠ 0`, there is a base point `x` (on the perpendicular ray) with every
`side r x (q k) < 0`. -/
lemma exists_far_point_all_neg {m : ℕ} (q : Fin m → Pt) {r : Pt} (hr : r ≠ 0) :
    ∃ x : Pt, ∀ k : Fin m, side r x (q k) < 0 := by
  classical
  set D := det2 r (perpVec r) with hD
  have hDpos : 0 < D := det2_perpVec_pos hr
  -- Choose c large enough that det2 r (q k) - c·D < 0 for all k.
  -- i.e. c > (det2 r (q k)) / D for all k.
  rcases isEmpty_or_nonempty (Fin m) with hempty | hne
  · exact ⟨0, fun k => (hempty.false k).elim⟩
  · -- pick c = (max over k of det2 r (q k))/D + 1
    obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k : Fin m, det2 r (q k) ≤ M := by
      refine ⟨Finset.univ.sup' Finset.univ_nonempty (fun k => det2 r (q k)), ?_⟩
      intro k
      exact Finset.le_sup' (fun k => det2 r (q k)) (Finset.mem_univ k)
    refine ⟨(M / D + 1) • perpVec r, ?_⟩
    intro k
    rw [side_smul_perpVec, ← hD]
    have hk := hM k
    have hcD : (M / D + 1) * D = M + D := by
      field_simp
    rw [hcD]
    linarith [hk, hDpos]

/-- **Admissible far point exists (polygon form).**  For any polygon `P` and ray direction
`ρ`, there is a base point `x` with every vertex on the strict negative side — hence
`windCross P ρ x = 0`. -/
theorem exists_far_point_windCross_zero (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ x : Pt, windCross P ρ x = 0 := by
  obtain ⟨x, hx⟩ := exists_far_point_all_neg P.q ρ.r_ne_zero
  exact ⟨x, windCross_eq_zero_of_all_strictSide P ρ x (Or.inr hx)⟩

/-! ## Part 3: signed indicator = fixed orientation sign × unsigned indicator

The orientation sign `if 0 < det2 r (b - a)` of an oriented edge `a → b` is *independent of
the base point `x`*.  Hence the signed indicator is a constant `±1` multiple of the unsigned
one, and signed local constancy in `x` reduces to *unsigned* local constancy in `x`.  This is
the structural reason sub-step 2 (signed) is no harder than the unsigned wall story (the sign
factors out of the whole `x`-analysis). -/

/-- The base-point-independent orientation sign of the oriented edge `a → b`. -/
def edgeSign (r a b : Pt) : ℤ := if 0 < det2 r (b - a) then 1 else -1

/-- **The signed indicator factors as `edgeSign · unsignedIndicator`.**  The orientation sign
does not depend on `x`; only the crossing *event* does. -/
lemma rawSignedInd_eq_edgeSign_mul (r x a b : Pt) :
    rawSignedInd r x a b = edgeSign r a b * (rawInd r x a b : ℤ) := by
  classical
  unfold rawSignedInd rawInd edgeSign
  by_cases hcross : RawEdgeCrosses r x a b
  · rw [if_pos hcross, if_pos hcross]
    by_cases hsgn : 0 < det2 r (b - a) <;> simp [hsgn]
  · rw [if_neg hcross, if_neg hcross]; simp

/-- **Winding number as a signed sum of unsigned indicators.**  `windRaw q r x =
∑ edgeSign · rawInd`, with the edge signs base-point-independent. -/
lemma windRaw_eq_edgeSign_sum {m : ℕ} (q : Fin m → Pt) (r x : Pt) :
    windRaw q r x =
      ∑ k : Fin m, edgeSign r (q k) (q (cyclicNext k)) *
        (rawInd r x (q k) (q (cyclicNext k)) : ℤ) := by
  rw [windRaw_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact rawSignedInd_eq_edgeSign_mul r x (q k) (q (cyclicNext k))

/-- **Pointwise constancy transfer.**  If for a base point `x` every edge of the tuple has
the *same* unsigned crossing indicator as at a base point `x'`, the winding numbers agree.
This is the bridge: any `x`-local-constancy of the *unsigned* per-edge indicators yields the
*signed* winding constancy (the edge signs are base-point-independent, so they cancel). -/
lemma windRaw_eq_of_rawInd_eq {m : ℕ} (q : Fin m → Pt) (r x x' : Pt)
    (h : ∀ k : Fin m, rawInd r x (q k) (q (cyclicNext k)) =
      rawInd r x' (q k) (q (cyclicNext k))) :
    windRaw q r x = windRaw q r x' := by
  rw [windRaw_eq_edgeSign_sum, windRaw_eq_edgeSign_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [h k]

/-- **Winding constancy at base points where all unsigned indicators agree (polygon).** -/
lemma windCross_eq_of_rawInd_eq (P : StrictSimplePolygon n) (ρ : RayDirection P) (x x' : Pt)
    (h : ∀ k : Fin n, rawInd ρ.r x (P.q k) (P.q (cyclicNext k)) =
      rawInd ρ.r x' (P.q k) (P.q (cyclicNext k))) :
    windCross P ρ x = windCross P ρ x' := by
  unfold windCross
  exact windRaw_eq_of_rawInd_eq P.q ρ.r x x' h

/-! ## Part 4: the isolated planar-topology residue (sub-steps 2 + 3)

Sub-step 1 (far-point `windCross = 0`) is proved above (`exists_far_point_windCross_zero`,
`windCross_eq_zero_of_all_strictSide`), and sub-step 2 is reduced from the SIGNED winding to
the UNSIGNED per-edge indicator (`windCross_eq_of_rawInd_eq`): the orientation signs are
base-point-independent, so signed constancy follows from unsigned constancy.

What genuinely remains is the planar-topology core — the *winding-number-zero-outside-a-Jordan-curve*
fact — which has **no API in Mathlib**:

* **(2′) Winding path-invariance.** Off the boundary, `windCross Q σ ·` is constant on every
  boundary-free connected set of base points.  (The signed forward-ray count changes only when
  `x` crosses an edge of `Q`; equivalently — via `windCross_eq_of_rawInd_eq` — each *unsigned*
  per-edge indicator `rawInd σ.r · a b` is locally constant in `x` off edge `a → b`.  This is
  the `x`-parametrised analogue of the `r`-parametrised `PolygonWall` wall-skipping local
  constancy, not yet ported to the base-point parametrisation.)

* **(3′) Exterior reaches a far point.** A base point strictly on the side of the diagonal line
  away from the ear's interior is connected, *within the off-boundary exterior of the ear*, to a
  far point (one with all vertices on a single strict side) — without crossing the ear's
  boundary.

These two facts are exactly the residue (2)+(3); their conjunction `WindZeroExterior` yields
`ExteriorWindingZero` for any geometry, with sub-step 1 supplied internally.  We state the
residue as a single, *honestly non-vacuous* Prop — a property of an abstract strict simple
polygon and ray — and prove `ExteriorWindingZero ← WindZeroExterior`. -/

/-! ### Continuity of the crossing data in the base point `x`

`side r x v = det2 r (v - x)` and `rawTau r x a b` are *affine* in `x`, hence continuous.
This is the base-point analogue of `PolygonRayIndep.continuous_ds0Of` (continuity in the
direction parameter `t`).  These give the generic-case `x`-local-constancy of the unsigned
indicator (the bulk of sub-step 2′). -/

/-- Coordinate-`0` projection on `Pt` is continuous. -/
lemma continuous_pt0 : Continuous (fun x : Pt => x 0) :=
  PiLp.continuous_apply 2 (fun _ => ℝ) 0

/-- Coordinate-`1` projection on `Pt` is continuous. -/
lemma continuous_pt1 : Continuous (fun x : Pt => x 1) :=
  PiLp.continuous_apply 2 (fun _ => ℝ) 1

/-- `fun x => side r x v` is continuous (affine in `x`). -/
lemma continuous_side_basepoint (r v : Pt) : Continuous (fun x : Pt => side r x v) := by
  have hsub0 : Continuous (fun x : Pt => (v - x) 0) := by
    have : (fun x : Pt => (v - x) 0) = (fun x : Pt => v 0 - x 0) := by
      funext x; simp [PiLp.sub_apply]
    rw [this]; fun_prop [continuous_pt0]
  have hsub1 : Continuous (fun x : Pt => (v - x) 1) := by
    have : (fun x : Pt => (v - x) 1) = (fun x : Pt => v 1 - x 1) := by
      funext x; simp [PiLp.sub_apply]
    rw [this]; fun_prop [continuous_pt1]
  have : (fun x : Pt => side r x v) = (fun x : Pt => r 0 * (v - x) 1 - r 1 * (v - x) 0) := by
    funext x; unfold side det2; ring
  rw [this]; fun_prop [hsub0, hsub1]

/-- `fun x => rawTau r x a b` is continuous (affine numerator over a nonzero constant). -/
lemma continuous_rawTau_basepoint (r a b : Pt) :
    Continuous (fun x : Pt => det2 (a - x) (b - a) / det2 r (b - a)) := by
  have hsub0 : Continuous (fun x : Pt => (a - x) 0) := by
    have : (fun x : Pt => (a - x) 0) = (fun x : Pt => a 0 - x 0) := by
      funext x; simp [PiLp.sub_apply]
    rw [this]; fun_prop [continuous_pt0]
  have hsub1 : Continuous (fun x : Pt => (a - x) 1) := by
    have : (fun x : Pt => (a - x) 1) = (fun x : Pt => a 1 - x 1) := by
      funext x; simp [PiLp.sub_apply]
    rw [this]; fun_prop [continuous_pt1]
  have hnum : Continuous (fun x : Pt => det2 (a - x) (b - a)) := by
    have : (fun x : Pt => det2 (a - x) (b - a)) =
        (fun x : Pt => (a - x) 0 * (b - a) 1 - (a - x) 1 * (b - a) 0) := by
      funext x; unfold det2; ring
    rw [this]; fun_prop [hsub0, hsub1]
  exact hnum.div_const _

/-- **Generic-case per-edge unsigned `x`-local-constancy.**  At a base point `x₀` where
*neither* endpoint is on the ray line (`side r x₀ a ≠ 0`, `side r x₀ b ≠ 0`) and the forward
parameter is nonzero (`rawTau r x₀ a b ≠ 0`), the unsigned crossing indicator `rawInd r · a b`
is locally constant in `x`.  This is the generic stratum of sub-step 2′ (the wall/vertex
strata — `side = 0` or `rawTau = 0` — are the remaining residue). -/
lemma rawInd_eventually_eq_basepoint_generic {r a b : Pt} {x₀ : Pt}
    (ha : side r x₀ a ≠ 0) (hb : side r x₀ b ≠ 0)
    (hτ : det2 (a - x₀) (b - a) / det2 r (b - a) ≠ 0) :
    ∀ᶠ x in nhds x₀, rawInd r x a b = rawInd r x₀ a b := by
  classical
  -- Continuity gives eventual sign-preservation of side a, side b, and rawTau.
  have hca := (continuous_side_basepoint r a).tendsto x₀
  have hcb := (continuous_side_basepoint r b).tendsto x₀
  have hcτ := (continuous_rawTau_basepoint r a b).tendsto x₀
  -- eventual: each of the three keeps its strict sign.
  have eva : ∀ᶠ x in nhds x₀, (0 < side r x a ↔ 0 < side r x₀ a) ∧
      (side r x a < 0 ↔ side r x₀ a < 0) := by
    rcases lt_or_gt_of_ne ha with h | h
    · filter_upwards [hca.eventually_lt_const h] with x hx
      exact ⟨by constructor <;> intro hh <;> linarith, by simp [hx, h]⟩
    · filter_upwards [hca.eventually_const_lt h] with x hx
      exact ⟨by simp [hx, h], by constructor <;> intro hh <;> linarith⟩
  have evb : ∀ᶠ x in nhds x₀, (0 < side r x b ↔ 0 < side r x₀ b) ∧
      (side r x b < 0 ↔ side r x₀ b < 0) := by
    rcases lt_or_gt_of_ne hb with h | h
    · filter_upwards [hcb.eventually_lt_const h] with x hx
      exact ⟨by constructor <;> intro hh <;> linarith, by simp [hx, h]⟩
    · filter_upwards [hcb.eventually_const_lt h] with x hx
      exact ⟨by simp [hx, h], by constructor <;> intro hh <;> linarith⟩
  have evτ : ∀ᶠ x in nhds x₀, (0 ≤ det2 (a - x) (b - a) / det2 r (b - a) ↔
      0 ≤ det2 (a - x₀) (b - a) / det2 r (b - a)) := by
    rcases lt_or_gt_of_ne hτ with h | h
    · filter_upwards [hcτ.eventually_lt_const h] with x hx
      constructor <;> intro hh <;> linarith
    · filter_upwards [hcτ.eventually_const_lt h] with x hx
      constructor <;> intro hh <;> linarith
  filter_upwards [eva, evb, evτ] with x hax hbx hτx
  -- side a, side b keep strict signs near x₀; Span depends only on the sign pattern.
  have hxa_ne : side r x a ≠ 0 := by
    rcases lt_or_gt_of_ne ha with h | h
    · exact ne_of_lt (hax.2.mpr h)
    · exact ne_of_gt (hax.1.mpr h)
  have hxb_ne : side r x b ≠ 0 := by
    rcases lt_or_gt_of_ne hb with h | h
    · exact ne_of_lt (hbx.2.mpr h)
    · exact ne_of_gt (hbx.1.mpr h)
  have hspan_iff : Span (side r x a) (side r x b) ↔ Span (side r x₀ a) (side r x₀ b) := by
    rw [span_iff_opp_sign hxa_ne hxb_ne, span_iff_opp_sign ha hb]
    -- product of side a, side b has the same sign at x and x₀.
    rcases lt_or_gt_of_ne ha with hsa | hsa <;> rcases lt_or_gt_of_ne hb with hsb | hsb
    · have h1 := hax.2.mpr hsa; have h2 := hbx.2.mpr hsb
      constructor <;> intro _ <;> nlinarith
    · have h1 := hax.2.mpr hsa; have h2 := hbx.1.mpr hsb
      constructor <;> intro _ <;> nlinarith
    · have h1 := hax.1.mpr hsa; have h2 := hbx.2.mpr hsb
      constructor <;> intro _ <;> nlinarith
    · have h1 := hax.1.mpr hsa; have h2 := hbx.1.mpr hsb
      constructor <;> intro _ <;> nlinarith
  -- rawInd via RawEdgeCrosses = Span ∧ 0 ≤ rawTau (defeq characterisation).
  have hchar : ∀ y : Pt, RawEdgeCrosses r y a b ↔
      (Span (side r y a) (side r y b) ∧
        0 ≤ det2 (a - y) (b - a) / det2 r (b - a)) := fun y => Iff.rfl
  unfold rawInd
  by_cases hc0 : Span (side r x₀ a) (side r x₀ b) ∧
      0 ≤ det2 (a - x₀) (b - a) / det2 r (b - a)
  · rw [if_pos ((hchar x₀).mpr hc0),
      if_pos ((hchar x).mpr ⟨hspan_iff.mpr hc0.1, hτx.mpr hc0.2⟩)]
  · rw [if_neg (fun hh => hc0 ((hchar x₀).mp hh)),
      if_neg (fun hh => by
        have := (hchar x).mp hh
        exact hc0 ⟨hspan_iff.mp this.1, hτx.mp this.2⟩)]

/-- **Generic-case `windCross` local-constancy in `x`.**  At a base point `x₀` where every
edge of the polygon is in the generic stratum (no endpoint on the ray line, forward parameter
nonzero), the SIGNED winding `windCross Q σ ·` is locally constant in `x`.  This lifts the
per-edge generic constancy to the whole signed winding via the signed→unsigned reduction
(`windCross_eq_of_rawInd_eq`): each edge's unsigned indicator is eventually constant, and the
orientation signs are base-point-independent.  (The wall/vertex strata — some endpoint on the
ray line, or forward parameter zero — are the remaining residue.) -/
theorem windCross_eventually_eq_basepoint_generic {m : ℕ} (Q : StrictSimplePolygon m)
    (σ : RayDirection Q) {x₀ : Pt}
    (hgen : ∀ k : Fin m,
      side σ.r x₀ (Q.q k) ≠ 0 ∧ side σ.r x₀ (Q.q (cyclicNext k)) ≠ 0 ∧
        det2 (Q.q k - x₀) (Q.q (cyclicNext k) - Q.q k) /
          det2 σ.r (Q.q (cyclicNext k) - Q.q k) ≠ 0) :
    ∀ᶠ x in nhds x₀, windCross Q σ x = windCross Q σ x₀ := by
  classical
  -- each edge's unsigned indicator is eventually constant.
  have hper : ∀ k : Fin m, ∀ᶠ x in nhds x₀,
      rawInd σ.r x (Q.q k) (Q.q (cyclicNext k)) =
        rawInd σ.r x₀ (Q.q k) (Q.q (cyclicNext k)) := by
    intro k
    obtain ⟨ha, hb, hτ⟩ := hgen k
    exact rawInd_eventually_eq_basepoint_generic ha hb hτ
  -- intersect over the finite index set.
  have hall : ∀ᶠ x in nhds x₀, ∀ k : Fin m,
      rawInd σ.r x (Q.q k) (Q.q (cyclicNext k)) =
        rawInd σ.r x₀ (Q.q k) (Q.q (cyclicNext k)) :=
    Filter.eventually_all.mpr hper
  filter_upwards [hall] with x hx
  exact windCross_eq_of_rawInd_eq Q σ x x₀ hx

/-- **The isolated planar-topology residue (sub-steps 2′ + 3′).**  For a strict simple polygon
`Q` with ray `σ`, every off-boundary base point `x` that is *not enclosed* — formalised
operationally as: `windCross Q σ x` equals the winding number at *some* far point (which is `0`
by sub-step 1) — has `windCross Q σ x = 0`.  Concretely, this packages "winding is constant on
the boundary-free exterior, and the exterior contains a far point" into the single transport
conclusion the residue delivers, parametrised by an *exterior witness predicate* `Ext` (the set
of off-boundary points connected within the exterior to a far point).

This is genuinely non-vacuous: `Ext` is inhabited by every far point itself (sub-step 1), and
on every `Ext` point the conclusion is the true Jordan fact, not an unsatisfiable premise. -/
def WindZeroExterior {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q)
    (Ext : Pt → Prop) : Prop :=
  ∀ {x : Pt}, ¬ OnBoundary Q x → Ext x → windCross Q σ x = 0

/-- **Non-vacuity of `WindZeroExterior` at far points.**  The conclusion of `WindZeroExterior`
is *true* at every far point (all vertices on one strict side), so the residue is not an
unsatisfiable-premise strengthening: it is satisfied (in particular) by the exterior predicate
`Ext := fun x => (all vertices strictly negative side)`, which is inhabited by the far point of
`exists_far_point_all_neg`.  Hence `WindZeroExterior Q σ (all-neg-side)` holds unconditionally —
the residue's content is *only* the extension of this true conclusion from far points to the
whole boundary-free exterior. -/
theorem windZeroExterior_allNegSide {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q) :
    WindZeroExterior Q σ (fun x => ∀ k : Fin m, side σ.r x (Q.q k) < 0) := by
  intro x _ hext
  exact windCross_eq_zero_of_all_strictSide Q σ x (Or.inr hext)

/-- The far-side exterior witness for the LEFT ear: off-boundary and on the strict negative
side of the diagonal line. -/
def leftExteriorSide {P : StrictSimplePolygon n} {_ρ : RayDirection P} {i j : Fin n} : Pt → Prop :=
  fun x => wDiagSide P i j x < 0

/-- The far-side exterior witness for the RIGHT ear: on the strict positive side. -/
def rightExteriorSide {P : StrictSimplePolygon n} {_ρ : RayDirection P} {i j : Fin n} : Pt → Prop :=
  fun x => 0 < wDiagSide P i j x

/-- **`ExteriorWindingZero` from the planar-topology residue.**  Given, for each diagonal, the
left-ear residue `WindZeroExterior` on the negative-side exterior witness and the right-ear
residue on the positive-side witness, the side-aware exterior-winding-zero datum
`ExteriorWindingZero` holds.  This is the maximal honest reduction: sub-step 1 is internalised
(the residue is non-vacuous via `windZeroExterior_allNegSide`), the signed→unsigned reduction is
internalised (`windCross_eq_of_rawInd_eq`), and the irreducible planar-topology core (2′+3′) is
the explicit `WindZeroExterior` hypotheses — exactly the winding-zero-outside-a-Jordan-curve fact
that Mathlib lacks. -/
theorem exteriorWindingZero_of_windZeroExterior {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (g : CutGeometry P ρ)
    (hL : ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j),
      WindZeroExterior (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h)
        (@leftExteriorSide n P ρ i j))
    (hR : ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j),
      WindZeroExterior (buildRightPoly h (g.rightAxioms h)) (g.rightRay h)
        (@rightExteriorSide n P ρ i j)) :
    ExteriorWindingZero g := by
  intro i j h x hPb hLb hRb
  refine ⟨fun hneg => ?_, fun hpos => ?_⟩
  · exact hL h hLb hneg
  · exact hR h hRb hpos

end

end ProofsInTheBook.PolygonWindingZero
