import ProofsInTheBook.PolygonSideCrossing
import ProofsInTheBook.PolygonWindingExterior
import ProofsInTheBook.ZinanCh36Lobes

/-!
# `ZinanCh36ArcSweep` — the arc-restricted parity sweep for Chapter 36

This file ports the polygon side-coordinate parity sweep
(`PolygonSideCrossing.crossingNumber'_parity_eventually_const`) from the *closed*
polygon to an **open chain** of segments.  The crossing parity of a forward ray is locally
constant in the base point, even across vertex events: interior chain vertices have BOTH
incident segments present, so the polygon's vertex-handoff atom
`span_mod_two_through_vertex` (the side-coordinate truth table
`[Span a s] + [Span s b] ≡ [Span a b]  (mod 2)`) neutralizes the event verbatim.  The only
new content over the polygon case is the **endpoint handling**: the two ends of an open chain
contribute an *unpaired* incident segment.  The hypothesis `Chain.EndpointSafe` excludes a
forward vertex event there (the endpoint segment is locally backward, hence uncounted), so the
endpoint vertices are parity-neutral too.

The geometry layer is the standalone side-coordinate machinery of `PolygonSideCrossing`
(`side`, `Span`, `span_mod_two_through_vertex`, `span_iff_opp_sign`, `span_const_two_sides`),
applied directly to the raw segment endpoints; the chain's `Transverse` hypothesis supplies the
"no segment parallel to the ray" guard (the chain analogue of `crossDen_ne_zero`).

## What is proved (axioms `{propext, Classical.choice, Quot.sound}`)

* **§1 substrate.**  `Chain`, `Chain.segA/segB/carrier/Transverse`, the side-coordinate ray
  parameter `segTau`, the forward crossing predicate `SegCrossesRay`, the per-segment indicator
  `segCrossInd`, and the crossing count `Chain.rayCount`.
* **§2 endpoint safety.**  `Chain.first/last/firstSeg/lastSeg` helpers and `Chain.EndpointSafe`.
* **§3 the port.**  `Chain.rayCountParity_eventually_eq`: along a generic ray
  (`Transverse η`, `z₀ ∉ carrier`, `EndpointSafe η z₀`) the crossing parity is locally constant
  in the base point.
* **§4 transport.**  `Chain.rayCountParity_constant_on_segment`: parity transported along a
  boundary-free, endpoint-safe straight segment (connectedness of `Icc 0 1`).
* **§5 cheap line lemmas.**  `lineCoord`, `lineCoord_on_line`, `side_ray_eta`, and
  `Chain.rayCount_zero_of_coordMax`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36ArcSweep

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonLocalConstancy
open Filter Topology
open scoped BigOperators

noncomputable section

variable {m : ℕ}

/-! ## §1. The chain substrate -/

/-- An open polygonal chain of `m` segments, given by its `m + 1` vertices. -/
structure Chain (m : ℕ) where
  p : Fin (m + 1) → Pt

/-- The start vertex of segment `i`. -/
def Chain.segA (C : Chain m) (i : Fin m) : Pt := C.p i.castSucc

/-- The end vertex of segment `i`. -/
def Chain.segB (C : Chain m) (i : Fin m) : Pt := C.p i.succ

/-- The carrier of the chain: the union of its closed segments. -/
def Chain.carrier (C : Chain m) : Set Pt := {z | ∃ i : Fin m, z ∈ seg (C.segA i) (C.segB i)}

/-- The chain is transverse to the ray direction `η` when `η ≠ 0` and no segment is parallel
to `η` (the chain analogue of `crossDen_ne_zero`). -/
def Chain.Transverse (C : Chain m) (η : Pt) : Prop :=
  η ≠ 0 ∧ ∀ i : Fin m, det2 η (C.segB i - C.segA i) ≠ 0

/-- The side-coordinate ray parameter of the segment `a → b` from base point `z` in direction
`η`: the unique `τ` with `z + τ•η` on the segment line. -/
def segTau (η z a b : Pt) : ℝ := det2 (a - z) (b - a) / det2 η (b - a)

/-- A segment `a → b` is crossed by the forward ray from `z` when its endpoints straddle the
ray line (side-coordinate half-open `Span`) and the ray parameter is nonnegative. -/
def SegCrossesRay (η z a b : Pt) : Prop :=
  Span (side η z a) (side η z b) ∧ 0 ≤ segTau η z a b

instance (η z a b : Pt) : Decidable (SegCrossesRay η z a b) := by
  unfold SegCrossesRay; infer_instance

/-- The integer per-segment crossing indicator. -/
def segCrossInd (η z a b : Pt) : ℤ := if SegCrossesRay η z a b then 1 else 0

/-- The crossing count of the forward ray from `z` against the whole chain. -/
def Chain.rayCount (C : Chain m) (η z : Pt) : ℤ :=
  ∑ i : Fin m, segCrossInd η z (C.segA i) (C.segB i)

/-! ## §1'. The side difference and the no-flat-segment lemma -/

/-- `side η z b - side η z a = det2 η (b - a)` (the chain analogue of `side_next_sub_side`). -/
lemma side_sub_side (η z a b : Pt) :
    side η z b - side η z a = det2 η (b - a) := by
  unfold side
  rw [← det2_sub_right]
  congr 1
  abel

/-- A transverse segment has nonzero side difference (its endpoints are not both on the ray
line). -/
lemma side_diff_ne_zero (C : Chain m) {η : Pt} (hη : C.Transverse η) (i : Fin m) :
    side η z (C.segB i) - side η z (C.segA i) ≠ 0 := by
  rw [side_sub_side]; exact hη.2 i

/-- No transverse segment has both endpoints on the ray line. -/
lemma not_both_on_line (C : Chain m) {η : Pt} (hη : C.Transverse η) (i : Fin m)
    (ha : side η z (C.segA i) = 0) (hb : side η z (C.segB i) = 0) : False := by
  have := side_diff_ne_zero C hη (z := z) i
  rw [ha, hb, sub_zero] at this; exact this rfl

/-- The edge parameter of the foot of the ray from `z`: `u = det2 η (z - a) / det2 η (b - a)`. -/
def segU (η z a b : Pt) : ℝ := det2 η (z - a) / det2 η (b - a)

/-- **Reconstruction (raw form).**  With `det2 η (b - a) ≠ 0`, the crossing system
`z + τ•η = lineMap a b u` is solved by `τ = segTau η z a b`, `u = segU η z a b`.  This is the
standalone analogue of `PolygonLocalConstancy.cross_eq`. -/
lemma seg_cross_eq {η z a b : Pt} (hden : det2 η (b - a) ≠ 0) :
    z + segTau η z a b • η = AffineMap.lineMap a b (segU η z a b) := by
  set D := det2 η (b - a) with hD
  set u := segU η z a b with hu
  set τ := segTau η z a b with hτ
  rw [← sub_eq_zero]
  apply eq_zero_of_det2_eq_zero (u := η) (v := b - a)
  · rw [← hD]; exact hden
  · -- det2 η ((z + τ•η) - lineMap a b u) = 0
    rw [det2_sub_right, det2_add_right, det2_smul_right, det2_self,
      ProofsInTheBook.PolygonResidues.det2_lineMap]
    have huD : u * D = det2 η z - det2 η a := by
      rw [hu, segU, ← hD, div_mul_cancel₀ _ hden, det2_sub_right]
    have hDval : D = det2 η b - det2 η a := by rw [hD, det2_sub_right]
    rw [hDval] at huD
    rw [mul_zero, add_zero]
    nlinarith [huD]
  · -- det2 (b - a) ((z + τ•η) - lineMap a b u) = 0
    rw [det2_sub_right, det2_add_right, det2_smul_right,
      ProofsInTheBook.PolygonResidues.det2_lineMap]
    have hbab : det2 (b - a) b = det2 (b - a) a := by
      unfold det2; simp only [PiLp.sub_apply]; ring
    have hdenτ : det2 (b - a) η = -D := by
      rw [hD, det2_antisymm η (b - a), neg_neg]
    have hτD : τ * det2 (b - a) η = det2 (b - a) (a - z) := by
      rw [hτ, segTau, ← hD, hdenτ]
      have hnum : det2 (a - z) (b - a) = -det2 (b - a) (a - z) := by
        unfold det2; simp only [PiLp.sub_apply]; ring
      rw [hnum, neg_div]; field_simp
    rw [det2_sub_right] at hτD
    rw [hbab]
    nlinarith [hτD]

/-- The foot parameter lies in `[0,1]` when the segment span-crosses (off-line endpoints). -/
lemma segU_mem_Icc {η z a b : Pt} (hden : det2 η (b - a) ≠ 0)
    (hspan : Span (side η z a) (side η z b))
    (ha : side η z a ≠ 0) (hb : side η z b ≠ 0) :
    segU η z a b ∈ Set.Icc (0 : ℝ) 1 := by
  have hprod : side η z a * side η z b < 0 := (span_iff_opp_sign ha hb).mp hspan
  -- side η z a = -det2 η (z - a), so det2 η (z - a) = -side η z a.
  have hsa : det2 η (z - a) = -side η z a := by
    unfold side det2; simp only [PiLp.sub_apply]; ring
  have hDeq : det2 η (b - a) = side η z b - side η z a := (side_sub_side η z a b).symm
  set sa := side η z a with hsadef
  set sb := side η z b with hsbdef
  have hseg : segU η z a b = -sa / (sb - sa) := by
    rw [segU, hsa, hDeq]
  rw [hseg]
  rcases lt_or_gt_of_ne ha with hsaneg | hsapos
  · have hsb : 0 < sb := by nlinarith
    refine ⟨?_, ?_⟩
    · apply div_nonneg (by linarith) (by linarith)
    · rw [div_le_one (by linarith)]; linarith
  · have hsb : sb < 0 := by nlinarith
    have h1 : -sa / (sb - sa) = sa / (sa - sb) := by
      rw [div_eq_div_iff (by linarith) (by linarith)]; ring
    rw [h1]
    refine ⟨?_, ?_⟩
    · apply div_nonneg (by linarith) (by linarith)
    · rw [div_le_one (by linarith)]; linarith

/-- **`segTau = 0` with a span puts the base point on the segment.**  Standalone analogue of
`PolygonSideCrossing.crossTau_eq_zero_span_imp_onEdge`. -/
lemma onSeg_of_segTau_zero_span {η z a b : Pt} (hden : det2 η (b - a) ≠ 0)
    (hτ : segTau η z a b = 0) (hspan : Span (side η z a) (side η z b))
    (ha : side η z a ≠ 0) (hb : side η z b ≠ 0) :
    z ∈ seg a b := by
  have hrec := seg_cross_eq (η := η) (z := z) (a := a) (b := b) hden
  rw [hτ, zero_smul, add_zero] at hrec
  rw [seg, segment_eq_image_lineMap]
  exact ⟨segU η z a b, segU_mem_Icc hden hspan ha hb, hrec.symm⟩

/-! ## §2. Endpoint safety -/

/-- The first vertex of the chain. -/
def Chain.first (C : Chain m) : Pt := C.p 0

/-- The last vertex of the chain. -/
def Chain.last (C : Chain m) : Pt := C.p (Fin.last m)

/-- The forward ray parameter of the segment `a → b`, written through `segTau`. -/
def Chain.segTauOf (C : Chain m) (η z : Pt) (i : Fin m) : ℝ :=
  segTau η z (C.segA i) (C.segB i)

/-- No unpaired endpoint contributes a forward vertex event: the first vertex is off the ray
line, or the first segment's ray parameter is `< 0` (locally backward); symmetrically for the
last vertex and the last segment. -/
def Chain.EndpointSafe (C : Chain m) (η z : Pt) : Prop :=
  (side η z (C.p 0) ≠ 0 ∨
    ∃ h : 0 < m, C.segTauOf η z ⟨0, h⟩ < 0) ∧
  (side η z (C.p (Fin.last m)) ≠ 0 ∨
    ∃ h : 0 < m, C.segTauOf η z ⟨m - 1, by omega⟩ < 0)

/-! ## §3. Continuity of the side coordinate and the ray parameter in the base point -/

/-- `fun z => side η z v` is continuous in the base point. -/
lemma continuous_side_base (η v : Pt) : Continuous (fun z : Pt => side η z v) := by
  unfold side det2
  fun_prop

/-- `fun z => segTau η z a b` is continuous in the base point (affine numerator over a fixed
nonzero denominator). -/
lemma continuous_segTau_base {η a b : Pt} (hden : det2 η (b - a) ≠ 0) :
    Continuous (fun z : Pt => segTau η z a b) := by
  unfold segTau
  have hnum : Continuous (fun z : Pt => det2 (a - z) (b - a)) := by
    unfold det2; fun_prop
  exact hnum.div_const _

/-! ## §3'. Per-segment local constancy and the vertex-pair parity (the side-coordinate sweep) -/

/-- `segCrossInd` of a segment with both endpoints off the ray line is locally constant in the
base point: the side signs are preserved, the span status is preserved (when the ray parameter
is nonzero), or the segment is locally not span-crossing (when the ray parameter is zero, which
would otherwise put the crossing point at `z` — excluded by the off-carrier hypothesis). -/
lemma segCrossInd_eventually_eq_generic (C : Chain m) {η : Pt} (hη : C.Transverse η) {z₀ : Pt}
    (hoff : z₀ ∉ C.carrier) (i : Fin m)
    (ha : side η z₀ (C.segA i) ≠ 0) (hb : side η z₀ (C.segB i) ≠ 0) :
    ∀ᶠ z in nhds z₀, segCrossInd η z (C.segA i) (C.segB i)
      = segCrossInd η z₀ (C.segA i) (C.segB i) := by
  classical
  set a := C.segA i with ha_def
  set b := C.segB i with hb_def
  have hden : det2 η (b - a) ≠ 0 := hη.2 i
  have hca := continuous_side_base η a
  have hcb := continuous_side_base η b
  have hcτ := continuous_segTau_base (η := η) (a := a) (b := b) hden
  -- side signs preserved near z₀.
  have evsa : ∀ᶠ z in nhds z₀,
      (0 < side η z a ↔ 0 < side η z₀ a) ∧ (side η z a < 0 ↔ side η z₀ a < 0) := by
    rcases lt_or_gt_of_ne ha with h | h
    · filter_upwards [(hca.tendsto z₀).eventually_lt_const h] with z hz
      exact ⟨⟨fun hp => by linarith, fun hp => by linarith⟩, ⟨fun _ => h, fun _ => hz⟩⟩
    · filter_upwards [(hca.tendsto z₀).eventually_const_lt h] with z hz
      exact ⟨⟨fun _ => h, fun _ => hz⟩, ⟨fun hn => by linarith, fun hn => by linarith⟩⟩
  have evsb : ∀ᶠ z in nhds z₀,
      (0 < side η z b ↔ 0 < side η z₀ b) ∧ (side η z b < 0 ↔ side η z₀ b < 0) := by
    rcases lt_or_gt_of_ne hb with h | h
    · filter_upwards [(hcb.tendsto z₀).eventually_lt_const h] with z hz
      exact ⟨⟨fun hp => by linarith, fun hp => by linarith⟩, ⟨fun _ => h, fun _ => hz⟩⟩
    · filter_upwards [(hcb.tendsto z₀).eventually_const_lt h] with z hz
      exact ⟨⟨fun _ => h, fun _ => hz⟩, ⟨fun hn => by linarith, fun hn => by linarith⟩⟩
  -- the span status is locally constant (both sides nonzero): each side keeps its strict sign,
  -- and `Span` of two nonzeros is the opposite-sign test on the product.
  have hspanev : ∀ᶠ z in nhds z₀,
      (Span (side η z a) (side η z b) ↔ Span (side η z₀ a) (side η z₀ b)) := by
    filter_upwards [evsa, evsb] with z hsa hsb
    have hza : side η z a ≠ 0 := by
      rcases lt_or_gt_of_ne ha with h | h
      · exact ne_of_lt (hsa.2.mpr h)
      · exact ne_of_gt (hsa.1.mpr h)
    have hzb : side η z b ≠ 0 := by
      rcases lt_or_gt_of_ne hb with h | h
      · exact ne_of_lt (hsb.2.mpr h)
      · exact ne_of_gt (hsb.1.mpr h)
    rw [span_iff_opp_sign hza hzb, span_iff_opp_sign ha hb]
    constructor
    · intro h
      rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
      · exfalso; nlinarith [hsa.2.mpr ha', hsb.2.mpr hb']
      · nlinarith [hsa.2.mpr ha', hsb.1.mpr hb']
      · nlinarith [hsa.1.mpr ha', hsb.2.mpr hb']
      · exfalso; nlinarith [hsa.1.mpr ha', hsb.1.mpr hb']
    · intro h
      rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
      · exfalso; nlinarith
      · have := hsa.2.mpr ha'; have := hsb.1.mpr hb'; nlinarith
      · have := hsa.1.mpr ha'; have := hsb.2.mpr hb'; nlinarith
      · exfalso; nlinarith
  by_cases hτ : segTau η z₀ a b = 0
  · -- ray parameter zero: a span here would put z₀ on the segment (in the carrier).
    have hnospan : ¬ Span (side η z₀ a) (side η z₀ b) := by
      intro hspan
      exact hoff ⟨i, onSeg_of_segTau_zero_span hden hτ hspan ha hb⟩
    -- both far sides nonzero ⟹ span locally false ⟹ contribution locally 0.
    have hval0 : segCrossInd η z₀ a b = 0 := by
      unfold segCrossInd SegCrossesRay
      rw [if_neg]; rintro ⟨h, _⟩; exact hnospan h
    rw [hval0]
    filter_upwards [hspanev] with z hsp
    unfold segCrossInd SegCrossesRay
    rw [if_neg]; rintro ⟨h, _⟩; exact hnospan (hsp.mp h)
  · -- ray parameter nonzero: both span and forward guard locally constant.
    rcases lt_or_gt_of_ne hτ with hneg | hpos
    · -- backward: locally uncounted, both at z₀ and near.
      have evτ : ∀ᶠ z in nhds z₀, segTau η z a b < 0 := by
        filter_upwards [(hcτ.tendsto z₀).eventually_lt_const hneg] with z hz using hz
      have hval0 : segCrossInd η z₀ a b = 0 := by
        unfold segCrossInd SegCrossesRay; rw [if_neg]; rintro ⟨_, h⟩; linarith
      rw [hval0]
      filter_upwards [evτ] with z hτz
      unfold segCrossInd SegCrossesRay; rw [if_neg]; rintro ⟨_, h⟩; linarith
    · -- forward: status = span, locally constant.
      have evτ : ∀ᶠ z in nhds z₀, 0 < segTau η z a b := by
        filter_upwards [(hcτ.tendsto z₀).eventually_const_lt hpos] with z hz using hz
      filter_upwards [hspanev, evτ] with z hsp hτz
      unfold segCrossInd SegCrossesRay
      by_cases hsp0 : Span (side η z₀ a) (side η z₀ b)
      · rw [if_pos ⟨hsp.mpr hsp0, le_of_lt hτz⟩, if_pos ⟨hsp0, le_of_lt hpos⟩]
      · rw [if_neg (fun h => hsp0 (hsp.mp h.1)), if_neg (fun h => hsp0 h.1)]

/-! ### Forward-regime per-segment value (span only) and the backward value (zero) -/

/-- In the forward regime (ray parameter strictly positive) the per-segment indicator is the
span indicator. -/
lemma segCrossInd_forward {η z a b : Pt} (hτ : 0 < segTau η z a b) :
    segCrossInd η z a b = (if Span (side η z a) (side η z b) then 1 else 0) := by
  unfold segCrossInd SegCrossesRay
  by_cases hsp : Span (side η z a) (side η z b)
  · rw [if_pos ⟨hsp, le_of_lt hτ⟩, if_pos hsp]
  · rw [if_neg (fun h => hsp h.1), if_neg hsp]

/-- In the backward regime (ray parameter strictly negative) the segment is uncounted. -/
lemma segCrossInd_backward {η z a b : Pt} (hτ : segTau η z a b < 0) :
    segCrossInd η z a b = 0 := by
  unfold segCrossInd SegCrossesRay
  rw [if_neg]; rintro ⟨_, h⟩; linarith

/-- **The ℤ image of the span vertex truth table.**  The same handover, with the indicators in
`ℤ` (as needed for `segCrossInd`): cast the proven `ℕ` identity
`span_mod_two_through_vertex`. -/
lemma span_mod_two_through_vertex_int {a b s : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ((if Span a s then (1 : ℤ) else 0) + (if Span s b then 1 else 0)) % 2
      = (if Span a b then 1 else 0) := by
  classical
  have hnat := span_mod_two_through_vertex (a := a) (b := b) (s := s) ha hb
  -- cast each ℤ indicator as the ℕ indicator.
  have cast1 : (if Span a s then (1 : ℤ) else 0) = ((if Span a s then 1 else 0 : ℕ) : ℤ) := by
    by_cases h : Span a s <;> simp [h]
  have cast2 : (if Span s b then (1 : ℤ) else 0) = ((if Span s b then 1 else 0 : ℕ) : ℤ) := by
    by_cases h : Span s b <;> simp [h]
  have cast3 : (if Span a b then (1 : ℤ) else 0) = ((if Span a b then 1 else 0 : ℕ) : ℤ) := by
    by_cases h : Span a b <;> simp [h]
  rw [cast1, cast2, cast3, ← Nat.cast_add]
  rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, ← Int.natCast_mod, hnat]

/-! ## §3'. The interior-vertex pair: parity-neutral handover

At an interior vertex event (shared vertex `p i.succ = segA j` on the ray line, with `j` the
successor segment), the two incident segments pair up.  In the backward regime both are
uncounted; in the forward regime both reduce to span indicators and the truth table
`span_mod_two_through_vertex` makes the pair-sum parity independent of the (moving) vertex side
value.  This is the verbatim chain image of `pair_count_eventually_const'`. -/

/-- **The shared ray parameters of two segments meeting at a vertex agree** when the shared
vertex is on the ray line.  If `segB i = segA j` and that vertex is on the line
(`side η z (segB i) = 0`), then `segTau η z (segA i) (segB i) = segTau η z (segA j) (segB j)`,
both equal to the ray parameter of the shared vertex. -/
lemma segTau_shared_eq {η z ai bi aj bj : Pt} (hshare : bi = aj)
    (hv : side η z bi = 0)
    (hdi : det2 η (bi - ai) ≠ 0) (hdj : det2 η (bj - aj) ≠ 0) :
    segTau η z ai bi = segTau η z aj bj := by
  -- side η z bi = 0 means bi is on the ray line: det2 η (bi - z) = 0.
  have hvz : det2 η (bi - z) = 0 := by
    have : side η z bi = det2 η (bi - z) := by unfold side; rfl
    rw [this] at hv; exact hv
  -- the foot of segment i is bi (u = 1): z + segTau_i • η = lineMap ai bi 1 = bi.
  have hreci := seg_cross_eq (η := η) (z := z) (a := ai) (b := bi) hdi
  have hrecj := seg_cross_eq (η := η) (z := z) (a := aj) (b := bj) hdj
  -- z + segTau_i • η = bi : because segU_i = 1 (shared vertex on the line).
  have hui : segU η z ai bi = 1 := by
    unfold segU
    have hnum : det2 η (z - ai) = det2 η (bi - ai) := by
      have h1 : det2 η (z - ai) = det2 η (z - bi) + det2 η (bi - ai) := by
        rw [← det2_add_right]; congr 1; abel
      have h2 : det2 η (z - bi) = 0 := by
        have : det2 η (z - bi) = -det2 η (bi - z) := by
          unfold det2; simp only [PiLp.sub_apply]; ring
        rw [this, hvz]; ring
      rw [h1, h2, zero_add]
    rw [hnum, div_self hdi]
  have huj : segU η z aj bj = 0 := by
    unfold segU
    have hnum : det2 η (z - aj) = 0 := by
      rw [← hshare]
      have : det2 η (z - bi) = -det2 η (bi - z) := by
        unfold det2; simp only [PiLp.sub_apply]; ring
      rw [this, hvz]; ring
    rw [hnum, zero_div]
  rw [hui, AffineMap.lineMap_apply_one] at hreci
  rw [huj, AffineMap.lineMap_apply_zero] at hrecj
  -- z + segTau_i • η = bi = aj = z + segTau_j • η ⟹ segTau_i = segTau_j (η ≠ 0).
  have heq : z + segTau η z ai bi • η = z + segTau η z aj bj • η := by
    rw [hreci, hrecj, hshare]
  have : segTau η z ai bi • η = segTau η z aj bj • η := by
    have := add_left_cancel heq; exact this
  -- η ≠ 0 (denominator nonzero forces η ≠ 0).
  have hη0 : η ≠ 0 := by
    intro h; apply hdi; rw [h]; unfold det2; simp
  by_contra hne
  have hsub : (segTau η z ai bi - segTau η z aj bj) • η = 0 := by
    rw [sub_smul]; rw [this]; abel
  rcases smul_eq_zero.mp hsub with h | h
  · exact hne (by linarith [sub_eq_zero.mp h])
  · exact hη0 h

/-- **Interior-vertex pair, eventually parity-constant.**  Two segments `(ai → bi)` and
`(aj → bj)` meeting at a shared vertex `bi = aj` that is on the ray line at `z₀`
(`side η z₀ bi = 0`), with both far endpoints off the line, have a locally
parity-constant pair-sum of crossing indicators.  Backward: both uncounted.  Forward: the
truth table `span_mod_two_through_vertex` neutralizes the event. -/
lemma pair_segCrossInd_eventually_eq {η z₀ ai bi aj bj : Pt}
    (hshare : bi = aj)
    (hdi : det2 η (bi - ai) ≠ 0) (hdj : det2 η (bj - aj) ≠ 0)
    (hv : side η z₀ bi = 0)
    (hfa : side η z₀ ai ≠ 0) (hfb : side η z₀ bj ≠ 0)
    (hτv : segTau η z₀ ai bi ≠ 0) :
    ∀ᶠ z in nhds z₀,
      (segCrossInd η z ai bi + segCrossInd η z aj bj) % 2
        = (segCrossInd η z₀ ai bi + segCrossInd η z₀ aj bj) % 2 := by
  classical
  have hcτi := continuous_segTau_base (η := η) (a := ai) (b := bi) hdi
  have hcτj := continuous_segTau_base (η := η) (a := aj) (b := bj) hdj
  have hca := continuous_side_base η ai
  have hcb := continuous_side_base η bj
  have hτj_eq : segTau η z₀ aj bj = segTau η z₀ ai bi :=
    (segTau_shared_eq hshare hv hdi hdj).symm
  rcases lt_or_gt_of_ne hτv with hback | hfwd
  · -- BACKWARD: both segments uncounted near z₀ and at z₀.
    have hτj0 : segTau η z₀ aj bj < 0 := by rw [hτj_eq]; exact hback
    have evτi : ∀ᶠ z in nhds z₀, segTau η z ai bi < 0 := by
      filter_upwards [(hcτi.tendsto z₀).eventually_lt_const hback] with z hz using hz
    have evτj : ∀ᶠ z in nhds z₀, segTau η z aj bj < 0 := by
      filter_upwards [(hcτj.tendsto z₀).eventually_lt_const hτj0] with z hz using hz
    filter_upwards [evτi, evτj] with z hτi hτj
    rw [segCrossInd_backward hτi, segCrossInd_backward hτj,
        segCrossInd_backward hback, segCrossInd_backward hτj0]
  · -- FORWARD: both segments span-only; pair parity = [Span ai bj], constant.
    have hτj0 : 0 < segTau η z₀ aj bj := by rw [hτj_eq]; exact hfwd
    have evτi : ∀ᶠ z in nhds z₀, 0 < segTau η z ai bi := by
      filter_upwards [(hcτi.tendsto z₀).eventually_const_lt hfwd] with z hz using hz
    have evτj : ∀ᶠ z in nhds z₀, 0 < segTau η z aj bj := by
      filter_upwards [(hcτj.tendsto z₀).eventually_const_lt hτj0] with z hz using hz
    -- far endpoints stay nonzero near z₀.
    have eva : ∀ᶠ z in nhds z₀, side η z ai ≠ 0 := by
      rcases lt_or_gt_of_ne hfa with h | h
      · filter_upwards [(hca.tendsto z₀).eventually_lt_const h] with z hz using ne_of_lt hz
      · filter_upwards [(hca.tendsto z₀).eventually_const_lt h] with z hz using ne_of_gt hz
    have evb : ∀ᶠ z in nhds z₀, side η z bj ≠ 0 := by
      rcases lt_or_gt_of_ne hfb with h | h
      · filter_upwards [(hcb.tendsto z₀).eventually_lt_const h] with z hz using ne_of_lt hz
      · filter_upwards [(hcb.tendsto z₀).eventually_const_lt h] with z hz using ne_of_gt hz
    -- [Span ai bj] is locally constant (two off-line far endpoints).
    have evsa : ∀ᶠ z in nhds z₀,
        (0 < side η z ai ↔ 0 < side η z₀ ai) ∧ (side η z ai < 0 ↔ side η z₀ ai < 0) := by
      rcases lt_or_gt_of_ne hfa with h | h
      · filter_upwards [(hca.tendsto z₀).eventually_lt_const h] with z hz
        exact ⟨⟨fun hp => by linarith, fun hp => by linarith⟩, ⟨fun _ => h, fun _ => hz⟩⟩
      · filter_upwards [(hca.tendsto z₀).eventually_const_lt h] with z hz
        exact ⟨⟨fun _ => h, fun _ => hz⟩, ⟨fun hn => by linarith, fun hn => by linarith⟩⟩
    have evsb : ∀ᶠ z in nhds z₀,
        (0 < side η z bj ↔ 0 < side η z₀ bj) ∧ (side η z bj < 0 ↔ side η z₀ bj < 0) := by
      rcases lt_or_gt_of_ne hfb with h | h
      · filter_upwards [(hcb.tendsto z₀).eventually_lt_const h] with z hz
        exact ⟨⟨fun hp => by linarith, fun hp => by linarith⟩, ⟨fun _ => h, fun _ => hz⟩⟩
      · filter_upwards [(hcb.tendsto z₀).eventually_const_lt h] with z hz
        exact ⟨⟨fun _ => h, fun _ => hz⟩, ⟨fun hn => by linarith, fun hn => by linarith⟩⟩
    -- the shared side `s := side η z (segB i) = side η z (segA j)` (definitionally equal).
    have hsab : ∀ z, side η z bi = side η z aj := fun z => by rw [hshare]
    -- forward-regime pair value = vertex truth table, parity-constant.
    have hpairval : ∀ z, 0 < segTau η z ai bi → 0 < segTau η z aj bj →
        side η z ai ≠ 0 → side η z bj ≠ 0 →
        (segCrossInd η z ai bi + segCrossInd η z aj bj) % 2 =
          (if Span (side η z ai) (side η z bj) then 1 else 0) := by
      intro z hτi hτj haz hbz
      rw [segCrossInd_forward hτi, segCrossInd_forward hτj, hsab z]
      exact span_mod_two_through_vertex_int haz hbz
    -- assemble: near z₀, forward, far endpoints nonzero, span constancy.
    filter_upwards [evτi, evτj, eva, evb, evsa, evsb]
      with z hτi hτj haz hbz hsa hsb
    rw [hpairval z hτi hτj haz hbz, hpairval z₀ hfwd hτj0 hfa hfb]
    -- [Span ai bj](z) = [Span ai bj](z₀) via matching strict signs.
    have hAB : (Span (side η z ai) (side η z bj) ↔ Span (side η z₀ ai) (side η z₀ bj)) := by
      rw [span_iff_opp_sign haz hbz, span_iff_opp_sign hfa hfb]
      constructor
      · intro h
        rcases lt_or_gt_of_ne hfa with ha' | ha' <;> rcases lt_or_gt_of_ne hfb with hb' | hb'
        · exfalso; nlinarith [hsa.2.mpr ha', hsb.2.mpr hb']
        · nlinarith [hsa.2.mpr ha', hsb.1.mpr hb']
        · nlinarith [hsa.1.mpr ha', hsb.2.mpr hb']
        · exfalso; nlinarith [hsa.1.mpr ha', hsb.1.mpr hb']
      · intro h
        rcases lt_or_gt_of_ne hfa with ha' | ha' <;> rcases lt_or_gt_of_ne hfb with hb' | hb'
        · exfalso; nlinarith
        · have := hsa.2.mpr ha'; have := hsb.1.mpr hb'; nlinarith
        · have := hsa.1.mpr ha'; have := hsb.2.mpr hb'; nlinarith
        · exfalso; nlinarith
    by_cases h : Span (side η z₀ ai) (side η z₀ bj)
    · rw [if_pos (hAB.mpr h), if_pos h]
    · rw [if_neg (fun hc => h (hAB.mp hc)), if_neg h]

/-! ## §3''. The endpoint-segment local constancy (the unpaired-end handover)

An unpaired endpoint vertex on the ray line forces the single incident segment to be locally
backward (by `EndpointSafe`), so its crossing indicator is locally constant `0`.  This is the
chain's new content over the polygon (the polygon has no unpaired endpoints). -/

/-- **Endpoint-segment local constancy.**  If one endpoint of a segment is on the ray line at
`z₀` but the segment's ray parameter is strictly negative there (the `EndpointSafe` regime), the
crossing indicator is locally constant `0`.  (When the on-line endpoint is the *start*, the
forward foot is at the start, so a nonnegative parameter would put `z₀` on the boundary; the
endpoint-safe hypothesis rules out the forward case.) -/
lemma segCrossInd_eventually_eq_endpoint {η z₀ a b : Pt}
    (hd : det2 η (b - a) ≠ 0) (hτ : segTau η z₀ a b < 0) :
    ∀ᶠ z in nhds z₀, segCrossInd η z a b = segCrossInd η z₀ a b := by
  have hcτ := continuous_segTau_base (η := η) (a := a) (b := b) hd
  have evτ : ∀ᶠ z in nhds z₀, segTau η z a b < 0 := by
    filter_upwards [(hcτ.tendsto z₀).eventually_lt_const hτ] with z hz using hz
  filter_upwards [evτ] with z hτz
  rw [segCrossInd_backward hτz, segCrossInd_backward hτ]

/-! ## §3'''. The pairing map of interior-vertex events

`nextSeg i` is the segment after `i` (total: clamps to `i` at the last segment, which never
arises in the pairing domain `i.val + 1 < m`).  On its true domain the start vertex of
`nextSeg i` is the end vertex of `i`, and it is injective. -/

/-- The successor segment of `i` (total `Nat`-indexed map; only used where `i.val + 1 < m`). -/
def nextSeg {m : ℕ} (i : Fin m) : Fin m :=
  if h : i.val + 1 < m then ⟨i.val + 1, h⟩ else i

/-- On the pairing domain (`i.val + 1 < m`), the successor segment's start vertex is segment
`i`'s end vertex. -/
lemma segA_nextSeg (C : Chain m) (i : Fin m) (h : i.val + 1 < m) :
    C.segA (nextSeg i) = C.segB i := by
  unfold Chain.segA Chain.segB nextSeg
  rw [dif_pos h]
  congr 1

/-- `nextSeg` is injective on the pairing domain. -/
lemma nextSeg_injOn {m : ℕ} {i j : Fin m} (hi : i.val + 1 < m) (hj : j.val + 1 < m)
    (h : nextSeg i = nextSeg j) : i = j := by
  unfold nextSeg at h
  rw [dif_pos hi, dif_pos hj] at h
  have hv : i.val + 1 = j.val + 1 := congrArg Fin.val h
  apply Fin.ext; omega

/-! ## §3''''. The headline parity sweep -/

set_option maxHeartbeats 1600000 in
/-- **The arc-restricted parity sweep (the port).**  Along a generic ray (`Transverse η`, base
point off the carrier, endpoint-safe), the crossing parity of the chain is locally constant in
the base point.  Interior vertex events pair up (truth-table neutral); endpoint events are
excluded by `EndpointSafe`; generic segments are individually locally constant. -/
theorem Chain.rayCountParity_eventually_eq (C : Chain m) {η z₀ : Pt}
    (hη : C.Transverse η) (hoff : z₀ ∉ C.carrier) (hend : C.EndpointSafe η z₀) :
    ∀ᶠ z in nhds z₀, C.rayCount η z % 2 = C.rayCount η z₀ % 2 := by
  classical
  -- Abbreviate the per-segment indicator.
  set F : Pt → Fin m → ℤ := fun z i => segCrossInd η z (C.segA i) (C.segB i) with hF
  -- Membership predicates: a-on-line (start), b-on-line (end).
  set N : Finset (Fin m) := Finset.univ.filter (fun i => side η z₀ (C.segA i) = 0) with hNdef
  set R : Finset (Fin m) := Finset.univ.filter (fun i => side η z₀ (C.segB i) = 0) with hRdef
  set Rest : Finset (Fin m) := Finset.univ.filter
    (fun i => side η z₀ (C.segA i) ≠ 0 ∧ side η z₀ (C.segB i) ≠ 0) with hRestdef
  -- end-on-line split: interior (paired) vs last-vertex (endpoint).
  set Rp : Finset (Fin m) := R.filter (fun i => i.val + 1 < m) with hRpdef
  set Re : Finset (Fin m) := R.filter (fun i => ¬ i.val + 1 < m) with hRedef
  -- start-on-line split: interior (paired) vs first-vertex (endpoint).
  set Np : Finset (Fin m) := N.filter (fun i => i.val ≠ 0) with hNpdef
  set Ne : Finset (Fin m) := N.filter (fun i => i.val = 0) with hNedef
  -- transversality: no segment has both endpoints on the ray line.
  have hboth : ∀ i : Fin m, ¬ (side η z₀ (C.segA i) = 0 ∧ side η z₀ (C.segB i) = 0) := by
    rintro i ⟨ha, hb⟩; exact not_both_on_line C hη i ha hb
  -- R, N, Rest are pairwise disjoint and cover univ.
  have hRN : Disjoint R N := by
    rw [Finset.disjoint_left]; intro i hiR hiN
    rw [hRdef, Finset.mem_filter] at hiR; rw [hNdef, Finset.mem_filter] at hiN
    exact hboth i ⟨hiN.2, hiR.2⟩
  have hcover : (Finset.univ : Finset (Fin m)) = Rest ∪ (R ∪ N) := by
    apply Finset.ext; intro i
    simp only [Finset.mem_univ, true_iff, Finset.mem_union, hRdef, hNdef, hRestdef,
      Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases ha : side η z₀ (C.segA i) = 0
    · by_cases hb : side η z₀ (C.segB i) = 0
      · exact absurd ⟨ha, hb⟩ (hboth i)
      · exact Or.inr (Or.inr ha)
    · by_cases hb : side η z₀ (C.segB i) = 0
      · exact Or.inr (Or.inl hb)
      · exact Or.inl ⟨ha, hb⟩
  have hRestRN : Disjoint Rest (R ∪ N) := by
    rw [Finset.disjoint_left]; intro i hiRest hiRN
    simp only [hRestdef, Finset.mem_filter, Finset.mem_univ, true_and] at hiRest
    simp only [Finset.mem_union, hRdef, hNdef, Finset.mem_filter, Finset.mem_univ,
      true_and] at hiRN
    rcases hiRN with h | h
    · exact hiRest.2 h
    · exact hiRest.1 h
  -- R = Rp ⊔ Re, N = Np ⊔ Ne.
  have hRsplit : R = Rp ∪ Re := by
    rw [hRpdef, hRedef]; exact (Finset.filter_union_filter_not_eq _ _).symm
  have hRdisj : Disjoint Rp Re := by
    rw [hRpdef, hRedef]; exact Finset.disjoint_filter_filter_not R R _
  have hNsplit : N = Np ∪ Ne := by
    apply Finset.ext; intro i
    simp only [hNpdef, hNedef, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hiN; rcases eq_or_ne i.val 0 with h | h
      · exact Or.inr ⟨hiN, h⟩
      · exact Or.inl ⟨hiN, h⟩
    · rintro (⟨hiN, _⟩ | ⟨hiN, _⟩) <;> exact hiN
  have hNdisj : Disjoint Np Ne := by
    rw [hNpdef, hNedef, Finset.disjoint_left]
    intro i hi hi'; rw [Finset.mem_filter] at hi hi'; exact hi.2 hi'.2
  -- Np = Rp.image nextSeg, with the pairing nextSeg i ↦ next segment.
  have hNpimg : Np = Rp.image nextSeg := by
    apply Finset.ext; intro j
    constructor
    · intro hj
      simp only [hNpdef, hNdef, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨haj, hj0⟩ := hj
      rw [Finset.mem_image]
      have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj0
      refine ⟨⟨j.val - 1, by omega⟩, ?_, ?_⟩
      · -- ⟨j.val - 1⟩ ∈ Rp.
        simp only [hRpdef, hRdef, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, show (j.val - 1) + 1 < m by omega⟩
        -- segB ⟨j-1⟩ = segA j, on line.
        have heq : C.segB ⟨j.val - 1, by omega⟩ = C.segA j := by
          unfold Chain.segB Chain.segA; congr 1; apply Fin.ext
          simp only [Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE]; omega
        rw [heq]; exact haj
      · -- nextSeg ⟨j-1⟩ = j.
        unfold nextSeg; rw [dif_pos (show (j.val - 1) + 1 < m by omega)]; apply Fin.ext
        show (j.val - 1) + 1 = j.val; omega
    · intro hj
      rw [Finset.mem_image] at hj
      obtain ⟨i, hiRp, rfl⟩ := hj
      simp only [hRpdef, hRdef, Finset.mem_filter, Finset.mem_univ, true_and] at hiRp
      obtain ⟨hbi, hilt⟩ := hiRp
      simp only [hNpdef, hNdef, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · rw [segA_nextSeg C i hilt]; exact hbi
      · unfold nextSeg; rw [dif_pos hilt]; simp
  -- the sum decomposition for any base point z (working over ℤ).
  have hsum : ∀ z : Pt, ∑ i : Fin m, F z i =
      (∑ i ∈ Rp, (F z i + F z (nextSeg i))) + (∑ i ∈ Re, F z i + ∑ i ∈ Ne, F z i)
        + ∑ i ∈ Rest, F z i := by
    intro z
    conv_lhs => rw [show (Finset.univ : Finset (Fin m)) = Rest ∪ (R ∪ N) from hcover]
    rw [Finset.sum_union hRestRN, Finset.sum_union hRN, hRsplit, hNsplit,
      Finset.sum_union hRdisj, Finset.sum_union hNdisj]
    -- ∑Np F = ∑Rp F (nextSeg ·).
    have hNpsum : ∑ i ∈ Np, F z i = ∑ i ∈ Rp, F z (nextSeg i) := by
      rw [hNpimg, Finset.sum_image]
      intro a ha b hb h
      have ha' : a.val + 1 < m := by
        have := Finset.mem_filter.mp ha; exact this.2
      have hb' : b.val + 1 < m := by
        have := Finset.mem_filter.mp hb; exact this.2
      exact nextSeg_injOn ha' hb' h
    rw [hNpsum, Finset.sum_add_distrib]
    abel
  -- now collect the eventual facts.
  -- (1) Rp pairs: parity constant.
  have hpairs : ∀ᶠ z in nhds z₀, ∀ i ∈ Rp,
      (F z i + F z (nextSeg i)) % 2 = (F z₀ i + F z₀ (nextSeg i)) % 2 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    simp only [hRpdef, hRdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hbi, hilt⟩ := hi
    -- shared vertex segB i = segA (nextSeg i), on the line; far endpoints off line.
    have hshare : C.segB i = C.segA (nextSeg i) := (segA_nextSeg C i hilt).symm
    have hdi : det2 η (C.segB i - C.segA i) ≠ 0 := hη.2 i
    have hdj : det2 η (C.segB (nextSeg i) - C.segA (nextSeg i)) ≠ 0 := hη.2 (nextSeg i)
    -- far endpoint of segment i (its start) off the line.
    have hfa : side η z₀ (C.segA i) ≠ 0 := fun h => hboth i ⟨h, hbi⟩
    -- far endpoint of nextSeg i (its end) off the line.
    have hfb : side η z₀ (C.segB (nextSeg i)) ≠ 0 := by
      intro h; exact hboth (nextSeg i) ⟨by rw [← hshare]; exact hbi, h⟩
    -- shared ray parameter nonzero (else z₀ = segB i, the shared vertex, in the carrier).
    have hτv : segTau η z₀ (C.segA i) (C.segB i) ≠ 0 := by
      intro h0
      apply hoff
      refine ⟨i, ?_⟩
      -- z₀ = lineMap (segA i) (segB i) (segU); shared vertex on line ⟹ segU = 1 ⟹ z₀ = segB i.
      have hrec := seg_cross_eq (η := η) (z := z₀) (a := C.segA i) (b := C.segB i) hdi
      rw [h0, zero_smul, add_zero] at hrec
      have hvz : det2 η (C.segB i - z₀) = 0 := by
        have : side η z₀ (C.segB i) = det2 η (C.segB i - z₀) := by unfold side; rfl
        rw [this] at hbi; exact hbi
      have hui : segU η z₀ (C.segA i) (C.segB i) = 1 := by
        unfold segU
        have hnum : det2 η (z₀ - C.segA i) = det2 η (C.segB i - C.segA i) := by
          have h1 : det2 η (z₀ - C.segA i)
              = det2 η (z₀ - C.segB i) + det2 η (C.segB i - C.segA i) := by
            rw [← det2_add_right]; congr 1; abel
          have h2 : det2 η (z₀ - C.segB i) = 0 := by
            have he : det2 η (z₀ - C.segB i) = -det2 η (C.segB i - z₀) := by
              unfold det2; simp only [PiLp.sub_apply]; ring
            rw [he, hvz]; ring
          rw [h1, h2, zero_add]
        rw [hnum, div_self hdi]
      rw [hui, AffineMap.lineMap_apply_one] at hrec
      rw [hrec, seg]; exact right_mem_segment ℝ _ _
    exact pair_segCrossInd_eventually_eq hshare hdi hdj hbi hfa hfb hτv
  -- (2) Re endpoint events (end on the last vertex): locally backward (EndpointSafe).
  -- (3) Ne endpoint events (start on the first vertex): locally backward (EndpointSafe).
  -- (4) Rest generic segments: locally constant.
  have hrest : ∀ᶠ z in nhds z₀, ∀ i ∈ Rest, F z i = F z₀ i := by
    rw [Filter.eventually_all_finset]
    intro i hi
    simp only [hRestdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact segCrossInd_eventually_eq_generic C hη hoff i hi.1 hi.2
  -- endpoint events: from EndpointSafe.  An end-on-last-vertex / start-on-first-vertex segment
  -- has its on-line endpoint as an unpaired endpoint; EndpointSafe forces backward.
  obtain ⟨hsafe0, hsafeL⟩ := hend
  -- For Re: i.succ = last m (as Fin (m+1)), i.e. i.val = m - 1; the chain's last segment.
  have hReback : ∀ᶠ z in nhds z₀, ∀ i ∈ Re, F z i = F z₀ i := by
    rw [Filter.eventually_all_finset]
    intro i hi
    simp only [hRedef, hRdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hbi, hilast⟩ := hi
    -- i.val + 1 = m, so i = ⟨m-1, _⟩; the on-line vertex segB i = p (last) is the last vertex.
    have hm : 0 < m := i.pos
    have hival : i.val = m - 1 := by omega
    have hlast : C.segB i = C.p (Fin.last m) := by
      unfold Chain.segB; congr 1; apply Fin.ext; simp [Fin.succ, Fin.last]; omega
    -- EndpointSafe last clause: side ≠ 0 ∨ segTau (last seg) < 0; the side is 0, so backward.
    have hτneg : segTau η z₀ (C.segA i) (C.segB i) < 0 := by
      rcases hsafeL with hne | ⟨_, hlt⟩
      · exact absurd (hlast ▸ hbi) hne
      · -- the last-segment tau is < 0; that segment is i.
        have hiseg : (⟨m - 1, by omega⟩ : Fin m) = i := by apply Fin.ext; simp; omega
        rw [Chain.segTauOf, hiseg] at hlt; exact hlt
    exact segCrossInd_eventually_eq_endpoint (hη.2 i) hτneg
  have hNeback : ∀ᶠ z in nhds z₀, ∀ i ∈ Ne, F z i = F z₀ i := by
    rw [Filter.eventually_all_finset]
    intro i hi
    simp only [hNedef, hNdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hai, hi0⟩ := hi
    have hm : 0 < m := i.pos
    -- i.val = 0, so i = ⟨0, _⟩; the on-line vertex segA i = p 0 is the first vertex.
    have hfirst : C.segA i = C.p 0 := by
      unfold Chain.segA; congr 1; apply Fin.ext; simp [Fin.castSucc, Fin.castAdd, Fin.castLE]; omega
    have hτneg : segTau η z₀ (C.segA i) (C.segB i) < 0 := by
      rcases hsafe0 with hne | ⟨_, hlt⟩
      · exact absurd (hfirst ▸ hai) hne
      · have hiseg : (⟨0, hm⟩ : Fin m) = i := by apply Fin.ext; simp; omega
        rw [Chain.segTauOf, hiseg] at hlt; exact hlt
    exact segCrossInd_eventually_eq_endpoint (hη.2 i) hτneg
  -- assemble.
  filter_upwards [hpairs, hrest, hReback, hNeback] with z hp hr hRe hNe
  show (∑ i : Fin m, F z i) % 2 = (∑ i : Fin m, F z₀ i) % 2
  rw [hsum z, hsum z₀]
  -- pair sums parity-equal; Re/Ne/Rest sums equal.
  have hpairsum :
      (∑ i ∈ Rp, (F z i + F z (nextSeg i))) % 2 =
      (∑ i ∈ Rp, (F z₀ i + F z₀ (nextSeg i))) % 2 := by
    rw [Finset.sum_int_mod, Finset.sum_int_mod
      (s := Rp) (f := fun i => F z₀ i + F z₀ (nextSeg i))]
    congr 1
    exact Finset.sum_congr rfl (fun i hi => hp i hi)
  have hReeq : ∑ i ∈ Re, F z i = ∑ i ∈ Re, F z₀ i :=
    Finset.sum_congr rfl (fun i hi => hRe i hi)
  have hNeeq : ∑ i ∈ Ne, F z i = ∑ i ∈ Ne, F z₀ i :=
    Finset.sum_congr rfl (fun i hi => hNe i hi)
  have hResteq : ∑ i ∈ Rest, F z i = ∑ i ∈ Rest, F z₀ i :=
    Finset.sum_congr rfl (fun i hi => hr i hi)
  -- combine mod 2: only the pair sum's parity matters; the rest are exactly equal.
  rw [hReeq, hNeeq, hResteq]
  -- goal is a `% 2` equality of two sums differing only in the pair block (parity-equal).
  have hpm : (∑ i ∈ Rp, (F z i + F z (nextSeg i))) ≡
      (∑ i ∈ Rp, (F z₀ i + F z₀ (nextSeg i))) [ZMOD 2] := hpairsum
  have := (hpm.add_right ((∑ i ∈ Re, F z₀ i + ∑ i ∈ Ne, F z₀ i) + ∑ i ∈ Rest, F z₀ i))
  -- reassociate to match the goal.
  calc (∑ i ∈ Rp, (F z i + F z (nextSeg i)) +
          (∑ i ∈ Re, F z₀ i + ∑ i ∈ Ne, F z₀ i) + ∑ i ∈ Rest, F z₀ i) % 2
      = ((∑ i ∈ Rp, (F z i + F z (nextSeg i))) +
          ((∑ i ∈ Re, F z₀ i + ∑ i ∈ Ne, F z₀ i) + ∑ i ∈ Rest, F z₀ i)) % 2 := by
        ring_nf
    _ = ((∑ i ∈ Rp, (F z₀ i + F z₀ (nextSeg i))) +
          ((∑ i ∈ Re, F z₀ i + ∑ i ∈ Ne, F z₀ i) + ∑ i ∈ Rest, F z₀ i)) % 2 := this
    _ = (∑ i ∈ Rp, (F z₀ i + F z₀ (nextSeg i)) +
          (∑ i ∈ Re, F z₀ i + ∑ i ∈ Ne, F z₀ i) + ∑ i ∈ Rest, F z₀ i) % 2 := by ring_nf

/-! ## §5. The along-ray coordinate and the far-point zero count

`lineCoord r η x p` is the position of `p` along the reference direction `r` relative to the
base `x`, normalised by the transverse `det2 r η`; it is affine on segments
(`lineCoord_on_line`).  The forward ray parameter `segTau` is exactly this coordinate read off a
ray point (`side_ray_eta`).  When the base point's coordinate exceeds every chain vertex's
coordinate, no segment is forward-crossed (`rayCount_zero_of_coordMax`). -/

/-- The along-`r` coordinate of `p` (base `x`, transverse normalisation `det2 r η`). -/
def lineCoord (r η x p : Pt) : ℝ := det2 (p - x) η / det2 r η

/-- `lineCoord` is affine along a segment. -/
lemma lineCoord_on_line (r η x a b : Pt) (u : ℝ) :
    lineCoord r η x (AffineMap.lineMap a b u)
      = (1 - u) * lineCoord r η x a + u * lineCoord r η x b := by
  unfold lineCoord
  rw [show (AffineMap.lineMap a b u - x : Pt) = (1 - u) • (a - x) + u • (b - x) by
    rw [AffineMap.lineMap_apply_module]; module,
    det2_add_left, det2_smul_left, det2_smul_left, add_div, mul_div_assoc, mul_div_assoc]

/-- **Side along the ray.**  Sliding the base point along the ray direction `η`:
`side η x (z + t•η) = side η x z + t · det2 η η = side η x z` … more usefully, the side of a
*ray point* against the ray-line through `x` reads `side r x (z + t•η) = side r x z + t·det2 r η`
for any reference `r` (the design's `side_ray_eta`). -/
lemma side_ray_eta (r x z η : Pt) (t : ℝ) :
    side r x (z + t • η) = side r x z + t * det2 r η := by
  unfold side
  rw [show (z + t • η - x : Pt) = (z - x) + t • η by abel, det2_add_right, det2_smul_right]

/-- **The foot parameter lies in `[0,1]` under a span** (weaker than `segU_mem_Icc`: one side may
be exactly `0`).  This is all that the far-point zero count needs. -/
lemma segU_mem_Icc_of_span {η z a b : Pt} (hden : det2 η (b - a) ≠ 0)
    (hspan : Span (side η z a) (side η z b)) :
    segU η z a b ∈ Set.Icc (0 : ℝ) 1 := by
  have hsa : det2 η (z - a) = -side η z a := by
    unfold side det2; simp only [PiLp.sub_apply]; ring
  have hDeq : det2 η (b - a) = side η z b - side η z a := (side_sub_side η z a b).symm
  set sa := side η z a with hsadef
  set sb := side η z b with hsbdef
  have hseg : segU η z a b = -sa / (sb - sa) := by rw [segU, hsa, hDeq]
  rw [hseg]
  rcases hspan with ⟨hsa', hsb'⟩ | ⟨hsb', hsa'⟩
  · -- sa ≤ 0, 0 < sb.
    refine ⟨?_, ?_⟩
    · apply div_nonneg (by linarith) (by linarith)
    · rw [div_le_one (by linarith)]; linarith
  · -- sb ≤ 0, 0 < sa.
    have h1 : -sa / (sb - sa) = sa / (sa - sb) := by
      rw [div_eq_div_iff (by linarith) (by linarith)]; ring
    rw [h1]
    refine ⟨?_, ?_⟩
    · apply div_nonneg (by linarith) (by linarith)
    · rw [div_le_one (by linarith)]; linarith

/-- **Far-point zero count.**  If, in the along-`r` coordinate (`0 < det2 r η`), every chain
vertex lies strictly behind the base point `z` (`lineCoord r η z (vertex) < 0`), then no segment
is forward-crossed and `rayCount η z = 0`.  A forward crossing would put the foot at coordinate
`segTau ≥ 0`, but the foot is a convex combination of two vertices, all of whose coordinates are
`< 0`. -/
lemma Chain.rayCount_zero_of_coordMax (C : Chain m) {η r z : Pt}
    (hrη : 0 < det2 r η) (hη : C.Transverse η)
    (hmax : ∀ i : Fin m,
      lineCoord r η z (C.segA i) < 0 ∧ lineCoord r η z (C.segB i) < 0) :
    C.rayCount η z = 0 := by
  classical
  -- `lineCoord r η z p < 0` with `0 < det2 r η` gives `det2 (p - z) η < 0`, i.e. the side
  -- `side η z p = det2 η (p - z) = -det2 (p - z) η > 0`.  All vertices strictly on one side of
  -- the ray line ⟹ no segment span-crosses ⟹ every indicator is `0`.
  have hpos : ∀ p : Pt, lineCoord r η z p < 0 → 0 < side η z p := by
    intro p hp
    unfold lineCoord at hp
    rw [div_neg_iff] at hp
    rcases hp with ⟨_, hden_neg⟩ | ⟨hnum_neg, _⟩
    · exact absurd hden_neg (not_lt.mpr (le_of_lt hrη))
    · have hs : side η z p = -det2 (p - z) η := by
        unfold side det2; simp only [PiLp.sub_apply]; ring
      rw [hs]; linarith
  have hside : ∀ i : Fin m, 0 < side η z (C.segA i) ∧ 0 < side η z (C.segB i) := by
    intro i
    obtain ⟨ha, hb⟩ := hmax i
    exact ⟨hpos _ ha, hpos _ hb⟩
  unfold Chain.rayCount
  rw [Finset.sum_eq_zero]
  intro i _
  unfold segCrossInd SegCrossesRay
  rw [if_neg]
  rintro ⟨hspan, _⟩
  obtain ⟨ha, hb⟩ := hside i
  -- both sides strictly positive ⟹ no span.
  exact span_false_same_pos ha hb hspan

/-! ## §4. Transport along a segment -/

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Parity transport along a boundary-free, endpoint-safe segment.**  If the open straight
segment from `z₀` to `z₁` avoids the carrier and stays endpoint-safe throughout, the crossing
parity is the same at the two ends.  Connectedness of `Icc 0 1` plus the local constancy of
the sweep, pulled back along `lineMap`. -/
theorem Chain.rayCountParity_constant_on_segment (C : Chain m) {η z₀ z₁ : Pt}
    (hη : C.Transverse η)
    (havoid : ∀ t ∈ Set.Icc (0:ℝ) 1, AffineMap.lineMap z₀ z₁ t ∉ C.carrier)
    (hend : ∀ t ∈ Set.Icc (0:ℝ) 1, C.EndpointSafe η (AffineMap.lineMap z₀ z₁ t)) :
    C.rayCount η z₀ % 2 = C.rayCount η z₁ % 2 := by
  classical
  haveI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) := by
    rw [← isPreconnected_iff_preconnectedSpace]; exact isPreconnected_Icc
  set γ : ℝ → Pt := fun t => AffineMap.lineMap z₀ z₁ t with hγ
  set f : Set.Icc (0 : ℝ) 1 → ℤ := fun t => C.rayCount η (γ (t : ℝ)) % 2 with hf
  have hcont : Continuous (fun t : Set.Icc (0:ℝ) 1 => γ (t : ℝ)) := by
    apply Continuous.comp _ continuous_subtype_val
    show Continuous (fun t : ℝ => AffineMap.lineMap z₀ z₁ t)
    exact AffineMap.lineMap_continuous
  have hLC : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    have hoff : γ (t : ℝ) ∉ C.carrier := havoid (t : ℝ) t.2
    have hendt : C.EndpointSafe η (γ (t : ℝ)) := hend (t : ℝ) t.2
    have hev := C.rayCountParity_eventually_eq hη hoff hendt
    have htends : Filter.Tendsto (fun s : Set.Icc (0:ℝ) 1 => γ (s : ℝ))
        (nhds t) (nhds (γ (t : ℝ))) := hcont.tendsto t
    filter_upwards [htends.eventually hev] with s hs
    simp only [hf]; exact hs
  have hconst := (IsLocallyConstant.iff_is_const.mp hLC)
    (⟨0, ⟨le_refl 0, zero_le_one⟩⟩ : Set.Icc (0:ℝ) 1)
    (⟨1, ⟨zero_le_one, le_refl 1⟩⟩ : Set.Icc (0:ℝ) 1)
  simp only [hf, hγ] at hconst
  rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at hconst
  exact hconst

end

end ProofsInTheBook.ZinanCh36ArcSweep

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.ZinanCh36ArcSweep.span_mod_two_through_vertex_int
#print axioms ProofsInTheBook.ZinanCh36ArcSweep.seg_cross_eq
#print axioms ProofsInTheBook.ZinanCh36ArcSweep.onSeg_of_segTau_zero_span
#print axioms ProofsInTheBook.ZinanCh36ArcSweep.segCrossInd_eventually_eq_generic
#print axioms ProofsInTheBook.ZinanCh36ArcSweep.pair_segCrossInd_eventually_eq
#print axioms ProofsInTheBook.ZinanCh36ArcSweep.Chain.rayCountParity_eventually_eq
#print axioms ProofsInTheBook.ZinanCh36ArcSweep.Chain.rayCountParity_constant_on_segment
#print axioms ProofsInTheBook.ZinanCh36ArcSweep.lineCoord_on_line
#print axioms ProofsInTheBook.ZinanCh36ArcSweep.side_ray_eta
#print axioms ProofsInTheBook.ZinanCh36ArcSweep.Chain.rayCount_zero_of_coordMax
