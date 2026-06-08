import ProofsInTheBook.PolygonWindingZero
import ProofsInTheBook.PolygonContainment

/-!
# Chapter 36 — closing the exterior signed-winding-zero residue (`PolygonWindingExterior`)

`PolygonWinding` / `PolygonWindingZero` reduced `OffDiagDisjoint` to the single named
side-aware Jordan residue `ExteriorWindingZero` (a point strictly off the diagonal line, on
the exterior side of an ear, has zero SIGNED winding around that ear).  This module discharges
`ExteriorWindingZero` *unconditionally*, by mechanizing the ChatGPT-Pro design
(`HANDOFF/CH36_WINDING_DESIGN.md`):

* **(A) signed local constancy off the boundary.**  `windCross Q σ ·` is locally constant in
  the base point off the boundary.  The substrate's `RayDirection` forbids any edge parallel to
  the ray (`no_adjacent_vertices_both_on_rayLine`), so every degenerate ray-block is a *singleton
  vertex* — the design's general maximal-ray-block machinery collapses to the singleton vertex
  event, which is handled by the SIGNED transfer truth table (`signedPair_eventually_eq`): at a
  vertex on the ray line the two incident signed contributions *transfer* (they do not always
  cancel), and the cluster sum is locally constant.  Generic edges use the existing
  `rawInd_eventually_eq_basepoint_generic`.

* **(B) the half-plane escape (no Jordan).**  With the subpolygon boundary in the closed
  half-plane `side ≤ 0` and the base point strictly on `side > 0`, the straight escape path
  `γ t = x + t•v` (`v` chosen with `0 < det2 (b-a) v` and `v.x ≠ 0`) stays on `side > 0`, hence
  avoids the boundary; its far endpoint, with `x`-coordinate outside the polygon's range, has
  zero winding (`windCross_eq_zero_of_all_strictSide`); local constancy transports `0` back to
  `x`.

These two facts discharge `ExteriorWindingZero` via the existing
`exteriorWindingZero_of_windZeroExterior` chain, closing `WindZeroExterior` and hence
`OffDiagDisjoint`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PolygonWindingExterior

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonOracle
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonVertexSweep
open ProofsInTheBook.PolygonWinding
open ProofsInTheBook.PolygonWindingZero
open Filter Topology
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part A0: the signed per-edge contribution as `edgeSign · status`

`rawSignedInd` of a polygon edge factors as the base-point-independent orientation sign
`edgeSign` times the unsigned `EdgeCrossesRay'` indicator.  This is the bridge from the signed
winding to the side-coordinate status machinery (`statusOf'`, `crossTau`, `crossU`). -/

/-- The signed contribution of polygon edge `i` at base point `z`. -/
def sEdge (P : StrictSimplePolygon n) (ρ : RayDirection P) (z : Pt) (i : Fin n) : ℤ :=
  rawSignedInd ρ.r z (P.q i) (P.q (cyclicNext i))

/-- The base-point-independent orientation sign of polygon edge `i`. -/
def eSign (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n) : ℤ :=
  edgeSign ρ.r (P.q i) (P.q (cyclicNext i))

/-- `sEdge = eSign · [EdgeCrossesRay']` (signed indicator factors). -/
lemma sEdge_eq_eSign_mul (P : StrictSimplePolygon n) (ρ : RayDirection P) (z : Pt) (i : Fin n) :
    sEdge P ρ z i = eSign P ρ i * (if EdgeCrossesRay' P ρ z i then 1 else 0) := by
  classical
  unfold sEdge eSign
  rw [rawSignedInd_eq_edgeSign_mul]
  congr 1
  unfold rawInd
  have hiff := edgeCrossesRay'_eq_raw P ρ z i
  by_cases h : RawEdgeCrosses ρ.r z (P.q i) (P.q (cyclicNext i))
  · rw [if_pos h, if_pos (hiff.mpr h)]; norm_num
  · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]; norm_num

/-- `windCross` as the signed sum of per-edge contributions. -/
lemma windCross_eq_sum_sEdge (P : StrictSimplePolygon n) (ρ : RayDirection P) (z : Pt) :
    windCross P ρ z = ∑ i : Fin n, sEdge P ρ z i := by
  rw [windCross_eq]; rfl

/-! ## Part A1: continuity of the base-point crossing data and the forward parameter

`side ρ.r · v` and `crossTau P ρ · i` are affine, hence continuous, in the base point.  The
existing `continuous_side_basepoint` / `continuous_rawTau_basepoint` give continuity; `crossTau`
coincides with the `rawTau` of the edge endpoints. -/

/-- `crossTau P ρ z i` is the `rawTau` of the edge endpoints (definitional). -/
lemma crossTau_eq_rawTau (P : StrictSimplePolygon n) (ρ : RayDirection P) (z : Pt) (i : Fin n) :
    crossTau P ρ z i =
      det2 (P.q i - z) (P.q (cyclicNext i) - P.q i) / det2 ρ.r (P.q (cyclicNext i) - P.q i) := by
  unfold crossTau crossDen; rfl

/-- `fun z => crossTau P ρ z i` is continuous in the base point. -/
lemma continuous_crossTau_basepoint (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n) :
    Continuous (fun z : Pt => crossTau P ρ z i) := by
  have h := continuous_rawTau_basepoint ρ.r (P.q i) (P.q (cyclicNext i))
  have heq : (fun z : Pt => crossTau P ρ z i) =
      (fun z : Pt => det2 (P.q i - z) (P.q (cyclicNext i) - P.q i) /
        det2 ρ.r (P.q (cyclicNext i) - P.q i)) := by
    funext z; exact crossTau_eq_rawTau P ρ z i
  rw [heq]; exact h

/-- **Forward parameter nonzero at a vertex event off the boundary.**  If edge `i`'s end vertex
is on the ray line at `x₀` (`crossU = 1`) and `x₀ ∉ boundary`, the forward parameter is nonzero
(otherwise the ray reaches the vertex at `τ = 0`, i.e. `x₀` is that vertex, on the boundary). -/
lemma crossTau_event_ne_zero (P : StrictSimplePolygon n) (ρ : RayDirection P) {x₀ : Pt}
    (hoff : ¬ OnBoundary P x₀) {i : Fin n} (hu : crossU P ρ x₀ i = 1) :
    crossTau P ρ x₀ i ≠ 0 := by
  intro h0
  have hrec := reconstruct_u_eq_one P ρ x₀ i hu
  rw [h0, zero_smul, add_zero] at hrec
  apply hoff
  exact ⟨cyclicNext i, by rw [hrec, Edge]; exact left_mem_segment ℝ _ _⟩

/-! ## Part A2: the SIGNED vertex transfer truth table

At a vertex `v` on the ray line (side value `s`, any sign), shared by the incoming edge with
far endpoint side `a ≠ 0` and the outgoing edge with far endpoint side `b ≠ 0`, the SIGNED
contribution of the two incident edges is **independent of `s`**.  The incoming edge `a → v`
carries orientation sign `edgeSign = (if 0 < s - a)`; the outgoing edge `v → b` carries
`edgeSign = (if 0 < b - s)`.  Unlike the unsigned/parity case (`span_mod_two_through_vertex`,
which only cancels mod 2), the signed sum is *integer*-constant: at a transverse vertex the
crossing is *transferred* from one incident edge to the other with the same sign.

The orientation signs are written with the values `a, s, b` directly so that the lemma applies
to *every* nearby base point (the orientation signs are base-point-independent, but their value
is read off the side values at `x₀`, where `s = 0`). -/

/-- The signed `±1` orientation factor of an edge whose endpoint side values differ by `d`. -/
def osign (d : ℝ) : ℤ := if 0 < d then 1 else -1

/-- The signed contribution of the two edges incident to a vertex with side value `s`, far
endpoint side values `a` (incoming) and `b` (outgoing).  The orientation signs are
`osign (s - a)` (= sign of `det2 r (v - a_pt)`) and `osign (b - s)`. -/
def vTransfer (a b s : ℝ) : ℤ :=
  osign (s - a) * (if Span a s then 1 else 0) +
    osign (b - s) * (if Span s b then 1 else 0)

/-- **`vTransfer` at a fixed sign pattern of `(a,b)` is a constant** (the four-case truth table).
For each of the four strict-sign patterns of `(a,b)` (both far endpoints nonzero) we evaluate
`vTransfer a b s` for all `s` by resolving the two `Span` indicators from the trichotomy of `s`.
The value is `0 / -1 / +1 / 0` for `(++, +-, -+, --)` — the crossing transfers with sign. -/
lemma vTransfer_const {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (s : ℝ) :
    vTransfer a b s =
      (if a < 0 then (if 0 < b then 1 else 0) else (if 0 < b then 0 else -1)) := by
  classical
  unfold vTransfer osign Span
  rcases lt_or_gt_of_ne ha with ha' | ha' <;>
    rcases lt_or_gt_of_ne hb with hb' | hb' <;>
      rcases lt_trichotomy s 0 with hs | hs | hs <;>
        split_ifs <;>
        -- normalise negated `Span`-disjunctions into conjunctions of linear bounds, break every
        -- positive `Span`-disjunction into its two cases, then each goal is numeric-true or a
        -- sign contradiction.
        ((try simp only [not_or, not_and_or, not_lt, not_le] at *) <;>
          (try casesm* _ ∨ _, _ ∧ _) <;>
          first | rfl | (exfalso; linarith))

lemma signed_vertex_transfer {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (s s' : ℝ) :
    vTransfer a b s = vTransfer a b s' := by
  rw [vTransfer_const ha hb s, vTransfer_const ha hb s']

/-! ## Part A3: bridging `sEdge` to the side coordinates and the signed pair lemma

`eSign` is `osign` of the endpoint side difference; in the forward regime the signed per-edge
contribution `sEdge` factors as `eSign · [Span …]`, so a vertex-event pair sum reads off the
`vTransfer` truth table. -/

/-- `eSign P ρ i = osign (side(end) - side(start))` for any base point `z` (the orientation sign
is the half-plane direction of the crossing, `det2 r (b - a) = side b - side a`). -/
lemma eSign_eq_osign (P : StrictSimplePolygon n) (ρ : RayDirection P) (z : Pt) (i : Fin n) :
    eSign P ρ i = osign (side ρ.r z (P.q (cyclicNext i)) - side ρ.r z (P.q i)) := by
  unfold eSign edgeSign osign
  rw [det2_eq_side_diff ρ.r z (P.q i) (P.q (cyclicNext i))]

/-- **Forward-regime per-edge value.**  Off the boundary, when the forward parameter is strictly
positive, the signed contribution of edge `i` is `eSign · [Span (side start) (side end)]`. -/
lemma sEdge_forward (P : StrictSimplePolygon n) (ρ : RayDirection P) (z : Pt) (i : Fin n)
    (hτ : 0 < crossTau P ρ z i) :
    sEdge P ρ z i =
      eSign P ρ i * (if Span (side ρ.r z (P.q i)) (side ρ.r z (P.q (cyclicNext i)))
        then 1 else 0) := by
  classical
  rw [sEdge_eq_eSign_mul]
  congr 1
  by_cases hsp : Span (side ρ.r z (P.q i)) (side ρ.r z (P.q (cyclicNext i)))
  · rw [if_pos hsp, if_pos]
    rw [EdgeCrossesRay', SpanCrossesSide]
    exact ⟨hsp, le_of_lt hτ⟩
  · rw [if_neg hsp, if_neg]
    rw [EdgeCrossesRay', SpanCrossesSide]
    rintro ⟨h, _⟩; exact hsp h

/-- **Backward-regime per-edge value.**  Off the boundary, when the forward parameter is strictly
negative, edge `i` does not cross, so its signed contribution is `0`. -/
lemma sEdge_backward (P : StrictSimplePolygon n) (ρ : RayDirection P) (z : Pt) (i : Fin n)
    (hτ : crossTau P ρ z i < 0) :
    sEdge P ρ z i = 0 := by
  classical
  rw [sEdge_eq_eSign_mul, if_neg, mul_zero]
  rw [EdgeCrossesRay', SpanCrossesSide]
  rintro ⟨_, h⟩; linarith

/-- **Signed vertex-event pair, eventually constant (2D base point).**  At a base point `x₀` off
the boundary where the end vertex of edge `i` is on the ray line (`crossU = 1`, i.e.
`side x₀ (q (next i)) = 0`), the signed two-edge contribution `sEdge i + sEdge (next i)` is
locally constant: in the backward regime both vanish; in the forward regime the value reads off
the `vTransfer` truth table, constant as the vertex side value varies. -/
lemma signedPair_eventually_eq (P : StrictSimplePolygon n) (ρ : RayDirection P) {x₀ : Pt}
    (hoff : ¬ OnBoundary P x₀) {i : Fin n} (hu : crossU P ρ x₀ i = 1) :
    ∀ᶠ z in nhds x₀,
      sEdge P ρ z i + sEdge P ρ z (cyclicNext i) =
        sEdge P ρ x₀ i + sEdge P ρ x₀ (cyclicNext i) := by
  classical
  set k := cyclicNext i with hk
  -- the end vertex of edge `i` is on the ray line.
  have hsv : side ρ.r x₀ (P.q (cyclicNext i)) = 0 :=
    (side_next_zero_iff_crossU_one P ρ x₀ i).mpr hu
  -- shared ray parameter τ_v ≠ 0 (else x₀ is the vertex, a boundary point).
  have hτvne : crossTau P ρ x₀ i ≠ 0 := crossTau_event_ne_zero P ρ hoff hu
  -- the two edges' forward parameters agree at the event.
  have hτk0 : crossTau P ρ x₀ k = crossTau P ρ x₀ i := crossTau_event_eq P ρ x₀ i hu
  -- far endpoints off the ray line.
  obtain ⟨ha, hb⟩ := event_far_endpoints_ne P ρ x₀ i hsv
  -- continuity of the two forward parameters and of the three side coordinates.
  have hcτi := continuous_crossTau_basepoint P ρ i
  have hcτk := continuous_crossTau_basepoint P ρ k
  have hca := continuous_side_basepoint ρ.r (P.q i)
  have hcb := continuous_side_basepoint ρ.r (P.q (cyclicNext (cyclicNext i)))
  -- far endpoints stay nonzero near x₀.
  have eva : ∀ᶠ z in nhds x₀, side ρ.r z (P.q i) ≠ 0 := by
    rcases lt_or_gt_of_ne ha with h | h
    · filter_upwards [(hca.tendsto x₀).eventually_lt_const h] with z hz using ne_of_lt hz
    · filter_upwards [(hca.tendsto x₀).eventually_const_lt h] with z hz using ne_of_gt hz
  have evb : ∀ᶠ z in nhds x₀, side ρ.r z (P.q (cyclicNext (cyclicNext i))) ≠ 0 := by
    rcases lt_or_gt_of_ne hb with h | h
    · filter_upwards [(hcb.tendsto x₀).eventually_lt_const h] with z hz using ne_of_lt hz
    · filter_upwards [(hcb.tendsto x₀).eventually_const_lt h] with z hz using ne_of_gt hz
  rcases lt_or_gt_of_ne hτvne with hback | hfwd
  · -- BACKWARD: τ_v < 0; both edges uncounted near and at x₀ → pair sum 0.
    have hτi0 : crossTau P ρ x₀ i < 0 := hback
    have hτk00 : crossTau P ρ x₀ k < 0 := by rw [hτk0]; exact hback
    have evτi : ∀ᶠ z in nhds x₀, crossTau P ρ z i < 0 := by
      filter_upwards [(hcτi.tendsto x₀).eventually_lt_const hτi0] with z hz using hz
    have evτk : ∀ᶠ z in nhds x₀, crossTau P ρ z k < 0 := by
      filter_upwards [(hcτk.tendsto x₀).eventually_lt_const hτk00] with z hz using hz
    filter_upwards [evτi, evτk] with z hτi hτk
    rw [sEdge_backward P ρ z i hτi, sEdge_backward P ρ z k hτk,
        sEdge_backward P ρ x₀ i hτi0, sEdge_backward P ρ x₀ k hτk00]
  · -- FORWARD: τ_v > 0; both contributions are span-only; pair sum = vTransfer, constant.
    have hτi0 : 0 < crossTau P ρ x₀ i := hfwd
    have hτk00 : 0 < crossTau P ρ x₀ k := by rw [hτk0]; exact hfwd
    have evτi : ∀ᶠ z in nhds x₀, 0 < crossTau P ρ z i := by
      filter_upwards [(hcτi.tendsto x₀).eventually_const_lt hτi0] with z hz using hz
    have evτk : ∀ᶠ z in nhds x₀, 0 < crossTau P ρ z k := by
      filter_upwards [(hcτk.tendsto x₀).eventually_const_lt hτk00] with z hz using hz
    -- the far endpoints keep their strict sign near x₀ (sign-preservation neighbourhoods).
    have evsA : ∀ᶠ z in nhds x₀,
        (side ρ.r z (P.q i) < 0 ↔ side ρ.r x₀ (P.q i) < 0) := by
      rcases lt_or_gt_of_ne ha with h | h
      · filter_upwards [(hca.tendsto x₀).eventually_lt_const h] with z hz
        exact ⟨fun _ => h, fun _ => hz⟩
      · filter_upwards [(hca.tendsto x₀).eventually_const_lt h] with z hz
        constructor <;> intro hh <;> linarith
    have evsB : ∀ᶠ z in nhds x₀,
        (0 < side ρ.r z (P.q (cyclicNext (cyclicNext i))) ↔
          0 < side ρ.r x₀ (P.q (cyclicNext (cyclicNext i)))) := by
      rcases lt_or_gt_of_ne hb with h | h
      · filter_upwards [(hcb.tendsto x₀).eventually_lt_const h] with z hz
        constructor <;> intro hh <;> linarith
      · filter_upwards [(hcb.tendsto x₀).eventually_const_lt h] with z hz
        exact ⟨fun _ => h, fun _ => hz⟩
    filter_upwards [evτi, evτk, eva, evb, evsA, evsB]
      with z hτi hτk haz hbz hsA hsB
    -- both pairs equal `vTransfer` of their side coordinates (forward regime).
    have hzval : sEdge P ρ z i + sEdge P ρ z k =
        vTransfer (side ρ.r z (P.q i)) (side ρ.r z (P.q (cyclicNext (cyclicNext i))))
          (side ρ.r z (P.q (cyclicNext i))) := by
      rw [sEdge_forward P ρ z i hτi, sEdge_forward P ρ z k hτk,
          eSign_eq_osign P ρ z i, eSign_eq_osign P ρ z k]; rfl
    have hx0val : sEdge P ρ x₀ i + sEdge P ρ x₀ k =
        vTransfer (side ρ.r x₀ (P.q i)) (side ρ.r x₀ (P.q (cyclicNext (cyclicNext i))))
          (side ρ.r x₀ (P.q (cyclicNext i))) := by
      rw [sEdge_forward P ρ x₀ i hτi0, sEdge_forward P ρ x₀ k hτk00,
          eSign_eq_osign P ρ x₀ i, eSign_eq_osign P ρ x₀ k]; rfl
    rw [hzval, hx0val]
    -- reduce both vTransfer to their constant value; the sign patterns of (a,b) match.
    rw [vTransfer_const haz hbz, vTransfer_const ha hb]
    -- the two nested `if`-values agree because the far endpoints share sign at z and x₀.
    by_cases hA : side ρ.r x₀ (P.q i) < 0
    · rw [if_pos hA, if_pos (hsA.mpr hA)]
      by_cases hB : 0 < side ρ.r x₀ (P.q (cyclicNext (cyclicNext i)))
      · rw [if_pos hB, if_pos (hsB.mpr hB)]
      · rw [if_neg hB, if_neg (fun hh => hB (hsB.mp hh))]
    · rw [if_neg hA, if_neg (fun hh => hA (hsA.mp hh))]
      by_cases hB : 0 < side ρ.r x₀ (P.q (cyclicNext (cyclicNext i)))
      · rw [if_pos hB, if_pos (hsB.mpr hB)]
      · rw [if_neg hB, if_neg (fun hh => hB (hsB.mp hh))]

/-! ## Part A4: generic-edge signed local constancy and the full assembly

A *generic* edge at `x₀` (neither endpoint on the ray line, forward parameter nonzero) has
locally constant unsigned indicator (`rawInd_eventually_eq_basepoint_generic`); since the
orientation sign is base-point-independent, the signed contribution `sEdge` is also locally
constant.  We then assemble: split the edges into the `crossU = 1` representatives `R`, their
cyclic successors `N`, and the non-event `Rest`; the `R`-pairs are handled by
`signedPair_eventually_eq`, the `Rest` edges by the generic lemma. -/

/-- **Generic-edge signed local constancy (forward-parameter form).**  At `x₀` with both
endpoints off the ray line (`side ≠ 0`) and forward parameter nonzero, the signed contribution
`sEdge i` is locally constant in the base point. -/
lemma sEdge_eventually_eq_generic_tau (P : StrictSimplePolygon n) (ρ : RayDirection P) {x₀ : Pt}
    {i : Fin n}
    (ha : side ρ.r x₀ (P.q i) ≠ 0) (hb : side ρ.r x₀ (P.q (cyclicNext i)) ≠ 0)
    (hτ : crossTau P ρ x₀ i ≠ 0) :
    ∀ᶠ z in nhds x₀, sEdge P ρ z i = sEdge P ρ x₀ i := by
  classical
  have hτ' : det2 (P.q i - x₀) (P.q (cyclicNext i) - P.q i) /
      det2 ρ.r (P.q (cyclicNext i) - P.q i) ≠ 0 := by
    rw [← crossTau_eq_rawTau]; exact hτ
  have hev := rawInd_eventually_eq_basepoint_generic (r := ρ.r) (a := P.q i)
    (b := P.q (cyclicNext i)) (x₀ := x₀) ha hb hτ'
  filter_upwards [hev] with z hz
  rw [sEdge_eq_eSign_mul, sEdge_eq_eSign_mul]
  congr 1
  -- the unsigned indicators agree; bridge `rawInd` ↔ `EdgeCrossesRay'`.
  have hzc := edgeCrossesRay'_eq_raw P ρ z i
  have hx0c := edgeCrossesRay'_eq_raw P ρ x₀ i
  by_cases h0 : RawEdgeCrosses ρ.r x₀ (P.q i) (P.q (cyclicNext i))
  · have h1 : RawEdgeCrosses ρ.r z (P.q i) (P.q (cyclicNext i)) := by
      have : rawInd ρ.r z (P.q i) (P.q (cyclicNext i)) = 1 := by
        rw [hz]; unfold rawInd; rw [if_pos h0]
      unfold rawInd at this; by_contra hc; rw [if_neg hc] at this; norm_num at this
    rw [if_pos (hzc.mpr h1), if_pos (hx0c.mpr h0)]
  · have h1 : ¬ RawEdgeCrosses ρ.r z (P.q i) (P.q (cyclicNext i)) := by
      have : rawInd ρ.r z (P.q i) (P.q (cyclicNext i)) = 0 := by
        rw [hz]; unfold rawInd; rw [if_neg h0]
      unfold rawInd at this; by_contra hc; rw [if_pos hc] at this; norm_num at this
    rw [if_neg (fun hh => h1 (hzc.mp hh)), if_neg (fun hh => h0 (hx0c.mp hh))]

/-- **Generic-edge signed local constancy (Rest form).**  At `x₀` off the boundary with both
endpoints off the ray line (`side ≠ 0`), the signed contribution `sEdge i` is locally constant.
If the forward parameter is nonzero this is the tau form; otherwise the edge does not span (a
spanning edge with `crossTau = 0` would put `x₀` on the boundary), so the contribution is
locally `0`. -/
lemma sEdge_eventually_eq_rest (P : StrictSimplePolygon n) (ρ : RayDirection P) {x₀ : Pt}
    (hoff : ¬ OnBoundary P x₀) {i : Fin n}
    (ha : side ρ.r x₀ (P.q i) ≠ 0) (hb : side ρ.r x₀ (P.q (cyclicNext i)) ≠ 0) :
    ∀ᶠ z in nhds x₀, sEdge P ρ z i = sEdge P ρ x₀ i := by
  classical
  by_cases hτ : crossTau P ρ x₀ i = 0
  · -- `crossTau = 0`: a span here would force `x₀` on the edge.  So no span; both far sides
    -- nonzero ⟹ span locally false ⟹ contribution locally `0`.
    have hnospan : ¬ SpanCrossesSide P ρ x₀ i := by
      intro hspan
      exact hoff ⟨i, crossTau_eq_zero_span_imp_onEdge P ρ x₀ i hτ hspan⟩
    -- `SpanCrossesSide = Span (side a) (side b)`; far sides keep sign, so span stays false.
    have hca := continuous_side_basepoint ρ.r (P.q i)
    have hcb := continuous_side_basepoint ρ.r (P.q (cyclicNext i))
    have evsa : ∀ᶠ z in nhds x₀,
        (0 < side ρ.r z (P.q i) ↔ 0 < side ρ.r x₀ (P.q i)) ∧
        (side ρ.r z (P.q i) < 0 ↔ side ρ.r x₀ (P.q i) < 0) := by
      rcases lt_or_gt_of_ne ha with h | h
      · filter_upwards [(hca.tendsto x₀).eventually_lt_const h] with z hz
        exact ⟨⟨fun hp => by linarith, fun hp => by linarith⟩, ⟨fun _ => h, fun _ => hz⟩⟩
      · filter_upwards [(hca.tendsto x₀).eventually_const_lt h] with z hz
        exact ⟨⟨fun _ => h, fun _ => hz⟩, ⟨fun hn => by linarith, fun hn => by linarith⟩⟩
    have evsb : ∀ᶠ z in nhds x₀,
        (0 < side ρ.r z (P.q (cyclicNext i)) ↔ 0 < side ρ.r x₀ (P.q (cyclicNext i))) ∧
        (side ρ.r z (P.q (cyclicNext i)) < 0 ↔ side ρ.r x₀ (P.q (cyclicNext i)) < 0) := by
      rcases lt_or_gt_of_ne hb with h | h
      · filter_upwards [(hcb.tendsto x₀).eventually_lt_const h] with z hz
        exact ⟨⟨fun hp => by linarith, fun hp => by linarith⟩, ⟨fun _ => h, fun _ => hz⟩⟩
      · filter_upwards [(hcb.tendsto x₀).eventually_const_lt h] with z hz
        exact ⟨⟨fun _ => h, fun _ => hz⟩, ⟨fun hn => by linarith, fun hn => by linarith⟩⟩
    have hsx0 : sEdge P ρ x₀ i = 0 := by
      rw [sEdge_eq_eSign_mul, if_neg, mul_zero]
      rw [EdgeCrossesRay']; rintro ⟨h, _⟩; exact hnospan h
    rw [hsx0]
    filter_upwards [evsa, evsb] with z hsa hsb
    rw [sEdge_eq_eSign_mul, if_neg, mul_zero]
    rw [EdgeCrossesRay']; rintro ⟨h, _⟩
    apply hnospan
    -- transfer the span from `z` to `x₀` via matching strict signs.
    rw [SpanCrossesSide] at h ⊢
    show Span (side ρ.r x₀ (P.q i)) (side ρ.r x₀ (P.q (cyclicNext i)))
    have hza : side ρ.r z (P.q i) ≠ 0 := by
      rcases lt_or_gt_of_ne ha with h | h
      · exact ne_of_lt (hsa.2.mpr h)
      · exact ne_of_gt (hsa.1.mpr h)
    have hzb : side ρ.r z (P.q (cyclicNext i)) ≠ 0 := by
      rcases lt_or_gt_of_ne hb with h | h
      · exact ne_of_lt (hsb.2.mpr h)
      · exact ne_of_gt (hsb.1.mpr h)
    rw [span_iff_opp_sign ha hb]
    rw [span_iff_opp_sign hza hzb] at h
    -- products have the same sign at z and x₀.
    rcases lt_or_gt_of_ne ha with hsa' | hsa' <;> rcases lt_or_gt_of_ne hb with hsb' | hsb'
    · nlinarith [hsa.2.mpr hsa', hsb.2.mpr hsb']
    · nlinarith [hsa.2.mpr hsa', hsb.1.mpr hsb']
    · nlinarith [hsa.1.mpr hsa', hsb.2.mpr hsb']
    · nlinarith [hsa.1.mpr hsa', hsb.1.mpr hsb']
  · exact sEdge_eventually_eq_generic_tau P ρ ha hb hτ

/-! ## Part A5: the full signed local-constancy theorem -/

/-- **Signed local constancy off the boundary (Part A headline).**  For a strict simple polygon
`Q` with ray `σ`, the signed winding `windCross Q σ ·` is locally constant in the base point at
every off-boundary point.  Edges split into the end-vertex events `R` (`crossU = 1`), their
cyclic successors `N` (`crossU = 0`), and generic `Rest`; the `R`-pairs use the signed transfer
(`signedPair_eventually_eq`), the `Rest` edges the generic constancy (`sEdge_eventually_eq_rest`).
This subsumes the generic-stratum `windCross_eventually_eq_basepoint_generic`. -/
theorem windCross_locally_constant_off_boundary {m : ℕ} (Q : StrictSimplePolygon m)
    (σ : RayDirection Q) {x : Pt} (hx : ¬ OnBoundary Q x) :
    ∀ᶠ y in nhds x, windCross Q σ y = windCross Q σ x := by
  classical
  have htwo : 2 ≤ m := Nat.le_trans (by decide) Q.hthree
  -- R = end-vertex events; N = start-vertex events; Rest = generic.
  set R : Finset (Fin m) := Finset.univ.filter (fun i => crossU Q σ x i = 1) with hR
  set N : Finset (Fin m) := Finset.univ.filter (fun i => crossU Q σ x i = 0) with hN
  have hRmem : ∀ i, i ∈ R ↔ crossU Q σ x i = 1 := by
    intro i; rw [hR, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hNmem : ∀ i, i ∈ N ↔ crossU Q σ x i = 0 := by
    intro i; rw [hN, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  -- N = cyclicNext '' R.
  have hNimg : N = R.image cyclicNext := by
    apply Finset.ext; intro k
    rw [hNmem, Finset.mem_image]
    constructor
    · intro hk0
      refine ⟨cyclicPrev k, ?_, cyclicNext_cyclicPrev htwo k⟩
      rw [hRmem]; exact (u_eq_one_of_u_eq_zero_prev Q σ x k hk0).1
    · rintro ⟨i, hi1, rfl⟩
      rw [hRmem] at hi1; exact (u_eq_zero_of_u_eq_one_next Q σ x i hi1).1
  have hdisj : Disjoint R N := by
    rw [Finset.disjoint_left]; intro i hiR hiN
    rw [hRmem] at hiR; rw [hNmem] at hiN; rw [hiR] at hiN; norm_num at hiN
  set Rest : Finset (Fin m) := Finset.univ \ (R ∪ N) with hRest
  have hpart : (Finset.univ : Finset (Fin m)) = (R ∪ N) ∪ Rest := by
    rw [hRest, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  have hdisj2 : Disjoint (R ∪ N) Rest := by rw [hRest]; exact Finset.disjoint_sdiff
  -- decompose the signed sum for any base point z.
  have hsum : ∀ z : Pt, (∑ i : Fin m, sEdge Q σ z i) =
      (∑ i ∈ R, sEdge Q σ z i + ∑ i ∈ N, sEdge Q σ z i) + ∑ i ∈ Rest, sEdge Q σ z i := by
    intro z
    conv_lhs => rw [show (Finset.univ : Finset (Fin m)) = (R ∪ N) ∪ Rest from hpart]
    rw [Finset.sum_union hdisj2, Finset.sum_union hdisj]
  have hNsum : ∀ z : Pt, (∑ i ∈ N, sEdge Q σ z i) =
      ∑ i ∈ R, sEdge Q σ z (cyclicNext i) := by
    intro z; rw [hNimg, Finset.sum_image]
    intro a _ b _ h; exact cyclicNext_injective h
  -- R-pairs eventually constant.
  have hpairs : ∀ᶠ z in nhds x, ∀ i ∈ R,
      sEdge Q σ z i + sEdge Q σ z (cyclicNext i) =
        sEdge Q σ x i + sEdge Q σ x (cyclicNext i) := by
    rw [eventually_all_finset]
    intro i hi
    exact signedPair_eventually_eq Q σ hx ((hRmem i).mp hi)
  -- Rest edges eventually constant.
  have hrest : ∀ᶠ z in nhds x, ∀ i ∈ Rest, sEdge Q σ z i = sEdge Q σ x i := by
    rw [eventually_all_finset]
    intro i hi
    have hi' : i ∉ R ∧ i ∉ N := by
      rw [hRest, Finset.mem_sdiff] at hi
      have := hi.2; rw [Finset.mem_union, not_or] at this; exact this
    have hu1 : crossU Q σ x i ≠ 1 := fun h => hi'.1 ((hRmem i).mpr h)
    have hu0 : crossU Q σ x i ≠ 0 := fun h => hi'.2 ((hNmem i).mpr h)
    -- neither endpoint on the ray line.
    have ha : side σ.r x (Q.q i) ≠ 0 := fun h => hu0 ((side_start_zero_iff_crossU_zero Q σ x i).mp h)
    have hb : side σ.r x (Q.q (cyclicNext i)) ≠ 0 :=
      fun h => hu1 ((side_next_zero_iff_crossU_one Q σ x i).mp h)
    exact sEdge_eventually_eq_rest Q σ hx ha hb
  -- assemble.
  filter_upwards [hpairs, hrest] with z hp hr
  rw [windCross_eq_sum_sEdge, windCross_eq_sum_sEdge, hsum z, hsum x, hNsum z, hNsum x]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hRsum : (∑ i ∈ R, (sEdge Q σ z i + sEdge Q σ z (cyclicNext i))) =
      ∑ i ∈ R, (sEdge Q σ x i + sEdge Q σ x (cyclicNext i)) :=
    Finset.sum_congr rfl (fun i hi => hp i hi)
  have hRestsum : (∑ i ∈ Rest, sEdge Q σ z i) = ∑ i ∈ Rest, sEdge Q σ x i :=
    Finset.sum_congr rfl (fun i hi => hr i hi)
  rw [hRsum, hRestsum]

/-! ## Part B: the half-plane escape (no Jordan)

Let `Q` be the subpolygon, `σ` its ray, and let `dDir`, `dBase` define the diagonal-line side
function `hp z := det2 dDir (z - dBase)`.  Suppose the subpolygon boundary lies in the closed
half-plane `hp ≤ 0` and the base point `x` is strictly on `0 < hp`.  Choose an escape vector `v`
with `0 < det2 dDir v` (so the straight ray `γ t = x + t•v` increases `hp` and stays in the open
half-plane, hence off the boundary) and `det2 σ.r v ≠ 0` (so for large `t` every vertex of `Q`
falls on a single strict side of the ray line through `γ T`, giving zero winding).  Local
constancy (Part A) transports `windCross (γ T) = 0` back to `x`. -/

variable {m : ℕ}

/-- The diagonal-line side functional for direction `dDir` and base `dBase`. -/
def hp (dDir dBase z : Pt) : ℝ := det2 dDir (z - dBase)

/-- `hp` is affine along a segment. -/
lemma hp_lineMap (dDir dBase x y : Pt) (t : ℝ) :
    hp dDir dBase (AffineMap.lineMap x y t) =
      (1 - t) * hp dDir dBase x + t * hp dDir dBase y := by
  unfold hp
  have hsub : (AffineMap.lineMap x y t : Pt) - dBase =
      AffineMap.lineMap (x - dBase) (y - dBase) t := by
    rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    ext k; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [hsub, AffineMap.lineMap_apply_module, det2_add_right, det2_smul_right, det2_smul_right]

/-- **Escape vector existence.**  For `dDir ≠ 0` there is a vector `v` with `0 < det2 dDir v`
and `det2 d2 v ≠ 0` for any second direction `d2`.  Take `v = perpVec dDir` (then
`det2 dDir v = ‖dDir‖² > 0`); if `det2 d2 v = 0`, perturb by a small multiple of `dDir`
(`det2 dDir dDir = 0` keeps the first slot, and `det2 d2 dDir ≠ 0` since `det2 d2 (perpVec) = 0`
would otherwise force `d2 ∥ perpVec ⊥ dDir`, but then `det2 d2 dDir ≠ 0`). -/
lemma exists_escape_vec {dDir : Pt} (hd : dDir ≠ 0) {d2 : Pt} (hd2 : d2 ≠ 0) :
    ∃ v : Pt, 0 < det2 dDir v ∧ det2 d2 v ≠ 0 := by
  classical
  set ν := perpVec dDir with hν
  have hpos : 0 < det2 dDir ν := det2_perpVec_pos hd
  by_cases h0 : det2 d2 ν = 0
  · -- perturb: v = ν + c • dDir with c chosen so det2 d2 v ≠ 0.
    -- det2 dDir v = det2 dDir ν + c * det2 dDir dDir = det2 dDir ν > 0 (det2_self).
    -- det2 d2 v = 0 + c * det2 d2 dDir; need det2 d2 dDir ≠ 0.
    have hd2d : det2 d2 dDir ≠ 0 := by
      intro hz
      -- det2 d2 ν = 0 and det2 d2 dDir = 0 with dDir, ν independent ⟹ d2 = 0; then det2 d2 dDir=0
      -- but also det2 dDir ν > 0 means dDir, ν independent.  d2 ⊥ both ⟹ d2 = 0.
      -- Use the determinant identity: det2 dDir ν • d2 = (det2 d2 ν)•dDir' ... simpler: components.
      have hν0 : ν 0 = - dDir 1 := by rw [hν, perpVec_zero]
      have hν1 : ν 1 = dDir 0 := by rw [hν, perpVec_one]
      have e1 : d2 0 * ν 1 - d2 1 * ν 0 = 0 := h0
      have e2 : d2 0 * dDir 1 - d2 1 * dDir 0 = 0 := hz
      rw [hν0, hν1] at e1
      -- e1: d2 0 * dDir 0 - d2 1 * (-dDir 1) = 0  ⟹ d2 0 * dDir 0 + d2 1 * dDir 1 = 0
      have e1' : d2 0 * dDir 0 + d2 1 * dDir 1 = 0 := by nlinarith [e1]
      -- e1' and e2 are an orthogonal pair; dDir ≠ 0 ⟹ d2 = 0.
      have hd2zero : d2 = 0 := by
        have hdsq : (dDir 0) ^ 2 + (dDir 1) ^ 2 ≠ 0 := by
          intro hsq
          apply hd
          have h0sq : (dDir 0) ^ 2 = 0 := by nlinarith [sq_nonneg (dDir 0), sq_nonneg (dDir 1)]
          have h1sq : (dDir 1) ^ 2 = 0 := by nlinarith [sq_nonneg (dDir 0), sq_nonneg (dDir 1)]
          exact pt_ext_zero_one (pow_eq_zero_iff (by norm_num) |>.mp h0sq)
            (pow_eq_zero_iff (by norm_num) |>.mp h1sq)
        have hd20 : d2 0 = 0 := by
          have key : (d2 0) * ((dDir 0) ^ 2 + (dDir 1) ^ 2) = 0 := by
            have := mul_eq_zero_of_left e1' (dDir 0)
            have := mul_eq_zero_of_left e2 (dDir 1)
            nlinarith [mul_eq_zero_of_left e1' (dDir 0), mul_eq_zero_of_left e2 (dDir 1)]
          rcases mul_eq_zero.mp key with h | h
          · exact h
          · exact absurd h hdsq
        have hd21 : d2 1 = 0 := by
          have key : (d2 1) * ((dDir 0) ^ 2 + (dDir 1) ^ 2) = 0 := by
            nlinarith [mul_eq_zero_of_left e1' (dDir 1), mul_eq_zero_of_left e2 (dDir 0)]
          rcases mul_eq_zero.mp key with h | h
          · exact h
          · exact absurd h hdsq
        exact pt_ext_zero_one hd20 hd21
      exact hd2 hd2zero
    -- choose c = 1 / det2 d2 dDir (any nonzero c works since det2 d2 dDir ≠ 0).
    refine ⟨ν + (1 : ℝ) • dDir, ?_, ?_⟩
    · rw [det2_add_right, det2_smul_right, det2_self, mul_zero, add_zero]; exact hpos
    · rw [det2_add_right, det2_smul_right, h0, zero_add, one_mul]; exact hd2d
  · exact ⟨ν, hpos, h0⟩

/-! ### Transport of the winding along a boundary-free straight path -/

/-- `fun t => x + t • v` is continuous. -/
lemma continuous_ray (x v : Pt) : Continuous (fun t : ℝ => x + t • v) := by fun_prop

/-- **Winding constant along a boundary-free straight path.**  If `γ t = x + t•v` avoids the
boundary of `Q` for all `t ∈ [0,T]`, then `windCross Q σ (γ 0) = windCross Q σ (γ T)`.  The map
`t ↦ windCross Q σ (γ t)` is locally constant on the connected `Icc 0 T` (Part A local constancy
pulled back along the continuous `γ`), hence constant. -/
lemma windCross_constant_on_ray (Q : StrictSimplePolygon m) (σ : RayDirection Q) (x v : Pt)
    {T : ℝ} (hT : 0 ≤ T)
    (havoid : ∀ t ∈ Set.Icc (0 : ℝ) T, ¬ OnBoundary Q (x + t • v)) :
    windCross Q σ x = windCross Q σ (x + T • v) := by
  classical
  haveI : PreconnectedSpace (Set.Icc (0 : ℝ) T) := by
    rw [← isPreconnected_iff_preconnectedSpace]; exact isPreconnected_Icc
  set γ : ℝ → Pt := fun t => x + t • v with hγ
  set f : Set.Icc (0 : ℝ) T → ℤ := fun t => windCross Q σ (γ (t : ℝ)) with hf
  have hcont : Continuous (fun t : Set.Icc (0:ℝ) T => γ (t : ℝ)) :=
    (continuous_ray x v).comp continuous_subtype_val
  -- `f` is locally constant: at every `t`, `γ t` is off-boundary, so windCross is eventually
  -- constant in 2D; pull back along the continuous `γ`.
  have hLC : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    have hoff : ¬ OnBoundary Q (γ (t : ℝ)) := havoid (t : ℝ) t.2
    have hev := windCross_locally_constant_off_boundary Q σ hoff
    have htends : Filter.Tendsto (fun s : Set.Icc (0:ℝ) T => γ (s : ℝ))
        (nhds t) (nhds (γ (t : ℝ))) := hcont.tendsto t
    filter_upwards [htends.eventually hev] with s hs
    simp only [hf]; exact hs
  -- `f` constant on the preconnected interval; compare endpoints `0` and `T`.
  have h0 : (⟨0, by exact ⟨le_refl 0, hT⟩⟩ : Set.Icc (0:ℝ) T) ∈ Set.univ := trivial
  have hTm : (⟨T, by exact ⟨hT, le_refl T⟩⟩ : Set.Icc (0:ℝ) T) ∈ Set.univ := trivial
  have hconst := (IsLocallyConstant.iff_is_const.mp hLC)
    (⟨0, ⟨le_refl 0, hT⟩⟩ : Set.Icc (0:ℝ) T) (⟨T, ⟨hT, le_refl T⟩⟩ : Set.Icc (0:ℝ) T)
  simp only [hf, hγ] at hconst
  simpa using hconst

/-! ### The half-plane escape theorem -/

/-- **`hp` along the escape ray is `hp x + t · det2 dDir v`.** -/
lemma hp_ray (dDir dBase x v : Pt) (t : ℝ) :
    hp dDir dBase (x + t • v) = hp dDir dBase x + t * det2 dDir v := by
  unfold hp
  rw [show (x + t • v - dBase : Pt) = (x - dBase) + t • v by abel,
    det2_add_right, det2_smul_right]

/-- **Escape path avoids the boundary.**  If the boundary of `Q` lies in `hp ≤ 0`, the base
point has `0 < hp x`, and the escape vector satisfies `0 < det2 dDir v`, then for `0 ≤ t` the
point `x + t•v` has `0 < hp`, so it is off the boundary. -/
lemma escape_avoids_boundary {Q : StrictSimplePolygon m} {dDir dBase x v : Pt}
    (hQside : ∀ z, OnBoundary Q z → hp dDir dBase z ≤ 0)
    (hxside : 0 < hp dDir dBase x) (hvside : 0 < det2 dDir v)
    {t : ℝ} (ht : 0 ≤ t) : ¬ OnBoundary Q (x + t • v) := by
  intro hmem
  have h1 : hp dDir dBase (x + t • v) ≤ 0 := hQside _ hmem
  have h2 : 0 < hp dDir dBase (x + t • v) := by
    rw [hp_ray]; nlinarith [hxside, hvside, ht]
  linarith

/-- **Side coordinate along the escape ray.**  `side σ.r (x + t•v) w = side σ.r x w - t·det2 σ.r v`. -/
lemma side_ray (r x v w : Pt) (t : ℝ) :
    side r (x + t • v) w = side r x w - t * det2 r v := by
  unfold side
  rw [show (w - (x + t • v) : Pt) = (w - x) - t • v by abel, det2_sub_right, det2_smul_right]

/-- **Far endpoint with all vertices on one strict side (large `t`).**  If `det2 σ.r v ≠ 0` then
for `t` large the ray line through `x + t•v` has every vertex of `Q` on one strict side, so
`windCross Q σ (x + t•v) = 0`.  Concretely a single large `T ≥ 0` suffices. -/
lemma exists_far_T_windCross_zero (Q : StrictSimplePolygon m) (σ : RayDirection Q) (x v : Pt)
    (hv : det2 σ.r v ≠ 0) :
    ∃ T : ℝ, 0 ≤ T ∧ windCross Q σ (x + T • v) = 0 := by
  classical
  set D := det2 σ.r v with hD
  have hne : Nonempty (Fin m) := ⟨⟨0, by have := Q.hthree; omega⟩⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k : Fin m, side σ.r x (Q.q k) ≤ M := by
    refine ⟨Finset.univ.sup' Finset.univ_nonempty (fun k => side σ.r x (Q.q k)), ?_⟩
    intro k; exact Finset.le_sup' (fun k => side σ.r x (Q.q k)) (Finset.mem_univ k)
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ k : Fin m, L ≤ side σ.r x (Q.q k) := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty (fun k => side σ.r x (Q.q k)), ?_⟩
    intro k; exact Finset.inf'_le (fun k => side σ.r x (Q.q k)) (Finset.mem_univ k)
  rcases lt_or_gt_of_ne hv with hDneg | hDpos
  · -- D < 0: side - t·D = side + t·(-D) grows positive; choose T so all strictly positive.
    -- need side x (qk) - T·D > 0, i.e. T·(-D) > -side, suffices T·(-D) > -L (since L ≤ side).
    set T := max 0 ((-L + 1) / (-D)) with hT
    have hTnn : 0 ≤ T := le_max_left _ _
    refine ⟨T, hTnn, ?_⟩
    apply windCross_eq_zero_of_all_strictSide; left; intro k
    rw [side_ray]
    have hTge : (-L + 1) / (-D) ≤ T := le_max_right _ _
    have hpos : 0 < -D := by linarith
    have hmul : (-L + 1) / (-D) * (-D) = -L + 1 := by field_simp
    have h1 : -L + 1 ≤ T * (-D) := by
      have := mul_le_mul_of_nonneg_right hTge (le_of_lt hpos)
      rwa [hmul] at this
    have hkL := hL k
    nlinarith [hkL, h1, hpos]
  · -- D > 0: side - t·D becomes negative; choose T so all strictly negative.
    set T := max 0 ((M + 1) / D) with hT
    have hTnn : 0 ≤ T := le_max_left _ _
    refine ⟨T, hTnn, ?_⟩
    apply windCross_eq_zero_of_all_strictSide; right; intro k
    rw [side_ray]
    have hTge : (M + 1) / D ≤ T := le_max_right _ _
    have hmul : (M + 1) / D * D = M + 1 := by field_simp
    have h1 : M + 1 ≤ T * D := by
      have := mul_le_mul_of_nonneg_right hTge (le_of_lt hDpos)
      rwa [hmul] at this
    have hkM := hM k
    nlinarith [hkM, h1, hDpos]

/-- **The half-plane exterior winding-zero theorem (Part B headline, no Jordan).**  If the
boundary of `Q` lies in the closed half-plane `hp dDir dBase ≤ 0` (`dDir ≠ 0`) and `x` is
strictly on the open side `0 < hp dDir dBase x`, then `windCross Q σ x = 0`.  The straight escape
ray in a direction `v` with `0 < det2 dDir v` and `det2 σ.r v ≠ 0` stays strictly inside the open
half-plane (off the boundary), so local constancy transports the zero winding of its far
endpoint back to `x`. -/
theorem ExteriorWindingZero_halfplane (Q : StrictSimplePolygon m) (σ : RayDirection Q)
    {dDir dBase x : Pt} (hd : dDir ≠ 0)
    (hQside : ∀ z, OnBoundary Q z → hp dDir dBase z ≤ 0)
    (hxside : 0 < hp dDir dBase x) :
    windCross Q σ x = 0 := by
  obtain ⟨v, hvside, hvσ⟩ := exists_escape_vec hd σ.r_ne_zero
  obtain ⟨T, hTnn, hfar⟩ := exists_far_T_windCross_zero Q σ x v hvσ
  have hconst : windCross Q σ x = windCross Q σ (x + T • v) :=
    windCross_constant_on_ray Q σ x v hTnn
      (fun t ht => escape_avoids_boundary hQside hxside hvside ht.1)
  rw [hconst]; exact hfar

/-! ## Part C: discharging `ExteriorWindingZero` via the ear half-plane containment

`ExteriorWindingZero` asks: off all boundaries, a point on the negative side of the diagonal
line has zero LEFT winding, and on the positive side zero RIGHT winding.  The half-plane theorem
of Part B closes this *given* that each ear's boundary lies in the closed half-plane on its own
side of the diagonal line — the LEFT ear in `wDiagSide ≥ 0`, the RIGHT ear in `wDiagSide ≤ 0`.

This **half-plane containment of the ears is the precise residue** that the abstract
`CutGeometry` interface does not carry (it has the convex vertex, transversality, strict axioms,
rays, and the region union/intersection identities, but not the geometric sidedness of each ear
relative to its cutting diagonal).  We isolate it as a single named, non-vacuous predicate
`EarHalfPlaneContainment` and prove `ExteriorWindingZero ← EarHalfPlaneContainment`. -/

/-- `wDiagSide` is `hp` of the diagonal direction and base. -/
lemma wDiagSide_eq_hp (P : StrictSimplePolygon n) (i j : Fin n) (z : Pt) :
    wDiagSide P i j z = hp (P.q j - P.q i) (P.q i) z := by
  unfold wDiagSide hp side; rfl

/-- **The ear half-plane containment (the isolated geometric residue).**  For every diagonal of
`P` (under ray `ρ`), the boundary of the LEFT ear lies in the closed half-plane `wDiagSide ≥ 0`
and the boundary of the RIGHT ear in `wDiagSide ≤ 0`.  This is the geometric sidedness of each
ear w.r.t. its cutting diagonal line — true for any genuine planar ear, and exactly the datum
`CutGeometry` omits. -/
def EarHalfPlaneContainment {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) : Prop :=
  ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j),
    (∀ z, OnBoundary (buildLeftPoly h (g.leftAxioms h)) z → 0 ≤ wDiagSide P i j z) ∧
    (∀ z, OnBoundary (buildRightPoly h (g.rightAxioms h)) z → wDiagSide P i j z ≤ 0)

/-- **`ExteriorWindingZero` from the ear half-plane containment.**  Off all boundaries, a point
on the strictly negative side of the diagonal line is in the open exterior half-plane of the
LEFT ear (which lies in `wDiagSide ≥ 0`); the half-plane escape (Part B) gives zero LEFT winding.
Symmetrically on the positive side for the RIGHT ear.  No Jordan curve theorem is used. -/
theorem exteriorWindingZero_of_earHalfPlane {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) (hc : EarHalfPlaneContainment g) :
    ExteriorWindingZero g := by
  intro i j h x _ _ _
  have hij : i ≠ j := h.1
  -- the diagonal direction is nonzero (distinct endpoints).
  have hdne : (P.q j - P.q i) ≠ 0 := by
    intro hz; exact hij (P.injective_q (by rw [← sub_eq_zero]; exact hz)).symm
  -- and its negation.
  have hdne' : (P.q i - P.q j) ≠ 0 := by
    intro hz; exact hij (P.injective_q (sub_eq_zero.mp hz))
  obtain ⟨hcL, hcR⟩ := hc h
  refine ⟨fun hneg => ?_, fun hpos => ?_⟩
  · -- LEFT: wDiagSide < 0.  Boundary of left ear in wDiagSide ≥ 0, i.e. hp (qj-qi) ≤ 0 fails…
    -- use dDir = qi - qj so hp = -wDiagSide: boundary in hp ≤ 0, x in hp > 0.
    apply ExteriorWindingZero_halfplane (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) hdne'
    · intro z hz
      have := hcL z hz
      -- hp (qi-qj) z = det2 (qi-qj)(z-qi) = - det2 (qj-qi)(z-qi) = - wDiagSide.
      have hflip : hp (P.q i - P.q j) (P.q i) z = - wDiagSide P i j z := by
        rw [wDiagSide_eq_hp]; unfold hp
        rw [show (P.q i - P.q j : Pt) = (-1 : ℝ) • (P.q j - P.q i) by module,
          det2_smul_left]; ring
      rw [hflip]; linarith
    · have hflip : hp (P.q i - P.q j) (P.q i) x = - wDiagSide P i j x := by
        rw [wDiagSide_eq_hp]; unfold hp
        rw [show (P.q i - P.q j : Pt) = (-1 : ℝ) • (P.q j - P.q i) by module,
          det2_smul_left]; ring
      rw [hflip]; linarith
  · -- RIGHT: wDiagSide > 0.  Boundary of right ear in wDiagSide ≤ 0, i.e. hp (qj-qi) ≤ 0;
    -- x in wDiagSide > 0 = hp > 0.
    apply ExteriorWindingZero_halfplane (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) hdne
    · intro z hz
      have := hcR z hz
      rw [← wDiagSide_eq_hp]; exact this
    · rw [← wDiagSide_eq_hp]; exact hpos

/-! ## Part D: discharging `WindZeroExterior` and `OffDiagDisjoint`

We package the result into the exact interfaces `PolygonWindingZero` / `PolygonWinding` set up:
`WindZeroExterior` for the LEFT ear on the negative-side witness and for the RIGHT ear on the
positive-side witness, and the side-aware `ExteriorWindingZero`.  Then `OffDiagDisjoint` follows
through the existing chain.  (Independently, `OffDiagDisjoint` is also available directly from
`CutGeometry.split_region_intersection` via `offDiagDisjoint_of_cutGeometry`; here we close it
through the *signed-winding* route, the genuine content of the residue.) -/

/-- **`WindZeroExterior` for the LEFT ear (negative-side witness), from the half-plane
containment.** -/
theorem windZeroExterior_left_of_earHalfPlane {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) (hc : EarHalfPlaneContainment g) {i j : Fin n}
    (h : IsDiagonal' P ρ i j) :
    WindZeroExterior (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h)
      (@leftExteriorSide n P ρ i j) := by
  intro x hLb hext
  -- leftExteriorSide x = wDiagSide < 0; left ear boundary in wDiagSide ≥ 0.  `WindZeroExterior`
  -- only gives the left boundary, so we close directly via the half-plane theorem.
  have hij : i ≠ j := h.1
  have hdne' : (P.q i - P.q j) ≠ 0 := fun hz => hij (P.injective_q (sub_eq_zero.mp hz))
  obtain ⟨hcL, _⟩ := hc h
  apply ExteriorWindingZero_halfplane (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) hdne'
  · intro z hz
    have := hcL z hz
    have hflip : hp (P.q i - P.q j) (P.q i) z = - wDiagSide P i j z := by
      rw [wDiagSide_eq_hp]; unfold hp
      rw [show (P.q i - P.q j : Pt) = (-1 : ℝ) • (P.q j - P.q i) by module, det2_smul_left]; ring
    rw [hflip]; linarith
  · have hflip : hp (P.q i - P.q j) (P.q i) x = - wDiagSide P i j x := by
      rw [wDiagSide_eq_hp]; unfold hp
      rw [show (P.q i - P.q j : Pt) = (-1 : ℝ) • (P.q j - P.q i) by module, det2_smul_left]; ring
    rw [hflip]
    have : wDiagSide P i j x < 0 := hext
    linarith

/-- **`WindZeroExterior` for the RIGHT ear (positive-side witness), from the half-plane
containment.** -/
theorem windZeroExterior_right_of_earHalfPlane {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) (hc : EarHalfPlaneContainment g) {i j : Fin n}
    (h : IsDiagonal' P ρ i j) :
    WindZeroExterior (buildRightPoly h (g.rightAxioms h)) (g.rightRay h)
      (@rightExteriorSide n P ρ i j) := by
  intro x hRb hext
  have hij : i ≠ j := h.1
  have hdne : (P.q j - P.q i) ≠ 0 := by
    intro hz; exact hij (P.injective_q (by rw [← sub_eq_zero]; exact hz)).symm
  obtain ⟨_, hcR⟩ := hc h
  apply ExteriorWindingZero_halfplane (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) hdne
  · intro z hz; rw [← wDiagSide_eq_hp]; exact hcR z hz
  · rw [← wDiagSide_eq_hp]; exact hext

/-- **`ExteriorWindingZero` discharged through the `WindZeroExterior` interface.**  This recovers
exactly the `exteriorWindingZero_of_windZeroExterior` chain of `PolygonWindingZero`, now with the
`WindZeroExterior` hypotheses *proved* from the ear half-plane containment. -/
theorem exteriorWindingZero_via_windZeroExterior {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (g : CutGeometry P ρ) (hc : EarHalfPlaneContainment g) :
    ExteriorWindingZero g := by
  apply exteriorWindingZero_of_windZeroExterior g
  · intro i j h; exact windZeroExterior_left_of_earHalfPlane g hc h
  · intro i j h; exact windZeroExterior_right_of_earHalfPlane g hc h

/-- **`OffDiagDisjoint` through the signed-winding route**, from the ear half-plane containment.
`ExteriorWindingZero` (closed above) yields `WindingSeparates` together with `OffDiagDisjoint`
(the intersection identity, `offDiagDisjoint_of_cutGeometry`); the combined `WindingSeparates`
re-derives `OffDiagDisjoint`.  The signed-winding development is thus a complete, self-contained
Jordan-substitute proof of the disjointness. -/
theorem offDiagDisjoint_via_windingExterior {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) (hc : EarHalfPlaneContainment g) :
    OffDiagDisjoint g := by
  have hewz : ExteriorWindingZero g := exteriorWindingZero_of_earHalfPlane g hc
  have hdisj0 : OffDiagDisjoint g :=
    ProofsInTheBook.PolygonContainment.offDiagDisjoint_of_cutGeometry g
  apply offDiagDisjoint_of_windingSeparates g
  exact windingSeparates_of_exteriorWindingZero g hewz hdisj0

/-! ## Non-vacuity of `EarHalfPlaneContainment` (§3.3 anti-vacuity)

`EarHalfPlaneContainment` is a conjunction of genuine geometric containments (each ear's boundary
in the closed half-plane on its side of the diagonal line).  It is *not* an unsatisfiable
premise: the two clauses are mutually consistent (one ear on each side of the same line), and the
diagonal endpoints — common to both ears — sit *on* the line (`wDiagSide = 0`), satisfying both
`0 ≤ wDiagSide` and `wDiagSide ≤ 0` simultaneously.  We record that the diagonal endpoints meet
both containment inequalities, certifying the premise is non-degenerate. -/

/-- **Diagonal endpoints satisfy both half-plane inequalities** (anti-vacuity witness): the shared
vertices `P.q i`, `P.q j` lie on the diagonal line, so `wDiagSide = 0`, which is `≤ 0` and `≥ 0`
at once — the two `EarHalfPlaneContainment` clauses are co-satisfiable along the cut. -/
theorem earHalfPlane_endpoints_on_line {P : StrictSimplePolygon n} (i j : Fin n) :
    wDiagSide P i j (P.q i) = 0 ∧ wDiagSide P i j (P.q j) = 0 :=
  ⟨wDiagSide_left P i j, wDiagSide_right P i j⟩

end

end ProofsInTheBook.PolygonWindingExterior
