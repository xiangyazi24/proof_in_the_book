import ProofsInTheBook.ZinanCh36InteriorValue
import ProofsInTheBook.PolygonTriangleConvex
import ProofsInTheBook.PolygonWindingBound

/-!
# `ZinanCh36TriBase` — the TRIANGLE SIGNED BASE of the interior-value package (Route C)

This file provides the BASE case of the split-induction value package
(`ZinanCh36InteriorValue.WindValuesWithSign`): the triangle's signed-winding value is
2-valued `{0, s}` with the orientation sign

  `triSign Q := if 0 < orient (q0) (q1) (q2) then 1 else -1`.

i.e. `WindValuesWithSign Q (triSign Q)` for every `3`-gon `Q`.

## The unified pure-arithmetic core (no interior/exterior split)

The design note suggested splitting into "interior ⟹ value `s`" and "exterior ⟹ value `0`".
We avoid the geometric exterior parity entirely: at EVERY generic off-boundary point the signed
winding of a triangle is a *pure-arithmetic* function of the three side coordinates
`s_k := side ρ.r x (q_k)`, the three edge crossTau-numerators `O_k := det2 (q_k - x) (q_{k+1} - q_k)`,
and the oriented area `O := orient q0 q1 q2`, subject to two coordinate identities that hold at
EVERY point (no positivity of any barycentric weight):

* `O0 + O1 + O2 = O`                         (`triNum_sum`)
* `O1 * s0 + O2 * s1 + O0 * s2 = 0`           (`triNum_side`)

Writing the signed winding as

  `windCross = osign(s1-s0)·[Span s0 s1 ∧ 0 ≤ O0·(s1-s0)]`
            `+ osign(s2-s1)·[Span s1 s2 ∧ 0 ≤ O1·(s2-s1)]`
            `+ osign(s0-s2)·[Span s2 s0 ∧ 0 ≤ O2·(s0-s2)]`

(`osign d := if 0 < d then 1 else -1`, the per-edge `eSign`), the two identities force this sum to
lie in `{0, osign O}` — verified by a finite real case analysis (`signed_forward_sum_mem`,
the signed analogue of `PolygonTriangleConvex.forward_count_eq_one`).  This is uniform across
interior AND exterior points: an exterior ray either misses (sum `0`) or enters-and-exits with
OPPOSITE `eSign` (sum `0`); an interior ray crosses once with `eSign = osign O` (sum `osign O`).
No half-plane, no Jordan exterior parity.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36TriBase

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonWinding
open ProofsInTheBook.PolygonWindingExterior
open ProofsInTheBook.PolygonWindingBound (eSign_mem windCross_eq_sum_crossing_eSign)
open ProofsInTheBook.PolygonTriangleConvex
  (cyclicNext_three orient_cyclic crossNum_eq_weight_orient crossTau_mul_crossDen
   crossTau_nonneg_iff)
open ProofsInTheBook.ZinanCh36Interval (windCross_mem_final)
open ProofsInTheBook.ZinanCh36InteriorValue (WindValuesWithSign)

noncomputable section

/-! ## Part 1: the triangle sign `triSign` -/

/-- **The triangle's orientation sign.**  `1` if the vertex triple `(q0, q1, q2)` is positively
oriented, `-1` otherwise (the orient is nonzero by `noncollinear_consecutive`). -/
def triSign (Q : StrictSimplePolygon 3) : ℤ :=
  if 0 < orient (Q.q ⟨0, by omega⟩) (Q.q ⟨1, by omega⟩) (Q.q ⟨2, by omega⟩) then 1 else -1

/-- **`triSign` is a unit sign.** -/
theorem triSign_unit (Q : StrictSimplePolygon 3) : triSign Q = 1 ∨ triSign Q = -1 := by
  unfold triSign
  by_cases h : 0 < orient (Q.q ⟨0, by omega⟩) (Q.q ⟨1, by omega⟩) (Q.q ⟨2, by omega⟩)
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)

/-! ## Part 2: the per-edge orientation sign `osign` and the two coordinate identities -/

/-- The `±1` orientation factor of a real difference: `1` if positive, `-1` otherwise.  This is the
per-edge `eSign` once the crossDen `s_{next} - s_i` is plugged in. -/
def osign (d : ℝ) : ℤ := if 0 < d then 1 else -1

lemma osign_mem (d : ℝ) : osign d = 1 ∨ osign d = -1 := by
  unfold osign; by_cases h : 0 < d
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)

/-- **The three edge crossTau-numerators sum to the oriented area** (holds at EVERY base point `x`).
`det2 (q0-x)(q1-q0) + det2 (q1-x)(q2-q1) + det2 (q2-x)(q0-q2) = orient q0 q1 q2`. -/
lemma triNum_sum (q0 q1 q2 x : Pt) :
    det2 (q0 - x) (q1 - q0) + det2 (q1 - x) (q2 - q1) + det2 (q2 - x) (q0 - q2) =
      orient q0 q1 q2 := by
  unfold orient det2
  simp only [PiLp.sub_apply]
  ring

/-- **The cross/side coupling identity** (holds at EVERY base point `x`).  With
`O_k := det2 (q_k - x)(q_{k+1} - q_k)` and `s_k := side r x q_k = det2 r (q_k - x)`,
`O1 * s0 + O2 * s1 + O0 * s2 = 0`.  This is the weightless form of the barycentric side identity:
`O0 = w2 O`, `O1 = w0 O`, `O2 = w1 O`, so the relation is `(w0 s0 + w1 s1 + w2 s2)·O = 0`. -/
lemma triNum_side (r q0 q1 q2 x : Pt) :
    det2 (q1 - x) (q2 - q1) * side r x q0 +
      det2 (q2 - x) (q0 - q2) * side r x q1 +
      det2 (q0 - x) (q1 - q0) * side r x q2 = 0 := by
  unfold side det2
  simp only [PiLp.sub_apply]
  ring

/-! ## Part 3: the unified signed forward-sum arithmetic

The signed analogue of `PolygonTriangleConvex.forward_count_eq_one`.  Three nonzero side values
`s0, s1, s2`, three crossTau-numerators `O0, O1, O2` with `O0 + O1 + O2 = O ≠ 0` and the coupling
`O1 s0 + O2 s1 + O0 s2 = 0`, give a signed forward indicator sum lying in `{0, osign O}`. -/

/-- The per-edge signed contribution `osign(crossDen)·[Span ∧ forward]`. -/
def sContrib (sa sb O' : ℝ) : ℤ :=
  osign (sb - sa) * (if Span sa sb ∧ 0 ≤ O' * (sb - sa) then 1 else 0)

/-- Resolve a signed contribution into the two cases: the `Span ∧ forward` condition holds and the
contribution is `osign(sb-sa)`, or it fails and the contribution is `0`.  Mirrors
`PolygonTriangleConvex.indicator_resolve` for the signed value. -/
lemma sContrib_resolve (sa sb O' : ℝ) :
    ((Span sa sb ∧ 0 ≤ O' * (sb - sa)) ∧ sContrib sa sb O' = osign (sb - sa)) ∨
      (¬ (Span sa sb ∧ 0 ≤ O' * (sb - sa)) ∧ sContrib sa sb O' = 0) := by
  unfold sContrib
  by_cases h : Span sa sb ∧ 0 ≤ O' * (sb - sa)
  · exact Or.inl ⟨h, by rw [if_pos h]; ring⟩
  · exact Or.inr ⟨h, by rw [if_neg h]; ring⟩

set_option maxHeartbeats 4000000 in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- **The signed forward sum is `0` or `osign O`** (pure arithmetic).  This is the heart of the
triangle base: under the two coordinate identities and ray-genericity, the orientation-signed sum of
the three cyclic forward indicators is `0` (exterior: ray misses, or enters-and-leaves with opposite
signs) or `osign O` (interior: ray crosses exactly once with sign `osign O`).  The proof mirrors
`forward_count_eq_one`: resolve the three signed indicators with `sContrib_resolve`, split the
`osign` if-then-elses, then close each leaf with `omega`/`nlinarith` against the two identities. -/
lemma signed_forward_sum_mem (s0 s1 s2 O0 O1 O2 O : ℝ)
    (hs0 : s0 ≠ 0) (hs1 : s1 ≠ 0) (hs2 : s2 ≠ 0) (hO : O ≠ 0)
    (hsum : O0 + O1 + O2 = O)
    (hside : O1 * s0 + O2 * s1 + O0 * s2 = 0) :
    sContrib s0 s1 O0 + sContrib s1 s2 O1 + sContrib s2 s0 O2 = 0 ∨
      sContrib s0 s1 O0 + sContrib s1 s2 O1 + sContrib s2 s0 O2 = osign O := by
  classical
  -- Two sign-driven span facts: opposite strict signs give a `Span`; equal strict signs forbid one.
  have spanNeg : ∀ a b : ℝ, a < 0 → 0 < b → Span a b := fun a b ha hb => Or.inl ⟨le_of_lt ha, hb⟩
  have spanPos : ∀ a b : ℝ, 0 < a → b < 0 → Span a b := fun a b ha hb => Or.inr ⟨le_of_lt hb, ha⟩
  have noSpanNeg : ∀ a b : ℝ, a < 0 → b < 0 → ¬ Span a b := by
    intro a b ha hb h; rcases h with ⟨_, hc⟩ | ⟨_, hc⟩ <;> linarith
  have noSpanPos : ∀ a b : ℝ, 0 < a → 0 < b → ¬ Span a b := by
    intro a b ha hb h; rcases h with ⟨hc, _⟩ | ⟨hc, _⟩ <;> linarith
  -- Split on the strict signs of `s0, s1, s2, O` FIRST (mirrors `forward_count_eq_one`); this fixes
  -- every `osign` argument's sign and makes every `Span` decidable.
  rcases lt_or_gt_of_ne hs0 with h0 | h0 <;>
    rcases lt_or_gt_of_ne hs1 with h1 | h1 <;>
      rcases lt_or_gt_of_ne hs2 with h2 | h2 <;>
        rcases lt_or_gt_of_ne hO with hOs | hOs <;>
    -- Resolve the three signed indicators.  ACTIVE: `hsp_k`, `hfw_k : 0 ≤ O_k·Δ_k`.  INACTIVE:
    -- `hn_k : ¬(Span ∧ forward)`.  When the (sign-determined) span holds, `hn_k` yields the
    -- BACKWARD bound `O_k·Δ_k < 0` — the load-bearing fact an inactive spanning edge carries.
    rcases sContrib_resolve s0 s1 O0 with ⟨⟨hsp0, hfw0⟩, e0⟩ | ⟨hn0, e0⟩ <;>
      rcases sContrib_resolve s1 s2 O1 with ⟨⟨hsp1, hfw1⟩, e1⟩ | ⟨hn1, e1⟩ <;>
        rcases sContrib_resolve s2 s0 O2 with ⟨⟨hsp2, hfw2⟩, e2⟩ | ⟨hn2, e2⟩ <;>
          rw [e0, e1, e2] <;>
    -- Kill leaves where a recorded active span contradicts the now-known equal endpoint signs.
    (try exact absurd hsp0 (noSpanNeg _ _ h0 h1)) <;>
    (try exact absurd hsp0 (noSpanPos _ _ h0 h1)) <;>
    (try exact absurd hsp1 (noSpanNeg _ _ h1 h2)) <;>
    (try exact absurd hsp1 (noSpanPos _ _ h1 h2)) <;>
    (try exact absurd hsp2 (noSpanNeg _ _ h2 h0)) <;>
    (try exact absurd hsp2 (noSpanPos _ _ h2 h0)) <;>
    -- Extract the backward bound from each inactive-but-spanning edge (a no-op otherwise).
    (try have hbw0 : O0 * (s1 - s0) < 0 := lt_of_not_ge (fun hf => hn0 ⟨spanNeg _ _ h0 h1, hf⟩)) <;>
    (try have hbw0 : O0 * (s1 - s0) < 0 := lt_of_not_ge (fun hf => hn0 ⟨spanPos _ _ h0 h1, hf⟩)) <;>
    (try have hbw1 : O1 * (s2 - s1) < 0 := lt_of_not_ge (fun hf => hn1 ⟨spanNeg _ _ h1 h2, hf⟩)) <;>
    (try have hbw1 : O1 * (s2 - s1) < 0 := lt_of_not_ge (fun hf => hn1 ⟨spanPos _ _ h1 h2, hf⟩)) <;>
    (try have hbw2 : O2 * (s0 - s2) < 0 := lt_of_not_ge (fun hf => hn2 ⟨spanNeg _ _ h2 h0, hf⟩)) <;>
    (try have hbw2 : O2 * (s0 - s2) < 0 := lt_of_not_ge (fun hf => hn2 ⟨spanPos _ _ h2 h0, hf⟩)) <;>
    -- Reduce each edge's product bound to a SIGN of `O_k` (dividing by the now-known sign of `Δ_k`).
    -- For an active edge `0 ≤ O_k·Δ_k`: `Δ_k>0 ⟹ O_k≥0`, `Δ_k<0 ⟹ O_k≤0`.  For an inactive spanning
    -- edge `O_k·Δ_k<0`: `Δ_k>0 ⟹ O_k<0`, `Δ_k<0 ⟹ O_k>0`.  These linear facts feed `hside`.
    (try have hO0 : 0 ≤ O0 := nonneg_of_mul_nonneg_left hfw0 (by linarith)) <;>
    (try have hO0 : O0 ≤ 0 := nonpos_of_mul_nonneg_left hfw0 (by linarith)) <;>
    (try have hO0 : O0 < 0 := by nlinarith [hbw0, h0, h1, h2]) <;>
    (try have hO0 : 0 < O0 := by nlinarith [hbw0, h0, h1, h2]) <;>
    (try have hO1 : 0 ≤ O1 := nonneg_of_mul_nonneg_left hfw1 (by linarith)) <;>
    (try have hO1 : O1 ≤ 0 := nonpos_of_mul_nonneg_left hfw1 (by linarith)) <;>
    (try have hO1 : O1 < 0 := by nlinarith [hbw1, h0, h1, h2]) <;>
    (try have hO1 : 0 < O1 := by nlinarith [hbw1, h0, h1, h2]) <;>
    (try have hO2 : 0 ≤ O2 := nonneg_of_mul_nonneg_left hfw2 (by linarith)) <;>
    (try have hO2 : O2 ≤ 0 := nonpos_of_mul_nonneg_left hfw2 (by linarith)) <;>
    (try have hO2 : O2 < 0 := by nlinarith [hbw2, h0, h1, h2]) <;>
    (try have hO2 : 0 < O2 := by nlinarith [hbw2, h0, h1, h2]) <;>
    -- The third (non-spanning, unbounded) `O_k` gets its sign from `hsum = O0+O1+O2 = O` and the
    -- other two signs; derive every consistent `0 < O_k` / `O_k < 0` we can, so `hside` (a sum of
    -- sign-known products) becomes a pure `nlinarith` contradiction.
    (try have gO0 : 0 < O0 := by nlinarith [hsum, hO1, hO2, hOs]) <;>
    (try have gO0 : O0 < 0 := by nlinarith [hsum, hO1, hO2, hOs]) <;>
    (try have gO1 : 0 < O1 := by nlinarith [hsum, hO0, hO2, hOs]) <;>
    (try have gO1 : O1 < 0 := by nlinarith [hsum, hO0, hO2, hOs]) <;>
    (try have gO2 : 0 < O2 := by nlinarith [hsum, hO0, hO1, hOs]) <;>
    (try have gO2 : O2 < 0 := by nlinarith [hsum, hO0, hO1, hOs]) <;>
    -- expose `osign Δ = if 0 < Δ then 1 else -1`, branch (each `Δ` sign fixed by `h0,h1,h2`), close.
    simp only [osign] <;>
    split_ifs <;>
    first
      | (left; first | rfl | omega | (exfalso; nlinarith [hsum, hside, h0, h1, h2, hOs]))
      | (right; first | rfl | omega | (exfalso; nlinarith [hsum, hside, h0, h1, h2, hOs]))
      | (exfalso; nlinarith [hsum, hside, h0, h1, h2, hOs])

/-! ## Part 4: `windCross` of a triangle as the `sContrib` sum

`windCross Q ρ x = ∑_k sEdge_k`, and over `Fin 3` each per-edge signed contribution `sEdge_k`
equals `sContrib s_i s_{i+1} O_i` with `s_k := side ρ.r x (q_k)`, `O_i := det2 (q_i - x)(q_{i+1}-q_i)`:
the orientation factor `eSign` is `osign(s_{i+1} - s_i)` (`= edgeSign` of the side difference), and
the unsigned indicator `[EdgeCrossesRay']` is `[Span ∧ 0 ≤ O_i·(s_{i+1}-s_i)]` (the forward guard in
product form, exactly as in `crossingNumber'_interior_eq_one`). -/

open ProofsInTheBook.PolygonWinding (rawSignedInd det2_eq_side_diff windCross_eq)
open ProofsInTheBook.PolygonWindingExterior (sEdge eSign windCross_eq_sum_sEdge sEdge_eq_eSign_mul)

/-- **The per-edge signed contribution equals `sContrib`.**  `sEdge Q ρ x i = sContrib (s_i)
(s_{cyclicNext i}) (det2 (q_i - x)(q_{i+1}-q_i))`. -/
lemma sEdge_eq_sContrib (Q : StrictSimplePolygon 3) (ρ : RayDirection Q) (x : Pt) (i : Fin 3) :
    sEdge Q ρ x i =
      sContrib (side ρ.r x (Q.q i)) (side ρ.r x (Q.q (cyclicNext i)))
        (det2 (Q.q i - x) (Q.q (cyclicNext i) - Q.q i)) := by
  classical
  rw [sEdge_eq_eSign_mul]
  -- `eSign = osign (s_next - s_i)` via the side-difference form of `det2 ρ.r (q_{i+1}-q_i)`.
  have hes : eSign Q ρ i = osign (side ρ.r x (Q.q (cyclicNext i)) - side ρ.r x (Q.q i)) := by
    unfold eSign osign PolygonWindingZero.edgeSign
    rw [det2_eq_side_diff ρ.r x (Q.q i) (Q.q (cyclicNext i))]
  -- `EdgeCrossesRay'` = `Span ∧ forward`, and the forward guard `0 ≤ crossTau` rewrites to
  -- `0 ≤ O_i·(s_next - s_i)`.
  have hfwd : (0 ≤ crossTau Q ρ x i) ↔
      0 ≤ det2 (Q.q i - x) (Q.q (cyclicNext i) - Q.q i) *
        (side ρ.r x (Q.q (cyclicNext i)) - side ρ.r x (Q.q i)) := by
    rw [crossTau_nonneg_iff Q ρ x i, crossTau_mul_crossDen]
    have hden : crossDen Q ρ i =
        side ρ.r x (Q.q (cyclicNext i)) - side ρ.r x (Q.q i) :=
      (side_next_sub_side Q ρ x i).symm
    rw [hden]
  rw [hes]
  unfold sContrib
  congr 1
  -- match the two indicators (`EdgeCrossesRay'` vs `Span ∧ forward-product`).
  by_cases hc : EdgeCrossesRay' Q ρ x i
  · rw [if_pos hc]
    rw [if_pos ⟨hc.1, hfwd.mp hc.2⟩]
  · rw [if_neg hc]
    rw [if_neg (fun h => hc ⟨h.1, hfwd.mpr h.2⟩)]

/-- **`windCross` of a `3`-gon is the `sContrib` sum over the three edges.** -/
lemma windCross_tri_eq_sContrib_sum (Q : StrictSimplePolygon 3) (ρ : RayDirection Q) (x : Pt) :
    windCross Q ρ x =
      sContrib (side ρ.r x (Q.q ⟨0, by omega⟩)) (side ρ.r x (Q.q ⟨1, by omega⟩))
          (det2 (Q.q ⟨0, by omega⟩ - x) (Q.q ⟨1, by omega⟩ - Q.q ⟨0, by omega⟩)) +
        sContrib (side ρ.r x (Q.q ⟨1, by omega⟩)) (side ρ.r x (Q.q ⟨2, by omega⟩))
          (det2 (Q.q ⟨1, by omega⟩ - x) (Q.q ⟨2, by omega⟩ - Q.q ⟨1, by omega⟩)) +
        sContrib (side ρ.r x (Q.q ⟨2, by omega⟩)) (side ρ.r x (Q.q ⟨0, by omega⟩))
          (det2 (Q.q ⟨2, by omega⟩ - x) (Q.q ⟨0, by omega⟩ - Q.q ⟨2, by omega⟩)) := by
  classical
  obtain ⟨hn0, hn1, hn2⟩ := cyclicNext_three
  rw [windCross_eq_sum_sEdge]
  rw [show (Finset.univ : Finset (Fin 3)) = {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [sEdge_eq_sContrib Q ρ x ⟨0, by omega⟩, sEdge_eq_sContrib Q ρ x ⟨1, by omega⟩,
      sEdge_eq_sContrib Q ρ x ⟨2, by omega⟩]
  rw [hn0, hn1, hn2]
  ring

/-! ## Part 5: the main theorem — `triangle_windValuesWithSign` -/

/-- **The triangle base of the interior-value package.**  Every `3`-gon `Q` is value-coherent with
its orientation sign `triSign Q`: at every generic off-boundary point the signed winding is `0` or
`triSign Q`.  This instantiates `WindValuesWithSign` for the base of the split induction. -/
theorem triangle_windValuesWithSign (Q : StrictSimplePolygon 3) :
    WindValuesWithSign Q (triSign Q) := by
  refine ⟨triSign_unit Q, ?_⟩
  intro ρ x _hoff hvert
  classical
  set i0 : Fin 3 := ⟨0, by omega⟩
  set i1 : Fin 3 := ⟨1, by omega⟩
  set i2 : Fin 3 := ⟨2, by omega⟩
  set s0 := side ρ.r x (Q.q i0) with hs0def
  set s1 := side ρ.r x (Q.q i1) with hs1def
  set s2 := side ρ.r x (Q.q i2) with hs2def
  set O0 := det2 (Q.q i0 - x) (Q.q i1 - Q.q i0) with hO0def
  set O1 := det2 (Q.q i1 - x) (Q.q i2 - Q.q i1) with hO1def
  set O2 := det2 (Q.q i2 - x) (Q.q i0 - Q.q i2) with hO2def
  set O := orient (Q.q i0) (Q.q i1) (Q.q i2) with hOdef
  -- `O ≠ 0`: the three triangle vertices are noncollinear (strict polygon, middle vertex).
  have hO : O ≠ 0 := by
    obtain ⟨_, hn1, _⟩ := cyclicNext_three
    have hnc := Q.noncollinear_consecutive i1
    have hpr : cyclicPrev i1 = i0 := by unfold cyclicPrev i1 i0; norm_num
    rw [hpr, hn1] at hnc
    exact hnc
  -- the three side values are nonzero (ray avoids every vertex).
  have hs0 : s0 ≠ 0 := hvert i0
  have hs1 : s1 ≠ 0 := hvert i1
  have hs2 : s2 ≠ 0 := hvert i2
  -- the two coordinate identities.
  have hsum : O0 + O1 + O2 = O := triNum_sum (Q.q i0) (Q.q i1) (Q.q i2) x
  have hside : O1 * s0 + O2 * s1 + O0 * s2 = 0 := by
    rw [hs0def, hs1def, hs2def, hO0def, hO1def, hO2def]
    exact triNum_side ρ.r (Q.q i0) (Q.q i1) (Q.q i2) x
  -- `windCross` as the `sContrib` sum.
  have hwc : windCross Q ρ x =
      sContrib s0 s1 O0 + sContrib s1 s2 O1 + sContrib s2 s0 O2 := by
    rw [windCross_tri_eq_sContrib_sum Q ρ x]
  -- `triSign Q = osign O`.
  have htri : triSign Q = osign O := by
    unfold triSign osign
    rw [← hOdef]
  rw [hwc, htri]
  exact signed_forward_sum_mem s0 s1 s2 O0 O1 O2 O hs0 hs1 hs2 hO hsum hside

end

#print axioms ProofsInTheBook.ZinanCh36TriBase.triangle_windValuesWithSign
#print axioms ProofsInTheBook.ZinanCh36TriBase.triSign_unit
#print axioms ProofsInTheBook.ZinanCh36TriBase.signed_forward_sum_mem

end ProofsInTheBook.ZinanCh36TriBase
