import ProofsInTheBook.PolygonGeometryData

/-!
# Chapter 36 — the convex-vertex triangle leaf, UNCONDITIONAL (`TriangleConvexLeaf`)

This file discharges the `hconv` oracle of `artGallery_strict_unconditional`: the
convex-vertex half of the triangle leaf,

```
TriangleConvexLeaf := ∀ (Q : StrictSimplePolygon 3) (σ : RayDirection Q),
  IsConvexVertex' Q σ ⟨1⟩
```

which (by `base_subset_iff_convexVertex_one`) is exactly the containment
`closedTri (v0 Q) (v1 Q) (v2 Q) ⊆ {x | ClosedRegion' Q σ x}`.

## The crossTau-sign lemma (the geometric heart)

Fix a triangle `Q` with vertices `q0, q1, q2` and oriented area
`O := orient q0 q1 q2 ≠ 0`.  For a base point `x = w0•q0 + w1•q1 + w2•q2` with
barycentric weights `w0, w1, w2 ≥ 0` summing to `1`, and a *valid* ray direction
`r` (not edge-parallel), the three side coordinates `s_k := side r x (q_k)` satisfy
the **barycentric side identity**

```
w0•s0 + w1•s1 + w2•s2 = side r x x = det2 r 0 = 0.
```

The crossTau numerator has the closed form (purely from `det2` bilinearity)

```
crossTau_i • crossDen_i = det2 (q_i - x) (q_{i+1} - q_i) = w_{i+2} • O
```

where `w_{i+2}` is the weight of the vertex *opposite* edge `i`.  Hence for a
*strictly interior* point (all `w_k > 0`) and a ray avoiding every vertex
(`s_k ≠ 0`):

* the weighted-zero identity forces the three `s_k` to NOT all share one strict
  sign — exactly one of them, `s_m`, carries the lone sign;
* the two edges incident to `q_m` are exactly the two that `Span` (opposite end
  signs); the third edge joins two same-sign vertices, so it does not span;
* those two spanning edges have `crossDen`s of *opposite* sign (`s_m - s_{m-1}`
  versus `s_{m+1} - s_m`, with `s_m` the lone sign), so since
  `crossTau_i = w_{i+2}•O / crossDen_i` with `w_{i+2} > 0`, their `crossTau`s have
  opposite sign — **exactly one is `≥ 0`** (forward).

Therefore the forward crossing count is `1`, i.e. `CrossingNumber' Q r x` is odd.
Ray-independence of the off-boundary parity (`crossingNumber'_wallGlobal_tri`,
already unconditional) transports this to the polygon's own ray `σ`.

A point of the closed triangle with some weight `= 0` lies on a triangle edge,
hence `OnBoundary` — the `Or.inl` branch of `ClosedRegion'`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonTriangleConvex

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonTriangulation (v0 v1 v2)
open ProofsInTheBook.PolygonLeaf

noncomputable section

/-! ## Part 1: barycentric extraction from a triangle hull membership

A point of `closedTri a b c = convexHull ℝ {a,b,c}` is a barycentric combination
of the three vertices.  We extract explicit nonnegative weights summing to one via
`convexJoin_singleton_segment`. -/

/-- **Barycentric coordinates of a triangle point.**  Every `x ∈ closedTri a b c`
is `w0•a + w1•b + w2•c` for some `w0, w1, w2 ≥ 0` with `w0 + w1 + w2 = 1`. -/
lemma exists_barycentric_of_mem_closedTri {a b c x : Pt}
    (hx : x ∈ closedTri a b c) :
    ∃ w0 w1 w2 : ℝ, 0 ≤ w0 ∧ 0 ≤ w1 ∧ 0 ≤ w2 ∧ w0 + w1 + w2 = 1 ∧
      x = w0 • a + w1 • b + w2 • c := by
  -- closedTri a b c = convexJoin {a} (segment b c)
  have hjoin : closedTri a b c = convexJoin ℝ {a} (segment ℝ b c) := by
    rw [closedTri, ← convexJoin_singleton_segment]
  rw [hjoin, mem_convexJoin] at hx
  obtain ⟨a', ha', y, hy, hseg⟩ := hx
  rw [Set.mem_singleton_iff] at ha'; subst ha'
  -- y ∈ segment b c: y = γ•b + δ•c
  obtain ⟨γ, δ, hγ, hδ, hγδ, hyeq⟩ := hy
  -- x ∈ segment a' y: x = α•a + β•y
  obtain ⟨α, β, hα, hβ, hαβ, hxeq⟩ := hseg
  refine ⟨α, β * γ, β * δ, hα, mul_nonneg hβ hγ, mul_nonneg hβ hδ, ?_, ?_⟩
  · have : β * γ + β * δ = β := by rw [← mul_add, hγδ, mul_one]
    rw [show α + β * γ + β * δ = α + (β * γ + β * δ) by ring, this, hαβ]
  · rw [← hxeq, ← hyeq]
    rw [smul_add, smul_smul, smul_smul]
    abel

/-! ## Part 2: the barycentric side identity and the crossTau closed form

For `x = w0•q0 + w1•q1 + w2•q2` with `w0+w1+w2 = 1`, the side coordinates obey
`∑ w_k • side r x q_k = 0` (linearity of `det2` and `side r x x = 0`).  The
crossTau numerator of edge `i` is `w_opp • orient`, with `w_opp` the weight of the
vertex opposite edge `i`. -/

/-- `side r x x = 0`. -/
lemma side_self (r x : Pt) : side r x x = 0 := by
  unfold side; rw [sub_self]; unfold det2; simp

/-- **Barycentric side identity.**  If `x = w0•a + w1•b + w2•c` with
`w0 + w1 + w2 = 1`, then `w0•side r x a + w1•side r x b + w2•side r x c = 0`. -/
lemma barycentric_side_sum (r a b c x : Pt) (w0 w1 w2 : ℝ)
    (hsum : w0 + w1 + w2 = 1) (hx : x = w0 • a + w1 • b + w2 • c) :
    w0 * side r x a + w1 * side r x b + w2 * side r x c = 0 := by
  -- expand `side r x v = det2 r (v - x)` to coordinates and close by `nlinarith`.
  have hxa : x 0 = w0 * a 0 + w1 * b 0 + w2 * c 0 := by
    have := congrArg (fun p : Pt => p 0) hx
    simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using this
  have hxb : x 1 = w0 * a 1 + w1 * b 1 + w2 * c 1 := by
    have := congrArg (fun p : Pt => p 1) hx
    simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using this
  unfold side det2
  simp only [PiLp.sub_apply]
  rw [hxa, hxb]
  have hs : w2 = 1 - w0 - w1 := by linarith
  rw [hs]; ring

/-- **crossTau numerator closed form.**  For any base point `x`,
`crossTau P ρ x i • crossDen P ρ i = det2 (P.q i - x) (P.q (cyclicNext i) - P.q i)`. -/
lemma crossTau_mul_crossDen {n : ℕ} (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (i : Fin n) :
    crossTau P ρ x i * crossDen P ρ i =
      det2 (P.q i - x) (P.q (cyclicNext i) - P.q i) := by
  unfold crossTau
  rw [div_mul_cancel₀]
  exact crossDen_ne_zero P ρ i

/-! ## Part 3: the Fin-3 setup — three vertices, three weights, three side values

We now fix a triangle `Q` and work with `q0 = Q.q ⟨0⟩`, `q1 = Q.q ⟨1⟩`,
`q2 = Q.q ⟨2⟩` and the cyclic edges.  The crossTau numerators of the three edges
factor as `w_opp • orient`. -/

/-- The three Fin-3 cyclic facts: `cyclicNext ⟨0⟩ = ⟨1⟩`, `cyclicNext ⟨1⟩ = ⟨2⟩`,
`cyclicNext ⟨2⟩ = ⟨0⟩`. -/
lemma cyclicNext_three :
    (cyclicNext (⟨0, by omega⟩ : Fin 3) = ⟨1, by omega⟩) ∧
    (cyclicNext (⟨1, by omega⟩ : Fin 3) = ⟨2, by omega⟩) ∧
    (cyclicNext (⟨2, by omega⟩ : Fin 3) = ⟨0, by omega⟩) := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold cyclicNext; norm_num)

/-- The cyclic orient of a triangle is invariant under the three cyclic shifts. -/
lemma orient_cyclic (a b c : Pt) :
    orient a b c = orient b c a ∧ orient a b c = orient c a b := by
  constructor <;> (unfold orient det2; simp only [PiLp.sub_apply]; ring)

/-- **Edge crossTau numerator as a weighted orient.**  If
`x = wa•a + wb•b + wc•c` with `wa + wb + wc = 1`, then the crossTau numerator of
the edge `a → b` equals `wc • orient a b c`:
`det2 (a - x) (b - a) = wc * orient a b c`. -/
lemma crossNum_eq_weight_orient (a b c x : Pt) (wa wb wc : ℝ)
    (hsum : wa + wb + wc = 1) (hx : x = wa • a + wb • b + wc • c) :
    det2 (a - x) (b - a) = wc * orient a b c := by
  have hxa : x 0 = wa * a 0 + wb * b 0 + wc * c 0 := by
    have := congrArg (fun p : Pt => p 0) hx
    simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using this
  have hxb : x 1 = wa * a 1 + wb * b 1 + wc * c 1 := by
    have := congrArg (fun p : Pt => p 1) hx
    simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using this
  unfold orient det2
  simp only [PiLp.sub_apply]
  rw [hxa, hxb]
  have hwa : wa = 1 - wb - wc := by linarith
  rw [hwa]; ring

/-- **Forward guard in product form.**  For a base point `x`, `0 ≤ crossTau P ρ x i`
iff `0 ≤ (crossTau P ρ x i * crossDen P ρ i) * crossDen P ρ i` (multiply by the
positive square `crossDen^2`). -/
lemma crossTau_nonneg_iff {n : ℕ} (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (i : Fin n) :
    0 ≤ crossTau P ρ x i ↔
      0 ≤ (crossTau P ρ x i * crossDen P ρ i) * crossDen P ρ i := by
  have hD : crossDen P ρ i ≠ 0 := crossDen_ne_zero P ρ i
  have hD2 : 0 < crossDen P ρ i * crossDen P ρ i := mul_self_pos.mpr hD
  constructor
  · intro h
    have hmul : 0 ≤ crossTau P ρ x i * (crossDen P ρ i * crossDen P ρ i) :=
      mul_nonneg h (le_of_lt hD2)
    nlinarith [hmul]
  · intro h
    have heq : (crossTau P ρ x i * crossDen P ρ i) * crossDen P ρ i =
        crossTau P ρ x i * (crossDen P ρ i * crossDen P ρ i) := by ring
    rw [heq] at h
    exact nonneg_of_mul_nonneg_left h hD2

/-! ## Part 4: the pure-arithmetic forward count for a triangle interior

Three nonzero side values that are *not* all of one strict sign (forced by the
barycentric identity with positive weights), and a nonzero orient: the three
cyclic edge indicators (Span + forward-product-sign) sum to exactly `1`. -/

/-- The forward-key sign reduces to `0 ≤ O * d` (drop the positive weight). -/
lemma fwdKey_iff {w O d : ℝ} (hw : 0 < w) : 0 ≤ w * (O * d) ↔ 0 ≤ O * d := by
  constructor
  · intro h
    have h' : 0 ≤ (O * d) * w := by rw [mul_comm]; exact h
    exact nonneg_of_mul_nonneg_left h' hw
  · intro h; exact mul_nonneg (le_of_lt hw) h

/-- Trivial 0/1 resolution of a `Span ∧ forward` indicator: it is `1` together with
the condition, or `0` together with its negation. -/
lemma indicator_resolve (a b k : ℝ) :
    ((Span a b ∧ 0 ≤ k) ∧ (if Span a b ∧ 0 ≤ k then (1 : ℕ) else 0) = 1) ∨
    (¬ (Span a b ∧ 0 ≤ k) ∧ (if Span a b ∧ 0 ≤ k then (1 : ℕ) else 0) = 0) := by
  by_cases h : Span a b ∧ 0 ≤ k
  · exact Or.inl ⟨h, if_pos h⟩
  · exact Or.inr ⟨h, if_neg h⟩

set_option maxHeartbeats 2000000 in
/-- **The forward count is one (pure arithmetic).**  Let `s0, s1, s2 ≠ 0` be three
side values with positive weights `w0, w1, w2` and barycentric identity
`w0 s0 + w1 s1 + w2 s2 = 0`, and `O ≠ 0`.  Then the three cyclic edge indicators —
`Span` *and* the forward product-sign condition (`0 ≤ (w_opp O)(s_{next} - s_i)`) —
sum to exactly `1`.  This is the crossTau-sign content: of the (exactly two)
spanning edges, exactly one is forward. -/
lemma forward_count_eq_one (s0 s1 s2 O w0 w1 w2 : ℝ)
    (hs0 : s0 ≠ 0) (hs1 : s1 ≠ 0) (hs2 : s2 ≠ 0) (hO : O ≠ 0)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2)
    (hbary : w0 * s0 + w1 * s1 + w2 * s2 = 0) :
    (if Span s0 s1 ∧ 0 ≤ (w2 * O) * (s1 - s0) then 1 else 0) +
    (if Span s1 s2 ∧ 0 ≤ (w0 * O) * (s2 - s1) then 1 else 0) +
    (if Span s2 s0 ∧ 0 ≤ (w1 * O) * (s0 - s2) then 1 else 0) = 1 := by
  -- reduce each forward key `0 ≤ (w_opp O) Δ` to `0 ≤ O Δ` (drop the positive weight).
  rw [show ((w2 * O) * (s1 - s0)) = w2 * (O * (s1 - s0)) by ring,
      show ((w0 * O) * (s2 - s1)) = w0 * (O * (s2 - s1)) by ring,
      show ((w1 * O) * (s0 - s2)) = w1 * (O * (s0 - s2)) by ring]
  simp only [fwdKey_iff hw2, fwdKey_iff hw0, fwdKey_iff hw1]
  -- not all three the same strict sign
  have hnotallpos : ¬ (0 < s0 ∧ 0 < s1 ∧ 0 < s2) := by
    rintro ⟨h0, h1, h2⟩; nlinarith [mul_pos hw0 h0, mul_pos hw1 h1, mul_pos hw2 h2]
  have hnotallneg : ¬ (s0 < 0 ∧ s1 < 0 ∧ s2 < 0) := by
    rintro ⟨h0, h1, h2⟩
    nlinarith [mul_pos hw0 (neg_pos.mpr h0), mul_pos hw1 (neg_pos.mpr h1),
      mul_pos hw2 (neg_pos.mpr h2)]
  -- products of weights with O are nonzero
  have hw0O : w0 * O ≠ 0 := mul_ne_zero (ne_of_gt hw0) hO
  have hw1O : w1 * O ≠ 0 := mul_ne_zero (ne_of_gt hw1) hO
  have hw2O : w2 * O ≠ 0 := mul_ne_zero (ne_of_gt hw2) hO
  -- case split on the strict signs of the three side values and of `O`.
  rcases lt_or_gt_of_ne hs0 with h0 | h0 <;>
    rcases lt_or_gt_of_ne hs1 with h1 | h1 <;>
      rcases lt_or_gt_of_ne hs2 with h2 | h2 <;>
        rcases lt_or_gt_of_ne hO with hOs | hOs
  -- the all-neg and all-pos sign patterns (4 leaves) are excluded.
  all_goals first
    | (exfalso; exact hnotallneg ⟨h0, h1, h2⟩)
    | (exfalso; exact hnotallpos ⟨h0, h1, h2⟩)
    | skip
  -- remaining 12 leaves: resolve each of the three indicators; the only consistent
  -- combination is "exactly one forward edge", giving the sum `1`.
  all_goals (
    rcases indicator_resolve s0 s1 (O * (s1 - s0)) with ⟨c0, e0⟩ | ⟨c0, e0⟩ <;>
    rcases indicator_resolve s1 s2 (O * (s2 - s1)) with ⟨c1, e1⟩ | ⟨c1, e1⟩ <;>
    rcases indicator_resolve s2 s0 (O * (s0 - s2)) with ⟨c2, e2⟩ | ⟨c2, e2⟩ <;>
      rw [e0, e1, e2] <;>
      first
        | (first | rfl | omega)
        | (exfalso;
            first
              | (rcases c0.1 with ⟨ca, cb⟩ | ⟨ca, cb⟩ <;> nlinarith [c0.2])
              | (rcases c1.1 with ⟨ca, cb⟩ | ⟨ca, cb⟩ <;> nlinarith [c1.2])
              | (rcases c2.1 with ⟨ca, cb⟩ | ⟨ca, cb⟩ <;> nlinarith [c2.2])
              | (apply c0; exact ⟨Or.inl ⟨le_of_lt h0, h1⟩, by nlinarith⟩)
              | (apply c0; exact ⟨Or.inr ⟨le_of_lt h1, h0⟩, by nlinarith⟩)
              | (apply c1; exact ⟨Or.inl ⟨le_of_lt h1, h2⟩, by nlinarith⟩)
              | (apply c1; exact ⟨Or.inr ⟨le_of_lt h2, h1⟩, by nlinarith⟩)
              | (apply c2; exact ⟨Or.inl ⟨le_of_lt h2, h0⟩, by nlinarith⟩)
              | (apply c2; exact ⟨Or.inr ⟨le_of_lt h0, h2⟩, by nlinarith⟩)))

/-! ## Part 5: the polygon-level interior-odd crossing number

We instantiate `forward_count_eq_one` against the actual triangle.  The forward
guard `0 ≤ crossTau` is rewritten (via `crossTau_nonneg_iff`,
`crossTau_mul_crossDen`, `crossNum_eq_weight_orient`, `side_next_sub_side`) into
the arithmetic forward-product condition. -/

/-- **Interior point of a triangle has crossing number `1`.**  For a `3`-gon `Q`, a
valid ray `r`, and a point `x = w0•q0 + w1•q1 + w2•q2` with all weights `> 0` and
all side values nonzero, `CrossingNumber' Q r x = 1`. -/
lemma crossingNumber'_interior_eq_one (Q : StrictSimplePolygon 3) (r : RayDirection Q)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • Q.q ⟨0, by omega⟩ + w1 • Q.q ⟨1, by omega⟩ + w2 • Q.q ⟨2, by omega⟩)
    (hs0 : side r.r x (Q.q ⟨0, by omega⟩) ≠ 0)
    (hs1 : side r.r x (Q.q ⟨1, by omega⟩) ≠ 0)
    (hs2 : side r.r x (Q.q ⟨2, by omega⟩) ≠ 0) :
    CrossingNumber' Q r x = 1 := by
  classical
  set i0 : Fin 3 := ⟨0, by omega⟩
  set i1 : Fin 3 := ⟨1, by omega⟩
  set i2 : Fin 3 := ⟨2, by omega⟩
  obtain ⟨hn0, hn1, hn2⟩ := cyclicNext_three
  set q0 := Q.q i0 with hq0
  set q1 := Q.q i1 with hq1
  set q2 := Q.q i2 with hq2
  set s0 := side r.r x q0 with hsd0
  set s1 := side r.r x q1 with hsd1
  set s2 := side r.r x q2 with hsd2
  set O := orient q0 q1 q2 with hOdef
  -- O ≠ 0: the three vertices are noncollinear (strict polygon).
  have hO : O ≠ 0 := by
    have hnc := Q.noncollinear_consecutive i1
    have hpr : cyclicPrev i1 = i0 := by unfold cyclicPrev i1 i0; norm_num
    rw [hpr, hn1] at hnc
    rw [hOdef, hq0, hq1, hq2]
    exact hnc
  -- the crossing number equals the three-edge forward sum.
  have hcard : CrossingNumber' Q r x =
      (if EdgeCrossesRay' Q r x i0 then 1 else 0) +
      (if EdgeCrossesRay' Q r x i1 then 1 else 0) +
      (if EdgeCrossesRay' Q r x i2 then 1 else 0) := by
    unfold CrossingNumber' CrossingEdges'
    rw [Finset.card_filter]
    rw [show (Finset.univ : Finset (Fin 3)) = {i0, i1, i2} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
    ring
  rw [hcard]
  -- rewrite each edge's `EdgeCrossesRay'` into the arithmetic span+forward form.
  have hedge : ∀ (i j : Fin 3) (a b : ℝ) (wopp : ℝ),
      cyclicNext i = j →
      side r.r x (Q.q i) = a → side r.r x (Q.q j) = b →
      (det2 (Q.q i - x) (Q.q (cyclicNext i) - Q.q i) = wopp * O) →
      ((if EdgeCrossesRay' Q r x i then (1:ℕ) else 0) =
        if Span a b ∧ 0 ≤ wopp * O * (b - a) then 1 else 0) := by
    intro i j a b wopp hnext ha hb hnum
    have hnextq : Q.q (cyclicNext i) = Q.q j := by rw [hnext]
    have hspan : SpanCrossesSide Q r x i ↔ Span a b := by
      unfold SpanCrossesSide
      rw [ha, hnextq, hb]
    have hfwd : (0 ≤ crossTau Q r x i) ↔ 0 ≤ wopp * O * (b - a) := by
      rw [crossTau_nonneg_iff Q r x i, crossTau_mul_crossDen, hnum]
      have hden : crossDen Q r i = b - a := by
        have := side_next_sub_side Q r x i
        rw [hnextq, ha, hb] at this; exact this.symm
      rw [hden]
    unfold EdgeCrossesRay'
    by_cases hc : SpanCrossesSide Q r x i ∧ 0 ≤ crossTau Q r x i
    · rw [if_pos hc, if_pos ⟨hspan.mp hc.1, hfwd.mp hc.2⟩]
    · rw [if_neg hc, if_neg (by rintro ⟨h1, h2⟩; exact hc ⟨hspan.mpr h1, hfwd.mpr h2⟩)]
  -- the three numerators as weighted orients.
  have hN0 : det2 (Q.q i0 - x) (Q.q (cyclicNext i0) - Q.q i0) = w2 * O := by
    rw [hn0, crossNum_eq_weight_orient q0 q1 q2 x w0 w1 w2 hsum hx]
  have hN1 : det2 (Q.q i1 - x) (Q.q (cyclicNext i1) - Q.q i1) = w0 * O := by
    rw [hn1, crossNum_eq_weight_orient q1 q2 q0 x w1 w2 w0 (by linarith)
      (by rw [hx]; module)]
    rw [hOdef, (orient_cyclic q0 q1 q2).1]
  have hN2 : det2 (Q.q i2 - x) (Q.q (cyclicNext i2) - Q.q i2) = w1 * O := by
    rw [hn2, crossNum_eq_weight_orient q2 q0 q1 x w2 w0 w1 (by linarith)
      (by rw [hx]; module)]
    rw [hOdef, (orient_cyclic q0 q1 q2).2]
  rw [hedge i0 i1 s0 s1 w2 hn0 rfl rfl hN0,
      hedge i1 i2 s1 s2 w0 hn1 rfl rfl hN1,
      hedge i2 i0 s2 s0 w1 hn2 rfl rfl hN2]
  exact forward_count_eq_one s0 s1 s2 O w0 w1 w2 hs0 hs1 hs2 hO hw0 hw1 hw2
    (by rw [hsd0, hsd1, hsd2]; exact barycentric_side_sum r.r q0 q1 q2 x w0 w1 w2 hsum hx)

/-! ## Part 6: a valid ray missing every vertex of the ray line through `x`

For a point `x` distinct from all three vertices, there is a valid `RayDirection`
(`mkPt 1 t`) whose ray line through `x` passes through *no* vertex
(`side r x q_k ≠ 0` for all `k`) — avoid the finitely many bad slopes (edge-
parallel and the three vertex-alignment slopes). -/

/-- `side (mkPt 1 t) x v = v 1 - x 1 - t * (v 0 - x 0)`; it vanishes iff
`t = badSlope (v - x)` (when `v ≠ x`). -/
lemma side_mkPt_one (t : ℝ) (x v : Pt) :
    side (mkPt 1 t) x v = (v - x) 1 - t * (v - x) 0 := by
  unfold side
  rw [det2_mkPt_one]

/-- **A valid ray whose line through `x` misses every vertex.**  If `x` is distinct
from all three vertices of the `3`-gon, there is a valid `RayDirection r` with
`side r.r x (Q.q k) ≠ 0` for every `k`. -/
lemma exists_rayDir_side_ne_zero (Q : StrictSimplePolygon 3) {x : Pt}
    (hne : ∀ k : Fin 3, Q.q k ≠ x) :
    ∃ r : RayDirection Q, ∀ k : Fin 3, side r.r x (Q.q k) ≠ 0 := by
  classical
  -- bad slopes: the three edge slopes and the three vertex-alignment slopes.
  set bad : Finset ℝ :=
    (Finset.univ.image fun i : Fin 3 => badSlope (edgeVec Q i)) ∪
      (Finset.univ.image fun k : Fin 3 => badSlope (Q.q k - x)) with hbad
  obtain ⟨t, ht⟩ := bad.exists_notMem
  have hedge : ∀ i : Fin 3, t ≠ badSlope (edgeVec Q i) := by
    intro i hi; apply ht; apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩
  have hvert : ∀ k : Fin 3, t ≠ badSlope (Q.q k - x) := by
    intro k hk; apply ht; apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk.symm⟩
  refine ⟨{ r := mkPt 1 t
            r_ne_zero := mkPt_one_ne_zero t
            no_edge_parallel := by
              intro i hdet
              exact hedge i (slope_eq_badSlope_of_det2_mkPt_one_eq_zero
                (edgeVec_ne_zero Q i) hdet) }, ?_⟩
  intro k hzero
  -- side = det2 (mkPt 1 t) (Q.q k - x) = 0 ⟹ t = badSlope (Q.q k - x).
  have hvk : Q.q k - x ≠ 0 := sub_ne_zero.mpr (hne k)
  have hdet : det2 (mkPt 1 t) (Q.q k - x) = 0 := by
    have := hzero; unfold side at this; exact this
  exact hvert k (slope_eq_badSlope_of_det2_mkPt_one_eq_zero hvk hdet)

/-! ## Part 7: a strictly-interior point is off the boundary

For `x = w0•q0 + w1•q1 + w2•q2` with all weights `> 0`, `orient q0 q1 x` equals
`w2 • orient q0 q1 q2 ≠ 0`, so `x` is not collinear with edge `q0 q1`; cyclically,
`x` lies on no edge of the triangle, hence off the polygon boundary. -/

/-- `orient a b x = wc • orient a b c` for a barycentric point. -/
lemma orient_base_eq_weight_orient (a b c x : Pt) (wa wb wc : ℝ)
    (hsum : wa + wb + wc = 1) (hx : x = wa • a + wb • b + wc • c) :
    orient a b x = wc * orient a b c := by
  have hxa : x 0 = wa * a 0 + wb * b 0 + wc * c 0 := by
    have := congrArg (fun p : Pt => p 0) hx
    simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using this
  have hxb : x 1 = wa * a 1 + wb * b 1 + wc * c 1 := by
    have := congrArg (fun p : Pt => p 1) hx
    simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using this
  unfold orient det2
  simp only [PiLp.sub_apply]
  rw [hxa, hxb]
  have hwa : wa = 1 - wb - wc := by linarith
  rw [hwa]; ring

/-- **A point on the closed segment `a b` is collinear: `orient a b z = 0`.** -/
lemma orient_eq_zero_of_mem_seg {a b z : Pt} (hz : z ∈ seg a b) :
    orient a b z = 0 := by
  rw [seg, segment_eq_image_lineMap] at hz
  obtain ⟨t, _, rfl⟩ := hz
  unfold orient det2
  rw [AffineMap.lineMap_apply_module]
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **Strictly interior triangle point is off the boundary.**  If
`x = w0•q0 + w1•q1 + w2•q2` with all weights `> 0` and the three vertices are
noncollinear, then `x` lies on no edge of the `3`-gon. -/
lemma not_onBoundary_of_interior (Q : StrictSimplePolygon 3) {x : Pt} {w0 w1 w2 : ℝ}
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • Q.q ⟨0, by omega⟩ + w1 • Q.q ⟨1, by omega⟩ + w2 • Q.q ⟨2, by omega⟩) :
    ¬ OnBoundary Q x := by
  set i0 : Fin 3 := ⟨0, by omega⟩
  set i1 : Fin 3 := ⟨1, by omega⟩
  set i2 : Fin 3 := ⟨2, by omega⟩
  obtain ⟨hn0, hn1, hn2⟩ := cyclicNext_three
  set q0 := Q.q i0
  set q1 := Q.q i1
  set q2 := Q.q i2
  have hO : orient q0 q1 q2 ≠ 0 := by
    have hnc := Q.noncollinear_consecutive i1
    have hpr : cyclicPrev i1 = i0 := by unfold cyclicPrev i1 i0; norm_num
    rw [hpr, hn1] at hnc; exact hnc
  rintro ⟨i, hi⟩
  -- identify edge i with one of the three segments and derive a nonzero orient.
  fin_cases i
  · -- edge 0: seg q0 q1; orient q0 q1 x = w2 * O ≠ 0.
    rw [Edge, hn0] at hi
    have h1 := orient_eq_zero_of_mem_seg hi
    have h2 := orient_base_eq_weight_orient q0 q1 q2 x w0 w1 w2 hsum hx
    rw [h2] at h1; exact (mul_ne_zero (ne_of_gt hw2) hO) h1
  · -- edge 1: seg q1 q2; orient q1 q2 x = w0 * O' ≠ 0.
    rw [Edge, hn1] at hi
    have h1 := orient_eq_zero_of_mem_seg hi
    have h2 := orient_base_eq_weight_orient q1 q2 q0 x w1 w2 w0 (by linarith)
      (by rw [hx]; module)
    rw [h2] at h1
    exact (mul_ne_zero (ne_of_gt hw0) ((orient_cyclic q0 q1 q2).1 ▸ hO)) h1
  · -- edge 2: seg q2 q0; orient q2 q0 x = w1 * O'' ≠ 0.
    rw [Edge, hn2] at hi
    have h1 := orient_eq_zero_of_mem_seg hi
    have h2 := orient_base_eq_weight_orient q2 q0 q1 x w2 w0 w1 (by linarith)
      (by rw [hx]; module)
    rw [h2] at h1
    exact (mul_ne_zero (ne_of_gt hw1) ((orient_cyclic q0 q1 q2).2 ▸ hO)) h1

/-! ## Part 8: assembly — `TriangleConvexLeaf` unconditional

Every point of `closedTri q0 q1 q2` is in `ClosedRegion' Q σ`: a barycentric point
with some zero weight is on an edge (boundary, `Or.inl`); a strictly-interior point
is off the boundary with `CrossingNumber' Q r x = 1` (odd) for a vertex-avoiding
valid ray `r`, transported to `σ` by the unconditional ray-independence
`closedRegion'_chain_tri`. -/

/-- **A strictly-interior triangle point is in the closed region for every ray.** -/
lemma interior_mem_region (Q : StrictSimplePolygon 3) (σ : RayDirection Q)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • Q.q ⟨0, by omega⟩ + w1 • Q.q ⟨1, by omega⟩ + w2 • Q.q ⟨2, by omega⟩) :
    ClosedRegion' Q σ x := by
  -- `x` is off the boundary.
  have hoff : ¬ OnBoundary Q x := not_onBoundary_of_interior Q hw0 hw1 hw2 hsum hx
  -- `x` is distinct from every vertex (vertices are on the boundary).
  have hne : ∀ k : Fin 3, Q.q k ≠ x := by
    intro k hk; exact hoff (hk ▸ ProofsInTheBook.PolygonResidues.vertex_onBoundary Q k)
  -- a valid ray missing every vertex.
  obtain ⟨r, hr⟩ := exists_rayDir_side_ne_zero Q hne
  -- crossing number is 1 for `r`.
  have hone : CrossingNumber' Q r x = 1 :=
    crossingNumber'_interior_eq_one Q r hw0 hw1 hw2 hsum hx (hr _) (hr _) (hr _)
  -- so `x` is in the region for `r` (odd), then transport to `σ`.
  have hregr : ClosedRegion' Q r x := Or.inr (by rw [hone]; exact odd_one)
  exact (ProofsInTheBook.PolygonDegenerateWall.closedRegion'_chain_tri r σ hoff).mp hregr

/-- **`closedTri q0 q1 q2 ⊆ ClosedRegion' Q σ` for every `3`-gon and ray.** -/
theorem closedTri_subset_region (Q : StrictSimplePolygon 3) (σ : RayDirection Q) :
    closedTri (Q.q ⟨0, by omega⟩) (Q.q ⟨1, by omega⟩) (Q.q ⟨2, by omega⟩)
      ⊆ {x : Pt | ClosedRegion' Q σ x} := by
  intro x hx
  obtain ⟨w0, w1, w2, hw0, hw1, hw2, hsum, hxeq⟩ :=
    exists_barycentric_of_mem_closedTri hx
  -- dichotomy: a zero weight ⟹ on an edge (boundary); else strictly interior.
  rcases eq_or_lt_of_le hw0 with h0 | h0
  · -- w0 = 0: x ∈ seg q1 q2 = Edge 1 ⟹ boundary.
    refine Or.inl ⟨⟨1, by omega⟩, ?_⟩
    rw [Edge, show cyclicNext (⟨1, by omega⟩ : Fin 3) = ⟨2, by omega⟩ from
      (cyclicNext_three).2.1, seg]
    refine ⟨w1, w2, hw1, hw2, by linarith, ?_⟩
    rw [hxeq, ← h0]; module
  rcases eq_or_lt_of_le hw1 with h1 | h1
  · -- w1 = 0: x ∈ seg q0 q2 = Edge 2 (reversed) ⟹ boundary.
    refine Or.inl ⟨⟨2, by omega⟩, ?_⟩
    rw [Edge, show cyclicNext (⟨2, by omega⟩ : Fin 3) = ⟨0, by omega⟩ from
      (cyclicNext_three).2.2, seg]
    refine ⟨w2, w0, hw2, hw0, by linarith, ?_⟩
    rw [hxeq, ← h1]; module
  rcases eq_or_lt_of_le hw2 with h2 | h2
  · -- w2 = 0: x ∈ seg q0 q1 = Edge 0 ⟹ boundary.
    refine Or.inl ⟨⟨0, by omega⟩, ?_⟩
    rw [Edge, show cyclicNext (⟨0, by omega⟩ : Fin 3) = ⟨1, by omega⟩ from
      (cyclicNext_three).1, seg]
    refine ⟨w0, w1, hw0, hw1, by linarith, ?_⟩
    rw [hxeq, ← h2]; module
  · -- all weights strictly positive: strictly interior.
    exact interior_mem_region Q σ h0 h1 h2 hsum hxeq

/-- **`TriangleConvexLeaf`, UNCONDITIONAL.**  For every `3`-gon `Q` and ray `σ`, the
convex-vertex primitive at the middle vertex holds: the adjacent triangle (the whole
hull) is contained in the closed region.  This discharges the `hconv` oracle of
`artGallery_strict_unconditional`. -/
theorem triangleConvexLeaf_holds : TriangleConvexLeaf := by
  intro Q σ
  -- `IsConvexVertex' Q σ ⟨1⟩` is `closedTri (q (prev 1)) (q 1) (q (next 1)) ⊆ region`.
  show closedTri (Q.q (cyclicPrev (⟨1, by omega⟩ : Fin 3))) (Q.q ⟨1, by omega⟩)
      (Q.q (cyclicNext (⟨1, by omega⟩ : Fin 3))) ⊆ {x : Pt | ClosedRegion' Q σ x}
  have hprev : cyclicPrev (⟨1, by omega⟩ : Fin 3) = ⟨0, by omega⟩ := by
    unfold cyclicPrev; norm_num
  have hnext : cyclicNext (⟨1, by omega⟩ : Fin 3) = ⟨2, by omega⟩ := (cyclicNext_three).2.1
  rw [hprev, hnext]
  exact closedTri_subset_region Q σ

/-! ## Part 9: the Chapter-36 headline over only TWO remaining oracles

With `hconv` (`TriangleConvexLeaf`) now discharged unconditionally and
`TriangleExteriorEven` already unconditional
(`PolygonDegenerateWall.triangleExteriorEven_unconditional`), the art-gallery
`⌊n/3⌋` headline is conditional on only the two genuinely-irreducible planar
inputs: the uniform residual geometry `D` and the diagonal-attach peel `M`. -/

/-- **Chapter-36 art-gallery headline over two oracles (`D`, `M`).**  Every strict
simple polygon with a ray direction admits `≤ ⌊n/3⌋` vertex guards seeing its whole
closed region, conditional on exactly the residual geometry data `D` and the
diagonal-attach peel `M` — the convex-vertex leaf (`hconv`) is now supplied
unconditionally by `triangleConvexLeaf_holds` (and `TriangleExteriorEven` by the
degenerate-wall transport).  Three oracles reduced to two. -/
theorem artGallery_strict {n : ℕ}
    (D : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
        ProofsInTheBook.PolygonOracleClose.ResidualGeometryData P ρ)
    (M : ProofsInTheBook.PolygonLast.DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, ProofsInTheBook.PolygonRayIndep.Sees P ρ (P.q v) x :=
  ProofsInTheBook.PolygonDegenerateWall.artGallery_strict_unconditional
    D triangleConvexLeaf_holds M P ρ

end

end ProofsInTheBook.PolygonTriangleConvex
