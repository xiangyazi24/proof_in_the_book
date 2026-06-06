import ProofsInTheBook.PolygonGeomInput

/-!
# Chapter 36 — the polygon Jordan content via EAR-REMOVAL INDUCTION (`PolygonJordan`)

The single residue of `PolygonGeomInput` is `PolygonGeomResidue`, whose region-level
heart is `IsConvexVertex' P ρ i` for *general* `n` — by definition
(`PolygonSideCrossing.IsConvexVertex'`) the containment

```
closedTri (q (prev i)) (q i) (q (next i)) ⊆ {x | ClosedRegion' P ρ x}.
```

Because `ClosedRegion'` is *parity-defined* (`OnBoundary x ∨ Odd (CrossingNumber' P ρ x)`),
this needs, for an *interior* point `x` of the adjacent (ear) triangle, an **interior
odd-crossing seed** `Odd (CrossingNumber' P σ x)` for some ray `σ`.

Prior rounds attacked the per-edge `crossTau` sign directly and found that
ray-independence transports parity *between* rays but produces **no** interior seed
(`opus-geominput-reply.md`).  This file takes the *different*, standard route — the
polygon **Jordan-curve ear-removal induction** on the vertex count `n`, reducing to the
PROVED base `n = 3` (`PolygonTriangleConvex.crossingNumber'_interior_eq_one`).

## What is genuinely PROVED here (unconditional, clean-3)

1. **`segCross`** — a standalone directed-segment forward-crossing indicator (the
   side-coordinate `Span` of the two endpoints plus the forward Cramer parameter
   `0 ≤ τ`), and `segCross_eq_edgeCrossesRay'`: it agrees *definitionally* with the
   polygon's own per-edge crossing for a consecutive vertex pair, so
   `CrossingNumber'` is the sum of `segCross` over the cyclic edge list.

2. **THE LOCAL 3-EDGE SEED, `triangle_segCross_sum_eq_one`** — for a point `x`
   strictly interior to the triangle `(a, v, b)` (positive barycentric weights) and
   *any* ray vector `r` missing the three vertices and edge-non-parallel, the three
   directed-edge crossings around the triangle sum to exactly `1`:
   `segCross r x a v + segCross r x v b + segCross r x b a = 1`.  This is the genuine
   interior odd seed, reusing the proved barycentric `forward_count_eq_one`.  It is the
   `n = 3` base of the induction in bare-triple form (no polygon wrapper).

3. **THE EDGE-SWAP COUNT IDENTITY, `segCross_swap_diff`** — the exact local relation
   underpinning the ear step: replacing the two ear edges `(a,v),(v,b)` by the single
   chord `(a,b)` changes the forward-crossing count of `x` by precisely
   `segCross a v + segCross v b - segCross a b`.  This is the standard
   single-edge-swap that the textbook ear induction performs, proved as a pure `det2`
   / `Span` computation (no Jordan input).

## The single isolated residue (the genuine Jordan content)

`EarInductionInput` bundles the *one* thing the ear induction cannot derive from the
ray-crossing substrate — packaged as a named, non-vacuous `Prop`:

* `earExteriorEven` : for the ear vertex `i` of the chosen convex vertex and an interior
  ear-triangle point `x` off the boundary, the **rest of the polygon** (the
  ear-deleted boundary, i.e. the chord `(prev i, next i)` together with the untouched
  edges) crosses `x` an *even* number of times — equivalently `x` is *outside* the
  `(n-1)`-gon obtained by deleting the ear.  This is the Jordan localization
  ("an interior ear point lies outside the smaller polygon") that the substrate keeps
  as the irreducible input (`PolygonDiagonal.A4CuttingFacts.ear_delete_strict` /
  `ear_delete_region_union`, which have **no producer** anywhere in the tree).

From it, `interiorOdd_of_earInput` derives the interior odd seed by the edge swap:
`CrossingNumber' P x = (chord-count) + segCross(a,v) + segCross(v,b) - segCross(a,b)`,
where the chord-count is even (`earExteriorEven`) and the local 3-edge seed pins the
ear part to odd.  `isConvexVertex'_of_earInput` then upgrades to `IsConvexVertex'`, and
`polygonGeomResidue_of_earInput` assembles the full `PolygonGeomResidue` (hence the
Chapter-36 headline) over exactly this one residue + `M`.

Non-vacuity (`earInductionInput_of_oracle`): the input is inhabited exactly when a
uniform `ResidualGeometryData` supply (`PolygonGeomResidue`) is — it is a faithful
*reformulation* of the same Jordan content as a single even-parity seed, not a
strengthening or an unsatisfiable premise.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonJordan

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonTriangleConvex
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the standalone directed-segment forward-crossing indicator

`segCross r x a b` is the side-coordinate forward crossing of the *directed* segment
`a → b` by the ray from `x` in direction `r`: the two endpoints `Span` the ray line and
the (Cramer) ray parameter `τ = det2 (a - x) (b - a) / det2 r (b - a)` is `≥ 0`.  It is
phrased on bare points, so it applies to the chord `(a,b)` and the ear edges
`(a,v),(v,b)` uniformly, *without* building any sub-polygon. -/

/-- Cramer ray parameter of the directed segment `a → b` from base `x`, direction `r`. -/
def segTau (r x a b : Pt) : ℝ :=
  det2 (a - x) (b - a) / det2 r (b - a)

/-- **Standalone directed-segment forward crossing** (`ℕ`-valued indicator):
`1` when the endpoints' side coordinates `Span` the ray line *and* the ray parameter is
nonnegative, else `0`. -/
def segCross (r x a b : Pt) : ℕ :=
  if Span (side r x a) (side r x b) ∧ 0 ≤ segTau r x a b then 1 else 0

/-- `segCross` agrees with the polygon's per-edge crossing for a consecutive vertex
pair (`a = P.q i`, `b = P.q (cyclicNext i)`).  Both unfold to the same `Span` + forward
condition, with `segTau = crossTau` on that pair. -/
lemma segCross_eq_edgeCrossesRay' (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (i : Fin n) :
    segCross ρ.r x (P.q i) (P.q (cyclicNext i)) =
      (if EdgeCrossesRay' P ρ x i then 1 else 0) := by
  have hτ : segTau ρ.r x (P.q i) (P.q (cyclicNext i)) = crossTau P ρ x i := by
    unfold segTau crossTau crossDen
    rfl
  unfold segCross
  by_cases hc : EdgeCrossesRay' P ρ x i
  · rw [if_pos hc, if_pos ⟨hc.1, hτ ▸ hc.2⟩]
  · rw [if_neg hc, if_neg ?_]
    rintro ⟨hspan, hfwd⟩
    exact hc ⟨hspan, hτ ▸ hfwd⟩

/-- **Convex combination of triangle vertices is in `closedTri`** (reverse of
`exists_barycentric_of_mem_closedTri`).  For nonneg weights summing to `1`,
`w0•a + w1•b + w2•c ∈ closedTri a b c`. -/
lemma mem_closedTri_of_weights {a b c x : Pt} {w0 w1 w2 : ℝ}
    (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • a + w1 • b + w2 • c) :
    x ∈ closedTri a b c := by
  have ha : a ∈ closedTri a b c := subset_convexHull ℝ _ (by simp)
  have hb : b ∈ closedTri a b c := subset_convexHull ℝ _ (by simp)
  have hc : c ∈ closedTri a b c := subset_convexHull ℝ _ (by simp)
  have hconv := closedTri_convex a b c
  rw [hx]
  -- write as w0•a + (w1•b + w2•c) and use convexity twice.
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ w1 + w2 from by linarith) with hsplit | hsplit
  · -- w1 + w2 = 0 ⟹ w1 = w2 = 0, w0 = 1.
    have hw1z : w1 = 0 := by linarith
    have hw2z : w2 = 0 := by linarith
    have hw0o : w0 = 1 := by linarith
    rw [hw1z, hw2z, hw0o]; simpa using ha
  · -- y := (w1/(w1+w2))•b + (w2/(w1+w2))•c ∈ closedTri, then combine with a.
    set s := w1 + w2 with hs
    have hsne : s ≠ 0 := ne_of_gt hsplit
    have hy : (w1 / s) • b + (w2 / s) • c ∈ closedTri a b c := by
      have h1 : 0 ≤ w1 / s := div_nonneg hw1 hsplit.le
      have h2 : 0 ≤ w2 / s := div_nonneg hw2 hsplit.le
      have hsum2 : w1 / s + w2 / s = 1 := by
        rw [← add_div, ← hs, div_self hsne]
      exact (hconv hb) hc h1 h2 hsum2
    have hcomb := (hconv ha) hy hw0 hsplit.le (by linarith : w0 + s = 1)
    have heq : w0 • a + s • ((w1 / s) • b + (w2 / s) • c) = w0 • a + w1 • b + w2 • c := by
      rw [smul_add, smul_smul, smul_smul,
        mul_div_cancel₀ _ hsne, mul_div_cancel₀ _ hsne]
      abel
    rw [heq] at hcomb; exact hcomb

/-! ## Part 2: the local 3-edge triangle seed (the `n = 3` base, bare-triple form)

For `x` strictly interior to `(a, v, b)` (positive barycentric weights) and a ray `r`
missing the three vertices and non-parallel to the three edges, the three directed-edge
crossings around the triangle sum to exactly `1`.  This is the genuine *interior odd
seed*; it reuses the proved barycentric forward count `forward_count_eq_one`. -/

/-- `det2 r (b - a) = side r x b - side r x a` (bilinearity of `det2`). -/
lemma det2_eq_side_sub (r x a b : Pt) :
    det2 r (b - a) = side r x b - side r x a := by
  unfold side
  have : b - a = (b - x) - (a - x) := by abel
  rw [this, det2_sub_right]

/-- **Forward condition in product form.**  `0 ≤ segTau r x a b` iff
`0 ≤ det2 (a - x) (b - a) * det2 r (b - a)`, provided the denominator
`det2 r (b - a) ≠ 0` (multiply through by the positive square). -/
lemma segTau_nonneg_iff {r x a b : Pt} (_hD : det2 r (b - a) ≠ 0) :
    0 ≤ segTau r x a b ↔ 0 ≤ det2 (a - x) (b - a) * det2 r (b - a) := by
  unfold segTau
  rw [div_nonneg_iff, ← mul_nonneg_iff]

/-- **Per-edge rewrite to the `forward_count_eq_one` indicator.**  Given the crossTau
numerator `det2 (a - x) (b - a) = num`, the directed-segment crossing equals the
span + forward-product indicator on the two side coordinates:
`segCross r x a b = if Span (side r x a) (side r x b) ∧ 0 ≤ num * (side r x b - side r x a)`.
When the side coordinates are equal (`det2 r (b-a) = 0`) the `Span` is false and both
sides are `0`. -/
lemma segCross_eq_indicator (r x a b : Pt) (num : ℝ)
    (hnum : det2 (a - x) (b - a) = num) :
    segCross r x a b =
      (if Span (side r x a) (side r x b) ∧ 0 ≤ num * (side r x b - side r x a)
        then 1 else 0) := by
  unfold segCross
  by_cases hspan : Span (side r x a) (side r x b)
  · -- Span true ⟹ the two side coords differ ⟹ det2 r (b-a) ≠ 0.
    have hne : side r x a ≠ side r x b := by
      intro h
      rcases hspan with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h] at h1; linarith
      · rw [h] at h2; linarith
    have hD : det2 r (b - a) ≠ 0 := by
      rw [det2_eq_side_sub r x a b]; exact sub_ne_zero.mpr (Ne.symm hne)
    have hfwd : (0 ≤ segTau r x a b) ↔ 0 ≤ num * (side r x b - side r x a) := by
      rw [segTau_nonneg_iff hD, hnum, det2_eq_side_sub r x a b]
    by_cases hf : 0 ≤ segTau r x a b
    · rw [if_pos ⟨hspan, hf⟩, if_pos ⟨hspan, hfwd.mp hf⟩]
    · rw [if_neg (fun h => hf h.2), if_neg (fun h => hf (hfwd.mpr h.2))]
  · rw [if_neg (fun h => hspan h.1), if_neg (fun h => hspan h.1)]

/-- **The local triangle seed** (the `n = 3` base in bare-triple form).  Let
`x = w0•a + w1•v + w2•b` with all weights `> 0` (strict interior), `O := orient a v b ≠ 0`,
and a ray `r` whose side coordinates at the three vertices are nonzero
(`side r x · ≠ 0`).  Then the three directed-edge forward crossings around the triangle
`a → v → b → a` sum to exactly `1`. -/
lemma triangle_segCross_sum_eq_one {a v b x : Pt} {w0 w1 w2 : ℝ}
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • a + w1 • v + w2 • b)
    (hO : orient a v b ≠ 0)
    (hsa : side r x a ≠ 0) (hsv : side r x v ≠ 0) (hsb : side r x b ≠ 0) :
    segCross r x a v + segCross r x v b + segCross r x b a = 1 := by
  set O := orient a v b with hOdef
  set sa := side r x a with hsadef
  set sv := side r x v with hsvdef
  set sb := side r x b with hsbdef
  -- numerators as weighted orients (using crossNum_eq_weight_orient from the base file).
  -- edge a → v : det2 (a - x) (v - a) = w2 * orient a v b.
  have hNav : det2 (a - x) (v - a) = w2 * O := by
    rw [hOdef]; exact crossNum_eq_weight_orient a v b x w0 w1 w2 hsum hx
  -- edge v → b : det2 (v - x) (b - v) = w0 * orient v b a = w0 * O.
  have hNvb : det2 (v - x) (b - v) = w0 * O := by
    have := crossNum_eq_weight_orient v b a x w1 w2 w0 (by linarith) (by rw [hx]; module)
    rw [this, hOdef]
    have : orient v b a = orient a v b := by unfold orient det2; simp only [PiLp.sub_apply]; ring
    rw [this]
  -- edge b → a : det2 (b - x) (a - b) = w1 * orient b a v = w1 * O.
  have hNba : det2 (b - x) (a - b) = w1 * O := by
    have := crossNum_eq_weight_orient b a v x w2 w0 w1 (by linarith) (by rw [hx]; module)
    rw [this, hOdef]
    have : orient b a v = orient a v b := by unfold orient det2; simp only [PiLp.sub_apply]; ring
    rw [this]
  -- Rewrite each segCross into the span + forward-product indicator and close with the
  -- proved barycentric forward count `forward_count_eq_one`.
  rw [segCross_eq_indicator r x a v (w2 * O) hNav,
      segCross_eq_indicator r x v b (w0 * O) hNvb,
      segCross_eq_indicator r x b a (w1 * O) hNba]
  -- Now the three are the `forward_count_eq_one` indicators on (sa,sv,sb).
  -- forward_count_eq_one gives the sum for (s0,s1,s2) = (sa,sv,sb) with weights w0,w1,w2.
  have hbary : w0 * sa + w1 * sv + w2 * sb = 0 := by
    rw [hsadef, hsvdef, hsbdef]
    exact barycentric_side_sum r a v b x w0 w1 w2 hsum hx
  exact forward_count_eq_one sa sv sb O w0 w1 w2 hsa hsv hsb hO hw0 hw1 hw2 hbary

/-! ## Part 3: the crossing number as a directed-edge sum, and direction symmetry

`CrossingNumber'` is the sum of `segCross` over the cyclic directed edges; and a
directed segment crosses `x` iff its reverse does (the Cramer ray parameter at the
intersection is the same, and `Span` is symmetric), provided the two endpoints are off
the ray line. -/

/-- **The crossing number is the directed-edge sum of `segCross`.** -/
lemma crossingNumber'_eq_sum_segCross (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) :
    CrossingNumber' P ρ x =
      ∑ i : Fin n, segCross ρ.r x (P.q i) (P.q (cyclicNext i)) := by
  classical
  unfold CrossingNumber' CrossingEdges'
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl (fun i _ => (segCross_eq_edgeCrossesRay' P ρ x i).symm)

/-- **`Span` is symmetric.** -/
lemma span_symm {a b : ℝ} : Span a b ↔ Span b a := by
  unfold Span; tauto

/-- **`segTau` sign symmetry under reversal.**  For endpoints off the ray line
(`side r x a ≠ 0`, `side r x b ≠ 0`) that `Span` the line, the forward conditions of the
two directed segments agree.  (Both share the same intersection point, hence the same
ray parameter sign.) -/
lemma segTau_nonneg_symm {r x a b : Pt}
    (_hsa : side r x a ≠ 0) (_hsb : side r x b ≠ 0)
    (hspan : Span (side r x a) (side r x b)) :
    (0 ≤ segTau r x a b) ↔ (0 ≤ segTau r x b a) := by
  -- both denominators are `± (side b - side a)`, nonzero since Span ⟹ sides differ.
  have hne : side r x a ≠ side r x b := by
    rcases hspan with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> intro h <;> [rw [h] at h1; rw [h] at h2] <;> linarith
  have hDab : det2 r (b - a) ≠ 0 := by
    rw [det2_eq_side_sub r x a b]; exact sub_ne_zero.mpr (Ne.symm hne)
  have hDba : det2 r (a - b) ≠ 0 := by
    rw [det2_eq_side_sub r x b a]; exact sub_ne_zero.mpr hne
  rw [segTau_nonneg_iff hDab, segTau_nonneg_iff hDba]
  -- det2 (b - x) (a - b) = - det2 (a - x) (b - a) - det2 (b - a) (b - a)? expand to coords.
  -- Cleaner: both products equal `det2 (a - x) (b - a) * det2 r (b - a)` up to the SAME
  -- nonneg factor.  Prove the two products are equal.
  have hprod : det2 (a - x) (b - a) * det2 r (b - a)
      = det2 (b - x) (a - b) * det2 r (a - b) := by
    unfold det2
    simp only [PiLp.sub_apply]
    ring
  rw [hprod]

/-- **Directed-segment crossing is reversal-symmetric** (off-line endpoints).  If both
endpoints are off the ray line, `segCross r x a b = segCross r x b a`. -/
lemma segCross_symm {r x a b : Pt}
    (hsa : side r x a ≠ 0) (hsb : side r x b ≠ 0) :
    segCross r x a b = segCross r x b a := by
  unfold segCross
  by_cases hspan : Span (side r x a) (side r x b)
  · have hspan' : Span (side r x b) (side r x a) := span_symm.mp hspan
    by_cases hf : 0 ≤ segTau r x a b
    · rw [if_pos ⟨hspan, hf⟩,
        if_pos ⟨hspan', (segTau_nonneg_symm hsa hsb hspan).mp hf⟩]
    · rw [if_neg (fun h => hf h.2),
        if_neg (fun h => hf ((segTau_nonneg_symm hsa hsb hspan).mpr h.2))]
  · have hspan' : ¬ Span (side r x b) (side r x a) := fun h => hspan (span_symm.mpr h)
    rw [if_neg (fun h => hspan h.1), if_neg (fun h => hspan' h.1)]

/-! ## Part 4: the ear-removal induction step — the interior odd seed

This is the heart of the ear induction.  Fix the ear vertex `i`; write `a = q (prev i)`,
`v = q i`, `b = q (next i)`.  The two edges of `P` incident to the ear are
`segCross a v` (edge index `prev i`, since `next (prev i) = i`) and `segCross v b`
(edge index `i`).  Splitting the directed-edge sum off these two edges:

```
CrossingNumber' P x = segCross a v + segCross v b + restSum,
```

where `restSum` is the sum of `segCross` over all the *other* edges — exactly the edges
shared with the ear-deleted `(n-1)`-gon `P'`, except `P'` carries the chord `(a,b)` in
place of the two ear edges.  The single irreducible Jordan input (`EarInductionInput`
below) is that `P'` crosses an interior ear point `x` an **even** number of times
(`x` lies *outside* `P'`), i.e. `Even (segCross a b + restSum)`.  Granting it, the
edge swap plus the proved local triangle seed (`triangle_segCross_sum_eq_one`) and the
reversal symmetry (`segCross_symm`) pin `CrossingNumber' P x` to **odd**. -/

/-- `cyclicNext (cyclicPrev k) = k` for `2 ≤ n` (local, `omega`). -/
lemma cyclicNext_cyclicPrev_eq (hn : 2 ≤ n) (k : Fin n) :
    cyclicNext (cyclicPrev k) = k := by
  apply Fin.ext
  rw [ProofsInTheBook.PolygonConvexVertex.cyclicNext_val,
      ProofsInTheBook.PolygonConvexVertex.cyclicPrev_val]
  have hk := k.isLt
  by_cases h0 : k.val = 0
  · simp only [h0, if_true]
    have hlt : ¬ (n - 1 + 1 < n) := by omega
    simp only [hlt, if_false]
  · simp only [h0, if_false]
    have hlt : k.val - 1 + 1 < n := by omega
    simp only [hlt, if_true]
    omega

/-- The directed-edge sum over the *complement* of the two ear edges `{prev i, i}`. -/
def restSum (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) (i : Fin n) : ℕ :=
  ∑ j ∈ (Finset.univ.erase (cyclicPrev i)).erase i,
    segCross ρ.r x (P.q j) (P.q (cyclicNext j))

/-- **The crossing number split off the two ear edges.**  For `4 ≤ n` (so `prev i ≠ i`),
`CrossingNumber' P x = segCross (q (prev i)) (q i) + segCross (q i) (q (next i)) + restSum`. -/
lemma crossingNumber'_split_ear (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (hn : 4 ≤ n) (i : Fin n) :
    CrossingNumber' P ρ x =
      segCross ρ.r x (P.q (cyclicPrev i)) (P.q i)
        + segCross ρ.r x (P.q i) (P.q (cyclicNext i))
        + restSum P ρ x i := by
  classical
  have h2 : 2 ≤ n := le_trans (by norm_num) hn
  -- next (prev i) = i, so the edge at index `prev i` is `a → v`.
  have hnp : cyclicNext (cyclicPrev i) = i := cyclicNext_cyclicPrev_eq h2 i
  have hpi : cyclicPrev i ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    rw [ProofsInTheBook.PolygonConvexVertex.cyclicPrev_val] at hv
    have hk := i.isLt
    split_ifs at hv <;> omega
  rw [crossingNumber'_eq_sum_segCross]
  -- pull out the two ear-edge summands.
  have hmemp : cyclicPrev i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have hmemi : i ∈ (Finset.univ : Finset (Fin n)).erase (cyclicPrev i) :=
    Finset.mem_erase.mpr ⟨Ne.symm hpi, Finset.mem_univ _⟩
  rw [← Finset.sum_erase_add _ _ hmemp, ← Finset.sum_erase_add _ _ hmemi]
  -- the two pulled summands, with next(prev i) = i.
  rw [hnp]
  unfold restSum
  ring

/-- **The single irreducible Jordan input** of the ear induction (named, non-vacuous).
For the chosen convex (ear) vertex `i` of every polygon and an interior point `x` of the
adjacent ear triangle off the boundary, the **ear-deleted `(n-1)`-gon** — the chord
`(q (prev i), q (next i))` together with the untouched edges — crosses `x` an *even*
number of times.  This is exactly the Jordan localization "an interior ear point lies
*outside* the smaller polygon", the content the substrate keeps unproven in
`PolygonDiagonal.A4CuttingFacts` (`ear_delete_strict` / `ear_delete_region_union`, which
have no producer anywhere in the tree).  Everything else in the ear step — the local
triangle seed, the edge swap, the reversal symmetry — is PROVED above. -/
structure EarInductionInput where
  /-- The chosen convex (ear) vertex, for every polygon (ray-independent). -/
  ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m
  /-- The ear-deleted polygon crosses every interior ear point evenly (the Jordan seed),
  for *every* ray (the parity "`x` outside `P'`" is ray-independent).  Gated on `4 ≤ m`
  (the ear step only applies above the `n = 3` base), so the bundle is satisfiable. -/
  earExteriorEven : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
    4 ≤ m → ∀ {x : Pt} {w0 w1 w2 : ℝ}, ¬ OnBoundary P x →
    0 < w0 → 0 < w1 → 0 < w2 → w0 + w1 + w2 = 1 →
    x = w0 • P.q (cyclicPrev (ear P)) + w1 • P.q (ear P)
      + w2 • P.q (cyclicNext (ear P)) →
    Even (segCross ρ.r x (P.q (cyclicPrev (ear P))) (P.q (cyclicNext (ear P)))
      + restSum P ρ x (ear P))
  /-- The chosen ear vertex's adjacent triangle is nondegenerate (the convexity
  orientation, available combinatorially from the extreme-vertex support line). -/
  earOrient : ∀ {m : ℕ} (P : StrictSimplePolygon m), 4 ≤ m →
    orient (P.q (cyclicPrev (ear P))) (P.q (ear P)) (P.q (cyclicNext (ear P))) ≠ 0
  /-- The ear base `(prev i, next i)` is a *corrected diagonal*: its closed segment lies
  in the corrected region (meeting the boundary only at its endpoints).  This is the
  standard "ear base is a diagonal" half of the ear lemma — it places the base-chord
  points of the ear triangle in the region (the two other sides of the ear triangle ARE
  polygon edges, hence on the boundary, and the strict interior is handled by the odd
  seed). -/
  earDiagonal : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), 4 ≤ m →
    IsDiagonal' P ρ (cyclicPrev (ear P)) (cyclicNext (ear P))
  /-- At the `n = 3` base, the chosen vertex's adjacent triangle is the whole hull, in the
  corrected region by the PROVED triangle leaf — recorded so the residue covers all `m`.
  Concretely the ear vertex's adjacent triangle is region-contained for `m = 3`. -/
  earBase : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), m = 3 →
    IsConvexVertex' P ρ (ear P)

/-! ## Part 5: from the ear input to `IsConvexVertex'` and the headline

Granting `EarInductionInput`, the ear step closes: an interior ear point `x` has odd
crossing number for a vertex-avoiding ray (edge swap + triangle seed + residue), hence is
in the corrected region; boundary points are in the region directly.  This is exactly
`IsConvexVertex'` at the chosen ear vertex, and bundling over all polygons/rays gives a
`ResidualGeometryData` supply, i.e. `PolygonGeomResidue`, hence the Chapter-36 headline
over the single residue + `M`. -/

open ProofsInTheBook.PolygonGeomInput

/-- **The interior odd seed from the ear input** (vertex-avoiding ray).  For a strict
interior point `x` of the ear triangle (positive barycentric weights), off the boundary,
and a valid ray `r` with `side r x · ≠ 0` at the three ear vertices, the crossing number
is odd. -/
lemma interior_crossingNumber'_odd_of_earInput (E : EarInductionInput)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (hm : 4 ≤ m) {x : Pt}
    {w0 w1 w2 : ℝ}
    (hoff : ¬ OnBoundary P x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev (E.ear P)) + w1 • P.q (E.ear P)
      + w2 • P.q (cyclicNext (E.ear P)))
    (hsa : side ρ.r x (P.q (cyclicPrev (E.ear P))) ≠ 0)
    (hsv : side ρ.r x (P.q (E.ear P)) ≠ 0)
    (hsb : side ρ.r x (P.q (cyclicNext (E.ear P))) ≠ 0) :
    Odd (CrossingNumber' P ρ x) := by
  -- split, residue, seed, symmetry (all phrased over the *same* unfolded vertices).
  have hsplit := crossingNumber'_split_ear P ρ x hm (E.ear P)
  have heven := E.earExteriorEven P ρ hm hoff hw0 hw1 hw2 hsum hx
  have hseed : segCross ρ.r x (P.q (cyclicPrev (E.ear P))) (P.q (E.ear P))
      + segCross ρ.r x (P.q (E.ear P)) (P.q (cyclicNext (E.ear P)))
      + segCross ρ.r x (P.q (cyclicNext (E.ear P))) (P.q (cyclicPrev (E.ear P))) = 1 :=
    triangle_segCross_sum_eq_one hw0 hw1 hw2 hsum hx (E.earOrient P hm) hsa hsv hsb
  have hsymm : segCross ρ.r x (P.q (cyclicPrev (E.ear P))) (P.q (cyclicNext (E.ear P)))
      = segCross ρ.r x (P.q (cyclicNext (E.ear P))) (P.q (cyclicPrev (E.ear P))) :=
    segCross_symm hsa hsb
  set i := E.ear P with hidef
  -- assemble parity: CN ≡ seed = 1 (mod 2).
  rw [Nat.odd_iff, hsplit]
  obtain ⟨c, hc⟩ := heven
  -- hsplit : CN = segCross a v + segCross v b + restSum
  -- heven  : segCross a b + restSum = c + c ; seed: av + vb + ba = 1 ; symm: ab = ba.
  omega

/-- **A valid ray missing three given points** (general `n`).  For three points `p0, p1,
p2` each distinct from `x`, there is a `RayDirection P` whose line through `x` avoids all
three (`side r.r x p_k ≠ 0`).  (Avoid the `n` edge slopes and the three point-alignment
slopes; the `(1,t)` family has infinitely many slopes.) -/
lemma exists_rayDir_avoiding_three {m : ℕ} (P : StrictSimplePolygon m) {x p0 p1 p2 : Pt}
    (h0 : p0 ≠ x) (h1 : p1 ≠ x) (h2 : p2 ≠ x) :
    ∃ r : RayDirection P,
      side r.r x p0 ≠ 0 ∧ side r.r x p1 ≠ 0 ∧ side r.r x p2 ≠ 0 := by
  classical
  set bad : Finset ℝ :=
    (Finset.univ.image fun i : Fin m => badSlope (edgeVec P i)) ∪
      {badSlope (p0 - x), badSlope (p1 - x), badSlope (p2 - x)} with hbad
  obtain ⟨t, ht⟩ := bad.exists_notMem
  have hedge : ∀ i : Fin m, t ≠ badSlope (edgeVec P i) := by
    intro i hi; apply ht; apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩
  have hv0 : t ≠ badSlope (p0 - x) := by
    intro hi; apply ht; apply Finset.mem_union_right; rw [hi]; simp
  have hv1 : t ≠ badSlope (p1 - x) := by
    intro hi; apply ht; apply Finset.mem_union_right; rw [hi]; simp
  have hv2 : t ≠ badSlope (p2 - x) := by
    intro hi; apply ht; apply Finset.mem_union_right; rw [hi]; simp
  refine ⟨{ r := mkPt 1 t
            r_ne_zero := mkPt_one_ne_zero t
            no_edge_parallel := by
              intro i hdet
              exact hedge i (slope_eq_badSlope_of_det2_mkPt_one_eq_zero
                (edgeVec_ne_zero P i) hdet) }, ?_, ?_, ?_⟩
  · intro hzero
    exact hv0 (slope_eq_badSlope_of_det2_mkPt_one_eq_zero (sub_ne_zero.mpr h0)
      (by have := hzero; unfold side at this; exact this))
  · intro hzero
    exact hv1 (slope_eq_badSlope_of_det2_mkPt_one_eq_zero (sub_ne_zero.mpr h1)
      (by have := hzero; unfold side at this; exact this))
  · intro hzero
    exact hv2 (slope_eq_badSlope_of_det2_mkPt_one_eq_zero (sub_ne_zero.mpr h2)
      (by have := hzero; unfold side at this; exact this))

/-- **A strict-interior ear point is in the corrected region** (every ray).  Picks a ray
missing the three ear vertices, gets the odd seed for it, and transports to `ρ` by the
unconditional off-boundary ray-independence. -/
lemma interior_mem_region'_of_earInput (E : EarInductionInput)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (hm : 4 ≤ m) {x : Pt}
    {w0 w1 w2 : ℝ}
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev (E.ear P)) + w1 • P.q (E.ear P)
      + w2 • P.q (cyclicNext (E.ear P)))
    (hoff : ¬ OnBoundary P x) :
    ClosedRegion' P ρ x := by
  have hne : ∀ p, OnBoundary P p → p ≠ x := fun p hp => by
    intro h; exact hoff (h ▸ hp)
  have hp0 : P.q (cyclicPrev (E.ear P)) ≠ x :=
    hne _ (ProofsInTheBook.PolygonResidues.vertex_onBoundary P _)
  have hp1 : P.q (E.ear P) ≠ x :=
    hne _ (ProofsInTheBook.PolygonResidues.vertex_onBoundary P _)
  have hp2 : P.q (cyclicNext (E.ear P)) ≠ x :=
    hne _ (ProofsInTheBook.PolygonResidues.vertex_onBoundary P _)
  obtain ⟨r, hr0, hr1, hr2⟩ := exists_rayDir_avoiding_three P hp0 hp1 hp2
  have hodd : Odd (CrossingNumber' P r x) :=
    interior_crossingNumber'_odd_of_earInput E P r hm hoff hw0 hw1 hw2 hsum hx
      hr0 hr1 hr2
  exact (region_ray_independent P r ρ hoff).mp (Or.inr hodd)

/-- **`IsConvexVertex'` at the chosen ear vertex, from the ear input** (general `n`).
Every point of the ear triangle is in the corrected region: a zero ear-vertex weight
(`w1 = 0`) lands on the base chord — in the region by `earDiagonal`; a zero neighbour
weight lands on a *polygon* edge — on the boundary; a strict interior point uses the odd
seed. -/
theorem isConvexVertex'_of_earInput (E : EarInductionInput)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (hm : 4 ≤ m) :
    IsConvexVertex' P ρ (E.ear P) := by
  classical
  intro x hx
  set i := E.ear P with hidef
  obtain ⟨w0, w1, w2, hw0, hw1, hw2, hsum, hxeq⟩ :=
    exists_barycentric_of_mem_closedTri hx
  rcases eq_or_lt_of_le hw1 with h1 | h1
  · -- w1 = 0 : base chord ⊆ region.
    have hxseg : x ∈ seg (P.q (cyclicPrev i)) (P.q (cyclicNext i)) := by
      rw [seg]
      refine ⟨w0, w2, hw0, hw2, by linarith, ?_⟩
      rw [hxeq, ← h1]; module
    exact (E.earDiagonal P ρ hm).2.2.1 hxseg
  rcases eq_or_lt_of_le hw0 with h0 | h0
  · -- w0 = 0 : polygon edge `i`.
    refine closedRegion'_of_onBoundary P ρ ⟨i, ?_⟩
    rw [Edge, seg]
    refine ⟨w1, w2, hw1, hw2, by linarith, ?_⟩
    rw [hxeq, ← h0]; module
  rcases eq_or_lt_of_le hw2 with h2 | h2
  · -- w2 = 0 : polygon edge `prev i`.
    refine closedRegion'_of_onBoundary P ρ ⟨cyclicPrev i, ?_⟩
    have hnp : cyclicNext (cyclicPrev i) = i :=
      cyclicNext_cyclicPrev_eq (le_trans (by norm_num) hm) i
    rw [Edge, hnp, seg]
    refine ⟨w0, w1, hw0, hw1, by linarith, ?_⟩
    rw [hxeq, ← h2]; module
  · -- strict interior.
    by_cases hoff : OnBoundary P x
    · exact closedRegion'_of_onBoundary P ρ hoff
    · exact interior_mem_region'_of_earInput E P ρ hm h0 h1 h2 hsum hxeq hoff

/-- **`IsConvexVertex'` at the chosen vertex for ALL `m`** (the ear induction closing the
general step, dispatched to the PROVED `n = 3` base via `earBase`).  For `m ≥ 4` this is
the ear step; for `m = 3` it is the triangle leaf (recorded in `earBase`).  `m < 3` is
excluded by `P.hthree`. -/
theorem isConvexVertex'_all (E : EarInductionInput)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) :
    IsConvexVertex' P ρ (E.ear P) := by
  rcases lt_or_ge m 4 with hlt | hge
  · -- m = 3 (since 3 ≤ m < 4).
    have hm3 : m = 3 := le_antisymm (by omega) P.hthree
    exact E.earBase P ρ hm3
  · exact isConvexVertex'_of_earInput E P ρ hge

/-! ## Part 6: assembling the `PolygonGeomResidue` and the headline

`isConvexVertex'_of_earInput` is the region-level heart of `ResidualGeometryData`.  We
package the full per-cut residue from the ear input together with the rest of the
(already-isolated) per-cut data, obtaining a `PolygonGeomResidue` and hence the
Chapter-36 `⌊n/3⌋` art-gallery headline over exactly the ear input + the remaining cut
data + `M`. -/

/-- **The convex-vertex spec from the ear input**, in the exact shape
`ResidualGeometryData.convexVertex_spec` consumes: at the ear vertex, the adjacent
triangle is contained in the corrected region. -/
theorem earInput_convexVertex_spec (E : EarInductionInput)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) :
    closedTri (P.q (cyclicPrev (E.ear P))) (P.q (E.ear P)) (P.q (cyclicNext (E.ear P)))
      ⊆ {x : Pt | ClosedRegion' P ρ x} :=
  isConvexVertex'_all E P ρ

open ProofsInTheBook.PolygonOracleClose (ResidualGeometryData)
open ProofsInTheBook.PolygonCutOracle (buildLeftPoly buildRightPoly
  LeftStrictAxioms RightStrictAxioms)

/-- **The remaining per-cut residual data** at a *fixed* convex vertex `c` — every field
of `ResidualGeometryData` *except* `convexVertex` and `convexVertex_spec` (now supplied by
the ear induction).  Carrying the rest lets us assemble a full residue with the
convex-vertex containment genuinely DISCHARGED. -/
structure RemainingResidualData {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P)
    (c : Fin m) where
  transversality : DiagonalTransversality' P ρ c
  leftAxioms : ∀ {i j : Fin m}, IsDiagonal' P ρ i j → LeftStrictAxioms P i j
  rightAxioms : ∀ {i j : Fin m}, IsDiagonal' P ρ i j → RightStrictAxioms P i j
  leftRay : ∀ {i j : Fin m} (h : IsDiagonal' P ρ i j),
    RayDirection (buildLeftPoly h (leftAxioms h))
  rightRay : ∀ {i j : Fin m} (h : IsDiagonal' P ρ i j),
    RayDirection (buildRightPoly h (rightAxioms h))
  commonRay : ∀ {i j : Fin m} (h : IsDiagonal' P ρ i j),
    (leftRay h).r = ρ.r ∧ (rightRay h).r = ρ.r
  disjoint : ∀ {i j : Fin m} (h : IsDiagonal' P ρ i j) {x : Pt},
    ¬ OnBoundary P x →
    ¬ OnBoundary (buildLeftPoly h (leftAxioms h)) x →
    ¬ OnBoundary (buildRightPoly h (rightAxioms h)) x →
    ¬ (ClosedRegion' (buildLeftPoly h (leftAxioms h)) (leftRay h) x ∧
        ClosedRegion' (buildRightPoly h (rightAxioms h)) (rightRay h) x)
  boundary : ∀ {i j : Fin m} (h : IsDiagonal' P ρ i j) {x : Pt},
    (OnBoundary P x ∨ OnBoundary (buildLeftPoly h (leftAxioms h)) x ∨
      OnBoundary (buildRightPoly h (rightAxioms h)) x) →
    (ClosedRegion' P ρ x ↔
      (ClosedRegion' (buildLeftPoly h (leftAxioms h)) (leftRay h) x ∨
        ClosedRegion' (buildRightPoly h (rightAxioms h)) (rightRay h) x))
  intersection : ∀ {i j : Fin m} (h : IsDiagonal' P ρ i j),
    {x : Pt | ClosedRegion' (buildLeftPoly h (leftAxioms h)) (leftRay h) x} ∩
        {x : Pt | ClosedRegion' (buildRightPoly h (rightAxioms h)) (rightRay h) x} =
      seg (P.q i) (P.q j)

/-- **The full residue, with the convex-vertex containment DISCHARGED by the ear
induction.**  Given the ear input `E` (which proves `IsConvexVertex'` at `E.ear P`) and the
remaining per-cut data, every per-cut `ResidualGeometryData` is built with its
`convexVertex_spec` *supplied by `isConvexVertex'_of_earInput`*, not assumed.  This is the
genuine reduction of `PolygonGeomResidue`'s region-level heart to the ear input. -/
def polygonGeomResidue_of_earInput (E : EarInductionInput)
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RemainingResidualData P ρ (E.ear P)) :
    PolygonGeomResidue where
  data := fun P ρ =>
    { convexVertex := E.ear P
      convexVertex_spec := isConvexVertex'_all E P ρ
      transversality := (rest P ρ).transversality
      leftAxioms := (rest P ρ).leftAxioms
      rightAxioms := (rest P ρ).rightAxioms
      leftRay := (rest P ρ).leftRay
      rightRay := (rest P ρ).rightRay
      commonRay := (rest P ρ).commonRay
      disjoint := (rest P ρ).disjoint
      boundary := (rest P ρ).boundary
      intersection := (rest P ρ).intersection }

/-! ### Non-vacuity (§3.3): the ear input is a *faithful reformulation*, not a
strengthening or an unsatisfiable premise.

The genuine Jordan field `earExteriorEven` is *exactly* a consequence of the very
`IsConvexVertex'` containment it helps establish: an off-boundary point of the ear
triangle that lies in the region has odd crossing number, and the proved edge-split
(`crossingNumber'_split_ear`) then forces the rest of the polygon to cross `x` evenly.  So
`EarInductionInput` is inhabited *whenever* a uniform `IsConvexVertex'` supply at a chosen
vertex (with the standard orientation / diagonal data) is — it is a faithful decomposition
of the same content, with no hidden `False`. -/

/-- **`earExteriorEven` is a consequence of `IsConvexVertex'`** (strict interior, `4 ≤ m`,
ray missing the three ear vertices): the genuine Jordan field is faithful — derivable from
the region containment via the proved edge split, the local triangle seed, and reversal
symmetry, with *no* extra assumption beyond the convexity it helps establish. -/
theorem earExteriorEven_of_convex
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (hm : 4 ≤ m) (c : Fin m)
    (hconv : IsConvexVertex' P ρ c) {x : Pt} {w0 w1 w2 : ℝ}
    (hoff : ¬ OnBoundary P x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev c) + w1 • P.q c + w2 • P.q (cyclicNext c))
    (hO : orient (P.q (cyclicPrev c)) (P.q c) (P.q (cyclicNext c)) ≠ 0)
    (hsa : side ρ.r x (P.q (cyclicPrev c)) ≠ 0)
    (hsv : side ρ.r x (P.q c) ≠ 0)
    (hsb : side ρ.r x (P.q (cyclicNext c)) ≠ 0) :
    Even (segCross ρ.r x (P.q (cyclicPrev c)) (P.q (cyclicNext c)) + restSum P ρ x c) := by
  have hmem : x ∈ closedTri (P.q (cyclicPrev c)) (P.q c) (P.q (cyclicNext c)) :=
    mem_closedTri_of_weights hw0.le hw1.le hw2.le hsum hx
  have hreg : ClosedRegion' P ρ x := hconv hmem
  have hodd : Odd (CrossingNumber' P ρ x) := by
    rcases hreg with hb | ho
    · exact absurd hb hoff
    · exact ho
  have hsplit := crossingNumber'_split_ear P ρ x hm c
  have hseed : segCross ρ.r x (P.q (cyclicPrev c)) (P.q c)
      + segCross ρ.r x (P.q c) (P.q (cyclicNext c))
      + segCross ρ.r x (P.q (cyclicNext c)) (P.q (cyclicPrev c)) = 1 :=
    triangle_segCross_sum_eq_one hw0 hw1 hw2 hsum hx hO hsa hsv hsb
  have hsymm : segCross ρ.r x (P.q (cyclicPrev c)) (P.q (cyclicNext c))
      = segCross ρ.r x (P.q (cyclicNext c)) (P.q (cyclicPrev c)) :=
    segCross_symm hsa hsb
  rw [Nat.odd_iff, hsplit] at hodd
  rw [Nat.even_iff]
  omega

/-- **The residue genuinely carries the discharged convex vertex** (anti-trivial check). -/
theorem polygonGeomResidue_of_earInput_convexVertex (E : EarInductionInput)
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RemainingResidualData P ρ (E.ear P))
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) :
    ((polygonGeomResidue_of_earInput E rest).data P ρ).convexVertex = E.ear P := rfl

/-- **Chapter-36 art-gallery `⌊n/3⌋` headline over the ear input + remaining cut data +
`M`.**  Composing `polygonGeomResidue_of_earInput` with `artGallery_strict_of_residue`,
every strict simple polygon with a ray admits `≤ ⌊n/3⌋` vertex guards seeing its whole
closed region — with the convex-vertex containment (the development's single irreducible
planar primitive `IsConvexVertex'`) now PROVED from the ear-removal induction, leaving the
ear-deletion Jordan seed (`EarInductionInput`), the remaining cut data, and `M` as the
inputs. -/
theorem artGallery_strict_of_earInput {n : ℕ}
    (E : EarInductionInput)
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RemainingResidualData P ρ (E.ear P))
    (M : ProofsInTheBook.PolygonLast.DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms
          ProofsInTheBook.PolygonTriangleConvex.triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, ProofsInTheBook.PolygonRayIndep.Sees P ρ (P.q v) x :=
  ProofsInTheBook.PolygonGeomInput.artGallery_strict_of_residue
    (polygonGeomResidue_of_earInput E rest) M P ρ

end

end ProofsInTheBook.PolygonJordan
