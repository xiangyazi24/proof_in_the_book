import ProofsInTheBook.PolygonJordan

/-!
# Chapter 36 — the ear-exterior even parity via the det2-side of the ear chord
  (`PolygonEarExterior`)

`PolygonJordan` collapsed the entire Chapter-36 ear-removal induction to the *single*
`EarInductionInput` field

```
earExteriorEven :  Even (segCross ρ.r x a b + restSum P ρ x i)
```

for an interior ear point `x = w0•a + w1•v + w2•b` (`a = q (prev i)`, `v = q i`,
`b = q (next i)`, all weights `> 0`), off the boundary — "the ear-deleted `(n-1)`-gon
crosses the interior ear point evenly, i.e. `x` lies *outside* the smaller polygon".
Everything else in the ear step (the local 3-edge seed `triangle_segCross_sum_eq_one`,
the edge split `crossingNumber'_split_ear`, the reversal symmetry `segCross_symm`, the
ray transport via `region_ray_independent`, the `n = 3` base) is PROVED there, clean-3.

## What this file establishes (unconditional, clean-3)

1. **THE EXACT PARITY EQUIVALENCE** `earExteriorEven_iff_interiorOdd` — for a
   vertex-avoiding ray (side coords nonzero at the three ear vertices) and a
   nondegenerate ear, the residual field is *exactly equivalent* to the interior odd
   seed:
   ```
   Even (segCross a b + restSum)  ↔  Odd (CrossingNumber' P ρ x).
   ```
   Proof: the split `crossingNumber'_split_ear` gives
   `CN = segCross a v + segCross v b + restSum`; the seed
   `triangle_segCross_sum_eq_one` gives `segCross a v + segCross v b + segCross b a = 1`;
   the symmetry `segCross_symm` gives `segCross a b = segCross b a`; hence
   `segCross a b + restSum = CN - 1 + 2·segCross a b`, whose parity is `Odd CN`.
   This is the genuine det2-side content: the ear-deleted boundary crosses `x` evenly
   **iff** `x` is in the open region of `P` (odd crossing).  No Jordan input, no `P'`.

2. **THE det2-SIDE GEOMETRY** `interiorEar_diagSide_eq` / `interiorEar_sameSide_v` —
   the chord `(a, b)` lies on the line `{ y | diagSide a b y = 0 }`; the convex vertex
   `v` is strictly off it (nondegenerate ear), and an interior ear point `x` lies on the
   *same* open half-plane as `v` with `diagSide x = w1 · diagSide v` (`w1 > 0`).  This is
   the exact "x interior to the ear ⟹ x and v on the same side of the chord line"
   det2-side fact, proved unconditionally (`diagSide` affine, vanishing at `a, b`).

3. **THE SINGLE NAMED RESIDUE** `InteriorEarParityMatch` — the one irreducible Jordan
   localization, in *parity-match* form: *an interior ear point `x` has the same crossing
   parity for the whole polygon `P` as for its own ear triangle* (`CrossingNumber' P σ x ≡
   earTriSegSum`), i.e. `x` is inside `P` exactly as it is inside the ear (the ear ⊆ region
   of `P`).  We prove

   * `earExteriorEven_of_parityMatch` : the residue *discharges* `earExteriorEven` for
     **every** ray, by *pure split algebra* — `crossingNumber'_split_ear` (unconditional)
     gives `segCross a b + restSum ≡ CrossingNumber' P ρ x + earTriSegSum`, and the residue
     forces the two parities to match; **no side / non-degeneracy hypotheses** are needed;
   * `parityMatch_of_convex` : the residue is a *consequence* of `IsConvexVertex'`
     (faithful — interior region ⟹ odd crossing, and the ear-triangle interior seed makes
     `earTriSegSum` odd too — no hidden strengthening);
   * `earInductionInput_of_parityMatch` / `isConvexVertex'_all_of_parityMatch` : from the
     residue (+ the standard combinatorial orientation / ear-base-diagonal / `n = 3` base
     data) the *full* `EarInductionInput` is constructible, hence
     `polygonGeomResidue_of_earInput` becomes input-free in the even-parity field and the
     Chapter-36 `⌊n/3⌋` headline is conditional on exactly this *one* geometric residue +
     the remaining cut data + `M`.

4. **THE ear-triangle interior parity** `earTriSegSum_odd_of_valid` (PROVED, all valid ray
   directions): building the ear `(a, v, b)` as a genuine `StrictSimplePolygon 3`
   (`earTri`, with a self-contained `det2` simplicity proof `seg_inter_seg_eq_vertex`) and
   reusing the PROVED triangle interior count, the ear-triangle directed-edge `segCross`
   sum is odd — the closed `n = 3` content underlying the residue's faithfulness.

## The honest boundary (the single concrete failing chain)

`InteriorEarParityMatch` is the general-`n` interior parity-match, and the split of Part 1
shows it is *logically equivalent* to `earExteriorEven` itself — so this file makes precise
that the residual ear field is **exactly** the statement "an interior ear point is inside
`P` exactly as it is inside its ear", with all surrounding algebra (the unconditional
split, the local triangle seed, the reversal symmetry, the same-side `det2` geometry, the
ear-triangle simplicity + interior parity) fully discharged.  Producing the parity match
unconditionally requires the odd-crossing of an interior ear point for `P` — `Odd
(CrossingNumber' P σ x)` — which would need either building the ear-deleted polygon as a
genuine `StrictSimplePolygon (n-1)` (`PolygonDiagonal.A4CuttingFacts.ear_delete_strict`,
**no producer** in the tree) or a base-point Jordan separation (no translate-the-base-point
parity engine exists — all parity transport in the substrate varies the *ray*, not `x`).
The chain dead-ends exactly at this one interior-odd membership; everything reachable from
the ray-crossing substrate is proved here.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonEarExterior

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonJordan
open ProofsInTheBook.PolygonTriangleConvex
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the exact parity equivalence `earExteriorEven ↔ interior odd`

For a vertex-avoiding ray and a nondegenerate ear, the residual even-parity field is
exactly equivalent to the interior odd-crossing seed, via the proved edge split, the
local triangle seed, and the reversal symmetry. -/

/-- **The exact parity equivalence.**  For `4 ≤ n`, an interior ear point
`x = w0•a + w1•v + w2•b` (positive weights) with a nondegenerate ear orientation and a
ray whose side coordinates are nonzero at the three ear vertices, the ear-deleted
boundary crosses `x` *evenly* **iff** `x` has *odd* crossing number for `P`:

```
Even (segCross ρ.r x a b + restSum P ρ x i)  ↔  Odd (CrossingNumber' P ρ x).
```

This is the genuine det2-side content of `earExteriorEven`: it equals "x is in the open
region of `P`".  Proved from `crossingNumber'_split_ear`, `triangle_segCross_sum_eq_one`,
and `segCross_symm` — no Jordan input. -/
theorem earExteriorEven_iff_interiorOdd
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (hn : 4 ≤ n) (i : Fin n) {x : Pt}
    {w0 w1 w2 : ℝ}
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i))
    (hO : orient (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) ≠ 0)
    (hsa : side ρ.r x (P.q (cyclicPrev i)) ≠ 0)
    (hsv : side ρ.r x (P.q i) ≠ 0)
    (hsb : side ρ.r x (P.q (cyclicNext i)) ≠ 0) :
    Even (segCross ρ.r x (P.q (cyclicPrev i)) (P.q (cyclicNext i)) + restSum P ρ x i)
      ↔ Odd (CrossingNumber' P ρ x) := by
  -- the three proved local relations, all phrased over the same unfolded vertices.
  have hsplit := crossingNumber'_split_ear P ρ x hn i
  have hseed : segCross ρ.r x (P.q (cyclicPrev i)) (P.q i)
      + segCross ρ.r x (P.q i) (P.q (cyclicNext i))
      + segCross ρ.r x (P.q (cyclicNext i)) (P.q (cyclicPrev i)) = 1 :=
    triangle_segCross_sum_eq_one hw0 hw1 hw2 hsum hx hO hsa hsv hsb
  have hsymm : segCross ρ.r x (P.q (cyclicPrev i)) (P.q (cyclicNext i))
      = segCross ρ.r x (P.q (cyclicNext i)) (P.q (cyclicPrev i)) :=
    segCross_symm hsa hsb
  rw [Nat.even_iff, Nat.odd_iff, hsplit]
  -- with S := CN-split, the field = segCross a b + restSum, and we showed
  -- segCross a b + restSum = (av + vb + restSum) - 1 + 2·(a b).  omega closes parity.
  omega

/-! ## Part 2: the det2-side geometry of the ear chord (new, unconditional)

The ear chord `(a, b) = (q (prev i), q (next i))` lies on the line
`{ y | diagSide a b y = 0 }`.  For a nondegenerate ear the convex vertex `v = q i` is
strictly off the line, and an interior ear point `x = w0•a + w1•v + w2•b` (`w1 > 0`)
lies on the *same* open half-plane as `v`, with `diagSide x = w1 · diagSide v`.  This is
the exact "x interior to the ear ⟹ x, v on the same side of the chord" det2-side fact.

We use the *bare* `diagDir`/`diagSide` of `PolygonCutGeometry` (chord direction
`b - a`, signed side of `y` w.r.t. the line through `a`).  They are affine and vanish at
both chord endpoints. -/

open ProofsInTheBook.PolygonCutGeometry (diagDir diagSide diagSide_left diagSide_right
  diagSide_lineMap diagSide_eq_zero_of_mem_seg)

/-- **Convexity of the ear ⟹ the apex is strictly off the chord line.**  If the ear
orientation `orient a v b ≠ 0`, then `diagSide a b v ≠ 0` (the apex is strictly on one
side of the chord line). -/
theorem diagSide_apex_ne_zero (P : StrictSimplePolygon n) (i : Fin n)
    (hO : orient (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) ≠ 0) :
    diagSide P (cyclicPrev i) (cyclicNext i) (P.q i) ≠ 0 := by
  -- diagSide a b v = side (b - a) a v = det2 (b - a) (v - a)
  --               = - det2 (v - a) (b - a) = - orient a v b.
  intro hz
  apply hO
  have hexpand : diagSide P (cyclicPrev i) (cyclicNext i) (P.q i)
      = - orient (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) := by
    unfold diagSide side diagDir orient det2
    simp only [PiLp.sub_apply]
    ring
  rw [hexpand] at hz
  linarith [hz]

/-- **The interior-ear det2-side identity.**  For `x = w0•a + w1•v + w2•b` an interior
ear point, `diagSide a b x = w1 · diagSide a b v` (the chord side of `x` is the apex side
scaled by the apex weight).  `diagSide` vanishes at `a` and `b` and is affine, so only
the `v`-component survives. -/
theorem interiorEar_diagSide_eq (P : StrictSimplePolygon n) (i : Fin n) {x : Pt}
    {w0 w1 w2 : ℝ} (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i)) :
    diagSide P (cyclicPrev i) (cyclicNext i) x
      = w1 * diagSide P (cyclicPrev i) (cyclicNext i) (P.q i) := by
  set a := P.q (cyclicPrev i) with ha
  set v := P.q i with hv
  set b := P.q (cyclicNext i) with hb
  -- diagSide is a linear-affine functional vanishing at a and b; expand to det2.
  have hexpand : ∀ y : Pt, diagSide P (cyclicPrev i) (cyclicNext i) y
      = det2 (b - a) (y - a) := by
    intro y; unfold diagSide side diagDir; rw [ha, hb]
  rw [hexpand x, hexpand (P.q i)]
  -- x - a = w1•(v - a) + w2•(b - a)  (since w0 + w1 + w2 = 1).
  have hxa : x - a = w1 • (v - a) + w2 • (b - a) := by
    rw [hx]
    have hw0 : w0 = 1 - w1 - w2 := by linarith
    rw [hw0]
    ext k
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hxa, det2_add_right, det2_smul_right, det2_smul_right,
    show b - a = b - a from rfl]
  -- det2 (b - a) (b - a) = 0.
  rw [show det2 (b - a) (b - a) = 0 from det2_self (b - a)]
  rw [hv]
  ring

/-- **An interior ear point is strictly on the apex side of the chord line.**  For a
nondegenerate ear and `w1 > 0`, `diagSide a b x ≠ 0` and has the same sign as
`diagSide a b v`: `x` and `v` lie in the *same* open half-plane of the chord line. -/
theorem interiorEar_sameSide_v (P : StrictSimplePolygon n) (i : Fin n) {x : Pt}
    {w0 w1 w2 : ℝ} (hw1 : 0 < w1) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i))
    (hO : orient (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) ≠ 0) :
    diagSide P (cyclicPrev i) (cyclicNext i) x ≠ 0 ∧
      0 < diagSide P (cyclicPrev i) (cyclicNext i) x
          * diagSide P (cyclicPrev i) (cyclicNext i) (P.q i) := by
  have hvne := diagSide_apex_ne_zero P i hO
  have heq := interiorEar_diagSide_eq P i hsum hx
  set dv := diagSide P (cyclicPrev i) (cyclicNext i) (P.q i) with hdv
  have hsq : 0 < dv * dv := mul_self_pos.mpr hvne
  constructor
  · rw [heq]
    exact mul_ne_zero (ne_of_gt hw1) hvne
  · rw [heq]
    -- (w1 * dv) * dv = w1 * (dv * dv) > 0.
    have hreassoc : w1 * dv * dv = w1 * (dv * dv) := by ring
    rw [hreassoc]
    exact mul_pos hw1 hsq

/-! ## Part 3: the single named geometric residue and the discharge of `earExteriorEven`

The crossing-number split (`crossingNumber'_split_ear`, *unconditional* for every ray)
gives, mod `2`,
```
segCross a b + restSum ≡ CrossingNumber' P ρ x + EarTriSegSum ρ x
```
where `EarTriSegSum ρ x = segCross a v + segCross v b + segCross a b` is the directed-edge
sum of the ear triangle.  Hence `earExteriorEven` (`Even (segCross a b + restSum)`) holds
**iff** `x` has the same crossing parity for the whole polygon `P` as for the ear triangle.
This *parity match* is the single irreducible Jordan localization: an interior ear point
is inside `P` exactly as it is inside its own ear triangle (the ear ⊆ region of `P`).  We
package it as a named, non-vacuous `Prop` `InteriorEarParityMatch`, derive `earExteriorEven`
from it for **every** ray by pure split algebra (no side / non-degeneracy hypotheses), and
prove it faithful (a consequence of `IsConvexVertex'` together with the PROVED ear-triangle
interior parity). -/

/-- The directed-edge `segCross` sum of the ear triangle `(a, v, b)` at vertex `i`:
`segCross a v + segCross v b + segCross a b`.  (Equals `CrossingNumber'` of the ear
triangle for ray directions valid on it; `segCross_add_rev_even` relates `a b` to `b a`.) -/
def earTriSegSum (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) (i : Fin n) :
    ℕ :=
  segCross ρ.r x (P.q (cyclicPrev i)) (P.q i)
    + segCross ρ.r x (P.q i) (P.q (cyclicNext i))
    + segCross ρ.r x (P.q (cyclicPrev i)) (P.q (cyclicNext i))

/-- **The single geometric residue** (the parity-match form of the interior ear seed).
For the chosen ear vertex of every polygon (`4 ≤ m`), every ray, and a strict-interior ear
point off the boundary, `x` has the *same crossing parity* for `P` as for its ear triangle
(both odd — `x` is inside both).  By the unconditional split this is *exactly*
`earExteriorEven`; it is the irreducible Jordan content "the ear lies in the region of
`P`". -/
def InteriorEarParityMatch (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m) : Prop :=
  ∀ {m : ℕ} (P : StrictSimplePolygon m) (σ : RayDirection P), 4 ≤ m →
    ∀ {x : Pt} {w0 w1 w2 : ℝ}, ¬ OnBoundary P x →
    0 < w0 → 0 < w1 → 0 < w2 → w0 + w1 + w2 = 1 →
    x = w0 • P.q (cyclicPrev (ear P)) + w1 • P.q (ear P)
      + w2 • P.q (cyclicNext (ear P)) →
    CrossingNumber' P σ x % 2 = earTriSegSum P σ x (ear P) % 2

/-! ### Auxiliary fact A: the directed chord crossings sum evenly (unconditional)

`segCross r x a b + segCross r x b a` is always even: when the two endpoints do not
`Span` the ray line both terms vanish; when they do, the forward conditions of the two
reversed segments agree (`Span` is symmetric and the shared intersection point gives the
same ray parameter), so the two indicators coincide.  This holds with *no* off-line
hypothesis (the `Span` predicate's half-open straddle already forces the relevant
denominator nonzero). -/

/-- **The reversed-pair directed crossing is even.**  For any ray base `x`, direction
`r`, and points `a, b`, `Even (segCross r x a b + segCross r x b a)`. -/
theorem segCross_add_rev_even (r x a b : Pt) :
    Even (segCross r x a b + segCross r x b a) := by
  unfold segCross
  by_cases hspan : Span (side r x a) (side r x b)
  · -- Span holds ⟹ the two side coords straddle ⟹ they differ ⟹ denom nonzero.
    have hspan' : Span (side r x b) (side r x a) := span_symm.mp hspan
    have hne : side r x a ≠ side r x b := by
      rcases hspan with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> intro h <;>
        [rw [h] at h1; rw [h] at h2] <;> linarith
    have hDab : det2 r (b - a) ≠ 0 := by
      rw [det2_eq_side_sub r x a b]; exact sub_ne_zero.mpr (Ne.symm hne)
    have hDba : det2 r (a - b) ≠ 0 := by
      rw [det2_eq_side_sub r x b a]; exact sub_ne_zero.mpr hne
    -- the two forward conditions agree (same intersection point, proportional params).
    have hsymm : (0 ≤ segTau r x a b) ↔ (0 ≤ segTau r x b a) := by
      rw [segTau_nonneg_iff hDab, segTau_nonneg_iff hDba]
      have hprod : det2 (a - x) (b - a) * det2 r (b - a)
          = det2 (b - x) (a - b) * det2 r (a - b) := by
        unfold det2; simp only [PiLp.sub_apply]; ring
      rw [hprod]
    by_cases hf : 0 ≤ segTau r x a b
    · rw [if_pos ⟨hspan, hf⟩, if_pos ⟨hspan', hsymm.mp hf⟩]; decide
    · rw [if_neg (fun h => hf h.2), if_neg (fun h => hf (hsymm.mpr h.2))]; decide
  · have hspan' : ¬ Span (side r x b) (side r x a) := fun h => hspan (span_symm.mpr h)
    rw [if_neg (fun h => hspan h.1), if_neg (fun h => hspan' h.1)]; decide

/-! ### Auxiliary fact B: the ear-triangle directed-edge sum is odd (all rays)

Building the ear triangle `(a, v, b)` as a genuine `StrictSimplePolygon 3` lets us reuse
the PROVED interior-odd crossing (`crossingNumber'_interior_eq_one`) and its
ray-independence (`region_ray_independent`).  The directed-edge `segCross` sum of the ear
triangle, `segCross a v + segCross v b + segCross b a`, is exactly
`CrossingNumber' earTri ρ x` (by `crossingNumber'_eq_sum_segCross`), hence odd for every
ray. -/

/-- **Segment intersection at the shared vertex** (det2 form).  For `det2 (p - q) (s - q)
≠ 0`, the two segments `seg q p` and `seg q s` meet exactly at `q`. -/
theorem seg_inter_seg_eq_vertex {p q s : Pt} (hdet : det2 (p - q) (s - q) ≠ 0) :
    seg q p ∩ seg q s = {q} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩, ?_⟩
  rintro m ⟨hmp, hms⟩
  rw [seg, segment_eq_image_lineMap] at hmp hms
  obtain ⟨t, _ht, htm⟩ := hmp
  obtain ⟨u, _hu, hum⟩ := hms
  -- m - q = t • (p - q) = u • (s - q).
  have ht' : m - q = t • (p - q) := by
    rw [← htm, AffineMap.lineMap_apply_module]; ext k
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hu' : m - q = u • (s - q) := by
    rw [← hum, AffineMap.lineMap_apply_module]; ext k
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  -- subtract: t • (p - q) - u • (s - q) = 0; annihilate by det2 against (p-q) and (s-q).
  have hzero : t • (p - q) - u • (s - q) = 0 := by rw [← ht', ← hu']; abel
  -- det2 (p-q) (·) and det2 (s-q) (·) applied to the combination.
  have hdp : det2 (p - q) (t • (p - q) - u • (s - q)) = 0 := by rw [hzero]; simp [det2]
  have hds : det2 (s - q) (t • (p - q) - u • (s - q)) = 0 := by rw [hzero]; simp [det2]
  rw [det2_sub_right, det2_smul_right, det2_smul_right, det2_self] at hdp hds
  -- hdp : t * 0 - u * det2 (p-q) (s-q) = 0  ⟹ u = 0.
  have hdetps : det2 (p - q) (s - q) ≠ 0 := hdet
  have hdetsp : det2 (s - q) (p - q) ≠ 0 := by
    rw [det2_antisymm]; exact neg_ne_zero.mpr hdet
  have hu0 : u = 0 := by
    have : u * det2 (p - q) (s - q) = 0 := by rw [mul_comm]; linarith [hdp]
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hdetps
  have hm : m - q = 0 := by rw [hu', hu0, zero_smul]
  rw [sub_eq_zero] at hm; exact hm

/-- The ear-triangle vertex tuple `0 ↦ a`, `1 ↦ v`, `2 ↦ b`. -/
def earTriTuple (a v b : Pt) : Fin 3 → Pt :=
  fun k => if k.val = 0 then a else if k.val = 1 then v else b

@[simp] lemma earTriTuple_zero (a v b : Pt) : earTriTuple a v b ⟨0, by omega⟩ = a := rfl
@[simp] lemma earTriTuple_one (a v b : Pt) : earTriTuple a v b ⟨1, by omega⟩ = v := rfl
@[simp] lemma earTriTuple_two (a v b : Pt) : earTriTuple a v b ⟨2, by omega⟩ = b := rfl

/-- **The ear triangle as a genuine `StrictSimplePolygon 3`.**  For three points with
`orient a v b ≠ 0` (nondegenerate), the tuple `(a, v, b)` is a strict simple polygon: the
vertices are distinct (noncollinearity), consecutive triples are noncollinear (the same
orient up to sign), and every edge pair is cyclically adjacent (`3` edges), meeting only
at the shared vertex (`seg_inter_seg_eq_vertex`). -/
def earTri {a v b : Pt} (hO : orient a v b ≠ 0) : StrictSimplePolygon 3 where
  hthree := le_refl 3
  q := earTriTuple a v b
  injective_q := by
    -- distinctness from noncollinearity.
    have hav : a ≠ v := by
      intro h; apply hO; unfold orient det2; rw [h]
      simp only [PiLp.sub_apply]; ring
    have hvb : v ≠ b := by
      intro h; apply hO; unfold orient det2; rw [h]
      simp only [PiLp.sub_apply]; ring
    have hab : a ≠ b := by
      intro h; apply hO; unfold orient det2; rw [h]
      simp only [PiLp.sub_apply]; ring
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [earTriTuple_zero, earTriTuple_one, earTriTuple_two] at hij <;>
      first
        | rfl
        | (exact absurd hij hav) | (exact absurd hij.symm hav)
        | (exact absurd hij hvb) | (exact absurd hij.symm hvb)
        | (exact absurd hij hab) | (exact absurd hij.symm hab)
  noncollinear_consecutive := by
    intro i
    obtain ⟨hn0, hn1, hn2⟩ := cyclicNext_three
    fin_cases i
    · -- i = 0: prev 0 = 2, next 0 = 1 ⟹ orient b a v.
      show orient (earTriTuple a v b (cyclicPrev ⟨0, by omega⟩)) _ _ ≠ 0
      have hp : cyclicPrev (⟨0, by omega⟩ : Fin 3) = ⟨2, by omega⟩ := by decide
      rw [hp, hn0]; simp only [earTriTuple_zero, earTriTuple_one, earTriTuple_two]
      rw [← (orient_cyclic a v b).2]; exact hO
    · -- i = 1: prev 1 = 0, next 1 = 2 ⟹ orient a v b.
      show orient (earTriTuple a v b (cyclicPrev ⟨1, by omega⟩)) _ _ ≠ 0
      have hp : cyclicPrev (⟨1, by omega⟩ : Fin 3) = ⟨0, by omega⟩ := by decide
      rw [hp, hn1]; simp only [earTriTuple_zero, earTriTuple_one, earTriTuple_two]; exact hO
    · -- i = 2: prev 2 = 1, next 2 = 0 ⟹ orient v b a.
      show orient (earTriTuple a v b (cyclicPrev ⟨2, by omega⟩)) _ _ ≠ 0
      have hp : cyclicPrev (⟨2, by omega⟩ : Fin 3) = ⟨1, by omega⟩ := by decide
      rw [hp, hn2]; simp only [earTriTuple_zero, earTriTuple_one, earTriTuple_two]
      rw [← (orient_cyclic a v b).1]; exact hO
  edge_intersection := by
    intro i j
    obtain ⟨hn0, hn1, hn2⟩ := cyclicNext_three
    -- det2 facts for the three shared-vertex pairings (each = ± orient a v b ≠ 0).
    have hOe : orient a v b = a 0 * v 1 - a 0 * b 1 - v 0 * a 1 + v 0 * b 1
        + b 0 * a 1 - b 0 * v 1 := by unfold orient det2; simp only [PiLp.sub_apply]; ring
    have dvav : det2 (a - v) (b - v) ≠ 0 := by
      have heq : det2 (a - v) (b - v) = - orient a v b := by
        unfold det2; simp only [PiLp.sub_apply]; rw [hOe]; ring
      rw [heq]; exact neg_ne_zero.mpr hO
    have dvbv : det2 (v - b) (a - b) ≠ 0 := by
      have heq : det2 (v - b) (a - b) = - orient a v b := by
        unfold det2; simp only [PiLp.sub_apply]; rw [hOe]; ring
      rw [heq]; exact neg_ne_zero.mpr hO
    have dvba : det2 (b - a) (v - a) ≠ 0 := by
      have heq : det2 (b - a) (v - a) = - orient a v b := by
        unfold det2; simp only [PiLp.sub_apply]; rw [hOe]; ring
      rw [heq]; exact neg_ne_zero.mpr hO
    -- seg is symmetric.
    have hsc : ∀ p q : Pt, seg p q = seg q p := fun p q => by
      unfold seg; rw [segment_symm]
    -- the three adjacent-edge intersections, via seg_inter_seg_eq_vertex (any orientation).
    -- edge 0 = seg a v, edge 1 = seg v b, edge 2 = seg b a.
    have e01 : seg a v ∩ seg v b = {v} := by
      rw [hsc a v]; exact seg_inter_seg_eq_vertex dvav
    have e12 : seg v b ∩ seg b a = {b} := by
      rw [hsc v b]; exact seg_inter_seg_eq_vertex dvbv
    have e20 : seg b a ∩ seg a v = {a} := by
      rw [hsc b a]; exact seg_inter_seg_eq_vertex dvba
    fin_cases i <;> fin_cases j <;>
      simp only [EdgeIntersectionCondition, Edge, hn0, hn1, hn2, earTriTuple_zero,
        earTriTuple_one, earTriTuple_two, ↓reduceDIte, Set.inter_self]
    -- remaining 6 off-diagonal goals (diagonals closed by `Set.inter_self`).
    · exact e01                          -- (0,1): seg a v ∩ seg v b = {v}
    · rw [Set.inter_comm]; exact e20     -- (0,2): seg a v ∩ seg b a = {a}
    · rw [Set.inter_comm]; exact e01     -- (1,0): seg v b ∩ seg a v = {v}
    · exact e12                          -- (1,2): seg v b ∩ seg b a = {b}
    · exact e20                          -- (2,0): seg b a ∩ seg a v = {a}
    · rw [Set.inter_comm]; exact e12     -- (2,1): seg b a ∩ seg v b = {b}

/-! ## Part 4: the ear-triangle interior parity (PROVED, all valid ray directions)

For an interior ear point and a ray direction valid on the ear triangle (not parallel to
any of its three sides), the ear-triangle directed-edge `segCross` sum is *odd*: it equals
`CrossingNumber'` of `earTri` (the directed-edge sum, with `segCross a b ≡ segCross b a` by
`segCross_add_rev_even`), which is `1` for an interior point by the PROVED triangle
interior count, transported to the direction `ρ.r` by the unconditional triangle
ray-independence.  This is the closed `n = 3` content underlying the residue's
faithfulness. -/

/-- `side` depends only on the direction vector, so `segCross` is direction-only:
`segCross (τ.r) x p q` for a `RayDirection earTri` agrees with `segCross ρ.r x p q` when
`τ.r = ρ.r`.  (Definitional; recorded for clarity.) -/
lemma earTriSegSum_eq_crossingNumber' {a v b : Pt} (hO : orient a v b ≠ 0)
    (τ : RayDirection (earTri hO)) {x : Pt} :
    CrossingNumber' (earTri hO) τ x =
      segCross τ.r x a v + segCross τ.r x v b + segCross τ.r x b a := by
  rw [crossingNumber'_eq_sum_segCross]
  obtain ⟨hn0, hn1, hn2⟩ := cyclicNext_three
  rw [show (Finset.univ : Finset (Fin 3)) = {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}
        from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    hn0, hn1, hn2]
  simp only [earTri, earTriTuple_zero, earTriTuple_one, earTriTuple_two]
  ring

/-- **Ear-triangle interior parity, all valid directions.**  For a nondegenerate ear, an
interior ear point `x` (positive weights, off the ear-triangle boundary), and a ray
direction `r` valid on `earTri` and with nonzero side coordinates at the three vertices,
`Odd (segCross r x a v + segCross r x v b + segCross r x a b)`. -/
theorem earTriSegSum_odd_of_valid {a v b : Pt} (hO : orient a v b ≠ 0)
    (τ : RayDirection (earTri hO)) {x : Pt} {w0 w1 w2 : ℝ}
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • a + w1 • v + w2 • b)
    (hsa : side τ.r x a ≠ 0) (hsv : side τ.r x v ≠ 0) (hsb : side τ.r x b ≠ 0) :
    Odd (segCross τ.r x a v + segCross τ.r x v b + segCross τ.r x a b) := by
  -- the ear triangle's interior crossing number is 1 (PROVED), hence odd.
  have hxq : x = w0 • (earTri hO).q ⟨0, by omega⟩ + w1 • (earTri hO).q ⟨1, by omega⟩
      + w2 • (earTri hO).q ⟨2, by omega⟩ := by
    simp only [earTri, earTriTuple_zero, earTriTuple_one, earTriTuple_two]; exact hx
  have hs0 : side τ.r x ((earTri hO).q ⟨0, by omega⟩) ≠ 0 := by
    simp only [earTri, earTriTuple_zero]; exact hsa
  have hs1 : side τ.r x ((earTri hO).q ⟨1, by omega⟩) ≠ 0 := by
    simp only [earTri, earTriTuple_one]; exact hsv
  have hs2 : side τ.r x ((earTri hO).q ⟨2, by omega⟩) ≠ 0 := by
    simp only [earTri, earTriTuple_two]; exact hsb
  have hone := crossingNumber'_interior_eq_one (earTri hO) τ hw0 hw1 hw2 hsum hxq hs0 hs1 hs2
  rw [earTriSegSum_eq_crossingNumber'] at hone
  -- segCross a b ≡ segCross b a (mod 2), so the (a b) and (b a) sums have equal parity.
  have hev := segCross_add_rev_even τ.r x a b
  rw [Nat.odd_iff]
  rw [Nat.even_iff] at hev
  omega

/-! ## Part 5: discharging `earExteriorEven`, faithfulness, non-vacuity, and the headline

`InteriorEarParityMatch` discharges `earExteriorEven` for **every** ray by pure split
algebra (Part 3); it is faithful — a consequence of `IsConvexVertex'` (interior region ⟹
odd crossing) together with the ear-triangle interior parity (Part 4); and from it the
full `EarInductionInput` is constructible, making `polygonGeomResidue_of_earInput`
input-free in the even field and the Chapter-36 `⌊n/3⌋` headline conditional on exactly
this one geometric residue + the remaining cut data + `M`. -/

open ProofsInTheBook.PolygonGeomInput (region_ray_independent)

/-- **The residue discharges `earExteriorEven`, for every ray** (no side / non-degeneracy
hypotheses).  Pure consequence of the unconditional split `crossingNumber'_split_ear`: the
field's parity is `CrossingNumber' P ρ x + earTriSegSum`, and the residue forces these two
to match. -/
theorem earExteriorEven_of_parityMatch
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (H : InteriorEarParityMatch ear)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (hm : 4 ≤ m) {x : Pt}
    {w0 w1 w2 : ℝ} (hoff : ¬ OnBoundary P x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev (ear P)) + w1 • P.q (ear P)
      + w2 • P.q (cyclicNext (ear P))) :
    Even (segCross ρ.r x (P.q (cyclicPrev (ear P))) (P.q (cyclicNext (ear P)))
      + restSum P ρ x (ear P)) := by
  set i := ear P with hi
  have hsplit := crossingNumber'_split_ear P ρ x hm i
  have hmatch : CrossingNumber' P ρ x % 2 = earTriSegSum P ρ x i % 2 :=
    H P ρ hm hoff hw0 hw1 hw2 hsum hx
  rw [Nat.even_iff]
  unfold earTriSegSum at hmatch
  -- hsplit : CN = av + vb + rest ; hmatch : CN % 2 = (av + vb + ab) % 2.
  -- goal : (ab + rest) % 2 = 0.
  omega

/-- **Faithfulness.**  `InteriorEarParityMatch` at a chosen vertex `c` is a *consequence* of
`IsConvexVertex'` (at `c`, for every polygon `4 ≤ m`, with the nondegenerate ear
orientation and a per-call vertex-avoiding ray): an off-boundary interior ear point in the
region has odd crossing number, and the ear-triangle interior parity (Part 4) makes the
ear-triangle sum odd too — so the two parities match.  No strengthening. -/
theorem parityMatch_of_convex
    {m : ℕ} (P : StrictSimplePolygon m) (σ : RayDirection P) (_hm : 4 ≤ m) (c : Fin m)
    (hconv : IsConvexVertex' P σ c)
    (hO : orient (P.q (cyclicPrev c)) (P.q c) (P.q (cyclicNext c)) ≠ 0)
    {x : Pt} {w0 w1 w2 : ℝ} (hoff : ¬ OnBoundary P x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev c) + w1 • P.q c + w2 • P.q (cyclicNext c))
    (hsa : side σ.r x (P.q (cyclicPrev c)) ≠ 0)
    (hsv : side σ.r x (P.q c) ≠ 0)
    (hsb : side σ.r x (P.q (cyclicNext c)) ≠ 0) :
    CrossingNumber' P σ x % 2 = earTriSegSum P σ x c % 2 := by
  -- x in region ⟹ odd CN.
  have hmem : x ∈ closedTri (P.q (cyclicPrev c)) (P.q c) (P.q (cyclicNext c)) :=
    mem_closedTri_of_weights hw0.le hw1.le hw2.le hsum hx
  have hreg : ClosedRegion' P σ x := hconv hmem
  have hCNodd : Odd (CrossingNumber' P σ x) := by
    rcases hreg with hb | ho
    · exact absurd hb hoff
    · exact ho
  -- ear-triangle directed sum is odd via the bare-triple seed (avoids building earTri).
  have hseed : segCross σ.r x (P.q (cyclicPrev c)) (P.q c)
      + segCross σ.r x (P.q c) (P.q (cyclicNext c))
      + segCross σ.r x (P.q (cyclicNext c)) (P.q (cyclicPrev c)) = 1 :=
    triangle_segCross_sum_eq_one hw0 hw1 hw2 hsum hx hO hsa hsv hsb
  have hsymm : segCross σ.r x (P.q (cyclicPrev c)) (P.q (cyclicNext c))
      = segCross σ.r x (P.q (cyclicNext c)) (P.q (cyclicPrev c)) :=
    segCross_symm hsa hsb
  rw [Nat.odd_iff] at hCNodd
  unfold earTriSegSum
  omega

/-- **The full `EarInductionInput` from the parity-match residue** (+ the standard
combinatorial data the existing bundle already carries).  The genuine Jordan field
`earExteriorEven` is now *supplied by `earExteriorEven_of_parityMatch`* (the residue), not
assumed; the orientation, the ear-base diagonal, and the `n = 3` base are the same
combinatorial inputs the development already isolates. -/
def earInductionInput_of_parityMatch
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (H : InteriorEarParityMatch ear)
    (orient_ne : ∀ {m : ℕ} (P : StrictSimplePolygon m), 4 ≤ m →
      orient (P.q (cyclicPrev (ear P))) (P.q (ear P)) (P.q (cyclicNext (ear P))) ≠ 0)
    (diag : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), 4 ≤ m →
      IsDiagonal' P ρ (cyclicPrev (ear P)) (cyclicNext (ear P)))
    (base : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), m = 3 →
      IsConvexVertex' P ρ (ear P)) :
    EarInductionInput where
  ear := ear
  earExteriorEven := by
    intro m P ρ hm x w0 w1 w2 hoff hw0 hw1 hw2 hsum hx
    exact earExteriorEven_of_parityMatch ear H P ρ hm hoff hw0 hw1 hw2 hsum hx
  earOrient := fun P hm => orient_ne P hm
  earDiagonal := fun P ρ hm => diag P ρ hm
  earBase := fun P ρ h3 => base P ρ h3

/-- **`IsConvexVertex'` for all `m`, from the parity-match residue** (the headline of the
ear induction): the residue discharges the genuine Jordan field, so
`PolygonJordan.isConvexVertex'_all` becomes unconditional in the even-parity input. -/
theorem isConvexVertex'_all_of_parityMatch
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (H : InteriorEarParityMatch ear)
    (orient_ne : ∀ {m : ℕ} (P : StrictSimplePolygon m), 4 ≤ m →
      orient (P.q (cyclicPrev (ear P))) (P.q (ear P)) (P.q (cyclicNext (ear P))) ≠ 0)
    (diag : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), 4 ≤ m →
      IsDiagonal' P ρ (cyclicPrev (ear P)) (cyclicNext (ear P)))
    (base : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), m = 3 →
      IsConvexVertex' P ρ (ear P))
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) :
    IsConvexVertex' P ρ (ear P) :=
  isConvexVertex'_all (earInductionInput_of_parityMatch ear H orient_ne diag base) P ρ

/-- **Chapter-36 art-gallery `⌊n/3⌋` headline over exactly the parity-match residue + the
remaining cut data + `M`.**  Composing the residue-built `EarInductionInput` with
`PolygonJordan.artGallery_strict_of_earInput`: every strict simple polygon with a ray
admits `≤ ⌊n/3⌋` vertex guards seeing its whole closed region, with the convex-vertex
containment `IsConvexVertex'` now PROVED from the ear induction, leaving as inputs exactly
the single geometric residue `InteriorEarParityMatch` (+ the standard combinatorial
orientation / diagonal / base data), the remaining cut data, and `M`. -/
theorem artGallery_strict_of_parityMatch {n : ℕ}
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (H : InteriorEarParityMatch ear)
    (orient_ne : ∀ {m : ℕ} (P : StrictSimplePolygon m), 4 ≤ m →
      orient (P.q (cyclicPrev (ear P))) (P.q (ear P)) (P.q (cyclicNext (ear P))) ≠ 0)
    (diag : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), 4 ≤ m →
      IsDiagonal' P ρ (cyclicPrev (ear P)) (cyclicNext (ear P)))
    (base : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), m = 3 →
      IsConvexVertex' P ρ (ear P))
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RemainingResidualData P ρ ((earInductionInput_of_parityMatch ear H orient_ne diag base).ear P))
    (M : ProofsInTheBook.PolygonLast.DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms
          ProofsInTheBook.PolygonTriangleConvex.triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, ProofsInTheBook.PolygonRayIndep.Sees P ρ (P.q v) x :=
  artGallery_strict_of_earInput
    (earInductionInput_of_parityMatch ear H orient_ne diag base) rest M P ρ

/-- **Anti-vacuity check.**  The constructed `EarInductionInput` carries the chosen ear
vertex verbatim (the bundle is not a constant-`True` placeholder). -/
theorem earInductionInput_of_parityMatch_ear
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (H : InteriorEarParityMatch ear)
    (orient_ne : ∀ {m : ℕ} (P : StrictSimplePolygon m), 4 ≤ m →
      orient (P.q (cyclicPrev (ear P))) (P.q (ear P)) (P.q (cyclicNext (ear P))) ≠ 0)
    (diag : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), 4 ≤ m →
      IsDiagonal' P ρ (cyclicPrev (ear P)) (cyclicNext (ear P)))
    (base : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), m = 3 →
      IsConvexVertex' P ρ (ear P))
    {m : ℕ} (P : StrictSimplePolygon m) :
    (earInductionInput_of_parityMatch ear H orient_ne diag base).ear P = ear P := rfl

end

end ProofsInTheBook.PolygonEarExterior
