import ProofsInTheBook.PolygonVertexSweep

/-!
# Chapter 36 — Side-coordinate crossing convention (the tangent repair)

`PolygonVertexSweep` proved that the original *edge-parameter* half-open crossing
convention (`0 ≤ u < 1`) makes the vertex-sweep residue `VertexSweepNeutral`
**false** in general: an opposite-side forward vertex sweep flips the parity
(the unit-square counterexample, `ρ.r = (1, 3/10)`, vertical segment `X = -1`).

This file installs the **side-coordinate half-open convention** (`CH36_TANGENT_REPAIR`),
the ruled repair under which *all* vertex events are parity-neutral **by
construction**, so local constancy along boundary-free segments is
**unconditional** — the `NoTangentialVertexSweep` hypothesis disappears.

## The convention

For a base point `x` and a vertex `v`, the signed side coordinate is

```
side ρ x v := det2 ρ.r (v - x)
```

(`v` is on the ray line `x + ℝ•ρ.r` iff `side ρ x v = 0`).  An edge `i` from
`a = P.q i` to `b = P.q (cyclicNext i)` is *span-crossed* when its two endpoints
straddle the ray line with the nonpositive side included and the positive side
excluded:

```
Span (side ρ x a) (side ρ x b)
  := (side ρ x a ≤ 0 ∧ 0 < side ρ x b) ∨ (side ρ x b ≤ 0 ∧ 0 < side ρ x a)
```

and it is *crossed forward* when additionally the (unique, Cramer) ray parameter
`crossTau P ρ x i` is nonnegative.  This is the classical scanline rule: endpoint
inclusion is chosen by the *side of the ray line*, not by the edge's local
parameterization.

## Why vertex events become neutral

At a swept vertex `v = P.q k` with incident edges `(prev k, k)`, the two side
values across `v` are the *same* number `s := side ρ x v`, and the far endpoints
have side values `a := side ρ x (P.q (cyclicPrev k))`, `b := side ρ x (P.q (cyclicNext k))`.
The single algebraic identity

```
Xor (Span a s) (Span s b) ↔ Span a b    (a ≠ 0, b ≠ 0)
```

(`span_xor_through_vertex`) shows the *combined* span contribution of the two
incident edges is independent of `s`, even as `s` changes sign through `0`.  The
non-parallel ray (`RayDirection`) keeps `a, b ≠ 0`, so this is exactly the
one-strict-one-weak handover that neutralizes the event — no same-side /
opposite-side distinction survives.

## Reuse

The Cramer/affine layer of `PolygonLocalConstancy` survives verbatim: `crossTau`
(the ray parameter), `crossDen`, `cross_eq`, `cross_unique`, the affineness
(`crossTau_lineMap`), continuity, and the boundary lemmas.  Only the crossing
*predicate* changes (`Span` of side coordinates in place of `0 ≤ u < 1`), and the
`side` coordinate is itself affine in `x`.
-/

namespace ProofsInTheBook.PolygonSideCrossing

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonParity
open ProofsInTheBook.PolygonConvexVertex
open ProofsInTheBook.PolygonResidues
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonVertexSweep
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Layer 1: the side coordinate and the span predicate

The side coordinate depends only on the ray *vector* `r`, so we phrase it on a
bare `r : Pt`; the polygon-tied form is `side ρ.r x v`. -/

/-- Signed side coordinate of a vertex `v` relative to the ray line `x + ℝ•r`:
`det2 r (v - x)`.  `v` is on the ray line iff this vanishes. -/
def side (r x v : Pt) : ℝ :=
  det2 r (v - x)

/-- The classical half-open span predicate on two side coordinates: the two
endpoints straddle the ray line with the nonpositive side *included* and the
positive side *excluded*. -/
def Span (a b : ℝ) : Prop :=
  (a ≤ 0 ∧ 0 < b) ∨ (b ≤ 0 ∧ 0 < a)

instance (a b : ℝ) : Decidable (Span a b) := by
  unfold Span; infer_instance

/-! ### The algebraic span truth table (Layer 3 of the ruling)

These are the whole vertex-event repair: at a swept vertex with side value `s`
(possibly `0`), the combined span contribution of the two incident edges is
independent of `s`. -/

lemma span_false_same_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) : ¬ Span a b := by
  rintro (⟨_, hb'⟩ | ⟨_, ha'⟩)
  · linarith
  · linarith

lemma span_false_same_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : ¬ Span a b := by
  rintro (⟨ha', _⟩ | ⟨hb', _⟩)
  · linarith
  · linarith

lemma span_true_neg_pos {a b : ℝ} (ha : a ≤ 0) (hb : 0 < b) : Span a b :=
  Or.inl ⟨ha, hb⟩

lemma span_true_pos_neg {a b : ℝ} (ha : 0 < a) (hb : b ≤ 0) : Span a b :=
  Or.inr ⟨hb, ha⟩

/-- Resolve `Span a b` to a boolean from the strict signs of `a` and a sign datum
on `b` (one weak, one strict).  Helper for the truth table. -/
lemma span_decide {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Span a b ↔ (a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0)) := by
  rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
  · constructor
    · intro h; exact absurd h (span_false_same_nonpos ha'.le hb'.le)
    · rintro (⟨_, h⟩ | ⟨h, _⟩) <;> linarith
  · exact ⟨fun _ => Or.inl ⟨ha', hb'⟩, fun _ => span_true_neg_pos ha'.le hb'⟩
  · exact ⟨fun _ => Or.inr ⟨ha', hb'⟩, fun _ => span_true_pos_neg ha' hb'.le⟩
  · constructor
    · intro h; exact absurd h (span_false_same_pos ha' hb')
    · rintro (⟨h, _⟩ | ⟨_, h⟩) <;> linarith

/-- `Span a b` is determined by the strict signs of `a` and `b` (both nonzero):
it holds iff they have opposite signs. -/
lemma span_iff_opp_sign {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Span a b ↔ a * b < 0 := by
  rw [span_decide ha hb]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact mul_neg_of_neg_of_pos h1 h2
    · exact mul_neg_of_pos_of_neg h1 h2
  · intro h
    rcases lt_or_gt_of_ne ha with ha' | ha'
    · have hb' : 0 < b := by nlinarith
      exact Or.inl ⟨ha', hb'⟩
    · have hb' : b < 0 := by nlinarith
      exact Or.inr ⟨ha', hb'⟩

/-- **Span truth table.**  With `a ≠ 0` and `b ≠ 0`, the parity-sum of the two
incident-edge span contributions across a swept vertex (side value `s`, any sign)
equals the single span `Span a b`, independent of `s`.  This is the algebraic
heart of the tangent repair: vertex events are parity-neutral by construction. -/
lemma span_mod_two_through_vertex {a b s : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ((if Span a s then 1 else 0) + (if Span s b then 1 else 0)) % 2
      = (if Span a b then 1 else 0) := by
  classical
  -- Resolve each span to a boolean from the strict signs of `a`, `b` and the
  -- trichotomy of `s`; the final ℕ arithmetic is then `rfl`.
  rcases lt_or_gt_of_ne ha with ha' | ha' <;>
    rcases lt_or_gt_of_ne hb with hb' | hb' <;>
      rcases lt_trichotomy s 0 with hs | hs | hs
  -- Stage 1: resolve `Span a s`.
  all_goals
    first
      | rw [if_pos (show Span a s by
            first
              | exact span_true_neg_pos ha'.le hs
              | exact span_true_pos_neg ha' hs.le
              | exact span_true_neg_pos ha'.le (by linarith)
              | exact span_true_pos_neg ha' (by linarith))]
      | rw [if_neg (show ¬ Span a s by
            first
              | exact span_false_same_nonpos ha'.le hs.le
              | exact span_false_same_pos ha' hs
              | exact span_false_same_nonpos ha'.le (by linarith)
              | exact span_false_same_pos ha' (by linarith))]
  -- Stage 2: resolve `Span s b`.
  all_goals
    first
      | rw [if_pos (show Span s b by
            first
              | exact span_true_neg_pos hs.le hb'
              | exact span_true_pos_neg hs hb'.le
              | exact span_true_neg_pos (by linarith) hb'
              | exact span_true_pos_neg (by linarith) hb'.le)]
      | rw [if_neg (show ¬ Span s b by
            first
              | exact span_false_same_nonpos hs.le hb'.le
              | exact span_false_same_pos hs hb'
              | exact span_false_same_nonpos (by linarith) hb'.le
              | exact span_false_same_pos (by linarith) hb')]
  -- Stage 3: resolve `Span a b`.
  all_goals
    first
      | rw [if_pos (show Span a b by
            first
              | exact span_true_neg_pos ha'.le hb'
              | exact span_true_pos_neg ha' hb'.le)]
      | rw [if_neg (show ¬ Span a b by
            first
              | exact span_false_same_nonpos ha'.le hb'.le
              | exact span_false_same_pos ha' hb')]
  all_goals rfl

/-! ## Layer 2: the side-coordinate crossing predicate and the new region

`side` is affine in `x`; the difference of the two endpoint side values of an
edge is the Cramer denominator `crossDen`, which is nonzero (non-parallel ray).
The forward condition reuses the existing ray parameter `crossTau`. -/

/-- `side ρ.r x (P.q i)` in terms of the existing `crossU` numerator:
`side ρ.r x (P.q i) = - det2 ρ.r (x - P.q i)`. -/
lemma side_eq_neg_det2 (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (i : Fin n) :
    side ρ.r x (P.q i) = - det2 ρ.r (x - P.q i) := by
  unfold side det2
  simp only [PiLp.sub_apply]
  ring

/-- **Side difference is the Cramer denominator.**  The two endpoint side values
of edge `i` differ by `crossDen P ρ i`, which is nonzero. -/
lemma side_next_sub_side (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (i : Fin n) :
    side ρ.r x (P.q (cyclicNext i)) - side ρ.r x (P.q i) = crossDen P ρ i := by
  unfold side crossDen
  rw [← det2_sub_right]
  congr 1
  abel

/-- **No edge has both endpoints on the ray line.**  If both endpoint side values
of edge `i` vanish, the edge is parallel to `ρ.r`, contradicting `RayDirection`. -/
lemma no_adjacent_vertices_both_on_rayLine (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (x : Pt) (i : Fin n)
    (h0 : side ρ.r x (P.q i) = 0)
    (h1 : side ρ.r x (P.q (cyclicNext i)) = 0) : False := by
  have hd := side_next_sub_side P ρ x i
  rw [h0, h1, sub_zero] at hd
  exact crossDen_ne_zero P ρ i hd.symm

/-- The span-crossing predicate for edge `i`: the two endpoints straddle the ray
line (side-coordinate half-open rule). -/
def SpanCrossesSide (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (i : Fin n) : Prop :=
  Span (side ρ.r x (P.q i)) (side ρ.r x (P.q (cyclicNext i)))

instance (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) (i : Fin n) :
    Decidable (SpanCrossesSide P ρ x i) := by
  unfold SpanCrossesSide; infer_instance

/-- **The new (side-coordinate) edge crossing.**  Edge `i` is crossed by the
forward ray from `x` when its endpoints span the ray line and the (Cramer) ray
parameter is nonnegative.  Unlike `EdgeCrossesRay`, there is *no* `x ∉ Edge i`
guard: a boundary point is handled separately by `ClosedRegion'`. -/
def EdgeCrossesRay' (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (i : Fin n) : Prop :=
  SpanCrossesSide P ρ x i ∧ 0 ≤ crossTau P ρ x i

instance (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) (i : Fin n) :
    Decidable (EdgeCrossesRay' P ρ x i) := by
  unfold EdgeCrossesRay'; infer_instance

/-- The finite set of edges span-crossed by the forward ray. -/
def CrossingEdges' (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => EdgeCrossesRay' P ρ x i

/-- The side-coordinate crossing number. -/
def CrossingNumber' (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) :
    ℕ :=
  (CrossingEdges' P ρ x).card

/-- Closed polygonal region under the corrected convention. -/
def ClosedRegion' (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) :
    Prop :=
  OnBoundary P x ∨ Odd (CrossingNumber' P ρ x)

lemma mem_crossingEdges'_iff (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (i : Fin n) :
    i ∈ CrossingEdges' P ρ x ↔ EdgeCrossesRay' P ρ x i := by
  classical
  unfold CrossingEdges'
  simp [Finset.mem_filter]

lemma crossingNumber'_eq_card (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) :
    CrossingNumber' P ρ x = (CrossingEdges' P ρ x).card := rfl

/-! ## Layer 2': affineness of `side` along a segment

`side r (lineMap x y t) v` is affine in `t`, hence continuous; this is what makes
each edge's span status locally constant away from the zeros of the side
functions. -/

/-- `side r (lineMap x y t) v` is affine in `t`. -/
lemma side_lineMap (r x y v : Pt) (t : ℝ) :
    side r (AffineMap.lineMap x y t) v =
      (1 - t) * side r x v + t * side r y v := by
  unfold side
  have hsub : v - AffineMap.lineMap x y t =
      AffineMap.lineMap (v - x) (v - y) t := by
    rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    ext k; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  rw [hsub, AffineMap.lineMap_apply_module, det2_add_right, det2_smul_right,
    det2_smul_right]

/-- `t ↦ side r (lineMap x y t) v` as a function. -/
def sideOf (r x y v : Pt) : ℝ → ℝ :=
  fun t => side r (AffineMap.lineMap x y t) v

lemma sideOf_eq (r x y v : Pt) (t : ℝ) :
    sideOf r x y v t = (1 - t) * side r x v + t * side r y v :=
  side_lineMap r x y v t

lemma continuous_sideOf (r x y v : Pt) : Continuous (sideOf r x y v) := by
  have : sideOf r x y v =
      fun t => (1 - t) * side r x v + t * side r y v := by
    funext t; exact sideOf_eq r x y v t
  rw [this]; fun_prop

/-! ## Kernel sanity: the square counterexample is FIXED

`PolygonVertexSweep`'s docstring exhibits the parity break of the *old*
convention: square `{(0,0),(4,0),(4,4),(0,4)}`, ray `ρ.r = (1, 3/10)`, vertical
boundary-free segment `X = -1`; at `t₀` the ray hits vertex `(0,4)` and the old
half-open count runs `2 / 1 / 0` (parity `0 / 1 / 0`) — NOT constant.

Under the side-coordinate convention the count is *constantly even*.  We verify
this with an exact rational kernel evaluator (`#eval`s below print `0` at all
three sample points: just-before, at, and just-after the event), independent of
the noncomputable `EuclideanSpace ℝ` machinery.

Setup (rational arithmetic, `side r x v = r.1*(v.2 - x.2) - r.2*(v.1 - x.1)`):
the square's four edges `A→B→C→D→A`, ray `r = (1, 3/10)`, base point on `X = -1`.
The forward ray parameter is positive for every span-crossed edge here (the
square lies to the *right* of the moving point), so the forward guard does not
remove any span crossing; the span count alone already exhibits the fix. -/

/-- Rational side coordinate `det2 r (v - x)` for the kernel check. -/
def qside (r x v : ℚ × ℚ) : ℚ :=
  r.1 * (v.2 - x.2) - r.2 * (v.1 - x.1)

/-- Rational `Span` (decidable on ℚ). -/
def qspan (a b : ℚ) : Bool :=
  (a ≤ 0 ∧ 0 < b) ∨ (b ≤ 0 ∧ 0 < a)

/-- Forward ray parameter `τ` for edge from `a` to `b`, base `x`, dir `r`,
via Cramer: `τ = det2 (a - x) (b - a) / det2 r (b - a)` (matches `crossTau`). -/
def qtau (r x a b : ℚ × ℚ) : ℚ :=
  let e := (b.1 - a.1, b.2 - a.2)
  let ax := (a.1 - x.1, a.2 - x.2)
  (ax.1 * e.2 - ax.2 * e.1) / (r.1 * e.2 - r.2 * e.1)

/-- Rational side-coordinate crossing count over the square's four edges. -/
def qCrossCount (r x : ℚ × ℚ) : ℕ :=
  let A : ℚ × ℚ := (0, 0)
  let B : ℚ × ℚ := (4, 0)
  let C : ℚ × ℚ := (4, 4)
  let D : ℚ × ℚ := (0, 4)
  let edges := [(A, B), (B, C), (C, D), (D, A)]
  (edges.filter (fun e =>
      qspan (qside r x e.1) (qside r x e.2) && (0 ≤ qtau r x e.1 e.2))).length

-- Ray direction and the three sample base points along the outside segment X = -1.
-- The event (ray through vertex D = (0,4)) is at y = 37/10.
-- side r x D = 1*(4 - y) - 3/10*(0 - (-1)) = 4 - y - 3/10 = 37/10 - y, which is
-- 0 exactly at y = 37/10.  Sample just-before (y = 36/10), at (37/10), after (38/10).
--
-- The raw counts (printed below) are 2 / 0 / 0:
#eval qCrossCount (1, 3/10) (-1, 36/10)         -- 2  (old convention: 2)
#eval qCrossCount (1, 3/10) (-1, 37/10)         -- 0  (old convention: 1  ← the break)
#eval qCrossCount (1, 3/10) (-1, 38/10)         -- 0  (old convention: 0)
--
-- The PARITIES (printed below) are 0 / 0 / 0 — CONSTANT even.  Under the old
-- edge-parameter convention they were 0 / 1 / 0, breaking at the event.  The
-- side-coordinate convention removes the `1` at the event (the vertex hit now
-- contributes 0, not 1), so the phantom boundary is gone.
#eval qCrossCount (1, 3/10) (-1, 36/10) % 2     -- 0
#eval qCrossCount (1, 3/10) (-1, 37/10) % 2     -- 0  ← was 1 under old convention
#eval qCrossCount (1, 3/10) (-1, 38/10) % 2     -- 0

/-- An integer-arithmetic mirror of `qCrossCount` so the kernel fact is provable
by `decide` (clears the `3/10` denominator: scale `r` by `10` to `(10, 3)` and
multiply each base coordinate by the common denominator, leaving every `side`,
`τ`-numerator and `τ`-denominator an *integer*; signs — hence `Span` and the
forward guard — are unchanged by the positive scaling).  Base points are scaled
by 10: `(-10, 36)`, `(-10, 37)`, `(-10, 38)`; square vertices by 10. -/
def zside (r x v : ℤ × ℤ) : ℤ :=
  r.1 * (v.2 - x.2) - r.2 * (v.1 - x.1)

def zspan (a b : ℤ) : Bool :=
  (a ≤ 0 ∧ 0 < b) ∨ (b ≤ 0 ∧ 0 < a)

/-- Sign of the forward ray parameter: `τ ≥ 0` iff `num` and `den` have the same
sign (or `num = 0`).  We test `0 ≤ num * den` (den ≠ 0 here). -/
def ztauNonneg (r x a b : ℤ × ℤ) : Bool :=
  let e := (b.1 - a.1, b.2 - a.2)
  let ax := (a.1 - x.1, a.2 - x.2)
  let num := ax.1 * e.2 - ax.2 * e.1
  let den := r.1 * e.2 - r.2 * e.1
  0 ≤ num * den

def zCrossCount (r x : ℤ × ℤ) : ℕ :=
  let A : ℤ × ℤ := (0, 0)
  let B : ℤ × ℤ := (40, 0)
  let C : ℤ × ℤ := (40, 40)
  let D : ℤ × ℤ := (0, 40)
  let edges := [(A, B), (B, C), (C, D), (D, A)]
  (edges.filter (fun e =>
      zspan (zside r x e.1) (zside r x e.2) && ztauNonneg r x e.1 e.2)).length

/-- **Kernel sanity, machine-checked (`decide`).**  Across the vertex event the
side-coordinate crossing parity is constantly even — the square counterexample of
`PolygonVertexSweep` is fixed. -/
example :
    zCrossCount (10, 3) (-10, 36) % 2 = 0 ∧
    zCrossCount (10, 3) (-10, 37) % 2 = 0 ∧
    zCrossCount (10, 3) (-10, 38) % 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## Layer 5: per-edge status and the no-event local constancy

The status of edge `i` along the segment is span-crossing plus the forward guard.
We abbreviate the two side functions and the status as functions of `t`, all
continuous (affine).  Away from a side zero and away from a forward-guard zero,
the status is locally constant; and a forward-guard zero *with* span crossing
forces a boundary point. -/

/-- The side coordinate of edge `i`'s start vertex along the segment. -/
def s0Of (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt) (i : Fin n) :
    ℝ → ℝ :=
  sideOf ρ.r x y (P.q i)

/-- The side coordinate of edge `i`'s end vertex along the segment. -/
def s1Of (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt) (i : Fin n) :
    ℝ → ℝ :=
  sideOf ρ.r x y (P.q (cyclicNext i))

/-- The status of edge `i` along the segment (span crossing + forward). -/
def statusOf' (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) : ℝ → Prop :=
  fun t => EdgeCrossesRay' P ρ (AffineMap.lineMap x y t) i

lemma s0Of_eq (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) (t : ℝ) :
    s0Of P ρ x y i t = side ρ.r (AffineMap.lineMap x y t) (P.q i) := rfl

lemma s1Of_eq (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) (t : ℝ) :
    s1Of P ρ x y i t = side ρ.r (AffineMap.lineMap x y t) (P.q (cyclicNext i)) := rfl

lemma continuous_s0Of (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) : Continuous (s0Of P ρ x y i) :=
  continuous_sideOf ρ.r x y (P.q i)

lemma continuous_s1Of (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) : Continuous (s1Of P ρ x y i) :=
  continuous_sideOf ρ.r x y (P.q (cyclicNext i))

/-- Status of edge `i` at parameter `t`, as the span+forward conjunction in terms
of the side/tau functions. -/
lemma statusOf'_iff (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x y : Pt) (i : Fin n) (t : ℝ) :
    statusOf' P ρ x y i t ↔
      Span (s0Of P ρ x y i t) (s1Of P ρ x y i t) ∧
        0 ≤ tauOf P ρ x y i t := by
  unfold statusOf' EdgeCrossesRay' SpanCrossesSide s0Of s1Of sideOf tauOf
  rfl

/-- **The forward-guard zero is a boundary point.**  If `crossTau P ρ z i = 0`
and edge `i` span-crosses (so the ray line meets the edge's side span), then `z`
lies on the closed edge `Edge i`, hence on the boundary.  This is the
side-coordinate analogue of `crossTau_eq_zero_imp_onEdge`. -/
lemma crossTau_eq_zero_span_imp_onEdge (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (z : Pt) (i : Fin n)
    (hτ : crossTau P ρ z i = 0)
    (hspan : SpanCrossesSide P ρ z i) :
    z ∈ Edge P.q i := by
  -- At τ = 0 the reconstructed crossing point is z itself: z = lineMap a b (crossU).
  have hce := cross_eq P ρ z i
  rw [hτ, zero_smul, add_zero] at hce
  -- Span on the side coordinates forces crossU ∈ [0,1]; then z ∈ seg a b.
  -- side z a = -det2 r (z - a) = -(crossU * D)  (from crossU = det2 r (z-a)/D).
  -- Use: crossU = det2 r (z - q_i)/D, and side z q_i = -det2 r (z - q_i).
  rw [Edge, seg, segment_eq_image_lineMap]
  refine ⟨crossU P ρ z i, ?_, hce.symm⟩
  -- Show 0 ≤ crossU ≤ 1 from the span.  side z a = -(crossU)*D, side z b = (1-crossU)*D.
  set D := crossDen P ρ i with hD
  have hDne : D ≠ 0 := crossDen_ne_zero P ρ i
  have hsa : side ρ.r z (P.q i) = - (crossU P ρ z i * D) := by
    rw [side_eq_neg_det2, crossU, ← hD]
    rw [div_mul_cancel₀ _ hDne]
  have hsb : side ρ.r z (P.q (cyclicNext i)) = (1 - crossU P ρ z i) * D := by
    have hdiff := side_next_sub_side P ρ z i
    rw [hsa, ← hD] at hdiff
    linarith [hdiff]
  -- Span (sa) (sb): straddling, so crossU ∈ [0,1].
  unfold SpanCrossesSide Span at hspan
  rw [hsa, hsb] at hspan
  set u := crossU P ρ z i with hu
  -- Cases on sign of D and the span disjunction.
  rcases lt_or_gt_of_ne hDne with hDneg | hDpos
  · rcases hspan with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- -(u*D) ≤ 0 ∧ 0 < (1-u)*D ; D<0 ⇒ u ≤ 0?  resolve to u ∈ [0,1].
      constructor
      · nlinarith
      · nlinarith
    · constructor
      · nlinarith
      · nlinarith
  · rcases hspan with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor
      · nlinarith
      · nlinarith
    · constructor
      · nlinarith
      · nlinarith

/-! ## Layer 6: no-event per-edge local constancy

Away from a side zero (both endpoint side functions nonzero at `t₀`), the span
status is locally constant; combined with the forward-guard handling (a
`crossTau = 0` span crossing is a boundary point), the full edge status is
eventually constant. -/

open Classical in
/-- Boolean count of the side-coordinate status. -/
noncomputable def fcount' (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x y : Pt) (i : Fin n) (t : ℝ) : ℕ :=
  if statusOf' P ρ x y i t then 1 else 0

open Classical in
lemma fcount'_eq (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) (t : ℝ) :
    fcount' P ρ x y i t = if statusOf' P ρ x y i t then 1 else 0 := rfl

/-- Span on two side functions is locally constant at `t₀` when both side
functions are nonzero at `t₀` (each keeps its strict sign nearby). -/
lemma span_eventually_const_of_sides_ne (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (x y : Pt) (i : Fin n) {t₀ : ℝ}
    (h0 : s0Of P ρ x y i t₀ ≠ 0) (h1 : s1Of P ρ x y i t₀ ≠ 0) :
    ∀ᶠ t in nhds t₀,
      (Span (s0Of P ρ x y i t) (s1Of P ρ x y i t)
        ↔ Span (s0Of P ρ x y i t₀) (s1Of P ρ x y i t₀)) := by
  have hc0 := continuous_s0Of P ρ x y i
  have hc1 := continuous_s1Of P ρ x y i
  -- s0, s1 keep their strict signs near t₀.
  have ev0 : ∀ᶠ t in nhds t₀,
      (0 < s0Of P ρ x y i t ↔ 0 < s0Of P ρ x y i t₀) ∧
      (s0Of P ρ x y i t < 0 ↔ s0Of P ρ x y i t₀ < 0) := by
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · filter_upwards [(hc0.tendsto t₀).eventually_lt_const hneg] with t ht
      constructor
      · constructor <;> intro h <;> linarith
      · constructor <;> intro _ <;> [exact hneg; exact ht]
    · filter_upwards [(hc0.tendsto t₀).eventually_const_lt hpos] with t ht
      constructor
      · constructor <;> intro _ <;> [exact hpos; exact ht]
      · constructor <;> intro h <;> linarith
  have ev1 : ∀ᶠ t in nhds t₀,
      (0 < s1Of P ρ x y i t ↔ 0 < s1Of P ρ x y i t₀) ∧
      (s1Of P ρ x y i t < 0 ↔ s1Of P ρ x y i t₀ < 0) := by
    rcases lt_or_gt_of_ne h1 with hneg | hpos
    · filter_upwards [(hc1.tendsto t₀).eventually_lt_const hneg] with t ht
      constructor
      · constructor <;> intro h <;> linarith
      · constructor <;> intro _ <;> [exact hneg; exact ht]
    · filter_upwards [(hc1.tendsto t₀).eventually_const_lt hpos] with t ht
      constructor
      · constructor <;> intro _ <;> [exact hpos; exact ht]
      · constructor <;> intro h <;> linarith
  filter_upwards [ev0, ev1] with t ht0 ht1
  -- both spans are opposite-sign tests; sign agreement gives the iff.
  rw [span_iff_opp_sign (by
        rcases lt_or_gt_of_ne h0 with h | h
        · exact ne_of_lt (ht0.2.mpr h)
        · exact ne_of_gt (ht0.1.mpr h))
      (by
        rcases lt_or_gt_of_ne h1 with h | h
        · exact ne_of_lt (ht1.2.mpr h)
        · exact ne_of_gt (ht1.1.mpr h)),
     span_iff_opp_sign h0 h1]
  -- a*b<0 ↔ a₀*b₀<0 from matching strict signs
  constructor
  · intro h
    rcases lt_or_gt_of_ne h0 with h0' | h0' <;> rcases lt_or_gt_of_ne h1 with h1' | h1'
    · exfalso; nlinarith [ht0.2.mpr h0', ht1.2.mpr h1']
    · nlinarith [ht0.2.mpr h0', ht1.1.mpr h1']
    · nlinarith [ht0.1.mpr h0', ht1.2.mpr h1']
    · exfalso; nlinarith [ht0.1.mpr h0', ht1.1.mpr h1']
  · intro h
    rcases lt_or_gt_of_ne h0 with h0' | h0' <;> rcases lt_or_gt_of_ne h1 with h1' | h1'
    · exfalso; nlinarith
    · have := ht0.2.mpr h0'; have := ht1.1.mpr h1'; nlinarith
    · have := ht0.1.mpr h0'; have := ht1.2.mpr h1'; nlinarith
    · exfalso; nlinarith

/-- **No-event per-edge local constancy.**  At an interior parameter `t₀` where
*neither* endpoint side function of edge `i` vanishes, the side-coordinate status
of edge `i` is locally constant.  (The forward-guard threshold is handled by the
boundary-free hypothesis: a `tauOf = 0` span crossing is a boundary point.) -/
lemma statusOf'_eventually_eq_of_noEvent (P : StrictSimplePolygon n)
    (ρ : RayDirection P) {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    (i : Fin n) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h0 : s0Of P ρ x y i t₀ ≠ 0) (h1 : s1Of P ρ x y i t₀ ≠ 0) :
    ∀ᶠ t in nhds t₀, statusOf' P ρ x y i t = statusOf' P ρ x y i t₀ := by
  classical
  have hoffev := eventually_off_boundary P ρ hfree ht₀
  have hoff0 : ¬ OnBoundary P (AffineMap.lineMap x y t₀) :=
    hfree _ (by rw [openSegment_eq_image_lineMap]; exact ⟨t₀, ht₀, rfl⟩)
  have hspanev := span_eventually_const_of_sides_ne P ρ x y i h0 h1
  have hctau := continuous_tauOf P ρ x y i
  set spanT₀ := Span (s0Of P ρ x y i t₀) (s1Of P ρ x y i t₀) with hspanT₀
  by_cases hcross : statusOf' P ρ x y i t₀
  · -- status true at t₀: span holds and tauOf t₀ ≥ 0; in fact tauOf t₀ > 0
    -- (tauOf = 0 + span ⇒ boundary).
    obtain ⟨hspan0, hτ0⟩ := (statusOf'_iff P ρ x y i t₀).mp hcross
    have hτpos : 0 < tauOf P ρ x y i t₀ := by
      rcases lt_or_eq_of_le hτ0 with h | h
      · exact h
      · exfalso; apply hoff0
        exact ⟨i, crossTau_eq_zero_span_imp_onEdge P ρ _ i h.symm hspan0⟩
    have evτ : ∀ᶠ t in nhds t₀, 0 < tauOf P ρ x y i t := by
      filter_upwards [(hctau.tendsto t₀).eventually_const_lt hτpos] with t ht using ht
    filter_upwards [hoffev, hspanev, evτ] with t hofft hspant hτt
    rw [eq_iff_iff, statusOf'_iff]
    constructor
    · intro _; exact (statusOf'_iff P ρ x y i t₀).mp hcross
    · intro _; exact ⟨hspant.mpr hspan0, le_of_lt hτt⟩
  · -- status false at t₀.
    have hcross' : ¬ (Span (s0Of P ρ x y i t₀) (s1Of P ρ x y i t₀) ∧
        0 ≤ tauOf P ρ x y i t₀) := fun h => hcross ((statusOf'_iff P ρ x y i t₀).mpr h)
    -- either span fails at t₀, or tauOf t₀ < 0.
    by_cases hspan0 : Span (s0Of P ρ x y i t₀) (s1Of P ρ x y i t₀)
    · -- span holds, so tauOf t₀ < 0.
      have hτneg : tauOf P ρ x y i t₀ < 0 := by
        by_contra hge
        exact hcross' ⟨hspan0, not_lt.1 hge⟩
      have evτ : ∀ᶠ t in nhds t₀, tauOf P ρ x y i t < 0 := by
        filter_upwards [(hctau.tendsto t₀).eventually_lt_const hτneg] with t ht using ht
      filter_upwards [hoffev, hspanev, evτ] with t hofft hspant hτt
      rw [eq_iff_iff, statusOf'_iff]
      constructor
      · rintro ⟨_, hge⟩; linarith
      · intro h; exact absurd ((statusOf'_iff P ρ x y i t₀).mp h) hcross'
    · -- span fails at t₀, hence eventually (constancy).
      filter_upwards [hspanev] with t hspant
      rw [eq_iff_iff, statusOf'_iff]
      constructor
      · rintro ⟨hs, _⟩; exact absurd (hspant.mp hs) hspan0
      · intro h; exact absurd ((statusOf'_iff P ρ x y i t₀).mp h) hcross'

/-! ## Layer 7: vertex-event pairing (the parity-neutral handover)

At a vertex event `side z (P.q k) = 0`, the two incident edges `j := cyclicPrev k`
and `k` share the vertex `P.q k`.  In the side coordinate, `s1Of j = side z (P.q k)`
and `s0Of k = side z (P.q k)` coincide, and this is exactly the shared `s` of the
span truth table.  We bridge the side-zero condition to the existing edge-parameter
event (`crossU = 1` resp. `0`) so the Cramer pairing of `PolygonVertexSweep`
(`u_eq_zero_of_u_eq_one_next`, `crossTau_event_eq`) carries over. -/

/-- **Side-zero ↔ `crossU = 1` (end vertex).**  `side z (P.q (cyclicNext i)) = 0`
iff the edge parameter `crossU P ρ z i = 1`. -/
lemma side_next_zero_iff_crossU_one (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (i : Fin n) :
    side ρ.r z (P.q (cyclicNext i)) = 0 ↔ crossU P ρ z i = 1 := by
  set D := crossDen P ρ i with hD
  have hDne : D ≠ 0 := crossDen_ne_zero P ρ i
  -- side z (q_{i+1}) = (1 - crossU) * D  (from side_next_sub_side and side z q_i = -crossU*D).
  have hsa : side ρ.r z (P.q i) = - (crossU P ρ z i * D) := by
    rw [side_eq_neg_det2, crossU, ← hD, div_mul_cancel₀ _ hDne]
  have hsb : side ρ.r z (P.q (cyclicNext i)) = (1 - crossU P ρ z i) * D := by
    have hdiff := side_next_sub_side P ρ z i
    rw [hsa, ← hD] at hdiff; linarith [hdiff]
  rw [hsb]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · linarith
    · exact absurd h1 hDne
  · intro h; rw [h]; ring

/-- **Side-zero ↔ `crossU = 0` (start vertex).**  `side z (P.q i) = 0` iff the
edge parameter `crossU P ρ z i = 0`. -/
lemma side_start_zero_iff_crossU_zero (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (z : Pt) (i : Fin n) :
    side ρ.r z (P.q i) = 0 ↔ crossU P ρ z i = 0 := by
  set D := crossDen P ρ i with hD
  have hDne : D ≠ 0 := crossDen_ne_zero P ρ i
  have hsa : side ρ.r z (P.q i) = - (crossU P ρ z i * D) := by
    rw [side_eq_neg_det2, crossU, ← hD, div_mul_cancel₀ _ hDne]
  rw [hsa]
  constructor
  · intro h
    have : crossU P ρ z i * D = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact h1
    · exact absurd h1 hDne
  · intro h; rw [h]; ring

/-- **Generic span constancy.**  For two continuous real functions `f, g` that
are nonzero at `t₀`, `Span (f t) (g t)` is locally constant at `t₀` (each keeps a
strict sign, and `Span` of nonzeros depends only on the sign product). -/
lemma span_const_two_sides {f g : ℝ → ℝ} {t₀ : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf0 : f t₀ ≠ 0) (hg0 : g t₀ ≠ 0) :
    ∀ᶠ t in nhds t₀, (Span (f t) (g t) ↔ Span (f t₀) (g t₀)) := by
  have evf : ∀ᶠ t in nhds t₀,
      (0 < f t ↔ 0 < f t₀) ∧ (f t < 0 ↔ f t₀ < 0) := by
    rcases lt_or_gt_of_ne hf0 with h | h
    · filter_upwards [(hf.tendsto t₀).eventually_lt_const h] with t ht
      exact ⟨⟨fun hp => by linarith, fun hp => by linarith⟩,
        ⟨fun _ => h, fun _ => ht⟩⟩
    · filter_upwards [(hf.tendsto t₀).eventually_const_lt h] with t ht
      exact ⟨⟨fun _ => h, fun _ => ht⟩, ⟨fun hn => by linarith, fun hn => by linarith⟩⟩
  have evg : ∀ᶠ t in nhds t₀,
      (0 < g t ↔ 0 < g t₀) ∧ (g t < 0 ↔ g t₀ < 0) := by
    rcases lt_or_gt_of_ne hg0 with h | h
    · filter_upwards [(hg.tendsto t₀).eventually_lt_const h] with t ht
      exact ⟨⟨fun hp => by linarith, fun hp => by linarith⟩,
        ⟨fun _ => h, fun _ => ht⟩⟩
    · filter_upwards [(hg.tendsto t₀).eventually_const_lt h] with t ht
      exact ⟨⟨fun _ => h, fun _ => ht⟩, ⟨fun hn => by linarith, fun hn => by linarith⟩⟩
  filter_upwards [evf, evg] with t htf htg
  have hft : f t ≠ 0 := by
    rcases lt_or_gt_of_ne hf0 with h | h
    · exact ne_of_lt (htf.2.mpr h)
    · exact ne_of_gt (htf.1.mpr h)
  have hgt : g t ≠ 0 := by
    rcases lt_or_gt_of_ne hg0 with h | h
    · exact ne_of_lt (htg.2.mpr h)
    · exact ne_of_gt (htg.1.mpr h)
  rw [span_iff_opp_sign hft hgt, span_iff_opp_sign hf0 hg0]
  constructor
  · intro h
    rcases lt_or_gt_of_ne hf0 with hf' | hf' <;> rcases lt_or_gt_of_ne hg0 with hg' | hg'
    · exfalso; nlinarith [htf.2.mpr hf', htg.2.mpr hg']
    · nlinarith [htf.2.mpr hf', htg.1.mpr hg']
    · nlinarith [htf.1.mpr hf', htg.2.mpr hg']
    · exfalso; nlinarith [htf.1.mpr hf', htg.1.mpr hg']
  · intro h
    rcases lt_or_gt_of_ne hf0 with hf' | hf' <;> rcases lt_or_gt_of_ne hg0 with hg' | hg'
    · exfalso; nlinarith
    · have := htf.2.mpr hf'; have := htg.1.mpr hg'; nlinarith
    · have := htf.1.mpr hf'; have := htg.2.mpr hg'; nlinarith
    · exfalso; nlinarith

/-- The shared event vertex's two far side coordinates are nonzero.  At a vertex
event for the pair `(i, cyclicNext i)` (shared vertex `P.q (cyclicNext i)`), the
two *far* endpoints `P.q i` and `P.q (cyclicNext (cyclicNext i))` are off the ray
line — because no edge has both endpoints on the ray line. -/
lemma event_far_endpoints_ne (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (i : Fin n) (hs : side ρ.r z (P.q (cyclicNext i)) = 0) :
    side ρ.r z (P.q i) ≠ 0 ∧
      side ρ.r z (P.q (cyclicNext (cyclicNext i))) ≠ 0 := by
  constructor
  · intro h0
    exact no_adjacent_vertices_both_on_rayLine P ρ z i h0 hs
  · intro h2
    exact no_adjacent_vertices_both_on_rayLine P ρ z (cyclicNext i) hs h2

/-- **Vertex-event pair count is eventually parity-constant (unconditional).**
For an event edge `i` (whose end vertex is on the ray line at `t₀`,
`s1Of i t₀ = 0`), the pair count `fcount' i + fcount' (cyclicNext i)` has
eventually-constant parity at `t₀`.  No `NoTangentialVertexSweep`: the span truth
table neutralizes the event in *both* the backward and the forward regime. -/
lemma pair_count_eventually_const' (P : StrictSimplePolygon n) (ρ : RayDirection P)
    {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (i : Fin n) (hs : s1Of P ρ x y i t₀ = 0) :
    ∀ᶠ t in nhds t₀,
      (fcount' P ρ x y i t + fcount' P ρ x y (cyclicNext i) t) % 2 =
        (fcount' P ρ x y i t₀ + fcount' P ρ x y (cyclicNext i) t₀) % 2 := by
  classical
  simp only [fcount'_eq]
  set k := cyclicNext i with hk
  set z₀ := AffineMap.lineMap x y t₀ with hz₀
  -- off-boundary near t₀, and at t₀.
  have hoffev := eventually_off_boundary P ρ hfree ht₀
  have hoff0 : ¬ OnBoundary P z₀ :=
    hfree _ (by rw [hz₀, openSegment_eq_image_lineMap]; exact ⟨t₀, ht₀, rfl⟩)
  -- bridge to the edge-parameter event: crossU i t₀ = 1, crossU k t₀ = 0.
  have hsdef : side ρ.r z₀ (P.q (cyclicNext i)) = 0 := hs
  have hu1 : crossU P ρ z₀ i = 1 := (side_next_zero_iff_crossU_one P ρ z₀ i).mp hsdef
  have hτk : crossTau P ρ z₀ k = crossTau P ρ z₀ i := crossTau_event_eq P ρ z₀ i hu1
  -- the shared ray parameter τ_v ≠ 0 (else z₀ is the vertex, a boundary point).
  have hτvne : crossTau P ρ z₀ i ≠ 0 := by
    intro h0
    apply hoff0
    have hrec : z₀ = P.q (cyclicNext i) := by
      have := reconstruct_u_eq_one P ρ z₀ i hu1
      rwa [h0, zero_smul, add_zero] at this
    exact ⟨cyclicNext i, by rw [hrec, Edge]; exact left_mem_segment ℝ _ _⟩
  -- far endpoints nonzero.
  obtain ⟨ha, hb⟩ := event_far_endpoints_ne P ρ z₀ i hsdef
  have ha' : s0Of P ρ x y i t₀ ≠ 0 := ha
  have hb' : s1Of P ρ x y k t₀ ≠ 0 := by
    show side ρ.r z₀ (P.q (cyclicNext (cyclicNext i))) ≠ 0; rw [hk] at *; exact hb
  -- continuity of the two ray parameters.
  have hctau_i := continuous_tauOf P ρ x y i
  have hctau_k := continuous_tauOf P ρ x y k
  -- shared side: s1Of i t = s0Of k t (= side z(t) (P.q k)), definitionally.
  have hshare : ∀ t, s1Of P ρ x y i t = s0Of P ρ x y k t := fun _ => rfl
  -- a(t), b(t) eventually nonzero (keep sign).
  have hca := continuous_s0Of P ρ x y i
  have hcb := continuous_s1Of P ρ x y k
  have eva : ∀ᶠ t in nhds t₀, s0Of P ρ x y i t ≠ 0 := by
    rcases lt_or_gt_of_ne ha' with h | h
    · filter_upwards [(hca.tendsto t₀).eventually_lt_const h] with t ht using ne_of_lt ht
    · filter_upwards [(hca.tendsto t₀).eventually_const_lt h] with t ht using ne_of_gt ht
  have evb : ∀ᶠ t in nhds t₀, s1Of P ρ x y k t ≠ 0 := by
    rcases lt_or_gt_of_ne hb' with h | h
    · filter_upwards [(hcb.tendsto t₀).eventually_lt_const h] with t ht using ne_of_lt ht
    · filter_upwards [(hcb.tendsto t₀).eventually_const_lt h] with t ht using ne_of_gt ht
  rcases lt_or_gt_of_ne hτvne with hback | hfwd
  · -- BACKWARD: τ_v < 0; both edges uncounted near and at t₀ → pair count 0.
    have hτi0 : tauOf P ρ x y i t₀ < 0 := hback
    have hτk0 : tauOf P ρ x y k t₀ < 0 := by
      show crossTau P ρ z₀ k < 0; rw [hτk]; exact hback
    have evτi : ∀ᶠ t in nhds t₀, tauOf P ρ x y i t < 0 := by
      filter_upwards [(hctau_i.tendsto t₀).eventually_lt_const hτi0] with t ht using ht
    have evτk : ∀ᶠ t in nhds t₀, tauOf P ρ x y k t < 0 := by
      filter_upwards [(hctau_k.tendsto t₀).eventually_lt_const hτk0] with t ht using ht
    -- both statuses false near and at t₀.
    have hfalse : ∀ t, tauOf P ρ x y i t < 0 → ¬ statusOf' P ρ x y i t := by
      intro t hτ hst; rw [statusOf'_iff] at hst; linarith [hst.2]
    have hfalsek : ∀ t, tauOf P ρ x y k t < 0 → ¬ statusOf' P ρ x y k t := by
      intro t hτ hst; rw [statusOf'_iff] at hst; linarith [hst.2]
    filter_upwards [evτi, evτk] with t hτi hτk
    rw [if_neg (hfalse t hτi), if_neg (hfalsek t hτk),
        if_neg (hfalse t₀ hτi0), if_neg (hfalsek t₀ hτk0)]
  · -- FORWARD: τ_v > 0; forward guard holds, pair count = span pair, parity [Span a b].
    have hτi0 : 0 < tauOf P ρ x y i t₀ := hfwd
    have hτk0 : 0 < tauOf P ρ x y k t₀ := by
      show 0 < crossTau P ρ z₀ k; rw [hτk]; exact hfwd
    have evτi : ∀ᶠ t in nhds t₀, 0 < tauOf P ρ x y i t := by
      filter_upwards [(hctau_i.tendsto t₀).eventually_const_lt hτi0] with t ht using ht
    have evτk : ∀ᶠ t in nhds t₀, 0 < tauOf P ρ x y k t := by
      filter_upwards [(hctau_k.tendsto t₀).eventually_const_lt hτk0] with t ht using ht
    -- with forward guard, status = span; reduce both fcount to span indicators.
    have hstatus_i : ∀ t, ¬ OnBoundary P (AffineMap.lineMap x y t) →
        0 < tauOf P ρ x y i t →
        (if statusOf' P ρ x y i t then 1 else 0) =
          (if Span (s0Of P ρ x y i t) (s1Of P ρ x y i t) then 1 else 0) := by
      intro t _ hτ
      by_cases hsp : Span (s0Of P ρ x y i t) (s1Of P ρ x y i t)
      · rw [if_pos hsp, if_pos (by rw [statusOf'_iff]; exact ⟨hsp, le_of_lt hτ⟩)]
      · rw [if_neg hsp, if_neg (by rw [statusOf'_iff]; rintro ⟨h, _⟩; exact hsp h)]
    have hstatus_k : ∀ t, ¬ OnBoundary P (AffineMap.lineMap x y t) →
        0 < tauOf P ρ x y k t →
        (if statusOf' P ρ x y k t then 1 else 0) =
          (if Span (s0Of P ρ x y k t) (s1Of P ρ x y k t) then 1 else 0) := by
      intro t _ hτ
      by_cases hsp : Span (s0Of P ρ x y k t) (s1Of P ρ x y k t)
      · rw [if_pos hsp, if_pos (by rw [statusOf'_iff]; exact ⟨hsp, le_of_lt hτ⟩)]
      · rw [if_neg hsp, if_neg (by rw [statusOf'_iff]; rintro ⟨h, _⟩; exact hsp h)]
    -- the span-pair parity equals [Span a b] (truth table), eventually constant.
    -- Determine the constant value c := [Span a(t₀) b(t₀)] mod 2.
    have hAB_iff : ∀ t, s0Of P ρ x y i t ≠ 0 → s1Of P ρ x y k t ≠ 0 →
        ((if Span (s0Of P ρ x y i t) (s1Of P ρ x y i t) then 1 else 0) +
          (if Span (s0Of P ρ x y k t) (s1Of P ρ x y k t) then 1 else 0)) % 2 =
          (if Span (s0Of P ρ x y i t) (s1Of P ρ x y k t) then 1 else 0) := by
      intro t hat hbt
      -- s1Of i t = s0Of k t (shared); apply the truth table with a, s, b.
      rw [← hshare t]
      exact span_mod_two_through_vertex hat hbt
    -- [Span a b] eventually constant (a := s0Of i, b := s1Of k both nonzero).
    have hABev := span_const_two_sides
      (continuous_s0Of P ρ x y i) (continuous_s1Of P ρ x y k) ha' hb'
    -- assemble: near t₀, off boundary, forward, a,b nonzero.
    filter_upwards [hoffev, evτi, evτk, eva, evb, hABev] with t hofft hτi hτk hat hbt hABt
    -- pair count at t reduces to span pair, parity [Span a(t) b(t)] = [Span a(t₀) b(t₀)].
    have key : ((if statusOf' P ρ x y i t then 1 else 0) +
        (if statusOf' P ρ x y k t then 1 else 0)) % 2 =
        (if Span (s0Of P ρ x y i t₀) (s1Of P ρ x y k t₀) then 1 else 0) := by
      rw [hstatus_i t hofft hτi, hstatus_k t hofft hτk, hAB_iff t hat hbt]
      by_cases h : Span (s0Of P ρ x y i t) (s1Of P ρ x y k t)
      · rw [if_pos h, if_pos (hABt.mp h)]
      · rw [if_neg h, if_neg (fun hc => h (hABt.mpr hc))]
    -- value at t₀: forward holds, span pair, [Span a(t₀) b(t₀)].
    have key0 : ((if statusOf' P ρ x y i t₀ then 1 else 0) +
        (if statusOf' P ρ x y k t₀ then 1 else 0)) % 2 =
        (if Span (s0Of P ρ x y i t₀) (s1Of P ρ x y k t₀) then 1 else 0) := by
      rw [hstatus_i t₀ hoff0 hτi0, hstatus_k t₀ hoff0 hτk0, hAB_iff t₀ ha' hb']
    rw [key, key0]

/-! ## Layer 8: assembly — unconditional local constancy of the parity

The crossing number is the `univ`-sum of `fcount'`.  Split edges into the `u = 1`
representatives `R` (`s1Of i t₀ = 0`), the `u = 0` set `N = cyclicNext '' R`, and
the non-event `Rest`.  Each `R`-pair has eventually-constant parity
(`pair_count_eventually_const'`); each `Rest` edge has eventually-constant status
(`statusOf'_eventually_eq_of_noEvent`).  Summing gives eventual parity constancy
of `CrossingNumber'` — *with no extra hypothesis*. -/

/-- `CrossingNumber'` as the `univ`-sum of the boolean status indicators. -/
lemma crossingNumber'_eq_sum (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x y : Pt) (t : ℝ) :
    CrossingNumber' P ρ (AffineMap.lineMap x y t) =
      ∑ i : Fin n, fcount' P ρ x y i t := by
  classical
  rw [crossingNumber'_eq_card]
  unfold CrossingEdges'
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [fcount'_eq]
  congr 1

/-- **Unconditional crossing-number parity constancy at every interior `t₀`.**
Along a boundary-free segment, the side-coordinate crossing number has eventually
constant parity at every interior parameter — including vertex events, which are
neutral by construction. -/
lemma crossingNumber'_parity_eventually_const (P : StrictSimplePolygon n)
    (ρ : RayDirection P) {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ t in nhds t₀,
      CrossingNumber' P ρ (AffineMap.lineMap x y t) % 2 =
        CrossingNumber' P ρ (AffineMap.lineMap x y t₀) % 2 := by
  classical
  have htwo : 2 ≤ n := Nat.le_trans (by decide) P.hthree
  -- R = u = 1 events (s1Of i t₀ = 0); N = u = 0 events (s0Of i t₀ = 0).
  set R : Finset (Fin n) := Finset.univ.filter (fun i => s1Of P ρ x y i t₀ = 0)
    with hR
  set N : Finset (Fin n) := Finset.univ.filter (fun i => s0Of P ρ x y i t₀ = 0)
    with hN
  -- bridge R/N to the crossU events to reuse the cyclic pairing.
  have hRmem : ∀ i, i ∈ R ↔ crossU P ρ (AffineMap.lineMap x y t₀) i = 1 := by
    intro i; rw [hR, Finset.mem_filter]
    constructor
    · rintro ⟨_, h⟩
      exact (side_next_zero_iff_crossU_one P ρ _ i).mp h
    · intro h
      exact ⟨Finset.mem_univ _, (side_next_zero_iff_crossU_one P ρ _ i).mpr h⟩
  have hNmem : ∀ i, i ∈ N ↔ crossU P ρ (AffineMap.lineMap x y t₀) i = 0 := by
    intro i; rw [hN, Finset.mem_filter]
    constructor
    · rintro ⟨_, h⟩
      exact (side_start_zero_iff_crossU_zero P ρ _ i).mp h
    · intro h
      exact ⟨Finset.mem_univ _, (side_start_zero_iff_crossU_zero P ρ _ i).mpr h⟩
  -- N = image cyclicNext R.
  have hNimg : N = R.image cyclicNext := by
    apply Finset.ext; intro k
    rw [hNmem, Finset.mem_image]
    constructor
    · intro hk0
      refine ⟨cyclicPrev k, ?_, cyclicNext_cyclicPrev htwo k⟩
      rw [hRmem]
      exact (u_eq_one_of_u_eq_zero_prev P ρ _ k hk0).1
    · rintro ⟨i, hi1, rfl⟩
      rw [hRmem] at hi1
      exact (u_eq_zero_of_u_eq_one_next P ρ _ i hi1).1
  have hdisj : Disjoint R N := by
    rw [Finset.disjoint_left]
    intro i hiR hiN
    rw [hRmem] at hiR; rw [hNmem] at hiN
    rw [hiR] at hiN; norm_num at hiN
  set Rest : Finset (Fin n) := Finset.univ \ (R ∪ N) with hRest
  have hpart : Finset.univ = (R ∪ N) ∪ Rest := by
    rw [hRest, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  have hdisj2 : Disjoint (R ∪ N) Rest := by
    rw [hRest]; exact Finset.disjoint_sdiff
  have hsum : ∀ t, ∑ i : Fin n, fcount' P ρ x y i t =
      (∑ i ∈ R, fcount' P ρ x y i t + ∑ i ∈ N, fcount' P ρ x y i t)
        + ∑ i ∈ Rest, fcount' P ρ x y i t := by
    intro t
    conv_lhs => rw [show (Finset.univ : Finset (Fin n)) = (R ∪ N) ∪ Rest from hpart]
    rw [Finset.sum_union hdisj2, Finset.sum_union hdisj]
  have hNsum : ∀ t, ∑ i ∈ N, fcount' P ρ x y i t =
      ∑ i ∈ R, fcount' P ρ x y (cyclicNext i) t := by
    intro t
    rw [hNimg, Finset.sum_image]
    intro a _ b _ h; exact cyclicNext_injective h
  -- pair sum over R eventually parity-constant.
  have hpairs : ∀ᶠ t in nhds t₀, ∀ i ∈ R,
      (fcount' P ρ x y i t + fcount' P ρ x y (cyclicNext i) t) % 2 =
        (fcount' P ρ x y i t₀ + fcount' P ρ x y (cyclicNext i) t₀) % 2 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hsi : s1Of P ρ x y i t₀ = 0 := by
      rw [hR, Finset.mem_filter] at hi; exact hi.2
    exact pair_count_eventually_const' P ρ hfree ht₀ i hsi
  -- rest sum eventually constant.
  have hrest : ∀ᶠ t in nhds t₀, ∀ i ∈ Rest,
      fcount' P ρ x y i t = fcount' P ρ x y i t₀ := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hi' : i ∉ R ∧ i ∉ N := by
      rw [hRest, Finset.mem_sdiff] at hi
      have := hi.2; rw [Finset.mem_union, not_or] at this; exact this
    have hs1 : s1Of P ρ x y i t₀ ≠ 0 := by
      intro h; exact hi'.1 (by rw [hR, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩)
    have hs0 : s0Of P ρ x y i t₀ ≠ 0 := by
      intro h; exact hi'.2 (by rw [hN, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩)
    have hev := statusOf'_eventually_eq_of_noEvent P ρ hfree i ht₀ hs0 hs1
    filter_upwards [hev] with t ht
    simp only [fcount'_eq, ht]
  -- combine, working mod 2.
  filter_upwards [hpairs, hrest] with t hp hr
  rw [crossingNumber'_eq_sum, crossingNumber'_eq_sum, hsum t, hsum t₀, hNsum t, hNsum t₀]
  -- merge each R-pair into a single sum, then take mod 2.
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  -- A_t := ∑R (fc_i + fc_next), B_t := ∑Rest fc.  A_t % 2 = A_t₀ % 2 and B_t = B_t₀.
  have hpairR :
      (∑ i ∈ R, (fcount' P ρ x y i t + fcount' P ρ x y (cyclicNext i) t)) % 2 =
      (∑ i ∈ R, (fcount' P ρ x y i t₀ + fcount' P ρ x y (cyclicNext i) t₀)) % 2 := by
    rw [Finset.sum_nat_mod, Finset.sum_nat_mod
      (s := R) (f := fun i => fcount' P ρ x y i t₀ + fcount' P ρ x y (cyclicNext i) t₀)]
    congr 1
    exact Finset.sum_congr rfl (fun i hi => hp i hi)
  have hrestEq : ∑ i ∈ Rest, fcount' P ρ x y i t = ∑ i ∈ Rest, fcount' P ρ x y i t₀ :=
    Finset.sum_congr rfl (fun i hi => hr i hi)
  rw [Nat.add_mod, hpairR, hrestEq, ← Nat.add_mod]

/-! ## Layer 9: region-indicator local constancy and the `loc'` residue

Off the boundary, `ClosedRegion'` is `Odd (CrossingNumber')`; with the crossing
parity eventually constant at every interior parameter, the region indicator is
eventually constant.  Pulling back to the open parameter subtype `(0,1)` gives
`IsLocallyConstant` — the *unconditional* analogue of
`OpenSegmentRegionLocallyConstant`. -/

/-- The region indicator along the segment, under the corrected convention. -/
def regionOf' (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt) :
    ℝ → Prop :=
  fun t => ClosedRegion' P ρ (AffineMap.lineMap x y t)

/-- Odd-parity is preserved when the `% 2` values agree. -/
lemma odd_iff_of_mod_two_eq {a b : ℕ} (h : a % 2 = b % 2) : Odd a ↔ Odd b := by
  rw [Nat.odd_iff, Nat.odd_iff, h]

/-- **Region indicator eventually constant at every interior `t₀` (unconditional).** -/
lemma regionOf'_eventually_eq (P : StrictSimplePolygon n) (ρ : RayDirection P)
    {x y : Pt} (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ t in nhds t₀, regionOf' P ρ x y t = regionOf' P ρ x y t₀ := by
  have hcn := crossingNumber'_parity_eventually_const P ρ hfree ht₀
  have hoffev := eventually_off_boundary P ρ hfree ht₀
  have hoff0 : ¬ OnBoundary P (AffineMap.lineMap x y t₀) :=
    hfree _ (by rw [openSegment_eq_image_lineMap]; exact ⟨t₀, ht₀, rfl⟩)
  filter_upwards [hcn, hoffev] with t hcnt hofft
  unfold regionOf' ClosedRegion'
  rw [eq_iff_iff]
  constructor
  · rintro (hb | ho)
    · exact absurd hb hofft
    · exact Or.inr ((odd_iff_of_mod_two_eq hcnt).mp ho)
  · rintro (hb | ho)
    · exact absurd hb hoff0
    · exact Or.inr ((odd_iff_of_mod_two_eq hcnt).mpr ho)

/-- **The corrected `loc` residue, UNCONDITIONAL.**  Along a boundary-free open
segment, the side-coordinate region indicator is locally constant.  Unlike the
old `OpenSegmentRegionLocallyConstant` (which needs `VertexSweepNeutral` /
`NoTangentialVertexSweep`, false in general), this holds with no extra
hypothesis. -/
def OpenSegmentRegionLocallyConstant' (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (x y : Pt) : Prop :=
  (∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z) →
    IsLocallyConstant
      (fun t : Set.Ioo (0 : ℝ) 1 =>
        ClosedRegion' P ρ (AffineMap.lineMap x y (t : ℝ)))

/-- **Unconditional local constancy of the corrected region indicator.** -/
theorem openSegmentRegionLocallyConstant'_unconditional
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt) :
    OpenSegmentRegionLocallyConstant' P ρ x y := by
  intro hfree
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have hev := regionOf'_eventually_eq P ρ hfree s.2
  have htends : Filter.Tendsto (Subtype.val : Set.Ioo (0:ℝ) 1 → ℝ)
      (nhds s) (nhds (s : ℝ)) := continuous_subtype_val.tendsto s
  have := htends.eventually hev
  filter_upwards [this] with s' hs'
  exact hs'

/-! ## Layer 10: the corrected region interface (item 4)

The A3 chain consumes a region-membership `loc` residue plus an interior region
witness, and produces a diagonal whose closed segment lies in the region.  Under
the corrected convention we re-derive this interface around `ClosedRegion'` with
the `loc'` residue now *unconditional*: the primed open-segment region constancy,
the primed diagonal predicate `IsDiagonal'`, and the certificate builder
`isDiagonal_of_certificate'`.

Per the ruling's migration plan, this is the cheaper of the two routes (the
generic-agreement bridge would require proving the old and new conventions agree
in parity, a generic-ray argument).  The combinatorial / triangle-containment
layers of the A3 chain are region-agnostic and reused verbatim; only the
region-membership facts are re-derived here. -/

/-- Primed diagonal predicate: nonadjacent vertex pair whose closed segment lies
in the *corrected* closed region, meeting the boundary only at its endpoints. -/
def IsDiagonal' (P : StrictSimplePolygon n) (ρ : RayDirection P) (i j : Fin n) :
    Prop :=
  i ≠ j ∧
  ¬ CyclicAdjacent i j ∧
  seg (P.q i) (P.q j) ⊆ {x : Pt | ClosedRegion' P ρ x} ∧
  seg (P.q i) (P.q j) ∩ {x : Pt | OnBoundary P x}
    = ({P.q i, P.q j} : Set Pt)

set_option synthInstance.maxHeartbeats 400000 in
/-- **Primed open-segment region constancy.**  If the open segment avoids the
boundary and some interior point is in the corrected region, every interior point
is.  Connectedness of `(0,1)` plus the unconditional local constancy. -/
theorem openSegment_region'_const_of_boundary_free
    (P : StrictSimplePolygon n) (ρ : RayDirection P) {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    {z₀ : Pt} (hz₀ : z₀ ∈ openSegment ℝ x y) (hz₀reg : ClosedRegion' P ρ z₀) :
    ∀ z ∈ openSegment ℝ x y, ClosedRegion' P ρ z := by
  classical
  haveI : PreconnectedSpace (Set.Ioo (0 : ℝ) 1) := by
    rw [← isPreconnected_iff_preconnectedSpace]; exact isPreconnected_Ioo
  have hLC := openSegmentRegionLocallyConstant'_unconditional P ρ x y hfree
  set f : Set.Ioo (0 : ℝ) 1 → Prop :=
    fun t => ClosedRegion' P ρ (AffineMap.lineMap x y (t : ℝ)) with hf
  have hclopen : IsClopen {t : Set.Ioo (0 : ℝ) 1 | f t = True} :=
    hLC.isClopen_fiber True
  rw [openSegment_eq_image_lineMap] at hz₀
  obtain ⟨t₀, ht₀, ht₀eq⟩ := hz₀
  have hseed : (⟨t₀, ht₀⟩ : Set.Ioo (0 : ℝ) 1) ∈
      {t : Set.Ioo (0 : ℝ) 1 | f t = True} := by
    simp only [Set.mem_setOf_eq, hf, eq_iff_iff, iff_true]
    rw [ht₀eq]; exact hz₀reg
  have huniv : {t : Set.Ioo (0 : ℝ) 1 | f t = True} = Set.univ :=
    IsClopen.eq_univ hclopen ⟨_, hseed⟩
  intro z hz
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨t, ht, hteq⟩ := hz
  have hmem : (⟨t, ht⟩ : Set.Ioo (0 : ℝ) 1) ∈
      {t : Set.Ioo (0 : ℝ) 1 | f t = True} := by rw [huniv]; trivial
  simp only [Set.mem_setOf_eq, hf, eq_iff_iff, iff_true] at hmem
  rw [hteq] at hmem
  exact hmem

/-- Boundary vertices are in the corrected region (`OnBoundary` branch). -/
lemma closedRegion'_of_onBoundary (P : StrictSimplePolygon n) (ρ : RayDirection P)
    {x : Pt} (hx : OnBoundary P x) : ClosedRegion' P ρ x := Or.inl hx

/-- **Primed diagonal certificate.**  From the combinatorial data, the boundary-
only-at-endpoints clause, boundary-freeness of the open segment, and a single
interior witness in the corrected region, the pair `i, j` is a corrected diagonal.
The `loc` clause is now discharged unconditionally. -/
theorem isDiagonal'_of_certificate
    (P : StrictSimplePolygon n) (ρ : RayDirection P) {i j : Fin n}
    (hij : i ≠ j) (hnadj : ¬ CyclicAdjacent i j)
    (hfree : ∀ z ∈ openSegment ℝ (P.q i) (P.q j), ¬ OnBoundary P z)
    {z₀ : Pt} (hz₀ : z₀ ∈ openSegment ℝ (P.q i) (P.q j))
    (hz₀reg : ClosedRegion' P ρ z₀)
    (hbdry : seg (P.q i) (P.q j) ∩ {x : Pt | OnBoundary P x}
      = ({P.q i, P.q j} : Set Pt)) :
    IsDiagonal' P ρ i j := by
  refine ⟨hij, hnadj, ?_, hbdry⟩
  intro z hz
  rcases (segment_eq_image_lineMap ℝ (P.q i) (P.q j) ▸ hz :
      z ∈ (AffineMap.lineMap (P.q i) (P.q j)) '' Set.Icc (0:ℝ) 1) with ⟨t, ht, hteq⟩
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · refine closedRegion'_of_onBoundary P ρ ⟨i, ?_⟩
    have hzi : z = P.q i := by rw [← hteq, ← h0]; simp
    rw [hzi, Edge]; exact left_mem_segment ℝ _ _
  · rcases eq_or_lt_of_le ht.2 with h1 | h1
    · refine closedRegion'_of_onBoundary P ρ ⟨j, ?_⟩
      have hzj : z = P.q j := by rw [← hteq, h1]; simp
      rw [hzj, Edge]; exact left_mem_segment ℝ _ _
    · have hzopen : z ∈ openSegment ℝ (P.q i) (P.q j) := by
        rw [openSegment_eq_image_lineMap]; exact ⟨t, ⟨h0, h1⟩, hteq⟩
      exact openSegment_region'_const_of_boundary_free P ρ hfree hz₀ hz₀reg z hzopen

/-! ## Layer 11: the corrected A3 headline — `exists_diagonal'`

We rebuild the ear / slide diagonal facts and `exists_diagonal'` around the
corrected region.  Convexity is captured by `IsConvexVertex'` (adjacent triangle
in the corrected region); the interior region witness is the convex-triangle
midpoint, in the region by triangle containment.  All combinatorial /
triangle-containment facts of `PolygonConvexVertex` are region-agnostic and are
reused verbatim. -/

/-- Primed convex vertex: the adjacent triangle is contained in the corrected
region. -/
def IsConvexVertex' (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n) :
    Prop :=
  closedTri (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i))
    ⊆ {x : Pt | ClosedRegion' P ρ x}

/-- From a primed convex vertex, any segment between two of the three adjacent-
triangle vertices lies in the corrected region. -/
lemma seg_subset_region'_of_convex_aux
    {P : StrictSimplePolygon n} {ρ : RayDirection P} {i : Fin n}
    (hconv : IsConvexVertex' P ρ i) {a b : Pt}
    (ha : a ∈ closedTri (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)))
    (hb : b ∈ closedTri (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i))) :
    seg a b ⊆ {z : Pt | ClosedRegion' P ρ z} :=
  (ProofsInTheBook.PolygonConvexVertex.seg_subset_closedTri ha hb).trans hconv

/-- Transversality residue for the corrected ear diagonal: the open base is
boundary-free.  (The `loc` clause is unconditional, so it is not carried.) -/
structure EarTransversality' (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (i : Fin n) : Prop where
  free : ∀ z ∈ openSegment ℝ (P.q (cyclicPrev i)) (P.q (cyclicNext i)),
    ¬ OnBoundary P z

/-- Transversality residue for the corrected slide diagonal. -/
structure SlideTransversality' (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (i z : Fin n) : Prop where
  free : ∀ w ∈ openSegment ℝ (P.q i) (P.q z), ¬ OnBoundary P w

/-- **Corrected empty-triangle ear.**  A primed-convex vertex whose adjacent
triangle is empty yields the corrected ear diagonal `prev i → next i`. -/
theorem convex_vertex_empty_triangle_gives_ear'
    {P : StrictSimplePolygon n} {ρ : RayDirection P} (hn : 4 ≤ n) (i : Fin n)
    (hconv : IsConvexVertex' P ρ i)
    (htrans : EarTransversality' P ρ i) :
    IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i) := by
  have hij : cyclicPrev i ≠ cyclicNext i :=
    ProofsInTheBook.PolygonConvexVertex.cyclicPrev_ne_cyclicNext hn i
  have hnadj : ¬ CyclicAdjacent (cyclicPrev i) (cyclicNext i) :=
    ProofsInTheBook.PolygonConvexVertex.not_cyclicAdjacent_prev_next hn i
  set B := P.q (cyclicPrev i) with hBdef
  set C := P.q (cyclicNext i) with hCdef
  have hBC : B ≠ C := by rw [hBdef, hCdef]; intro h; exact hij (P.injective_q h)
  set z₀ := midpoint ℝ B C with hz₀def
  have hz₀open : z₀ ∈ openSegment ℝ B C :=
    ProofsInTheBook.PolygonConvexVertex.midpoint_mem_openSegment hBC
  have hz₀reg : ClosedRegion' P ρ z₀ := by
    have hsub : seg B C ⊆ {z : Pt | ClosedRegion' P ρ z} :=
      seg_subset_region'_of_convex_aux hconv
        (ProofsInTheBook.PolygonConvexVertex.mem_closedTri_left B (P.q i) C)
        (ProofsInTheBook.PolygonConvexVertex.mem_closedTri_right B (P.q i) C)
    exact hsub (by rw [seg]; exact openSegment_subset_segment ℝ B C hz₀open)
  have hbdry : seg B C ∩ {x : Pt | OnBoundary P x} = ({B, C} : Set Pt) :=
    bdry_of_free (vertex_onBoundary P (cyclicPrev i))
      (vertex_onBoundary P (cyclicNext i)) htrans.free
  exact isDiagonal'_of_certificate P ρ hij hnadj htrans.free hz₀open hz₀reg hbdry

/-- **Corrected slide diagonal.**  A primed-convex vertex `i` and a slide-height-
maximal enclosed vertex `z` give the corrected diagonal `i → z`. -/
theorem slide_last_vertex_gives_diagonal'
    {P : StrictSimplePolygon n} {ρ : RayDirection P} (i z : Fin n)
    (hconv : IsConvexVertex' P ρ i)
    (hz : z ∈ verticesInAdjacentTriangle P i)
    (htrans : SlideTransversality' P ρ i z) :
    IsDiagonal' P ρ i z := by
  obtain ⟨hzi, _, _⟩ := ProofsInTheBook.PolygonConvexVertex.vertexInTriangle_ne hz
  have hij : i ≠ z := Ne.symm hzi
  have hnadj : ¬ CyclicAdjacent i z :=
    ProofsInTheBook.PolygonConvexVertex.not_cyclicAdjacent_slide hz
  have hqz : P.q z ∈ closedTri (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) := by
    have := (mem_verticesInAdjacentTriangle_iff P i z).mp hz
    simpa [adjacentTriangle] using this.2.2.2
  set A := P.q i
  set Z := P.q z
  have hAZ : A ≠ Z := by intro h; exact hij (P.injective_q h)
  set z₀ := midpoint ℝ A Z with hz₀def
  have hz₀open : z₀ ∈ openSegment ℝ A Z :=
    ProofsInTheBook.PolygonConvexVertex.midpoint_mem_openSegment hAZ
  have hz₀reg : ClosedRegion' P ρ z₀ := by
    have hsub : seg A Z ⊆ {w : Pt | ClosedRegion' P ρ w} :=
      seg_subset_region'_of_convex_aux hconv
        (ProofsInTheBook.PolygonConvexVertex.mem_closedTri_mid
          (P.q (cyclicPrev i)) A (P.q (cyclicNext i)))
        hqz
    exact hsub (by rw [seg]; exact openSegment_subset_segment ℝ A Z hz₀open)
  have hbdry : seg A Z ∩ {x : Pt | OnBoundary P x} = ({A, Z} : Set Pt) :=
    bdry_of_free (vertex_onBoundary P i) (vertex_onBoundary P z) htrans.free
  exact isDiagonal'_of_certificate P ρ hij hnadj htrans.free hz₀open hz₀reg hbdry

/-- Corrected branch-aware transversality dispatcher (ear when the adjacent
triangle is empty; slide at every enclosed maximal vertex). -/
structure DiagonalTransversality' (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (i : Fin n) : Prop where
  ear : (verticesInAdjacentTriangle P i) = ∅ → EarTransversality' P ρ i
  slide : ∀ z ∈ verticesInAdjacentTriangle P i,
    (∀ w ∈ verticesInAdjacentTriangle P i,
      heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q w) ≤
        heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q z)) →
    SlideTransversality' P ρ i z

/-- **Corrected A3 headline: existence of a diagonal** (`4 ≤ n`).  Every strict
simple polygon with at least four vertices has a *corrected* diagonal, given a
primed-convex extreme vertex and the branch-aware free-segment dispatcher.  All
local-constancy content (including every vertex sweep) is discharged
unconditionally by the side-coordinate convention. -/
theorem exists_diagonal'
    {P : StrictSimplePolygon n} {ρ : RayDirection P} (hn : 4 ≤ n)
    {i : Fin n} (hconvi : IsConvexVertex' P ρ i)
    (htrans : DiagonalTransversality' P ρ i) :
    ∃ a b : Fin n, IsDiagonal' P ρ a b := by
  classical
  by_cases hempty : (verticesInAdjacentTriangle P i) = ∅
  · refine ⟨cyclicPrev i, cyclicNext i, ?_⟩
    exact convex_vertex_empty_triangle_gives_ear' hn i hconvi (htrans.ear hempty)
  · have hS : (verticesInAdjacentTriangle P i).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨z, hzmem, hzmax⟩ :=
      ProofsInTheBook.PolygonDiagonal.slide_last_vertex_exists P i hS
    refine ⟨i, z, ?_⟩
    exact slide_last_vertex_gives_diagonal' i z hconvi hzmem (htrans.slide z hzmem hzmax)

end

end ProofsInTheBook.PolygonSideCrossing
