import ProofsInTheBook.PolygonResidues

/-!
# Chapter 36 — Crossing-parity local constancy (the `loc` residue)

This file develops the **genuine geometric core** that `PolygonParity` /
`PolygonResidues` deliberately isolated as the residue
`OpenSegmentRegionLocallyConstant`: along an open segment whose points avoid the
polygon boundary, the half-open crossing-parity region membership is *locally
constant* in the segment parameter.

## The route

Fix the strict simple polygon `P`, the non-parallel ray direction `ρ` (so
`det2 ρ.r (edge vector) ≠ 0` for every edge), and the base point `z`.  For a
single edge `i` from `a = P.q i` to `b = P.q (cyclicNext i)`, the half-open
crossing condition `RayProperlyCrossesHalfOpenEdge ρ.r z a b` is an existential
in two scalar parameters `(τ, u)` constrained by one *linear* vector equation
`z + τ • r = a + u • (b - a)`.  Because `det2 r (b - a) ≠ 0`, that linear system
has a **unique** solution, given by Cramer's rule:

* `crossU  ρ z i := det2 ρ.r (z - a) / det2 ρ.r (b - a)`   (the edge parameter)
* `crossTau ρ z i := det2 (a - z) (b - a) / det2 ρ.r (b - a)` (the ray parameter)

and the crossing condition becomes the **conjunction of three real
inequalities** that are each *affine* in `z`:

```
EdgeCrossesRay P ρ z i  ↔  z ∉ Edge i  ∧  0 ≤ crossTau ρ z i
                                       ∧  0 ≤ crossU ρ z i ∧ crossU ρ z i < 1.
```

Both `crossU` and `crossTau` are affine in `z`; restricted to a segment
`z = lineMap x y t` they are affine in the parameter `t`.  Each inequality's
truth therefore changes at most at one parameter value, where the corresponding
affine quantity hits an **equality** (`crossTau = 0`, `crossU = 0`, or
`crossU = 1`).

* `crossTau = 0` with the other conditions holding forces `z` onto the closed
  edge `Edge i` — a *boundary point*, excluded by the boundary-free hypothesis
  (`crossTau_eq_zero_imp_onEdge`).
* `crossU = 0` / `crossU = 1` mean the ray passes through a **vertex** of the
  polygon (`a` resp. `b`).  These are the vertex-sweep events; the half-open
  `[0,1)` convention pairs them across the two incident edges so that the parity
  is preserved.

The purely algebraic and "no active `τ = 0` event" parts are discharged here
unconditionally.  The vertex-sweep parity preservation — the genuinely hard,
design-sanctioned plane-sweep step — is isolated as the single, minimally
stated, honestly named local hypothesis `VertexSweepNeutral`, and the residue
`OpenSegmentRegionLocallyConstant` is assembled from it.
-/

namespace ProofsInTheBook.PolygonLocalConstancy

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonParity
open ProofsInTheBook.PolygonConvexVertex
open ProofsInTheBook.PolygonResidues
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## 0. `det2` bilinearity helpers

`det2 u v = u 0 * v 1 - u 1 * v 0` is bilinear and alternating.  We record the
exact algebraic identities the Cramer computation needs. -/

lemma det2_self (u : Pt) : det2 u u = 0 := by
  unfold det2; ring

lemma det2_add_right (u v w : Pt) :
    det2 u (v + w) = det2 u v + det2 u w := by
  unfold det2
  simp only [PiLp.add_apply]
  ring

lemma det2_smul_right (u v : Pt) (c : ℝ) :
    det2 u (c • v) = c * det2 u v := by
  unfold det2
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

lemma det2_sub_right (u v w : Pt) :
    det2 u (v - w) = det2 u v - det2 u w := by
  unfold det2
  simp only [PiLp.sub_apply]
  ring

lemma det2_add_left (u v w : Pt) :
    det2 (u + v) w = det2 u w + det2 v w := by
  unfold det2
  simp only [PiLp.add_apply]
  ring

lemma det2_smul_left (u v : Pt) (c : ℝ) :
    det2 (c • u) v = c * det2 u v := by
  unfold det2
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

lemma det2_sub_left (u v w : Pt) :
    det2 (u - v) w = det2 u w - det2 v w := by
  unfold det2
  simp only [PiLp.sub_apply]
  ring

/-- Two covectors with nonzero determinant annihilate only the zero vector:
if `det2 u w = 0`, `det2 v w = 0` and `det2 u v ≠ 0` then `w = 0`. -/
lemma eq_zero_of_det2_eq_zero {u v w : Pt}
    (huv : det2 u v ≠ 0) (hu : det2 u w = 0) (hv : det2 v w = 0) :
    w = 0 := by
  -- coordinates: u0 w1 = u1 w0 and v0 w1 = v1 w0, determinant u0 v1 - u1 v0 ≠ 0.
  have hu' : u 0 * w 1 - u 1 * w 0 = 0 := hu
  have hv' : v 0 * w 1 - v 1 * w 0 = 0 := hv
  have huv' : u 0 * v 1 - u 1 * v 0 ≠ 0 := huv
  have hw0 : w 0 = 0 := by
    have key : (u 0 * v 1 - u 1 * v 0) * w 0 = 0 := by
      have e1 : v 0 * (u 0 * w 1 - u 1 * w 0) = 0 := by rw [hu']; ring
      have e2 : u 0 * (v 0 * w 1 - v 1 * w 0) = 0 := by rw [hv']; ring
      nlinarith [e1, e2]
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h huv'
    · exact h
  have hw1 : w 1 = 0 := by
    have key : (u 0 * v 1 - u 1 * v 0) * w 1 = 0 := by
      have e1 : v 1 * (u 0 * w 1 - u 1 * w 0) = 0 := by rw [hu']; ring
      have e2 : u 1 * (v 0 * w 1 - v 1 * w 0) = 0 := by rw [hv']; ring
      nlinarith [e1, e2]
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h huv'
    · exact h
  exact pt_ext_zero_one hw0 hw1

/-! ## 1. Cramer characterization of the half-open crossing

For edge `i` from `a = P.q i` to `b = P.q (cyclicNext i)` and base point `z`, the
crossing system `z + τ • r = a + u • (b - a)` has the unique Cramer solution
below (denominator `det2 r (b - a) ≠ 0`). -/

/-- Edge vector `P.q (cyclicNext i) - P.q i`, the substrate's `edgeVec`. -/
local notation3 "ev" P i => edgeVec P i

/-- Cramer denominator: `det2 ρ.r (edge vector)`, nonzero by `no_edge_parallel`. -/
def crossDen (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n) : ℝ :=
  det2 ρ.r (P.q (cyclicNext i) - P.q i)

/-- The edge-parameter `u` of the (unique) ray/edge intersection. -/
def crossU (P : StrictSimplePolygon n) (ρ : RayDirection P) (z : Pt) (i : Fin n) :
    ℝ :=
  det2 ρ.r (z - P.q i) / crossDen P ρ i

/-- The ray-parameter `τ` of the (unique) ray/edge intersection. -/
def crossTau (P : StrictSimplePolygon n) (ρ : RayDirection P) (z : Pt) (i : Fin n) :
    ℝ :=
  det2 (P.q i - z) (P.q (cyclicNext i) - P.q i) / crossDen P ρ i

lemma crossDen_ne_zero (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n) :
    crossDen P ρ i ≠ 0 :=
  ρ.no_edge_parallel i

/-- The unique vector solution of the crossing equation reconstructs the point:
with `τ = crossTau` and `u = crossU`, the equation `z + τ•r = a + u•(b-a)` holds.
This is the backward (existence) half: it produces the witness. -/
lemma cross_eq (P : StrictSimplePolygon n) (ρ : RayDirection P) (z : Pt) (i : Fin n) :
    z + crossTau P ρ z i • ρ.r =
      AffineMap.lineMap (P.q i) (P.q (cyclicNext i)) (crossU P ρ z i) := by
  set a := P.q i
  set b := P.q (cyclicNext i)
  set D := crossDen P ρ i with hD
  have hDne : D ≠ 0 := crossDen_ne_zero P ρ i
  -- abbreviate the two scalars
  set u := crossU P ρ z i with hu
  set τ := crossTau P ρ z i with hτ
  -- reduce to `w = 0` where `w = (z + τ•r) - lineMap a b u`
  set L : Pt := AffineMap.lineMap a b u with hL
  set w : Pt := (z + τ • ρ.r) - L with hw
  have hgoal : z + τ • ρ.r = L ↔ w = 0 := by
    rw [hw]; constructor
    · intro h; rw [h]; simp
    · intro h; rw [sub_eq_zero] at h; exact h
  rw [hgoal]
  -- annihilate `w` by `r` and by `(b - a)`
  apply eq_zero_of_det2_eq_zero (u := ρ.r) (v := b - a) (w := w)
  · -- det2 r (b-a) = D ≠ 0
    show det2 ρ.r (b - a) ≠ 0
    have : det2 ρ.r (b - a) = D := by rw [hD, crossDen]
    rw [this]; exact hDne
  · -- det2 r w = 0
    rw [hw, det2_sub_right, det2_add_right, det2_smul_right, det2_self, hL,
        det2_lineMap]
    -- det2 r z + τ*0 - ((1-u) det2 r a + u det2 r b) = 0
    have hden : det2 ρ.r (b - a) = D := by rw [hD, crossDen]
    have huD : u * det2 ρ.r (b - a) = det2 ρ.r (z - a) := by
      rw [hden, hu, crossU]
      have ha : (P.q i : Pt) = a := rfl
      rw [ha, ← hD, div_mul_cancel₀]
      exact hDne
    rw [det2_sub_right, det2_sub_right] at huD
    -- u*(det2 r b - det2 r a) = det2 r z - det2 r a
    linarith [huD]
  · -- det2 (b-a) w = 0
    rw [hw, det2_sub_right, det2_add_right, det2_smul_right, hL, det2_lineMap]
    -- det2 (b-a) z + τ*det2 (b-a) r - ((1-u) det2 (b-a) a + u det2 (b-a) b) = 0
    have hbab : det2 (b - a) b = det2 (b - a) a := by
      unfold det2; simp only [PiLp.sub_apply]; ring
    have hdenτ : det2 (b - a) ρ.r = -D := by
      rw [hD, crossDen, det2_antisymm ρ.r (b - a), neg_neg]
    -- τ = det2 (a-z)(b-a)/D, and det2(a-z)(b-a) = -det2(b-a)(a-z)
    have hτval : τ = det2 (a - z) (b - a) / D := by
      rw [hτ, crossTau, ← hD]
    have hτD : τ * det2 (b - a) ρ.r = det2 (b - a) (a - z) := by
      rw [hτval, hdenτ]
      have hnum : det2 (a - z) (b - a) = - det2 (b - a) (a - z) := by
        unfold det2; simp only [PiLp.sub_apply]; ring
      rw [hnum, neg_div]
      field_simp
    rw [det2_sub_right] at hτD
    rw [hbab]
    linarith [hτD]

/-- **Uniqueness.**  Any solution `(τ', u')` of the crossing equation equals the
Cramer solution: `u' = crossU` and `τ' = crossTau`. -/
lemma cross_unique (P : StrictSimplePolygon n) (ρ : RayDirection P) (z : Pt)
    (i : Fin n) {τ' u' : ℝ}
    (heq : z + τ' • ρ.r =
      AffineMap.lineMap (P.q i) (P.q (cyclicNext i)) u') :
    u' = crossU P ρ z i ∧ τ' = crossTau P ρ z i := by
  set a := P.q i
  set b := P.q (cyclicNext i)
  set D := crossDen P ρ i with hD
  have hDne : D ≠ 0 := crossDen_ne_zero P ρ i
  have hden : det2 ρ.r (b - a) = D := by rw [hD, crossDen]
  -- apply det2 ρ.r to both sides of `z + τ'•r = lineMap a b u'`.
  have hr : det2 ρ.r (z + τ' • ρ.r) =
      det2 ρ.r (AffineMap.lineMap a b u') := by rw [heq]
  rw [det2_add_right, det2_smul_right, det2_self, det2_lineMap, mul_zero,
      add_zero] at hr
  -- det2 r z = (1-u') det2 r a + u' det2 r b
  -- ⇒ det2 r (z - a) = u' (det2 r b - det2 r a) = u' * det2 r (b-a)
  have hu' : u' * D = det2 ρ.r (z - a) := by
    rw [← hden, det2_sub_right, det2_sub_right]
    nlinarith [hr]
  -- apply det2 (b-a) similarly
  have hb : det2 (b - a) (z + τ' • ρ.r) =
      det2 (b - a) (AffineMap.lineMap a b u') := by rw [heq]
  rw [det2_add_right, det2_smul_right, det2_lineMap] at hb
  have hbab : det2 (b - a) b = det2 (b - a) a := by
    unfold det2; simp only [PiLp.sub_apply]; ring
  have hdenτ : det2 (b - a) ρ.r = -D := by
    rw [hD, crossDen, det2_antisymm ρ.r (b - a), neg_neg]
  -- det2 (b-a) z + τ' det2 (b-a) r = (1-u') det2(b-a) a + u' det2(b-a) b
  -- ⇒ τ' det2(b-a) r = det2(b-a) a - det2(b-a) z = det2(b-a)(a-z)
  have hτ' : τ' * (-D) = det2 (b - a) (a - z) := by
    rw [← hdenτ, det2_sub_right]
    rw [hbab] at hb
    nlinarith [hb]
  constructor
  · -- u' = crossU
    rw [crossU, ← hD, eq_div_iff hDne]
    linarith [hu']
  · -- τ' = crossTau
    rw [crossTau, ← hD, eq_div_iff hDne]
    -- τ' * D = det2 (a-z)(b-a), and τ'*(-D) = det2(b-a)(a-z)
    have hnum : det2 (a - z) (b - a) = - det2 (b - a) (a - z) := by
      unfold det2; simp only [PiLp.sub_apply]; ring
    rw [hnum]
    nlinarith [hτ']

/-- **Cramer equivalence for the half-open crossing.**  An edge `i` is crossed by
the half-open ray from `z` iff `z` is not already on the edge and the Cramer
solution lies in the admissible region `0 ≤ τ`, `0 ≤ u < 1`. -/
lemma edgeCrossesRay_iff (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (i : Fin n) :
    EdgeCrossesRay P ρ z i ↔
      z ∉ Edge P.q i ∧ 0 ≤ crossTau P ρ z i ∧
        0 ≤ crossU P ρ z i ∧ crossU P ρ z i < 1 := by
  unfold EdgeCrossesRay RayProperlyCrossesHalfOpenEdge
  constructor
  · rintro ⟨hnot, τ', u', hτ', hu0, hu1, heq⟩
    obtain ⟨huu, hττ⟩ := cross_unique P ρ z i heq
    subst huu; subst hττ
    exact ⟨hnot, hτ', hu0, hu1⟩
  · rintro ⟨hnot, hτ, hu0, hu1⟩
    exact ⟨hnot, crossTau P ρ z i, crossU P ρ z i, hτ, hu0, hu1, cross_eq P ρ z i⟩

/-! ## 2. Affineness of the Cramer scalars along a segment, and the `τ = 0` event

Both `crossU` and `crossTau` are affine in the base point `z`.  Restricted to a
segment `z = lineMap x y t` they are affine in `t`, so each crossing inequality
flips at most at a single `t`.  The `τ = 0` event, when the crossing inequalities
on `u` hold, lands `z` exactly on the closed edge — a boundary point. -/

/-- `det2 ρ.r (lineMap x y t - c)` is affine in `t`. -/
lemma det2_r_sub_lineMap (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x y c : Pt) (t : ℝ) :
    det2 ρ.r (AffineMap.lineMap x y t - c) =
      (1 - t) * det2 ρ.r (x - c) + t * det2 ρ.r (y - c) := by
  have hsub : AffineMap.lineMap x y t - c =
      AffineMap.lineMap (x - c) (y - c) t := by
    rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    ext k; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  rw [hsub, det2_lineMap]

/-- `crossU` is affine along the segment `lineMap x y t`. -/
lemma crossU_lineMap (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x y : Pt) (i : Fin n) (t : ℝ) :
    crossU P ρ (AffineMap.lineMap x y t) i =
      (1 - t) * crossU P ρ x i + t * crossU P ρ y i := by
  unfold crossU
  rw [det2_r_sub_lineMap]
  rw [add_div, mul_div_assoc, mul_div_assoc]

/-- `crossTau` is affine along the segment `lineMap x y t`. -/
lemma crossTau_lineMap (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x y : Pt) (i : Fin n) (t : ℝ) :
    crossTau P ρ (AffineMap.lineMap x y t) i =
      (1 - t) * crossTau P ρ x i + t * crossTau P ρ y i := by
  unfold crossTau
  set a := P.q i
  set b := P.q (cyclicNext i)
  -- det2 (a - lineMap x y t) (b - a) is affine in t
  have hkey : det2 (a - AffineMap.lineMap x y t) (b - a) =
      (1 - t) * det2 (a - x) (b - a) + t * det2 (a - y) (b - a) := by
    have hsub : a - AffineMap.lineMap x y t =
        AffineMap.lineMap (a - x) (a - y) t := by
      rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
      ext k; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [hsub]
    -- det2 (lineMap (a-x)(a-y) t) (b-a) via left-affineness
    rw [AffineMap.lineMap_apply_module]
    rw [det2_add_left, det2_smul_left, det2_smul_left]
  rw [hkey, add_div, mul_div_assoc, mul_div_assoc]

/-- **The `τ = 0` event is a boundary point.**  If `crossTau P ρ z i = 0` and the
edge-parameter `crossU` lies in `[0,1)` (so the crossing inequalities on `u`
hold), then `z` lies on the closed edge `Edge i`, hence on the boundary. -/
lemma crossTau_eq_zero_imp_onEdge (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (z : Pt) (i : Fin n) (hτ : crossTau P ρ z i = 0)
    (hu0 : 0 ≤ crossU P ρ z i) (hu1 : crossU P ρ z i < 1) :
    z ∈ Edge P.q i := by
  have hce := cross_eq P ρ z i
  rw [hτ, zero_smul, add_zero] at hce
  rw [Edge, seg, segment_eq_image_lineMap]
  exact ⟨crossU P ρ z i, ⟨hu0, le_of_lt hu1⟩, hce.symm⟩

/-! ## 3. Per-edge local constancy of the crossing status away from `u`-events

Along a boundary-free open segment, the `z ∉ Edge i` clause of `EdgeCrossesRay`
is automatically satisfied (interior points are off the boundary), so the
crossing status reduces to the three affine inequalities.  Each is affine — hence
continuous — in the segment parameter `t`, so the status is locally constant at
any `t₀` where none of the inequalities is at its threshold.  The `τ = 0`
threshold is excluded by boundary-freeness; the remaining `u ∈ {0,1}` thresholds
are the vertex-sweep events isolated in §4. -/

/-- Parameter functions: `uOf`, `tauOf` are the Cramer scalars along the segment,
as real-valued affine (hence continuous) functions of `t`. -/
def uOf (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt) (i : Fin n) :
    ℝ → ℝ :=
  fun t => crossU P ρ (AffineMap.lineMap x y t) i

def tauOf (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt) (i : Fin n) :
    ℝ → ℝ :=
  fun t => crossTau P ρ (AffineMap.lineMap x y t) i

lemma uOf_eq (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) (t : ℝ) :
    uOf P ρ x y i t =
      (1 - t) * crossU P ρ x i + t * crossU P ρ y i :=
  crossU_lineMap P ρ x y i t

lemma tauOf_eq (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) (t : ℝ) :
    tauOf P ρ x y i t =
      (1 - t) * crossTau P ρ x i + t * crossTau P ρ y i :=
  crossTau_lineMap P ρ x y i t

lemma continuous_uOf (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) : Continuous (uOf P ρ x y i) := by
  have : uOf P ρ x y i =
      fun t => (1 - t) * crossU P ρ x i + t * crossU P ρ y i := by
    funext t; exact uOf_eq P ρ x y i t
  rw [this]; fun_prop

lemma continuous_tauOf (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) : Continuous (tauOf P ρ x y i) := by
  have : tauOf P ρ x y i =
      fun t => (1 - t) * crossTau P ρ x i + t * crossTau P ρ y i := by
    funext t; exact tauOf_eq P ρ x y i t
  rw [this]; fun_prop

/-- The crossing status along the segment, as a predicate on `t`. -/
def statusOf (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt)
    (i : Fin n) : ℝ → Prop :=
  fun t => EdgeCrossesRay P ρ (AffineMap.lineMap x y t) i

/-- Off the boundary, the crossing status reduces to the three affine
inequalities (the `z ∉ Edge` clause is automatic). -/
lemma statusOf_iff_ineqs (P : StrictSimplePolygon n) (ρ : RayDirection P)
    {x y : Pt} (i : Fin n) {t : ℝ}
    (hoff : ¬ OnBoundary P (AffineMap.lineMap x y t)) :
    statusOf P ρ x y i t ↔
      0 ≤ tauOf P ρ x y i t ∧ 0 ≤ uOf P ρ x y i t ∧ uOf P ρ x y i t < 1 := by
  unfold statusOf uOf tauOf
  rw [edgeCrossesRay_iff]
  have hnot : AffineMap.lineMap x y t ∉ Edge P.q i := fun hmem => hoff ⟨i, hmem⟩
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨hnot, h⟩

/-- Near an interior parameter `t₀`, the segment point stays off the boundary
(`Ioo 0 1` is open and interior points are boundary-free). -/
lemma eventually_off_boundary (P : StrictSimplePolygon n) (_ρ : RayDirection P)
    {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ t in nhds t₀, ¬ OnBoundary P (AffineMap.lineMap x y t) := by
  have hopen : (Set.Ioo (0 : ℝ) 1) ∈ nhds t₀ :=
    IsOpen.mem_nhds isOpen_Ioo ht₀
  filter_upwards [hopen] with t ht
  have hz : AffineMap.lineMap x y t ∈ openSegment ℝ x y := by
    rw [openSegment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩
  exact hfree _ hz

/-- **Per-edge local constancy away from `u`-events (the unconditional core).**
At an interior parameter `t₀` where the edge-parameter `uOf … t₀` is neither `0`
nor `1`, the crossing status of edge `i` is locally constant. -/
lemma statusOf_eventually_eq_of_noEvent (P : StrictSimplePolygon n)
    (ρ : RayDirection P) {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    (i : Fin n) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hu0 : uOf P ρ x y i t₀ ≠ 0) (hu1 : uOf P ρ x y i t₀ ≠ 1) :
    ∀ᶠ t in nhds t₀, statusOf P ρ x y i t = statusOf P ρ x y i t₀ := by
  -- off boundary near t₀
  have hoffev := eventually_off_boundary P ρ hfree ht₀
  have hoff0 : ¬ OnBoundary P (AffineMap.lineMap x y t₀) :=
    hfree _ (by rw [openSegment_eq_image_lineMap]; exact ⟨t₀, ht₀, rfl⟩)
  -- continuity of the two affine parameters
  have hcu := continuous_uOf P ρ x y i
  have hctau := continuous_tauOf P ρ x y i
  set u₀ := uOf P ρ x y i t₀ with hu₀
  set τ₀ := tauOf P ρ x y i t₀ with hτ₀
  -- status at t₀ as the inequalities
  have hstat0 := statusOf_iff_ineqs P ρ i hoff0
  by_cases hcross : statusOf P ρ x y i t₀
  · -- true at t₀: all three strict (τ>0 via τ=0 excluded by boundary-freeness)
    rw [hstat0] at hcross
    obtain ⟨hτge, huge, hult⟩ := hcross
    -- u₀ ∈ (0,1) strictly
    have hu0pos : 0 < u₀ := lt_of_le_of_ne huge (Ne.symm hu0)
    -- τ₀ > 0: if τ₀ = 0 then z(t₀) ∈ Edge i (boundary), contradiction
    have hτpos : 0 < τ₀ := by
      rcases lt_or_eq_of_le hτge with h | h
      · exact h
      · exfalso
        apply hoff0
        exact ⟨i, crossTau_eq_zero_imp_onEdge P ρ _ i h.symm huge hult⟩
    -- neighborhoods where each strict inequality persists
    have ev_tau : ∀ᶠ t in nhds t₀, 0 < tauOf P ρ x y i t := by
      filter_upwards [(hctau.tendsto t₀).eventually_const_lt
        (show (0:ℝ) < τ₀ from hτpos)] with t ht using ht
    have ev_ulo : ∀ᶠ t in nhds t₀, 0 < uOf P ρ x y i t := by
      filter_upwards [(hcu.tendsto t₀).eventually_const_lt
        (show (0:ℝ) < u₀ from hu0pos)] with t ht using ht
    have ev_uhi : ∀ᶠ t in nhds t₀, uOf P ρ x y i t < 1 := by
      filter_upwards [(hcu.tendsto t₀).eventually_lt_const
        (show u₀ < (1:ℝ) from hult)] with t ht using ht
    filter_upwards [hoffev, ev_tau, ev_ulo, ev_uhi] with t hofft htau hulo huhi
    rw [eq_iff_iff]
    rw [statusOf_iff_ineqs P ρ i hofft]
    constructor
    · intro _; rw [hstat0]; exact ⟨hτge, huge, hult⟩
    · intro _; exact ⟨le_of_lt htau, le_of_lt hulo, huhi⟩
  · -- false at t₀: one of τ<0, u<0, u>1 holds strictly
    have hcross' : ¬ (0 ≤ τ₀ ∧ 0 ≤ u₀ ∧ u₀ < 1) := by
      rw [← statusOf_iff_ineqs P ρ i hoff0]; exact hcross
    -- determine which strict failure occurs (u₀ ≠ 0, ≠1)
    have hfail : τ₀ < 0 ∨ u₀ < 0 ∨ 1 < u₀ := by
      by_cases hτ : 0 ≤ τ₀
      · by_cases hu : 0 ≤ u₀
        · -- then need u₀ ≥ 1, and u₀ ≠ 1 ⇒ u₀ > 1
          have hge1 : 1 ≤ u₀ := by
            by_contra hlt
            exact hcross' ⟨hτ, hu, lt_of_not_ge hlt⟩
          exact Or.inr (Or.inr (lt_of_le_of_ne hge1 (Ne.symm hu1)))
        · exact Or.inr (Or.inl (lt_of_not_ge hu))
      · exact Or.inl (lt_of_not_ge hτ)
    -- in each case a strict open condition persists, keeping status false
    have evfalse : ∀ᶠ t in nhds t₀, ¬ (0 ≤ tauOf P ρ x y i t ∧
        0 ≤ uOf P ρ x y i t ∧ uOf P ρ x y i t < 1) := by
      rcases hfail with hτneg | hulo | huhi
      · filter_upwards [(hctau.tendsto t₀).eventually_lt_const
          (show τ₀ < (0:ℝ) from hτneg)] with t ht
        rintro ⟨hge, _, _⟩; linarith
      · filter_upwards [(hcu.tendsto t₀).eventually_lt_const
          (show u₀ < (0:ℝ) from hulo)] with t ht
        rintro ⟨_, hge, _⟩; linarith
      · filter_upwards [(hcu.tendsto t₀).eventually_const_lt
          (show (1:ℝ) < u₀ from huhi)] with t ht
        rintro ⟨_, _, hlt⟩; linarith
    filter_upwards [hoffev, evfalse] with t hofft hfalset
    rw [eq_iff_iff]
    rw [statusOf_iff_ineqs P ρ i hofft]
    constructor
    · intro h; exact absurd h hfalset
    · intro h; exact absurd h hcross

/-! ## 4. Finite assembly and the vertex-sweep residue

If at `t₀` *every* edge has locally constant crossing status, then the entire
crossing `Finset` (and hence the region indicator) is locally constant at `t₀`.
The only edges that can fail no-event status constancy are those at a vertex
sweep (`uOf … t₀ ∈ {0,1}`).  The vertex-sweep parity preservation — that the
half-open `[0,1)` convention swaps the two incident edges so the parity is
unchanged — is the single, design-sanctioned geometric residue, isolated as
`VertexSweepNeutral`. -/

/-- If every edge's crossing status is eventually constant at `t₀`, then the
crossing `Finset` is eventually constant at `t₀`. -/
lemma crossingEdges_eventually_eq (P : StrictSimplePolygon n) (ρ : RayDirection P)
    {x y : Pt} {t₀ : ℝ}
    (h : ∀ i : Fin n, ∀ᶠ t in nhds t₀,
        statusOf P ρ x y i t = statusOf P ρ x y i t₀) :
    ∀ᶠ t in nhds t₀,
      CrossingEdges P ρ (AffineMap.lineMap x y t) =
        CrossingEdges P ρ (AffineMap.lineMap x y t₀) := by
  classical
  -- finite conjunction of eventual equalities
  have hall : ∀ᶠ t in nhds t₀, ∀ i : Fin n,
      statusOf P ρ x y i t = statusOf P ρ x y i t₀ :=
    (Filter.eventually_all).2 h
  filter_upwards [hall] with t ht
  apply Finset.ext
  intro i
  rw [mem_crossingEdges_iff, mem_crossingEdges_iff]
  have := ht i
  unfold statusOf at this
  rw [eq_iff_iff] at this
  exact this

/-- The region indicator along the segment, as a predicate on `t`. -/
def regionOf (P : StrictSimplePolygon n) (ρ : RayDirection P) (x y : Pt) :
    ℝ → Prop :=
  fun t => ClosedRegion P ρ (AffineMap.lineMap x y t)

/-- If every edge's crossing status is eventually constant at an interior `t₀`,
then the region indicator is eventually constant at `t₀`. -/
lemma regionOf_eventually_eq_of_allEdges (P : StrictSimplePolygon n)
    (ρ : RayDirection P) {x y : Pt}
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h : ∀ i : Fin n, ∀ᶠ t in nhds t₀,
        statusOf P ρ x y i t = statusOf P ρ x y i t₀) :
    ∀ᶠ t in nhds t₀, regionOf P ρ x y t = regionOf P ρ x y t₀ := by
  have hce := crossingEdges_eventually_eq P ρ h
  have hoffev := eventually_off_boundary P ρ hfree ht₀
  have hoff0 : ¬ OnBoundary P (AffineMap.lineMap x y t₀) :=
    hfree _ (by rw [openSegment_eq_image_lineMap]; exact ⟨t₀, ht₀, rfl⟩)
  filter_upwards [hce, hoffev] with t hcet hofft
  unfold regionOf
  rw [eq_iff_iff]
  exact closedRegion_iff_of_crossingEdges_eq P ρ hofft hoff0 hcet

/-- **Vertex-sweep neutrality (the isolated geometric residue).**  At every
interior parameter `t₀` that is a *vertex-sweep event* — i.e. the ray through the
moving point passes through a polygon vertex, witnessed by some edge `i` with
`uOf … t₀ ∈ {0,1}` — the region indicator is still locally constant.  This is the
half-open `[0,1)` convention's parity-preservation across a vertex sweep: the two
incident edges swap crossing status, leaving the crossing-number parity (hence
region membership) unchanged.

Everything *away* from such events is discharged unconditionally above; this
predicate isolates exactly the vertex-sweep parity step that the round-2 design
names as the one genuine geometric residue of the ray-crossing substrate. -/
def VertexSweepNeutral (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x y : Pt) : Prop :=
  (∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z) →
    ∀ t₀ ∈ Set.Ioo (0 : ℝ) 1,
      (∃ i : Fin n, uOf P ρ x y i t₀ = 0 ∨ uOf P ρ x y i t₀ = 1) →
      ∀ᶠ t in nhds t₀, regionOf P ρ x y t = regionOf P ρ x y t₀

/-- **Region indicator eventually constant at every interior parameter.**
Combining the unconditional no-event per-edge constancy with the vertex-sweep
residue, the region indicator is locally constant at every interior `t₀`. -/
lemma regionOf_eventually_eq (P : StrictSimplePolygon n) (ρ : RayDirection P)
    {x y : Pt} (hsweep : VertexSweepNeutral P ρ x y)
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ t in nhds t₀, regionOf P ρ x y t = regionOf P ρ x y t₀ := by
  by_cases hevent : ∃ i : Fin n, uOf P ρ x y i t₀ = 0 ∨ uOf P ρ x y i t₀ = 1
  · -- vertex-sweep event: use the residue
    exact hsweep hfree t₀ ht₀ hevent
  · -- no event: every edge is no-event, discharge unconditionally
    have hno : ∀ i : Fin n, uOf P ρ x y i t₀ ≠ 0 ∧ uOf P ρ x y i t₀ ≠ 1 := by
      intro i
      exact ⟨fun h => hevent ⟨i, Or.inl h⟩, fun h => hevent ⟨i, Or.inr h⟩⟩
    apply regionOf_eventually_eq_of_allEdges P ρ hfree ht₀
    intro i
    exact statusOf_eventually_eq_of_noEvent P ρ hfree i ht₀
      (hno i).1 (hno i).2

/-! ## 5. The `loc` residue: `OpenSegmentRegionLocallyConstant`

Pulling the eventual-constancy back to the open parameter subtype `(0,1)` gives
`IsLocallyConstant`, which is exactly the `loc` residue consumed by
`PolygonResidues`. -/

/-- **The `loc` residue, discharged modulo the vertex-sweep neutrality.**  Given
`VertexSweepNeutral`, the open-segment region indicator is locally constant — the
`OpenSegmentRegionLocallyConstant` predicate `earTransversality_of` /
`slideTransversality_of` consume. -/
theorem openSegmentRegionLocallyConstant_of_sweepNeutral
    (P : StrictSimplePolygon n) (ρ : RayDirection P) {x y : Pt}
    (hsweep : VertexSweepNeutral P ρ x y) :
    OpenSegmentRegionLocallyConstant P ρ x y := by
  intro hfree
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  -- pull the ℝ-eventually constancy back along the continuous coercion
  have hev := regionOf_eventually_eq P ρ hsweep hfree s.2
  have htends : Filter.Tendsto (Subtype.val : Set.Ioo (0:ℝ) 1 → ℝ)
      (nhds s) (nhds (s : ℝ)) := continuous_subtype_val.tendsto s
  have := htends.eventually hev
  filter_upwards [this] with s' hs'
  -- `hs' : regionOf … (s'.val) = regionOf … (s.val)`
  exact hs'

/-! ## 6. Builders and the maximally-discharged A3 headline

The `loc` residue is now reduced to `VertexSweepNeutral`.  We rebuild the
`EarTransversality` / `SlideTransversality` structures and the slimmed A3
residue surface so that the A3 headlines flow through the *narrower* hypothesis
set in which `loc` is replaced by `VertexSweepNeutral` (everything else — the
finite-geometry `bdry`, the no-event local constancy — is discharged). -/

/-- Build `EarTransversality` from vertex-sweep neutrality and open-segment
edge-avoidance: `loc` comes from `openSegmentRegionLocallyConstant_of_sweepNeutral`
and `bdry` from `bdry_of_free`. -/
def earTransversality_of_sweep {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (i : Fin n)
    (hsweep : VertexSweepNeutral P ρ
      (P.q (cyclicPrev i)) (P.q (cyclicNext i)))
    (free : ∀ z ∈ openSegment ℝ (P.q (cyclicPrev i)) (P.q (cyclicNext i)),
      ¬ OnBoundary P z) :
    EarTransversality P ρ i :=
  earTransversality_of i
    (openSegmentRegionLocallyConstant_of_sweepNeutral P ρ hsweep) free

/-- Build `SlideTransversality` from vertex-sweep neutrality and open-segment
edge-avoidance. -/
def slideTransversality_of_sweep {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (i z : Fin n)
    (hsweep : VertexSweepNeutral P ρ (P.q i) (P.q z))
    (free : ∀ w ∈ openSegment ℝ (P.q i) (P.q z), ¬ OnBoundary P w) :
    SlideTransversality P ρ i z :=
  slideTransversality_of i z
    (openSegmentRegionLocallyConstant_of_sweepNeutral P ρ hsweep) free

/-- Slimmed A3 residue surface with `loc` replaced by `VertexSweepNeutral`.
Compared to `A3ResiduesSlim`, the local-constancy clause of each transversality
residue is replaced by the *strictly narrower* vertex-sweep neutrality
predicate; everything else (the `bdry` clause, the no-event part of local
constancy) is discharged.  This is the maximally-discharged residue surface for
the A3 diagonal/convex-vertex headlines. -/
structure A3ResiduesSweep (P : StrictSimplePolygon n) (ρ : RayDirection P) where
  extreme : ExtremeConvexResidue P ρ
  earSweep : ∀ i : Fin n, IsConvexVertex P ρ i →
    (∀ z : Fin n, z ≠ i → z ≠ cyclicPrev i → z ≠ cyclicNext i →
      P.q z ∉ adjacentTriangle P i) →
    VertexSweepNeutral P ρ (P.q (cyclicPrev i)) (P.q (cyclicNext i))
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
    VertexSweepNeutral P ρ (P.q i) (P.q z)
  slideFree : ∀ i z : Fin n, IsConvexVertex P ρ i →
    z ∈ verticesInAdjacentTriangle P i →
    (∀ w ∈ verticesInAdjacentTriangle P i,
      heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q w) ≤
        heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q z)) →
    ∀ w ∈ openSegment ℝ (P.q i) (P.q z), ¬ OnBoundary P w

/-- Convert the sweep-residue surface to the `loc`-based slimmed package by
discharging every `loc` clause through
`openSegmentRegionLocallyConstant_of_sweepNeutral`. -/
def a3ResiduesSlim_of_sweep {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (H : A3ResiduesSweep P ρ) : A3ResiduesSlim P ρ where
  extreme := H.extreme
  earLoc := fun i hconv hempty =>
    openSegmentRegionLocallyConstant_of_sweepNeutral P ρ
      (H.earSweep i hconv hempty)
  earFree := H.earFree
  slideLoc := fun i z hconv hz hmax =>
    openSegmentRegionLocallyConstant_of_sweepNeutral P ρ
      (H.slideSweep i z hconv hz hmax)
  slideFree := H.slideFree

/-- **A3 headline through the sweep-residue surface: existence of a convex
vertex.** -/
theorem exists_convex_vertex_sweep {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (H : A3ResiduesSweep P ρ) :
    ∃ i : Fin n, IsConvexVertex P ρ i :=
  exists_convex_vertex_slim (a3ResiduesSlim_of_sweep H)

/-- **A3 headline through the sweep-residue surface: existence of a diagonal**
(`4 ≤ n`).  Every strict simple polygon with at least four vertices has a
diagonal, with the *only* remaining geometric hypothesis being the vertex-sweep
parity neutrality `VertexSweepNeutral` at the relevant ear/slide bases (plus the
extreme-vertex convexity and the open-segment edge-avoidance `free`).  All of the
local-constancy machinery *away from* vertex sweeps, the half-open `τ = 0`
exclusion, and the `bdry` boundary-only-at-endpoints clause are discharged
unconditionally in this file. -/
theorem exists_diagonal_sweep {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (hn : 4 ≤ n) (H : A3ResiduesSweep P ρ) :
    ∃ i j : Fin n, IsDiagonal P ρ i j :=
  exists_diagonal_slim hn (a3ResiduesSlim_of_sweep H)

end

end ProofsInTheBook.PolygonLocalConstancy
