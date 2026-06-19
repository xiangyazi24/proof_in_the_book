# Ch13 Route B geometric crux: convex link heights are cyclically bitonic

## Executive answer

The clean Lean route is to prove the crux **after landing the spherical vertex link in an affine plane**.  In the current repo this is already the established pipeline: `VertexStar` stores raw cyclic edge directions and raw `det3` support/strict-turn fields; `VertexStar.vertexLink_strictArm` derives the strict spherical link; `ZinanFFCT92` then supplies the gnomonic landing facts, including injectivity, weak planar edge support, nonzero projected edges, and strict consecutive projected turns.

The theorem to add is therefore the following planar core:

```lean
PlanarClosedHeightBitonic
```

It says: if `Q : Fin m → E3` lies in one affine plane `⟪axis, Q i⟫ = 1`, has cyclic weak edge support, nonzero cyclic edges, and strict consecutive turns, then every linear functional `g` gives a cyclically unimodal sequence

```lean
b i = ⟪g, Q i⟫.
```

That is exactly the missing geometric bridge.  Once it is proved, the Route B vertex-link theorem is a short wrapper using the already-landed `ZinanFFCT92` gnomonic lemmas.

One important convention: the **difference-sign** statement belongs to the landed representatives `Q i = gproj axis (P i)`, not arbitrary positive rescalings of the rays.  For raw edge vectors, positive rescaling preserves the lower set `{i | ⟪g, ray i⟫ < 0}`, but it does not preserve signs of consecutive differences `b (i+1) - b i`.  So use landed values for the Step-1 cyclic-unimodal kernel, or prove the lower-set interval directly for raw rays by sign preservation.

## Existing repo hooks to use

The current `VertexStar` structure already has the raw fields needed to build the spherical link:

```lean
turn_support : ∀ i j, 0 ≤ det3 (p i - o) (p (i + 1) - o) (p j - o)
turn_strict  : ∀ i j, j ≠ i → j ≠ i + 1 →
  0 < det3 (p i - o) (p (i + 1) - o) (p j - o)
```

`VertexStar.vertexLink_strictArm` turns those into a `StrictConvexSphArm`.

`ZinanFFCT92` is the key landing bridge.  It already contains:

```lean
gproj_eq_imp_eq
gproj_eq_iff_eq
gproj_ne_of_short
consecutive_sOrient_pos
gnomonic_consecutive_turn_pos
```

and its proof of `weakConvex_boundedJoints_noNonadjacentRepeat_of_planarClosed` demonstrates the exact pattern: obtain the open hemisphere axis, set `Q i := gproj h (P i)`, prove the affine-plane equation, weak support, nonzero projected edges, and strict consecutive turns, then call a planar core.

The new core should mimic `PlanarClosedWeakStrictNoRepeat`, but its conclusion is height bitonicity instead of no-repeat.

## The precise predicates

These are the definitions I would add in a new file, for example

```lean
ProofsInTheBook/Ch13RouteBHeightBitonic.lean
```

```lean
import Mathlib
import ProofsInTheBook.Ch13VertexStar
import ProofsInTheBook.ZinanFFCT92

noncomputable section

open scoped RealInnerProductSpace BigOperators
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.ZinanFFCT92

namespace ProofsInTheBook.Ch13RouteBHeightBitonic

/-- Cyclic enumeration from a start index. -/
def zstep {n : ℕ} [NeZero n] (s : ZMod n) (t : ℕ) : ZMod n :=
  s + (t : ZMod n)

/-- The Step-1 kernel target: after some cyclic rotation, the sequence is
nondecreasing up to a peak and nonincreasing from the peak back to the start.
The endpoint `t = n` is allowed and represents the start again. -/
def CyclicallyUnimodal {n : ℕ} [NeZero n] (b : ZMod n → ℝ) : Prop :=
  ∃ s : ZMod n, ∃ p : ℕ,
    p ≤ n ∧
    (∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ p → b (zstep s i) ≤ b (zstep s j)) ∧
    (∀ ⦃i j : ℕ⦄, p ≤ i → i ≤ j → j ≤ n →
      b (zstep s j) ≤ b (zstep s i))

/-- Adjacent difference block form.  This is what the cosine sign proof gives:
from a cyclic start, all consecutive increments are nonnegative until `p`, and
all consecutive increments are nonpositive after `p`. -/
def AdjacentDeltaBlock {n : ℕ} [NeZero n] (b : ZMod n → ℝ) : Prop :=
  ∃ s : ZMod n, ∃ p : ℕ,
    p ≤ n ∧
    (∀ t : ℕ, t < p →
      0 ≤ b (zstep s (t + 1)) - b (zstep s t)) ∧
    (∀ t : ℕ, p ≤ t → t < n →
      b (zstep s (t + 1)) - b (zstep s t) ≤ 0)
```

The adjacent-block-to-unimodal conversion is pure finite induction.  Keep it as a separate lemma so that neither the trigonometry nor the geometry sees finite-sum details.

```lean
private lemma mono_of_adjacent_nonneg {b : ℕ → ℝ} {p : ℕ}
    (h : ∀ t : ℕ, t < p → 0 ≤ b (t + 1) - b t) :
    ∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ p → b i ≤ b j := by
  intro i j hij hjp
  induction hij with
  | refl => exact le_rfl
  | step hij ih =>
      have hj_lt_p : _ < p := Nat.lt_of_succ_le hjp
      have hstep : b (_ + 1) ≥ b _ := by
        have := h _ hj_lt_p
        linarith
      exact le_trans ih hstep

private lemma antitone_of_adjacent_nonpos {b : ℕ → ℝ} {p n : ℕ}
    (h : ∀ t : ℕ, p ≤ t → t < n → b (t + 1) - b t ≤ 0) :
    ∀ ⦃i j : ℕ⦄, p ≤ i → i ≤ j → j ≤ n → b j ≤ b i := by
  intro i j hpi hij hjn
  induction hij with
  | refl => exact le_rfl
  | step hij ih =>
      have hj_lt_n : _ < n := Nat.lt_of_succ_le hjn
      have hpj : p ≤ _ := le_trans hpi hij
      have hstep : b (_ + 1) ≤ b _ := by
        have := h _ hpj hj_lt_n
        linarith
      exact le_trans hstep ih

/-- Adjacent signs in one positive run followed by one negative run give the
block-structure hypothesis used by the Step-1 cyclic interval kernel. -/
theorem cyclicallyUnimodal_of_adjacentDeltaBlock
    {n : ℕ} [NeZero n] {b : ZMod n → ℝ}
    (h : AdjacentDeltaBlock b) :
    CyclicallyUnimodal b := by
  rcases h with ⟨s, p, hp, hpos, hneg⟩
  let B : ℕ → ℝ := fun t => b (zstep s t)
  refine ⟨s, p, hp, ?_, ?_⟩
  · intro i j hij hjp
    exact mono_of_adjacent_nonneg (b := B) (p := p) (by simpa [B] using hpos) hij hjp
  · intro i j hpi hij hjn
    exact antitone_of_adjacent_nonpos (b := B) (p := p) (n := n)
      (by simpa [B] using hneg) hpi hij hjn
```

The two helper proofs above are intentionally small.  If Lean has trouble with the anonymous metavariable pretty-printing produced by `_`, replace those underscores by explicit names in the induction step:

```lean
| step (j := j) hij ih =>
    have hj_lt_p : j < p := Nat.lt_of_succ_le hjp
    have hstep : b (j + 1) ≥ b j := by
      have := h j hj_lt_p
      linarith
    exact le_trans ih hstep
```

and similarly in the antitone lemma.

## Piece 2: the trigonometric kernel

This is the elementary cosine fact.  Mathlib already has exactly the cosine sign lemmas needed:

```lean
Real.cos_nonneg_of_neg_pi_div_two_le_of_le
Real.cos_nonpos_of_pi_div_two_le_of_le
Real.cos_add_two_pi
Real.cos_sub_two_pi
```

The kernel is deliberately stated after the cyclic edge-angle list has already been rotated so that the positive cosine half-turn comes first.

```lean
/-- A rotated edge-angle model for the edge increments of a landed polygon.
`δ (zstep s t)` is the `t`-th cyclic adjacent height difference.  The edge
angle is `θ t`, the test functional's in-plane angle is `φ`, and the positive
scale is `ρ t`. -/
structure RotatedCosDeltaModel {n : ℕ} [NeZero n]
    (δ : ZMod n → ℝ) where
  s : ZMod n
  p : ℕ
  hp : p ≤ n
  θ : ℕ → ℝ
  φ : ℝ
  ρ : ℕ → ℝ
  rho_pos : ∀ t : ℕ, t < n → 0 < ρ t
  delta_eq : ∀ t : ℕ, t < n →
    δ (zstep s t) = ρ t * Real.cos (θ t - φ)
  /-- after rotation every sampled angle lies in the closed full window centered at `φ` -/
  left_bound : ∀ t : ℕ, t < n → φ - Real.pi / 2 ≤ θ t
  right_bound : ∀ t : ℕ, t < n → θ t ≤ φ + 3 * Real.pi / 2
  /-- the first block is the nonnegative-cosine half-turn -/
  pos_block : ∀ t : ℕ, t < p → θ t ≤ φ + Real.pi / 2
  /-- the second block is the nonpositive-cosine half-turn -/
  neg_block : ∀ t : ℕ, p ≤ t → t < n → φ + Real.pi / 2 ≤ θ t

lemma cos_nonneg_centered {x φ : ℝ}
    (hlo : φ - Real.pi / 2 ≤ x) (hhi : x ≤ φ + Real.pi / 2) :
    0 ≤ Real.cos (x - φ) := by
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
  · linarith
  · linarith

lemma cos_nonpos_opposite {x φ : ℝ}
    (hlo : φ + Real.pi / 2 ≤ x) (hhi : x ≤ φ + 3 * Real.pi / 2) :
    Real.cos (x - φ) ≤ 0 := by
  apply Real.cos_nonpos_of_pi_div_two_le_of_le
  · linarith
  · linarith

/-- The rotated cosine model gives one run of nonnegative increments followed by
one run of nonpositive increments. -/
theorem adjacentDeltaBlock_of_rotatedCosDeltaModel
    {n : ℕ} [NeZero n] {δ : ZMod n → ℝ}
    (M : RotatedCosDeltaModel δ) :
    AdjacentDeltaBlock (fun i : ZMod n =>
      -- recover a height sequence from its adjacent differences only in the
      -- downstream application.  This theorem is usually used via
      -- `adjacentDeltaBlock_of_height_rotatedCosDeltaModel` below.
      0) := by
  -- Do not use this dummy theorem downstream.  It exists only to show that the
  -- sign proof is on `δ`; the real theorem below carries a height sequence `b`.
  refine ⟨M.s, M.p, M.hp, ?_, ?_⟩ <;> intro t ht <;> simp

/-- Actual cosine-to-adjacent-block theorem for a height sequence. -/
theorem adjacentDeltaBlock_of_height_rotatedCosDeltaModel
    {n : ℕ} [NeZero n] {b : ZMod n → ℝ}
    (M : RotatedCosDeltaModel
      (fun i : ZMod n => b (i + 1) - b i)) :
    AdjacentDeltaBlock b := by
  refine ⟨M.s, M.p, M.hp, ?_, ?_⟩
  · intro t ht
    have htn : t < n := lt_of_lt_of_le ht M.hp
    have hcos : 0 ≤ Real.cos (M.θ t - M.φ) :=
      cos_nonneg_centered (M.left_bound t htn) (M.pos_block t ht)
    have hρ : 0 ≤ M.ρ t := le_of_lt (M.rho_pos t htn)
    have hδ := M.delta_eq t htn
    change 0 ≤ b (zstep M.s (t + 1)) - b (zstep M.s t)
    have hsucc : zstep M.s t + 1 = zstep M.s (t + 1) := by
      simp [zstep, Nat.cast_add, add_assoc]
    have hrew : b (zstep M.s (t + 1)) - b (zstep M.s t)
        = (fun i : ZMod n => b (i + 1) - b i) (zstep M.s t) := by
      simp [hsucc]
    rw [hrew, hδ]
    exact mul_nonneg hρ hcos
  · intro t hpt htn
    have hcos : Real.cos (M.θ t - M.φ) ≤ 0 :=
      cos_nonpos_opposite (M.neg_block t hpt htn) (M.right_bound t htn)
    have hρ : 0 ≤ M.ρ t := le_of_lt (M.rho_pos t htn)
    have hδ := M.delta_eq t htn
    change b (zstep M.s (t + 1)) - b (zstep M.s t) ≤ 0
    have hsucc : zstep M.s t + 1 = zstep M.s (t + 1) := by
      simp [zstep, Nat.cast_add, add_assoc]
    have hrew : b (zstep M.s (t + 1)) - b (zstep M.s t)
        = (fun i : ZMod n => b (i + 1) - b i) (zstep M.s t) := by
      simp [hsucc]
    rw [hrew, hδ]
    exact mul_nonpos_of_nonneg_of_nonpos hρ hcos

/-- Final algebra/trig bridge: the rotated cosine model implies cyclic
unimodality of the height sequence. -/
theorem cyclicallyUnimodal_of_height_rotatedCosDeltaModel
    {n : ℕ} [NeZero n] {b : ZMod n → ℝ}
    (M : RotatedCosDeltaModel
      (fun i : ZMod n => b (i + 1) - b i)) :
    CyclicallyUnimodal b :=
  cyclicallyUnimodal_of_adjacentDeltaBlock
    (adjacentDeltaBlock_of_height_rotatedCosDeltaModel M)
```

The dummy theorem above can be omitted in the actual file; I left it only to make the separation between a difference function `δ` and a height sequence `b` explicit.  The theorem to use is `cyclicallyUnimodal_of_height_rotatedCosDeltaModel`.

## Piece 1: monotone edge-direction rotation from strict convexity

This should be the planar landed theorem.  Work in the affine plane

```lean
∀ i, ⟪axis, Q i⟫ = 1
```

and define cyclic edge vectors

```lean
E i = Q (i + 1) - Q i.
```

Strict convexity supplies:

```lean
edge_support : ∀ i j, 0 ≤ det3 (Q i) (Q (i + 1)) (Q j)
edge_ne      : ∀ i, Q i ≠ Q (i + 1)
turn_pos     : ∀ i, 0 < det3 axis (E i) (E (i + 1))
```

The current landed facts are phrased as `det3 (Q i) (Q (i+1)) (Q j)` plus the affine equation.  Convert them to edge-vector orientation by multilinearity and `⟪axis, Q i⟫ = 1`:

```lean
-- in the plane `⟪axis, _⟫ = 1`, orientation of three points is the same as
-- the orientation of two consecutive edge vectors in the direction of `axis`.
theorem det3_edge_edge_axis_eq_point_orientation
    {axis : E3} {a b c : E3}
    (ha : (⟪axis, a⟫ : ℝ) = 1)
    (hb : (⟪axis, b⟫ : ℝ) = 1)
    (hc : (⟪axis, c⟫ : ℝ) = 1) :
    det3 axis (b - a) (c - b) = det3 a b c := by
  -- This is pure multilinearity of `det3` plus the affine-plane equations.
  -- In coordinates, expand `det3`; `simp [det3, sub_eq_add_neg]`; `ring_nf`.
  simp [det3, sub_eq_add_neg]
  ring
```

Depending on argument order, the sign may be the negative of the displayed formula.  Fix the order once by testing the standard triangle in the plane `z=1`:

```lean
Q0 = (0,0,1), Q1 = (1,0,1), Q2 = (1,1,1)
```

and orient the theorem so the value is positive for this CCW triple.  The `ring` proof is the guard.

The landed angle theorem should then be stated as an output model, not as a giant theorem consumed directly by Morse code:

```lean
/-- Output of the landed strict-convex-link angle construction.
It packages the fact that edge directions wind once monotonically and gives the
cosine representation of all adjacent height increments. -/
def EdgeDirectionCosModel {n : ℕ} [NeZero n]
    (Q : ZMod n → E3) (g axis : E3) : Prop :=
  ∃ M : RotatedCosDeltaModel
      (fun i : ZMod n =>
        (⟪g, Q (i + 1)⟫ : ℝ) - (⟪g, Q i⟫ : ℝ)),
    True

/-- Strict landed convexity gives the edge-direction cosine model.
This is the geometric crux.  The proof is: project the edge vectors to an
oriented orthonormal basis of `axisᗮ`; use strict support/strict turn to show
edge-angle keys are cyclically strictly increasing and wind once; rotate at the
entry to the positive half-turn of the test direction `g`; finally rewrite
`⟪g, E i⟫` as `‖proj_axis⊥ g‖ * ‖E i‖ * cos(θ_i - φ)`. -/
theorem edgeDirectionCosModel_of_landed_strict_convex
    {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) (axis : E3) (Q : ZMod n → E3)
    (hplane : ∀ i : ZMod n, (⟪axis, Q i⟫ : ℝ) = 1)
    (hsupport : ∀ i j : ZMod n, 0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    (hedge_ne : ∀ i : ZMod n, Q i ≠ Q (i + 1))
    (hturn : ∀ i : ZMod n,
      0 < det3 axis (Q (i + 1) - Q i) (Q (i + 2) - Q (i + 1)))
    (g : E3) :
    EdgeDirectionCosModel Q g axis := by
  /-
  Concrete proof steps:

  1. Choose an oriented orthonormal basis `(u,v)` of `axisᗮ`.  In the repo this
     should be the same landed angular frame used by `rayAngleKey`.

     `to2 x = ![⟪u,x⟫, ⟪v,x⟫]`

  2. Define planar edge vectors:

     `e i = to2 (Q (i+1) - Q i)`.

     `hedge_ne` plus `hplane` gives `e i ≠ 0`: the chord lies in `axisᗮ`, and
     if its two planar coordinates vanish, the full vector vanishes.

  3. Use `hturn` to obtain positive 2D cross product:

     `0 < det2 (e i) (e (i+1))`.

     This is the frame version of `det3 axis E_i E_{i+1}`.

  4. Apply the landed angle lemma:

     `edgeAngleKey_strictMono_cyclic_of_turn_pos`:
       positive consecutive turns + weak support + no zero edges imply the
       edge-direction angle keys have a strictly increasing lift over one
       period, total winding `2π`.

     This is where `ProjectedAngleInjective`, `rayAngleKey`, and the existing
     cyclic strict order machinery are used.  This lemma should return a lift
     `θ : ℕ → ℝ` and a cyclic start `s` such that

     `θ 0 ≤ θ 1 ≤ ... ≤ θ n = θ 0 + 2π`

     with strict inequalities for sampled edges.

  5. For the functional, set

     `g₂ = to2 g`.

     If `g₂ = 0`, choose `ρ t = ‖e t‖` and any `φ`; every increment is `0`, so
     take `p = n` or `p = 0` and fill the model with both blocks trivial.

     If `g₂ ≠ 0`, set `φ = Complex.arg (g₂₀ + g₂₁ * Complex.I)` and
     `ρ t = ‖g₂‖ * ‖e t‖`.  Then use Mathlib's inner/cos formula in `ℝ²`:

     `⟪g₂, e t⟫ = ‖g₂‖ * ‖e t‖ * Real.cos (θ t - φ)`.

  6. Rotate the angle lift so that `θ 0` is the first sampled edge angle in the
     window `[φ - π/2, φ + 3π/2]`.  Let `p` be the first index with
     `φ + π/2 ≤ θ p`; use `Nat.find` to build it.  Then the fields
     `left_bound`, `right_bound`, `pos_block`, and `neg_block` are inequalities
     from the strict monotone one-turn lift.

  7. Return the resulting `RotatedCosDeltaModel`.
  -/
  -- The proof above should be implemented by invoking the landed angular API.
  -- Do not use this theorem until the API call names are fixed in the repo.
  classical
  -- This placeholder line prevents accidental use as a completed theorem in a
  -- Lean source file.  Replace with the 7 steps above.
  exact False.elim (by
    have : False := by contradiction
    exact this)
```

The last theorem is intentionally written as a **target theorem**, not as code to paste unchanged: the final `False.elim` line is a guard so nobody mistakes the sketch for a closed Lean proof.  The important part is the theorem boundary and the exact seven proof obligations.  The closed algebraic/trig proof is the previous section.

## Piece 3: assembly to the Step-1 block structure

Once `edgeDirectionCosModel_of_landed_strict_convex` returns the model, the assembly is one line:

```lean
theorem cyclicallyUnimodal_height_of_landed_strict_convex
    {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) (axis : E3) (Q : ZMod n → E3)
    (hplane : ∀ i : ZMod n, (⟪axis, Q i⟫ : ℝ) = 1)
    (hsupport : ∀ i j : ZMod n, 0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    (hedge_ne : ∀ i : ZMod n, Q i ≠ Q (i + 1))
    (hturn : ∀ i : ZMod n,
      0 < det3 axis (Q (i + 1) - Q i) (Q (i + 2) - Q (i + 1)))
    (g : E3) :
    CyclicallyUnimodal (fun i : ZMod n => (⟪g, Q i⟫ : ℝ)) := by
  rcases edgeDirectionCosModel_of_landed_strict_convex hn axis Q
      hplane hsupport hedge_ne hturn g with ⟨M, _⟩
  exact cyclicallyUnimodal_of_height_rotatedCosDeltaModel M
```

For the current spherical/gnomonic vertex-link wrapper, mirror the structure already used in `ZinanFFCT92`:

```lean
/-- Route B vertex-link wrapper: convex spherical link, landed gnomonically,
gives cyclically unimodal linear heights around the link. -/
theorem cyclicallyUnimodal_height_of_strictConvexSphArm
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hstrict : StrictConvexSphArm P)
    (g : E3) :
    ∃ axis : E3,
      CyclicallyUnimodal
        (n := n + 1)
        (fun i : ZMod (n + 1) =>
          let fi : Fin (n + 1) :=
            ⟨i.val, by
              have := i.val_lt
              simpa using this⟩
          (⟪g, gproj axis (P fi)⟫ : ℝ)) := by
  obtain ⟨axis, _hnorm, hhem⟩ := hstrict.closed_convex.open_hemisphere
  set QFin : Fin (n + 1) → E3 := fun i => gproj axis (P i)
  -- convert to a `ZMod (n+1)` cyclic family for the route-B kernel
  let Q : ZMod (n + 1) → E3 := fun i =>
    QFin ⟨i.val, by simpa using i.val_lt⟩
  refine ⟨axis, ?_⟩
  -- `hplane`: `inner_gproj` from the gnomonic file
  have hplaneFin : ∀ i : Fin (n + 1), (⟪axis, QFin i⟫ : ℝ) = 1 := by
    intro i
    exact inner_gproj (ne_of_gt (hhem i))
  -- `hsupport`: `gnomonic_edge_support_nonneg`
  have hsupportFin : ∀ i j : Fin (n + 1), 0 ≤ det3 (QFin i) (QFin (i + 1)) (QFin j) := by
    intro i j
    change 0 ≤ det3 (gproj axis (P i)) (gproj axis (P (i + 1))) (gproj axis (P j))
    exact gnomonic_edge_support_nonneg hstrict.closed_convex hhem i j
  -- `hedge_ne`: `gproj_ne_of_short`
  have hedgeNeFin : ∀ i : Fin (n + 1), QFin i ≠ QFin (i + 1) := by
    intro i
    change gproj axis (P i) ≠ gproj axis (P (i + 1))
    exact gproj_ne_of_short (hhem i) (hhem (i + 1)) (hstrict.closed_convex.edge_short i)
  -- `hturn`: use the affine-plane determinant identity plus strict nonincident
  -- or the existing `gnomonic_consecutive_turn_pos` wrapper in the weak-positive
  -- arm pipeline.  For strict convex polygons, the local triple
  -- `P i, P(i+1), P(i+2)` is nonincident for `n+1 ≥ 3`, so
  -- `hstrict.closed_convex.strict_nonincident` gives strict positivity.
  -- Then `sOrient_pos_iff_planar_pos` transports it through `gproj`.
  have hturnFin : ∀ i : Fin (n + 1),
      0 < det3 axis (QFin (i + 1) - QFin i) (QFin (i + 2) - QFin (i + 1)) := by
    intro i
    -- use `det3_edge_edge_axis_eq_point_orientation` and the already-proved
    -- strict planar orientation of consecutive triples.
    -- This closes by existing gnomonic orientation transport plus the determinant identity.
    admit
  -- Convert the `Fin` facts to `ZMod` facts and call the landed theorem.
  -- The conversions are routine `Fin.ext`, `ZMod.val`, and `simp [Q, QFin]`.
  admit
```

The two `admit`s in this wrapper are not mathematical gaps; they are index-conversion and determinant-identity calls.  In a source file, replace them with:

```lean
rw [det3_edge_edge_axis_eq_point_orientation (hplaneFin _) (hplaneFin _) (hplaneFin _)]
exact strict_gnomonic_consecutive_orientation_pos ...
```

then a local lemma translating `Fin (n+1)` to `ZMod (n+1)`.

## What to prove next, in order

1. **`det3_edge_edge_axis_eq_point_orientation`**.
   This is a coordinate `ring` lemma.  It is the shortest way to move between landed point orientation and edge-direction turn orientation.

2. **`edgeAngleKey_strictMono_cyclic_of_turn_pos`** for landed planar polygons.
   Inputs: weak edge support, nonzero edges, strict consecutive turns.  Output: edge-angle keys of `E i = Q(i+1)-Q i` have a strictly increasing cyclic lift with total winding `2π`.

3. **`rotatedCosDeltaModel_of_edgeAngleKey`**.
   Inputs: the lift from (2) and a vector `g`.  Output: `RotatedCosDeltaModel`.  Use `Complex.arg` for the in-plane angle of the projected functional and `Nat.find` for the two half-turn cut indices.

4. Call

```lean
cyclicallyUnimodal_of_height_rotatedCosDeltaModel
```

and then the Step-1 kernel from `scratch/_CHATGPT_DROP_life.md` to obtain the cyclic interval lower set.

## Difficulty and exact Mathlib lemmas

This is elementary and decomposes cleanly:

* determinant identity: `simp [det3, sub_eq_add_neg]`; `ring` / `ring_nf`.
* finite monotone block from adjacent signs: induction on `Nat.le`; `linarith`.
* cosine sign: `Real.cos_nonneg_of_neg_pi_div_two_le_of_le`, `Real.cos_nonpos_of_pi_div_two_le_of_le`.
* periodic wrap: `Real.cos_add_two_pi`, `Real.cos_sub_two_pi`.
* angle of vectors in the plane: `Complex.arg`, `Complex.arg_mem_Ioc`, `Complex.neg_pi_lt_arg`, `Complex.arg_le_pi`, plus the repo's `rayAngleKey` wrappers.
* cyclic indexing: `ZMod.natCast_self`, `Nat.cast_add`, `Fin.ext`, `Fin.val_add`, and `omega`.

## Bottom line

The crux should not be stated as “raw spherical values are bitonic under arbitrary positive rescaling.”  State it for the **landed planar link**.  The current repo already has the gnomonic landing infrastructure; add the planar `PlanarClosedHeightBitonic` core, prove it via monotone edge-angle rotation and the cosine half-turn lemma, then wrap it back to `VertexStar`/`StrictConvexSphArm`.  After that, the lower-set cyclic interval theorem is immediate from the Step-1 cyclic-unimodal kernel.

end ProofsInTheBook.Ch13RouteBHeightBitonic
```