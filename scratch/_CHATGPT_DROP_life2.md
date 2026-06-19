# Ch13 Route B geometric crux: convex landed link heights are cyclically bitonic

## Bottom line

Prove the crux for the **landed planar link**, not for arbitrary positive rescalings of the rays.  This is the clean Lean statement:

> A cyclically ordered landed strictly convex polygon `Q` in one affine plane has the property that every linear height sequence `b i = ⟪g, Q i⟫` is cyclically unimodal.  Equivalently, after one cyclic rotation, adjacent differences are nonnegative for one block and nonpositive for the complementary block.

Then the lower-neighbor set is a cyclic interval by the Step-1 kernel in `scratch/_CHATGPT_DROP_life.md`.

The current repo already has the geometry-to-landed-plane bridge:

* `VertexStar` stores raw `turn_support` and `turn_strict` as determinant inequalities on raw edge directions.
* `VertexStar.vertexLink_strictArm` derives the strict spherical vertex link from that raw data.
* `ZinanFFCT92` already lands spherical links gnomonically: `gproj_eq_imp_eq`, `gproj_ne_of_short`, `gnomonic_edge_support_nonneg`, and `gnomonic_consecutive_turn_pos` are the exact pattern to reuse.

The one new geometric theorem to add is a planar core, parallel to the existing `PlanarClosedWeakStrictNoRepeat` core:

```lean
PlanarClosedHeightBitonic
```

It should consume affine-plane membership, weak cyclic edge support, nonzero cyclic edges, and strict consecutive turns, and output `CyclicallyUnimodal (fun i => ⟪g, Q i⟫)` for every `g`.

Important convention: for raw edge vectors, positive rescaling preserves the sign lower set `{i | ⟪g, ray i⟫ < 0}`, but it does **not** preserve signs of differences `b (i+1) - b i`.  Therefore the difference-sign/bitonic proof belongs to the landed representatives `Q i = gproj axis (P i)` or an equivalent fixed affine section.

## Closed Lean kernel: adjacent sign blocks imply cyclic unimodality

This is the pure combinatorial piece used after the cosine proof.  It is independent of geometry.

```lean
import Mathlib

noncomputable section

open scoped BigOperators

namespace ProofsInTheBook.Ch13RouteBHeightBitonic

/-- Cyclic enumeration from a start index. -/
def zstep {n : ℕ} [NeZero n] (s : ZMod n) (t : ℕ) : ZMod n :=
  s + (t : ZMod n)

/-- After some cyclic rotation, the sequence is nondecreasing up to a peak and
nonincreasing from the peak back to the start.  The endpoint `t = n` represents
`zstep s 0` again. -/
def CyclicallyUnimodal {n : ℕ} [NeZero n] (b : ZMod n → ℝ) : Prop :=
  ∃ s : ZMod n, ∃ p : ℕ,
    p ≤ n ∧
    (∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ p → b (zstep s i) ≤ b (zstep s j)) ∧
    (∀ ⦃i j : ℕ⦄, p ≤ i → i ≤ j → j ≤ n →
      b (zstep s j) ≤ b (zstep s i))

/-- Adjacent block form: one run of nonnegative increments, then one run of
nonpositive increments. -/
def AdjacentDeltaBlock {n : ℕ} [NeZero n] (b : ZMod n → ℝ) : Prop :=
  ∃ s : ZMod n, ∃ p : ℕ,
    p ≤ n ∧
    (∀ t : ℕ, t < p →
      0 ≤ b (zstep s (t + 1)) - b (zstep s t)) ∧
    (∀ t : ℕ, p ≤ t → t < n →
      b (zstep s (t + 1)) - b (zstep s t) ≤ 0)

private lemma mono_of_adjacent_nonneg {b : ℕ → ℝ} {p : ℕ}
    (h : ∀ t : ℕ, t < p → 0 ≤ b (t + 1) - b t) :
    ∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ p → b i ≤ b j := by
  intro i j hij hjp
  induction hij with
  | refl => exact le_rfl
  | step hle ih =>
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
  | step hle ih =>
      have hj_lt_n : _ < n := Nat.lt_of_succ_le hjn
      have hpj : p ≤ _ := le_trans hpi hle
      have hstep : b (_ + 1) ≤ b _ := by
        have := h _ hpj hj_lt_n
        linarith
      exact le_trans hstep ih

/-- Adjacent sign blocks imply the Step-1 cyclic-unimodal block structure. -/
theorem cyclicallyUnimodal_of_adjacentDeltaBlock
    {n : ℕ} [NeZero n] {b : ZMod n → ℝ}
    (h : AdjacentDeltaBlock b) :
    CyclicallyUnimodal b := by
  rcases h with ⟨s, p, hp, hpos, hneg⟩
  let B : ℕ → ℝ := fun t => b (zstep s t)
  refine ⟨s, p, hp, ?_, ?_⟩
  · intro i j hij hjp
    exact mono_of_adjacent_nonneg (b := B) (p := p)
      (by intro t ht; simpa [B] using hpos t ht) hij hjp
  · intro i j hpi hij hjn
    exact antitone_of_adjacent_nonpos (b := B) (p := p) (n := n)
      (by intro t hpt htn; simpa [B] using hneg t hpt htn) hpi hij hjn
```

If Lean reports trouble with the anonymous `_` names inside the two private induction lemmas, replace the induction cases by named versions:

```lean
| step (j := j) hle ih =>
    have hj_lt_p : j < p := Nat.lt_of_succ_le hjp
    have hstep : b (j + 1) ≥ b j := by
      have := h j hj_lt_p
      linarith
    exact le_trans ih hstep
```

and similarly for the antitone lemma.  The proof itself is just induction on `i ≤ j`.

## Closed Lean kernel: cosine half-turn signs give the adjacent block

The trigonometric core should be stated after the edge-angle list has been cyclically rotated so that the positive cosine half-turn comes first.

```lean
/-- Rotated cosine model for adjacent height differences.

`δ (zstep s t)` is the `t`-th adjacent difference.  `θ t` is the landed edge
angle, `φ` is the in-plane direction angle of the projected functional, and
`ρ t > 0` is the positive scale `‖proj g‖ * ‖edge t‖`. -/
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
  left_bound : ∀ t : ℕ, t < n → φ - Real.pi / 2 ≤ θ t
  right_bound : ∀ t : ℕ, t < n → θ t ≤ φ + 3 * Real.pi / 2
  pos_block : ∀ t : ℕ, t < p → θ t ≤ φ + Real.pi / 2
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

/-- The rotated cosine model for the adjacent differences of a height sequence
produces one nonnegative run followed by one nonpositive run. -/
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
    have hsucc : zstep M.s t + 1 = zstep M.s (t + 1) := by
      simp [zstep, Nat.cast_add, add_assoc]
    change 0 ≤ b (zstep M.s (t + 1)) - b (zstep M.s t)
    calc
      0 ≤ M.ρ t * Real.cos (M.θ t - M.φ) := mul_nonneg hρ hcos
      _ = (fun i : ZMod n => b (i + 1) - b i) (zstep M.s t) := by
        rw [← hδ]
      _ = b (zstep M.s (t + 1)) - b (zstep M.s t) := by
        simp [hsucc]
  · intro t hpt htn
    have hcos : Real.cos (M.θ t - M.φ) ≤ 0 :=
      cos_nonpos_opposite (M.neg_block t hpt htn) (M.right_bound t htn)
    have hρ : 0 ≤ M.ρ t := le_of_lt (M.rho_pos t htn)
    have hδ := M.delta_eq t htn
    have hsucc : zstep M.s t + 1 = zstep M.s (t + 1) := by
      simp [zstep, Nat.cast_add, add_assoc]
    change b (zstep M.s (t + 1)) - b (zstep M.s t) ≤ 0
    calc
      b (zstep M.s (t + 1)) - b (zstep M.s t)
          = (fun i : ZMod n => b (i + 1) - b i) (zstep M.s t) := by
            simp [hsucc]
      _ = M.ρ t * Real.cos (M.θ t - M.φ) := hδ
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ hcos

/-- Final trig/combinatorics bridge. -/
theorem cyclicallyUnimodal_of_height_rotatedCosDeltaModel
    {n : ℕ} [NeZero n] {b : ZMod n → ℝ}
    (M : RotatedCosDeltaModel
      (fun i : ZMod n => b (i + 1) - b i)) :
    CyclicallyUnimodal b :=
  cyclicallyUnimodal_of_adjacentDeltaBlock
    (adjacentDeltaBlock_of_height_rotatedCosDeltaModel M)

end ProofsInTheBook.Ch13RouteBHeightBitonic
```

This is the reusable no-geometry kernel.  The only trig lemmas used are exactly:

```lean
Real.cos_nonneg_of_neg_pi_div_two_le_of_le
Real.cos_nonpos_of_pi_div_two_le_of_le
```

For wrap normalization in the edge-angle construction, use:

```lean
Real.cos_add_two_pi
Real.cos_sub_two_pi
```

## Geometric planar core to add

Add this as a proposition/theorem boundary next to the existing planar gnomonic core.  It is the precise geometric crux.

```lean
/-- Planar landed height-bitonic core.

A cyclic landed strictly convex polygon in the affine plane `⟪axis, x⟫ = 1`
has cyclically unimodal heights for every linear functional. -/
def PlanarClosedHeightBitonic : Prop :=
  ∀ {m : ℕ} [NeZero m], 3 ≤ m →
  ∀ (axis : E3) (Q : ZMod m → E3),
    (∀ i : ZMod m, (⟪axis, Q i⟫ : ℝ) = 1) →
    (∀ i j : ZMod m, 0 ≤ det3 (Q i) (Q (i + 1)) (Q j)) →
    (∀ i : ZMod m, Q i ≠ Q (i + 1)) →
    (∀ i : ZMod m,
      0 < det3 axis (Q (i + 1) - Q i) (Q (i + 2) - Q (i + 1))) →
    ∀ g : E3,
      CyclicallyUnimodal (fun i : ZMod m => (⟪g, Q i⟫ : ℝ))
```

The proof of `PlanarClosedHeightBitonic` is the three-step route below.

### Step A: point orientation equals edge-turn orientation

In the affine plane `⟪axis, x⟫ = 1`, the orientation of consecutive point triples is the orientation of consecutive edge vectors around `axis`.  The exact sign depends on the argument order of `det3`; fix it by checking the standard CCW triangle in the plane `z = 1`.

Target lemma:

```lean
theorem det3_axis_edge_edge_eq_det3_point
    {axis a b c : E3}
    (ha : (⟪axis, a⟫ : ℝ) = 1)
    (hb : (⟪axis, b⟫ : ℝ) = 1)
    (hc : (⟪axis, c⟫ : ℝ) = 1) :
    det3 axis (b - a) (c - b) = det3 a b c := by
  -- With the repo's coordinate definition of `det3`, this is pure algebra.
  -- If the sign is opposite for the chosen `det3` order, swap the two edge
  -- arguments and keep this lemma as the sign guard.
  simp [det3, sub_eq_add_neg]
  ring
```

If `ring` does not close because the affine equations are not used by `simp`, expand `det3`, rewrite the three inner-product equations in coordinates for the chosen orthonormal frame of the landed plane, and then use `ring_nf`.  In the gnomonic setup, `axis` is the landing normal and `inner_gproj` gives the affine equation.

### Step B: strict convexity gives monotone edge-angle rotation

Define landed edge vectors

```lean
E i = Q (i + 1) - Q i.
```

Project them to an oriented orthonormal basis `(u,v)` of `axisᗮ`:

```lean
to2 x = ![⟪u, x⟫, ⟪v, x⟫]
e2 i = to2 (E i)
```

Then prove:

```lean
theorem edgeAngleLift_strictMono_of_landed_strict_convex
    {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (axis : E3) (Q : ZMod m → E3)
    (hplane : ∀ i, (⟪axis, Q i⟫ : ℝ) = 1)
    (hsupport : ∀ i j, 0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    (hedge_ne : ∀ i, Q i ≠ Q (i + 1))
    (hturn : ∀ i,
      0 < det3 axis (Q (i + 1) - Q i) (Q (i + 2) - Q (i + 1))) :
    ∃ θ : ℕ → ℝ,
      (∀ t : ℕ, t < m →
        θ t = rayAngleKey (to2 (Q (t + 1 : ZMod m) - Q (t : ZMod m)))) ∧
      StrictMonoOn θ (Set.Iio m) ∧
      θ m = θ 0 + 2 * Real.pi :=
by
  -- This is the landed angular lemma.  It uses:
  -- * `hedge_ne` to show each edge direction is nonzero;
  -- * `hturn` to show consecutive edge directions turn positively;
  -- * `hsupport` to rule out wrap/backtracking and force total winding one;
  -- * `ProjectedAngleInjective` / `rayAngleKey` to turn positive determinants
  --   into strict increase of the lifted angle keys.
  -- The proof should be implemented in the landed-angle file, not in the
  -- discrete-Morse file.
  exact edgeAngleLift_strictMono_cyclic_of_turn_pos hm axis Q hplane hsupport hedge_ne hturn
```

The final line names the lemma to expose from the landed-angle file.  If the existing file uses a different name, make this theorem the compatibility wrapper and keep all downstream code depending on this statement only.

### Step C: monotone one-turn edge angles give the rotated cosine model

For `g`, project it to the same `axisᗮ` frame.  If the planar projection is zero, every adjacent height difference is zero and the model is trivial.  Otherwise set

```lean
φ = Complex.arg (g₂ 0 + g₂ 1 * Complex.I)
ρ t = ‖g₂‖ * ‖e2 t‖
```

and prove

```lean
⟪g, Q (i+1) - Q i⟫ = ρ i * Real.cos (θ i - φ)
```

using the usual real inner-product angle formula in `ℝ²`.  Rotate the one-turn lift so the first sampled edge lies at the entry to the positive half-turn `[φ - π/2, φ + π/2]`, and choose `p` as the first sampled edge at or after `φ + π/2`.  `Nat.find` gives the cut index.  The resulting inequalities are exactly the fields of `RotatedCosDeltaModel`.

Target wrapper:

```lean
theorem rotatedCosDeltaModel_of_landed_strict_convex
    {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (axis : E3) (Q : ZMod m → E3)
    (hplane : ∀ i, (⟪axis, Q i⟫ : ℝ) = 1)
    (hsupport : ∀ i j, 0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    (hedge_ne : ∀ i, Q i ≠ Q (i + 1))
    (hturn : ∀ i,
      0 < det3 axis (Q (i + 1) - Q i) (Q (i + 2) - Q (i + 1)))
    (g : E3) :
    RotatedCosDeltaModel
      (fun i : ZMod m =>
        (⟪g, Q (i + 1)⟫ : ℝ) - (⟪g, Q i⟫ : ℝ)) := by
  -- 1. obtain the one-turn strict angle lift from Step B;
  -- 2. project `g` to the landed plane;
  -- 3. handle `g₂ = 0` by the all-zero model;
  -- 4. otherwise use `Complex.arg` and the inner-product/cosine formula;
  -- 5. rotate at the positive-halfturn entry and define the cut by `Nat.find`.
  exact rotatedCosDeltaModel_of_edgeAngleLift hm axis Q hplane hsupport hedge_ne hturn g
```

Again, expose `rotatedCosDeltaModel_of_edgeAngleLift` from the landed-angle file.  Its body is finite order/trig bookkeeping; the cosine sign conclusion is already closed above.

Then the planar core is one line:

```lean
theorem planarClosedHeightBitonic : PlanarClosedHeightBitonic := by
  intro m _ hm axis Q hplane hsupport hedge_ne hturn g
  exact cyclicallyUnimodal_of_height_rotatedCosDeltaModel
    (rotatedCosDeltaModel_of_landed_strict_convex
      hm axis Q hplane hsupport hedge_ne hturn g)
```

## Route B wrapper from `StrictConvexSphArm`

Mirror the already-working pattern in `ZinanFFCT92`:

```lean
theorem cyclicallyUnimodal_height_of_strictConvexSphArm
    (hplanar : PlanarClosedHeightBitonic)
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hstrict : StrictConvexSphArm P) (g : E3) :
    ∃ axis : E3,
      CyclicallyUnimodal
        (n := n + 1)
        (fun i : ZMod (n + 1) =>
          let fi : Fin (n + 1) := ⟨i.val, by simpa using i.val_lt⟩
          (⟪g, gproj axis (P fi)⟫ : ℝ)) := by
  obtain ⟨axis, _hnorm, hhem⟩ := hstrict.closed_convex.open_hemisphere
  set QFin : Fin (n + 1) → E3 := fun i => gproj axis (P i)
  let Q : ZMod (n + 1) → E3 := fun i => QFin ⟨i.val, by simpa using i.val_lt⟩
  refine ⟨axis, ?_⟩
  -- Build the four planar hypotheses by the existing gnomonic lemmas:
  -- * plane: `inner_gproj (ne_of_gt (hhem i))`
  -- * support: `gnomonic_edge_support_nonneg hstrict.closed_convex hhem i j`
  -- * edge nonzero: `gproj_ne_of_short (hhem i) (hhem (i+1)) ...`
  -- * strict turns: strict nonincident + `sOrient_pos_iff_planar_pos` +
  --   `det3_axis_edge_edge_eq_det3_point`.
  -- Then convert `Fin` statements to `ZMod` statements by `Fin.ext`/`simp [Q]`.
  exact hplanar hstrict.closed_convex.three_le axis Q
    (by intro i; exact inner_gproj (ne_of_gt (hhem ⟨i.val, by simpa using i.val_lt⟩)))
    (by
      intro i j
      -- `simp [Q, QFin]` then existing support lemma.
      simpa [Q, QFin] using
        gnomonic_edge_support_nonneg hstrict.closed_convex hhem
          ⟨i.val, by simpa using i.val_lt⟩
          ⟨j.val, by simpa using j.val_lt⟩)
    (by
      intro i
      -- `simp [Q, QFin]` then `gproj_ne_of_short`.
      simpa [Q, QFin] using
        gproj_ne_of_short
          (hhem ⟨i.val, by simpa using i.val_lt⟩)
          (hhem (⟨i.val, by simpa using i.val_lt⟩ + 1))
          (hstrict.closed_convex.edge_short ⟨i.val, by simpa using i.val_lt⟩))
    (by
      intro i
      -- Convert the strict orientation of the consecutive landed triple into
      -- edge-turn form.  Use `det3_axis_edge_edge_eq_det3_point` and the
      -- gnomonic strict orientation transport.
      -- This is the only index-heavy line in the wrapper.
      exact strict_landed_edge_turn_pos_of_strictConvex hstrict hhem i)
    g
```

The wrapper is intentionally factored through `PlanarClosedHeightBitonic`, just as `ZinanFFCT92` factors through `PlanarClosedWeakStrictNoRepeat`.  The only new wrapper helper is:

```lean
strict_landed_edge_turn_pos_of_strictConvex
```

whose proof is exactly: strict spherical orientation of `P i, P(i+1), P(i+2)`; transport by `sOrient_pos_iff_planar_pos`; rewrite point orientation as edge-turn orientation by `det3_axis_edge_edge_eq_det3_point`.

## Summary of the proof dependency chain

```text
VertexStar.turn_support / turn_strict
  ⟹ VertexStar.vertexLink_strictArm
  ⟹ gnomonic landed polygon Q in plane ⟪axis,Q⟫=1
  ⟹ weak support + nonzero edges + strict turns for Q
  ⟹ monotone one-turn edge-angle lift for E_i = Q_{i+1}-Q_i
  ⟹ sign(⟪g,E_i⟫) is + block then - block by cosine half-turn
  ⟹ b_i = ⟪g,Q_i⟫ is cyclically unimodal
  ⟹ {i | b_i < c} is a cyclic interval by Step-1
```

This is elementary, local, and fully modular.  The real geometric crux is the landed planar theorem `edgeAngleLift_strictMono_of_landed_strict_convex`; after that, everything is `Real.cos` inequalities, `Nat.find`, and cyclic index simplification.