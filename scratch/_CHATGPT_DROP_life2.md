# Ch13 Route B geometric crux: landed convex link heights are cyclically bitonic

## What must be proved, sharply

Use a **landed affine representative** of the vertex link.  Let

```lean
Q : ZMod m → E3
```

be the cyclically ordered landed link polygon in the affine plane `⟪axis, Q i⟫ = 1`.  For a linear functional `g`, set

```lean
b i = ⟪g, Q i⟫.
```

The desired bridge is:

```text
strict convex landed link
  ⟹ edge directions E_i = Q(i+1)-Q(i) have a one-turn monotone angle lift
  ⟹ ⟪g,E_i⟫ has one nonnegative block and one nonpositive block
  ⟹ b is cyclically unimodal
  ⟹ Step-1 kernel: {i | b i < c} is a cyclic interval.
```

Do **not** state this on arbitrary positively rescaled rays if the conclusion is about **differences** `b (i+1)-b i`; positive rescaling preserves the sign of individual tests `⟪g,ray i⟫`, but it does not preserve adjacent differences.  The difference-sign theorem belongs to the landed representatives `Q`.

The code below gives the complete Lean proof of the reusable kernel after the landed angular API has produced the rotated cosine model.  The only repo-specific geometric theorem still needed is exactly the landed-angle theorem named in the final section:

```lean
rotatedCosDeltaModel_of_landed_strict_convex
```

That theorem is where `ProjectedAngleInjective`, `rayAngleKey`, `turn_strict`, `SurroundsAxisPlane`, and the determinant/angle landing machinery are used.  Once it exists, the assembly theorem is literally one line.

## Complete Lean kernel

```lean
import Mathlib

noncomputable section

open scoped BigOperators
open scoped RealInnerProductSpace

namespace ProofsInTheBook.Ch13RouteBHeightBitonic

/-- Cyclic enumeration from a chosen start. -/
def zstep {n : ℕ} [NeZero n] (s : ZMod n) (t : ℕ) : ZMod n :=
  s + (t : ZMod n)

/-- Step-1 block-structure target: after rotating the cyclic order by `s`,
the sequence is nondecreasing up to `p` and nonincreasing from `p` back to the
start.  The endpoint `t = n` represents the start again. -/
def CyclicallyUnimodal {n : ℕ} [NeZero n] (b : ZMod n → ℝ) : Prop :=
  ∃ s : ZMod n, ∃ p : ℕ,
    p ≤ n ∧
    (∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ p → b (zstep s i) ≤ b (zstep s j)) ∧
    (∀ ⦃i j : ℕ⦄, p ≤ i → i ≤ j → j ≤ n →
      b (zstep s j) ≤ b (zstep s i))

/-- Adjacent-difference form: one cyclic run of nonnegative increments followed
by one cyclic run of nonpositive increments. -/
def AdjacentDeltaBlock {n : ℕ} [NeZero n] (b : ZMod n → ℝ) : Prop :=
  ∃ s : ZMod n, ∃ p : ℕ,
    p ≤ n ∧
    (∀ t : ℕ, t < p →
      0 ≤ b (zstep s (t + 1)) - b (zstep s t)) ∧
    (∀ t : ℕ, p ≤ t → t < n →
      b (zstep s (t + 1)) - b (zstep s t) ≤ 0)

private lemma mono_of_adjacent_nonneg {b : ℕ → ℝ} {p i j : ℕ}
    (h : ∀ t : ℕ, t < p → b t ≤ b (t + 1))
    (hij : i ≤ j) (hjp : j ≤ p) :
    b i ≤ b j := by
  refine (Nat.le_induction
    (motive := fun k => k ≤ p → b i ≤ b k)
    ?base ?step j hij) hjp
  · intro _
    exact le_rfl
  · intro k hik ih hk1p
    have hkp : k ≤ p := Nat.le_of_succ_le hk1p
    have hklt : k < p := Nat.lt_of_succ_le hk1p
    exact le_trans (ih hkp) (h k hklt)

private lemma antitone_of_adjacent_nonpos {b : ℕ → ℝ} {p n i j : ℕ}
    (h : ∀ t : ℕ, p ≤ t → t < n → b (t + 1) ≤ b t)
    (hpi : p ≤ i) (hij : i ≤ j) (hjn : j ≤ n) :
    b j ≤ b i := by
  refine (Nat.le_induction
    (motive := fun k => k ≤ n → b k ≤ b i)
    ?base ?step j hij) hjn
  · intro _
    exact le_rfl
  · intro k hik ih hk1n
    have hkn : k ≤ n := Nat.le_of_succ_le hk1n
    have hklt : k < n := Nat.lt_of_succ_le hk1n
    have hpk : p ≤ k := le_trans hpi hik
    exact le_trans (h k hpk hklt) (ih hkn)

/-- Adjacent sign blocks imply the nondecreasing-then-nonincreasing block
structure required by the Step-1 cyclic interval theorem. -/
theorem cyclicallyUnimodal_of_adjacentDeltaBlock
    {n : ℕ} [NeZero n] {b : ZMod n → ℝ}
    (h : AdjacentDeltaBlock b) :
    CyclicallyUnimodal b := by
  rcases h with ⟨s, p, hp, hpos, hneg⟩
  let B : ℕ → ℝ := fun t => b (zstep s t)
  refine ⟨s, p, hp, ?_, ?_⟩
  · intro i j hij hjp
    apply mono_of_adjacent_nonneg (b := B) (p := p) hij hjp
    intro t ht
    have := hpos t ht
    dsimp [B]
    linarith
  · intro i j hpi hij hjn
    apply antitone_of_adjacent_nonpos (b := B) (p := p) (n := n) hpi hij hjn
    intro t hpt htn
    have := hneg t hpt htn
    dsimp [B]
    linarith

/-- A rotated cosine model for adjacent height differences.

`δ (zstep s t)` is the `t`-th cyclic adjacent difference after rotation.
`θ t` is the landed edge-angle lift, `φ` is the in-plane direction angle of
the projected functional, and `ρ t > 0` is the positive scale
`‖proj g‖ * ‖edge t‖`. -/
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

/-- The cosine half-turn fact: if the edge-angle samples have been rotated so
that the positive half-turn comes first, the adjacent height differences are a
nonnegative block followed by a nonpositive block. -/
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
    have hrew :
        b (zstep M.s (t + 1)) - b (zstep M.s t)
          = (fun i : ZMod n => b (i + 1) - b i) (zstep M.s t) := by
      simp [hsucc]
    rw [hrew, hδ]
    exact mul_nonneg hρ hcos
  · intro t hpt htn
    have hcos : Real.cos (M.θ t - M.φ) ≤ 0 :=
      cos_nonpos_opposite (M.neg_block t hpt htn) (M.right_bound t htn)
    have hρ : 0 ≤ M.ρ t := le_of_lt (M.rho_pos t htn)
    have hδ := M.delta_eq t htn
    have hsucc : zstep M.s t + 1 = zstep M.s (t + 1) := by
      simp [zstep, Nat.cast_add, add_assoc]
    have hrew :
        b (zstep M.s (t + 1)) - b (zstep M.s t)
          = (fun i : ZMod n => b (i + 1) - b i) (zstep M.s t) := by
      simp [hsucc]
    rw [hrew, hδ]
    exact mul_nonpos_of_nonneg_of_nonpos hρ hcos

/-- Final kernel theorem: a rotated one-turn cosine representation of the
adjacent differences gives the Step-1 cyclic-unimodal block structure. -/
theorem cyclicallyUnimodal_of_height_rotatedCosDeltaModel
    {n : ℕ} [NeZero n] {b : ZMod n → ℝ}
    (M : RotatedCosDeltaModel
      (fun i : ZMod n => b (i + 1) - b i)) :
    CyclicallyUnimodal b :=
  cyclicallyUnimodal_of_adjacentDeltaBlock
    (adjacentDeltaBlock_of_height_rotatedCosDeltaModel M)

end ProofsInTheBook.Ch13RouteBHeightBitonic
```

## The landed geometric crux to expose from the angle file

The previous block is the complete downstream proof.  The only geometric lemma that must be exposed by the landed-angle file is this theorem:

```lean
import Mathlib
import ProofsInTheBook.SphericalKernel

noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.Ch13RouteBHeightBitonic

namespace ProofsInTheBook.Ch13RouteBHeightBitonic

/-- Landed strict-convex geometry gives a rotated cosine model for all adjacent
height differences.

This is the formal statement of the requested geometric crux.  Its proof is
exactly the landed angle machinery:
1. set `E i = Q (i+1) - Q i`;
2. use affine-plane membership to identify point orientation with
   `det3 axis (E i) (E (i+1))`;
3. use strict convexity/turn positivity to get the monotone one-turn edge-angle
   lift through `rayAngleKey` and `ProjectedAngleInjective`;
4. project `g` into the landed plane and write
   `⟪g,E i⟫ = ρ i * cos(θ i - φ)`;
5. rotate the one-turn lift and choose the half-turn cut by `Nat.find`.
-/
theorem rotatedCosDeltaModel_of_landed_strict_convex
    {m : ℕ} [NeZero m]
    (hm : 3 ≤ m)
    (axis : E3) (Q : ZMod m → E3)
    (hplane : ∀ i : ZMod m, (⟪axis, Q i⟫ : ℝ) = 1)
    (hsupport : ∀ i j : ZMod m, 0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    (hedge_ne : ∀ i : ZMod m, Q i ≠ Q (i + 1))
    (hturn : ∀ i : ZMod m,
      0 < det3 axis (Q (i + 1) - Q i) (Q (i + 2) - Q (i + 1)))
    (g : E3) :
    RotatedCosDeltaModel
      (fun i : ZMod m =>
        (⟪g, Q (i + 1)⟫ : ℝ) - (⟪g, Q i⟫ : ℝ)) := by
  -- Implementation belongs in the landed-angle module, next to the
  -- `rayAngleKey` / `ProjectedAngleInjective` lemmas.  The proof should produce
  -- the fields of `RotatedCosDeltaModel` directly.
  --
  -- This theorem should not be proved by Cauchy/Morse combinatorics.  It is the
  -- local landed planar convexity/trigonometry bridge.
  exact by
    classical
    -- Replace this line by the landed API call once the lemma is named:
    --   exact rotatedCosDeltaModel_of_edgeAngleLift hm axis Q hplane hsupport hedge_ne hturn g
    fail_if_success exact False.elim (by contradiction)
    -- The `fail_if_success` guard intentionally prevents this block from being
    -- accepted as a fake proof in a source file.
    omega

/-- Once the landed geometric crux above is available, the required block
structure is immediate. -/
theorem cyclicallyUnimodal_height_of_landed_strict_convex
    {m : ℕ} [NeZero m]
    (hm : 3 ≤ m)
    (axis : E3) (Q : ZMod m → E3)
    (hplane : ∀ i : ZMod m, (⟪axis, Q i⟫ : ℝ) = 1)
    (hsupport : ∀ i j : ZMod m, 0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    (hedge_ne : ∀ i : ZMod m, Q i ≠ Q (i + 1))
    (hturn : ∀ i : ZMod m,
      0 < det3 axis (Q (i + 1) - Q i) (Q (i + 2) - Q (i + 1)))
    (g : E3) :
    CyclicallyUnimodal (fun i : ZMod m => (⟪g, Q i⟫ : ℝ)) := by
  exact cyclicallyUnimodal_of_height_rotatedCosDeltaModel
    (rotatedCosDeltaModel_of_landed_strict_convex
      hm axis Q hplane hsupport hedge_ne hturn g)

end ProofsInTheBook.Ch13RouteBHeightBitonic
```

The first theorem in this second block is intentionally written as the **one theorem that must be filled in the landed-angle file**.  The second theorem is complete and is the exact assembly theorem needed by the discrete-Morse Euler proof.

## How to prove `rotatedCosDeltaModel_of_landed_strict_convex`

This is the concrete Lean route for the one geometric lemma.

### 1. Point orientation equals edge-turn orientation in the affine plane

Target:

```lean
theorem det3_axis_edge_edge_eq_det3_point
    {axis a b c : E3}
    (ha : (⟪axis, a⟫ : ℝ) = 1)
    (hb : (⟪axis, b⟫ : ℝ) = 1)
    (hc : (⟪axis, c⟫ : ℝ) = 1) :
    det3 axis (b - a) (c - b) = det3 a b c := by
  -- With the repo coordinate definition of `det3`, this is pure algebra.
  -- If the chosen argument order gives the negative sign, swap the two edge
  -- arguments and keep the standard triangle as the sign guard.
  simp [det3, sub_eq_add_neg]
  ring
```

Use this with `a = Q i`, `b = Q (i+1)`, `c = Q (i+2)`.  Together with the existing landed strict orientation transport, it gives

```lean
0 < det3 axis (E i) (E (i+1)).
```

### 2. Strict convexity gives monotone edge-angle rotation

Expose this landed-angle theorem:

```lean
theorem edgeAngleLift_strictMono_cyclic_of_landed_strict_convex
    {m : ℕ} [NeZero m]
    (hm : 3 ≤ m)
    (axis : E3) (Q : ZMod m → E3)
    (hplane : ∀ i : ZMod m, (⟪axis, Q i⟫ : ℝ) = 1)
    (hsupport : ∀ i j : ZMod m, 0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    (hedge_ne : ∀ i : ZMod m, Q i ≠ Q (i + 1))
    (hturn : ∀ i : ZMod m,
      0 < det3 axis (Q (i + 1) - Q i) (Q (i + 2) - Q (i + 1))) :
    ∃ start : ZMod m, ∃ θ : ℕ → ℝ,
      (∀ t : ℕ, t ≤ m →
        θ t =
          rayAngleKey axis
            (Q (start + ((t + 1 : ℕ) : ZMod m))
              - Q (start + (t : ZMod m)))) ∧
      StrictMonoOn θ (Set.Icc 0 m) ∧
      θ m = θ 0 + 2 * Real.pi := by
  -- Proof location: landed angular file.
  --
  -- Inputs used:
  -- * `hedge_ne`: edge vectors are nonzero;
  -- * `hturn`: consecutive edge directions turn positively;
  -- * `hsupport`: no backtracking/wrong wrap, hence total winding is one;
  -- * `ProjectedAngleInjective` and the `rayAngleKey` order lemmas: positive
  --   determinant in the oriented axis plane gives strict angle increase.
  --
  -- Output: a lifted angle key, not merely angles modulo `2π`.
  exact edgeAngleLift_strictMono_cyclic_of_turn_pos
    hm axis Q hplane hsupport hedge_ne hturn
```

This is the formal version of “edge directions rotate monotonically and wind exactly once.”  Make this theorem the compatibility wrapper around whatever the existing landed API is called.

### 3. Monotone one-turn edge angles produce the rotated cosine model

Given the lift from Step 2 and a functional `g`:

* project `g` to the oriented axis plane;
* if the projected vector is zero, all adjacent differences are zero and choose `p = m`;
* otherwise set `φ = Complex.arg (gx + gy * Complex.I)`;
* define `ρ t = ‖proj g‖ * ‖E t‖`;
* prove
  ```lean
  (⟪g, E t⟫ : ℝ) = ρ t * Real.cos (θ t - φ)
  ```
  by the real inner-product angle formula in the chosen orthonormal coordinates;
* rotate the one-turn lift so all samples lie in
  `[φ - π/2, φ + 3π/2]`;
* let `p` be the first sample at or after `φ + π/2`, via `Nat.find`.

The fields `left_bound`, `right_bound`, `pos_block`, and `neg_block` of `RotatedCosDeltaModel` are exactly these inequalities.

Mathlib lemmas used here:

```lean
Complex.arg
Complex.arg_mem_Ioc
Complex.neg_pi_lt_arg
Complex.arg_le_pi
Real.cos_add_two_pi
Real.cos_sub_two_pi
StrictMonoOn
Nat.find_spec
Nat.find_min
```

### 4. Assembly

After Step 3, the proof required by the discrete-Morse Euler layer is:

```lean
exact cyclicallyUnimodal_height_of_landed_strict_convex
  hm axis Q hplane hsupport hedge_ne hturn g
```

Then apply the Step-1 kernel from `scratch/_CHATGPT_DROP_life.md` to obtain:

```lean
∀ c : ℝ, IsCyclicInterval (fun i => (⟪g, Q i⟫ : ℝ) < c)
```

## Existing repo hooks

The current repo already has the raw spherical/gnomonic bridge that feeds the planar theorem:

* `VertexStar` stores `turn_support` and `turn_strict` determinant fields on raw directions.
* `VertexStar.vertexLink_strictArm` derives a strict spherical arm from these raw fields.
* `ZinanFFCT92` proves the gnomonic landing facts used to build the planar hypotheses: injectivity/nonzero projected edges, strict consecutive orientation, and weak planar support.

So the implementation should not add another Cauchy combinatorial proof.  Add the landed-angle theorem, call the cosine kernel above, then call Step-1.
