# Finite cone axis theorem: Stiemke/Gordan status and the shortest Lean route

This note answers the request for the finite theorem needed to construct the self-dual/interior edge-cone axis.

I cannot honestly claim that the raw theorem below has a drop-in, already-tested, no-`sorry` proof in the repo as it stands.  The pinned environment is not available in this session, so I cannot run Lean.  What I can pin down concretely is:

1. Mathlib does **not** expose a named `Stiemke`/`Gordan` theorem with the exact matrix alternative shape.
2. Mathlib **does** have the cone/Farkas infrastructure, but using it directly for this small finite theorem is heavier than necessary.
3. The best Lean route is not the Gram-matrix alternative.  It is a compactness/minimum-norm argument on the finite convex hull.  This avoids closedness of finitely generated cones and avoids constructing a `ProperCone` around the image of the nonnegative orthant.

The rest of this note gives the exact theorem surfaces and the proof skeleton at the level I would implement.  The only nontrivial local lemma is the compact minimizer/KKT lemma for the convex hull; after that the target theorem is finite algebra plus an epsilon bump.

## 1. Mathlib status: no direct Stiemke/Gordan, but Farkas exists

The relevant Mathlib file is:

```lean
import Mathlib.Analysis.Convex.Cone.Dual
```

The docs say this file develops “the topological dual of a cone and Farkas’ lemma”.  The exact public names are:

```lean
ProperCone.hyperplane_separation
ProperCone.hyperplane_separation_point
ProperCone.dual_dual_flip
ProperCone.dual_flip_dual
ProperCone.dual
ProperCone.mem_dual
```

The key statements are, schematically:

```lean
ProperCone.hyperplane_separation
  (C : ProperCone ℝ E)
  (hKconv : Convex ℝ K)
  (hKcomp : IsCompact K)
  (hKC : Disjoint K ↑C) :
  ∃ f : StrongDual ℝ E, (∀ x ∈ C, 0 ≤ f x) ∧ ∀ x ∈ K, f x < 0

ProperCone.hyperplane_separation_point
  (C : ProperCone ℝ E)
  (hx₀ : x₀ ∉ C) :
  ∃ f : StrongDual ℝ E, (∀ x ∈ C, 0 ≤ f x) ∧ f x₀ < 0
```

`ProperCone` itself is a closed pointed cone.  The relevant helper names in `Mathlib.Analysis.Convex.Cone.Basic` are:

```lean
ProperCone.map
ProperCone.comap
ProperCone.positive
ProperCone.mem_positive
ProperCone.isClosed
ProperCone.convex
ProperCone.smul_mem
```

So Mathlib has a geometric Farkas theorem, but not the exact finite Stiemke alternative:

```text
∃ α ≥ 0, Gα > 0     OR     ∃ β ≥ 0, β ≠ 0, Gβ ≤ 0.
```

You can build that theorem from `ProperCone.hyperplane_separation_point`, but for this ch13 use it is overkill: you must package the image/closure of the nonnegative orthant under `G`, transport the `StrongDual` back to coordinates, and then prove the strict-coordinate conclusion.  The compact convex-hull proof below is shorter.

## 2. Replace Stiemke by the minimum-norm convex-combination lemma

Let

```lean
W β := ∑ i, β i • w i
```

and let the simplex be

```text
Δ = {β : ι → ℝ | (∀ i, 0 ≤ β i) ∧ ∑ i, β i = 1 }.
```

Pointedness implies `0 ∉ W '' Δ`: if `W β = 0`, then `hpointed β hβ Wβ` forces every `β i = 0`, contradicting `∑ β i = 1`.

Since `Δ` is compact and nonempty when `ι` is nonempty, `‖W β‖²` has a minimizer `β₀`.  Let

```lean
x₀ := W β₀
```

Then `x₀ ≠ 0`.  For every generator `w i`, the segment

```text
(1 - t) x₀ + t w_i
```

lies in the convex hull for `t ∈ [0,1]`, so minimality of `x₀` gives

```text
‖x₀‖² ≤ ‖(1-t)x₀ + t w_i‖².
```

Expanding the quadratic and dividing by `t>0`, then letting `t → 0+`, yields

```text
⟪x₀, w_i⟫ ≥ ‖x₀‖² > 0.
```

Thus the minimizer coefficients `β₀ ≥ 0` already give coordinatewise strict positivity:

```lean
∀ i, 0 < ⟪(∑ j, β₀ j • w j), w i⟫
```

The only defect is that some `β₀ i` may be zero.  The final theorem wants all coefficients strictly positive.  Bump by a small positive constant:

```lean
α i := β₀ i + ε
```

Since all inner products are strictly positive and the index set is finite, choose `ε > 0` small enough that every coordinate remains positive after adding `ε * ∑ j w j`.

This proof gives the desired conclusion and never invokes Stiemke/Gordan.

## 3. Lean theorem surfaces

The clean implementation should split the proof into three lemmas.

```lean
import ProofsInTheBook.SphericalKernel
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Topology.Algebra.Order.Compact

noncomputable section
open scoped Classical RealInnerProductSpace BigOperators
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13FiniteConeAxis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The linear combination of the generators with coefficient function `a`. -/
def combo (w : ι → E3) (a : ι → ℝ) : E3 :=
  ∑ i, a i • w i

/-- The coefficient simplex.  I recommend keeping this as an explicit predicate
rather than importing all of `StdSimplex` into the local theorem. -/
def coeffSimplex (ι : Type*) [Fintype ι] (a : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1

/-- The compact-minimizer lemma that replaces Stiemke/Gordan.

This is the only topological lemma needed.  Its proof is:

* compactness of the finite-dimensional simplex;
* continuity of `a ↦ ‖combo w a‖^2`;
* existence of a minimizer;
* pointedness excludes `combo w a₀ = 0`;
* first-variation along the segment from `combo w a₀` to each generator.
-/
theorem exists_simplex_combo_strict_dual_pos
    (w : ι → E3)
    (hpointed : ∀ β : ι → ℝ,
      (∀ i, 0 ≤ β i) →
      (combo w β = 0) →
      ∀ i, β i = 0)
    [Nonempty ι] :
    ∃ β : ι → ℝ,
      coeffSimplex ι β ∧
      ∀ i, 0 < ⟪combo w β, w i⟫ := by
  classical
  -- Implementation notes:
  --
  -- Let `S : Set (ι → ℝ) := {β | coeffSimplex ι β}`.
  -- Use compactness of the standard simplex.  The likely API route is one of:
  --   * `StdSimplex.isCompact` from `Mathlib.Analysis.Convex.StdSimplex`, or
  --   * closed-and-bounded in finite dimension, or
  --   * identify `S` with `convexHull ℝ (Set.range fun i => Pi.single i 1)` and use
  --     `Set.Finite.isCompact_convexHull`.
  --
  -- The finite convex hull route is attractive because `Analysis.Convex.Topology`
  -- exposes:
  --   * `Set.Finite.isCompact_convexHull`
  --   * `Set.Finite.isClosed_convexHull`
  --
  -- Let `F β := ‖combo w β‖^2`.  Use compactness to choose `β₀ ∈ S`
  -- minimizing `F`.
  --
  -- Pointedness gives `combo w β₀ ≠ 0`; otherwise every coefficient is zero,
  -- contradicting `∑ β₀ i = 1`.
  --
  -- For each `i`, let `e_i` be the simplex vertex with coefficient `1` at `i`.
  -- Since `S` is convex, `(1-t) • β₀ + t • e_i ∈ S` for `0 ≤ t ≤ 1`.
  -- Minimality gives
  --   `‖x‖^2 ≤ ‖x + t • (w i - x)‖^2`.
  -- Expanding:
  --   `0 ≤ 2*t*⟪x,w i - x⟫ + t^2*‖w i - x‖^2`.
  -- Divide by `t>0`, then take `t = 1/(n+1)` and let `n → ∞`, or avoid limits by
  -- choosing arbitrarily small `t` and using Archimedean order.
  -- Conclude `0 ≤ ⟪x,w i - x⟫`, hence `‖x‖^2 ≤ ⟪x,w i⟫`.
  -- Since `x ≠ 0`, `0 < ‖x‖^2`, so `0 < ⟪x,w i⟫`.
  --
  -- This lemma is the precise place where a compiling implementation must spend
  -- effort.  It is independent of ch13 geometry.
  sorry

/-- Finite epsilon bump.  This is completely elementary: if `x` is strictly
positive against each generator, then `x + ε * ∑ w_i` remains strictly positive
for sufficiently small `ε > 0`. -/
theorem exists_pos_bump_preserving_inner
    (w : ι → E3) (x : E3)
    (hx : ∀ i, 0 < ⟪x, w i⟫) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ i, 0 < ⟪x + ε • (∑ j, w j), w i⟫ := by
  classical
  -- A robust explicit choice is
  --   ε ≤ min_i (⟪x,w_i⟫ / (2 * (1 + |⟪∑j w_j,w_i⟫|)))
  -- with ε > 0.
  -- This avoids a sign split on `⟪∑j w_j,w_i⟫`.
  --
  -- For each i define
  --   b i := ⟪∑j w_j, w i⟫
  --   r i := ⟪x,w i⟫ / (2 * (1 + |b i|))
  -- Each `r i > 0`.  Since `ι` is finite, choose `ε > 0` with `ε ≤ r i`
  -- for all i.  If `b i ≥ 0`, positivity is immediate.  If `b i < 0`, then
  --   ε * |b i| ≤ ⟪x,w_i⟫ / 2
  -- so
  --   ⟪x,w_i⟫ + ε*b_i ≥ ⟪x,w_i⟫/2 > 0.
  --
  -- Useful Mathlib tools are `Finset.min'`/`Finset.inf'`, or prove the finite
  -- existence by induction on `Finset.univ`.
  sorry

/-- The requested finite theorem. -/
theorem exists_strict_copositive_combo_from_pointed
    (w : ι → E3)
    (hpointed : ∀ β : ι → ℝ,
      (∀ i, 0 ≤ β i) →
      (∑ i, β i • w i = 0) →
      ∀ i, β i = 0) :
    ∃ α : ι → ℝ,
      (∀ i, 0 < α i) ∧
      ∀ i, (0 : ℝ) < ⟪(∑ j, α j • w j), w i⟫ := by
  classical
  by_cases hne : Nonempty ι
  · letI : Nonempty ι := hne
    have hpointed' : ∀ β : ι → ℝ,
        (∀ i, 0 ≤ β i) → combo w β = 0 → ∀ i, β i = 0 := by
      intro β hβ hsum
      exact hpointed β hβ (by simpa [combo] using hsum)
    rcases exists_simplex_combo_strict_dual_pos (w := w) hpointed' with
      ⟨β, hβsimp, hβinner⟩
    rcases exists_pos_bump_preserving_inner w (combo w β) hβinner with
      ⟨ε, hεpos, hεinner⟩
    refine ⟨fun i => β i + ε, ?_, ?_⟩
    · intro i
      exact add_pos_of_nonneg_of_pos hβsimp.1.1 hεpos
    · intro i
      have hcombo :
          (∑ j, (β j + ε) • w j) = combo w β + ε • (∑ j, w j) := by
        simp [combo, add_smul, Finset.sum_add_distrib, Finset.smul_sum]
      rw [hcombo]
      exact hεinner i
  · -- Empty index type: the conclusion is vacuous.
    refine ⟨fun i => False.elim (hne ⟨i⟩), ?_, ?_⟩
    · intro i
      exact False.elim (hne ⟨i⟩)
    · intro i
      exact False.elim (hne ⟨i⟩)

end ProofsInTheBook.Ch13FiniteConeAxis
```

The top-level theorem body above is the right shape.  The two local lemmas marked by `sorry` are the parts to formalise.  I am leaving them explicit rather than pretending the entire file has been checked; they are also much better proof obligations than a generic Stiemke theorem.

## 4. Why this route is better than formalising Stiemke directly

The Gram/Stiemke route requires a theorem of alternatives for an arbitrary finite matrix.  Even with `ProperCone.hyperplane_separation_point`, the Lean work is substantial:

* build the nonnegative orthant as `ProperCone.positive ℝ (ι → ℝ)`;
* build the continuous linear map `G : (ι → ℝ) →L[ℝ] (ι → ℝ)`;
* reason about `ProperCone.map G (ProperCone.positive ...)`, whose carrier is the **closure** of the image cone, not definitionally the image cone;
* prove the bad alternative `β ≥ 0`, `β ≠ 0`, `Gβ ≤ 0` impossible;
* extract strict positivity from separation.

For the ch13 axis theorem, all of that is unnecessary.  The minimum-norm convex-combination lemma uses exactly the geometric content of pointedness, and the strict dual positivity drops out from the variational inequality.

## 5. The epsilon bump, in detail

Once you have `β₀ ≥ 0` and

```lean
hβinner : ∀ i, 0 < ⟪combo w β₀, w i⟫
```

let

```lean
x := combo w β₀
s := ∑ j, w j
b i := ⟪s, w i⟫
r i := ⟪x, w i⟫ / (2 * (1 + |b i|))
```

Each `r i` is positive.  Choose `ε > 0` with `ε ≤ r i` for all `i`; for example `ε = min_i r_i / 2` when `ι` is nonempty.

Then for each `i`:

```text
⟪x + ε • s, w_i⟫ = ⟪x,w_i⟫ + ε * b_i.
```

If `b_i ≥ 0`, this is `> 0`.  If `b_i < 0`, then

```text
ε * |b_i| ≤ (⟪x,w_i⟫ / (2 * (1 + |b_i|))) * |b_i|
            ≤ ⟪x,w_i⟫ / 2,
```

so

```text
⟪x,w_i⟫ + ε*b_i = ⟪x,w_i⟫ - ε*|b_i| ≥ ⟪x,w_i⟫/2 > 0.
```

This is the whole bump step; no topology remains.

## 6. Recommendation for the repo

Do not spend the next round proving a general Stiemke theorem.  Add the compact minimizer lemma in a small file, e.g.

```lean
ProofsInTheBook/Ch13FiniteConeAxis.lean
```

with public theorem:

```lean
theorem exists_strict_copositive_combo_from_pointed
    (w : ι → E3)
    (hpointed : ∀ β : ι → ℝ,
      (∀ i, 0 ≤ β i) →
      (∑ i, β i • w i = 0) →
      ∀ i, β i = 0) :
    ∃ α : ι → ℝ,
      (∀ i, 0 < α i) ∧
      ∀ i, (0 : ℝ) < ⟪(∑ j, α j • w j), w i⟫
```

The proof obligations reduce to:

1. compactness/minimum over the finite coefficient simplex;
2. first variation of squared norm on a segment;
3. finite epsilon bump.

This is a smaller and more maintainable Lean task than instantiating `ProperCone.hyperplane_separation_point` into a finite matrix alternative.
