# Ch13 Route B: vertex LP optimality / tangent-cone H=V route

This is the requested Mathlib-backed route for the final convexity theorem:

> Let `polytope = convexHull ℝ S` for a finite vertex set.  At a vertex `v`, let `D` be the finite set of outgoing edge directions `pos w - pos v` for edges `{v,w}` incident to `v`.  If `0 ≤ ⟪g, e⟫` for every `e ∈ D`, then `0 ≤ ⟪g, x - pos v⟫` for every `x ∈ polytope`; equivalently, `v` minimizes `x ↦ ⟪g,x⟫` on the polytope.

The conclusion splits cleanly into:

```text
(geometry)   every vertex displacement pos u - pos v is in cone(D)
(algebra)    nonnegative on D ⇒ nonnegative on cone(D)
(convexity)  nonnegative on all vertices ⇒ nonnegative on convexHull(vertices)
```

Mathlib gives the algebra/convexity tools, but not the geometric tangent-cone H=V theorem for polytopes.

## Current Mathlib search results

### 1. Finite convex hull: YES

Relevant import:

```lean
import Mathlib.Analysis.Convex.Combination
```

Exact declarations to use:

```lean
Finset.mem_convexHull'
```

Rendered signature:

```lean
x ∈ convexHull R (s : Set E) ↔
  ∃ w : E → R,
    (∀ y ∈ s, 0 ≤ w y) ∧
    ∑ y ∈ s, w y = 1 ∧
    ∑ y ∈ s, w y • y = x
```

Also useful:

```lean
Finset.mem_convexHull
Finset.convexHull_eq
Set.Finite.convexHull_eq
mem_convexHull_of_exists_fintype
mem_convexHull_iff_exists_fintype
Convex.sum_mem
Convex.centerMass_mem
```

I did **not** find a ready-made theorem named `convexHull_min`, nor a direct theorem saying “a linear functional on a finite convex hull attains its min/max on the finite set.”  The proof from `Finset.mem_convexHull'` is short and included below.

### 2. Extreme points: YES, but not the desired theorem

Relevant import:

```lean
import Mathlib.Analysis.Convex.Extreme
```

Exact declarations:

```lean
Set.extremePoints
mem_extremePoints
mem_extremePoints_iff_left
mem_extremePoints_iff_forall_segment
Convex.mem_extremePoints_iff_convex_sdiff
Convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff
extremePoints_convexHull_subset
```

Representative signatures:

```lean
def Set.extremePoints (R) (A : Set E) : Set E

theorem mem_extremePoints :
  x ∈ Set.extremePoints R A ↔
    x ∈ A ∧
      ∀ x₁ ∈ A, ∀ x₂ ∈ A,
        x ∈ openSegment R x₁ x₂ → x₁ = x ∧ x₂ = x

theorem extremePoints_convexHull_subset :
  Set.extremePoints R (convexHull R A) ⊆ A
```

These are good for formalizing “`v` is a vertex/extreme point,” but they do not identify the tangent cone at `v` and do not imply that checking only incident edges suffices for LP optimality.

### 3. Cone hulls and dual cones: PARTIAL YES

Relevant imports:

```lean
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.Analysis.Convex.Cone.Dual
```

Cone hull API:

```lean
ConvexCone.hull
ConvexCone.subset_hull
ConvexCone.hull_min
ConvexCone.hull_le_iff
ConvexCone.gc_hull_coe
ConvexCone.gi
ConvexCone.mem_hull_of_convex
ConvexCone.coe_hull_of_convex
```

Important signatures:

```lean
def ConvexCone.hull (R) (s : Set M) : ConvexCone R M

theorem ConvexCone.subset_hull :
  s ⊆ (ConvexCone.hull R s : Set M)

theorem ConvexCone.hull_min {C : ConvexCone R M} :
  s ⊆ (C : Set M) → ConvexCone.hull R s ≤ C

theorem ConvexCone.hull_le_iff {C : ConvexCone R M} :
  ConvexCone.hull R s ≤ C ↔ s ⊆ (C : Set M)
```

For a convex base `s`, Mathlib has:

```lean
theorem ConvexCone.mem_hull_of_convex (hs : Convex R s) :
  x ∈ ConvexCone.hull R s ↔ ∃ r, 0 < r ∧ x ∈ r • s

theorem ConvexCone.coe_hull_of_convex (hs : Convex R s) :
  (ConvexCone.hull R s : Set M) = {x | ∃ r, 0 < r ∧ x ∈ r • s}
```

Algebraic dual cone API:

```lean
PointedCone.dual
PointedCone.mem_dual
PointedCone.dual_singleton
PointedCone.dual_union
PointedCone.dual_iUnion
PointedCone.dual_eq_iInter_dual_singleton
PointedCone.subset_dual_dual
PointedCone.subset_dual_flip_iff_subset_dual
PointedCone.dual_hull
```

Important signatures:

```lean
def PointedCone.dual
    (p : M →ₗ[R] N →ₗ[R] R) (s : Set M) : PointedCone R N

theorem PointedCone.mem_dual :
  y ∈ PointedCone.dual p s ↔ ∀ ⦃x : M⦄, x ∈ s → 0 ≤ (p x) y

theorem PointedCone.dual_hull :
  PointedCone.dual p (ConvexCone.hull R s : Set M) = PointedCone.dual p s
```

Topological/proper dual cone + Farkas API:

```lean
ProperCone.dual
ProperCone.mem_dual
ProperCone.hyperplane_separation
ProperCone.hyperplane_separation_point
ProperCone.subset_dual_dual
ProperCone.dual_flip_dual
ProperCone.dual_dual_flip
```

Important signatures:

```lean
def ProperCone.dual
    (p : M →ₗ[R] N →ₗ[R] R) [p.IsContPerfPair] (s : Set M) : ProperCone R N

theorem ProperCone.mem_dual :
  y ∈ ProperCone.dual p s ↔ ∀ ⦃x : M⦄, x ∈ s → 0 ≤ (p x) y

theorem ProperCone.hyperplane_separation_point
    (C : ProperCone ℝ E) (hx₀ : x₀ ∉ C) :
  ∃ f : StrongDual ℝ E, (∀ x ∈ C, 0 ≤ f x) ∧ f x₀ < 0

theorem ProperCone.dual_flip_dual
    (p : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [p.IsContPerfPair]
    (C : ProperCone ℝ E) :
  ProperCone.dual p.flip (ProperCone.dual p (C : Set E) : Set F) = C

theorem ProperCone.dual_dual_flip
    (p : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) [p.IsContPerfPair]
    (C : ProperCone ℝ E) :
  ProperCone.dual p (ProperCone.dual p.flip (C : Set E) : Set F) = C
```

Naming note: I did **not** find declarations named `inner_dualCone` or `dualCone_dualCone`.  The current API names are `PointedCone.dual`/`ProperCone.dual`, and membership is via `PointedCone.mem_dual`/`ProperCone.mem_dual`.

### 4. Tangent cone / normal cone / polyhedral H=V: NOT FOUND

I did not find a direct Mathlib API for:

```lean
tangentCone
normalCone
Mathlib.Analysis.Convex.Normal
ConvexCone.FG
MinkowskiWeyl
polyhedral cone H-representation = V-representation
vertex LP optimality from incident edges
```

So the direct “normal cone = polar tangent cone, tangent cone = edge cone” LP theorem is not currently a one-liner in Mathlib.

## Cleanest assembly for this project

Use one local geometric lemma, then discharge the rest with finite sums and `Finset.mem_convexHull'`.

### Minimal extra geometric lemma

Use the repo’s actual polytope data to prove:

```lean
-- schematic; replace names by landed fields
 theorem vertex_displacement_mem_outgoingEdgeCone
    (P : ConvexTriangulatedPolytope) (v u : P.Vertex) :
    P.pos u - P.pos v ∈ coneSpanFinset (outgoingEdgeDirs P v)
```

This is the tangent-cone H=V theorem in the exact finite coefficient form needed downstream.

### Clean proof route for that geometric lemma from face halfspaces

1. Define the incident-face H-cone:

```lean
def Hcone (P) (v) : Set E3 :=
  {y | ∀ f ∈ incidentFaces P v, ⟪P.normal f, y⟫ ≤ 0}
```

with the sign chosen so `P` lies in `⟪P.normal f, x - P.facePoint f⟫ ≤ 0`.

2. Prove every polytope displacement from `v` lies in the incident H-cone:

```lean
theorem displacement_mem_Hcone
    (hx : x ∈ P.polytope) : x - P.pos v ∈ Hcone P v
```

because `v` is on every incident face and every point of the polytope satisfies every supporting halfspace.

3. Prove the local 3D H=V cone lemma:

```lean
theorem Hcone_eq_outgoingEdgeCone :
  Hcone P v = coneSpanFinset (outgoingEdgeDirs P v)
```

The least invasive 3D proof is via the vertex link, not full Minkowski-Weyl:

* Choose an inward axis `a` through the interior of the tangent cone.
* Slice the H-cone by `⟪a,y⟫ = 1`.  This section is a convex polygon in an affine plane.
* The vertices of that section are the normalized outgoing edge rays.
* Use `Finset.mem_convexHull'` to write any section point as a convex combination of those normalized rays.
* Multiply by the positive height to obtain the conic combination of unnormalized edge directions.

This is exactly the H-cone = V-cone fact needed, but it avoids formalizing full general Minkowski-Weyl.

## Complete Lean LP assembly after the geometric lemma

The following theorem stack is the reusable algebraic/convex part.  It does not depend on the repo’s polytope structure except through the one hypothesis

```lean
hT : ∀ u, pos u - pos v ∈ coneSpanFinset D
```

```lean
import Mathlib

noncomputable section

open scoped BigOperators
open Set

namespace ProofsInTheBook.Ch13VertexLPRoute

variable {E : Type*}

/-- Finite conic span with exposed coefficients.  This is intentionally used instead
of an abstract cone hull because the LP step needs the coefficients immediately. -/
def coneSpanFinset [AddCommMonoid E] [Module ℝ E] (D : Finset E) : Set E :=
  {x | ∃ a : E → ℝ,
      (∀ e ∈ D, 0 ≤ a e) ∧
      ∑ e in D, a e • e = x}

section Linear

variable [AddCommGroup E] [Module ℝ E]

/-- A linear functional nonnegative on every generator is nonnegative on the
finite conic span of those generators. -/
theorem LinearMap.nonneg_on_coneSpanFinset
    {D : Finset E} (ℓ : E →ₗ[ℝ] ℝ) {x : E}
    (hx : x ∈ coneSpanFinset D)
    (hD : ∀ e ∈ D, 0 ≤ ℓ e) :
    0 ≤ ℓ x := by
  rcases hx with ⟨a, ha_nonneg, hxsum⟩
  have hsum_nonneg : 0 ≤ ∑ e in D, a e * ℓ e := by
    exact Finset.sum_nonneg (fun e he =>
      mul_nonneg (ha_nonneg e he) (hD e he))
  have hmap : ℓ (∑ e in D, a e • e) = ∑ e in D, a e * ℓ e := by
    simp [map_sum, map_smul]
  rwa [← hmap, hxsum] at hsum_nonneg

/-- Vertex-level LP optimality on the finite vertex type.  The only geometric input
is that every vertex displacement from `v` lies in the outgoing-edge cone `D`. -/
theorem vertex_min_on_vertices_of_edgeCone
    {ι : Type*} [Fintype ι]
    (pos : ι → E) (D : Finset E) (v : ι) (ℓ : E →ₗ[ℝ] ℝ)
    (hT : ∀ u : ι, pos u - pos v ∈ coneSpanFinset D)
    (hD : ∀ e ∈ D, 0 ≤ ℓ e) :
    ∀ u : ι, ℓ (pos v) ≤ ℓ (pos u) := by
  intro u
  have hnonneg : 0 ≤ ℓ (pos u - pos v) :=
    LinearMap.nonneg_on_coneSpanFinset ℓ (hT u) hD
  have hdiff : 0 ≤ ℓ (pos u) - ℓ (pos v) := by
    simpa using hnonneg
  exact sub_nonneg.mp hdiff

/-- If a linear functional is bounded below by its value at `v` on every point of a
finite set `S`, then it is bounded below by that value on `convexHull ℝ S`.

This is the “linear functions on a finite convex hull are controlled by vertices”
lemma, proved directly from `Finset.mem_convexHull'`. -/
theorem linear_ge_on_convexHull_of_ge_on_finset
    (S : Finset E) (ℓ : E →ₗ[ℝ] ℝ) (v : E)
    (hS : ∀ y ∈ S, ℓ v ≤ ℓ y) :
    ∀ x ∈ convexHull ℝ (S : Set E), ℓ v ≤ ℓ x := by
  classical
  intro x hx
  rcases (Finset.mem_convexHull' (R := ℝ) (s := S) (x := x)).mp hx with
    ⟨w, hw_nonneg, hw_sum, hxsum⟩
  have hmap : ℓ x = ∑ y in S, w y * ℓ y := by
    rw [← hxsum]
    simp [map_sum, map_smul]
  have hweighted : ∑ y in S, w y * ℓ v ≤ ∑ y in S, w y * ℓ y := by
    exact Finset.sum_le_sum (fun y hy =>
      mul_le_mul_of_nonneg_left (hS y hy) (hw_nonneg y hy))
  have hleft : ∑ y in S, w y * ℓ v = ℓ v := by
    rw [← Finset.sum_mul, hw_sum, one_mul]
  linarith

/-- Global polytope optimality for a finite vertex set.  The polytope is
`convexHull ℝ (Set.range pos)`. -/
theorem vertex_min_on_convexHull_from_edgeCone
    {ι : Type*} [Fintype ι] [DecidableEq E]
    (pos : ι → E) (D : Finset E) (v : ι) (ℓ : E →ₗ[ℝ] ℝ)
    (hT : ∀ u : ι, pos u - pos v ∈ coneSpanFinset D)
    (hD : ∀ e ∈ D, 0 ≤ ℓ e) :
    ∀ x ∈ convexHull ℝ (Set.range pos), ℓ (pos v) ≤ ℓ x := by
  classical
  let S : Finset E := Finset.univ.image pos
  have hrange : Set.range pos = (S : Set E) := by
    ext x
    simp [S]
  have hVert : ∀ y ∈ S, ℓ (pos v) ≤ ℓ y := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨u, _hu, rfl⟩
    exact vertex_min_on_vertices_of_edgeCone pos D v ℓ hT hD u
  intro x hx
  rw [hrange] at hx
  exact linear_ge_on_convexHull_of_ge_on_finset S ℓ (pos v) hVert x hx

end Linear

section Inner

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner-product linear functional `x ↦ ⟪g, x⟫`. -/
def innerLinear (g : E) : E →ₗ[ℝ] ℝ where
  toFun x := ⟪g, x⟫
  map_add' := by
    intro x y
    simp [inner_add_right]
  map_smul' := by
    intro r x
    simp [inner_smul_right]

@[simp] theorem innerLinear_apply (g x : E) : innerLinear g x = ⟪g, x⟫ := rfl

/-- Inner-product statement matching the Route B use case: checking `g` on the
outgoing-edge cone generators makes `v` a global minimizer on the convex hull. -/
theorem inner_vertex_min_on_convexHull_from_edgeCone
    {ι : Type*} [Fintype ι] [DecidableEq E]
    (pos : ι → E) (D : Finset E) (v : ι) (g : E)
    (hT : ∀ u : ι, pos u - pos v ∈ coneSpanFinset D)
    (hD : ∀ e ∈ D, 0 ≤ ⟪g, e⟫) :
    ∀ x ∈ convexHull ℝ (Set.range pos), ⟪g, pos v⟫ ≤ ⟪g, x⟫ := by
  simpa using
    (vertex_min_on_convexHull_from_edgeCone
      (pos := pos) (D := D) (v := v) (ℓ := innerLinear g) hT hD)

/-- Inner-product displacement form: `0 ≤ ⟪g, x - pos v⟫` for all points of the
polytope. -/
theorem inner_nonneg_displacement_on_convexHull_from_edgeCone
    {ι : Type*} [Fintype ι] [DecidableEq E]
    (pos : ι → E) (D : Finset E) (v : ι) (g : E)
    (hT : ∀ u : ι, pos u - pos v ∈ coneSpanFinset D)
    (hD : ∀ e ∈ D, 0 ≤ ⟪g, e⟫) :
    ∀ x ∈ convexHull ℝ (Set.range pos), 0 ≤ ⟪g, x - pos v⟫ := by
  intro x hx
  have hxle := inner_vertex_min_on_convexHull_from_edgeCone pos D v g hT hD x hx
  have hdiff : 0 ≤ ⟪g, x⟫ - ⟪g, pos v⟫ := sub_nonneg.mpr hxle
  simpa [inner_sub_right] using hdiff

end Inner

end ProofsInTheBook.Ch13VertexLPRoute
```

## Outgoing-edge wrapper

A typical finite edge-direction set, adapted to the repo’s actual edge predicate, is:

```lean
noncomputable def outgoingEdgeDirs
    {V E : Type*} [Fintype V] [DecidableEq E]
    [AddCommGroup E] [Module ℝ E]
    (pos : V → E) (Edge : V → V → Prop) [DecidableRel Edge] (v : V) : Finset E :=
  (Finset.univ.filter (fun w => Edge v w)).image (fun w => pos w - pos v)
```

Then instantiate:

```lean
D := outgoingEdgeDirs pos Edge v
```

The edge nonnegativity hypothesis becomes:

```lean
hD : ∀ e ∈ D, 0 ≤ ⟪g, e⟫
```

by `Finset.mem_image` and the given assumptions on incident edges.  The only nontrivial geometry remains:

```lean
hT : ∀ u, pos u - pos v ∈ coneSpanFinset D
```

which is the local tangent-cone H=V theorem.

## Bottom line

The shortest viable route for `eulerChar = 2` from convexity is:

```text
prove once in the repo:
  vertex_displacement_mem_outgoingEdgeCone

then apply:
  inner_nonneg_displacement_on_convexHull_from_edgeCone
```

I would not try to route this through Mathlib’s `ProperCone.hyperplane_separation_point` unless the project already has the tangent cone and normal cone packaged as closed `ProperCone`s.  That route is mathematically elegant but creates more Lean infrastructure than the finite coefficient proof above.
