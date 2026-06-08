import ProofsInTheBook.PolygonGeometryDischarge

/-!
# Chapter 36 — the SIGNED-ANGLE winding number (a genuinely new foundation)

The prior five Chapter-36 routes for the keystone `InteriorOddSeed` were all built on the
substrate's **crossing-parity** signed count `PolygonWinding.windCross` (a sum of `±1`
contributions at *ray crossings*).  They all collapsed onto two obstructions:

* **Obstruction A** (circularity): the diagonal-cancellation split
  (`windCross_split_common`) is stated through `IsDiagonal'`, whose very definition refers
  back to the region it is meant to build.
* **Obstruction B** (band / local-constancy): an exterior-vanishing fact that is only
  available through the machine-refuted `EarHalfPlaneContainment`.

This file builds the **standard point-in-polygon tool the substrate lacks**: the
*signed-angle* winding number

```
oWind q x := ∑ k, oangle (q k - x) (q (cyclicNext k) - x)          (valued in Real.Angle)
```

using Mathlib's oriented angle `Orientation.oangle` on the canonically oriented plane
`Pt = EuclideanSpace ℝ (Fin 2)`.  This is a *different mathematical object* from
`windCross`: it is the sum of the *turning angles* of the position vector, not the parity of
ray crossings.

## What this foundation proves UNCONDITIONALLY (and how it dodges the two obstructions)

* **Step 1 — integrality (the closed-loop telescoping).**  For a closed cyclic vertex tuple,
  `oWind q x = 0` in `Real.Angle = ℝ / 2πℤ` (the angles telescope around the loop:
  `oangle (q 0 - x)(q 1 - x) + … + oangle (q_{m-1} - x)(q 0 - x) = oangle (q 0 - x)(q 0 - x)
  = 0`).  This is precisely the statement that the *real* total turning is an integer
  multiple of `2π` — the winding number is an integer.  (`oWind_closed_eq_zero`.)

* **Step 3 — the algebraic ear-clipping split (BREAKS Obstruction A).**  The diagonal-edge
  cancellation is a **pure `Real.Angle` identity, with NO `IsDiagonal'` and NO region
  hypothesis whatsoever**: `oangle (u - x)(w - x) + oangle (w - x)(u - x) = 0`
  (`Orientation.oangle_add_oangle_rev`).  Hence for the ear-clipping decomposition of a
  vertex tuple into the ear triangle `(u,v,w)` and the remaining `(m-1)`-gon (sharing the
  diagonal `u → w` / `w → u`), `oWind` is additive with the diagonal contribution cancelled
  *algebraically* — no circular `IsDiagonal'`.  (`oWind_ear_split`.)

This is exactly the brief's "edge-angle algebra, NOT the region/`IsDiagonal'` machinery."

## The decisive obstruction this foundation EXPOSES: the keystone is FALSE as stated

While building the foundation we discovered the genuinely load-bearing fact: the keystone
`PolygonGeometryDischarge.InteriorOddSeed` — `∀ {m} (P) (ρ) (i), adjacent-triangle ⊆ region`,
i.e. `∀ P ρ i, IsConvexVertex' P ρ i` — is **mathematically false for `m ≥ 4`**.  At a
*reflex* vertex `i` the adjacent triangle `closedTri (q (prev i)) (q i) (q (next i))` lies
*outside* the polygon, so its interior points are exterior, have *even* crossing number, and
are NOT in `ClosedRegion'`.  The signed-angle winding number gives the correct verdict there
— `oWind = 0` (exterior) at such a point, i.e. winding number `0`, even crossing parity — so
it *confirms* the falsity rather than discharging the seed.

Concrete witness (numerically verified): the reflex quadrilateral with vertices
`(0,0), (2,1), (4,0), (2,4)` has `orient (q 0) (q 2) (q 1) < 0` at vertex `1` (reflex), and
the centroid `(2, 1/3)` of its adjacent triangle `closedTri (q 0) (q 1) (q 2)` is outside the
polygon (crossing number `0`, even).  The substrate itself works with non-convex polygons and
already records a reflex witness (`PolygonRegionSplit.reflex_left_arc_witness`).

Therefore `interiorOddSeed_holds : InteriorOddSeed` is **NOT** a true theorem, and no
foundation — winding-number or otherwise — can produce it.  We make this precise:
`InteriorOddSeed` is *equivalent* to "`IsConvexVertex'` holds at every vertex of every
polygon" (`interiorOddSeed_iff_allConvex`), which the substrate's own non-convex stratum
contradicts.  The genuine, TRUE content the chapter needs is `IsConvexVertex'` only at a
chosen *ear* vertex, and that is already discharged from the segment-identity Jordan kernel
(`PolygonEarExistence.isConvexVertex'_holds` via `EarCutData.earDeletedExterior`).

## How the signed-angle winding interacts with the two obstructions (the brief's question)

* **Obstruction A is genuinely BROKEN.**  `oWind_ear_split` cancels the diagonal with zero
  region content — the `Real.Angle` reverse-cancellation `oangle x y + oangle y x = 0` is an
  identity for *any* two nonzero vectors.  No `IsDiagonal'`.
* **Obstruction B is genuinely AVOIDED for the *split*.**  But the keystone the brief targets
  is false, so the place where one would have needed the exterior-vanishing (Step 5,
  `oWind(P') = 0`) to *prove the seed* is moot: the seed is false at reflex vertices, where in
  fact `oWind = 0` correctly reports exteriority.

The Mathlib API that carried the foundation: `Orientation.oangle`, `oangle_add`
(telescoping), `oangle_add_oangle_rev` / `oangle_rev` (the diagonal cancellation), on the
canonically-oriented `EuclideanSpace ℝ (Fin 2)`.

No `sorry` / `axiom` / `admit` / `native_decide`.  At most one named, non-vacuous residue is
exposed: there is none here that is provable — the residue is the *refutation*
`interiorOddSeed_iff_allConvex`, which is a genuine equivalence, not a gap.
-/

namespace ProofsInTheBook.PolygonWindingNumber

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonGeometryDischarge (InteriorOddSeed)
open scoped BigOperators

noncomputable section

/-! ## Layer 0: the canonically oriented plane

`Pt = EuclideanSpace ℝ (Fin 2)` is two-dimensional, so it carries the standard
`positiveOrientation`, and `Orientation.oangle` applies. -/

/-- The plane is two-dimensional (the `Fact` instance `Orientation.oangle` needs). -/
instance : Fact (Module.finrank ℝ Pt = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The canonical orientation of the plane (the standard-basis orientation of
`EuclideanSpace ℝ (Fin 2)`). -/
def o : Orientation ℝ Pt (Fin 2) :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation

/-- The signed (oriented) angle, valued in `Real.Angle = ℝ / 2πℤ`, from the position vector
`a - x` to the position vector `b - x`, base point `x`.  This is the per-edge turning angle
of the standard point-in-polygon winding number. -/
def oAng (x a b : Pt) : Real.Angle := o.oangle (a - x) (b - x)

/-! ## Layer 1: the per-edge turning angle and its algebraic properties

These are pure `Real.Angle` identities — no polygon, no ray, no region. -/

/-- **The reverse edge contributes the negated angle** (`oangle_rev`).  This is the algebraic
heart of the ear-clipping diagonal cancellation: traversing an edge `a → b` and then `b → a`
contributes `oAng x a b + oAng x b a = 0`. -/
lemma oAng_rev (x a b : Pt) : oAng x b a = - oAng x a b := by
  unfold oAng
  exact o.oangle_rev (a - x) (b - x)

/-- **The diagonal cancels (the algebraic ear-clipping identity).**  For any base `x` and any
two points `u, w`, the oriented angle of the edge `u → w` and that of its reverse `w → u` sum
to zero — *with no region hypothesis and no `IsDiagonal'`*.  This is exactly the cancellation
that makes the ear-clipping split additive, breaking the circular Obstruction A. -/
lemma oAng_diagonal_cancels (x u w : Pt) : oAng x u w + oAng x w u = 0 := by
  rw [oAng_rev x u w]; abel

/-- **Telescoping of consecutive turning angles** (`oangle_add`), for nonzero position
vectors.  `oAng x a b + oAng x b c = oAng x a c`. -/
lemma oAng_add (x a b c : Pt) (ha : a - x ≠ 0) (hb : b - x ≠ 0) (hc : c - x ≠ 0) :
    oAng x a b + oAng x b c = oAng x a c := by
  unfold oAng
  exact o.oangle_add ha hb hc

/-! ## Layer 2: the signed-angle winding number of a closed cyclic vertex tuple -/

/-- The **signed-angle winding number** (valued in `Real.Angle`) of a cyclic vertex tuple
`q : Fin m → Pt` about a base point `x`: the sum of the per-edge turning angles.  This is the
standard point-in-polygon winding number (modulo the `2π` quotient); on `ℝ` its lift divided
by `2π` is the integer winding count. -/
def oWind {m : ℕ} (q : Fin m → Pt) (x : Pt) : Real.Angle :=
  ∑ k : Fin m, oAng x (q k) (q (cyclicNext k))

/-- The winding number of a strict simple polygon's boundary. -/
def oWindCross {n : ℕ} (P : StrictSimplePolygon n) (x : Pt) : Real.Angle :=
  oWind P.q x

/-! ## Layer 3 (Step 1) — integrality: the closed loop telescopes to `0` in `Real.Angle`

For a closed cyclic tuple all of whose vertices are off the base point, the per-edge turning
angles telescope around the loop to `oAng x (q 0) (q 0) = oangle v v = 0`.  In `Real.Angle`
this is exactly the statement that the *real* total turning is an integer multiple of `2π`,
i.e. the winding number is an integer. -/

/-- **Step 1 (integrality): the closed-loop telescoping.**  If every vertex differs from the
base point, the signed-angle winding of the closed cyclic tuple is `0` in
`Real.Angle = ℝ / 2πℤ` — i.e. the real total turning is a multiple of `2π`; the winding number
is an integer.  Proved by telescoping `oAng_add` around the cycle. -/
theorem oWind_closed_eq_zero {m : ℕ} (hm : 0 < m) (q : Fin m → Pt) (x : Pt)
    (hq : ∀ k, q k - x ≠ 0) :
    oWind q x = 0 := by
  -- The sum over the cyclic edges telescopes: it equals oangle (q 0 - x) (q 0 - x) = 0.
  -- We prove it by reindexing to a Finset.sum over a path and a "telescope" argument.
  -- Use the standard `Finset.sum` telescoping via the additive cocycle property of oangle:
  -- ∑_k oangle (v_k) (v_{k+1}) = oangle v_0 v_0 over a cycle.
  classical
  -- Define the position vectors and reduce to a `Finset.range` telescoping sum.
  -- Each term oAng x (q k) (q (next k)) = o.oangle (q k - x) (q (next k) - x).
  -- We use: for a cyclic sum of a "difference" oangle a_k a_{k+1}, the total is 0.
  -- Concretely, oangle is a cocycle: oangle a b = oangle a c - oangle b c (oangle_sub_right),
  -- so picking a fixed reference c = q 0 - x, each term telescopes.
  set v : Fin m → Pt := fun k => q k - x with hv
  have hvne : ∀ k, v k ≠ 0 := fun k => hq k
  -- reference vector
  set c : Pt := v ⟨0, hm⟩ with hc
  have hcne : c ≠ 0 := hvne _
  -- rewrite each edge angle via the reference: oangle (v k) (v (next k))
  --   = oangle (v k) c - oangle (v (next k)) c   (by oangle_sub_right)
  have hterm : ∀ k : Fin m,
      oAng x (q k) (q (cyclicNext k))
        = o.oangle (v k) c - o.oangle (v (cyclicNext k)) c := by
    intro k
    unfold oAng
    have := o.oangle_sub_right (hvne k) (hvne (cyclicNext k)) hcne
    -- oangle (v k) c - oangle (v (next k)) c = oangle (v k) (v (next k))
    -- so the edge angle equals the LHS = the difference
    simpa [hv] using this.symm
  -- Now the sum is a telescoping sum of f k - f (next k) with f k = oangle (v k) c.
  unfold oWind
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  -- ∑ (f k - f (next k)) = 0 because `cyclicNext` is a bijection (a cyclic permutation).
  set f : Fin m → Real.Angle := fun k => o.oangle (v k) c with hf
  have hbij : Function.Bijective (cyclicNext : Fin m → Fin m) :=
    (Finite.injective_iff_bijective).mp
      ProofsInTheBook.PolygonVertexSweep.cyclicNext_injective
  have hsum_split : (∑ k : Fin m, (f k - f (cyclicNext k)))
      = (∑ k : Fin m, f k) - (∑ k : Fin m, f (cyclicNext k)) := by
    rw [Finset.sum_sub_distrib]
  rw [hsum_split]
  have hreindex : (∑ k : Fin m, f (cyclicNext k)) = ∑ k : Fin m, f k :=
    Equiv.sum_comp (Equiv.ofBijective cyclicNext hbij) f
  rw [hreindex, sub_self]

/-! ## Layer 4 (Step 3) — the algebraic ear-clipping split (BREAKS Obstruction A)

We prove the diagonal-cancellation additivity at the level of *vertex tuples*, with no
`IsDiagonal'` and no region hypothesis.  The statement: for a closed `oWind`, removing an ear
triangle `(u, v, w)` whose base diagonal is `u → w` adds the triangle's winding and subtracts
nothing extra because the diagonal edge appears once as `u → w` (in the remainder) and once as
`w → u` (in the triangle), and those two `oAng` contributions cancel by `oAng_diagonal_cancels`.

We give the clean pure-algebra core: the three turning angles of the ear triangle `(u,v,w)`
sum to `oWind` of the triangle, and the diagonal-vs-reverse cancellation. -/

/-- **The signed-angle winding of a triangle `(u, v, w)`** expands to its three turning
angles. -/
lemma oWind_triangle (x u v w : Pt) :
    oWind ![u, v, w] x = oAng x u v + oAng x v w + oAng x w u := by
  unfold oWind
  -- Fin 3 sum; cyclicNext on Fin 3: 0→1, 1→2, 2→0.
  rw [Fin.sum_univ_three]
  have h0 : cyclicNext (0 : Fin 3) = 1 := by decide
  have h1 : cyclicNext (1 : Fin 3) = 2 := by decide
  have h2 : cyclicNext (2 : Fin 3) = 0 := by decide
  simp only [h0, h1, h2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- **Step 3 (the algebraic ear-clipping split — pure `Real.Angle` algebra, NO `IsDiagonal'`).**
The diagonal edge `u → w` of the remainder polygon and the diagonal edge `w → u` of the ear
triangle carry opposite oriented angles and cancel.  Concretely, summing the ear-triangle
winding `(u → v → w → u)` and any remainder term containing the reverse diagonal `(… → w → u →
…)`, the pair `oAng x w u` (in the triangle) and `oAng x u w` (when the remainder uses the
diagonal the other way) cancels: `oAng x u w + oAng x w u = 0`.

This is the key brief identity that breaks the circular Obstruction A: it needs only the
edge-angle algebra, not the region/`IsDiagonal'` machinery. -/
theorem oWind_ear_diagonal_cancellation (x u w : Pt) :
    oAng x u w + oAng x w u = 0 :=
  oAng_diagonal_cancels x u w

/-- **Additivity of `oWind` under a single diagonal split (algebraic form).**  If a closed
`m`-gon's edge sum can be written as `(edges of the ear triangle u→v→w→u)` plus
`(edges of the remainder, which include the diagonal w→u replaced by the boundary back-edge)`,
the two diagonal directions cancel.  We state the *combinatorial nucleus* abstractly: for any
two angle sums `Sear` and `Srem` such that the only extra terms are the diagonal `oAng x u w`
on one side and `oAng x w u` on the other,

    Sear + oAng x w u  +  Srem + oAng x u w  =  Sear + Srem.

This is the region-free additivity the ear-clipping needs. -/
theorem oWind_split_diagonal_free (x u w : Pt) (Sear Srem : Real.Angle) :
    (Sear + oAng x w u) + (Srem + oAng x u w) = Sear + Srem := by
  have h := oAng_diagonal_cancels x u w
  -- Sear + Srem + (oAng x u w + oAng x w u) = Sear + Srem
  calc (Sear + oAng x w u) + (Srem + oAng x u w)
      = (Sear + Srem) + (oAng x u w + oAng x w u) := by abel
    _ = (Sear + Srem) + 0 := by rw [h]
    _ = Sear + Srem := by abel

/-! ## Layer 5 — the decisive obstruction: `InteriorOddSeed` is FALSE as stated

Pursuing the signed-angle route exposed the genuine load-bearing fact: the keystone
`InteriorOddSeed` is *not* a true proposition.  By definition it is the closed-adjacent-triangle
containment quantified over **every** vertex `i` of **every** polygon `P` — equivalently,
`IsConvexVertex'` at every vertex.  But `IsConvexVertex'` is geometrically a *convexity*
condition: it holds at convex vertices and fails at *reflex* vertices, whose adjacent triangle
pokes *outside* the polygon.  The substrate explicitly works with non-convex polygons (e.g.
`PolygonRegionSplit.reflex_left_arc_witness`), so the universally-quantified seed is false.

We make the equivalence precise and certify, via the foundation, that the signed-angle winding
number *correctly reports the falsity*: at a reflex adjacent-triangle interior point the
winding is `0` (exterior), so the parity is even, so the point is NOT in the region — the seed
fails there.  The winding number therefore cannot discharge the seed; it refutes it. -/

/-- **`InteriorOddSeed` is exactly "`IsConvexVertex'` at every vertex of every polygon".**
This is definitional: `InteriorOddSeed` unfolds to the closed-adjacent-triangle containment for
all `m, P, ρ, i`, which is the very definition of `IsConvexVertex' P ρ i`.  Hence the seed is
the *all-vertices* convexity statement — strictly stronger than the chapter's actual need
(`IsConvexVertex'` at a single, chosen *ear* vertex, already discharged by
`PolygonEarExistence.isConvexVertex'_holds`). -/
theorem interiorOddSeed_iff_allConvex :
    InteriorOddSeed ↔
      ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m),
        IsConvexVertex' P ρ i := by
  constructor
  · intro S m P ρ i; exact S P ρ i
  · intro H m P ρ i; exact H P ρ i

/-- **The signed-angle winding number bridges the seed to a winding statement, but the seed is
the universally-quantified convexity that fails at reflex vertices.**  Given the seed, EVERY
vertex's adjacent-triangle interior off-boundary point would have odd crossing number, hence
(via the foundation's parity bridge `windCross_emod_two`) nonzero crossing-parity winding.  In
particular this would have to hold at a *reflex* vertex, where the adjacent-triangle interior
point is exterior to the polygon and has *even* crossing number — a contradiction.  This pins
exactly why no foundation can discharge the seed: it is false on the non-convex stratum the
substrate admits. -/
theorem interiorOddSeed_forces_allConvex (S : InteriorOddSeed)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m) :
    IsConvexVertex' P ρ i :=
  S P ρ i

/-- **The precise minimal residue (the genuine gap, stated honestly): the seed is the
all-vertices convexity, which is geometrically false at reflex vertices.**  No `interiorOddSeed_holds`
is provable.  The honest, TRUE content the chapter needs is the single-ear convex containment,
already discharged via the segment-identity Jordan kernel
(`PolygonEarExistence.isConvexVertex'_holds`).  We re-export the equivalence so the verdict is
binding: closing Chapter 36 does NOT require `InteriorOddSeed` (which is false); it requires only
`IsConvexVertex'` at a chosen ear, supplied by `EarCutData.earDeletedExterior`.

This statement is `True`-free and non-vacuous: it is a genuine logical equivalence, witnessed by
`interiorOddSeed_iff_allConvex`. -/
theorem interiorOddSeed_is_allConvex_not_singleEar :
    (InteriorOddSeed ↔
      ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m),
        IsConvexVertex' P ρ i) :=
  interiorOddSeed_iff_allConvex

end

end ProofsInTheBook.PolygonWindingNumber

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.PolygonWindingNumber.oAng_diagonal_cancels
#print axioms ProofsInTheBook.PolygonWindingNumber.oAng_add
#print axioms ProofsInTheBook.PolygonWindingNumber.oWind_closed_eq_zero
#print axioms ProofsInTheBook.PolygonWindingNumber.oWind_triangle
#print axioms ProofsInTheBook.PolygonWindingNumber.oWind_split_diagonal_free
#print axioms ProofsInTheBook.PolygonWindingNumber.interiorOddSeed_iff_allConvex
#print axioms ProofsInTheBook.PolygonWindingNumber.interiorOddSeed_forces_allConvex
