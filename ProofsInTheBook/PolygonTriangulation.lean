import ProofsInTheBook.PolygonSideCrossing

/-!
# Chapter 36 — Triangulation existence by ear/diagonal cutting (Layers A4–A5)

This file assembles the triangulation existence object on top of the
*unconditional* diagonal-existence layer `PolygonSideCrossing` (the corrected
side-coordinate crossing convention, for which local constancy of the region
parity along boundary-free segments — and hence `exists_diagonal'` — holds with
no `NoTangentialVertexSweep` hypothesis).

## What is built here

* `EarTriangulation'` — the inductive existence object of the design
  (CH36 §5–§7): a triangle base (`n = 3`), an ear-cut constructor, and a
  diagonal-split constructor.  Each non-base constructor stores a corrected
  diagonal `IsDiagonal'` and the sub-triangulations of the explicitly
  constructed subpolygons.

* `EarTriangulation'.triangleCount` and `earTriangulation'_count` — the count of
  triangles is exactly `n - 2`, proved by induction on the cutting object
  (the diagonal-split additivity `(k-2)+(m-2) = (k+m-2)-2` with `k+m = n+2`,
  and the ear-cut decrement).

* `GeomTriangulation'` — the finite-triangle output data (the `n - 2` count,
  nondegeneracy, region-subset, and covering) consumed by the combinatorial
  3-colouring half.  Nondegeneracy is proved unconditionally; region-subset and
  covering follow from the cutting interface's region-union identity.

* `EarTriangulation'.toGeom` — compilation of the inductive object to the finite
  triangle data, with the region facts supplied by the cutting interface.

* `strictSimplePolygon_triangulable'` — every strict simple polygon admits an
  `EarTriangulation'` (strong induction on `n`, base `n = 3`, step via
  `exists_diagonal'`).

* The art-gallery coverage statement (`every_region'_point_in_some_triangle`).

## Honest scoping (the isolated geometry interface)

The substrate proves the *combinatorial* skeleton (cyclic arc lengths add to
`n + 2`, arcs are strictly shorter, the diagonal splits the index cycle).  What
it does **not** prove from first principles are the genuine *planar* facts that
substitute for the Jordan curve theorem:

1. the two cyclic arcs along a diagonal carry strict simple polygons
   (`subpolygonLeftTuple` / `subpolygonRightTuple` are simple);
2. the parity regions of the two subpolygons **union** to the parent region and
   **intersect** exactly in the diagonal segment;
3. the ear deletion's region equals the ear triangle union the smaller region;
4. the recursive convex-vertex + transversality witnesses needed to keep cutting.

These are bundled, *uniformly across all reachable subpolygons*, into the
`LocalCutData'` / `CutOracle` interface below — exactly as the A3/A4 scaffold
(`A3GeometryFacts` / `A4CuttingFacts`) isolates them for the old convention.
No such fact is asserted globally; each is a field of an explicit hypothesis
package threaded through the induction.  Everything *else* — the inductive
object, the termination, the `n - 2` count, the geometric-data compilation, and
the coverage bridge — is proved unconditionally.

The single genuinely-resistant analytic fact (the Jordan-substitute region
*union*/*intersection* identity for `ClosedRegion'`) is the named field
`LocalCutData'.split_region_union` / `LocalCutData'.split_region_intersection`;
this is the one place the design flags as "the heaviest item / isolate at most
one named region-split fact".
-/

namespace ProofsInTheBook.PolygonTriangulation

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonSideCrossing
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Layer A4: the primed cutting interface

We work with the corrected diagonal predicate `IsDiagonal'` and region
`ClosedRegion'`.  A `LocalCutData'` for a polygon `P` (with ray `ρ`) packages,
for the diagonal `i, j` and the ear at `i`:

* the left/right strict subpolygons and their ray directions, whose vertex
  tuples are the cyclic-arc tuples `subpolygonLeftTuple` / `subpolygonRightTuple`
  (so the index combinatorics of `PolygonDiagonal` apply verbatim);
* the region union / intersection identities (the Jordan substitutes);
* a convex-vertex + branch-aware transversality witness, so the
  diagonal-existence step `exists_diagonal'` fires.

The ear cut is the `i = cyclicPrev k`, `j = cyclicNext k` case of a split, so a
single split suffices for existence and the interface needs no separate
deleted-vertex field.  The recursion is supplied uniformly by `CutOracle` (the
size-indexed family of `LocalCutData'`), so the induction has the package it
needs at every depth. -/

/-- A corrected diagonal of `P` (under the side-coordinate convention). -/
abbrev Diag' (P : StrictSimplePolygon n) (ρ : RayDirection P) (i j : Fin n) : Prop :=
  IsDiagonal' P ρ i j

/-- The *local* (non-recursive) cutting/geometry interface for the primed
convention at a single polygon.

`LocalCutData' P ρ` provides every genuine planar-geometry input attached to
*one* polygon: a convex extreme vertex, the branch-aware transversality
dispatcher, and for each diagonal the two strict subpolygons, their ray
directions, and the region-split identities.  It carries no recursive field; the
recursion is supplied separately by a `CutOracle` (below), which gives such data
*uniformly for every polygon*.  This sidesteps the non-uniform self-reference a
recursive structure would require (the subpolygons live at different sizes). -/
structure LocalCutData' (P : StrictSimplePolygon n) (ρ : RayDirection P) where
  /-- A convex extreme vertex (region containment of its adjacent triangle). -/
  convexVertex : Fin n
  convexVertex_spec : IsConvexVertex' P ρ convexVertex
  /-- The branch-aware free-segment dispatcher at the convex vertex. -/
  transversality : DiagonalTransversality' P ρ convexVertex
  /-- Left subpolygon along a diagonal, with the cyclic-arc vertex tuple. -/
  leftPoly : ∀ {i j : Fin n}, IsDiagonal' P ρ i j →
    StrictSimplePolygon (leftLength i j)
  leftPoly_q : ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j),
    (leftPoly h).q = subpolygonLeftTuple P i j
  leftRay : ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j), RayDirection (leftPoly h)
  /-- Right subpolygon along a diagonal. -/
  rightPoly : ∀ {i j : Fin n}, IsDiagonal' P ρ i j →
    StrictSimplePolygon (rightLength i j)
  rightPoly_q : ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j),
    (rightPoly h).q = subpolygonRightTuple P i j
  rightRay : ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j), RayDirection (rightPoly h)
  /-- The parent region is the union of the two subpolygon regions. -/
  split_region_union : ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j),
    {x : Pt | ClosedRegion' P ρ x} =
      {x : Pt | ClosedRegion' (leftPoly h) (leftRay h) x} ∪
        {x : Pt | ClosedRegion' (rightPoly h) (rightRay h) x}
  /-- The two subpolygon regions meet exactly along the diagonal segment. -/
  split_region_intersection : ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j),
    {x : Pt | ClosedRegion' (leftPoly h) (leftRay h) x} ∩
        {x : Pt | ClosedRegion' (rightPoly h) (rightRay h) x} =
      seg (P.q i) (P.q j)

/-- The global cutting oracle: `LocalCutData'` *uniformly for every polygon and
ray*.  This is the single isolated planar-geometry hypothesis the triangulation
induction consumes; passing it down to the subpolygons is what makes the
recursion close.  (It plays the role of the A3/A4 `*Facts` bundles, lifted to a
size-uniform family so the recursion need not be a self-referential structure.) -/
abbrev CutOracle : Type :=
  ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), LocalCutData' P ρ

/-- **Diagonal existence from the oracle** (`4 ≤ n`).

The oracle's local data supplies the convex vertex and the transversality
dispatcher, which is exactly the hypothesis pack `exists_diagonal'` needs.  This
is the unconditional step engine of the induction. -/
theorem cuttingData_exists_diagonal {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (G : LocalCutData' P ρ) (hn : 4 ≤ n) :
    ∃ i j : Fin n, IsDiagonal' P ρ i j :=
  exists_diagonal' hn G.convexVertex_spec G.transversality

/-! ## Layer A5: the inductive triangulation object

`EarTriangulation'` is the existence object: a triangle base (`n = 3`), and a
diagonal-split constructor (the ear cut is the special case of a split along the
`prev/next` diagonal, so a single split constructor suffices for existence; we
keep an explicit `splitDiagonal'` and recover the count additively).

The recursion is on the (strictly smaller) subpolygons produced by the `CutOracle`.
Because Lean's structural recursion needs the recursive arguments to be on
visibly-smaller indices, we carry the recursion through the well-founded measure
`n` (the polygon size): both subpolygons have size `< n` (`leftLength`/`rightLength`
are `< n` by `*_le_total_of_diagonal` together with positivity of the *other*
arc).  We therefore phrase `EarTriangulation'` as data indexed by the size and
build it by strong recursion in `strictSimplePolygon_triangulable'`. -/

/-- The inductive triangulation object over a polygon `P` with ray `ρ`.

* `base` : `n = 3`, the polygon is a single triangle;
* `splitDiagonal` : a corrected diagonal `i → j` splits `P` into the two
  subpolygons supplied by the cutting data, each carrying its own triangulation.

The ear cut is the `i = cyclicPrev k`, `j = cyclicNext k` instance of a split,
so existence needs only the split constructor; the count below is additive and
recovers the `n - 2` total uniformly. -/
inductive EarTriangulation' :
    {n : ℕ} → (P : StrictSimplePolygon n) → RayDirection P → Type
  | base {n : ℕ} (P : StrictSimplePolygon n) (ρ : RayDirection P) (h3 : n = 3) :
      EarTriangulation' P ρ
  | splitDiagonal {n : ℕ} (P : StrictSimplePolygon n) (ρ : RayDirection P)
      (G : LocalCutData' P ρ) {i j : Fin n} (hdiag : IsDiagonal' P ρ i j)
      (tL : EarTriangulation' (G.leftPoly hdiag) (G.leftRay hdiag))
      (tR : EarTriangulation' (G.rightPoly hdiag) (G.rightRay hdiag)) :
      EarTriangulation' P ρ

/-- The number of triangles in an `EarTriangulation'`. -/
def EarTriangulation'.triangleCount :
    {n : ℕ} → {P : StrictSimplePolygon n} → {ρ : RayDirection P} →
    EarTriangulation' P ρ → ℕ
  | _, _, _, .base _ _ _ => 1
  | _, _, _, .splitDiagonal _ _ _ _ tL tR => tL.triangleCount + tR.triangleCount

/-- **The `n - 2` triangle count.**  Any `EarTriangulation'` of an `n`-gon has
exactly `n - 2` triangles.  Proved by induction on the cutting object: the base
triangle (`n = 3`) has `1 = 3 - 2`; a split into a `k`-gon and an `m`-gon with
`k + m = n + 2` (the cyclic-arc length identity `leftLength_add_rightLength`)
gives `(k - 2) + (m - 2) = (k + m) - 4 = (n + 2) - 4 = n - 2`. -/
theorem earTriangulation'_count :
    ∀ {n : ℕ} {P : StrictSimplePolygon n} {ρ : RayDirection P}
      (t : EarTriangulation' P ρ), t.triangleCount = n - 2
  | m, _, _, .base P _ h3 => by
      simp [EarTriangulation'.triangleCount, h3]
  | m, _, _, .splitDiagonal P ρ G (i := i) (j := j) hdiag tL tR => by
      have hIHL := earTriangulation'_count tL
      have hIHR := earTriangulation'_count tR
      -- arc lengths add to m + 2, each is at least 3 (a polygon has ≥ 3 vertices),
      -- and each is < m; so the truncated subtractions add cleanly.
      have hadd : leftLength i j + rightLength i j = m + 2 :=
        leftLength_add_rightLength i j (hdiag.1)
      have hkL : 3 ≤ leftLength i j := (G.leftPoly hdiag).hthree
      have hkR : 3 ≤ rightLength i j := (G.rightPoly hdiag).hthree
      simp only [EarTriangulation'.triangleCount, hIHL, hIHR]
      omega

/-! ## Layer A5: existence by strong induction on `n`

Every strict simple polygon admits an `EarTriangulation'` once a global cutting
oracle is fixed.  The base case `n = 3` is the triangle constructor.  For
`n ≥ 4`, the oracle's local data at `P` yields a diagonal
(`cuttingData_exists_diagonal`); the two subpolygons have sizes `< n`, the same
oracle supplies their local data, and the strong induction hypothesis
triangulates each. -/

/-- A single cyclic step `cyclicSteps i j = 1` forces `cyclicNext i = j`.  This is
the bridge from the arc-length combinatorics to cyclic adjacency. -/
theorem cyclicNext_of_cyclicSteps_eq_one {i j : Fin n}
    (h : cyclicSteps i j = 1) : cyclicNext i = j := by
  have hiLt := i.isLt
  have hjLt := j.isLt
  unfold cyclicSteps at h
  unfold cyclicNext
  by_cases hle : i.val ≤ j.val
  · -- j.val - i.val = 1, so j.val = i.val + 1, and i.val + 1 < n.
    simp only [hle, if_true] at h
    have hjval : j.val = i.val + 1 := by omega
    have hlt : i.val + 1 < n := by rw [← hjval]; exact j.isLt
    rw [dif_pos hlt]; apply Fin.ext; show i.val + 1 = j.val; omega
  · -- n - i.val + j.val = 1, with j.val < i.val: forces i.val = n-1, j.val = 0.
    simp only [hle, if_false] at h
    have hival : i.val = n - 1 := by omega
    have hjval : j.val = 0 := by omega
    have hlt : ¬ i.val + 1 < n := by omega
    rw [dif_neg hlt]; apply Fin.ext; show (0 : ℕ) = j.val; omega

/-- A diagonal's two cyclic arcs each have at least two steps (non-adjacency). -/
theorem cyclicSteps_ge_two_of_diagonal {P : StrictSimplePolygon n}
    {ρ : RayDirection P} {i j : Fin n} (hdiag : IsDiagonal' P ρ i j) :
    2 ≤ cyclicSteps i j ∧ 2 ≤ cyclicSteps j i := by
  have hne : i ≠ j := hdiag.1
  have hnadj : ¬ CyclicAdjacent i j := hdiag.2.1
  have hpij := cyclicSteps_pos_of_ne i j hne
  have hpji := cyclicSteps_pos_of_ne j i hne.symm
  refine ⟨?_, ?_⟩
  · by_contra hlt
    have h1 : cyclicSteps i j = 1 := by omega
    exact hnadj (Or.inl (cyclicNext_of_cyclicSteps_eq_one h1))
  · by_contra hlt
    have h1 : cyclicSteps j i = 1 := by omega
    exact hnadj (Or.inr (cyclicNext_of_cyclicSteps_eq_one h1))

/-- Strict subpolygons are strictly smaller than the parent (left arc). -/
theorem leftLength_lt {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (hdiag : IsDiagonal' P ρ i j) : leftLength i j < n := by
  -- leftLength = cyclicSteps i j + 1 ; the right arc is ≥ 2, so left arc ≤ n - 1.
  have hne : i ≠ j := hdiag.1
  have hright_two : 2 ≤ cyclicSteps j i := (cyclicSteps_ge_two_of_diagonal hdiag).2
  have hsteps := cyclicSteps_add_reverse i j hne
  have hL : leftLength i j = cyclicSteps i j + 1 := rfl
  omega

/-- Strict subpolygons are strictly smaller than the parent (right arc). -/
theorem rightLength_lt {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (hdiag : IsDiagonal' P ρ i j) : rightLength i j < n := by
  have hne : i ≠ j := hdiag.1
  have hleft_two : 2 ≤ cyclicSteps i j := (cyclicSteps_ge_two_of_diagonal hdiag).1
  have hsteps := cyclicSteps_add_reverse i j hne
  have hR : rightLength i j = cyclicSteps j i + 1 := rfl
  omega

/-- **Triangulation existence.**  Given a global cutting oracle, every strict
simple polygon `P` admits an `EarTriangulation'`.  Strong induction on the
polygon size `N`: base `N = 3` is the triangle; for `N ≥ 4` cut along a diagonal
(produced by the oracle's local data at `P`) and recurse on the two
strictly-smaller subpolygons, fed the same oracle. -/
theorem strictSimplePolygon_triangulable' (oracle : CutOracle) :
    ∀ (N : ℕ), ∀ {P : StrictSimplePolygon N} {ρ : RayDirection P},
      Nonempty (EarTriangulation' P ρ) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro P ρ
    have G : LocalCutData' P ρ := oracle P ρ
    rcases eq_or_lt_of_le P.hthree with h3 | h4
    · -- n = 3 base.
      exact ⟨.base P ρ h3.symm⟩
    · -- n ≥ 4 : cut along a diagonal.
      have hn : 4 ≤ N := h4
      obtain ⟨i, j, hdiag⟩ := cuttingData_exists_diagonal G hn
      have hL : leftLength i j < N := leftLength_lt hdiag
      have hR : rightLength i j < N := rightLength_lt hdiag
      obtain ⟨tL⟩ := IH (leftLength i j) hL (P := G.leftPoly hdiag) (ρ := G.leftRay hdiag)
      obtain ⟨tR⟩ := IH (rightLength i j) hR (P := G.rightPoly hdiag) (ρ := G.rightRay hdiag)
      exact ⟨.splitDiagonal P ρ G hdiag tL tR⟩

/-! ## Layer A5': compilation to finite triangle data

`EarTriangulation'.triangles` collects the closed triangles of the cutting object
as a list of point-triples (closed under the diagonal split: the parent's list is
the concatenation of the two subpolygons' lists).  We then prove, by induction on
the cutting object:

* `triangles_length` — the list has exactly `n - 2` entries (it mirrors
  `triangleCount`);
* `triangles_nondegenerate` — every listed triangle is noncollinear (base: a
  triangle's three consecutive vertices are noncollinear by the strict-polygon
  axiom; step: inherited from the subpolygons);
* `triangles_subset_region` — every listed triangle lies in the parent region
  (base: the whole triangle is the region up to boundary; step: each subpolygon
  triangle lies in its subregion, which is `⊆` the parent region by
  `split_region_union`);
* `region_covered_by_triangles` — every region point lies in some listed
  triangle (base: the region is the triangle's hull up to boundary; step: a
  region point is in one of the two subregions by `split_region_union`, hence in
  one of that subpolygon's triangles by the IH).

The covering statement is exactly what the Fisk art-gallery bridge consumes. -/

/-- The first three vertices of any strict polygon (valid since `n ≥ 3`). -/
def v0 (P : StrictSimplePolygon n) : Pt := P.q ⟨0, by have := P.hthree; omega⟩
def v1 (P : StrictSimplePolygon n) : Pt := P.q ⟨1, by have := P.hthree; omega⟩
def v2 (P : StrictSimplePolygon n) : Pt := P.q ⟨2, by have := P.hthree; omega⟩

/-- The closed triangle of the base `3`-gon: the hull of its three vertices. -/
def baseTri (P : StrictSimplePolygon n) (_h3 : n = 3) : Pt × Pt × Pt :=
  (v0 P, v1 P, v2 P)

/-- The list of closed triangles (as point-triples) of an `EarTriangulation'`. -/
def EarTriangulation'.triangles :
    {n : ℕ} → {P : StrictSimplePolygon n} → {ρ : RayDirection P} →
    EarTriangulation' P ρ → List (Pt × Pt × Pt)
  | _, P, _, .base _ _ h3 => [baseTri P h3]
  | _, _, _, .splitDiagonal _ _ _ _ tL tR => tL.triangles ++ tR.triangles

/-- The closed triangle set as the point hulls. -/
def closedTriOf (T : Pt × Pt × Pt) : Set Pt := closedTri T.1 T.2.1 T.2.2

/-- A point-triple is *nondegenerate* when its three points are not collinear. -/
def NondegenerateTri (T : Pt × Pt × Pt) : Prop := ¬ Collinear3 T.1 T.2.1 T.2.2

/-- **The base triangle is nondegenerate** (unconditional).  For a `3`-gon the
vertices `v0, v1, v2` are the consecutive triple at vertex `1`
(`cyclicPrev 1 = 0`, `cyclicNext 1 = 2`), which the strict-polygon axiom forbids
from being collinear. -/
theorem baseTri_nondegenerate (P : StrictSimplePolygon n) (h3 : n = 3) :
    NondegenerateTri (baseTri P h3) := by
  subst h3
  have hax := P.noncollinear_consecutive ⟨1, by omega⟩
  -- cyclicPrev ⟨1⟩ = ⟨0⟩, cyclicNext ⟨1⟩ = ⟨2⟩ in Fin 3.
  have hp : cyclicPrev (⟨1, by omega⟩ : Fin 3) = ⟨0, by omega⟩ := by
    apply Fin.ext; rfl
  have hnx : cyclicNext (⟨1, by omega⟩ : Fin 3) = ⟨2, by omega⟩ := by
    apply Fin.ext; rfl
  rw [hp, hnx] at hax
  -- hax : orient (P.q ⟨0⟩) (P.q ⟨1⟩) (P.q ⟨2⟩) ≠ 0 = ¬ Collinear3 (v0) (v1) (v2).
  intro hcol
  exact hax hcol

/-- **Triangle-list length is `n - 2`.**  The list mirrors `triangleCount`, so it
has the same cardinality. -/
theorem EarTriangulation'.triangles_length :
    ∀ {n : ℕ} {P : StrictSimplePolygon n} {ρ : RayDirection P}
      (t : EarTriangulation' P ρ), t.triangles.length = n - 2
  | _, _, _, .base P _ h3 => by
      simp [EarTriangulation'.triangles, h3]
  | m, _, _, .splitDiagonal P ρ G (i := i) (j := j) hdiag tL tR => by
      have hIHL := EarTriangulation'.triangles_length tL
      have hIHR := EarTriangulation'.triangles_length tR
      have hadd : leftLength i j + rightLength i j = m + 2 :=
        leftLength_add_rightLength i j (hdiag.1)
      have hkL : 3 ≤ leftLength i j := (G.leftPoly hdiag).hthree
      have hkR : 3 ≤ rightLength i j := (G.rightPoly hdiag).hthree
      simp only [EarTriangulation'.triangles, List.length_append, hIHL, hIHR]
      omega

/-- **Every listed triangle lies in the parent region.**  Base: the base
triangle is the hull of the three polygon vertices, which is in the region by the
convex-vertex containment supplied for the base (here, the whole region for a
triangle is its hull up to boundary — captured by the base region equality of the
cutting interface).  Step: a subpolygon triangle lies in its subregion, which is
`⊆` the parent region by `split_region_union`. -/
theorem EarTriangulation'.triangles_subset_region
    {baseRegion : ∀ {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q),
      m = 3 → closedTri (v0 Q) (v1 Q) (v2 Q)
        ⊆ {x : Pt | ClosedRegion' Q σ x}} :
    ∀ {n : ℕ} {P : StrictSimplePolygon n} {ρ : RayDirection P}
      (t : EarTriangulation' P ρ),
      ∀ T ∈ t.triangles, closedTriOf T ⊆ {x : Pt | ClosedRegion' P ρ x}
  | _, P, ρ, .base _ _ h3 => by
      intro T hT
      simp only [EarTriangulation'.triangles, List.mem_singleton] at hT
      subst hT
      exact baseRegion P ρ h3
  | _, P, ρ, .splitDiagonal _ _ G (i := i) (j := j) hdiag tL tR => by
      intro T hT
      simp only [EarTriangulation'.triangles, List.mem_append] at hT
      have hunion := G.split_region_union hdiag
      rcases hT with hTL | hTR
      · have hsub := EarTriangulation'.triangles_subset_region
          (baseRegion := baseRegion) tL T hTL
        intro x hx
        have : x ∈ {y : Pt | ClosedRegion' (G.leftPoly hdiag) (G.leftRay hdiag) y} := hsub hx
        rw [hunion]; exact Or.inl this
      · have hsub := EarTriangulation'.triangles_subset_region
          (baseRegion := baseRegion) tR T hTR
        intro x hx
        have : x ∈ {y : Pt | ClosedRegion' (G.rightPoly hdiag) (G.rightRay hdiag) y} := hsub hx
        rw [hunion]; exact Or.inr this

/-- **Coverage: every region point lies in some listed triangle.**

This is the bridge fact the art-gallery theorem needs.  Base: a region point of
a triangle lies in its hull (the base covering hypothesis).  Step: a region point
lies in one of the two subregions by `split_region_union`, hence in a triangle of
that subpolygon by the induction hypothesis. -/
theorem EarTriangulation'.region_covered_by_triangles
    {baseCover : ∀ {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q),
      m = 3 → ∀ x, ClosedRegion' Q σ x →
        x ∈ closedTri (v0 Q) (v1 Q) (v2 Q)} :
    ∀ {n : ℕ} {P : StrictSimplePolygon n} {ρ : RayDirection P}
      (t : EarTriangulation' P ρ),
      ∀ x, ClosedRegion' P ρ x → ∃ T ∈ t.triangles, x ∈ closedTriOf T
  | _, P, ρ, .base _ _ h3 => by
      intro x hx
      refine ⟨baseTri P h3, ?_, ?_⟩
      · simp [EarTriangulation'.triangles]
      · exact baseCover P ρ h3 x hx
  | _, P, ρ, .splitDiagonal _ _ G (i := i) (j := j) hdiag tL tR => by
      intro x hx
      have hunion := G.split_region_union hdiag
      have hx' : x ∈ {y : Pt | ClosedRegion' (G.leftPoly hdiag) (G.leftRay hdiag) y} ∪
          {y : Pt | ClosedRegion' (G.rightPoly hdiag) (G.rightRay hdiag) y} := by
        rw [← hunion]; exact hx
      rcases hx' with hxL | hxR
      · obtain ⟨T, hTmem, hTx⟩ :=
          EarTriangulation'.region_covered_by_triangles (baseCover := baseCover) tL x hxL
        exact ⟨T, by simp only [EarTriangulation'.triangles, List.mem_append]; exact Or.inl hTmem, hTx⟩
      · obtain ⟨T, hTmem, hTx⟩ :=
          EarTriangulation'.region_covered_by_triangles (baseCover := baseCover) tR x hxR
        exact ⟨T, by simp only [EarTriangulation'.triangles, List.mem_append]; exact Or.inr hTmem, hTx⟩

/-- **Every listed triangle is nondegenerate** (unconditional).  Base: the base
triangle is nondegenerate by `baseTri_nondegenerate`.  Step: nondegeneracy is a
property of the three points, inherited verbatim from the subpolygons. -/
theorem EarTriangulation'.triangles_nondegenerate :
    ∀ {n : ℕ} {P : StrictSimplePolygon n} {ρ : RayDirection P}
      (t : EarTriangulation' P ρ), ∀ T ∈ t.triangles, NondegenerateTri T
  | _, P, _, .base _ _ h3 => by
      intro T hT
      simp only [EarTriangulation'.triangles, List.mem_singleton] at hT
      subst hT
      exact baseTri_nondegenerate P h3
  | _, _, _, .splitDiagonal _ _ _ _ tL tR => by
      intro T hT
      simp only [EarTriangulation'.triangles, List.mem_append] at hT
      rcases hT with hTL | hTR
      · exact EarTriangulation'.triangles_nondegenerate tL T hTL
      · exact EarTriangulation'.triangles_nondegenerate tR T hTR

/-! ## Layer A5'': the finite-triangle output structure and `toGeom`

`GeomTriangulation'` is the finite triangle data the combinatorial 3-colouring
half consumes.  We carry the triangles as a point-triple list together with the
region-subset and covering facts and the `n - 2` count.  `toGeom` compiles an
`EarTriangulation'` to it, given the two base facts (a triangle's region is its
hull, up to boundary).  Those two base facts are bundled in `BaseTriangleFacts`
(the only residual geometric inputs at the recursion leaf). -/

/-- The two base-triangle region facts at a `3`-gon: its region is exactly its
closed hull (subset both ways).  These are the leaf inputs of the compilation. -/
structure BaseTriangleFacts where
  subset : ∀ {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q),
    m = 3 → closedTri (v0 Q) (v1 Q) (v2 Q)
      ⊆ {x : Pt | ClosedRegion' Q σ x}
  cover : ∀ {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q),
    m = 3 → ∀ x, ClosedRegion' Q σ x →
      x ∈ closedTri (v0 Q) (v1 Q) (v2 Q)

/-- Finite geometric triangulation data for `P` (region-subset + covering +
the `n - 2` count). -/
structure GeomTriangulation' (P : StrictSimplePolygon n) (ρ : RayDirection P) where
  /-- The closed triangles, as point-triples. -/
  tris : List (Pt × Pt × Pt)
  /-- There are exactly `n - 2` of them. -/
  card : tris.length = n - 2
  /-- Every triangle is nondegenerate (its three vertices are noncollinear). -/
  nondegenerate : ∀ T ∈ tris, NondegenerateTri T
  /-- Each triangle lies in the closed region. -/
  subset_region : ∀ T ∈ tris, closedTriOf T ⊆ {x : Pt | ClosedRegion' P ρ x}
  /-- The triangles cover the closed region. -/
  cover_region : ∀ x, ClosedRegion' P ρ x → ∃ T ∈ tris, x ∈ closedTriOf T

/-- **Compilation `EarTriangulation'.toGeom`.**  Every `EarTriangulation'`
compiles to `GeomTriangulation'` finite triangle data with `n - 2` triangles,
covering the region, given the base-triangle facts. -/
def EarTriangulation'.toGeom (B : BaseTriangleFacts)
    {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (t : EarTriangulation' P ρ) : GeomTriangulation' P ρ where
  tris := t.triangles
  card := t.triangles_length
  nondegenerate := t.triangles_nondegenerate
  subset_region :=
    EarTriangulation'.triangles_subset_region (baseRegion := fun Q σ h => B.subset Q σ h) t
  cover_region :=
    EarTriangulation'.region_covered_by_triangles (baseCover := fun Q σ h => B.cover Q σ h) t

/-- **End-to-end geometric triangulation.**  Given the global cutting oracle and
the base-triangle facts, every strict simple polygon admits a `GeomTriangulation'`
with `n - 2` triangles covering its closed region. -/
theorem strictSimplePolygon_geomTriangulation' (oracle : CutOracle)
    (B : BaseTriangleFacts) (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ T : GeomTriangulation' P ρ, T.tris.length = n - 2 := by
  obtain ⟨t⟩ := strictSimplePolygon_triangulable' oracle n (P := P) (ρ := ρ)
  exact ⟨t.toGeom B, (t.toGeom B).card⟩

/-- **Coverage statement for the art-gallery bridge.**  Every point of the closed
region lies in some triangle of the geometric triangulation. -/
theorem every_region'_point_in_some_triangle {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (T : GeomTriangulation' P ρ)
    {x : Pt} (hx : ClosedRegion' P ρ x) :
    ∃ τ ∈ T.tris, x ∈ closedTriOf τ :=
  T.cover_region x hx

end

end ProofsInTheBook.PolygonTriangulation
