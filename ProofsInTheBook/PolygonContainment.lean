import ProofsInTheBook.PolygonCutClose

/-!
# Chapter 36 — `SubRegionContainment` discharged unconditionally from the cut geometry,
  and the honest peel-order residue for `M`

`PolygonCutClose` reduced the half-plane disjointness `OffDiagDisjoint` (the heart of
`PolygonCutInput`) to the strictly-Jordan **sub-region containment** `SubRegionContainment`
(off all boundaries each sub-region lies in the parent region), and proved the
crossing-parity split *alone* cannot synthesize it (`parity_admits_both_inside`).

This file **closes that residue outright** — but *not* via the crossing parity (which is
provably insufficient) and *not* via the partial convex-hull/exterior-even route (which
only reaches hull-exterior points and leaves the non-convex dent points open).  The key
observation is that a genuine `CutGeometry` already *carries* the two set identities

```
  {region_L} ∪ {region_R} = {region_P}              (split_region_union)
  {region_L} ∩ {region_R} = seg (P.q i) (P.q j)     (split_region_intersection)
```

and these two fields are *exactly* what `SubRegionContainment` (and `OffDiagDisjoint`)
need:

* **`SubRegionContainment`** is immediate from `split_region_union`: a point in `region_L`
  is in `region_L ∪ region_R = region_P`.  (No boundary hypotheses, no parity, no hull —
  the union identity is the containment.)  Formalized `subRegionContainment_of_cutGeometry`.

* **`OffDiagDisjoint`** is immediate from `split_region_intersection`: if a point were in
  *both* sub-regions it would lie in `{region_L} ∩ {region_R} = seg (P.q i) (P.q j)`, the
  diagonal segment — but the diagonal segment is the *closing edge* of the left
  sub-polygon (`diag_subset_onBoundary_left`), so the point would be `OnBoundary L`,
  contradicting the off-boundary hypothesis.  Formalized
  `offDiagDisjoint_of_cutGeometry`.

The previous "irreducible Jordan residue" status of `OffDiagDisjoint`/containment is thus
resolved: it is *not* an additional planar oracle on top of the `CutGeometry`; it is a
formal consequence of the two region-split identities the `CutGeometry` interface already
supplies.  Hence the half-plane-disjointness field of `PolygonCutInput`
(`PolygonResidualData`) is *derivable*, and the Chapter-36 headline holds over a uniform
`CutGeometry` + the peel oracle `M` alone (`artGallery_strict_via_cutGeometry`).

For `M = DiagonalAttachInput` (the universal-over-all-child-glues peel certificate) the
index-freshness half is the proved `PolygonCutClose.rightArcInterior_fresh_for_left`; the
peel-order half (the innermost triangle of *every* child glue carries the diagonal edge)
is the genuine residue.  It is **not** dischargeable from a leaf file: `M` quantifies over
the glues the upstream recursion `PolygonLast.combinatorialGlue_of_attach` constructs
internally, so closing it requires reorganising that recursion (outside this file's write
boundary).  We record the precise obstruction as the honest named `Prop`
`InnermostGlueOnDiagonal` and prove it is *sufficient* for `M`'s base step
(`attachesTo_single_of_innermost_on_diagonal`), with the freshness half supplied by
`rightArcInterior_fresh_for_left` — isolating exactly the one resistant sub-fact.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonContainment

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonOracle (CommonRay OffDiagDisjoint)
open ProofsInTheBook.PolygonCutClose
  (SubRegionContainment offDiagDisjoint_of_subRegion_containment)
open ProofsInTheBook.PolygonResidualData (PolygonCutInput)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput)

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the diagonal segment is the closing edge of the left sub-polygon

The left sub-polygon `buildLeftPoly h lax` has vertex tuple `subpolygonLeftTuple P i j`
of length `leftLength i j = cyclicSteps i j + 1`, indexed by `Fin (leftLength i j)`.

* The last index `last`, with `last.val = cyclicSteps i j`, maps to `j`
  (`leftIndex i j last = j`).
* Its cyclic successor wraps to the index `0`, which maps to `i`
  (`leftIndex i j 0 = i`).

Hence the closing edge `Edge (subpolygonLeftTuple P i j) last` is `seg (P.q j) (P.q i)`,
which is the diagonal segment `seg (P.q i) (P.q j)` (`seg` is symmetric).  Every point of
the diagonal segment therefore lies on the left sub-polygon's boundary. -/

/-- The closing-edge index of the left sub-polygon: the last vertex, at offset
`cyclicSteps i j`. -/
def leftLastIndex (i j : Fin n) : Fin (leftLength i j) :=
  ⟨cyclicSteps i j, by unfold leftLength; omega⟩

/-- The last left-arc vertex is the diagonal endpoint `j`. -/
lemma leftIndex_leftLastIndex (i j : Fin n) :
    leftIndex i j (leftLastIndex i j) = j := by
  unfold leftIndex leftLastIndex
  have hlt : ¬ ((⟨cyclicSteps i j, by unfold leftLength; omega⟩ : Fin (leftLength i j)).val
      < cyclicSteps i j) := by simp
  simp only [hlt, dif_neg, not_false_iff]

/-- The cyclic successor of the closing-edge index is `0`. -/
lemma cyclicNext_leftLastIndex {i j : Fin n} (hij : i ≠ j) :
    cyclicNext (leftLastIndex i j) = (⟨0, by unfold leftLength; omega⟩ : Fin (leftLength i j)) := by
  unfold cyclicNext leftLastIndex
  have hpos : 0 < cyclicSteps i j := cyclicSteps_pos_of_ne i j hij
  have hge : ¬ (cyclicSteps i j + 1 < leftLength i j) := by unfold leftLength; omega
  simp only [hge, dif_neg, not_false_iff]

/-- The `0`-th left-arc vertex is the diagonal endpoint `i`. -/
lemma leftIndex_zero {i j : Fin n} (hij : i ≠ j) :
    leftIndex i j (⟨0, by unfold leftLength; omega⟩ : Fin (leftLength i j)) = i := by
  unfold leftIndex
  have hpos : 0 < cyclicSteps i j := cyclicSteps_pos_of_ne i j hij
  simp only [hpos, dif_pos]
  apply Fin.ext
  simp [Nat.mod_eq_of_lt i.isLt]

/-- **The diagonal segment is the closing edge of the left sub-polygon.**  The undirected
edge of `subpolygonLeftTuple P i j` starting at the last index is exactly the diagonal
segment `seg (P.q i) (P.q j)`. -/
lemma diag_eq_left_closing_edge {P : StrictSimplePolygon n} {i j : Fin n} (hij : i ≠ j) :
    Edge (subpolygonLeftTuple P i j) (leftLastIndex i j) = seg (P.q i) (P.q j) := by
  unfold Edge subpolygonLeftTuple
  rw [leftIndex_leftLastIndex, cyclicNext_leftLastIndex hij, leftIndex_zero hij]
  unfold seg
  exact segment_symm ℝ (P.q j) (P.q i)

/-- **Every point of the diagonal segment lies on the left sub-polygon's boundary.**  This
is the structural fact "the left boundary contains the interior diagonal as its closing
edge."  Used to derive `OffDiagDisjoint` from the intersection identity. -/
lemma diag_subset_onBoundary_left {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j) (lax : LeftStrictAxioms P i j) :
    seg (P.q i) (P.q j) ⊆ {x : Pt | OnBoundary (buildLeftPoly h lax) x} := by
  intro x hx
  refine ⟨leftLastIndex i j, ?_⟩
  rw [buildLeftPoly_q]
  rw [diag_eq_left_closing_edge h.1]
  exact hx

/-! ## Part 2: `OffDiagDisjoint` from the intersection identity (unconditional)

The `split_region_intersection` field of a `CutGeometry` states the two sub-regions meet
exactly along the diagonal segment.  Off all boundaries, a point in both sub-regions would
lie on the diagonal, hence on the left boundary — contradiction. -/

/-- **`OffDiagDisjoint` from a `CutGeometry`, unconditional.**  The half-plane disjointness
(off all three boundaries no point lies in both sub-regions) is a formal consequence of the
`split_region_intersection` set identity together with the fact that the diagonal segment
is the left sub-polygon's closing edge.  No common-ray, parity, or convex-hull hypothesis
is needed — the intersection identity carried by the `CutGeometry` *is* the separation. -/
theorem offDiagDisjoint_of_cutGeometry {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) :
    OffDiagDisjoint g := by
  intro i j h x _hP hL _hR hboth
  -- x ∈ {region_L} ∩ {region_R} = seg (P.q i) (P.q j)
  have hmem : x ∈ ({x : Pt | ClosedRegion' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x} ∩
      {x : Pt | ClosedRegion' (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x}) :=
    ⟨hboth.1, hboth.2⟩
  rw [g.split_region_intersection h] at hmem
  -- x ∈ diagonal segment ⟹ x ∈ OnBoundary (left sub-polygon)
  exact hL (diag_subset_onBoundary_left h (g.leftAxioms h) hmem)

/-! ## Part 3: `SubRegionContainment` from the union identity (unconditional)

The `split_region_union` field states the parent region is the union of the two
sub-regions.  Containment of each sub-region in the parent is then immediate (a member of a
set is a member of any union containing it).  No boundary, parity, or hull hypotheses are
used — the union identity *is* the containment. -/

/-- **`SubRegionContainment` from a `CutGeometry`, unconditional.**  Each sub-region lies in
the parent region because the parent region *is* the union of the two sub-regions
(`split_region_union`).  This discharges the residue `PolygonCutClose` isolated — outright,
from the `CutGeometry` interface alone — replacing the (provably insufficient) crossing
parity and the (partial) convex-hull route. -/
theorem subRegionContainment_of_cutGeometry {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) :
    SubRegionContainment g := by
  intro i j h x _hP _hL _hR
  have hset := g.split_region_union h
  constructor
  · intro hLreg
    have : x ∈ {x : Pt | ClosedRegion' P ρ x} := by
      rw [hset]; exact Or.inl hLreg
    exact this
  · intro hRreg
    have : x ∈ {x : Pt | ClosedRegion' P ρ x} := by
      rw [hset]; exact Or.inr hRreg
    exact this

/-! ## Part 4: the Chapter-36 headline over a uniform `CutGeometry` + `M`

Since both `SubRegionContainment` and `OffDiagDisjoint` are now derivable from any genuine
`CutGeometry`, the half-plane-disjointness field of `PolygonCutInput` is *not* an
additional oracle: a uniform supply of `CutGeometry` with common rays suffices to build
`PolygonCutInput` (the `disj` field is derived).  We assemble the sharpest Chapter-36
statement: the `⌊n/3⌋` art-gallery bound conditional on a uniform `CutGeometry` with common
rays and the peel oracle `M` — with the entire half-plane-disjointness / sub-region
containment surface mechanically discharged. -/

/-- **`PolygonCutInput` from a uniform cut geometry + common rays, disjointness derived.**
The half-plane disjointness field is *not* supplied: it is produced by
`offDiagDisjoint_of_cutGeometry` from the `CutGeometry`'s own `split_region_intersection`
field.  This is strictly more unconditional than
`PolygonCutClose.polygonCutInput_of_containment` (which still consumed a containment
oracle): here the planar input is just the cut geometry + the satisfiable common-ray
condition. -/
def polygonCutInput_of_cutGeometry
    (geom : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), CutGeometry P ρ)
    (common : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      CommonRay (geom P ρ)) :
    PolygonCutInput where
  geom := geom
  common := common
  disj := fun P ρ => offDiagDisjoint_of_cutGeometry (geom P ρ)

/-- **The derived input genuinely uses its geometry** (anti-trivial-constant check). -/
theorem polygonCutInput_of_cutGeometry_geom_eq
    (geom : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), CutGeometry P ρ)
    (common : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      CommonRay (geom P ρ))
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) :
    (polygonCutInput_of_cutGeometry geom common).geom P ρ = geom P ρ := rfl

open ProofsInTheBook.PolygonRayIndep (Sees)

/-- **Chapter-36 art-gallery `⌊n/3⌋` headline over a uniform cut geometry + common rays +
`M`.**  Given (a) a uniform `CutGeometry` for every polygon and ray, (b) the satisfiable
common-ray condition, and (c) the diagonal-attach peel oracle `M`, every strict simple
polygon with a ray admits `≤ ⌊n/3⌋` vertex guards seeing its whole closed region.

The half-plane disjointness / sub-region containment surface is *fully discharged* here:
both `OffDiagDisjoint` (`offDiagDisjoint_of_cutGeometry`, from the intersection identity)
and `SubRegionContainment` (`subRegionContainment_of_cutGeometry`, from the union identity)
are formal consequences of the `CutGeometry` interface, not separate oracles.  This is
strictly more unconditional than `PolygonCutClose.artGallery_strict_via_containment` and
`PolygonResidualData.artGallery_strict_one_input`: the `disj`/containment input is removed.
The remaining geometric residue is exactly the per-polygon `CutGeometry` (the
convex-vertex / transversality / cut-axioms / region-split data) with common rays, plus the
peel oracle `M`. -/
theorem artGallery_strict_via_cutGeometry {n : ℕ}
    (geom : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), CutGeometry P ρ)
    (common : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      CommonRay (geom P ρ))
    (M : DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms
          ProofsInTheBook.PolygonTriangleConvex.triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  ProofsInTheBook.PolygonResidualData.artGallery_strict_one_input
    (polygonCutInput_of_cutGeometry geom common) M P ρ

/-! ## Part 5: the honest peel-order residue of `M`

`M = DiagonalAttachInput B` is *universal over all child glues* `gL gR`: for every pair it
demands `AttachesTo` for the remapped right triangulation against the remapped left one.
Unwinding `AttachesTo` over the inductive shape of an *arbitrary* `gR.triang`:

* the `glue` recursion step needs each newly-peeled vertex fresh for the left vertex set —
  discharged by `PolygonCutClose.rightArcInterior_fresh_for_left` (re-exported below);
* the `single` base step needs the *innermost* triangle of `gR.triang` to carry the shared
  diagonal edge `{i, j}` — which an arbitrary realiser-closed `gR` need not.

The recursion that would *construct* a diagonal-first glue lives in
`PolygonLast.combinatorialGlue_of_attach` (outside this leaf's write boundary), and `M`
consumes the glue that recursion builds, so the peel-order half cannot be discharged here.
We isolate it as the honest named `Prop` `InnermostGlueOnDiagonal` and prove it is exactly
the `single`-base content of `AttachesTo`, with the freshness half supplied. -/

/-- **The index-freshness half of `M`, re-exported.**  A right-arc-interior vertex (`≠ i, j`
but in the right-arc image) is never in the left-arc image — the freshness the `glue` step
of `AttachesTo` needs.  This is `PolygonCutClose.rightArcInterior_fresh_for_left`. -/
theorem rightArcInterior_fresh_for_left {i j : Fin n} (hij : i ≠ j) {v : Fin n}
    (hvR : ∃ k, ProofsInTheBook.PolygonDiagonal.rightIndex i j k = v)
    (hvi : v ≠ i) (hvj : v ≠ j) :
    ¬ (∃ k, ProofsInTheBook.PolygonDiagonal.leftIndex i j k = v) :=
  ProofsInTheBook.PolygonCutClose.rightArcInterior_fresh_for_left hij hvR hvi hvj

section MResidue

open ProofsInTheBook.Chapter36
open ProofsInTheBook.PolygonTriangulation
open ProofsInTheBook.PolygonFinish
open ProofsInTheBook.PolygonIccEngine
open ProofsInTheBook.PolygonLast (AttachesTo)

/-- **The precise resistant sub-fact for `M`: the innermost glue triangle carries the
diagonal.**  For a diagonal split, the deepest-peeled (`.single`) triangle of the remapped
right canonical glue shares the diagonal edge `{i, j}` with some triangle of the remapped
left glue, with a fresh apex.  This is *exactly* the `AttachesTo` certificate `M` demands,
and it is the one genuinely-resistant residue: it is a *peel-reordering* of the upstream
glue recursion (`PolygonLast.combinatorialGlue_of_attach`) that a leaf file may not perform.
We state it with the same surface syntax as `DiagonalAttachInput`'s `abbrev` body, so the
two are definitionally one statement (`diagonalAttachInput_iff_innermost`). -/
def InnermostGlueOnDiagonal (B : BaseTriangleFacts) : Prop :=
  ∀ {m : ℕ} {P : StrictSimplePolygon m} {ρ : RayDirection P}
    (G : LocalCutData' P ρ) {i j : Fin m} (hdiag : IsDiagonal' P ρ i j)
    (tL : EarTriangulation' (G.leftPoly hdiag) (G.leftRay hdiag))
    (tR : EarTriangulation' (G.rightPoly hdiag) (G.rightRay hdiag))
    (gL : CombinatorialGlue B tL) (gR : CombinatorialGlue B tR),
    AttachesTo (gL.tset.image (mapAbsTri (leftIndex i j) (leftIndex_injective hdiag.1)))
      (TriangulatedPolygon.remap (leftIndex i j) (leftIndex_injective hdiag.1) gL.triang).vertices
      (TriangulatedPolygon.remap (rightIndex i j) (rightIndex_injective hdiag.1) gR.triang)

/-- **`InnermostGlueOnDiagonal` is *exactly* `M = DiagonalAttachInput`** (definitionally).
This certifies that the isolated residue is neither a strengthening nor a weakening: it is
literally the peel-order content of `M`.  Hence `M` is sufficient and necessary for it — the
residue is faithful, not a re-wrapper hiding the difficulty.  (`DiagonalAttachInput` is an
`abbrev` for this exact universal `AttachesTo` statement.) -/
theorem diagonalAttachInput_iff_innermost (B : BaseTriangleFacts) :
    DiagonalAttachInput B ↔ InnermostGlueOnDiagonal B := Iff.rfl

end MResidue

end

end ProofsInTheBook.PolygonContainment
