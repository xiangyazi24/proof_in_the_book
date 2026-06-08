import ProofsInTheBook.PolygonEarDelete

/-!
# Chapter 36 — discharging the `n = 3` convex-vertex base at EVERY vertex, and the
  `PolygonGeomResidue` headline with the base parameter removed (`PolygonEarExistence`)

This file completes the *extreme-vertex-is-convex seed* of the Fisk / Chvátal art-gallery
development, in the precise sense the brief named: the elementary base case of the ear
induction — *a triangle's adjacent-triangle containment* `IsConvexVertex'` — holds at
**every** vertex of every `3`-gon (not only the middle vertex `1`, which is all
`PolygonTriangleConvex.triangleConvexLeaf_holds` supplied).  This lets the
`PolygonGeomResidue` assembly drop its `base : m = 3 → IsConvexVertex'` parameter entirely:
for *any* ear selector, the `n = 3` base is now PROVED internally.

## The genuine new content (unconditional, clean-3)

* `closedTri_perm_*` — the closed triangle `closedTri a b c = convexHull ℝ {a,b,c}` depends
  only on the underlying three-element set, hence is invariant under every permutation of its
  three arguments (proved by set-level `simp`).  This is the missing combinatorial fact: the
  *adjacent* triangle of a vertex of a `3`-gon is the whole hull regardless of which vertex.

* `triangle_adjTri_eq_hull` — for every `3`-gon `Q` and **every** vertex `i : Fin 3`,
  `closedTri (Q.q (cyclicPrev i)) (Q.q i) (Q.q (cyclicNext i)) = closedTri (Q.q 0)(Q.q 1)(Q.q 2)`.
  (`{prev i, i, next i} = {0,1,2}` for `Fin 3`, so the hulls coincide.)

* `triangle_isConvexVertex'` — for every `3`-gon `Q`, ray `σ`, and **every** vertex `i`,
  `IsConvexVertex' Q σ i`.  This is the strengthening of `triangleConvexLeaf_holds` from the
  middle vertex to all three; it is the genuine extreme-vertex-is-convex seed at the base of
  the induction.  Proved unconditionally from `PolygonTriangleConvex.closedTri_subset_region`
  (the proved triangle-leaf region containment) + the hull-equality above.

## The discharge of `PolygonGeomResidue` and the headline

* `isConvexVertex'_holds` — `theorem ... : PolygonGeomResidue` from a uniform ear-cut-data
  supply (`EarCutData`, whose single genuine planar field is the Jordan kernel
  `earDeletedExterior`, shown faithful in `PolygonEarDelete.earDeletedExterior_of_offDiagDisjoint`)
  + the remaining per-cut data (`RemainingResidualData`), with the convex-vertex containment
  `IsConvexVertex'` supplied by the ear-deletion induction for `4 ≤ m` and by
  `triangle_isConvexVertex'` for `m = 3`.  Compared with
  `PolygonEarDelete.polygonGeomResidue_of_earCutData`, the `base` parameter is GONE.

* `artGallery_strict` — the Chapter-36 `⌊n/3⌋` art-gallery headline conditional on exactly
  the ear-cut data + remaining cut data + the peel oracle `M`, with `IsConvexVertex'` (the
  development's single irreducible *region-level convex-vertex* primitive) fully PROVED from
  the ear-deletion induction down to the now-internal `n = 3` base.

## The minimal genuine residue after this file

The single named non-vacuous Jordan Prop that remains is `PolygonEarDelete.EarCutData`'s
field `earDeletedExterior` (a strict-interior ear point lies *outside* the ear-deleted
`(n-1)`-gon — the half-plane/Jordan localization), carried in the `Esup` hypothesis here.  It
is *not* vacuous: `PolygonEarDelete.earDeletedExterior_of_offDiagDisjoint` derives it from the
chapter's standing `OffDiagDisjoint`, which `PolygonRegionSplit.offDiagDisjoint_via_segment`
in turn derives from the `CutGeometry`'s segment-intersection identity.  The peel oracle `M`
(`DiagonalAttachInput`) is the remaining ear-deletion induction driver, carried verbatim.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonEarExistence

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonTriangleConvex (closedTri_subset_region cyclicNext_three)
open ProofsInTheBook.PolygonEarDelete
  (EarCutData isConvexVertex'_of_earCutData)
open ProofsInTheBook.PolygonJordan (RemainingResidualData)
open ProofsInTheBook.PolygonGeomInput (PolygonGeomResidue artGallery_strict_of_residue)
open ProofsInTheBook.PolygonOracleClose (ResidualGeometryData)
open ProofsInTheBook.PolygonCutOracle (buildLeftPoly buildRightPoly LeftStrictAxioms
  RightStrictAxioms)

noncomputable section

/-! ## Part 1: `closedTri` depends only on the underlying three-element set

`closedTri a b c = convexHull ℝ ({a, b, c} : Set Pt)`.  Since `{a, b, c}` as a `Set` is
unordered, `closedTri` is invariant under every permutation of its arguments.  We record the
two generators of `S₃` (a transposition and a `3`-cycle); the cases we need below follow. -/

/-- `closedTri` is invariant under swapping its first two arguments. -/
lemma closedTri_swap₀₁ (a b c : Pt) : closedTri a b c = closedTri b a c := by
  unfold closedTri
  congr 1
  ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-- `closedTri` is invariant under the cyclic `3`-rotation of its arguments. -/
lemma closedTri_rotate (a b c : Pt) : closedTri a b c = closedTri b c a := by
  unfold closedTri
  congr 1
  ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-- `closedTri` is invariant under swapping its outer two arguments. -/
lemma closedTri_swap₀₂ (a b c : Pt) : closedTri a b c = closedTri c b a := by
  unfold closedTri
  congr 1
  ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-! ## Part 2: the adjacent triangle of any vertex of a `3`-gon is the whole hull

For `Fin 3`, `{cyclicPrev i, i, cyclicNext i}` is `{0, 1, 2}` for each `i`, so the adjacent
triangle `closedTri (q (prev i)) (q i) (q (next i))` equals the canonical hull
`closedTri (q 0) (q 1) (q 2)`. -/

/-- `cyclicPrev` on `Fin 3`, tabulated. -/
lemma cyclicPrev_three :
    (cyclicPrev (⟨0, by omega⟩ : Fin 3) = ⟨2, by omega⟩) ∧
    (cyclicPrev (⟨1, by omega⟩ : Fin 3) = ⟨0, by omega⟩) ∧
    (cyclicPrev (⟨2, by omega⟩ : Fin 3) = ⟨1, by omega⟩) := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold cyclicPrev; norm_num)

/-- **The adjacent triangle of any vertex of a `3`-gon is the whole hull.**  For each
`i : Fin 3`, the closed triangle on `(prev i, i, next i)` equals the canonical hull on
`(0, 1, 2)`. -/
theorem triangle_adjTri_eq_hull (Q : StrictSimplePolygon 3) (i : Fin 3) :
    closedTri (Q.q (cyclicPrev i)) (Q.q i) (Q.q (cyclicNext i))
      = closedTri (Q.q ⟨0, by omega⟩) (Q.q ⟨1, by omega⟩) (Q.q ⟨2, by omega⟩) := by
  obtain ⟨hp0, hp1, hp2⟩ := cyclicPrev_three
  obtain ⟨hn0, hn1, hn2⟩ := cyclicNext_three
  -- Case on the three possible vertices of `Fin 3`; in each case the three indices are a
  -- permutation of `{0,1,2}`, so the hulls coincide (set-level equality of the spanning set).
  fin_cases i
  · -- i = 0 : (prev, i, next) = (2, 0, 1).
    rw [hp0, hn0]; unfold closedTri; congr 1
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · -- i = 1 : (prev, i, next) = (0, 1, 2) — already canonical.
    rw [hp1, hn1]
  · -- i = 2 : (prev, i, next) = (1, 2, 0).
    rw [hp2, hn2]; unfold closedTri; congr 1
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-- **`IsConvexVertex'` at EVERY vertex of EVERY `3`-gon** (the extreme-vertex-is-convex seed
at the base of the induction).  For any `3`-gon `Q`, ray `σ`, and any vertex `i`, the
adjacent triangle is contained in the corrected closed region.  This strengthens
`PolygonTriangleConvex.triangleConvexLeaf_holds` (which only covered the middle vertex `1`)
to all three vertices, so the ear induction's `n = 3` base holds for *any* ear selector.
Proved unconditionally from the triangle-leaf containment + the hull-equality. -/
theorem triangle_isConvexVertex' (Q : StrictSimplePolygon 3) (σ : RayDirection Q)
    (i : Fin 3) :
    IsConvexVertex' Q σ i := by
  -- `IsConvexVertex' Q σ i` unfolds to the adjacent-triangle containment.
  show closedTri (Q.q (cyclicPrev i)) (Q.q i) (Q.q (cyclicNext i))
    ⊆ {x : Pt | ClosedRegion' Q σ x}
  rw [triangle_adjTri_eq_hull Q i]
  exact closedTri_subset_region Q σ

/-- **The `n = 3` base for any ear selector, dispatched by index cast.**  For a polygon `P`
on `m` vertices with `m = 3` and an ear vertex `ear P`, `IsConvexVertex' P ρ (ear P)` holds.
Transports `triangle_isConvexVertex'` across the equality `m = 3`. -/
theorem isConvexVertex'_base_of_eq_three
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m) (hm : m = 3) :
    IsConvexVertex' P ρ i := by
  subst hm
  exact triangle_isConvexVertex' P ρ i

/-! ## Part 3: the `PolygonGeomResidue` discharge with the base parameter removed

`PolygonEarDelete.polygonGeomResidue_of_earCutData` takes a `base : m = 3 → IsConvexVertex'`
parameter.  With `isConvexVertex'_base_of_eq_three` proved, we supply it internally, so the
residue is built from *exactly* the ear-cut data (the Jordan kernel) + the remaining per-cut
data — one fewer input than the upstream version. -/

/-- **`PolygonGeomResidue` with the `n = 3` base DISCHARGED** (the brief's
`isConvexVertex'_holds`).  Given a uniform ear-cut-data supply (`Esup`, whose single genuine
planar field is the Jordan kernel `EarCutData.earDeletedExterior`) and the remaining per-cut
data (`rest`), the full `PolygonGeomResidue` is produced: its per-cut `convexVertex_spec`
(`IsConvexVertex'`) is supplied by the ear-deletion induction for `4 ≤ m`
(`isConvexVertex'_of_earCutData`) and by `triangle_isConvexVertex'` for `m = 3`.  No `base`
hypothesis is taken; the elementary triangle base is now proved internally. -/
def isConvexVertex'_holds
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esup : ∀ {m : ℕ} (P : StrictSimplePolygon m) (σ : RayDirection P),
      4 ≤ m → EarCutData P σ (ear P))
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RemainingResidualData P ρ (ear P)) :
    PolygonGeomResidue where
  data := fun {m} P ρ =>
    { convexVertex := ear P
      convexVertex_spec := by
        rcases lt_or_ge m 4 with hlt | hge
        · have hm3 : m = 3 := le_antisymm (by omega) P.hthree
          exact isConvexVertex'_base_of_eq_three P ρ (ear P) hm3
        · exact isConvexVertex'_of_earCutData hge P ρ (ear P)
            (fun σ => Esup P σ hge)
      transversality := (rest P ρ).transversality
      leftAxioms := (rest P ρ).leftAxioms
      rightAxioms := (rest P ρ).rightAxioms
      leftRay := (rest P ρ).leftRay
      rightRay := (rest P ρ).rightRay
      commonRay := (rest P ρ).commonRay
      disjoint := (rest P ρ).disjoint
      boundary := (rest P ρ).boundary
      intersection := (rest P ρ).intersection }

/-- **The discharged residue genuinely carries the chosen ear vertex** (anti-vacuity check):
the residue's per-cut `convexVertex` is `ear P`, not a placeholder. -/
theorem isConvexVertex'_holds_convexVertex
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esup : ∀ {m : ℕ} (P : StrictSimplePolygon m) (σ : RayDirection P),
      4 ≤ m → EarCutData P σ (ear P))
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RemainingResidualData P ρ (ear P))
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) :
    ((isConvexVertex'_holds ear Esup rest).data P ρ).convexVertex = ear P := rfl

/-! ## Part 4: the Chapter-36 `⌊n/3⌋` headline over the base-free residue + `M`

Composing `isConvexVertex'_holds` with the proved
`PolygonGeomInput.artGallery_strict_of_residue` gives the art-gallery `⌊n/3⌋` bound
conditional on exactly the ear-cut data + remaining cut data + the peel oracle `M`, with the
convex-vertex containment fully discharged (ear induction above `n = 3`, the proved triangle
leaf at `n = 3`). -/

/-- **Chapter-36 art-gallery `⌊n/3⌋` headline over the base-free residue + `M`.**  Every
strict simple polygon with a ray admits `≤ ⌊n/3⌋` vertex guards seeing its whole closed
region, with `IsConvexVertex'` (the development's single irreducible region-level
convex-vertex primitive) now PROVED from the ear-deletion induction down to the *internal*
`n = 3` base.  The remaining inputs are the single Jordan kernel `EarCutData.earDeletedExterior`
(carried in `Esup`), the standard combinatorial cut data (`rest`), and the peel oracle `M` —
the `base` parameter of the upstream assembly is eliminated. -/
theorem artGallery_strict {n : ℕ}
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esup : ∀ {m : ℕ} (P : StrictSimplePolygon m) (σ : RayDirection P),
      4 ≤ m → EarCutData P σ (ear P))
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RemainingResidualData P ρ (ear P))
    (M : ProofsInTheBook.PolygonLast.DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms
          ProofsInTheBook.PolygonTriangleConvex.triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, ProofsInTheBook.PolygonRayIndep.Sees P ρ (P.q v) x :=
  artGallery_strict_of_residue (isConvexVertex'_holds ear Esup rest) M P ρ

end

end ProofsInTheBook.PolygonEarExistence

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.PolygonEarExistence.closedTri_swap₀₁
#print axioms ProofsInTheBook.PolygonEarExistence.closedTri_rotate
#print axioms ProofsInTheBook.PolygonEarExistence.triangle_adjTri_eq_hull
#print axioms ProofsInTheBook.PolygonEarExistence.triangle_isConvexVertex'
#print axioms ProofsInTheBook.PolygonEarExistence.isConvexVertex'_base_of_eq_three
#print axioms ProofsInTheBook.PolygonEarExistence.isConvexVertex'_holds
#print axioms ProofsInTheBook.PolygonEarExistence.isConvexVertex'_holds_convexVertex
#print axioms ProofsInTheBook.PolygonEarExistence.artGallery_strict
