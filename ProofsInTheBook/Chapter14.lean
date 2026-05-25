import Mathlib

/-!
# Chapter 14: Touching simplices

From *Proofs from THE BOOK*, Chapter 14:

* Bagemihl's conjecture predicts `f(d) = 2^d`.
* Perles's theorem, which is the upper-bound theorem actually proved in the
  chapter, states `f(d) < 2^(d+1)` for pairwise touching `d`-simplices.
  This is the statement printed as Theorem 2 in the local Springer PDF; the
  sharper `≤ 2^d` is the conjectural sharp value discussed just before the
  lower-bound construction, not the Perles bound proved by the book.

The old formalization only proved a pigeonhole statement from an already
injective map into `Fin d → Bool`.  That is not the Chapter 14 argument.  This
file now records the geometric objects and proves the Perles B/C-matrix
counting step.  It also proves the local simplex-side geometry available in
Mathlib: a simplex's closed body is weakly on the same side of each facet as
the opposite vertex, and its relative interior is strictly on that side.
The remaining unformalized frontier is the extraction of the certified Perles
matrix from a raw family of touching simplices; see
`PerlesFacetSeparationData` below for the exact missing fields:

* enumerate the distinct oriented facet hyperplanes of the configuration;
  this file now constructs the finite type of distinct unoriented affine facet
  hyperplanes, proves the no-accidental-containment/dimension lemma, and proves
  the exact `d+1` row-incidence count for `HasFacetIn`;
* prove the exact row-incidence count for the chosen global oriented
  hyperplanes: this is now `FacetHyperplanes.card_oriented_hasFacetIn`.  Under
  the precise side-completeness condition that every incident simplex lies in
  one of the two chosen sides, `FacetHyperplanes.rowZeroCard_of_side_complete`
  proves the B-row zero count;
* package affine facet hyperplanes as oriented halfspaces compatible with the
  Mathlib `WSameSide`/`SSameSide` facts proved below; this file now orients
  each concrete simplex facet by signed distance and proves the owning simplex
  is on its positive side.  For each distinct hyperplane,
  `FacetHyperplanes.oriented` chooses one incident facet and orients by that
  facet; the remaining frontier is classifying all other incident simplices as
  positive or negative for that chosen orientation;
* prove a touching pair has opposite signs in some shared facet hyperplane from
  the raw touching relation; `TouchesAcrossFacets` isolates the exact
  opposite-vertex `SOppSide` condition and proves it implies
  `TouchesAlongFacets`, and
  `exists_orientedHyperplane_opposite_entries_of_touchesAcrossFacets` proves
  the local opposite B-entries under that condition, but the
  converse/extraction from raw touching remains unproved;
* construct a point outside all simplices and facet hyperplanes to obtain the
  missing completed sign vector.

Why this file does not claim `Fintype.card ι ≤ 2^d`: the current B/C-matrix
data only proves that the completed rows form a proper subset of the `2^s` sign
vectors.  That gives
`2^(s-d-1) * r < 2^s`, hence `r < 2^(d+1)`.  Removing the remaining factor of
two would require an additional half-cube invariant, for example that completed
rows contain at most one vector from each antipodal pair, or equivalently that
one sign coordinate/parity is determined by the rest.  Such an invariant is not
part of `PerlesFacetSeparationData` and is not proved from the current abstract
matrix fields.  The gap to `≤ 2^d`, if one wants to pursue the conjectural
sharp bound rather than the book's Perles theorem, is exactly this extra
geometric half-cube argument.

This file does formalize the sharpened combinatorial endpoint under one such
extra half-cube invariant: if all completed sign vectors have a fixed value in
one coordinate, then the completed rows inject into a half-cube and
`Fintype.card ι ≤ 2^d`; see `PerlesMatrix.card_le_two_pow_of_fixedCoordinate`
and `chapter14_sharp_of_fixedCoordinate`.  It also proves the more natural
antipodal-free half-cube endpoint; see
`PerlesMatrix.card_le_two_pow_of_antipodalFree` and
`chapter14_sharp_of_antipodalFree`.  The remaining gap is geometric: derive
that fixed-coordinate/parity/antipodal-free invariant, or an equivalent
half-cube bound, from raw touching simplices.
-/

noncomputable section

namespace ProofsInTheBook.Chapter14

open scoped Classical

/-! ## Geometric setup -/

/-- The ambient Euclidean space for Chapter 14. -/
abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A `d`-simplex in `ℝ^d`, using Mathlib's bundled affine simplex. -/
abbrev DSimplex (d : ℕ) := Affine.Simplex ℝ (Ambient d) d

/-- The closed simplex, i.e. the convex hull of its vertices. -/
def DSimplex.body {d : ℕ} (S : DSimplex d) : Set (Ambient d) :=
  S.closedInterior

/-- The relative interior of a simplex in its affine span. -/
def DSimplex.relInterior {d : ℕ} (S : DSimplex d) : Set (Ambient d) :=
  S.interior

/-- The affine hyperplane spanned by the facet opposite a vertex. -/
def DSimplex.facetHyperplane {d : ℕ} [NeZero d] (S : DSimplex d)
    (i : Fin (d + 1)) : AffineSubspace ℝ (Ambient d) :=
  affineSpan ℝ (Set.range (S.faceOpposite i).points)

/-- The vertices of the facet opposite `i` lie in its facet hyperplane. -/
lemma DSimplex.face_points_subset_facetHyperplane {d : ℕ} [NeZero d] (S : DSimplex d)
    (i : Fin (d + 1)) :
    Set.range (S.faceOpposite i).points ⊆ S.facetHyperplane i := by
  intro p hp
  exact mem_affineSpan ℝ hp

/-- The vertex opposite a facet is not contained in the facet hyperplane. -/
lemma DSimplex.opposite_vertex_notMem_facetHyperplane {d : ℕ} [NeZero d]
    (S : DSimplex d) (i : Fin (d + 1)) :
    S.points i ∉ S.facetHyperplane i := by
  simp [DSimplex.facetHyperplane]

/-- Distinct vertices determine distinct opposite facet hyperplanes. -/
lemma DSimplex.facetHyperplane_injective {d : ℕ} [NeZero d] (S : DSimplex d) :
    Function.Injective S.facetHyperplane := by
  intro i j hij
  by_contra hne
  have hi_mem_j : S.points i ∈ S.facetHyperplane j := by
    rw [DSimplex.facetHyperplane]
    exact (S.points_mem_affineSpan_faceOpposite (i := j) (j := i)).2 hne
  rw [← hij] at hi_mem_j
  exact S.opposite_vertex_notMem_facetHyperplane i hi_mem_j

/-- A simplex has exactly `d+1` distinct facet hyperplanes. -/
lemma DSimplex.card_facetHyperplane_image {d : ℕ} [NeZero d] (S : DSimplex d) :
    (Finset.univ.image S.facetHyperplane).card = d + 1 := by
  classical
  rw [Finset.card_image_of_injective _ S.facetHyperplane_injective]
  simp

/-- The direction of a simplex facet hyperplane has dimension `d - 1`. -/
lemma DSimplex.finrank_direction_facetHyperplane {d : ℕ} [NeZero d] (S : DSimplex d)
    (i : Fin (d + 1)) :
    Module.finrank ℝ (S.facetHyperplane i).direction = d - 1 := by
  rw [DSimplex.facetHyperplane, direction_affineSpan]
  exact (S.faceOpposite i).independent.finrank_vectorSpan (Fintype.card_fin _)

/--
No accidental containment: if all vertices of one facet of `S` lie in a facet
hyperplane of `T`, then the two facet hyperplanes are equal.
-/
lemma DSimplex.facetHyperplane_eq_of_face_points_subset {d : ℕ} [NeZero d]
    (S T : DSimplex d) (i j : Fin (d + 1))
    (hsubset : Set.range (S.faceOpposite i).points ⊆ T.facetHyperplane j) :
    S.facetHyperplane i = T.facetHyperplane j := by
  have hle : S.facetHyperplane i ≤ T.facetHyperplane j :=
    affineSpan_le_of_subset_coe hsubset
  have hdir : (S.facetHyperplane i).direction = (T.facetHyperplane j).direction := by
    refine Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) ?_
    rw [S.finrank_direction_facetHyperplane i, T.finrank_direction_facetHyperplane j]
  have hnonempty : (S.facetHyperplane i : Set (Ambient d)).Nonempty := by
    exact ⟨(S.faceOpposite i).points 0,
      S.face_points_subset_facetHyperplane i (Set.mem_range_self 0)⟩
  exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir hnonempty hle

/-- The set of distinct affine facet hyperplanes appearing in a finite family. -/
def FacetHyperplaneSet {ι : Type*} {d : ℕ} [NeZero d]
    (simplices : ι → DSimplex d) : Set (AffineSubspace ℝ (Ambient d)) :=
  Set.range fun x : ι × Fin (d + 1) => (simplices x.1).facetHyperplane x.2

/-- A bundled finite type of distinct affine facet hyperplanes of a family. -/
abbrev FacetHyperplanes {ι : Type*} {d : ℕ} [NeZero d]
    (simplices : ι → DSimplex d) : Type _ :=
  {H : AffineSubspace ℝ (Ambient d) // H ∈ FacetHyperplaneSet simplices}

lemma facetHyperplane_mem_facetHyperplaneSet {ι : Type*} {d : ℕ} [NeZero d]
    (simplices : ι → DSimplex d) (a : ι) (i : Fin (d + 1)) :
    (simplices a).facetHyperplane i ∈ FacetHyperplaneSet simplices := by
  exact ⟨(a, i), rfl⟩

lemma finite_facetHyperplaneSet {ι : Type*} [Fintype ι] {d : ℕ} [NeZero d]
    (simplices : ι → DSimplex d) :
    (FacetHyperplaneSet simplices).Finite := by
  simpa [FacetHyperplaneSet] using
    (Set.finite_range fun x : ι × Fin (d + 1) => (simplices x.1).facetHyperplane x.2)

noncomputable instance facetHyperplanesFintype {ι : Type*} [Fintype ι] {d : ℕ}
    [NeZero d] (simplices : ι → DSimplex d) : Fintype (FacetHyperplanes simplices) :=
  (finite_facetHyperplaneSet simplices).fintype

/-- The facet-hyperplane subtype element corresponding to one concrete facet. -/
def facetHyperplaneIndexOf {ι : Type*} {d : ℕ} [NeZero d]
    (simplices : ι → DSimplex d) (a : ι) (i : Fin (d + 1)) :
    FacetHyperplanes simplices :=
  ⟨(simplices a).facetHyperplane i, facetHyperplane_mem_facetHyperplaneSet simplices a i⟩

lemma facetHyperplaneIndexOf_injective {ι : Type*} {d : ℕ} [NeZero d]
    (simplices : ι → DSimplex d) (a : ι) :
    Function.Injective (facetHyperplaneIndexOf simplices a) := by
  intro i j hij
  exact (simplices a).facetHyperplane_injective (Subtype.ext_iff.mp hij)

/--
For a nonempty finite family, the distinct affine facet hyperplanes have
cardinality at least `d+1`, because the facets of any one simplex are distinct.
-/
lemma card_facetHyperplanes_ge {ι : Type*} [Fintype ι] [Nonempty ι] {d : ℕ}
    [NeZero d] (simplices : ι → DSimplex d) :
    d + 1 ≤ Fintype.card (FacetHyperplanes simplices) := by
  classical
  let a : ι := Classical.choice (inferInstance : Nonempty ι)
  calc
    d + 1 = Fintype.card (Fin (d + 1)) := by simp
    _ ≤ Fintype.card (FacetHyperplanes simplices) :=
      Fintype.card_le_of_injective (facetHyperplaneIndexOf simplices a)
        (facetHyperplaneIndexOf_injective simplices a)

/--
Every point of a simplex's closed body is weakly on the same side of a facet
hyperplane as the opposite vertex.
-/
lemma DSimplex.body_wSameSide_opposite_vertex {d : ℕ} [NeZero d] (S : DSimplex d)
    (i : Fin (d + 1)) {p : Ambient d} (hp : p ∈ S.body) :
    (S.facetHyperplane i).WSameSide p (S.points i) := by
  rw [DSimplex.body] at hp
  rcases hp with ⟨w, hw, hw01, rfl⟩
  rw [DSimplex.facetHyperplane]
  exact (S.wSameSide_affineSpan_faceOpposite_point_right_iff hw).2 (hw01 i).1

/--
Signed-distance form of the previous weak-side fact: if a facet is oriented
toward its opposite vertex by `Affine.Simplex.signedInfDist`, then the whole
closed simplex has nonnegative signed distance from that facet.
-/
lemma DSimplex.signedInfDist_nonneg_of_mem_body {d : ℕ} [NeZero d] (S : DSimplex d)
    (i : Fin (d + 1)) {p : Ambient d} (hp : p ∈ S.body) :
    0 ≤ S.signedInfDist i p := by
  rw [DSimplex.body] at hp
  rcases hp with ⟨w, hw, hw01, rfl⟩
  rw [S.signedInfDist_affineCombination i hw]
  exact mul_nonneg (hw01 i).1 (norm_nonneg _)

/-- The opposite vertex has nonzero perpendicular displacement from its facet span. -/
lemma DSimplex.opposite_vertex_vsub_orthogonalProjectionSpan_ne_zero {d : ℕ}
    [NeZero d] (S : DSimplex d) (i : Fin (d + 1)) :
    S.points i -ᵥ (S.faceOpposite i).orthogonalProjectionSpan (S.points i) ≠ 0 := by
  intro hzero
  have hEq :
      S.points i = ((S.faceOpposite i).orthogonalProjectionSpan (S.points i) : Ambient d) :=
    vsub_eq_zero_iff_eq.mp hzero
  have hmem : S.points i ∈ S.facetHyperplane i := by
    rw [hEq, DSimplex.facetHyperplane]
    exact ((S.faceOpposite i).orthogonalProjectionSpan (S.points i)).2
  exact S.opposite_vertex_notMem_facetHyperplane i hmem

/--
The signed-distance orientation is strictly positive on the simplex relative
interior.
-/
lemma DSimplex.signedInfDist_pos_of_mem_relInterior {d : ℕ} [NeZero d]
    (S : DSimplex d) (i : Fin (d + 1)) {p : Ambient d} (hp : p ∈ S.relInterior) :
    0 < S.signedInfDist i p := by
  rw [DSimplex.relInterior] at hp
  rcases hp with ⟨w, hw, hw01, rfl⟩
  rw [S.signedInfDist_affineCombination i hw]
  exact mul_pos (hw01 i).1
    (norm_pos_iff.mpr (S.opposite_vertex_vsub_orthogonalProjectionSpan_ne_zero i))

/--
Every point of a simplex's relative interior is strictly on the same side of a
facet hyperplane as the opposite vertex.
-/
lemma DSimplex.relInterior_sSameSide_opposite_vertex {d : ℕ} [NeZero d]
    (S : DSimplex d) (i : Fin (d + 1)) {p : Ambient d} (hp : p ∈ S.relInterior) :
    (S.facetHyperplane i).SSameSide p (S.points i) := by
  rw [DSimplex.relInterior] at hp
  rcases hp with ⟨w, hw, hw01, rfl⟩
  rw [DSimplex.facetHyperplane]
  exact (S.sSameSide_affineSpan_faceOpposite_point_right_iff hw).2 (hw01 i).1

/--
If two simplices have a common facet hyperplane and the two opposite vertices
are strictly on opposite sides of it, then all relative-interior points are
strictly on opposite sides.  This is the formal local side-composition lemma
needed for the geometric `pairwiseOpposite` field.
-/
lemma DSimplex.relInterior_sOppSide_of_commonFacet_of_vertices_sOppSide {d : ℕ}
    [NeZero d] (S T : DSimplex d) (i j : Fin (d + 1))
    {p q : Ambient d} (hp : p ∈ S.relInterior) (hq : q ∈ T.relInterior)
    (hfacet : S.facetHyperplane i = T.facetHyperplane j)
    (hopposite : (S.facetHyperplane i).SOppSide (S.points i) (T.points j)) :
    (S.facetHyperplane i).SOppSide p q := by
  have hp_side := S.relInterior_sSameSide_opposite_vertex i hp
  have hq_side : (S.facetHyperplane i).SSameSide (T.points j) q := by
    simpa [hfacet] using (T.relInterior_sSameSide_opposite_vertex j hq).symm
  exact (hp_side.trans_sOppSide hopposite).trans_sSameSide hq_side

/--
Closed-body version of the same side-composition fact: under the same common
facet/opposite-vertex hypothesis, any two body points are weakly on opposite
sides of the common facet hyperplane.
-/
lemma DSimplex.body_wOppSide_of_commonFacet_of_vertices_sOppSide {d : ℕ}
    [NeZero d] (S T : DSimplex d) (i j : Fin (d + 1))
    {p q : Ambient d} (hp : p ∈ S.body) (hq : q ∈ T.body)
    (hfacet : S.facetHyperplane i = T.facetHyperplane j)
    (hopposite : (S.facetHyperplane i).SOppSide (S.points i) (T.points j)) :
    (S.facetHyperplane i).WOppSide p q := by
  have hp_side := S.body_wSameSide_opposite_vertex i hp
  have hq_side : (S.facetHyperplane i).WSameSide (T.points j) q := by
    simpa [hfacet] using (T.body_wSameSide_opposite_vertex j hq).symm
  exact (hp_side.trans_sOppSide hopposite).trans_wSameSide hq_side hopposite.2.2

/--
Structured touching data across a specified common facet hyperplane: the closed
bodies meet, and the two opposite vertices are strictly on opposite sides of
that common facet hyperplane.
-/
def TouchesAcrossFacets {d : ℕ} [NeZero d] (S T : DSimplex d) : Prop :=
  (S.body ∩ T.body).Nonempty ∧
    ∃ i j, S.facetHyperplane i = T.facetHyperplane j ∧
      (S.facetHyperplane i).SOppSide (S.points i) (T.points j)

/--
Two `d`-simplices touch along facets if their relative interiors are disjoint,
their closed bodies meet, and some facet hyperplane of one agrees with a facet
hyperplane of the other.

This is the concrete geometric relation used by the Perles matrix construction.
It is intentionally stronger/more structured than a bare nonempty boundary
intersection, because the B-matrix proof uses the common supporting facet
hyperplane.
-/
def TouchesAlongFacets {d : ℕ} [NeZero d] (S T : DSimplex d) : Prop :=
  Disjoint S.relInterior T.relInterior ∧
    (S.body ∩ T.body).Nonempty ∧
      ∃ i j, S.facetHyperplane i = T.facetHyperplane j

/--
The opposite-vertex side condition is strong enough to imply disjoint relative
interiors, hence the weaker `TouchesAlongFacets` relation.
-/
lemma touchesAlongFacets_of_touchesAcrossFacets {d : ℕ} [NeZero d]
    {S T : DSimplex d} (h : TouchesAcrossFacets S T) :
    TouchesAlongFacets S T := by
  rcases h with ⟨hmeet, i, j, hfacet, hopposite⟩
  refine ⟨?_, hmeet, ⟨i, j, hfacet⟩⟩
  rw [Set.disjoint_left]
  intro p hpS hpT
  exact AffineSubspace.not_sOppSide_self (S.facetHyperplane i) p
    (S.relInterior_sOppSide_of_commonFacet_of_vertices_sOppSide T i j hpS hpT hfacet hopposite)

/-- A finite family of pairwise touching `d`-simplices. -/
def PairwiseTouching {ι : Type*} {d : ℕ} [NeZero d]
    (simplices : ι → DSimplex d) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → TouchesAlongFacets (simplices i) (simplices j)

/-- Pairwise touching with the stronger explicit opposite-side facet data. -/
def PairwiseTouchingAcrossFacets {ι : Type*} {d : ℕ} [NeZero d]
    (simplices : ι → DSimplex d) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → TouchesAcrossFacets (simplices i) (simplices j)

lemma pairwiseTouching_of_pairwiseTouchingAcrossFacets {ι : Type*} {d : ℕ}
    [NeZero d] {simplices : ι → DSimplex d}
    (h : PairwiseTouchingAcrossFacets simplices) :
    PairwiseTouching simplices := by
  intro i j hij
  exact touchesAlongFacets_of_touchesAcrossFacets (h hij)

/--
An oriented affine hyperplane, represented by its carrier and the two closed
sides chosen for Perles's sign convention.

The fields are deliberately set-theoretic: Mathlib has affine subspaces and
simplex interiors, but it does not package "oriented facet hyperplane with the
two closed halfspaces and all containment facts" in the form needed here.
-/
structure OrientedHyperplane (d : ℕ) where
  carrier : Set (Ambient d)
  positiveSide : Set (Ambient d)
  negativeSide : Set (Ambient d)

namespace OrientedHyperplane

/--
Orient one concrete simplex facet by signed distance, with the positive side
chosen toward the facet's opposite vertex.
-/
def ofSimplexFacet {d : ℕ} [NeZero d] (S : DSimplex d) (i : Fin (d + 1)) :
    OrientedHyperplane d where
  carrier := S.facetHyperplane i
  positiveSide := {p | 0 ≤ S.signedInfDist i p}
  negativeSide := {p | S.signedInfDist i p ≤ 0}

/--
Orient one concrete simplex facet using Mathlib's weak side predicates.  This
orientation is useful for the Perles B-entry proof because opposite vertices on
opposite strict sides immediately force opposite weak-side containment.
-/
def ofSimplexFacetSide {d : ℕ} [NeZero d] (S : DSimplex d) (i : Fin (d + 1)) :
    OrientedHyperplane d where
  carrier := S.facetHyperplane i
  positiveSide := {p | (S.facetHyperplane i).WSameSide p (S.points i)}
  negativeSide := {p | (S.facetHyperplane i).WOppSide p (S.points i)}

/-- A simplex has a facet in the carrier of an oriented hyperplane. -/
def HasFacetIn {d : ℕ} [NeZero d] (H : OrientedHyperplane d) (S : DSimplex d) : Prop :=
  ∃ i : Fin (d + 1), Set.range (S.faceOpposite i).points ⊆ H.carrier

lemma ofSimplexFacet_hasFacetIn_self {d : ℕ} [NeZero d] (S : DSimplex d)
    (i : Fin (d + 1)) :
    (ofSimplexFacet S i).HasFacetIn S := by
  exact ⟨i, by simpa [ofSimplexFacet] using S.face_points_subset_facetHyperplane i⟩

lemma ofSimplexFacetSide_hasFacetIn_self {d : ℕ} [NeZero d] (S : DSimplex d)
    (i : Fin (d + 1)) :
    (ofSimplexFacetSide S i).HasFacetIn S := by
  exact ⟨i, by simpa [ofSimplexFacetSide] using S.face_points_subset_facetHyperplane i⟩

lemma ofSimplexFacetSide_hasFacetIn_of_commonFacet {d : ℕ} [NeZero d]
    (S T : DSimplex d) (i j : Fin (d + 1))
    (hfacet : S.facetHyperplane i = T.facetHyperplane j) :
    (ofSimplexFacetSide S i).HasFacetIn T := by
  refine ⟨j, ?_⟩
  intro p hp
  have hp' : p ∈ T.facetHyperplane j := T.face_points_subset_facetHyperplane j hp
  simpa [ofSimplexFacetSide, ← hfacet] using hp'

lemma ofSimplexFacet_hasFacetIn_iff {d : ℕ} [NeZero d]
    (S T : DSimplex d) (i : Fin (d + 1)) :
    (ofSimplexFacet S i).HasFacetIn T ↔
      ∃ j : Fin (d + 1), T.facetHyperplane j = S.facetHyperplane i := by
  constructor
  · rintro ⟨j, hsub⟩
    have hsub' : Set.range (T.faceOpposite j).points ⊆ S.facetHyperplane i := by
      simpa [ofSimplexFacet] using hsub
    exact ⟨j, T.facetHyperplane_eq_of_face_points_subset S j i hsub'⟩
  · rintro ⟨j, hfacet⟩
    refine ⟨j, ?_⟩
    intro p hp
    have hp' : p ∈ T.facetHyperplane j := T.face_points_subset_facetHyperplane j hp
    simpa [ofSimplexFacet, ← hfacet] using hp'

lemma ofSimplexFacetSide_hasFacetIn_iff {d : ℕ} [NeZero d]
    (S T : DSimplex d) (i : Fin (d + 1)) :
    (ofSimplexFacetSide S i).HasFacetIn T ↔
      ∃ j : Fin (d + 1), T.facetHyperplane j = S.facetHyperplane i := by
  constructor
  · rintro ⟨j, hsub⟩
    have hsub' : Set.range (T.faceOpposite j).points ⊆ S.facetHyperplane i := by
      simpa [ofSimplexFacetSide] using hsub
    exact ⟨j, T.facetHyperplane_eq_of_face_points_subset S j i hsub'⟩
  · rintro ⟨j, hfacet⟩
    exact ofSimplexFacetSide_hasFacetIn_of_commonFacet S T i j hfacet.symm

lemma body_subset_positiveSide_ofSimplexFacet {d : ℕ} [NeZero d] (S : DSimplex d)
    (i : Fin (d + 1)) :
    S.body ⊆ (ofSimplexFacet S i).positiveSide := by
  intro p hp
  simpa [ofSimplexFacet] using S.signedInfDist_nonneg_of_mem_body i hp

lemma body_subset_positiveSide_ofSimplexFacetSide {d : ℕ} [NeZero d] (S : DSimplex d)
    (i : Fin (d + 1)) :
    S.body ⊆ (ofSimplexFacetSide S i).positiveSide := by
  intro p hp
  simpa [ofSimplexFacetSide] using S.body_wSameSide_opposite_vertex i hp

lemma relInterior_subset_positiveSide_ofSimplexFacet {d : ℕ} [NeZero d]
    (S : DSimplex d) (i : Fin (d + 1)) :
    S.relInterior ⊆ (ofSimplexFacet S i).positiveSide := by
  intro p hp
  simpa [ofSimplexFacet] using (S.signedInfDist_pos_of_mem_relInterior i hp).le

lemma body_subset_negativeSide_ofSimplexFacetSide_of_vertices_sOppSide {d : ℕ}
    [NeZero d] (S T : DSimplex d) (i j : Fin (d + 1))
    (hfacet : S.facetHyperplane i = T.facetHyperplane j)
    (hopposite : (S.facetHyperplane i).SOppSide (S.points i) (T.points j)) :
    T.body ⊆ (ofSimplexFacetSide S i).negativeSide := by
  intro q hq
  have hpS : S.points i ∈ S.body := by
    simpa [DSimplex.body] using S.point_mem_closedInterior i
  have hOpp :=
    S.body_wOppSide_of_commonFacet_of_vertices_sOppSide T i j hpS hq hfacet hopposite
  simpa [ofSimplexFacetSide] using hOpp.symm

lemma not_body_subset_positiveSide_ofSimplexFacetSide_of_vertices_sOppSide {d : ℕ}
    [NeZero d] (S T : DSimplex d) (i j : Fin (d + 1))
    (hopposite : (S.facetHyperplane i).SOppSide (S.points i) (T.points j)) :
    ¬ T.body ⊆ (ofSimplexFacetSide S i).positiveSide := by
  intro hsub
  have hT : T.points j ∈ T.body := by
    simpa [DSimplex.body] using T.point_mem_closedInterior j
  have hsame : (S.facetHyperplane i).WSameSide (T.points j) (S.points i) := by
    simpa [ofSimplexFacetSide] using hsub hT
  exact hopposite.not_wSameSide hsame.symm

/--
The `B`-matrix entry attached to a simplex and an oriented facet hyperplane.
It is `some true` on the chosen positive side, `some false` on the chosen
negative side, and `none` when the simplex has no facet in this hyperplane or
the supplied halfspace data do not certify a side.
-/
def simplexFacetSide {d : ℕ} [NeZero d] (H : OrientedHyperplane d)
    (S : DSimplex d) : Option Bool := by
  classical
  exact
    if H.HasFacetIn S then
      if S.body ⊆ H.positiveSide then
        some true
      else if S.body ⊆ H.negativeSide then
        some false
      else
        none
    else
      none

lemma simplexFacetSide_eq_none_iff_not_hasFacetIn_of_side_complete {d : ℕ} [NeZero d]
    (H : OrientedHyperplane d) (S : DSimplex d)
    (hside : H.HasFacetIn S → S.body ⊆ H.positiveSide ∨ S.body ⊆ H.negativeSide) :
    H.simplexFacetSide S = none ↔ ¬ H.HasFacetIn S := by
  constructor
  · intro hnone hfacet
    unfold simplexFacetSide at hnone
    rw [if_pos hfacet] at hnone
    rcases hside hfacet with hpos | hneg
    · rw [if_pos hpos] at hnone
      simp at hnone
    · by_cases hpos : S.body ⊆ H.positiveSide
      · rw [if_pos hpos] at hnone
        simp at hnone
      · rw [if_neg hpos, if_pos hneg] at hnone
        simp at hnone
  · intro hnot
    unfold simplexFacetSide
    rw [if_neg hnot]

/-- The signed-distance orientation of a simplex's own facet gives a positive B-entry. -/
lemma simplexFacetSide_ofSimplexFacet_self {d : ℕ} [NeZero d] (S : DSimplex d)
    (i : Fin (d + 1)) :
    (ofSimplexFacet S i).simplexFacetSide S = some true := by
  classical
  unfold simplexFacetSide
  rw [if_pos (ofSimplexFacet_hasFacetIn_self S i)]
  rw [if_pos (body_subset_positiveSide_ofSimplexFacet S i)]

/-- The side-predicate orientation of a simplex's own facet gives a positive B-entry. -/
lemma simplexFacetSide_ofSimplexFacetSide_self {d : ℕ} [NeZero d] (S : DSimplex d)
    (i : Fin (d + 1)) :
    (ofSimplexFacetSide S i).simplexFacetSide S = some true := by
  classical
  unfold simplexFacetSide
  rw [if_pos (ofSimplexFacetSide_hasFacetIn_self S i)]
  rw [if_pos (body_subset_positiveSide_ofSimplexFacetSide S i)]

/--
If another simplex has the same facet hyperplane and its opposite vertex is
strictly on the opposite side, the side-predicate orientation gives that
simplex a negative B-entry.
-/
lemma simplexFacetSide_ofSimplexFacetSide_of_vertices_sOppSide {d : ℕ} [NeZero d]
    (S T : DSimplex d) (i j : Fin (d + 1))
    (hfacet : S.facetHyperplane i = T.facetHyperplane j)
    (hopposite : (S.facetHyperplane i).SOppSide (S.points i) (T.points j)) :
    (ofSimplexFacetSide S i).simplexFacetSide T = some false := by
  classical
  unfold simplexFacetSide
  rw [if_pos (ofSimplexFacetSide_hasFacetIn_of_commonFacet S T i j hfacet)]
  rw [if_neg (not_body_subset_positiveSide_ofSimplexFacetSide_of_vertices_sOppSide
    S T i j hopposite)]
  rw [if_pos (body_subset_negativeSide_ofSimplexFacetSide_of_vertices_sOppSide
    S T i j hfacet hopposite)]

end OrientedHyperplane

/--
For one across-facet touching pair, the side-predicate orientation of the first
simplex's common facet gives opposite B-entries.  This is the local geometric
content of the `pairwiseOpposite` matrix field, before choosing a single global
finite hyperplane index type for the whole configuration.
-/
lemma exists_orientedHyperplane_opposite_entries_of_touchesAcrossFacets {d : ℕ}
    [NeZero d] {S T : DSimplex d} (h : TouchesAcrossFacets S T) :
    ∃ H : OrientedHyperplane d, ∃ b : Bool,
      H.simplexFacetSide S = some b ∧ H.simplexFacetSide T = some (!b) := by
  rcases h with ⟨_, i, j, hfacet, hopposite⟩
  refine ⟨OrientedHyperplane.ofSimplexFacetSide S i, true, ?_, ?_⟩
  · exact OrientedHyperplane.simplexFacetSide_ofSimplexFacetSide_self S i
  · simpa using
      OrientedHyperplane.simplexFacetSide_ofSimplexFacetSide_of_vertices_sOppSide
        S T i j hfacet hopposite

namespace FacetHyperplanes

variable {ι : Type*} {d : ℕ} [NeZero d] (simplices : ι → DSimplex d)

/-- A chosen concrete facet witnessing a bundled distinct facet hyperplane. -/
noncomputable def witness (H : FacetHyperplanes simplices) : ι × Fin (d + 1) :=
  Classical.choose H.2

lemma witness_spec (H : FacetHyperplanes simplices) :
    (simplices (witness simplices H).1).facetHyperplane (witness simplices H).2 = H.1 :=
  Classical.choose_spec H.2

/--
Orient a distinct facet hyperplane by the signed-distance orientation of one
chosen incident facet.
-/
noncomputable def oriented (H : FacetHyperplanes simplices) : OrientedHyperplane d where
  carrier := H.1
  positiveSide :=
    (OrientedHyperplane.ofSimplexFacet (simplices (witness simplices H).1)
      (witness simplices H).2).positiveSide
  negativeSide :=
    (OrientedHyperplane.ofSimplexFacet (simplices (witness simplices H).1)
      (witness simplices H).2).negativeSide

lemma oriented_hasFacetIn_witness (H : FacetHyperplanes simplices) :
    (oriented simplices H).HasFacetIn (simplices (witness simplices H).1) := by
  refine ⟨(witness simplices H).2, ?_⟩
  intro p hp
  have hp' :
      p ∈ (simplices (witness simplices H).1).facetHyperplane (witness simplices H).2 :=
    (simplices (witness simplices H).1).face_points_subset_facetHyperplane
      (witness simplices H).2 hp
  simpa [oriented, witness_spec simplices H] using hp'

lemma oriented_hasFacetIn_iff (H : FacetHyperplanes simplices) (T : DSimplex d) :
    (oriented simplices H).HasFacetIn T ↔
      ∃ j : Fin (d + 1), T.facetHyperplane j = H.1 := by
  constructor
  · rintro ⟨j, hsub⟩
    have hsub_carrier : Set.range (T.faceOpposite j).points ⊆ H.1 := by
      simpa [oriented] using hsub
    have hsub_witness : Set.range (T.faceOpposite j).points ⊆
        (simplices (witness simplices H).1).facetHyperplane (witness simplices H).2 := by
      simpa [witness_spec simplices H] using hsub_carrier
    have hEq := T.facetHyperplane_eq_of_face_points_subset
      (simplices (witness simplices H).1) j (witness simplices H).2 hsub_witness
    exact ⟨j, by simpa [witness_spec simplices H] using hEq⟩
  · rintro ⟨j, hfacet⟩
    refine ⟨j, ?_⟩
    intro p hp
    have hp' : p ∈ T.facetHyperplane j := T.face_points_subset_facetHyperplane j hp
    simpa [oriented, ← hfacet] using hp'

lemma body_subset_positiveSide_oriented_witness (H : FacetHyperplanes simplices) :
    (simplices (witness simplices H).1).body ⊆ (oriented simplices H).positiveSide := by
  intro p hp
  simpa [oriented] using
    OrientedHyperplane.body_subset_positiveSide_ofSimplexFacet
      (simplices (witness simplices H).1) (witness simplices H).2 hp

/--
For the chosen witness facet of a distinct hyperplane, the induced global
orientation gives a positive B-entry.
-/
lemma simplexFacetSide_oriented_witness_self (H : FacetHyperplanes simplices) :
    (oriented simplices H).simplexFacetSide (simplices (witness simplices H).1) =
      some true := by
  classical
  unfold OrientedHyperplane.simplexFacetSide
  rw [if_pos (oriented_hasFacetIn_witness simplices H)]
  rw [if_pos (body_subset_positiveSide_oriented_witness simplices H)]

lemma oriented_hasFacetIn_iff_exists_facetHyperplaneIndexOf
    (H : FacetHyperplanes simplices) (a : ι) :
    (oriented simplices H).HasFacetIn (simplices a) ↔
      ∃ i : Fin (d + 1), facetHyperplaneIndexOf simplices a i = H := by
  constructor
  · rintro ⟨i, hsubset⟩
    have hsubsetH :
        Set.range ((simplices a).faceOpposite i).points ⊆ (H.1 : Set (Ambient d)) := by
      simpa [oriented] using hsubset
    have hsubsetWitness :
        Set.range ((simplices a).faceOpposite i).points ⊆
          (simplices (witness simplices H).1).facetHyperplane (witness simplices H).2 := by
      intro p hp
      rw [witness_spec simplices H]
      exact hsubsetH hp
    have heq :
        (simplices a).facetHyperplane i =
          (simplices (witness simplices H).1).facetHyperplane (witness simplices H).2 :=
      (simplices a).facetHyperplane_eq_of_face_points_subset
        (simplices (witness simplices H).1) i (witness simplices H).2 hsubsetWitness
    refine ⟨i, Subtype.ext ?_⟩
    exact heq.trans (witness_spec simplices H)
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    intro p hp
    simpa [oriented] using (simplices a).face_points_subset_facetHyperplane i hp

/--
For the global type of distinct facet hyperplanes, a fixed simplex is incident
with exactly its own `d+1` facet hyperplanes.
-/
lemma card_oriented_hasFacetIn [Fintype ι] (a : ι) :
    (Finset.univ.filter fun H : FacetHyperplanes simplices =>
      (oriented simplices H).HasFacetIn (simplices a)).card = d + 1 := by
  classical
  have hfilter :
      (Finset.univ.filter fun H : FacetHyperplanes simplices =>
        (oriented simplices H).HasFacetIn (simplices a)) =
        Finset.univ.image (facetHyperplaneIndexOf simplices a) := by
    ext H
    simp [oriented_hasFacetIn_iff_exists_facetHyperplaneIndexOf]
  rw [hfilter, Finset.card_image_of_injective _ (facetHyperplaneIndexOf_injective simplices a)]
  simp

/--
Once every incident simplex is certified to lie in one of the two oriented
sides, the zero count in the Perles B-row follows from the exact facet
incidence count.
-/
lemma rowZeroCard_of_side_complete [Fintype ι] (a : ι)
    (hside : ∀ H : FacetHyperplanes simplices,
      (oriented simplices H).HasFacetIn (simplices a) →
        (simplices a).body ⊆ (oriented simplices H).positiveSide ∨
          (simplices a).body ⊆ (oriented simplices H).negativeSide) :
    (Finset.univ.filter fun H : FacetHyperplanes simplices =>
      (oriented simplices H).simplexFacetSide (simplices a) = none).card =
        Fintype.card (FacetHyperplanes simplices) - (d + 1) := by
  classical
  have hfilter :
      (Finset.univ.filter fun H : FacetHyperplanes simplices =>
        (oriented simplices H).simplexFacetSide (simplices a) = none) =
        Finset.univ.filter fun H : FacetHyperplanes simplices =>
          ¬ (oriented simplices H).HasFacetIn (simplices a) := by
    apply Finset.filter_congr
    intro H _
    exact OrientedHyperplane.simplexFacetSide_eq_none_iff_not_hasFacetIn_of_side_complete
      (oriented simplices H) (simplices a) (hside H)
  rw [hfilter]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (FacetHyperplanes simplices)))
    (p := fun H : FacetHyperplanes simplices =>
      (oriented simplices H).HasFacetIn (simplices a))
  rw [card_oriented_hasFacetIn simplices a, Finset.card_univ] at hsum
  omega

end FacetHyperplanes

/-! ## Perles B/C-matrix core -/

/-- A full sign vector extends one row of the `B`-matrix when it agrees with
all nonzero entries in that row. -/
def EntryExtends {κ : Type*} (row : κ → Option Bool) (v : κ → Bool) : Prop :=
  ∀ j b, row j = some b → v j = b

/--
The finite B-matrix data used in Perles's proof.

For a real touching-simplex configuration these fields should be derived from
the facet hyperplanes:

* `rowZeroCard`: a `d`-simplex has exactly `d+1` facet hyperplanes, hence
  `s-(d+1)` zeros in a row when there are `s` distinct facet hyperplanes.
* `pairwiseOpposite`: touching simplices share a facet hyperplane and lie on
  opposite sides of it.
* `missingSignVector`: choose a point outside all simplices and all facet
  hyperplanes; its side vector is not represented by any completed row.

Those are precisely the remaining geometric extraction obligations.  They are
not the final cardinality conclusion and they are not an assumed injective sign
map.
-/
structure PerlesMatrix (ι κ : Type*) [Fintype ι] [Fintype κ] (d : ℕ) where
  entry : ι → κ → Option Bool
  dimension_le_columns : d + 1 ≤ Fintype.card κ
  rowZeroCard :
    ∀ i : ι, (Finset.univ.filter fun j : κ => entry i j = none).card =
      Fintype.card κ - (d + 1)
  pairwiseOpposite :
    ∀ ⦃i j : ι⦄, i ≠ j → ∃ h : κ, ∃ b : Bool,
      entry i h = some b ∧ entry j h = some (!b)
  missingSignVector : ∃ v : κ → Bool, ∀ i : ι, ¬ EntryExtends (entry i) v

namespace PerlesMatrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}

/-- Zero positions in one row of the Perles `B`-matrix. -/
abbrev ZeroPos (M : PerlesMatrix ι κ d) (i : ι) : Type _ :=
  {j : κ // M.entry i j = none}

/-- Indices of the rows of the expanded `C`-matrix: choose a row of `B` and
then choose signs for all zero positions in that row. -/
abbrev CompletionIndex (M : PerlesMatrix ι κ d) : Type _ :=
  Σ i : ι, M.ZeroPos i → Bool

/-- The completed `{+,-}` sign vector corresponding to one row of `C`. -/
def completedSign (M : PerlesMatrix ι κ d) (x : M.CompletionIndex) : κ → Bool :=
  fun j =>
    if h : M.entry x.1 j = none then
      x.2 ⟨j, h⟩
    else
      (M.entry x.1 j).getD false

lemma completedSign_of_some (M : PerlesMatrix ι κ d) {i : ι}
    (z : M.ZeroPos i → Bool) {j : κ} {b : Bool} (h : M.entry i j = some b) :
    M.completedSign ⟨i, z⟩ j = b := by
  simp [completedSign, h]

lemma completedSign_of_none (M : PerlesMatrix ι κ d) {i : ι}
    (z : M.ZeroPos i → Bool) {j : κ} (h : M.entry i j = none) :
    M.completedSign ⟨i, z⟩ j = z ⟨j, h⟩ := by
  simp [completedSign, h]

lemma completedSign_extends (M : PerlesMatrix ι κ d) (x : M.CompletionIndex) :
    EntryExtends (M.entry x.1) (M.completedSign x) := by
  intro j b hb
  exact M.completedSign_of_some x.2 hb

lemma completedSign_injective (M : PerlesMatrix ι κ d) :
    Function.Injective M.completedSign := by
  rintro ⟨i, zi⟩ ⟨j, zj⟩ h
  by_cases hij : i = j
  · subst j
    congr
    funext z
    have hz := congrFun h z.1
    rw [M.completedSign_of_none zi z.2, M.completedSign_of_none zj z.2] at hz
    exact hz
  · rcases M.pairwiseOpposite hij with ⟨c, b, hic, hjc⟩
    have hc := congrFun h c
    have hi : M.completedSign ⟨i, zi⟩ c = b := by
      exact M.completedSign_of_some zi hic
    have hj : M.completedSign ⟨j, zj⟩ c = !b := by
      exact M.completedSign_of_some zj hjc
    rw [hi, hj] at hc
    cases b <;> simp at hc

lemma completedSign_not_surjective (M : PerlesMatrix ι κ d) :
    ¬ Function.Surjective M.completedSign := by
  rintro hsurj
  rcases M.missingSignVector with ⟨v, hv⟩
  rcases hsurj v with ⟨x, rfl⟩
  exact hv x.1 (M.completedSign_extends x)

lemma card_zeroPos (M : PerlesMatrix ι κ d) (i : ι) :
    Fintype.card (M.ZeroPos i) = Fintype.card κ - (d + 1) := by
  classical
  change Fintype.card {j : κ // M.entry i j = none} = Fintype.card κ - (d + 1)
  rw [Fintype.card_subtype]
  exact M.rowZeroCard i

lemma card_completionIndex (M : PerlesMatrix ι κ d) :
    Fintype.card M.CompletionIndex =
      Fintype.card ι * 2 ^ (Fintype.card κ - (d + 1)) := by
  classical
  simp [CompletionIndex, card_zeroPos, Fintype.card_sigma, Finset.sum_const,
    Finset.card_univ]

/-- The C-matrix has fewer rows than all possible sign vectors of length `s`. -/
theorem scaled_bound (M : PerlesMatrix ι κ d) :
    Fintype.card ι * 2 ^ (Fintype.card κ - (d + 1)) < 2 ^ Fintype.card κ := by
  classical
  have hlt := Fintype.card_lt_of_injective_not_surjective M.completedSign
    M.completedSign_injective M.completedSign_not_surjective
  rw [M.card_completionIndex] at hlt
  simpa using hlt

/-- Perles's B/C-matrix counting conclusion. -/
theorem card_lt_two_pow_succ (M : PerlesMatrix ι κ d) :
    Fintype.card ι < 2 ^ (d + 1) := by
  classical
  have hscaled := M.scaled_bound
  have hpow :
      2 ^ Fintype.card κ =
        2 ^ (d + 1) * 2 ^ (Fintype.card κ - (d + 1)) := by
    rw [← pow_add, Nat.add_sub_of_le M.dimension_le_columns]
  rw [hpow] at hscaled
  exact Nat.lt_of_mul_lt_mul_right hscaled

/-- Remove one sign coordinate from a full Boolean sign vector. -/
def eraseCoordinate (anchor : κ) (v : κ → Bool) : ({j : κ // j ≠ anchor} → Bool) :=
  fun j => v j.1

/--
The half-cube invariant needed to remove the extra factor of two: every
completed row has a fixed value in one sign coordinate.

This is a sufficient sharpened endpoint condition.  A parity or antipodal-free
condition could replace it, but none of these is currently derived from the raw
touching-simplex geometry.
-/
def FixedCoordinateCompletions (M : PerlesMatrix ι κ d) : Prop :=
  ∃ anchor : κ, ∀ x : M.CompletionIndex, M.completedSign x anchor = true

/-- Flip every coordinate of a Boolean sign vector. -/
def complementSign (v : κ → Bool) : κ → Bool :=
  fun j => !v j

/-- The natural half-cube condition: completed rows contain no antipodal pair. -/
def AntipodalFreeCompletions (M : PerlesMatrix ι κ d) : Prop :=
  ∀ x y : M.CompletionIndex, M.completedSign y ≠ complementSign (M.completedSign x)

lemma eraseCoordinate_completedSign_injective_of_fixed (M : PerlesMatrix ι κ d)
    {anchor : κ} (hfixed : ∀ x : M.CompletionIndex, M.completedSign x anchor = true) :
    Function.Injective
      (fun x : M.CompletionIndex => eraseCoordinate anchor (M.completedSign x)) := by
  intro x y hxy
  apply M.completedSign_injective
  funext j
  by_cases hj : j = anchor
  · subst j
    rw [hfixed x, hfixed y]
  · exact congrFun hxy ⟨j, hj⟩

lemma card_bool_functions_off_coordinate (anchor : κ) :
    Fintype.card ({j : κ // j ≠ anchor} → Bool) = 2 ^ (Fintype.card κ - 1) := by
  classical
  simp [Fintype.card_subtype_compl]

/--
Choose the representative of an antipodal pair whose anchor coordinate is
`true`, then erase the anchor coordinate.
-/
def normalizeOffCoordinate (anchor : κ) (v : κ → Bool) : ({j : κ // j ≠ anchor} → Bool) :=
  if v anchor = true then eraseCoordinate anchor v else eraseCoordinate anchor (complementSign v)

omit [Fintype κ] in
lemma eq_or_eq_complementSign_of_normalizeOffCoordinate_eq (anchor : κ)
    {v w : κ → Bool} (h : normalizeOffCoordinate anchor v = normalizeOffCoordinate anchor w) :
    w = v ∨ w = complementSign v := by
  classical
  by_cases hv : v anchor = true
  · by_cases hw : w anchor = true
    · left
      funext j
      by_cases hj : j = anchor
      · subst j
        rw [hv, hw]
      · have hj_eq := congrFun h ⟨j, hj⟩
        exact (by simpa [normalizeOffCoordinate, eraseCoordinate, hv, hw] using hj_eq.symm)
    · right
      have hwfalse : w anchor = false := by
        cases hwa : w anchor <;> simp_all
      funext j
      by_cases hj : j = anchor
      · subst j
        simp [complementSign, hv, hwfalse]
      · have hj_eq := congrFun h ⟨j, hj⟩
        have hcoord : v j = !w j := by
          simpa [normalizeOffCoordinate, eraseCoordinate, complementSign, hv, hw] using hj_eq
        cases hvj : v j <;> cases hwj : w j <;>
          simp [complementSign, hvj, hwj] at hcoord ⊢
  · by_cases hw : w anchor = true
    · right
      have hvfalse : v anchor = false := by
        cases hva : v anchor <;> simp_all
      funext j
      by_cases hj : j = anchor
      · subst j
        simp [complementSign, hvfalse, hw]
      · have hj_eq := congrFun h ⟨j, hj⟩
        have hcoord : v j = !w j := by
          simpa [normalizeOffCoordinate, eraseCoordinate, complementSign, hv, hw] using hj_eq
        cases hvj : v j <;> cases hwj : w j <;>
          simp [complementSign, hvj, hwj] at hcoord ⊢
    · left
      have hvfalse : v anchor = false := by
        cases hva : v anchor <;> simp_all
      have hwfalse : w anchor = false := by
        cases hwa : w anchor <;> simp_all
      funext j
      by_cases hj : j = anchor
      · subst j
        rw [hvfalse, hwfalse]
      · have hj_eq := congrFun h ⟨j, hj⟩
        have hcoord : !v j = !w j := by
          simpa [normalizeOffCoordinate, eraseCoordinate, complementSign, hv, hw] using hj_eq
        cases hvj : v j <;> cases hwj : w j <;>
          simp [hvj, hwj] at hcoord ⊢

lemma normalizeOffCoordinate_completedSign_injective_of_antipodalFree (M : PerlesMatrix ι κ d)
    {anchor : κ} (hanti : M.AntipodalFreeCompletions) :
    Function.Injective
      (fun x : M.CompletionIndex => normalizeOffCoordinate anchor (M.completedSign x)) := by
  intro x y hxy
  rcases eq_or_eq_complementSign_of_normalizeOffCoordinate_eq anchor hxy with hsame | hantiPair
  · exact M.completedSign_injective hsame.symm
  · exact False.elim (hanti x y hantiPair)

lemma completionIndex_card_le_halfCube_of_fixed (M : PerlesMatrix ι κ d)
    {anchor : κ} (hfixed : ∀ x : M.CompletionIndex, M.completedSign x anchor = true) :
    Fintype.card M.CompletionIndex ≤ 2 ^ (Fintype.card κ - 1) := by
  classical
  calc
    Fintype.card M.CompletionIndex ≤
        Fintype.card ({j : κ // j ≠ anchor} → Bool) :=
      Fintype.card_le_of_injective
        (fun x : M.CompletionIndex => eraseCoordinate anchor (M.completedSign x))
        (M.eraseCoordinate_completedSign_injective_of_fixed hfixed)
    _ = 2 ^ (Fintype.card κ - 1) := card_bool_functions_off_coordinate anchor

/--
The C-matrix has at most half of the Boolean cube if its completed rows contain
no antipodal pair.
-/
lemma completionIndex_card_le_halfCube_of_antipodalFree (M : PerlesMatrix ι κ d)
    (anchor : κ) (hanti : M.AntipodalFreeCompletions) :
    Fintype.card M.CompletionIndex ≤ 2 ^ (Fintype.card κ - 1) := by
  classical
  calc
    Fintype.card M.CompletionIndex ≤
        Fintype.card ({j : κ // j ≠ anchor} → Bool) :=
      Fintype.card_le_of_injective
        (fun x : M.CompletionIndex => normalizeOffCoordinate anchor (M.completedSign x))
        (M.normalizeOffCoordinate_completedSign_injective_of_antipodalFree hanti)
    _ = 2 ^ (Fintype.card κ - 1) := card_bool_functions_off_coordinate anchor

/--
Sharp combinatorial endpoint: a Perles B/C-matrix whose completions lie in a
fixed half-cube gives the conjectural `2^d` bound.
-/
theorem card_le_two_pow_of_fixedCoordinate (M : PerlesMatrix ι κ d)
    (hfixed : M.FixedCoordinateCompletions) :
    Fintype.card ι ≤ 2 ^ d := by
  classical
  rcases hfixed with ⟨anchor, hanchor⟩
  have hhalf := M.completionIndex_card_le_halfCube_of_fixed hanchor
  rw [M.card_completionIndex] at hhalf
  have hpow :
      2 ^ (Fintype.card κ - 1) =
        2 ^ d * 2 ^ (Fintype.card κ - (d + 1)) := by
    rw [← pow_add]
    congr
    have hcolumns : d + 1 ≤ Fintype.card κ := M.dimension_le_columns
    omega
  rw [hpow] at hhalf
  exact Nat.le_of_mul_le_mul_right hhalf (Nat.two_pow_pos _)

/--
Sharp combinatorial endpoint in the antipodal-free form: if the completed rows
contain no antipodal pair, then the cardinality bound tightens to `2^d`.
-/
theorem card_le_two_pow_of_antipodalFree [Nonempty κ] (M : PerlesMatrix ι κ d)
    (hanti : M.AntipodalFreeCompletions) :
    Fintype.card ι ≤ 2 ^ d := by
  classical
  let anchor : κ := Classical.choice (inferInstance : Nonempty κ)
  have hhalf := M.completionIndex_card_le_halfCube_of_antipodalFree anchor hanti
  rw [M.card_completionIndex] at hhalf
  have hpow :
      2 ^ (Fintype.card κ - 1) =
        2 ^ d * 2 ^ (Fintype.card κ - (d + 1)) := by
    rw [← pow_add]
    congr
    have hcolumns : d + 1 ≤ Fintype.card κ := M.dimension_le_columns
    omega
  rw [hpow] at hhalf
  exact Nat.le_of_mul_le_mul_right hhalf (Nat.two_pow_pos _)

end PerlesMatrix

/-! ## Certified geometric data for Chapter 14 -/

/--
Certified Perles facet-separation data for a concrete touching family.

The type exposes the current honest frontier: Mathlib has the basic simplex
objects, but this file does not yet prove that every raw pairwise touching
family supplies these data.  In playbook point-17 terms, `chapter14` below is
state ③: conditional on the unproved geometric extraction of these fields.

This file now discharges the local simplex-side facts: see
`DSimplex.body_wSameSide_opposite_vertex`,
`DSimplex.relInterior_sSameSide_opposite_vertex`,
`DSimplex.facetHyperplane_injective`, and the two common-facet side-composition
lemmas above.  The remaining geometric construction is not a single Lean API
lookup.  It still requires at least the following facts:

* build the finite type of distinct facet hyperplanes from all simplex facets;
  the unoriented affine version is now `FacetHyperplanes`, with
  `card_facetHyperplanes_ge` proving the local `d+1` lower bound for nonempty
  families;
* prove the exact row-zero count for `simplexFacetSide`; the
  no-accidental-containment step is now proved as
  `DSimplex.facetHyperplane_eq_of_face_points_subset` and connected to
  `HasFacetIn` by
  `FacetHyperplanes.oriented_hasFacetIn_iff_exists_facetHyperplaneIndexOf`.
  Under side completeness, `FacetHyperplanes.rowZeroCard_of_side_complete`
  proves the row-zero count, and `ofFacetHyperplanes` uses it to fill the
  `rowZeroCard` field;
* orient each such affine hyperplane by closed halfspaces in
  `EuclideanSpace ℝ (Fin d)` and connect those halfspaces to Mathlib's
  `WSameSide`/`SSameSide` predicates; `FacetHyperplanes.oriented` chooses one
  incident facet for each distinct hyperplane, and
  `simplexFacetSide_oriented_witness_self` proves that witness simplex's
  positive B-entry, but all other incident simplices must still be classified
  as lying in the chosen positive or negative side;
* prove that the raw touching relation forces the opposite-vertex `SOppSide`
  hypothesis isolated by `TouchesAcrossFacets`; the local opposite B-entry
  theorem is now
  `exists_orientedHyperplane_opposite_entries_of_touchesAcrossFacets`, but it
  is not yet assembled into one global finite Perles matrix;
* choose a point avoiding the finite union of facet hyperplanes and simplex
  bodies to obtain the missing completed sign vector.

The sharper `≤ 2^d` theorem additionally needs a half-cube invariant for the
completed sign vectors.  This file proves both the fixed-coordinate endpoint
(`PerlesMatrix.FixedCoordinateCompletions`) and the antipodal-free endpoint
(`PerlesMatrix.AntipodalFreeCompletions`); the remaining task is deriving one
of these invariants geometrically.
-/
structure PerlesFacetSeparationData {ι : Type*} [Fintype ι] {d : ℕ} [NeZero d]
    (simplices : ι → DSimplex d) (κ : Type*) [Fintype κ] where
  hyperplane : κ → OrientedHyperplane d
  dimension_le_hyperplanes : d + 1 ≤ Fintype.card κ
  rowZeroCard :
    ∀ i : ι,
      (Finset.univ.filter fun j : κ =>
        (hyperplane j).simplexFacetSide (simplices i) = none).card =
          Fintype.card κ - (d + 1)
  pairwiseOpposite_of_touching :
    PairwiseTouching simplices →
      ∀ ⦃i j : ι⦄, i ≠ j → ∃ h : κ, ∃ b : Bool,
        (hyperplane h).simplexFacetSide (simplices i) = some b ∧
          (hyperplane h).simplexFacetSide (simplices j) = some (!b)
  missingSignVector :
    ∃ v : κ → Bool, ∀ i : ι,
      ¬ EntryExtends (fun j : κ => (hyperplane j).simplexFacetSide (simplices i)) v

namespace PerlesFacetSeparationData

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ} [NeZero d]
    {simplices : ι → DSimplex d}

/--
Build certified Perles data using the actual finite type of distinct facet
hyperplanes.  This discharges the hyperplane enumeration, dimension lower
bound, and B-row zero count; the remaining inputs are exactly the side
classification, pairwise opposite-sign, and missing-sign-vector geometry.
-/
def ofFacetHyperplanes [Nonempty ι] (simplices : ι → DSimplex d)
    (hside : ∀ (a : ι) (H : FacetHyperplanes simplices),
      (FacetHyperplanes.oriented simplices H).HasFacetIn (simplices a) →
        (simplices a).body ⊆ (FacetHyperplanes.oriented simplices H).positiveSide ∨
          (simplices a).body ⊆ (FacetHyperplanes.oriented simplices H).negativeSide)
    (hpairwise : PairwiseTouching simplices →
      ∀ ⦃a b : ι⦄, a ≠ b → ∃ H : FacetHyperplanes simplices, ∃ sign : Bool,
        (FacetHyperplanes.oriented simplices H).simplexFacetSide (simplices a) = some sign ∧
          (FacetHyperplanes.oriented simplices H).simplexFacetSide (simplices b) =
            some (!sign))
    (hmissing : ∃ v : FacetHyperplanes simplices → Bool, ∀ a : ι,
      ¬ EntryExtends
        (fun H : FacetHyperplanes simplices =>
          (FacetHyperplanes.oriented simplices H).simplexFacetSide (simplices a)) v) :
    PerlesFacetSeparationData simplices (FacetHyperplanes simplices) where
  hyperplane := FacetHyperplanes.oriented simplices
  dimension_le_hyperplanes := card_facetHyperplanes_ge simplices
  rowZeroCard := by
    intro a
    exact FacetHyperplanes.rowZeroCard_of_side_complete simplices a (hside a)
  pairwiseOpposite_of_touching := hpairwise
  missingSignVector := hmissing

/-- Convert certified geometric facet data into the abstract Perles matrix. -/
def toPerlesMatrix (D : PerlesFacetSeparationData simplices κ)
    (htouch : PairwiseTouching simplices) : PerlesMatrix ι κ d where
  entry i j := (D.hyperplane j).simplexFacetSide (simplices i)
  dimension_le_columns := D.dimension_le_hyperplanes
  rowZeroCard := D.rowZeroCard
  pairwiseOpposite := D.pairwiseOpposite_of_touching htouch
  missingSignVector := D.missingSignVector

end PerlesFacetSeparationData

/--
Chapter 14, as currently formalized: Perles's upper bound follows from a raw
pairwise touching family once the facet-hyperplane sign data have been
extracted and certified.

This deliberately no longer accepts an arbitrary injective sign map.  The
remaining missing theorem is the geometric construction of
`PerlesFacetSeparationData` from `PairwiseTouching simplices`.
-/
theorem chapter14 {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ} [NeZero d]
    (simplices : ι → DSimplex d) (htouch : PairwiseTouching simplices)
    (data : PerlesFacetSeparationData simplices κ) :
    Fintype.card ι < 2 ^ (d + 1) :=
  (data.toPerlesMatrix htouch).card_lt_two_pow_succ

/--
Conditional sharp version: if the geometric Perles data also supply a
half-cube invariant in the concrete fixed-coordinate form, then the cardinality
bound tightens to `2^d`.

The unproved frontier is deriving `FixedCoordinateCompletions` from the raw
touching-simplex geometry, or replacing it by an equivalent parity/antipodal
condition and proving that condition geometrically.
-/
theorem chapter14_sharp_of_fixedCoordinate {ι κ : Type*} [Fintype ι] [Fintype κ]
    {d : ℕ} [NeZero d] (simplices : ι → DSimplex d)
    (htouch : PairwiseTouching simplices) (data : PerlesFacetSeparationData simplices κ)
    (hfixed : (data.toPerlesMatrix htouch).FixedCoordinateCompletions) :
    Fintype.card ι ≤ 2 ^ d :=
  (data.toPerlesMatrix htouch).card_le_two_pow_of_fixedCoordinate hfixed

/--
Conditional sharp version in the antipodal-free form: if the completed sign
vectors contain no antipodal pair, then the cardinality bound tightens to
`2^d`.

The unproved frontier is deriving this antipodal-free condition from the raw
touching-simplex geometry.
-/
theorem chapter14_sharp_of_antipodalFree {ι κ : Type*} [Fintype ι] [Fintype κ]
    {d : ℕ} [NeZero d] (simplices : ι → DSimplex d)
    (htouch : PairwiseTouching simplices) (data : PerlesFacetSeparationData simplices κ)
    (hanti : (data.toPerlesMatrix htouch).AntipodalFreeCompletions) :
    Fintype.card ι ≤ 2 ^ d := by
  classical
  have hκpos : 0 < Fintype.card κ := by
    exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ d) data.dimension_le_hyperplanes
  haveI : Nonempty κ := Fintype.card_pos_iff.mp hκpos
  exact (data.toPerlesMatrix htouch).card_le_two_pow_of_antipodalFree hanti

end ProofsInTheBook.Chapter14
