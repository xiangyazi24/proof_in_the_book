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
counting step.  The remaining unformalized frontier is the extraction of the
certified Perles matrix from a raw family of touching simplices; see
`PerlesFacetSeparationData` below for the exact missing fields:

* enumerate the distinct oriented facet hyperplanes of the configuration;
* prove each simplex contributes exactly `d+1` nonzero B-entries;
* prove a touching pair has opposite signs in some shared facet hyperplane, and
  construct a point outside all simplices and facet hyperplanes to obtain the
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
and `chapter14_sharp_of_fixedCoordinate`.  The remaining gap is geometric:
derive that fixed-coordinate/parity/antipodal-free invariant, or an equivalent
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

/-- A finite family of pairwise touching `d`-simplices. -/
def PairwiseTouching {ι : Type*} {d : ℕ} [NeZero d]
    (simplices : ι → DSimplex d) : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → TouchesAlongFacets (simplices i) (simplices j)

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

/-- A simplex has a facet in the carrier of an oriented hyperplane. -/
def HasFacetIn {d : ℕ} [NeZero d] (H : OrientedHyperplane d) (S : DSimplex d) : Prop :=
  ∃ i : Fin (d + 1), Set.range (S.faceOpposite i).points ⊆ H.carrier

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

end OrientedHyperplane

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

end PerlesMatrix

/-! ## Certified geometric data for Chapter 14 -/

/--
Certified Perles facet-separation data for a concrete touching family.

The type exposes the current honest frontier: Mathlib has the basic simplex
objects, but this file does not yet prove that every raw pairwise touching
family supplies these data.  In playbook point-17 terms, `chapter14` below is
state ③: conditional on the unproved geometric extraction of these fields.

The missing geometric construction is not a single Lean API lookup.  It requires
at least the following facts:

* build the finite type of distinct facet hyperplanes from all simplex facets;
* orient each affine hyperplane by closed halfspaces in `EuclideanSpace ℝ (Fin d)`;
* prove every simplex with a facet in a listed hyperplane lies entirely in one
  of the two closed sides;
* prove that touching along a common facet forces opposite side signs;
* choose a point avoiding the finite union of facet hyperplanes and simplex
  bodies to obtain the missing completed sign vector.

The sharper `≤ 2^d` theorem would additionally need a half-cube invariant for
the completed sign vectors, such as the fixed-coordinate condition formalized
in `PerlesMatrix.FixedCoordinateCompletions`.
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

end ProofsInTheBook.Chapter14
