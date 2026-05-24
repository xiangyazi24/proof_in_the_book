import Mathlib

/-!
# Chapter 16: Borsuk's conjecture

From "Proofs from THE BOOK":

**Borsuk's conjecture**: Can every bounded set in ℝ^d be partitioned
into d+1 parts, each of smaller diameter? Borsuk conjectured yes (1933).

The book discusses the conjecture and its Kahn-Kalai (1993) disproof in
dimension `1325`.  The later `d ≥ 298` bound is due to Hinrichs-Richter
(2003) and uses a different construction.

Formalization status: this file defines finite color-class bookkeeping, states
the corrected `BorsukConjecture d` for covers of a bounded set by subsets of
itself in `EuclideanSpace ℝ (Fin d)`, packages a counterexample as
`KahnKalaiCertificate d`, and formalizes enough of the
Frankl-Wilson/Kahn-Kalai pipeline to prove the unconditional `chapter16`
statement from the pointed `p = 17` family.  The local construction currently
gives counterexamples for `4624 ≤ d ≤ 6848`.

Gap to the full book theorem: the Kahn-Kalai `d = 1325` bound still needs the
sharper fixed-layer Frankl-Wilson bound and the codimension-one cut-vector
realization.  Mathlib has Euclidean metric spaces and finite-set tools, but not
this Frankl-Wilson/Kahn-Kalai pipeline as an available theorem.

TODO (future): formalize the Hinrichs-Richter (2003) construction to reach
`d ≥ 298`; needs a separate 2-distance-set / strongly-regular-graph
construction not in the book's proof.

Mathlib search status (2026-05-24): no Frankl-Wilson theorem, modular
intersection theorem, Ray-Chaudhuri-Wilson theorem, or oddtown/eventown theorem
was present under those names or nearby combinatorial names.  The local
additions below provide the reusable diagonal-functional linear independence
core, its mod-2 oddtown specialization, and the prime modular-intersection
form needed by the pointed Kahn-Kalai construction.
-/

namespace ProofsInTheBook.Chapter16

/--
A finite coloring certificate for a Borsuk-style partition: points with the
same color are required to have pairwise distance below the target bound.
-/
def HasSmallColorClasses {α : Type*} [PseudoMetricSpace α] {d : ℕ} (points : Finset α)
    (diamBound : ℝ) (color : α → Fin (d + 1)) : Prop :=
  ∀ x ∈ points, ∀ y ∈ points, color x = color y → dist x y < diamBound

/-- One color class in the finite partition. -/
def colorClass {α : Type*} {d : ℕ} (points : Finset α) (color : α → Fin (d + 1))
    (c : Fin (d + 1)) : Finset α :=
  points.filter fun x => color x = c

theorem mem_colorClass_iff {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    (points : Finset α) (color : α → Fin (d + 1)) (c : Fin (d + 1)) (x : α) :
    x ∈ colorClass points color c ↔ x ∈ points ∧ color x = c := by
  simp [colorClass]

theorem colorClass_subset_points {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    (points : Finset α) (color : α → Fin (d + 1)) (c : Fin (d + 1)) :
    colorClass points color c ⊆ points := by
  intro x hx
  exact (mem_colorClass_iff points color c x).mp hx |>.1

theorem mem_colorClass_of_mem {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    {points : Finset α} {color : α → Fin (d + 1)} {x : α}
    (hx : x ∈ points) : x ∈ colorClass points color (color x) := by
  rw [mem_colorClass_iff]
  exact ⟨hx, rfl⟩

theorem exists_colorClass_of_mem {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    {points : Finset α} {color : α → Fin (d + 1)} {x : α}
    (hx : x ∈ points) : ∃ c : Fin (d + 1), x ∈ colorClass points color c :=
  ⟨color x, mem_colorClass_of_mem hx⟩

theorem disjoint_colorClass_of_ne {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    {points : Finset α} {color : α → Fin (d + 1)} {c₁ c₂ : Fin (d + 1)}
    (hne : c₁ ≠ c₂) : Disjoint (colorClass points color c₁) (colorClass points color c₂) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  have h₁ := (mem_colorClass_iff points color c₁ x).mp hx₁
  have h₂ := (mem_colorClass_iff points color c₂ x).mp hx₂
  exact hne (h₁.2.symm.trans h₂.2)

/-- The union of all color classes is the original point set. -/
theorem colorClass_biUnion_eq_points {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    [DecidableEq α] (points : Finset α) (color : α → Fin (d + 1)) :
    (Finset.univ.biUnion (fun c : Fin (d + 1) => colorClass points color c)) = points := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_colorClass_iff]
  constructor
  · rintro ⟨_, hx, _⟩; exact hx
  · intro hx; exact ⟨color x, hx, rfl⟩

/-- Each color class is bounded above by the total point count. -/
theorem colorClass_card_le {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    (points : Finset α) (color : α → Fin (d + 1)) (c : Fin (d + 1)) :
    (colorClass points color c).card ≤ points.card :=
  Finset.card_le_card (colorClass_subset_points points color c)

/-- The color class containing `x` is nonempty (since it contains `x`). -/
theorem colorClass_nonempty_of_mem {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    {points : Finset α} {color : α → Fin (d + 1)} {x : α}
    (hx : x ∈ points) :
    (colorClass points color (color x)).Nonempty :=
  ⟨x, mem_colorClass_of_mem hx⟩

/-- A color class is nonempty iff some point gets that color. -/
theorem colorClass_nonempty_iff {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    (points : Finset α) (color : α → Fin (d + 1)) (c : Fin (d + 1)) :
    (colorClass points color c).Nonempty ↔ ∃ x ∈ points, color x = c := by
  constructor
  · rintro ⟨x, hx⟩
    rw [mem_colorClass_iff] at hx
    exact ⟨x, hx.1, hx.2⟩
  · rintro ⟨x, hxp, hxc⟩
    exact ⟨x, (mem_colorClass_iff points color c x).mpr ⟨hxp, hxc⟩⟩

/-- The color classes partition the point set; cardinalities sum to `|points|`. -/
theorem colorClass_card_sum {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    [DecidableEq α] (points : Finset α) (color : α → Fin (d + 1)) :
    (∑ c : Fin (d + 1), (colorClass points color c).card) = points.card := by
  classical
  have h_disj :
      ((Finset.univ : Finset (Fin (d + 1))) : Set (Fin (d + 1))).PairwiseDisjoint
        (fun c => colorClass points color c) :=
    fun c₁ _ c₂ _ hne => disjoint_colorClass_of_ne hne
  have hcard := Finset.card_biUnion h_disj
  rw [colorClass_biUnion_eq_points] at hcard
  simpa using hcard.symm

/--
The basic verification step for a Borsuk partition: every color class has
the advertised smaller pairwise diameter bound.
-/
theorem same_color_dist_lt_of_mem_colorClass {α : Type*} [PseudoMetricSpace α] {d : ℕ}
    [DecidableEq (Fin (d + 1))] {points : Finset α} {diamBound : ℝ}
    {color : α → Fin (d + 1)} (h : HasSmallColorClasses points diamBound color)
    {c : Fin (d + 1)} {x y : α}
    (hx : x ∈ colorClass points color c) (hy : y ∈ colorClass points color c) :
    dist x y < diamBound := by
  rw [mem_colorClass_iff] at hx hy
  exact h x hx.1 y hy.1 (hx.2.trans hy.2.symm)

/--
Linear-algebra core used by Frankl-Wilson style arguments: a family of vectors
is linearly independent if there are linear functionals whose evaluation matrix
is diagonal with nonzero diagonal.
-/
theorem linearIndependent_of_linear_functionals_diagonal
    {K : Type*} [Field K] {ι M : Type*} [Fintype ι]
    [AddCommGroup M] [Module K M] (v : ι → M) (φ : ι → M →ₗ[K] K)
    (hdiag : ∀ i, φ i (v i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → φ i (v j) = 0) :
    LinearIndependent K v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  have happly : φ i (∑ j, g j • v j) = φ i 0 := congrArg (fun x => φ i x) hsum
  simp only [map_sum, map_smul, map_zero] at happly
  have hsingle : (∑ j, g j • φ i (v j)) = g i • φ i (v i) := by
    rw [Finset.sum_eq_single i]
    · intro j _ hji
      rw [hoff i j hji.symm]
      simp
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hsingle] at happly
  have hmul : g i * φ i (v i) = 0 := by simpa [smul_eq_mul] using happly
  exact (mul_eq_zero.mp hmul).resolve_right (hdiag i)

/-- Dimension bound form of `linearIndependent_of_linear_functionals_diagonal`. -/
theorem fintype_card_le_finrank_of_linear_functionals_diagonal
    {K : Type*} [Field K] {ι M : Type*} [Fintype ι]
    [AddCommGroup M] [Module K M] [Module.Finite K M]
    (v : ι → M) (φ : ι → M →ₗ[K] K)
    (hdiag : ∀ i, φ i (v i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → φ i (v j) = 0) :
    Fintype.card ι ≤ Module.finrank K M :=
  (linearIndependent_of_linear_functionals_diagonal v φ hdiag hoff).fintype_card_le_finrank

/-- The incidence vector of a finite set over `ZMod 2`. -/
def incidenceVector {α : Type*} [DecidableEq α] (A : Finset α) : α → ZMod 2 :=
  fun a => if a ∈ A then 1 else 0

/-- Dot product with a fixed vector over `ZMod 2`, as a linear functional. -/
def modTwoDotLinear {α : Type*} [Fintype α] (w : α → ZMod 2) :
    (α → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ a, v a * w a
  map_add' v₁ v₂ := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c v := by simp [mul_assoc, Finset.mul_sum]

/-- The mod-2 dot product of incidence vectors counts the intersection modulo 2. -/
theorem modTwoDotLinear_incidenceVector {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) :
    modTwoDotLinear (incidenceVector B) (incidenceVector A) = ((A ∩ B).card : ZMod 2) := by
  rw [Finset.card_eq_sum_ones]
  simp [modTwoDotLinear, incidenceVector, Finset.inter_comm]

/--
Oddtown linear independence: over `ZMod 2`, incidence vectors of sets with odd
self-intersection and even pairwise intersections are linearly independent.
-/
theorem incidenceVector_linearIndependent_of_odd_self_even_inter
    {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (sets : ι → Finset α)
    (hodd : ∀ i, Odd (sets i).card)
    (heven : ∀ i j, i ≠ j → Even ((sets i ∩ sets j).card)) :
    LinearIndependent (ZMod 2) (fun i => incidenceVector (sets i)) := by
  refine linearIndependent_of_linear_functionals_diagonal
    (K := ZMod 2) (v := fun i => incidenceVector (sets i))
    (φ := fun i => modTwoDotLinear (incidenceVector (sets i))) ?_ ?_
  · intro i
    rw [modTwoDotLinear_incidenceVector, Finset.inter_self]
    have hcast : ((sets i).card : ZMod 2) = 1 := Odd.natCast_zmod_two (hodd i)
    simp [hcast]
  · intro i j hne
    rw [modTwoDotLinear_incidenceVector]
    exact Even.natCast_zmod_two (heven j i hne.symm)

/--
Oddtown bound: a family of subsets of a finite ground set with odd sizes and
even pairwise intersections has at most as many members as ground elements.
This is the simplest eventown/oddtown-shaped fragment of the Frankl-Wilson
linear algebra method.
-/
theorem oddtown_card_le
    {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (sets : ι → Finset α)
    (hodd : ∀ i, Odd (sets i).card)
    (heven : ∀ i j, i ≠ j → Even ((sets i ∩ sets j).card)) :
    Fintype.card ι ≤ Fintype.card α := by
  have hlin := incidenceVector_linearIndependent_of_odd_self_even_inter sets hodd heven
  have hle := hlin.fintype_card_le_finrank
  simpa [Module.finrank_fintype_fun_eq_card] using hle

/-- Boolean monomial on finite subsets: it evaluates to `1` exactly when `I ⊆ X`. -/
def subsetMonomial (K : Type*) [Zero K] [One K] {α : Type*} [DecidableEq α]
    (I : Finset α) : Finset α → K :=
  fun X => if I ⊆ X then 1 else 0

/--
The subspace of Boolean functions spanned by monomials of degree at most `r`.
This is the direct set-family substitute for the low-degree multilinear
polynomial space in the Frankl-Wilson proof.
-/
def lowDegreeBooleanSubmodule (K : Type*) [Field K] (α : Type*) [Fintype α]
    [DecidableEq α] (r : ℕ) : Submodule K (Finset α → K) :=
  Submodule.span K
    (Set.range (fun I : {I : Finset α // I.card ≤ r} => subsetMonomial K I.1))

theorem subsetMonomial_mem_lowDegree {K α : Type*} [Field K] [Fintype α] [DecidableEq α]
    {r : ℕ} {I : Finset α} (hI : I.card ≤ r) :
    subsetMonomial K I ∈ lowDegreeBooleanSubmodule K α r :=
  Submodule.subset_span ⟨⟨I, hI⟩, rfl⟩

theorem finrank_lowDegreeBooleanSubmodule_le
    (K α : Type*) [Field K] [Fintype α] [DecidableEq α] (r : ℕ) :
    Module.finrank K (lowDegreeBooleanSubmodule K α r) ≤
      Fintype.card {I : Finset α // I.card ≤ r} :=
  finrank_range_le_card (R := K) (M := Finset α → K)
    (b := fun I : {I : Finset α // I.card ≤ r} => subsetMonomial K I.1)

theorem sum_subsetMonomial_insert_apply {K α : Type*} [Field K] [DecidableEq α]
    (A I X : Finset α) :
    (∑ a ∈ A, subsetMonomial K (insert a I) X) =
      ((A ∩ X).card : K) * subsetMonomial K I X := by
  by_cases hIX : I ⊆ X
  · have h_insert_iff : ∀ a, insert a I ⊆ X ↔ a ∈ X := by
      intro a
      constructor
      · intro h
        exact h (Finset.mem_insert_self a I)
      · intro ha x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact ha
        · exact hIX hx
    rw [Finset.card_eq_sum_ones]
    simp [subsetMonomial, hIX, h_insert_iff]
  · have h_insert_false : ∀ a, ¬ insert a I ⊆ X := by
      intro a h
      exact hIX ((Finset.subset_insert a I).trans h)
    simp [subsetMonomial, hIX, h_insert_false]

/-- Multiply a Boolean function by the affine intersection-count factor `|A ∩ X| - c`. -/
def booleanIntersectionFactor (K : Type*) [Field K] {α : Type*} [DecidableEq α]
    (A : Finset α) (c : K) : (Finset α → K) →ₗ[K] (Finset α → K) where
  toFun f := fun X => (((A ∩ X).card : K) - c) * f X
  map_add' f g := by
    ext X
    simp [mul_add]
  map_smul' c' f := by
    ext X
    simp only [Pi.smul_apply, RingHom.id_apply]
    ring

/--
The basic multilinearization identity: multiplying a monomial by `|A ∩ X| - c`
is a linear combination of monomials whose supports have grown by at most one.
-/
theorem booleanIntersectionFactor_subsetMonomial {K α : Type*} [Field K] [Fintype α]
    [DecidableEq α] (A I : Finset α) (c : K) :
    booleanIntersectionFactor K A c (subsetMonomial K I) =
      (∑ a ∈ A, subsetMonomial K (insert a I)) - c • subsetMonomial K I := by
  ext X
  simp only [booleanIntersectionFactor, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply,
    Pi.smul_apply, Finset.sum_apply]
  rw [sum_subsetMonomial_insert_apply (K := K) A I X]
  ring

/--
One Frankl-Wilson factor raises Boolean degree by at most one.  Iterating this
will put the usual product of forbidden-residue factors in the expected
low-degree space.
-/
theorem booleanIntersectionFactor_mem_lowDegree_succ {K α : Type*} [Field K] [Fintype α]
    [DecidableEq α] {r : ℕ} {A : Finset α} {c : K} {f : Finset α → K}
    (hf : f ∈ lowDegreeBooleanSubmodule K α r) :
    booleanIntersectionFactor K A c f ∈ lowDegreeBooleanSubmodule K α (r + 1) := by
  let target := lowDegreeBooleanSubmodule K α (r + 1)
  change booleanIntersectionFactor K A c f ∈ target
  refine Submodule.span_induction (s := Set.range
      (fun I : {I : Finset α // I.card ≤ r} => subsetMonomial K I.1)) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨I, rfl⟩
    rw [booleanIntersectionFactor_subsetMonomial]
    apply target.sub_mem
    · apply Submodule.sum_mem
      intro a _ha
      exact subsetMonomial_mem_lowDegree (K := K) (α := α)
        ((Finset.card_insert_le a I.1).trans (Nat.succ_le_succ I.2))
    · exact target.smul_mem c
        (subsetMonomial_mem_lowDegree (K := K) (α := α) (I.2.trans (Nat.le_succ r)))
  · simp
  · intro x y _ _ hx hy
    simpa using target.add_mem hx hy
  · intro a x _ hx
    simpa using target.smul_mem a hx

/--
The Frankl-Wilson product attached to a set `A` and a finite set of forbidden
field values.  On a Boolean input `X`, this is
`∏ c ∈ L, (|A ∩ X| - c)`.
-/
def franklWilsonFunction (K : Type*) [Field K] {α : Type*} [DecidableEq α]
    (A : Finset α) (L : Finset K) : Finset α → K :=
  fun X => ∏ c ∈ L, (((A ∩ X).card : K) - c)

theorem franklWilsonFunction_insert {K α : Type*} [Field K] [DecidableEq K]
    [DecidableEq α] {c : K} {L : Finset K} (hc : c ∉ L) (A : Finset α) :
    franklWilsonFunction K A (insert c L) =
      booleanIntersectionFactor K A c (franklWilsonFunction K A L) := by
  ext X
  simp [franklWilsonFunction, booleanIntersectionFactor, hc, mul_comm]

/--
The Frankl-Wilson product has Boolean degree at most the number of forbidden
values.  This is the low-degree half of the modular intersection theorem.
-/
theorem franklWilsonFunction_mem_lowDegree {K α : Type*} [Field K] [Fintype α]
    [DecidableEq K] [DecidableEq α] (A : Finset α) (L : Finset K) :
    franklWilsonFunction K A L ∈ lowDegreeBooleanSubmodule K α L.card := by
  induction L using Finset.induction_on with
  | empty =>
      simpa [franklWilsonFunction, subsetMonomial] using
        (subsetMonomial_mem_lowDegree (K := K) (α := α) (I := (∅ : Finset α)) (r := 0)
          (by simp))
  | insert c L hc hL =>
      rw [franklWilsonFunction_insert (K := K) (α := α) hc A]
      have hmem := booleanIntersectionFactor_mem_lowDegree_succ (K := K) (α := α)
        (A := A) (c := c) (f := franklWilsonFunction K A L) hL
      simpa [Finset.card_insert_of_notMem hc] using hmem

/-- Evaluation at a Boolean input as a linear functional on the Boolean function space. -/
def booleanEvalLinear (K : Type*) [Semiring K] {α : Type*} (X : Finset α) :
    (Finset α → K) →ₗ[K] K where
  toFun f := f X
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/--
Frankl-Wilson modular intersection bound over an arbitrary field.  If every
set has self-intersection outside `L`, while every distinct pair has
intersection in `L`, then the family size is at most the number of Boolean
monomials of degree at most `|L|`.
-/
theorem franklWilson_modular_intersection_bound
    {K α ι : Type*} [Field K] [Fintype α] [DecidableEq α] [DecidableEq K] [Fintype ι]
    (sets : ι → Finset α) (L : Finset K)
    (hself : ∀ i, ((sets i).card : K) ∉ L)
    (hinter : ∀ i j, i ≠ j → (((sets i ∩ sets j).card : K) ∈ L)) :
    Fintype.card ι ≤ Fintype.card {I : Finset α // I.card ≤ L.card} := by
  let target := lowDegreeBooleanSubmodule K α L.card
  let v : ι → target := fun i =>
    ⟨franklWilsonFunction K (sets i) L, franklWilsonFunction_mem_lowDegree (K := K)
      (α := α) (sets i) L⟩
  let φ : ι → target →ₗ[K] K := fun i => (booleanEvalLinear K (sets i)).comp target.subtype
  have hdiag : ∀ i, φ i (v i) ≠ 0 := by
    intro i
    dsimp [φ, v, booleanEvalLinear]
    rw [franklWilsonFunction, Finset.inter_self]
    change (∏ x ∈ L, (((sets i).card : K) - x)) ≠ 0
    rw [Finset.prod_ne_zero_iff]
    intro c hc
    rw [sub_ne_zero]
    intro h
    exact hself i (by simpa [h] using hc)
  have hoff : ∀ i j, i ≠ j → φ i (v j) = 0 := by
    intro i j hij
    dsimp [φ, v, booleanEvalLinear]
    rw [franklWilsonFunction]
    exact Finset.prod_eq_zero (hinter j i hij.symm) (by simp)
  have hcard_le_finrank : Fintype.card ι ≤ Module.finrank K target :=
    fintype_card_le_finrank_of_linear_functionals_diagonal v φ hdiag hoff
  exact hcard_le_finrank.trans (finrank_lowDegreeBooleanSubmodule_le K α L.card)

/-- The fixed-card slice of the Boolean cube. -/
abbrev FixedCardSubsets (α : Type*) [Fintype α] [DecidableEq α] (q : ℕ) :=
  {X : Finset α // X.card = q}

/-- A Boolean monomial restricted to the fixed-card slice. -/
def sliceSubsetMonomial (K : Type*) [Zero K] [One K] {α : Type*} [Fintype α]
    [DecidableEq α] {q : ℕ} (I : Finset α) : FixedCardSubsets α q → K :=
  fun X => subsetMonomial K I X.1

/--
On the fixed-card slice, monomials of degree at most `r` are spanned by
monomials of exact degree `r`, provided the relevant binomial coefficients are
nonzero in the field.
-/
def exactDegreeSliceSubmodule (K : Type*) [Field K] (α : Type*) [Fintype α]
    [DecidableEq α] (q r : ℕ) : Submodule K (FixedCardSubsets α q → K) :=
  Submodule.span K
    (Set.range (fun I : {I : Finset α // I.card = r} =>
      sliceSubsetMonomial K (q := q) I.1))

theorem exactDegreeSliceSubmodule_finrank_le
    (K α : Type*) [Field K] [Fintype α] [DecidableEq α] (q r : ℕ) :
    Module.finrank K (exactDegreeSliceSubmodule K α q r) ≤
      Fintype.card {I : Finset α // I.card = r} :=
  finrank_range_le_card (R := K) (M := FixedCardSubsets α q → K)
    (b := fun I : {I : Finset α // I.card = r} =>
      sliceSubsetMonomial K (q := q) I.1)

theorem sum_exact_slice_monomials_of_subset {K α : Type*} [Field K] [Fintype α]
    [DecidableEq α] {q r : ℕ} (I : Finset α) (hIr : I.card ≤ r) :
    (∑ J ∈ (Finset.univ : Finset α).powersetCard r with I ⊆ J,
        sliceSubsetMonomial K (q := q) J) =
      ((q - I.card).choose (r - I.card) : K) • sliceSubsetMonomial K (q := q) I := by
  ext X
  simp only [Finset.sum_apply]
  dsimp [sliceSubsetMonomial, subsetMonomial]
  by_cases hIX : I ⊆ X.1
  · have hleft_filter :
        ((Finset.univ : Finset α).powersetCard r).filter (fun J => I ⊆ J ∧ J ⊆ X.1) =
          (X.1.powersetCard r).filter (fun J => I ⊆ J) := by
      ext J
      simp [Finset.mem_powersetCard]
      aesop
    have hcard :
        (((Finset.univ : Finset α).powersetCard r).filter
            (fun J => I ⊆ J ∧ J ⊆ X.1)).card =
          (q - I.card).choose (r - I.card) := by
      rw [hleft_filter, Finset.card_filter_powersetCard_subset I X.1 r hIX hIr, X.2]
    rw [if_pos hIX]
    rw [← hcard]
    rw [← Finset.sum_boole (R := K) (s := (Finset.univ : Finset α).powersetCard r)
      (p := fun J => I ⊆ J ∧ J ⊆ X.1)]
    rw [Finset.sum_filter]
    rw [mul_one]
    apply Finset.sum_congr rfl
    intro J _hJ
    by_cases hIJ : I ⊆ J <;> by_cases hJX : J ⊆ X.1 <;> simp [hIJ, hJX]
  · have hzero :
        (∑ J ∈ (Finset.univ : Finset α).powersetCard r with I ⊆ J,
            if J ⊆ X.1 then (1 : K) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro J hJ
      rw [Finset.mem_filter] at hJ
      have hJXfalse : ¬ J ⊆ X.1 := by
        intro hJX
        exact hIX (hJ.2.trans hJX)
      simp [hJXfalse]
    rw [if_neg hIX]
    simpa using hzero

theorem sliceSubsetMonomial_mem_exact_of_card_le {K α : Type*} [Field K] [Fintype α]
    [DecidableEq α] {q r : ℕ} {I : Finset α} (hIr : I.card ≤ r)
    (hcoeff : ((q - I.card).choose (r - I.card) : K) ≠ 0) :
    sliceSubsetMonomial K (q := q) I ∈ exactDegreeSliceSubmodule K α q r := by
  let target := exactDegreeSliceSubmodule K α q r
  have hsum_mem :
      (∑ J ∈ (Finset.univ : Finset α).powersetCard r with I ⊆ J,
          sliceSubsetMonomial K (q := q) J) ∈ target := by
    apply Submodule.sum_mem
    intro J hJ
    rw [Finset.mem_filter] at hJ
    have hJcard : J.card = r := (Finset.mem_powersetCard.mp hJ.1).2
    exact Submodule.subset_span ⟨⟨J, hJcard⟩, rfl⟩
  have hscaled : ((q - I.card).choose (r - I.card) : K) •
      sliceSubsetMonomial K (q := q) I ∈ target := by
    simpa [target] using (by
      rw [← sum_exact_slice_monomials_of_subset (K := K) (q := q) I hIr]
      exact hsum_mem)
  exact (target.smul_mem_iff hcoeff).mp hscaled

theorem lowDegree_restrict_mem_exact {K α : Type*} [Field K] [Fintype α]
    [DecidableEq α] {q r : ℕ} {f : Finset α → K}
    (hcoeff : ∀ I : Finset α, I.card ≤ r →
      ((q - I.card).choose (r - I.card) : K) ≠ 0)
    (hf : f ∈ lowDegreeBooleanSubmodule K α r) :
    (fun X : FixedCardSubsets α q => f X.1) ∈ exactDegreeSliceSubmodule K α q r := by
  let target := exactDegreeSliceSubmodule K α q r
  change (fun X : FixedCardSubsets α q => f X.1) ∈ target
  refine Submodule.span_induction (s := Set.range
      (fun I : {I : Finset α // I.card ≤ r} => subsetMonomial K I.1)) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨I, rfl⟩
    change sliceSubsetMonomial K (q := q) I.1 ∈ target
    exact sliceSubsetMonomial_mem_exact_of_card_le (K := K) (α := α) (q := q) I.2
      (hcoeff I.1 I.2)
  · exact target.zero_mem
  · intro x y _ _ hx hy
    simpa using target.add_mem hx hy
  · intro a x _ hx
    simpa using target.smul_mem a hx

/-- Evaluation at a point of the fixed-card slice. -/
def fixedEvalLinear (K : Type*) [Semiring K] {α : Type*} [Fintype α] [DecidableEq α]
    {q : ℕ} (X : FixedCardSubsets α q) : (FixedCardSubsets α q → K) →ₗ[K] K where
  toFun f := f X
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/--
Frankl-Wilson bound sharpened on a fixed-card slice: the low-degree space can
be replaced by exact-degree monomials.
-/
theorem franklWilson_fixed_card_modular_intersection_bound
    {K α ι : Type*} [Field K] [Fintype α] [DecidableEq α] [DecidableEq K] [Fintype ι]
    {q : ℕ} (sets : ι → Finset α) (L : Finset K)
    (hcard : ∀ i, (sets i).card = q)
    (hcoeff : ∀ I : Finset α, I.card ≤ L.card →
      ((q - I.card).choose (L.card - I.card) : K) ≠ 0)
    (hself : ∀ i, ((sets i).card : K) ∉ L)
    (hinter : ∀ i j, i ≠ j → (((sets i ∩ sets j).card : K) ∈ L)) :
    Fintype.card ι ≤ Fintype.card {I : Finset α // I.card = L.card} := by
  let target := exactDegreeSliceSubmodule K α q L.card
  let v : ι → target := fun i =>
    ⟨fun X : FixedCardSubsets α q => franklWilsonFunction K (sets i) L X.1,
      lowDegree_restrict_mem_exact (K := K) (α := α) (q := q) (r := L.card)
        hcoeff (franklWilsonFunction_mem_lowDegree (K := K) (α := α) (sets i) L)⟩
  let φ : ι → target →ₗ[K] K := fun i =>
    (fixedEvalLinear K ⟨sets i, hcard i⟩).comp target.subtype
  have hdiag : ∀ i, φ i (v i) ≠ 0 := by
    intro i
    dsimp [φ, v, fixedEvalLinear]
    rw [franklWilsonFunction, Finset.inter_self]
    change (∏ x ∈ L, (((sets i).card : K) - x)) ≠ 0
    rw [Finset.prod_ne_zero_iff]
    intro c hc
    rw [sub_ne_zero]
    intro h
    exact hself i (by simpa [h] using hc)
  have hoff : ∀ i j, i ≠ j → φ i (v j) = 0 := by
    intro i j hij
    dsimp [φ, v, fixedEvalLinear]
    rw [franklWilsonFunction]
    exact Finset.prod_eq_zero (hinter j i hij.symm) (by simp)
  have hcard_le_finrank : Fintype.card ι ≤ Module.finrank K target :=
    fintype_card_le_finrank_of_linear_functionals_diagonal v φ hdiag hoff
  exact hcard_le_finrank.trans (exactDegreeSliceSubmodule_finrank_le K α q L.card)

/-- Count fixed-card subsets of a finite type. -/
theorem exactSubsets_card_eq_choose {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ) :
    Fintype.card {I : Finset α // I.card = r} = (Fintype.card α).choose r := by
  rw [Fintype.card_subtype]
  have hset : ({I : Finset α | I.card = r} : Finset (Finset α)) =
      (Finset.univ : Finset α).powersetCard r := by
    ext I
    simp [Finset.mem_powersetCard]
  rw [hset, Finset.card_powersetCard, Finset.card_univ]

/--
Coloring form of the fixed-card Frankl-Wilson bound.
-/
theorem exists_monochromatic_pair_fixed_card_intersection_notMem
    {K α ι κ : Type*} [Field K] [Fintype α] [DecidableEq α] [DecidableEq K]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    {q : ℕ} (sets : ι → Finset α) (L : Finset K) (color : ι → κ)
    (hcard : ∀ i, (sets i).card = q)
    (hcoeff : ∀ I : Finset α, I.card ≤ L.card →
      ((q - I.card).choose (L.card - I.card) : K) ≠ 0)
    (hself : ∀ i, ((sets i).card : K) ∉ L)
    (hlarge :
      Fintype.card κ * Fintype.card {I : Finset α // I.card = L.card} < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ color i = color j ∧ (((sets i ∩ sets j).card : K) ∉ L) := by
  obtain ⟨c, hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card color hlarge
  rw [← Fintype.card_subtype (fun i : ι => color i = c)] at hc
  let fiber := {i : ι // color i = c}
  let restrictedSets : fiber → Finset α := fun i => sets i.1
  have hcard_fiber : ∀ i : fiber, (restrictedSets i).card = q := by
    intro i
    exact hcard i.1
  have hself_fiber : ∀ i : fiber, ((restrictedSets i).card : K) ∉ L := by
    intro i
    exact hself i.1
  by_contra hno
  push Not at hno
  have hinter_fiber :
      ∀ i j : fiber, i ≠ j → (((restrictedSets i ∩ restrictedSets j).card : K) ∈ L) := by
    intro i j hij
    simpa [restrictedSets] using
      hno i.1 j.1 (fun h => hij (Subtype.ext h)) (i.2.trans j.2.symm)
  have hle :=
    franklWilson_fixed_card_modular_intersection_bound restrictedSets L hcard_fiber hcoeff
      hself_fiber hinter_fiber
  exact (not_lt_of_ge hle) hc


/--
Contrapositive form of `franklWilson_modular_intersection_bound`: a family
larger than the low-degree bound must contain a distinct pair whose
intersection cardinality avoids the allowed residue set.
-/
theorem exists_pair_intersection_notMem_of_card_bound_lt
    {K α ι : Type*} [Field K] [Fintype α] [DecidableEq α] [DecidableEq K] [Fintype ι]
    (sets : ι → Finset α) (L : Finset K)
    (hself : ∀ i, ((sets i).card : K) ∉ L)
    (hlarge : Fintype.card {I : Finset α // I.card ≤ L.card} < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ (((sets i ∩ sets j).card : K) ∉ L) := by
  by_contra hno
  push Not at hno
  have hinter : ∀ i j, i ≠ j → (((sets i ∩ sets j).card : K) ∈ L) := by
    intro i j hij
    exact hno i j hij
  have hle := franklWilson_modular_intersection_bound sets L hself hinter
  exact (not_lt_of_ge hle) hlarge

/--
Coloring form of Frankl-Wilson.  If a set family is larger than
`(# colors) * (low-degree bound)`, then every coloring contains a monochromatic
pair whose intersection cardinality avoids the allowed residue set.
-/
theorem exists_monochromatic_pair_intersection_notMem
    {K α ι κ : Type*} [Field K] [Fintype α] [DecidableEq α] [DecidableEq K]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (sets : ι → Finset α) (L : Finset K) (color : ι → κ)
    (hself : ∀ i, ((sets i).card : K) ∉ L)
    (hlarge :
      Fintype.card κ * Fintype.card {I : Finset α // I.card ≤ L.card} < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ color i = color j ∧ (((sets i ∩ sets j).card : K) ∉ L) := by
  obtain ⟨c, hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card color hlarge
  rw [← Fintype.card_subtype (fun i : ι => color i = c)] at hc
  let fiber := {i : ι // color i = c}
  let restrictedSets : fiber → Finset α := fun i => sets i.1
  have hself_fiber : ∀ i : fiber, ((restrictedSets i).card : K) ∉ L := by
    intro i
    exact hself i.1
  obtain ⟨i, j, hij, hnot⟩ :=
    exists_pair_intersection_notMem_of_card_bound_lt restrictedSets L hself_fiber hc
  exact ⟨i.1, j.1, fun h => hij (Subtype.ext h), i.2.trans j.2.symm, hnot⟩

/--
The Hamming distance between two finite subsets of a finite ground type,
counted as the number of coordinates where their membership indicators differ.
-/
def finsetSymmDiffSet {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) : Finset α :=
  Finset.univ.filter fun a => (a ∈ A ∧ a ∉ B) ∨ (a ∈ B ∧ a ∉ A)

def finsetSymmDiffCard {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) : ℕ :=
  (finsetSymmDiffSet A B).card

theorem mem_finsetSymmDiffSet_iff {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Finset α} {a : α} :
    a ∈ finsetSymmDiffSet A B ↔ (a ∈ A ∧ a ∉ B) ∨ (a ∈ B ∧ a ∉ A) := by
  simp [finsetSymmDiffSet]

theorem finsetSymmDiffSet_eq_sdiff_union_sdiff
    {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) :
    finsetSymmDiffSet A B = (A \ B) ∪ (B \ A) := by
  ext a
  simp [finsetSymmDiffSet]

theorem finsetSymmDiffCard_eq_card_sdiff_add_card_sdiff
    {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) :
    finsetSymmDiffCard A B = (A \ B).card + (B \ A).card := by
  rw [finsetSymmDiffCard, finsetSymmDiffSet_eq_sdiff_union_sdiff]
  rw [Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro a ha hb
  simp at ha hb
  exact ha.2 hb.1

theorem finsetSymmDiffCard_eq_two_mul_sub_inter_of_card_eq
    {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) {r : ℕ}
    (hA : A.card = r) (hB : B.card = r) :
    finsetSymmDiffCard A B = 2 * (r - (A ∩ B).card) := by
  rw [finsetSymmDiffCard_eq_card_sdiff_add_card_sdiff]
  have hAB := Finset.card_sdiff_add_card_inter (s := B) (t := A)
  have hBA := Finset.card_sdiff_add_card_inter (s := A) (t := B)
  rw [Finset.inter_comm B A] at hAB
  omega

theorem finsetSymmDiffSet_image_equiv
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (A B : Finset α) :
    finsetSymmDiffSet (A.image e) (B.image e) = (finsetSymmDiffSet A B).image e := by
  ext b
  constructor
  · intro hb
    obtain ⟨a, rfl⟩ := e.surjective b
    simpa [finsetSymmDiffSet] using hb
  · intro hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    simpa [finsetSymmDiffSet] using ha

theorem finsetSymmDiffCard_image_equiv
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (A B : Finset α) :
    finsetSymmDiffCard (A.image e) (B.image e) = finsetSymmDiffCard A B := by
  rw [finsetSymmDiffCard, finsetSymmDiffSet_image_equiv]
  exact Finset.card_image_of_injective _ e.injective

theorem finsetSymmDiffSet_image_embedding
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (A B : Finset α) :
    finsetSymmDiffSet (A.image e) (B.image e) = (finsetSymmDiffSet A B).image e := by
  ext b
  constructor
  · intro hb
    simp only [finsetSymmDiffSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image] at hb ⊢
    rcases hb with hb | hb
    · obtain ⟨a, haA, rfl⟩ := hb.1
      have haB : a ∉ B := by
        intro haB
        exact hb.2 ⟨a, haB, rfl⟩
      exact ⟨a, Or.inl ⟨haA, haB⟩, rfl⟩
    · obtain ⟨a, haB, rfl⟩ := hb.1
      have haA : a ∉ A := by
        intro haA
        exact hb.2 ⟨a, haA, rfl⟩
      exact ⟨a, Or.inr ⟨haB, haA⟩, rfl⟩
  · intro hb
    simp only [finsetSymmDiffSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image] at hb ⊢
    obtain ⟨a, ha, rfl⟩ := hb
    rcases ha with ha | ha
    · exact Or.inl ⟨⟨a, ha.1, rfl⟩, by
        rintro ⟨a', haB, heq⟩
        exact ha.2 ((e.injective heq.symm) ▸ haB)⟩
    · exact Or.inr ⟨⟨a, ha.1, rfl⟩, by
        rintro ⟨a', haA, heq⟩
        exact ha.2 ((e.injective heq.symm) ▸ haA)⟩

theorem finsetSymmDiffCard_image_embedding
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (A B : Finset α) :
    finsetSymmDiffCard (A.image e) (B.image e) = finsetSymmDiffCard A B := by
  rw [finsetSymmDiffCard, finsetSymmDiffSet_image_embedding]
  exact Finset.card_image_of_injective _ e.injective

/-- The directed cut induced by a finite subset of the vertex set. -/
def directedCutSet {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) : Finset (α × α) :=
  Finset.univ.filter fun e => (e.1 ∈ A ∧ e.2 ∉ A) ∨ (e.1 ∉ A ∧ e.2 ∈ A)

theorem mem_directedCutSet_iff {α : Type*} [Fintype α] [DecidableEq α]
    {A : Finset α} {e : α × α} :
    e ∈ directedCutSet A ↔ (e.1 ∈ A ∧ e.2 ∉ A) ∨ (e.1 ∉ A ∧ e.2 ∈ A) := by
  simp [directedCutSet]

theorem directedCutSet_symmDiffSet_eq {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) :
    finsetSymmDiffSet (directedCutSet A) (directedCutSet B) =
      (finsetSymmDiffSet A B ×ˢ (finsetSymmDiffSet A B)ᶜ) ∪
        ((finsetSymmDiffSet A B)ᶜ ×ˢ finsetSymmDiffSet A B) := by
  ext e
  rcases e with ⟨x, y⟩
  by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;>
    by_cases hyA : y ∈ A <;> by_cases hyB : y ∈ B <;>
    simp [finsetSymmDiffSet, directedCutSet, hxA, hxB, hyA, hyB]

/--
For directed cut incidence vectors, the number of changed coordinates is
`2r(|V|-r)`, where `r` is the vertex Hamming distance between the two sides.
-/
theorem directedCutSet_symmDiffCard {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) :
    finsetSymmDiffCard (directedCutSet A) (directedCutSet B) =
      2 * finsetSymmDiffCard A B * (Fintype.card α - finsetSymmDiffCard A B) := by
  rw [finsetSymmDiffCard, directedCutSet_symmDiffSet_eq]
  have hdisj : Disjoint (finsetSymmDiffSet A B ×ˢ (finsetSymmDiffSet A B)ᶜ)
      ((finsetSymmDiffSet A B)ᶜ ×ˢ finsetSymmDiffSet A B) := by
    rw [Finset.disjoint_product]
    exact Or.inl disjoint_compl_right
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product,
    Finset.card_compl]
  rw [finsetSymmDiffCard]
  ring

/-- The number of ordered crossing pairs for a cut. -/
theorem directedCutSet_card {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) :
    (directedCutSet A).card = 2 * A.card * (Fintype.card α - A.card) := by
  rw [directedCutSet]
  have hset :
      (Finset.univ.filter fun e : α × α =>
          (e.1 ∈ A ∧ e.2 ∉ A) ∨ (e.1 ∉ A ∧ e.2 ∈ A)) =
        (A ×ˢ Aᶜ) ∪ (Aᶜ ×ˢ A) := by
    ext e
    simp
  rw [hset]
  have hdisj : Disjoint (A ×ˢ Aᶜ) (Aᶜ ×ˢ A) := by
    rw [Finset.disjoint_product]
    exact Or.inl disjoint_compl_right
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product,
    Finset.card_compl]
  ring

/-- The type of unordered non-loop edges on a vertex type. -/
abbrev UndirectedEdge (α : Type*) := {e : Sym2 α // ¬ e.IsDiag}

/-- The complete bipartite cut graph determined by `A`. -/
def cutGraph {α : Type*} [DecidableEq α] (A : Finset α) : SimpleGraph α :=
  SimpleGraph.fromRel fun x y => x ∈ A ∧ y ∉ A

/-- The unordered cut as a finite set of non-loop edges. -/
noncomputable def undirectedCutSet {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) : Finset (UndirectedEdge α) := by
  classical
  exact Finset.univ.filter fun e => e.1 ∈ (cutGraph A).edgeSet

theorem mem_undirectedCutSet_iff {α : Type*} [Fintype α] [DecidableEq α]
    {A : Finset α} {e : UndirectedEdge α} :
    e ∈ undirectedCutSet A ↔ e.1 ∈ (cutGraph A).edgeSet := by
  classical
  simp [undirectedCutSet]

noncomputable def cutEdgeSubtypeEquiv {α : Type*} [DecidableEq α] (G : SimpleGraph α) :
    {e : UndirectedEdge α // e.1 ∈ G.edgeSet} ≃ G.edgeSet where
  toFun e := ⟨e.1.1, e.2⟩
  invFun e := ⟨⟨e.1, SimpleGraph.not_isDiag_of_mem_edgeSet G e.2⟩, e.2⟩
  left_inv := by
    rintro ⟨⟨e, _hdiag⟩, _hedge⟩
    rfl
  right_inv := by
    rintro ⟨e, _hedge⟩
    rfl

/-- The unordered cut has `|A| * |Aᶜ|` edges. -/
theorem undirectedCutSet_card {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) :
    (undirectedCutSet A).card = A.card * (Fintype.card α - A.card) := by
  classical
  let G := cutGraph A
  letI : Fintype G.edgeSet := G.fintypeEdgeSet
  have htwo := SimpleGraph.two_mul_card_edgeFinset G
  rw [SimpleGraph.edgeFinset_card] at htwo
  have hdir : ({x : α × α | G.Adj x.1 x.2} : Finset (α × α)).card =
      (directedCutSet A).card := by
    apply congrArg Finset.card
    rw [directedCutSet]
    ext e
    simp [G, cutGraph]
    constructor
    · intro h
      rcases h.2 with hxy | hyx
      · exact Or.inl hxy
      · exact Or.inr ⟨hyx.2, hyx.1⟩
    · intro h
      refine ⟨?_, ?_⟩
      · intro heq
        rcases h with hxy | hyx
        · exact hxy.2 (by simpa [heq] using hxy.1)
        · exact hyx.1 (by simpa [heq] using hyx.2)
      · rcases h with hxy | hyx
        · exact Or.inl hxy
        · exact Or.inr ⟨hyx.2, hyx.1⟩
  rw [hdir, directedCutSet_card] at htwo
  have hGcard : Fintype.card G.edgeSet = A.card * (Fintype.card α - A.card) := by
    have htwo' : 2 * Fintype.card G.edgeSet =
        2 * (A.card * (Fintype.card α - A.card)) := by
      simpa [mul_assoc] using htwo
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) htwo'
  have hsubCard :
      Fintype.card {e : UndirectedEdge α // e.1 ∈ G.edgeSet} = (undirectedCutSet A).card := by
    exact Fintype.card_ofFinset (undirectedCutSet A) (by
      intro e
      change e ∈ undirectedCutSet A ↔ e.1 ∈ G.edgeSet
      simp [undirectedCutSet, G])
  rw [← hsubCard]
  rw [Fintype.card_congr (cutEdgeSubtypeEquiv G)]
  exact hGcard

theorem undirectedCutSet_symmDiffSet_eq {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) :
    finsetSymmDiffSet (undirectedCutSet A) (undirectedCutSet B) =
      undirectedCutSet (finsetSymmDiffSet A B) := by
  classical
  ext e
  rw [mem_finsetSymmDiffSet_iff]
  simp only [mem_undirectedCutSet_iff]
  obtain ⟨z, _hz⟩ := e
  obtain ⟨⟨x, y⟩, hxy⟩ := Quot.exists_rep z
  subst z
  simp [cutGraph, finsetSymmDiffSet]
  tauto

theorem undirectedCutSet_symmDiffCard {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) :
    finsetSymmDiffCard (undirectedCutSet A) (undirectedCutSet B) =
      finsetSymmDiffCard A B * (Fintype.card α - finsetSymmDiffCard A B) := by
  rw [finsetSymmDiffCard, undirectedCutSet_symmDiffSet_eq, undirectedCutSet_card,
    finsetSymmDiffCard]

theorem undirectedCutSet_symmDiffCard_of_card_eq
    {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) {r : ℕ}
    (hA : A.card = r) (hB : B.card = r) :
    finsetSymmDiffCard (undirectedCutSet A) (undirectedCutSet B) =
      (2 * (r - (A ∩ B).card)) *
        (Fintype.card α - 2 * (r - (A ∩ B).card)) := by
  rw [undirectedCutSet_symmDiffCard,
    finsetSymmDiffCard_eq_two_mul_sub_inter_of_card_eq A B hA hB]

theorem undirectedCutSet_symmDiffCard_of_kahnKalai_intersection
    {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) {k : ℕ}
    (hground : Fintype.card α = 4 * k)
    (hA : A.card = 2 * k) (hB : B.card = 2 * k)
    (hinter : (A ∩ B).card = k) :
    finsetSymmDiffCard (undirectedCutSet A) (undirectedCutSet B) = 4 * k * k := by
  rw [undirectedCutSet_symmDiffCard_of_card_eq A B hA hB, hground, hinter]
  have hsub : 2 * k - k = k := by omega
  rw [hsub]
  have hsub' : 4 * k - 2 * k = 2 * k := by omega
  rw [hsub']
  ring

theorem directedCutSet_symmDiffCard_of_card_eq
    {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) {r : ℕ}
    (hA : A.card = r) (hB : B.card = r) :
    finsetSymmDiffCard (directedCutSet A) (directedCutSet B) =
      2 * (2 * (r - (A ∩ B).card)) *
        (Fintype.card α - 2 * (r - (A ∩ B).card)) := by
  rw [directedCutSet_symmDiffCard,
    finsetSymmDiffCard_eq_two_mul_sub_inter_of_card_eq A B hA hB]

theorem directedCutSet_symmDiffCard_of_kahnKalai_intersection
    {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) {k : ℕ}
    (hground : Fintype.card α = 4 * k)
    (hA : A.card = 2 * k) (hB : B.card = 2 * k)
    (hinter : (A ∩ B).card = k) :
    finsetSymmDiffCard (directedCutSet A) (directedCutSet B) = 8 * k * k := by
  rw [directedCutSet_symmDiffCard_of_card_eq A B hA hB, hground, hinter]
  have hsub : 2 * k - k = k := by omega
  rw [hsub]
  have hsub' : 4 * k - 2 * k = 2 * k := by omega
  rw [hsub']
  ring

/-- The `0/1` incidence vector of a finite set, viewed as a Euclidean point. -/
noncomputable def realIncidencePoint {α : Type*} [DecidableEq α]
    (A : Finset α) : EuclideanSpace ℝ α :=
  WithLp.toLp 2 fun a => if a ∈ A then (1 : ℝ) else 0

@[simp]
theorem realIncidencePoint_apply {α : Type*} [DecidableEq α]
    (A : Finset α) (a : α) :
    realIncidencePoint A a = if a ∈ A then (1 : ℝ) else 0 :=
  rfl

theorem sum_sq_indicator_sub_eq_finsetSymmDiffCard
    {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) :
    (∑ a : α, ((if a ∈ A then (1 : ℝ) else 0) -
        (if a ∈ B then (1 : ℝ) else 0)) ^ 2) =
      (finsetSymmDiffCard A B : ℝ) := by
  rw [finsetSymmDiffCard, finsetSymmDiffSet]
  rw [← Finset.sum_boole (R := ℝ) (s := Finset.univ)
    (p := fun a => (a ∈ A ∧ a ∉ B) ∨ (a ∈ B ∧ a ∉ A))]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;> simp [hA, hB]

/--
The squared Euclidean distance between incidence vectors is the Hamming
distance of the underlying sets.
-/
theorem realIncidencePoint_dist_sq {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) :
    dist (realIncidencePoint A) (realIncidencePoint B) ^ 2 =
      (finsetSymmDiffCard A B : ℝ) := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  rw [PiLp.inner_apply]
  trans ∑ a : α, ((if a ∈ A then (1 : ℝ) else 0) -
      (if a ∈ B then (1 : ℝ) else 0)) ^ 2
  · apply Finset.sum_congr rfl
    intro a _
    simp [pow_two]
  · exact sum_sq_indicator_sub_eq_finsetSymmDiffCard A B

theorem realIncidencePoint_dist_eq_sqrt {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) :
    dist (realIncidencePoint A) (realIncidencePoint B) =
      Real.sqrt (finsetSymmDiffCard A B : ℝ) := by
  have hsq :
      dist (realIncidencePoint A) (realIncidencePoint B) ^ 2 =
        (Real.sqrt (finsetSymmDiffCard A B : ℝ)) ^ 2 := by
    rw [realIncidencePoint_dist_sq, Real.sq_sqrt]
    exact Nat.cast_nonneg _
  have habs :
      |dist (realIncidencePoint A) (realIncidencePoint B)| =
        |Real.sqrt (finsetSymmDiffCard A B : ℝ)| :=
    (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
  rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg (Real.sqrt_nonneg _)] at habs

theorem realIncidencePoint_dist_eq_of_symmDiffCard_eq
    {α : Type*} [Fintype α] [DecidableEq α] {A B C D : Finset α}
    (h : finsetSymmDiffCard A B = finsetSymmDiffCard C D) :
    dist (realIncidencePoint A) (realIncidencePoint B) =
      dist (realIncidencePoint C) (realIncidencePoint D) := by
  rw [realIncidencePoint_dist_eq_sqrt, realIncidencePoint_dist_eq_sqrt, h]

/-- Reindex an incidence vector along an equivalence to a `Fin d` coordinate type. -/
noncomputable def finReindexedIncidencePoint
    {β : Type*} [Fintype β] [DecidableEq β] {d : ℕ}
    (e : β ≃ Fin d) (A : Finset β) : EuclideanSpace ℝ (Fin d) :=
  realIncidencePoint (A.image e)

theorem finReindexedIncidencePoint_dist_sq
    {β : Type*} [Fintype β] [DecidableEq β] {d : ℕ}
    (e : β ≃ Fin d) (A B : Finset β) :
    dist (finReindexedIncidencePoint e A) (finReindexedIncidencePoint e B) ^ 2 =
      (finsetSymmDiffCard A B : ℝ) := by
  change dist (realIncidencePoint (A.image e)) (realIncidencePoint (B.image e)) ^ 2 =
    (finsetSymmDiffCard A B : ℝ)
  rw [realIncidencePoint_dist_sq, finsetSymmDiffCard_image_equiv]

noncomputable def finReindexedDirectedCutPoint
    {α : Type*} [Fintype α] [DecidableEq α] {d : ℕ}
    (e : (α × α) ≃ Fin d) (A : Finset α) : EuclideanSpace ℝ (Fin d) :=
  finReindexedIncidencePoint e (directedCutSet A)

theorem finReindexedDirectedCutPoint_dist_sq_of_kahnKalai_intersection
    {α : Type*} [Fintype α] [DecidableEq α] {d k : ℕ}
    (e : (α × α) ≃ Fin d) (A B : Finset α)
    (hground : Fintype.card α = 4 * k)
    (hA : A.card = 2 * k) (hB : B.card = 2 * k)
    (hinter : (A ∩ B).card = k) :
    dist (finReindexedDirectedCutPoint e A) (finReindexedDirectedCutPoint e B) ^ 2 =
      ((8 * k * k : ℕ) : ℝ) := by
  change dist (finReindexedIncidencePoint e (directedCutSet A))
      (finReindexedIncidencePoint e (directedCutSet B)) ^ 2 = ((8 * k * k : ℕ) : ℝ)
  rw [finReindexedIncidencePoint_dist_sq,
    directedCutSet_symmDiffCard_of_kahnKalai_intersection A B hground hA hB hinter]

theorem kahnKalai_quadratic_bound_real {p x : ℕ} (hx : x ≤ 2 * p) :
    ((2 * (2 * x) * (4 * p - 2 * x) : ℕ) : ℝ) ≤ ((8 * p * p : ℕ) : ℝ) := by
  have hx2 : 2 * x ≤ 4 * p := by nlinarith
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hx2]
  norm_num
  have hs : 0 ≤ ((x : ℝ) - p) ^ 2 := sq_nonneg _
  nlinarith

theorem finReindexedDirectedCutPoint_dist_sq_le_kahnKalai
    {α : Type*} [Fintype α] [DecidableEq α] {d p : ℕ}
    (coord : (α × α) ≃ Fin d) (A B : Finset α)
    (hground : Fintype.card α = 4 * p)
    (hA : A.card = 2 * p) (hB : B.card = 2 * p) :
    dist (finReindexedDirectedCutPoint coord A) (finReindexedDirectedCutPoint coord B) ^ 2 ≤
      ((8 * p * p : ℕ) : ℝ) := by
  change dist (finReindexedIncidencePoint coord (directedCutSet A))
      (finReindexedIncidencePoint coord (directedCutSet B)) ^ 2 ≤ ((8 * p * p : ℕ) : ℝ)
  rw [finReindexedIncidencePoint_dist_sq,
    directedCutSet_symmDiffCard_of_card_eq A B hA hB, hground]
  exact kahnKalai_quadratic_bound_real (Nat.sub_le _ _)

/-- Reindex an incidence vector along an embedding into a `Fin d` coordinate type. -/
noncomputable def finEmbeddedIncidencePoint
    {β : Type*} [Fintype β] [DecidableEq β] {d : ℕ}
    (e : β ↪ Fin d) (A : Finset β) : EuclideanSpace ℝ (Fin d) :=
  realIncidencePoint (A.image e)

theorem finEmbeddedIncidencePoint_dist_sq
    {β : Type*} [Fintype β] [DecidableEq β] {d : ℕ}
    (e : β ↪ Fin d) (A B : Finset β) :
    dist (finEmbeddedIncidencePoint e A) (finEmbeddedIncidencePoint e B) ^ 2 =
      (finsetSymmDiffCard A B : ℝ) := by
  change dist (realIncidencePoint (A.image e)) (realIncidencePoint (B.image e)) ^ 2 =
    (finsetSymmDiffCard A B : ℝ)
  rw [realIncidencePoint_dist_sq, finsetSymmDiffCard_image_embedding]

noncomputable def finEmbeddedDirectedCutPoint
    {α : Type*} [Fintype α] [DecidableEq α] {d : ℕ}
    (e : (α × α) ↪ Fin d) (A : Finset α) : EuclideanSpace ℝ (Fin d) :=
  finEmbeddedIncidencePoint e (directedCutSet A)

theorem finEmbeddedDirectedCutPoint_dist_sq_of_kahnKalai_intersection
    {α : Type*} [Fintype α] [DecidableEq α] {d k : ℕ}
    (e : (α × α) ↪ Fin d) (A B : Finset α)
    (hground : Fintype.card α = 4 * k)
    (hA : A.card = 2 * k) (hB : B.card = 2 * k)
    (hinter : (A ∩ B).card = k) :
    dist (finEmbeddedDirectedCutPoint e A) (finEmbeddedDirectedCutPoint e B) ^ 2 =
      ((8 * k * k : ℕ) : ℝ) := by
  change dist (finEmbeddedIncidencePoint e (directedCutSet A))
      (finEmbeddedIncidencePoint e (directedCutSet B)) ^ 2 = ((8 * k * k : ℕ) : ℝ)
  rw [finEmbeddedIncidencePoint_dist_sq,
    directedCutSet_symmDiffCard_of_kahnKalai_intersection A B hground hA hB hinter]

theorem finEmbeddedDirectedCutPoint_dist_sq_le_kahnKalai
    {α : Type*} [Fintype α] [DecidableEq α] {d p : ℕ}
    (coord : (α × α) ↪ Fin d) (A B : Finset α)
    (hground : Fintype.card α = 4 * p)
    (hA : A.card = 2 * p) (hB : B.card = 2 * p) :
    dist (finEmbeddedDirectedCutPoint coord A) (finEmbeddedDirectedCutPoint coord B) ^ 2 ≤
      ((8 * p * p : ℕ) : ℝ) := by
  change dist (finEmbeddedIncidencePoint coord (directedCutSet A))
      (finEmbeddedIncidencePoint coord (directedCutSet B)) ^ 2 ≤ ((8 * p * p : ℕ) : ℝ)
  rw [finEmbeddedIncidencePoint_dist_sq,
    directedCutSet_symmDiffCard_of_card_eq A B hA hB, hground]
  exact kahnKalai_quadratic_bound_real (Nat.sub_le _ _)

theorem dist_le_sqrt_of_dist_sq_le {X : Type*} [PseudoMetricSpace X]
    {x y : X} {R : ℝ} (hR : 0 ≤ R) (h : dist x y ^ 2 ≤ R) :
    dist x y ≤ Real.sqrt R :=
  (Real.le_sqrt dist_nonneg hR).2 h

theorem dist_eq_sqrt_of_dist_sq_eq {X : Type*} [PseudoMetricSpace X]
    {x y : X} {R : ℝ} (hR : 0 ≤ R) (h : dist x y ^ 2 = R) :
    dist x y = Real.sqrt R := by
  apply le_antisymm
  · exact dist_le_sqrt_of_dist_sq_le hR h.le
  · have hsq : Real.sqrt R ^ 2 ≤ dist x y ^ 2 := by rw [Real.sq_sqrt hR, h]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) dist_nonneg).mp hsq

theorem finite_diam_eq_of_forall_dist_le_of_exists_dist_eq
    {X : Type*} [PseudoMetricSpace X] (points : Finset X) {R : ℝ}
    (hR : 0 ≤ R)
    (hle : ∀ x ∈ points, ∀ y ∈ points, dist x y ≤ R)
    (hexists : ∃ x ∈ points, ∃ y ∈ points, dist x y = R) :
    Metric.diam (points : Set X) = R := by
  have hupper : Metric.diam (points : Set X) ≤ R :=
    Metric.diam_le_of_forall_dist_le hR (by simpa using hle)
  obtain ⟨x, hx, y, hy, hdist⟩ := hexists
  have hlower : R ≤ Metric.diam (points : Set X) := by
    rw [← hdist]
    exact Metric.dist_le_diam_of_mem (Finset.finite_toSet points).isBounded hx hy
  exact le_antisymm hupper hlower

theorem finReindexedDirectedCutPoint_dist_le_kahnKalai
    {α : Type*} [Fintype α] [DecidableEq α] {d p : ℕ}
    (coord : (α × α) ≃ Fin d) (A B : Finset α)
    (hground : Fintype.card α = 4 * p)
    (hA : A.card = 2 * p) (hB : B.card = 2 * p) :
    dist (finReindexedDirectedCutPoint coord A) (finReindexedDirectedCutPoint coord B) ≤
      Real.sqrt ((8 * p * p : ℕ) : ℝ) :=
  dist_le_sqrt_of_dist_sq_le (Nat.cast_nonneg _)
    (finReindexedDirectedCutPoint_dist_sq_le_kahnKalai coord A B hground hA hB)

theorem finReindexedDirectedCutPoint_dist_eq_sqrt_of_kahnKalai_intersection
    {α : Type*} [Fintype α] [DecidableEq α] {d p : ℕ}
    (coord : (α × α) ≃ Fin d) (A B : Finset α)
    (hground : Fintype.card α = 4 * p)
    (hA : A.card = 2 * p) (hB : B.card = 2 * p)
    (hinter : (A ∩ B).card = p) :
    dist (finReindexedDirectedCutPoint coord A) (finReindexedDirectedCutPoint coord B) =
      Real.sqrt ((8 * p * p : ℕ) : ℝ) :=
  dist_eq_sqrt_of_dist_sq_eq (Nat.cast_nonneg _)
    (finReindexedDirectedCutPoint_dist_sq_of_kahnKalai_intersection coord A B hground hA hB
      hinter)

theorem primeDirectedCutFamily_diam_eq_sqrt
    {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] {d p : ℕ}
    (coord : (α × α) ≃ Fin d) (sets : ι → Finset α)
    (hground : Fintype.card α = 4 * p)
    (hcard : ∀ i, (sets i).card = 2 * p)
    (hexists : ∃ i j, (sets i ∩ sets j).card = p) :
    Metric.diam
      ((Finset.univ.image (fun i => finReindexedDirectedCutPoint coord (sets i)) :
          Finset (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))) =
      Real.sqrt ((8 * p * p : ℕ) : ℝ) := by
  let points : Finset (EuclideanSpace ℝ (Fin d)) :=
    Finset.univ.image fun i => finReindexedDirectedCutPoint coord (sets i)
  refine finite_diam_eq_of_forall_dist_le_of_exists_dist_eq points (Real.sqrt_nonneg _) ?_ ?_
  · intro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨j, _hj, rfl⟩
    exact finReindexedDirectedCutPoint_dist_le_kahnKalai coord (sets i) (sets j) hground
      (hcard i) (hcard j)
  · obtain ⟨i, j, hij⟩ := hexists
    refine ⟨finReindexedDirectedCutPoint coord (sets i), ?_,
      finReindexedDirectedCutPoint coord (sets j), ?_, ?_⟩
    · simp [points]
    · simp [points]
    · exact finReindexedDirectedCutPoint_dist_eq_sqrt_of_kahnKalai_intersection coord
        (sets i) (sets j) hground (hcard i) (hcard j) hij

theorem primeDirectedCutFamily_diam_sq_eq
    {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] {d p : ℕ}
    (coord : (α × α) ≃ Fin d) (sets : ι → Finset α)
    (hground : Fintype.card α = 4 * p)
    (hcard : ∀ i, (sets i).card = 2 * p)
    (hexists : ∃ i j, (sets i ∩ sets j).card = p) :
    Metric.diam
      ((Finset.univ.image (fun i => finReindexedDirectedCutPoint coord (sets i)) :
          Finset (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))) ^ 2 =
        ((8 * p * p : ℕ) : ℝ) := by
  rw [primeDirectedCutFamily_diam_eq_sqrt coord sets hground hcard hexists,
    Real.sq_sqrt (Nat.cast_nonneg _)]

theorem finEmbeddedDirectedCutPoint_dist_le_kahnKalai
    {α : Type*} [Fintype α] [DecidableEq α] {d p : ℕ}
    (coord : (α × α) ↪ Fin d) (A B : Finset α)
    (hground : Fintype.card α = 4 * p)
    (hA : A.card = 2 * p) (hB : B.card = 2 * p) :
    dist (finEmbeddedDirectedCutPoint coord A) (finEmbeddedDirectedCutPoint coord B) ≤
      Real.sqrt ((8 * p * p : ℕ) : ℝ) :=
  dist_le_sqrt_of_dist_sq_le (Nat.cast_nonneg _)
    (finEmbeddedDirectedCutPoint_dist_sq_le_kahnKalai coord A B hground hA hB)

theorem finEmbeddedDirectedCutPoint_dist_eq_sqrt_of_kahnKalai_intersection
    {α : Type*} [Fintype α] [DecidableEq α] {d p : ℕ}
    (coord : (α × α) ↪ Fin d) (A B : Finset α)
    (hground : Fintype.card α = 4 * p)
    (hA : A.card = 2 * p) (hB : B.card = 2 * p)
    (hinter : (A ∩ B).card = p) :
    dist (finEmbeddedDirectedCutPoint coord A) (finEmbeddedDirectedCutPoint coord B) =
      Real.sqrt ((8 * p * p : ℕ) : ℝ) :=
  dist_eq_sqrt_of_dist_sq_eq (Nat.cast_nonneg _)
    (finEmbeddedDirectedCutPoint_dist_sq_of_kahnKalai_intersection coord A B hground hA hB
      hinter)

theorem primeDirectedCutFamilyEmbedding_diam_eq_sqrt
    {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] {d p : ℕ}
    (coord : (α × α) ↪ Fin d) (sets : ι → Finset α)
    (hground : Fintype.card α = 4 * p)
    (hcard : ∀ i, (sets i).card = 2 * p)
    (hexists : ∃ i j, (sets i ∩ sets j).card = p) :
    Metric.diam
      ((Finset.univ.image (fun i => finEmbeddedDirectedCutPoint coord (sets i)) :
          Finset (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))) =
      Real.sqrt ((8 * p * p : ℕ) : ℝ) := by
  let points : Finset (EuclideanSpace ℝ (Fin d)) :=
    Finset.univ.image fun i => finEmbeddedDirectedCutPoint coord (sets i)
  refine finite_diam_eq_of_forall_dist_le_of_exists_dist_eq points (Real.sqrt_nonneg _) ?_ ?_
  · intro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨j, _hj, rfl⟩
    exact finEmbeddedDirectedCutPoint_dist_le_kahnKalai coord (sets i) (sets j) hground
      (hcard i) (hcard j)
  · obtain ⟨i, j, hij⟩ := hexists
    refine ⟨finEmbeddedDirectedCutPoint coord (sets i), ?_,
      finEmbeddedDirectedCutPoint coord (sets j), ?_, ?_⟩
    · simp [points]
    · simp [points]
    · exact finEmbeddedDirectedCutPoint_dist_eq_sqrt_of_kahnKalai_intersection coord
        (sets i) (sets j) hground (hcard i) (hcard j) hij

theorem primeDirectedCutFamilyEmbedding_diam_sq_eq
    {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] {d p : ℕ}
    (coord : (α × α) ↪ Fin d) (sets : ι → Finset α)
    (hground : Fintype.card α = 4 * p)
    (hcard : ∀ i, (sets i).card = 2 * p)
    (hexists : ∃ i j, (sets i ∩ sets j).card = p) :
    Metric.diam
      ((Finset.univ.image (fun i => finEmbeddedDirectedCutPoint coord (sets i)) :
          Finset (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))) ^ 2 =
        ((8 * p * p : ℕ) : ℝ) := by
  rw [primeDirectedCutFamilyEmbedding_diam_eq_sqrt coord sets hground hcard hexists,
    Real.sq_sqrt]
  exact Nat.cast_nonneg _

theorem directedCutSet_realIncidencePoint_dist_sq
    {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) :
    dist (realIncidencePoint (directedCutSet A)) (realIncidencePoint (directedCutSet B)) ^ 2 =
      ((2 * finsetSymmDiffCard A B *
          (Fintype.card α - finsetSymmDiffCard A B) : ℕ) : ℝ) := by
  rw [realIncidencePoint_dist_sq, directedCutSet_symmDiffCard]

theorem directedCutSet_realIncidencePoint_dist_sq_of_kahnKalai_intersection
    {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) {k : ℕ}
    (hground : Fintype.card α = 4 * k)
    (hA : A.card = 2 * k) (hB : B.card = 2 * k)
    (hinter : (A ∩ B).card = k) :
    dist (realIncidencePoint (directedCutSet A)) (realIncidencePoint (directedCutSet B)) ^ 2 =
      ((8 * k * k : ℕ) : ℝ) := by
  rw [realIncidencePoint_dist_sq,
    directedCutSet_symmDiffCard_of_kahnKalai_intersection A B hground hA hB hinter]

theorem nat_eq_of_dvd_of_le_two_mul_of_ne_zero_of_ne_two_mul {p n : ℕ}
    (hp : 0 < p) (hdvd : p ∣ n) (hle : n ≤ 2 * p)
    (hn0 : n ≠ 0) (hn2 : n ≠ 2 * p) :
    n = p := by
  rcases hdvd with ⟨q, rfl⟩
  have hle' : p * q ≤ p * 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hle
  have hqle : q ≤ 2 := Nat.le_of_mul_le_mul_left hle' hp
  interval_cases q
  · exact (hn0 (by simp)).elim
  · simp
  · exact (hn2 (by ring)).elim

/--
For a prime modulus, a natural number in `[0,2p]` that is zero in `ZMod p`
is exactly `p` once the two degenerate endpoints are excluded.
-/
theorem nat_eq_of_zmod_eq_zero_of_le_two_mul_of_ne_zero_of_ne_two_mul {p n : ℕ}
    [Fact p.Prime] (hcast : (n : ZMod p) = 0) (hle : n ≤ 2 * p)
    (hn0 : n ≠ 0) (hn2 : n ≠ 2 * p) :
    n = p := by
  have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp hcast
  exact nat_eq_of_dvd_of_le_two_mul_of_ne_zero_of_ne_two_mul
    (Fact.out : Nat.Prime p).pos hdvd hle hn0 hn2

/--
Modular Frankl-Wilson gives intersection size `0` in `ZMod p`; for two
`2p`-subsets, excluding the empty and identical-intersection degeneracies
turns this into the exact Kahn-Kalai intersection size `p`.
-/
theorem card_inter_eq_prime_of_zmod_eq_zero_of_half_card_no_degenerate
    {p : ℕ} [Fact p.Prime] {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (hA : A.card = 2 * p)
    (hcast : (((A ∩ B).card : ZMod p) = 0))
    (hn0 : (A ∩ B).card ≠ 0) (hn2 : (A ∩ B).card ≠ 2 * p) :
    (A ∩ B).card = p := by
  have hleA : (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
  have hle : (A ∩ B).card ≤ 2 * p := by omega
  exact nat_eq_of_zmod_eq_zero_of_le_two_mul_of_ne_zero_of_ne_two_mul hcast hle hn0 hn2

theorem eq_of_inter_card_eq_left_card_of_card_eq {α : Type*} [DecidableEq α]
    {A B : Finset α} (hinter : (A ∩ B).card = A.card) (hcard : A.card = B.card) :
    A = B := by
  have hInterA : A ∩ B = A := by
    exact Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hsub : A ⊆ B := by
    intro a ha
    have : a ∈ A ∩ B := by simpa [hInterA]
    exact (Finset.mem_inter.mp this).2
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

theorem inter_card_ne_of_ne_of_card_eq {α : Type*} [DecidableEq α]
    {A B : Finset α} {r : ℕ} (hA : A.card = r) (hB : B.card = r) (hne : A ≠ B) :
    (A ∩ B).card ≠ r := by
  intro hInter
  exact hne (eq_of_inter_card_eq_left_card_of_card_eq (by omega) (by omega))

/--
Convenient exact-intersection form for an injective half-size family: after
modular Frankl-Wilson finds a zero residue, nonempty intersection and distinct
sets force the actual intersection size to be `p`.
-/
theorem card_inter_eq_prime_of_zmod_eq_zero_of_half_cards_of_nonzero_of_ne
    {p : ℕ} [Fact p.Prime] {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (hA : A.card = 2 * p) (hB : B.card = 2 * p)
    (hcast : (((A ∩ B).card : ZMod p) = 0))
    (hn0 : (A ∩ B).card ≠ 0) (hne : A ≠ B) :
    (A ∩ B).card = p := by
  refine card_inter_eq_prime_of_zmod_eq_zero_of_half_card_no_degenerate A B hA hcast hn0 ?_
  exact inter_card_ne_of_ne_of_card_eq hA hB hne

/--
Prime-modulus Frankl-Wilson, specialized to injective `2p`-uniform families:
if the family is larger than the low-degree bound times the number of colors,
then every coloring has a monochromatic pair with exact intersection size `p`.
The `hnonzero` hypothesis is the partition-level exclusion of complementary
representatives.
-/
theorem exists_monochromatic_pair_prime_intersection_eq
    {p : ℕ} [Fact p.Prime] {α ι κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (sets : ι → Finset α) (color : ι → κ)
    (hcard : ∀ i, (sets i).card = 2 * p)
    (hinj : Function.Injective sets)
    (hnonzero : ∀ i j, i ≠ j → (sets i ∩ sets j).card ≠ 0)
    (hlarge : Fintype.card κ *
        Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          Fintype.card ι) :
    ∃ i j, i ≠ j ∧ color i = color j ∧ (sets i ∩ sets j).card = p := by
  let L : Finset (ZMod p) := Finset.univ.erase 0
  have hself : ∀ i, ((sets i).card : ZMod p) ∉ L := by
    intro i
    rw [hcard i]
    simp [L]
  obtain ⟨i, j, hij, hsame, hbad⟩ :=
    exists_monochromatic_pair_intersection_notMem (sets := sets) (L := L) (color := color)
      hself (by simpa [L] using hlarge)
  have hcast : (((sets i ∩ sets j).card : ZMod p) = 0) := by
    simpa [L] using hbad
  have hinter : (sets i ∩ sets j).card = p :=
    card_inter_eq_prime_of_zmod_eq_zero_of_half_cards_of_nonzero_of_ne
      (sets i) (sets j) (hcard i) (hcard j) hcast (hnonzero i j hij) (hinj.ne hij)
  exact ⟨i, j, hij, hsame, hinter⟩

theorem exists_monochromatic_pair_directedCutSet_dist_sq_eq
    {p : ℕ} [Fact p.Prime] {α ι κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (sets : ι → Finset α) (color : ι → κ)
    (hground : Fintype.card α = 4 * p)
    (hcard : ∀ i, (sets i).card = 2 * p)
    (hinj : Function.Injective sets)
    (hnonzero : ∀ i j, i ≠ j → (sets i ∩ sets j).card ≠ 0)
    (hlarge : Fintype.card κ *
        Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          Fintype.card ι) :
    ∃ i j, i ≠ j ∧ color i = color j ∧
      dist (realIncidencePoint (directedCutSet (sets i)))
          (realIncidencePoint (directedCutSet (sets j))) ^ 2 = ((8 * p * p : ℕ) : ℝ) := by
  obtain ⟨i, j, hij, hsame, hinter⟩ :=
    exists_monochromatic_pair_prime_intersection_eq (sets := sets) (color := color)
      hcard hinj hnonzero hlarge
  exact ⟨i, j, hij, hsame,
    directedCutSet_realIncidencePoint_dist_sq_of_kahnKalai_intersection
      (sets i) (sets j) hground (hcard i) (hcard j) hinter⟩

theorem exists_prime_intersection_of_large
    {d p : ℕ} [Fact p.Prime] {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (sets : ι → Finset α)
    (hcard : ∀ i, (sets i).card = 2 * p)
    (hinj : Function.Injective sets)
    (hnonzero : ∀ i j, i ≠ j → (sets i ∩ sets j).card ≠ 0)
    (hlarge : (d + 1) *
        Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          Fintype.card ι) :
    ∃ i j, (sets i ∩ sets j).card = p := by
  let B := Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card}
  have hlarge1 : Fintype.card Unit * B < Fintype.card ι := by
    have hle : B ≤ (d + 1) * B := Nat.le_mul_of_pos_left B (Nat.succ_pos d)
    exact lt_of_le_of_lt (by simpa [B] using hle) (by simpa [B] using hlarge)
  obtain ⟨i, j, _hij, _hsame, hinter⟩ :=
    exists_monochromatic_pair_prime_intersection_eq (sets := sets)
      (color := fun _ => ()) hcard hinj hnonzero hlarge1
  exact ⟨i, j, hinter⟩

theorem dist_eq_of_dist_sq_eq_diam_sq {X : Type*} [PseudoMetricSpace X]
    {S : Set X} {x y : X} (h : dist x y ^ 2 = Metric.diam S ^ 2) :
    dist x y = Metric.diam S := by
  have habs : |dist x y| = |Metric.diam S| :=
    (sq_eq_sq_iff_abs_eq_abs _ _).mp h
  rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg Metric.diam_nonneg] at habs

theorem diam_pos_of_diam_sq_eq_pos {X : Type*} [PseudoMetricSpace X]
    {S : Set X} {r : ℝ} (h : Metric.diam S ^ 2 = r) (hr : 0 < r) :
    0 < Metric.diam S := by
  have hne : Metric.diam S ≠ 0 := by
    intro hzero
    have hr0 : r = 0 := by simpa [hzero] using h.symm
    exact (ne_of_gt hr) hr0
  exact lt_of_le_of_ne' Metric.diam_nonneg hne

/-- Borsuk's conjecture in dimension d: every bounded set with positive
diameter can be covered by d+1 subsets of itself, each of strictly smaller
diameter.  The subset condition is essential: in a noncompact proper space
`Metric.diam Set.univ = 0`, so allowing arbitrary covering sets would make the
formal statement spuriously true. -/
def BorsukConjecture (d : ℕ) : Prop :=
  ∀ (S : Set (EuclideanSpace ℝ (Fin d))),
    Bornology.IsBounded S → 0 < Metric.diam S →
    ∃ parts : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)),
      S ⊆ ⋃ i, parts i ∧
      (∀ i, parts i ⊆ S) ∧
      ∀ i, Metric.diam (parts i) < Metric.diam S

/--
A Kahn-Kalai certificate is a counterexample set in `ℝ^d` that is bounded,
has positive diameter, but cannot be covered by `d + 1` subsets of itself with
strictly smaller diameter.
-/
structure KahnKalaiCertificate (d : ℕ) where
  S : Set (EuclideanSpace ℝ (Fin d))
  bounded : Bornology.IsBounded S
  pos_diam : 0 < Metric.diam S
  no_partition : ¬ ∃ parts : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)),
    S ⊆ ⋃ i, parts i ∧
    (∀ i, parts i ⊆ S) ∧
    ∀ i, Metric.diam (parts i) < Metric.diam S

/--
A finite point configuration gives a Kahn-Kalai certificate once every
`(d + 1)`-coloring has a monochromatic pair at the full diameter of the
configuration.  This is the geometric interface needed after the
Frankl-Wilson set-system construction: the combinatorics only has to rule out
small-diameter color classes.
-/
def KahnKalaiCertificate.ofFiniteDiameterObstruction {d : ℕ}
    (points : Finset (EuclideanSpace ℝ (Fin d)))
    (hpos : 0 < Metric.diam (points : Set (EuclideanSpace ℝ (Fin d))))
    (hobstruction : ∀ color : EuclideanSpace ℝ (Fin d) → Fin (d + 1),
      ∃ x ∈ points, ∃ y ∈ points,
        color x = color y ∧ dist x y = Metric.diam (points : Set (EuclideanSpace ℝ (Fin d)))) :
    KahnKalaiCertificate d := by
  classical
  refine ⟨(points : Set (EuclideanSpace ℝ (Fin d))), (Finset.finite_toSet points).isBounded,
    hpos, ?_⟩
  rintro ⟨parts, hcover, hsub, hsmall⟩
  let color : EuclideanSpace ℝ (Fin d) → Fin (d + 1) := fun x =>
    if hx : x ∈ (points : Set (EuclideanSpace ℝ (Fin d))) then
      Classical.choose (Set.mem_iUnion.mp (hcover hx))
    else 0
  have hmem_part {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ points) :
      x ∈ parts (color x) := by
    have hxset : x ∈ (points : Set (EuclideanSpace ℝ (Fin d))) := by simpa using hx
    dsimp [color]
    simpa [hxset] using Classical.choose_spec (Set.mem_iUnion.mp (hcover hxset))
  obtain ⟨x, hx, y, hy, hsame, hdiam⟩ := hobstruction color
  have hxpart : x ∈ parts (color x) := hmem_part hx
  have hypart : y ∈ parts (color x) := by
    have hy' : y ∈ parts (color y) := hmem_part hy
    simpa [hsame] using hy'
  have hpart_bounded : Bornology.IsBounded (parts (color x)) :=
    (Finset.finite_toSet points).isBounded.subset (hsub (color x))
  have hle : dist x y ≤ Metric.diam (parts (color x)) :=
    Metric.dist_le_diam_of_mem hpart_bounded hxpart hypart
  rw [hdiam] at hle
  exact not_lt_of_ge hle (hsmall (color x))

/--
Squared-distance version of `ofFiniteDiameterObstruction`.  This is convenient
for incidence-vector constructions, where the natural formulas compute
distance squared as a Hamming count.
-/
def KahnKalaiCertificate.ofFiniteSquaredDiameterObstruction {d : ℕ}
    (points : Finset (EuclideanSpace ℝ (Fin d)))
    (hpos : 0 < Metric.diam (points : Set (EuclideanSpace ℝ (Fin d))))
    (hobstruction : ∀ color : EuclideanSpace ℝ (Fin d) → Fin (d + 1),
      ∃ x ∈ points, ∃ y ∈ points,
        color x = color y ∧
          dist x y ^ 2 = Metric.diam (points : Set (EuclideanSpace ℝ (Fin d))) ^ 2) :
    KahnKalaiCertificate d :=
  KahnKalaiCertificate.ofFiniteDiameterObstruction points hpos fun color => by
    obtain ⟨x, hx, y, hy, hsame, hsq⟩ := hobstruction color
    exact ⟨x, hx, y, hy, hsame, dist_eq_of_dist_sq_eq_diam_sq hsq⟩

/--
Prime Frankl-Wilson plus a squared-distance geometric realization gives a
Kahn-Kalai certificate.  This is the main reusable interface for the remaining
Kahn-Kalai construction: instantiate `pointOf` by the cut-incidence vectors and
prove their squared diameter.
-/
noncomputable def KahnKalaiCertificate.ofPrimeFranklWilsonSquaredConfiguration {d p : ℕ}
    [Fact p.Prime] {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (sets : ι → Finset α) (pointOf : ι → EuclideanSpace ℝ (Fin d))
    (hcard : ∀ i, (sets i).card = 2 * p)
    (hinj : Function.Injective sets)
    (hnonzero : ∀ i j, i ≠ j → (sets i ∩ sets j).card ≠ 0)
    (hlarge : (d + 1) *
        Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          Fintype.card ι)
    (hpos : 0 < Metric.diam
      ((Finset.univ.image pointOf : Finset (EuclideanSpace ℝ (Fin d))) :
        Set (EuclideanSpace ℝ (Fin d))))
    (hdistSq : ∀ i j, i ≠ j → (sets i ∩ sets j).card = p →
      dist (pointOf i) (pointOf j) ^ 2 = Metric.diam
        ((Finset.univ.image pointOf : Finset (EuclideanSpace ℝ (Fin d))) :
          Set (EuclideanSpace ℝ (Fin d))) ^ 2) :
    KahnKalaiCertificate d := by
  classical
  let points : Finset (EuclideanSpace ℝ (Fin d)) := Finset.univ.image pointOf
  refine KahnKalaiCertificate.ofFiniteSquaredDiameterObstruction points ?_ ?_
  · simpa [points] using hpos
  · intro color
    have hlarge' :
        Fintype.card (Fin (d + 1)) *
            Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          Fintype.card ι := by
      simpa [Fintype.card_fin] using hlarge
    obtain ⟨i, j, hij, hsame, hinter⟩ :=
      exists_monochromatic_pair_prime_intersection_eq (sets := sets)
        (color := fun i => color (pointOf i)) hcard hinj hnonzero hlarge'
    refine ⟨pointOf i, ?_, pointOf j, ?_, hsame, ?_⟩
    · simp [points]
    · simp [points]
    · simpa [points] using hdistSq i j hij hinter

/--
Certificate interface for the directed-cut version of the Kahn-Kalai
configuration.  The remaining geometric input is exactly the squared diameter
calculation for the finite cut-incidence point set.
-/
noncomputable def KahnKalaiCertificate.ofPrimeDirectedCutFamily {d p : ℕ}
    [Fact p.Prime] {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (coord : (α × α) ≃ Fin d) (sets : ι → Finset α)
    (hground : Fintype.card α = 4 * p)
    (hcard : ∀ i, (sets i).card = 2 * p)
    (hinj : Function.Injective sets)
    (hnonzero : ∀ i j, i ≠ j → (sets i ∩ sets j).card ≠ 0)
    (hlarge : (d + 1) *
        Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          Fintype.card ι)
    (hpos : 0 < Metric.diam
      ((Finset.univ.image (fun i => finReindexedDirectedCutPoint coord (sets i)) :
          Finset (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))))
    (hdiamSq : Metric.diam
      ((Finset.univ.image (fun i => finReindexedDirectedCutPoint coord (sets i)) :
          Finset (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))) ^ 2 =
        ((8 * p * p : ℕ) : ℝ)) :
    KahnKalaiCertificate d := by
  refine KahnKalaiCertificate.ofPrimeFranklWilsonSquaredConfiguration (sets := sets)
    (pointOf := fun i => finReindexedDirectedCutPoint coord (sets i))
    hcard hinj hnonzero hlarge hpos ?_
  intro i j _hij hinter
  rw [finReindexedDirectedCutPoint_dist_sq_of_kahnKalai_intersection coord (sets i) (sets j)
    hground (hcard i) (hcard j) hinter, ← hdiamSq]

/--
Same as `ofPrimeDirectedCutFamily`, with positivity of the diameter derived
from the squared-diameter calculation.
-/
noncomputable def KahnKalaiCertificate.ofPrimeDirectedCutFamilyOfDiameterSq {d p : ℕ}
    [Fact p.Prime] {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (coord : (α × α) ≃ Fin d) (sets : ι → Finset α)
    (hground : Fintype.card α = 4 * p)
    (hcard : ∀ i, (sets i).card = 2 * p)
    (hinj : Function.Injective sets)
    (hnonzero : ∀ i j, i ≠ j → (sets i ∩ sets j).card ≠ 0)
    (hlarge : (d + 1) *
        Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          Fintype.card ι)
    (hdiamSq : Metric.diam
      ((Finset.univ.image (fun i => finReindexedDirectedCutPoint coord (sets i)) :
          Finset (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))) ^ 2 =
        ((8 * p * p : ℕ) : ℝ)) :
    KahnKalaiCertificate d := by
  have hsq_pos : (0 : ℝ) < ((8 * p * p : ℕ) : ℝ) := by
    have hp : 0 < p := (Fact.out : Nat.Prime p).pos
    positivity
  refine KahnKalaiCertificate.ofPrimeDirectedCutFamily coord sets hground hcard hinj hnonzero
    hlarge ?_ hdiamSq
  exact diam_pos_of_diam_sq_eq_pos hdiamSq hsq_pos

/--
Directed-cut certificate with the diameter calculation supplied by the
existence of one critical pair.
-/
noncomputable def KahnKalaiCertificate.ofPrimeDirectedCutFamilyOfCriticalPair {d p : ℕ}
    [Fact p.Prime] {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (coord : (α × α) ≃ Fin d) (sets : ι → Finset α)
    (hground : Fintype.card α = 4 * p)
    (hcard : ∀ i, (sets i).card = 2 * p)
    (hinj : Function.Injective sets)
    (hnonzero : ∀ i j, i ≠ j → (sets i ∩ sets j).card ≠ 0)
    (hlarge : (d + 1) *
        Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          Fintype.card ι)
    (hexists : ∃ i j, (sets i ∩ sets j).card = p) :
    KahnKalaiCertificate d := by
  refine KahnKalaiCertificate.ofPrimeDirectedCutFamilyOfDiameterSq coord sets hground hcard hinj
    hnonzero hlarge ?_
  exact primeDirectedCutFamily_diam_sq_eq coord sets hground hcard hexists

/--
Directed-cut certificate where Frankl-Wilson supplies both the monochromatic
critical pair and the pair witnessing the diameter.
-/
noncomputable def KahnKalaiCertificate.ofPrimeDirectedCutFamilyOfLarge {d p : ℕ}
    [Fact p.Prime] {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (coord : (α × α) ≃ Fin d) (sets : ι → Finset α)
    (hground : Fintype.card α = 4 * p)
    (hcard : ∀ i, (sets i).card = 2 * p)
    (hinj : Function.Injective sets)
    (hnonzero : ∀ i j, i ≠ j → (sets i ∩ sets j).card ≠ 0)
    (hlarge : (d + 1) *
        Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          Fintype.card ι) :
    KahnKalaiCertificate d :=
  KahnKalaiCertificate.ofPrimeDirectedCutFamilyOfCriticalPair coord sets hground hcard hinj
    hnonzero hlarge (exists_prime_intersection_of_large (d := d) sets hcard hinj hnonzero hlarge)

/--
Embedding-coordinate version of `ofPrimeDirectedCutFamily`.  This is used to
place the same cut-incidence configuration in any larger ambient dimension.
-/
noncomputable def KahnKalaiCertificate.ofPrimeDirectedCutFamilyEmbedding {d p : ℕ}
    [Fact p.Prime] {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (coord : (α × α) ↪ Fin d) (sets : ι → Finset α)
    (hground : Fintype.card α = 4 * p)
    (hcard : ∀ i, (sets i).card = 2 * p)
    (hinj : Function.Injective sets)
    (hnonzero : ∀ i j, i ≠ j → (sets i ∩ sets j).card ≠ 0)
    (hlarge : (d + 1) *
        Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          Fintype.card ι)
    (hpos : 0 < Metric.diam
      ((Finset.univ.image (fun i => finEmbeddedDirectedCutPoint coord (sets i)) :
          Finset (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))))
    (hdiamSq : Metric.diam
      ((Finset.univ.image (fun i => finEmbeddedDirectedCutPoint coord (sets i)) :
          Finset (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))) ^ 2 =
        ((8 * p * p : ℕ) : ℝ)) :
    KahnKalaiCertificate d := by
  refine KahnKalaiCertificate.ofPrimeFranklWilsonSquaredConfiguration (sets := sets)
    (pointOf := fun i => finEmbeddedDirectedCutPoint coord (sets i))
    hcard hinj hnonzero hlarge hpos ?_
  intro i j _hij hinter
  rw [finEmbeddedDirectedCutPoint_dist_sq_of_kahnKalai_intersection coord (sets i) (sets j)
    hground (hcard i) (hcard j) hinter, ← hdiamSq]

/--
Embedding-coordinate directed-cut certificate with positivity derived from the
squared-diameter calculation.
-/
noncomputable def KahnKalaiCertificate.ofPrimeDirectedCutFamilyEmbeddingOfDiameterSq
    {d p : ℕ} [Fact p.Prime] {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (coord : (α × α) ↪ Fin d) (sets : ι → Finset α)
    (hground : Fintype.card α = 4 * p)
    (hcard : ∀ i, (sets i).card = 2 * p)
    (hinj : Function.Injective sets)
    (hnonzero : ∀ i j, i ≠ j → (sets i ∩ sets j).card ≠ 0)
    (hlarge : (d + 1) *
        Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          Fintype.card ι)
    (hdiamSq : Metric.diam
      ((Finset.univ.image (fun i => finEmbeddedDirectedCutPoint coord (sets i)) :
          Finset (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))) ^ 2 =
        ((8 * p * p : ℕ) : ℝ)) :
    KahnKalaiCertificate d := by
  have hsq_pos : (0 : ℝ) < ((8 * p * p : ℕ) : ℝ) := by
    have hp : 0 < p := (Fact.out : Nat.Prime p).pos
    positivity
  refine KahnKalaiCertificate.ofPrimeDirectedCutFamilyEmbedding coord sets hground hcard hinj
    hnonzero hlarge ?_ hdiamSq
  exact diam_pos_of_diam_sq_eq_pos hdiamSq hsq_pos

/-- Embedding-coordinate directed-cut certificate supplied by one critical pair. -/
noncomputable def KahnKalaiCertificate.ofPrimeDirectedCutFamilyEmbeddingOfCriticalPair
    {d p : ℕ} [Fact p.Prime] {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (coord : (α × α) ↪ Fin d) (sets : ι → Finset α)
    (hground : Fintype.card α = 4 * p)
    (hcard : ∀ i, (sets i).card = 2 * p)
    (hinj : Function.Injective sets)
    (hnonzero : ∀ i j, i ≠ j → (sets i ∩ sets j).card ≠ 0)
    (hlarge : (d + 1) *
        Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          Fintype.card ι)
    (hexists : ∃ i j, (sets i ∩ sets j).card = p) :
    KahnKalaiCertificate d := by
  refine KahnKalaiCertificate.ofPrimeDirectedCutFamilyEmbeddingOfDiameterSq coord sets hground
    hcard hinj hnonzero hlarge ?_
  exact primeDirectedCutFamilyEmbedding_diam_sq_eq coord sets hground hcard hexists

/--
Embedding-coordinate directed-cut certificate where Frankl-Wilson supplies both
the monochromatic critical pair and the diameter-witnessing pair.
-/
noncomputable def KahnKalaiCertificate.ofPrimeDirectedCutFamilyEmbeddingOfLarge
    {d p : ℕ} [Fact p.Prime] {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (coord : (α × α) ↪ Fin d) (sets : ι → Finset α)
    (hground : Fintype.card α = 4 * p)
    (hcard : ∀ i, (sets i).card = 2 * p)
    (hinj : Function.Injective sets)
    (hnonzero : ∀ i j, i ≠ j → (sets i ∩ sets j).card ≠ 0)
    (hlarge : (d + 1) *
        Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          Fintype.card ι) :
    KahnKalaiCertificate d :=
  KahnKalaiCertificate.ofPrimeDirectedCutFamilyEmbeddingOfCriticalPair coord sets hground hcard hinj
    hnonzero hlarge (exists_prime_intersection_of_large (d := d) sets hcard hinj hnonzero hlarge)

/--
The pointed half-size family used in the Kahn-Kalai construction: all
`2p`-subsets of the ground set that contain a fixed base point.  Pointedness
rules out the zero-intersection degeneracy needed by the directed-cut bridge.
-/
abbrev pointedHalfSubsets (α : Type*) [Fintype α] [DecidableEq α] (p : ℕ) (base : α) :
    Type _ :=
  {A : Finset α // A.card = 2 * p ∧ base ∈ A}

/--
Erase the distinguished base point from a pointed half-size set.  This is the
basic counting bijection for the pointed Kahn-Kalai family.
-/
noncomputable def pointedHalfSubsetsEraseEquiv {α : Type*} [Fintype α] [DecidableEq α]
    {p : ℕ} (base : α) (hp : 0 < p) :
    pointedHalfSubsets α p base ≃
      {B : Finset α // B ∈ (Finset.univ.erase base).powersetCard (2 * p - 1)} where
  toFun A := by
    refine ⟨A.1.erase base, ?_⟩
    rw [Finset.mem_powersetCard]
    constructor
    · intro x hx
      rw [Finset.mem_erase] at hx ⊢
      exact ⟨hx.1, Finset.mem_univ x⟩
    · rw [Finset.card_erase_of_mem A.2.2, A.2.1]
  invFun B := by
    refine ⟨insert base B.1, ?_⟩
    have hB := Finset.mem_powersetCard.mp B.2
    have hnot : base ∉ B.1 := by
      intro hb
      have hbErase : base ∈ Finset.univ.erase base := hB.1 hb
      exact (Finset.mem_erase.mp hbErase).1 rfl
    constructor
    · rw [Finset.card_insert_of_notMem hnot, hB.2]
      omega
    · simp
  left_inv A := by
    exact Subtype.ext (Finset.insert_erase A.2.2)
  right_inv B := by
    apply Subtype.ext
    have hB := Finset.mem_powersetCard.mp B.2
    have hnot : base ∉ B.1 := by
      intro hb
      have hbErase : base ∈ Finset.univ.erase base := hB.1 hb
      exact (Finset.mem_erase.mp hbErase).1 rfl
    exact Finset.erase_insert hnot

/-- The pointed half-size family has binomial size. -/
theorem pointedHalfSubsets_card {α : Type*} [Fintype α] [DecidableEq α]
    {p : ℕ} (base : α) (hp : 0 < p) :
    Fintype.card (pointedHalfSubsets α p base) =
      (Fintype.card α - 1).choose (2 * p - 1) := by
  rw [Fintype.card_congr (pointedHalfSubsetsEraseEquiv (α := α) base hp)]
  rw [Fintype.card_subtype]
  have hset :
      ({x | x ∈ (Finset.univ.erase base).powersetCard (2 * p - 1)} :
        Finset (Finset α)) =
        (Finset.univ.erase base).powersetCard (2 * p - 1) := by
    ext B
    simp
  rw [hset, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ base),
    Finset.card_univ]

/-- Pointed half-size family count after substituting a `4p`-element ground set. -/
theorem pointedHalfSubsets_card_of_ground {α : Type*} [Fintype α] [DecidableEq α]
    {p : ℕ} (base : α) (hp : 0 < p) (hground : Fintype.card α = 4 * p) :
    Fintype.card (pointedHalfSubsets α p base) = (4 * p - 1).choose (2 * p - 1) := by
  rw [pointedHalfSubsets_card base hp, hground]

/-- The nonzero residue classes modulo a prime `p` have cardinality `p - 1`. -/
theorem zmod_nonzero_card (p : ℕ) [Fact p.Prime] :
    (Finset.univ.erase (0 : ZMod p)).card = p - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)), Finset.card_univ,
    ZMod.card p]

/-- Count all subsets of a finite type whose cardinality is at most `r`. -/
theorem smallSubsets_card_eq_sum_choose {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ) :
    Fintype.card {I : Finset α // I.card ≤ r} =
      ∑ k ∈ Finset.range (r + 1), (Fintype.card α).choose k := by
  rw [Fintype.card_subtype]
  have hset :
      ({I | I.card ≤ r} : Finset (Finset α)) =
        (Finset.range (r + 1)).biUnion fun k =>
          (Finset.univ : Finset α).powersetCard k := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard]
    constructor
    · intro hI
      exact ⟨I.card, Nat.lt_succ_of_le hI, fun x _ => Finset.mem_univ x, rfl⟩
    · rintro ⟨k, hk, _hsub, hcard⟩
      rw [hcard]
      exact Nat.le_of_lt_succ hk
  rw [hset]
  have hdisj :
      ((Finset.range (r + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (fun k => (Finset.univ : Finset α).powersetCard k) := by
    intro i _hi j _hj hij
    exact (Finset.univ : Finset α).pairwise_disjoint_powersetCard hij
  rw [Finset.card_biUnion hdisj]
  simp [Finset.card_powersetCard]

/--
Directed-cut certificate specialized to the pointed half-size family.  The
remaining Kahn-Kalai arithmetic is the lower bound on this family size against
the Frankl-Wilson low-degree bound.
-/
noncomputable def KahnKalaiCertificate.ofPrimePointedHalfFamilyOfLarge {d p : ℕ}
    [Fact p.Prime] {α : Type*} [Fintype α] [DecidableEq α]
    (base : α) (coord : (α × α) ≃ Fin d)
    (hground : Fintype.card α = 4 * p)
    (hlarge : (d + 1) *
        Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          Fintype.card (pointedHalfSubsets α p base)) :
    KahnKalaiCertificate d := by
  let sets : pointedHalfSubsets α p base → Finset α := fun A => A.1
  have hcard : ∀ A, (sets A).card = 2 * p := fun A => A.2.1
  have hinj : Function.Injective sets := by
    intro A B h
    exact Subtype.ext h
  have hnonzero : ∀ A B, A ≠ B → (sets A ∩ sets B).card ≠ 0 := by
    intro A B _hne hzero
    have hbase : base ∈ sets A ∩ sets B := by
      simp [sets, A.2.2, B.2.2]
    have hpos : 0 < (sets A ∩ sets B).card := Finset.card_pos.mpr ⟨base, hbase⟩
    omega
  exact KahnKalaiCertificate.ofPrimeDirectedCutFamilyOfLarge coord sets hground hcard hinj
    hnonzero hlarge

/--
Binomial-count version of `ofPrimePointedHalfFamilyOfLarge` after substituting
the `4p` ground-set size.
-/
noncomputable def KahnKalaiCertificate.ofPrimePointedHalfFamilyOfChooseLarge {d p : ℕ}
    [Fact p.Prime] {α : Type*} [Fintype α] [DecidableEq α]
    (base : α) (coord : (α × α) ≃ Fin d)
    (hground : Fintype.card α = 4 * p)
    (hlarge : (d + 1) *
        Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          (4 * p - 1).choose (2 * p - 1)) :
    KahnKalaiCertificate d := by
  refine KahnKalaiCertificate.ofPrimePointedHalfFamilyOfLarge base coord hground ?_
  rw [pointedHalfSubsets_card_of_ground base (Fact.out : Nat.Prime p).pos hground]
  exact hlarge

/--
Numeric low-degree-bound version of the pointed Kahn-Kalai certificate, using
`|ZMod p \ {0}| = p - 1`.
-/
noncomputable def KahnKalaiCertificate.ofPrimePointedHalfFamilyOfNumericLarge {d p : ℕ}
    [Fact p.Prime] {α : Type*} [Fintype α] [DecidableEq α]
    (base : α) (coord : (α × α) ≃ Fin d)
    (hground : Fintype.card α = 4 * p)
    (hlarge : (d + 1) * Fintype.card {I : Finset α // I.card ≤ p - 1} <
          (4 * p - 1).choose (2 * p - 1)) :
    KahnKalaiCertificate d := by
  refine KahnKalaiCertificate.ofPrimePointedHalfFamilyOfChooseLarge base coord hground ?_
  simpa [zmod_nonzero_card p] using hlarge

/--
Sum-of-binomial version of the pointed Kahn-Kalai certificate.  This is the
finite arithmetic shape left after the Frankl-Wilson linear-algebra argument.
-/
noncomputable def KahnKalaiCertificate.ofPrimePointedHalfFamilyOfSumLarge {d p : ℕ}
    [Fact p.Prime] {α : Type*} [Fintype α] [DecidableEq α]
    (base : α) (coord : (α × α) ≃ Fin d)
    (hground : Fintype.card α = 4 * p)
    (hlarge : (d + 1) * (∑ k ∈ Finset.range p, (4 * p).choose k) <
          (4 * p - 1).choose (2 * p - 1)) :
    KahnKalaiCertificate d := by
  refine KahnKalaiCertificate.ofPrimePointedHalfFamilyOfNumericLarge base coord hground ?_
  rw [smallSubsets_card_eq_sum_choose (α := α) (r := p - 1), hground]
  have hp1 : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
  rw [Nat.sub_add_cancel hp1]
  exact hlarge

/--
Concrete `Fin (4p)` instance of the pointed Kahn-Kalai bridge.  The only
remaining input is a pure binomial inequality.
-/
noncomputable def KahnKalaiCertificate.ofPrimePointedFinFamilyOfSumLarge {p : ℕ}
    [Fact p.Prime]
    (hlarge : (((4 * p) * (4 * p)) + 1) *
        (∑ k ∈ Finset.range p, (4 * p).choose k) <
          (4 * p - 1).choose (2 * p - 1)) :
    KahnKalaiCertificate ((4 * p) * (4 * p)) := by
  let base : Fin (4 * p) := ⟨0, by
    have hp : 0 < p := (Fact.out : Nat.Prime p).pos
    omega⟩
  refine KahnKalaiCertificate.ofPrimePointedHalfFamilyOfSumLarge (p := p) base
    (coord := finProdFinEquiv) ?_ hlarge
  simp [Fintype.card_fin]

/-- Embedding-coordinate version of `ofPrimePointedHalfFamilyOfLarge`. -/
noncomputable def KahnKalaiCertificate.ofPrimePointedHalfFamilyEmbeddingOfLarge {d p : ℕ}
    [Fact p.Prime] {α : Type*} [Fintype α] [DecidableEq α]
    (base : α) (coord : (α × α) ↪ Fin d)
    (hground : Fintype.card α = 4 * p)
    (hlarge : (d + 1) *
        Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          Fintype.card (pointedHalfSubsets α p base)) :
    KahnKalaiCertificate d := by
  let sets : pointedHalfSubsets α p base → Finset α := fun A => A.1
  have hcard : ∀ A, (sets A).card = 2 * p := fun A => A.2.1
  have hinj : Function.Injective sets := by
    intro A B h
    exact Subtype.ext h
  have hnonzero : ∀ A B, A ≠ B → (sets A ∩ sets B).card ≠ 0 := by
    intro A B _hne hzero
    have hbase : base ∈ sets A ∩ sets B := by
      simp [sets, A.2.2, B.2.2]
    have hpos : 0 < (sets A ∩ sets B).card := Finset.card_pos.mpr ⟨base, hbase⟩
    omega
  exact KahnKalaiCertificate.ofPrimeDirectedCutFamilyEmbeddingOfLarge coord sets hground hcard
    hinj hnonzero hlarge

/-- Binomial-count embedding-coordinate pointed certificate. -/
noncomputable def KahnKalaiCertificate.ofPrimePointedHalfFamilyEmbeddingOfChooseLarge
    {d p : ℕ} [Fact p.Prime] {α : Type*} [Fintype α] [DecidableEq α]
    (base : α) (coord : (α × α) ↪ Fin d)
    (hground : Fintype.card α = 4 * p)
    (hlarge : (d + 1) *
        Fintype.card {I : Finset α // I.card ≤ (Finset.univ.erase (0 : ZMod p)).card} <
          (4 * p - 1).choose (2 * p - 1)) :
    KahnKalaiCertificate d := by
  refine KahnKalaiCertificate.ofPrimePointedHalfFamilyEmbeddingOfLarge base coord hground ?_
  rw [pointedHalfSubsets_card_of_ground base (Fact.out : Nat.Prime p).pos hground]
  exact hlarge

/-- Numeric low-degree-bound embedding-coordinate pointed certificate. -/
noncomputable def KahnKalaiCertificate.ofPrimePointedHalfFamilyEmbeddingOfNumericLarge
    {d p : ℕ} [Fact p.Prime] {α : Type*} [Fintype α] [DecidableEq α]
    (base : α) (coord : (α × α) ↪ Fin d)
    (hground : Fintype.card α = 4 * p)
    (hlarge : (d + 1) * Fintype.card {I : Finset α // I.card ≤ p - 1} <
          (4 * p - 1).choose (2 * p - 1)) :
    KahnKalaiCertificate d := by
  refine KahnKalaiCertificate.ofPrimePointedHalfFamilyEmbeddingOfChooseLarge base coord hground ?_
  simpa [zmod_nonzero_card p] using hlarge

/--
Sum-of-binomial embedding-coordinate pointed certificate.  This is the useful
high-dimensional interface: the `d + 1` color count is explicit.
-/
noncomputable def KahnKalaiCertificate.ofPrimePointedHalfFamilyEmbeddingOfSumLarge
    {d p : ℕ} [Fact p.Prime] {α : Type*} [Fintype α] [DecidableEq α]
    (base : α) (coord : (α × α) ↪ Fin d)
    (hground : Fintype.card α = 4 * p)
    (hlarge : (d + 1) * (∑ k ∈ Finset.range p, (4 * p).choose k) <
          (4 * p - 1).choose (2 * p - 1)) :
    KahnKalaiCertificate d := by
  refine KahnKalaiCertificate.ofPrimePointedHalfFamilyEmbeddingOfNumericLarge base coord hground ?_
  rw [smallSubsets_card_eq_sum_choose (α := α) (r := p - 1), hground]
  have hp1 : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
  rw [Nat.sub_add_cancel hp1]
  exact hlarge

/--
Concrete finite-coordinate embedding version.  It constructs the coordinate
embedding from `(4p)^2 ≤ d`; the remaining hypothesis is pure arithmetic.
-/
noncomputable def KahnKalaiCertificate.ofPrimePointedFinFamilyEmbeddingOfSumLarge
    {d p : ℕ} [Fact p.Prime]
    (hdim : (4 * p) * (4 * p) ≤ d)
    (hlarge : (d + 1) * (∑ k ∈ Finset.range p, (4 * p).choose k) <
          (4 * p - 1).choose (2 * p - 1)) :
    KahnKalaiCertificate d := by
  let base : Fin (4 * p) := ⟨0, by
    have hp : 0 < p := (Fact.out : Nat.Prime p).pos
    omega⟩
  let coord : (Fin (4 * p) × Fin (4 * p)) ↪ Fin d :=
    finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb hdim)
  refine KahnKalaiCertificate.ofPrimePointedHalfFamilyEmbeddingOfSumLarge (p := p) base coord
    ?_ hlarge
  simp [Fintype.card_fin]

/-- The concrete binomial inequality needed for the `p = 17` pointed construction. -/
theorem kahnKalai_numeric_17 :
    (((4 * 17) * (4 * 17)) + 1) *
        (∑ k ∈ Finset.range 17, (4 * 17).choose k) <
          (4 * 17 - 1).choose (2 * 17 - 1) := by
  norm_num [Finset.sum_range_succ, Nat.choose_succ_succ]

/-- A fully constructed Kahn-Kalai certificate in dimension `4624`. -/
noncomputable def kahnKalaiCertificate_4624 : KahnKalaiCertificate 4624 := by
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  simpa using KahnKalaiCertificate.ofPrimePointedFinFamilyOfSumLarge (p := 17)
    kahnKalai_numeric_17

/-- The `p = 17` pointed construction remains large enough through dimension `6848`. -/
theorem kahnKalai_numeric_17_6848 :
    (6848 + 1) * (∑ k ∈ Finset.range 17, (4 * 17).choose k) <
      (4 * 17 - 1).choose (2 * 17 - 1) := by
  norm_num [Finset.sum_range_succ, Nat.choose_succ_succ]

theorem kahnKalai_numeric_17_of_le {d : ℕ} (hd : d ≤ 6848) :
    (d + 1) * (∑ k ∈ Finset.range 17, (4 * 17).choose k) <
      (4 * 17 - 1).choose (2 * 17 - 1) := by
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.succ_le_succ hd))
    kahnKalai_numeric_17_6848

/-- Kahn-Kalai certificates in the full range covered by the `p = 17` inequality. -/
noncomputable def kahnKalaiCertificate_of_dim_between_4624_6848 {d : ℕ}
    (hlo : 4624 ≤ d) (hhi : d ≤ 6848) : KahnKalaiCertificate d := by
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  refine KahnKalaiCertificate.ofPrimePointedFinFamilyEmbeddingOfSumLarge (p := 17) ?_ ?_
  · norm_num
    exact hlo
  · exact kahnKalai_numeric_17_of_le hhi

/--
Bridge from the Frankl-Wilson coloring obstruction to a Borsuk counterexample
certificate.  A concrete Kahn-Kalai construction can use this once it supplies
the Euclidean point map and proves that the forbidden intersection pairs are
exactly full-diameter pairs.
-/
noncomputable def KahnKalaiCertificate.ofFranklWilsonPointConfiguration {d : ℕ}
    {K α ι : Type*} [Field K] [Fintype α] [DecidableEq α] [DecidableEq K] [Fintype ι]
    (sets : ι → Finset α) (L : Finset K)
    (pointOf : ι → EuclideanSpace ℝ (Fin d))
    (hself : ∀ i, ((sets i).card : K) ∉ L)
    (hlarge : (d + 1) * Fintype.card {I : Finset α // I.card ≤ L.card} < Fintype.card ι)
    (hpos : 0 < Metric.diam
      ((Finset.univ.image pointOf : Finset (EuclideanSpace ℝ (Fin d))) :
        Set (EuclideanSpace ℝ (Fin d))))
    (hdist : ∀ i j, i ≠ j → (((sets i ∩ sets j).card : K) ∉ L) →
      dist (pointOf i) (pointOf j) = Metric.diam
        ((Finset.univ.image pointOf : Finset (EuclideanSpace ℝ (Fin d))) :
          Set (EuclideanSpace ℝ (Fin d)))) :
    KahnKalaiCertificate d := by
  classical
  let points : Finset (EuclideanSpace ℝ (Fin d)) := Finset.univ.image pointOf
  refine KahnKalaiCertificate.ofFiniteDiameterObstruction points ?_ ?_
  · simpa [points] using hpos
  · intro color
    have hlarge' :
        Fintype.card (Fin (d + 1)) *
            Fintype.card {I : Finset α // I.card ≤ L.card} < Fintype.card ι := by
      simpa [Fintype.card_fin] using hlarge
    obtain ⟨i, j, hij, hsame, hbad⟩ :=
      exists_monochromatic_pair_intersection_notMem (sets := sets) (L := L)
        (color := fun i => color (pointOf i)) hself hlarge'
    refine ⟨pointOf i, ?_, pointOf j, ?_, hsame, ?_⟩
    · simp [points]
    · simp [points]
    · simpa [points] using hdist i j hij hbad

/-- The finite diameter obstruction immediately gives failure of Borsuk's conjecture. -/
theorem not_borsukConjecture_of_finite_diameter_obstruction {d : ℕ}
    (points : Finset (EuclideanSpace ℝ (Fin d)))
    (hpos : 0 < Metric.diam (points : Set (EuclideanSpace ℝ (Fin d))))
    (hobstruction : ∀ color : EuclideanSpace ℝ (Fin d) → Fin (d + 1),
      ∃ x ∈ points, ∃ y ∈ points,
        color x = color y ∧ dist x y = Metric.diam (points : Set (EuclideanSpace ℝ (Fin d)))) :
    ¬ BorsukConjecture d := by
  intro h
  exact (KahnKalaiCertificate.ofFiniteDiameterObstruction points hpos hobstruction).no_partition
    (h _ (Finset.finite_toSet points).isBounded hpos)

/--
A Kahn-Kalai certificate gives failure of Borsuk's conjecture in that dimension.
-/
theorem not_borsukConjecture_of_certificate {d : ℕ} (cert : KahnKalaiCertificate d) :
    ¬ BorsukConjecture d := fun h =>
  cert.no_partition (h cert.S cert.bounded cert.pos_diam)

/-- Unconditional Borsuk counterexample obtained from the local Kahn-Kalai pipeline. -/
theorem not_borsukConjecture_4624 : ¬ BorsukConjecture 4624 :=
  not_borsukConjecture_of_certificate kahnKalaiCertificate_4624

/-- Unconditional Borsuk counterexamples in the range covered by `p = 17`. -/
theorem not_borsukConjecture_of_dim_between_4624_6848 {d : ℕ}
    (hlo : 4624 ≤ d) (hhi : d ≤ 6848) : ¬ BorsukConjecture d :=
  not_borsukConjecture_of_certificate
    (kahnKalaiCertificate_of_dim_between_4624_6848 hlo hhi)

/--
Chapter 16: Borsuk's conjecture is false in some finite dimension.

The local formalization gives the explicit witness `d = 4624`.
-/
theorem chapter16 : ∃ d : ℕ, ¬ BorsukConjecture d :=
  ⟨4624, not_borsukConjecture_4624⟩

/-- Borsuk's conjecture in dimension `d` unfolded as its finite-dimensional statement. -/
theorem borsukConjecture_iff_no_certificate (d : ℕ) :
    BorsukConjecture d ↔ ∀ S : Set (EuclideanSpace ℝ (Fin d)),
      Bornology.IsBounded S → 0 < Metric.diam S →
        ∃ parts : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)),
          S ⊆ ⋃ i, parts i ∧
          (∀ i, parts i ⊆ S) ∧
          ∀ i, Metric.diam (parts i) < Metric.diam S :=
  Iff.rfl

/-- If a Kahn-Kalai certificate exists, the underlying set is nonempty
(since `0 < diam S` forces `S` to contain at least two points). -/
theorem KahnKalaiCertificate.nonempty {d : ℕ} (cert : KahnKalaiCertificate d) :
    cert.S.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hd : Metric.diam cert.S = 0 := by rw [h]; simp
  exact absurd cert.pos_diam (by rw [hd]; simp)

/-- Conversely, if Borsuk's conjecture holds in dimension `d`, no
Kahn-Kalai certificate exists. -/
theorem borsuk_no_certificate_of_conjecture {d : ℕ} (h : BorsukConjecture d) :
    IsEmpty (KahnKalaiCertificate d) := by
  constructor
  intro cert
  exact cert.no_partition (h cert.S cert.bounded cert.pos_diam)

/-- Borsuk's conjecture holds vacuously in dimension `0`: in `ℝ⁰` all subsets
have zero diameter, so the hypothesis `0 < Metric.diam S` is never satisfied. -/
theorem borsukConjecture_zero : BorsukConjecture 0 := by
  intro S _ hdiam
  -- In `EuclideanSpace ℝ (Fin 0)`, all points equal (there's only one).
  -- So `diam S ≤ 0`, contradicting `hdiam`.
  have h_diam_zero : Metric.diam S = 0 := by
    rcases S.eq_empty_or_nonempty with hS | ⟨x, _⟩
    · rw [hS]; simp
    · -- Subsingleton: every two points in S are equal (since EuclideanSpace ℝ (Fin 0) is).
      have hsub : S.Subsingleton := fun a _ b _ => Subsingleton.elim a b
      exact Metric.diam_subsingleton hsub
  rw [h_diam_zero] at hdiam
  exact absurd hdiam (lt_irrefl _)

/-- No Kahn-Kalai certificate exists in dimension 0 (since Borsuk's conjecture
holds vacuously there). -/
theorem KahnKalaiCertificate.isEmpty_zero : IsEmpty (KahnKalaiCertificate 0) :=
  borsuk_no_certificate_of_conjecture borsukConjecture_zero

/-- A Kahn-Kalai certificate's set contains at least one point.  This is a weaker
form of `nonempty`, packaged for direct membership-style use. -/
theorem KahnKalaiCertificate.exists_mem {d : ℕ} (cert : KahnKalaiCertificate d) :
    ∃ x, x ∈ cert.S :=
  cert.nonempty

/-- Borsuk's conjecture in dimension `d` is closed under the contrapositive: it
fails iff a Kahn-Kalai certificate exists. -/
theorem not_borsukConjecture_iff_exists_certificate (d : ℕ) :
    ¬ BorsukConjecture d ↔ Nonempty (KahnKalaiCertificate d) := by
  constructor
  · intro hfail
    -- ¬ BorsukConjecture d unfolds to a ∃-style negated statement; classical extraction.
    classical
    by_contra hno
    rw [not_nonempty_iff] at hno
    apply hfail
    intro S hbd hpos
    by_contra hno_part
    exact hno.elim ⟨S, hbd, hpos, hno_part⟩
  · rintro ⟨cert⟩ hyp
    exact not_borsukConjecture_of_certificate cert hyp

end ProofsInTheBook.Chapter16
