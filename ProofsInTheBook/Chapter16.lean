import Mathlib

/-!
# Chapter 16: Borsuk's conjecture

From "Proofs from THE BOOK":

**Borsuk's conjecture**: Can every bounded set in ℝ^d be partitioned
into d+1 parts, each of smaller diameter? Borsuk conjectured yes (1933).

The book discusses the conjecture and its eventual disproof (for d ≥ 298)
by Kahn and Kalai (1993) using combinatorial arguments.

Formalization status: this file closes the certificate layer for Borsuk's
conjecture.  It defines finite color-class bookkeeping, states the corrected
`BorsukConjecture d` for covers of a bounded set by subsets of itself in
`EuclideanSpace ℝ (Fin d)`, packages a counterexample as
`KahnKalaiCertificate d`, proves `chapter16` from such a certificate, and
proves the dimension-zero sanity check.

Gap to the full book theorem: the missing upstream mathematics is the actual
Kahn-Kalai construction.  A complete proof needs the Frankl-Wilson modular
intersection theorem in the finite-set form used by Kahn and Kalai, the
translation from the resulting set system to a finite Euclidean point
configuration, the exact diameter and smaller-diameter color-class estimates,
and the dimension bookkeeping giving a counterexample in the advertised high
dimensions.  Mathlib has Euclidean metric spaces and finite-set tools, but not
this Frankl-Wilson/Kahn-Kalai pipeline as an available theorem.

Mathlib search status (2026-05-24): no Frankl-Wilson theorem, modular
intersection theorem, Ray-Chaudhuri-Wilson theorem, or oddtown/eventown theorem
was present under those names or nearby combinatorial names.  The local
additions below therefore stop at the reusable diagonal-functional linear
independence core, its mod-2 oddtown specialization, and the finite geometric
obstruction bridge to `KahnKalaiCertificate`.
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
Chapter 16 (Borsuk's conjecture in high dimensions, Tier 1 conditional):
Given a Kahn-Kalai-style counterexample — a bounded set with positive diameter
in ℝ^d that cannot be covered by d+1 subsets of itself with strictly smaller
diameter — Borsuk's conjecture fails in dimension d.

TODO (Tier 2): Construct the actual Kahn-Kalai counterexample for `d ≥ 298`
via Frankl-Wilson combinatorics on hypergraph color codes to produce a
`KahnKalaiCertificate d`.
-/
theorem chapter16 {d : ℕ} (cert : KahnKalaiCertificate d) :
    ¬ BorsukConjecture d := fun h =>
  cert.no_partition (h cert.S cert.bounded cert.pos_diam)

/-- Borsuk's conjecture in dimension `d` is equivalent to the non-existence
of a Kahn-Kalai certificate.  This packages `chapter16` as a biconditional. -/
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
    exact chapter16 cert hyp

end ProofsInTheBook.Chapter16
