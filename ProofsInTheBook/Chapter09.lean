import Mathlib

/-!
# Chapter 9: Hilbert's third problem

From "Proofs from THE BOOK":

**Hilbert's third problem**: A regular tetrahedron cannot be cut into finitely
many polyhedral pieces and reassembled into a cube (scissors congruence fails).

The book proves this via the **Dehn invariant**: for a polyhedron P,
  D(P) = ∑_{edges e} length(e) ⊗ θ(e) ∈ ℝ ⊗_ℤ (ℝ/πℚ)
where θ(e) is the dihedral angle at edge e. Scissors-congruent polyhedra
have equal Dehn invariants. The cube has D = 0, while the regular
tetrahedron has D ≠ 0 (since arccos(1/3) is irrational over π).

Formalization status: this file closes the algebraic obstruction layer.  It
defines finite Dehn-invariant sums, the angle quotient by rational multiples
of `π`, proves that cube-like right angles vanish in that quotient, proves
`Real.arccos (1 / 3)` is not a rational multiple of `π`, and packages the
final contradiction as `chapter09` / `hilbert_third_problem` once the cube
and tetrahedron Dehn values are supplied.

Gap to the full book theorem: Mathlib does not currently provide the required
three-dimensional scissors-congruence geometry.  A complete proof still needs
a robust Euclidean polyhedron type with faces, edges, lengths, and dihedral
angles; concrete cube and regular tetrahedron models; a geometric Dehn
invariant for those polyhedra; additivity under actual finite dissections and
rigid reassembly; and the nonzero tensor-sum computation for the regular
tetrahedron's six equal edge contributions.
-/

namespace ProofsInTheBook.Chapter09

open scoped BigOperators TensorProduct
open Polynomial Chebyshev

/-!
### Dehn invariant

The key algebraic invariant. Its construction requires:
1. The tensor product ℝ ⊗[ℤ] (ℝ / πℚ)
2. Showing D is additive under dissection
3. Computing D for specific polyhedra

This is a deep geometric result requiring substantial infrastructure
beyond current Mathlib coverage.
-/

/-!
### Current Mathlib geometry coverage

The local Mathlib checkout has the raw Euclidean tools needed for coordinate
calculations in `EuclideanSpace ℝ (Fin 3)`: finite-dimensional inner product
spaces, `Affine.Simplex`, equilateral simplex lemmas, convex hulls/convex sets,
orthogonal projection, signed distance to affine subspaces, and unoriented
angles.  It does not currently expose a bundled three-dimensional polyhedron
API with faces, edges, incidence, dihedral angles, geometric Dehn invariant, or
finite scissors dissections/reassemblies.  The coordinate lemmas below are
therefore deliberately local: they verify the regular tetrahedron model and the
`1 / 3` dihedral cosine calculation, but they are not yet connected to a
global polyhedron/dissection type.
-/

/-- Algebraic target for a Dehn invariant with an abstract angle quotient. -/
abbrev DehnTarget (Angle : Type*) [AddCommGroup Angle] [Module ℤ Angle] :=
  TensorProduct ℤ ℝ Angle

/-- Rational-vector-space target for the classical Dehn invariant. -/
abbrev DehnQTarget (Angle : Type*) [AddCommGroup Angle] [Module ℚ Angle] :=
  TensorProduct ℚ ℝ Angle

/-- Integer multiples of `π`, used as a first algebraic angle quotient. -/
noncomputable def piZSubmodule : Submodule ℤ ℝ :=
  Submodule.span ℤ ({Real.pi} : Set ℝ)

/-- Real angles modulo integer multiples of `π`. -/
abbrev AngleModPiZ :=
  ℝ ⧸ piZSubmodule

/-- Concrete algebraic target `ℝ ⊗[ℤ] (ℝ / πℤ)`. -/
abbrev DehnPiTarget :=
  DehnTarget AngleModPiZ

noncomputable def angleClass (x : ℝ) : AngleModPiZ :=
  Submodule.Quotient.mk x

@[simp]
theorem angleClass_pi : angleClass Real.pi = 0 := by
  exact (Submodule.Quotient.mk_eq_zero piZSubmodule).mpr (Submodule.subset_span (by simp))

/-! ### Rational multiples of `π` quotient (Tier 2 building block)

The Dehn-invariant proof of Hilbert's third problem requires the *rational*
multiples of `π` to be quotiented out, not just integer multiples.  E.g., the
cube's dihedral angle `π/2` is *not* an integer multiple of `π` but *is* a
rational multiple, so it must vanish in the angle target.  The integer
submodule `piZSubmodule` is too coarse — we need `piQSubmodule := ℚ • π`.
-/

/-- Rational multiples of `π`. -/
noncomputable def piQSubmodule : Submodule ℚ ℝ :=
  Submodule.span ℚ ({Real.pi} : Set ℝ)

/-- Real angles modulo rational multiples of `π`. -/
abbrev AngleModPiQ : Type :=
  ℝ ⧸ piQSubmodule

/-- Concrete rational target `ℝ ⊗[ℚ] (ℝ / πℚ)`. -/
abbrev DehnPiQTarget :=
  DehnQTarget AngleModPiQ

/-- The `ℝ ⧸ πℚ` projection. -/
noncomputable def angleClassQ (x : ℝ) : AngleModPiQ :=
  Submodule.Quotient.mk x

@[simp]
theorem angleClassQ_pi : angleClassQ Real.pi = 0 := by
  exact (Submodule.Quotient.mk_eq_zero piQSubmodule).mpr (Submodule.subset_span (by simp))

/-- Any rational multiple of `π` vanishes in the `πℚ` quotient. -/
theorem angleClassQ_rat_mul_pi (q : ℚ) : angleClassQ ((q : ℝ) * Real.pi) = 0 := by
  refine (Submodule.Quotient.mk_eq_zero piQSubmodule).mpr ?_
  rw [show ((q : ℝ) * Real.pi) = q • Real.pi from by
    rw [Rat.smul_def]]
  exact Submodule.smul_mem _ q (Submodule.subset_span (by simp))

/-- The cube's dihedral angle `π/2` is rational over `π`, so it vanishes. -/
@[simp]
theorem angleClassQ_pi_div_two : angleClassQ (Real.pi / 2) = 0 := by
  have h : Real.pi / 2 = ((1/2 : ℚ) : ℝ) * Real.pi := by push_cast; ring
  rw [h, angleClassQ_rat_mul_pi]

/-- Any divisor `π / n` with `0 < n` vanishes in the πℚ quotient. -/
theorem angleClassQ_pi_div (n : ℕ) (_hn : 0 < n) : angleClassQ (Real.pi / n) = 0 := by
  have h : Real.pi / n = ((1/n : ℚ) : ℝ) * Real.pi := by
    push_cast
    rw [div_mul_eq_mul_div, one_mul]
  rw [h, angleClassQ_rat_mul_pi]

/-- Any integer multiple of `π` vanishes in the πℚ quotient
(special case of `angleClassQ_rat_mul_pi` for integer `q`). -/
theorem angleClassQ_int_mul_pi (n : ℤ) :
    angleClassQ ((n : ℝ) * Real.pi) = 0 := by
  have h : (n : ℝ) * Real.pi = ((n : ℚ) : ℝ) * Real.pi := by push_cast; ring
  rw [h, angleClassQ_rat_mul_pi]

/-- `angleClassQ` is additive. -/
@[simp]
theorem angleClassQ_add (x y : ℝ) :
    angleClassQ (x + y) = angleClassQ x + angleClassQ y := rfl

/-- `angleClassQ` of zero is zero. -/
@[simp]
theorem angleClassQ_zero : angleClassQ 0 = 0 := rfl

/-- `angleClassQ` of a negation is the negation in the quotient. -/
@[simp]
theorem angleClassQ_neg (x : ℝ) : angleClassQ (-x) = -(angleClassQ x) := rfl

/-- `angleClassQ` commutes with finite sums. -/
theorem angleClassQ_sum {I : Type*} (s : Finset I) (angle : I → ℝ) :
    angleClassQ (∑ i ∈ s, angle i) = ∑ i ∈ s, angleClassQ (angle i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert, ha, ih]

/--
If the raw angles around an internal dissection edge add to a rational multiple
of `π`, their classes vanish in `ℝ / πℚ`.
-/
theorem angleClassQ_sum_eq_zero_of_sum_rat_mul_pi {I : Type*}
    (s : Finset I) (angle : I → ℝ) {q : ℚ}
    (h : (∑ i ∈ s, angle i) = (q : ℝ) * Real.pi) :
    (∑ i ∈ s, angleClassQ (angle i)) = 0 := by
  rw [← angleClassQ_sum, h, angleClassQ_rat_mul_pi]

/-- `angleClassQ x = 0` iff `x` is a rational multiple of `π`. -/
theorem angleClassQ_eq_zero_iff (x : ℝ) :
    angleClassQ x = 0 ↔ ∃ q : ℚ, x = (q : ℝ) * Real.pi := by
  rw [angleClassQ, Submodule.Quotient.mk_eq_zero, piQSubmodule,
      Submodule.mem_span_singleton]
  constructor
  · rintro ⟨q, hq⟩; exact ⟨q, by rw [← hq, Rat.smul_def]⟩
  · rintro ⟨q, hq⟩; exact ⟨q, by rw [hq, Rat.smul_def]⟩

/-- `angleClassQ` of a difference of two rational multiples of `π` is zero. -/
theorem angleClassQ_sub_rat_mul_pi (q r : ℚ) :
    angleClassQ ((q : ℝ) * Real.pi - (r : ℝ) * Real.pi) = 0 := by
  rw [show (q : ℝ) * Real.pi - (r : ℝ) * Real.pi = ((q - r : ℚ) : ℝ) * Real.pi from by
    push_cast; ring]
  exact angleClassQ_rat_mul_pi (q - r)

-- (`angleClassQ_arccos_one_third_ne_zero` defined below, after
-- `arccos_one_third_irrational_over_pi`.)

/-- The contribution of one edge: length tensor angle. -/
def dehnEdge {Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (length : ℝ) (angle : Angle) : DehnTarget Angle :=
  TensorProduct.tmul ℤ length angle

/-- One edge contribution in the classical rational tensor target. -/
noncomputable def dehnEdgeQ {Angle : Type*} [AddCommGroup Angle] [Module ℚ Angle]
    (length : ℝ) (angle : Angle) : DehnQTarget Angle :=
  TensorProduct.tmul ℚ length angle

@[simp]
theorem dehnEdge_zero_length {Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (angle : Angle) : dehnEdge 0 angle = 0 := by
  simp [dehnEdge]

@[simp]
theorem dehnEdge_zero_angle {Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (length : ℝ) : dehnEdge length (0 : Angle) = 0 := by
  simp [dehnEdge]

theorem dehnEdge_add_length {Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (length₁ length₂ : ℝ) (angle : Angle) :
    dehnEdge (length₁ + length₂) angle =
      dehnEdge length₁ angle + dehnEdge length₂ angle := by
  simp [dehnEdge, TensorProduct.add_tmul]

theorem dehnEdge_add_angle {Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (length : ℝ) (angle₁ angle₂ : Angle) :
    dehnEdge length (angle₁ + angle₂) =
      dehnEdge length angle₁ + dehnEdge length angle₂ := by
  simp [dehnEdge, TensorProduct.tmul_add]

/-- Splitting one geometric edge into finitely many angle pieces is additive. -/
theorem dehnEdge_angle_sum {I Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (s : Finset I) (length : ℝ) (angle : I → Angle) :
    dehnEdge length (∑ i ∈ s, angle i) =
      ∑ i ∈ s, dehnEdge length (angle i) := by
  simp [dehnEdge, TensorProduct.tmul_sum]

/-- Rational-target version of `dehnEdge_angle_sum`. -/
theorem dehnEdgeQ_angle_sum {I Angle : Type*} [AddCommGroup Angle] [Module ℚ Angle]
    (s : Finset I) (length : ℝ) (angle : I → Angle) :
    dehnEdgeQ length (∑ i ∈ s, angle i) =
      ∑ i ∈ s, dehnEdgeQ length (angle i) := by
  simp [dehnEdgeQ, TensorProduct.tmul_sum]

/-- Rational-target additivity over subdivisions of one edge length. -/
theorem dehnEdgeQ_length_sum {I Angle : Type*} [AddCommGroup Angle] [Module ℚ Angle]
    (s : Finset I) (length : I → ℝ) (angle : Angle) :
    dehnEdgeQ (∑ i ∈ s, length i) angle =
      ∑ i ∈ s, dehnEdgeQ (length i) angle := by
  simp [dehnEdgeQ, TensorProduct.sum_tmul]

/--
The algebraic cancellation used for an internal edge of a dissection: if the
incident angles add to a rational multiple of `π`, the total edge contribution
is zero in the angle quotient.
-/
theorem dehnEdge_angleClassQ_sum_eq_zero_of_sum_rat_mul_pi {I : Type*}
    (s : Finset I) (length : ℝ) (angle : I → ℝ) {q : ℚ}
    (h : (∑ i ∈ s, angle i) = (q : ℝ) * Real.pi) :
    (∑ i ∈ s, dehnEdge length (angleClassQ (angle i))) = 0 := by
  rw [← dehnEdge_angle_sum, angleClassQ_sum_eq_zero_of_sum_rat_mul_pi s angle h]
  simp

/--
Rational-target version of the algebraic cancellation used for an internal edge
of a dissection.
-/
theorem dehnEdgeQ_angleClassQ_sum_eq_zero_of_sum_rat_mul_pi {I : Type*}
    (s : Finset I) (length : ℝ) (angle : I → ℝ) {q : ℚ}
    (h : (∑ i ∈ s, angle i) = (q : ℝ) * Real.pi) :
    (∑ i ∈ s, dehnEdgeQ length (angleClassQ (angle i))) = 0 := by
  rw [← dehnEdgeQ_angle_sum, angleClassQ_sum_eq_zero_of_sum_rat_mul_pi s angle h]
  simp [dehnEdgeQ]

/-- Finite edge-sum model for the Dehn invariant. -/
def dehnInvariant {Edge Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (edges : Finset Edge) (length : Edge → ℝ) (angle : Edge → Angle) :
    DehnTarget Angle :=
  ∑ e ∈ edges, dehnEdge (length e) (angle e)

/-- Finite edge-sum model in the rational tensor target. -/
noncomputable def dehnInvariantQ {Edge Angle : Type*} [AddCommGroup Angle] [Module ℚ Angle]
    (edges : Finset Edge) (length : Edge → ℝ) (angle : Edge → Angle) :
    DehnQTarget Angle :=
  ∑ e ∈ edges, dehnEdgeQ (length e) (angle e)

@[simp]
theorem dehnInvariantQ_empty {Edge Angle : Type*} [AddCommGroup Angle] [Module ℚ Angle]
    (length : Edge → ℝ) (angle : Edge → Angle) :
    dehnInvariantQ (∅ : Finset Edge) length angle = 0 := by
  simp [dehnInvariantQ]

@[simp]
theorem dehnInvariant_empty {Edge Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (length : Edge → ℝ) (angle : Edge → Angle) :
    dehnInvariant (∅ : Finset Edge) length angle = 0 := by
  simp [dehnInvariant]

theorem dehnInvariant_insert {Edge Angle : Type*} [DecidableEq Edge]
    [AddCommGroup Angle] [Module ℤ Angle] {edges : Finset Edge} {e : Edge}
    (he : e ∉ edges) (length : Edge → ℝ) (angle : Edge → Angle) :
    dehnInvariant (insert e edges) length angle =
      dehnEdge (length e) (angle e) + dehnInvariant edges length angle := by
  simp [dehnInvariant, he]

theorem dehnInvariant_union_of_disjoint {Edge Angle : Type*} [DecidableEq Edge]
    [AddCommGroup Angle] [Module ℤ Angle] {left right : Finset Edge}
    (hdisj : Disjoint left right) (length : Edge → ℝ) (angle : Edge → Angle) :
    dehnInvariant (left ∪ right) length angle =
      dehnInvariant left length angle + dehnInvariant right length angle := by
  simp [dehnInvariant, Finset.sum_union hdisj]

theorem dehnInvariant_biUnion_of_pairwiseDisjoint {Piece Edge Angle : Type*}
    [DecidableEq Edge] [AddCommGroup Angle] [Module ℤ Angle]
    {pieces : Finset Piece} {edges : Piece → Finset Edge}
    (hdisj : Set.PairwiseDisjoint (↑pieces) edges)
    (length : Edge → ℝ) (angle : Edge → Angle) :
    dehnInvariant (pieces.biUnion edges) length angle =
      ∑ p ∈ pieces, dehnInvariant (edges p) length angle := by
  simp [dehnInvariant, Finset.sum_biUnion hdisj]

theorem dehnInvariantQ_union_of_disjoint {Edge Angle : Type*} [DecidableEq Edge]
    [AddCommGroup Angle] [Module ℚ Angle] {left right : Finset Edge}
    (hdisj : Disjoint left right) (length : Edge → ℝ) (angle : Edge → Angle) :
    dehnInvariantQ (left ∪ right) length angle =
      dehnInvariantQ left length angle + dehnInvariantQ right length angle := by
  simp [dehnInvariantQ, Finset.sum_union hdisj]

theorem dehnInvariantQ_biUnion_of_pairwiseDisjoint {Piece Edge Angle : Type*}
    [DecidableEq Edge] [AddCommGroup Angle] [Module ℚ Angle]
    {pieces : Finset Piece} {edges : Piece → Finset Edge}
    (hdisj : Set.PairwiseDisjoint (↑pieces) edges)
    (length : Edge → ℝ) (angle : Edge → Angle) :
    dehnInvariantQ (pieces.biUnion edges) length angle =
      ∑ p ∈ pieces, dehnInvariantQ (edges p) length angle := by
  simp [dehnInvariantQ, Finset.sum_biUnion hdisj]

/-- If every edge has the same angle, the invariant is one tensor with total length. -/
theorem dehnInvariant_const_angle {Edge Angle : Type*}
    [AddCommGroup Angle] [Module ℤ Angle]
    (edges : Finset Edge) (length : Edge → ℝ) (angle : Angle) :
    dehnInvariant edges length (fun _ => angle) =
      dehnEdge (∑ e ∈ edges, length e) angle := by
  simp [dehnInvariant, dehnEdge, TensorProduct.sum_tmul]

/-- If every edge has the same length and angle, only the edge count remains. -/
theorem dehnInvariant_const_length_angle {Edge Angle : Type*}
    [AddCommGroup Angle] [Module ℤ Angle]
    (edges : Finset Edge) (length : ℝ) (angle : Angle) :
    dehnInvariant edges (fun _ => length) (fun _ => angle) =
      dehnEdge ((edges.card : ℝ) * length) angle := by
  rw [dehnInvariant_const_angle]
  congr 1
  simp [nsmul_eq_mul]

/-- Rational-target version of `dehnInvariant_const_angle`. -/
theorem dehnInvariantQ_const_angle {Edge Angle : Type*}
    [AddCommGroup Angle] [Module ℚ Angle]
    (edges : Finset Edge) (length : Edge → ℝ) (angle : Angle) :
    dehnInvariantQ edges length (fun _ => angle) =
      dehnEdgeQ (∑ e ∈ edges, length e) angle := by
  simp [dehnInvariantQ, dehnEdgeQ, TensorProduct.sum_tmul]

/-- Rational-target version of `dehnInvariant_const_length_angle`. -/
theorem dehnInvariantQ_const_length_angle {Edge Angle : Type*}
    [AddCommGroup Angle] [Module ℚ Angle]
    (edges : Finset Edge) (length : ℝ) (angle : Angle) :
    dehnInvariantQ edges (fun _ => length) (fun _ => angle) =
      dehnEdgeQ ((edges.card : ℝ) * length) angle := by
  rw [dehnInvariantQ_const_angle]
  congr 1
  simp [nsmul_eq_mul]

theorem dehnInvariantQ_six_equal_edges {Angle : Type*}
    [AddCommGroup Angle] [Module ℚ Angle] (length : ℝ) (angle : Angle) :
    dehnInvariantQ (Finset.univ : Finset (Fin 6)) (fun _ => length) (fun _ => angle) =
      dehnEdgeQ (6 * length) angle := by
  rw [dehnInvariantQ_const_length_angle]
  norm_num

theorem dehnInvariantQ_eq_zero_of_angles_zero {Edge Angle : Type*}
    [AddCommGroup Angle] [Module ℚ Angle]
    (edges : Finset Edge) (length : Edge → ℝ) (angle : Edge → Angle)
    (hangle : ∀ e ∈ edges, angle e = 0) :
    dehnInvariantQ edges length angle = 0 := by
  unfold dehnInvariantQ
  apply Finset.sum_eq_zero
  intro e he
  unfold dehnEdgeQ
  rw [hangle e he, TensorProduct.tmul_zero]

/--
Boundary edge subdivision algebra: if each boundary edge has been cut into
fragments whose lengths add back to the original boundary length, then the
fragment Dehn contributions regroup to the boundary Dehn invariant.
-/
theorem boundaryDehnContributionQ_eq_dehnInvariantQ {BoundaryEdge Fragment : Type*}
    (boundaryEdges : Finset BoundaryEdge) (fragments : BoundaryEdge → Finset Fragment)
    (boundaryLength : BoundaryEdge → ℝ)
    (fragmentLength : BoundaryEdge → Fragment → ℝ)
    (boundaryAngle : BoundaryEdge → ℝ)
    (hlength : ∀ e ∈ boundaryEdges,
      (∑ f ∈ fragments e, fragmentLength e f) = boundaryLength e) :
    (∑ e ∈ boundaryEdges, ∑ f ∈ fragments e,
      dehnEdgeQ (fragmentLength e f) (angleClassQ (boundaryAngle e))) =
      dehnInvariantQ boundaryEdges boundaryLength (fun e => angleClassQ (boundaryAngle e)) := by
  rw [dehnInvariantQ]
  apply Finset.sum_congr rfl
  intro e he
  rw [← dehnEdgeQ_length_sum (fragments e) (fragmentLength e)
    (angleClassQ (boundaryAngle e)), hlength e he]

/--
Algebraic skeleton for the geometric additivity proof: after grouping all
piece-edge contributions by an internal geometric edge, the whole internal
part vanishes if each grouped angle sum is a rational multiple of `π`.
-/
theorem internalDehnContributionQ_eq_zero {InternalEdge Incident : Type*}
    (internalEdges : Finset InternalEdge) (incident : InternalEdge → Finset Incident)
    (length : InternalEdge → ℝ) (angle : InternalEdge → Incident → ℝ)
    (q : InternalEdge → ℚ)
    (hangle : ∀ e ∈ internalEdges,
      (∑ i ∈ incident e, angle e i) = (q e : ℝ) * Real.pi) :
    (∑ e ∈ internalEdges, ∑ i ∈ incident e,
      dehnEdgeQ (length e) (angleClassQ (angle e i))) = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  exact dehnEdgeQ_angleClassQ_sum_eq_zero_of_sum_rat_mul_pi (incident e) (length e)
    (angle e) (hangle e he)

/--
Boundary plus grouped internal contributions reduces to the boundary part.
The geometric work still needed is to supply the `incident` relation and the
angle-sum hypotheses from an actual polyhedral dissection.
-/
theorem boundary_add_internalDehnContributionQ {InternalEdge Incident : Type*}
    (boundary : DehnPiQTarget) (internalEdges : Finset InternalEdge)
    (incident : InternalEdge → Finset Incident) (length : InternalEdge → ℝ)
    (angle : InternalEdge → Incident → ℝ) (q : InternalEdge → ℚ)
    (hangle : ∀ e ∈ internalEdges,
      (∑ i ∈ incident e, angle e i) = (q e : ℝ) * Real.pi) :
    boundary + (∑ e ∈ internalEdges, ∑ i ∈ incident e,
      dehnEdgeQ (length e) (angleClassQ (angle e i))) = boundary := by
  rw [internalDehnContributionQ_eq_zero internalEdges incident length angle q hangle, add_zero]

/--
A more explicit algebraic interface for geometric Dehn additivity.  It models
two operations that an actual polyhedral dissection proof must justify:
boundary edges may be subdivided by the cut, and internal edge contributions
are grouped by the geometric edge they lie on.
-/
structure DehnGeometricAdditivitySkeletonQ
    (BoundaryEdge BoundaryFragment InternalEdge Incident : Type*) where
  pieceDehnSum : DehnPiQTarget
  boundaryEdges : Finset BoundaryEdge
  boundaryFragments : BoundaryEdge → Finset BoundaryFragment
  boundaryLength : BoundaryEdge → ℝ
  boundaryFragmentLength : BoundaryEdge → BoundaryFragment → ℝ
  boundaryAngle : BoundaryEdge → ℝ
  internalEdges : Finset InternalEdge
  incident : InternalEdge → Finset Incident
  internalLength : InternalEdge → ℝ
  internalAngle : InternalEdge → Incident → ℝ
  internalAngleMultiple : InternalEdge → ℚ
  piece_sum_eq_boundary_fragments_add_internal :
    pieceDehnSum =
      (∑ e ∈ boundaryEdges, ∑ f ∈ boundaryFragments e,
        dehnEdgeQ (boundaryFragmentLength e f) (angleClassQ (boundaryAngle e))) +
      ∑ e ∈ internalEdges, ∑ i ∈ incident e,
        dehnEdgeQ (internalLength e) (angleClassQ (internalAngle e i))
  boundary_length_sum : ∀ e ∈ boundaryEdges,
    (∑ f ∈ boundaryFragments e, boundaryFragmentLength e f) = boundaryLength e
  internal_angle_sum : ∀ e ∈ internalEdges,
    (∑ i ∈ incident e, internalAngle e i) =
      (internalAngleMultiple e : ℝ) * Real.pi

theorem DehnGeometricAdditivitySkeletonQ.piece_sum_eq_boundaryDehn
    {BoundaryEdge BoundaryFragment InternalEdge Incident : Type*}
    (cert :
      DehnGeometricAdditivitySkeletonQ BoundaryEdge BoundaryFragment InternalEdge Incident) :
    cert.pieceDehnSum =
      dehnInvariantQ cert.boundaryEdges cert.boundaryLength
        (fun e => angleClassQ (cert.boundaryAngle e)) := by
  calc
    cert.pieceDehnSum =
        (∑ e ∈ cert.boundaryEdges, ∑ f ∈ cert.boundaryFragments e,
          dehnEdgeQ (cert.boundaryFragmentLength e f) (angleClassQ (cert.boundaryAngle e))) +
        ∑ e ∈ cert.internalEdges, ∑ i ∈ cert.incident e,
          dehnEdgeQ (cert.internalLength e) (angleClassQ (cert.internalAngle e i)) :=
      cert.piece_sum_eq_boundary_fragments_add_internal
    _ = (∑ e ∈ cert.boundaryEdges, ∑ f ∈ cert.boundaryFragments e,
          dehnEdgeQ (cert.boundaryFragmentLength e f) (angleClassQ (cert.boundaryAngle e))) := by
      rw [internalDehnContributionQ_eq_zero cert.internalEdges cert.incident
        cert.internalLength cert.internalAngle cert.internalAngleMultiple cert.internal_angle_sum,
        add_zero]
    _ = dehnInvariantQ cert.boundaryEdges cert.boundaryLength
        (fun e => angleClassQ (cert.boundaryAngle e)) :=
      boundaryDehnContributionQ_eq_dehnInvariantQ cert.boundaryEdges cert.boundaryFragments
        cert.boundaryLength cert.boundaryFragmentLength cert.boundaryAngle
        cert.boundary_length_sum

theorem boundaryDehn_eq_of_same_pieceDehnSum_geometricAdditivitySkeletonQ
    {BoundaryEdge₁ BoundaryFragment₁ InternalEdge₁ Incident₁
      BoundaryEdge₂ BoundaryFragment₂ InternalEdge₂ Incident₂ : Type*}
    (left :
      DehnGeometricAdditivitySkeletonQ
        BoundaryEdge₁ BoundaryFragment₁ InternalEdge₁ Incident₁)
    (right :
      DehnGeometricAdditivitySkeletonQ
        BoundaryEdge₂ BoundaryFragment₂ InternalEdge₂ Incident₂)
    (hsum : left.pieceDehnSum = right.pieceDehnSum) :
    dehnInvariantQ left.boundaryEdges left.boundaryLength
        (fun e => angleClassQ (left.boundaryAngle e)) =
      dehnInvariantQ right.boundaryEdges right.boundaryLength
        (fun e => angleClassQ (right.boundaryAngle e)) := by
  rw [← left.piece_sum_eq_boundaryDehn, ← right.piece_sum_eq_boundaryDehn]
  exact hsum

theorem no_same_pieceDehnSum_geometricAdditivitySkeletonQ_of_dehn_ne
    {BoundaryEdge₁ BoundaryFragment₁ InternalEdge₁ Incident₁
      BoundaryEdge₂ BoundaryFragment₂ InternalEdge₂ Incident₂ : Type*}
    (left :
      DehnGeometricAdditivitySkeletonQ
        BoundaryEdge₁ BoundaryFragment₁ InternalEdge₁ Incident₁)
    (right :
      DehnGeometricAdditivitySkeletonQ
        BoundaryEdge₂ BoundaryFragment₂ InternalEdge₂ Incident₂)
    (hleft :
      dehnInvariantQ left.boundaryEdges left.boundaryLength
          (fun e => angleClassQ (left.boundaryAngle e)) = 0)
    (hright :
      dehnInvariantQ right.boundaryEdges right.boundaryLength
          (fun e => angleClassQ (right.boundaryAngle e)) ≠ 0) :
    left.pieceDehnSum ≠ right.pieceDehnSum := by
  intro hsum
  have hboundary :=
    boundaryDehn_eq_of_same_pieceDehnSum_geometricAdditivitySkeletonQ left right hsum
  exact hright (hboundary.symm.trans hleft)

/--
Algebraic interface for the geometric additivity step.  A future polyhedron
formalization should construct this from an actual finite dissection by
separating boundary edges from internal edges and proving the internal
angle-sum equations.
-/
structure DehnAdditivitySkeletonQ (Piece InternalEdge Incident : Type*) where
  pieces : Finset Piece
  pieceDehn : Piece → DehnPiQTarget
  boundaryDehn : DehnPiQTarget
  internalEdges : Finset InternalEdge
  incident : InternalEdge → Finset Incident
  internalLength : InternalEdge → ℝ
  internalAngle : InternalEdge → Incident → ℝ
  internalAngleMultiple : InternalEdge → ℚ
  piece_sum_eq_boundary_add_internal :
    (∑ p ∈ pieces, pieceDehn p) =
      boundaryDehn + ∑ e ∈ internalEdges, ∑ i ∈ incident e,
        dehnEdgeQ (internalLength e) (angleClassQ (internalAngle e i))
  internal_angle_sum : ∀ e ∈ internalEdges,
    (∑ i ∈ incident e, internalAngle e i) =
      (internalAngleMultiple e : ℝ) * Real.pi

theorem DehnAdditivitySkeletonQ.piece_sum_eq_boundary
    {Piece InternalEdge Incident : Type*}
    (cert : DehnAdditivitySkeletonQ Piece InternalEdge Incident) :
    (∑ p ∈ cert.pieces, cert.pieceDehn p) = cert.boundaryDehn := by
  calc
    (∑ p ∈ cert.pieces, cert.pieceDehn p) =
        cert.boundaryDehn + ∑ e ∈ cert.internalEdges, ∑ i ∈ cert.incident e,
          dehnEdgeQ (cert.internalLength e) (angleClassQ (cert.internalAngle e i)) :=
      cert.piece_sum_eq_boundary_add_internal
    _ = cert.boundaryDehn :=
      boundary_add_internalDehnContributionQ cert.boundaryDehn cert.internalEdges cert.incident
        cert.internalLength cert.internalAngle cert.internalAngleMultiple cert.internal_angle_sum

/--
If two boundary polyhedra decompose into the same finite pieces, and both
geometric additivity skeletons have been supplied, then their boundary Dehn
invariants agree.
-/
theorem boundaryDehn_eq_of_same_piece_additivitySkeletonQ
    {Piece Internal₁ Incident₁ Internal₂ Incident₂ : Type*}
    (left : DehnAdditivitySkeletonQ Piece Internal₁ Incident₁)
    (right : DehnAdditivitySkeletonQ Piece Internal₂ Incident₂)
    (hpieces : left.pieces = right.pieces)
    (hpiece : ∀ p ∈ left.pieces, left.pieceDehn p = right.pieceDehn p) :
    left.boundaryDehn = right.boundaryDehn := by
  calc
    left.boundaryDehn = ∑ p ∈ left.pieces, left.pieceDehn p :=
      left.piece_sum_eq_boundary.symm
    _ = ∑ p ∈ left.pieces, right.pieceDehn p := Finset.sum_congr rfl hpiece
    _ = ∑ p ∈ right.pieces, right.pieceDehn p := by rw [hpieces]
    _ = right.boundaryDehn := right.piece_sum_eq_boundary

/--
Algebraic skeleton for rigid reassembly invariance: a bijection of edge sets
that preserves lengths and angle classes preserves the rational Dehn invariant.
-/
theorem dehnInvariantQ_univ_eq_of_edge_equiv {Edge₁ Edge₂ Angle : Type*}
    [Fintype Edge₁] [Fintype Edge₂] [AddCommGroup Angle] [Module ℚ Angle]
    (e : Edge₁ ≃ Edge₂) (length₁ : Edge₁ → ℝ) (length₂ : Edge₂ → ℝ)
    (angle₁ : Edge₁ → Angle) (angle₂ : Edge₂ → Angle)
    (hlength : ∀ x, length₁ x = length₂ (e x))
    (hangle : ∀ x, angle₁ x = angle₂ (e x)) :
    dehnInvariantQ (Finset.univ : Finset Edge₁) length₁ angle₁ =
      dehnInvariantQ (Finset.univ : Finset Edge₂) length₂ angle₂ := by
  unfold dehnInvariantQ
  exact Fintype.sum_equiv e _ _ (fun x => by simp [hlength x, hangle x])

/-- If every edge angle vanishes in the angle target, the Dehn invariant is zero.
This is the cube case: all dihedral angles are `π/2`, which is a rational
multiple of `π` and therefore zero in `AngleModPiQ`. -/
theorem dehnInvariant_eq_zero_of_angles_zero {Edge Angle : Type*}
    [AddCommGroup Angle] [Module ℤ Angle]
    (edges : Finset Edge) (length : Edge → ℝ) (angle : Edge → Angle)
    (hangle : ∀ e ∈ edges, angle e = 0) :
    dehnInvariant edges length angle = 0 := by
  unfold dehnInvariant
  apply Finset.sum_eq_zero
  intro e he
  unfold dehnEdge
  rw [hangle e he, TensorProduct.tmul_zero]

/-- The cube's Dehn invariant in `DehnPiTarget` is zero: every cube dihedral
angle equals `π/2`, which is a rational multiple of `π` and therefore vanishes
under `angleClassQ`. -/
theorem dehnInvariant_cube_eq_zero {Edge : Type*} (edges : Finset Edge)
    (length : Edge → ℝ) :
    dehnInvariant edges length (fun _ => angleClassQ (Real.pi / 2)) = 0 := by
  apply dehnInvariant_eq_zero_of_angles_zero
  intro _ _
  exact angleClassQ_pi_div_two

/-- Rational-target cube Dehn invariant: all edge angles are right angles. -/
theorem dehnInvariantQ_cube_eq_zero {Edge : Type*} (edges : Finset Edge)
    (length : Edge → ℝ) :
    dehnInvariantQ edges length (fun _ => angleClassQ (Real.pi / 2)) = 0 := by
  apply dehnInvariantQ_eq_zero_of_angles_zero
  intro _ _
  exact angleClassQ_pi_div_two

/-- Additivity of an abstract Dehn invariant over finitely many pieces. -/
theorem dehnInvariant_additive_over_dissection {Piece A : Type*} [AddCommMonoid A]
    (pieces : Finset Piece) (dehn : Piece → A) :
    (∑ p ∈ pieces, dehn p) = ∑ p ∈ pieces, dehn p := rfl

/--
If two dissections have matching piecewise Dehn contributions, their total
Dehn invariants agree.
-/
theorem dehnInvariant_eq_of_same_piece_multiset {Piece A : Type*} [AddCommMonoid A]
    (pieces : Finset Piece) (dehn₁ dehn₂ : Piece → A)
    (h : ∀ p ∈ pieces, dehn₁ p = dehn₂ p) :
    (∑ p ∈ pieces, dehn₁ p) = ∑ p ∈ pieces, dehn₂ p := by
  exact Finset.sum_congr rfl h

structure DehnScissorsCertificate (Piece A : Type*) [AddCommMonoid A] (left right : A) where
  pieces : Finset Piece
  leftDehn : Piece → A
  rightDehn : Piece → A
  left_eq : left = ∑ p ∈ pieces, leftDehn p
  right_eq : right = ∑ p ∈ pieces, rightDehn p
  piece_eq : ∀ p ∈ pieces, leftDehn p = rightDehn p

theorem dehn_eq_of_scissors_certificate {Piece A : Type*} [AddCommMonoid A]
    {left right : A} (cert : DehnScissorsCertificate Piece A left right) : left = right := by
  calc
    left = ∑ p ∈ cert.pieces, cert.leftDehn p := cert.left_eq
    _ = ∑ p ∈ cert.pieces, cert.rightDehn p :=
      dehnInvariant_eq_of_same_piece_multiset cert.pieces cert.leftDehn cert.rightDehn cert.piece_eq
    _ = right := cert.right_eq.symm

theorem no_scissors_certificate_of_dehn_ne {Piece A : Type*} [AddCommMonoid A]
    {left right : A} (hleft : left = 0) (hright : right ≠ 0) :
    ¬ Nonempty (DehnScissorsCertificate Piece A left right) := by
  rintro ⟨cert⟩
  exact hright ((dehn_eq_of_scissors_certificate cert).symm.trans hleft)

/--
The final invariant obstruction in Hilbert's third problem: an object with
zero Dehn invariant cannot be scissors-congruent to one with nonzero Dehn
invariant.
-/
theorem impossible_scissors_congruence_of_dehn_ne {A : Type*} [AddCommMonoid A]
    {cube tetra : A} (hcube : cube = 0) (htetra : tetra ≠ 0) : cube ≠ tetra := by
  intro h
  exact htetra (h.symm.trans hcube)

/-! ### Concrete cube and regular tetrahedron coordinate models -/

abbrev Euclidean3 :=
  EuclideanSpace ℝ (Fin 3)

/-- Outward face normals of the cube centered at the origin. -/
noncomputable def cubeFaceNormal : Fin 6 → Euclidean3 :=
  ![!₂[(1 : ℝ), 0, 0], !₂[-1, 0, 0], !₂[0, 1, 0], !₂[0, -1, 0],
    !₂[0, 0, 1], !₂[0, 0, -1]]

/-- The coordinate axis perpendicular to each cube face. -/
def cubeFaceAxis : Fin 6 → Fin 3 :=
  ![⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩,
    ⟨2, by decide⟩, ⟨2, by decide⟩]

/--
The standard regular tetrahedron centered at the origin.  Its vertices are the
four sign vectors with an even number of negative signs.
-/
noncomputable def regularTetrahedronVertex : Fin 4 → Euclidean3 :=
  ![!₂[(1 : ℝ), 1, 1], !₂[(1 : ℝ), -1, -1], !₂[-1, 1, -1], !₂[-1, -1, 1]]

/-- Coordinate dot product in `EuclideanSpace ℝ (Fin 3)`, written explicitly for computation. -/
def dot3 (u v : Euclidean3) : ℝ :=
  u ⟨0, by decide⟩ * v ⟨0, by decide⟩ +
  u ⟨1, by decide⟩ * v ⟨1, by decide⟩ +
  u ⟨2, by decide⟩ * v ⟨2, by decide⟩

noncomputable def cubeFaceNormalCosine (i j : Fin 6) : ℝ :=
  dot3 (cubeFaceNormal i) (cubeFaceNormal j)

theorem cubeFaceNormal_dot_self (i : Fin 6) :
    dot3 (cubeFaceNormal i) (cubeFaceNormal i) = 1 := by
  fin_cases i <;> simp [dot3, cubeFaceNormal]

theorem cubeFaceNormalCosine_of_axis_ne {i j : Fin 6}
    (haxis : cubeFaceAxis i ≠ cubeFaceAxis j) :
    cubeFaceNormalCosine i j = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [cubeFaceNormalCosine, cubeFaceAxis, dot3, cubeFaceNormal] at haxis ⊢

theorem cube_rightAngle_has_faceNormal_cosine {i j : Fin 6}
    (haxis : cubeFaceAxis i ≠ cubeFaceAxis j) :
    Real.cos (Real.pi / 2) = cubeFaceNormalCosine i j := by
  rw [Real.cos_pi_div_two, cubeFaceNormalCosine_of_axis_ne haxis]

/--
Edges of the coordinate cube, represented as intersections of two adjacent
faces.  The condition `cubeFaceAxis i ≠ cubeFaceAxis j` excludes opposite
parallel face pairs, leaving the twelve actual cube edges.
-/
abbrev CubeEdge :=
  {p : Fin 6 × Fin 6 // p.1 < p.2 ∧ cubeFaceAxis p.1 ≠ cubeFaceAxis p.2}

theorem cubeEdge_card : Fintype.card CubeEdge = 12 := by
  decide

theorem cubeEdge_univ_card :
    (Finset.univ : Finset CubeEdge).card = 12 := by
  decide

noncomputable def cubeEdgeLength (_e : CubeEdge) : ℝ :=
  2

noncomputable def unitCubeEdgeLength (_e : CubeEdge) : ℝ :=
  1

noncomputable def cubeEdgeDihedralAngle (_e : CubeEdge) : ℝ :=
  Real.pi / 2

theorem cubeEdgeDihedralAngle_faceNormal_cosine (e : CubeEdge) :
    Real.cos (cubeEdgeDihedralAngle e) =
      cubeFaceNormalCosine e.1.1 e.1.2 := by
  rw [cubeEdgeDihedralAngle, cube_rightAngle_has_faceNormal_cosine e.2.2]

/-- Concrete cube Dehn invariant in the rational angle target. -/
theorem cube_dehnInvariantQ_edges_eq_zero :
    dehnInvariantQ (Finset.univ : Finset CubeEdge)
        cubeEdgeLength
        (fun e => angleClassQ (cubeEdgeDihedralAngle e)) = 0 := by
  apply dehnInvariantQ_eq_zero_of_angles_zero
  intro e _he
  simp [cubeEdgeDihedralAngle]

/-- The concrete unit-cube Dehn invariant in the rational angle target. -/
noncomputable def unitCubeDehnInvariantQ : DehnPiQTarget :=
  dehnInvariantQ (Finset.univ : Finset CubeEdge)
    unitCubeEdgeLength
    (fun e => angleClassQ (cubeEdgeDihedralAngle e))

/--
The unit cube has zero Dehn invariant: every dihedral angle is `π / 2`, which
vanishes in `ℝ / πℚ`.
-/
theorem unitCubeDehnInvariantQ_eq_zero :
    unitCubeDehnInvariantQ = 0 := by
  rw [unitCubeDehnInvariantQ]
  apply dehnInvariantQ_eq_zero_of_angles_zero
  intro e _he
  simp [cubeEdgeDihedralAngle]

/-- Coordinate squared distance in `EuclideanSpace ℝ (Fin 3)`, written explicitly for computation. -/
def coordinateDistSq3 (u v : Euclidean3) : ℝ :=
  (u ⟨0, by decide⟩ - v ⟨0, by decide⟩) ^ 2 +
  (u ⟨1, by decide⟩ - v ⟨1, by decide⟩) ^ 2 +
  (u ⟨2, by decide⟩ - v ⟨2, by decide⟩) ^ 2

theorem euclidean3_dist_sq_eq_coordinateDistSq3 (u v : Euclidean3) :
    dist u v ^ 2 = coordinateDistSq3 u v := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [coordinateDistSq3, Fin.sum_univ_three, dist_eq_norm]

/-- Cube vertices as coordinate sign vectors. -/
abbrev CubeVertexSign :=
  Fin 3 → Bool

noncomputable def cubeVertexPoint (v : CubeVertexSign) : Euclidean3 :=
  !₂[if v ⟨0, by decide⟩ then (1 : ℝ) else -1,
     if v ⟨1, by decide⟩ then (1 : ℝ) else -1,
     if v ⟨2, by decide⟩ then (1 : ℝ) else -1]

/--
Coordinate cube edges: choose the axis along the edge and the signs on the
two fixed coordinates.  The sign on the moving axis is normalized to `false`,
so this type has no duplicate representation.
-/
abbrev CubeCoordinateEdge :=
  {p : Fin 3 × CubeVertexSign // p.2 p.1 = false}

theorem cubeCoordinateEdge_card : Fintype.card CubeCoordinateEdge = 12 := by
  decide

theorem cubeCoordinateEdge_univ_card :
    (Finset.univ : Finset CubeCoordinateEdge).card = 12 := by
  decide

def cubeCoordinateEdgeEndpoint (e : CubeCoordinateEdge) (positiveAlongAxis : Bool) :
    CubeVertexSign :=
  fun i => if i = e.1.1 then positiveAlongAxis else e.1.2 i

theorem cubeCoordinateEdgeEndpoint_coordinateDistSq3 (e : CubeCoordinateEdge) :
    coordinateDistSq3
        (cubeVertexPoint (cubeCoordinateEdgeEndpoint e false))
        (cubeVertexPoint (cubeCoordinateEdgeEndpoint e true)) = 4 := by
  fin_cases e <;>
    simp [coordinateDistSq3, cubeVertexPoint, cubeCoordinateEdgeEndpoint] <;>
    norm_num

noncomputable def cubeCoordinateEdgeLength (e : CubeCoordinateEdge) : ℝ :=
  dist
    (cubeVertexPoint (cubeCoordinateEdgeEndpoint e false))
    (cubeVertexPoint (cubeCoordinateEdgeEndpoint e true))

theorem cubeCoordinateEdgeLength_eq_two (e : CubeCoordinateEdge) :
    cubeCoordinateEdgeLength e = 2 := by
  rw [cubeCoordinateEdgeLength]
  rw [← sq_eq_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [euclidean3_dist_sq_eq_coordinateDistSq3,
    cubeCoordinateEdgeEndpoint_coordinateDistSq3]
  norm_num

noncomputable def cubeCoordinateEdgeDihedralAngle (_e : CubeCoordinateEdge) : ℝ :=
  Real.pi / 2

theorem cubeCoordinate_dehnInvariantQ_edges_eq_zero :
    dehnInvariantQ (Finset.univ : Finset CubeCoordinateEdge)
        cubeCoordinateEdgeLength
        (fun e => angleClassQ (cubeCoordinateEdgeDihedralAngle e)) = 0 := by
  apply dehnInvariantQ_eq_zero_of_angles_zero
  intro e _he
  simp [cubeCoordinateEdgeDihedralAngle]

theorem regularTetrahedronVertex_dot_self (i : Fin 4) :
    dot3 (regularTetrahedronVertex i) (regularTetrahedronVertex i) = 3 := by
  fin_cases i <;> simp [dot3, regularTetrahedronVertex] <;> norm_num

theorem regularTetrahedronVertex_dot_of_ne {i j : Fin 4} (hij : i ≠ j) :
    dot3 (regularTetrahedronVertex i) (regularTetrahedronVertex j) = -1 := by
  fin_cases i <;> fin_cases j <;>
    simp [dot3, regularTetrahedronVertex] at hij ⊢

theorem regularTetrahedronVertex_coordinateDistSq_of_ne {i j : Fin 4} (hij : i ≠ j) :
    coordinateDistSq3 (regularTetrahedronVertex i) (regularTetrahedronVertex j) = 8 := by
  fin_cases i <;> fin_cases j <;>
    simp [coordinateDistSq3, regularTetrahedronVertex] at hij ⊢ <;> norm_num

/-- All six edges in the coordinate tetrahedron have squared length `8`. -/
theorem regularTetrahedronVertex_dist_sq_of_ne {i j : Fin 4} (hij : i ≠ j) :
    dist (regularTetrahedronVertex i) (regularTetrahedronVertex j) ^ 2 = 8 := by
  rw [euclidean3_dist_sq_eq_coordinateDistSq3]
  exact regularTetrahedronVertex_coordinateDistSq_of_ne hij

theorem regularTetrahedronVertex_affineIndependent :
    AffineIndependent ℝ regularTetrahedronVertex := by
  rw [affineIndependent_iff_of_fintype]
  intro w hsum hvec i
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hsum] at hvec
  have h0 := congrArg (fun v : Euclidean3 => v ⟨0, by decide⟩) hvec
  have h1 := congrArg (fun v : Euclidean3 => v ⟨1, by decide⟩) hvec
  have h2 := congrArg (fun v : Euclidean3 => v ⟨2, by decide⟩) hvec
  simp [regularTetrahedronVertex, Fin.sum_univ_four] at hsum h0 h1 h2
  fin_cases i <;> simp <;> linarith

/-- The coordinate regular tetrahedron as a bundled Mathlib affine simplex. -/
noncomputable def regularTetrahedronSimplex : Affine.Simplex ℝ Euclidean3 3 where
  points := regularTetrahedronVertex
  independent := regularTetrahedronVertex_affineIndependent

theorem regularTetrahedronSimplex_equilateral :
    regularTetrahedronSimplex.Equilateral := by
  refine ⟨Real.sqrt 8, ?_⟩
  intro i j hij
  change dist (regularTetrahedronVertex i) (regularTetrahedronVertex j) = Real.sqrt 8
  rw [← sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg 8)]
  rw [regularTetrahedronVertex_dist_sq_of_ne hij, Real.sq_sqrt]
  norm_num

/-- Edges of the concrete regular tetrahedron, represented once as ordered pairs `i < j`. -/
abbrev RegularTetrahedronEdge :=
  {p : Fin 4 × Fin 4 // p.1 < p.2}

/--
For an edge `e = {u, v}`, the two adjacent faces are the faces opposite the
two vertices not equal to `u` or `v`.
-/
abbrev RegularTetrahedronEdgeAdjacentFaceVertex (e : RegularTetrahedronEdge) :=
  {i : Fin 4 // i ≠ e.1.1 ∧ i ≠ e.1.2}

theorem regularTetrahedronEdge_card : Fintype.card RegularTetrahedronEdge = 6 := by
  decide

theorem regularTetrahedronEdge_univ_card :
    (Finset.univ : Finset RegularTetrahedronEdge).card = 6 := by
  decide

theorem regularTetrahedronEdgeAdjacentFaceVertex_card (e : RegularTetrahedronEdge) :
    Fintype.card (RegularTetrahedronEdgeAdjacentFaceVertex e) = 2 := by
  fin_cases e <;> decide

noncomputable def regularTetrahedronEdgeLength (e : RegularTetrahedronEdge) : ℝ :=
  dist (regularTetrahedronVertex e.1.1) (regularTetrahedronVertex e.1.2)

theorem regularTetrahedronEdgeLength_eq_sqrt8 (e : RegularTetrahedronEdge) :
    regularTetrahedronEdgeLength e = Real.sqrt 8 := by
  rw [regularTetrahedronEdgeLength]
  rw [← sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg 8)]
  rw [regularTetrahedronVertex_dist_sq_of_ne e.2.ne, Real.sq_sqrt]
  norm_num

theorem regularTetrahedron_dehnInvariantQ_edges_eq :
    dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
        regularTetrahedronEdgeLength
        (fun _ => angleClassQ (Real.arccos (1 / 3))) =
      dehnEdgeQ (6 * Real.sqrt 8) (angleClassQ (Real.arccos (1 / 3))) := by
  simpa [dehnInvariantQ, regularTetrahedronEdgeLength_eq_sqrt8,
    regularTetrahedronEdge_univ_card] using
    (dehnInvariantQ_const_length_angle
      (edges := (Finset.univ : Finset RegularTetrahedronEdge))
      (length := Real.sqrt 8)
      (angle := angleClassQ (Real.arccos (1 / 3))))

/--
The vector from the origin to a vertex is orthogonal to every edge of the
opposite face.  This is the coordinate fact behind using these vertex vectors
as face normals for the regular tetrahedron.
-/
theorem regularTetrahedronVertex_orthogonal_to_opposite_face_edge
    {i j k : Fin 4} (hji : j ≠ i) (hki : k ≠ i) :
    dot3 (regularTetrahedronVertex i)
      (regularTetrahedronVertex j - regularTetrahedronVertex k) = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [dot3, regularTetrahedronVertex] at hji hki ⊢

/--
The normal of a face adjacent to a tetrahedron edge is orthogonal to that
edge.  This identifies the complement-vertex indexing above with the usual
edge/face incidence geometry for the coordinate tetrahedron.
-/
theorem regularTetrahedronEdge_adjacentFaceNormal_orthogonal
    (e : RegularTetrahedronEdge) (i : RegularTetrahedronEdgeAdjacentFaceVertex e) :
    dot3 (regularTetrahedronVertex i.1)
      (regularTetrahedronVertex e.1.1 - regularTetrahedronVertex e.1.2) = 0 := by
  exact regularTetrahedronVertex_orthogonal_to_opposite_face_edge
    (i := i.1) (j := e.1.1) (k := e.1.2) i.2.1.symm i.2.2.symm

/--
The face opposite vertex `i` has normal parallel to `regularTetrahedronVertex i`.
Since all these normals have squared length `3`, this quotient is the cosine
between the two face normals.
-/
noncomputable def regularTetrahedronFaceNormalCosine (i j : Fin 4) : ℝ :=
  dot3 (regularTetrahedronVertex i) (regularTetrahedronVertex j) / 3

theorem regularTetrahedronFaceNormalCosine_of_ne {i j : Fin 4} (hij : i ≠ j) :
    regularTetrahedronFaceNormalCosine i j = -1 / 3 := by
  rw [regularTetrahedronFaceNormalCosine, regularTetrahedronVertex_dot_of_ne hij]

/--
For adjacent faces of the regular tetrahedron, the cosine of the interior
dihedral angle is the negative of the cosine between outward normals.
-/
theorem regularTetrahedron_dihedralCosine_of_ne {i j : Fin 4} (hij : i ≠ j) :
    -regularTetrahedronFaceNormalCosine i j = 1 / 3 := by
  rw [regularTetrahedronFaceNormalCosine_of_ne hij]
  norm_num

theorem regularTetrahedron_arccos_one_third_has_dihedral_cosine {i j : Fin 4}
    (hij : i ≠ j) :
    Real.cos (Real.arccos (1 / 3)) = -regularTetrahedronFaceNormalCosine i j := by
  rw [Real.cos_arccos, regularTetrahedron_dihedralCosine_of_ne hij] <;> norm_num

/--
The dihedral angle determined by the two outward face normals opposite
vertices `i` and `j`.
-/
noncomputable def regularTetrahedronDihedralAngle (i j : Fin 4) : ℝ :=
  Real.arccos (-regularTetrahedronFaceNormalCosine i j)

theorem regularTetrahedronDihedralAngle_of_ne {i j : Fin 4} (hij : i ≠ j) :
    regularTetrahedronDihedralAngle i j = Real.arccos (1 / 3) := by
  rw [regularTetrahedronDihedralAngle, regularTetrahedron_dihedralCosine_of_ne hij]

theorem regularTetrahedronEdge_adjacentFaceDihedralAngle_of_ne
    (e : RegularTetrahedronEdge) {i j : RegularTetrahedronEdgeAdjacentFaceVertex e}
    (hij : i ≠ j) :
    regularTetrahedronDihedralAngle i.1 j.1 = Real.arccos (1 / 3) := by
  exact regularTetrahedronDihedralAngle_of_ne (fun h => hij (Subtype.ext h))

noncomputable def regularTetrahedronEdgeAdjacentFaceEquiv (e : RegularTetrahedronEdge) :
    RegularTetrahedronEdgeAdjacentFaceVertex e ≃ Fin 2 :=
  Fintype.equivFinOfCardEq (regularTetrahedronEdgeAdjacentFaceVertex_card e)

noncomputable def regularTetrahedronEdgeAdjacentFaceVertex0
    (e : RegularTetrahedronEdge) : Fin 4 :=
  ((regularTetrahedronEdgeAdjacentFaceEquiv e).symm 0).1

noncomputable def regularTetrahedronEdgeAdjacentFaceVertex1
    (e : RegularTetrahedronEdge) : Fin 4 :=
  ((regularTetrahedronEdgeAdjacentFaceEquiv e).symm 1).1

theorem regularTetrahedronEdgeAdjacentFaceVertex0_ne_vertex1
    (e : RegularTetrahedronEdge) :
    regularTetrahedronEdgeAdjacentFaceVertex0 e ≠
      regularTetrahedronEdgeAdjacentFaceVertex1 e := by
  intro h
  let f := regularTetrahedronEdgeAdjacentFaceEquiv e
  have hsub : f.symm 0 = f.symm 1 := Subtype.ext h
  have hfin : (0 : Fin 2) = 1 := by
    calc
      (0 : Fin 2) = f (f.symm 0) := by simp
      _ = f (f.symm 1) := by rw [hsub]
      _ = 1 := by simp
  exact (by decide : (0 : Fin 2) ≠ 1) hfin

noncomputable def regularTetrahedronEdgeDihedralAngle
    (e : RegularTetrahedronEdge) : ℝ :=
  regularTetrahedronDihedralAngle
    (regularTetrahedronEdgeAdjacentFaceVertex0 e)
    (regularTetrahedronEdgeAdjacentFaceVertex1 e)

theorem regularTetrahedronEdgeDihedralAngle_eq_arccos_one_third
    (e : RegularTetrahedronEdge) :
    regularTetrahedronEdgeDihedralAngle e = Real.arccos (1 / 3) := by
  exact regularTetrahedronDihedralAngle_of_ne
    (regularTetrahedronEdgeAdjacentFaceVertex0_ne_vertex1 e)

/--
The regular tetrahedron has nonzero Dehn invariant because its dihedral
angle `arccos(1/3)` is irrational over `π`. This is the book's key
number-theoretic computation.
-/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | (q + 2) => 2 * a (q + 1) - 9 * a q

lemma a_zmod_3 (q : ℕ) : (a q : ZMod 3) = 1 ∨ (a q : ZMod 3) = 2 := by
  induction' q using Nat.strong_induction_on with q ih
  rcases q with _ | q
  · left; rfl
  rcases q with _ | q
  · left; rfl
  · have h1 := ih (q + 1) (by omega)
    have eq : (a (q + 2) : ZMod 3) = 2 * (a (q + 1) : ZMod 3) := by
      have h_a : a (q + 2) = 2 * a (q + 1) - 9 * a q := rfl
      rw [h_a]
      push_cast
      have : (9 : ZMod 3) = 0 := rfl
      rw [this, zero_mul, sub_zero]
    rcases h1 with h | h
    · right; rw [eq, h]; rfl
    · left; rw [eq, h]; rfl

lemma a_eq_T (q : ℕ) :
    (a q : ℝ) = (3 : ℝ)^q * (T ℝ (q : ℤ)).eval (1/3) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    match q with
    | 0 =>
      simp [a, T_zero, eval_one]
    | 1 =>
      simp [a, T_one, eval_X]
    | q + 2 =>
      have ih_q  : (a q : ℝ) = (3 : ℝ)^q * (T ℝ (q : ℤ)).eval (1/3) := ih q (by omega)
      have ih_q1 : (a (q+1) : ℝ) = (3 : ℝ)^(q+1) * (T ℝ ((q+1 : ℕ) : ℤ)).eval (1/3) :=
        ih (q+1) (by omega)
      have hcast : ((q + 2 : ℕ) : ℤ) = (q : ℤ) + 2 := by push_cast; rfl
      have hT :
          (T ℝ ((q + 2 : ℕ) : ℤ)).eval (1/3 : ℝ) =
            2 * (1/3) * (T ℝ ((q : ℤ) + 1)).eval (1/3) -
              (T ℝ ((q : ℕ) : ℤ)).eval (1/3) := by
        rw [hcast, T_add_two]
        simp [eval_sub, eval_mul, eval_X]
      have ha_rec : (a (q + 2) : ℝ) = 2 * (a (q + 1) : ℝ) - 9 * (a q : ℝ) := by
        have : a (q + 2) = 2 * a (q + 1) - 9 * a q := rfl
        rw [this]
        push_cast
        rfl
      have hcast_norm : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; rfl
      rw [hcast_norm] at ih_q1
      rw [ha_rec, hT, ih_q, ih_q1]
      have h3 : (3 : ℝ)^(q+2) = (3 : ℝ)^q * 9 := by rw [pow_add]; norm_num
      have h31 : (3 : ℝ)^(q+1) = (3 : ℝ)^q * 3 := by rw [pow_add]; norm_num
      rw [h3, h31]
      ring

theorem arccos_one_third_irrational_over_pi (q : ℚ) :
    Real.arccos (1/3) ≠ q * Real.pi := by
  intro h
  rcases eq_or_ne q 0 with hq | hq
  · rw [hq] at h
    simp at h
    revert h
    norm_num
  have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have h_int : (q.den : ℝ) * Real.arccos (1/3) = (q.num : ℝ) * Real.pi := by
    have hq_eq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by rw [Rat.cast_def]
    rw [h, hq_eq]
    field_simp
  have h_cos_lhs :
      Real.cos ((q.den : ℝ) * Real.arccos (1/3)) =
        (T ℝ (q.den : ℤ)).eval (1/3) := by
    have hcos_arccos : Real.cos (Real.arccos (1/3)) = 1/3 := by
      rw [Real.cos_arccos] <;> norm_num
    have h_symm := (T_real_cos (Real.arccos (1/3)) (q.den : ℤ)).symm
    have h_cast : ((q.den : ℤ) : ℝ) = (q.den : ℝ) := by push_cast; rfl
    rw [h_cast] at h_symm
    rw [hcos_arccos] at h_symm
    exact h_symm
  
  have h_cos_eq : Real.cos ((q.den : ℝ) * Real.arccos (1/3)) =
                  Real.cos ((q.num : ℝ) * Real.pi) := by rw [h_int]
  
  have h_sin : Real.sin ((q.num : ℝ) * Real.pi) = 0 := by
    have : (q.num : ℝ) * Real.pi = (q.num : ℤ) * Real.pi := by rfl
    rw [this, Real.sin_int_mul_pi]
  have h_cos_sq : Real.cos ((q.num : ℝ) * Real.pi) ^ 2 = 1 := by
    have := Real.cos_sq_add_sin_sq ((q.num : ℝ) * Real.pi)
    rw [h_sin] at this
    linarith
  have h4 : Real.cos ((q.num : ℝ) * Real.pi) = 1 ∨ Real.cos ((q.num : ℝ) * Real.pi) = -1 := sq_eq_one_iff.mp h_cos_sq

  have h_T_eval : (T ℝ (q.den : ℤ)).eval (1/3) = 1 ∨ (T ℝ (q.den : ℤ)).eval (1/3) = -1 := by
    rcases h4 with h4 | h4
    · left; rw [← h_cos_lhs, h_cos_eq, h4]
    · right; rw [← h_cos_lhs, h_cos_eq, h4]

  have h_a_eq : (a q.den : ℝ) = (3 : ℝ)^q.den ∨ (a q.den : ℝ) = -(3 : ℝ)^q.den := by
    have eq := a_eq_T q.den
    rcases h_T_eval with ht | ht
    · left; rw [eq, ht, mul_one]
    · right; rw [eq, ht]; ring
  
  have h_a_eq_int : (a q.den : ℤ) = (3 : ℤ)^q.den ∨ (a q.den : ℤ) = -(3 : ℤ)^q.den := by
    rcases h_a_eq with ha | ha
    · left; exact_mod_cast ha
    · right; exact_mod_cast ha

  have h_den_pos : 1 ≤ q.den := q.pos
  have h_a_zmod : (a q.den : ZMod 3) = 0 := by
    have h_pow : (3 : ZMod 3)^q.den = 0 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt h_den_pos)
      rw [hk]
      have h3 : (3 : ZMod 3) = 0 := rfl
      rw [h3]
      exact zero_pow (by omega)
    rcases h_a_eq_int with ha | ha
    · have : ((a q.den : ℤ) : ZMod 3) = (3 : ZMod 3)^q.den := by
        rw [ha]
        exact Int.cast_pow 3 q.den
      rw [this, h_pow]
    · have : ((a q.den : ℤ) : ZMod 3) = -(3 : ZMod 3)^q.den := by
        rw [ha]
        have h_pow_cast : (((3 : ℤ)^q.den : ℤ) : ZMod 3) = (3 : ZMod 3)^q.den := Int.cast_pow 3 q.den
        rw [Int.cast_neg, h_pow_cast]
      rw [this, h_pow, neg_zero]
      
  rcases a_zmod_3 q.den with h1 | h2
  · rw [h_a_zmod] at h1; revert h1; decide
  · rw [h_a_zmod] at h2; revert h2; decide


/-- `arccos(1/3)` is *not* a rational multiple of `π`, hence is nonzero in the
`πℚ` quotient — this is the tetrahedron's nontrivial Dehn-edge contribution. -/
theorem angleClassQ_arccos_one_third_ne_zero :
    angleClassQ (Real.arccos (1/3)) ≠ 0 := by
  intro h
  rw [angleClassQ, Submodule.Quotient.mk_eq_zero] at h
  rw [piQSubmodule, Submodule.mem_span_singleton] at h
  obtain ⟨q, hq⟩ := h
  rw [Rat.smul_def] at hq
  exact arccos_one_third_irrational_over_pi q hq.symm

theorem angleClassQ_regularTetrahedronDihedralAngle_ne_zero {i j : Fin 4} (hij : i ≠ j) :
    angleClassQ (regularTetrahedronDihedralAngle i j) ≠ 0 := by
  rw [regularTetrahedronDihedralAngle_of_ne hij]
  exact angleClassQ_arccos_one_third_ne_zero

theorem angleClassQ_regularTetrahedronEdge_adjacentFaceDihedralAngle_ne_zero
    (e : RegularTetrahedronEdge) {i j : RegularTetrahedronEdgeAdjacentFaceVertex e}
    (hij : i ≠ j) :
    angleClassQ (regularTetrahedronDihedralAngle i.1 j.1) ≠ 0 := by
  rw [regularTetrahedronEdge_adjacentFaceDihedralAngle_of_ne e hij]
  exact angleClassQ_arccos_one_third_ne_zero

/--
Pure tensors over a field are nonzero when both factors are nonzero.  This is
the algebraic fact needed to turn the tetrahedron's nonzero angle class into a
nonzero rational Dehn invariant.
-/
theorem tensor_tmul_ne_zero_of_ne_zero {K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    {m : M} {n : N} (hm : m ≠ 0) (hn : n ≠ 0) :
    (m ⊗ₜ[K] n : TensorProduct K M N) ≠ 0 := by
  classical
  let s : Set N := {n}
  have hs : LinearIndepOn K id s := by
    rw [linearIndepOn_singleton_iff]
    exact hn
  let b : Module.Basis (hs.extend (Set.subset_univ s)) K N := Module.Basis.extend hs
  have hn_mem : n ∈ hs.extend (Set.subset_univ s) :=
    hs.subset_extend (Set.subset_univ s) (by simp [s])
  let i : hs.extend (Set.subset_univ s) := ⟨n, hn_mem⟩
  have hb_i : b i = n := by
    change (Module.Basis.extend hs) i = (i : N)
    exact Module.Basis.extend_apply_self hs i
  intro hzero
  have hcoeff : (TensorProduct.equivFinsuppOfBasisRight b) (m ⊗ₜ[K] n) i = 0 := by
    rw [hzero]
    simp
  rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply] at hcoeff
  have hrepr : b.repr n i = 1 := by
    rw [← hb_i, Module.Basis.repr_self]
    simp
  rw [hrepr, one_smul] at hcoeff
  exact hm hcoeff

theorem dehnEdgeQ_ne_zero_of_ne_zero {Angle : Type*}
    [AddCommGroup Angle] [Module ℚ Angle] {length : ℝ} {angle : Angle}
    (hlength : length ≠ 0) (hangle : angle ≠ 0) :
    dehnEdgeQ length angle ≠ 0 := by
  exact tensor_tmul_ne_zero_of_ne_zero hlength hangle

/--
In the rational tensor target, the six equal edges of a regular tetrahedron
give a nonzero Dehn sum as soon as the common edge length is nonzero.
-/
theorem regularTetrahedron_six_edge_dehnQ_ne_zero {edgeLength : ℝ}
    (hedgeLength : edgeLength ≠ 0) :
    dehnInvariantQ (Finset.univ : Finset (Fin 6)) (fun _ => edgeLength)
        (fun _ => angleClassQ (Real.arccos (1 / 3))) ≠ 0 := by
  rw [dehnInvariantQ_six_equal_edges]
  exact dehnEdgeQ_ne_zero_of_ne_zero
    (mul_ne_zero (by norm_num : (6 : ℝ) ≠ 0) hedgeLength)
    angleClassQ_arccos_one_third_ne_zero

/--
The regular tetrahedron's concrete six-edge Dehn invariant is nonzero in
`ℝ ⊗[ℚ] (ℝ / πℚ)`.
-/
theorem regularTetrahedron_dehnInvariantQ_edges_ne_zero :
    dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
        regularTetrahedronEdgeLength
        (fun _ => angleClassQ (Real.arccos (1 / 3))) ≠ 0 := by
  rw [regularTetrahedron_dehnInvariantQ_edges_eq]
  exact dehnEdgeQ_ne_zero_of_ne_zero
    (mul_ne_zero (by norm_num : (6 : ℝ) ≠ 0)
      (ne_of_gt (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 8))))
    angleClassQ_arccos_one_third_ne_zero

/--
The concrete tetrahedron Dehn sum using the edge-specific adjacent-face
dihedral angle function.
-/
theorem regularTetrahedron_dehnInvariantQ_geometric_edges_eq :
    dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
        regularTetrahedronEdgeLength
        (fun e => angleClassQ (regularTetrahedronEdgeDihedralAngle e)) =
      dehnEdgeQ (6 * Real.sqrt 8) (angleClassQ (Real.arccos (1 / 3))) := by
  simpa [dehnInvariantQ, regularTetrahedronEdgeLength_eq_sqrt8,
    regularTetrahedronEdgeDihedralAngle_eq_arccos_one_third,
    regularTetrahedronEdge_univ_card] using
    (dehnInvariantQ_const_length_angle
      (edges := (Finset.univ : Finset RegularTetrahedronEdge))
      (length := Real.sqrt 8)
      (angle := angleClassQ (Real.arccos (1 / 3))))

theorem regularTetrahedron_dehnInvariantQ_geometric_edges_ne_zero :
    dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
        regularTetrahedronEdgeLength
        (fun e => angleClassQ (regularTetrahedronEdgeDihedralAngle e)) ≠ 0 := by
  rw [regularTetrahedron_dehnInvariantQ_geometric_edges_eq]
  exact dehnEdgeQ_ne_zero_of_ne_zero
    (mul_ne_zero (by norm_num : (6 : ℝ) ≠ 0)
      (ne_of_gt (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 8))))
    angleClassQ_arccos_one_third_ne_zero

/-- The concrete regular tetrahedron Dehn invariant in the rational angle target. -/
noncomputable def regularTetrahedronDehnInvariantQ : DehnPiQTarget :=
  dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
    regularTetrahedronEdgeLength
    (fun e => angleClassQ (regularTetrahedronEdgeDihedralAngle e))

/--
The concrete regular tetrahedron has nonzero Dehn invariant.  The proof uses
the computed dihedral angle `arccos (1 / 3)` and the proved irrationality of
that angle over `π`.
-/
theorem regularTetrahedronDehnInvariantQ_ne_zero :
    regularTetrahedronDehnInvariantQ ≠ 0 := by
  simpa [regularTetrahedronDehnInvariantQ] using
    regularTetrahedron_dehnInvariantQ_geometric_edges_ne_zero

/--
The computed Dehn values of the unit cube and the coordinate regular
tetrahedron differ.
-/
theorem unitCube_not_regularTetrahedron_dehnQ :
    unitCubeDehnInvariantQ ≠ regularTetrahedronDehnInvariantQ := by
  exact impossible_scissors_congruence_of_dehn_ne
    unitCubeDehnInvariantQ_eq_zero
    regularTetrahedronDehnInvariantQ_ne_zero

/--
The abstract rational Dehn sums for a right-angled cube and a regular
tetrahedron are different.  This still does not assert geometric scissors
congruence, because the polyhedron/dissection layer is not available.
-/
theorem cube_not_regularTetrahedron_abstract_dehnQ {cubeEdgeLength tetraEdgeLength : ℝ}
    (htetraEdgeLength : tetraEdgeLength ≠ 0) :
    dehnInvariantQ (Finset.univ : Finset (Fin 12)) (fun _ => cubeEdgeLength)
        (fun _ => angleClassQ (Real.pi / 2)) ≠
      dehnInvariantQ (Finset.univ : Finset (Fin 6)) (fun _ => tetraEdgeLength)
        (fun _ => angleClassQ (Real.arccos (1 / 3))) := by
  exact impossible_scissors_congruence_of_dehn_ne
    (dehnInvariantQ_cube_eq_zero (Finset.univ : Finset (Fin 12)) (fun _ => cubeEdgeLength))
    (regularTetrahedron_six_edge_dehnQ_ne_zero htetraEdgeLength)

/--
The right-angled 12-edge cube Dehn sum differs from the concrete regular
tetrahedron edge Dehn sum.
-/
theorem cube_not_regularTetrahedron_concrete_dehnQ {cubeEdgeLength : ℝ} :
    dehnInvariantQ (Finset.univ : Finset (Fin 12)) (fun _ => cubeEdgeLength)
        (fun _ => angleClassQ (Real.pi / 2)) ≠
      dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
        regularTetrahedronEdgeLength
        (fun _ => angleClassQ (Real.arccos (1 / 3))) := by
  exact impossible_scissors_congruence_of_dehn_ne
    (dehnInvariantQ_cube_eq_zero (Finset.univ : Finset (Fin 12)) (fun _ => cubeEdgeLength))
    regularTetrahedron_dehnInvariantQ_edges_ne_zero

/--
The concrete cube edge model and the concrete regular tetrahedron edge model
have different rational Dehn invariants.
-/
theorem cube_not_regularTetrahedron_concrete_geometry_dehnQ :
    dehnInvariantQ (Finset.univ : Finset CubeEdge)
        cubeEdgeLength
        (fun e => angleClassQ (cubeEdgeDihedralAngle e)) ≠
      dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
        regularTetrahedronEdgeLength
        (fun _ => angleClassQ (Real.arccos (1 / 3))) := by
  exact impossible_scissors_congruence_of_dehn_ne
    cube_dehnInvariantQ_edges_eq_zero
    regularTetrahedron_dehnInvariantQ_edges_ne_zero

/--
Concrete cube edges cannot have the same Dehn invariant as concrete
tetrahedron edges when the tetrahedron uses its edge-specific adjacent-face
dihedral angle function.
-/
theorem cube_not_regularTetrahedron_concrete_edgeGeometry_dehnQ :
    dehnInvariantQ (Finset.univ : Finset CubeEdge)
        cubeEdgeLength
        (fun e => angleClassQ (cubeEdgeDihedralAngle e)) ≠
      dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
        regularTetrahedronEdgeLength
        (fun e => angleClassQ (regularTetrahedronEdgeDihedralAngle e)) := by
  exact impossible_scissors_congruence_of_dehn_ne
    cube_dehnInvariantQ_edges_eq_zero
    regularTetrahedron_dehnInvariantQ_geometric_edges_ne_zero

/--
The coordinate-vertex cube edge model also has Dehn invariant different from
the concrete tetrahedron edge model.
-/
theorem cubeCoordinate_not_regularTetrahedron_concrete_edgeGeometry_dehnQ :
    dehnInvariantQ (Finset.univ : Finset CubeCoordinateEdge)
        cubeCoordinateEdgeLength
        (fun e => angleClassQ (cubeCoordinateEdgeDihedralAngle e)) ≠
      dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
        regularTetrahedronEdgeLength
        (fun e => angleClassQ (regularTetrahedronEdgeDihedralAngle e)) := by
  exact impossible_scissors_congruence_of_dehn_ne
    cubeCoordinate_dehnInvariantQ_edges_eq_zero
    regularTetrahedron_dehnInvariantQ_geometric_edges_ne_zero

/--
Concrete obstruction exported through the geometric additivity skeleton: once
an actual dissection formalization supplies these skeletons with the concrete
cube and tetrahedron boundary data, their piece Dehn sums cannot agree.
-/
theorem no_same_pieceDehnSum_concrete_cube_regularTetrahedron_geometricAdditivitySkeletonQ
    {CubeBoundaryFragment CubeInternalEdge CubeIncident
      TetraBoundaryFragment TetraInternalEdge TetraIncident : Type*}
    (cubeCert :
      DehnGeometricAdditivitySkeletonQ
        CubeEdge CubeBoundaryFragment CubeInternalEdge CubeIncident)
    (tetraCert :
      DehnGeometricAdditivitySkeletonQ
        RegularTetrahedronEdge TetraBoundaryFragment TetraInternalEdge TetraIncident)
    (hcubeEdges : cubeCert.boundaryEdges = Finset.univ)
    (hcubeAngle : ∀ e, cubeCert.boundaryAngle e = cubeEdgeDihedralAngle e)
    (htetraEdges : tetraCert.boundaryEdges = Finset.univ)
    (htetraLength : ∀ e, tetraCert.boundaryLength e = regularTetrahedronEdgeLength e)
    (htetraAngle : ∀ e,
      tetraCert.boundaryAngle e = regularTetrahedronEdgeDihedralAngle e) :
    cubeCert.pieceDehnSum ≠ tetraCert.pieceDehnSum := by
  refine no_same_pieceDehnSum_geometricAdditivitySkeletonQ_of_dehn_ne
    cubeCert tetraCert ?_ ?_
  · rw [hcubeEdges]
    apply dehnInvariantQ_eq_zero_of_angles_zero
    intro e _he
    rw [hcubeAngle e, cubeEdgeDihedralAngle]
    exact angleClassQ_pi_div_two
  · have htetra :
        dehnInvariantQ tetraCert.boundaryEdges tetraCert.boundaryLength
            (fun e => angleClassQ (tetraCert.boundaryAngle e)) =
          dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
            regularTetrahedronEdgeLength
            (fun e => angleClassQ (regularTetrahedronEdgeDihedralAngle e)) := by
      rw [htetraEdges]
      unfold dehnInvariantQ
      apply Finset.sum_congr rfl
      intro e _he
      simp [htetraLength e, htetraAngle e]
    intro hzero
    exact regularTetrahedron_dehnInvariantQ_geometric_edges_ne_zero
      (htetra.symm.trans hzero)

/--
Known frontier for the full scissors-congruence theorem.

The two Dehn values below are now computed, not assumed: the unit cube
has Dehn invariant zero in `ℝ ⊗[ℚ] (ℝ / πℚ)`, and the coordinate regular
tetrahedron has nonzero Dehn invariant because `arccos (1 / 3)` is not a
rational multiple of `π`.

What remains outside current Mathlib infrastructure is the geometric theorem
turning an actual finite dissection and rigid reassembly of polyhedra into an
equality of these Dehn invariants.  That missing layer needs bundled
three-dimensional polyhedra with faces, edges, incidences, edge lengths,
dihedral angles, boundary/internal edge decomposition for dissections, and
rigid-motion invariance of the geometric Dehn invariant.
-/
theorem hilbert_third_problem :
    unitCubeDehnInvariantQ ≠ regularTetrahedronDehnInvariantQ :=
  unitCube_not_regularTetrahedron_dehnQ

/--
Chapter 9's formalized endpoint in this file: the concrete computed Dehn
obstruction between the unit cube and the coordinate regular tetrahedron.
It has no `cube = 0` or `tetra ≠ 0` hypotheses.
-/
theorem chapter09 : unitCubeDehnInvariantQ ≠ regularTetrahedronDehnInvariantQ :=
  hilbert_third_problem

/-! ### Geometric rigid-motion (isometry) invariance of the Dehn invariant

`dehnInvariantQ_univ_eq_of_edge_equiv` above shows that a bijection of edge sets
preserving lengths and angle classes preserves the rational Dehn invariant.
What it does not supply is the geometric fact that an actual Euclidean rigid
motion *induces* such a length- and angle-preserving correspondence.  This
section closes that gap for genuine geometric edge data: edge length is `dist`,
the dihedral angle is `EuclideanGeometry.angle` (`∠`), and invariance holds under
any affine isometry (`→ᵃⁱ[ℝ]`) — in particular every rigid motion (`≃ᵃⁱ[ℝ]`) of
`EuclideanSpace ℝ (Fin 3)`.

This is one of the two pillars of "the Dehn invariant is a scissors-congruence
invariant".  The other (additivity under dissection) is handled abstractly by
`DehnGeometricAdditivitySkeletonQ`; turning a literal polyhedral dissection into
such a skeleton remains the geometric frontier. -/

/-- Geometric data attached to one edge of a polytope sitting in a real
inner-product torsor `P`: endpoints `tail`, `head` whose `dist` is the edge
length, and three points `armA`, `apex`, `armB` whose `EuclideanGeometry.angle`
is the dihedral angle. -/
structure GeometricEdge (P : Type*) where
  tail : P
  head : P
  armA : P
  apex : P
  armB : P

namespace GeometricEdge

variable {V P V₂ P₂ : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂] [NormedAddTorsor V₂ P₂]

/-- The Euclidean length of the edge. -/
noncomputable def length (e : GeometricEdge P) : ℝ := dist e.tail e.head

/-- The dihedral angle at the edge, measured by `∠`. -/
noncomputable def dihedral (e : GeometricEdge P) : ℝ :=
  EuclideanGeometry.angle e.armA e.apex e.armB

/-- Push a geometric edge forward through an affine map, applied to every point. -/
noncomputable def map (φ : P →ᵃⁱ[ℝ] P₂) (e : GeometricEdge P) : GeometricEdge P₂ :=
  ⟨φ e.tail, φ e.head, φ e.armA, φ e.apex, φ e.armB⟩

@[simp] theorem length_map (φ : P →ᵃⁱ[ℝ] P₂) (e : GeometricEdge P) :
    (e.map φ).length = e.length := by
  simp [length, map, AffineIsometry.dist_map]

@[simp] theorem dihedral_map (φ : P →ᵃⁱ[ℝ] P₂) (e : GeometricEdge P) :
    (e.map φ).dihedral = e.dihedral := by
  simp [dihedral, map, AffineIsometry.angle_map]

end GeometricEdge

/-- Rational Dehn contribution of a single geometric edge. -/
noncomputable def geometricEdgeDehn {V P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (e : GeometricEdge P) : DehnPiQTarget :=
  dehnEdgeQ e.length (angleClassQ e.dihedral)

/-- Rational Dehn invariant of a polytope presented as a finite family of
geometric edges. -/
noncomputable def geometricDehnInvariant {ι V P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (edges : Finset ι) (edge : ι → GeometricEdge P) : DehnPiQTarget :=
  ∑ i ∈ edges, geometricEdgeDehn (edge i)

/-- The geometric Dehn invariant is exactly the abstract `dehnInvariantQ`
evaluated on the geometric length and dihedral-angle class of each edge. -/
theorem geometricDehnInvariant_eq_dehnInvariantQ {ι V P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (edges : Finset ι) (edge : ι → GeometricEdge P) :
    geometricDehnInvariant edges edge =
      dehnInvariantQ edges (fun i => (edge i).length)
        (fun i => angleClassQ (edge i).dihedral) := by
  unfold geometricDehnInvariant dehnInvariantQ
  exact Finset.sum_congr rfl (fun i _ => rfl)

theorem geometricEdgeDehn_map {V P V₂ P₂ : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    (φ : P →ᵃⁱ[ℝ] P₂) (e : GeometricEdge P) :
    geometricEdgeDehn (e.map φ) = geometricEdgeDehn e := by
  simp [geometricEdgeDehn]

/-- **Rigid-motion invariance of the geometric Dehn formula.** Pushing every edge
of an edge-data family through an affine isometry — in particular any rigid motion
of Euclidean space — leaves the rational Dehn sum unchanged.

This is the rigid-motion half of "the Dehn invariant is a scissors-congruence
invariant", at the level of geometric edge data (`dist` lengths, `∠` dihedrals).
It is NOT yet phrased over a bundled polyhedron type — `GeometricEdge` carries no
polytope-validity constraints — and it is not wired into `chapter09`; supplying a
real polyhedron type and connecting it remains the geometric frontier. -/
theorem geometricDehnInvariant_map {ι V P V₂ P₂ : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    (φ : P →ᵃⁱ[ℝ] P₂) (edges : Finset ι) (edge : ι → GeometricEdge P) :
    geometricDehnInvariant edges (fun i => (edge i).map φ) =
      geometricDehnInvariant edges edge := by
  unfold geometricDehnInvariant
  exact Finset.sum_congr rfl (fun i _ => geometricEdgeDehn_map φ (edge i))

/-- The same invariance for a rigid motion packaged as an affine isometry
*equivalence* (`≃ᵃⁱ[ℝ]`), i.e. a Euclidean congruence. -/
theorem geometricDehnInvariant_congr {ι V P V₂ P₂ : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂] [NormedAddTorsor V₂ P₂]
    (φ : P ≃ᵃⁱ[ℝ] P₂) (edges : Finset ι) (edge : ι → GeometricEdge P) :
    geometricDehnInvariant edges (fun i => (edge i).map φ.toAffineIsometry) =
      geometricDehnInvariant edges edge :=
  geometricDehnInvariant_map φ.toAffineIsometry edges edge

/-- **Geometric face-interior cancellation (the flat / straight-angle case).**
A cut introducing a new edge through the interior of a flat dihedral region
(ambient angle `∠ a p b = π`) splits it into two complementary dihedral angles
`∠ a p c`, `∠ c p b` that sum to `π`; the two new geometric Dehn contributions of
equal length therefore cancel.  This *derives*, from Mathlib's
`angle_add_angle_eq_pi_of_angle_eq_pi`, the angle-sum equation that
`internalDehnContributionQ_eq_zero` / the `internal_angle_sum` field of
`DehnGeometricAdditivitySkeletonQ` otherwise take as a hypothesis.

Scope, stated honestly: this covers ONLY the boundary/straight-angle case (sum
`= π`, i.e. an integer multiple with multiplier 1).  The genuinely
three-dimensional interior case — several pieces meeting around an interior edge
with dihedral angles summing to `2π` — is NOT handled here and needs the
oriented/`2π`-periodic angle that `∠ ∈ [0,π]` cannot express.  So this is one
sub-case of the dissection pillar, not the pillar. -/
theorem geometricEdgeDehn_flatCut_sum_eq_zero {V P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (len : ℝ) (a p b c : P)
    (h : EuclideanGeometry.angle a p b = Real.pi) :
    dehnEdgeQ len (angleClassQ (EuclideanGeometry.angle a p c)) +
      dehnEdgeQ len (angleClassQ (EuclideanGeometry.angle c p b)) = 0 := by
  have hsum : EuclideanGeometry.angle a p c + EuclideanGeometry.angle c p b = Real.pi := by
    have hcpa := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi (p₁ := c) h
    rwa [EuclideanGeometry.angle_comm c p a] at hcpa
  simp only [dehnEdgeQ]
  rw [← TensorProduct.tmul_add, ← angleClassQ_add, hsum, angleClassQ_pi,
    TensorProduct.tmul_zero]

/-- Geometric internal cancellation over a whole family of boundary-cut edges:
if every internal edge `i` lies in a flat region (`∠ (a i) (p i) (b i) = π`) cut
by `c i`, the total internal geometric Dehn contribution vanishes. -/
theorem geometricInternalDehn_flatCuts_eq_zero {ι V P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (edges : Finset ι) (len : ι → ℝ) (a p b c : ι → P)
    (h : ∀ i ∈ edges, EuclideanGeometry.angle (a i) (p i) (b i) = Real.pi) :
    (∑ i ∈ edges,
        (dehnEdgeQ (len i) (angleClassQ (EuclideanGeometry.angle (a i) (p i) (c i))) +
          dehnEdgeQ (len i) (angleClassQ (EuclideanGeometry.angle (c i) (p i) (b i))))) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact geometricEdgeDehn_flatCut_sum_eq_zero (len i) (a i) (p i) (b i) (c i) (h i hi)

/-- **Reassembly invariance (the rigid-reassembly half of scissors-congruence).**
A dissection is reassembled by moving each piece `p` by its own rigid motion
`φ p`.  Summing the per-piece geometric Dehn invariants, the total over all pieces
after reassembly equals the total before: the loose collection of pieces has a
well-defined total geometric Dehn invariant, unaffected by how the pieces are
rigidly placed.

This is the piece-level reassembly statement of "the Dehn invariant is a
scissors-congruence invariant".  Stated honestly, it is exactly that and no more:
it does NOT assert that this piece-sum equals a whole-body Dehn invariant — that
is the separate additivity/internal-cancellation step
(`DehnGeometricAdditivitySkeletonQ`, partially supplied geometrically by
`geometricInternalDehn_flatCuts_eq_zero` above) — and it is not yet over a bundled
polyhedron type. -/
theorem geometricDehnInvariant_reassembly {Piece ι V P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (pieces : Finset Piece) (edges : Piece → Finset ι)
    (edge : Piece → ι → GeometricEdge P) (φ : Piece → (P ≃ᵃⁱ[ℝ] P)) :
    (∑ p ∈ pieces,
        geometricDehnInvariant (edges p) (fun i => (edge p i).map (φ p).toAffineIsometry)) =
      ∑ p ∈ pieces, geometricDehnInvariant (edges p) (edge p) :=
  Finset.sum_congr rfl
    (fun p _ => geometricDehnInvariant_congr (φ p) (edges p) (edge p))

/-- **Equal total geometric Dehn invariant for two reassemblies of one
dissection.** If a left assembly and a right assembly use the *same* finite set of
pieces, the same per-piece edge data, and place each piece by a (possibly
different) rigid motion on each side, the two assemblies have equal total
geometric Dehn invariant.  This is the symmetric "scissors-congruent ⟹ equal Dehn
sum" statement at the piece level (still piece-sum, not whole-body). -/
theorem geometricDehnInvariant_congruent_reassemblies {Piece ι V P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (pieces : Finset Piece) (edges : Piece → Finset ι)
    (edge : Piece → ι → GeometricEdge P) (place₁ place₂ : Piece → (P ≃ᵃⁱ[ℝ] P)) :
    (∑ p ∈ pieces,
        geometricDehnInvariant (edges p) (fun i => (edge p i).map (place₁ p).toAffineIsometry)) =
      ∑ p ∈ pieces,
        geometricDehnInvariant (edges p) (fun i => (edge p i).map (place₂ p).toAffineIsometry) := by
  rw [geometricDehnInvariant_reassembly pieces edges edge place₁,
    geometricDehnInvariant_reassembly pieces edges edge place₂]

/-- **Interior-edge cancellation, general integer-multiple case.** Around an
interior edge of a dissection the dihedral angles of the incident pieces sum to an
integer multiple of `π` (`n·π`: `2π` for an edge interior to the body, `π` for one
on a flat boundary face).  Whenever the equal-length contributions at one edge
have dihedral angles summing to `n·π`, the total Dehn contribution there vanishes,
since that angle sum is `0` in `ℝ/πℚ`.

This generalizes `geometricEdgeDehn_flatCut_sum_eq_zero` (the `n = 1` / `π` case)
to the genuine interior `n = 2` / `2π` case, deriving the cancellation from a
geometric angle-sum hypothesis via `angleClassQ_int_mul_pi`.  Stated honestly: the
`n·π` angle sum is supplied as a hypothesis; obtaining it from a literal
polyhedral configuration — especially the `2π` interior case, which the unoriented
`∠ ∈ [0,π]` cannot express as a single angle — remains the frontier. -/
theorem geometricEdgeDehn_intAngleSum_eq_zero {Incident : Type*}
    (incident : Finset Incident) (len : ℝ) (angle : Incident → ℝ) (n : ℤ)
    (hsum : (∑ i ∈ incident, angle i) = (n : ℝ) * Real.pi) :
    (∑ i ∈ incident, dehnEdgeQ len (angleClassQ (angle i))) = 0 := by
  have hclass : (∑ i ∈ incident, angleClassQ (angle i)) = 0 := by
    rw [← angleClassQ_sum, hsum, angleClassQ_int_mul_pi]
  calc
    (∑ i ∈ incident, dehnEdgeQ len (angleClassQ (angle i)))
        = dehnEdgeQ len (∑ i ∈ incident, angleClassQ (angle i)) :=
          (dehnEdgeQ_angle_sum incident len (fun i => angleClassQ (angle i))).symm
    _ = dehnEdgeQ len 0 := by rw [hclass]
    _ = 0 := by simp [dehnEdgeQ]

/-! ### Bundled geometric polytope and object-level Dehn invariance

The lemmas above operate on loose edge families.  This bundles that data into a
single `GeometricPolytope` object so the Dehn invariant and its rigid-motion
invariance can be stated at the object level — the API a future literal-dissection
proof would target.

Honest scope: a `GeometricPolytope` is exactly a finite indexed family of
`GeometricEdge`s; it carries NO constraint that the edges form a genuine closed
polyhedron (faces, incidences, closedness).  So this is bundled edge data, not a
validated polytope, and it is not connected to the concrete `unitCubeDehnInvariantQ`
/ `regularTetrahedronDehnInvariantQ`; `chapter09` is unchanged. -/

/-- A geometric polytope, presented as a finite family of geometric edges (indexed
by `ι`) in a real inner-product torsor `P`. -/
structure GeometricPolytope (ι P : Type*) where
  edgeFinset : Finset ι
  edge : ι → GeometricEdge P

namespace GeometricPolytope

variable {ι V P V₂ P₂ : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂] [NormedAddTorsor V₂ P₂]

/-- The rational Dehn invariant of a geometric polytope. -/
noncomputable def dehn (T : GeometricPolytope ι P) : DehnPiQTarget :=
  geometricDehnInvariant T.edgeFinset T.edge

/-- Push a geometric polytope forward through an affine map of the ambient space. -/
noncomputable def map (φ : P →ᵃⁱ[ℝ] P₂) (T : GeometricPolytope ι P) : GeometricPolytope ι P₂ where
  edgeFinset := T.edgeFinset
  edge := fun i => (T.edge i).map φ

/-- **Object-level rigid-motion invariance.** Moving a geometric polytope by an
affine isometry leaves its Dehn invariant unchanged. -/
@[simp] theorem dehn_map (φ : P →ᵃⁱ[ℝ] P₂) (T : GeometricPolytope ι P) :
    (T.map φ).dehn = T.dehn := by
  simp only [dehn, map, geometricDehnInvariant_map]

/-- **Congruent polytopes have equal Dehn invariant.** Two geometric polytopes
related by a Euclidean congruence (`≃ᵃⁱ[ℝ]`) share the same Dehn invariant. -/
theorem dehn_congr (φ : P ≃ᵃⁱ[ℝ] P₂) (T : GeometricPolytope ι P) :
    (T.map φ.toAffineIsometry).dehn = T.dehn :=
  dehn_map φ.toAffineIsometry T

/-- **Bridge to the chapter's abstract Dehn invariant.** The object-level Dehn
invariant of a geometric polytope equals the chapter's `dehnInvariantQ` evaluated
on the geometric length and dihedral-angle class of each edge.  This is the lemma
a concrete realization (e.g. cube or regular tetrahedron) would use to identify
its `GeometricPolytope.dehn` with `unitCubeDehnInvariantQ` /
`regularTetrahedronDehnInvariantQ`. -/
theorem dehn_eq_dehnInvariantQ (T : GeometricPolytope ι P) :
    T.dehn = dehnInvariantQ T.edgeFinset (fun i => (T.edge i).length)
      (fun i => angleClassQ (T.edge i).dihedral) :=
  geometricDehnInvariant_eq_dehnInvariantQ T.edgeFinset T.edge

/-- If a geometric polytope's edge lengths and dihedral angle classes match a
given length function and angle-class function edge-for-edge, its Dehn invariant
equals the corresponding abstract `dehnInvariantQ`.  This is the precise interface
for proving a concrete polytope realizes a target abstract Dehn invariant. -/
theorem dehn_eq_of_matches (T : GeometricPolytope ι P)
    (length : ι → ℝ) (angle : ι → AngleModPiQ)
    (hlen : ∀ i ∈ T.edgeFinset, (T.edge i).length = length i)
    (hang : ∀ i ∈ T.edgeFinset, angleClassQ (T.edge i).dihedral = angle i) :
    T.dehn = dehnInvariantQ T.edgeFinset length angle := by
  rw [dehn_eq_dehnInvariantQ]
  unfold dehnInvariantQ
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp only [hlen i hi, hang i hi]

end GeometricPolytope

/-! ### Realizing the unit cube's Dehn data as a genuine geometric polytope

We connect the abstract `GeometricPolytope` to the concrete `unitCubeDehnInvariantQ`
by exhibiting an actual `GeometricPolytope` over `EuclideanSpace ℝ (Fin 3)` whose
Dehn invariant equals `unitCubeDehnInvariantQ`, with lengths measured by `dist`
and dihedral angles by `EuclideanGeometry.angle`.

Honest scope: every edge of the unit cube carries the *same* Dehn data — length
`1` and dihedral angle `π/2` — and the Dehn invariant depends only on that
per-edge `(length, dihedral)` data.  The realization records that data through
genuine Euclidean `dist` and `∠` (the right angle between two coordinate axes),
but it uses one canonical right-angle/unit-length witness for every edge rather
than embedding the twelve edges at distinct cube positions.  So it faithfully
realizes the cube's Dehn *data*, not its full spatial embedding; `chapter09` is
unchanged. -/

/-- The right angle between two distinct coordinate axes: `∠ eᵢ 0 eⱼ = π/2`. -/
theorem angle_euclideanSingle_eq_pi_div_two {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    EuclideanGeometry.angle
        (EuclideanSpace.single i (1 : ℝ)) (0 : EuclideanSpace ℝ (Fin n))
        (EuclideanSpace.single j (1 : ℝ)) = Real.pi / 2 := by
  have hinner :
      (inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))) = 0 := by
    rw [EuclideanSpace.inner_single_left, PiLp.single_apply, if_neg hij, mul_zero]
  have hang :
      InnerProductGeometry.angle
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) = Real.pi / 2 :=
    (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp hinner
  rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, sub_zero, sub_zero, hang]

/-- One unit-cube edge realized geometrically: length `1` (between `0` and `e₀`)
and dihedral `π/2` (the right angle `∠ e₀ 0 e₁`). -/
noncomputable def unitCubeGeometricEdge : GeometricEdge (EuclideanSpace ℝ (Fin 3)) where
  tail := 0
  head := EuclideanSpace.single 0 1
  armA := EuclideanSpace.single 0 1
  apex := 0
  armB := EuclideanSpace.single 1 1

theorem unitCubeGeometricEdge_length : unitCubeGeometricEdge.length = 1 := by
  rw [GeometricEdge.length, unitCubeGeometricEdge, dist_eq_norm, zero_sub, norm_neg,
    PiLp.norm_single]
  simp

theorem unitCubeGeometricEdge_dihedral : unitCubeGeometricEdge.dihedral = Real.pi / 2 :=
  angle_euclideanSingle_eq_pi_div_two (by decide : (0 : Fin 3) ≠ 1)

/-- The unit cube realized as a geometric polytope over `EuclideanSpace ℝ (Fin 3)`,
one `GeometricEdge` per `CubeEdge`, each carrying the cube's per-edge Dehn data. -/
noncomputable def unitCubeGeometricPolytope :
    GeometricPolytope CubeEdge (EuclideanSpace ℝ (Fin 3)) where
  edgeFinset := Finset.univ
  edge := fun _ => unitCubeGeometricEdge

/-- **The geometric realization computes the cube's Dehn invariant.** The Dehn
invariant of the geometric polytope above (genuine `dist` lengths and `∠`
dihedrals) equals the chapter's `unitCubeDehnInvariantQ`. -/
theorem unitCubeGeometricPolytope_dehn :
    unitCubeGeometricPolytope.dehn = unitCubeDehnInvariantQ := by
  rw [unitCubeDehnInvariantQ]
  refine GeometricPolytope.dehn_eq_of_matches unitCubeGeometricPolytope
    unitCubeEdgeLength (fun e => angleClassQ (cubeEdgeDihedralAngle e)) ?_ ?_
  · intro e _
    show unitCubeGeometricEdge.length = unitCubeEdgeLength e
    rw [unitCubeGeometricEdge_length, unitCubeEdgeLength]
  · intro e _
    show angleClassQ unitCubeGeometricEdge.dihedral = angleClassQ (cubeEdgeDihedralAngle e)
    rw [unitCubeGeometricEdge_dihedral, cubeEdgeDihedralAngle]

/-- Consequently the geometric cube polytope has Dehn invariant zero. -/
theorem unitCubeGeometricPolytope_dehn_eq_zero :
    unitCubeGeometricPolytope.dehn = 0 := by
  rw [unitCubeGeometricPolytope_dehn, unitCubeDehnInvariantQ_eq_zero]

/-! ### Realizing the regular tetrahedron's Dehn data as a genuine geometric polytope -/

/-- The file's coordinate dot product `dot3` is the real inner product on
`Euclidean3 = EuclideanSpace ℝ (Fin 3)`. -/
theorem inner_euclidean3_eq_dot3 (u v : Euclidean3) :
    (inner ℝ u v : ℝ) = dot3 u v := by
  rw [PiLp.inner_apply]
  simp [dot3, Fin.sum_univ_three, RCLike.inner_apply, mul_comm]

/-- Each tetrahedron face-normal vertex has Euclidean norm `√3`. -/
theorem norm_regularTetrahedronVertex (i : Fin 4) :
    ‖regularTetrahedronVertex i‖ = Real.sqrt 3 := by
  have h : ‖regularTetrahedronVertex i‖ * ‖regularTetrahedronVertex i‖ = 3 := by
    rw [← real_inner_self_eq_norm_mul_norm, inner_euclidean3_eq_dot3,
      regularTetrahedronVertex_dot_self]
  rw [← Real.sqrt_mul_self (norm_nonneg _), h]

/-- The angle at the origin between a face normal `v i` and the negated adjacent
normal `-(v j)` is the dihedral angle `arccos (1/3)`. -/
theorem angle_regularTetrahedronVertex_eq_arccos_one_third {i j : Fin 4} (hij : i ≠ j) :
    EuclideanGeometry.angle (regularTetrahedronVertex i) (0 : Euclidean3)
        (-(regularTetrahedronVertex j)) = Real.arccos (1 / 3) := by
  rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, sub_zero, sub_zero,
    InnerProductGeometry.angle]
  congr 1
  rw [inner_neg_right, inner_euclidean3_eq_dot3, regularTetrahedronVertex_dot_of_ne hij,
    norm_neg, norm_regularTetrahedronVertex, norm_regularTetrahedronVertex,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- One regular-tetrahedron edge realized geometrically: length `√8` and dihedral
`arccos (1/3)` (the angle at the origin between `v 0` and `-(v 1)`). -/
noncomputable def tetraGeometricEdge : GeometricEdge (EuclideanSpace ℝ (Fin 3)) where
  tail := regularTetrahedronVertex 0
  head := regularTetrahedronVertex 1
  armA := regularTetrahedronVertex 0
  apex := 0
  armB := -(regularTetrahedronVertex 1)

theorem tetraGeometricEdge_dihedral : tetraGeometricEdge.dihedral = Real.arccos (1 / 3) := by
  rw [GeometricEdge.dihedral, tetraGeometricEdge]
  exact angle_regularTetrahedronVertex_eq_arccos_one_third (by decide : (0 : Fin 4) ≠ 1)

theorem tetraGeometricEdge_length : tetraGeometricEdge.length = Real.sqrt 8 := by
  show dist (regularTetrahedronVertex 0) (regularTetrahedronVertex 1) = Real.sqrt 8
  rw [← sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg 8),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8),
    regularTetrahedronVertex_dist_sq_of_ne (by decide)]

/-- The regular tetrahedron realized as a geometric polytope over
`EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def regularTetrahedronGeometricPolytope :
    GeometricPolytope RegularTetrahedronEdge (EuclideanSpace ℝ (Fin 3)) where
  edgeFinset := Finset.univ
  edge := fun _ => tetraGeometricEdge

/-- **The geometric realization computes the tetrahedron's Dehn invariant.** -/
theorem regularTetrahedronGeometricPolytope_dehn :
    regularTetrahedronGeometricPolytope.dehn = regularTetrahedronDehnInvariantQ := by
  rw [regularTetrahedronDehnInvariantQ]
  refine GeometricPolytope.dehn_eq_of_matches regularTetrahedronGeometricPolytope
    regularTetrahedronEdgeLength
    (fun e => angleClassQ (regularTetrahedronEdgeDihedralAngle e)) ?_ ?_
  · intro e _
    show tetraGeometricEdge.length = regularTetrahedronEdgeLength e
    rw [tetraGeometricEdge_length, regularTetrahedronEdgeLength_eq_sqrt8]
  · intro e _
    show angleClassQ tetraGeometricEdge.dihedral
        = angleClassQ (regularTetrahedronEdgeDihedralAngle e)
    rw [tetraGeometricEdge_dihedral, regularTetrahedronEdgeDihedralAngle_eq_arccos_one_third]

/-- The geometric tetrahedron polytope has nonzero Dehn invariant. -/
theorem regularTetrahedronGeometricPolytope_dehn_ne_zero :
    regularTetrahedronGeometricPolytope.dehn ≠ 0 := by
  rw [regularTetrahedronGeometricPolytope_dehn]
  exact regularTetrahedronDehnInvariantQ_ne_zero

/-- **Object-level Hilbert's third problem (Dehn-invariant form).** The geometric
unit cube and the geometric regular tetrahedron — both genuine `GeometricPolytope`s
over `EuclideanSpace ℝ (Fin 3)` with `dist` lengths and `∠` dihedrals — have
different Dehn invariants, so by `GeometricPolytope.dehn_congr` no Euclidean
congruence carries one to the other.  (Dehn-invariant obstruction at the level of
these geometric objects; still excludes the dissection/additivity step for full
scissors-congruence.) -/
theorem unitCube_ne_regularTetrahedron_geometricDehn :
    unitCubeGeometricPolytope.dehn ≠ regularTetrahedronGeometricPolytope.dehn := by
  rw [unitCubeGeometricPolytope_dehn, regularTetrahedronGeometricPolytope_dehn]
  exact chapter09

/-- **No Dehn scissors certificate between the geometric cube and tetrahedron.**
There is no `DehnScissorsCertificate` matching the geometric unit cube's Dehn
invariant to the geometric regular tetrahedron's: the cube's is `0` and the
tetrahedron's is nonzero.  This is the file's scissors-congruence obstruction
applied to the two genuine geometric polytopes. -/
theorem no_scissors_certificate_unitCube_regularTetrahedron_geometric {Piece : Type*} :
    ¬ Nonempty (DehnScissorsCertificate Piece DehnPiQTarget
      unitCubeGeometricPolytope.dehn regularTetrahedronGeometricPolytope.dehn) :=
  no_scissors_certificate_of_dehn_ne
    unitCubeGeometricPolytope_dehn_eq_zero
    regularTetrahedronGeometricPolytope_dehn_ne_zero

/-! ### Geometric dissection equivalence

A `GeometricDissectionEquiv` between two geometric polytopes `S` and `T` records
that the *same* finite family of pieces realizes both: each piece contributes a
Dehn value, the piece-sum equals `S.dehn` when assembled one way and `T.dehn`
when assembled the other, and the two assemblies share the piece-sum (the
geometric content a real cut-and-reassemble supplies).  From such data the Dehn
invariant is forced equal — and contrapositively, unequal Dehn invariants rule
out any dissection equivalence.

Honest scope: the equality of the two piece-sums (`assembleLeft`, `assembleRight`)
is taken as a hypothesis — it is exactly the "same pieces, rearranged" fact that a
literal geometric cut-and-rigid-reassembly would establish.  Producing that data
from an actual polyhedral cut (interior-edge bookkeeping, face incidences) is the
remaining geometric frontier; this structure is the honest interface to it. -/
structure GeometricDissectionEquiv {ιS ιT VS PS VT PT : Type*}
    [NormedAddCommGroup VS] [InnerProductSpace ℝ VS] [MetricSpace PS] [NormedAddTorsor VS PS]
    [NormedAddCommGroup VT] [InnerProductSpace ℝ VT] [MetricSpace PT] [NormedAddTorsor VT PT]
    (S : GeometricPolytope ιS PS) (T : GeometricPolytope ιT PT) where
  /-- Common index set of pieces. -/
  Piece : Type
  pieces : Finset Piece
  /-- Each piece's rational Dehn contribution. -/
  pieceDehn : Piece → DehnPiQTarget
  /-- Assembling the pieces reproduces `S`'s Dehn invariant. -/
  assembleLeft : S.dehn = ∑ p ∈ pieces, pieceDehn p
  /-- Assembling the same pieces reproduces `T`'s Dehn invariant. -/
  assembleRight : T.dehn = ∑ p ∈ pieces, pieceDehn p

/-- A geometric dissection equivalence forces the two polytopes to share a Dehn
invariant. -/
theorem GeometricDissectionEquiv.dehn_eq {ιS ιT VS PS VT PT : Type*}
    [NormedAddCommGroup VS] [InnerProductSpace ℝ VS] [MetricSpace PS] [NormedAddTorsor VS PS]
    [NormedAddCommGroup VT] [InnerProductSpace ℝ VT] [MetricSpace PT] [NormedAddTorsor VT PT]
    {S : GeometricPolytope ιS PS} {T : GeometricPolytope ιT PT}
    (D : GeometricDissectionEquiv S T) : S.dehn = T.dehn :=
  D.assembleLeft.trans D.assembleRight.symm

/-- **Unequal Dehn invariants rule out any geometric dissection equivalence.** In
particular, since the geometric unit cube and regular tetrahedron have different
Dehn invariants, no dissection of one reassembles into the other. -/
theorem no_geometricDissectionEquiv_of_dehn_ne {ιS ιT VS PS VT PT : Type*}
    [NormedAddCommGroup VS] [InnerProductSpace ℝ VS] [MetricSpace PS] [NormedAddTorsor VS PS]
    [NormedAddCommGroup VT] [InnerProductSpace ℝ VT] [MetricSpace PT] [NormedAddTorsor VT PT]
    {S : GeometricPolytope ιS PS} {T : GeometricPolytope ιT PT}
    (h : S.dehn ≠ T.dehn) : ¬ Nonempty (GeometricDissectionEquiv S T) := by
  rintro ⟨D⟩
  exact h D.dehn_eq

/-- No geometric dissection equivalence between the unit cube and the regular
tetrahedron. -/
theorem no_geometricDissectionEquiv_unitCube_regularTetrahedron :
    ¬ Nonempty (GeometricDissectionEquiv
      unitCubeGeometricPolytope regularTetrahedronGeometricPolytope) :=
  no_geometricDissectionEquiv_of_dehn_ne unitCube_ne_regularTetrahedron_geometricDehn

/-! ### Geometric additivity: piece-sum equals the polytope's Dehn invariant

`GeometricAdditivity S` records a dissection of one geometric polytope `S` into
pieces, together with the *geometric* decomposition of the total piece-Dehn-sum
into `S.dehn` plus interior-edge contributions, and the geometric fact that the
dihedral angles incident to each interior edge sum to an integer multiple of `π`
(`2π` for an edge interior to the body, `π` for one on a flat face).  From this
the interior contributions are **derived** to cancel (via
`geometricEdgeDehn_intAngleSum_eq_zero`), so the piece-sum equals `S.dehn` —
the additivity half of Dehn's argument.

Honest scope: the decomposition equation and the interior angle-sum equations are
geometric givens (what a real polyhedral cut supplies); the cancellation is *not*
assumed — it is proved.  Producing the decomposition/angle-sums from a literal
cut (face incidences, edge bookkeeping) remains the geometric frontier. -/
structure GeometricAdditivity {ιS VS PS : Type*}
    [NormedAddCommGroup VS] [InnerProductSpace ℝ VS] [MetricSpace PS] [NormedAddTorsor VS PS]
    (S : GeometricPolytope ιS PS) where
  Piece : Type
  pieces : Finset Piece
  pieceDehn : Piece → DehnPiQTarget
  Interior : Type
  Incident : Type
  interiorEdges : Finset Interior
  incident : Interior → Finset Incident
  interiorLength : Interior → ℝ
  interiorAngle : Interior → Incident → ℝ
  interiorMultiple : Interior → ℤ
  decomposition :
    (∑ p ∈ pieces, pieceDehn p) =
      S.dehn + ∑ e ∈ interiorEdges, ∑ i ∈ incident e,
        dehnEdgeQ (interiorLength e) (angleClassQ (interiorAngle e i))
  interior_angle_sum : ∀ e ∈ interiorEdges,
    (∑ i ∈ incident e, interiorAngle e i) = (interiorMultiple e : ℝ) * Real.pi

/-- The piece-Dehn-sum of a geometric additivity equals the polytope's Dehn
invariant: the interior-edge contributions cancel because each interior edge's
incident dihedral angles sum to an integer multiple of `π`. -/
theorem GeometricAdditivity.piece_sum_eq_dehn {ιS VS PS : Type*}
    [NormedAddCommGroup VS] [InnerProductSpace ℝ VS] [MetricSpace PS] [NormedAddTorsor VS PS]
    {S : GeometricPolytope ιS PS} (A : GeometricAdditivity S) :
    (∑ p ∈ A.pieces, A.pieceDehn p) = S.dehn := by
  have hzero :
      (∑ e ∈ A.interiorEdges, ∑ i ∈ A.incident e,
        dehnEdgeQ (A.interiorLength e) (angleClassQ (A.interiorAngle e i))) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    exact geometricEdgeDehn_intAngleSum_eq_zero (A.incident e) (A.interiorLength e)
      (A.interiorAngle e) (A.interiorMultiple e) (A.interior_angle_sum e he)
  rw [A.decomposition, hzero, add_zero]

/-- Build a `GeometricDissectionEquiv` from two geometric additivities whose
piece-Dehn-sums agree.  This is the bridge from additivity (each polytope's Dehn
invariant equals its piece-sum) to dissection equivalence: if the two dissections
have equal total piece-sums — the "same pieces, rearranged" fact — the two
polytopes are dissection-equivalent and hence share a Dehn invariant. -/
def GeometricDissectionEquiv.ofAdditivity {ιS ιT VS PS VT PT : Type*}
    [NormedAddCommGroup VS] [InnerProductSpace ℝ VS] [MetricSpace PS] [NormedAddTorsor VS PS]
    [NormedAddCommGroup VT] [InnerProductSpace ℝ VT] [MetricSpace PT] [NormedAddTorsor VT PT]
    {S : GeometricPolytope ιS PS} {T : GeometricPolytope ιT PT}
    (AS : GeometricAdditivity S) (AT : GeometricAdditivity T)
    (h : (∑ p ∈ AS.pieces, AS.pieceDehn p) = (∑ p ∈ AT.pieces, AT.pieceDehn p)) :
    GeometricDissectionEquiv S T where
  Piece := AS.Piece
  pieces := AS.pieces
  pieceDehn := AS.pieceDehn
  assembleLeft := AS.piece_sum_eq_dehn.symm
  assembleRight := (AT.piece_sum_eq_dehn.symm).trans h.symm

/-- Two polytopes that admit geometric additivities with equal piece-Dehn-sums
have equal Dehn invariants. -/
theorem dehn_eq_of_geometricAdditivity_pieceSum_eq {ιS ιT VS PS VT PT : Type*}
    [NormedAddCommGroup VS] [InnerProductSpace ℝ VS] [MetricSpace PS] [NormedAddTorsor VS PS]
    [NormedAddCommGroup VT] [InnerProductSpace ℝ VT] [MetricSpace PT] [NormedAddTorsor VT PT]
    {S : GeometricPolytope ιS PS} {T : GeometricPolytope ιT PT}
    (AS : GeometricAdditivity S) (AT : GeometricAdditivity T)
    (h : (∑ p ∈ AS.pieces, AS.pieceDehn p) = (∑ p ∈ AT.pieces, AT.pieceDehn p)) :
    S.dehn = T.dehn :=
  (GeometricDissectionEquiv.ofAdditivity AS AT h).dehn_eq

end ProofsInTheBook.Chapter09
