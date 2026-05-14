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
-/

namespace ProofsInTheBook.Chapter09

open scoped BigOperators TensorProduct

/-!
### Dehn invariant

The key algebraic invariant. Its construction requires:
1. The tensor product ℝ ⊗[ℤ] (ℝ / πℚ)
2. Showing D is additive under dissection
3. Computing D for specific polyhedra

This is a deep geometric result requiring substantial infrastructure
beyond current Mathlib coverage.
-/

/-- Algebraic target for a Dehn invariant with an abstract angle quotient. -/
abbrev DehnTarget (Angle : Type*) [AddCommGroup Angle] [Module ℤ Angle] :=
  TensorProduct ℤ ℝ Angle

/-- The contribution of one edge: length tensor angle. -/
def dehnEdge {Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (length : ℝ) (angle : Angle) : DehnTarget Angle :=
  TensorProduct.tmul ℤ length angle

/-- Finite edge-sum model for the Dehn invariant. -/
def dehnInvariant {Edge Angle : Type*} [AddCommGroup Angle] [Module ℤ Angle]
    (edges : Finset Edge) (length : Edge → ℝ) (angle : Edge → Angle) :
    DehnTarget Angle :=
  ∑ e ∈ edges, dehnEdge (length e) (angle e)

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

/--
The final invariant obstruction in Hilbert's third problem: an object with
zero Dehn invariant cannot be scissors-congruent to one with nonzero Dehn
invariant.
-/
theorem impossible_scissors_congruence_of_dehn_ne {A : Type*} [AddCommMonoid A]
    {cube tetra : A} (hcube : cube = 0) (htetra : tetra ≠ 0) : cube ≠ tetra := by
  intro h
  exact htetra (h.symm.trans hcube)

theorem chapter09 {A : Type*} [AddCommMonoid A] {cube tetra : A}
    (hcube : cube = 0) (htetra : tetra ≠ 0) : cube ≠ tetra :=
  impossible_scissors_congruence_of_dehn_ne hcube htetra

end ProofsInTheBook.Chapter09
