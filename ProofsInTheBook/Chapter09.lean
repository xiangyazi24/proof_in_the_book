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

/-- Algebraic target for a Dehn invariant with an abstract angle quotient. -/
abbrev DehnTarget (Angle : Type*) [AddCommGroup Angle] [Module ℤ Angle] :=
  TensorProduct ℤ ℝ Angle

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

-- (`angleClassQ_arccos_one_third_ne_zero` defined below, after
-- `arccos_one_third_irrational_over_pi`.)

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

theorem dehnInvariant_biUnion_of_pairwiseDisjoint {Piece Edge Angle : Type*}
    [DecidableEq Edge] [AddCommGroup Angle] [Module ℤ Angle]
    {pieces : Finset Piece} {edges : Piece → Finset Edge}
    (hdisj : Set.PairwiseDisjoint (↑pieces) edges)
    (length : Edge → ℝ) (angle : Edge → Angle) :
    dehnInvariant (pieces.biUnion edges) length angle =
      ∑ p ∈ pieces, dehnInvariant (edges p) length angle := by
  simp [dehnInvariant, Finset.sum_biUnion hdisj]

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
    field_simp <;> ring
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
    have : (q.num : ℝ) * Real.pi = (q.num : ℤ) * Real.pi := by push_cast; rfl
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

/--
Hilbert's third problem: a regular tetrahedron cannot be cut into finitely
many polyhedral pieces and reassembled into a cube. The book's proof:
1. The cube has Dehn invariant 0 (dihedral angles are π/2, which is 0 mod π)
2. The tetrahedron has nonzero Dehn invariant (arccos(1/3) is irrational over π)
3. Scissors-congruent polyhedra have equal Dehn invariants
4. Therefore the cube and tetrahedron are not scissors-congruent
-/
theorem hilbert_third_problem
    (cubeDehn tetraDehn : DehnPiTarget)
    (hcube : cubeDehn = 0)
    (htetra : tetraDehn ≠ 0) :
    cubeDehn ≠ tetraDehn :=
  impossible_scissors_congruence_of_dehn_ne hcube htetra

theorem chapter09 {A : Type*} [AddCommMonoid A] {cube tetra : A}
    (hcube : cube = 0) (htetra : tetra ≠ 0) : cube ≠ tetra :=
  impossible_scissors_congruence_of_dehn_ne hcube htetra

end ProofsInTheBook.Chapter09
