import Mathlib

/-!
# Chapter 30: Lattice paths and determinants

From "Proofs from THE BOOK":

**Lindström-Gessel-Viennot lemma**: The number of non-intersecting
lattice path systems from sources to sinks equals a determinant.

The book applies this to count standard Young tableaux and proves
the hook length formula: |SYT(λ)| = n! / ∏ hook_lengths.
-/

namespace ProofsInTheBook.Chapter30

open Matrix BigOperators

/--
The determinant expansion over signed permutations, the algebraic starting
point of the Lindström-Gessel-Viennot cancellation argument.
-/
theorem det_eq_sum_signed_permutations {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] (M : Matrix ι ι R) :
    M.det = ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, M (σ i) i := by
  exact Matrix.det_apply M

/--
The diagonal case of the Lindström-Gessel-Viennot determinant: when the
path-counting matrix has no off-diagonal contributions, the determinant
has only the identity permutation term.
-/
theorem det_eq_diag_product_of_offdiag_zero {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] (M : Matrix ι ι R)
    (hzero : ∀ i j, i ≠ j → M i j = 0) :
    M.det = ∏ i, M i i := by
  have hM : M = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij, hzero i j hij]
  rw [hM]
  simp

/--
Finite sign-reversing reindexing lemma.

In an arbitrary additive group this gives `S = -S`, not necessarily `S = 0`
unless the target has no `2`-torsion.
-/
theorem sum_eq_neg_self_of_sign_reversing_equiv {α R : Type*} [Fintype α]
    [AddCommGroup R] (τ : α ≃ α) (w : α → R) (hw : ∀ x, w (τ x) = -w x) :
    (∑ x : α, w x) = -∑ x : α, w x := by
  classical
  have hreindex : (∑ x : α, w (τ x)) = ∑ x : α, w x := by
    simpa using
      (Fintype.sum_equiv τ
        (fun x : α => w (τ x))
        (fun y : α => w y)
        (by intro x; rfl))
  calc
    (∑ x : α, w x) = ∑ x : α, w (τ x) := hreindex.symm
    _ = ∑ x : α, -w x := by simp [hw]
    _ = -∑ x : α, w x := by simp

/-- A sign-reversing involution makes the total signed sum `2`-torsion. -/
theorem two_nsmul_sum_eq_zero_of_sign_reversing_equiv {α R : Type*} [Fintype α]
    [AddCommGroup R] (τ : α ≃ α) (w : α → R) (hw : ∀ x, w (τ x) = -w x) :
    (2 : ℕ) • (∑ x : α, w x) = 0 := by
  classical
  let S : R := ∑ x : α, w x
  have h : S = -S := by
    simpa [S] using sum_eq_neg_self_of_sign_reversing_equiv τ w hw
  change (2 : ℕ) • S = 0
  rw [two_nsmul]
  nth_rewrite 1 [h]
  exact neg_add_cancel S

/-- A sign-reversing involution cancels the sum in an additive torsion-free target. -/
theorem sum_eq_zero_of_sign_reversing_equiv {α R : Type*} [Fintype α]
    [AddCommGroup R] [IsAddTorsionFree R] (τ : α ≃ α) (w : α → R)
    (hw : ∀ x, w (τ x) = -w x) :
    (∑ x : α, w x) = 0 := by
  classical
  have h2 := two_nsmul_sum_eq_zero_of_sign_reversing_equiv τ w hw
  rcases (nsmul_eq_zero_iff.mp h2) with hsum | htwo
  · exact hsum
  · norm_num at htwo

/--
LGV split layer: if the bad finite subfamily cancels by a sign-reversing
equivalence, then the total signed sum is the contribution from the good
subfamily.
-/
theorem total_sum_eq_good_sum_of_bad_sign_reversing {α R : Type*} [Fintype α]
    [DecidableEq α] [AddCommGroup R] [IsAddTorsionFree R]
    (bad : α → Prop) [DecidablePred bad] (τbad : {x : α // bad x} ≃ {x : α // bad x})
    (w : α → R) (hw : ∀ x : {x : α // bad x}, w (τbad x).1 = -w x.1) :
    (∑ x : α, w x) = ∑ x ∈ (Finset.univ.filter fun x : α => ¬ bad x), w x := by
  classical
  let badSet : Finset α := Finset.univ.filter fun x : α => bad x
  let goodSet : Finset α := Finset.univ.filter fun x : α => ¬ bad x
  have hbad_sum : (∑ x ∈ badSet, w x) = 0 := by
    let wbad : {x : α // bad x} → R := fun x => w x.1
    have hwbad : ∀ x : {x : α // bad x}, wbad (τbad x) = -wbad x := by
      intro x
      exact hw x
    have h := sum_eq_zero_of_sign_reversing_equiv τbad wbad hwbad
    have hfilter : (∑ x ∈ badSet, w x) = ∑ x : {x : α // bad x}, wbad x := by
      rw [← Finset.sum_subtype]
      simp [badSet]
    rw [hfilter, h]
  have huniv : (Finset.univ : Finset α) = badSet ∪ goodSet := by
    ext x
    by_cases hx : bad x <;> simp [badSet, goodSet, hx]
  have hdisj : Disjoint badSet goodSet := by
    rw [Finset.disjoint_left]
    intro x hxbad hxgood
    simp [badSet] at hxbad
    simp [goodSet, hxbad] at hxgood
  calc
    (∑ x : α, w x) = ∑ x ∈ (Finset.univ : Finset α), w x := by simp
    _ = ∑ x ∈ badSet ∪ goodSet, w x := by rw [huniv]
    _ = (∑ x ∈ badSet, w x) + ∑ x ∈ goodSet, w x := by
      rw [Finset.sum_union hdisj]
    _ = ∑ x ∈ goodSet, w x := by rw [hbad_sum, zero_add]
    _ = ∑ x ∈ (Finset.univ.filter fun x : α => ¬ bad x), w x := rfl

theorem chapter30 {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] (M : Matrix ι ι R)
    (hzero : ∀ i j, i ≠ j → M i j = 0) :
    M.det = ∏ i, M i i :=
  det_eq_diag_product_of_offdiag_zero M hzero

end ProofsInTheBook.Chapter30
