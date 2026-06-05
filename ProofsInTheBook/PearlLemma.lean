/-
The abstract Pearl Lemma (Chapter 9, book page 55).

Given finitely many "segments" with positive real lengths and finitely many
balance constraints — pairs of segment sets whose total lengths agree (the
book's "each edge of a piece `P_k` decomposes into the same total as the
corresponding edge of `Q_k`", plus the extra balance constraints used for
equicomplementability) — there is a positive *integer* weighting (a number of
"pearls" per segment) satisfying the same balance constraints.

This is exactly the Cone Lemma (`ProofsInTheBook.cone_lemma`) applied to the
incidence matrix of the constraint system, with the real lengths as the
positive real solution.
-/
import ProofsInTheBook.ConeLemma

namespace ProofsInTheBook

open scoped BigOperators

namespace PearlLemma

variable {N : ℕ}

/-- The `±1/0` incidence matrix of a finite family of balance constraints:
row `p` demands that the weights over `p.1` and over `p.2` have equal sums. -/
noncomputable def constraintMatrix
    (pairs : Finset (Finset (Fin N) × Finset (Fin N)))
    (r : pairs) (i : Fin N) : ℚ :=
  (if i ∈ (r : Finset (Fin N) × Finset (Fin N)).1 then (1 : ℚ) else 0)
    - (if i ∈ (r : Finset (Fin N) × Finset (Fin N)).2 then (1 : ℚ) else 0)

lemma constraintMatrix_row_mulVec
    (pairs : Finset (Finset (Fin N) × Finset (Fin N)))
    (r : pairs) (w : Fin N → ℚ) :
    (∑ i, constraintMatrix pairs r i * w i)
      = (∑ i ∈ (r : Finset (Fin N) × Finset (Fin N)).1, w i)
        - ∑ i ∈ (r : Finset (Fin N) × Finset (Fin N)).2, w i := by
  classical
  have h :
      ∀ i, constraintMatrix pairs r i * w i
        = (if i ∈ (r : Finset (Fin N) × Finset (Fin N)).1 then w i else 0)
          - (if i ∈ (r : Finset (Fin N) × Finset (Fin N)).2 then w i else 0) := by
    intro i
    by_cases h1 : i ∈ (r : Finset (Fin N) × Finset (Fin N)).1 <;>
      by_cases h2 : i ∈ (r : Finset (Fin N) × Finset (Fin N)).2 <;>
        simp [constraintMatrix, h1, h2]
  calc
    (∑ i, constraintMatrix pairs r i * w i)
        = ∑ i, ((if i ∈ (r : Finset (Fin N) × Finset (Fin N)).1 then w i else 0)
            - if i ∈ (r : Finset (Fin N) × Finset (Fin N)).2 then w i else 0) := by
          exact Finset.sum_congr rfl fun i _ => h i
    _ = (∑ i, if i ∈ (r : Finset (Fin N) × Finset (Fin N)).1 then w i else 0)
          - ∑ i, if i ∈ (r : Finset (Fin N) × Finset (Fin N)).2 then w i else 0 := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ i ∈ (r : Finset (Fin N) × Finset (Fin N)).1, w i)
          - ∑ i ∈ (r : Finset (Fin N) × Finset (Fin N)).2, w i := by
          rw [Finset.sum_ite_mem, Finset.sum_ite_mem]
          simp

/-- Same computation over `ℝ` for the real-length solution. -/
lemma constraintMatrix_row_mulVec_real
    (pairs : Finset (Finset (Fin N) × Finset (Fin N)))
    (r : pairs) (w : Fin N → ℝ) :
    (∑ i, ((constraintMatrix pairs r i : ℚ) : ℝ) * w i)
      = (∑ i ∈ (r : Finset (Fin N) × Finset (Fin N)).1, w i)
        - ∑ i ∈ (r : Finset (Fin N) × Finset (Fin N)).2, w i := by
  classical
  have h :
      ∀ i, ((constraintMatrix pairs r i : ℚ) : ℝ) * w i
        = (if i ∈ (r : Finset (Fin N) × Finset (Fin N)).1 then w i else 0)
          - (if i ∈ (r : Finset (Fin N) × Finset (Fin N)).2 then w i else 0) := by
    intro i
    by_cases h1 : i ∈ (r : Finset (Fin N) × Finset (Fin N)).1 <;>
      by_cases h2 : i ∈ (r : Finset (Fin N) × Finset (Fin N)).2 <;>
        simp [constraintMatrix, h1, h2]
  calc
    (∑ i, ((constraintMatrix pairs r i : ℚ) : ℝ) * w i)
        = ∑ i, ((if i ∈ (r : Finset (Fin N) × Finset (Fin N)).1 then w i else 0)
            - if i ∈ (r : Finset (Fin N) × Finset (Fin N)).2 then w i else 0) := by
          exact Finset.sum_congr rfl fun i _ => h i
    _ = (∑ i, if i ∈ (r : Finset (Fin N) × Finset (Fin N)).1 then w i else 0)
          - ∑ i, if i ∈ (r : Finset (Fin N) × Finset (Fin N)).2 then w i else 0 := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ i ∈ (r : Finset (Fin N) × Finset (Fin N)).1, w i)
          - ∑ i ∈ (r : Finset (Fin N) × Finset (Fin N)).2, w i := by
          rw [Finset.sum_ite_mem, Finset.sum_ite_mem]
          simp

end PearlLemma

open PearlLemma in
/--
**The Pearl Lemma** (abstract form).  If positive real lengths satisfy all the
balance constraints, then there is a positive integer pearl assignment
satisfying the same constraints.
-/
theorem pearl_lemma {N : ℕ}
    (pairs : Finset (Finset (Fin N) × Finset (Fin N)))
    (len : Fin N → ℝ) (hlen : ∀ i, 0 < len i)
    (hbal : ∀ p ∈ pairs,
      (∑ i ∈ p.1, len i) = ∑ i ∈ p.2, len i) :
    ∃ m : Fin N → ℤ, (∀ i, 0 < m i) ∧
      ∀ p ∈ pairs, (∑ i ∈ p.1, m i) = ∑ i ∈ p.2, m i := by
  classical
  -- re-index the rows by `Fin pairs.card`
  let e : Fin pairs.card ≃ pairs := (pairs.equivFin).symm
  let A : Matrix (Fin pairs.card) (Fin N) ℚ :=
    fun r i => constraintMatrix pairs (e r) i
  have hsol : (A.map ((↑) : ℚ → ℝ)).mulVec len = 0 := by
    funext r
    have := constraintMatrix_row_mulVec_real pairs (e r) len
    have hzero :
        (∑ i ∈ ((e r : Finset (Fin N) × Finset (Fin N))).1, len i)
          - ∑ i ∈ ((e r : Finset (Fin N) × Finset (Fin N))).2, len i = 0 := by
      have hb := hbal _ (e r).2
      linarith [hb]
    simpa [Matrix.mulVec, Matrix.map, dotProduct, A, this] using
      this.trans hzero
  obtain ⟨z, hzpos, hzker⟩ := cone_lemma A len hsol hlen
  refine ⟨z, hzpos, ?_⟩
  intro p hp
  -- read the row equation for `p` back out of the kernel identity
  have hrow := congrFun hzker (e.symm ⟨p, hp⟩)
  have hq :
      (∑ i ∈ p.1, (z i : ℚ)) - ∑ i ∈ p.2, (z i : ℚ) = 0 := by
    have hcalc := constraintMatrix_row_mulVec pairs ⟨p, hp⟩ (fun i => (z i : ℚ))
    have hAe : A (e.symm ⟨p, hp⟩) = constraintMatrix pairs ⟨p, hp⟩ := by
      have : e (e.symm ⟨p, hp⟩) = ⟨p, hp⟩ := e.apply_symm_apply _
      simp [A, this]
    have hmv :
        (∑ i, A (e.symm ⟨p, hp⟩) i * (z i : ℚ)) = 0 := by
      simpa [Matrix.mulVec, dotProduct] using hrow
    rw [hAe] at hmv
    rw [hcalc] at hmv
    exact hmv
  have : (∑ i ∈ p.1, (z i : ℚ)) = ∑ i ∈ p.2, (z i : ℚ) := by linarith
  exact_mod_cast this

end ProofsInTheBook
