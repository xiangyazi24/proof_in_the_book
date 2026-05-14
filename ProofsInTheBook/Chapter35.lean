import Mathlib

/-!
# Chapter 35: Five-coloring plane graphs

From "Proofs from THE BOOK":

**Five color theorem**: Every planar graph is 5-colorable.

The book's proof uses Euler's formula (E ≤ 3V-6 for planar graphs)
to find a vertex of degree ≤ 5, then applies induction with a
Kempe chain argument to handle the degree-5 case.
-/

namespace ProofsInTheBook.Chapter35

open scoped BigOperators

/--
The averaging step in the five-color theorem: if the total degree is less
than `6` times the number of vertices, some vertex has degree at most `5`.
In the planar-graph proof, Euler's formula supplies this strict average
bound, and this lemma starts the induction.
-/
theorem exists_degree_le_five_of_average_lt_six {α : Type*} (vertices : Finset α)
    (degree : α → ℕ) (hsum : (∑ v ∈ vertices, degree v) < 6 * vertices.card) :
    ∃ v ∈ vertices, degree v ≤ 5 := by
  by_contra hnone
  have hall : ∀ v ∈ vertices, 6 ≤ degree v := by
    intro v hv
    have hnot : ¬ degree v ≤ 5 := by
      intro hv5
      exact hnone ⟨v, hv, hv5⟩
    omega
  have hlower : 6 * vertices.card ≤ ∑ v ∈ vertices, degree v := by
    calc
      6 * vertices.card = ∑ v ∈ vertices, 6 := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ vertices, degree v := by
        exact Finset.sum_le_sum fun v hv => hall v hv
  omega

theorem chapter35 {α : Type*} (vertices : Finset α) (degree : α → ℕ)
    (hsum : (∑ v ∈ vertices, degree v) < 6 * vertices.card) :
    ∃ v ∈ vertices, degree v ≤ 5 :=
  exists_degree_le_five_of_average_lt_six vertices degree hsum

end ProofsInTheBook.Chapter35
