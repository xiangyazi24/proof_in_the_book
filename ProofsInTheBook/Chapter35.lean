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

/-- If fewer than five colors are used, one of the five colors is still free. -/
theorem exists_unused_five_color (used : Finset (Fin 5)) (hused : used.card < 5) :
    ∃ c : Fin 5, c ∉ used := by
  by_contra hnone
  push Not at hnone
  have huniv : used = Finset.univ := by
    ext c
    exact ⟨fun _ => Finset.mem_univ c, fun _ => hnone c⟩
  have : used.card = 5 := by simp [huniv]
  omega

/--
The easy induction-extension step in the five-color proof: a vertex with at
most four neighbors can receive a color unused by its neighbors.
-/
theorem exists_unused_color_of_neighbor_bound {V : Type*} [DecidableEq V]
    (neighbors : Finset V) (color : V → Fin 5) (hdeg : neighbors.card ≤ 4) :
    ∃ c : Fin 5, ∀ v ∈ neighbors, color v ≠ c := by
  classical
  let used := neighbors.image color
  have hused : used.card < 5 := by
    have hle : used.card ≤ neighbors.card := Finset.card_image_le
    omega
  rcases exists_unused_five_color used hused with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro v hv hvc
  apply hc
  exact Finset.mem_image.mpr ⟨v, hv, hvc⟩

end ProofsInTheBook.Chapter35
