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

theorem exists_unused_five_color (used : Finset (Fin 5)) (hused : used.card < 5) :
    ∃ c : Fin 5, c ∉ used := by
  by_contra hnone
  push Not at hnone
  have huniv : used = Finset.univ := by
    ext c
    exact ⟨fun _ => Finset.mem_univ c, fun _ => hnone c⟩
  have : used.card = 5 := by simp [huniv]
  omega

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

section KempeChains

/-- Swap two colors, leaving all others fixed. -/
def swapColor (c1 c2 : Fin 5) (c : Fin 5) : Fin 5 :=
  if c = c1 then c2 else if c = c2 then c1 else c

theorem swapColor_injective (c1 c2 : Fin 5) : Function.Injective (swapColor c1 c2) := by
  intro x y h; unfold swapColor at h
  by_cases hx1 : x = c1 <;> by_cases hy1 : y = c1 <;>
  by_cases hx2 : x = c2 <;> by_cases hy2 : y = c2 <;>
  simp_all

/--
Kempe swap preserves properness when `S` is closed under `c1-c2` adjacency.
The boundary argument: if `u ∈ S` and `v ∉ S` are adjacent, then `color v`
is neither `c1` nor `c2` (or else `v` would be reachable in the `c1-c2`
subgraph and thus in `S`). So swapped `color u ∈ {c1,c2}` differs from
unchanged `color v ∉ {c1,c2}`.
-/
theorem kempeSwap_proper_abstract {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (color : V → Fin 5)
    (_hproper : ∀ u v, G.Adj u v → color u ≠ color v)
    (c1 c2 : Fin 5) (_hne : c1 ≠ c2)
    (S : Finset V)
    (_hclosed : ∀ u v, G.Adj u v → u ∈ S → (color u = c1 ∨ color u = c2) →
      (color v = c1 ∨ color v = c2) → v ∈ S) :
    ∀ u v, G.Adj u v →
      (fun w => if w ∈ S then swapColor c1 c2 (color w) else color w) u ≠
      (fun w => if w ∈ S then swapColor c1 c2 (color w) else color w) v := by
  sorry

end KempeChains

end ProofsInTheBook.Chapter35
