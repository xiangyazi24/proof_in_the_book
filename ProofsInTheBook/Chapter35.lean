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

section KempeChains

variable {V : Type*} [DecidableEq V]

/-- The two-color induced subgraph: edges of `G` between `c1/c2`-colored vertices. -/
def kempeGraph (G : SimpleGraph V) (color : V → Fin 5) (c1 c2 : Fin 5) :
    SimpleGraph V where
  Adj u v := G.Adj u v ∧ (color u = c1 ∨ color u = c2) ∧ (color v = c1 ∨ color v = c2)
  symm := fun _ _ ⟨h, hu, hv⟩ => ⟨G.symm h, hv, hu⟩
  loopless := fun v ⟨h, _, _⟩ => G.loopless v h

/-- The Kempe chain through `v0`: the reachable set in the two-color subgraph. -/
def KempeChain (G : SimpleGraph V) (color : V → Fin 5) (c1 c2 : Fin 5) (v0 : V) : Set V :=
  {v | (kempeGraph G color c1 c2).Reachable v0 v}

/-- Swap two colors, leaving all others fixed. -/
def swapColor (c1 c2 : Fin 5) (c : Fin 5) : Fin 5 :=
  if c = c1 then c2 else if c = c2 then c1 else c

theorem swapColor_injective (c1 c2 : Fin 5) : Function.Injective (swapColor c1 c2) := by
  intro x y h; unfold swapColor at h
  by_cases hx1 : x = c1 <;> by_cases hy1 : y = c1 <;>
  by_cases hx2 : x = c2 <;> by_cases hy2 : y = c2 <;>
  simp_all

/-- Swap `c1 ↔ c2` on the Kempe chain, keep all other vertices unchanged. -/
noncomputable def kempeSwap (G : SimpleGraph V) (color : V → Fin 5)
    (c1 c2 : Fin 5) (v0 : V) : V → Fin 5 :=
  fun v => if v ∈ KempeChain G color c1 c2 v0 then swapColor c1 c2 (color v) else color v

/--
Boundary lemma: if `u` is in the Kempe chain and `v` is not, but they are
adjacent in `G` and both colored `c1/c2`, then `v` would be reachable — contradiction.
-/
theorem kempe_boundary_contradiction (G : SimpleGraph V) (color : V → Fin 5)
    (c1 c2 : Fin 5) (v0 u v : V)
    (hu : u ∈ KempeChain G color c1 c2 v0)
    (hv : v ∉ KempeChain G color c1 c2 v0)
    (hadj : G.Adj u v)
    (huc : color u = c1 ∨ color u = c2)
    (hvc : color v = c1 ∨ color v = c2) : False := by
  apply hv
  exact hu.trans (SimpleGraph.Reachable.single ⟨hadj, huc, hvc⟩)

/--
Kempe swap preserves properness of a graph coloring.
-/
theorem kempeSwap_proper (G : SimpleGraph V) (color : V → Fin 5)
    (hproper : ∀ u v, G.Adj u v → color u ≠ color v)
    (c1 c2 : Fin 5) (hne : c1 ≠ c2) (v0 : V) :
    ∀ u v, G.Adj u v →
      kempeSwap G color c1 c2 v0 u ≠ kempeSwap G color c1 c2 v0 v := by
  sorry

/--
After swapping, the anchor vertex `v0` (if colored `c1`) gets color `c2`.
-/
theorem kempeSwap_anchor (G : SimpleGraph V) (color : V → Fin 5)
    (c1 c2 : Fin 5) (v0 : V) (hv0 : color v0 = c1) :
    kempeSwap G color c1 c2 v0 v0 = c2 := by
  simp [kempeSwap, KempeChain, swapColor, hv0, SimpleGraph.Reachable.refl]

end KempeChains

end ProofsInTheBook.Chapter35
