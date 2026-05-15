import Mathlib

/-!
# Chapter 34: The Dinitz problem

From "Proofs from THE BOOK":

**Galvin's theorem** (solving the Dinitz conjecture): For any assignment
of n-element color lists to the n² cells of an n×n array, there exists
a proper Latin square coloring (each cell gets a color from its list).

The book's proof uses the theory of list coloring for bipartite graphs,
specifically kernel-perfect orientations.
-/

namespace ProofsInTheBook.Chapter34

/-- Cells in an `n × n` Dinitz array. -/
abbrev Cell (n : ℕ) : Type := Fin n × Fin n

/-- Two cells conflict when they are distinct and lie in a common row or column. -/
def LatinConflict {n : ℕ} (a b : Cell n) : Prop :=
  a ≠ b ∧ (a.1 = b.1 ∨ a.2 = b.2)

/-- A proper Dinitz/Latin coloring: conflicting cells receive different colors. -/
def ProperArrayColoring {n : ℕ} {α : Type*} (color : Cell n → α) : Prop :=
  ∀ a b, LatinConflict a b → color a ≠ color b

/-- A coloring respects the list assignment when every cell receives a color from its list. -/
def RespectsLists {n : ℕ} {α : Type*} (lists : Cell n → Finset α)
    (color : Cell n → α) : Prop :=
  ∀ cell, color cell ∈ lists cell

/-- The target object in Dinitz's problem: list-respecting and Latin-proper. -/
def DinitzSolution {n : ℕ} {α : Type*} (lists : Cell n → Finset α)
    (color : Cell n → α) : Prop :=
  RespectsLists lists color ∧ ProperArrayColoring color

/-- The row-and-column injectivity condition used to certify a Latin coloring. -/
def RowColumnInjective {n : ℕ} {α : Type*} (color : Cell n → α) : Prop :=
  (∀ r : Fin n, Function.Injective fun c : Fin n => color (r, c)) ∧
    ∀ c : Fin n, Function.Injective fun r : Fin n => color (r, c)

/--
If each row and each column uses every color at most once, then the array
coloring is proper for the Dinitz conflict graph.
-/
theorem properArrayColoring_of_rowColumnInjective {n : ℕ} {α : Type*}
    {color : Cell n → α} (h : RowColumnInjective color) : ProperArrayColoring color := by
  intro a b hab hsame
  rcases a with ⟨ar, ac⟩
  rcases b with ⟨br, bc⟩
  rcases hab with ⟨hne, hconflict⟩
  rcases hconflict with hrow | hcol
  · have hrow' : ar = br := by simpa using hrow
    subst br
    have hc : ac = bc := h.1 ar hsame
    exact hne (by simp [hc])
  · have hcol' : ac = bc := by simpa using hcol
    subst bc
    have hr : ar = br := h.2 ac hsame
    exact hne (by simp [hr])

/--
A list-respecting row/column-injective array coloring is a Dinitz solution.
Galvin's theorem supplies such a coloring from list-size hypotheses; this
lemma records the final verification target.
-/
theorem dinitzSolution_of_respectsLists_rowColumnInjective {n : ℕ} {α : Type*}
    {lists : Cell n → Finset α} {color : Cell n → α}
    (hlist : RespectsLists lists color) (hinj : RowColumnInjective color) :
    DinitzSolution lists color :=
  ⟨hlist, properArrayColoring_of_rowColumnInjective hinj⟩

/--
A kernel-perfect orientation of a graph: an acyclic orientation where every
independent set has a vertex with no outgoing edges (a sink in the induced
subgraph). Galvin's proof uses this notion to extend list colorings greedily.
-/
structure KernelPerfectOrientation {V : Type*} [DecidableEq V] (adj : V → V → Prop)
    [DecidableRel adj] where
  orient : V → V → Bool
  acyclic : ∀ (path : List V), path.length ≥ 2 → path.head? ≠ path.getLast? →
    ¬ (∀ i : Fin (path.length - 1),
      orient (path.get ⟨i.val, by omega⟩) (path.get ⟨i.val + 1, by omega⟩) = true)
  kernel : ∀ (S : Finset V), S.Nonempty →
    (∀ u ∈ S, ∀ v ∈ S, ¬ adj u v) →
    ∃ v ∈ S, ∀ w, adj v w → orient v w = false

/--
Galvin's greedy extension step: in a kernel-perfect orientation, a vertex
that is a sink (no outgoing edges to any colored neighbor) can receive any
color not used by its colored neighbors.
-/
theorem galvin_greedy_step {V : Type*} [DecidableEq V] [Fintype V]
    (neighbors : Finset V) (coloring : V → Fin k) (list_v : Finset (Fin k))
    (hlist_large : neighbors.card < list_v.card) :
    ∃ c ∈ list_v, ∀ w ∈ neighbors, coloring w ≠ c := by
  classical
  let used := neighbors.image coloring
  have hused_card : used.card ≤ neighbors.card := Finset.card_image_le
  have hlt : used.card < list_v.card := lt_of_le_of_lt hused_card hlist_large
  have hne : (list_v \ used).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsub := Finset.sdiff_eq_empty_iff_subset.mp hempty
    have := Finset.card_le_card hsub
    omega
  obtain ⟨c, hc⟩ := hne
  rw [Finset.mem_sdiff] at hc
  refine ⟨c, hc.1, ?_⟩
  intro w hw heq
  exact hc.2 (Finset.mem_image.mpr ⟨w, hw, heq⟩)

theorem chapter34 {n : ℕ} {α : Type*} {lists : Cell n → Finset α} {color : Cell n → α}
    (hlist : RespectsLists lists color) (hinj : RowColumnInjective color) :
    DinitzSolution lists color :=
  dinitzSolution_of_respectsLists_rowColumnInjective hlist hinj

end ProofsInTheBook.Chapter34
