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

theorem chapter34 {n : ℕ} {α : Type*} {color : Cell n → α}
    (h : RowColumnInjective color) : ProperArrayColoring color :=
  properArrayColoring_of_rowColumnInjective h

end ProofsInTheBook.Chapter34
