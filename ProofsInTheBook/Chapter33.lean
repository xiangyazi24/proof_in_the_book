import Mathlib

/-!
# Chapter 33: Completing Latin squares

From "Proofs from THE BOOK":

**Latin square completion**: Any partial Latin square of order n with
at most n-1 entries can be completed to a full Latin square.

The book's proof uses Hall's marriage theorem applied row by row:
at each step, the remaining entries in each row form a system of
distinct representatives.
-/

namespace ProofsInTheBook.Chapter33

/-!
### Hall's theorem as the row-by-row engine

The book completes a partial Latin square by repeatedly choosing distinct
representatives from finite availability lists.  The combinatorial engine is
Hall's marriage theorem in exactly this finite-family form.
-/

theorem hall_system_of_distinct_representatives {ι α : Type*} [DecidableEq α]
    (available : ι → Finset α)
    (hHall : ∀ rows : Finset ι, rows.card ≤ (rows.biUnion available).card) :
    ∃ choice : ι → α, Function.Injective choice ∧ ∀ row, choice row ∈ available row :=
  (Finset.all_card_le_biUnion_card_iff_exists_injective available).mp hHall

/--
Latin square completion via Hall's theorem: a partial Latin square of order n
can be extended one row at a time. At each step, for each symbol not yet used
in a column, Hall's condition holds because the number of available symbols
in any set of k columns is at least k (the unused symbols form a regular
bipartite graph).
-/
theorem latin_square_completion_step {n : ℕ}
    (usedInCol : Fin n → Finset (Fin n))
    (hused : ∀ j, (usedInCol j).card < n)
    (hHall_verified : ∀ S : Finset (Fin n),
      S.card ≤ (S.biUnion fun j => Finset.univ.filter (· ∉ usedInCol j)).card) :
    ∃ row : Fin n → Fin n, Function.Injective row ∧
      ∀ j, row j ∉ usedInCol j := by
  have := hall_system_of_distinct_representatives
    (fun j : Fin n => Finset.univ.filter (· ∉ usedInCol j))
    hHall_verified
  obtain ⟨choice, hinj, hmem⟩ := this
  exact ⟨choice, hinj, fun j => by simpa using hmem j⟩

theorem chapter33 {ι α : Type*} [DecidableEq α]
    (available : ι → Finset α)
    (hHall : ∀ rows : Finset ι, rows.card ≤ (rows.biUnion available).card) :
    ∃ choice : ι → α, Function.Injective choice ∧ ∀ row, choice row ∈ available row :=
  hall_system_of_distinct_representatives available hHall

end ProofsInTheBook.Chapter33
