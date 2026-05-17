import Mathlib
open Finset
open Classical

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

/-!
### Proving Hall's condition from the partial Latin square structure

The premise `hHall_verified` in the Latin square completion step below can be
proved from the partial Latin square structure using double counting.

Key idea: For a set S of columns, let B be the symbols used in every column of S.
Every pair (a, j) with a ∈ B and j ∈ S corresponds to a distinct filled cell.
Since the partial Latin square has at most n-1 filled cells, |B|·|S| ≤ n-1.
If Hall's condition fails (|⋃ available(j)| < |S|), then |B| ≥ n-|S|+1, giving
|B|·|S| ≥ n, a contradiction.
-/

/-- Symbols not yet used in column j. -/
def available {n : ℕ} (usedInCol : Fin n → Finset (Fin n)) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun a => a ∉ usedInCol j

/-- Symbols that are used in *every* column of S. -/
def commonUsed {n : ℕ} (usedInCol : Fin n → Finset (Fin n)) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun a => ∀ j ∈ S, a ∈ usedInCol j

lemma card_add_compl {n : ℕ} (usedInCol : Fin n → Finset (Fin n)) (S : Finset (Fin n)) :
    (S.biUnion (available usedInCol)).card + (commonUsed usedInCol S).card = n := by
  classical
  let A := S.biUnion (available usedInCol)
  let B := commonUsed usedInCol S
  have hA_union_B : A ∪ B = Finset.univ := by
    ext a; simp [A, B, available, commonUsed]
    by_cases h : ∀ j ∈ S, a ∈ usedInCol j
    · right; exact h
    · left; push Not at h; exact h
  have hA_inter_B : A ∩ B = ∅ := by
    ext a; simp [A, B, available, commonUsed]
  have hcard_union : (A ∪ B).card = A.card + B.card := by
    have h := Finset.card_union_add_card_inter A B
    rw [hA_inter_B, Finset.card_empty, add_zero] at h
    omega
  calc
    (S.biUnion (available usedInCol)).card + (commonUsed usedInCol S).card = A.card + B.card := rfl
    _ = (A ∪ B).card := by symm; exact hcard_union
    _ = (Finset.univ : Finset (Fin n)).card := by rw [hA_union_B]
    _ = n := by simp

lemma nat_ineq (n k : ℕ) (hkpos : 0 < k) (hkn : k ≤ n) : n ≤ (n - k + 1) * k := by
  have hz : (n : ℤ) ≤ ((n : ℤ) - (k : ℤ) + 1) * (k : ℤ) := by nlinarith
  exact_mod_cast hz

lemma hall_from_commonUsed_count {n : ℕ}
    (usedInCol : Fin n → Finset (Fin n))
    (hcount : ∀ S : Finset (Fin n), (commonUsed usedInCol S).card * S.card ≤ n - 1) :
    ∀ S : Finset (Fin n), S.card ≤ (S.biUnion (available usedInCol)).card := by
  classical
  intro S
  by_contra! hbad
  let A := S.biUnion (available usedInCol)
  let B := commonUsed usedInCol S
  have hAB : A.card + B.card = n :=
    card_add_compl usedInCol S
  have hcount' : B.card * S.card ≤ n - 1 := hcount S
  have hA_lt_S : A.card < S.card := hbad
  have hSpos : 0 < S.card := by
    by_contra! hzero
    have : A.card < 0 := by omega
    omega
  have hSle_n : S.card ≤ n := by
    calc
      S.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
      _ = n := by simp
  have hB_ge : n - S.card + 1 ≤ B.card := by omega
  have h_mul_le : (n - S.card + 1) * S.card ≤ B.card * S.card :=
    Nat.mul_le_mul_right S.card hB_ge
  have h_ineq : n ≤ (n - S.card + 1) * S.card := nat_ineq n S.card hSpos hSle_n
  have h_contra : n ≤ B.card * S.card := le_trans h_ineq h_mul_le
  omega

/-!
### Connecting to the partial Latin square representation

A partial Latin square is `P : Fin n → Fin n → Option (Fin n)` where
`P i j = some a` means cell (i,j) contains symbol a, and `P i j = none` means empty.
-/

/-- The set of filled cells of a partial Latin square. -/
def filledCells {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun ij : Fin n × Fin n => (P ij.1 ij.2).isSome

/-- If every used symbol has a witness cell, then the pair count of common-used
symbols times columns is bounded by the total filled cells. -/
lemma commonUsed_mul_le_filledCells {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (usedInCol : Fin n → Finset (Fin n))
    (hused_witness : ∀ j a, a ∈ usedInCol j → ∃ i, P i j = some a)
    (S : Finset (Fin n)) :
    (commonUsed usedInCol S).card * S.card ≤ (filledCells P).card := by
  classical
  choose g hg using hused_witness
  let B := commonUsed usedInCol S
  have hprod_card : (B ×ˢ S).card = B.card * S.card := by simp
  let f : Fin n × Fin n → Fin n × Fin n := fun p =>
    if h : p.1 ∈ usedInCol p.2 then (g p.2 p.1 h, p.2) else (p.2, p.2)
  have hf_mem : ∀ (p : Fin n × Fin n), p ∈ (B ×ˢ S) → f p ∈ filledCells P := by
    intro p hp
    rcases Finset.mem_product.1 hp with ⟨haB, hpS⟩
    have ha_used : p.1 ∈ usedInCol p.2 := ((Finset.mem_filter.mp haB).2) p.2 hpS
    simp [f, ha_used, filledCells, hg p.2 p.1 ha_used]
  have hinj : ∀ (p : Fin n × Fin n), p ∈ (B ×ˢ S) → ∀ (q : Fin n × Fin n),
      q ∈ (B ×ˢ S) → f p = f q → p = q := by
    intro p hp q hq h_eq
    rcases Finset.mem_product.1 hp with ⟨haB_p, hpS⟩
    rcases Finset.mem_product.1 hq with ⟨haB_q, hqS⟩
    have ha_used_p : p.1 ∈ usedInCol p.2 := ((Finset.mem_filter.mp haB_p).2) p.2 hpS
    have ha_used_q : q.1 ∈ usedInCol q.2 := ((Finset.mem_filter.mp haB_q).2) q.2 hqS
    have hcol : p.2 = q.2 := by
      simpa [f, ha_used_p, ha_used_q] using congr_arg Prod.snd h_eq
    have hfst_eq : g p.2 p.1 ha_used_p = g q.2 q.1 ha_used_q := by
      simpa [f, ha_used_p, ha_used_q] using congr_arg Prod.fst h_eq
    rcases p with ⟨a, j⟩
    rcases q with ⟨a', j'⟩
    subst hcol
    -- now j' = j, so the remaining goal is (a, j) = (a', j), i.e. a = a'
    have ha_used_q' : a' ∈ usedInCol j := ha_used_q
    have hfst_eq' : g j a ha_used_p = g j a' ha_used_q' := hfst_eq
    have hcell_p : P (g j a ha_used_p) j = some a := hg j a ha_used_p
    have hcell_q : P (g j a ha_used_p) j = some a' := by
      rw [hfst_eq']
      exact hg j a' ha_used_q'
    have h_sym_eq : some a = some a' := by
      rw [← hcell_p, hcell_q]
    have h_a_eq : a = a' := Option.some_injective _ h_sym_eq
    exact Prod.ext h_a_eq rfl
  have hprod_le : (B ×ˢ S).card ≤ (filledCells P).card :=
    Finset.card_le_card_of_injOn f hf_mem hinj
  calc
    (commonUsed usedInCol S).card * S.card = B.card * S.card := rfl
    _ = (B ×ˢ S).card := by symm; exact hprod_card
    _ ≤ (filledCells P).card := hprod_le

/-- From a partial Latin square with at most n-1 filled cells, Hall's condition
holds for the column-availability graph. -/
lemma hall_from_partial_square {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (usedInCol : Fin n → Finset (Fin n))
    (hused_witness : ∀ j a, a ∈ usedInCol j → ∃ i, P i j = some a)
    (hfilled_le : (filledCells P).card ≤ n - 1) :
    ∀ S : Finset (Fin n), S.card ≤ (S.biUnion (available usedInCol)).card := by
  apply hall_from_commonUsed_count usedInCol
  intro S
  calc
    (commonUsed usedInCol S).card * S.card ≤ (filledCells P).card :=
      commonUsed_mul_le_filledCells P usedInCol hused_witness S
    _ ≤ n - 1 := hfilled_le

/--
Latin square completion via Hall's theorem: given a partial Latin square P and
a column-usage map `usedInCol` supported by P's filled cells, with at most n-1
filled cells total, we can extend by one row.

The proof proves Hall's condition internally using the partial Latin square
structure, eliminating the need for an external premise.
-/
theorem latin_square_completion_step_from_partial {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (usedInCol : Fin n → Finset (Fin n))
    (_hused : ∀ j, (usedInCol j).card < n)
    (hused_witness : ∀ j a, a ∈ usedInCol j → ∃ i, P i j = some a)
    (hfilled_le : (filledCells P).card ≤ n - 1) :
    ∃ row : Fin n → Fin n, Function.Injective row ∧ ∀ j, row j ∉ usedInCol j := by
  have hHall : ∀ S : Finset (Fin n),
      S.card ≤ (S.biUnion (available usedInCol)).card :=
    hall_from_partial_square P usedInCol hused_witness hfilled_le
  have hHall' : ∀ S : Finset (Fin n),
      S.card ≤ (S.biUnion fun j => Finset.univ.filter (· ∉ usedInCol j)).card := by
    intro S; simpa [available] using hHall S
  have := hall_system_of_distinct_representatives
    (fun j : Fin n => Finset.univ.filter (· ∉ usedInCol j))
    hHall'
  obtain ⟨choice, hinj, hmem⟩ := this
  exact ⟨choice, hinj, fun j => by simpa using hmem j⟩

end ProofsInTheBook.Chapter33
