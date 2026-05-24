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

Point-17 status: this file now contains two genuine Hall engines: the
row-completion step for a sparse partial square and the standard extension of
a Latin rectangle by one row.  It is still not the full Evans/Smetaniuk
completion theorem.  The remaining missing infrastructure is Smetaniuk's
stateful induction: conjugating a sparse partial square so the active entries
lie below the diagonal, applying the order-`n - 1` induction hypothesis, and
performing the final column-switching process.  A direct iteration of
`latin_square_completion_step_from_partial` is not valid after one whole row
is added, because the current partial square then has more than `n - 1`
filled cells and the double-counting hypotheses below no longer describe the
enlarged state.
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
A regular finite family satisfies Hall's condition.

If every set in the family has size `d`, and each element belongs to at most
`d` sets, then every subfamily has union at least as large as its index set.
This is the double-counting form used for Latin rectangle extension.
-/
lemma hall_condition_of_regular_family {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (A : ι → Finset α) (d : ℕ)
    (hcard : ∀ i, (A i).card = d)
    (hfiber : ∀ a, ((Finset.univ : Finset ι).filter fun i => a ∈ A i).card ≤ d)
    (hd : 0 < d) :
    ∀ S : Finset ι, S.card ≤ (S.biUnion A).card := by
  intro S
  let T := S.biUnion A
  let I : Finset (ι × α) := (S ×ˢ T).filter fun p => p.2 ∈ A p.1
  have hI_le : I.card ≤ T.card * d := by
    have hmap : (I : Set (ι × α)).MapsTo Prod.snd T := by
      intro p hp
      have hp' : p ∈ I := hp
      have hmem : p ∈ S ×ˢ T ∧ p.2 ∈ A p.1 := by
        simpa [I] using (Finset.mem_filter.mp hp')
      exact (Finset.mem_product.mp hmem.1).2
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    calc
      (∑ b ∈ T, #{p ∈ I | Prod.snd p = b}) ≤ ∑ b ∈ T, d := by
        apply Finset.sum_le_sum
        intro b _hb
        have hle_to_global : #{p ∈ I | Prod.snd p = b} ≤
            ((Finset.univ : Finset ι).filter fun i => b ∈ A i).card := by
          refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
          · intro p hp
            have hpI : p ∈ I := (Finset.mem_filter.mp hp).1
            have hpb : Prod.snd p = b := (Finset.mem_filter.mp hp).2
            have hmem : p ∈ S ×ˢ T ∧ p.2 ∈ A p.1 := by
              simpa [I] using (Finset.mem_filter.mp hpI)
            have hbA : b ∈ A p.1 := by
              simpa [Prod.snd, hpb.symm] using hmem.2
            simp [hbA]
          · intro p hp q hq hpq
            have hpb : Prod.snd p = b := (Finset.mem_filter.mp hp).2
            have hqb : Prod.snd q = b := (Finset.mem_filter.mp hq).2
            exact Prod.ext hpq (by simp [hpb, hqb])
        exact le_trans hle_to_global (hfiber b)
      _ = T.card * d := by simp [Nat.mul_comm]
  have hI_eq : I.card = S.card * d := by
    have hmap : (I : Set (ι × α)).MapsTo Prod.fst S := by
      intro p hp
      have hp' : p ∈ I := hp
      have hmem : p ∈ S ×ˢ T ∧ p.2 ∈ A p.1 := by
        simpa [I] using (Finset.mem_filter.mp hp')
      exact (Finset.mem_product.mp hmem.1).1
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    calc
      (∑ i ∈ S, #{p ∈ I | Prod.fst p = i}) = ∑ i ∈ S, d := by
        apply Finset.sum_congr rfl
        intro i hi
        have hfib_eq : #{p ∈ I | Prod.fst p = i} = (A i).card := by
          have hle1 : #{p ∈ I | Prod.fst p = i} ≤ (A i).card := by
            refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
            · intro p hp
              have hpI : p ∈ I := (Finset.mem_filter.mp hp).1
              have hmem : p ∈ S ×ˢ T ∧ p.2 ∈ A p.1 := by
                simpa [I] using (Finset.mem_filter.mp hpI)
              have hpi : Prod.fst p = i := (Finset.mem_filter.mp hp).2
              simpa [Prod.fst, hpi] using hmem.2
            · intro p hp q hq hpq
              have hpi : Prod.fst p = i := (Finset.mem_filter.mp hp).2
              have hqi : Prod.fst q = i := (Finset.mem_filter.mp hq).2
              exact Prod.ext (by simp [hpi, hqi]) hpq
          have hle2 : (A i).card ≤ #{p ∈ I | Prod.fst p = i} := by
            refine Finset.card_le_card_of_injOn (fun a => (i, a)) ?_ ?_
            · intro a ha
              have haT : a ∈ T := Finset.mem_biUnion.mpr ⟨i, hi, ha⟩
              have hpI : (i, a) ∈ I := by
                exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, haT⟩, ha⟩
              exact Finset.mem_filter.mpr ⟨hpI, rfl⟩
            · intro a _ b _ hab
              exact Prod.mk.inj hab |>.2
          exact le_antisymm hle1 hle2
        simpa [hcard i] using hfib_eq
      _ = S.card * d := by simp [Nat.mul_comm]
  have hmul : S.card * d ≤ T.card * d := by simpa [hI_eq] using hI_le
  exact Nat.le_of_mul_le_mul_right hmul hd

/-!
### Latin rectangles

The first Hall application in the book says that every `r × n` Latin
rectangle with `r < n` can be extended by one more row.
-/

/-- Symbols missing from column `j` of a Latin rectangle. -/
def rectangleAvailable {r n : ℕ} (R : Fin r → Fin n → Fin n) (j : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun a => ∀ i : Fin r, R i j ≠ a

lemma rectangleAvailable_card {r n : ℕ} {R : Fin r → Fin n → Fin n}
    (hcol : ∀ j : Fin n, Function.Injective fun i : Fin r => R i j) (j : Fin n) :
    (rectangleAvailable R j).card = n - r := by
  classical
  let used : Finset (Fin n) := (Finset.univ : Finset (Fin r)).image fun i => R i j
  have hused_card : used.card = r := by
    dsimp [used]
    rw [Finset.card_image_of_injective]
    · simp
    · exact hcol j
  have hAvail : rectangleAvailable R j = (Finset.univ : Finset (Fin n)) \ used := by
    ext a
    simp [rectangleAvailable, used]
  rw [hAvail]
  have hsub : used ⊆ (Finset.univ : Finset (Fin n)) := by
    intro a _ha
    simp
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, Fintype.card_fin, hused_card]

/-- The column in which row `i` contains symbol `a`. -/
noncomputable def symbolColumn {r n : ℕ} {R : Fin r → Fin n → Fin n}
    (hrow : ∀ i : Fin r, Function.Injective (R i)) (a : Fin n) (i : Fin r) : Fin n :=
  Classical.choose ((hrow i).surjective_of_finite (Equiv.refl (Fin n)) a)

lemma symbolColumn_spec {r n : ℕ} {R : Fin r → Fin n → Fin n}
    (hrow : ∀ i : Fin r, Function.Injective (R i)) (a : Fin n) (i : Fin r) :
    R i (symbolColumn hrow a i) = a :=
  Classical.choose_spec ((hrow i).surjective_of_finite (Equiv.refl (Fin n)) a)

lemma symbolColumn_injective {r n : ℕ} {R : Fin r → Fin n → Fin n}
    (hrow : ∀ i : Fin r, Function.Injective (R i))
    (hcol : ∀ j : Fin n, Function.Injective fun i : Fin r => R i j) (a : Fin n) :
    Function.Injective (symbolColumn hrow a) := by
  intro i k hik
  have hi : R i (symbolColumn hrow a i) = a := symbolColumn_spec hrow a i
  have hk : R k (symbolColumn hrow a k) = a := symbolColumn_spec hrow a k
  have hsame : R i (symbolColumn hrow a i) = R k (symbolColumn hrow a i) := by
    rw [hi]
    rw [hik]
    exact hk.symm
  exact hcol (symbolColumn hrow a i) hsame

lemma rectangleAvailable_fiber_card {r n : ℕ} {R : Fin r → Fin n → Fin n}
    (hrow : ∀ i : Fin r, Function.Injective (R i))
    (hcol : ∀ j : Fin n, Function.Injective fun i : Fin r => R i j) (a : Fin n) :
    ((Finset.univ : Finset (Fin n)).filter fun j => a ∈ rectangleAvailable R j).card =
      n - r := by
  classical
  let usedCols : Finset (Fin n) :=
    (Finset.univ : Finset (Fin r)).image (symbolColumn hrow a)
  have hused_card : usedCols.card = r := by
    dsimp [usedCols]
    rw [Finset.card_image_of_injective]
    · simp
    · exact symbolColumn_injective hrow hcol a
  have hfilter :
      ((Finset.univ : Finset (Fin n)).filter fun j => a ∈ rectangleAvailable R j) =
        (Finset.univ : Finset (Fin n)) \ usedCols := by
    ext j
    simp [rectangleAvailable, usedCols]
    constructor
    · intro h i hji
      have hspec := symbolColumn_spec hrow a i
      exact h i (by rw [← hji]; exact hspec)
    · intro h i hij
      have hspec := symbolColumn_spec hrow a i
      have hji : j = symbolColumn hrow a i := hrow i (by rw [hij, hspec])
      exact h i hji.symm
  rw [hfilter]
  have hsub : usedCols ⊆ (Finset.univ : Finset (Fin n)) := by
    intro j _hj
    simp
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, Fintype.card_fin, hused_card]

/--
Book Lemma 1: an `r × n` Latin rectangle with `r < n` can be extended by one
row.  The returned row is a permutation of the symbols and avoids every symbol
already present in its column.
-/
theorem latin_rectangle_extend_one {r n : ℕ} (R : Fin r → Fin n → Fin n)
    (hrow : ∀ i : Fin r, Function.Injective (R i))
    (hcol : ∀ j : Fin n, Function.Injective fun i : Fin r => R i j)
    (hrn : r < n) :
    ∃ row : Fin n → Fin n, Function.Injective row ∧ ∀ i j, row j ≠ R i j := by
  classical
  have hd : 0 < n - r := Nat.sub_pos_of_lt hrn
  have hHall : ∀ S : Finset (Fin n), S.card ≤ (S.biUnion (rectangleAvailable R)).card :=
    hall_condition_of_regular_family (A := rectangleAvailable R) (d := n - r)
      (fun j => rectangleAvailable_card hcol j)
      (fun a => le_of_eq (rectangleAvailable_fiber_card hrow hcol a)) hd
  obtain ⟨row, hrow_inj, hrow_mem⟩ :=
    hall_system_of_distinct_representatives (rectangleAvailable R) hHall
  refine ⟨row, hrow_inj, ?_⟩
  intro i j
  have h := hrow_mem j
  simp [rectangleAvailable] at h
  exact fun hEq => h i hEq.symm

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

/--
Canonical Chapter 33 entry point.

This is currently the genuine Hall row-completion step from the partial-square
hypotheses, with Hall's condition proved internally.  It is intentionally kept
as a step theorem until the stateful fixed-entry row-extension lemma described
in the module note is formalized.
-/
theorem chapter33 {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (usedInCol : Fin n → Finset (Fin n))
    (_hused : ∀ j, (usedInCol j).card < n)
    (hused_witness : ∀ j a, a ∈ usedInCol j → ∃ i, P i j = some a)
    (hfilled_le : (filledCells P).card ≤ n - 1) :
    ∃ row : Fin n → Fin n, Function.Injective row ∧ ∀ j, row j ∉ usedInCol j :=
  latin_square_completion_step_from_partial P usedInCol _hused hused_witness hfilled_le

end ProofsInTheBook.Chapter33
