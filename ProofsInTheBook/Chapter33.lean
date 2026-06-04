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

Point-17 status: this file now contains several genuine pieces: the
row-completion Hall step for a sparse partial square, the state update that
fills an empty row while preserving the partial Latin property and with an
exact filled-cell count, row/column/symbol relabeling infrastructure for the
normalization step in Smetaniuk's exact-cardinality induction, a reduction from
the exact case to a normalized exact case with one prescribed filled cell, the standard
extension of a Latin rectangle by one row, and the padding reduction
`completion_from_exact_cardinality_case`, which proves that the `|P| ≤ n - 1`
case reduces to the exact `|P| = n - 1` Evans case by adding legal entries one
at a time.  The complete completion theorem is also discharged for all partial
squares with at most one filled cell and for orders `0`, `1`, `2`, and `3`.
The canonical `chapter33` theorem is now stated as the full completion theorem
conditional on the exact-cardinality Evans/Smetaniuk case.  It is still not an
unconditional full Evans/Smetaniuk completion theorem.  The
remaining missing infrastructure is the exact-cardinality Smetaniuk induction:
permuting rows/columns/symbols so a singleton symbol lies on the back diagonal
and all other filled cells lie above it, applying the order-`n - 1` induction
hypothesis after deleting that diagonal cell and the last row/column, and
formalizing Smetaniuk's completion of the associated `P(L)` by column
switching.  A direct iteration of `latin_square_completion_step_from_partial`
is not valid after one whole row is added, because the current partial square
then has more than `n - 1` filled cells and the double-counting hypotheses
below no longer describe the enlarged state.

The tempting strengthened row step with fixed entries in the active row also
does not follow from the existing count alone.  After `r` completed rows and
`m = n - r` unfinished rows, Hall for a set `S` of still-empty columns can be
forced by elementary counting in the small range `|S| ≤ m - k` and in the
large range `r < |S|`, where `k` is the number of fixed entries in the active
row.  The middle range `m - k < |S| ≤ r` is exactly where the naive induction
has no contradiction from the available pair counts; this is the point where
the book uses Smetaniuk's diagonal placement and switching construction.  That
switching lemma is the honest remaining frontier for upgrading `chapter33` to
the full completion theorem.
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

/-- Row and column Latin conditions for a partial square. -/
def IsPartialLatin {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) : Prop :=
  (∀ i j₁ j₂ a, P i j₁ = some a → P i j₂ = some a → j₁ = j₂) ∧
    ∀ i₁ i₂ j a, P i₁ j = some a → P i₂ j = some a → i₁ = i₂

/-- A full Latin square, represented by its value in each cell. -/
def IsLatinSquare {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ i : Fin n, Function.Injective (L i)) ∧
    ∀ j : Fin n, Function.Injective fun i : Fin n => L i j

/-- A full square completes a partial square if it is Latin and preserves filled cells. -/
def Completes {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (L : Fin n → Fin n → Fin n) : Prop :=
  IsLatinSquare L ∧ ∀ i j a, P i j = some a → L i j = a

/-- The full Evans/Smetaniuk completion theorem for one order. -/
def LatinSquareCompletionTheorem (n : ℕ) : Prop :=
  ∀ P : Fin n → Fin n → Option (Fin n),
    IsPartialLatin P → (filledCells P).card ≤ n - 1 →
      ∃ L : Fin n → Fin n → Fin n, Completes P L

/--
The exact-cardinality case left by the proved padding reduction.  This is the
Smetaniuk switching frontier: once `|P| = n - 1` is completed, the full
`≤ n - 1` theorem follows.
-/
def EvansExactCardinalityCase (n : ℕ) : Prop :=
  ∀ P : Fin n → Fin n → Option (Fin n),
    IsPartialLatin P → (filledCells P).card = n - 1 →
      ∃ L : Fin n → Fin n → Fin n, Completes P L

/-- One partial square extends another when all filled cells are preserved. -/
def ExtendsPartial {n : ℕ} (P Q : Fin n → Fin n → Option (Fin n)) : Prop :=
  ∀ i j a, P i j = some a → Q i j = some a

/-- Symbols already used in row `i`. -/
def rowSymbols {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) (i : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun a => ∃ j, P i j = some a

/-- Symbols already used in column `j`. -/
def colSymbols {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) (j : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun a => ∃ i, P i j = some a

/-- Filled cells in a fixed row. -/
def rowCells {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) (i : Fin n) :
    Finset (Fin n × Fin n) :=
  (filledCells P).filter fun ij => ij.1 = i

/-- Filled cells in a fixed column. -/
def colCells {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) (j : Fin n) :
    Finset (Fin n × Fin n) :=
  (filledCells P).filter fun ij => ij.2 = j

/-- Fill one cell of a partial square, leaving all other cells unchanged. -/
def setCell {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (i₀ j₀ a : Fin n) : Fin n → Fin n → Option (Fin n) :=
  fun i j => if i = i₀ ∧ j = j₀ then some a else P i j

/-- Fill a whole row of a partial square, leaving all other rows unchanged. -/
def setRow {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (i₀ : Fin n) (row : Fin n → Fin n) : Fin n → Fin n → Option (Fin n) :=
  fun i j => if i = i₀ then some (row j) else P i j

/-- The cells in a fixed full row, independent of whether they are filled. -/
def fullRowCells {n : ℕ} (i₀ : Fin n) : Finset (Fin n × Fin n) :=
  Finset.univ.image fun j : Fin n => (i₀, j)

/--
Relabel rows, columns, and symbols of a partial Latin square.

The row and column permutations are read as new-coordinate to old-coordinate
maps, so a filled old cell `(i,j)` appears at
`(rowPerm.symm i, colPerm.symm j)`.
-/
def relabelPartial {n : ℕ} (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    (P : Fin n → Fin n → Option (Fin n)) : Fin n → Fin n → Option (Fin n) :=
  fun i j => Option.map symPerm (P (rowPerm i) (colPerm j))

/-- Relabel rows, columns, and symbols of a full Latin square. -/
def relabelSquare {n : ℕ} (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    (L : Fin n → Fin n → Fin n) : Fin n → Fin n → Fin n :=
  fun i j => symPerm (L (rowPerm i) (colPerm j))

lemma relabelPartial_eq_some_iff {n : ℕ} (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    (P : Fin n → Fin n → Option (Fin n)) (i j a : Fin n) :
    relabelPartial rowPerm colPerm symPerm P i j = some a ↔
      P (rowPerm i) (colPerm j) = some (symPerm.symm a) := by
  constructor
  · intro h
    rcases (by simpa [relabelPartial] using h) with ⟨b, hb, hbmap⟩
    have hb_eq : b = symPerm.symm a := by
      rw [← hbmap]
      simp
    simpa [hb_eq] using hb
  · intro h
    simp [relabelPartial, h]

lemma isPartialLatin_relabelPartial {n : ℕ}
    (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    {P : Fin n → Fin n → Option (Fin n)} (hP : IsPartialLatin P) :
    IsPartialLatin (relabelPartial rowPerm colPerm symPerm P) := by
  constructor
  · intro i j₁ j₂ a h₁ h₂
    have h₁P : P (rowPerm i) (colPerm j₁) = some (symPerm.symm a) :=
      (relabelPartial_eq_some_iff rowPerm colPerm symPerm P i j₁ a).mp h₁
    have h₂P : P (rowPerm i) (colPerm j₂) = some (symPerm.symm a) :=
      (relabelPartial_eq_some_iff rowPerm colPerm symPerm P i j₂ a).mp h₂
    have hcol : colPerm j₁ = colPerm j₂ :=
      hP.1 (rowPerm i) (colPerm j₁) (colPerm j₂) (symPerm.symm a) h₁P h₂P
    exact colPerm.injective hcol
  · intro i₁ i₂ j a h₁ h₂
    have h₁P : P (rowPerm i₁) (colPerm j) = some (symPerm.symm a) :=
      (relabelPartial_eq_some_iff rowPerm colPerm symPerm P i₁ j a).mp h₁
    have h₂P : P (rowPerm i₂) (colPerm j) = some (symPerm.symm a) :=
      (relabelPartial_eq_some_iff rowPerm colPerm symPerm P i₂ j a).mp h₂
    have hrow : rowPerm i₁ = rowPerm i₂ :=
      hP.2 (rowPerm i₁) (rowPerm i₂) (colPerm j) (symPerm.symm a) h₁P h₂P
    exact rowPerm.injective hrow

lemma isLatinSquare_relabelSquare {n : ℕ}
    (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) :
    IsLatinSquare (relabelSquare rowPerm colPerm symPerm L) := by
  constructor
  · intro i j₁ j₂ h
    have h' : L (rowPerm i) (colPerm j₁) = L (rowPerm i) (colPerm j₂) :=
      symPerm.injective h
    have hcol : colPerm j₁ = colPerm j₂ := hL.1 (rowPerm i) h'
    exact colPerm.injective hcol
  · intro j i₁ i₂ h
    have h' : L (rowPerm i₁) (colPerm j) = L (rowPerm i₂) (colPerm j) :=
      symPerm.injective h
    have hrow : rowPerm i₁ = rowPerm i₂ := hL.2 (colPerm j) h'
    exact rowPerm.injective hrow

lemma completes_relabelPartial {n : ℕ} (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    {P : Fin n → Fin n → Option (Fin n)} {L : Fin n → Fin n → Fin n}
    (hL : Completes P L) :
    Completes (relabelPartial rowPerm colPerm symPerm P)
      (relabelSquare rowPerm colPerm symPerm L) := by
  constructor
  · exact isLatinSquare_relabelSquare rowPerm colPerm symPerm hL.1
  · intro i j a hcell
    have hP : P (rowPerm i) (colPerm j) = some (symPerm.symm a) :=
      (relabelPartial_eq_some_iff rowPerm colPerm symPerm P i j a).mp hcell
    have hbase := hL.2 (rowPerm i) (colPerm j) (symPerm.symm a) hP
    simp [relabelSquare, hbase]

lemma completes_of_relabelPartial {n : ℕ} (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    {P : Fin n → Fin n → Option (Fin n)} {L' : Fin n → Fin n → Fin n}
    (hL' : Completes (relabelPartial rowPerm colPerm symPerm P) L') :
    Completes P (relabelSquare rowPerm.symm colPerm.symm symPerm.symm L') := by
  constructor
  · exact isLatinSquare_relabelSquare rowPerm.symm colPerm.symm symPerm.symm hL'.1
  · intro i j a hP
    have hcell :
        relabelPartial rowPerm colPerm symPerm P (rowPerm.symm i) (colPerm.symm j) =
          some (symPerm a) := by
      simp [relabelPartial, hP]
    have hbase := hL'.2 (rowPerm.symm i) (colPerm.symm j) (symPerm a) hcell
    simp [relabelSquare, hbase]

lemma completion_exists_relabelPartial_iff {n : ℕ}
    (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    (P : Fin n → Fin n → Option (Fin n)) :
    (∃ L : Fin n → Fin n → Fin n, Completes (relabelPartial rowPerm colPerm symPerm P) L) ↔
      ∃ L : Fin n → Fin n → Fin n, Completes P L := by
  constructor
  · intro h
    rcases h with ⟨L', hL'⟩
    exact ⟨relabelSquare rowPerm.symm colPerm.symm symPerm.symm L',
      completes_of_relabelPartial rowPerm colPerm symPerm hL'⟩
  · intro h
    rcases h with ⟨L, hL⟩
    exact ⟨relabelSquare rowPerm colPerm symPerm L,
      completes_relabelPartial rowPerm colPerm symPerm hL⟩

lemma filledCells_relabelPartial {n : ℕ} (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    (P : Fin n → Fin n → Option (Fin n)) :
    filledCells (relabelPartial rowPerm colPerm symPerm P) =
      (filledCells P).image (fun ij : Fin n × Fin n =>
        (rowPerm.symm ij.1, colPerm.symm ij.2)) := by
  classical
  ext ij
  constructor
  · intro hij
    have hfilled : (P (rowPerm ij.1) (colPerm ij.2)).isSome := by
      simpa [filledCells, relabelPartial] using hij
    refine Finset.mem_image.mpr ⟨(rowPerm ij.1, colPerm ij.2), ?_, ?_⟩
    · simpa [filledCells] using hfilled
    · simp
  · intro hij
    rcases Finset.mem_image.mp hij with ⟨ijOld, hOld, hijEq⟩
    have hfilledOld : (P ijOld.1 ijOld.2).isSome := by
      simpa [filledCells] using hOld
    have hi : ij.1 = rowPerm.symm ijOld.1 := (congrArg Prod.fst hijEq).symm
    have hj : ij.2 = colPerm.symm ijOld.2 := (congrArg Prod.snd hijEq).symm
    simp [filledCells, relabelPartial, hi, hj, hfilledOld]

lemma filledCells_relabelPartial_card {n : ℕ}
    (rowPerm colPerm symPerm : Equiv.Perm (Fin n))
    (P : Fin n → Fin n → Option (Fin n)) :
    (filledCells (relabelPartial rowPerm colPerm symPerm P)).card =
      (filledCells P).card := by
  rw [filledCells_relabelPartial rowPerm colPerm symPerm P]
  rw [Finset.card_image_of_injective]
  intro x y h
  exact Prod.ext (rowPerm.symm.injective (congrArg Prod.fst h))
    (colPerm.symm.injective (congrArg Prod.snd h))

lemma relabelPartial_swap_cell {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    {iOld jOld aOld iNew jNew aNew : Fin n}
    (hcell : P iOld jOld = some aOld) :
    relabelPartial (Equiv.swap iNew iOld) (Equiv.swap jNew jOld)
        (Equiv.swap aOld aNew) P iNew jNew = some aNew := by
  simp [relabelPartial, hcell]

lemma completion_exists_relabelPartial_swap_cell_iff {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (iOld jOld aOld iNew jNew aNew : Fin n) :
    (∃ L : Fin n → Fin n → Fin n,
        Completes
          (relabelPartial (Equiv.swap iNew iOld) (Equiv.swap jNew jOld)
            (Equiv.swap aOld aNew) P) L) ↔
      ∃ L : Fin n → Fin n → Fin n, Completes P L :=
  completion_exists_relabelPartial_iff
    (Equiv.swap iNew iOld) (Equiv.swap jNew jOld) (Equiv.swap aOld aNew) P

/--
It is enough to prove the exact-cardinality case for partial squares with one
fixed prescribed cell.  Any exact square of order at least two has a filled
cell, and the relabeling lemmas above move that cell to the prescribed
position and symbol without changing partial Latinity, cardinality, or
completion existence.
-/
theorem evansExactCardinalityCase_of_normalized_cell_case {n : ℕ}
    (hn : 2 ≤ n) (iTarget jTarget aTarget : Fin n)
    (hnormal : ∀ P : Fin n → Fin n → Option (Fin n),
      IsPartialLatin P → (filledCells P).card = n - 1 →
        P iTarget jTarget = some aTarget →
          ∃ L : Fin n → Fin n → Fin n, Completes P L) :
    EvansExactCardinalityCase n := by
  intro P hP hcard
  have hcard_pos : 0 < (filledCells P).card := by
    rw [hcard]
    omega
  obtain ⟨ij, hij⟩ := Finset.card_pos.mp hcard_pos
  have hSome : (P ij.1 ij.2).isSome := by
    simpa [filledCells] using hij
  cases hcell_eq : P ij.1 ij.2 with
  | none =>
      simp [hcell_eq] at hSome
  | some aOld =>
      let P' := relabelPartial (Equiv.swap iTarget ij.1) (Equiv.swap jTarget ij.2)
        (Equiv.swap aOld aTarget) P
      have hP' : IsPartialLatin P' := by
        dsimp [P']
        exact isPartialLatin_relabelPartial
          (Equiv.swap iTarget ij.1) (Equiv.swap jTarget ij.2)
          (Equiv.swap aOld aTarget) hP
      have hcard' : (filledCells P').card = n - 1 := by
        dsimp [P']
        rw [filledCells_relabelPartial_card]
        exact hcard
      have htarget : P' iTarget jTarget = some aTarget := by
        dsimp [P']
        exact relabelPartial_swap_cell P hcell_eq
      obtain ⟨L', hL'⟩ := hnormal P' hP' hcard' htarget
      exact (completion_exists_relabelPartial_swap_cell_iff P ij.1 ij.2 aOld
        iTarget jTarget aTarget).mp ⟨L', hL'⟩

lemma completes_of_extendsPartial {n : ℕ} {P Q : Fin n → Fin n → Option (Fin n)}
    {L : Fin n → Fin n → Fin n} (hPQ : ExtendsPartial P Q) (hQL : Completes Q L) :
    Completes P L := by
  rcases hQL with ⟨hLatin, hcomp⟩
  exact ⟨hLatin, fun i j a hP => hcomp i j a (hPQ i j a hP)⟩

lemma extendsPartial_refl {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) :
    ExtendsPartial P P := by
  intro i j a h
  exact h

lemma extendsPartial_trans {n : ℕ} {P Q R : Fin n → Fin n → Option (Fin n)}
    (hPQ : ExtendsPartial P Q) (hQR : ExtendsPartial Q R) :
    ExtendsPartial P R := by
  intro i j a h
  exact hQR i j a (hPQ i j a h)

lemma extendsPartial_setCell_of_empty {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    {i₀ j₀ a : Fin n} (hempty : P i₀ j₀ = none) :
    ExtendsPartial P (setCell P i₀ j₀ a) := by
  intro i j b hP
  by_cases hcell : i = i₀ ∧ j = j₀
  · rcases hcell with ⟨hi, hj⟩
    subst i
    subst j
    rw [hempty] at hP
    cases hP
  · simp [setCell, hcell, hP]

lemma extendsPartial_setRow_of_empty {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    {i₀ : Fin n} {row : Fin n → Fin n} (hempty : ∀ j, P i₀ j = none) :
    ExtendsPartial P (setRow P i₀ row) := by
  intro i j a hP
  by_cases hi : i = i₀
  · subst i
    rw [hempty j] at hP
    cases hP
  · simp [setRow, hi, hP]

lemma isPartialLatin_setCell {n : ℕ} {P : Fin n → Fin n → Option (Fin n)}
    {i₀ j₀ a : Fin n} (hP : IsPartialLatin P) (_hempty : P i₀ j₀ = none)
    (haRow : a ∉ rowSymbols P i₀) (haCol : a ∉ colSymbols P j₀) :
    IsPartialLatin (setCell P i₀ j₀ a) := by
  constructor
  · intro i j₁ j₂ b hb₁ hb₂
    by_cases h₁ : i = i₀ ∧ j₁ = j₀
    · by_cases h₂ : i = i₀ ∧ j₂ = j₀
      · exact h₁.2.trans h₂.2.symm
      · have hi : i = i₀ := h₁.1
        have hj₁ : j₁ = j₀ := h₁.2
        have hab : a = b := Option.some.inj (by simpa [setCell, h₁] using hb₁)
        have hb₂P : P i j₂ = some b := by simpa [setCell, h₂] using hb₂
        have : a ∈ rowSymbols P i₀ := by
          simp [rowSymbols]
          exact ⟨j₂, by simpa [hi, hab] using hb₂P⟩
        exact False.elim (haRow this)
    · by_cases h₂ : i = i₀ ∧ j₂ = j₀
      · have hi : i = i₀ := h₂.1
        have hj₂ : j₂ = j₀ := h₂.2
        have hab : a = b := Option.some.inj (by simpa [setCell, h₂] using hb₂)
        have hb₁P : P i j₁ = some b := by simpa [setCell, h₁] using hb₁
        have : a ∈ rowSymbols P i₀ := by
          simp [rowSymbols]
          exact ⟨j₁, by simpa [hi, hab] using hb₁P⟩
        exact False.elim (haRow this)
      · have hb₁P : P i j₁ = some b := by simpa [setCell, h₁] using hb₁
        have hb₂P : P i j₂ = some b := by simpa [setCell, h₂] using hb₂
        exact hP.1 i j₁ j₂ b hb₁P hb₂P
  · intro i₁ i₂ j b hb₁ hb₂
    by_cases h₁ : i₁ = i₀ ∧ j = j₀
    · by_cases h₂ : i₂ = i₀ ∧ j = j₀
      · exact h₁.1.trans h₂.1.symm
      · have hi₁ : i₁ = i₀ := h₁.1
        have hj : j = j₀ := h₁.2
        have hab : a = b := Option.some.inj (by simpa [setCell, h₁] using hb₁)
        have hb₂P : P i₂ j = some b := by simpa [setCell, h₂] using hb₂
        have : a ∈ colSymbols P j₀ := by
          simp [colSymbols]
          exact ⟨i₂, by simpa [hj, hab] using hb₂P⟩
        exact False.elim (haCol this)
    · by_cases h₂ : i₂ = i₀ ∧ j = j₀
      · have hi₂ : i₂ = i₀ := h₂.1
        have hj : j = j₀ := h₂.2
        have hab : a = b := Option.some.inj (by simpa [setCell, h₂] using hb₂)
        have hb₁P : P i₁ j = some b := by simpa [setCell, h₁] using hb₁
        have : a ∈ colSymbols P j₀ := by
          simp [colSymbols]
          exact ⟨i₁, by simpa [hj, hab] using hb₁P⟩
        exact False.elim (haCol this)
      · have hb₁P : P i₁ j = some b := by simpa [setCell, h₁] using hb₁
        have hb₂P : P i₂ j = some b := by simpa [setCell, h₂] using hb₂
        exact hP.2 i₁ i₂ j b hb₁P hb₂P

lemma isPartialLatin_setRow_of_empty {n : ℕ} {P : Fin n → Fin n → Option (Fin n)}
    {i₀ : Fin n} {row : Fin n → Fin n} (hP : IsPartialLatin P)
    (_hempty : ∀ j, P i₀ j = none)
    (hrow : Function.Injective row) (havoid : ∀ j, row j ∉ colSymbols P j) :
    IsPartialLatin (setRow P i₀ row) := by
  constructor
  · intro i j₁ j₂ a h₁ h₂
    by_cases hi : i = i₀
    · subst i
      have ha₁ : row j₁ = a := Option.some.inj (by simpa [setRow] using h₁)
      have ha₂ : row j₂ = a := Option.some.inj (by simpa [setRow] using h₂)
      exact hrow (ha₁.trans ha₂.symm)
    · have h₁P : P i j₁ = some a := by simpa [setRow, hi] using h₁
      have h₂P : P i j₂ = some a := by simpa [setRow, hi] using h₂
      exact hP.1 i j₁ j₂ a h₁P h₂P
  · intro i₁ i₂ j a h₁ h₂
    by_cases hi₁ : i₁ = i₀
    · by_cases hi₂ : i₂ = i₀
      · exact hi₁.trans hi₂.symm
      · subst i₁
        have ha : row j = a := Option.some.inj (by simpa [setRow] using h₁)
        have h₂P : P i₂ j = some a := by simpa [setRow, hi₂] using h₂
        have hmem : row j ∈ colSymbols P j := by
          simp [colSymbols]
          exact ⟨i₂, by simpa [ha] using h₂P⟩
        exact False.elim (havoid j hmem)
    · by_cases hi₂ : i₂ = i₀
      · subst i₂
        have h₁P : P i₁ j = some a := by simpa [setRow, hi₁] using h₁
        have ha : row j = a := Option.some.inj (by simpa [setRow] using h₂)
        have hmem : row j ∈ colSymbols P j := by
          simp [colSymbols]
          exact ⟨i₁, by simpa [ha] using h₁P⟩
        exact False.elim (havoid j hmem)
      · have h₁P : P i₁ j = some a := by simpa [setRow, hi₁] using h₁
        have h₂P : P i₂ j = some a := by simpa [setRow, hi₂] using h₂
        exact hP.2 i₁ i₂ j a h₁P h₂P

lemma filledCells_setCell_of_empty {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) {i₀ j₀ a : Fin n}
    (hempty : P i₀ j₀ = none) :
    filledCells (setCell P i₀ j₀ a) = insert (i₀, j₀) (filledCells P) := by
  classical
  ext ij
  by_cases hcell : ij = (i₀, j₀)
  · subst ij
    simp [filledCells, setCell, hempty]
  · have hnot : ¬ (ij.1 = i₀ ∧ ij.2 = j₀) := by
      intro h
      exact hcell (Prod.ext h.1 h.2)
    simp [filledCells, setCell, hnot, hcell]

lemma filledCells_setCell_card_of_empty {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) {i₀ j₀ a : Fin n}
    (hempty : P i₀ j₀ = none) :
    (filledCells (setCell P i₀ j₀ a)).card = (filledCells P).card + 1 := by
  classical
  rw [filledCells_setCell_of_empty P hempty]
  have hnotmem : (i₀, j₀) ∉ filledCells P := by
    simp [filledCells, hempty]
  rw [Finset.card_insert_of_notMem hnotmem]

lemma fullRowCells_card {n : ℕ} (i₀ : Fin n) : (fullRowCells i₀).card = n := by
  rw [fullRowCells]
  rw [Finset.card_image_of_injective]
  · simp
  · intro j₁ j₂ h
    exact congrArg Prod.snd h

lemma fullRowCells_disjoint_filledCells_of_empty {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) {i₀ : Fin n}
    (hempty : ∀ j, P i₀ j = none) :
    Disjoint (fullRowCells i₀) (filledCells P) := by
  rw [Finset.disjoint_left]
  intro ij hijRow hijFilled
  rcases Finset.mem_image.mp hijRow with ⟨j, _hj, hij⟩
  subst ij
  simp [filledCells, hempty j] at hijFilled

lemma filledCells_setRow {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) {i₀ : Fin n} {row : Fin n → Fin n} :
    filledCells (setRow P i₀ row) = fullRowCells i₀ ∪ filledCells P := by
  classical
  ext ij
  by_cases hi : ij.1 = i₀
  · have hijRow : ij ∈ fullRowCells i₀ := by
      refine Finset.mem_image.mpr ⟨ij.2, by simp, ?_⟩
      exact Prod.ext hi.symm rfl
    simp [filledCells, setRow, hi, hijRow]
  · have hijNotRow : ij ∉ fullRowCells i₀ := by
      intro hijRow
      rcases Finset.mem_image.mp hijRow with ⟨j, _hj, hij⟩
      exact hi (congrArg Prod.fst hij).symm
    simp [filledCells, setRow, hi, hijNotRow]

lemma filledCells_setRow_card_of_empty {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) {i₀ : Fin n} {row : Fin n → Fin n}
    (hempty : ∀ j, P i₀ j = none) :
    (filledCells (setRow P i₀ row)).card = (filledCells P).card + n := by
  rw [filledCells_setRow P]
  rw [Finset.card_union_of_disjoint (fullRowCells_disjoint_filledCells_of_empty P hempty)]
  rw [fullRowCells_card]
  omega

lemma exists_empty_row_of_filledCells_lt {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (hcard : (filledCells P).card < n) :
    ∃ i : Fin n, ∀ j, P i j = none := by
  classical
  by_contra hno
  have hex : ∀ i : Fin n, ∃ j : Fin n, (i, j) ∈ filledCells P := by
    intro i
    by_contra hrow
    have hempty : ∀ j, P i j = none := by
      intro j
      cases h : P i j with
      | none => rfl
      | some a =>
          have hmem : (i, j) ∈ filledCells P := by
            simp [filledCells, h]
          exact False.elim (hrow ⟨j, hmem⟩)
    exact hno ⟨i, hempty⟩
  let chosenCell : Fin n → {ij : Fin n × Fin n // ij ∈ filledCells P} :=
    fun i => ⟨(i, Classical.choose (hex i)), Classical.choose_spec (hex i)⟩
  have hinj : Function.Injective chosenCell := by
    intro i₁ i₂ h
    exact congrArg (fun ij : {ij : Fin n × Fin n // ij ∈ filledCells P} => ij.1.1) h
  have hle := Fintype.card_le_of_injective chosenCell hinj
  simp [Fintype.card_fin] at hle
  omega

lemma exists_empty_row_of_filledCells_le_pred {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (hn : 0 < n)
    (hcard : (filledCells P).card ≤ n - 1) :
    ∃ i : Fin n, ∀ j, P i j = none :=
  exists_empty_row_of_filledCells_lt P (by omega)

lemma rowSymbols_card_le_rowCells_card {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (i : Fin n) :
    (rowSymbols P i).card ≤ (rowCells P i).card := by
  classical
  let witness : Fin n → Fin n := fun a =>
    if h : ∃ j, P i j = some a then Classical.choose h else i
  refine Finset.card_le_card_of_injOn (fun a => (i, witness a)) ?_ ?_
  · intro a ha
    have hex : ∃ j, P i j = some a := by simpa [rowSymbols] using ha
    have hcell : P i (witness a) = some a := by
      simpa [witness, hex] using Classical.choose_spec hex
    simp [rowCells, filledCells, hcell]
  · intro a ha b hb hab
    have hexa : ∃ j, P i j = some a := by simpa [rowSymbols] using ha
    have hexb : ∃ j, P i j = some b := by simpa [rowSymbols] using hb
    have hw : witness a = witness b := Prod.mk.inj hab |>.2
    have hcella : P i (witness a) = some a := by
      simpa [witness, hexa] using Classical.choose_spec hexa
    have hcellb : P i (witness b) = some b := by
      simpa [witness, hexb] using Classical.choose_spec hexb
    have hsome : some a = some b := by
      rw [← hcella, hw, hcellb]
    exact Option.some.inj hsome

lemma colSymbols_card_le_colCells_card {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (j : Fin n) :
    (colSymbols P j).card ≤ (colCells P j).card := by
  classical
  let witness : Fin n → Fin n := fun a =>
    if h : ∃ i, P i j = some a then Classical.choose h else j
  refine Finset.card_le_card_of_injOn (fun a => (witness a, j)) ?_ ?_
  · intro a ha
    have hex : ∃ i, P i j = some a := by simpa [colSymbols] using ha
    have hcell : P (witness a) j = some a := by
      simpa [witness, hex] using Classical.choose_spec hex
    simp [colCells, filledCells, hcell]
  · intro a ha b hb hab
    have hexa : ∃ i, P i j = some a := by simpa [colSymbols] using ha
    have hexb : ∃ i, P i j = some b := by simpa [colSymbols] using hb
    have hw : witness a = witness b := Prod.mk.inj hab |>.1
    have hcella : P (witness a) j = some a := by
      simpa [witness, hexa] using Classical.choose_spec hexa
    have hcellb : P (witness b) j = some b := by
      simpa [witness, hexb] using Classical.choose_spec hexb
    have hsome : some a = some b := by
      rw [← hcella, hw, hcellb]
    exact Option.some.inj hsome

lemma rowCells_disjoint_colCells_of_empty {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) {i₀ j₀ : Fin n}
    (hempty : P i₀ j₀ = none) :
    Disjoint (rowCells P i₀) (colCells P j₀) := by
  rw [Finset.disjoint_left]
  intro ij hijRow hijCol
  have hfilled : (P ij.1 ij.2).isSome := by
    simpa [rowCells, filledCells] using (Finset.mem_filter.mp hijRow).1
  have hi : ij.1 = i₀ := (Finset.mem_filter.mp hijRow).2
  have hj : ij.2 = j₀ := (Finset.mem_filter.mp hijCol).2
  rw [hi, hj, hempty] at hfilled
  simp at hfilled

lemma rowCells_union_colCells_card_le_filledCells {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (i₀ j₀ : Fin n) :
    ((rowCells P i₀) ∪ (colCells P j₀)).card ≤ (filledCells P).card := by
  exact Finset.card_le_card (by
    intro ij hij
    rcases Finset.mem_union.mp hij with hijRow | hijCol
    · exact (Finset.mem_filter.mp hijRow).1
    · exact (Finset.mem_filter.mp hijCol).1)

lemma row_col_symbols_card_le_filledCells_of_empty {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)}
    {i₀ j₀ : Fin n} (hempty : P i₀ j₀ = none) :
    ((rowSymbols P i₀) ∪ (colSymbols P j₀)).card ≤ (filledCells P).card := by
  classical
  have hrow := rowSymbols_card_le_rowCells_card P i₀
  have hcol := colSymbols_card_le_colCells_card P j₀
  have hsym_union :
      ((rowSymbols P i₀) ∪ (colSymbols P j₀)).card ≤
        (rowSymbols P i₀).card + (colSymbols P j₀).card :=
    Finset.card_union_le _ _
  have hcell_sum :
      (rowCells P i₀).card + (colCells P j₀).card =
        ((rowCells P i₀) ∪ (colCells P j₀)).card := by
    rw [Finset.card_union_of_disjoint (rowCells_disjoint_colCells_of_empty P hempty)]
  have hcell_union := rowCells_union_colCells_card_le_filledCells P i₀ j₀
  calc
    ((rowSymbols P i₀) ∪ (colSymbols P j₀)).card
        ≤ (rowSymbols P i₀).card + (colSymbols P j₀).card := hsym_union
    _ ≤ (rowCells P i₀).card + (colCells P j₀).card := Nat.add_le_add hrow hcol
    _ = ((rowCells P i₀) ∪ (colCells P j₀)).card := hcell_sum
    _ ≤ (filledCells P).card := hcell_union

lemma exists_symbol_not_row_col_of_filledCells_le {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)}
    {i₀ j₀ : Fin n} (hempty : P i₀ j₀ = none)
    (hfilled_le : (filledCells P).card ≤ n - 2) :
    ∃ a : Fin n, a ∉ rowSymbols P i₀ ∧ a ∉ colSymbols P j₀ := by
  classical
  let U := (rowSymbols P i₀) ∪ (colSymbols P j₀)
  have hU_le : U.card ≤ n - 2 := by
    exact le_trans (row_col_symbols_card_le_filledCells_of_empty hempty) hfilled_le
  have hU_lt : U.card < n := by
    have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le i₀.val) i₀.isLt
    omega
  by_contra hnone
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ U := by
    intro a _ha
    by_cases haU : a ∈ U
    · exact haU
    · have hrow : a ∉ rowSymbols P i₀ := by
        intro h
        exact haU (Finset.mem_union.mpr (Or.inl h))
      have hcol : a ∉ colSymbols P j₀ := by
        intro h
        exact haU (Finset.mem_union.mpr (Or.inr h))
      exact False.elim (hnone ⟨a, hrow, hcol⟩)
  have hn_le : n ≤ U.card := by
    calc
      n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ U.card := Finset.card_le_card hsub
  omega

lemma exists_empty_cell_of_filledCells_lt_pred {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (hcard_lt : (filledCells P).card < n - 1) :
    ∃ i j, P i j = none := by
  classical
  have hnpos : 0 < n := by omega
  have hnn : n ≤ n * n := by
    nth_rewrite 1 [← Nat.mul_one n]
    exact Nat.mul_le_mul_left n (Nat.succ_le_of_lt hnpos)
  have hlt_univ : (filledCells P).card < (Finset.univ : Finset (Fin n × Fin n)).card := by
    have hcard_univ : (Finset.univ : Finset (Fin n × Fin n)).card = n * n := by simp
    rw [hcard_univ]
    exact lt_of_lt_of_le hcard_lt (le_trans (Nat.sub_le n 1) hnn)
  by_contra hnone
  push Not at hnone
  have hfull : filledCells P = (Finset.univ : Finset (Fin n × Fin n)) := by
    ext ij
    simp [filledCells]
    cases hcell : P ij.1 ij.2 with
    | none =>
        exact False.elim (hnone ij.1 ij.2 hcell)
    | some a =>
        simp
  have hnot_lt : ¬ (filledCells P).card < (Finset.univ : Finset (Fin n × Fin n)).card := by
    rw [hfull]
    exact lt_irrefl _
  exact hnot_lt hlt_univ

/--
If a partial Latin square has fewer than `n - 1` entries, one more entry can be
added while preserving the partial Latin property.

This formalizes the easy final sentence in Smetaniuk's proof: the case
`|P| < n - 1` can be reduced to the exact `|P| = n - 1` case by adding
entries one at a time.
-/
theorem extend_partialLatin_one {n : ℕ} {P : Fin n → Fin n → Option (Fin n)}
    (hP : IsPartialLatin P) (hcard_lt : (filledCells P).card < n - 1) :
    ∃ Q : Fin n → Fin n → Option (Fin n),
      IsPartialLatin Q ∧ ExtendsPartial P Q ∧
        (filledCells Q).card = (filledCells P).card + 1 := by
  classical
  obtain ⟨i₀, j₀, hempty⟩ := exists_empty_cell_of_filledCells_lt_pred P hcard_lt
  have hfilled_le : (filledCells P).card ≤ n - 2 := by omega
  obtain ⟨a, haRow, haCol⟩ :=
    exists_symbol_not_row_col_of_filledCells_le hempty hfilled_le
  refine ⟨setCell P i₀ j₀ a, ?_, ?_, ?_⟩
  · exact isPartialLatin_setCell hP hempty haRow haCol
  · exact extendsPartial_setCell_of_empty P hempty
  · exact filledCells_setCell_card_of_empty P hempty

theorem extend_partialLatin_to_exact {n : ℕ} {P : Fin n → Fin n → Option (Fin n)}
    (hP : IsPartialLatin P) (hfilled_le : (filledCells P).card ≤ n - 1) :
    ∃ Q : Fin n → Fin n → Option (Fin n),
      IsPartialLatin Q ∧ ExtendsPartial P Q ∧ (filledCells Q).card = n - 1 := by
  classical
  let d₀ := n - 1 - (filledCells P).card
  have hmain :
      ∀ d : ℕ,
        (∀ e < d,
          ∀ R : Fin n → Fin n → Option (Fin n),
            IsPartialLatin R →
              (filledCells R).card ≤ n - 1 →
                e = n - 1 - (filledCells R).card →
                  ∃ Q : Fin n → Fin n → Option (Fin n),
                    IsPartialLatin Q ∧ ExtendsPartial R Q ∧
                      (filledCells Q).card = n - 1) →
        ∀ R : Fin n → Fin n → Option (Fin n),
          IsPartialLatin R →
            (filledCells R).card ≤ n - 1 →
              d = n - 1 - (filledCells R).card →
                ∃ Q : Fin n → Fin n → Option (Fin n),
                  IsPartialLatin Q ∧ ExtendsPartial R Q ∧
                    (filledCells Q).card = n - 1 := by
    intro d ih R hR hR_le hd
    by_cases hexact : (filledCells R).card = n - 1
    · refine ⟨R, hR, extendsPartial_refl R, hexact⟩
    · have hlt : (filledCells R).card < n - 1 := lt_of_le_of_ne hR_le hexact
      obtain ⟨R₁, hR₁, hRR₁, hcard₁⟩ := extend_partialLatin_one hR hlt
      have hR₁_le : (filledCells R₁).card ≤ n - 1 := by omega
      let e := n - 1 - (filledCells R₁).card
      have heq : e = n - 1 - (filledCells R₁).card := rfl
      have he_lt : e < d := by
        subst d
        dsimp [e]
        omega
      obtain ⟨Q, hQ, hR₁Q, hQcard⟩ := ih e he_lt R₁ hR₁ hR₁_le heq
      exact ⟨Q, hQ, extendsPartial_trans hRR₁ hR₁Q, hQcard⟩
  let motive := fun d : ℕ =>
    ∀ R : Fin n → Fin n → Option (Fin n),
      IsPartialLatin R →
        (filledCells R).card ≤ n - 1 →
          d = n - 1 - (filledCells R).card →
            ∃ Q : Fin n → Fin n → Option (Fin n),
              IsPartialLatin Q ∧ ExtendsPartial R Q ∧ (filledCells Q).card = n - 1
  exact (Nat.strong_induction_on (p := motive) d₀ hmain) P hP hfilled_le rfl

/--
Reduction from the `≤ n - 1` Evans statement to the exact `= n - 1` case.

The remaining unformalized Smetaniuk frontier is therefore the exact-cardinality
case; the padding step for smaller partial squares is proved here without any
extra premise.
-/
theorem completion_from_exact_cardinality_case {n : ℕ}
    (hexact : EvansExactCardinalityCase n) :
    LatinSquareCompletionTheorem n := by
  intro P hP hfilled_le
  obtain ⟨Q, hQ, hPQ, hQcard⟩ := extend_partialLatin_to_exact hP hfilled_le
  obtain ⟨L, hL⟩ := hexact Q hQ hQcard
  exact ⟨L, completes_of_extendsPartial hPQ hL⟩

/-!
### Elementary complete orders

Squares with at most one filled cell, and orders `0`, `1`, `2`, and `3`, do not
need the Evans/Smetaniuk induction.
-/

/-- The cyclic Latin square on `Fin n`. -/
def cyclicLatinSquare (n : ℕ) : Fin n → Fin n → Fin n := fun i j => i + j

theorem isLatinSquare_cyclicLatinSquare (n : ℕ) : IsLatinSquare (cyclicLatinSquare n) := by
  constructor
  · intro i x y h
    exact add_left_cancel h
  · intro j x y h
    exact add_right_cancel h

/-- A cyclic Latin square with one prescribed cell value, obtained by a symbol swap. -/
def cyclicLatinSquareWithCell {n : ℕ} (i₀ j₀ a₀ : Fin n) : Fin n → Fin n → Fin n :=
  fun i j => Equiv.swap (i₀ + j₀) a₀ (i + j)

theorem isLatinSquare_cyclicLatinSquareWithCell {n : ℕ} (i₀ j₀ a₀ : Fin n) :
    IsLatinSquare (cyclicLatinSquareWithCell i₀ j₀ a₀) := by
  constructor
  · intro i x y h
    unfold cyclicLatinSquareWithCell at h
    have h' : i + x = i + y := (Equiv.swap (i₀ + j₀) a₀).injective h
    exact add_left_cancel h'
  · intro j x y h
    unfold cyclicLatinSquareWithCell at h
    have h' : x + j = y + j := (Equiv.swap (i₀ + j₀) a₀).injective h
    exact add_right_cancel h'

theorem cyclicLatinSquareWithCell_spec {n : ℕ} (i₀ j₀ a₀ : Fin n) :
    cyclicLatinSquareWithCell i₀ j₀ a₀ i₀ j₀ = a₀ := by
  simp [cyclicLatinSquareWithCell]

theorem latin_square_completion_card_le_one {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (hfilled_le : (filledCells P).card ≤ 1) :
    ∃ L : Fin n → Fin n → Fin n, Completes P L := by
  classical
  by_cases hfilled : ∃ i j a, P i j = some a
  · rcases hfilled with ⟨i₀, j₀, a₀, hcell₀⟩
    refine ⟨cyclicLatinSquareWithCell i₀ j₀ a₀, ?_⟩
    constructor
    · exact isLatinSquare_cyclicLatinSquareWithCell i₀ j₀ a₀
    · intro i j a hcell
      have hmem : (i, j) ∈ filledCells P := by
        simp [filledCells, hcell]
      have hmem₀ : (i₀, j₀) ∈ filledCells P := by
        simp [filledCells, hcell₀]
      have hp_eq : (i, j) = (i₀, j₀) :=
        (Finset.card_le_one_iff.mp hfilled_le) hmem hmem₀
      have hi : i = i₀ := congrArg Prod.fst hp_eq
      have hj : j = j₀ := congrArg Prod.snd hp_eq
      subst i
      subst j
      have ha : a = a₀ := by
        have hsome : some a = some a₀ := by
          rw [← hcell, hcell₀]
        exact Option.some.inj hsome
      subst a
      exact cyclicLatinSquareWithCell_spec i₀ j₀ a₀
  · refine ⟨cyclicLatinSquare n, ?_⟩
    constructor
    · exact isLatinSquare_cyclicLatinSquare n
    · intro i j a hcell
      exact False.elim (hfilled ⟨i, j, a, hcell⟩)

theorem latin_square_completion_order_zero (P : Fin 0 → Fin 0 → Option (Fin 0)) :
    ∃ L : Fin 0 → Fin 0 → Fin 0, Completes P L := by
  refine ⟨fun i => Fin.elim0 i, ?_⟩
  simp [Completes, IsLatinSquare]

theorem latin_square_completion_order_one (P : Fin 1 → Fin 1 → Option (Fin 1)) :
    ∃ L : Fin 1 → Fin 1 → Fin 1, Completes P L := by
  refine ⟨fun _ _ => 0, ?_⟩
  constructor
  · constructor
    · intro _i x y _h
      exact Subsingleton.elim x y
    · intro _j x y _h
      exact Subsingleton.elim x y
  · intro _i _j _a _hP
    exact Subsingleton.elim _ _

theorem latin_square_completion_order_le_one (n : ℕ) (hn : n ≤ 1)
    (P : Fin n → Fin n → Option (Fin n)) :
    ∃ L : Fin n → Fin n → Fin n, Completes P L := by
  interval_cases n
  · simpa using latin_square_completion_order_zero P
  · simpa using latin_square_completion_order_one P

private def latinSquareFinTwoWithCell (i₀ j₀ a₀ : Fin 2) : Fin 2 → Fin 2 → Fin 2 :=
  fun i j =>
    if i = i₀ then
      if j = j₀ then a₀ else Equiv.swap (0 : Fin 2) 1 a₀
    else
      if j = j₀ then Equiv.swap (0 : Fin 2) 1 a₀ else a₀

private theorem isLatinSquare_latinSquareFinTwoWithCell (i₀ j₀ a₀ : Fin 2) :
    IsLatinSquare (latinSquareFinTwoWithCell i₀ j₀ a₀) := by
  constructor
  · intro i x y hxy
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      fin_cases i₀ <;> fin_cases j₀ <;> fin_cases a₀ <;>
      simp [latinSquareFinTwoWithCell] at hxy ⊢
  · intro j x y hxy
    fin_cases j <;> fin_cases x <;> fin_cases y <;>
      fin_cases i₀ <;> fin_cases j₀ <;> fin_cases a₀ <;>
      simp [latinSquareFinTwoWithCell] at hxy ⊢

private theorem latinSquareFinTwoWithCell_spec (i₀ j₀ a₀ : Fin 2) :
    latinSquareFinTwoWithCell i₀ j₀ a₀ i₀ j₀ = a₀ := by
  simp [latinSquareFinTwoWithCell]

theorem latin_square_completion_order_two
    (P : Fin 2 → Fin 2 → Option (Fin 2))
    (hfilled_le : (filledCells P).card ≤ 1) :
    ∃ L : Fin 2 → Fin 2 → Fin 2, Completes P L := by
  classical
  by_cases hfilled : ∃ i j a, P i j = some a
  · rcases hfilled with ⟨i₀, j₀, a₀, hcell₀⟩
    refine ⟨latinSquareFinTwoWithCell i₀ j₀ a₀, ?_⟩
    constructor
    · exact isLatinSquare_latinSquareFinTwoWithCell i₀ j₀ a₀
    · intro i j a hcell
      have hmem : (i, j) ∈ filledCells P := by
        simp [filledCells, hcell]
      have hmem₀ : (i₀, j₀) ∈ filledCells P := by
        simp [filledCells, hcell₀]
      have hp_eq : (i, j) = (i₀, j₀) :=
        (Finset.card_le_one_iff.mp hfilled_le) hmem hmem₀
      have hi : i = i₀ := congrArg Prod.fst hp_eq
      have hj : j = j₀ := congrArg Prod.snd hp_eq
      subst i
      subst j
      have ha : a = a₀ := by
        have hsome : some a = some a₀ := by
          rw [← hcell, hcell₀]
        exact Option.some.inj hsome
      subst a
      exact latinSquareFinTwoWithCell_spec i₀ j₀ a₀
  · refine ⟨latinSquareFinTwoWithCell 0 0 0, ?_⟩
    constructor
    · exact isLatinSquare_latinSquareFinTwoWithCell 0 0 0
    · intro i j a hcell
      exact False.elim (hfilled ⟨i, j, a, hcell⟩)

theorem latin_square_completion_order_le_two (n : ℕ) (hn : n ≤ 2)
    (P : Fin n → Fin n → Option (Fin n))
    (hfilled_le : (filledCells P).card ≤ n - 1) :
    ∃ L : Fin n → Fin n → Fin n, Completes P L := by
  interval_cases n
  · simpa using latin_square_completion_order_zero P
  · simpa using latin_square_completion_order_one P
  · simpa using latin_square_completion_order_two P hfilled_le

theorem latin_square_completion_theorem_order_le_two (n : ℕ) (hn : n ≤ 2) :
    LatinSquareCompletionTheorem n := by
  intro P _hP hfilled_le
  exact latin_square_completion_order_le_two n hn P hfilled_le

/--
The exact-cardinality Evans/Smetaniuk premise is already unconditional in the
degenerate and order-two cases.
-/
theorem evansExactCardinalityCase_le_two (n : ℕ) (hn : n ≤ 2) :
    EvansExactCardinalityCase n := by
  intro P _hP hcard
  exact latin_square_completion_order_le_two n hn P (by omega)

private theorem finThree_sub_eq_zero_iff_eq (x y : Fin 3) : x - y = 0 ↔ x = y := by
  fin_cases x <;> fin_cases y <;> decide

private theorem finThree_mul_sub (u x y : Fin 3) :
    u * (x - y) = u * x - u * y := by
  fin_cases u <;> fin_cases x <;> fin_cases y <;> decide

private theorem finThree_sub_add_sub (a b c d : Fin 3) :
    (a - b) + (c - d) = (a + c) - (b + d) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

private theorem finThree_add_sub_of_sub_eq {x y a b : Fin 3}
    (h : x - y = b - a) : x + (a - y) = b := by
  fin_cases x <;> fin_cases y <;> fin_cases a <;> fin_cases b <;> revert h <;> decide

private theorem exists_nonzero_mul_add_eq_finThree
    (di dj da : Fin 3) (hnot : di ≠ 0 ∨ dj ≠ 0)
    (hrow : di = 0 → da ≠ 0) (hcol : dj = 0 → da ≠ 0) :
    ∃ u v : Fin 3, u ≠ 0 ∧ v ≠ 0 ∧ u * di + v * dj = da := by
  fin_cases di <;> fin_cases dj <;> fin_cases da <;>
    simp at hnot hrow hcol ⊢ <;> decide

private theorem mul_left_cancel_finThree {u x y : Fin 3} (hu : u ≠ 0)
    (h : u * x = u * y) : x = y := by
  fin_cases u <;> simp at hu h ⊢
  all_goals fin_cases x <;> fin_cases y <;> simp at h ⊢

/-- The linear Latin squares of order three over `Fin 3`. -/
private def linearLatinFinThree (u v c : Fin 3) : Fin 3 → Fin 3 → Fin 3 :=
  fun i j => u * i + v * j + c

private theorem isLatinSquare_linearLatinFinThree {u v c : Fin 3}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    IsLatinSquare (linearLatinFinThree u v c) := by
  constructor
  · intro i x y hxy
    unfold linearLatinFinThree at hxy
    have h1 : u * i + v * x = u * i + v * y := add_right_cancel hxy
    have h2 : v * x = v * y := add_left_cancel h1
    exact mul_left_cancel_finThree hv h2
  · intro j x y hxy
    unfold linearLatinFinThree at hxy
    have h1 : u * x + v * j = u * y + v * j := add_right_cancel hxy
    have h2 : u * x = u * y := add_right_cancel h1
    exact mul_left_cancel_finThree hu h2

private theorem linearLatinFinThree_spec_left
    (u v i j a : Fin 3) :
    linearLatinFinThree u v (a - (u * i + v * j)) i j = a := by
  fin_cases u <;> fin_cases v <;> fin_cases i <;> fin_cases j <;> fin_cases a <;>
    decide

private theorem linearLatinFinThree_spec_right
    (u v i₁ j₁ a₁ i₂ j₂ a₂ : Fin 3)
    (h : u * (i₂ - i₁) + v * (j₂ - j₁) = a₂ - a₁) :
    linearLatinFinThree u v (a₁ - (u * i₁ + v * j₁)) i₂ j₂ = a₂ := by
  apply finThree_add_sub_of_sub_eq
  calc
    u * i₂ + v * j₂ - (u * i₁ + v * j₁)
        = (u * i₂ - u * i₁) + (v * j₂ - v * j₁) := by
            rw [finThree_sub_add_sub]
    _ = u * (i₂ - i₁) + v * (j₂ - j₁) := by
            rw [finThree_mul_sub, finThree_mul_sub]
    _ = a₂ - a₁ := h

private theorem latin_square_completion_order_three_two_cells
    (P : Fin 3 → Fin 3 → Option (Fin 3)) (hP : IsPartialLatin P)
    {i₁ j₁ a₁ i₂ j₂ a₂ : Fin 3}
    (hcell₁ : P i₁ j₁ = some a₁) (hcell₂ : P i₂ j₂ = some a₂)
    (hne : (i₁, j₁) ≠ (i₂, j₂))
    (hfilled_le : (filledCells P).card ≤ 2) :
    ∃ L : Fin 3 → Fin 3 → Fin 3, Completes P L := by
  classical
  have hnot : i₂ - i₁ ≠ 0 ∨ j₂ - j₁ ≠ 0 := by
    by_contra h
    push Not at h
    have hi₂ : i₂ = i₁ := (finThree_sub_eq_zero_iff_eq i₂ i₁).mp h.1
    have hj₂ : j₂ = j₁ := (finThree_sub_eq_zero_iff_eq j₂ j₁).mp h.2
    exact hne (Prod.ext hi₂.symm hj₂.symm)
  have hrow : i₂ - i₁ = 0 → a₂ - a₁ ≠ 0 := by
    intro hi hsym
    have hi₂ : i₂ = i₁ := (finThree_sub_eq_zero_iff_eq i₂ i₁).mp hi
    have ha₂ : a₂ = a₁ := (finThree_sub_eq_zero_iff_eq a₂ a₁).mp hsym
    have hcell₂' : P i₁ j₂ = some a₁ := by simpa [hi₂, ha₂] using hcell₂
    have hj : j₁ = j₂ := hP.1 i₁ j₁ j₂ a₁ hcell₁ hcell₂'
    exact hne (Prod.ext hi₂.symm hj)
  have hcol : j₂ - j₁ = 0 → a₂ - a₁ ≠ 0 := by
    intro hj hsym
    have hj₂ : j₂ = j₁ := (finThree_sub_eq_zero_iff_eq j₂ j₁).mp hj
    have ha₂ : a₂ = a₁ := (finThree_sub_eq_zero_iff_eq a₂ a₁).mp hsym
    have hcell₂' : P i₂ j₁ = some a₁ := by simpa [hj₂, ha₂] using hcell₂
    have hi : i₁ = i₂ := hP.2 i₁ i₂ j₁ a₁ hcell₁ hcell₂'
    exact hne (Prod.ext hi hj₂.symm)
  obtain ⟨u, v, hu, hv, hsolve⟩ :=
    exists_nonzero_mul_add_eq_finThree (i₂ - i₁) (j₂ - j₁) (a₂ - a₁) hnot hrow hcol
  let c : Fin 3 := a₁ - (u * i₁ + v * j₁)
  refine ⟨linearLatinFinThree u v c, ?_⟩
  constructor
  · exact isLatinSquare_linearLatinFinThree hu hv
  · intro i j a hcell
    let S := filledCells P
    have hmem : (i, j) ∈ S := by simp [S, filledCells, hcell]
    have hmem₁ : (i₁, j₁) ∈ S := by simp [S, filledCells, hcell₁]
    have hmem₂ : (i₂, j₂) ∈ S := by simp [S, filledCells, hcell₂]
    by_cases hp₁ : (i, j) = (i₁, j₁)
    · have hi : i = i₁ := congrArg Prod.fst hp₁
      have hj : j = j₁ := congrArg Prod.snd hp₁
      subst i
      subst j
      have ha : a = a₁ := by
        have hsome : some a = some a₁ := by rw [← hcell, hcell₁]
        exact Option.some.inj hsome
      subst a
      exact linearLatinFinThree_spec_left u v i₁ j₁ a₁
    · have hcard_erase : (S.erase (i₁, j₁)).card ≤ 1 := by
        have hcard : S.card ≤ 2 := hfilled_le
        rw [Finset.card_erase_of_mem hmem₁]
        omega
      have hmem_erase : (i, j) ∈ S.erase (i₁, j₁) := by simp [hmem, hp₁]
      have hmem₂_erase : (i₂, j₂) ∈ S.erase (i₁, j₁) := by simp [hmem₂, hne.symm]
      have hp₂ : (i, j) = (i₂, j₂) :=
        (Finset.card_le_one_iff.mp hcard_erase) hmem_erase hmem₂_erase
      have hi : i = i₂ := congrArg Prod.fst hp₂
      have hj : j = j₂ := congrArg Prod.snd hp₂
      subst i
      subst j
      have ha : a = a₂ := by
        have hsome : some a = some a₂ := by rw [← hcell, hcell₂]
        exact Option.some.inj hsome
      subst a
      exact linearLatinFinThree_spec_right u v i₁ j₁ a₁ i₂ j₂ a₂ hsolve

theorem latin_square_completion_order_three
    (P : Fin 3 → Fin 3 → Option (Fin 3))
    (hP : IsPartialLatin P) (hfilled_le : (filledCells P).card ≤ 2) :
    ∃ L : Fin 3 → Fin 3 → Fin 3, Completes P L := by
  classical
  by_cases hle_one : (filledCells P).card ≤ 1
  · exact latin_square_completion_card_le_one P hle_one
  · have hone_lt : 1 < (filledCells P).card := by omega
    obtain ⟨p₁, hp₁, p₂, hp₂, hpne⟩ := Finset.one_lt_card.mp hone_lt
    obtain ⟨a₁, hcell₁⟩ : ∃ a, P p₁.1 p₁.2 = some a := by
      have hs : (P p₁.1 p₁.2).isSome := by simpa [filledCells] using hp₁
      cases hopt : P p₁.1 p₁.2 with
      | none => simp [hopt] at hs
      | some a => exact ⟨a, rfl⟩
    obtain ⟨a₂, hcell₂⟩ : ∃ a, P p₂.1 p₂.2 = some a := by
      have hs : (P p₂.1 p₂.2).isSome := by simpa [filledCells] using hp₂
      cases hopt : P p₂.1 p₂.2 with
      | none => simp [hopt] at hs
      | some a => exact ⟨a, rfl⟩
    exact latin_square_completion_order_three_two_cells P hP hcell₁ hcell₂ hpne hfilled_le

theorem latin_square_completion_order_le_three (n : ℕ) (hn : n ≤ 3)
    (P : Fin n → Fin n → Option (Fin n))
    (hP : IsPartialLatin P) (hfilled_le : (filledCells P).card ≤ n - 1) :
    ∃ L : Fin n → Fin n → Fin n, Completes P L := by
  interval_cases n
  · simpa using latin_square_completion_order_zero P
  · simpa using latin_square_completion_order_one P
  · simpa using latin_square_completion_order_two P hfilled_le
  · simpa using latin_square_completion_order_three P hP hfilled_le

theorem latin_square_completion_theorem_order_le_three (n : ℕ) (hn : n ≤ 3) :
    LatinSquareCompletionTheorem n := by
  intro P hP hfilled_le
  exact latin_square_completion_order_le_three n hn P hP hfilled_le

theorem evansExactCardinalityCase_of_completion {n : ℕ}
    (hcomplete : LatinSquareCompletionTheorem n) :
    EvansExactCardinalityCase n := by
  intro P hP hcard
  exact hcomplete P hP (by omega)

/--
The proved padding reduction is sharp: for each fixed order, the full
`≤ n - 1` Evans theorem is equivalent to the exact `= n - 1` case.
-/
theorem latinSquareCompletionTheorem_iff_exact (n : ℕ) :
    LatinSquareCompletionTheorem n ↔ EvansExactCardinalityCase n :=
  ⟨evansExactCardinalityCase_of_completion, completion_from_exact_cardinality_case⟩

theorem evansExactCardinalityCase_le_three (n : ℕ) (hn : n ≤ 3) :
    EvansExactCardinalityCase n :=
  evansExactCardinalityCase_of_completion (latin_square_completion_theorem_order_le_three n hn)

theorem evansExactCardinalityCase_three : EvansExactCardinalityCase 3 :=
  evansExactCardinalityCase_le_three 3 (by omega)

theorem chapter33_order_le_three (n : ℕ) (hn : n ≤ 3) :
    LatinSquareCompletionTheorem n :=
  completion_from_exact_cardinality_case (evansExactCardinalityCase_le_three n hn)

theorem chapter33_three : LatinSquareCompletionTheorem 3 :=
  chapter33_order_le_three 3 (by omega)

def EvansNormalizedCellCase (n : ℕ) (iTarget jTarget aTarget : Fin n) : Prop :=
  ∀ P : Fin n → Fin n → Option (Fin n),
    IsPartialLatin P → (filledCells P).card = n - 1 →
      P iTarget jTarget = some aTarget →
        ∃ L : Fin n → Fin n → Fin n, Completes P L

private def lastIndex (n : ℕ) (hn : 0 < n) : Fin n :=
  ⟨n - 1, by omega⟩

theorem evansExactCardinalityCase_of_normalizedCellCase {n : ℕ}
    (hn : 2 ≤ n) {iTarget jTarget aTarget : Fin n}
    (hnormal : EvansNormalizedCellCase n iTarget jTarget aTarget) :
    EvansExactCardinalityCase n :=
  evansExactCardinalityCase_of_normalized_cell_case hn iTarget jTarget aTarget hnormal

theorem evansExactCardinalityCase_all_of_normalized_ge_four
    (hnormal : ∀ n (hnpos : 0 < n), 4 ≤ n →
      EvansNormalizedCellCase n
        (lastIndex n hnpos) (lastIndex n hnpos) (lastIndex n hnpos)) :
    ∀ n, EvansExactCardinalityCase n := by
  intro n
  by_cases hsmall : n ≤ 3
  · exact evansExactCardinalityCase_le_three n hsmall
  · have hge_four : 4 ≤ n := by omega
    have hnpos : 0 < n := by omega
    exact evansExactCardinalityCase_of_normalizedCellCase (n := n) (by omega)
      (hnormal n hnpos hge_four)

theorem chapter33_unconditional_of_normalized_ge_four
    (hnormal : ∀ n (hnpos : 0 < n), 4 ≤ n →
      EvansNormalizedCellCase n
        (lastIndex n hnpos) (lastIndex n hnpos) (lastIndex n hnpos)) :
    ∀ n, LatinSquareCompletionTheorem n :=
  fun n =>
    completion_from_exact_cardinality_case
      ((evansExactCardinalityCase_all_of_normalized_ge_four hnormal) n)

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
Use the sparse Hall row step to fill a genuinely empty row of a partial Latin
square.  This packages the row returned by Hall into a new partial square and
proves the state update preserves both extension and the partial Latin
property.  It is still only one state update; after the row is filled the
global `≤ n - 1` count needed by the sparse Hall lemma need not remain true.
-/
theorem extend_partialLatin_empty_row {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (hP : IsPartialLatin P)
    (hfilled_le : (filledCells P).card ≤ n - 1) {i₀ : Fin n}
    (hempty : ∀ j, P i₀ j = none) :
    ∃ Q : Fin n → Fin n → Option (Fin n),
      IsPartialLatin Q ∧ ExtendsPartial P Q ∧ ∀ j, ∃ a, Q i₀ j = some a := by
  classical
  have hused_witness : ∀ j a, a ∈ colSymbols P j → ∃ i, P i j = some a := by
    intro j a ha
    simpa [colSymbols] using ha
  obtain ⟨row, hrow, havoid⟩ :=
    latin_square_completion_step_from_partial P (colSymbols P) hused_witness hfilled_le
  refine ⟨setRow P i₀ row, ?_, ?_, ?_⟩
  · exact isPartialLatin_setRow_of_empty hP hempty hrow havoid
  · exact extendsPartial_setRow_of_empty P hempty
  · intro j
    exact ⟨row j, by simp [setRow]⟩

/--
The same sparse Hall state update, with the exact filled-cell count after the
empty row is filled.  This records precisely how far the naive row iteration
moves the state: one empty row update adds `n` filled cells.
-/
theorem extend_partialLatin_empty_row_with_card {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (hP : IsPartialLatin P)
    (hfilled_le : (filledCells P).card ≤ n - 1) {i₀ : Fin n}
    (hempty : ∀ j, P i₀ j = none) :
    ∃ Q : Fin n → Fin n → Option (Fin n),
      IsPartialLatin Q ∧ ExtendsPartial P Q ∧
        (∀ j, ∃ a, Q i₀ j = some a) ∧
        (filledCells Q).card = (filledCells P).card + n := by
  classical
  have hused_witness : ∀ j a, a ∈ colSymbols P j → ∃ i, P i j = some a := by
    intro j a ha
    simpa [colSymbols] using ha
  obtain ⟨row, hrow, havoid⟩ :=
    latin_square_completion_step_from_partial P (colSymbols P) hused_witness hfilled_le
  refine ⟨setRow P i₀ row, ?_, ?_, ?_, ?_⟩
  · exact isPartialLatin_setRow_of_empty hP hempty hrow havoid
  · exact extendsPartial_setRow_of_empty P hempty
  · intro j
    exact ⟨row j, by simp [setRow]⟩
  · exact filledCells_setRow_card_of_empty P hempty

/--
Sparse Hall row update without explicitly specifying the empty row: if a
partial Latin square has at most `n - 1` filled cells, then some empty row can
be filled completely, preserving the partial Latin property and adding exactly
`n` cells.
-/
theorem extend_partialLatin_some_empty_row_with_card {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (hP : IsPartialLatin P)
    (hn : 0 < n) (hfilled_le : (filledCells P).card ≤ n - 1) :
    ∃ i₀ : Fin n, ∃ Q : Fin n → Fin n → Option (Fin n),
      IsPartialLatin Q ∧ ExtendsPartial P Q ∧
        (∀ j, ∃ a, Q i₀ j = some a) ∧
        (filledCells Q).card = (filledCells P).card + n := by
  obtain ⟨i₀, hempty⟩ := exists_empty_row_of_filledCells_le_pred P hn hfilled_le
  obtain ⟨Q, hQ, hPQ, hrow, hcard⟩ :=
    extend_partialLatin_empty_row_with_card P hP hfilled_le hempty
  exact ⟨i₀, Q, hQ, hPQ, hrow, hcard⟩

/--
The actual marriage condition for the sparse row-completion step.  For the
true column-symbol sets of a partial square, Hall's inequality follows from
the double-counting argument above and is not an external assumption.
-/
theorem chapter33_hall_condition {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (hfilled_le : (filledCells P).card ≤ n - 1) :
    ∀ S : Finset (Fin n),
      S.card ≤ (S.biUnion fun j => Finset.univ.filter (· ∉ colSymbols P j)).card := by
  have hused_witness : ∀ j a, a ∈ colSymbols P j → ∃ i, P i j = some a := by
    intro j a ha
    simpa [colSymbols] using ha
  intro S
  simpa [available] using hall_from_partial_square P (colSymbols P) hused_witness hfilled_le S

/--
The genuine Hall row-completion step from the sparse partial-square hypotheses.
The marriage condition is proved by `chapter33_hall_condition`, so this public
row-step interface exposes only the partial square and its sparse count.
-/
theorem chapter33_row_completion_step {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (hfilled_le : (filledCells P).card ≤ n - 1) :
    ∃ row : Fin n → Fin n, Function.Injective row ∧ ∀ j, row j ∉ colSymbols P j := by
  have hHall := chapter33_hall_condition P hfilled_le
  have := hall_system_of_distinct_representatives
    (fun j : Fin n => Finset.univ.filter (· ∉ colSymbols P j)) hHall
  obtain ⟨choice, hinj, hmem⟩ := this
  exact ⟨choice, hinj, fun j => by simpa using hmem j⟩

theorem chapter33_column_row_completion_step {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (hfilled_le : (filledCells P).card ≤ n - 1) :
    ∃ row : Fin n → Fin n, Function.Injective row ∧ ∀ j, row j ∉ colSymbols P j :=
  chapter33_row_completion_step P hfilled_le

/--
Canonical Chapter 33 entry point: the full Latin-square completion theorem,
reduced to the exact-cardinality Evans/Smetaniuk switching case.

The missing unconditional ingredient is precisely `EvansExactCardinalityCase n`;
the Hall row step above cannot simply be iterated after a whole row is added.
-/
theorem chapter33 {n : ℕ} (hexact : EvansExactCardinalityCase n) :
    LatinSquareCompletionTheorem n :=
  completion_from_exact_cardinality_case hexact

/-- Canonical Chapter 33 is fully unconditional in orders `0`, `1`, `2`, and `3`. -/
theorem chapter33_low_dim (n : ℕ) (hn : n ≤ 3) :
    LatinSquareCompletionTheorem n :=
  chapter33 (evansExactCardinalityCase_le_three n hn)

end ProofsInTheBook.Chapter33
