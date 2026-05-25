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
row-completion Hall step for a sparse partial square, the standard extension
of a Latin rectangle by one row, and the padding reduction
`completion_from_exact_cardinality_case`, which proves that the `|P| ≤ n - 1`
case reduces to the exact `|P| = n - 1` Evans case by adding legal entries one
at a time.  The complete completion theorem is also discharged for all partial
squares with at most one filled cell and for orders `0`, `1`, and `2`.
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

Squares with at most one filled cell, and orders `0`, `1`, and `2`, do not
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
The genuine Hall row-completion step from the sparse partial-square hypotheses.
Hall's condition is proved internally, but this theorem is only a one-row step:
it is not by itself an iteration proof of the full Evans/Smetaniuk theorem.
-/
theorem chapter33_row_completion_step {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (usedInCol : Fin n → Finset (Fin n))
    (_hused : ∀ j, (usedInCol j).card < n)
    (hused_witness : ∀ j a, a ∈ usedInCol j → ∃ i, P i j = some a)
    (hfilled_le : (filledCells P).card ≤ n - 1) :
    ∃ row : Fin n → Fin n, Function.Injective row ∧ ∀ j, row j ∉ usedInCol j :=
  latin_square_completion_step_from_partial P usedInCol _hused hused_witness hfilled_le

/--
Canonical Chapter 33 entry point: the full Latin-square completion theorem,
reduced to the exact-cardinality Evans/Smetaniuk switching case.

The missing unconditional ingredient is precisely `EvansExactCardinalityCase n`;
the Hall row step above cannot simply be iterated after a whole row is added.
-/
theorem chapter33 {n : ℕ} (hexact : EvansExactCardinalityCase n) :
    LatinSquareCompletionTheorem n :=
  completion_from_exact_cardinality_case hexact

/-- Canonical Chapter 33 is fully unconditional in orders `0`, `1`, and `2`. -/
theorem chapter33_low_dim (n : ℕ) (hn : n ≤ 2) :
    LatinSquareCompletionTheorem n :=
  chapter33 (evansExactCardinalityCase_le_two n hn)

end ProofsInTheBook.Chapter33
