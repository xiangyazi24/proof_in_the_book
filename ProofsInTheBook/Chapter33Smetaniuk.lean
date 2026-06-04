import ProofsInTheBook.Chapter33

open Finset
open Classical

namespace ProofsInTheBook.Chapter33

/-!
# Chapter 33: Smetaniuk switching frontier

This file isolates the coordinate bookkeeping for Smetaniuk's normalized
induction.  The hard switching lemma is deliberately left as a named
proposition, not as an unproved theorem.
-/

/-- A symbol occurs in exactly one filled cell. -/
def SymbolOccursExactlyOnce {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (a : Fin n) : Prop :=
  ∃! ij : Fin n × Fin n, P ij.1 ij.2 = some a

/-- All filled cells not using the distinguished symbol lie strictly above the
main diagonal. -/
def StrictUpperTriangle {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (newSym : Fin n) : Prop :=
  ∀ i j s, P i j = some s → s ≠ newSym → i < j

/-- The distinguished symbol occurs exactly once, at the prescribed main
diagonal cell. -/
def MainDiagonalNewSymbol {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (d newSym : Fin n) : Prop :=
  P d d = some newSym ∧ SymbolOccursExactlyOnce P newSym

/-- The strengthened normalized Smetaniuk invariant requested by the handoff. -/
def SmetaniukTriangularNormalized {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (d newSym : Fin n) : Prop :=
  MainDiagonalNewSymbol P d newSym ∧ StrictUpperTriangle P newSym

lemma mainDiagonalNewSymbol_cell_eq {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} {d newSym i j : Fin n}
    (hmain : MainDiagonalNewSymbol P d newSym)
    (hcell : P i j = some newSym) : i = d ∧ j = d := by
  rcases hmain with ⟨hdiag, huniq⟩
  rcases huniq with ⟨ij₀, hij₀, huniq₀⟩
  have hij : (i, j) = ij₀ := huniq₀ (i, j) hcell
  have hdd : (d, d) = ij₀ := huniq₀ (d, d) hdiag
  have hp : (i, j) = (d, d) := hij.trans hdd.symm
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

lemma fin_castSucc_ne_last {N : ℕ} (i : Fin N) :
    (Fin.castSucc i : Fin (N + 1)) ≠ Fin.last N := by
  intro h
  have hv : i.val = N := by
    simpa [Fin.castSucc, Fin.last] using congrArg Fin.val h
  exact (Nat.ne_of_lt i.isLt) hv

lemma fin_succ_ne_zero {N : ℕ} (i : Fin N) :
    (Fin.succ i : Fin (N + 1)) ≠ 0 := by
  intro h
  have hv : i.val + 1 = 0 := by
    simpa [Fin.succ] using congrArg Fin.val h
  omega

lemma fin_zero_ne_last {N : ℕ} (hN : 0 < N) :
    (0 : Fin (N + 1)) ≠ Fin.last N := by
  intro h
  have hv : (0 : ℕ) = N := by
    simpa [Fin.last] using congrArg Fin.val h
  omega

/-- Drop the last symbol when passing from order `N + 1` to order `N`. -/
def dropLastSymbol {N : ℕ} (a : Fin (N + 1)) : Option (Fin N) :=
  if h : a.val < N then some ⟨a.val, h⟩ else none

@[simp] lemma dropLastSymbol_castSucc {N : ℕ} (a : Fin N) :
    dropLastSymbol (Fin.castSucc a : Fin (N + 1)) = some a := by
  unfold dropLastSymbol
  have h : (Fin.castSucc a : Fin (N + 1)).val < N := by
    simp [Fin.castSucc]
  simp

lemma dropLastSymbol_eq_some {N : ℕ} {a : Fin (N + 1)} {b : Fin N}
    (h : dropLastSymbol a = some b) : a = Fin.castSucc b := by
  unfold dropLastSymbol at h
  by_cases ha : a.val < N
  · simp [ha] at h
    have hb : (⟨a.val, ha⟩ : Fin N) = b := h
    exact Fin.ext (by simpa [Fin.castSucc] using congrArg Fin.val hb)
  · simp [ha] at h

/-- Reverse columns; this is the move from main-diagonal to back-diagonal
coordinates. -/
def reverseColumnsPartial {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) :
    Fin n → Fin n → Option (Fin n) :=
  relabelPartial (Equiv.refl (Fin n)) Fin.revPerm (Equiv.refl (Fin n)) P

@[simp] lemma reverseColumnsPartial_eq {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (i j : Fin n) :
    reverseColumnsPartial P i j = P i (Fin.rev j) := by
  simp [reverseColumnsPartial, relabelPartial]

lemma isPartialLatin_reverseColumnsPartial {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)}
    (hP : IsPartialLatin P) : IsPartialLatin (reverseColumnsPartial P) :=
  isPartialLatin_relabelPartial (Equiv.refl (Fin n)) Fin.revPerm
    (Equiv.refl (Fin n)) hP

lemma filledCells_reverseColumnsPartial_card {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) :
    (filledCells (reverseColumnsPartial P)).card = (filledCells P).card := by
  simpa [reverseColumnsPartial] using
    filledCells_relabelPartial_card (Equiv.refl (Fin n)) Fin.revPerm
      (Equiv.refl (Fin n)) P

lemma reverseColumnsPartial_last_zero_of_last_last {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    {a : Fin (N + 1)} (h : P (Fin.last N) (Fin.last N) = some a) :
    reverseColumnsPartial P (Fin.last N) 0 = some a := by
  simpa [Fin.rev] using h

lemma reverseColumns_strictUpper_sum_lt {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (htri : StrictUpperTriangle P (Fin.last N))
    {i j s : Fin (N + 1)}
    (hcell : reverseColumnsPartial P i j = some s)
    (hs : s ≠ Fin.last N) : i.val + j.val < N := by
  have hP : P i (Fin.rev j) = some s := by
    simpa using hcell
  have hlt : i < Fin.rev j := htri i (Fin.rev j) s hP hs
  have hrev : (Fin.rev j).val = N - j.val := by
    simp [Fin.rev]
  have hltVal₀ : i.val < (Fin.rev j).val := hlt
  have hltVal : i.val < N - j.val := by
    simpa [hrev] using hltVal₀
  omega

lemma triangularNormalized_col_zero_empty {N : ℕ} (hN : 0 < N)
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (hmain : MainDiagonalNewSymbol P (Fin.last N) (Fin.last N))
    (htri : StrictUpperTriangle P (Fin.last N)) (i : Fin (N + 1)) :
    P i 0 = none := by
  cases hcell : P i 0 with
  | none => rfl
  | some a =>
      exfalso
      by_cases ha : a = Fin.last N
      · have hij := mainDiagonalNewSymbol_cell_eq hmain (by simpa [ha] using hcell)
        exact fin_zero_ne_last hN hij.2
      · have hlt : i < (0 : Fin (N + 1)) := htri i 0 a hcell ha
        have hltVal : i.val < (0 : Fin (N + 1)).val := hlt
        simp at hltVal

lemma triangularNormalized_last_row_cell {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (hmain : MainDiagonalNewSymbol P (Fin.last N) (Fin.last N))
    (htri : StrictUpperTriangle P (Fin.last N))
    {j a : Fin (N + 1)}
    (hcell : P (Fin.last N) j = some a) :
    j = Fin.last N ∧ a = Fin.last N := by
  by_cases ha : a = Fin.last N
  · have hij := mainDiagonalNewSymbol_cell_eq hmain (by simpa [ha] using hcell)
    exact ⟨hij.2, ha⟩
  · have hlt : Fin.last N < j := htri (Fin.last N) j a hcell ha
    have hltVal : N < j.val := by
      simpa [Fin.last] using hlt
    omega

lemma triangularNormalized_last_row_nonlast_empty {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (hmain : MainDiagonalNewSymbol P (Fin.last N) (Fin.last N))
    (htri : StrictUpperTriangle P (Fin.last N))
    {j : Fin (N + 1)} (hj : j ≠ Fin.last N) :
    P (Fin.last N) j = none := by
  cases hcell : P (Fin.last N) j with
  | none => rfl
  | some a =>
      exfalso
      exact hj (triangularNormalized_last_row_cell hmain htri hcell).1

/-!
## Step 1: deletion and shrink in back-diagonal coordinates

For a back-diagonal normalized square `Q`, delete the last row and column `0`.
The retained cell `(i,j)` of the order-`N` problem is `Q i.castSucc j.succ`.
The last symbol is dropped from the symbol type.
-/

def smetShrink {N : ℕ}
    (Q : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))) :
    Fin N → Fin N → Option (Fin N) :=
  fun i j => (Q (Fin.castSucc i) (Fin.succ j)).bind dropLastSymbol

lemma smetShrink_eq_some_iff {N : ℕ}
    (Q : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1)))
    (i j : Fin N) (a : Fin N) :
    smetShrink Q i j = some a ↔
      Q (Fin.castSucc i) (Fin.succ j) = some (Fin.castSucc a) := by
  constructor
  · intro h
    unfold smetShrink at h
    cases hQ : Q (Fin.castSucc i) (Fin.succ j) with
    | none =>
        simp [hQ] at h
    | some b =>
        simp [hQ] at h
        have hb : b = Fin.castSucc a := dropLastSymbol_eq_some h
        simp [hb]
  · intro h
    simp [smetShrink, h]

lemma isPartialLatin_smetShrink {N : ℕ}
    {Q : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (hQ : IsPartialLatin Q) : IsPartialLatin (smetShrink Q) := by
  constructor
  · intro i j₁ j₂ a h₁ h₂
    have h₁Q := (smetShrink_eq_some_iff Q i j₁ a).mp h₁
    have h₂Q := (smetShrink_eq_some_iff Q i j₂ a).mp h₂
    have hcols :
        Fin.succ j₁ = Fin.succ j₂ :=
      hQ.1 (Fin.castSucc i) (Fin.succ j₁) (Fin.succ j₂)
        (Fin.castSucc a) h₁Q h₂Q
    exact Fin.succ_inj.mp hcols
  · intro i₁ i₂ j a h₁ h₂
    have h₁Q := (smetShrink_eq_some_iff Q i₁ j a).mp h₁
    have h₂Q := (smetShrink_eq_some_iff Q i₂ j a).mp h₂
    have hrows :
        Fin.castSucc i₁ = Fin.castSucc i₂ :=
      hQ.2 (Fin.castSucc i₁) (Fin.castSucc i₂) (Fin.succ j)
        (Fin.castSucc a) h₁Q h₂Q
    exact Fin.castSucc_inj.mp hrows

lemma filledCells_smetShrink_card_le_erase_backCorner {N : ℕ}
    (Q : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))) :
    (filledCells (smetShrink Q)).card ≤
      ((filledCells Q).erase (Fin.last N, (0 : Fin (N + 1)))).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun ij : Fin N × Fin N =>
      ((Fin.castSucc ij.1 : Fin (N + 1)), Fin.succ ij.2)) ?_ ?_
  · intro ij hij
    have hs : (smetShrink Q ij.1 ij.2).isSome := by
      simpa [filledCells] using hij
    cases hcell : smetShrink Q ij.1 ij.2 with
    | none =>
        simp [hcell] at hs
    | some a =>
        have hQ := (smetShrink_eq_some_iff Q ij.1 ij.2 a).mp hcell
        have hne : ((Fin.castSucc ij.1 : Fin (N + 1)), Fin.succ ij.2) ≠
            (Fin.last N, (0 : Fin (N + 1))) := by
          intro hp
          exact fin_castSucc_ne_last ij.1 (congrArg Prod.fst hp)
        simp [filledCells, hQ, hne]
  · intro x hx y hy hxy
    exact Prod.ext
      (Fin.castSucc_inj.mp (congrArg Prod.fst hxy))
      (Fin.succ_inj.mp (congrArg Prod.snd hxy))

theorem smetShrink_step1 {N : ℕ}
    {Q : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (hQ : IsPartialLatin Q)
    (hcorner : Q (Fin.last N) 0 = some (Fin.last N))
    (hcard : (filledCells Q).card = N) :
    IsPartialLatin (smetShrink Q) ∧
      (filledCells (smetShrink Q)).card ≤ N - 1 := by
  constructor
  · exact isPartialLatin_smetShrink hQ
  · have hle := filledCells_smetShrink_card_le_erase_backCorner Q
    have hmem : (Fin.last N, (0 : Fin (N + 1))) ∈ filledCells Q := by
      simp [filledCells, hcorner]
    rw [Finset.card_erase_of_mem hmem] at hle
    omega

theorem smetMainShrink_step1 {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (hP : IsPartialLatin P)
    (hdiag : P (Fin.last N) (Fin.last N) = some (Fin.last N))
    (hcard : (filledCells P).card = N) :
    IsPartialLatin (smetShrink (reverseColumnsPartial P)) ∧
      (filledCells (smetShrink (reverseColumnsPartial P))).card ≤ N - 1 := by
  have hQ : IsPartialLatin (reverseColumnsPartial P) :=
    isPartialLatin_reverseColumnsPartial hP
  have hcorner :
      reverseColumnsPartial P (Fin.last N) 0 = some (Fin.last N) :=
    reverseColumnsPartial_last_zero_of_last_last hdiag
  have hcardQ :
      (filledCells (reverseColumnsPartial P)).card = N := by
    rw [filledCells_reverseColumnsPartial_card]
    exact hcard
  exact smetShrink_step1 hQ hcorner hcardQ

theorem smetMainShrink_completes_from_IH {N : ℕ}
    (hIH : LatinSquareCompletionTheorem N)
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (hP : IsPartialLatin P)
    (hdiag : P (Fin.last N) (Fin.last N) = some (Fin.last N))
    (hcard : (filledCells P).card = N) :
    ∃ L₀ : Fin N → Fin N → Fin N,
      Completes (smetShrink (reverseColumnsPartial P)) L₀ := by
  have hstep := smetMainShrink_step1 hP hdiag hcard
  exact hIH (smetShrink (reverseColumnsPartial P)) hstep.1 hstep.2

/-!
## Smetaniuk's back-diagonal partial square

Given an order-`N` Latin square `L₀`, `smetBackPartial L₀` is the canonical
order-`N + 1` partial square with the new symbol on the back diagonal, `L₀`
below that diagonal, and empty cells above it.
-/

def smetBackPartial {N : ℕ} (L₀ : Fin N → Fin N → Fin N) :
    Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1)) :=
  fun i j =>
    if hdiag : i.val + j.val = N then
      some (Fin.last N)
    else if hlt : i.val + j.val < N then
      some (Fin.castSucc
        (L₀ ⟨i.val, by omega⟩ ⟨j.val, by omega⟩))
    else
      none

lemma smetBackPartial_back_diagonal {N : ℕ} (L₀ : Fin N → Fin N → Fin N)
    {i j : Fin (N + 1)} (hdiag : i.val + j.val = N) :
    smetBackPartial L₀ i j = some (Fin.last N) := by
  simp [smetBackPartial, hdiag]

lemma smetBackPartial_above {N : ℕ} (L₀ : Fin N → Fin N → Fin N)
    {i j : Fin (N + 1)} (habove : N < i.val + j.val) :
    smetBackPartial L₀ i j = none := by
  have hne : i.val + j.val ≠ N := by omega
  have hnlt : ¬ i.val + j.val < N := by omega
  simp [smetBackPartial, hne, hnlt]

lemma isPartialLatin_smetBackPartial {N : ℕ}
    {L₀ : Fin N → Fin N → Fin N} (hL₀ : IsLatinSquare L₀) :
    IsPartialLatin (smetBackPartial L₀) := by
  constructor
  · intro i j₁ j₂ a h₁ h₂
    by_cases hd₁ : i.val + j₁.val = N
    · have ha : a = Fin.last N := by
        simpa [smetBackPartial, hd₁] using h₁.symm
      subst a
      by_cases hd₂ : i.val + j₂.val = N
      · exact Fin.ext (by omega)
      · by_cases hlt₂ : i.val + j₂.val < N
        · have hcast :
              Fin.castSucc
                (L₀ ⟨i.val, by omega⟩ ⟨j₂.val, by omega⟩) =
                Fin.last N := by
            simp [smetBackPartial, hd₂, hlt₂] at h₂
          exact False.elim (fin_castSucc_ne_last _ hcast)
        · simp [smetBackPartial, hd₂, hlt₂] at h₂
    · by_cases hlt₁ : i.val + j₁.val < N
      · by_cases hd₂ : i.val + j₂.val = N
        · have ha : a = Fin.last N := by
            simpa [smetBackPartial, hd₂] using h₂.symm
          subst a
          have hcast :
              Fin.castSucc
                (L₀ ⟨i.val, by omega⟩ ⟨j₁.val, by omega⟩) =
                Fin.last N := by
            simp [smetBackPartial, hd₁, hlt₁] at h₁
          exact False.elim (fin_castSucc_ne_last _ hcast)
        · by_cases hlt₂ : i.val + j₂.val < N
          · let ii₁ : Fin N := ⟨i.val, by omega⟩
            let ii₂ : Fin N := ⟨i.val, by omega⟩
            let jj₁ : Fin N := ⟨j₁.val, by omega⟩
            let jj₂ : Fin N := ⟨j₂.val, by omega⟩
            have hcell₁ : Fin.castSucc (L₀ ii₁ jj₁) = a := by
              simpa [smetBackPartial, hd₁, hlt₁, ii₁, jj₁] using h₁
            have hcell₂ : Fin.castSucc (L₀ ii₂ jj₂) = a := by
              simpa [smetBackPartial, hd₂, hlt₂, ii₂, jj₂] using h₂
            have hii : ii₁ = ii₂ := by
              exact Fin.ext rfl
            have hval : L₀ ii₁ jj₁ = L₀ ii₂ jj₂ :=
              Fin.castSucc_inj.mp (hcell₁.trans hcell₂.symm)
            have hval' : L₀ ii₁ jj₁ = L₀ ii₁ jj₂ := by
              simpa [hii] using hval
            have hjj : jj₁ = jj₂ := hL₀.1 ii₁ hval'
            exact Fin.ext (by simpa [jj₁, jj₂] using congrArg Fin.val hjj)
          · simp [smetBackPartial, hd₂, hlt₂] at h₂
      · simp [smetBackPartial, hd₁, hlt₁] at h₁
  · intro i₁ i₂ j a h₁ h₂
    by_cases hd₁ : i₁.val + j.val = N
    · have ha : a = Fin.last N := by
        simpa [smetBackPartial, hd₁] using h₁.symm
      subst a
      by_cases hd₂ : i₂.val + j.val = N
      · exact Fin.ext (by omega)
      · by_cases hlt₂ : i₂.val + j.val < N
        · have hcast :
              Fin.castSucc
                (L₀ ⟨i₂.val, by omega⟩ ⟨j.val, by omega⟩) =
                Fin.last N := by
            simp [smetBackPartial, hd₂, hlt₂] at h₂
          exact False.elim (fin_castSucc_ne_last _ hcast)
        · simp [smetBackPartial, hd₂, hlt₂] at h₂
    · by_cases hlt₁ : i₁.val + j.val < N
      · by_cases hd₂ : i₂.val + j.val = N
        · have ha : a = Fin.last N := by
            simpa [smetBackPartial, hd₂] using h₂.symm
          subst a
          have hcast :
              Fin.castSucc
                (L₀ ⟨i₁.val, by omega⟩ ⟨j.val, by omega⟩) =
                Fin.last N := by
            simp [smetBackPartial, hd₁, hlt₁] at h₁
          exact False.elim (fin_castSucc_ne_last _ hcast)
        · by_cases hlt₂ : i₂.val + j.val < N
          · let ii₁ : Fin N := ⟨i₁.val, by omega⟩
            let ii₂ : Fin N := ⟨i₂.val, by omega⟩
            let jj₁ : Fin N := ⟨j.val, by omega⟩
            let jj₂ : Fin N := ⟨j.val, by omega⟩
            have hcell₁ : Fin.castSucc (L₀ ii₁ jj₁) = a := by
              simpa [smetBackPartial, hd₁, hlt₁, ii₁, jj₁] using h₁
            have hcell₂ : Fin.castSucc (L₀ ii₂ jj₂) = a := by
              simpa [smetBackPartial, hd₂, hlt₂, ii₂, jj₂] using h₂
            have hjj : jj₁ = jj₂ := by
              exact Fin.ext rfl
            have hval : L₀ ii₁ jj₁ = L₀ ii₂ jj₂ :=
              Fin.castSucc_inj.mp (hcell₁.trans hcell₂.symm)
            have hval' : L₀ ii₁ jj₁ = L₀ ii₂ jj₁ := by
              simpa [hjj] using hval
            have hii : ii₁ = ii₂ := hL₀.2 jj₁ hval'
            exact Fin.ext (by simpa [ii₁, ii₂] using congrArg Fin.val hii)
          · simp [smetBackPartial, hd₂, hlt₂] at h₂
      · simp [smetBackPartial, hd₁, hlt₁] at h₁

def smetMainPartial {N : ℕ} (L₀ : Fin N → Fin N → Fin N) :
    Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1)) :=
  reverseColumnsPartial (smetBackPartial L₀)

lemma isPartialLatin_smetMainPartial {N : ℕ}
    {L₀ : Fin N → Fin N → Fin N} (hL₀ : IsLatinSquare L₀) :
    IsPartialLatin (smetMainPartial L₀) := by
  exact isPartialLatin_reverseColumnsPartial (isPartialLatin_smetBackPartial hL₀)

lemma smetMainPartial_last_last {N : ℕ} (L₀ : Fin N → Fin N → Fin N) :
    smetMainPartial L₀ (Fin.last N) (Fin.last N) = some (Fin.last N) := by
  simp [smetMainPartial, smetBackPartial, Fin.rev]

theorem reverseColumnsPartial_completion_iff {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) :
    (∃ L : Fin n → Fin n → Fin n, Completes (reverseColumnsPartial P) L) ↔
      ∃ L : Fin n → Fin n → Fin n, Completes P L := by
  simpa [reverseColumnsPartial] using
    completion_exists_relabelPartial_iff (Equiv.refl (Fin n)) Fin.revPerm
      (Equiv.refl (Fin n)) P

theorem smetMainPartial_completable_of_smetBackPartial_completable {N : ℕ}
    {L₀ : Fin N → Fin N → Fin N}
    (h : ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
      Completes (smetBackPartial L₀) L) :
    ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
      Completes (smetMainPartial L₀) L := by
  exact (reverseColumnsPartial_completion_iff (smetBackPartial L₀)).mpr h

/-- The exact hard lemma still missing: Smetaniuk's column-switching
construction completes every canonical back-diagonal partial square obtained
from an order-`N` Latin square. -/
def SmetBackDiagonalCompletableCore : Prop :=
  ∀ {N : ℕ}, 3 ≤ N →
    ∀ L₀ : Fin N → Fin N → Fin N,
      IsLatinSquare L₀ →
        ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
          Completes (smetBackPartial L₀) L

theorem smetMainPartial_completable_of_core
    (hcore : SmetBackDiagonalCompletableCore)
    {N : ℕ} (hN : 3 ≤ N) {L₀ : Fin N → Fin N → Fin N}
    (hL₀ : IsLatinSquare L₀) :
    ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
      Completes (smetMainPartial L₀) L := by
  exact smetMainPartial_completable_of_smetBackPartial_completable
    (hcore hN L₀ hL₀)

/-- The normalized theorem that would close the exact-cardinality induction in
orders at least four.  It is recorded as a proposition so the remaining proof
obligation is explicit without introducing an unproved theorem. -/
def SmetaniukExactNormalizedStatement (N : ℕ) : Prop :=
  3 ≤ N →
    ∀ P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1)),
      IsPartialLatin P →
        (filledCells P).card = N →
          SmetaniukTriangularNormalized P (Fin.last N) (Fin.last N) →
            ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
              Completes P L

end ProofsInTheBook.Chapter33
