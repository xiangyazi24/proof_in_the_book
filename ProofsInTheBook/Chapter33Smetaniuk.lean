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

/-!
## The Smetaniuk switching rectangle

The core construction first turns the first `N` rows into an `N × (N + 1)`
Latin rectangle.  Column `N` is used as the temporary holding column.  When
processing a column `c`, the active rows are the bottom rows `N - c, …, N - 1`.
Swapping in the first active row puts the new symbol on the back diagonal; if
that creates a repeated old symbol in the holding column, the repair follows
the unique row carrying that old symbol.  The reachable-row closure below
packages exactly that repair chain.
-/

inductive switchReach {N : ℕ}
    (R : Fin N → Fin (N + 1) → Fin (N + 1)) (c : Fin (N + 1))
    (active : Fin N → Prop) (start : Fin N) : Fin N → Prop
  | start : switchReach R c active start start
  | step {q r : Fin N} :
      switchReach R c active start q →
        active r →
          R r (Fin.last N) = R q c →
            switchReach R c active start r

lemma switchReach_active {N : ℕ}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)} {c : Fin (N + 1)}
    {active : Fin N → Prop} {start i : Fin N}
    (hstart : active start) (h : switchReach R c active start i) :
    active i := by
  induction h with
  | start => exact hstart
  | step _ hr _ _ => exact hr

lemma switchReach_forward {N : ℕ}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)} {c : Fin (N + 1)}
    {active : Fin N → Prop} {start q r : Fin N}
    (hq : switchReach R c active start q) (hr : active r)
    (hval : R r (Fin.last N) = R q c) :
    switchReach R c active start r :=
  switchReach.step hq hr hval

lemma switchReach_backward {N : ℕ}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)} {c : Fin (N + 1)}
    {active : Fin N → Prop} {start i q : Fin N}
    (hcol : Function.Injective fun r : Fin N => R r c)
    (hstartLast : R start (Fin.last N) = Fin.last N)
    (hcol_ne_last : ∀ r : Fin N, R r c ≠ Fin.last N)
    (hi : switchReach R c active start i)
    (hval : R i (Fin.last N) = R q c) :
    switchReach R c active start q := by
  induction hi with
  | start =>
      exfalso
      exact hcol_ne_last q (by simpa [hstartLast] using hval.symm)
  | step hp hr hstep ih =>
      rename_i q₀ r₀
      have hq : q₀ = q := hcol (hstep.symm.trans hval)
      simpa [hq] using hp

noncomputable def smetSwitchColumn {N : ℕ}
    (R : Fin N → Fin (N + 1) → Fin (N + 1)) (c : Fin (N + 1))
    (active : Fin N → Prop) (start : Fin N) :
    Fin N → Fin (N + 1) → Fin (N + 1) :=
  fun i j =>
    if switchReach R c active start i then
      if j = c then R i (Fin.last N)
      else if j = Fin.last N then R i c
      else R i j
    else R i j

lemma smetSwitchColumn_row_injective {N : ℕ}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)} {c : Fin (N + 1)}
    {active : Fin N → Prop} {start : Fin N}
    (hrow : ∀ i : Fin N, Function.Injective (R i))
    (_hc : c ≠ Fin.last N) :
    ∀ i : Fin N, Function.Injective (smetSwitchColumn R c active start i) := by
  intro i j₁ j₂ h
  unfold smetSwitchColumn at h
  by_cases hi : switchReach R c active start i
  · simp [hi] at h
    have hswap :
        (fun j : Fin (N + 1) =>
          if j = c then R i (Fin.last N)
          else if j = Fin.last N then R i c
          else R i j) =
        fun j : Fin (N + 1) => R i ((Equiv.swap c (Fin.last N)) j) := by
      funext j
      by_cases hjc : j = c
      · subst j
        simp
      · by_cases hjl : j = Fin.last N
        · subst j
          simp [hjc]
        · simp [hjc, hjl, Equiv.swap_apply_of_ne_of_ne hjc hjl]
    have h' : R i ((Equiv.swap c (Fin.last N)) j₁) =
        R i ((Equiv.swap c (Fin.last N)) j₂) := by
      exact (congrFun hswap j₁).symm.trans (h.trans (congrFun hswap j₂))
    exact (Equiv.swap c (Fin.last N)).injective ((hrow i) h')
  · simp [hi] at h
    exact hrow i h

lemma smetSwitchColumn_col_ne_injective {N : ℕ}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)} {c d : Fin (N + 1)}
    {active : Fin N → Prop} {start : Fin N}
    (hdc : d ≠ c) (hdl : d ≠ Fin.last N)
    (hcol : Function.Injective fun i : Fin N => R i d) :
    Function.Injective fun i : Fin N => smetSwitchColumn R c active start i d := by
  intro i₁ i₂ h
  unfold smetSwitchColumn at h
  by_cases h₁ : switchReach R c active start i₁ <;>
    by_cases h₂ : switchReach R c active start i₂ <;>
      simp [h₁, h₂, hdc, hdl] at h
  all_goals exact hcol h

lemma smetSwitchColumn_col_c_injective {N : ℕ}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)} {c : Fin (N + 1)}
    {active : Fin N → Prop} {start : Fin N}
    (hcol : Function.Injective fun i : Fin N => R i c)
    (hlastActive :
      ∀ i₁ i₂ : Fin N, active i₁ → active i₂ →
        R i₁ (Fin.last N) = R i₂ (Fin.last N) → i₁ = i₂)
    (hstartActive : active start)
    (hstartLast : R start (Fin.last N) = Fin.last N)
    (hcol_ne_last : ∀ i : Fin N, R i c ≠ Fin.last N) :
    Function.Injective fun i : Fin N => smetSwitchColumn R c active start i c := by
  intro i₁ i₂ h
  unfold smetSwitchColumn at h
  by_cases h₁ : switchReach R c active start i₁
  · by_cases h₂ : switchReach R c active start i₂
    · simp [h₁, h₂] at h
      exact hlastActive i₁ i₂
        (switchReach_active hstartActive h₁)
        (switchReach_active hstartActive h₂) h
    · simp [h₁, h₂] at h
      have h₂reach :
          switchReach R c active start i₂ :=
        switchReach_backward hcol hstartLast hcol_ne_last h₁ h
      exact False.elim (h₂ h₂reach)
  · by_cases h₂ : switchReach R c active start i₂
    · simp [h₁, h₂] at h
      have h₁reach :
          switchReach R c active start i₁ :=
        switchReach_backward hcol hstartLast hcol_ne_last h₂ h.symm
      exact False.elim (h₁ h₁reach)
    · simp [h₁, h₂] at h
      exact hcol h

lemma smetSwitchColumn_last_active_injective {N : ℕ}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)} {c : Fin (N + 1)}
    {active : Fin N → Prop} {start : Fin N}
    (hc : c ≠ Fin.last N)
    (hcol : Function.Injective fun i : Fin N => R i c)
    (hlastActive :
      ∀ i₁ i₂ : Fin N, active i₁ → active i₂ →
        R i₁ (Fin.last N) = R i₂ (Fin.last N) → i₁ = i₂) :
    ∀ i₁ i₂ : Fin N, active i₁ → active i₂ →
      smetSwitchColumn R c active start i₁ (Fin.last N) =
        smetSwitchColumn R c active start i₂ (Fin.last N) →
          i₁ = i₂ := by
  intro i₁ i₂ hi₁ hi₂ h
  have hlast_ne_c : Fin.last N ≠ c := fun hEq => hc hEq.symm
  unfold smetSwitchColumn at h
  by_cases h₁ : switchReach R c active start i₁
  · by_cases h₂ : switchReach R c active start i₂
    · simp [h₁, h₂, hlast_ne_c] at h
      exact hcol h
    · simp [h₁, h₂, hlast_ne_c] at h
      have h₂reach :
          switchReach R c active start i₂ :=
        switchReach_forward h₁ hi₂ h.symm
      exact False.elim (h₂ h₂reach)
  · by_cases h₂ : switchReach R c active start i₂
    · simp [h₁, h₂, hlast_ne_c] at h
      have h₁reach :
          switchReach R c active start i₁ :=
        switchReach_forward h₂ hi₁ h
      exact False.elim (h₁ h₁reach)
    · simp [h₁, h₂] at h
      exact hlastActive i₁ i₂ hi₁ hi₂ h

def smetRectInitial {N : ℕ} (L₀ : Fin N → Fin N → Fin N) :
    Fin N → Fin (N + 1) → Fin (N + 1) :=
  fun i j =>
    if h : j.val < N then
      Fin.castSucc (L₀ i ⟨j.val, h⟩)
    else
      Fin.last N

@[simp] lemma smetRectInitial_old {N : ℕ}
    (L₀ : Fin N → Fin N → Fin N) (i : Fin N) (j : Fin (N + 1))
    (hj : j.val < N) :
    smetRectInitial L₀ i j =
      Fin.castSucc (L₀ i ⟨j.val, hj⟩) := by
  simp [smetRectInitial, hj]

@[simp] lemma smetRectInitial_last {N : ℕ}
    (L₀ : Fin N → Fin N → Fin N) (i : Fin N) :
    smetRectInitial L₀ i (Fin.last N) = Fin.last N := by
  simp [smetRectInitial, Fin.last]

noncomputable def smetRectStep {N : ℕ}
    (R : Fin N → Fin (N + 1) → Fin (N + 1)) (t : ℕ) :
    Fin N → Fin (N + 1) → Fin (N + 1) :=
      if ht : t + 1 < N then
        smetSwitchColumn R ⟨t + 1, by omega⟩
          (fun i : Fin N => N - (t + 1) ≤ i.val)
          ⟨N - (t + 1), by omega⟩
      else
        R

noncomputable def smetRectStage {N : ℕ}
    (L₀ : Fin N → Fin N → Fin N) :
    Nat → Fin N → Fin (N + 1) → Fin (N + 1)
  | 0 => smetRectInitial L₀
  | t + 1 => smetRectStep (smetRectStage L₀ t) t

lemma smetRectInitial_row_injective {N : ℕ}
    {L₀ : Fin N → Fin N → Fin N} (hL₀ : IsLatinSquare L₀) :
    ∀ i : Fin N, Function.Injective (smetRectInitial L₀ i) := by
  intro i j₁ j₂ h
  unfold smetRectInitial at h
  by_cases h₁ : j₁.val < N
  · by_cases h₂ : j₂.val < N
    · simp [h₁, h₂] at h
      have hcols :
          (⟨j₁.val, h₁⟩ : Fin N) = ⟨j₂.val, h₂⟩ :=
        hL₀.1 i h
      exact Fin.ext (by simpa using congrArg Fin.val hcols)
    · simp [h₁, h₂] at h
  · by_cases h₂ : j₂.val < N
    · simp [h₁, h₂] at h
      exact False.elim (fin_castSucc_ne_last _ h.symm)
    · have hj₁ : j₁ = Fin.last N := Fin.ext (by
        have hj₁le : j₁.val ≤ N := Nat.lt_succ_iff.mp j₁.isLt
        have hj₁ge : N ≤ j₁.val := Nat.le_of_not_gt h₁
        simpa [Fin.last] using le_antisymm hj₁le hj₁ge)
      have hj₂ : j₂ = Fin.last N := Fin.ext (by
        have hj₂le : j₂.val ≤ N := Nat.lt_succ_iff.mp j₂.isLt
        have hj₂ge : N ≤ j₂.val := Nat.le_of_not_gt h₂
        simpa [Fin.last] using le_antisymm hj₂le hj₂ge)
      exact hj₁.trans hj₂.symm

lemma smetRectInitial_col_injective {N : ℕ}
    {L₀ : Fin N → Fin N → Fin N} (hL₀ : IsLatinSquare L₀)
    (j : Fin (N + 1)) (hj : j.val < N) :
    Function.Injective fun i : Fin N => smetRectInitial L₀ i j := by
  intro i₁ i₂ h
  simp [smetRectInitial, hj] at h
  exact hL₀.2 ⟨j.val, hj⟩ h

structure SmetRectStageInvariant {N : ℕ}
    (L₀ : Fin N → Fin N → Fin N) (t : ℕ)
    (R : Fin N → Fin (N + 1) → Fin (N + 1)) : Prop where
  row_inj : ∀ i : Fin N, Function.Injective (R i)
  col_inj : ∀ j : Fin (N + 1), j.val < N →
    Function.Injective fun i : Fin N => R i j
  last_active_inj : ∀ i₁ i₂ : Fin N, N - t ≤ i₁.val → N - t ≤ i₂.val →
    R i₁ (Fin.last N) = R i₂ (Fin.last N) → i₁ = i₂
  last_unactive_new : ∀ i : Fin N, i.val < N - t →
    R i (Fin.last N) = Fin.last N
  unprocessed : ∀ (i : Fin N) (j : Fin (N + 1)) (_htj : t < j.val)
    (hj : j.val < N),
      R i j = Fin.castSucc (L₀ i ⟨j.val, hj⟩)
  required_old : ∀ (i : Fin N) (j : Fin (N + 1)) (hj : j.val < N),
    i.val + j.val < N →
      R i j = Fin.castSucc (L₀ i ⟨j.val, hj⟩)
  diag_active : ∀ i : Fin N, N - t ≤ i.val →
    R i ⟨N - i.val, by omega⟩ = Fin.last N

lemma smetRectInitial_invariant {N : ℕ}
    {L₀ : Fin N → Fin N → Fin N} (hL₀ : IsLatinSquare L₀)
    (hN : 0 < N) :
    SmetRectStageInvariant L₀ 0 (smetRectInitial L₀) := by
  constructor
  · exact smetRectInitial_row_injective hL₀
  · exact smetRectInitial_col_injective hL₀
  · intro i₁ _i₂ hi₁ _hi₂ _h
    have : i₁.val < N := i₁.isLt
    omega
  · intro i _hi
    exact smetRectInitial_last L₀ i
  · intro i j _htj hj
    exact smetRectInitial_old L₀ i j hj
  · intro i j hj _hij
    exact smetRectInitial_old L₀ i j hj
  · intro i hi
    have : i.val < N := i.isLt
    omega

lemma smetRectStep_invariant {N t : ℕ}
    {L₀ : Fin N → Fin N → Fin N}
    {R : Fin N → Fin (N + 1) → Fin (N + 1)}
    (ht : t + 1 < N)
    (inv : SmetRectStageInvariant L₀ t R) :
    SmetRectStageInvariant L₀ (t + 1) (smetRectStep R t) := by
  let c : Fin (N + 1) := ⟨t + 1, by omega⟩
  let active : Fin N → Prop := fun i => N - (t + 1) ≤ i.val
  let start : Fin N := ⟨N - (t + 1), by omega⟩
  have hstep :
      smetRectStep R t = smetSwitchColumn R c active start := by
    unfold smetRectStep
    simp [ht, c, active, start]
  rw [hstep]
  have hc_ltN : c.val < N := by
    dsimp [c]
    omega
  have hc_ne_last : c ≠ Fin.last N := by
    intro h
    have hv : c.val = N := by simpa [Fin.last] using congrArg Fin.val h
    dsimp [c] at hv
    omega
  have hstartActive : active start := by
    dsimp [active, start]
    omega
  have hstartLast : R start (Fin.last N) = Fin.last N := by
    exact inv.last_unactive_new start (by dsimp [start]; omega)
  have hcolC : Function.Injective fun i : Fin N => R i c :=
    inv.col_inj c hc_ltN
  have hcol_ne_last : ∀ i : Fin N, R i c ≠ Fin.last N := by
    intro i
    have hval : R i c = Fin.castSucc (L₀ i ⟨c.val, hc_ltN⟩) :=
      inv.unprocessed i c (by dsimp [c]; omega) hc_ltN
    rw [hval]
    exact fin_castSucc_ne_last _
  have oldLast_ne_last :
      ∀ i : Fin N, N - t ≤ i.val → R i (Fin.last N) ≠ Fin.last N := by
    intro i hiOld hlast
    let d : Fin (N + 1) := ⟨N - i.val, by omega⟩
    have hdiag : R i d = Fin.last N := by
      simpa [d] using inv.diag_active i hiOld
    have hd_eq_last : d = Fin.last N := inv.row_inj i (by rw [hdiag, hlast])
    have hv : N - i.val = N := by
      simpa [d, Fin.last] using congrArg Fin.val hd_eq_last
    have hi_lt : i.val < N := i.isLt
    omega
  have hlastActiveBefore :
      ∀ i₁ i₂ : Fin N, active i₁ → active i₂ →
        R i₁ (Fin.last N) = R i₂ (Fin.last N) → i₁ = i₂ := by
    intro i₁ i₂ hi₁ hi₂ hlastEq
    have hNt : N - t = N - (t + 1) + 1 := by omega
    by_cases h₁old : N - t ≤ i₁.val
    · by_cases h₂old : N - t ≤ i₂.val
      · exact inv.last_active_inj i₁ i₂ h₁old h₂old hlastEq
      · have hi₂start : i₂ = start := Fin.ext (by
          have hi₂lt : i₂.val < N - t := Nat.lt_of_not_ge h₂old
          have hi₂le : i₂.val ≤ N - (t + 1) := by omega
          exact le_antisymm hi₂le hi₂)
        subst i₂
        have hbad : R i₁ (Fin.last N) = Fin.last N := by
          simpa [hstartLast] using hlastEq
        exact False.elim (oldLast_ne_last i₁ h₁old hbad)
    · have hi₁start : i₁ = start := Fin.ext (by
        have hi₁lt : i₁.val < N - t := Nat.lt_of_not_ge h₁old
        have hi₁le : i₁.val ≤ N - (t + 1) := by omega
        exact le_antisymm hi₁le hi₁)
      subst i₁
      by_cases h₂old : N - t ≤ i₂.val
      · have hbad : R i₂ (Fin.last N) = Fin.last N := by
          simpa [hstartLast] using hlastEq.symm
        exact False.elim (oldLast_ne_last i₂ h₂old hbad)
      · have hi₂start : i₂ = start := Fin.ext (by
          have hi₂lt : i₂.val < N - t := Nat.lt_of_not_ge h₂old
          have hi₂le : i₂.val ≤ N - (t + 1) := by omega
          exact le_antisymm hi₂le hi₂)
        exact hi₂start.symm
  constructor
  · exact smetSwitchColumn_row_injective inv.row_inj hc_ne_last
  · intro j hj
    by_cases hjc : j = c
    · subst j
      exact smetSwitchColumn_col_c_injective hcolC hlastActiveBefore
        hstartActive hstartLast hcol_ne_last
    · have hjlast : j ≠ Fin.last N := by
        intro hjlast
        have hv : j.val = N := by simpa [Fin.last] using congrArg Fin.val hjlast
        omega
      exact smetSwitchColumn_col_ne_injective hjc hjlast (inv.col_inj j hj)
  · exact smetSwitchColumn_last_active_injective hc_ne_last hcolC hlastActiveBefore
  · intro i hi
    have hnotActive : ¬ active i := by
      intro ha
      dsimp [active] at ha
      omega
    have hnotReach : ¬ switchReach R c active start i := by
      intro hr
      exact hnotActive (switchReach_active hstartActive hr)
    unfold smetSwitchColumn
    simp [hnotReach, inv.last_unactive_new i (by omega)]
  · intro i j htj hj
    have hjc : j ≠ c := by
      intro h
      subst j
      dsimp [c] at htj
      omega
    have hjlast : j ≠ Fin.last N := by
      intro h
      have hv : j.val = N := by simpa [Fin.last] using congrArg Fin.val h
      omega
    unfold smetSwitchColumn
    by_cases hr : switchReach R c active start i
    · simp [hr, hjc, hjlast, inv.unprocessed i j (by omega) hj]
    · simp [hr, inv.unprocessed i j (by omega) hj]
  · intro i j hj hij
    have hjlast : j ≠ Fin.last N := by
      intro h
      have hv : j.val = N := by simpa [Fin.last] using congrArg Fin.val h
      omega
    by_cases hjc : j = c
    · subst j
      have hnotActive : ¬ active i := by
        intro ha
        have hsubadd : N - (t + 1) + (t + 1) = N :=
          Nat.sub_add_cancel (by omega)
        dsimp [active, c] at ha
        have hge : N ≤ i.val + (t + 1) := by
          calc
            N = N - (t + 1) + (t + 1) := hsubadd.symm
            _ ≤ i.val + (t + 1) := Nat.add_le_add_right ha (t + 1)
        have hlt : i.val + (t + 1) < N := by
          simpa [c] using hij
        omega
      have hnotReach : ¬ switchReach R c active start i := by
        intro hr
        exact hnotActive (switchReach_active hstartActive hr)
      unfold smetSwitchColumn
      simp [hnotReach, inv.required_old i c hc_ltN (by simpa [c] using hij)]
    · unfold smetSwitchColumn
      by_cases hr : switchReach R c active start i
      · simp [hr, hjc, hjlast, inv.required_old i j hj hij]
      · simp [hr, inv.required_old i j hj hij]
  · intro i hi
    let d : Fin (N + 1) := ⟨N - i.val, by omega⟩
    change smetSwitchColumn R c active start i d = Fin.last N
    by_cases hiOld : N - t ≤ i.val
    · have hd_ne_c : d ≠ c := by
        intro hdc
        have hv : N - i.val = t + 1 := by
          simpa [d, c] using congrArg Fin.val hdc
        omega
      have hd_ne_last : d ≠ Fin.last N := by
        intro hdl
        have hv : N - i.val = N := by
          simpa [d, Fin.last] using congrArg Fin.val hdl
        have hi_lt : i.val < N := i.isLt
        omega
      have hdiag : R i d = Fin.last N := by
        simpa [d] using inv.diag_active i hiOld
      unfold smetSwitchColumn
      by_cases hr : switchReach R c active start i
      · simp [hr, hd_ne_c, hd_ne_last, hdiag]
      · simp [hr, hdiag]
    · have histart : i = start := Fin.ext (by
        have hNt : N - t = N - (t + 1) + 1 := by omega
        have hilt : i.val < N - t := Nat.lt_of_not_ge hiOld
        have hile : i.val ≤ N - (t + 1) := by omega
        exact le_antisymm hile hi)
      subst i
      have hd_eq_c : d = c := Fin.ext (by
        dsimp [d, start, c]
        omega)
      unfold smetSwitchColumn
      rw [hd_eq_c]
      simp [switchReach.start, hstartLast]

lemma smetRectStage_invariant {N t : ℕ}
    {L₀ : Fin N → Fin N → Fin N} (hL₀ : IsLatinSquare L₀)
    (ht : t < N) :
    SmetRectStageInvariant L₀ t (smetRectStage L₀ t) := by
  induction t with
  | zero =>
      exact smetRectInitial_invariant hL₀ (by omega)
  | succ t ih =>
      change SmetRectStageInvariant L₀ (t + 1)
        (smetRectStep (smetRectStage L₀ t) t)
      exact smetRectStep_invariant ht (ih (by omega))

theorem SmetBackDiagonalCompletableCore {N : ℕ} (hN : 3 ≤ N)
    (L₀ : Fin N → Fin N → Fin N) (hL₀ : IsLatinSquare L₀) :
    ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
      Completes (smetBackPartial L₀) L := by
  let R : Fin N → Fin (N + 1) → Fin (N + 1) :=
    smetRectStage L₀ (N - 1)
  have hInv : SmetRectStageInvariant L₀ (N - 1) R := by
    dsimp [R]
    exact smetRectStage_invariant hL₀ (by omega)
  have hlast_ne_of_pos :
      ∀ i : Fin N, 0 < i.val → R i (Fin.last N) ≠ Fin.last N := by
    intro i hiPos hlast
    let d : Fin (N + 1) := ⟨N - i.val, by omega⟩
    have hactive : N - (N - 1) ≤ i.val := by omega
    have hdiag : R i d = Fin.last N := by
      simpa [d] using hInv.diag_active i hactive
    have hd_eq_last : d = Fin.last N := hInv.row_inj i (by rw [hdiag, hlast])
    have hv : N - i.val = N := by
      simpa [d, Fin.last] using congrArg Fin.val hd_eq_last
    omega
  have hlast_col_inj :
      Function.Injective fun i : Fin N => R i (Fin.last N) := by
    intro i₁ i₂ h
    by_cases h₁zero : i₁.val = 0
    · by_cases h₂zero : i₂.val = 0
      · exact Fin.ext (h₁zero.trans h₂zero.symm)
      · have h₁last : R i₁ (Fin.last N) = Fin.last N := by
          exact hInv.last_unactive_new i₁ (by omega)
        have h₂pos : 0 < i₂.val := by omega
        have h₂last : R i₂ (Fin.last N) = Fin.last N := by
          exact h.symm.trans h₁last
        exact False.elim (hlast_ne_of_pos i₂ h₂pos h₂last)
    · have h₁pos : 0 < i₁.val := by omega
      by_cases h₂zero : i₂.val = 0
      · have h₂last : R i₂ (Fin.last N) = Fin.last N := by
          exact hInv.last_unactive_new i₂ (by omega)
        have h₁last : R i₁ (Fin.last N) = Fin.last N := by
          exact h.trans h₂last
        exact False.elim (hlast_ne_of_pos i₁ h₁pos h₁last)
      · have h₂pos : 0 < i₂.val := by omega
        exact hInv.last_active_inj i₁ i₂ (by omega) (by omega) h
  have hcolR : ∀ j : Fin (N + 1), Function.Injective fun i : Fin N => R i j := by
    intro j
    by_cases hj : j.val < N
    · exact hInv.col_inj j hj
    · have hjlast : j = Fin.last N := Fin.ext (by
        have hjle : j.val ≤ N := Nat.lt_succ_iff.mp j.isLt
        have hjge : N ≤ j.val := Nat.le_of_not_gt hj
        simpa [Fin.last] using le_antisymm hjle hjge)
      subst j
      exact hlast_col_inj
  obtain ⟨lastRow, hlastRow_inj, hlastRow_avoid⟩ :
      ∃ row : Fin (N + 1) → Fin (N + 1), Function.Injective row ∧
        ∀ i j, row j ≠ R i j :=
    latin_rectangle_extend_one R hInv.row_inj hcolR (by omega)
  let L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) :=
    fun i j => if hi : i.val < N then R ⟨i.val, hi⟩ j else lastRow j
  have hrowL : ∀ i : Fin (N + 1), Function.Injective (L i) := by
    intro i j₁ j₂ h
    by_cases hi : i.val < N
    · have h' : R ⟨i.val, hi⟩ j₁ = R ⟨i.val, hi⟩ j₂ := by
        simpa [L, hi] using h
      exact hInv.row_inj ⟨i.val, hi⟩ h'
    · have h' : lastRow j₁ = lastRow j₂ := by
        simpa [L, hi] using h
      exact hlastRow_inj h'
  have hcolL : ∀ j : Fin (N + 1), Function.Injective fun i : Fin (N + 1) => L i j := by
    intro j i₁ i₂ h
    by_cases h₁ : i₁.val < N
    · by_cases h₂ : i₂.val < N
      · have hR : R ⟨i₁.val, h₁⟩ j = R ⟨i₂.val, h₂⟩ j := by
          simpa [L, h₁, h₂] using h
        have hii : (⟨i₁.val, h₁⟩ : Fin N) = ⟨i₂.val, h₂⟩ :=
          hcolR j hR
        exact Fin.ext (by simpa using congrArg Fin.val hii)
      · have hlast : i₂ = Fin.last N := Fin.ext (by
          have hle : i₂.val ≤ N := Nat.lt_succ_iff.mp i₂.isLt
          have hge : N ≤ i₂.val := Nat.le_of_not_gt h₂
          simpa [Fin.last] using le_antisymm hle hge)
        subst i₂
        have hbad : lastRow j = R ⟨i₁.val, h₁⟩ j := by
          simpa [L, h₁] using h.symm
        exact False.elim (hlastRow_avoid ⟨i₁.val, h₁⟩ j hbad)
    · by_cases h₂ : i₂.val < N
      · have hlast : i₁ = Fin.last N := Fin.ext (by
          have hle : i₁.val ≤ N := Nat.lt_succ_iff.mp i₁.isLt
          have hge : N ≤ i₁.val := Nat.le_of_not_gt h₁
          simpa [Fin.last] using le_antisymm hle hge)
        subst i₁
        have hbad : lastRow j = R ⟨i₂.val, h₂⟩ j := by
          simpa [L, h₂] using h
        exact False.elim (hlastRow_avoid ⟨i₂.val, h₂⟩ j hbad)
      · have hi₁last : i₁ = Fin.last N := Fin.ext (by
          have hle : i₁.val ≤ N := Nat.lt_succ_iff.mp i₁.isLt
          have hge : N ≤ i₁.val := Nat.le_of_not_gt h₁
          simpa [Fin.last] using le_antisymm hle hge)
        have hi₂last : i₂ = Fin.last N := Fin.ext (by
          have hle : i₂.val ≤ N := Nat.lt_succ_iff.mp i₂.isLt
          have hge : N ≤ i₂.val := Nat.le_of_not_gt h₂
          simpa [Fin.last] using le_antisymm hle hge)
        exact hi₁last.trans hi₂last.symm
  have hlastRow_zero : lastRow 0 = Fin.last N := by
    by_contra hne
    have hvlt : (lastRow 0).val < N := by
      have hvle : (lastRow 0).val ≤ N := Nat.lt_succ_iff.mp (lastRow 0).isLt
      have hvne : (lastRow 0).val ≠ N := by
        intro hv
        exact hne (Fin.ext (by simpa [Fin.last] using hv))
      omega
    let a : Fin N := ⟨(lastRow 0).val, hvlt⟩
    let zN : Fin N := ⟨0, by omega⟩
    obtain ⟨i₀, hi₀⟩ :=
      (hL₀.2 zN).surjective_of_finite (Equiv.refl (Fin N)) a
    have hzero_lt : (0 : Fin (N + 1)).val < N := by
      show 0 < N
      omega
    have hR0 : R i₀ 0 = Fin.castSucc (L₀ i₀ zN) := by
      have hreq := hInv.required_old i₀ (0 : Fin (N + 1)) hzero_lt (by simpa using i₀.isLt)
      simpa [zN] using hreq
    have hcasta : Fin.castSucc a = lastRow 0 := Fin.ext (by rfl)
    have hRlast : R i₀ 0 = lastRow 0 := by
      calc
        R i₀ 0 = Fin.castSucc (L₀ i₀ zN) := hR0
        _ = Fin.castSucc a := congrArg Fin.castSucc hi₀
        _ = lastRow 0 := hcasta
    exact hlastRow_avoid i₀ 0 hRlast.symm
  refine ⟨L, ?_⟩
  constructor
  · exact ⟨hrowL, hcolL⟩
  · intro i j a hcell
    by_cases hi : i.val < N
    · let ii : Fin N := ⟨i.val, hi⟩
      by_cases hdiag : i.val + j.val = N
      · have ha : a = Fin.last N := by
          simpa [smetBackPartial, hdiag] using hcell.symm
        subst a
        have hj_eq : j = ⟨N - ii.val, by omega⟩ := Fin.ext (by
          dsimp [ii]
          omega)
        have hdiagR : R ii ⟨N - ii.val, by omega⟩ = Fin.last N := by
          by_cases hrow0 : ii.val = 0
          · have hdlast : (⟨N - ii.val, by omega⟩ : Fin (N + 1)) = Fin.last N :=
              Fin.ext (by
                have hv : N - ii.val = N := by omega
                simpa [Fin.last] using hv)
            rw [hdlast]
            exact hInv.last_unactive_new ii (by omega)
          · have hactive : N - (N - 1) ≤ ii.val := by omega
            exact hInv.diag_active ii hactive
        simpa [L, hi, R, ii, hj_eq] using hdiagR
      · by_cases hlt : i.val + j.val < N
        · have hjN : j.val < N := by omega
          have ha : a = Fin.castSucc (L₀ ii ⟨j.val, hjN⟩) := by
            simpa [smetBackPartial, hdiag, hlt, ii] using hcell.symm
          subst a
          have hreq := hInv.required_old ii j hjN (by simpa [ii] using hlt)
          simpa [L, hi, R] using hreq
        · simp [smetBackPartial, hdiag, hlt] at hcell
    · have hilast : i = Fin.last N := Fin.ext (by
        have hle : i.val ≤ N := Nat.lt_succ_iff.mp i.isLt
        have hge : N ≤ i.val := Nat.le_of_not_gt hi
        simpa [Fin.last] using le_antisymm hle hge)
      subst i
      have hlastInfo : j = 0 ∧ a = Fin.last N := by
        by_cases hdiag : (Fin.last N).val + j.val = N
        · have hj0 : j = 0 := Fin.ext (by
            simpa [Fin.last] using hdiag)
          have ha : a = Fin.last N := by
            have htmp :
                smetBackPartial L₀ (Fin.last N) j = some (Fin.last N) :=
              smetBackPartial_back_diagonal L₀ hdiag
            have hsome : some (Fin.last N) = some a := by
              simpa [htmp] using hcell
            exact (Option.some.inj hsome).symm
          exact ⟨hj0, ha⟩
        · have hlt : ¬ (Fin.last N).val + j.val < N := by
            intro hlt'
            have hv : (Fin.last N).val = N := by simp [Fin.last]
            omega
          simp [smetBackPartial, hdiag, hlt] at hcell
          exact ⟨hcell.1, hcell.2.symm⟩
      rcases hlastInfo with ⟨hj0, ha⟩
      rw [hj0, ha]
      simpa [L, hlastRow_zero]

theorem smetMainPartial_completable_of_core
    {N : ℕ} (hN : 3 ≤ N) {L₀ : Fin N → Fin N → Fin N}
    (hL₀ : IsLatinSquare L₀) :
    ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
      Completes (smetMainPartial L₀) L := by
  exact smetMainPartial_completable_of_smetBackPartial_completable
    (SmetBackDiagonalCompletableCore hN L₀ hL₀)

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
