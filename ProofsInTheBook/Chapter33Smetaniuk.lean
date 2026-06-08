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

/-!
## Improper Latin squares

Smetaniuk's induction keeps the order-`N` intermediate square as a signed
array.  A proper cell `[x]` contributes one copy of `x`; an improper cell
`[x+y-z]` contributes `+x + y - z` to every row and column balance, while a
prescribed entry is satisfied by positive syntactic occurrence.
-/

inductive SignedCell (α : Type*) where
  | proper : α → SignedCell α
  | improper : α → α → α → SignedCell α
deriving DecidableEq

namespace SignedCell

variable {α : Type*} [DecidableEq α]

def coeff : SignedCell α → α → ℤ
  | proper x, s => if s = x then 1 else 0
  | improper x y z, s =>
      (if s = x then 1 else 0) + (if s = y then 1 else 0) -
        (if s = z then 1 else 0)

def Pos : SignedCell α → α → Prop
  | proper x, s => s = x
  | improper x y _z, s => s = x ∨ s = y

def principal : SignedCell α → α
  | proper x => x
  | improper x _y _z => x

def isImproper : SignedCell α → Bool
  | proper _ => false
  | improper _ _ _ => true

@[simp] lemma coeff_proper (x s : α) :
    coeff (proper x) s = if s = x then 1 else 0 := rfl

@[simp] lemma coeff_improper (x y z s : α) :
    coeff (improper x y z) s =
      (if s = x then 1 else 0) + (if s = y then 1 else 0) -
        (if s = z then 1 else 0) := rfl

@[simp] lemma pos_proper (x s : α) :
    Pos (proper x) s ↔ s = x := Iff.rfl

@[simp] lemma pos_improper (x y z s : α) :
    Pos (improper x y z) s ↔ s = x ∨ s = y := Iff.rfl

@[simp] lemma principal_proper (x : α) :
    principal (proper x) = x := rfl

@[simp] lemma principal_improper (x y z : α) :
    principal (improper x y z) = x := rfl

@[simp] lemma isImproper_proper (x : α) :
    isImproper (proper x) = false := rfl

@[simp] lemma isImproper_improper (x y z : α) :
    isImproper (improper x y z) = true := rfl

lemma eq_proper_principal_of_isImproper_eq_false {c : SignedCell α}
    (hc : c.isImproper = false) :
    c = proper c.principal := by
  cases c with
  | proper x => rfl
  | improper x y z => simp at hc

end SignedCell

noncomputable def signedImproperCells {n : ℕ}
    (L : Fin n → Fin n → SignedCell (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun ij => (L ij.1 ij.2).isImproper

def ImproperLatinSquare {n : ℕ}
    (L : Fin n → Fin n → SignedCell (Fin n)) : Prop :=
  (∀ i a : Fin n, (∑ j : Fin n, SignedCell.coeff (L i j) a) = 1) ∧
    (∀ j a : Fin n, (∑ i : Fin n, SignedCell.coeff (L i j) a) = 1) ∧
      (signedImproperCells L).card ≤ 1

def ImproperlyExtends {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (L : Fin n → Fin n → SignedCell (Fin n)) : Prop :=
  ∀ i j a, P i j = some a → SignedCell.Pos (L i j) a

def ImproperCompletionTheorem (n : ℕ) : Prop :=
  ∀ P : Fin n → Fin n → Option (Fin n),
    IsPartialLatin P → (filledCells P).card ≤ n →
      ∃ L : Fin n → Fin n → SignedCell (Fin n),
        ImproperLatinSquare L ∧ ImproperlyExtends P L

def properSigned {n : ℕ} (L : Fin n → Fin n → Fin n) :
    Fin n → Fin n → SignedCell (Fin n) :=
  fun i j => SignedCell.proper (L i j)

noncomputable def signedPrincipalSquare {n : ℕ}
    (L : Fin n → Fin n → SignedCell (Fin n)) : Fin n → Fin n → Fin n :=
  fun i j => (L i j).principal

private lemma signedCell_eq_proper_principal_of_not_improper_mem {n : ℕ}
    {L : Fin n → Fin n → SignedCell (Fin n)} {i j : Fin n}
    (hnot : (i, j) ∉ signedImproperCells L) :
    L i j = SignedCell.proper ((L i j).principal) := by
  have hfalse : (L i j).isImproper = false := by
    by_cases htrue : (L i j).isImproper = true
    · have hmem : (i, j) ∈ signedImproperCells L := by
        simp [signedImproperCells, htrue]
      exact False.elim (hnot hmem)
    · cases h : (L i j).isImproper <;> simp [h] at htrue ⊢
  exact SignedCell.eq_proper_principal_of_isImproper_eq_false hfalse

private lemma signedCoeff_proper_sum_eq_filter_card {n : ℕ}
    (f : Fin n → Fin n) (a : Fin n) :
    (∑ j : Fin n, SignedCell.coeff (SignedCell.proper (f j)) a) =
      (((Finset.univ : Finset (Fin n)).filter fun j => a = f j).card : ℤ) := by
  classical
  calc
    (∑ j : Fin n, SignedCell.coeff (SignedCell.proper (f j)) a) =
        ∑ j : Fin n, (if a = f j then (1 : ℤ) else 0) := by
          simp [SignedCell.coeff]
    _ = ((∑ j : Fin n, if a = f j then (1 : ℕ) else 0) : ℤ) := by
          simpa using
            ((Nat.cast_sum (R := ℤ) (Finset.univ : Finset (Fin n))
              (fun j => if a = f j then (1 : ℕ) else 0)).symm)
    _ = (((Finset.univ : Finset (Fin n)).filter fun j => a = f j).card : ℤ) := by
          have hcard_nat :
              (∑ j : Fin n, if a = f j then (1 : ℕ) else 0) =
                ((Finset.univ : Finset (Fin n)).filter fun j => a = f j).card := by
            simpa using
              ((Finset.card_filter (fun j : Fin n => a = f j)
                (Finset.univ : Finset (Fin n))).symm)
          exact_mod_cast hcard_nat

private lemma injective_of_signedCoeff_proper_sum_one {n : ℕ}
    (f : Fin n → Fin n)
    (hsum : ∀ a : Fin n,
      (∑ j : Fin n, SignedCell.coeff (SignedCell.proper (f j)) a) = 1) :
    Function.Injective f := by
  classical
  intro j₁ j₂ hval
  let S : Finset (Fin n) := (Finset.univ.filter fun j => f j₁ = f j)
  have hcard_int : (S.card : ℤ) = 1 := by
    have h := hsum (f j₁)
    simpa [S, signedCoeff_proper_sum_eq_filter_card] using h
  have hcard : S.card = 1 := by
    exact_mod_cast hcard_int
  have hle : S.card ≤ 1 := by omega
  have hj₁ : j₁ ∈ S := by
    simp [S]
  have hj₂ : j₂ ∈ S := by
    simp [S, hval]
  exact (Finset.card_le_one_iff.mp hle) hj₁ hj₂

theorem isLatinSquare_signedPrincipalSquare_of_no_improper {n : ℕ}
    {L : Fin n → Fin n → SignedCell (Fin n)}
    (hL : ImproperLatinSquare L) (hno : signedImproperCells L = ∅) :
    IsLatinSquare (signedPrincipalSquare L) := by
  classical
  constructor
  · intro i
    apply injective_of_signedCoeff_proper_sum_one
    intro a
    have hrow := hL.1 i a
    convert hrow using 1
    apply Finset.sum_congr rfl
    intro j _hj
    have hnot : (i, j) ∉ signedImproperCells L := by
      simp [hno]
    rw [signedCell_eq_proper_principal_of_not_improper_mem hnot]
    rfl
  · intro j
    apply injective_of_signedCoeff_proper_sum_one
    intro a
    have hcol := hL.2.1 j a
    convert hcol using 1
    apply Finset.sum_congr rfl
    intro i _hi
    have hnot : (i, j) ∉ signedImproperCells L := by
      simp [hno]
    rw [signedCell_eq_proper_principal_of_not_improper_mem hnot]
    rfl

theorem completes_signedPrincipalSquare_of_no_improper {n : ℕ}
    {Q : Fin n → Fin n → Option (Fin n)}
    {L : Fin n → Fin n → SignedCell (Fin n)}
    (hLatin : IsLatinSquare (signedPrincipalSquare L))
    (hExt : ImproperlyExtends Q L) (hno : signedImproperCells L = ∅) :
    Completes Q (signedPrincipalSquare L) := by
  classical
  constructor
  · exact hLatin
  · intro i j a hcell
    have hnot : (i, j) ∉ signedImproperCells L := by
      simp [hno]
    have hproper := signedCell_eq_proper_principal_of_not_improper_mem hnot
    have hpos := hExt i j a hcell
    rw [hproper] at hpos
    simpa [signedPrincipalSquare] using hpos.symm

lemma signedCoeff_sum_proper_of_injective {n : ℕ} (f : Fin n → Fin n)
    (hf : Function.Injective f) (a : Fin n) :
    (∑ j : Fin n, SignedCell.coeff (SignedCell.proper (f j)) a) = 1 := by
  classical
  obtain ⟨j₀, hj₀⟩ := hf.surjective_of_finite (Equiv.refl (Fin n)) a
  rw [Finset.sum_eq_single j₀]
  · simp [hj₀]
  · intro j _hj hj_ne
    have hne : f j ≠ a := by
      intro hja
      exact hj_ne (hf (hja.trans hj₀.symm))
    have hne' : a ≠ f j := fun h => hne h.symm
    simp [hne']
  · intro hnot
    simp at hnot

lemma signedImproperCells_properSigned {n : ℕ} (L : Fin n → Fin n → Fin n) :
    signedImproperCells (properSigned L) = ∅ := by
  classical
  ext ij
  simp [signedImproperCells, properSigned]

theorem improperLatinSquare_of_isLatinSquare {n : ℕ}
    {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L) :
    ImproperLatinSquare (properSigned L) := by
  constructor
  · intro i a
    exact signedCoeff_sum_proper_of_injective (L i) (hL.1 i) a
  · constructor
    · intro j a
      exact signedCoeff_sum_proper_of_injective (fun i => L i j) (hL.2 j) a
    · rw [signedImproperCells_properSigned]
      simp

theorem improperlyExtends_of_completes {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)}
    {L : Fin n → Fin n → Fin n} (hL : Completes P L) :
    ImproperlyExtends P (properSigned L) := by
  intro i j a hcell
  have hval := hL.2 i j a hcell
  simp [properSigned, hval.symm]

theorem improperCompletion_of_completion {n : ℕ}
    (hcomplete : LatinSquareCompletionTheorem n)
    {P : Fin n → Fin n → Option (Fin n)}
    (hP : IsPartialLatin P) (hcard : (filledCells P).card ≤ n - 1) :
    ∃ L : Fin n → Fin n → SignedCell (Fin n),
      ImproperLatinSquare L ∧ ImproperlyExtends P L := by
  obtain ⟨L, hL⟩ := hcomplete P hP hcard
  exact ⟨properSigned L, improperLatinSquare_of_isLatinSquare hL.1,
    improperlyExtends_of_completes hL⟩

def clearCell {n : ℕ} (P : Fin n → Fin n → Option (Fin n))
    (i₀ j₀ : Fin n) : Fin n → Fin n → Option (Fin n) :=
  fun i j => if i = i₀ ∧ j = j₀ then none else P i j

lemma clearCell_eq_some_iff {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (i₀ j₀ i j a : Fin n) :
    clearCell P i₀ j₀ i j = some a ↔
      P i j = some a ∧ ¬ (i = i₀ ∧ j = j₀) := by
  by_cases hcell : i = i₀ ∧ j = j₀
  · simp [clearCell, hcell]
  · simp [clearCell, hcell]

lemma isPartialLatin_clearCell {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} (hP : IsPartialLatin P)
    (i₀ j₀ : Fin n) : IsPartialLatin (clearCell P i₀ j₀) := by
  constructor
  · intro i j₁ j₂ a h₁ h₂
    exact hP.1 i j₁ j₂ a
      ((clearCell_eq_some_iff P i₀ j₀ i j₁ a).mp h₁).1
      ((clearCell_eq_some_iff P i₀ j₀ i j₂ a).mp h₂).1
  · intro i₁ i₂ j a h₁ h₂
    exact hP.2 i₁ i₂ j a
      ((clearCell_eq_some_iff P i₀ j₀ i₁ j a).mp h₁).1
      ((clearCell_eq_some_iff P i₀ j₀ i₂ j a).mp h₂).1

lemma filledCells_clearCell {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) (i₀ j₀ : Fin n) :
    filledCells (clearCell P i₀ j₀) = (filledCells P).erase (i₀, j₀) := by
  classical
  ext ij
  by_cases hcell : ij = (i₀, j₀)
  · subst ij
    simp [filledCells, clearCell]
  · have hnot : ¬ (ij.1 = i₀ ∧ ij.2 = j₀) := by
      intro h
      exact hcell (Prod.ext h.1 h.2)
    simp [filledCells, clearCell, hnot, hcell]

lemma filledCells_clearCell_card_of_some {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} {i₀ j₀ a : Fin n}
    (hcell : P i₀ j₀ = some a) :
    (filledCells (clearCell P i₀ j₀)).card = (filledCells P).card - 1 := by
  classical
  rw [filledCells_clearCell]
  have hmem : (i₀, j₀) ∈ filledCells P := by
    simp [filledCells, hcell]
  rw [Finset.card_erase_of_mem hmem]

lemma completes_of_clearCell_and_cell {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} {L : Fin n → Fin n → Fin n}
    {i₀ j₀ a : Fin n}
    (hL : Completes (clearCell P i₀ j₀) L)
    (hcell : P i₀ j₀ = some a) (hval : L i₀ j₀ = a) :
    Completes P L := by
  constructor
  · exact hL.1
  · intro i j b hb
    by_cases hij : i = i₀ ∧ j = j₀
    · rcases hij with ⟨hi, hj⟩
      subst i
      subst j
      have hb_eq : b = a := Option.some.inj (by rw [← hb, hcell])
      simpa [hb_eq] using hval
    · have hclear : clearCell P i₀ j₀ i j = some b := by
        simp [clearCell, hij, hb]
      exact hL.2 i j b hclear

private lemma sum_eq_of_eq_off_two_of_pair_sum {ι : Type*} [Fintype ι]
    [DecidableEq ι] (f g : ι → ℤ) {x y : ι} (hxy : x ≠ y)
    (hsame : ∀ z, z ≠ x → z ≠ y → g z = f z)
    (hpair : g x + g y = f x + f y) :
    (∑ z : ι, g z) = ∑ z : ι, f z := by
  classical
  let S : Finset ι := ((Finset.univ.erase y).erase x)
  have hx_mem_erase_y : x ∈ (Finset.univ.erase y : Finset ι) := by
    simp [hxy]
  have hSsum : (∑ z ∈ S, g z) = (∑ z ∈ S, f z) := by
    apply Finset.sum_congr rfl
    intro z hz
    have hz_ne_x : z ≠ x := (Finset.mem_erase.mp hz).1
    have hz_in_erase_y : z ∈ (Finset.univ.erase y : Finset ι) :=
      (Finset.mem_erase.mp hz).2
    have hz_ne_y : z ≠ y := (Finset.mem_erase.mp hz_in_erase_y).1
    exact hsame z hz_ne_x hz_ne_y
  have hdecomp_g_y :
      (∑ z : ι, g z) = (∑ z ∈ (Finset.univ.erase y : Finset ι), g z) + g y := by
    exact (Finset.sum_erase_add Finset.univ g (by simp)).symm
  have hdecomp_g_x :
      (∑ z ∈ (Finset.univ.erase y : Finset ι), g z) = (∑ z ∈ S, g z) + g x := by
    dsimp [S]
    exact (Finset.sum_erase_add (Finset.univ.erase y) g hx_mem_erase_y).symm
  have hdecomp_f_y :
      (∑ z : ι, f z) = (∑ z ∈ (Finset.univ.erase y : Finset ι), f z) + f y := by
    exact (Finset.sum_erase_add Finset.univ f (by simp)).symm
  have hdecomp_f_x :
      (∑ z ∈ (Finset.univ.erase y : Finset ι), f z) = (∑ z ∈ S, f z) + f x := by
    dsimp [S]
    exact (Finset.sum_erase_add (Finset.univ.erase y) f hx_mem_erase_y).symm
  calc
    (∑ z : ι, g z) = (∑ z ∈ S, g z) + (g x + g y) := by
      rw [hdecomp_g_y, hdecomp_g_x]
      abel
    _ = (∑ z ∈ S, f z) + (f x + f y) := by
      rw [hSsum, hpair]
    _ = ∑ z : ι, f z := by
      rw [hdecomp_f_y, hdecomp_f_x]
      abel

noncomputable def symbolRow {n : ℕ} {L : Fin n → Fin n → Fin n}
    (hcol : ∀ j : Fin n, Function.Injective fun i : Fin n => L i j)
    (a : Fin n) (j : Fin n) : Fin n :=
  Classical.choose ((hcol j).surjective_of_finite (Equiv.refl (Fin n)) a)

lemma symbolRow_spec {n : ℕ} {L : Fin n → Fin n → Fin n}
    (hcol : ∀ j : Fin n, Function.Injective fun i : Fin n => L i j)
    (a : Fin n) (j : Fin n) :
    L (symbolRow hcol a j) j = a :=
  Classical.choose_spec ((hcol j).surjective_of_finite (Equiv.refl (Fin n)) a)

noncomputable def restoredSignedSquare {n : ℕ}
    (L : Fin n → Fin n → Fin n) (hL : IsLatinSquare L)
    (r c a : Fin n) : Fin n → Fin n → SignedCell (Fin n) :=
  let b : Fin n := L r c
  let cₐ : Fin n := symbolColumn hL.1 a r
  let rₐ : Fin n := symbolRow hL.2 a c
  let d : Fin n := L rₐ cₐ
  fun i j =>
    if i = r ∧ j = c then
      SignedCell.proper a
    else if i = r ∧ j = cₐ then
      SignedCell.proper b
    else if i = rₐ ∧ j = c then
      SignedCell.proper b
    else if i = rₐ ∧ j = cₐ then
      SignedCell.improper a d b
    else
      SignedCell.proper (L i j)

private lemma signedCoeff_improper_trade {n : ℕ} (a b d s : Fin n) :
    SignedCell.coeff (SignedCell.proper b) s +
        SignedCell.coeff (SignedCell.improper a d b) s =
      SignedCell.coeff (SignedCell.proper a) s +
        SignedCell.coeff (SignedCell.proper d) s := by
  by_cases hsb : s = b <;> by_cases hsa : s = a <;> by_cases hsd : s = d <;>
    simp [SignedCell.coeff, hsb, hsa, hsd] <;> ring

theorem improperLatinSquare_restoredSignedSquare {n : ℕ}
    {L : Fin n → Fin n → Fin n} (hL : IsLatinSquare L)
    {r c a : Fin n} (hneq : L r c ≠ a) :
    ImproperLatinSquare (restoredSignedSquare L hL r c a) := by
  classical
  let b : Fin n := L r c
  let cₐ : Fin n := symbolColumn hL.1 a r
  let rₐ : Fin n := symbolRow hL.2 a c
  let d : Fin n := L rₐ cₐ
  have hrow_a : L r cₐ = a := by
    simpa [cₐ] using symbolColumn_spec hL.1 a r
  have hcol_a : L rₐ c = a := by
    simpa [rₐ] using symbolRow_spec hL.2 a c
  have hcₐ_ne_c : cₐ ≠ c := by
    intro h
    exact hneq (by simpa [cₐ, h] using hrow_a)
  have hc_ne_cₐ : c ≠ cₐ := fun h => hcₐ_ne_c h.symm
  have hrₐ_ne_r : rₐ ≠ r := by
    intro h
    exact hneq (by simpa [rₐ, h] using hcol_a)
  have hr_ne_rₐ : r ≠ rₐ := fun h => hrₐ_ne_r h.symm
  constructor
  · intro i s
    by_cases hir : i = r
    · subst i
      have hsum :
          (∑ j : Fin n, SignedCell.coeff (restoredSignedSquare L hL r c a r j) s) =
            ∑ j : Fin n, SignedCell.coeff (SignedCell.proper (L r j)) s := by
        apply sum_eq_of_eq_off_two_of_pair_sum
          (f := fun j => SignedCell.coeff (SignedCell.proper (L r j)) s)
          (g := fun j => SignedCell.coeff (restoredSignedSquare L hL r c a r j) s)
          (x := c) (y := cₐ) hc_ne_cₐ
        · intro z hz_c hz_cₐ
          simp [restoredSignedSquare, b, cₐ, rₐ, d, hz_c, hz_cₐ, hr_ne_rₐ]
        · have hg_c :
              SignedCell.coeff (restoredSignedSquare L hL r c a r c) s =
                SignedCell.coeff (SignedCell.proper a) s := by
            simp [restoredSignedSquare, b, cₐ, rₐ, d]
          have hg_cₐ :
              SignedCell.coeff (restoredSignedSquare L hL r c a r cₐ) s =
                SignedCell.coeff (SignedCell.proper b) s := by
            simp [restoredSignedSquare, b, cₐ, rₐ, d, hcₐ_ne_c, hr_ne_rₐ]
          have hf_c :
              SignedCell.coeff (SignedCell.proper (L r c)) s =
                SignedCell.coeff (SignedCell.proper b) s := by
            simp [b]
          have hf_cₐ :
              SignedCell.coeff (SignedCell.proper (L r cₐ)) s =
                SignedCell.coeff (SignedCell.proper a) s := by
            rw [hrow_a]
          rw [hg_c, hg_cₐ, hf_c, hf_cₐ]
          abel
      rw [hsum]
      exact signedCoeff_sum_proper_of_injective (L r) (hL.1 r) s
    · by_cases hirₐ : i = rₐ
      · subst i
        have hsum :
            (∑ j : Fin n, SignedCell.coeff (restoredSignedSquare L hL r c a rₐ j) s) =
              ∑ j : Fin n, SignedCell.coeff (SignedCell.proper (L rₐ j)) s := by
          apply sum_eq_of_eq_off_two_of_pair_sum
            (f := fun j => SignedCell.coeff (SignedCell.proper (L rₐ j)) s)
            (g := fun j => SignedCell.coeff (restoredSignedSquare L hL r c a rₐ j) s)
            (x := c) (y := cₐ) hc_ne_cₐ
          · intro z hz_c hz_cₐ
            simp [restoredSignedSquare, b, cₐ, rₐ, d, hz_c, hz_cₐ, hrₐ_ne_r]
          · have hg_c :
                SignedCell.coeff (restoredSignedSquare L hL r c a rₐ c) s =
                  SignedCell.coeff (SignedCell.proper b) s := by
              simp [restoredSignedSquare, b, cₐ, rₐ, d, hrₐ_ne_r]
            have hg_cₐ :
                SignedCell.coeff (restoredSignedSquare L hL r c a rₐ cₐ) s =
                  SignedCell.coeff (SignedCell.improper a d b) s := by
              simp [restoredSignedSquare, b, cₐ, rₐ, d, hcₐ_ne_c, hrₐ_ne_r]
            have hf_c :
                SignedCell.coeff (SignedCell.proper (L rₐ c)) s =
                  SignedCell.coeff (SignedCell.proper a) s := by
              rw [hcol_a]
            have hf_cₐ :
                SignedCell.coeff (SignedCell.proper (L rₐ cₐ)) s =
                  SignedCell.coeff (SignedCell.proper d) s := by
              simp [d]
            rw [hg_c, hg_cₐ, hf_c, hf_cₐ]
            exact signedCoeff_improper_trade a b d s
        rw [hsum]
        exact signedCoeff_sum_proper_of_injective (L rₐ) (hL.1 rₐ) s
      · have hsum :
            (∑ j : Fin n, SignedCell.coeff (restoredSignedSquare L hL r c a i j) s) =
              ∑ j : Fin n, SignedCell.coeff (SignedCell.proper (L i j)) s := by
          apply Finset.sum_congr rfl
          intro j _hj
          simp [restoredSignedSquare, b, cₐ, rₐ, d, hir, hirₐ]
        rw [hsum]
        exact signedCoeff_sum_proper_of_injective (L i) (hL.1 i) s
  · constructor
    · intro j s
      by_cases hjc : j = c
      · subst j
        have hsum :
            (∑ i : Fin n, SignedCell.coeff (restoredSignedSquare L hL r c a i c) s) =
              ∑ i : Fin n, SignedCell.coeff (SignedCell.proper (L i c)) s := by
          apply sum_eq_of_eq_off_two_of_pair_sum
            (f := fun i => SignedCell.coeff (SignedCell.proper (L i c)) s)
            (g := fun i => SignedCell.coeff (restoredSignedSquare L hL r c a i c) s)
            (x := r) (y := rₐ) hr_ne_rₐ
          · intro z hz_r hz_rₐ
            simp [restoredSignedSquare, b, cₐ, rₐ, d, hz_r, hz_rₐ, hc_ne_cₐ]
          · have hg_r :
                SignedCell.coeff (restoredSignedSquare L hL r c a r c) s =
                  SignedCell.coeff (SignedCell.proper a) s := by
              simp [restoredSignedSquare, b, cₐ, rₐ, d]
            have hg_rₐ :
                SignedCell.coeff (restoredSignedSquare L hL r c a rₐ c) s =
                  SignedCell.coeff (SignedCell.proper b) s := by
              simp [restoredSignedSquare, b, cₐ, rₐ, d, hrₐ_ne_r]
            have hf_r :
                SignedCell.coeff (SignedCell.proper (L r c)) s =
                  SignedCell.coeff (SignedCell.proper b) s := by
              simp [b]
            have hf_rₐ :
                SignedCell.coeff (SignedCell.proper (L rₐ c)) s =
                  SignedCell.coeff (SignedCell.proper a) s := by
              rw [hcol_a]
            rw [hg_r, hg_rₐ, hf_r, hf_rₐ]
            abel
        rw [hsum]
        exact signedCoeff_sum_proper_of_injective (fun i => L i c) (hL.2 c) s
      · by_cases hjcₐ : j = cₐ
        · subst j
          have hsum :
              (∑ i : Fin n, SignedCell.coeff (restoredSignedSquare L hL r c a i cₐ) s) =
                ∑ i : Fin n, SignedCell.coeff (SignedCell.proper (L i cₐ)) s := by
            apply sum_eq_of_eq_off_two_of_pair_sum
              (f := fun i => SignedCell.coeff (SignedCell.proper (L i cₐ)) s)
              (g := fun i => SignedCell.coeff (restoredSignedSquare L hL r c a i cₐ) s)
              (x := r) (y := rₐ) hr_ne_rₐ
            · intro z hz_r hz_rₐ
              simp [restoredSignedSquare, b, cₐ, rₐ, d, hz_r, hz_rₐ, hcₐ_ne_c]
            · have hg_r :
                  SignedCell.coeff (restoredSignedSquare L hL r c a r cₐ) s =
                    SignedCell.coeff (SignedCell.proper b) s := by
                simp [restoredSignedSquare, b, cₐ, rₐ, d, hcₐ_ne_c, hr_ne_rₐ]
              have hg_rₐ :
                  SignedCell.coeff (restoredSignedSquare L hL r c a rₐ cₐ) s =
                    SignedCell.coeff (SignedCell.improper a d b) s := by
                simp [restoredSignedSquare, b, cₐ, rₐ, d, hcₐ_ne_c, hrₐ_ne_r]
              have hf_r :
                  SignedCell.coeff (SignedCell.proper (L r cₐ)) s =
                    SignedCell.coeff (SignedCell.proper a) s := by
                rw [hrow_a]
              have hf_rₐ :
                  SignedCell.coeff (SignedCell.proper (L rₐ cₐ)) s =
                    SignedCell.coeff (SignedCell.proper d) s := by
                simp [d]
              rw [hg_r, hg_rₐ, hf_r, hf_rₐ]
              exact signedCoeff_improper_trade a b d s
          rw [hsum]
          exact signedCoeff_sum_proper_of_injective (fun i => L i cₐ) (hL.2 cₐ) s
        · have hsum :
              (∑ i : Fin n, SignedCell.coeff (restoredSignedSquare L hL r c a i j) s) =
                ∑ i : Fin n, SignedCell.coeff (SignedCell.proper (L i j)) s := by
            apply Finset.sum_congr rfl
            intro i _hi
            simp [restoredSignedSquare, b, cₐ, rₐ, d, hjc, hjcₐ]
          rw [hsum]
          exact signedCoeff_sum_proper_of_injective (fun i => L i j) (hL.2 j) s
    · have hsubset :
          signedImproperCells (restoredSignedSquare L hL r c a) ⊆ {(rₐ, cₐ)} := by
        intro ij hij
        have himp :
            (restoredSignedSquare L hL r c a ij.1 ij.2).isImproper = true := by
          simpa [signedImproperCells] using hij
        by_cases h₁ : ij.1 = r ∧ ij.2 = c
        · simp [restoredSignedSquare, b, cₐ, rₐ, d, h₁] at himp
        · by_cases h₂ : ij.1 = r ∧ ij.2 = cₐ
          · exfalso
            rcases ij with ⟨ii, jj⟩
            rcases h₂ with ⟨hi, hj⟩
            change ii = r at hi
            change jj = cₐ at hj
            subst ii
            subst jj
            simp [restoredSignedSquare, b, cₐ, rₐ, d, hcₐ_ne_c] at himp
          · by_cases h₃ : ij.1 = rₐ ∧ ij.2 = c
            · exfalso
              rcases ij with ⟨ii, jj⟩
              rcases h₃ with ⟨hi, hj⟩
              change ii = rₐ at hi
              change jj = c at hj
              subst ii
              subst jj
              simp [restoredSignedSquare, b, cₐ, rₐ, d, hrₐ_ne_r] at himp
            · by_cases h₄ : ij.1 = rₐ ∧ ij.2 = cₐ
              · exact Finset.mem_singleton.mpr (Prod.ext h₄.1 h₄.2)
              · simp [restoredSignedSquare, b, cₐ, rₐ, d, h₁, h₂, h₃, h₄] at himp
      have hcard := Finset.card_le_card hsubset
      simpa using hcard

theorem improperlyExtends_restoredSignedSquare {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} (hP : IsPartialLatin P)
    {r c a : Fin n} {L : Fin n → Fin n → Fin n}
    (hL : Completes (clearCell P r c) L)
    (hcell : P r c = some a) (hneq : L r c ≠ a) :
    ImproperlyExtends P (restoredSignedSquare L hL.1 r c a) := by
  classical
  let b : Fin n := L r c
  let cₐ : Fin n := symbolColumn hL.1.1 a r
  let rₐ : Fin n := symbolRow hL.1.2 a c
  let d : Fin n := L rₐ cₐ
  have hrow_a : L r cₐ = a := by
    simpa [cₐ] using symbolColumn_spec hL.1.1 a r
  have hcol_a : L rₐ c = a := by
    simpa [rₐ] using symbolRow_spec hL.1.2 a c
  have hcₐ_ne_c : cₐ ≠ c := by
    intro h
    exact hneq (by simpa [cₐ, h] using hrow_a)
  have hrₐ_ne_r : rₐ ≠ r := by
    intro h
    exact hneq (by simpa [rₐ, h] using hcol_a)
  intro i j s hs
  by_cases hrc : i = r ∧ j = c
  · rcases hrc with ⟨hi, hj⟩
    subst i
    subst j
    have hs_eq : s = a := Option.some.inj (by rw [← hs, hcell])
    simp [restoredSignedSquare, b, cₐ, rₐ, d, hs_eq]
  · by_cases hr_cₐ : i = r ∧ j = cₐ
    · exfalso
      rcases hr_cₐ with ⟨hi, hj⟩
      subst i
      subst j
      have hclear : clearCell P r c r cₐ = some s := by
        simp [clearCell, hcₐ_ne_c, hs]
      have hLs : L r cₐ = s := hL.2 r cₐ s hclear
      have hs_eq : s = a := by
        rw [← hLs, hrow_a]
      have hdup : c = cₐ := hP.1 r c cₐ a hcell (by simpa [hs_eq] using hs)
      exact hcₐ_ne_c hdup.symm
    · by_cases hrₐ_c : i = rₐ ∧ j = c
      · exfalso
        rcases hrₐ_c with ⟨hi, hj⟩
        subst i
        subst j
        have hclear : clearCell P r c rₐ c = some s := by
          simp [clearCell, hrₐ_ne_r, hs]
        have hLs : L rₐ c = s := hL.2 rₐ c s hclear
        have hs_eq : s = a := by
          rw [← hLs, hcol_a]
        have hdup : r = rₐ := hP.2 r rₐ c a hcell (by simpa [hs_eq] using hs)
        exact hrₐ_ne_r hdup.symm
      · by_cases hrₐ_cₐ : i = rₐ ∧ j = cₐ
        · rcases hrₐ_cₐ with ⟨hi, hj⟩
          subst i
          subst j
          have hclear : clearCell P r c rₐ cₐ = some s := by
            have hnot : ¬ (rₐ = r ∧ cₐ = c) := by
              intro h
              exact hrₐ_ne_r h.1
            simp [clearCell, hnot, hs]
          have hLs : L rₐ cₐ = s := hL.2 rₐ cₐ s hclear
          have hs_eq : s = d := by
            simpa [d] using hLs.symm
          simp [restoredSignedSquare, b, cₐ, rₐ, d, hcₐ_ne_c, hrₐ_ne_r, hs_eq]
        · have hclear : clearCell P r c i j = some s := by
            simp [clearCell, hrc, hs]
          have hLs : L i j = s := hL.2 i j s hclear
          simp [restoredSignedSquare, b, cₐ, rₐ, d, hrc, hr_cₐ, hrₐ_c, hrₐ_cₐ,
            hLs.symm]

theorem improperCompletion_restore_one {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} (hP : IsPartialLatin P)
    {r c a : Fin n} (hcell : P r c = some a)
    {L : Fin n → Fin n → Fin n} (hL : Completes (clearCell P r c) L) :
    ∃ S : Fin n → Fin n → SignedCell (Fin n),
      ImproperLatinSquare S ∧ ImproperlyExtends P S := by
  by_cases hmatch : L r c = a
  · have hLP : Completes P L := completes_of_clearCell_and_cell hL hcell hmatch
    exact ⟨properSigned L, improperLatinSquare_of_isLatinSquare hLP.1,
      improperlyExtends_of_completes hLP⟩
  · exact ⟨restoredSignedSquare L hL.1 r c a,
      improperLatinSquare_restoredSignedSquare hL.1 hmatch,
      improperlyExtends_restoredSignedSquare hP hL hcell hmatch⟩

theorem evans_to_improperCompletion {n : ℕ}
    (hE : LatinSquareCompletionTheorem n) :
    ImproperCompletionTheorem n := by
  intro P hP hcard
  by_cases hsmall : (filledCells P).card ≤ n - 1
  · exact improperCompletion_of_completion hE hP hsmall
  · have hcard_eq : (filledCells P).card = n := by omega
    have hpos : 0 < (filledCells P).card := by omega
    obtain ⟨ij, hij⟩ := Finset.card_pos.mp hpos
    have hisSome : (P ij.1 ij.2).isSome := by
      simpa [filledCells] using hij
    obtain ⟨a, hcell⟩ : ∃ a, P ij.1 ij.2 = some a := by
      cases hopt : P ij.1 ij.2 with
      | none =>
          simp [hopt] at hisSome
      | some a =>
          exact ⟨a, rfl⟩
    have hPclear : IsPartialLatin (clearCell P ij.1 ij.2) :=
      isPartialLatin_clearCell hP ij.1 ij.2
    have hcard_clear : (filledCells (clearCell P ij.1 ij.2)).card ≤ n - 1 := by
      rw [filledCells_clearCell_card_of_some hcell, hcard_eq]
    obtain ⟨L, hL⟩ := hE (clearCell P ij.1 ij.2) hPclear hcard_clear
    exact improperCompletion_restore_one hP hcell hL

noncomputable def usedSymbols {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun a => ∃ i j, P i j = some a

lemma usedSymbols_mem_of_cell {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} {i j a : Fin n}
    (hcell : P i j = some a) : a ∈ usedSymbols P := by
  classical
  simp [usedSymbols]
  exact ⟨i, j, hcell⟩

lemma usedSymbols_card_le_filledCells_card {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n)) :
    (usedSymbols P).card ≤ (filledCells P).card := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [usedSymbols, filledCells]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let default : Fin n × Fin n := (⟨0, hnpos⟩, ⟨0, hnpos⟩)
    have hwitness :
        ∀ a : Fin n, a ∈ usedSymbols P →
          ∃ ij : Fin n × Fin n, ij ∈ filledCells P ∧ P ij.1 ij.2 = some a := by
      intro a ha
      rcases (by simpa [usedSymbols] using ha) with ⟨i, j, hcell⟩
      exact ⟨(i, j), by simp [filledCells, hcell], hcell⟩
    choose g hg using hwitness
    let f : Fin n → Fin n × Fin n := fun a =>
      if ha : a ∈ usedSymbols P then g a ha else default
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro a ha
      dsimp [f]
      have hfa :
          (if ha' : a ∈ usedSymbols P then g a ha' else default) = g a ha :=
        dif_pos ha
      simpa [hfa] using (hg a ha).1
    · intro a ha b hb hfg
      have hga : f a = g a ha := by
        dsimp [f]
        exact dif_pos ha
      have hgb : f b = g b hb := by
        dsimp [f]
        exact dif_pos hb
      have hgab : g a ha = g b hb := by simpa [hga, hgb] using hfg
      have hcell_a : P (g b hb).1 (g b hb).2 = some a := by
        simpa [hgab] using (hg a ha).2
      have hcell_b : P (g b hb).1 (g b hb).2 = some b := (hg b hb).2
      have hsome : some a = some b := by rw [← hcell_a, hcell_b]
      exact Option.some.inj hsome

private lemma exists_two_cells_of_used_not_once {n : ℕ}
    {P : Fin n → Fin n → Option (Fin n)} {a : Fin n}
    (ha : a ∈ usedSymbols P) (hnot : ¬ SymbolOccursExactlyOnce P a) :
    ∃ ij₀ ij₁ : Fin n × Fin n,
      ij₀ ∈ filledCells P ∧ ij₁ ∈ filledCells P ∧
        P ij₀.1 ij₀.2 = some a ∧ P ij₁.1 ij₁.2 = some a ∧ ij₀ ≠ ij₁ := by
  classical
  rcases (by simpa [usedSymbols] using ha) with ⟨i₀, j₀, hcell₀⟩
  let ij₀ : Fin n × Fin n := (i₀, j₀)
  have hmem₀ : ij₀ ∈ filledCells P := by
    simp [ij₀, filledCells, hcell₀]
  have hsecond : ∃ ij₁ : Fin n × Fin n,
      P ij₁.1 ij₁.2 = some a ∧ ij₁ ≠ ij₀ := by
    by_contra hnone
    have hall : ∀ ij : Fin n × Fin n,
        P ij.1 ij.2 = some a → ij = ij₀ := by
      intro ij hcell
      by_contra hne
      exact hnone ⟨ij, hcell, hne⟩
    exact hnot ⟨ij₀, by simpa [ij₀] using hcell₀, hall⟩
  rcases hsecond with ⟨ij₁, hcell₁, hne₁⟩
  have hmem₁ : ij₁ ∈ filledCells P := by
    simp [filledCells, hcell₁]
  exact ⟨ij₀, ij₁, hmem₀, hmem₁, by simpa [ij₀] using hcell₀, hcell₁, hne₁.symm⟩

theorem exists_symbol_occursExactlyOnce_of_many_used {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (hcard : (filledCells P).card ≤ n - 1)
    (hmany : n < 2 * (usedSymbols P).card) :
    ∃ a : Fin n, SymbolOccursExactlyOnce P a := by
  classical
  by_contra hnone
  let U : Finset (Fin n) := usedSymbols P
  have hnot_once : ∀ a : Fin n, a ∈ U → ¬ SymbolOccursExactlyOnce P a := by
    intro a ha hone
    exact hnone ⟨a, hone⟩
  have htwo : ∀ a : Fin n, a ∈ U →
      ∃ ij₀ ij₁ : Fin n × Fin n,
        ij₀ ∈ filledCells P ∧ ij₁ ∈ filledCells P ∧
          P ij₀.1 ij₀.2 = some a ∧ P ij₁.1 ij₁.2 = some a ∧ ij₀ ≠ ij₁ := by
    intro a ha
    exact exists_two_cells_of_used_not_once ha (hnot_once a ha)
  choose first second hfirst using htwo
  let D : Finset (Fin n × Fin 2) := U ×ˢ (Finset.univ : Finset (Fin 2))
  let f : Fin n × Fin 2 → Fin n × Fin n := fun p =>
    if ha : p.1 ∈ U then
      if p.2 = 0 then first p.1 ha else second p.1 ha
    else
      (p.1, p.1)
  have hf_mem : ∀ p : Fin n × Fin 2, p ∈ D → f p ∈ filledCells P := by
    intro p hp
    have ha : p.1 ∈ U := (Finset.mem_product.mp hp).1
    by_cases hb : p.2 = 0
    · have hf : f p = first p.1 ha := by
        simp [f, ha, hb]
      simpa [hf] using (hfirst p.1 ha).1
    · have hf : f p = second p.1 ha := by
        simp [f, ha, hb]
      simpa [hf] using (hfirst p.1 ha).2.1
  have hf_sym : ∀ p : Fin n × Fin 2, p ∈ D →
      P (f p).1 (f p).2 = some p.1 := by
    intro p hp
    have ha : p.1 ∈ U := (Finset.mem_product.mp hp).1
    by_cases hb : p.2 = 0
    · have hf : f p = first p.1 ha := by
        simp [f, ha, hb]
      simpa [hf] using (hfirst p.1 ha).2.2.1
    · have hf : f p = second p.1 ha := by
        simp [f, ha, hb]
      simpa [hf] using (hfirst p.1 ha).2.2.2.1
  have hf_inj : ∀ x ∈ D, ∀ y ∈ D, f x = f y → x = y := by
    intro x hx y hy hxy
    have hxcell := hf_sym x hx
    have hycell := hf_sym y hy
    have hsym : x.1 = y.1 := by
      exact Option.some.inj (by rw [← hxcell, hxy, hycell])
    cases x with
    | mk ax bx =>
      cases y with
      | mk ay byy =>
        have hsym' : ax = ay := by
          simpa using hsym
        subst ay
        have hax : ax ∈ U := (Finset.mem_product.mp hx).1
        have hfirst_ne_second : first ax hax ≠ second ax hax :=
          (hfirst ax hax).2.2.2.2
        fin_cases bx <;> fin_cases byy <;> simp [f, hax] at hxy ⊢
        · exact False.elim (hfirst_ne_second hxy)
        · exact False.elim (hfirst_ne_second hxy.symm)
  have hle_card : D.card ≤ (filledCells P).card :=
    Finset.card_le_card_of_injOn f hf_mem hf_inj
  have hDcard : D.card = 2 * U.card := by
    simp [D, Nat.mul_comm]
  have htwo_le : 2 * (usedSymbols P).card ≤ (filledCells P).card := by
    simpa [U, hDcard] using hle_card
  have hlt_filled : (filledCells P).card < n := by omega
  omega

lemma exists_symbol_not_used_of_card_lt {n : ℕ}
    (P : Fin n → Fin n → Option (Fin n))
    (hcard : (filledCells P).card < n) :
    ∃ a : Fin n, ∀ i j, P i j ≠ some a := by
  classical
  have hused_lt : (usedSymbols P).card < n :=
    lt_of_le_of_lt (usedSymbols_card_le_filledCells_card P) hcard
  by_contra hnone
  have hall : (Finset.univ : Finset (Fin n)) ⊆ usedSymbols P := by
    intro a _ha
    by_contra ha_used
    have hnot : ∀ i j, P i j ≠ some a := by
      intro i j hcell
      exact ha_used (usedSymbols_mem_of_cell hcell)
    exact hnone ⟨a, hnot⟩
  have hn_le : n ≤ (usedSymbols P).card := by
    calc
      n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ (usedSymbols P).card := Finset.card_le_card hall
  omega

def StrictUpperAll {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) : Prop :=
  ∀ i j a, P i j = some a → i < j

def WeakUpperTriangle {n : ℕ} (P : Fin n → Fin n → Option (Fin n)) : Prop :=
  ∀ i j a, P i j = some a → i ≤ j

def NoLastSymbol {N : ℕ}
    (P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))) : Prop :=
  ∀ i j, P i j ≠ some (Fin.last N)

def strictDropLastSymbol {N : ℕ} (a : Fin (N + 1)) : Option (Fin N) :=
  if h : a.val < N then some ⟨a.val, h⟩ else none

@[simp] lemma strictDropLastSymbol_castSucc {N : ℕ} (a : Fin N) :
    strictDropLastSymbol (Fin.castSucc a : Fin (N + 1)) = some a := by
  unfold strictDropLastSymbol
  have h : (Fin.castSucc a : Fin (N + 1)).val < N := by
    simp [Fin.castSucc]
  simp

lemma strictDropLastSymbol_eq_some {N : ℕ} {a : Fin (N + 1)} {b : Fin N}
    (h : strictDropLastSymbol a = some b) : a = Fin.castSucc b := by
  unfold strictDropLastSymbol at h
  by_cases ha : a.val < N
  · simp [ha] at h
    have hb : (⟨a.val, ha⟩ : Fin N) = b := h
    exact Fin.ext (by simpa [Fin.castSucc] using congrArg Fin.val hb)
  · simp [ha] at h

def strictShrink {N : ℕ}
    (P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))) :
    Fin N → Fin N → Option (Fin N) :=
  fun i j => (P (Fin.castSucc i) (Fin.succ j)).bind strictDropLastSymbol

lemma strictShrink_eq_some_iff {N : ℕ}
    (P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1)))
    (i j : Fin N) (a : Fin N) :
    strictShrink P i j = some a ↔
      P (Fin.castSucc i) (Fin.succ j) = some (Fin.castSucc a) := by
  constructor
  · intro h
    unfold strictShrink at h
    cases hP : P (Fin.castSucc i) (Fin.succ j) with
    | none =>
        simp [hP] at h
    | some b =>
        simp [hP] at h
        have hb : b = Fin.castSucc a := strictDropLastSymbol_eq_some h
        simp [hb]
  · intro h
    simp [strictShrink, h]

lemma isPartialLatin_strictShrink {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (hP : IsPartialLatin P) : IsPartialLatin (strictShrink P) := by
  constructor
  · intro i j₁ j₂ a h₁ h₂
    have h₁P := (strictShrink_eq_some_iff P i j₁ a).mp h₁
    have h₂P := (strictShrink_eq_some_iff P i j₂ a).mp h₂
    have hcols :
        Fin.succ j₁ = Fin.succ j₂ :=
      hP.1 (Fin.castSucc i) (Fin.succ j₁) (Fin.succ j₂)
        (Fin.castSucc a) h₁P h₂P
    exact Fin.succ_inj.mp hcols
  · intro i₁ i₂ j a h₁ h₂
    have h₁P := (strictShrink_eq_some_iff P i₁ j a).mp h₁
    have h₂P := (strictShrink_eq_some_iff P i₂ j a).mp h₂
    have hrows :
        Fin.castSucc i₁ = Fin.castSucc i₂ :=
      hP.2 (Fin.castSucc i₁) (Fin.castSucc i₂) (Fin.succ j)
        (Fin.castSucc a) h₁P h₂P
    exact Fin.castSucc_inj.mp hrows

lemma filledCells_strictShrink_card_le_erase_corner {N : ℕ}
    (P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))) :
    (filledCells (strictShrink P)).card ≤
      ((filledCells P).erase (Fin.last N, (0 : Fin (N + 1)))).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun ij : Fin N × Fin N =>
      ((Fin.castSucc ij.1 : Fin (N + 1)), Fin.succ ij.2)) ?_ ?_
  · intro ij hij
    have hs : (strictShrink P ij.1 ij.2).isSome := by
      simpa [filledCells] using hij
    cases hcell : strictShrink P ij.1 ij.2 with
    | none =>
        simp [hcell] at hs
    | some a =>
        have hP := (strictShrink_eq_some_iff P ij.1 ij.2 a).mp hcell
        have hne : ((Fin.castSucc ij.1 : Fin (N + 1)), Fin.succ ij.2) ≠
            (Fin.last N, (0 : Fin (N + 1))) := by
          intro hp
          have hv : ij.1.val = N := by
            simpa [Fin.castSucc, Fin.last] using congrArg Fin.val (congrArg Prod.fst hp)
          exact (Nat.ne_of_lt ij.1.isLt) hv
        simp [filledCells, hP, hne]
  · intro x hx y hy hxy
    exact Prod.ext
      (Fin.castSucc_inj.mp (congrArg Prod.fst hxy))
      (Fin.succ_inj.mp (congrArg Prod.snd hxy))

theorem strictShrink_weakUpper_of_strictUpper {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (hstrict : StrictUpperAll P) :
    WeakUpperTriangle (strictShrink P) := by
  intro i j a hcell
  have hP := (strictShrink_eq_some_iff P i j a).mp hcell
  have hlt : (Fin.castSucc i : Fin (N + 1)) < Fin.succ j :=
    hstrict (Fin.castSucc i) (Fin.succ j) (Fin.castSucc a) hP
  change i.val ≤ j.val
  have hltVal : i.val < j.val + 1 := by
    change (Fin.castSucc i : Fin (N + 1)).val <
      (Fin.succ j : Fin (N + 1)).val at hlt
    simpa [Fin.castSucc, Fin.succ] using hlt
  omega

def ShiftedCompletes {N : ℕ}
    (Q : Fin N → Fin N → Option (Fin N))
    (L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1)) : Prop :=
  IsLatinSquare L ∧
    ∀ i j a, Q i j = some a →
      L (Fin.castSucc i) (Fin.succ j) = Fin.castSucc a

def ImproperSmetaniukExtensionStatement (N : ℕ) : Prop :=
  ∀ Q : Fin N → Fin N → Option (Fin N),
    IsPartialLatin Q →
      WeakUpperTriangle Q →
        ∀ Lstar : Fin N → Fin N → SignedCell (Fin N),
          ImproperLatinSquare Lstar →
            ImproperlyExtends Q Lstar →
              ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
                ShiftedCompletes Q L

theorem strictUpper_completion_of_improperExtension {N : ℕ}
    (hI : ImproperCompletionTheorem N)
    (hExt : ImproperSmetaniukExtensionStatement N)
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (hP : IsPartialLatin P) (hstrict : StrictUpperAll P)
    (hNoLast : NoLastSymbol P) (hcard : (filledCells P).card ≤ N) :
    ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1), Completes P L := by
  classical
  have hQpartial : IsPartialLatin (strictShrink P) :=
    isPartialLatin_strictShrink hP
  have hQweak : WeakUpperTriangle (strictShrink P) :=
    strictShrink_weakUpper_of_strictUpper hstrict
  have hQcard : (filledCells (strictShrink P)).card ≤ N := by
    have hle := filledCells_strictShrink_card_le_erase_corner P
    have herase_le :
        ((filledCells P).erase (Fin.last N, (0 : Fin (N + 1)))).card ≤
          (filledCells P).card := by
      exact Finset.card_le_card (by intro x hx; exact (Finset.mem_erase.mp hx).2)
    exact le_trans hle (le_trans herase_le hcard)
  obtain ⟨Lstar, hLstar, hLstar_ext⟩ := hI (strictShrink P) hQpartial hQcard
  obtain ⟨L, hLshift⟩ := hExt (strictShrink P) hQpartial hQweak Lstar hLstar hLstar_ext
  refine ⟨L, ?_⟩
  constructor
  · exact hLshift.1
  · intro i j a hcell
    have hlt : i < j := hstrict i j a hcell
    have hi_ltN : i.val < N := by
      have hj_le : j.val ≤ N := Nat.lt_succ_iff.mp j.isLt
      have hltVal : i.val < j.val := hlt
      omega
    have hj_pos : 0 < j.val := by
      have hltVal : i.val < j.val := hlt
      omega
    have ha_ne_last : a ≠ Fin.last N := by
      intro ha
      exact hNoLast i j (by simpa [ha] using hcell)
    have ha_ltN : a.val < N := by
      have hle : a.val ≤ N := Nat.lt_succ_iff.mp a.isLt
      by_contra hltN
      have hge : N ≤ a.val := Nat.le_of_not_gt hltN
      exact ha_ne_last (Fin.ext (le_antisymm hle hge))
    let ii : Fin N := ⟨i.val, hi_ltN⟩
    let jj : Fin N := ⟨j.val - 1, by omega⟩
    let aa : Fin N := ⟨a.val, ha_ltN⟩
    have hi_cast : (Fin.castSucc ii : Fin (N + 1)) = i := Fin.ext rfl
    have hj_succ : (Fin.succ jj : Fin (N + 1)) = j := by
      apply Fin.ext
      simp [Fin.succ, jj]
      omega
    have ha_cast : (Fin.castSucc aa : Fin (N + 1)) = a := Fin.ext rfl
    have hsmall : strictShrink P ii jj = some aa := by
      apply (strictShrink_eq_some_iff P ii jj aa).mpr
      simpa [hi_cast, hj_succ, ha_cast] using hcell
    have hLcell := hLshift.2 ii jj aa hsmall
    simpa [hi_cast, hj_succ, ha_cast] using hLcell

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

private noncomputable def finSuccAboveEquivNe {m : ℕ} (x₀ : Fin (m + 1)) :
    Fin m ≃ {x : Fin (m + 1) // x ≠ x₀} := by
  classical
  refine Equiv.ofBijective (fun i => ⟨x₀.succAbove i, Fin.succAbove_ne x₀ i⟩) ?_
  constructor
  · intro i j hij
    exact x₀.succAbove_right_injective (congrArg Subtype.val hij)
  · intro x
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq x.2
    exact ⟨i, Subtype.ext hi⟩

private noncomputable def splitAt {m : ℕ} (x₀ : Fin (m + 1)) :
    Fin (m + 1) ≃ Option (Fin m) where
  toFun x :=
    if hx : x = x₀ then none else some ((finSuccAboveEquivNe x₀).symm ⟨x, hx⟩)
  invFun o := match o with
    | none => x₀
    | some i => x₀.succAbove i
  left_inv := by
    intro x
    by_cases hx : x = x₀
    · simp [hx]
    · simp [hx]
      exact congrArg Subtype.val ((finSuccAboveEquivNe x₀).apply_symm_apply ⟨x, hx⟩)
  right_inv := by
    intro o
    cases o with
    | none => simp
    | some i =>
        have hne : x₀.succAbove i ≠ x₀ := Fin.succAbove_ne x₀ i
        simp [hne]
        have hsub : (⟨x₀.succAbove i, hne⟩ : {x : Fin (m + 1) // x ≠ x₀}) =
            finSuccAboveEquivNe x₀ i := rfl
        simp [hsub]

private noncomputable def rankLift {m : ℕ} (x₀ : Fin (m + 1))
    (ρ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  (splitAt x₀).trans ((Equiv.optionCongr ρ).trans (finSuccEquiv m).symm)

@[simp] private lemma rankLift_base {m : ℕ} (x₀ : Fin (m + 1))
    (ρ : Equiv.Perm (Fin m)) :
    rankLift x₀ ρ x₀ = 0 := by
  simp [rankLift, splitAt]

private lemma rankLift_succAbove {m : ℕ} (x₀ : Fin (m + 1))
    (ρ : Equiv.Perm (Fin m)) (i : Fin m) :
    rankLift x₀ ρ (x₀.succAbove i) = Fin.succ (ρ i) := by
  have hne : x₀.succAbove i ≠ x₀ := Fin.succAbove_ne x₀ i
  simp [rankLift, splitAt, hne]
  have hsub : (⟨x₀.succAbove i, hne⟩ : {x : Fin (m + 1) // x ≠ x₀}) =
      finSuccAboveEquivNe x₀ i := rfl
  simp [hsub]

private lemma exists_empty_column_of_card_lt {n : ℕ}
    (S : Finset (Fin n × Fin n)) (hS : S.card < n) :
    ∃ c₀ : Fin n, ∀ p ∈ S, p.2 ≠ c₀ := by
  classical
  by_contra hnone
  have hcols_all : ∀ c : Fin n, c ∈ S.image Prod.snd := by
    intro c
    by_contra hc
    exact hnone ⟨c, by
      intro p hp hpcol
      exact hc (Finset.mem_image.mpr ⟨p, hp, hpcol⟩)⟩
  have hn_le_cols : n ≤ (S.image Prod.snd).card := by
    calc
      n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ (S.image Prod.snd).card := by
        exact Finset.card_le_card (by
          intro c _hc
          exact hcols_all c)
  have hcols_le_S : (S.image Prod.snd).card ≤ S.card := Finset.card_image_le
  omega

/--
If fewer than `n` cells are marked in an `n × n` board, rows and columns can be
permuted so every marked cell lies strictly above the diagonal.

The proof is the peeling induction used in Smetaniuk's normalization: choose
an empty column and a nonempty row, send both to rank `0`, recurse after
deleting them, then lift the recursive ranks by `+1`.
-/
theorem exists_perm_strictly_above {n : ℕ} (S : Finset (Fin n × Fin n))
    (hS : S.card < n) :
    ∃ σ τ : Equiv.Perm (Fin n), ∀ p ∈ S, σ p.1 < τ p.2 := by
  classical
  revert S
  refine Nat.strong_induction_on n ?_
  intro n ih S hS
  by_cases hEmpty : S = ∅
  · refine ⟨1, 1, ?_⟩
    intro p hp
    simp [hEmpty] at hp
  · obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    cases n with
    | zero =>
        have hpos : 0 < S.card := Finset.card_pos.mpr ⟨p₀, hp₀⟩
        omega
    | succ m =>
        let r₀ : Fin (m + 1) := p₀.1
        obtain ⟨c₀, hc₀⟩ := exists_empty_column_of_card_lt S hS
        have hScard_pos : 0 < S.card := Finset.card_pos.mpr ⟨p₀, hp₀⟩
        have hmpos : 0 < m := by omega
        let rowIndex : Fin (m + 1) → Fin m := fun i =>
          if hi : i = r₀ then ⟨0, hmpos⟩ else (finSuccAboveEquivNe r₀).symm ⟨i, hi⟩
        let colIndex : Fin (m + 1) → Fin m := fun j =>
          if hj : j = c₀ then ⟨0, hmpos⟩ else (finSuccAboveEquivNe c₀).symm ⟨j, hj⟩
        let S' : Finset (Fin m × Fin m) :=
          (S.filter fun p => p.1 ≠ r₀).image fun p => (rowIndex p.1, colIndex p.2)
        have hfilter_subset_erase :
            (S.filter fun p => p.1 ≠ r₀) ⊆ S.erase p₀ := by
          intro p hp
          have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
          have hprow : p.1 ≠ r₀ := (Finset.mem_filter.mp hp).2
          have hpne : p ≠ p₀ := by
            intro h
            exact hprow (by simp [r₀, h])
          simp [hpS, hpne]
        have hfilter_card_le :
            (S.filter fun p => p.1 ≠ r₀).card ≤ S.card - 1 := by
          have hle := Finset.card_le_card hfilter_subset_erase
          have herase := Finset.card_erase_of_mem hp₀
          omega
        have hS'_le_filter :
            S'.card ≤ (S.filter fun p => p.1 ≠ r₀).card := by
          exact Finset.card_image_le
        have hS' : S'.card < m := by
          omega
        obtain ⟨σ', τ', hrec⟩ := ih m (Nat.lt_succ_self m) S' hS'
        let σ : Equiv.Perm (Fin (m + 1)) := rankLift r₀ σ'
        let τ : Equiv.Perm (Fin (m + 1)) := rankLift c₀ τ'
        refine ⟨σ, τ, ?_⟩
        intro p hp
        have hpcol_ne : p.2 ≠ c₀ := hc₀ p hp
        by_cases hrow : p.1 = r₀
        · have hσbase : σ p.1 = 0 := by
            rw [hrow]
            simp [σ]
          have hcol_succ :
              c₀.succAbove (colIndex p.2) = p.2 := by
            simp [colIndex, hpcol_ne]
            exact congrArg Subtype.val
              ((finSuccAboveEquivNe c₀).apply_symm_apply ⟨p.2, hpcol_ne⟩)
          have hτ :
              τ p.2 = Fin.succ (τ' (colIndex p.2)) := by
            calc
              τ p.2 = τ (c₀.succAbove (colIndex p.2)) := by rw [hcol_succ]
              _ = Fin.succ (τ' (colIndex p.2)) :=
                rankLift_succAbove c₀ τ' (colIndex p.2)
          rw [hσbase, hτ]
          change (0 : ℕ) < (τ' (colIndex p.2)).val + 1
          omega
        · have hrow_succ :
              r₀.succAbove (rowIndex p.1) = p.1 := by
            simp [rowIndex, hrow]
            exact congrArg Subtype.val
              ((finSuccAboveEquivNe r₀).apply_symm_apply ⟨p.1, hrow⟩)
          have hcol_succ :
              c₀.succAbove (colIndex p.2) = p.2 := by
            simp [colIndex, hpcol_ne]
            exact congrArg Subtype.val
              ((finSuccAboveEquivNe c₀).apply_symm_apply ⟨p.2, hpcol_ne⟩)
          have hp_filter : p ∈ S.filter fun q => q.1 ≠ r₀ :=
            Finset.mem_filter.mpr ⟨hp, hrow⟩
          have hpS' : (rowIndex p.1, colIndex p.2) ∈ S' :=
            Finset.mem_image.mpr ⟨p, hp_filter, rfl⟩
          have hlt' : σ' (rowIndex p.1) < τ' (colIndex p.2) :=
            hrec (rowIndex p.1, colIndex p.2) hpS'
          have hσ :
              σ p.1 = Fin.succ (σ' (rowIndex p.1)) := by
            calc
              σ p.1 = σ (r₀.succAbove (rowIndex p.1)) := by rw [hrow_succ]
              _ = Fin.succ (σ' (rowIndex p.1)) :=
                rankLift_succAbove r₀ σ' (rowIndex p.1)
          have hτ :
              τ p.2 = Fin.succ (τ' (colIndex p.2)) := by
            calc
              τ p.2 = τ (c₀.succAbove (colIndex p.2)) := by rw [hcol_succ]
              _ = Fin.succ (τ' (colIndex p.2)) :=
                rankLift_succAbove c₀ τ' (colIndex p.2)
          rw [hσ, hτ]
          exact show Fin.succ (σ' (rowIndex p.1)) < Fin.succ (τ' (colIndex p.2)) by
            simpa [Fin.succ] using Nat.succ_lt_succ (show (σ' (rowIndex p.1)).val <
              (τ' (colIndex p.2)).val from hlt')

/--
Peeling normalization with one distinguished cell: fewer than `n` marked cells
can be permuted so the distinguished cell lies on the main diagonal and every
other marked cell lies strictly above it.
-/
theorem exists_perm_singleton_diagonal_strictly_above {n : ℕ}
    (S : Finset (Fin n × Fin n)) {e : Fin n × Fin n}
    (he : e ∈ S) (hS : S.card < n) :
    ∃ σ τ : Equiv.Perm (Fin n), ∃ d : Fin n,
      σ e.1 = d ∧ τ e.2 = d ∧
        ∀ p ∈ S, p ≠ e → σ p.1 < τ p.2 := by
  classical
  revert e S
  refine Nat.strong_induction_on n ?_
  intro n ih S e he hS
  cases n with
  | zero =>
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨e, he⟩
      omega
  | succ m =>
      by_cases houtside : ∃ p : Fin (m + 1) × Fin (m + 1),
          p ∈ S ∧ p ≠ e ∧ p.1 ≠ e.1
      · rcases houtside with ⟨p₀, hp₀, hp₀_ne_e, hp₀_row_ne⟩
        let r₀ : Fin (m + 1) := p₀.1
        obtain ⟨c₀, hc₀⟩ := exists_empty_column_of_card_lt S hS
        have hmpos : 0 < m := by
          have hpos : 0 < S.card := Finset.card_pos.mpr ⟨e, he⟩
          omega
        have he_row_ne : e.1 ≠ r₀ := by
          intro h
          exact hp₀_row_ne h.symm
        have he_col_ne : e.2 ≠ c₀ := hc₀ e he
        let rowIndex : Fin (m + 1) → Fin m := fun i =>
          if hi : i = r₀ then ⟨0, hmpos⟩ else (finSuccAboveEquivNe r₀).symm ⟨i, hi⟩
        let colIndex : Fin (m + 1) → Fin m := fun j =>
          if hj : j = c₀ then ⟨0, hmpos⟩ else (finSuccAboveEquivNe c₀).symm ⟨j, hj⟩
        let S' : Finset (Fin m × Fin m) :=
          (S.filter fun p => p.1 ≠ r₀).image fun p => (rowIndex p.1, colIndex p.2)
        let e' : Fin m × Fin m := (rowIndex e.1, colIndex e.2)
        have he_filter : e ∈ S.filter fun p => p.1 ≠ r₀ :=
          Finset.mem_filter.mpr ⟨he, he_row_ne⟩
        have he' : e' ∈ S' := by
          exact Finset.mem_image.mpr ⟨e, he_filter, rfl⟩
        have hfilter_subset_erase :
            (S.filter fun p => p.1 ≠ r₀) ⊆ S.erase p₀ := by
          intro p hp
          have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
          have hprow : p.1 ≠ r₀ := (Finset.mem_filter.mp hp).2
          have hpne : p ≠ p₀ := by
            intro h
            exact hprow (by simp [r₀, h])
          simp [hpS, hpne]
        have hfilter_card_le :
            (S.filter fun p => p.1 ≠ r₀).card ≤ S.card - 1 := by
          have hle := Finset.card_le_card hfilter_subset_erase
          have herase := Finset.card_erase_of_mem hp₀
          omega
        have hS'_le_filter :
            S'.card ≤ (S.filter fun p => p.1 ≠ r₀).card := by
          exact Finset.card_image_le
        have hS' : S'.card < m := by
          omega
        obtain ⟨σ', τ', d', hσ'e, hτ'e, hrec⟩ :=
          ih m (Nat.lt_succ_self m) S' he' hS'
        let σ : Equiv.Perm (Fin (m + 1)) := rankLift r₀ σ'
        let τ : Equiv.Perm (Fin (m + 1)) := rankLift c₀ τ'
        refine ⟨σ, τ, Fin.succ d', ?_, ?_, ?_⟩
        · have hrow_succ :
              r₀.succAbove (rowIndex e.1) = e.1 := by
            simp [rowIndex, he_row_ne]
            exact congrArg Subtype.val
              ((finSuccAboveEquivNe r₀).apply_symm_apply ⟨e.1, he_row_ne⟩)
          calc
            σ e.1 = σ (r₀.succAbove (rowIndex e.1)) := by rw [hrow_succ]
            _ = Fin.succ (σ' (rowIndex e.1)) :=
              rankLift_succAbove r₀ σ' (rowIndex e.1)
            _ = Fin.succ d' := by rw [hσ'e]
        · have hcol_succ :
              c₀.succAbove (colIndex e.2) = e.2 := by
            simp [colIndex, he_col_ne]
            exact congrArg Subtype.val
              ((finSuccAboveEquivNe c₀).apply_symm_apply ⟨e.2, he_col_ne⟩)
          calc
            τ e.2 = τ (c₀.succAbove (colIndex e.2)) := by rw [hcol_succ]
            _ = Fin.succ (τ' (colIndex e.2)) :=
              rankLift_succAbove c₀ τ' (colIndex e.2)
            _ = Fin.succ d' := by rw [hτ'e]
        · intro p hp hp_ne_e
          have hpcol_ne : p.2 ≠ c₀ := hc₀ p hp
          by_cases hprow : p.1 = r₀
          · have hσbase : σ p.1 = 0 := by
              rw [hprow]
              simp [σ]
            have hcol_succ :
                c₀.succAbove (colIndex p.2) = p.2 := by
              simp [colIndex, hpcol_ne]
              exact congrArg Subtype.val
                ((finSuccAboveEquivNe c₀).apply_symm_apply ⟨p.2, hpcol_ne⟩)
            have hτ :
                τ p.2 = Fin.succ (τ' (colIndex p.2)) := by
              calc
                τ p.2 = τ (c₀.succAbove (colIndex p.2)) := by rw [hcol_succ]
                _ = Fin.succ (τ' (colIndex p.2)) :=
                  rankLift_succAbove c₀ τ' (colIndex p.2)
            rw [hσbase, hτ]
            change (0 : ℕ) < (τ' (colIndex p.2)).val + 1
            omega
          · have hrow_succ :
                r₀.succAbove (rowIndex p.1) = p.1 := by
              simp [rowIndex, hprow]
              exact congrArg Subtype.val
                ((finSuccAboveEquivNe r₀).apply_symm_apply ⟨p.1, hprow⟩)
            have hcol_succ :
                c₀.succAbove (colIndex p.2) = p.2 := by
              simp [colIndex, hpcol_ne]
              exact congrArg Subtype.val
                ((finSuccAboveEquivNe c₀).apply_symm_apply ⟨p.2, hpcol_ne⟩)
            have hp_filter : p ∈ S.filter fun q => q.1 ≠ r₀ :=
              Finset.mem_filter.mpr ⟨hp, hprow⟩
            have hpS' : (rowIndex p.1, colIndex p.2) ∈ S' :=
              Finset.mem_image.mpr ⟨p, hp_filter, rfl⟩
            have hp'_ne_e' : (rowIndex p.1, colIndex p.2) ≠ e' := by
              intro hpe'
              have hrow_eq : p.1 = e.1 := by
                have hidx : rowIndex p.1 = rowIndex e.1 :=
                  congrArg Prod.fst hpe'
                have hs₁ : r₀.succAbove (rowIndex p.1) =
                    r₀.succAbove (rowIndex e.1) := by rw [hidx]
                have he_row_succ :
                    r₀.succAbove (rowIndex e.1) = e.1 := by
                  simp [rowIndex, he_row_ne]
                  exact congrArg Subtype.val
                    ((finSuccAboveEquivNe r₀).apply_symm_apply ⟨e.1, he_row_ne⟩)
                exact hrow_succ.symm.trans (hs₁.trans he_row_succ)
              have hcol_eq : p.2 = e.2 := by
                have hidx : colIndex p.2 = colIndex e.2 :=
                  congrArg Prod.snd hpe'
                have hs₁ : c₀.succAbove (colIndex p.2) =
                    c₀.succAbove (colIndex e.2) := by rw [hidx]
                have he_col_succ :
                    c₀.succAbove (colIndex e.2) = e.2 := by
                  simp [colIndex, he_col_ne]
                  exact congrArg Subtype.val
                    ((finSuccAboveEquivNe c₀).apply_symm_apply ⟨e.2, he_col_ne⟩)
                exact hcol_succ.symm.trans (hs₁.trans he_col_succ)
              exact hp_ne_e (Prod.ext hrow_eq hcol_eq)
            have hlt' : σ' (rowIndex p.1) < τ' (colIndex p.2) :=
              hrec (rowIndex p.1, colIndex p.2) hpS' hp'_ne_e'
            have hσ :
                σ p.1 = Fin.succ (σ' (rowIndex p.1)) := by
              calc
                σ p.1 = σ (r₀.succAbove (rowIndex p.1)) := by rw [hrow_succ]
                _ = Fin.succ (σ' (rowIndex p.1)) :=
                  rankLift_succAbove r₀ σ' (rowIndex p.1)
            have hτ :
                τ p.2 = Fin.succ (τ' (colIndex p.2)) := by
              calc
                τ p.2 = τ (c₀.succAbove (colIndex p.2)) := by rw [hcol_succ]
                _ = Fin.succ (τ' (colIndex p.2)) :=
                  rankLift_succAbove c₀ τ' (colIndex p.2)
            rw [hσ, hτ]
            exact show Fin.succ (σ' (rowIndex p.1)) < Fin.succ (τ' (colIndex p.2)) by
              simpa [Fin.succ] using Nat.succ_lt_succ
                (show (σ' (rowIndex p.1)).val < (τ' (colIndex p.2)).val from hlt')
      · let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 e.1
        let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 e.2
        refine ⟨σ, τ, 0, ?_, ?_, ?_⟩
        · simp [σ]
        · simp [τ]
        · intro p hp hp_ne_e
          have hrow : p.1 = e.1 := by
            by_contra hne
            exact houtside ⟨p, hp, hp_ne_e, hne⟩
          have hcol_ne : p.2 ≠ e.2 := by
            intro hcol
            exact hp_ne_e (Prod.ext hrow hcol)
          have hτ_ne_zero : τ p.2 ≠ 0 := by
            intro hzero
            have hτe : τ e.2 = 0 := by simp [τ]
            have hcol : p.2 = e.2 := τ.injective (hzero.trans hτe.symm)
            exact hcol_ne hcol
          have hτ_pos : 0 < (τ p.2).val := by
            have hval_ne : (τ p.2).val ≠ 0 := by
              intro hval
              exact hτ_ne_zero (Fin.ext hval)
            omega
          rw [hrow]
          change (σ e.1).val < (τ p.2).val
          simp [σ]
          exact hτ_pos

theorem exists_relabel_singleton_smetaniukTriangularNormalized {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    {a : Fin (N + 1)}
    (hcard : (filledCells P).card ≤ N)
    (hone : SymbolOccursExactlyOnce P a) :
    ∃ rowPerm colPerm symPerm : Equiv.Perm (Fin (N + 1)), ∃ d : Fin (N + 1),
      SmetaniukTriangularNormalized
        (relabelPartial rowPerm colPerm symPerm P) d (Fin.last N) := by
  classical
  rcases hone with ⟨e, hcell_e, huniq⟩
  have he : e ∈ filledCells P := by
    simp [filledCells, hcell_e]
  have hlt : (filledCells P).card < N + 1 := by omega
  obtain ⟨σ, τ, d, hσe, hτe, hstrict⟩ :=
    exists_perm_singleton_diagonal_strictly_above (filledCells P) he hlt
  let symPerm : Equiv.Perm (Fin (N + 1)) := Equiv.swap a (Fin.last N)
  refine ⟨σ.symm, τ.symm, symPerm, d, ?_⟩
  have hrow_old : σ.symm d = e.1 := by
    apply σ.injective
    simp [hσe]
  have hcol_old : τ.symm d = e.2 := by
    apply τ.injective
    simp [hτe]
  have hsym_last : symPerm.symm (Fin.last N) = a := by
    simp [symPerm]
  have hdiag :
      relabelPartial σ.symm τ.symm symPerm P d d = some (Fin.last N) := by
    apply (relabelPartial_eq_some_iff σ.symm τ.symm symPerm P d d
      (Fin.last N)).mpr
    simpa [hrow_old, hcol_old, hsym_last] using hcell_e
  constructor
  · constructor
    · exact hdiag
    · refine ⟨(d, d), hdiag, ?_⟩
      intro ij hij
      have hold :
          P (σ.symm ij.1) (τ.symm ij.2) = some a := by
        have hraw :=
          (relabelPartial_eq_some_iff σ.symm τ.symm symPerm P ij.1 ij.2
            (Fin.last N)).mp hij
        simpa [hsym_last] using hraw
      have hp : (σ.symm ij.1, τ.symm ij.2) = e := huniq _ hold
      apply Prod.ext
      · have hrow : σ.symm ij.1 = e.1 := congrArg Prod.fst hp
        calc
          ij.1 = σ (σ.symm ij.1) := by simp
          _ = σ e.1 := by rw [hrow]
          _ = d := hσe
      · have hcol : τ.symm ij.2 = e.2 := congrArg Prod.snd hp
        calc
          ij.2 = τ (τ.symm ij.2) := by simp
          _ = τ e.2 := by rw [hcol]
          _ = d := hτe
  · intro i j s hcell hs
    have hold :
        P (σ.symm i) (τ.symm j) = some (symPerm.symm s) :=
      (relabelPartial_eq_some_iff σ.symm τ.symm symPerm P i j s).mp hcell
    have hp : (σ.symm i, τ.symm j) ∈ filledCells P := by
      simp [filledCells, hold]
    have hp_ne : (σ.symm i, τ.symm j) ≠ e := by
      intro hp_eq
      have hsym_eq : symPerm.symm s = a := by
        have hsame : some (symPerm.symm s) = some a := by
          rw [← hold]
          simpa [← hp_eq] using hcell_e
        exact Option.some.inj hsame
      have hs_last : s = Fin.last N := by
        calc
          s = symPerm (symPerm.symm s) := by simp
          _ = symPerm a := by rw [hsym_eq]
          _ = Fin.last N := by simp [symPerm]
      exact hs hs_last
    have hlt' := hstrict (σ.symm i, τ.symm j) hp hp_ne
    simpa using hlt'

theorem latinSquareCompletion_step_of_improperExtension {N : ℕ}
    (hE : LatinSquareCompletionTheorem N)
    (hExt : ImproperSmetaniukExtensionStatement N) :
    LatinSquareCompletionTheorem (N + 1) := by
  classical
  intro P hP hcard
  have hcardN : (filledCells P).card ≤ N := by
    simpa using hcard
  have hlt : (filledCells P).card < N + 1 := by omega
  obtain ⟨fresh, hfresh⟩ := exists_symbol_not_used_of_card_lt P hlt
  obtain ⟨σ, τ, hstrictPos⟩ := exists_perm_strictly_above (filledCells P) hlt
  let symPerm : Equiv.Perm (Fin (N + 1)) := Equiv.swap fresh (Fin.last N)
  let P' : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1)) :=
    relabelPartial σ.symm τ.symm symPerm P
  have hP' : IsPartialLatin P' := by
    dsimp [P']
    exact isPartialLatin_relabelPartial σ.symm τ.symm symPerm hP
  have hstrict : StrictUpperAll P' := by
    intro i j a hcell
    have hold :
        P (σ.symm i) (τ.symm j) = some (symPerm.symm a) := by
      exact (relabelPartial_eq_some_iff σ.symm τ.symm symPerm P i j a).mp hcell
    have hp : (σ.symm i, τ.symm j) ∈ filledCells P := by
      simp [filledCells, hold]
    have hpos := hstrictPos (σ.symm i, τ.symm j) hp
    simpa using hpos
  have hNoLast : NoLastSymbol P' := by
    intro i j hcell
    have hold :
        P (σ.symm i) (τ.symm j) =
          some (symPerm.symm (Fin.last N)) := by
      exact (relabelPartial_eq_some_iff σ.symm τ.symm symPerm P i j
        (Fin.last N)).mp hcell
    have hsym : symPerm.symm (Fin.last N) = fresh := by
      simp [symPerm]
    exact hfresh (σ.symm i) (τ.symm j) (by simpa [hsym] using hold)
  have hcard' : (filledCells P').card ≤ N := by
    dsimp [P']
    rw [filledCells_relabelPartial_card]
    exact hcardN
  obtain ⟨L', hL'⟩ :=
    strictUpper_completion_of_improperExtension
      (evans_to_improperCompletion hE) hExt hP' hstrict hNoLast hcard'
  exact (completion_exists_relabelPartial_iff σ.symm τ.symm symPerm P).mp ⟨L', hL'⟩

theorem chapter33_unconditional_of_improperExtensionStatements
    (hExt : ∀ N : ℕ, ImproperSmetaniukExtensionStatement N) :
    ∀ n : ℕ, LatinSquareCompletionTheorem n := by
  intro n
  induction n with
  | zero =>
      exact chapter33_order_le_three 0 (by omega)
  | succ N ih =>
      by_cases hsmall : N + 1 ≤ 3
      · exact chapter33_order_le_three (N + 1) hsmall
      · exact latinSquareCompletion_step_of_improperExtension ih (hExt N)

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

def reverseSeedColumns {N : ℕ} (L₀ : Fin N → Fin N → Fin N) :
    Fin N → Fin N → Fin N :=
  fun i j => L₀ i (Fin.rev j)

lemma isPartialLatin_smetMainPartial {N : ℕ}
    {L₀ : Fin N → Fin N → Fin N} (hL₀ : IsLatinSquare L₀) :
    IsPartialLatin (smetMainPartial L₀) := by
  exact isPartialLatin_reverseColumnsPartial (isPartialLatin_smetBackPartial hL₀)

lemma isLatinSquare_reverseSeedColumns {N : ℕ}
    {L₀ : Fin N → Fin N → Fin N} (hL₀ : IsLatinSquare L₀) :
    IsLatinSquare (reverseSeedColumns L₀) := by
  constructor
  · intro i j₁ j₂ h
    have hrev : Fin.rev j₁ = Fin.rev j₂ := hL₀.1 i h
    exact Fin.revPerm.injective hrev
  · intro j i₁ i₂ h
    exact hL₀.2 (Fin.rev j) h

lemma smetMainPartial_last_last {N : ℕ} (L₀ : Fin N → Fin N → Fin N) :
    smetMainPartial L₀ (Fin.last N) (Fin.last N) = some (Fin.last N) := by
  simp [smetMainPartial, smetBackPartial, Fin.rev]

lemma smetMainPartial_diagonal {N : ℕ} (L₀ : Fin N → Fin N → Fin N)
    (i : Fin (N + 1)) :
    smetMainPartial L₀ i i = some (Fin.last N) := by
  rw [smetMainPartial, reverseColumnsPartial_eq]
  apply smetBackPartial_back_diagonal
  simp [Fin.rev]
  have hi : i.val ≤ N := Nat.lt_succ_iff.mp i.isLt
  omega

lemma smetMainPartial_reverseSeedColumns_shifted {N : ℕ}
    (L₀ : Fin N → Fin N → Fin N) {i j : Fin N} (hij : i ≤ j) :
    smetMainPartial (reverseSeedColumns L₀) (Fin.castSucc i) (Fin.succ j) =
      some (Fin.castSucc (L₀ i j)) := by
  let k : Fin N := Fin.rev j
  have hrev_succ :
      Fin.rev (Fin.succ j : Fin (N + 1)) = (Fin.castSucc k : Fin (N + 1)) := by
    apply Fin.ext
    simp [Fin.rev, Fin.succ, Fin.castSucc, k]
  have hsum_lt :
      (Fin.castSucc i : Fin (N + 1)).val +
          (Fin.castSucc k : Fin (N + 1)).val < N := by
    have hijVal : i.val ≤ j.val := hij
    simp [Fin.castSucc, k, Fin.rev]
    omega
  have hsum_ne :
      (Fin.castSucc i : Fin (N + 1)).val +
          (Fin.castSucc k : Fin (N + 1)).val ≠ N := by
    omega
  have hi_eq : (⟨(Fin.castSucc i : Fin (N + 1)).val, by omega⟩ : Fin N) = i := by
    exact Fin.ext rfl
  have hk_rev : Fin.rev (⟨(Fin.castSucc k : Fin (N + 1)).val, by omega⟩ : Fin N) = j := by
    apply Fin.ext
    simp [Fin.castSucc, k, Fin.rev]
    omega
  have hsum_lt' : i.val + k.val < N := by
    simpa [Fin.castSucc] using hsum_lt
  have hsum_ne' : i.val + k.val ≠ N := by
    simpa [Fin.castSucc] using hsum_ne
  have hk_rev' : Fin.rev k = j := by
    have hk_eq : (⟨(Fin.castSucc k : Fin (N + 1)).val, by omega⟩ : Fin N) = k := by
      exact Fin.ext rfl
    simpa [hk_eq] using hk_rev
  change reverseColumnsPartial (smetBackPartial (reverseSeedColumns L₀))
      (Fin.castSucc i) (Fin.succ j) = some (Fin.castSucc (L₀ i j))
  rw [reverseColumnsPartial_eq, hrev_succ]
  simp [smetBackPartial, reverseSeedColumns, hsum_ne', hsum_lt', hi_eq, hk_rev']

theorem shiftedCompletes_of_smetMainPartial_reverseSeedColumns {N : ℕ}
    {Q : Fin N → Fin N → Option (Fin N)} {L₀ : Fin N → Fin N → Fin N}
    {L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1)}
    (hweak : WeakUpperTriangle Q)
    (hQ : ∀ i j a, Q i j = some a → L₀ i j = a)
    (hL : Completes (smetMainPartial (reverseSeedColumns L₀)) L) :
    ShiftedCompletes Q L := by
  constructor
  · exact hL.1
  · intro i j a hcell
    have hij : i ≤ j := hweak i j a hcell
    have hmain :=
      smetMainPartial_reverseSeedColumns_shifted L₀ hij
    have hmain' :
        smetMainPartial (reverseSeedColumns L₀)
          (Fin.castSucc i) (Fin.succ j) = some (Fin.castSucc a) := by
      simpa [hQ i j a hcell] using hmain
    exact hL.2 (Fin.castSucc i) (Fin.succ j) (Fin.castSucc a) hmain'

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

/--
The shrink compatible with `smetMainPartial`: delete the last row and main
column `0`, and reverse the remaining `N` columns.  Thus smaller column `k`
records main column `N - k`, including the original last column as `k = 0`.
-/
def smetMainKeepLastShrink {N : ℕ}
    (P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))) :
    Fin N → Fin N → Option (Fin N) :=
  fun i j => (P (Fin.castSucc i) (Fin.rev (Fin.castSucc j))).bind dropLastSymbol

lemma smetMainKeepLastShrink_eq_some_iff {N : ℕ}
    (P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1)))
    (i j : Fin N) (a : Fin N) :
    smetMainKeepLastShrink P i j = some a ↔
      P (Fin.castSucc i) (Fin.rev (Fin.castSucc j)) = some (Fin.castSucc a) := by
  constructor
  · intro h
    unfold smetMainKeepLastShrink at h
    cases hP : P (Fin.castSucc i) (Fin.rev (Fin.castSucc j)) with
    | none =>
        simp [hP] at h
    | some b =>
        simp [hP] at h
        have hb : b = Fin.castSucc a := dropLastSymbol_eq_some h
        simp [hb]
  · intro h
    simp [smetMainKeepLastShrink, h]

lemma isPartialLatin_smetMainKeepLastShrink {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (hP : IsPartialLatin P) : IsPartialLatin (smetMainKeepLastShrink P) := by
  constructor
  · intro i j₁ j₂ a h₁ h₂
    have h₁P := (smetMainKeepLastShrink_eq_some_iff P i j₁ a).mp h₁
    have h₂P := (smetMainKeepLastShrink_eq_some_iff P i j₂ a).mp h₂
    have hcols :
        Fin.rev (Fin.castSucc j₁) = Fin.rev (Fin.castSucc j₂) :=
      hP.1 (Fin.castSucc i) (Fin.rev (Fin.castSucc j₁))
        (Fin.rev (Fin.castSucc j₂)) (Fin.castSucc a) h₁P h₂P
    have hcast : Fin.castSucc j₁ = Fin.castSucc j₂ :=
      Fin.revPerm.injective hcols
    exact Fin.castSucc_inj.mp hcast
  · intro i₁ i₂ j a h₁ h₂
    have h₁P := (smetMainKeepLastShrink_eq_some_iff P i₁ j a).mp h₁
    have h₂P := (smetMainKeepLastShrink_eq_some_iff P i₂ j a).mp h₂
    have hrows :
        Fin.castSucc i₁ = Fin.castSucc i₂ :=
      hP.2 (Fin.castSucc i₁) (Fin.castSucc i₂) (Fin.rev (Fin.castSucc j))
        (Fin.castSucc a) h₁P h₂P
    exact Fin.castSucc_inj.mp hrows

lemma filledCells_smetMainKeepLastShrink_card_le_erase_diag {N : ℕ}
    (P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))) :
    (filledCells (smetMainKeepLastShrink P)).card ≤
      ((filledCells P).erase (Fin.last N, Fin.last N)).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun ij : Fin N × Fin N =>
      ((Fin.castSucc ij.1 : Fin (N + 1)), Fin.rev (Fin.castSucc ij.2))) ?_ ?_
  · intro ij hij
    have hs : (smetMainKeepLastShrink P ij.1 ij.2).isSome := by
      simpa [filledCells] using hij
    cases hcell : smetMainKeepLastShrink P ij.1 ij.2 with
    | none =>
        simp [hcell] at hs
    | some a =>
        have hP := (smetMainKeepLastShrink_eq_some_iff P ij.1 ij.2 a).mp hcell
        have hne : ((Fin.castSucc ij.1 : Fin (N + 1)), Fin.rev (Fin.castSucc ij.2)) ≠
            (Fin.last N, Fin.last N) := by
          intro hp
          exact fin_castSucc_ne_last ij.1 (congrArg Prod.fst hp)
        simp [filledCells, hP, hne]
  · intro x hx y hy hxy
    have hrow : x.1 = y.1 :=
      Fin.castSucc_inj.mp (congrArg Prod.fst hxy)
    have hcol_rev : Fin.rev (Fin.castSucc x.2) = Fin.rev (Fin.castSucc y.2) :=
      congrArg Prod.snd hxy
    have hcol_cast : Fin.castSucc x.2 = Fin.castSucc y.2 :=
      Fin.revPerm.injective hcol_rev
    exact Prod.ext hrow (Fin.castSucc_inj.mp hcol_cast)

theorem smetMainKeepLastShrink_step {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (hP : IsPartialLatin P)
    (hdiag : P (Fin.last N) (Fin.last N) = some (Fin.last N))
    (hcard : (filledCells P).card = N) :
    IsPartialLatin (smetMainKeepLastShrink P) ∧
      (filledCells (smetMainKeepLastShrink P)).card ≤ N - 1 := by
  constructor
  · exact isPartialLatin_smetMainKeepLastShrink hP
  · have hle := filledCells_smetMainKeepLastShrink_card_le_erase_diag P
    have hmem : (Fin.last N, Fin.last N) ∈ filledCells P := by
      simp [filledCells, hdiag]
    rw [Finset.card_erase_of_mem hmem] at hle
    omega

lemma filledCells_smetMainKeepLastShrink_card_le_erase_newSymbol {N : ℕ}
    (P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1)))
    {d : Fin (N + 1)}
    (hmain : MainDiagonalNewSymbol P d (Fin.last N)) :
    (filledCells (smetMainKeepLastShrink P)).card ≤
      ((filledCells P).erase (d, d)).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun ij : Fin N × Fin N =>
      ((Fin.castSucc ij.1 : Fin (N + 1)), Fin.rev (Fin.castSucc ij.2))) ?_ ?_
  · intro ij hij
    have hs : (smetMainKeepLastShrink P ij.1 ij.2).isSome := by
      simpa [filledCells] using hij
    cases hcell : smetMainKeepLastShrink P ij.1 ij.2 with
    | none =>
        simp [hcell] at hs
    | some a =>
        have hP := (smetMainKeepLastShrink_eq_some_iff P ij.1 ij.2 a).mp hcell
        have hne : ((Fin.castSucc ij.1 : Fin (N + 1)), Fin.rev (Fin.castSucc ij.2)) ≠
            (d, d) := by
          intro hp
          have hrow : (Fin.castSucc ij.1 : Fin (N + 1)) = d :=
            congrArg Prod.fst hp
          have hcol : Fin.rev (Fin.castSucc ij.2 : Fin (N + 1)) = d :=
            congrArg Prod.snd hp
          have hPdiag : P d d = some (Fin.castSucc a) := by
            simpa [hrow, hcol] using hP
          have hlast : Fin.castSucc a = Fin.last N := by
            exact Option.some.inj (by rw [← hPdiag, hmain.1])
          exact fin_castSucc_ne_last a hlast
        simp [filledCells, hP, hne]
  · intro x hx y hy hxy
    have hrow : x.1 = y.1 :=
      Fin.castSucc_inj.mp (congrArg Prod.fst hxy)
    have hcol_rev : Fin.rev (Fin.castSucc x.2) = Fin.rev (Fin.castSucc y.2) :=
      congrArg Prod.snd hxy
    have hcol_cast : Fin.castSucc x.2 = Fin.castSucc y.2 :=
      Fin.revPerm.injective hcol_rev
    exact Prod.ext hrow (Fin.castSucc_inj.mp hcol_cast)

theorem smetMainKeepLastShrink_step_of_mainDiagonalNewSymbol {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (hP : IsPartialLatin P) {d : Fin (N + 1)}
    (hmain : MainDiagonalNewSymbol P d (Fin.last N))
    (hcard : (filledCells P).card ≤ N) :
    IsPartialLatin (smetMainKeepLastShrink P) ∧
      (filledCells (smetMainKeepLastShrink P)).card ≤ N - 1 := by
  constructor
  · exact isPartialLatin_smetMainKeepLastShrink hP
  · have hle := filledCells_smetMainKeepLastShrink_card_le_erase_newSymbol P hmain
    have hmem : (d, d) ∈ filledCells P := by
      simp [filledCells, hmain.1]
    have hpos : 0 < (filledCells P).card := Finset.card_pos.mpr ⟨(d, d), hmem⟩
    rw [Finset.card_erase_of_mem hmem] at hle
    omega

private lemma fin_ne_last_iff_val_lt {N : ℕ} {a : Fin (N + 1)} :
    a ≠ Fin.last N ↔ a.val < N := by
  constructor
  · intro h
    have hle : a.val ≤ N := Nat.lt_succ_iff.mp a.isLt
    by_contra hlt
    have hge : N ≤ a.val := Nat.le_of_not_gt hlt
    exact h (Fin.ext (le_antisymm hle hge))
  · intro hlt h
    have hv : a.val = N := by simpa [Fin.last] using congrArg Fin.val h
    omega

lemma smetMainPartial_extends_of_keepLastShrink_completion {N : ℕ}
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    {L₀ : Fin N → Fin N → Fin N}
    (hL₀ : Completes (smetMainKeepLastShrink P) L₀)
    {d : Fin (N + 1)}
    (hnorm : SmetaniukTriangularNormalized P d (Fin.last N)) :
    ExtendsPartial P (smetMainPartial L₀) := by
  intro i j a hcell
  rcases hnorm with ⟨hmain, htri⟩
  by_cases haLast : a = Fin.last N
  · subst a
    have hij := mainDiagonalNewSymbol_cell_eq hmain hcell
    rcases hij with ⟨hi, hj⟩
    subst i
    subst j
    exact smetMainPartial_diagonal L₀ d
  · have hlt : i < j := htri i j a hcell haLast
    have hi_ltN : i.val < N := by
      have hj_le : j.val ≤ N := Nat.lt_succ_iff.mp j.isLt
      have hltVal : i.val < j.val := hlt
      omega
    have hj_pos : 0 < j.val := by
      have hltVal : i.val < j.val := hlt
      omega
    have ha_ltN : a.val < N := (fin_ne_last_iff_val_lt.mp haLast)
    let ii : Fin N := ⟨i.val, hi_ltN⟩
    let kk : Fin N := ⟨N - j.val, by omega⟩
    let aa : Fin N := ⟨a.val, ha_ltN⟩
    have hi_cast : (Fin.castSucc ii : Fin (N + 1)) = i := by
      exact Fin.ext rfl
    have ha_cast : (Fin.castSucc aa : Fin (N + 1)) = a := by
      exact Fin.ext rfl
    have hj_repr : Fin.rev (Fin.castSucc kk : Fin (N + 1)) = j := by
      apply Fin.ext
      simp [Fin.rev, kk]
      have hj_le : j.val ≤ N := Nat.lt_succ_iff.mp j.isLt
      omega
    have hsmall :
        smetMainKeepLastShrink P ii kk = some aa := by
      apply (smetMainKeepLastShrink_eq_some_iff P ii kk aa).mpr
      simpa [hi_cast, hj_repr, ha_cast] using hcell
    have hLcell : L₀ ii kk = aa := hL₀.2 ii kk aa hsmall
    have hrev_j : Fin.rev j = (Fin.castSucc kk : Fin (N + 1)) := by
      rw [← hj_repr]
      simp
    have hback_lt : i.val + (Fin.rev j).val < N := by
      have hrev_val : (Fin.rev j).val = N - j.val := by simp [Fin.rev]
      have hltVal : i.val < j.val := hlt
      rw [hrev_val]
      omega
    have hback_ne : i.val + (Fin.rev j).val ≠ N := by omega
    have hii : (⟨i.val, by omega⟩ : Fin N) = ii := by
      exact Fin.ext rfl
    have hsum_lt : i.val + kk.val < N := by
      simpa [hrev_j] using hback_lt
    have hsum_ne : i.val + kk.val ≠ N := by omega
    simp [smetMainPartial, smetBackPartial, hsum_ne, hsum_lt, hLcell,
      hrev_j, hii, ha_cast]

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

theorem shiftedCompletable_of_properSeed {N : ℕ} (hN : 3 ≤ N)
    {Q : Fin N → Fin N → Option (Fin N)}
    {L₀ : Fin N → Fin N → Fin N}
    (hL₀ : IsLatinSquare L₀) (hweak : WeakUpperTriangle Q)
    (hQ : ∀ i j a, Q i j = some a → L₀ i j = a) :
    ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
      ShiftedCompletes Q L := by
  obtain ⟨L, hL⟩ :=
    smetMainPartial_completable_of_core hN
      (isLatinSquare_reverseSeedColumns hL₀)
  exact ⟨L, shiftedCompletes_of_smetMainPartial_reverseSeedColumns hweak hQ hL⟩

theorem shiftedCompletable_of_no_improperSeed {N : ℕ} (hN : 3 ≤ N)
    {Q : Fin N → Fin N → Option (Fin N)}
    {Lstar : Fin N → Fin N → SignedCell (Fin N)}
    (hweak : WeakUpperTriangle Q)
    (hLstar : ImproperLatinSquare Lstar)
    (hExt : ImproperlyExtends Q Lstar)
    (hno : signedImproperCells Lstar = ∅) :
    ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
      ShiftedCompletes Q L := by
  let L₀ : Fin N → Fin N → Fin N := signedPrincipalSquare Lstar
  have hL₀ : IsLatinSquare L₀ := by
    dsimp [L₀]
    exact isLatinSquare_signedPrincipalSquare_of_no_improper hLstar hno
  have hcomp : Completes Q L₀ := by
    dsimp [L₀]
    exact completes_signedPrincipalSquare_of_no_improper
      (isLatinSquare_signedPrincipalSquare_of_no_improper hLstar hno) hExt hno
  exact shiftedCompletable_of_properSeed hN hL₀ hweak hcomp.2

theorem smetaniuk_normalized_of_IH {N : ℕ} (hN : 3 ≤ N)
    (hIH : LatinSquareCompletionTheorem N)
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    {d : Fin (N + 1)}
    (hP : IsPartialLatin P)
    (hcard : (filledCells P).card ≤ N)
    (hnorm : SmetaniukTriangularNormalized P d (Fin.last N)) :
    ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1), Completes P L := by
  have hstep :=
    smetMainKeepLastShrink_step_of_mainDiagonalNewSymbol hP hnorm.1 hcard
  obtain ⟨L₀, hL₀⟩ := hIH (smetMainKeepLastShrink P) hstep.1 hstep.2
  obtain ⟨L, hL⟩ := smetMainPartial_completable_of_core hN hL₀.1
  exact ⟨L, completes_of_extendsPartial
    (smetMainPartial_extends_of_keepLastShrink_completion hL₀ hnorm) hL⟩

theorem smetaniuk_exact_normalized_of_IH {N : ℕ} (hN : 3 ≤ N)
    (hIH : LatinSquareCompletionTheorem N)
    {P : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1))}
    (hP : IsPartialLatin P)
    (hcard : (filledCells P).card = N)
    (hnorm : SmetaniukTriangularNormalized P (Fin.last N) (Fin.last N)) :
    ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1), Completes P L := by
  exact smetaniuk_normalized_of_IH hN hIH hP (by omega) hnorm

def ryser_few_elements_completes (n : ℕ) : Prop :=
  ∀ P : Fin n → Fin n → Option (Fin n),
    IsPartialLatin P → (filledCells P).card ≤ n - 1 →
      2 * (usedSymbols P).card ≤ n →
        ∃ L : Fin n → Fin n → Fin n, Completes P L

theorem latinSquareCompletion_step_of_ryser {N : ℕ} (hN : 3 ≤ N)
    (hIH : LatinSquareCompletionTheorem N)
    (hR : ryser_few_elements_completes (N + 1)) :
    LatinSquareCompletionTheorem (N + 1) := by
  classical
  intro P hP hcard
  by_cases hfew : 2 * (usedSymbols P).card ≤ N + 1
  · exact hR P hP hcard hfew
  · have hmany : N + 1 < 2 * (usedSymbols P).card :=
      Nat.lt_of_not_ge hfew
    obtain ⟨a, hone⟩ :=
      exists_symbol_occursExactlyOnce_of_many_used P hcard hmany
    have hcardN : (filledCells P).card ≤ N := by
      simpa using hcard
    obtain ⟨rowPerm, colPerm, symPerm, d, hnorm⟩ :=
      exists_relabel_singleton_smetaniukTriangularNormalized
        (P := P) (a := a) hcardN hone
    let P' : Fin (N + 1) → Fin (N + 1) → Option (Fin (N + 1)) :=
      relabelPartial rowPerm colPerm symPerm P
    have hP' : IsPartialLatin P' := by
      dsimp [P']
      exact isPartialLatin_relabelPartial rowPerm colPerm symPerm hP
    have hcard' : (filledCells P').card ≤ N := by
      dsimp [P']
      rw [filledCells_relabelPartial_card]
      exact hcardN
    obtain ⟨L', hL'⟩ :=
      smetaniuk_normalized_of_IH hN hIH hP' hcard' hnorm
    exact (completion_exists_relabelPartial_iff rowPerm colPerm symPerm P).mp
      ⟨L', hL'⟩

theorem chapter33_unconditional_of_ryser
    (hR : ∀ n : ℕ, ryser_few_elements_completes n) :
    ∀ n : ℕ, LatinSquareCompletionTheorem n := by
  intro n
  induction n with
  | zero =>
      exact chapter33_order_le_three 0 (by omega)
  | succ N ih =>
      by_cases hsmall : N + 1 ≤ 3
      · exact chapter33_order_le_three (N + 1) hsmall
      · have hN : 3 ≤ N := by omega
        exact latinSquareCompletion_step_of_ryser hN ih (hR (N + 1))

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
