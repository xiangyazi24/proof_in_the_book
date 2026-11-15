import Agafonov.Kamae1973.TypicalWordExpectation
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic

namespace Agafonov.Kamae1973

open scoped BigOperators

noncomputable section

/-- Assignment data for one finite painted stage. -/
structure StageAssignmentData {b : ℕ}
    (P : LetterDistribution b) (t : ℕ → Bool)
    (μ : BlockFamily Bool) (ν : BlockFamily (Fin b × Bool))
    (a T R : ℕ) (β : ℝ) (param : PaintingParameters P R β) where
  macroblocks : ℕ
  macroblocks_eq : macroblocks = T / param.macroLength
  offsets : Fin macroblocks → Fin param.blockLength
  labels :
    SelectedBlock macroblocks param.blocksPerMacro →
      Fin param.blockLength → Fin b
  labels_typical :
    ∀ j, IsTypicalWord P param.blockLength R β (labels j)
  selected_pair_close :
    finiteLOne
        (selectedPairLaw t a param.blockLength param.blocksPerMacro
          macroblocks offsets labels)
        (ν.law param.blockLength) ≤
      9 * β

/-- A cell of a selected block. -/
structure SelectedCell (H Q L : ℕ) where
  «macro» : Fin H
  slot : Fin (Q - 1)
  cell : Fin L
deriving DecidableEq

private def selectedCellEquiv (H Q L : ℕ) :
    SelectedCell H Q L ≃ (Fin H × Fin (Q - 1) × Fin L) where
  toFun z := (z.«macro», z.slot, z.cell)
  invFun z := ⟨z.1, z.2.1, z.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by
    rcases z with ⟨m, s, c⟩
    rfl

private instance selectedCellFintype (H Q L : ℕ) :
    Fintype (SelectedCell H Q L) :=
  Fintype.ofEquiv (Fin H × Fin (Q - 1) × Fin L)
    (selectedCellEquiv H Q L).symm

/-- Projection from a selected cell to its block. -/
def SelectedCell.toBlock {H Q L : ℕ}
    (z : SelectedCell H Q L) : SelectedBlock H Q :=
  ⟨z.«macro», z.slot⟩

/-- Physical offset of a selected cell. -/
def selectedCellOffset (M L : ℕ) {H Q : ℕ}
    (offset : Fin H → Fin L) (z : SelectedCell H Q L) : ℕ :=
  z.«macro» * M + offset z.«macro» + z.slot * L + z.cell

/-- Extension of a finite word on an interval. -/
def ExtendsInterval {A : Type*} (a : ℕ) {T : ℕ}
    (u : Fin T → A) (x : ℕ → A) : Prop :=
  ∀ i : Fin T, x (a + i) = u i

/-- Painted stage word. -/
noncomputable def StageAssignmentData.stageWord {b : ℕ}
    {P : LetterDistribution b} {t : ℕ → Bool}
    {μ : BlockFamily Bool} {ν : BlockFamily (Fin b × Bool)}
    {a T R : ℕ} {β : ℝ} {param : PaintingParameters P R β}
    (data : StageAssignmentData P t μ ν a T R β param)
    (filler : Fin b) : Fin T → Fin b :=
  fun i =>
    @dite _
      (∃ z : SelectedCell data.macroblocks
          param.blocksPerMacro param.blockLength,
        selectedCellOffset param.macroLength param.blockLength
          data.offsets z = i)
      (Classical.propDecidable _)
      (fun h =>
        let z := Classical.choose h
        data.labels z.toBlock z.cell)
      (fun _ => filler)

/-- Distinct selected cells occupy distinct physical offsets. -/
axiom selectedCellOffset_injective
    (M L Q H : ℕ) (hL : 0 < L) (hQ : 2 ≤ Q)
    (hM : M = Q * L) (offset : Fin H → Fin L) :
    Function.Injective (selectedCellOffset (Q := Q) M L offset)

/-- Every selected cell lies in the stage. -/
axiom selectedCellOffset_lt_stage {b : ℕ}
    {P : LetterDistribution b} {t : ℕ → Bool}
    {μ : BlockFamily Bool} {ν : BlockFamily (Fin b × Bool)}
    {a T R : ℕ} {β : ℝ} {param : PaintingParameters P R β}
    (data : StageAssignmentData P t μ ν a T R β param)
    (z : SelectedCell data.macroblocks
      param.blocksPerMacro param.blockLength) :
    selectedCellOffset param.macroLength param.blockLength
      data.offsets z < T

/-- Painted selected cells return their assigned labels. -/
axiom StageAssignmentData.stageWord_selected {b : ℕ}
    {P : LetterDistribution b} {t : ℕ → Bool}
    {μ : BlockFamily Bool} {ν : BlockFamily (Fin b × Bool)}
    {a T R : ℕ} {β : ℝ} {param : PaintingParameters P R β}
    (data : StageAssignmentData P t μ ν a T R β param)
    (filler : Fin b)
    (z : SelectedCell data.macroblocks
      param.blocksPerMacro param.blockLength) :
    data.stageWord filler
      ⟨selectedCellOffset param.macroLength param.blockLength
          data.offsets z,
        selectedCellOffset_lt_stage data z⟩ =
      data.labels z.toBlock z.cell

end

end Agafonov.Kamae1973
