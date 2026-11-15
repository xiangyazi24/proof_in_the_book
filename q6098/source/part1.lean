import Agafonov.Kamae1973.StagePaint
import Agafonov.Kamae1973.TypicalWordExpectation
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform prefix estimates inside a painted stage

Complete macroblocks contribute typical selected blocks.  Their internal word
counts are reindexed as physical starts of the painted stage, while the
uncovered macroblock fraction, the incomplete final macroblock, and block-edge
starts are bounded separately.  This is the uniform-prefix estimate in Kamae
(1973), Theorem 3, p. 139.
-/

namespace Agafonov.Kamae1973

open scoped BigOperators

noncomputable section

private theorem card_filter_range_eq_countP (p : ℕ → Bool) (N : ℕ) :
    ((Finset.range N).filter fun i => p i = true).card =
      (List.range N).countP p := by
  induction N with
  | zero => simp
  | succ N ih =>
      cases hp : p N <;>
        simp [Finset.range_add_one, Finset.filter_insert,
          List.range_succ, ih, hp]

private def stageHit {b r : ℕ} (x : ℕ → Fin b) (a : ℕ)
    (w : Fin r → Fin b) (i : ℕ) : Prop :=
  prefixList (fun j => x (a + (i + j))) r = List.ofFn w

private theorem intervalWordCount_eq_filter_card
    {b r : ℕ} (x : ℕ → Fin b) (a s : ℕ) (w : Fin r → Fin b) :
    intervalWordCount x a s (List.ofFn w) =
      ((Finset.range s).filter (stageHit x a w)).card := by
  unfold intervalWordCount wordCount
  rw [← card_filter_range_eq_countP]
  apply congrArg Finset.card
  ext i
  simp [stageHit, Nat.add_assoc]

private theorem filtered_card_bounds_real
    {α : Type*} [DecidableEq α]
    (small large : Finset α) (hsub : small ⊆ large)
    (p : α → Prop) [DecidablePred p] :
    (((small.filter p).card : ℕ) : ℝ) ≤
        (((large.filter p).card : ℕ) : ℝ) ∧
      (((large.filter p).card : ℕ) : ℝ) ≤
        (((small.filter p).card : ℕ) : ℝ) +
          (((large.card - small.card : ℕ) : ℕ) : ℝ) := by
  classical
  have hfilter : small.filter p ⊆ large.filter p := by
    intro i hi
    have hiData := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hsub hiData.1, hiData.2⟩
  have hcover :
      large.filter p ⊆ small.filter p ∪ (large \ small) := by
    intro i hi
    have hiData := Finset.mem_filter.mp hi
    by_cases hismall : i ∈ small
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hismall, hiData.2⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hiData.1, hismall⟩)
  have hlowerNat : (small.filter p).card ≤ (large.filter p).card :=
    Finset.card_le_card hfilter
  have hupperNat :
      (large.filter p).card ≤
        (small.filter p).card + (large.card - small.card) := by
    calc
      (large.filter p).card ≤
          (small.filter p ∪ (large \ small)).card :=
        Finset.card_le_card hcover
      _ ≤ (small.filter p).card + (large \ small).card :=
        Finset.card_union_le _ _
      _ = (small.filter p).card + (large.card - small.card) := by
        rw [Finset.card_sdiff_of_subset hsub]
  exact ⟨Nat.cast_le.mpr hlowerNat, Nat.cast_le.mpr hupperNat⟩

private theorem ofFn_drop_take_eq_window
    {A : Type*} {L r : ℕ} (u : Fin L → A)
    (j : Fin (L + 1 - r)) :
    ((List.ofFn u).drop j.val).take r =
      List.ofFn (fun k : Fin r =>
        u ⟨j.val + k.val, by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro n hnLeft hnRight
    simp [List.getElem_take, List.getElem_drop]

private abbrev PrefixBlockIndex (K Q : ℕ) :=
  Fin K × Fin (Q - 1)

private abbrev PrefixInternalIndex (K Q L r : ℕ) :=
  PrefixBlockIndex K Q × Fin (L + 1 - r)

private def prefixMacroLift {K H : ℕ}
    (hKH : K ≤ H) (m : Fin K) : Fin H :=
  ⟨m.val, lt_of_lt_of_le m.isLt hKH⟩

private def prefixBlockLift {K H Q : ℕ}
    (hKH : K ≤ H) (j : PrefixBlockIndex K Q) : SelectedBlock H Q :=
  ⟨prefixMacroLift hKH j.1, j.2⟩

private def prefixInternalCell {K H Q L r : ℕ}
    (hKH : K ≤ H) (hr : 1 ≤ r)
    (z : PrefixInternalIndex K Q L r) : SelectedCell H Q L :=
  ⟨prefixMacroLift hKH z.1.1, z.1.2,
    ⟨z.2.val, by
      have hz := z.2.isLt
      omega⟩⟩

private def prefixShiftCell {K H Q L r : ℕ}
    (hKH : K ≤ H) (z : PrefixInternalIndex K Q L r)
    (k : Fin r) : SelectedCell H Q L :=
  ⟨prefixMacroLift hKH z.1.1, z.1.2,
    ⟨z.2.val + k.val, by
      have hz := z.2.isLt
      have hk := k.isLt
      omega⟩⟩

private def prefixInternalOffset
    (M L : ℕ) {K H Q r : ℕ}
    (offset : Fin H → Fin L) (hKH : K ≤ H) (hr : 1 ≤ r)
    (z : PrefixInternalIndex K Q L r) : ℕ :=
  selectedCellOffset M L offset (prefixInternalCell hKH hr z)

private def prefixInternalHit
    {b K H Q L r : ℕ}
    (label : SelectedBlock H Q → Fin L → Fin b)
    (hKH : K ≤ H) (w : Fin r → Fin b)
    (z : PrefixInternalIndex K Q L r) : Prop :=
  ((List.ofFn (label (prefixBlockLift hKH z.1))).drop z.2.val).take r =
    List.ofFn w

private def prefixInternalStartSet
    (M L : ℕ) {K H Q r : ℕ}
    (offset : Fin H → Fin L) (hKH : K ≤ H) (hr : 1 ≤ r) :
    Finset ℕ :=
  (Finset.univ : Finset (PrefixInternalIndex K Q L r)).image
    (prefixInternalOffset M L offset hKH hr)

private theorem prefixInternalCell_injective
    {K H Q L r : ℕ} (hKH : K ≤ H) (hr : 1 ≤ r)
    {z z' : PrefixInternalIndex K Q L r}
    (h : prefixInternalCell hKH hr z = prefixInternalCell hKH hr z') :
    z = z' := by
  apply Prod.ext
  · apply Prod.ext
    · apply Fin.ext
      simpa [prefixInternalCell, prefixMacroLift] using
        congrArg (fun c : SelectedCell H Q L => c.«macro».val) h
    · apply Fin.ext
      simpa [prefixInternalCell] using
        congrArg (fun c : SelectedCell H Q L => c.slot.val) h
  · apply Fin.ext
    simpa [prefixInternalCell] using
      congrArg (fun c : SelectedCell H Q L => c.cell.val) h

private theorem prefixInternalOffset_injective
    (M L Q K H r : ℕ) (hL : 0 < L) (hQ : 2 ≤ Q)
    (hM : M = Q * L) (offset : Fin H → Fin L)
    (hKH : K ≤ H) (hr : 1 ≤ r) :
    Function.Injective
      (prefixInternalOffset M L offset hKH hr :
        PrefixInternalIndex K Q L r → ℕ) := by
  intro z z' h
  apply prefixInternalCell_injective hKH hr
  exact selectedCellOffset_injective M L Q H hL hQ hM offset h

private theorem prefixShiftCell_offset
    (M L : ℕ) {K H Q r : ℕ}
    (offset : Fin H → Fin L) (hKH : K ≤ H) (hr : 1 ≤ r)
    (z : PrefixInternalIndex K Q L r) (k : Fin r) :
    selectedCellOffset M L offset (prefixShiftCell hKH z k) =
      prefixInternalOffset M L offset hKH hr z + k.val := by
  simp [prefixShiftCell, prefixInternalOffset, prefixInternalCell,
    selectedCellOffset, prefixMacroLift, Nat.add_assoc]

@[simp] private theorem prefixShiftCell_toBlock
    {K H Q L r : ℕ} (hKH : K ≤ H)
    (z : PrefixInternalIndex K Q L r) (k : Fin r) :
    (prefixShiftCell hKH z k).toBlock = prefixBlockLift hKH z.1 := by
  rfl

private theorem selectedCellRemainder_lt_for_prefix
    (L Q H : ℕ) (hQ : 2 ≤ Q)
    (offset : Fin H → Fin L) (z : SelectedCell H Q L) :
    (offset z.«macro» : ℕ) + (z.slot : ℕ) * L + (z.cell : ℕ) <
      Q * L := by
  have hslotCell :
      (z.slot : ℕ) * L + (z.cell : ℕ) < (Q - 1) * L := by
    calc
      (z.slot : ℕ) * L + (z.cell : ℕ) <
          (z.slot : ℕ) * L + L :=
        Nat.add_lt_add_left z.cell.isLt _
      _ = ((z.slot : ℕ) + 1) * L := by
        rw [Nat.add_mul, one_mul]
      _ ≤ (Q - 1) * L :=
        Nat.mul_le_mul_right L (Nat.succ_le_of_lt z.slot.isLt)
  calc
    (offset z.«macro» : ℕ) + (z.slot : ℕ) * L + (z.cell : ℕ) =
        (offset z.«macro» : ℕ) +
          ((z.slot : ℕ) * L + (z.cell : ℕ)) :=
      Nat.add_assoc _ _ _
    _ < L + ((z.slot : ℕ) * L + (z.cell : ℕ)) :=
      Nat.add_lt_add_right (offset z.«macro»).isLt _
    _ < L + (Q - 1) * L :=
      Nat.add_lt_add_left hslotCell _
    _ = (1 + (Q - 1)) * L := by
      rw [Nat.add_mul, one_mul]
