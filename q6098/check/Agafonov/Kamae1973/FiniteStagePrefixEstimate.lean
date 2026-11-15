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

private instance stageHitDecidable {b r : ℕ}
    (x : ℕ → Fin b) (a : ℕ) (w : Fin r → Fin b) :
    DecidablePred (stageHit x a w) := by
  intro i
  unfold stageHit
  exact Classical.propDecidable _

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
  constructor
  · exact Nat.cast_le.mpr hlowerNat
  · rw [← Nat.cast_add]
    exact Nat.cast_le.mpr hupperNat

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

private instance prefixInternalHitDecidable
    {b K H Q L r : ℕ}
    (label : SelectedBlock H Q → Fin L → Fin b)
    (hKH : K ≤ H) (w : Fin r → Fin b) :
    DecidablePred (prefixInternalHit label hKH w) := by
  intro z
  unfold prefixInternalHit
  exact Classical.propDecidable _

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

private theorem finApply_eq_of_val_eq
    {A : Type*} {n i j : ℕ} (f : Fin n → A)
    (hi : i < n) (hj : j < n) (hij : i = j) :
    f ⟨i, hi⟩ = f ⟨j, hj⟩ := by
  apply congrArg f
  apply Fin.ext
  exact hij

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
    _ = Q * L := by
      have hQsub : 1 + (Q - 1) = Q := by omega
      rw [hQsub]

private theorem selectedCellOffset_lt_completePrefix
    (M L Q H K s : ℕ) (hQ : 2 ≤ Q) (hM : M = Q * L)
    (offset : Fin H → Fin L) (z : SelectedCell H Q L)
    (hzK : (z.«macro» : ℕ) < K) (hKM : K * M ≤ s) :
    selectedCellOffset M L offset z < s := by
  have hrem :
      (offset z.«macro» : ℕ) + (z.slot : ℕ) * L + (z.cell : ℕ) < M := by
    rw [hM]
    exact selectedCellRemainder_lt_for_prefix L Q H hQ offset z
  calc
    selectedCellOffset M L offset z =
        (z.«macro» : ℕ) * M +
          ((offset z.«macro» : ℕ) + (z.slot : ℕ) * L +
            (z.cell : ℕ)) := by
      simp [selectedCellOffset, Nat.add_assoc]
    _ < (z.«macro» : ℕ) * M + M :=
      Nat.add_lt_add_left hrem _
    _ = ((z.«macro» : ℕ) + 1) * M := by
      rw [Nat.add_mul, one_mul]
    _ ≤ K * M :=
      Nat.mul_le_mul_right M (Nat.succ_le_of_lt hzK)
    _ ≤ s := hKM

private theorem prefixInternalStartSet_subset_range
    (M L Q K H r s : ℕ) (hQ : 2 ≤ Q) (hM : M = Q * L)
    (offset : Fin H → Fin L) (hKH : K ≤ H) (hr : 1 ≤ r)
    (hKM : K * M ≤ s) :
    prefixInternalStartSet (Q := Q) M L offset hKH hr ⊆ Finset.range s := by
  classical
  intro i hi
  rcases Finset.mem_image.mp hi with ⟨z, _hz, rfl⟩
  apply Finset.mem_range.mpr
  apply selectedCellOffset_lt_completePrefix M L Q H K s
    hQ hM offset (prefixInternalCell hKH hr z)
  · simpa [prefixInternalCell, prefixMacroLift] using z.1.1.isLt
  · exact hKM

private theorem prefixInternalStartSet_card
    (M L Q K H r : ℕ) (hL : 0 < L) (hQ : 2 ≤ Q)
    (hM : M = Q * L) (offset : Fin H → Fin L)
    (hKH : K ≤ H) (hr : 1 ≤ r) :
    (prefixInternalStartSet (Q := Q) M L offset hKH hr).card =
      K * (Q - 1) * (L + 1 - r) := by
  classical
  unfold prefixInternalStartSet
  rw [Finset.card_image_of_injective _
    (prefixInternalOffset_injective M L Q K H r
      hL hQ hM offset hKH hr)]
  simp [PrefixInternalIndex, PrefixBlockIndex, Nat.mul_assoc]

private theorem stage_window_eq_label_slice
    {b : ℕ}
    {P : LetterDistribution b} {t : ℕ → Bool}
    {μ : BlockFamily Bool} {ν : BlockFamily (Fin b × Bool)}
    {a T R : ℕ} {β : ℝ} {param : PaintingParameters P R β}
    (data : StageAssignmentData P t μ ν a T R β param)
    (filler : Fin b) (x : ℕ → Fin b)
    (hx : ExtendsInterval a (data.stageWord filler) x)
    {K r : ℕ} (hKH : K ≤ data.macroblocks) (hr : 1 ≤ r)
    (z : PrefixInternalIndex K param.blocksPerMacro
      param.blockLength r) :
    prefixList
        (fun n => x (a +
          (prefixInternalOffset param.macroLength param.blockLength
            data.offsets hKH hr z + n))) r =
      ((List.ofFn (data.labels (prefixBlockLift hKH z.1))).drop z.2.val).take r := by
  have hpoint (k : Fin r) :
      x (a +
          (prefixInternalOffset param.macroLength param.blockLength
            data.offsets hKH hr z + k.val)) =
        data.labels (prefixBlockLift hKH z.1)
          ⟨z.2.val + k.val, by
            have hz := z.2.isLt
            have hk := k.isLt
            omega⟩ := by
    have hsumlt :
        prefixInternalOffset param.macroLength param.blockLength
            data.offsets hKH hr z + k.val < T := by
      rw [← prefixShiftCell_offset param.macroLength param.blockLength
        data.offsets hKH hr z k]
      exact selectedCellOffset_lt_stage data (prefixShiftCell hKH z k)
    have hpainted :
        data.stageWord filler
            ⟨prefixInternalOffset param.macroLength param.blockLength
                data.offsets hKH hr z + k.val, hsumlt⟩ =
          data.labels (prefixShiftCell hKH z k).toBlock
            (prefixShiftCell hKH z k).cell := by
      calc
        data.stageWord filler
            ⟨prefixInternalOffset param.macroLength param.blockLength
                data.offsets hKH hr z + k.val, hsumlt⟩ =
          data.stageWord filler
            ⟨selectedCellOffset param.macroLength param.blockLength
                data.offsets (prefixShiftCell hKH z k),
              selectedCellOffset_lt_stage data (prefixShiftCell hKH z k)⟩ := by
            exact finApply_eq_of_val_eq (data.stageWord filler) hsumlt
              (selectedCellOffset_lt_stage data (prefixShiftCell hKH z k))
              (prefixShiftCell_offset param.macroLength param.blockLength
                data.offsets hKH hr z k).symm
        _ = data.labels (prefixShiftCell hKH z k).toBlock
              (prefixShiftCell hKH z k).cell :=
          data.stageWord_selected filler (prefixShiftCell hKH z k)
    have hstage :=
      (hx ⟨prefixInternalOffset param.macroLength param.blockLength
        data.offsets hKH hr z + k.val, hsumlt⟩).trans hpainted
    simpa [prefixShiftCell, prefixBlockLift, prefixMacroLift,
      SelectedCell.toBlock] using hstage
  calc
    prefixList
        (fun n => x (a +
          (prefixInternalOffset param.macroLength param.blockLength
            data.offsets hKH hr z + n))) r =
      List.ofFn (fun k : Fin r =>
        data.labels (prefixBlockLift hKH z.1)
          ⟨z.2.val + k.val, by
            have hz := z.2.isLt
            have hk := k.isLt
            omega⟩) := by
        unfold prefixList
        apply congrArg List.ofFn
        funext k
        exact hpoint k
    _ = ((List.ofFn
          (data.labels (prefixBlockLift hKH z.1))).drop z.2.val).take r := by
      symm
      simpa using
        (ofFn_drop_take_eq_window
          (data.labels (prefixBlockLift hKH z.1)) z.2)

private theorem prefixInternalHit_iff_stageHit
    {b : ℕ}
    {P : LetterDistribution b} {t : ℕ → Bool}
    {μ : BlockFamily Bool} {ν : BlockFamily (Fin b × Bool)}
    {a T R : ℕ} {β : ℝ} {param : PaintingParameters P R β}
    (data : StageAssignmentData P t μ ν a T R β param)
    (filler : Fin b) (x : ℕ → Fin b)
    (hx : ExtendsInterval a (data.stageWord filler) x)
    {K r : ℕ} (hKH : K ≤ data.macroblocks) (hr : 1 ≤ r)
    (w : Fin r → Fin b)
    (z : PrefixInternalIndex K param.blocksPerMacro
      param.blockLength r) :
    stageHit x a w
        (prefixInternalOffset param.macroLength param.blockLength
          data.offsets hKH hr z) ↔
      prefixInternalHit data.labels hKH w z := by
  unfold stageHit prefixInternalHit
  rw [stage_window_eq_label_slice data filler x hx hKH hr z]

private theorem internalOccurrenceCount_cast_sum_private
    {b L r : ℕ} (u : Fin L → Fin b) (w : Fin r → Fin b) :
    (internalOccurrenceCount u w : ℝ) =
      ∑ j : Fin (L + 1 - r),
        if ((List.ofFn u).drop j.val).take r = List.ofFn w
        then (1 : ℝ) else 0 := by
  classical
  unfold internalOccurrenceCount
  calc
    (((Finset.univ : Finset (Fin (L + 1 - r))).filter fun j =>
        ((List.ofFn u).drop j.val).take r = List.ofFn w).card : ℝ) =
      ∑ j ∈ ((Finset.univ : Finset (Fin (L + 1 - r))).filter fun j =>
        ((List.ofFn u).drop j.val).take r = List.ofFn w),
        (1 : ℝ) := by simp
    _ = ∑ j : Fin (L + 1 - r),
        if ((List.ofFn u).drop j.val).take r = List.ofFn w
        then (1 : ℝ) else 0 := by
      rw [Finset.sum_filter]

private theorem prefixInternalHitSet_cast_card_eq_sum
    {b K H Q L r : ℕ}
    (label : SelectedBlock H Q → Fin L → Fin b)
    (hKH : K ≤ H) (w : Fin r → Fin b) :
    ((((Finset.univ : Finset (PrefixInternalIndex K Q L r)).filter
      (prefixInternalHit label hKH w)).card : ℕ) : ℝ) =
      ∑ j : PrefixBlockIndex K Q,
        (internalOccurrenceCount (label (prefixBlockLift hKH j)) w : ℝ) := by
  classical
  calc
    ((((Finset.univ : Finset (PrefixInternalIndex K Q L r)).filter
        (prefixInternalHit label hKH w)).card : ℕ) : ℝ) =
      ∑ z ∈ ((Finset.univ : Finset (PrefixInternalIndex K Q L r)).filter
        (prefixInternalHit label hKH w)), (1 : ℝ) := by simp
    _ = ∑ z : PrefixInternalIndex K Q L r,
        if prefixInternalHit label hKH w z then (1 : ℝ) else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ j : PrefixBlockIndex K Q,
        ∑ c : Fin (L + 1 - r),
          if prefixInternalHit label hKH w (j, c)
          then (1 : ℝ) else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ j : PrefixBlockIndex K Q,
        (internalOccurrenceCount (label (prefixBlockLift hKH j)) w : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [internalOccurrenceCount_cast_sum_private]
      rfl

private theorem card_filter_image_of_injective
    {D E : Type*} [Fintype D] [DecidableEq D] [DecidableEq E]
    (f : D → E) (hf : Function.Injective f)
    (p : D → Prop) (q : E → Prop)
    [DecidablePred p] [DecidablePred q]
    (hiff : ∀ d, q (f d) ↔ p d) :
    ((((Finset.univ : Finset D).image f).filter q).card) =
      ((Finset.univ : Finset D).filter p).card := by
  classical
  have hset :
      ((Finset.univ : Finset D).filter p).image f =
        ((Finset.univ : Finset D).image f).filter q := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨d, hd, rfl⟩
      have hdData := Finset.mem_filter.mp hd
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩,
          (hiff d).2 hdData.2⟩
    · intro hy
      have hyData := Finset.mem_filter.mp hy
      rcases Finset.mem_image.mp hyData.1 with ⟨d, _hd, rfl⟩
      exact Finset.mem_image.mpr
        ⟨d, Finset.mem_filter.mpr
          ⟨Finset.mem_univ d, (hiff d).1 hyData.2⟩, rfl⟩
  rw [← hset, Finset.card_image_of_injective _ hf]

private theorem prefixInternalHitCount_eq
    {b : ℕ}
    {P : LetterDistribution b} {t : ℕ → Bool}
    {μ : BlockFamily Bool} {ν : BlockFamily (Fin b × Bool)}
    {a T R : ℕ} {β : ℝ} {param : PaintingParameters P R β}
    (data : StageAssignmentData P t μ ν a T R β param)
    (filler : Fin b) (x : ℕ → Fin b)
    (hx : ExtendsInterval a (data.stageWord filler) x)
    {K r : ℕ} (hKH : K ≤ data.macroblocks) (hr : 1 ≤ r)
    (w : Fin r → Fin b) :
    ((((prefixInternalStartSet param.macroLength param.blockLength
        data.offsets hKH hr).filter (stageHit x a w)).card : ℕ) : ℝ) =
      ∑ j : PrefixBlockIndex K param.blocksPerMacro,
        (internalOccurrenceCount
          (data.labels (prefixBlockLift hKH j)) w : ℝ) := by
  classical
  have hL : 0 < param.blockLength :=
    lt_of_lt_of_le Nat.zero_lt_one param.one_le_blockLength
  have hinj :
      Function.Injective
        (prefixInternalOffset param.macroLength param.blockLength
          data.offsets hKH hr :
          PrefixInternalIndex K param.blocksPerMacro
            param.blockLength r → ℕ) :=
    prefixInternalOffset_injective
      param.macroLength param.blockLength param.blocksPerMacro
      K data.macroblocks r hL param.two_le_blocksPerMacro
      param.macro_eq data.offsets hKH hr
  unfold prefixInternalStartSet
  have hcard :=
    card_filter_image_of_injective
      (prefixInternalOffset param.macroLength param.blockLength
        data.offsets hKH hr) hinj
      (prefixInternalHit data.labels hKH w)
      (stageHit x a w)
      (fun z =>
        prefixInternalHit_iff_stageHit
          data filler x hx hKH hr w z)
  rw [hcard]
  exact prefixInternalHitSet_cast_card_eq_sum data.labels hKH w

private theorem typical_internalOccurrence_abs
    {b L R r : ℕ} (P : LetterDistribution b)
    {β : ℝ} (hL : 0 < L)
    {u : Fin L → Fin b} (hu : IsTypicalWord P L R β u)
    (hr : 1 ≤ r) (hrR : r ≤ R) (w : Fin r → Fin b) :
    |(internalOccurrenceCount u w : ℝ) -
        (L : ℝ) * P.wordMass (List.ofFn w)| ≤
      β * (L : ℝ) := by
  have htyp := hu r hr hrR w
  have hLne : (L : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)
  have hid :
      (internalFrequency u w - P.wordMass (List.ofFn w)) * (L : ℝ) =
        (internalOccurrenceCount u w : ℝ) -
          (L : ℝ) * P.wordMass (List.ofFn w) := by
    unfold internalFrequency
    field_simp [hLne]
    ring
  rw [← hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg L)]
  exact mul_le_mul_of_nonneg_right htyp (Nat.cast_nonneg L)

private theorem prefixTypicalSum_abs
    {b : ℕ}
    {P : LetterDistribution b} {t : ℕ → Bool}
    {μ : BlockFamily Bool} {ν : BlockFamily (Fin b × Bool)}
    {a T R : ℕ} {β : ℝ} {param : PaintingParameters P R β}
    (data : StageAssignmentData P t μ ν a T R β param)
    {K r : ℕ} (hKH : K ≤ data.macroblocks)
    (hr : 1 ≤ r) (hrR : r ≤ R) (w : Fin r → Fin b) :
    |(∑ j : PrefixBlockIndex K param.blocksPerMacro,
        (internalOccurrenceCount
          (data.labels (prefixBlockLift hKH j)) w : ℝ)) -
        ((K * (param.blocksPerMacro - 1) *
          param.blockLength : ℕ) : ℝ) *
          P.wordMass (List.ofFn w)| ≤
      β * ((K * (param.blocksPerMacro - 1) *
        param.blockLength : ℕ) : ℝ) := by
  classical
  have hL : 0 < param.blockLength :=
    lt_of_lt_of_le Nat.zero_lt_one param.one_le_blockLength
  have hterm (j : PrefixBlockIndex K param.blocksPerMacro) :
      |(internalOccurrenceCount
          (data.labels (prefixBlockLift hKH j)) w : ℝ) -
        (param.blockLength : ℝ) * P.wordMass (List.ofFn w)| ≤
      β * (param.blockLength : ℝ) :=
    typical_internalOccurrence_abs P hL
      (data.labels_typical (prefixBlockLift hKH j)) hr hrR w
  have hconst :
      (∑ _j : PrefixBlockIndex K param.blocksPerMacro,
        (param.blockLength : ℝ) * P.wordMass (List.ofFn w)) =
      ((K * (param.blocksPerMacro - 1) *
        param.blockLength : ℕ) : ℝ) * P.wordMass (List.ofFn w) := by
    simp [PrefixBlockIndex, Nat.cast_mul]
    ring
  have hrewrite :
      (∑ j : PrefixBlockIndex K param.blocksPerMacro,
          (internalOccurrenceCount
            (data.labels (prefixBlockLift hKH j)) w : ℝ)) -
        ((K * (param.blocksPerMacro - 1) *
          param.blockLength : ℕ) : ℝ) * P.wordMass (List.ofFn w) =
      ∑ j : PrefixBlockIndex K param.blocksPerMacro,
        ((internalOccurrenceCount
            (data.labels (prefixBlockLift hKH j)) w : ℝ) -
          (param.blockLength : ℝ) * P.wordMass (List.ofFn w)) := by
    calc
      (∑ j : PrefixBlockIndex K param.blocksPerMacro,
          (internalOccurrenceCount
            (data.labels (prefixBlockLift hKH j)) w : ℝ)) -
        ((K * (param.blocksPerMacro - 1) *
          param.blockLength : ℕ) : ℝ) * P.wordMass (List.ofFn w) =
        (∑ j : PrefixBlockIndex K param.blocksPerMacro,
          (internalOccurrenceCount
            (data.labels (prefixBlockLift hKH j)) w : ℝ)) -
          ∑ _j : PrefixBlockIndex K param.blocksPerMacro,
            (param.blockLength : ℝ) * P.wordMass (List.ofFn w) := by
              rw [hconst]
      _ = ∑ j : PrefixBlockIndex K param.blocksPerMacro,
          ((internalOccurrenceCount
              (data.labels (prefixBlockLift hKH j)) w : ℝ) -
            (param.blockLength : ℝ) * P.wordMass (List.ofFn w)) := by
        rw [Finset.sum_sub_distrib]
  rw [hrewrite]
  calc
    |∑ j : PrefixBlockIndex K param.blocksPerMacro,
        ((internalOccurrenceCount
            (data.labels (prefixBlockLift hKH j)) w : ℝ) -
          (param.blockLength : ℝ) * P.wordMass (List.ofFn w))| ≤
      ∑ j : PrefixBlockIndex K param.blocksPerMacro,
        |(internalOccurrenceCount
            (data.labels (prefixBlockLift hKH j)) w : ℝ) -
          (param.blockLength : ℝ) * P.wordMass (List.ofFn w)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : PrefixBlockIndex K param.blocksPerMacro,
        β * (param.blockLength : ℝ) :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = β * ((K * (param.blocksPerMacro - 1) *
        param.blockLength : ℕ) : ℝ) := by
      simp [PrefixBlockIndex, Nat.cast_mul]
      ring

/-- Every prefix of a painted stage has the prescribed Bernoulli word counts,
up to the typical-block error, uncovered macroblock mass, and internal-edge
loss.  This is the uniform within-stage estimate in Kamae (1973), Theorem 3,
p. 139. -/
theorem StageAssignmentData.prefix_count_le {b : ℕ}
    {P : LetterDistribution b} {t : ℕ → Bool}
    {μ : BlockFamily Bool} {ν : BlockFamily (Fin b × Bool)}
    {a T R : ℕ} {β : ℝ} {param : PaintingParameters P R β}
    (data : StageAssignmentData P t μ ν a T R β param)
    (filler : Fin b) (x : ℕ → Fin b)
    (hx : ExtendsInterval a (data.stageWord filler) x)
    (s : ℕ) (hs : s ≤ T)
    (r : ℕ) (hr : 1 ≤ r) (hrR : r ≤ R)
    (w : Fin r → Fin b) :
    |(intervalWordCount x a s (List.ofFn w) : ℝ) -
        (s : ℝ) * P.wordMass (List.ofFn w)| ≤
      4 * β * (s : ℝ) + param.macroLength := by
  classical
  let K : ℕ := s / param.macroLength
  let blocks : ℕ := K * (param.blocksPerMacro - 1)
  let covered : ℕ := blocks * param.blockLength
  let edge : ℕ := blocks * (r - 1)
  let good : ℕ := blocks * (param.blockLength + 1 - r)
  let deficit : ℕ := s - covered
  let missing : ℕ := s - good
  let p : ℝ := P.wordMass (List.ofFn w)
  let A : ℝ :=
    ∑ j : PrefixBlockIndex K param.blocksPerMacro,
      (internalOccurrenceCount
        (data.labels (prefixBlockLift (K := K)
          (H := data.macroblocks)
          (Q := param.blocksPerMacro) (by
            dsimp [K]
            rw [data.macroblocks_eq]
            exact Nat.div_le_div_right hs) j)) w : ℝ)
  let C : ℝ := (intervalWordCount x a s (List.ofFn w) : ℝ)
  have hLpos : 0 < param.blockLength :=
    lt_of_lt_of_le Nat.zero_lt_one param.one_le_blockLength
  have hQpos : 0 < param.blocksPerMacro := by
    have htwo := param.two_le_blocksPerMacro
    omega
  have hMpos : 0 < param.macroLength := by
    rw [param.macro_eq]
    exact Nat.mul_pos hQpos hLpos
  have hrL : r ≤ param.blockLength :=
    hrR.trans param.resolution_le
  have hKH : K ≤ data.macroblocks := by
    dsimp [K]
    rw [data.macroblocks_eq]
    exact Nat.div_le_div_right hs
  have hKM : K * param.macroLength ≤ s := by
    dsimp [K]
    exact Nat.div_mul_le_self s param.macroLength
  have hQsubLe :
      param.blocksPerMacro - 1 ≤ param.blocksPerMacro :=
    Nat.sub_le _ _
  have hslotLength :
      (param.blocksPerMacro - 1) * param.blockLength ≤
        param.blocksPerMacro * param.blockLength :=
    Nat.mul_le_mul_right param.blockLength hQsubLe
  have hcoveredKM : covered ≤ K * param.macroLength := by
    dsimp [covered, blocks]
    rw [param.macro_eq]
    have hmul := Nat.mul_le_mul_left K hslotLength
    simpa [Nat.mul_assoc] using hmul
  have hcovered : covered ≤ s := hcoveredKM.trans hKM
  have hlengthSplit :
      param.blockLength + 1 - r + (r - 1) = param.blockLength := by
    omega
  have hgoodEdge : good + edge = covered := by
    dsimp [good, edge, covered]
    calc
      blocks * (param.blockLength + 1 - r) + blocks * (r - 1) =
          blocks * ((param.blockLength + 1 - r) + (r - 1)) := by
        ring
      _ = blocks * param.blockLength := by rw [hlengthSplit]
  have hmissingEq : missing = deficit + edge := by
    dsimp [missing, deficit]
    omega
  have hQsplit :
      param.blocksPerMacro - 1 + 1 = param.blocksPerMacro := by
    omega
  have hcoverSplit :
      covered + K * param.blockLength = K * param.macroLength := by
    dsimp [covered, blocks]
    rw [param.macro_eq]
    calc
      K * (param.blocksPerMacro - 1) * param.blockLength +
          K * param.blockLength =
        K * ((param.blocksPerMacro - 1) + 1) * param.blockLength := by
          ring
      _ = K * param.blocksPerMacro * param.blockLength := by
        rw [hQsplit]
      _ = K * (param.blocksPerMacro * param.blockLength) := by
        ring
  have hdivision :
      K * param.macroLength + s % param.macroLength = s := by
    dsimp [K]
    exact Nat.div_add_mod' s param.macroLength
  have hremainder :
      s - K * param.macroLength = s % param.macroLength := by
    omega
  have hdeficitEq :
      deficit = (s - K * param.macroLength) + K * param.blockLength := by
    dsimp [deficit]
    omega
  have hmodLe : s % param.macroLength ≤ param.macroLength :=
    (Nat.mod_lt s hMpos).le
  have hdeficitNat :
      deficit ≤ K * param.blockLength + param.macroLength := by
    omega
  have hQRealPos : (0 : ℝ) < (param.blocksPerMacro : ℝ) :=
    Nat.cast_pos.mpr hQpos
  have hLRealPos : (0 : ℝ) < (param.blockLength : ℝ) :=
    Nat.cast_pos.mpr hLpos
  have hβpos : 0 < β :=
    lt_of_lt_of_le (one_div_pos.mpr hQRealPos)
      param.reciprocal_blocks_le
  have hβnonneg : 0 ≤ β := hβpos.le
  have hreciprocal :
      (1 : ℝ) ≤ β * (param.blocksPerMacro : ℝ) :=
    (div_le_iff₀ hQRealPos).1 param.reciprocal_blocks_le
  have hscaledReciprocal :=
    mul_le_mul_of_nonneg_left hreciprocal
      (mul_nonneg (Nat.cast_nonneg K)
        (Nat.cast_nonneg param.blockLength))
  have hblockLengthBound :
      ((K * param.blockLength : ℕ) : ℝ) ≤ β * (s : ℝ) := by
    calc
      ((K * param.blockLength : ℕ) : ℝ) =
          (K : ℝ) * (param.blockLength : ℝ) := by
        rw [Nat.cast_mul]
      _ ≤ ((K : ℝ) * (param.blockLength : ℝ)) *
          (β * (param.blocksPerMacro : ℝ)) := by
        simpa using hscaledReciprocal
      _ = β * ((K * param.macroLength : ℕ) : ℝ) := by
        rw [param.macro_eq]
        simp only [Nat.cast_mul]
        ring
      _ ≤ β * (s : ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hKM) hβnonneg
  have hdeficitBound :
      (deficit : ℝ) ≤ β * (s : ℝ) + (param.macroLength : ℝ) := by
    calc
      (deficit : ℝ) ≤
          ((K * param.blockLength + param.macroLength : ℕ) : ℝ) :=
        Nat.cast_le.mpr hdeficitNat
      _ = ((K * param.blockLength : ℕ) : ℝ) +
          (param.macroLength : ℝ) := by
        rw [Nat.cast_add]
      _ ≤ β * (s : ℝ) + (param.macroLength : ℝ) :=
        add_le_add_right hblockLengthBound _
  have hrSub : r - 1 ≤ R - 1 :=
    Nat.sub_le_sub_right hrR 1
  have hedgeUnit :
      ((r - 1 : ℕ) : ℝ) ≤ β * (param.blockLength : ℝ) :=
    (Nat.cast_le.mpr hrSub).trans
      ((div_le_iff₀ hLRealPos).1 param.edge_le)
  have hedgeScaled :=
    mul_le_mul_of_nonneg_left hedgeUnit (Nat.cast_nonneg blocks)
  have hedgeBound : (edge : ℝ) ≤ β * (s : ℝ) := by
    calc
      (edge : ℝ) = (blocks : ℝ) * ((r - 1 : ℕ) : ℝ) := by
        simp [edge, Nat.cast_mul]
      _ ≤ (blocks : ℝ) * (β * (param.blockLength : ℝ)) :=
        hedgeScaled
      _ = β * (covered : ℝ) := by
        simp [covered, Nat.cast_mul]
        ring
      _ ≤ β * (s : ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcovered) hβnonneg
  have hβcovered : β * (covered : ℝ) ≤ β * (s : ℝ) :=
    mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcovered) hβnonneg
  have hdeficitCast :
      (deficit : ℝ) = (s : ℝ) - (covered : ℝ) := by
    dsimp [deficit]
    rw [Nat.cast_sub hcovered]
  have hmissingCast :
      (missing : ℝ) = (deficit : ℝ) + (edge : ℝ) := by
    rw [hmissingEq, Nat.cast_add]
  have hsmallSub :
      prefixInternalStartSet param.macroLength param.blockLength
          data.offsets hKH hr ⊆ Finset.range s :=
    prefixInternalStartSet_subset_range
      param.macroLength param.blockLength param.blocksPerMacro
      K data.macroblocks r s param.two_le_blocksPerMacro
      param.macro_eq data.offsets hKH hr hKM
  have hsmallCard :
      (prefixInternalStartSet param.macroLength param.blockLength
        data.offsets hKH hr).card = good := by
    have hcard :=
      prefixInternalStartSet_card
        param.macroLength param.blockLength param.blocksPerMacro
        K data.macroblocks r hLpos param.two_le_blocksPerMacro
        param.macro_eq data.offsets hKH hr
    simpa [good, blocks, Nat.mul_assoc] using hcard
  have hgoodCount :
      ((((prefixInternalStartSet param.macroLength param.blockLength
          data.offsets hKH hr).filter (stageHit x a w)).card : ℕ) : ℝ) = A := by
    have hcount :=
      prefixInternalHitCount_eq data filler x hx hKH hr w
    simpa [A] using hcount
  have htotalCount :
      C = ((((Finset.range s).filter (stageHit x a w)).card : ℕ) : ℝ) := by
    dsimp [C]
    exact congrArg (fun n : ℕ => (n : ℝ))
      (intervalWordCount_eq_filter_card x a s w)
  have hfilters :=
    filtered_card_bounds_real
      (prefixInternalStartSet param.macroLength param.blockLength
        data.offsets hKH hr)
      (Finset.range s) hsmallSub (stageHit x a w)
  have hA_le_C : A ≤ C := by
    calc
      A = ((((prefixInternalStartSet param.macroLength param.blockLength
          data.offsets hKH hr).filter (stageHit x a w)).card : ℕ) : ℝ) :=
        hgoodCount.symm
      _ ≤ ((((Finset.range s).filter (stageHit x a w)).card : ℕ) : ℝ) :=
        hfilters.1
      _ = C := htotalCount.symm
  have hC_le : C ≤ A + (missing : ℝ) := by
    calc
      C = ((((Finset.range s).filter (stageHit x a w)).card : ℕ) : ℝ) :=
        htotalCount
      _ ≤ ((((prefixInternalStartSet param.macroLength param.blockLength
          data.offsets hKH hr).filter (stageHit x a w)).card : ℕ) : ℝ) +
          ((((Finset.range s).card -
            (prefixInternalStartSet param.macroLength param.blockLength
              data.offsets hKH hr).card : ℕ) : ℕ) : ℝ) :=
        hfilters.2
      _ = A + (missing : ℝ) := by
        rw [hgoodCount, Finset.card_range, hsmallCard]
  have hC_le_expanded :
      C ≤ A + (deficit : ℝ) + (edge : ℝ) := by
    calc
      C ≤ A + (missing : ℝ) := hC_le
      _ = A + (deficit : ℝ) + (edge : ℝ) := by
        rw [hmissingCast]
        ring
  have hAabs :
      |A - (covered : ℝ) * p| ≤ β * (covered : ℝ) := by
    have htyp := prefixTypicalSum_abs data hKH hr hrR w
    simpa [A, covered, blocks, p] using htyp
  have hAlower :
      (covered : ℝ) * p - β * (covered : ℝ) ≤ A := by
    have := (abs_le.mp hAabs).1
    linarith
  have hAupper :
      A ≤ (covered : ℝ) * p + β * (covered : ℝ) := by
    have := (abs_le.mp hAabs).2
    linarith
  have hpNonneg : 0 ≤ p := by
    dsimp [p]
    exact P.wordMass_nonneg (List.ofFn w)
  have hpLe : p ≤ 1 := by
    dsimp [p]
    exact P.wordMass_le_one (List.ofFn w)
  have hdeficitNonneg : 0 ≤ (deficit : ℝ) := Nat.cast_nonneg _
  have hdeficitMulLe : (deficit : ℝ) * p ≤ (deficit : ℝ) := by
    have := mul_le_mul_of_nonneg_left hpLe hdeficitNonneg
    simpa using this
  have hβsNonneg : 0 ≤ β * (s : ℝ) :=
    mul_nonneg hβnonneg (Nat.cast_nonneg s)
  have hupperDev :
      C - (s : ℝ) * p ≤
        4 * β * (s : ℝ) + (param.macroLength : ℝ) := by
    calc
      C - (s : ℝ) * p ≤
          (A + (deficit : ℝ) + (edge : ℝ)) - (s : ℝ) * p :=
        sub_le_sub_right hC_le_expanded _
      _ ≤ (((covered : ℝ) * p + β * (covered : ℝ)) +
          (deficit : ℝ) + (edge : ℝ)) - (s : ℝ) * p := by
        linarith [hAupper]
      _ = β * (covered : ℝ) + (deficit : ℝ) + (edge : ℝ) -
          (deficit : ℝ) * p := by
        rw [hdeficitCast]
        ring
      _ ≤ β * (covered : ℝ) + (deficit : ℝ) + (edge : ℝ) := by
        have hmul : 0 ≤ (deficit : ℝ) * p :=
          mul_nonneg hdeficitNonneg hpNonneg
        linarith
      _ ≤ β * (s : ℝ) +
          (β * (s : ℝ) + (param.macroLength : ℝ)) +
          β * (s : ℝ) := by
        linarith [hβcovered, hdeficitBound, hedgeBound]
      _ ≤ 4 * β * (s : ℝ) + (param.macroLength : ℝ) := by
        linarith
  have hlowerDev :
      (s : ℝ) * p - C ≤
        4 * β * (s : ℝ) + (param.macroLength : ℝ) := by
    calc
      (s : ℝ) * p - C ≤ (s : ℝ) * p - A :=
        sub_le_sub_left hA_le_C _
      _ ≤ (s : ℝ) * p -
          ((covered : ℝ) * p - β * (covered : ℝ)) :=
        sub_le_sub_left hAlower _
      _ = (deficit : ℝ) * p + β * (covered : ℝ) := by
        rw [hdeficitCast]
        ring
      _ ≤ (deficit : ℝ) + β * (s : ℝ) := by
        linarith [hdeficitMulLe, hβcovered]
      _ ≤ (β * (s : ℝ) + (param.macroLength : ℝ)) +
          β * (s : ℝ) := by
        linarith [hdeficitBound]
      _ ≤ 4 * β * (s : ℝ) + (param.macroLength : ℝ) := by
        linarith
  change |C - (s : ℝ) * p| ≤
    4 * β * (s : ℝ) + (param.macroLength : ℝ)
  apply abs_le.mpr
  constructor
  · linarith [hlowerDev]
  · exact hupperDev

end

end Agafonov.Kamae1973

#print axioms Agafonov.Kamae1973.StageAssignmentData.prefix_count_le
