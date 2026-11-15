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
    prefixInternalStartSet M L offset hKH hr ⊆ Finset.range s := by
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
    (prefixInternalStartSet M L offset hKH hr).card =
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
    have hstage :=
      (hx ⟨
        selectedCellOffset param.macroLength param.blockLength
          data.offsets (prefixShiftCell hKH z k),
        selectedCellOffset_lt_stage data (prefixShiftCell hKH z k)⟩).trans
        (data.stageWord_selected filler (prefixShiftCell hKH z k))
    rw [prefixShiftCell_offset param.macroLength param.blockLength
      data.offsets hKH hr z k] at hstage
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
