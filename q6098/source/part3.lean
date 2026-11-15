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
