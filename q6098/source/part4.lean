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
