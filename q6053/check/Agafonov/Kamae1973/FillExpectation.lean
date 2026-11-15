import Agafonov.Kamae1973.LocalCorrectionMean
import Agafonov.Kamae1973.SelectedPairProduct
import Agafonov.Kamae1973.SelectorCounts

/-!
# Finite-window fill expectations

A window that avoids the selector has its Bernoulli product mass.  At a window
anchored by its first selected position, the deviation from that mass is the
local correction encoded by the shifted selected letters and capped gaps.  This
is the conditional-expectation identity in Kamae (1973), statement (4.9),
pp. 142–147.
-/

namespace Agafonov.Kamae1973

open scoped BigOperators

noncomputable section

private instance fillSelectedOffsetDecidable {q : ℕ}
    (a : Fin q) (γ : Fin q → Fin (q + 1)) (ell : Fin q) :
    Decidable (isLocalSelectedOffset a γ ell) := by
  unfold isLocalSelectedOffset
  infer_instance

/-- The conditional probability that one filled input window equals `w`.
Selected coordinates are fixed by `y`, while all other coordinates retain their
letter probabilities.  This is the one-window expectation in Kamae (1973),
statement (4.9), pp. 142–147. -/
noncomputable def fillWindowExpectation {b q : ℕ}
    (P : LetterDistribution b) (τ : ℕ → ℕ) (y : ℕ → Fin b)
    (i : ℕ) (w : Fin q → Fin b) : ℝ :=
  ∏ r : Fin q,
    if h : i + r.val ∈ Set.range τ then
      if y (Classical.choose h) = w r then 1 else 0
    else P.prob (w r)

private theorem fillLocalOffset_eq_cappedGapSum
    (τ : ℕ → ℕ) {q k : ℕ} (hk : 0 < k)
    (a r : Fin q) :
    localSelectedOffset a
        (fun s => cappedGap τ q (k - 1 + s.val)) r =
      a.val + ∑ s ∈ Finset.range r.val,
        (cappedGap τ q (k + s)).val := by
  unfold localSelectedOffset
  rw [Finset.sum_fin_eq_sum_range]
  apply congrArg (fun z : ℕ => a.val + z)
  apply Finset.sum_congr rfl
  intro s hs
  rw [dif_pos (Finset.mem_range.mp hs)]
  have hindex : k - 1 + (s + 1) = k + s := by
    omega
  change (cappedGap τ q (k - 1 + (s + 1))).val =
    (cappedGap τ q (k + s)).val
  rw [hindex]

private theorem fillCappedGap_eq_selectorGap_of_lt
    (τ : ℕ → ℕ) {q j : ℕ}
    (hlt : (cappedGap τ q j).val < q) :
    (cappedGap τ q j).val = selectorGap τ j := by
  rw [cappedGap_val] at hlt ⊢
  by_cases hle : selectorGap τ j ≤ q
  · exact min_eq_left hle
  · have hqle : q ≤ selectorGap τ j := by
      omega
    rw [min_eq_right hqle] at hlt
    omega

private theorem fillLocalOffset_eq_add_selectorSpan_of_lt
    (τ : ℕ → ℕ) (hτ : StrictMono τ)
    {q k : ℕ} (hk : 0 < k) (a r : Fin q)
    (hlt : localSelectedOffset a
      (fun s => cappedGap τ q (k - 1 + s.val)) r < q) :
    localSelectedOffset a
        (fun s => cappedGap τ q (k - 1 + s.val)) r =
      a.val + selectorSpan τ k r.val := by
  rw [fillLocalOffset_eq_cappedGapSum τ hk a r] at hlt ⊢
  rw [selectorSpan_eq_sum_gap τ hτ k r.val]
  apply congrArg (fun z : ℕ => a.val + z)
  apply Finset.sum_congr rfl
  intro s hs
  have hterm :
      (cappedGap τ q (k + s)).val ≤
        ∑ u ∈ Finset.range r.val, (cappedGap τ q (k + u)).val := by
    exact Finset.single_le_sum
      (f := fun u : ℕ => (cappedGap τ q (k + u)).val)
      (fun u _ => Nat.zero_le _)
      hs
  have hcap : (cappedGap τ q (k + s)).val < q := by
    omega
  exact fillCappedGap_eq_selectorGap_of_lt τ hcap

private theorem anchoredLocalOffset_return
    (τ : ℕ → ℕ) (hτ : StrictMono τ)
    {q k : ℕ} (hk : 0 < k) (a r : Fin q)
    (hstart : a.val ≤ τ k)
    (hlt : localSelectedOffset a
      (fun s => cappedGap τ q (k - 1 + s.val)) r < q) :
    τ k - a.val +
        localSelectedOffset a
          (fun s => cappedGap τ q (k - 1 + s.val)) r =
      τ (k + r.val) := by
  have hoffset :=
    fillLocalOffset_eq_add_selectorSpan_of_lt τ hτ hk a r hlt
  rw [hoffset]
  unfold selectorSpan
  have hmono : τ k ≤ τ (k + r.val) :=
    hτ.monotone (by omega)
  omega

private noncomputable def localIndexForOffset {q : ℕ}
    (hq : 0 < q) (a : Fin q) (γ : Fin q → Fin (q + 1))
    (ell : Fin q) : Fin q :=
  if h : isLocalSelectedOffset a γ ell then
    Classical.choose h
  else ⟨0, hq⟩

private theorem localIndexForOffset_spec {q : ℕ}
    (hq : 0 < q) (a : Fin q) (γ : Fin q → Fin (q + 1))
    (ell : Fin q) (h : isLocalSelectedOffset a γ ell) :
    localSelectedOffset a γ (localIndexForOffset hq a γ ell) = ell.val := by
  unfold localIndexForOffset
  rw [dif_pos h]
  exact Classical.choose_spec h

private noncomputable def localOffsetIndex {q : ℕ}
    (hq : 0 < q) (a : Fin q) (γ : Fin q → Fin (q + 1))
    (r : Fin q) : Fin q :=
  if h : localSelectedOffset a γ r < q then
    ⟨localSelectedOffset a γ r, h⟩
  else ⟨0, hq⟩

private theorem localOffsetIndex_val {q : ℕ}
    (hq : 0 < q) (a : Fin q) (γ : Fin q → Fin (q + 1))
    (r : Fin q) (h : localSelectedOffset a γ r < q) :
    (localOffsetIndex hq a γ r).val = localSelectedOffset a γ r := by
  unfold localOffsetIndex
  rw [dif_pos h]

private noncomputable def physicalMatchFactor {b q : ℕ}
    (y : ℕ → Fin b) (k : ℕ) (w : Fin q → Fin b)
    (hq : 0 < q) (a : Fin q) (γ : Fin q → Fin (q + 1))
    (ell : Fin q) : ℝ :=
  if isLocalSelectedOffset a γ ell then
    if y (k + (localIndexForOffset hq a γ ell).val) = w ell then 1 else 0
  else 1

private noncomputable def physicalFreeFactor {b q : ℕ}
    (P : LetterDistribution b) (w : Fin q → Fin b)
    (a : Fin q) (γ : Fin q → Fin (q + 1)) (ell : Fin q) : ℝ :=
  if isLocalSelectedOffset a γ ell then 1 else P.prob (w ell)

private noncomputable def indexMatchFactor {b q : ℕ}
    (y : ℕ → Fin b) (k : ℕ) (w : Fin q → Fin b)
    (hq : 0 < q) (a : Fin q) (γ : Fin q → Fin (q + 1))
    (r : Fin q) : ℝ :=
  if localSelectedOffset a γ r < q then
    if y (k + r.val) = w (localOffsetIndex hq a γ r) then 1 else 0
  else 1

private theorem physicalMatch_product_eq_indexMatch_product
    {b q : ℕ} (y : ℕ → Fin b) (k : ℕ) (w : Fin q → Fin b)
    (hq : 0 < q) (a : Fin q) (γ : Fin q → Fin (q + 1))
    (hγ : ∀ r, 0 < (γ r).val) :
    (∏ ell : Fin q, physicalMatchFactor y k w hq a γ ell) =
      ∏ r : Fin q, indexMatchFactor y k w hq a γ r := by
  classical
  unfold physicalMatchFactor indexMatchFactor
  rw [Finset.prod_ite, Finset.prod_ite]
  simp only [Finset.prod_const_one, mul_one]
  refine Finset.prod_bij
    (fun ell _ => localIndexForOffset hq a γ ell) ?_ ?_ ?_ ?_
  · intro ell hell
    have hsel : isLocalSelectedOffset a γ ell :=
      (Finset.mem_filter.mp hell).2
    have hspec := localIndexForOffset_spec hq a γ ell hsel
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hspec.trans_lt ell.isLt⟩
  · intro ell₁ hell₁ ell₂ hell₂ heq
    have hsel₁ : isLocalSelectedOffset a γ ell₁ :=
      (Finset.mem_filter.mp hell₁).2
    have hsel₂ : isLocalSelectedOffset a γ ell₂ :=
      (Finset.mem_filter.mp hell₂).2
    have hspec₁ := localIndexForOffset_spec hq a γ ell₁ hsel₁
    have hspec₂ := localIndexForOffset_spec hq a γ ell₂ hsel₂
    apply Fin.ext
    calc
      ell₁.val =
          localSelectedOffset a γ (localIndexForOffset hq a γ ell₁) :=
        hspec₁.symm
      _ = localSelectedOffset a γ (localIndexForOffset hq a γ ell₂) := by
        rw [heq]
      _ = ell₂.val := hspec₂
  · intro r hr
    have hvis : localSelectedOffset a γ r < q :=
      (Finset.mem_filter.mp hr).2
    let ell : Fin q := localOffsetIndex hq a γ r
    have hellval : ell.val = localSelectedOffset a γ r := by
      dsimp only [ell]
      exact localOffsetIndex_val hq a γ r hvis
    have hsel : isLocalSelectedOffset a γ ell :=
      ⟨r, hellval.symm⟩
    have hellmem : ell ∈
        (Finset.univ.filter fun ell : Fin q =>
          isLocalSelectedOffset a γ ell) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsel⟩
    refine ⟨ell, hellmem, ?_⟩
    apply (localSelectedOffset_strictMono a γ hγ).injective
    exact (localIndexForOffset_spec hq a γ ell hsel).trans hellval
  · intro ell hell
    have hsel : isLocalSelectedOffset a γ ell :=
      (Finset.mem_filter.mp hell).2
    have hspec := localIndexForOffset_spec hq a γ ell hsel
    have hvis :
        localSelectedOffset a γ (localIndexForOffset hq a γ ell) < q :=
      hspec.trans_lt ell.isLt
    have hoffset :
        localOffsetIndex hq a γ (localIndexForOffset hq a γ ell) = ell := by
      apply Fin.ext
      rw [localOffsetIndex_val hq a γ
        (localIndexForOffset hq a γ ell) hvis]
      exact hspec
    rw [hoffset]

private theorem anchoredFactor_eq_mul
    {b q : ℕ} (P : LetterDistribution b)
    (τ : ℕ → ℕ) (hτ : StrictMono τ) (y : ℕ → Fin b)
    (hq : 0 < q) {k : ℕ} (hk : 0 < k) (a : Fin q)
    (hstart : a.val ≤ τ k)
    (hfirst : a.val < selectorGap τ (k - 1))
    (w : Fin q → Fin b) (ell : Fin q) :
    (if h : τ k - a.val + ell.val ∈ Set.range τ then
        if y (Classical.choose h) = w ell then 1 else 0
      else P.prob (w ell)) =
      physicalMatchFactor y k w hq a
          (fun r => cappedGap τ q (k - 1 + r.val)) ell *
        physicalFreeFactor P w a
          (fun r => cappedGap τ q (k - 1 + r.val)) ell := by
  classical
  have hmemiff :
      τ k - a.val + ell.val ∈ Set.range τ ↔
        isLocalSelectedOffset a
          (fun r => cappedGap τ q (k - 1 + r.val)) ell :=
    (rangeIndicator_eq_true_iff τ _).symm.trans
      (cappedGaps_determine_selected_offsets
        τ hτ hq hk a ell hstart hfirst)
  by_cases hsel : isLocalSelectedOffset a
      (fun r => cappedGap τ q (k - 1 + r.val)) ell
  · have hmem : τ k - a.val + ell.val ∈ Set.range τ :=
      hmemiff.mpr hsel
    let r : Fin q := localIndexForOffset hq a
      (fun s => cappedGap τ q (k - 1 + s.val)) ell
    have hspec :
        localSelectedOffset a
          (fun s => cappedGap τ q (k - 1 + s.val)) r = ell.val := by
      dsimp only [r]
      exact localIndexForOffset_spec hq a
        (fun s => cappedGap τ q (k - 1 + s.val)) ell hsel
    have hvis :
        localSelectedOffset a
          (fun s => cappedGap τ q (k - 1 + s.val)) r < q :=
      hspec.trans_lt ell.isLt
    have hreturn :=
      anchoredLocalOffset_return τ hτ hk a r hstart hvis
    have hphysical :
        τ k - a.val + ell.val = τ (k + r.val) := by
      calc
        τ k - a.val + ell.val =
            τ k - a.val +
              localSelectedOffset a
                (fun s => cappedGap τ q (k - 1 + s.val)) r := by
          rw [hspec]
        _ = τ (k + r.val) := hreturn
    have hchoose : Classical.choose hmem = k + r.val :=
      hτ.injective ((Classical.choose_spec hmem).trans hphysical)
    simp [physicalMatchFactor, physicalFreeFactor, hsel, hmem,
      hchoose, r]
  · have hnotmem : τ k - a.val + ell.val ∉ Set.range τ := by
      intro hmem
      exact hsel (hmemiff.mp hmem)
    simp [physicalMatchFactor, physicalFreeFactor, hsel, hnotmem]

private theorem fillWindowExpectation_eq_factorProducts
    {b q : ℕ} (P : LetterDistribution b)
    (τ : ℕ → ℕ) (hτ : StrictMono τ) (y : ℕ → Fin b)
    (hq : 0 < q) {k : ℕ} (hk : 0 < k) (a : Fin q)
    (hstart : a.val ≤ τ k)
    (hfirst : a.val < selectorGap τ (k - 1))
    (w : Fin q → Fin b) :
    fillWindowExpectation P τ y (τ k - a.val) w =
      (∏ ell : Fin q,
        physicalMatchFactor y k w hq a
          (fun r => cappedGap τ q (k - 1 + r.val)) ell) *
      ∏ ell : Fin q,
        physicalFreeFactor P w a
          (fun r => cappedGap τ q (k - 1 + r.val)) ell := by
  classical
  unfold fillWindowExpectation
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro ell _
  exact anchoredFactor_eq_mul P τ hτ y hq hk a hstart hfirst w ell

private theorem selectedPair_anchor_fst
    {b q : ℕ} (τ : ℕ → ℕ) (y : ℕ → Fin b)
    {k : ℕ} (hk : 0 < k) (r : Fin q) :
    (selectedPair τ q y (k - 1 + r.val)).1 = y (k + r.val) := by
  unfold selectedPair
  congr 1
  omega

private theorem localFillWeight_selectedPair_eq_factorProducts
    {b q : ℕ} (P : LetterDistribution b)
    (τ : ℕ → ℕ) (y : ℕ → Fin b)
    (hq : 0 < q) {k : ℕ} (hk : 0 < k)
    (a : Fin q) (w : Fin q → Fin b) :
    localFillWeight P w a
        (fun r => selectedPair τ q y (k - 1 + r.val)) =
      (∏ r : Fin q,
        indexMatchFactor y k w hq a
          (fun s => cappedGap τ q (k - 1 + s.val)) r) *
      ∏ ell : Fin q,
        physicalFreeFactor P w a
          (fun s => cappedGap τ q (k - 1 + s.val)) ell := by
  classical
  unfold localFillWeight
  dsimp only [selectedPair]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro r _
    have hindex : k - 1 + r.val + 1 = k + r.val := by
      omega
    by_cases hvis :
        localSelectedOffset a
          (fun s => cappedGap τ q (k - 1 + s.val)) r < q
    · rw [dif_pos hvis]
      unfold indexMatchFactor
      rw [if_pos hvis]
      unfold localOffsetIndex
      rw [dif_pos hvis, hindex]
    · rw [dif_neg hvis]
      simp [indexMatchFactor, hvis]
  · unfold physicalFreeFactor
    rfl

private theorem fillWindowExpectation_at_anchor_uncentered
    {b q : ℕ} (P : LetterDistribution b)
    (τ : ℕ → ℕ) (hτ : StrictMono τ) (y : ℕ → Fin b)
    (hq : 0 < q) {k : ℕ} (hk : 0 < k) (a : Fin q)
    (hstart : a.val ≤ τ k)
    (hfirst : a.val < selectorGap τ (k - 1))
    (w : Fin q → Fin b) :
    fillWindowExpectation P τ y (τ k - a.val) w =
      localFillWeight P w a
        (fun r => selectedPair τ q y (k - 1 + r.val)) := by
  have hγ (r : Fin q) :
      0 < (cappedGap τ q (k - 1 + r.val)).val :=
    (cappedGap_mem_Icc τ hτ hq (k - 1 + r.val)).1
  calc
    fillWindowExpectation P τ y (τ k - a.val) w =
        (∏ ell : Fin q,
          physicalMatchFactor y k w hq a
            (fun r => cappedGap τ q (k - 1 + r.val)) ell) *
        ∏ ell : Fin q,
          physicalFreeFactor P w a
            (fun r => cappedGap τ q (k - 1 + r.val)) ell :=
      fillWindowExpectation_eq_factorProducts
        P τ hτ y hq hk a hstart hfirst w
    _ = (∏ r : Fin q,
          indexMatchFactor y k w hq a
            (fun s => cappedGap τ q (k - 1 + s.val)) r) *
        ∏ ell : Fin q,
          physicalFreeFactor P w a
            (fun s => cappedGap τ q (k - 1 + s.val)) ell := by
      rw [physicalMatch_product_eq_indexMatch_product
        y k w hq a
        (fun r => cappedGap τ q (k - 1 + r.val)) hγ]
    _ = localFillWeight P w a
        (fun r => selectedPair τ q y (k - 1 + r.val)) :=
      (localFillWeight_selectedPair_eq_factorProducts
        P τ y hq hk a w).symm

/-- A window containing no selected coordinate has exactly its Bernoulli word
mass.  This is the unselected-window case in Kamae (1973), statement (4.9),
pp. 142–147. -/
theorem fillWindowExpectation_of_no_selected
    {b q : ℕ} (P : LetterDistribution b)
    (τ : ℕ → ℕ) (y : ℕ → Fin b) (i : ℕ) (w : Fin q → Fin b)
    (hnone : ∀ r : Fin q, i + r.val ∉ Set.range τ) :
    fillWindowExpectation P τ y i w = P.wordMass (List.ofFn w) := by
  classical
  unfold fillWindowExpectation
  rw [P.wordMass_ofFn]
  apply Finset.prod_congr rfl
  intro r _
  rw [dif_neg (hnone r)]

/-- At a window whose first selected position is `τ k`, its centered fill
expectation is the local correction read from the shifted selected-pair block.
This is the anchored identity in Kamae (1973), statement (4.9), pp. 142–147. -/
theorem fillWindowExpectation_at_anchor
    {b q : ℕ} (P : LetterDistribution b)
    (τ : ℕ → ℕ) (hτ : StrictMono τ)
    (y : ℕ → Fin b) (hq : 0 < q)
    {k : ℕ} (hk : 0 < k) (a : Fin q)
    (hstart : a.val ≤ τ k)
    (hfirst : a.val < selectorGap τ (k - 1))
    (w : Fin q → Fin b) :
    fillWindowExpectation P τ y (τ k - a.val) w -
        P.wordMass (List.ofFn w) =
      localCorrection P hq w a
        (fun r => selectedPair τ q y (k - 1 + r.val)) := by
  have hcap : a.val < (cappedGap τ q (k - 1)).val := by
    rw [cappedGap_val]
    exact lt_min hfirst a.isLt
  have hbranch :
      a.val <
        ((((fun r : Fin q =>
          selectedPair τ q y (k - 1 + r.val)) ⟨0, hq⟩).2).val) := by
    change a.val < (cappedGap τ q (k - 1 + 0)).val
    simpa using hcap
  unfold localCorrection
  rw [if_pos hbranch]
  rw [fillWindowExpectation_at_anchor_uncentered
    P τ hτ y hq hk a hstart hfirst w]

end

end Agafonov.Kamae1973

#print axioms Agafonov.Kamae1973.fillWindowExpectation_of_no_selected
#print axioms Agafonov.Kamae1973.fillWindowExpectation_at_anchor
