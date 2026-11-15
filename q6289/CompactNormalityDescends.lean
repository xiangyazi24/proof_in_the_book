import Agafonov.Kamae1973.CompactContinuityCylinders
import Mathlib.MeasureTheory.Measure.Portmanteau
import Agafonov.WeightedNormality
import Agafonov.Kamae1973.CompactEmpiricalFrequency
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# Normality descends through finite continuity quantizations

The null-frontier portmanteau theorem transfers compact-window frequencies
to finite quantization cylinders, and the one-coordinate version transfers
selected letter frequencies. This is the quantization descent step in
Kamae (1973), Section 1, pp. 121–124.
-/

namespace Agafonov.Kamae1973

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

private theorem listRange_countP_eq_filter_card
    (p : ℕ → Bool) (N : ℕ) :
    (List.range N).countP p =
      ((Finset.range N).filter (fun i => p i = true)).card := by
  classical
  have hnodup : ((List.range N).filter p).Nodup :=
    (List.filter_sublist (p := p) (l := List.range N)).nodup List.nodup_range
  calc
    (List.range N).countP p =
        ((List.range N).filter p).length := List.countP_eq_length_filter
    _ = ((List.range N).filter p).toFinset.card := by
      symm
      exact List.toFinset_card_of_nodup hnodup
    _ = ((Finset.range N).filter (fun i => p i = true)).card := by
      simp [List.toFinset_filter, List.toFinset_range]

private theorem blockCount_eq_filter_card
    {b : ℕ} (x : ℕ → Fin b) (w : List (Fin b)) (N : ℕ) :
    blockCount x w N =
      ((Finset.range N).filter
        (fun i => prefixList (fun j => x (i + j)) w.length = w)).card := by
  classical
  unfold blockCount
  simpa [beq_iff_eq] using
    (listRange_countP_eq_filter_card
      (fun i => prefixList (fun j => x (i + j)) w.length == w) N)

private theorem wordCount_eq_filter_card
    {C : Type*} [DecidableEq C] (x : ℕ → C) (w : List C) (N : ℕ) :
    wordCount x w N =
      ((Finset.range N).filter
        (fun i => prefixList (fun j => x (i + j)) w.length = w)).card := by
  classical
  unfold wordCount
  simpa using
    (listRange_countP_eq_filter_card
      (fun i => decide (prefixList (fun j => x (i + j)) w.length = w)) N)

/-- A compact-normal sequence has the expected limiting frequencies for every
finite quantization word. This is the continuity-set transfer in Kamae
(1973), Section 1, pp. 121–124. -/
theorem compactNormal_quantize
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (q : CompactQuantization X P)
    (ξ : ℕ → X) (hξ : IsCompactNormal P ξ) :
    IsWeightedNormal (quantizationLetterLaw P q)
      (quantizeSequence q ξ) := by
  classical
  change ∀ w : List (Fin q.size),
    Tendsto
      (fun N : ℕ =>
        (blockCount (quantizeSequence q ξ) w N : ℝ) / (N : ℝ))
      atTop (𝓝 ((quantizationLetterLaw P q).wordMass w))
  intro w
  let r : ℕ := w.length
  let u : Fin r → Fin q.size := fun j => w.get j
  have hword : List.ofFn u = w := by
    simp [u, r, List.ofFn_get]
  let z : ℕ → Fin q.size := quantizeSequence q ξ
  have hlist (i : ℕ) :
      List.ofFn (fun j : Fin r => z (i + j.val)) = List.ofFn u ↔
        (fun j : Fin r => z (i + j.val)) = u := by
    constructor
    · intro h
      funext j
      have hj := congrArg (fun l : List (Fin q.size) => l[j.val]?) h
      simpa using hj
    · intro h
      exact congrArg List.ofFn h
  have hwindow (i : ℕ) :
      prefixList (fun j => z (i + j)) r = w ↔
        compactWindow ξ i r ∈ quantizationCylinder q r u := by
    change List.ofFn (fun j : Fin r => z (i + j.val)) = w ↔ _
    rw [← hword, hlist i]
    change (fun j : Fin r => z (i + j.val)) = u ↔
      quantizeWindow q (compactWindow ξ i r) = u
    rw [quantizeWindow_compactWindow]
    rfl
  have hcount (N : ℕ) :
      blockCount z w N =
        ((Finset.range N).filter
          (fun i => compactWindow ξ i r ∈ quantizationCylinder q r u)).card := by
    rw [blockCount_eq_filter_card]
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, hp⟩
      exact ⟨hi, (hwindow i).mp hp⟩
    · rintro ⟨hi, hp⟩
      exact ⟨hi, (hwindow i).mpr hp⟩
  have hfreq :=
    compactNormal_windowFrequency_tendsto P ξ hξ r
      (quantizationCylinder q r u)
      (quantizationCylinder_null_frontier P q r u)
  have hfreq' :
      Tendsto
        (fun N : ℕ => (blockCount z w N : ℝ) / (N : ℝ))
        atTop
        (𝓝 ((Measure.pi (fun _ : Fin r => P)
          (quantizationCylinder q r u)).toReal)) :=
    Tendsto.congr (fun N => by rw [hcount N]) hfreq
  have hmass :
      (Measure.pi (fun _ : Fin r => P)
        (quantizationCylinder q r u)).toReal =
          (quantizationLetterLaw P q).wordMass w := by
    rw [quantizationCylinder_measure]
    rw [ENNReal.toReal_ofReal
      (LetterDistribution.wordMass_nonneg
        (quantizationLetterLaw P q) (List.ofFn u))]
    rw [hword]
  simpa [z, hmass] using hfreq'

/-- A compact-collective sequence has the expected selected frequencies
for every letter of a finite continuity quantization. This is the
one-coordinate continuity-set transfer in Kamae (1973), Section 1,
pp. 121–124. -/
theorem compactCollective_quantize
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (q : CompactQuantization X P)
    (ξ : ℕ → X) (τ : ℕ → ℕ)
    (hξ : IsCompactCollective P ξ τ) :
    IsCollective (quantizationLetterLaw P q)
      (quantizeSequence q ξ) τ := by
  classical
  change ∀ a : Fin q.size,
    Tendsto
      (fun N : ℕ =>
        (wordCount (fun n => (quantizeSequence q ξ) (τ n)) [a] N : ℝ) /
          (N : ℝ))
      atTop (𝓝 ((quantizationLetterLaw P q).prob a))
  intro a
  have hcount (N : ℕ) :
      wordCount (fun n => (quantizeSequence q ξ) (τ n)) [a] N =
        ((Finset.range N).filter
          (fun i => ξ (τ i) ∈ quantizationCell q a)).card := by
    rw [wordCount_eq_filter_card]
    apply congrArg Finset.card
    ext i
    simp [prefixList, quantizeSequence, quantizationCell]
  have hfreq :=
    compactCollective_frequency_tendsto P ξ τ hξ
      (quantizationCell q a) (q.null_frontier a)
  have hfreq' :
      Tendsto
        (fun N : ℕ =>
          (wordCount (fun n => (quantizeSequence q ξ) (τ n)) [a] N : ℝ) /
            (N : ℝ))
        atTop (𝓝 (P (quantizationCell q a)).toReal) :=
    Tendsto.congr (fun N => by rw [hcount N]) hfreq
  simpa [quantizationLetterLaw, quantizationMass] using hfreq'

#print axioms compactNormal_quantize
#print axioms compactCollective_quantize

end Agafonov.Kamae1973
