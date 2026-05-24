import Mathlib

/-!
# Chapter 29: Shuffling cards

From "Proofs from THE BOOK":

**Gilbert-Shannon-Reeds riffle shuffles**: the distribution of an `a`-shuffle
on permutations is obtained by uniformly assigning each of the `n` cards one
of `a` labels, then stably sorting by labels.

The book then uses this distribution to analyze total-variation mixing:
about `(3 / 2) * log_2 n` riffle shuffles suffice, and seven shuffles are
enough for a 52-card deck.  This file proves the finite GSR distribution
formula.  The unformalized endpoint is the total-variation statement
`(1 / 2) * sum_sigma |P_{2^k,n}(sigma) - 1 / n!|`, where `P_{a,n}` is the
GSR distribution proved below; the book's cutoff theorem says this drops at
about `k = (3 / 2) * log_2 n`, with the standard 52-card numerical conclusion
at `k = 7`.  That analytic estimate remains an honest frontier: it requires
the Bayer-Diaconis closed formula and real asymptotic/numerical estimates not
developed here.
-/

namespace ProofsInTheBook.Chapter29

/-!
### Riffle-label counting

In the Gilbert-Shannon-Reeds model, an `a`-shuffle can be encoded by assigning
each of the `n` cards one of `a` pile labels, then preserving relative order
inside each pile.  This file records the basic count of such labelings.
-/

abbrev RiffleLabels (a n : ℕ) : Type :=
  Fin n → Fin a

/-- The cards assigned to one pile label in the GSR encoding. -/
def pileOfLabel (a n : ℕ) (labels : RiffleLabels a n) (pile : Fin a) : Finset (Fin n) :=
  Finset.univ.filter fun card => labels card = pile

/-- Membership in the pile selected by a label. -/
theorem mem_pileOfLabel_iff (a n : ℕ) (labels : RiffleLabels a n) (pile : Fin a)
    (card : Fin n) :
    card ∈ pileOfLabel a n labels pile ↔ labels card = pile := by
  simp [pileOfLabel]

/-- The label piles cover the whole deck. -/
theorem pileOfLabel_biUnion_eq_univ (a n : ℕ) (labels : RiffleLabels a n) :
    (Finset.univ.biUnion (fun pile : Fin a => pileOfLabel a n labels pile)) =
      (Finset.univ : Finset (Fin n)) := by
  ext card
  simp [pileOfLabel]

/-- Distinct label piles are disjoint. -/
theorem pileOfLabel_pairwiseDisjoint (a n : ℕ) (labels : RiffleLabels a n) :
    ((Finset.univ : Finset (Fin a)) : Set (Fin a)).PairwiseDisjoint
      (fun pile : Fin a => pileOfLabel a n labels pile) := by
  intro p _ q _ hpq
  change Disjoint (pileOfLabel a n labels p) (pileOfLabel a n labels q)
  rw [Finset.disjoint_left]
  intro card hcp hcq
  simp [pileOfLabel] at hcp hcq
  exact hpq (hcp.symm.trans hcq)

/-- The vector of pile sizes induced by a label assignment. -/
def pileSizeVector (a n : ℕ) (labels : RiffleLabels a n) : Fin a → ℕ :=
  fun pile => (pileOfLabel a n labels pile).card

/-- The pile sizes induced by a label assignment sum to the deck size. -/
theorem pile_card_sum_eq_deck_size (a n : ℕ) (labels : RiffleLabels a n) :
    (∑ pile : Fin a, (pileOfLabel a n labels pile).card) = n := by
  classical
  have hcard := Finset.card_biUnion (s := (Finset.univ : Finset (Fin a)))
    (t := fun pile : Fin a => pileOfLabel a n labels pile)
    (pileOfLabel_pairwiseDisjoint a n labels)
  rw [pileOfLabel_biUnion_eq_univ a n labels] at hcard
  simpa using hcard.symm

/-- The pile-size vector has total size equal to the deck size. -/
theorem pileSizeVector_sum_eq_deck_size (a n : ℕ) (labels : RiffleLabels a n) :
    (∑ pile : Fin a, pileSizeVector a n labels pile) = n := by
  simpa [pileSizeVector] using pile_card_sum_eq_deck_size a n labels

theorem riffleLabels_card (a n : ℕ) :
    Fintype.card (RiffleLabels a n) = a ^ n := by
  simp [RiffleLabels]

/-- Each pile in a riffle labeling contains at most all `n` cards. -/
theorem pileOfLabel_card_le (a n : ℕ) (labels : RiffleLabels a n) (pile : Fin a) :
    (pileOfLabel a n labels pile).card ≤ n := by
  calc (pileOfLabel a n labels pile).card
      ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := Finset.card_univ.trans (Fintype.card_fin n)

/-- The pile-size vector is pointwise bounded by `n`. -/
theorem pileSizeVector_le (a n : ℕ) (labels : RiffleLabels a n) (pile : Fin a) :
    pileSizeVector a n labels pile ≤ n :=
  pileOfLabel_card_le a n labels pile

/-- A card belongs to exactly one pile, namely the one labeled by its label. -/
theorem mem_pileOfLabel_self (a n : ℕ) (labels : RiffleLabels a n) (card : Fin n) :
    card ∈ pileOfLabel a n labels (labels card) :=
  (mem_pileOfLabel_iff a n labels (labels card) card).mpr rfl

/-- The pile a card belongs to is unique. -/
theorem pileOfLabel_eq_of_mem (a n : ℕ) (labels : RiffleLabels a n)
    {card : Fin n} {pile : Fin a} (h : card ∈ pileOfLabel a n labels pile) :
    labels card = pile :=
  (mem_pileOfLabel_iff a n labels pile card).mp h

/-- A pile is empty iff no card has its label. -/
theorem pileOfLabel_eq_empty_iff (a n : ℕ) (labels : RiffleLabels a n) (pile : Fin a) :
    pileOfLabel a n labels pile = ∅ ↔ ∀ card : Fin n, labels card ≠ pile := by
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h card heq
    exact h card ((mem_pileOfLabel_iff a n labels pile card).mpr heq)
  · intro h card hmem
    exact h card ((mem_pileOfLabel_iff a n labels pile card).mp hmem)

/-- A pile is nonempty iff some card has its label. -/
theorem pileOfLabel_nonempty_iff (a n : ℕ) (labels : RiffleLabels a n) (pile : Fin a) :
    (pileOfLabel a n labels pile).Nonempty ↔ ∃ card : Fin n, labels card = pile := by
  constructor
  · rintro ⟨card, hcard⟩
    exact ⟨card, (mem_pileOfLabel_iff a n labels pile card).mp hcard⟩
  · rintro ⟨card, hcard⟩
    exact ⟨card, (mem_pileOfLabel_iff a n labels pile card).mpr hcard⟩

/-- `pileSizeVector` is the cardinality of the label preimage. -/
theorem pileSizeVector_eq_filter_card (a n : ℕ) (labels : RiffleLabels a n) (pile : Fin a) :
    pileSizeVector a n labels pile =
      (Finset.univ.filter (fun card : Fin n => labels card = pile)).card := rfl

/-- The all-zero labeling sends every card to pile 0. -/
def constantLabeling {n : ℕ} (a : ℕ) [NeZero a] : RiffleLabels a n :=
  fun _ => ⟨0, NeZero.pos a⟩

/-- The constant labeling puts all cards in pile 0 and other piles are empty. -/
theorem pileOfLabel_constantLabeling_zero {n : ℕ} (a : ℕ) [NeZero a]
    (pile : Fin a) :
    pileOfLabel a n (constantLabeling a) pile =
      if pile = ⟨0, NeZero.pos a⟩ then (Finset.univ : Finset (Fin n)) else ∅ := by
  ext card
  simp only [mem_pileOfLabel_iff, constantLabeling]
  split_ifs with h
  · simp [h]
  · simp only [Finset.notMem_empty, iff_false]
    intro heq
    exact h heq.symm

/-- The canonical permutation from a riffle labeling: sort cards by their pile
labels using Mathlib's `Tuple.sort` (which breaks ties by the original index).
This is the concrete `permFromLabels` used in the GSR count. -/
noncomputable def riffleSort (a n : ℕ) (labels : RiffleLabels a n) :
    Equiv.Perm (Fin n) :=
  Tuple.sort labels

/-- `riffleSort` produces a permutation that orders cards by their pile labels
in nondecreasing fashion. -/
theorem labels_comp_riffleSort_monotone (a n : ℕ) (labels : RiffleLabels a n) :
    Monotone (labels ∘ riffleSort a n labels) :=
  Tuple.monotone_sort labels

/-- `constantLabeling` is a monotone (in fact constant) function `Fin n → Fin a`. -/
theorem constantLabeling_monotone {n : ℕ} (a : ℕ) [NeZero a] :
    Monotone (constantLabeling (n := n) a) := fun _ _ _ => le_refl _

/-- `riffleSort` applied to the constant labeling is the identity permutation.
The constant labeling assigns the same pile to every card, so the stable sort
preserves the original index order — sorting a constant sequence is a no-op. -/
theorem riffleSort_constantLabeling {n : ℕ} (a : ℕ) [NeZero a] :
    riffleSort a n (constantLabeling a) = Equiv.refl (Fin n) := by
  unfold riffleSort
  exact (Tuple.sort_eq_refl_iff_monotone).mpr (constantLabeling_monotone a)

/-- The constant labeling has zero piles size for non-zero piles. -/
theorem pileSizeVector_constantLabeling {n : ℕ} (a : ℕ) [NeZero a] (pile : Fin a)
    (h_pile : pile ≠ ⟨0, NeZero.pos a⟩) :
    pileSizeVector a n (constantLabeling a) pile = 0 := by
  unfold pileSizeVector
  rw [pileOfLabel_constantLabeling_zero, if_neg h_pile]
  rfl

/-- The constant labeling sends all `n` cards to pile 0. -/
theorem pileSizeVector_constantLabeling_zero {n : ℕ} (a : ℕ) [NeZero a] :
    pileSizeVector a n (constantLabeling a) ⟨0, NeZero.pos a⟩ = n := by
  unfold pileSizeVector
  rw [pileOfLabel_constantLabeling_zero, if_pos rfl]
  exact Finset.card_univ.trans (Fintype.card_fin n)

/--
The stable riffle order induced by a label assignment: card `i` comes before
card `j` in the shuffled deck iff `labels i < labels j`, or `labels i = labels j`
and `i < j` (within-pile stability).
-/
def riffleOrder (a n : ℕ) (labels : RiffleLabels a n) (i j : Fin n) : Prop :=
  labels i < labels j ∨ (labels i = labels j ∧ i < j)

instance (a n : ℕ) (labels : RiffleLabels a n) : DecidableRel (riffleOrder a n labels) :=
  fun i j => by unfold riffleOrder; exact inferInstance

theorem riffleOrder_irrefl (a n : ℕ) (labels : RiffleLabels a n) (i : Fin n) :
    ¬ riffleOrder a n labels i i := by
  intro h
  rcases h with hlt | ⟨_, hlt⟩
  · exact lt_irrefl _ hlt
  · exact lt_irrefl _ hlt

theorem riffleOrder_trans (a n : ℕ) (labels : RiffleLabels a n) {i j k : Fin n}
    (hij : riffleOrder a n labels i j) (hjk : riffleOrder a n labels j k) :
    riffleOrder a n labels i k := by
  rcases hij with h1 | ⟨h1, h2⟩ <;> rcases hjk with h3 | ⟨h3, h4⟩
  · exact Or.inl (lt_trans h1 h3)
  · exact Or.inl (h3 ▸ h1)
  · exact Or.inl (h1 ▸ h3)
  · exact Or.inr ⟨h1.trans h3, lt_trans h2 h4⟩

theorem riffleOrder_trichotomy (a n : ℕ) (labels : RiffleLabels a n) (i j : Fin n)
    (hij : i ≠ j) :
    riffleOrder a n labels i j ∨ riffleOrder a n labels j i := by
  rcases lt_trichotomy (labels i) (labels j) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy i j with h2 | h2 | h2
    · exact Or.inl (Or.inr ⟨h, h2⟩)
    · exact absurd h2 hij
    · exact Or.inr (Or.inr ⟨h.symm, h2⟩)
  · exact Or.inr (Or.inl h)

/-- Within-pile characterization of riffleOrder: when two cards share a pile
label, riffleOrder reduces to the underlying `Fin n` order. -/
theorem riffleOrder_of_same_label (a n : ℕ) (labels : RiffleLabels a n)
    {i j : Fin n} (heq : labels i = labels j) :
    riffleOrder a n labels i j ↔ i < j := by
  unfold riffleOrder
  constructor
  · rintro (hlt | ⟨_, hlt⟩)
    · rw [heq] at hlt; exact absurd hlt (lt_irrefl _)
    · exact hlt
  · intro hlt
    exact Or.inr ⟨heq, hlt⟩

/-- Across-pile characterization: when two cards have different pile labels and
the first is smaller, riffleOrder follows the label order. -/
theorem riffleOrder_of_label_lt (a n : ℕ) (labels : RiffleLabels a n)
    {i j : Fin n} (hlt : labels i < labels j) :
    riffleOrder a n labels i j :=
  Or.inl hlt

/-- The inversion pattern of a target riffle permutation, written in shuffled
position coordinates.  A compatible sorted label sequence must strictly increase
across every such pair. -/
def rifflePattern (n : ℕ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) : Prop :=
  i < j ∧ σ j < σ i

/-- The interval form of the adjacent descent pattern.  It records that the
open interval between two shuffled positions contains an adjacent descent of
`σ`.  This is determined by the usual descent set of `σ`. -/
def riffleDescentIntervalPattern (n : ℕ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    Prop :=
  i < j ∧
    ∃ k : ℕ, (i : ℕ) ≤ k ∧ k + 1 ≤ (j : ℕ) ∧
      ∃ hk : k + 1 < n,
        σ ⟨k + 1, hk⟩ < σ ⟨k, Nat.lt_of_succ_lt hk⟩

/-- A sorted label sequence compatible with a target riffle pattern. -/
def patternCompatible (a n : ℕ) (pattern : Fin n → Fin n → Prop)
    (seq : RiffleLabels a n) : Prop :=
  Monotone seq ∧ ∀ i j : Fin n, pattern i j → seq i < seq j

private theorem exists_adjacent_drop_nat {α : Type*} [LinearOrder α] (f : ℕ → α) :
    ∀ {i j : ℕ}, i < j → f j < f i →
      ∃ k : ℕ, i ≤ k ∧ k + 1 ≤ j ∧ f (k + 1) < f k := by
  intro i j hij hdrop
  induction j generalizing i with
  | zero =>
      exact (Nat.not_lt_zero _ hij).elim
  | succ j ih =>
      by_cases hij' : i < j
      · by_cases hstep : f (j + 1) < f j
        · exact ⟨j, Nat.le_of_lt hij', le_rfl, hstep⟩
        · have hle : f j ≤ f (j + 1) := le_of_not_gt hstep
          have hdrop' : f j < f i := lt_of_le_of_lt hle hdrop
          rcases ih hij' hdrop' with ⟨k, hik, hkj, hkdrop⟩
          exact ⟨k, hik, hkj.trans (Nat.le_succ j), hkdrop⟩
      · have hji : j ≤ i := Nat.le_of_not_gt hij'
        have hij_le : i ≤ j := Nat.le_of_lt_succ hij
        have hi_eq : i = j := le_antisymm hij_le hji
        subst i
        exact ⟨j, le_rfl, le_rfl, hdrop⟩

/-- Every inversion pair contains an adjacent descent between its endpoints. -/
theorem exists_adjacentDescent_of_rifflePattern (n : ℕ) (σ : Equiv.Perm (Fin n))
    {i j : Fin n} (hpattern : rifflePattern n σ i j) :
    ∃ k : ℕ, (i : ℕ) ≤ k ∧ k + 1 ≤ (j : ℕ) ∧
      ∃ hk : k + 1 < n,
        σ ⟨k + 1, hk⟩ < σ ⟨k, Nat.lt_of_succ_lt hk⟩ := by
  rcases hpattern with ⟨hij, hdrop⟩
  let f : ℕ → Fin n := fun t => if ht : t < n then σ ⟨t, ht⟩ else σ i
  have hdropNat : f j < f i := by
    simp [f, i.isLt, j.isLt, hdrop]
  rcases exists_adjacent_drop_nat f (show (i : ℕ) < (j : ℕ) from hij) hdropNat with
    ⟨k, hik, hkj, hkdrop⟩
  have hk : k + 1 < n := hkj.trans_lt j.isLt
  refine ⟨k, hik, hkj, hk, ?_⟩
  have hk0 : k < n := Nat.lt_of_succ_lt hk
  simpa [f, hk, hk0] using hkdrop

/-- Precompose labels by a target permutation.  This changes from original-card
coordinates to shuffled-position coordinates. -/
def labelsEquivSortedSeq (a n : ℕ) (σ : Equiv.Perm (Fin n)) :
    RiffleLabels a n ≃ RiffleLabels a n where
  toFun labels := labels ∘ σ
  invFun seq := seq ∘ σ.symm
  left_inv labels := by
    funext card
    simp [Function.comp_apply]
  right_inv seq := by
    funext card
    simp [Function.comp_apply]

/-- A labeling sorts to `σ` iff the labels, read in the order prescribed by
`σ`, form a monotone sequence with strict increases across the inversion
pattern of `σ`. -/
theorem riffleSort_eq_iff_patternCompatible (a n : ℕ) (labels : RiffleLabels a n)
    (σ : Equiv.Perm (Fin n)) :
    riffleSort a n labels = σ ↔
      patternCompatible a n (rifflePattern n σ) (labels ∘ σ) := by
  constructor
  · intro hsort
    have htuple :
        Monotone (labels ∘ σ) ∧
          ∀ i j, i < j → labels (σ i) = labels (σ j) → σ i < σ j := by
      exact (Tuple.eq_sort_iff (f := labels) (σ := σ)).mp hsort.symm
    refine ⟨htuple.1, ?_⟩
    intro i j hpattern
    rcases hpattern with ⟨hij, hinv⟩
    have hle : (labels ∘ σ) i ≤ (labels ∘ σ) j := htuple.1 hij.le
    exact lt_of_le_of_ne hle fun heq => by
      have hσlt : σ i < σ j := htuple.2 i j hij heq
      exact (lt_asymm hσlt hinv).elim
  · intro hcompat
    have htuple :
        Monotone (labels ∘ σ) ∧
          ∀ i j, i < j → labels (σ i) = labels (σ j) → σ i < σ j := by
      refine ⟨hcompat.1, ?_⟩
      intro i j hij heq
      have hσne : σ i ≠ σ j := by
        intro hσeq
        exact hij.ne (σ.injective hσeq)
      rcases lt_or_gt_of_ne hσne with hσlt | hσgt
      · exact hσlt
      · have hstrict : (labels ∘ σ) i < (labels ∘ σ) j :=
          hcompat.2 i j ⟨hij, hσgt⟩
        have hstrict' : labels (σ i) < labels (σ j) := hstrict
        rw [heq] at hstrict'
        exact (lt_irrefl _ hstrict').elim
    exact ((Tuple.eq_sort_iff (f := labels) (σ := σ)).mpr htuple).symm

/-- For monotone label sequences, requiring strict increases across all
inversion pairs is equivalent to requiring them across intervals containing an
adjacent descent. -/
theorem patternCompatible_rifflePattern_iff_descentIntervalPattern (a n : ℕ)
    (σ : Equiv.Perm (Fin n)) (seq : RiffleLabels a n) :
    patternCompatible a n (rifflePattern n σ) seq ↔
      patternCompatible a n (riffleDescentIntervalPattern n σ) seq := by
  constructor
  · intro hcompat
    refine ⟨hcompat.1, ?_⟩
    intro i j hpattern
    rcases hpattern with ⟨_hij, k, hik, hkj, hk, hdesc⟩
    let lo : Fin n := ⟨k, Nat.lt_of_succ_lt hk⟩
    let hi : Fin n := ⟨k + 1, hk⟩
    have hlohi : lo < hi := by
      change k < k + 1
      exact Nat.lt_succ_self k
    have hleft : seq i ≤ seq lo := by
      apply hcompat.1
      change (i : ℕ) ≤ k
      exact hik
    have hright : seq hi ≤ seq j := by
      apply hcompat.1
      change k + 1 ≤ (j : ℕ)
      exact hkj
    have hstrict : seq lo < seq hi := hcompat.2 lo hi ⟨hlohi, hdesc⟩
    exact lt_of_le_of_lt hleft (lt_of_lt_of_le hstrict hright)
  · intro hcompat
    refine ⟨hcompat.1, ?_⟩
    intro i j hpattern
    rcases hpattern with ⟨hij, hdrop⟩
    rcases exists_adjacentDescent_of_rifflePattern n σ ⟨hij, hdrop⟩ with
      ⟨k, hik, hkj, hk, hdesc⟩
    exact hcompat.2 i j ⟨hij, k, hik, hkj, hk, hdesc⟩

/-- The number of sorted label sequences compatible with a fixed riffle
pattern.  This is the Bayer-Diaconis count written as a fiber over the
descent/inversion pattern, rather than as a closed binomial expression. -/
noncomputable def rifflePatternCount (a n : ℕ) (pattern : Fin n → Fin n → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter fun seq : RiffleLabels a n =>
    patternCompatible a n pattern seq).card

/-- The number of riffle labelings producing `σ` is determined by the riffle
pattern of `σ`. -/
theorem count_determined_by_piles (a n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun labels : RiffleLabels a n => riffleSort a n labels = σ)).card =
      rifflePatternCount a n (rifflePattern n σ) := by
  classical
  let e :
      {labels : RiffleLabels a n // riffleSort a n labels = σ} ≃
        {seq : RiffleLabels a n // patternCompatible a n (rifflePattern n σ) seq} :=
    (labelsEquivSortedSeq a n σ).subtypeEquiv fun labels => by
      change riffleSort a n labels = σ ↔
        patternCompatible a n (rifflePattern n σ) (labels ∘ σ)
      exact riffleSort_eq_iff_patternCompatible a n labels σ
  calc
    (Finset.univ.filter (fun labels : RiffleLabels a n => riffleSort a n labels = σ)).card =
        Fintype.card {labels : RiffleLabels a n // riffleSort a n labels = σ} := by
      exact (Fintype.card_subtype fun labels : RiffleLabels a n =>
        riffleSort a n labels = σ).symm
    _ = Fintype.card
        {seq : RiffleLabels a n // patternCompatible a n (rifflePattern n σ) seq} :=
      Fintype.card_congr e
    _ = rifflePatternCount a n (rifflePattern n σ) := by
      rw [rifflePatternCount]
      exact Fintype.card_subtype fun seq : RiffleLabels a n =>
        patternCompatible a n (rifflePattern n σ) seq

/-- The same fiber count expressed using only the adjacent descent interval
pattern of the target permutation. -/
theorem count_determined_by_descents (a n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun labels : RiffleLabels a n => riffleSort a n labels = σ)).card =
      rifflePatternCount a n (riffleDescentIntervalPattern n σ) := by
  rw [count_determined_by_piles]
  rw [rifflePatternCount, rifflePatternCount]
  congr 1
  ext seq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact patternCompatible_rifflePattern_iff_descentIntervalPattern a n σ seq

/-- The pattern count depends only on the pattern predicate, extensionally. -/
theorem rifflePatternCount_eq_of_same_pattern (a n : ℕ)
    {pattern pattern' : Fin n → Fin n → Prop}
    (hpattern : ∀ i j : Fin n, pattern i j ↔ pattern' i j) :
    rifflePatternCount a n pattern = rifflePatternCount a n pattern' := by
  classical
  rw [rifflePatternCount, rifflePatternCount]
  congr 1
  ext seq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hseq
    exact ⟨hseq.1, fun i j hij => hseq.2 i j ((hpattern i j).mpr hij)⟩
  · intro hseq
    exact ⟨hseq.1, fun i j hij => hseq.2 i j ((hpattern i j).mp hij)⟩

/-- Hence the riffleSort fiber cardinal depends only on the target
permutation's riffle pattern. -/
theorem count_eq_of_same_rifflePattern (a n : ℕ) {σ τ : Equiv.Perm (Fin n)}
    (hpattern : ∀ i j : Fin n, rifflePattern n σ i j ↔ rifflePattern n τ i j) :
    (Finset.univ.filter (fun labels : RiffleLabels a n => riffleSort a n labels = σ)).card =
      (Finset.univ.filter (fun labels : RiffleLabels a n => riffleSort a n labels = τ)).card := by
  rw [count_determined_by_piles, count_determined_by_piles]
  exact rifflePatternCount_eq_of_same_pattern a n hpattern

/-- The riffleSort fiber cardinal depends only on the adjacent descent interval
pattern of the target permutation. -/
theorem count_eq_of_same_riffleDescentIntervalPattern (a n : ℕ)
    {σ τ : Equiv.Perm (Fin n)}
    (hpattern :
      ∀ i j : Fin n,
        riffleDescentIntervalPattern n σ i j ↔ riffleDescentIntervalPattern n τ i j) :
    (Finset.univ.filter (fun labels : RiffleLabels a n => riffleSort a n labels = σ)).card =
      (Finset.univ.filter (fun labels : RiffleLabels a n => riffleSort a n labels = τ)).card := by
  rw [count_determined_by_descents, count_determined_by_descents]
  exact rifflePatternCount_eq_of_same_pattern a n hpattern

/-- The uniform GSR probability of obtaining `σ` from an `(a,n)` label shuffle. -/
noncomputable def gsrShuffleProbability (a n : ℕ) (σ : Equiv.Perm (Fin n)) : ℚ≥0 :=
  (Finset.univ.filter (fun labels : RiffleLabels a n => riffleSort a n labels = σ)).dens

/--
The fiber-count form: the number of `(a,n)` riffle labelings that produce a
target permutation under stable riffle sorting is determined by the target's
adjacent descent interval pattern.
-/
theorem chapter29_fiber_count (a n : ℕ) :
    ∀ σ : Equiv.Perm (Fin n),
      (Finset.univ.filter (fun labels : RiffleLabels a n => riffleSort a n labels = σ)).card =
        rifflePatternCount a n (riffleDescentIntervalPattern n σ) :=
  count_determined_by_descents a n

/--
GSR distribution formula: under the uniform choice of one of the `a^n` label
assignments, the probability of a permutation is its riffle-pattern fiber count
divided by `a^n`.
-/
theorem gsrShuffleProbability_eq_rifflePatternCount (a n : ℕ) [NeZero a]
    (σ : Equiv.Perm (Fin n)) :
    gsrShuffleProbability a n σ =
      (rifflePatternCount a n (riffleDescentIntervalPattern n σ) : ℚ≥0) /
        ((a ^ n : ℕ) : ℚ≥0) := by
  simp [gsrShuffleProbability, Finset.dens, count_determined_by_descents,
    RiffleLabels]

/-- The GSR shuffle probabilities over all permutations have total mass one. -/
theorem gsrShuffleProbability_sum (a n : ℕ) [NeZero a] :
    (∑ σ : Equiv.Perm (Fin n), gsrShuffleProbability a n σ) = 1 := by
  classical
  have h := Finset.dens_eq_sum_dens_fiberwise
    (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (t := (Finset.univ : Finset (RiffleLabels a n)))
    (f := fun labels : RiffleLabels a n => riffleSort a n labels)
    (by intro labels _; exact Finset.mem_univ _)
  simpa [gsrShuffleProbability] using h.symm

/--
Chapter 29 (Gilbert-Shannon-Reeds shuffle distribution): for every positive
`a`, the GSR probabilities form a probability distribution on permutations,
and the probability of `σ` is `rifflePatternCount / a^n`.
-/
theorem chapter29 (a n : ℕ) [NeZero a] :
    (∀ σ : Equiv.Perm (Fin n),
      gsrShuffleProbability a n σ =
        (rifflePatternCount a n (riffleDescentIntervalPattern n σ) : ℚ≥0) /
          ((a ^ n : ℕ) : ℚ≥0)) ∧
      (∑ σ : Equiv.Perm (Fin n), gsrShuffleProbability a n σ) = 1 :=
  ⟨gsrShuffleProbability_eq_rifflePatternCount a n,
    gsrShuffleProbability_sum a n⟩

end ProofsInTheBook.Chapter29
