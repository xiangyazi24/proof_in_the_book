import Mathlib

/-!
# Chapter 29: Shuffling cards

From "Proofs from THE BOOK":

**Perfect shuffles**: 2·log₂(n) perfect riffle shuffles suffice to
bring a deck of n cards close to random (variation distance < 1/2).

The book analyses the Gilbert-Shannon-Reeds model and the
"seven shuffles suffice" theorem for a standard 52-card deck.
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

/-- Certificate for the Gilbert-Shannon-Reeds (GSR) shuffle.
The combinatorial heart of the GSR shuffle is that the number of riffle labelings
that map to a given permutation depends only on the pile sizes (or equivalently,
the descent pattern) induced by that permutation. -/
structure GSRShuffleCertificate (a n : ℕ) where
  /-- The permutation generated by a riffle label assignment. -/
  permFromLabels : RiffleLabels a n → Equiv.Perm (Fin n)
  /-- A function computing the multinomial count for a pile-size vector. -/
  pileSizeCount : (Fin a → ℕ) → ℕ
  /-- The pile-size vector induced by a permutation's descent pattern. -/
  pileSizesFromPerm : Equiv.Perm (Fin n) → Fin a → ℕ
  /-- The number of labelings yielding a permutation σ is exactly the
      multinomial count of its pile-size vector. -/
  count_determined_by_piles :
    ∀ σ : Equiv.Perm (Fin n),
      (Finset.univ.filter (fun ℓ => permFromLabels ℓ = σ)).card =
      pileSizeCount (pileSizesFromPerm σ)

/--
Chapter 29 (Gilbert-Shannon-Reeds shuffle, Tier 1 conditional):
Given a `GSRShuffleCertificate` packaging the structural mapping from random
riffle labels to permutations, the preimage count for any permutation is
determined completely by its pile-size geometry (descent pattern).

TODO (Tier 2): Construct `GSRShuffleCertificate` by explicitly defining
`permFromLabels` via `riffleOrder` sorting, and verify the Aldous-Diaconis
count (multinomial coefficients) and uniform convergence bounds.
-/
theorem chapter29 (a n : ℕ) (cert : GSRShuffleCertificate a n) :
    ∀ σ : Equiv.Perm (Fin n),
      (Finset.univ.filter (fun ℓ => cert.permFromLabels ℓ = σ)).card =
      cert.pileSizeCount (cert.pileSizesFromPerm σ) :=
  cert.count_determined_by_piles

end ProofsInTheBook.Chapter29
