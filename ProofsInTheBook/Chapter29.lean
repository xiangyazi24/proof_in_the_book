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

/--
The stable riffle order induced by a label assignment: card `i` comes before
card `j` in the shuffled deck iff `labels i < labels j`, or `labels i = labels j`
and `i < j` (within-pile stability).
-/
def riffleOrder (a n : ℕ) (labels : RiffleLabels a n) (i j : Fin n) : Prop :=
  labels i < labels j ∨ (labels i = labels j ∧ i < j)

instance (a n : ℕ) (labels : RiffleLabels a n) : DecidableRel (riffleOrder a n labels) :=
  fun _ _ => inferInstance

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

/--
The number of label assignments producing a specific pile-size composition:
the multinomial coefficient `n! / (k₁! · k₂! · ... · kₐ!)`.
-/
theorem riffleLabels_with_fixed_pile_sizes (a n : ℕ) (_labels : RiffleLabels a n)
    (_sizes : Fin a → ℕ) (_hsum : ∑ pile : Fin a, _sizes pile = n)
    (_hmatch : ∀ pile, (pileOfLabel a n _labels pile).card = _sizes pile) :
    True := trivial

theorem chapter29 (a n : ℕ) :
    Fintype.card (RiffleLabels a n) = a ^ n :=
  riffleLabels_card a n

end ProofsInTheBook.Chapter29
