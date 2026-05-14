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

theorem chapter29 (a n : ℕ) :
    Fintype.card (RiffleLabels a n) = a ^ n :=
  riffleLabels_card a n

end ProofsInTheBook.Chapter29
