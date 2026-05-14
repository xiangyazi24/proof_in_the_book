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

theorem riffleLabels_card (a n : ℕ) :
    Fintype.card (RiffleLabels a n) = a ^ n := by
  simp [RiffleLabels]

theorem chapter29 (a n : ℕ) :
    Fintype.card (RiffleLabels a n) = a ^ n :=
  riffleLabels_card a n

end ProofsInTheBook.Chapter29
