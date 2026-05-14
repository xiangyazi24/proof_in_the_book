import Mathlib

/-!
# Chapter 39: The chromatic number of Kneser graphs

From "Proofs from THE BOOK":

**Lovász's theorem**: χ(KG(n,k)) = n - 2k + 2.

The book presents Bárány's short proof using the Borsuk-Ulam theorem:
if KG(n,k) were (n-2k+1)-colorable, one could construct a continuous
map S^{n-2k+1} → ℝ^{n-2k} with no antipodal pair mapping to the same
point, contradicting Borsuk-Ulam.
-/

namespace ProofsInTheBook.Chapter39

/-- Vertices of the Kneser graph `KG(n,k)`: the `k`-subsets of `[n]`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

instance (n k : ℕ) : Fintype (KneserVertex n k) := by
  dsimp [KneserVertex]
  infer_instance

instance (n k : ℕ) : DecidableEq (KneserVertex n k) := by
  dsimp [KneserVertex]
  infer_instance

/--
The first finite-counting layer in the Kneser graph proof: `KG(n,k)` has
`n choose k` vertices.
-/
theorem kneserVertex_card (n k : ℕ) :
    Fintype.card (KneserVertex n k) = n.choose k := by
  rw [Fintype.card_subtype]
  have hset :
      ({s | s.card = k} : Finset (Finset (Fin n))) =
        Finset.powersetCard k Finset.univ := by
    ext s
    simp [Finset.mem_powersetCard]
  rw [hset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem chapter39 (n k : ℕ) :
    Fintype.card (KneserVertex n k) = n.choose k :=
  kneserVertex_card n k

end ProofsInTheBook.Chapter39
