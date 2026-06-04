import ProofsInTheBook.Chapter39

/-!
# Chapter 39 (Kneser) — Tucker lemma, sound foundation

A correct (non-degenerate) reduction for `TuckerLemmaStatement`, replacing the earlier
empty-alternating-chain framework (whose `PositiveAlternatingPrefixLabels` is provably
unsatisfiable: it demands `StrictMono (Fin n → Fin (n-1))`, impossible by pigeonhole).

The genuine combinatorial content: along any maximal chain (a signed-permutation prefix
chain of length `n`), the `n` labels live in `SignedLabel (n-1)` (only `n-1` indices), so two
of them share an index.  If two comparable signed subsets carry same-index, opposite-sign
labels, that *is* a complementary comparable pair — the Tucker conclusion.  So Tucker reduces
to producing one chain with a same-index, opposite-sign pair; the "same index" half is free
(pigeonhole), and the remaining content (forcing opposite signs via antipodality) is the real
path argument, now resting on a sound base.
-/

namespace ProofsInTheBook.Chapter39

open SignedPermutation

/-- **Pigeonhole on a maximal chain.** The `n` labels of a signed-permutation prefix chain,
valued in `SignedLabel (n-1)`, cannot all have distinct indices: two share an index. -/
theorem exists_same_index_in_prefixChain {n : ℕ} (hn : 1 ≤ n)
    (label : NonzeroSignedSubset n → SignedLabel (n - 1)) (P : SignedPermutation n) :
    ∃ i j : Fin n, i ≠ j ∧
      (label (P.prefixChain i)).index = (label (P.prefixChain j)).index := by
  have hcard : Fintype.card (Fin (n - 1)) < Fintype.card (Fin n) := by
    simp only [Fintype.card_fin]; omega
  obtain ⟨i, j, hij, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin n => (label (P.prefixChain i)).index) hcard
  exact ⟨i, j, hij, heq⟩

/-- **Sound reduction for Tucker.** If every antipodal labeling admits a maximal chain with two
positions `i < j` whose labels share an index but differ in sign, then `TuckerLemmaStatement n`
holds.  (Those two prefix subsets are comparable by `prefixChain_le`, and same-index/opposite-sign
means each label is the negation of the other — a complementary comparable pair.) -/
theorem tuckerLemmaStatement_of_chain_complementary {n : ℕ}
    (h : ∀ label : NonzeroSignedSubset n → SignedLabel (n - 1),
          (∀ X, label X.antipode = (label X).neg) →
          ∃ (P : SignedPermutation n) (i j : Fin n), i < j ∧
            (label (P.prefixChain i)).index = (label (P.prefixChain j)).index ∧
            (label (P.prefixChain i)).positive ≠ (label (P.prefixChain j)).positive) :
    TuckerLemmaStatement n := by
  intro label hanti
  obtain ⟨P, i, j, hij, hidx, hsign⟩ := h label hanti
  refine ⟨P.prefixChain i, P.prefixChain j, prefixChain_le P (le_of_lt hij), ?_⟩
  refine SignedLabel.ext ?_ ?_
  · -- positive components are opposite
    simp only [SignedLabel.neg]
    revert hsign
    cases hpi : (label (P.prefixChain i)).positive <;>
      cases hpj : (label (P.prefixChain j)).positive <;> simp
  · -- indices agree (neg keeps the index)
    simp only [SignedLabel.neg]
    exact hidx

end ProofsInTheBook.Chapter39
