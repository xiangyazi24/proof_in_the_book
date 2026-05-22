import Mathlib
import ProofsInTheBook.Chapter31

open ProofsInTheBook.Chapter31
open SimpleGraph

namespace ProofsInTheBook.Chapter31

/-! Ch31 Tier 2 sub-development. -/

/-- The decoded edge set's underlying graph has no edges initially (m = 0). -/
private theorem pruferDecodeAux_zero_degree (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (v : Fin n) (hm : 0 ≤ n - 2) :
    (fromEdgeSet (V := Fin n)
      ((pruferDecodeAux hn s 0 hm).val.2 : Set (Sym2 (Fin n)))).degree v = 0 := by
  -- At step 0, edges = ∅. So fromEdgeSet on coerced ∅ has no Adj at all.
  -- Use neighborFinset.card = 0 via ext.
  unfold SimpleGraph.degree
  rw [Finset.card_eq_zero]
  ext x
  rw [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj]
  constructor
  · rintro ⟨hmem, _⟩
    -- (pruferDecodeAux hn s 0 hm).val.2 = ∅ by rfl; coerced ∅ is empty set.
    have : (pruferDecodeAux hn s 0 hm).val.2 = ∅ := rfl
    rw [this] at hmem
    simp at hmem
  · intro h
    exact absurd h (by simp)

end ProofsInTheBook.Chapter31
