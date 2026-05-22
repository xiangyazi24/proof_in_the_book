import Mathlib
import ProofsInTheBook.Chapter31

open ProofsInTheBook.Chapter31
open SimpleGraph

namespace ProofsInTheBook.Chapter31

/-! Ch31 Tier 2: recursive structural lemma for the round-trip.

After processing position 0 of the code:
- The smallest tree-leaf nextLeaf_0 = (Finset.univ.filter ¬∈image s).min'
- Its unique neighbor is s_0
- Deleting nextLeaf_0 from the tree (via `deleteSmallestLeafTreeSucc`) gives a tree
  on (n-1) vertices that should equal pruferDecode of the SHIFTED code.

The shifted code s' : pruferCodeSpace (n-1) is defined as follows:
- For j' : Fin (n-3), take j := ⟨j' + 1, _⟩ : Fin (n-2)
- s' j' = (finSuccAboveEquivCompl nextLeaf_0).symm ⟨s j, hmem⟩

But this is only well-defined when s j ≠ nextLeaf_0 (otherwise can't lift).
Need: s j ≠ nextLeaf_0 for all j ≥ 1 (this is exactly the filter condition).

Statement: `deleteSmallestLeafTreeSucc (pruferDecode hn s) = pruferDecode hn' (shiftCode s)`

Implementation: heavy. This is THE blocking lemma for Tier 2 round-trip via induction.

Defer to future session. -/

/-- Shifted code on n-1 vertices after removing nextLeaf_0 and dropping position 0.
TODO: formalize this construction. -/
private def shiftedCode {n : ℕ} (hn : 3 ≤ n) (s : pruferCodeSpace n) :
    pruferCodeSpace (n - 1) := by
  sorry

end ProofsInTheBook.Chapter31
