import Mathlib
import ProofsInTheBook.Chapter31
import Ch31Inverse  -- scratch_ch31_inverse renamed if needed; otherwise just import file path

open ProofsInTheBook.Chapter31
open SimpleGraph

namespace ProofsInTheBook.Chapter31

/-! Ch31 Tier 2: structural recursion for the round-trip. -/

/-- The smallest tree-leaf of the decoded tree (used as the "pop" target at step 0). -/
private noncomputable def nextLeaf0 {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) : Fin n :=
  smallestTreeLeaf n hn (pruferDecode hn s)

/-- nextLeaf0 doesn't appear in s anywhere (it's a Prüfer-leaf). -/
private theorem nextLeaf0_not_in_image {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    ∀ j : Fin (n - 2), s j ≠ nextLeaf0 hn s := by
  sorry

/-- The shifted code on (n-1) vertices: drop position 0, lift through
finSuccAboveEquivCompl on nextLeaf0. -/
noncomputable def shiftedCode {n : ℕ} (hn : 3 ≤ n) (s : pruferCodeSpace n) :
    pruferCodeSpace (n - 1) := fun j' =>
  let nL : Fin n := nextLeaf0 (by omega) s
  let j : Fin (n - 2) := ⟨j'.val + 1, by have := j'.isLt; omega⟩
  let hNe : s j ≠ nL := nextLeaf0_not_in_image (by omega) s j
  let lifted : {v : Fin n // v ∈ ({nL}ᶜ : Set (Fin n))} := ⟨s j, by simp [hNe]⟩
  let preimg : Fin (n - 1) := by
    -- finSuccAboveEquivCompl maps Fin (n-1) ≃ {v : Fin n // v ∈ {nL}ᶜ}
    -- We need an Equiv on Fin (n-1) here, not Fin (m+0) etc.
    sorry
  preimg

end ProofsInTheBook.Chapter31
