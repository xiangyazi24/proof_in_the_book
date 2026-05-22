import Mathlib
import ProofsInTheBook.Chapter31

open ProofsInTheBook.Chapter31
open SimpleGraph

namespace ProofsInTheBook.Chapter31

theorem smallestTreeLeaf_pruferDecode (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    smallestTreeLeaf n hn (pruferDecode hn s) =
    (Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v)).min'
      (by
        have h0_le : 0 ≤ n - 2 := Nat.zero_le _
        have h_nonempty := nextLeaf_nonempty hn s 0 h0_le Finset.univ (by simp)
        have h_finsets : Finset.univ.filter (fun v => ∀ j : Fin (n - 2), 0 ≤ j.val → s j ≠ v) =
                         Finset.univ.filter (fun v => ∀ j : Fin (n - 2), s j ≠ v) := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h j => h j (Nat.zero_le _), fun h j _ => h j⟩
        rw [h_finsets] at h_nonempty
        exact h_nonempty) := sorry

lemma step_one_edge (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) (hge : 3 ≤ n) :
    let h1 : 0 + 1 ≤ n - 2 := by omega
    let v := smallestTreeLeaf n hn (pruferDecode hn s)
    (pruferDecodeAux hn s 1 h1).val.2 = {s(v, s ⟨0, by omega⟩)} := by
  intro h1 v
  have h_v_eq := smallestTreeLeaf_pruferDecode n hn s
  dsimp [pruferDecodeAux]
  exact 0

end ProofsInTheBook.Chapter31
