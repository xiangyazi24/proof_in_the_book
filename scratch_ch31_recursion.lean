import Mathlib
import ProofsInTheBook.Chapter31

open ProofsInTheBook.Chapter31
open SimpleGraph

namespace ProofsInTheBook.Chapter31

-- I will paste the definitions of L_monotone and min'_commutes_L here.
lemma L_monotone {m : ℕ} (nL : Fin (m + 2)) (a b : Fin (m + 1)) (h : a ≤ b) :
    (finSuccAboveEquivCompl nL a).1 ≤ (finSuccAboveEquivCompl nL b).1 :=
  StrictMono.monotone (Fin.strictMono_succAbove nL) h

lemma min'_commutes_L {m : ℕ} (nL : Fin (m + 2))
    (S : Finset (Fin (m + 1))) (h_nonempty : S.Nonempty) :
    let L := finSuccAboveEquivCompl nL
    (L (S.min' h_nonempty)).1 = (S.image (fun v => (L v).1)).min' (Finset.Nonempty.image h_nonempty _) := by
  intro L
  apply le_antisymm
  · apply Finset.le_min'
    intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    have h_le : S.min' h_nonempty ≤ v := Finset.min'_le _ _ hv
    exact StrictMono.monotone (Fin.strictMono_succAbove nL) h_le
  · apply Finset.min'_le
    simp only [Finset.mem_image]
    exact ⟨S.min' h_nonempty, Finset.min'_mem _ _, rfl⟩

-- Now I'll add pruferDecodeAux_succ_val_2 here so it's available!
private lemma pruferDecodeAux_succ_val_2 {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (m : ℕ) (hm : m + 1 ≤ n - 2) :
    ∃ nextLeaf : Fin n,
      nextLeaf ∈ (pruferDecodeAux hn s m (by omega)).val.1 ∧
      (∀ j : Fin (n - 2), m ≤ j.val → s j ≠ nextLeaf) ∧
      (pruferDecodeAux hn s (m + 1) hm).val.2 =
        insert s(nextLeaf, s ⟨m, by omega⟩)
          (pruferDecodeAux hn s m (by omega)).val.2 ∧
      (pruferDecodeAux hn s (m + 1) hm).val.1 =
        (pruferDecodeAux hn s m (by omega)).val.1.erase nextLeaf := by
  set prev := pruferDecodeAux hn s m (by omega)
  set state := prev.val with hstate
  have h_card := prev.property.2.1
  have h_nonempty := nextLeaf_nonempty hn s m (by omega) state.1 h_card
  set nextLeaf := (state.1.filter (fun v => ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ v)).min' h_nonempty
    with hnextLeaf
  have h_mem_filter : nextLeaf ∈ state.1.filter (fun v => ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ v) :=
    Finset.min'_mem _ _
  rw [Finset.mem_filter] at h_mem_filter
  exact ⟨nextLeaf, h_mem_filter.1, h_mem_filter.2, rfl, rfl⟩

-- And shiftedCode_v2
def shiftedCode_v2 {m : ℕ} (hm : 1 ≤ m) (s : pruferCodeSpace (m + 2)) :
    pruferCodeSpace (m + 1) :=
  fun (j' : Fin (m + 1 - 2)) =>
    let nL := nextLeaf0 (by omega) s
    let hj_lt : j'.val + 1 < m + 2 - 2 := by omega
    let j : Fin (m + 2 - 2) := ⟨j'.val + 1, hj_lt⟩
    let L := finSuccAboveEquivCompl nL
    have h_not_eq : s j ≠ nL := by
      -- we will just use a sorry for testing the structure
      sorry
    L.symm ⟨s j, h_not_eq⟩

-- And the main lemmas
private theorem pruferDecodeAux_shifted_correspondence {m : ℕ} (hm : 1 ≤ m)
    (s : pruferCodeSpace (m + 2)) :
    ∀ (k : ℕ) (hk : k ≤ (m + 1) - 2),
    (∀ v : Fin (m + 1),
       v ∈ (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k hk).val.1 ↔
       (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) v).1
         ∈ (pruferDecodeAux (by omega) s (k + 1) (by omega)).val.1) ∧
    (∀ a b : Fin (m + 1),
       s(a, b) ∈ (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k hk).val.2 ↔
       s((finSuccAboveEquivCompl (nextLeaf0 (by omega) s) a).1,
          (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) b).1)
         ∈ (pruferDecodeAux (by omega) s (k + 1) (by omega)).val.2) := by
  intro k
  induction k with
  | zero =>
    sorry
  | succ k ih =>
    sorry

end ProofsInTheBook.Chapter31
