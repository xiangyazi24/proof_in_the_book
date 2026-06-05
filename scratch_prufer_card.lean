import Mathlib
import ProofsInTheBook.Chapter31
open ProofsInTheBook.Chapter31
open SimpleGraph

lemma nextLeaf_nonempty {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) (m : ℕ) (hm : m ≤ n - 2)
    (available : Finset (Fin n)) (h_card : available.card = n - m) :
    (available.filter (fun v => ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ v)).Nonempty := by
  let remaining_indices := Finset.univ.filter (fun j : Fin (n - 2) => m ≤ j.val)
  let img := remaining_indices.image s
  have h_rem_card : remaining_indices.card ≤ n - 2 - m := by
    have h_inj : Function.Injective (fun j : Fin (n - 2) => j.val) := Fin.val_injective
    have h_map : remaining_indices.image (fun j : Fin (n - 2) => j.val) ⊆ Finset.Ico m (n - 2) := by
      intro x hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨j, hj, rfl⟩
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_Ico]
      exact ⟨hj.2, j.isLt⟩
    calc
      remaining_indices.card = (remaining_indices.image (fun j => j.val)).card := (Finset.card_image_of_injective remaining_indices h_inj).symm
      _ ≤ (Finset.Ico m (n - 2)).card := Finset.card_le_card h_map
      _ = n - 2 - m := by rw [Nat.card_Ico]
  have h_img_card : img.card ≤ n - 2 - m := by
    calc
      img.card ≤ remaining_indices.card := Finset.card_image_le
      _ ≤ n - 2 - m := h_rem_card
  have h_intersect_card : (available ∩ img).card ≤ n - 2 - m := by
    calc
      (available ∩ img).card ≤ img.card := Finset.card_le_card Finset.inter_subset_right
      _ ≤ n - 2 - m := h_img_card
  have h_diff_card : 0 < (available \ img).card := by
    have h_add : (available \ img).card + (available ∩ img).card = available.card := Finset.card_sdiff_add_card_inter available img
    omega
  have h_nonempty : (available \ img).Nonempty := Finset.card_pos.mp h_diff_card
  rcases h_nonempty with ⟨v, hv⟩
  rw [Finset.mem_sdiff, Finset.mem_image] at hv
  refine ⟨v, Finset.mem_filter.mpr ⟨hv.1, ?_⟩⟩
  intro j hj heq
  exact hv.2 ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, heq⟩
