import Mathlib
import ProofsInTheBook.Chapter31
open ProofsInTheBook.Chapter31
open SimpleGraph

-- [Include decodeForest_init, decodeForest_step, nextLeaf_nonempty from previous successful files]
import Mathlib
import ProofsInTheBook.Chapter31

open ProofsInTheBook.Chapter31
open SimpleGraph

namespace ProofsInTheBook.Chapter31

structure DecodeForestFull (n : ℕ) (state : Finset (Fin n) × Finset (Sym2 (Fin n))) : Prop where
  acyclic : (fromEdgeSet (state.2 : Set (Sym2 (Fin n)))).IsAcyclic
  covers : ∀ u : Fin n, ∃ v ∈ state.1, (fromEdgeSet (state.2 : Set _)).Reachable u v
  uniq : ∀ v ∈ state.1, ∀ w ∈ state.1, v ≠ w → ¬ (fromEdgeSet (state.2 : Set _)).Reachable v w

lemma decodeForest_init (n : ℕ) (hn : 2 ≤ n) :
    DecodeForestFull n (Finset.univ, ∅) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u p hp
    have hne := hp.ne_nil
    cases p with
    | nil => exact False.elim (hne rfl)
    | cons hadj _ => simp at hadj
  · intro u
    exact ⟨u, Finset.mem_univ u, Walk.nil.reachable⟩
  · intro v _ w _ hvw hreach
    rcases hreach with ⟨walk⟩
    cases walk with
    | nil => exact hvw rfl
    | cons hadj _ => simp at hadj

lemma refl_symm {V : Type*} {G : SimpleGraph V} {x y : V}
    (h : Relation.ReflTransGen G.Adj x y) : Relation.ReflTransGen G.Adj y x :=
  (reachable_iff_reflTransGen y x).mp ((reachable_iff_reflTransGen x y).mpr h).symm

lemma reachable_sup_edge {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (hreach : Relation.ReflTransGen (G.Adj ⊔ (edge u v).Adj) x y) :
    Relation.ReflTransGen G.Adj x y ∨
    (Relation.ReflTransGen G.Adj x u ∧ Relation.ReflTransGen G.Adj v y) ∨
    (Relation.ReflTransGen G.Adj x v ∧ Relation.ReflTransGen G.Adj u y) := by
  induction hreach with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | tail h_trans h_adj ih =>
    rcases h_adj with (hG | hedge)
    · rcases ih with (ih1 | ⟨ih2u, ih2v⟩ | ⟨ih3v, ih3u⟩)
      · exact Or.inl (Relation.ReflTransGen.tail ih1 hG)
      · exact Or.inr (Or.inl ⟨ih2u, Relation.ReflTransGen.tail ih2v hG⟩)
      · exact Or.inr (Or.inr ⟨ih3v, Relation.ReflTransGen.tail ih3u hG⟩)
    · revert hedge
      simp [edge, Sym2.ToRel, Sym2.mk_isDiag_iff, Sym2.eq]
      intro hedge'
      rcases hedge' with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · intro _
        rcases ih with (ih1 | ⟨ih2u, ih2v⟩ | ⟨ih3v, ih3u⟩)
        · exact Or.inr (Or.inl ⟨ih1, Relation.ReflTransGen.refl⟩)
        · exact Or.inl (Relation.ReflTransGen.trans ih2u (refl_symm ih2v))
        · exact Or.inl ih3v
      · intro _
        rcases ih with (ih1 | ⟨ih2u, ih2v⟩ | ⟨ih3v, ih3u⟩)
        · exact Or.inr (Or.inr ⟨ih1, Relation.ReflTransGen.refl⟩)
        · exact Or.inl ih2u
        · exact Or.inl (Relation.ReflTransGen.trans ih3v (refl_symm ih3u))

lemma reachable_sup_edge_graph {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (hreach : (G ⊔ edge u v).Reachable x y) :
    G.Reachable x y ∨
    (G.Reachable x u ∧ G.Reachable v y) ∨
    (G.Reachable x v ∧ G.Reachable u y) := by
  have h1 := reachable_sup_edge (reachable_iff_reflTransGen x y |>.mp hreach)
  rcases h1 with (h2 | ⟨h3u, h3v⟩ | ⟨h4v, h4u⟩)
  · exact Or.inl (reachable_iff_reflTransGen x y |>.mpr h2)
  · exact Or.inr (Or.inl ⟨reachable_iff_reflTransGen x u |>.mpr h3u, reachable_iff_reflTransGen v y |>.mpr h3v⟩)
  · exact Or.inr (Or.inr ⟨reachable_iff_reflTransGen x v |>.mpr h4v, reachable_iff_reflTransGen u y |>.mpr h4u⟩)

lemma decodeForest_step {n : ℕ} {state : Finset (Fin n) × Finset (Sym2 (Fin n))}
    (h_forest : DecodeForestFull n state) (nextLeaf : Fin n) (hnL : nextLeaf ∈ state.1)
    (si : Fin n) (h_future : si ∈ state.1) (h_not_eq : nextLeaf ≠ si) :
    DecodeForestFull n (state.1.erase nextLeaf, insert s(nextLeaf, si) state.2) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [Prod.snd]
    have hsup : fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _) = fromEdgeSet (state.2 : Set _) ⊔ edge nextLeaf si := by
      ext a b; simp [fromEdgeSet, edge, Sym2.ToRel, Sym2.eq]; tauto
    rw [hsup]
    rw [isAcyclic_sup_fromEdgeSet_iff]
    refine ⟨h_forest.acyclic, ?_⟩
    intro hreach
    have h_not_reach := h_forest.uniq nextLeaf hnL si h_future h_not_eq
    exact False.elim (h_not_reach hreach)
  · intro u
    dsimp only [Prod.fst, Prod.snd]
    have hsup : fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _) = fromEdgeSet (state.2 : Set _) ⊔ edge nextLeaf si := by
      ext a b; simp [fromEdgeSet, edge, Sym2.ToRel, Sym2.eq]; tauto
    rcases h_forest.covers u with ⟨r, hr, hreach⟩
    by_cases h_r : r = nextLeaf
    · rw [h_r] at hreach
      have h_new_reach : (fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _)).Reachable u nextLeaf := by
        rw [hsup]
        exact hreach.mono le_sup_left
      have h_edge : (fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _)).Adj nextLeaf si := by
        rw [hsup]
        exact Or.inr ⟨by simp [edge, Sym2.ToRel], h_not_eq⟩
      have h_si_reach := Reachable.trans h_new_reach (Adj.reachable h_edge)
      rcases h_forest.covers si with ⟨r', hr', hreach'⟩
      have h_r'_neq : r' ≠ nextLeaf := by
        intro heq
        rw [heq] at hreach'
        have h_not_reach := h_forest.uniq si h_future nextLeaf hnL h_not_eq.symm
        exact h_not_reach hreach'
      have h_r'_reach : (fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _)).Reachable si r' := by
        rw [hsup]
        exact hreach'.mono le_sup_left
      exact ⟨r', Finset.mem_erase_of_ne_of_mem h_r'_neq hr', Reachable.trans h_si_reach h_r'_reach⟩
    · have h_new_reach : (fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _)).Reachable u r := by
        rw [hsup]
        exact hreach.mono le_sup_left
      exact ⟨r, Finset.mem_erase_of_ne_of_mem h_r hr, h_new_reach⟩
  · intro v' hv' w' hw' hvw' hreach
    dsimp only [Prod.snd] at hreach
    rw [Finset.mem_erase] at hv' hw'
    have hsup : fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _) = fromEdgeSet (state.2 : Set _) ⊔ edge nextLeaf si := by
      ext a b; simp [fromEdgeSet, edge, Sym2.ToRel, Sym2.eq]; tauto
    rw [hsup] at hreach
    have h1 := reachable_sup_edge_graph hreach
    rcases h1 with (h2 | ⟨h3u, h3v⟩ | ⟨h4v, h4u⟩)
    · exact h_forest.uniq v' hv'.2 w' hw'.2 hvw' h2
    · have h_eq := h_forest.uniq v' hv'.2 nextLeaf hnL
      by_cases h_v' : v' = nextLeaf
      · exact hv'.1 h_v'
      · exact h_eq h_v' h3u
    · have h_eq := h_forest.uniq w' hw'.2 nextLeaf hnL
      by_cases h_w' : w' = nextLeaf
      · exact hw'.1 h_w'
      · exact h_eq h_w' h4u.symm

end ProofsInTheBook.Chapter31
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

def pruferDecodeAux {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    (m : ℕ) → (hm : m ≤ n - 2) →
    { state : Finset (Fin n) × Finset (Sym2 (Fin n)) //
      DecodeForestFull n state ∧ state.1.card = n - m ∧
      ∀ j : Fin (n - 2), m ≤ j.val → s j ∈ state.1 }
| 0, _ => ⟨(Finset.univ, ∅), by
    refine ⟨decodeForest_init n hn, by simp, ?_⟩
    intro j hj
    exact Finset.mem_univ _⟩
| m + 1, hm => by
    have h_m_le : m ≤ n - 2 := by omega
    let prev := pruferDecodeAux hn s m h_m_le
    let state := prev.val
    have h_forest := prev.property.1
    have h_card := prev.property.2.1
    have h_future := prev.property.2.2
    
    let si : Fin n := s ⟨m, by omega⟩
    have h_si_in : si ∈ state.1 := h_future ⟨m, by omega⟩ (by rfl)
    
    have h_nonempty := nextLeaf_nonempty hn s m h_m_le state.1 h_card
    let nextLeaf := (state.1.filter (fun v => ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ v)).min' h_nonempty
    have h_mem_filter : nextLeaf ∈ state.1.filter (fun v => ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ v) :=
      Finset.min'_mem _ _
    rw [Finset.mem_filter] at h_mem_filter
    have hnL : nextLeaf ∈ state.1 := h_mem_filter.1
    have h_not_in_future : ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ nextLeaf := h_mem_filter.2
    
    have h_not_eq : nextLeaf ≠ si := by
      have h := h_not_in_future ⟨m, by omega⟩ (by rfl)
      exact h.symm
      
    let new_state := (state.1.erase nextLeaf, insert s(nextLeaf, si) state.2)
    have h_new_forest := decodeForest_step h_forest nextLeaf hnL si h_si_in h_not_eq
    
    have h_new_card : new_state.1.card = n - (m + 1) := by
      dsimp [new_state]
      rw [Finset.card_erase_of_mem hnL]
      rw [h_card]
      omega
      
    have h_new_future : ∀ j : Fin (n - 2), m + 1 ≤ j.val → s j ∈ new_state.1 := by
      intro j hj
      dsimp [new_state]
      rw [Finset.mem_erase]
      have h_m_le_j : m ≤ j.val := by omega
      have h1 := h_future j h_m_le_j
      have h2 := h_not_in_future j h_m_le_j
      exact ⟨h2.symm, h1⟩
      
    exact ⟨new_state, h_new_forest, h_new_card, h_new_future⟩
