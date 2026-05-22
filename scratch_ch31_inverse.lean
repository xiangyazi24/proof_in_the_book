import Mathlib
import ProofsInTheBook.Chapter31

open ProofsInTheBook.Chapter31
open SimpleGraph

namespace ProofsInTheBook.Chapter31

/-! Ch31 Tier 2: degree formula for the decoded forest. -/

private def countOccurrences {n : ℕ} (s : pruferCodeSpace n) (m : ℕ) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun (j : Fin (n - 2)) => j.val < m ∧ s j = v)).card

/-- Base case: at m = 0, no edges. -/
private theorem pruferDecodeAux_zero_degree (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (v : Fin n) (hm : 0 ≤ n - 2) :
    (fromEdgeSet (V := Fin n)
      ((pruferDecodeAux hn s 0 hm).val.2 : Set (Sym2 (Fin n)))).degree v = 0 := by
  unfold SimpleGraph.degree
  rw [Finset.card_eq_zero]
  ext x
  rw [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj]
  constructor
  · rintro ⟨hmem, _⟩
    have : (pruferDecodeAux hn s 0 hm).val.2 = ∅ := rfl
    rw [this] at hmem
    simp at hmem
  · intro h
    exact absurd h (by simp)

/-- Recursive structure: edge set at m+1 = insert one edge into edge set at m. -/
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

/-- Helper: degree in `fromEdgeSet (insert e S : Set _)` for a vertex not in
the new edge equals degree in `fromEdgeSet (S : Set _)`. -/
private lemma fromEdgeSet_insert_degree_other {n : ℕ}
    (S : Finset (Sym2 (Fin n))) (u w v : Fin n) (huw : u ≠ w)
    (hv_u : v ≠ u) (hv_w : v ≠ w) :
    (fromEdgeSet (V := Fin n) (insert s(u, w) S : Set (Sym2 (Fin n)))).degree v =
    (fromEdgeSet (V := Fin n) (S : Set (Sym2 (Fin n)))).degree v := by
  unfold SimpleGraph.degree
  congr 1
  ext x
  simp only [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj, Finset.coe_insert,
             Set.mem_insert_iff, Sym2.eq_iff]
  constructor
  · rintro ⟨hmem, hne⟩
    refine ⟨?_, hne⟩
    rcases hmem with ⟨heq | heq_swap⟩ | hinS
    · rcases heq with ⟨rfl, rfl⟩
      exact absurd rfl hv_u
    · rcases heq_swap with ⟨rfl, rfl⟩
      exact absurd rfl hv_w
    · exact hinS
  · rintro ⟨hmem, hne⟩
    exact ⟨Or.inr hmem, hne⟩

end ProofsInTheBook.Chapter31
