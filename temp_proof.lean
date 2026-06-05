theorem deleteSmallestLeaf_pruferDecode_v2 {m : ℕ} (hm : 1 ≤ m)
    (s : pruferCodeSpace (m + 2)) :
    deleteSmallestLeafTreeSucc (m + 1) (by omega) (pruferDecode (by omega) s) =
    pruferDecode (by omega : 2 ≤ m + 1) (shiftedCode_v2 hm s) := by
  ext a b
  let shift_s := shiftedCode_v2 hm s
  have hm_sub : m - 1 ≤ m + 1 - 2 := by omega
  have h_corr := pruferDecodeAux_shifted_correspondence hm s (m - 1) hm_sub
  have h_corr_v := h_corr.1
  have h_corr_e := h_corr.2
  
  let L := finSuccAboveEquivCompl (nextLeaf0 (by omega) s)
  have h_state_shift : (pruferFinalState (by omega) shift_s).1 = (pruferDecodeAux (by omega) shift_s (m - 1) hm_sub).val.1 := rfl
  have h_state_s : (pruferFinalState (by omega) s).1 = (pruferDecodeAux (by omega) s m (by omega)).val.1 := by
    have hm_eq : m + 2 - 2 = m := by omega
    exact congrArg (fun k => (pruferDecodeAux (by omega) s k (by omega)).val.1) hm_eq
  
  have h_image_eq : (pruferFinalState (by omega) shift_s).1.image (fun v => (L v).1) = (pruferFinalState (by omega) s).1 := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [h_state_shift] at hv
      rw [h_state_s]
      exact h_corr_v v |>.mp hv
    · intro hx
      have h_not_nL : x ≠ nextLeaf0 (by omega) s := by
        have h_leaf_mem : nextLeaf0 (by omega) s ∈ (pruferDecodeAux (by omega) s 0 (by omega)).val.1 := Finset.mem_univ _
        have h_not_in_final : nextLeaf0 (by omega) s ∉ (pruferFinalState (by omega) s).1 := by
          rw [h_state_s]
          have h_erase : (pruferDecodeAux (by omega) s 1 (by omega)).val.1 = Finset.univ.erase (nextLeaf0 (by omega) s) := by
            have h_eq := pruferDecodeAux_succ_step (by omega) s 0 (by omega)
            dsimp at h_eq
            have h_min_eq := step_zero_min_eq_nextLeaf0 hm s
            rw [h_min_eq] at h_eq
            exact congrArg Prod.fst h_eq
          have h_subset := pruferDecodeAux_mono_val_1 (by omega) s 1 m (by omega) (by omega)
          intro h_mem
          have h_mem_erase := h_subset h_mem
          rw [h_erase] at h_mem_erase
          simp only [Finset.mem_erase, ne_eq] at h_mem_erase
          exact h_mem_erase.1 rfl
        rintro rfl
        exact h_not_in_final hx
      have h_mem_compl : x ∈ ({nextLeaf0 (by omega) s}ᶜ : Set (Fin (m + 2))) := h_not_nL
      let x_lift : {v // v ∈ ({nextLeaf0 (by omega) s}ᶜ : Set (Fin (m + 2)))} := ⟨x, h_mem_compl⟩
      use L.symm x_lift
      constructor
      · rw [h_state_shift]
        apply h_corr_v (L.symm x_lift) |>.mpr
        rw [← h_state_s]
        have h_eval : (L (L.symm x_lift)).1 = x := rfl
        rw [h_eval]
        exact hx
      · exact rfl

  have h_U_eq : (L (pruferLastU (by omega) shift_s)).1 = pruferLastU (by omega) s := by
    have h_min := min'_commutes_L (nextLeaf0 (by omega) s) (pruferFinalState (by omega) shift_s).1 (pruferFinalState_nonempty (by omega) shift_s)
    rw [h_image_eq] at h_min
    exact h_min

  have h_erase_image : ((pruferFinalState (by omega) shift_s).1.erase (pruferLastU (by omega) shift_s)).image (fun v => (L v).1) = (pruferFinalState (by omega) s).1.erase (pruferLastU (by omega) s) := by
    rw [← h_image_eq]
    ext x
    simp only [Finset.mem_image, Finset.mem_erase, ne_eq]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨?_, ⟨v, hv.2, rfl⟩⟩
      intro h_eq
      have h_eq_L : (L v).1 = (L (pruferLastU (by omega) shift_s)).1 := by
        rw [h_U_eq]
        exact h_eq
      have h_eq_v : L v = L (pruferLastU (by omega) shift_s) := Subtype.ext h_eq_L
      have h_eq_v2 := Equiv.injective L h_eq_v
      exact hv.1 h_eq_v2
    · rintro ⟨hx_ne, ⟨v, hv, rfl⟩⟩
      refine ⟨v, ⟨?_, hv⟩, rfl⟩
      intro h_eq
      have h_eq_L : (L v).1 = (L (pruferLastU (by omega) shift_s)).1 := by
        rw [h_eq]
      rw [h_U_eq] at h_eq_L
      exact hx_ne h_eq_L

  have h_V_eq : (L (pruferLastV (by omega) shift_s)).1 = pruferLastV (by omega) s := by
    have h_min := min'_commutes_L (nextLeaf0 (by omega) s) ((pruferFinalState (by omega) shift_s).1.erase (pruferLastU (by omega) shift_s)) (pruferFinalErase_nonempty (by omega) shift_s)
    rw [h_erase_image] at h_min
    exact h_min

  have h_edges_corr : s(a, b) ∈ (pruferFinalState (by omega) shift_s).2 ↔ s((L a).1, (L b).1) ∈ (pruferFinalState (by omega) s).2 := by
    have h_state_shift_2 : (pruferFinalState (by omega) shift_s).2 = (pruferDecodeAux (by omega) shift_s (m - 1) hm_sub).val.2 := rfl
    have h_state_s_2 : (pruferFinalState (by omega) s).2 = (pruferDecodeAux (by omega) s m (by omega)).val.2 := by
      have hm_eq : m + 2 - 2 = m := by omega
      exact congrArg (fun k => (pruferDecodeAux (by omega) s k (by omega)).val.2) hm_eq
    rw [h_state_shift_2, h_state_s_2]
    exact h_corr_e a b

  simp only [pruferDecode, SimpleGraph.fromEdgeSet_adj, Finset.mem_insert, deleteSmallestLeafTreeSucc, SimpleGraph.comap_adj, Function.Embedding.coeFn_mk, SimpleGraph.induce_adj, Set.mem_compl_iff, Set.mem_singleton_iff]
  
  -- Now simplify the RHS
  have h_L_a_prop := (L a).property
  have h_L_b_prop := (L b).property
  
  constructor
  · rintro (h_eq | h_mem)
    · refine ⟨h_L_a_prop, h_L_b_prop, ?_⟩
      left
      rw [h_U_eq, h_V_eq]
      exact h_eq
    · refine ⟨h_L_a_prop, h_L_b_prop, ?_⟩
      right
      exact h_edges_corr.mp h_mem
  · rintro ⟨_, _, (h_eq | h_mem)⟩
    · left
      rw [← h_U_eq, ← h_V_eq] at h_eq
      exact h_eq
    · right
      exact h_edges_corr.mpr h_mem

