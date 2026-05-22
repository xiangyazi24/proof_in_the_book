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

/-- Degree at an endpoint of a newly inserted edge increases by 1, provided
the edge was not already present and endpoints are distinct. -/
private lemma fromEdgeSet_insert_degree_endpoint {n : ℕ}
    (S : Finset (Sym2 (Fin n))) (u w : Fin n) (huw : u ≠ w)
    (h_not_in : s(u, w) ∉ S) :
    (fromEdgeSet (V := Fin n) (insert s(u, w) S : Set (Sym2 (Fin n)))).degree u =
    (fromEdgeSet (V := Fin n) (S : Set (Sym2 (Fin n)))).degree u + 1 := by
  unfold SimpleGraph.degree
  -- neighborFinset of new graph at u = neighborFinset of old + {w}, disjoint.
  have h_w_not_neighbor :
      w ∉ (fromEdgeSet (V := Fin n) (S : Set (Sym2 (Fin n)))).neighborFinset u := by
    rw [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj]
    rintro ⟨hmem, _⟩
    exact h_not_in (by exact_mod_cast hmem)
  have h_eq : (fromEdgeSet (V := Fin n) (insert s(u, w) S : Set _)).neighborFinset u =
              insert w ((fromEdgeSet (V := Fin n) (S : Set _)).neighborFinset u) := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj, Finset.coe_insert,
               Set.mem_insert_iff, Finset.mem_insert, Sym2.eq_iff]
    constructor
    · rintro ⟨hmem, hne⟩
      rcases hmem with hnew | hold
      · rcases hnew with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact absurd rfl hne
      · exact Or.inr ⟨hold, hne⟩
    · rintro (rfl | ⟨hmem, hne⟩)
      · refine ⟨Or.inl (Or.inl ?_), huw⟩
        tauto
      · exact ⟨Or.inr hmem, hne⟩
  rw [h_eq]
  exact Finset.card_insert_of_notMem h_w_not_neighbor

/-- Sym2 commutativity: `s(u, w) = s(w, u)` so the insert is symmetric. -/
private lemma sym2_pair_swap {V : Type*} (u w : V) : s(u, w) = s(w, u) :=
  Sym2.eq_swap

/-- Endpoint version usable when goal has `↑(insert e S : Finset _)` form. -/
private lemma fromEdgeSet_finset_insert_degree_endpoint {n : ℕ}
    (S : Finset (Sym2 (Fin n))) (u w : Fin n) (huw : u ≠ w)
    (h_not_in : s(u, w) ∉ S) :
    (fromEdgeSet (V := Fin n)
      (((insert s(u, w) S : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))))).degree u =
    (fromEdgeSet (V := Fin n) (S : Set (Sym2 (Fin n)))).degree u + 1 := by
  -- The base form is in Set.insert: lemma proven in that form.
  -- Use ext-based proof: unfold degree as neighborFinset.card, then case-split.
  unfold SimpleGraph.degree
  have h_w_not_neighbor :
      w ∉ (fromEdgeSet (V := Fin n) (S : Set (Sym2 (Fin n)))).neighborFinset u := by
    rw [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj]
    rintro ⟨hmem, _⟩
    exact h_not_in (by exact_mod_cast hmem)
  have h_eq : (fromEdgeSet (V := Fin n)
        (((insert s(u, w) S : Finset _) : Set _))).neighborFinset u =
      insert w ((fromEdgeSet (V := Fin n) (S : Set _)).neighborFinset u) := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj, Finset.coe_insert,
               Set.mem_insert_iff, Finset.mem_insert, Sym2.eq_iff]
    constructor
    · rintro ⟨hmem, hne⟩
      rcases hmem with hnew | hold
      · rcases hnew with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact absurd rfl hne
      · exact Or.inr ⟨hold, hne⟩
    · rintro (rfl | ⟨hmem, hne⟩)
      · refine ⟨Or.inl (Or.inl ?_), huw⟩
        tauto
      · exact ⟨Or.inr hmem, hne⟩
  rw [h_eq]
  exact Finset.card_insert_of_notMem h_w_not_neighbor

/-- Other version usable when goal has `↑(insert e S : Finset _)` form. -/
private lemma fromEdgeSet_finset_insert_degree_other {n : ℕ}
    (S : Finset (Sym2 (Fin n))) (u w v : Fin n) (huw : u ≠ w)
    (hv_u : v ≠ u) (hv_w : v ≠ w) :
    (fromEdgeSet (V := Fin n)
      (((insert s(u, w) S : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))))).degree v =
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

/-- countOccurrences recursion: stepping `m` to `m+1` adds 1 iff `s ⟨m, _⟩ = v`. -/
private lemma countOccurrences_succ {n : ℕ} (s : pruferCodeSpace n)
    (m : ℕ) (hm : m + 1 ≤ n - 2) (v : Fin n) :
    countOccurrences s (m + 1) v =
    countOccurrences s m v + (if s ⟨m, by omega⟩ = v then 1 else 0) := by
  unfold countOccurrences
  -- Filter at m+1 = filter at m ∪ (singleton ⟨m, _⟩ if s_m = v).
  rw [show (Finset.univ.filter (fun (j : Fin (n - 2)) => j.val < m + 1 ∧ s j = v)) =
       (Finset.univ.filter (fun (j : Fin (n - 2)) => j.val < m ∧ s j = v)) ∪
       (Finset.univ.filter (fun (j : Fin (n - 2)) => j.val = m ∧ s j = v)) from ?_]
  · rw [Finset.card_union_of_disjoint]
    · congr 1
      by_cases hsm : s ⟨m, by omega⟩ = v
      · simp [hsm]
        rw [show (Finset.univ.filter (fun (j : Fin (n - 2)) => j.val = m ∧ s j = v)) =
             {⟨m, by omega⟩} from ?_]
        · simp
        · ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨hval, _⟩
            ext
            exact hval
          · rintro rfl
            exact ⟨rfl, hsm⟩
      · simp [hsm]
        intro x hval hsx
        apply hsm
        have : x = ⟨m, by omega⟩ := by ext; exact hval
        rw [← hsx, this]
    · rw [Finset.disjoint_filter]
      intros j _ h1 h2
      omega
  · ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hval, hs⟩
      by_cases h : j.val = m
      · exact Or.inr ⟨h, hs⟩
      · exact Or.inl ⟨by omega, hs⟩
    · rintro (⟨h, hs⟩ | ⟨h, hs⟩)
      · exact ⟨by omega, hs⟩
      · exact ⟨by omega, hs⟩

/-- Degree formula: after m iterations of `pruferDecodeAux`, the degree of
vertex v in the constructed graph equals the number of times v appears as
`s j` for `j.val < m`, plus 1 if v has already been "popped" (i.e., v has
been chosen as a `nextLeaf` and erased from the available set). -/
private theorem pruferDecodeAux_degree (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    ∀ (m : ℕ) (hm : m ≤ n - 2) (v : Fin n),
    (fromEdgeSet (V := Fin n)
      ((pruferDecodeAux hn s m hm).val.2 : Set (Sym2 (Fin n)))).degree v =
    countOccurrences s m v +
    (if v ∈ (pruferDecodeAux hn s m hm).val.1 then 0 else 1) := by
  intro m
  induction m with
  | zero =>
    intro hm v
    rw [pruferDecodeAux_zero_degree n hn s v hm]
    have hcount : countOccurrences s 0 v = 0 := by
      apply Finset.card_eq_zero.mpr
      ext j; simp [countOccurrences]
    have hmem : v ∈ (pruferDecodeAux hn s 0 hm).val.1 := by
      show v ∈ Finset.univ; exact Finset.mem_univ v
    rw [hcount, if_pos hmem]
  | succ m ih =>
    intro hm v
    -- Sub-key facts about transitions from step m to m+1.
    have h_m_le : m ≤ n - 2 := by omega
    obtain ⟨nextLeaf, hnL_mem, hnL_filter, h_edges_eq, h_avail_eq⟩ :=
      pruferDecodeAux_succ_val_2 hn s m hm
    -- The m-th code entry.
    set si : Fin n := s ⟨m, by omega⟩ with hsi_def
    -- nextLeaf ≠ si: from filter property at j = ⟨m, _⟩.
    have h_nL_ne_si : nextLeaf ≠ si := by
      have := hnL_filter ⟨m, by omega⟩ (by rfl)
      exact (this.symm)
    -- si is in available set at step m (from h_future invariant).
    have h_si_in_prev : si ∈ (pruferDecodeAux hn s m h_m_le).val.1 := by
      have h_future := (pruferDecodeAux hn s m h_m_le).property.2.2
      exact h_future ⟨m, by omega⟩ (by rfl)
    -- Edge s(nextLeaf, si) not already in state.2:
    -- Proof: if it were, then since fromEdgeSet (state.2) is a forest, and
    -- nextLeaf, si are connected in fromEdgeSet (state.2), they're in different
    -- trees. But h_si_in_prev and hnL_mem say both in state.1, and the forest
    -- has each state.1 vertex as a distinct tree root → they aren't reachable
    -- to each other (uniq property).
    have h_edge_not_in : s(nextLeaf, si) ∉ (pruferDecodeAux hn s m h_m_le).val.2 := by
      intro hmem
      have h_forest := (pruferDecodeAux hn s m h_m_le).property.1
      have h_adj : (fromEdgeSet (V := Fin n)
        ((pruferDecodeAux hn s m h_m_le).val.2 : Set (Sym2 (Fin n)))).Adj nextLeaf si := by
        rw [fromEdgeSet_adj]
        exact ⟨by exact_mod_cast hmem, h_nL_ne_si⟩
      have h_reach := h_adj.reachable
      have h_uniq := h_forest.uniq
      exact h_uniq nextLeaf hnL_mem si h_si_in_prev h_nL_ne_si h_reach
    -- Now case on v's relation to nextLeaf and si.
    -- Rewrite goal's val.2 and val.1 via the recursion equations.
    -- Both sides reduce to expressions in `(pruferDecodeAux hn s m h_m_le).val.{1,2}`.
    have h_lhs_eq : (fromEdgeSet (V := Fin n)
        ((pruferDecodeAux hn s (m+1) hm).val.2 : Set (Sym2 (Fin n)))).degree v =
      (fromEdgeSet (V := Fin n)
        ((insert s(nextLeaf, si) (pruferDecodeAux hn s m h_m_le).val.2 :
            Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))).degree v := by
      rw [h_edges_eq]
    have h_indicator_eq :
        (if v ∈ (pruferDecodeAux hn s (m+1) hm).val.1 then (0:ℕ) else 1) =
        (if v ∈ (pruferDecodeAux hn s m h_m_le).val.1.erase nextLeaf
          then (0:ℕ) else 1) := by
      rw [h_avail_eq]
    rw [h_lhs_eq, h_indicator_eq]
    rw [countOccurrences_succ s m hm v]
    have ih_m := ih h_m_le v
    by_cases hv_nL : v = nextLeaf
    · -- Case 1: v = nextLeaf. Substitute v throughout.
      subst hv_nL
      rw [fromEdgeSet_finset_insert_degree_endpoint
        (pruferDecodeAux hn s m h_m_le).val.2 v si h_nL_ne_si h_edge_not_in]
      rw [ih_m, if_pos hnL_mem]
      have hsm_ne : ¬ s ⟨m, by omega⟩ = v := h_nL_ne_si.symm
      simp [hsm_ne]
    · by_cases hv_si : v = si
      · -- Case 2: v = si.
        rw [hv_si]  -- Goal now has si everywhere instead of v.
        have h_edge_swap : s(nextLeaf, si) = s(si, nextLeaf) := sym2_pair_swap _ _
        rw [h_edge_swap]
        have h_edge_not_in' : s(si, nextLeaf) ∉ (pruferDecodeAux hn s m h_m_le).val.2 := by
          rw [← h_edge_swap]; exact h_edge_not_in
        have h_si_ne_nL : si ≠ nextLeaf := h_nL_ne_si.symm
        rw [fromEdgeSet_finset_insert_degree_endpoint
          (pruferDecodeAux hn s m h_m_le).val.2 si nextLeaf h_si_ne_nL h_edge_not_in']
        rw [hv_si] at ih_m
        rw [ih_m, if_pos h_si_in_prev]
        have hsm_eq : s ⟨m, by omega⟩ = si := rfl
        rw [if_pos hsm_eq]
        have hsi_in_erase : si ∈ (pruferDecodeAux hn s m h_m_le).val.1.erase nextLeaf := by
          rw [Finset.mem_erase]
          exact ⟨h_si_ne_nL, h_si_in_prev⟩
        rw [if_pos hsi_in_erase]
      · -- Case 3: v ≠ nextLeaf and v ≠ si.
        rw [fromEdgeSet_finset_insert_degree_other
          (pruferDecodeAux hn s m h_m_le).val.2 nextLeaf si v h_nL_ne_si hv_nL hv_si]
        rw [ih_m]
        have hsm_ne : ¬ s ⟨m, by omega⟩ = v := fun h => hv_si (h.symm)
        rw [if_neg hsm_ne]
        have h_erase_iff :
            (v ∈ (pruferDecodeAux hn s m h_m_le).val.1.erase nextLeaf) ↔
            (v ∈ (pruferDecodeAux hn s m h_m_le).val.1) := by
          rw [Finset.mem_erase]
          exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv_nL, h⟩⟩
        by_cases h : v ∈ (pruferDecodeAux hn s m h_m_le).val.1
        · rw [if_pos h, if_pos (h_erase_iff.mpr h)]
        · rw [if_neg h, if_neg (fun hh => h (h_erase_iff.mp hh))]

/-- pruferFinalState.1 = {pruferLastU, pruferLastV}. -/
private lemma pruferFinalState_1_eq_pair (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 = {pruferLastU hn s, pruferLastV hn s} := by
  have h_uv_ne : pruferLastU hn s ≠ pruferLastV hn s := pruferLastU_ne_V hn s
  have h_u_mem : pruferLastU hn s ∈ (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := pruferLastU_mem hn s
  have h_v_mem : pruferLastV hn s ∈ (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := pruferLastV_mem hn s
  have h_card : (pruferDecodeAux hn s (n - 2) (by rfl)).val.1.card = 2 := pruferFinalState_card hn s
  have h_sub : ({pruferLastU hn s, pruferLastV hn s} : Finset (Fin n)) ⊆
               (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h_u_mem
    · exact h_v_mem
  have h_pair_card : ({pruferLastU hn s, pruferLastV hn s} : Finset (Fin n)).card = 2 :=
    Finset.card_pair h_uv_ne
  exact (Finset.eq_of_subset_of_card_le h_sub (by omega)).symm

/-- The famous Prüfer degree formula: in the decoded tree, every vertex's
degree equals `1 + (# times v appears in the code)`. -/
theorem pruferDecode_degree (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (v : Fin n) :
    ((pruferDecode hn s).1).degree v = countOccurrences s (n - 2) v + 1 := by
  -- pruferDecode = ⟨fromEdgeSet (pruferDecodeEdges hn s : Set _), _⟩.
  -- Both LHS and RHS interpret degree via SimpleGraph.degree; the underlying
  -- graphs are defeq but Fintype instances differ. Use Nat.card via neighborSet.
  have h_card_eq : ((pruferDecode hn s).1).degree v =
      (fromEdgeSet (V := Fin n)
        (pruferDecodeEdges hn s : Set (Sym2 (Fin n)))).degree v := by
    -- Both degrees equal Nat.card (neighborSet v), independent of Fintype instance.
    have h1 : ((pruferDecode hn s).1).degree v =
              (((pruferDecode hn s).1).neighborFinset v).card := rfl
    have h2 : (fromEdgeSet (V := Fin n)
        (pruferDecodeEdges hn s : Set (Sym2 (Fin n)))).degree v =
              ((fromEdgeSet (V := Fin n)
        (pruferDecodeEdges hn s : Set (Sym2 (Fin n)))).neighborFinset v).card := rfl
    rw [h1, h2]
    -- Both neighborFinsets contain the same elements (Adj is the same).
    congr 1
    ext x
    simp [SimpleGraph.mem_neighborFinset]
    rfl
  rw [h_card_eq]
  unfold pruferDecodeEdges
  set u := pruferLastU hn s with hu_def
  set w := pruferLastV hn s with hw_def
  -- pruferDecodeEdges = insert s(u, w) (pruferDecodeAux hn s (n - 2) (by rfl)).val.2.
  have h_uw_ne : u ≠ w := pruferLastU_ne_V hn s
  -- Unfold pruferFinalState to match pruferDecodeAux_degree's signature.
  show (fromEdgeSet (V := Fin n)
        ((insert s(u, w) (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 :
            Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))).degree v =
        countOccurrences s (n - 2) v + 1
  -- Step 2: edge s(u, w) not in pruferFinalState.2 (forest invariant).
  have h_edge_not_in : s(u, w) ∉ (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 := by
    intro hmem
    have h_forest := (pruferDecodeAux hn s (n - 2) (by rfl)).property.1
    have h_adj : (fromEdgeSet (V := Fin n)
      ((pruferDecodeAux hn s (n - 2) (by rfl)).val.2 : Set (Sym2 (Fin n)))).Adj u w := by
      rw [fromEdgeSet_adj]
      exact ⟨by exact_mod_cast hmem, h_uw_ne⟩
    exact h_forest.uniq u (pruferLastU_mem hn s) w (pruferLastV_mem hn s)
      h_uw_ne h_adj.reachable
  -- Step 3: case split on whether v = u or v = w or neither.
  by_cases hv_u : v = u
  · -- After subst, v ↦ u; use u throughout.
    subst hv_u
    rw [fromEdgeSet_finset_insert_degree_endpoint
      (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 u w h_uw_ne h_edge_not_in]
    rw [pruferDecodeAux_degree n hn s (n - 2) (by rfl) u]
    have h_u_mem : u ∈ (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := pruferLastU_mem hn s
    rw [if_pos h_u_mem]
  · by_cases hv_w : v = w
    · subst hv_w
      have h_swap : s(u, w) = s(w, u) := sym2_pair_swap _ _
      rw [h_swap]
      have h_edge_not_in' : s(w, u) ∉ (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 := by
        rw [← h_swap]; exact h_edge_not_in
      have h_w_ne_u : w ≠ u := hv_u
      rw [fromEdgeSet_finset_insert_degree_endpoint
        (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 w u h_w_ne_u h_edge_not_in']
      rw [pruferDecodeAux_degree n hn s (n - 2) (by rfl) w]
      have h_w_mem : w ∈ (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := pruferLastV_mem hn s
      rw [if_pos h_w_mem]
    · rw [fromEdgeSet_finset_insert_degree_other
        (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 u w v h_uw_ne hv_u hv_w]
      rw [pruferDecodeAux_degree n hn s (n - 2) (by rfl) v]
      have h_v_notin : v ∉ (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := by
        rw [pruferFinalState_1_eq_pair]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hv_u, hv_w⟩
      rw [if_neg h_v_notin]

lemma degree_eq_one_iff_exists_unique_adj {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n} :
    G.degree v = 1 ↔ ∃! w, G.Adj v w := by
  have h_deg : G.degree v = (G.neighborFinset v).card := rfl
  rw [h_deg, Finset.card_eq_one]
  constructor
  · rintro ⟨w, hw⟩
    use w
    have h_mem : w ∈ G.neighborFinset v := by rw [hw]; exact Finset.mem_singleton_self w
    simp only [SimpleGraph.mem_neighborFinset] at h_mem
    refine ⟨h_mem, ?_⟩
    intro y hy
    have h_mem_y : y ∈ G.neighborFinset v := by simp only [SimpleGraph.mem_neighborFinset, hy]
    rw [hw, Finset.mem_singleton] at h_mem_y
    exact h_mem_y
  · rintro ⟨w, hw1, hw2⟩
    use w
    ext x
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · intro hx
      exact hw2 x hx
    · rintro rfl
      exact hw1

/-- A vertex is a tree-leaf in the decoded tree iff it doesn't appear in the code. -/
theorem pruferDecode_isLeaf_iff (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (v : Fin n) :
    v ∈ treeLeaves (pruferDecode hn s) ↔ isLeafInPrufer s v := by
  have h_leaf : v ∈ treeLeaves (pruferDecode hn s) ↔ ((pruferDecode hn s).1).degree v = 1 := by
    unfold treeLeaves
    classical
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact degree_eq_one_iff_exists_unique_adj.symm
  rw [h_leaf]
  rw [pruferDecode_degree n hn s v]
  have h_eq : countOccurrences s (n - 2) v + 1 = 1 ↔ countOccurrences s (n - 2) v = 0 := by omega
  rw [h_eq]
  unfold countOccurrences
  rw [Finset.card_eq_zero]
  constructor
  · intro h i
    have hi : i ∉ Finset.univ.filter (fun (j : Fin (n - 2)) => j.val < n - 2 ∧ s j = v) := by
      rw [h]
      simp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hi
    exact hi i.isLt
  · intro h
    ext i
    simp [h i]

/-- The smallest tree-leaf of `pruferDecode s` equals the smallest vertex not
appearing in `s`, which is `nextLeaf_0` from the decode process. -/
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
        exact h_nonempty) := by
  have h_eq : treeLeaves (pruferDecode hn s) = Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v) := by
    ext v
    rw [pruferDecode_isLeaf_iff n hn s v]
    unfold isLeafInPrufer
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold smallestTreeLeaf
  congr

private theorem smallestTreeLeaf_eq_min_filter (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    smallestTreeLeaf n hn (pruferDecode hn s) ∈
    (Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v)) ∧
    ∀ v ∈ (Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v)),
      smallestTreeLeaf n hn (pruferDecode hn s) ≤ v := by
  have h_eq := smallestTreeLeaf_pruferDecode n hn s
  rw [h_eq]
  exact ⟨Finset.min'_mem _ _, fun v hv => Finset.min'_le _ _ hv⟩

lemma step_one_edge_mem (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) (hge : 3 ≤ n) (e : Sym2 (Fin n))
    (he : e ∈ (pruferDecodeAux hn s 1 (by omega)).val.2) :
    e ∈ pruferDecodeEdges hn s := by
  have h_mono : ∀ m (h_ge1 : 1 ≤ m) (hm_le : m ≤ n - 2), e ∈ (pruferDecodeAux hn s m hm_le).val.2 := by
    intro m
    induction m with
    | zero => intro h1 _; omega
    | succ m ih =>
      intro h_ge hm_le
      by_cases h_eq : m = 0
      · subst h_eq
        have h_rw : (pruferDecodeAux hn s 1 (by omega)).val.2 = (pruferDecodeAux hn s 1 hm_le).val.2 := rfl
        rw [← h_rw]
        exact he
      · have hm_ge1 : 1 ≤ m := by omega
        have hm_le_prev : m ≤ n - 2 := by omega
        have ih_m := ih hm_ge1 hm_le_prev
        have h_succ : m + 1 ≤ n - 2 := hm_le
        obtain ⟨_, _, _, h_edges, _⟩ := pruferDecodeAux_succ_val_2 hn s m h_succ
        have h_rw : (pruferDecodeAux hn s (m + 1) hm_le).val.2 = (pruferDecodeAux hn s (m + 1) h_succ).val.2 := rfl
        rw [h_rw, h_edges]
        exact Finset.mem_insert_of_mem ih_m
  have h_in_n2 := h_mono (n - 2) (by omega) (by rfl)
  unfold pruferDecodeEdges
  exact Finset.mem_insert_of_mem h_in_n2

theorem smallestTreeLeafNeighbor_pruferDecode (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (hge : 3 ≤ n) :
    smallestTreeLeafNeighbor n hn (pruferDecode hn s) = s ⟨0, by omega⟩ := by
  set v := smallestTreeLeaf n hn (pruferDecode hn s)
  have h1 : 0 + 1 ≤ n - 2 := by omega
  have hv_min : v = (Finset.univ.filter (fun x => ∀ j : Fin (n - 2), 0 ≤ j.val → s j ≠ x)).min' (nextLeaf_nonempty hn s 0 (by omega) Finset.univ (by simp)) := by
    apply le_antisymm
    · apply Finset.le_min'
      intro y hy
      have hv_le : ∀ x ∈ Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v), v ≤ x :=
        (smallestTreeLeaf_eq_min_filter n hn s).2
      apply hv_le
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      intro j
      exact hy j (Nat.zero_le _)
    · apply Finset.min'_le
      have hv_mem : v ∈ Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v) :=
        (smallestTreeLeaf_eq_min_filter n hn s).1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv_mem ⊢
      intro j _
      exact hv_mem j
  have h_step1 : (pruferDecodeAux hn s 1 h1).val.2 = {s(v, s ⟨0, by omega⟩)} := by
    dsimp [pruferDecodeAux]
    congr 2
    exact hv_min.symm
  have he : s(v, s ⟨0, by omega⟩) ∈ (pruferDecodeAux hn s 1 h1).val.2 := by
    rw [h_step1]
    exact Finset.mem_singleton_self _
  have he_rewrite : s(v, s ⟨0, by omega⟩) ∈ (pruferDecodeAux hn s 1 (by omega)).val.2 := by
    -- we can just change the proof of hm_le
    have h_rw : (pruferDecodeAux hn s 1 h1).val.2 = (pruferDecodeAux hn s 1 (by omega)).val.2 := rfl
    rw [← h_rw]
    exact he
  have h_in_final := step_one_edge_mem n hn s hge _ he_rewrite
  have h_adj : (fromEdgeSet (V := Fin n) (pruferDecodeEdges hn s : Set (Sym2 (Fin n)))).Adj v (s ⟨0, by omega⟩) := by
    rw [fromEdgeSet_adj]
    refine ⟨by exact_mod_cast h_in_final, ?_⟩
    have hv_mem : v ∈ Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v) :=
      (smallestTreeLeaf_eq_min_filter n hn s).1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv_mem
    exact (hv_mem ⟨0, by omega⟩).symm
  
  have h_deg : ((pruferDecode hn s).1).degree v = 1 := by
    have h_leaf : v ∈ treeLeaves (pruferDecode hn s) := Finset.min'_mem _ _
    rw [pruferDecode_isLeaf_iff n hn s v] at h_leaf
    rw [pruferDecode_degree n hn s v]
    have h_occur : countOccurrences s (n - 2) v = 0 := by
      unfold countOccurrences
      rw [Finset.card_eq_zero]
      ext j
      simp [h_leaf j]
    rw [h_occur]
  
  have h_adj' : ((pruferDecode hn s).1).Adj v (s ⟨0, by omega⟩) := h_adj
  exact (smallestTreeLeaf_neighbor_unique n hn (pruferDecode hn s) h_adj').symm

theorem pruferEncode_pruferDecode_zero (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (hge : 3 ≤ n) :
    (pruferEncode hn (pruferDecode hn s)) ⟨0, by omega⟩ = s ⟨0, by omega⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  show (pruferEncodeAux m (pruferDecode _ s)) ⟨0, by omega⟩ = s ⟨0, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  show smallestTreeLeafNeighbor (m' + 3) _ (pruferDecode _ s) = s ⟨0, by omega⟩
  exact smallestTreeLeafNeighbor_pruferDecode (m' + 3) _ s (by omega)

/-- nextLeaf_0: the smallest tree-leaf of the decoded tree (= smallest Prüfer-leaf). -/
noncomputable def nextLeaf0 {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) : Fin n :=
  smallestTreeLeaf n hn (pruferDecode hn s)

/-- nextLeaf_0 doesn't appear in s anywhere. Immediate from pruferDecode_isLeaf_iff. -/
theorem nextLeaf0_not_in_image {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    ∀ j : Fin (n - 2), s j ≠ nextLeaf0 hn s := by
  have h_leaf : nextLeaf0 hn s ∈ treeLeaves (pruferDecode hn s) :=
    smallestTreeLeaf_mem_leaves n hn (pruferDecode hn s)
  rw [pruferDecode_isLeaf_iff n hn s] at h_leaf
  exact h_leaf

/-- The shifted code: drop position 0, lift values through `(finSuccAboveEquivCompl nextLeaf0).symm`. -/
noncomputable def shiftedCode_v2 {m : ℕ} (hm : 1 ≤ m) (s : pruferCodeSpace (m + 2)) :
    pruferCodeSpace (m + 1) := by
  intro j'
  classical
  have h2le : 2 ≤ m + 2 := by omega
  let nL : Fin (m + 2) := nextLeaf0 h2le s
  have hj_lt : j'.val + 1 < (m + 2) - 2 := by have := j'.isLt; omega
  let j : Fin ((m + 2) - 2) := ⟨j'.val + 1, hj_lt⟩
  have hNe : s j ≠ nL := nextLeaf0_not_in_image h2le s j
  have hMem : (s j : Fin (m + 2)) ∈ ({nL}ᶜ : Set (Fin (m + 2))) := by simp [hNe]
  let lifted : {v : Fin (m + 2) // v ∈ ({nL}ᶜ : Set (Fin (m + 2)))} := ⟨s j, hMem⟩
  exact (finSuccAboveEquivCompl nL).symm lifted

theorem deleteSmallestLeaf_pruferDecode_v2 {m : ℕ} (hm : 1 ≤ m)
    (s : pruferCodeSpace (m + 2)) :
    deleteSmallestLeafTreeSucc (m + 1) (by omega) (pruferDecode (by omega) s) =
    pruferDecode (by omega : 2 ≤ m + 1) (shiftedCode_v2 hm s) := by
  have h2le : 2 ≤ m + 2 := by omega
  let nL := nextLeaf0 h2le s
  let L := finSuccAboveEquivCompl nL
  
  -- The LHS is a LabeledTree constructed by taking the induced subgraph on {nL}ᶜ
  -- and relabeling via L.symm.
  -- The RHS is the LabeledTree from pruferDecode on shiftedCode.
  apply Subtype.ext
  ext a b
  
  -- LHS Adj
  have h_LHS_adj : (deleteSmallestLeafTreeSucc (m + 1) (by omega) (pruferDecode (by omega) s)).1.Adj a b ↔
                   (pruferDecode (by omega : 2 ≤ m + 2) s).1.Adj (L a).1 (L b).1 := by
    -- By definition of deleteSmallestLeafTreeSucc and relabeling
    -- Actually deleteSmallestLeafTreeSucc uses finSuccAboveEquivCompl implicitly
    -- Wait, deleteSmallestLeafTree is defined in Chapter31.
    sorry
    
  -- RHS Adj
  have h_RHS_adj : (pruferDecode (by omega : 2 ≤ m + 1) (shiftedCode_v2 hm s)).1.Adj a b ↔
                   s(a, b) ∈ pruferDecodeEdges (by omega) (shiftedCode_v2 hm s) := by
    rw [fromEdgeSet_adj]
    -- wait, fromEdgeSet_adj has an extra a ≠ b condition.
    -- trees don't have self-loops.
    sorry

  sorry

end ProofsInTheBook.Chapter31
