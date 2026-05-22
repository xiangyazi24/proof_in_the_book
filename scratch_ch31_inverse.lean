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

lemma L_monotone {m : ℕ} (nL : Fin (m + 2)) (a b : Fin (m + 1)) (h : a ≤ b) :
    (finSuccAboveEquivCompl nL a).1 ≤ (finSuccAboveEquivCompl nL b).1 :=
  StrictMono.monotone (Fin.strictMono_succAbove nL) h

lemma min'_congr {α : Type} [LinearOrder α] {S1 S2 : Finset α} (h : S1 = S2)
    (h1 : S1.Nonempty) (h2 : S2.Nonempty) : S1.min' h1 = S2.min' h2 := by
  subst h
  rfl

lemma min'_commutes_L {m : ℕ} (nL : Fin (m + 2))
    (S : Finset (Fin (m + 1))) (h_nonempty : S.Nonempty) :
    (finSuccAboveEquivCompl nL (S.min' h_nonempty)).1 = (S.image (fun v => (finSuccAboveEquivCompl nL v).1)).min' (Finset.Nonempty.image h_nonempty _) := by
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

lemma pruferDecodeAux_succ_step {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (k : ℕ) (hk : k + 1 ≤ n - 2) :
    let state := (pruferDecodeAux hn s k (by omega)).val
    let nL := (state.1.filter (fun v => ∀ j : Fin (n - 2), k ≤ j.val → s j ≠ v)).min' (nextLeaf_nonempty hn s k (by omega) state.1 (pruferDecodeAux hn s k (by omega)).property.2.1)
    let si := s ⟨k, by omega⟩
    (pruferDecodeAux hn s (k + 1) hk).val = (state.1.erase nL, insert s(nL, si) state.2) := rfl

private lemma nextLeaf_correspond_lift {m : ℕ} (hm : 1 ≤ m) (s : pruferCodeSpace (m + 2)) (k : ℕ)
    (hk : k + 1 ≤ m + 1 - 2)
    (ih_avail : ∀ v : Fin (m + 1),
       v ∈ (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k (by omega)).val.1 ↔
       (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) v).1 ∈ (pruferDecodeAux (by omega) s (k + 1) (by omega)).val.1) :
    let state_shifted := (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k (by omega)).val
    let state_orig := (pruferDecodeAux (by omega) s (k + 1) (by omega)).val
    let nL_k := (state_shifted.1.filter
      (fun v => ∀ j : Fin (m + 1 - 2), k ≤ j.val → shiftedCode_v2 hm s j ≠ v)).min'
      (nextLeaf_nonempty (by omega) (shiftedCode_v2 hm s) k (by omega) state_shifted.1 (pruferDecodeAux (by omega) _ k (by omega)).property.2.1)
    let nL_k' := (state_orig.1.filter
      (fun v => ∀ j : Fin (m + 2 - 2), k + 1 ≤ j.val → s j ≠ v)).min'
      (nextLeaf_nonempty (by omega) s (k + 1) (by omega) state_orig.1 (pruferDecodeAux (by omega) s (k + 1) (by omega)).property.2.1)
    (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) nL_k).1 = nL_k' := by
  intro state_shifted state_orig nL_k nL_k'
  let L := finSuccAboveEquivCompl (nextLeaf0 (by omega) s)
  let S := state_shifted.1.filter (fun v => ∀ j : Fin (m + 1 - 2), k ≤ j.val → shiftedCode_v2 hm s j ≠ v)
  let S' := state_orig.1.filter (fun v => ∀ j : Fin (m + 2 - 2), k + 1 ≤ j.val → s j ≠ v)
  have h_card_shifted : state_shifted.1.card = m + 1 - k := (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k (by omega)).property.2.1
  have h_card_orig : state_orig.1.card = m + 1 - k := by
    have h : state_orig.1.card = m + 2 - (k + 1) := (pruferDecodeAux (by omega) s (k + 1) (by omega)).property.2.1
    omega
  have h_img : state_shifted.1.image (fun v => (L v).1) = state_orig.1 := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ih_avail y |>.mp hy
    · rw [Finset.card_image_of_injective]
      · omega
      · intro y1 y2 h_eq
        have h_L : L y1 = L y2 := Subtype.ext h_eq
        exact Equiv.injective L h_L
  have h_S_eq : S.image (fun v => (L v).1) = S' := by
    ext x
    dsimp [S, S']
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨y, ⟨hy_avail, hy_not_in⟩, rfl⟩
      refine ⟨ih_avail y |>.mp hy_avail, ?_⟩
      intro j hj
      let j' : Fin (m + 1 - 2) := ⟨j.val - 1, by omega⟩
      have hj_val : j'.val = j.val - 1 := rfl
      have hj' : k ≤ j'.val := by omega
      have hy_not := hy_not_in j' hj'
      have h_shift_eval : (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) (shiftedCode_v2 hm s j')).1 = s j := by
        have h_j_eq : (⟨j'.val + 1, by omega⟩ : Fin (m + 2 - 2)) = j := by
          apply Fin.ext
          change j'.val + 1 = j.val
          omega
        dsimp [shiftedCode_v2]
        simp only [Equiv.apply_symm_apply]
        rw [h_j_eq]
      intro h_eq
      rw [← h_shift_eval] at h_eq
      have h_eq2 : L (shiftedCode_v2 hm s j') = L y := Subtype.ext h_eq
      have h_eq3 : shiftedCode_v2 hm s j' = y := Equiv.injective L h_eq2
      exact hy_not h_eq3
    · rintro ⟨hx_avail, hx_not_in⟩
      have hx_img : x ∈ state_shifted.1.image (fun v => (L v).1) := by
        rw [h_img]
        exact hx_avail
      simp only [Finset.mem_image] at hx_img
      obtain ⟨y, hy_avail, rfl⟩ := hx_img
      refine ⟨y, ⟨hy_avail, ?_⟩, rfl⟩
      intro j' hj'
      let j : Fin (m + 2 - 2) := ⟨j'.val + 1, by omega⟩
      have hj_val : j.val = j'.val + 1 := rfl
      have hj : k + 1 ≤ j.val := by omega
      have hx_not := hx_not_in j hj
      have h_shift_eval : (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) (shiftedCode_v2 hm s j')).1 = s j := by
        have h_j_eq : (⟨j'.val + 1, by omega⟩ : Fin (m + 2 - 2)) = j := by
          apply Fin.ext
          change j'.val + 1 = j.val
          omega
        dsimp [shiftedCode_v2]
        simp only [Equiv.apply_symm_apply]
        rw [h_j_eq]
      intro h_eq
      rw [h_eq] at h_shift_eval
      exact hx_not h_shift_eval.symm
  have h_min := min'_commutes_L (nextLeaf0 (by omega) s) S (nextLeaf_nonempty (by omega) (shiftedCode_v2 hm s) k (by omega) state_shifted.1 (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k (by omega)).property.2.1)
  rw [h_min]
  apply le_antisymm
  · apply Finset.le_min'
    intro y hy
    have h_eq_elem := Finset.ext_iff.mp h_S_eq y
    have hy_img := h_eq_elem.mpr hy
    exact Finset.min'_le _ _ hy_img
  · apply Finset.min'_le
    have h_nonempty_S' : S'.Nonempty := nextLeaf_nonempty (by omega) s (k + 1) (by omega) state_orig.1 (pruferDecodeAux (by omega) s (k + 1) (by omega)).property.2.1
    have h_nonempty_S_img : (S.image (fun v => (L v).1)).Nonempty := by
      rw [h_S_eq]
      exact h_nonempty_S'
    have h_mem := Finset.min'_mem (S.image (fun v => (L v).1)) h_nonempty_S_img
    have h_eq_elem := Finset.ext_iff.mp h_S_eq ((S.image (fun v => (L v).1)).min' h_nonempty_S_img)
    exact h_eq_elem.mp h_mem

lemma step_zero_min_eq_nextLeaf0 {m : ℕ} (hm : 1 ≤ m) (s : pruferCodeSpace (m + 2)) :
    ((pruferDecodeAux (by omega) s 0 (by omega)).val.1.filter (fun v => ∀ j : Fin (m + 2 - 2), 0 ≤ j.val → s j ≠ v)).min' (nextLeaf_nonempty (by omega) s 0 (by omega) (pruferDecodeAux (by omega) s 0 (by omega)).val.1 (pruferDecodeAux (by omega) s 0 (by omega)).property.2.1) = nextLeaf0 (by omega) s := by
  have h_val : (pruferDecodeAux (by omega) s 0 (by omega)).val.1 = Finset.univ := rfl
  have h_S : ((pruferDecodeAux (by omega) s 0 (by omega)).val.1.filter (fun v => ∀ j : Fin (m + 2 - 2), 0 ≤ j.val → s j ≠ v)) = Finset.univ.filter (fun v => ∀ j : Fin (m + 2 - 2), s j ≠ v) := by
    rw [h_val]
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j
      exact h j (by omega)
    · intro h j _
      exact h j
  dsimp [nextLeaf0, smallestTreeLeaf]
  apply le_antisymm
  · apply Finset.le_min'
    intro y hy
    rw [pruferDecode_isLeaf_iff] at hy
    have h_univ : y ∈ Finset.univ.filter (fun v => ∀ j : Fin (m + 2 - 2), s j ≠ v) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hy
    have hy' := Finset.ext_iff.mp h_S y |>.mpr h_univ
    exact Finset.min'_le _ _ hy'
  · apply Finset.min'_le
    set m_elem := ((pruferDecodeAux (by omega) s 0 (by omega)).val.1.filter (fun v => ∀ j : Fin (m + 2 - 2), 0 ≤ j.val → s j ≠ v)).min' (nextLeaf_nonempty (by omega) s 0 (by omega) (pruferDecodeAux (by omega) s 0 (by omega)).val.1 (pruferDecodeAux (by omega) s 0 (by omega)).property.2.1)
    have hy := Finset.min'_mem _ (nextLeaf_nonempty (by omega) s 0 (by omega) (pruferDecodeAux (by omega) s 0 (by omega)).val.1 (pruferDecodeAux (by omega) s 0 (by omega)).property.2.1)
    have h_univ : m_elem ∈ Finset.univ.filter (fun v => ∀ j : Fin (m + 2 - 2), s j ≠ v) := Finset.ext_iff.mp h_S m_elem |>.mp hy
    rw [Finset.mem_filter] at h_univ
    rw [pruferDecode_isLeaf_iff]
    exact h_univ.2

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
    intro hk
    constructor
    · intro v
      have h_step_orig := pruferDecodeAux_succ_step (by omega) s 0 (by omega)
      have h_state0_orig : (pruferDecodeAux (by omega) s 0 (by omega)).val = (Finset.univ, ∅) := rfl
      have h_state0_shift : (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) 0 hk).val = (Finset.univ, ∅) := rfl
      have h_nL_eq := step_zero_min_eq_nextLeaf0 hm s
      let L := finSuccAboveEquivCompl (nextLeaf0 (by omega) s)
      rw [h_state0_shift]
      have h_orig1 : (pruferDecodeAux (by omega) s 1 (by omega)).val.1 = Finset.univ.erase (nextLeaf0 (by omega) s) := by
        rw [h_step_orig]
        dsimp
        rw [h_nL_eq]
        rw [h_state0_orig]
      rw [h_orig1]
      simp only [Finset.mem_univ, Finset.mem_erase, ne_eq, and_true]
      exact iff_of_true trivial (L v).property
    · intro a b
      have h_step_orig := pruferDecodeAux_succ_step (by omega) s 0 (by omega)
      have h_state0_orig : (pruferDecodeAux (by omega) s 0 (by omega)).val = (Finset.univ, ∅) := rfl
      have h_state0_shift : (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) 0 hk).val = (Finset.univ, ∅) := rfl
      have h_nL_eq := step_zero_min_eq_nextLeaf0 hm s
      let L := finSuccAboveEquivCompl (nextLeaf0 (by omega) s)
      rw [h_state0_shift]
      have h_orig1 : (pruferDecodeAux (by omega) s 1 (by omega)).val.2 = {s(nextLeaf0 (by omega) s, s ⟨0, by omega⟩)} := by
        rw [h_step_orig]
        dsimp
        rw [h_nL_eq]
        rw [h_state0_orig]
        rfl
      rw [h_orig1]
      simp only [Finset.mem_singleton, Sym2.eq_iff]
      constructor
      · intro h_empty
        revert h_empty
        simp
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact (L a).property h1 |>.elim
        · exact (L b).property h2 |>.elim
  | succ k ih =>
    intro hk
    have hm1 : m + 1 - 2 = m - 1 := by omega
    have hm2 : m + 2 - 2 = m := by omega
    have hk_curr : k + 1 ≤ m + 1 - 2 := hk
    have hk_prev : k ≤ m + 1 - 2 := by omega
    have hk_next : k + 2 ≤ m + 2 - 2 := by omega
    have hk_next_orig : k + 1 ≤ m + 2 - 2 := by omega
    have ih_k := ih hk_prev
    have ih_avail := ih_k.1
    have ih_edges := ih_k.2
    
    let state_shifted := (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k hk_prev).val
    let state_orig := (pruferDecodeAux (by omega) s (k + 1) hk_next_orig).val
    let L := finSuccAboveEquivCompl (nextLeaf0 (by omega) s)
    
    have h_step_shift := pruferDecodeAux_succ_step (by omega) (shiftedCode_v2 hm s) k hk_curr
    have h_step_orig := pruferDecodeAux_succ_step (by omega) s (k + 1) hk_next
    
    have h_nL_eq := nextLeaf_correspond_lift hm s k hk_curr ih_avail
    have h_nonempty_shift := nextLeaf_nonempty (by omega) (shiftedCode_v2 hm s) k hk_prev state_shifted.1 (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k hk_prev).property.2.1
    have h_nonempty_orig := nextLeaf_nonempty (by omega) s (k + 1) hk_next_orig state_orig.1 (pruferDecodeAux (by omega) s (k + 1) hk_next_orig).property.2.1
    set nL_k := (state_shifted.1.filter (fun v => ∀ j : Fin (m + 1 - 2), k ≤ j.val → shiftedCode_v2 hm s j ≠ v)).min' h_nonempty_shift
    set nL_k' := (state_orig.1.filter (fun v => ∀ j : Fin (m + 2 - 2), k + 1 ≤ j.val → s j ≠ v)).min' h_nonempty_orig
    have h_L_nL : (L nL_k).1 = nL_k' := h_nL_eq
    
    constructor
    · intro v
      have h_shift_val : (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) (k + 1) hk_curr).val.1 = state_shifted.1.erase nL_k := by
        rw [h_step_shift]
      have h_orig_val : (pruferDecodeAux (by omega) s (k + 2) hk_next).val.1 = state_orig.1.erase nL_k' := by
        rw [h_step_orig]
      rw [h_shift_val, h_orig_val]
      simp only [Finset.mem_erase, ne_eq]
      rw [ih_avail v]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        intro h_eq
        have h_L_eq : (L v).1 = (L nL_k).1 := by
          rw [h_eq, h_L_nL]
        have h_v_eq := Equiv.injective L (Subtype.ext h_L_eq)
        exact h1 h_v_eq
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        intro h_eq
        have h_L_eq : (L v).1 = nL_k' := by
          rw [h_eq, h_L_nL]
        exact h1 h_L_eq
    · intro a b
      have h_shift_val : (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) (k + 1) hk_curr).val.2 = insert s(nL_k, shiftedCode_v2 hm s ⟨k, by omega⟩) state_shifted.2 := by
        rw [h_step_shift]
      have h_orig_val : (pruferDecodeAux (by omega) s (k + 2) hk_next).val.2 = insert s(nL_k', s ⟨k + 1, by omega⟩) state_orig.2 := by
        rw [h_step_orig]
      rw [h_shift_val, h_orig_val]
      rw [Finset.mem_insert, Finset.mem_insert]
      rw [ih_edges a b]
      have hk_lt1 : k < m + 1 - 2 := by omega
      have hk_lt2 : k + 1 < m + 2 - 2 := by omega
      have h_shift_code_eval : (L (shiftedCode_v2 hm s ⟨k, hk_lt1⟩)).1 = s ⟨k + 1, hk_lt2⟩ := by
        dsimp [L, shiftedCode_v2]
        simp only [Equiv.apply_symm_apply]
      have h_edge_eq : s((L a).1, (L b).1) = s(nL_k', s ⟨k + 1, hk_lt2⟩) ↔ s(a, b) = s(nL_k, shiftedCode_v2 hm s ⟨k, hk_lt1⟩) := by
        simp only [Sym2.eq_iff]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · left
            constructor
            · have h_ext : L a = L nL_k := Subtype.ext (by rw [h1, ← h_L_nL])
              exact Equiv.injective L h_ext
            · have h_ext : L b = L (shiftedCode_v2 hm s ⟨k, by omega⟩) := Subtype.ext (by rw [h2, ← h_shift_code_eval])
              exact Equiv.injective L h_ext
          · right
            constructor
            · have h_ext : L a = L (shiftedCode_v2 hm s ⟨k, by omega⟩) := Subtype.ext (by rw [h1, ← h_shift_code_eval])
              exact Equiv.injective L h_ext
            · have h_ext : L b = L nL_k := Subtype.ext (by rw [h2, ← h_L_nL])
              exact Equiv.injective L h_ext
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · left
            constructor
            · rw [h1, h_L_nL]
            · rw [h2, h_shift_code_eval]
          · right
            constructor
            · rw [h1, h_shift_code_eval]
            · rw [h2, h_L_nL]
      rw [h_edge_eq]

lemma deleteSmallestLeafTreeSucc_val_adj {m : ℕ} (hm : 1 ≤ m) (T : LabeledTree (m + 1)) (a b : Fin m) :
    (↑(deleteSmallestLeafTreeSucc m hm T) : SimpleGraph (Fin m)).Adj a b ↔
    (↑T : SimpleGraph (Fin (m + 1))).Adj ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) a).1
            ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) b).1 := by
  dsimp [deleteSmallestLeafTreeSucc]
  simp only [SimpleGraph.comap_adj, Function.Embedding.coeFn_mk, SimpleGraph.induce_adj, Set.mem_compl_iff, Set.mem_singleton_iff]
  have h_a : ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) a).1 ≠ smallestTreeLeaf (m + 1) (by omega) T :=
    ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) a).2
  have h_b : ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) b).1 ≠ smallestTreeLeaf (m + 1) (by omega) T :=
    ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) b).2
  tauto

lemma pruferDecodeAux_val_1_congr {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) {k1 k2 : ℕ} (hk1 : k1 ≤ n - 2) (hk2 : k2 ≤ n - 2) (h : k1 = k2) :
    (pruferDecodeAux hn s k1 hk1).val.1 = (pruferDecodeAux hn s k2 hk2).val.1 := by
  subst h; rfl

lemma pruferDecodeAux_val_2_congr {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) {k1 k2 : ℕ} (hk1 : k1 ≤ n - 2) (hk2 : k2 ≤ n - 2) (h : k1 = k2) :
    (pruferDecodeAux hn s k1 hk1).val.2 = (pruferDecodeAux hn s k2 hk2).val.2 := by
  subst h; rfl

lemma pruferDecodeAux_val_1_subset {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) {k1 k2 : ℕ} (hk1 : k1 ≤ n - 2) (hk2 : k2 ≤ n - 2) (hle : k1 ≤ k2) :
    (pruferDecodeAux hn s k2 hk2).val.1 ⊆ (pruferDecodeAux hn s k1 hk1).val.1 := by
  revert hk2
  induction hle with
  | refl =>
    intro hk2 x hx
    exact hx
  | @step k_mid h_le ih =>
    intro hk2
    have hk_succ : k_mid + 1 ≤ n - 2 := hk2
    have hk_mid : k_mid ≤ n - 2 := by omega
    have h_ih := ih hk_mid
    have h_eq := pruferDecodeAux_succ_step hn s k_mid hk_succ
    have h_c := pruferDecodeAux_val_1_congr hn s (by omega : k_mid + 1 ≤ n - 2) hk2 rfl
    rw [← h_c]
    have h_val : (pruferDecodeAux hn s (k_mid + 1) hk_succ).val.1 = (pruferDecodeAux hn s k_mid hk_mid).val.1.erase _ := congrArg Prod.fst h_eq
    rw [h_val]
    intro x hx
    have h_erase := Finset.erase_subset _ _ hx
    exact h_ih h_erase

theorem deleteSmallestLeaf_pruferDecode_v2 {m : ℕ} (hm : 1 ≤ m)
    (s : pruferCodeSpace (m + 2)) :
    deleteSmallestLeafTreeSucc (m + 1) (by omega) (pruferDecode (by omega) s) =
    pruferDecode (by omega : 2 ≤ m + 1) (shiftedCode_v2 hm s) := by
  ext a b
  let shift_s := shiftedCode_v2 hm s
  have hn_shift : 2 ≤ m + 1 := by omega
  have hn_s : 2 ≤ m + 2 := by omega
  have hm_sub : m - 1 ≤ (m + 1) - 2 := by omega
  have h_corr := pruferDecodeAux_shifted_correspondence hm s (m - 1) hm_sub
  have h_corr_v := h_corr.1
  have h_corr_e := h_corr.2
  
  have h_state_shift : (pruferFinalState hn_shift shift_s).1 = (pruferDecodeAux hn_shift shift_s (m - 1) hm_sub).val.1 := rfl
  have h_state_s : (pruferFinalState hn_s s).1 = (pruferDecodeAux hn_s s m (by omega)).val.1 := by
    have h_idx : m + 2 - 2 = m := by omega
    exact pruferDecodeAux_val_1_congr hn_s s (by omega) (by omega) h_idx
  
  have h_image_eq : (pruferFinalState hn_shift shift_s).1.image (fun v => (finSuccAboveEquivCompl (nextLeaf0 hn_s s) v).1) = (pruferFinalState hn_s s).1 := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have h_corr_v_spec := h_corr_v v
      have h_s_eq : (pruferDecodeAux hn_s s (m - 1 + 1) (by omega)).val.1 = (pruferFinalState hn_s s).1 := by
        have h_idx : m - 1 + 1 = m + 2 - 2 := by omega
        exact pruferDecodeAux_val_1_congr hn_s s (by omega) (by omega) h_idx
      rw [h_s_eq] at h_corr_v_spec
      exact h_corr_v_spec.mp hv
    · intro hx
      have h_not_nL : x ≠ nextLeaf0 hn_s s := by
        have h_leaf_mem : nextLeaf0 hn_s s ∈ (pruferDecodeAux hn_s s 0 (by omega)).val.1 := Finset.mem_univ _
        have h_not_in_final : nextLeaf0 hn_s s ∉ (pruferFinalState hn_s s).1 := by
          have h_s_eq : (pruferFinalState hn_s s).1 = (pruferDecodeAux hn_s s (m + 2 - 2) (by omega)).val.1 := rfl
          rw [h_s_eq]
          have h_erase : (pruferDecodeAux hn_s s 1 (by omega)).val.1 = Finset.univ.erase (nextLeaf0 hn_s s) := by
            have h_eq := pruferDecodeAux_succ_step hn_s s 0 (by omega)
            dsimp at h_eq
            have h_min_eq := step_zero_min_eq_nextLeaf0 hm s
            rw [h_min_eq] at h_eq
            exact congrArg Prod.fst h_eq
          have h_subset := pruferDecodeAux_val_1_subset hn_s s (by omega) (by omega) (by omega : 1 ≤ m + 2 - 2)
          intro h_mem
          have h_mem_erase := h_subset h_mem
          rw [h_erase] at h_mem_erase
          simp only [Finset.mem_erase, ne_eq] at h_mem_erase
          exact h_mem_erase.1 trivial
        rintro rfl
        exact h_not_in_final hx
      have h_mem_compl : x ∈ ({nextLeaf0 hn_s s}ᶜ : Set (Fin (m + 2))) := h_not_nL
      let x_lift : {v // v ∈ ({nextLeaf0 hn_s s}ᶜ : Set (Fin (m + 2)))} := ⟨x, h_mem_compl⟩
      use (finSuccAboveEquivCompl (nextLeaf0 hn_s s)).symm x_lift
      constructor
      · have h_corr_v_spec := h_corr_v ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)).symm x_lift)
        have h_s_eq : (pruferDecodeAux hn_s s (m - 1 + 1) (by omega)).val.1 = (pruferFinalState hn_s s).1 := by
          have h_idx : m - 1 + 1 = m + 2 - 2 := by omega
          exact pruferDecodeAux_val_1_congr hn_s s (by omega) (by omega) h_idx
        rw [h_s_eq] at h_corr_v_spec
        apply h_corr_v_spec.mpr
        have h_eval : ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)).symm x_lift)).1 = x := by
          have h1 := Equiv.apply_symm_apply (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) x_lift
          rw [h1]
        rw [h_eval]
        exact hx
      · have h_eval : ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)).symm x_lift)).1 = x := by
          have h1 := Equiv.apply_symm_apply (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) x_lift
          rw [h1]
        exact h_eval

  have h_U_eq : ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastU hn_shift shift_s)).1 = pruferLastU hn_s s := by
    have h_min := min'_commutes_L (nextLeaf0 hn_s s) (pruferFinalState hn_shift shift_s).1 (pruferFinalState_nonempty hn_shift shift_s)
    have h_congr := min'_congr h_image_eq (Finset.Nonempty.image (pruferFinalState_nonempty hn_shift shift_s) _) (pruferFinalState_nonempty hn_s s)
    exact h_min.trans h_congr

  have h_erase_image : ((pruferFinalState hn_shift shift_s).1.erase (pruferLastU hn_shift shift_s)).image (fun v => ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) v).1) = (pruferFinalState hn_s s).1.erase (pruferLastU hn_s s) := by
    have h_im := h_image_eq
    ext x
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨v, ⟨hv_ne, hv_mem⟩, rfl⟩
      constructor
      · intro h_eq
        have h_eq_val : ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) v).1 = ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastU hn_shift shift_s)).1 := by
          rw [h_eq, h_U_eq]
        have h_inj := (finSuccAboveEquivCompl (nextLeaf0 hn_s s)).injective
        have h_eq_v := h_inj (Subtype.ext h_eq_val)
        exact hv_ne h_eq_v
      · rw [← h_im]
        simp only [Finset.mem_image]
        exact ⟨v, hv_mem, rfl⟩
    · rintro ⟨hx_ne, hx_mem⟩
      rw [← h_im] at hx_mem
      simp only [Finset.mem_image] at hx_mem
      rcases hx_mem with ⟨v, hv_mem, rfl⟩
      use v
      refine ⟨⟨?_, hv_mem⟩, rfl⟩
      intro h_eq_v
      rw [h_eq_v] at hx_ne
      exact hx_ne h_U_eq

  have h_V_eq : ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastV hn_shift shift_s)).1 = pruferLastV hn_s s := by
    have h_min := min'_commutes_L (nextLeaf0 hn_s s) ((pruferFinalState hn_shift shift_s).1.erase (pruferLastU hn_shift shift_s)) (pruferFinalErase_nonempty hn_shift shift_s)
    have h_congr := min'_congr h_erase_image (Finset.Nonempty.image (pruferFinalErase_nonempty hn_shift shift_s) _) (pruferFinalErase_nonempty hn_s s)
    exact h_min.trans h_congr

  have h_edges_corr : s(a, b) ∈ (pruferFinalState hn_shift shift_s).2 ↔ s(((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a).1, ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b).1) ∈ (pruferFinalState hn_s s).2 := by
    have h_corr_e_spec := h_corr_e a b
    have h_s_eq : (pruferDecodeAux hn_s s (m - 1 + 1) (by omega)).val.2 = (pruferFinalState hn_s s).2 := by
      have h_idx : m - 1 + 1 = m + 2 - 2 := by omega
      exact pruferDecodeAux_val_2_congr hn_s s (by omega) (by omega) h_idx
    rw [h_s_eq] at h_corr_e_spec
    exact h_corr_e_spec

  rw [deleteSmallestLeafTreeSucc_val_adj]
  dsimp [pruferDecode]
  simp only [SimpleGraph.fromEdgeSet_adj]
  
  change s(((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a).1, ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b).1) ∈ pruferDecodeEdges hn_s s ∧
    ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a).1 ≠ ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b).1 ↔
    s(a, b) ∈ pruferDecodeEdges hn_shift shift_s ∧ a ≠ b
  
  have h_ne_iff : (((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a).1 ≠ ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b).1) ↔ (a ≠ b) := by
    constructor
    · intro h h_eq
      rw [h_eq] at h
      exact h rfl
    · intro h h_eq
      have h_inj := (finSuccAboveEquivCompl (nextLeaf0 hn_s s)).injective
      have h_eq_v := Subtype.ext h_eq
      have h_eq_a := h_inj h_eq_v
      exact h h_eq_a
  
  rw [h_ne_iff]
  
  dsimp [pruferDecodeEdges]
  simp only [Finset.mem_insert]
  
  constructor
  · rintro ⟨(h_eq | h_mem), h_ne⟩
    · refine ⟨?_, h_ne⟩
      left
      simp only [Sym2.eq_iff] at h_eq ⊢
      rcases h_eq with (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left
        have h_ext_a : (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a = (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastU hn_shift shift_s) := Subtype.ext (by rw [h1, ← h_U_eq])
        have h_ext_b : (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b = (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastV hn_shift shift_s) := Subtype.ext (by rw [h2, ← h_V_eq])
        exact ⟨Equiv.injective _ h_ext_a, Equiv.injective _ h_ext_b⟩
      · right
        have h_ext_a : (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a = (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastV hn_shift shift_s) := Subtype.ext (by rw [h1, ← h_V_eq])
        have h_ext_b : (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b = (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastU hn_shift shift_s) := Subtype.ext (by rw [h2, ← h_U_eq])
        exact ⟨Equiv.injective _ h_ext_a, Equiv.injective _ h_ext_b⟩
    · refine ⟨?_, h_ne⟩
      right
      exact h_edges_corr.mpr h_mem
  · rintro ⟨(h_eq | h_mem), h_ne⟩
    · refine ⟨?_, h_ne⟩
      left
      simp only [Sym2.eq_iff] at h_eq ⊢
      rcases h_eq with (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left
        rw [h1, h2, h_U_eq, h_V_eq]
        exact ⟨rfl, rfl⟩
      · right
        rw [h1, h2, h_U_eq, h_V_eq]
        exact ⟨rfl, rfl⟩
    · refine ⟨?_, h_ne⟩
      right
      exact h_edges_corr.mp h_mem

lemma leftInverse_pruferDecode_aux
    (h_correspondence : ∀ (m' : ℕ) (hm' : 1 ≤ m') (s : pruferCodeSpace (m' + 2)),
       deleteSmallestLeafTreeSucc (m' + 1) (by omega) (pruferDecode (by omega) s) =
       pruferDecode (by omega : 2 ≤ m' + 1) (shiftedCode_v2 hm' s)) :
    ∀ (m : ℕ) (s : pruferCodeSpace (m + 2)), pruferEncodeAux m (pruferDecode (by omega) s) = s := by
  intro m
  induction m with
  | zero =>
    intro s
    ext i
    exact Fin.elim0 i
  | succ m ih =>
    intro s
    funext i
    by_cases h0 : i.val = 0
    · have hi : i = ⟨0, by omega⟩ := Fin.ext h0
      rw [hi]
      have h_zero := pruferEncode_pruferDecode_zero (m + 3) (by omega) s (by omega)
      exact h_zero
    · have hm1 : 1 ≤ m + 1 := by omega
      let leaf := smallestTreeLeaf (m + 3) (by omega) (pruferDecode (by omega) s)
      let T' := deleteSmallestLeafTreeSucc (m + 2) (by omega) (pruferDecode (by omega) s)
      have hT' : T' = pruferDecode (by omega) (shiftedCode_v2 hm1 s) := h_correspondence (m + 1) hm1 s
      
      have h_eval : (pruferEncodeAux (m + 1) (pruferDecode (by omega) s)) i =
          ((finSuccAboveEquivCompl leaf) (pruferEncodeAux m T' ⟨i.val - 1, by omega⟩)).1 := by
        dsimp [pruferEncodeAux]
        have h_pos : 0 < i.val := Nat.pos_of_ne_zero h0
        rw [dif_neg h0]
        
      rw [h_eval, hT']
      have h_ih := ih (shiftedCode_v2 hm1 s)
      have h_inner : pruferEncodeAux m (pruferDecode (by omega) (shiftedCode_v2 hm1 s)) ⟨i.val - 1, by omega⟩ =
          shiftedCode_v2 hm1 s ⟨i.val - 1, by omega⟩ := by
        rw [h_ih]
        rfl
      rw [h_inner]
      
      have h_leaf_eq : leaf = nextLeaf0 (by omega) s := rfl
      rw [h_leaf_eq]
      
      have h_i_pos : 1 ≤ i.val := Nat.pos_of_ne_zero h0
      have h_j_lt : i.val - 1 < m := by omega
      let j' : Fin m := ⟨i.val - 1, h_j_lt⟩
      let L := finSuccAboveEquivCompl (nextLeaf0 (by omega) s)
      have h_shift_def : shiftedCode_v2 hm1 s j' =
          L.symm ⟨s i, nextLeaf0_not_in_image (by omega) s i⟩ := by
        dsimp [shiftedCode_v2]
        congr 1
        congr 1
        congr 1
        apply Fin.ext
        exact Nat.sub_add_cancel h_i_pos
      have h_L_app : (L (shiftedCode_v2 hm1 s j')).1 = s i := by
        rw [h_shift_def]
        simp only [Equiv.apply_symm_apply]
      exact h_L_app

-- Tier 1.5: take the structural correspondence as hypothesis.
theorem chapter31_tier2_of_correspondence {n : ℕ} (hn : 2 ≤ n)
    (h_correspondence : ∀ (m : ℕ) (hm : 1 ≤ m) (s : pruferCodeSpace (m + 2)),
       deleteSmallestLeafTreeSucc (m + 1) (by omega)
         (pruferDecode (by omega) s) =
       pruferDecode (by omega : 2 ≤ m + 1) (shiftedCode_v2 hm s)) :
    Fintype.card (LabeledTree n) = n ^ (n - 2) := by
  have h_left_inv : Function.LeftInverse (pruferEncode hn) (pruferDecode hn) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    intro s
    exact leftInverse_pruferDecode_aux h_correspondence m s
  have h_inj : Function.Injective (pruferDecode hn) := h_left_inv.injective
  -- cardinality of range = cardinality of domain
  have h_card_eq_ineq : Fintype.card (pruferCodeSpace n) ≤ Fintype.card (LabeledTree n) := Fintype.card_le_of_injective _ h_inj
  rw [pruferCodeSpace_card n] at h_card_eq_ineq
  have h_card_le := cayley_upper_bound n hn
  exact le_antisymm h_card_le h_card_eq_ineq

end ProofsInTheBook.Chapter31
