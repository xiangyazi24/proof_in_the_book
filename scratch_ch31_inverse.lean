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

end ProofsInTheBook.Chapter31
