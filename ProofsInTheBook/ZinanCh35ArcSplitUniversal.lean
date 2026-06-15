import ProofsInTheBook.ZinanCh35BoundaryAssembler

/-!
# Chapter 35 — the universal arc-split from `VertexNodup` (positive non-vacuity keystone)

`ZinanCh35BoundaryAssembler.BoundaryCycle.arcSplit_of_nodup_nonBoundaryEdge` already builds a
`BoundaryArcSplit` for any **non-adjacent** pair from `VertexNodup`. After the foundation fix that
made `BoundaryArcSplit.path*_internal_of_proper` one-directional, the **adjacent** case is also
satisfiable (the long complementary arc may carry internal vertices; the short edge arc need not).

This file delivers the **universal** producer

  `arcSplit_of_nodup (C) (hC : C.VertexNodup) {u v} (u ≠ v) (u,v ∈ vertices)
     : BoundaryArcSplit M C.vertices C.edges u v`

for **every** distinct boundary-vertex pair, from `VertexNodup` ALONE — discharging the
`BoundaryCycle.arcSplit` field (which quantifies over all distinct pairs) as a *consequence* of
simplicity, not as primitive Jordan data. Hence `arcSplit` was never genuine discrete-Schoenflies
content: any simple boundary cycle has it for free.

The construction merges the two complementary cyclic runs of `nonEdgeRuns` with the field assembly
of `arcSplit_of_nodup_nonBoundaryEdge`; the only difference is that the non-adjacency fact `hnbe`
is moved *out of the parameters and into the two `internal_of_proper` field proofs* (each derives
its run length `≥ 2` from `proper`, which is exactly when an internal vertex is required).

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ArcSplitUniversal

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ZinanCh35Aligned
open ProofsInTheBook.ZinanCh35BoundaryAssembler
open ProofsInTheBook.ZinanCh35BoundaryAssembler.BoundaryCycle

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D} {f : M.Face}

/-- **The universal arc-split from `VertexNodup`.** For any two distinct listed boundary vertices
`u, v` (no adjacency restriction), the two complementary cyclic runs assemble a
`BoundaryArcSplit M C.vertices C.edges u v`. Pure list combinatorics from simplicity. -/
noncomputable def arcSplit_of_nodup (C : BoundaryCycle M f) (hC : C.VertexNodup)
    {u v : M.Vertex} (hne : u ≠ v)
    (hu : C.IsBoundaryVertex u) (hv : C.IsBoundaryVertex v) :
    BoundaryArcSplit M C.vertices C.edges u v := by
  classical
  set L := C.darts.length with hL
  have hLpos : 0 < L := C.darts_length_pos
  set puF := (C.exists_pos_of_isBoundaryVertex hu).choose with hpuF
  have eu0 := (C.exists_pos_of_isBoundaryVertex hu).choose_spec
  set pvF := (C.exists_pos_of_isBoundaryVertex hv).choose with hpvF
  have ev0 := (C.exists_pos_of_isBoundaryVertex hv).choose_spec
  set pu := puF.1 with hpuval
  set pv := pvF.1 with hpvval
  have hpu : pu < L := puF.2
  have hpv : pv < L := pvF.2
  have eu : M.tail (C.darts[pu]'hpu) = u := eu0
  have ev : M.tail (C.darts[pv]'hpv) = v := ev0
  have hpune : pu ≠ pv := by
    intro hpe; apply hne
    rw [← eu, ← ev]
    have : C.darts[pu]'hpu = C.darts[pv]'hpv := getElem_congr rfl hpe hpu
    rw [this]
  set kf := (pv + L - pu) % L with hkf
  set kb := (pu + L - pv) % L with hkb
  obtain ⟨hkf1, hkb1, hsum, hpfkf, hcov⟩ :=
    ZinanCh35Aligned.mod_cover L pu pv hLpos hpu hpv hpune kf kb hkf hkb
  obtain ⟨_, _, _, hpvkb, _⟩ :=
    ZinanCh35Aligned.mod_cover L pv pu hLpos hpv hpu (Ne.symm hpune) kb kf hkb hkf
  have hkfL : kf < L := by rw [hkf]; exact Nat.mod_lt _ hLpos
  have hkbL : kb < L := by rw [hkb]; exact Nat.mod_lt _ hLpos
  set AUV := C.cyclicDartArc hC pu kf hkf1 hkfL hpu with hAUV
  set AVU := C.cyclicDartArc hC pv kb hkb1 hkbL hpv with hAVU
  have euv2 : M.tail (C.darts[(pu + kf) % L]'(Nat.mod_lt _ (by omega))) = v := by
    have : C.darts[(pu + kf) % L]'(Nat.mod_lt _ (by omega)) = C.darts[pv]'hpv := by congr 1
    rw [this]; exact ev
  have evu2 : M.tail (C.darts[(pv + kb) % L]'(Nat.mod_lt _ (by omega))) = u := by
    have : C.darts[(pv + kb) % L]'(Nat.mod_lt _ (by omega)) = C.darts[pu]'hpu := by congr 1
    rw [this]; exact eu
  have htailUV : ∀ i : Fin (daCast AUV eu euv2).len,
      M.tail ((daCast AUV eu euv2).arcDart i)
        = M.tail (C.darts[(pu + i.1) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i; exact daCast_cyclic_tail C hC pu kf hkf1 hkfL hpu eu euv2 i
  have htailVU : ∀ i : Fin (daCast AVU ev evu2).len,
      M.tail ((daCast AVU ev evu2).arcDart i)
        = M.tail (C.darts[(pv + i.1) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i; exact daCast_cyclic_tail C hC pv kb hkb1 hkbL hpv ev evu2 i
  have htailUV_fwd : ∀ j : ℕ, (hj : j < kf) →
      ∃ i : Fin (daCast AUV eu euv2).len,
        M.tail ((daCast AUV eu euv2).arcDart i)
          = M.tail (C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro j hj
    have hjlen : j < (daCast AUV eu euv2).len := by rw [daCast_len]; exact hj
    exact ⟨⟨j, hjlen⟩, htailUV ⟨j, hjlen⟩⟩
  have htailVU_fwd : ∀ j : ℕ, (hj : j < kb) →
      ∃ i : Fin (daCast AVU ev evu2).len,
        M.tail ((daCast AVU ev evu2).arcDart i)
          = M.tail (C.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro j hj
    have hjlen : j < (daCast AVU ev evu2).len := by rw [daCast_len]; exact hj
    exact ⟨⟨j, hjlen⟩, htailVU ⟨j, hjlen⟩⟩
  have htailUV_bwd : ∀ i : Fin (daCast AUV eu euv2).len,
      ∃ j : ℕ, j < kf ∧
        M.tail ((daCast AUV eu euv2).arcDart i)
          = M.tail (C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i
    have hi : i.1 < kf := lt_of_lt_of_eq i.2 (daCast_len AUV eu euv2)
    exact ⟨i.1, hi, htailUV i⟩
  have htailVU_bwd : ∀ i : Fin (daCast AVU ev evu2).len,
      ∃ j : ℕ, j < kb ∧
        M.tail ((daCast AVU ev evu2).arcDart i)
          = M.tail (C.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i
    have hi : i.1 < kb := lt_of_lt_of_eq i.2 (daCast_len AVU ev evu2)
    exact ⟨i.1, hi, htailVU i⟩
  -- covering and disjointness of the two runs' tails (no length-≥2 needed)
  have hmap : (C.darts.map M.tail).Nodup := by
    have := hC; rwa [BoundaryCycle.VertexNodup, C.vertices_eq] at this
  have covering : ∀ {w : M.Vertex}, C.IsBoundaryVertex w →
      (∃ i, M.tail ((daCast AUV eu euv2).arcDart i) = w) ∨
      (∃ i, M.tail ((daCast AVU ev evu2).arcDart i) = w) ∨ w = u ∨ w = v := by
    intro w hw
    obtain ⟨q, hqt⟩ := C.exists_pos_of_isBoundaryVertex hw
    rcases hcov q.1 q.2 with ⟨j, hj, hjq⟩ | ⟨j, hj, hjq⟩
    · left
      obtain ⟨i, hi⟩ := htailUV_fwd j hj
      refine ⟨i, ?_⟩
      rw [hi]
      have : C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)) = C.darts[q.1]'q.2 :=
        getElem_congr rfl hjq _
      rw [this, hqt]
    · right; left
      obtain ⟨i, hi⟩ := htailVU_fwd j hj
      refine ⟨i, ?_⟩
      rw [hi]
      have : C.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega)) = C.darts[q.1]'q.2 :=
        getElem_congr rfl hjq _
      rw [this, hqt]
  have disjoint : ∀ {w : M.Vertex},
      (∃ i, M.tail ((daCast AUV eu euv2).arcDart i) = w) →
      (∃ i, M.tail ((daCast AVU ev evu2).arcDart i) = w) → w = u ∨ w = v := by
    rintro w ⟨i, hiw⟩ ⟨i', hi'w⟩
    obtain ⟨j, hj, hjeq⟩ := htailUV_bwd i
    obtain ⟨j', hj', hj'eq⟩ := htailVU_bwd i'
    have heq : M.tail (C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)))
        = M.tail (C.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega))) := by
      rw [← hjeq, ← hj'eq, hiw, hi'w]
    have hposeq : (pu + j) % L = (pv + j') % L := by
      have hmem1 : C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)) ∈ C.darts :=
        List.getElem_mem _
      have hmem2 : C.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega)) ∈ C.darts :=
        List.getElem_mem _
      have hdarts : C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))
          = C.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega)) :=
        List.inj_on_of_nodup_map hmap hmem1 hmem2 heq
      exact (C.normalized.nodup.getElem_inj_iff).mp hdarts
    by_cases hj0 : j = 0
    · left
      rw [← hiw, hjeq, hj0]
      simp only [Nat.add_zero, Nat.mod_eq_of_lt hpu]
      exact eu
    · by_cases hj'0 : j' = 0
      · right
        rw [← hi'w, hj'eq, hj'0]
        simp only [Nat.add_zero, Nat.mod_eq_of_lt hpv]
        exact ev
      · exfalso
        have hpvmod : pv % L = (pu + kf) % L := by rw [hpfkf, Nat.mod_eq_of_lt hpv]
        have h2 : Nat.ModEq L pv (pu + kf) := by
          show pv % L = (pu + kf) % L; exact hpvmod
        have hcong : Nat.ModEq L (pu + j) (pu + (kf + j')) := by
          have h1 : Nat.ModEq L (pu + j) (pv + j') := hposeq
          have h3 : Nat.ModEq L (pv + j') (pu + kf + j') := h2.add_right j'
          have h4 : Nat.ModEq L (pu + j) (pu + kf + j') := h1.trans h3
          rwa [show pu + kf + j' = pu + (kf + j') from by ring] at h4
        have hcong' : Nat.ModEq L j (kf + j') := Nat.ModEq.add_left_cancel' pu hcong
        have hjlt : j < L := by omega
        have hkfj' : kf + j' < L := by omega
        have : j = kf + j' := by
          have hj1 : j % L = j := Nat.mod_eq_of_lt hjlt
          have hj2 : (kf + j') % L = kf + j' := Nat.mod_eq_of_lt hkfj'
          rw [Nat.ModEq, hj1, hj2] at hcong'; exact hcong'
        omega
  -- length-≥2 from non-adjacency (only needed inside `internal_of_proper`)
  have hkf2_of_proper : ¬ C.IsBoundaryEdge s(u, v) → 2 ≤ kf := by
    intro hnbe
    rcases Nat.lt_or_ge kf 2 with hlt | hge
    · exfalso
      have hkf1' : kf = 1 := by omega
      apply not_consecutive_of_nonBoundaryEdge C hnbe hpu hpv eu ev
      rw [show (pu + 1) % L = (pu + kf) % L from by rw [hkf1'], hpfkf]
    · exact hge
  have hkb2_of_proper : ¬ C.IsBoundaryEdge s(u, v) → 2 ≤ kb := by
    intro hnbe
    rcases Nat.lt_or_ge kb 2 with hlt | hge
    · exfalso
      have hkb1' : kb = 1 := by omega
      have hnbe' : ¬ C.IsBoundaryEdge s(v, u) := by rw [Sym2.eq_swap]; exact hnbe
      exact not_consecutive_of_nonBoundaryEdge C hnbe' hpv hpu ev eu
        (by rw [show (pv + 1) % L = (pv + kb) % L from by rw [hkb1'], hpvkb])
    · exact hge
  refine
    { path₁ := bpOfDartArc (daCast AUV eu euv2)
      path₂ := bpOfDartArc (daCast AVU ev evu2)
      path₁_boundary_vertices := fun {w} hw => bpOfDartArc_boundary_vertices (daCast AUV eu euv2) hv hw
      path₂_boundary_vertices := fun {w} hw => bpOfDartArc_boundary_vertices (daCast AVU ev evu2) hu hw
      boundary_vertices_covered := ?_
      internally_disjoint := ?_
      path₁_internal_of_proper := ?_
      path₂_internal_of_proper := ?_ }
  · intro w
    constructor
    · intro hw
      rcases covering hw with ⟨i, hi⟩ | ⟨i, hi⟩ | hwu | hwv
      · left
        rw [bpOfDartArc_vertices, List.mem_append]
        refine Or.inl ?_
        rw [← hi]
        exact List.mem_map_of_mem (by
          rw [DartArc.dartList]; exact List.mem_map_of_mem (List.mem_finRange i))
      · right
        rw [bpOfDartArc_vertices, List.mem_append]
        refine Or.inl ?_
        rw [← hi]
        exact List.mem_map_of_mem (by
          rw [DartArc.dartList]; exact List.mem_map_of_mem (List.mem_finRange i))
      · left
        rw [bpOfDartArc_vertices, List.mem_append]
        refine Or.inl ?_
        have hu_tail : M.tail ((daCast AUV eu euv2).arcDart (daCast AUV eu euv2).firstIdx) = w :=
          (daCast AUV eu euv2).tail_first.trans hwu.symm
        have hmem : M.tail ((daCast AUV eu euv2).arcDart (daCast AUV eu euv2).firstIdx)
            ∈ (daCast AUV eu euv2).dartList.map M.tail :=
          List.mem_map_of_mem (by
            rw [DartArc.dartList]; exact List.mem_map_of_mem (List.mem_finRange _))
        exact hu_tail ▸ hmem
      · left
        rw [bpOfDartArc_vertices, List.mem_append]
        exact Or.inr (by rw [hwv]; exact List.mem_singleton_self _)
    · intro hw
      rcases hw with hw | hw
      · exact bpOfDartArc_boundary_vertices (daCast AUV eu euv2) hv hw
      · exact bpOfDartArc_boundary_vertices (daCast AVU ev evu2) hu hw
  · intro w hw1 hw2
    obtain ⟨i, hi⟩ := bpOfDartArc_internal_tail (daCast AUV eu euv2) hw1
    obtain ⟨i', hi'⟩ := bpOfDartArc_internal_tail (daCast AVU ev evu2) hw2
    have hwuv : w = u ∨ w = v := disjoint ⟨i, hi⟩ ⟨i', hi'⟩
    have hwu : w ≠ u := (bpOfDartArc (daCast AUV eu euv2)).internalVertex_ne_start hw1
    have hwv : w ≠ v := (bpOfDartArc (daCast AUV eu euv2)).internalVertex_ne_end hw1
    rcases hwuv with h' | h'
    · exact hwu h'
    · exact hwv h'
  · intro hnbe
    exact bpOfDartArc_hasInternal (daCast AUV eu euv2)
      (by rw [daCast_len]; exact hkf2_of_proper hnbe)
  · intro hnbe
    exact bpOfDartArc_hasInternal (daCast AVU ev evu2)
      (by rw [daCast_len]; exact hkb2_of_proper hnbe)

end ProofsInTheBook.ZinanCh35ArcSplitUniversal

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35ArcSplitUniversal.arcSplit_of_nodup
