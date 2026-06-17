import ProofsInTheBook.ZinanCh35ChordlessSite
import ProofsInTheBook.ZinanCh35DeletedAssembly
import ProofsInTheBook.ZinanCh35DeletedBoundary
import ProofsInTheBook.ZinanCh35ChordlessOracle

/-!
# Chordless supplier assembly

This file is the final Phase-C supplier layer.  It starts by exposing the
deleted-boundary classification API needed by the Thomassen-list transport.
-/

set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35ChordlessSupplier

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}

/-- Boundary-cycle vertices are exactly tails of listed boundary darts. -/
theorem boundary_vertex_iff_exists_dart_tail {K : CombMap D} {f : K.Face}
    (C : BoundaryCycle K f) (W : K.Vertex) :
    C.IsBoundaryVertex W ↔ ∃ d : D, d ∈ C.darts ∧ K.tail d = W := by
  constructor
  · intro hW
    rw [BoundaryCycle.IsBoundaryVertex, C.vertices_eq] at hW
    simpa [List.mem_map] using hW
  · rintro ⟨d, hd, rfl⟩
    rw [BoundaryCycle.IsBoundaryVertex, C.vertices_eq]
    exact List.mem_map_of_mem hd

/-- Boundary-cycle edges are exactly dart edges of listed boundary darts. -/
theorem boundary_edge_iff_exists_dart_edge {K : CombMap D} {f : K.Face}
    (C : BoundaryCycle K f) (e : Sym2 K.Vertex) :
    C.IsBoundaryEdge e ↔ ∃ d : D, d ∈ C.darts ∧ K.dartEdge d = e := by
  constructor
  · intro he
    rw [BoundaryCycle.IsBoundaryEdge, C.edges_eq] at he
    simpa [List.mem_map] using he
  · rintro ⟨d, hd, rfl⟩
    rw [BoundaryCycle.IsBoundaryEdge, C.edges_eq]
    exact List.mem_map_of_mem hd

/-- An endpoint of a listed boundary edge is a boundary vertex. -/
lemma boundary_vertex_of_boundary_edge_left {K : CombMap D} {f : K.Face}
    (C : BoundaryCycle K f) {x y : K.Vertex}
    (he : C.IsBoundaryEdge s(x, y)) :
    C.IsBoundaryVertex x := by
  classical
  obtain ⟨d, hd, hdedge⟩ := (boundary_edge_iff_exists_dart_edge C s(x, y)).1 he
  rw [CombMap.dartEdge, Sym2.eq_iff] at hdedge
  rcases hdedge with ⟨htail, _hhead⟩ | ⟨_htail, hhead⟩
  · exact (boundary_vertex_iff_exists_dart_tail C x).2 ⟨d, hd, htail⟩
  · have hφd : K.φ d ∈ C.darts := C.phi_mem_darts hd
    exact (boundary_vertex_iff_exists_dart_tail C x).2
      ⟨K.φ d, hφd, by rw [K.tail_phi, hhead]⟩

/-- Consecutive in/out darts at a simple boundary vertex have distinct other
endpoints. -/
lemma boundary_neighbors_distinct_public {bin bout : D}
    (hbin_mem : bin ∈ hNT.outerCycle.darts) (hbout_mem : bout ∈ hNT.outerCycle.darts)
    (hbin_phi : M.φ bin = bout) :
    M.tail bin ≠ M.head bout := by
  intro hxy
  have hφbout_mem : M.φ bout ∈ hNT.outerCycle.darts :=
    hNT.outerCycle.phi_mem_darts hbout_mem
  have htail : M.tail bin = M.tail (M.φ bout) := by
    rw [tail_phi, hxy]
  have hbin_eq_phi_bout : bin = M.φ bout :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hbin_mem hφbout_mem htail
  have hφ2 : M.φ (M.φ bout) = bout := by
    rw [← hbin_eq_phi_bout, hbin_phi]
  have hφ : M.φ bout ≠ bout :=
    phi_ne_self_of_isSimpleGraph M hNT.simpleGraph bout
  have hcard2 :
      (M.φ.cycleOf bout).support.card = 2 :=
    card_support_cycleOf_eq_two_of_apply_apply_eq_self M.φ hφ hφ2
  have hbout_face : M.dartFace bout = hNT.outerFace :=
    (hNT.outerCycle.mem_darts_iff bout).mp hbout_mem
  have hface2 : M.faceLen hNT.outerFace = 2 := by
    have hsupport := faceLen_dartFace_eq_card_support_cycleOf M hφ
    rw [hbout_face, hcard2] at hsupport
    exact hsupport
  have hlen2 : hNT.outerCycle.length = 2 :=
    hNT.outerCycle.faceLen_eq_length.symm.trans hface2
  have hge : 3 ≤ hNT.outerCycle.length := hNT.outer_len
  omega

/-- Any old boundary vertex that survives a vertex deletion has an old boundary
edge incident with it whose other endpoint also survives. -/
lemma old_boundary_vertex_has_surviving_boundary_edge
    {d0 : D} (htail0 : M.tail d0 = v0)
    {u : M.Vertex}
    (hu_old : hNT.outerCycle.IsBoundaryVertex u)
    (hu_ne : u ≠ M.tail d0) :
    ∃ w : M.Vertex, w ≠ M.tail d0 ∧ hNT.outerCycle.IsBoundaryEdge s(u, w) := by
  classical
  obtain ⟨bin, bout, hbin, _hbin_unique, hbout, _hbout_unique, hbin_phi⟩ :=
    hNT.outer_v0_darts_consecutive hu_old
  rcases hbin with ⟨hbin_mem, hbin_head⟩
  rcases hbout with ⟨hbout_mem, hbout_tail⟩
  by_cases hsucc_ne : M.head bout ≠ M.tail d0
  · refine ⟨M.head bout, hsucc_ne, ?_⟩
    show s(u, M.head bout) ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    have hedge : M.dartEdge bout = s(u, M.head bout) := by
      simp [CombMap.dartEdge, hbout_tail]
    rw [← hedge]
    exact List.mem_map_of_mem hbout_mem
  · have hsucc_eq : M.head bout = M.tail d0 := by simpa using not_not.mp hsucc_ne
    have hpred_ne : M.tail bin ≠ M.tail d0 := by
      intro hpred_eq
      exact boundary_neighbors_distinct_public (hNT := hNT) hbin_mem hbout_mem hbin_phi
        (by rw [hpred_eq, hsucc_eq])
    refine ⟨M.tail bin, hpred_ne, ?_⟩
    show s(u, M.tail bin) ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    have hedge : M.dartEdge bin = s(u, M.tail bin) := by
      simp [CombMap.dartEdge, hbin_head, Sym2.eq_swap]
    rw [← hedge]
    exact List.mem_map_of_mem hbin_mem

/-- If a dart is on the outer face, its reverse is not also on the outer face.
This is the local no-digon consequence of the simple outer boundary. -/
theorem alpha_dartFace_ne_outer_of_outer_local {e : D}
    (he : M.dartFace e = hNT.outerFace) :
    M.dartFace (M.α e) ≠ hNT.outerFace := by
  intro hαe
  have he_mem : e ∈ hNT.outerCycle.darts := (hNT.outerCycle.mem_darts_iff e).2 he
  have hαe_mem : M.α e ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff (M.α e)).2 hαe
  have hφe_mem : M.φ e ∈ hNT.outerCycle.darts := by
    rw [hNT.outerCycle.mem_darts_iff]
    show M.dartFace (M.φ e) = hNT.outerFace
    rw [M.dartFace_phi]; exact he
  have htail_eq : M.tail (M.φ e) = M.tail (M.α e) := by
    rw [M.tail_phi, M.tail_alpha]
  have hφα : M.φ e = M.α e :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hφe_mem hαe_mem htail_eq
  have htail2 : M.tail (M.φ (M.φ e)) = M.tail e := by
    rw [hφα, M.tail_phi, M.head_alpha]
  have hφ2_mem : M.φ (M.φ e) ∈ hNT.outerCycle.darts := by
    rw [hNT.outerCycle.mem_darts_iff]
    show M.dartFace (M.φ (M.φ e)) = hNT.outerFace
    rw [M.dartFace_phi, M.dartFace_phi]; exact he
  have hφ2 : M.φ (M.φ e) = e :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hφ2_mem he_mem htail2
  have hφ : M.φ e ≠ e :=
    phi_ne_self_of_isSimpleGraph M hNT.simpleGraph e
  have hcard2 : (M.φ.cycleOf e).support.card = 2 :=
    card_support_cycleOf_eq_two_of_apply_apply_eq_self M.φ hφ hφ2
  have hface2 : M.faceLen hNT.outerFace = 2 := by
    have hsupport := faceLen_dartFace_eq_card_support_cycleOf M hφ
    rw [he, hcard2] at hsupport
    exact hsupport
  have hlen2 : hNT.outerCycle.length = 2 :=
    hNT.outerCycle.faceLen_eq_length.symm.trans hface2
  have hge : 3 ≤ hNT.outerCycle.length := hNT.outer_len
  omega

lemma mem_of_sigma_sameCycle_of_closed
    (S : Finset D)
    (hσS : ∀ ⦃d : D⦄, d ∈ S → M.σ d ∈ S)
    {a b : D} (ha : a ∈ S) (hab : M.σ.SameCycle a b) :
    b ∈ S := by
  obtain ⟨n, hn⟩ := hab.exists_nat_pow_eq
  have hpow : ∀ n : ℕ, (M.σ ^ n) a ∈ S := by
    intro n
    induction n with
    | zero => simpa using ha
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hσS ih
  simpa [hn] using hpow n

lemma univ_subset_of_connected_closed
    (S : Finset D) {base : D}
    (hbase : base ∈ S)
    (hαS : ∀ ⦃d : D⦄, d ∈ S → M.α d ∈ S)
    (hσS : ∀ ⦃d : D⦄, d ∈ S → M.σ d ∈ S)
    (hconn : M.Connected) :
    ∀ d : D, d ∈ S := by
  intro d
  have hreach : Relation.ReflTransGen M.dartStep base d := hconn base d
  induction hreach with
  | refl => exact hbase
  | tail hreach hstep ih =>
      rcases hstep with hsame | halpha
      · exact mem_of_sigma_sameCycle_of_closed (M := M) S hσS ih hsame
      · rw [halpha]
        exact hαS ih

lemma alpha_outer_of_inner_boundary_edge {e : D}
    (hinner : M.dartFace e ≠ hNT.outerFace)
    (hedge : hNT.outerCycle.IsBoundaryEdge (M.dartEdge e)) :
    M.dartFace (M.α e) = hNT.outerFace := by
  classical
  obtain ⟨b, hbmem, hbedge⟩ :=
    (boundary_edge_iff_exists_dart_edge hNT.outerCycle (M.dartEdge e)).1 hedge
  have hbface : M.dartFace b = hNT.outerFace :=
    hNT.outerCycle.dartFace_of_mem_darts hbmem
  have hsc : M.α.SameCycle b e :=
    hNT.simpleGraph.no_parallel hbedge
  have hcases := (M.alpha_sameCycle_iff e b).mp hsc.symm
  rcases hcases with rfl | hb
  · exact False.elim (hinner hbface)
  · rw [hb] at hbface
    exact hbface

lemma phi_outer_eq_of_same_tail {e b : D}
    (he : M.dartFace e = hNT.outerFace)
    (hb : M.dartFace b = hNT.outerFace)
    (htail : M.tail (M.φ e) = M.tail b) :
    M.φ e = b := by
  have hφe_mem : M.φ e ∈ hNT.outerCycle.darts := by
    rw [hNT.outerCycle.mem_darts_iff]
    show M.dartFace (M.φ e) = hNT.outerFace
    rw [M.dartFace_phi]; exact he
  have hb_mem : b ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff b).2 hb
  exact hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hφe_mem hb_mem htail

lemma length_le_two_of_tail_dropLast_nil {β : Type*} (l : List β)
    (h : l.tail.dropLast = []) : l.length ≤ 2 := by
  cases l with
  | nil => simp
  | cons a l =>
      cases l with
      | nil => simp
      | cons b l =>
          cases l with
          | nil => simp
          | cons c l =>
              simp at h

lemma tail_dropLast_nil_of_length_le_two {β : Type*} (l : List β)
    (h : l.length ≤ 2) : l.tail.dropLast = [] := by
  cases l with
  | nil => simp
  | cons a l =>
      cases l with
      | nil => simp
      | cons b l =>
          cases l with
          | nil => simp
          | cons c l =>
              simp at h

/-- Reverse half of the canonical base count: on a base triangle, the canonical
strict middle of any nontrivial vertex star is empty. -/
theorem canonInterior_empty_of_baseTriangle
    {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hbase : hNT.IsBaseTriangle) :
    ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior (M := M) (d0 := d0) = [] := by
  classical
  let hlist : List M.Vertex := (M.vertexDartList d0).map M.head
  have hnodup : hlist.Nodup := by
    dsimp [hlist]
    exact ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.vertexDartList_heads_nodup
      hNT hσ rfl
  have hsub : hlist.toFinset ⊆ (Finset.univ.erase (M.tail d0) : Finset M.Vertex) := by
    intro z hz
    rw [List.mem_toFinset] at hz
    obtain ⟨e, he_mem, rfl⟩ := List.mem_map.mp hz
    rw [Finset.mem_erase]
    constructor
    · have htail_e : M.tail e = M.tail d0 :=
        M.vertexDartList_tail hσ he_mem
      intro h
      exact hNT.simpleGraph.no_loop e (by rw [h, htail_e])
    · simp
  have herase_card : (Finset.univ.erase (M.tail d0) : Finset M.Vertex).card = 2 := by
    have hcard : Fintype.card M.Vertex = 3 := by
      unfold NearTriangulation.IsBaseTriangle at hbase
      exact hbase
    rw [Finset.card_erase_of_mem (by simp), Finset.card_univ, hcard]
  have hlen_le : hlist.length ≤ 2 := by
    have hcard_le := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnodup, herase_card] at hcard_le
    exact hcard_le
  apply tail_dropLast_nil_of_length_le_two
  simpa [ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior, hlist] using hlen_le

/-- Empty canonical fan interior means the `v0` star has exactly two darts. -/
lemma vertexDartList_length_eq_two_of_canonInterior_empty
    {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hempty :
      ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior (M := M) (d0 := d0) = []) :
    (M.vertexDartList d0).length = 2 := by
  set hlist := (M.vertexDartList d0).map M.head with hlistdef
  have hle : hlist.length ≤ 2 := by
    apply length_le_two_of_tail_dropLast_nil
    simpa [ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior, hlistdef] using hempty
  have hge : 2 ≤ hlist.length := by
    rw [hlistdef, List.length_map]
    exact ProofsInTheBook.ZinanCh35ChordlessFull.vertexDartList_length_ge_two hσ
  have hlen : hlist.length = 2 := le_antisymm hle hge
  simpa [hlistdef] using hlen

/-- With an empty canonical interior, the two boundary spokes are the same
non-root star dart: `σ d0 = σ⁻¹ d0`. -/
lemma sigma_eq_symm_of_canonInterior_empty
    {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hempty :
      ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior (M := M) (d0 := d0) = []) :
    M.σ d0 = M.σ.symm d0 := by
  have hlen := vertexDartList_length_eq_two_of_canonInterior_empty
    (M := M) hσ hempty
  have hpow := M.vertexDartList_pow_length hσ
  rw [hlen] at hpow
  apply M.σ.injective
  rw [Equiv.apply_symm_apply]
  simpa [pow_succ, pow_one, Equiv.Perm.coe_mul, Function.comp_apply] using hpow

/-- If the canonical fan interior is empty, the two old boundary neighbours of
`v0` are adjacent through the unique inner triangle incident with the outgoing
boundary edge. -/
lemma boundary_neighbours_adj_of_canonInterior_empty
    {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hface0 : M.dartFace d0 = hNT.outerFace)
    (hempty :
      ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior (M := M) (d0 := d0) = []) :
    M.toSimpleGraph.Adj (M.head d0) (M.head (M.σ.symm d0)) := by
  classical
  let d2 : D := M.φ (M.φ (M.α d0))
  have hinner : M.dartFace (M.α d0) ≠ hNT.outerFace :=
    alpha_dartFace_ne_outer_of_outer_local (hNT := hNT) hface0
  have hcube : M.φ (M.φ (M.φ (M.α d0))) = M.α d0 :=
    faceLen_three_phi_cube_eq_self M hNT.simpleGraph
      (hNT.inner_tri (M.dartFace (M.α d0)) hinner)
  have hsigsym : M.σ d0 = M.σ.symm d0 :=
    sigma_eq_symm_of_canonInterior_empty (M := M) hσ hempty
  have htail_d2 : M.tail d2 = M.head (M.σ.symm d0) := by
    dsimp [d2]
    have hφα : M.φ (M.α d0) = M.σ d0 := by
      show (M.σ * M.α) (M.α d0) = M.σ d0
      simp [Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]
    rw [hφα, M.tail_phi, hsigsym]
  have hhead_d2 : M.head d2 = M.head d0 := by
    dsimp [d2]
    rw [← M.tail_phi, hcube, M.tail_alpha]
  have hadj : M.toSimpleGraph.Adj (M.tail d2) (M.head d2) :=
    M.toSimpleGraph_adj_of_dart hNT.simpleGraph d2
  have hadj' : M.toSimpleGraph.Adj (M.head (M.σ.symm d0)) (M.head d0) := by
    simpa [htail_d2, hhead_d2] using hadj
  exact hadj'.symm

/-- If the two neighbours from the empty canonical fan are not already joined by
an outer-boundary edge, they form a boundary chord. -/
lemma chord_of_canonInterior_empty_of_not_boundary_edge
    {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hface0 : M.dartFace d0 = hNT.outerFace)
    (hempty :
      ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior (M := M) (d0 := d0) = [])
    (hnot :
      ¬ hNT.outerCycle.IsBoundaryEdge s(M.head d0, M.head (M.σ.symm d0))) :
    hNT.outerCycle.Chord (M.head d0) (M.head (M.σ.symm d0)) := by
  refine
    { endpoints_ne := ?_
      left_boundary := ProofsInTheBook.ZinanCh35Chordless.head_outgoing_boundary hNT hface0
      right_boundary := ProofsInTheBook.ZinanCh35Chordless.head_incoming_boundary hNT hface0
      adj := boundary_neighbours_adj_of_canonInterior_empty
        (hNT := hNT) hσ hface0 hempty
      not_boundary_edge := hnot }
  intro h
  have hinner : M.dartFace (M.α d0) ≠ hNT.outerFace :=
    alpha_dartFace_ne_outer_of_outer_local (hNT := hNT) hface0
  have hdistinct :=
    hNT.inner_face_vertices_pairwiseDistinct (d := M.α d0) hinner
  have hsigsym : M.σ d0 = M.σ.symm d0 :=
    sigma_eq_symm_of_canonInterior_empty (M := M) hσ hempty
  have hφeq : M.φ (M.α d0) = M.σ d0 := by
    show (M.σ * M.α) (M.α d0) = M.σ d0
    simp [Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]
  have htail1 : M.tail (M.α d0) = M.head d0 := by rw [M.tail_alpha]
  have htail3 : M.tail (M.φ (M.φ (M.α d0))) = M.head (M.σ.symm d0) := by
    rw [hφeq, M.tail_phi, hsigsym]
  exact hdistinct.2.2 (by rw [htail3, htail1, h])

lemma alpha_sigmaSymm_outer_of_outer {d0 : D}
    (hface0 : M.dartFace d0 = hNT.outerFace) :
    M.dartFace (M.α (M.σ.symm d0)) = hNT.outerFace := by
  have hkey :
      M.dartFace (M.σ (M.σ.symm d0)) =
        M.dartFace (M.α (M.σ.symm d0)) :=
    ProofsInTheBook.ZinanCh35StarConn.dartFace_sigma_eq_alpha (M := M) (M.σ.symm d0)
  rw [Equiv.apply_symm_apply] at hkey
  rw [← hkey]
  exact hface0

/-- Six-dart closure for the empty-fan base count: once the third edge is also
on the outer boundary, the six darts of the two triangular faces are closed under
`α` and `σ`; connectedness then forces them to be all darts, hence only three
vertex orbits. -/
theorem baseTriangle_of_canonInterior_empty_of_third_boundary_edge
    {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hface0 : M.dartFace d0 = hNT.outerFace)
    (hempty :
      ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior (M := M) (d0 := d0) = [])
    (hbedge :
      hNT.outerCycle.IsBoundaryEdge s(M.head d0, M.head (M.σ.symm d0))) :
    hNT.IsBaseTriangle := by
  classical
  let e1 : D := M.σ.symm d0
  let e2 : D := M.φ (M.φ (M.α d0))
  let S : Finset D := {d0, M.α d0, e1, M.α e1, e2, M.α e2}
  have htail_e1 : M.tail e1 = M.tail d0 := by
    dsimp [e1]
    have h := M.tail_sigma (M.σ.symm d0)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  have hsigsym : M.σ d0 = e1 := by
    dsimp [e1]
    exact sigma_eq_symm_of_canonInterior_empty (M := M) hσ hempty
  have hφeq : M.φ (M.α d0) = e1 := by
    dsimp [e1]
    show (M.σ * M.α) (M.α d0) = M.σ.symm d0
    rw [show (M.σ * M.α) (M.α d0) = M.σ d0 by
      simp [Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]]
    exact hsigsym
  have hinner : M.dartFace (M.α d0) ≠ hNT.outerFace :=
    alpha_dartFace_ne_outer_of_outer_local (hNT := hNT) hface0
  have hcube : M.φ (M.φ (M.φ (M.α d0))) = M.α d0 :=
    faceLen_three_phi_cube_eq_self M hNT.simpleGraph
      (hNT.inner_tri (M.dartFace (M.α d0)) hinner)
  have htail_e2 : M.tail e2 = M.head e1 := by
    dsimp [e2]
    rw [hφeq, M.tail_phi]
  have hhead_e2 : M.head e2 = M.head d0 := by
    dsimp [e2]
    rw [← M.tail_phi, hcube, M.tail_alpha]
  have hedge_e2 : M.dartEdge e2 = s(M.head d0, M.head e1) := by
    rw [CombMap.dartEdge, htail_e2, hhead_e2, Sym2.eq_swap]
  have hbedge_e2 : hNT.outerCycle.IsBoundaryEdge (M.dartEdge e2) := by
    simpa [hedge_e2, e1] using hbedge
  have hαe2_outer : M.dartFace (M.α e2) = hNT.outerFace :=
    alpha_outer_of_inner_boundary_edge (hNT := hNT) (e := e2) (by
      dsimp [e2]
      rw [M.dartFace_phi, M.dartFace_phi]
      exact hinner) hbedge_e2
  have hαe1_outer : M.dartFace (M.α e1) = hNT.outerFace := by
    dsimp [e1]
    exact alpha_sigmaSymm_outer_of_outer (hNT := hNT) hface0
  have hφd0 : M.φ d0 = M.α e2 := by
    apply phi_outer_eq_of_same_tail (hNT := hNT) hface0 hαe2_outer
    rw [M.tail_phi, M.tail_alpha, hhead_e2]
  have hφαe2 : M.φ (M.α e2) = M.α e1 := by
    apply phi_outer_eq_of_same_tail (hNT := hNT) hαe2_outer hαe1_outer
    rw [M.tail_phi, M.head_alpha, M.tail_alpha, htail_e2]
  have hσS : ∀ ⦃d : D⦄, d ∈ S → M.σ d ∈ S := by
    intro d hd
    simp [S] at hd ⊢
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl hsigsym))
    · have : M.σ (M.α d0) = M.α e2 := by
        rw [← hφd0]
        rfl
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr this))))
    · dsimp [e1]
      simp
    · have : M.σ (M.α e1) = e2 := by
        rw [← hφeq]
        rfl
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl this))))
    · have : M.σ e2 = M.α e1 := by
        rw [← hφαe2]
        show M.σ e2 = M.φ (M.α e2)
        simp [CombMap.φ, Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]
      exact Or.inr (Or.inr (Or.inr (Or.inl this)))
    · have : M.σ (M.α e2) = M.α d0 := by
        rw [← hcube]
        rfl
      exact Or.inr (Or.inl this)
  have hαS : ∀ ⦃d : D⦄, d ∈ S → M.α d ∈ S := by
    intro d hd
    simp [S] at hd ⊢
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [S, M.alpha_alpha]
  have hall : ∀ d : D, d ∈ S :=
    univ_subset_of_connected_closed (M := M) S (base := d0)
      (by simp [S]) hαS hσS hNT.sphere.1
  let A : M.Vertex := M.tail d0
  let B : M.Vertex := M.head d0
  let C : M.Vertex := M.head e1
  have hver : ∀ Q : M.Vertex,
      Q ∈ ({A, B, C} : Finset M.Vertex) := by
    intro Q
    induction Q using Quotient.inductionOn with
    | h d =>
        have hd := hall d
        simp [S] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
        · change A ∈ ({A, B, C} : Finset M.Vertex)
          simp
        · change M.tail (M.α d0) ∈ ({A, B, C} : Finset M.Vertex)
          rw [M.tail_alpha]
          simp [B]
        · change M.tail e1 ∈ ({A, B, C} : Finset M.Vertex)
          rw [htail_e1]
          simp [A]
        · change M.tail (M.α e1) ∈ ({A, B, C} : Finset M.Vertex)
          rw [M.tail_alpha]
          simp [C]
        · change M.tail e2 ∈ ({A, B, C} : Finset M.Vertex)
          rw [htail_e2]
          simp [C]
        · change M.tail (M.α e2) ∈ ({A, B, C} : Finset M.Vertex)
          rw [M.tail_alpha, hhead_e2]
          simp [B]
  have hVle : M.V ≤ 3 := by
    calc
      M.V = (Finset.univ : Finset M.Vertex).card := rfl
      _ ≤ ({A, B, C} : Finset M.Vertex).card :=
        Finset.card_le_card (by intro Q _; exact hver Q)
      _ ≤ 3 := by
        simpa using
          (List.toFinset_card_le (l := [A, B, C]))
  have hVge : 3 ≤ M.V := ProofsInTheBook.ThomassenInduction.three_le_V hNT
  unfold NearTriangulation.IsBaseTriangle
  omega

/-- Forward half of the canonical `BaseCount` for an outgoing outer spoke. -/
theorem baseTriangle_of_canonInterior_empty_of_chordless
    {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hface0 : M.dartFace d0 = hNT.outerFace)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hempty :
      ProofsInTheBook.ZinanCh35ChordlessFull.canonInterior (M := M) (d0 := d0) = []) :
    hNT.IsBaseTriangle := by
  by_cases hbedge :
      hNT.outerCycle.IsBoundaryEdge s(M.head d0, M.head (M.σ.symm d0))
  · exact baseTriangle_of_canonInterior_empty_of_third_boundary_edge
      (hNT := hNT) hσ hface0 hempty hbedge
  · exact False.elim
      (hchordless (chord_of_canonInterior_empty_of_not_boundary_edge
        (hNT := hNT) hσ hface0 hempty hbedge))

/-- The canonical `BaseCount` required by the σ-derived fan constructor, for an
outgoing outer spoke. -/
theorem baseCount_of_outer_spoke
    {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hface0 : M.dartFace d0 = hNT.outerFace) :
    ProofsInTheBook.ZinanCh35ChordlessFull.BaseCount hNT (d0 := d0) := by
  intro hchordless
  constructor
  · intro hempty
    exact baseTriangle_of_canonInterior_empty_of_chordless
      (hNT := hNT) hσ hface0 hchordless hempty
  · intro hbase
    exact canonInterior_empty_of_baseTriangle (hNT := hNT) hσ hbase

/-- The second vertex of a fan consecutive pair is either exposed-interior or
the terminal endpoint. -/
lemma consecutivePair_second_mem_interior_or_w
    (fan : BoundaryVertexFan hNT v0) {a b : M.Vertex}
    (hp : (a, b) ∈ consecutivePairs fan.path) :
    b ∈ fan.interior ∨ b = fan.w := by
  have hb_tail : b ∈ fan.path.tail := by
    rw [consecutivePairs] at hp
    exact (List.of_mem_zip hp).2
  rw [BoundaryVertexFan.path, fanPath] at hb_tail
  simpa using hb_tail

/-- Any listed interior fan vertex has a predecessor in the fan path. -/
lemma fan_interior_exists_predecessor_pair
    (fan : BoundaryVertexFan hNT v0) {z : M.Vertex}
    (hz : z ∈ fan.interior) :
    ∃ a : M.Vertex, (a, z) ∈ consecutivePairs fan.path := by
  classical
  have aux : ∀ (x : M.Vertex) (l : List M.Vertex),
      z ∈ l → ∃ a : M.Vertex, (a, z) ∈ consecutivePairs (x :: l ++ [fan.w]) := by
    intro x l
    induction l generalizing x with
    | nil =>
        intro hz
        simp at hz
    | cons y ys ih =>
        intro hz
        rw [List.mem_cons] at hz
        rcases hz with rfl | hz
        · refine ⟨x, ?_⟩
          simp [consecutivePairs]
        · obtain ⟨a, ha⟩ := ih y hz
          refine ⟨a, ?_⟩
          simp [consecutivePairs] at ha ⊢
          exact Or.inr ha
  rw [BoundaryVertexFan.path, fanPath]
  exact aux fan.x fan.interior hz

/-- Fan interior vertices are old-map interior vertices in the chordless case. -/
theorem fan_interior_old_interior
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    {z : M.Vertex} (hz : z ∈ fan.interior.toFinset) :
    ¬ hNT.outerCycle.IsBoundaryVertex z := by
  rw [List.mem_toFinset] at hz
  exact fan_interior_vertices_not_boundary_of_chordless hNT fan hchordless z hz

/-- A surviving dart whose old face was incident with the deleted vertex has its
tail over either an old boundary vertex or an exposed fan-interior vertex. -/
theorem incident_survivor_tail_oldBoundary_or_fanInterior
    (fan : BoundaryVertexFan hNT v0) {d0 : D} (htail0 : M.tail d0 = v0)
    (y : {d : D // d ∉ M.deleteVertexSet d0})
    (hyinc : M.dartFace y.1 ∈ M.vertexFaces d0) :
    hNT.outerCycle.IsBoundaryVertex (M.tail y.1) ∨
      M.tail y.1 ∈ fan.interior.toFinset := by
  classical
  by_cases hyouter : M.dartFace y.1 = hNT.outerFace
  · left
    exact ProofsInTheBook.ZinanCh35DeletedAssembly.isBoundaryVertex_tail_of_outer_dart
      (hNT := hNT) hyouter
  ·
    obtain ⟨a, b, hp, hy_eq⟩ :=
      ProofsInTheBook.ZinanCh35DeletedAssembly.incident_nonouter_survivor_eq_fan_edge
        fan htail0 y hyinc hyouter
    have htail_b : M.tail y.1 = b := by
      rw [hy_eq]
      exact (fan.incident_faces_exact.triangle_of_pair hp).tail1
    rcases consecutivePair_second_mem_interior_or_w fan hp with hbint | hbw
    · right
      simpa [htail_b] using hbint
    · left
      rw [htail_b, hbw]
      exact fan.w_boundary

/-- Forward half of deleted-boundary classification, abstracted over any deleted
boundary cycle whose darts are known to be old faces incident with the deleted
vertex. -/
theorem deleted_boundary_vertex_oldBoundary_or_fanInterior_of_incident_darts
    (fan : BoundaryVertexFan hNT v0) {d0 : D} (htail0 : M.tail d0 = v0)
    {outerFace : (M.deleteVertex d0).Face}
    (C : BoundaryCycle (M.deleteVertex d0) outerFace)
    (hinc : ∀ y : {d : D // d ∉ M.deleteVertexSet d0},
      y ∈ C.darts → M.dartFace y.1 ∈ M.vertexFaces d0)
    {u' : (M.deleteVertex d0).Vertex}
    (hu' : C.IsBoundaryVertex u') :
    hNT.outerCycle.IsBoundaryVertex (deletedVertexToM M d0 u') ∨
      deletedVertexToM M d0 u' ∈ fan.interior.toFinset := by
  classical
  obtain ⟨y, hy, hy_tail⟩ := (boundary_vertex_iff_exists_dart_tail C u').1 hu'
  have hclass := incident_survivor_tail_oldBoundary_or_fanInterior fan htail0 y (hinc y hy)
  have htoM : deletedVertexToM M d0 u' = M.tail y.1 := by
    rw [← hy_tail]
    exact deletedVertexToM_tail M d0 y
  simpa [htoM] using hclass

/-- Darts on the produced fan-pair deleted outer cycle are exactly old faces
incident with the deleted vertex, forward direction. -/
theorem fan_pair_deleted_outerCycle_dart_incident
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    (y : {d : D // d ∉ M.deleteVertexSet d0})
    (hy : y ∈
      ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.darts)) :
    M.dartFace y.1 ∈ M.vertexFaces d0 := by
  classical
  let root : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        (fan.incident_faces_exact.triangle_of_pair hp) htail0⟩
  let hmerge : DeleteVertexMergedFaceSingleOrbit M d0 :=
    ProofsInTheBook.ZinanCh35MergedArc.deleteVertexMergedFaceSingleOrbit_of_fan_pair_seam
      fan hchordless htail0 hbin_mem hbin_head hp hbin_tail hbout hoPre_surv hoPre_phi
  have hroot_inc : M.dartFace root.1 ∈ M.vertexFaces d0 :=
    ProofsInTheBook.ZinanCh35DeletedAssembly.fanPairSeamEdge_incident fan htail0 hp
  change y ∈ (M.deleteVertex d0).faceDartList root at hy
  exact (ProofsInTheBook.ZinanCh35DeletedAssembly.mem_faceDartList_root_iff_incident
    hNT htail0 root y hroot_inc hmerge).1 hy

/-- Any survivor whose old face is incident with the deleted vertex is listed on
the produced fan-pair deleted outer cycle. -/
theorem fan_pair_incident_survivor_mem_deleted_outerCycle
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    (y : {d : D // d ∉ M.deleteVertexSet d0})
    (hyinc : M.dartFace y.1 ∈ M.vertexFaces d0) :
    y ∈
      ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.darts) := by
  classical
  let root : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        (fan.incident_faces_exact.triangle_of_pair hp) htail0⟩
  let hmerge : DeleteVertexMergedFaceSingleOrbit M d0 :=
    ProofsInTheBook.ZinanCh35MergedArc.deleteVertexMergedFaceSingleOrbit_of_fan_pair_seam
      fan hchordless htail0 hbin_mem hbin_head hp hbin_tail hbout hoPre_surv hoPre_phi
  have hroot_inc : M.dartFace root.1 ∈ M.vertexFaces d0 :=
    ProofsInTheBook.ZinanCh35DeletedAssembly.fanPairSeamEdge_incident fan htail0 hp
  change y ∈ (M.deleteVertex d0).faceDartList root
  exact (ProofsInTheBook.ZinanCh35DeletedAssembly.mem_faceDartList_root_iff_incident
    hNT htail0 root y hroot_inc hmerge).2 hyinc

/-- Forward half of `DeletedBoundaryClassification.boundary_iff` for the closed
fan-pair seam assembly. -/
theorem fan_pair_deleted_boundary_vertex_oldBoundary_or_fanInterior
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    {u' : (M.deleteVertex d0).Vertex}
    (hu' :
      ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.IsBoundaryVertex u')) :
    hNT.outerCycle.IsBoundaryVertex (deletedVertexToM M d0 u') ∨
      deletedVertexToM M d0 u' ∈ fan.interior.toFinset := by
  exact deleted_boundary_vertex_oldBoundary_or_fanInterior_of_incident_darts
    fan htail0
    ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle)
    (fun y hy => fan_pair_deleted_outerCycle_dart_incident
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi y hy)
    hu'

/-- A deleted vertex whose old image is an exposed fan-interior vertex is on the
produced deleted outer boundary. -/
theorem fan_pair_fanInterior_deleted_boundary_vertex
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    {u' : (M.deleteVertex d0).Vertex}
    (hu'fan : deletedVertexToM M d0 u' ∈ fan.interior.toFinset) :
    ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.IsBoundaryVertex u') := by
  classical
  rw [List.mem_toFinset] at hu'fan
  obtain ⟨a₀, hp₀⟩ := fan_interior_exists_predecessor_pair fan hu'fan
  let T := fan.incident_faces_exact.triangle_of_pair hp₀
  let y : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨T.d1, ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
      T htail0⟩
  have hyinc : M.dartFace y.1 ∈ M.vertexFaces d0 :=
    ProofsInTheBook.ZinanCh35DeletedAssembly.fanPairSeamEdge_incident fan htail0 hp₀
  have hy_mem := fan_pair_incident_survivor_mem_deleted_outerCycle
    fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
    hoPre_surv hoPre_phi y hyinc
  have htail_old : M.tail y.1 = deletedVertexToM M d0 u' := by
    dsimp [y, T]
    rw [(fan.incident_faces_exact.triangle_of_pair hp₀).tail1]
  have htail_deleted : (M.deleteVertex d0).tail y = u' := by
    apply deletedVertexToM_injective M d0
    rw [deletedVertexToM_tail, htail_old]
  exact (boundary_vertex_iff_exists_dart_tail
    ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle) u').2
    ⟨y, hy_mem, htail_deleted⟩

/-- The canonical section is the unique deleted vertex with the prescribed old
image. -/
lemma deleted_vertex_eq_sectionToDeleted_of_toM_eq
    {d0 : D} (R : FanSurgeryReconstruction hNT d0)
    {W : (M.deleteVertex d0).Vertex} {x : M.Vertex}
    (hx : x ≠ M.tail d0)
    (hW : deletedVertexToM M d0 W = x) :
    W = sectionToDeleted R x hx := by
  apply deletedVertexToM_injective M d0
  rw [hW, deletedVertexToM_sectionToDeleted]

/-- Old boundary edges whose endpoints survive the deletion remain boundary
edges of the produced deleted outer cycle. -/
theorem fan_pair_old_boundary_edge_survives
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hp : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    {x y : M.Vertex}
    (hx : x ≠ M.tail d0) (hy : y ≠ M.tail d0)
    (hedge : hNT.outerCycle.IsBoundaryEdge s(x, y)) :
    let R :=
      (ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon
    R.nearTriangulation.outerCycle.IsBoundaryEdge
      s(sectionToDeleted R x hx, sectionToDeleted R y hy) := by
  classical
  intro R
  obtain ⟨e, he_mem, he_edge⟩ :=
    (boundary_edge_iff_exists_dart_edge hNT.outerCycle s(x, y)).1 hedge
  have he_face : M.dartFace e = hNT.outerFace :=
    hNT.outerCycle.dartFace_of_mem_darts he_mem
  have htail_ne : M.tail e ≠ M.tail d0 := by
    rw [CombMap.dartEdge, Sym2.eq_iff] at he_edge
    rcases he_edge with ⟨ht, _hh⟩ | ⟨ht, _hh⟩
    · rw [ht]; exact hx
    · rw [ht]; exact hy
  have hhead_ne : M.head e ≠ M.tail d0 := by
    rw [CombMap.dartEdge, Sym2.eq_iff] at he_edge
    rcases he_edge with ⟨_ht, hh⟩ | ⟨_ht, hh⟩
    · rw [hh]; exact hy
    · rw [hh]; exact hx
  have hsurv : e ∉ M.deleteVertexSet d0 :=
    dart_notMem_deleteVertexSet_of_endpoints_ne M d0 htail_ne hhead_ne
  let e' : {d : D // d ∉ M.deleteVertexSet d0} := ⟨e, hsurv⟩
  have houter_inc : hNT.outerFace ∈ M.vertexFaces d0 :=
    ProofsInTheBook.ZinanCh35DeletedAssembly.oldOuterFace_incident_of_seam
      htail0 hbin_mem hbin_head hbout
  have he_inc : M.dartFace e'.1 ∈ M.vertexFaces d0 := by
    dsimp [e']
    rw [he_face]
    exact houter_inc
  have he'_mem := fan_pair_incident_survivor_mem_deleted_outerCycle
    fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
    hoPre_surv hoPre_phi e' he_inc
  refine (boundary_edge_iff_exists_dart_edge R.nearTriangulation.outerCycle
    s(sectionToDeleted R x hx, sectionToDeleted R y hy)).2 ⟨e', he'_mem, ?_⟩
  have he_edge_saved : M.dartEdge e = s(x, y) := he_edge
  rw [CombMap.dartEdge, Sym2.eq_iff] at he_edge_saved ⊢
  rcases he_edge_saved with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · left
    constructor
    · exact deleted_vertex_eq_sectionToDeleted_of_toM_eq R hx (by
        rw [deletedVertexToM_tail]
        exact ht)
    · exact deleted_vertex_eq_sectionToDeleted_of_toM_eq R hy (by
        rw [deletedVertexToM_head]
        exact hh)
  · right
    constructor
    · exact deleted_vertex_eq_sectionToDeleted_of_toM_eq R hy (by
        rw [deletedVertexToM_tail]
        exact ht)
    · exact deleted_vertex_eq_sectionToDeleted_of_toM_eq R hx (by
        rw [deletedVertexToM_head]
        exact hh)

/-- Old boundary vertices that survive the deletion lie on the produced deleted
outer boundary. -/
theorem fan_pair_oldBoundary_deleted_boundary_vertex
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hp : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    {u' : (M.deleteVertex d0).Vertex}
    (hu_old : hNT.outerCycle.IsBoundaryVertex (deletedVertexToM M d0 u')) :
    ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.IsBoundaryVertex u') := by
  classical
  let R :=
    (ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi).chordlessRecon
  let u := deletedVertexToM M d0 u'
  have hu_ne : u ≠ M.tail d0 := by
    dsimp [u]
    exact deletedVertexToM_ne_v0 M d0 u'
  obtain ⟨w, hw_ne, hedge⟩ :=
    old_boundary_vertex_has_surviving_boundary_edge
      (hNT := hNT) (v0 := v0) htail0 hu_old hu_ne
  have hedge' :
      R.nearTriangulation.outerCycle.IsBoundaryEdge
        s(sectionToDeleted R u hu_ne, sectionToDeleted R w hw_ne) := by
    simpa [R] using
      (fan_pair_old_boundary_edge_survives
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi hu_ne hw_ne hedge)
  have hsec_boundary :
      R.nearTriangulation.outerCycle.IsBoundaryVertex
        (sectionToDeleted R u hu_ne) :=
    boundary_vertex_of_boundary_edge_left R.nearTriangulation.outerCycle hedge'
  have hu'_eq : u' = sectionToDeleted R u hu_ne :=
    deleted_vertex_eq_sectionToDeleted_of_toM_eq R hu_ne (by rfl)
  simpa [R, hu'_eq]
    using hsec_boundary

/-- Full vertex-level deleted-boundary classification for the produced
fan-pair seam assembly. -/
theorem fan_pair_deleted_boundary_iff_oldBoundary_or_fanInterior
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hp : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    (u' : (M.deleteVertex d0).Vertex) :
    ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.IsBoundaryVertex u') ↔
      hNT.outerCycle.IsBoundaryVertex (deletedVertexToM M d0 u') ∨
        deletedVertexToM M d0 u' ∈ fan.interior.toFinset := by
  constructor
  · intro hu'
    exact fan_pair_deleted_boundary_vertex_oldBoundary_or_fanInterior
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi hu'
  · intro hclass
    rcases hclass with hold | hfan
    · exact fan_pair_oldBoundary_deleted_boundary_vertex
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi hold
    · exact fan_pair_fanInterior_deleted_boundary_vertex
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi hfan

/-- Deleted non-boundary vertices map to old non-boundary vertices and are not
exposed fan-interior vertices. -/
theorem fan_pair_deleted_nonboundary_old_interior
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hp : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    {u' : (M.deleteVertex d0).Vertex}
    (hu' :
      ¬ ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.IsBoundaryVertex u')) :
    ¬ hNT.outerCycle.IsBoundaryVertex (deletedVertexToM M d0 u') ∧
      deletedVertexToM M d0 u' ∉ fan.interior.toFinset := by
  constructor
  · intro hold
    exact hu' (fan_pair_oldBoundary_deleted_boundary_vertex
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi hold)
  · intro hfan
    exact hu' (fan_pair_fanInterior_deleted_boundary_vertex
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi hfan)

/-- Thomassen-list transport for the produced fan-pair deletion.  The deleted
precolored edge is the surviving copy of the original precolored edge. -/
noncomputable def fan_pair_deleted_thomassenLists
    (fan : BoundaryVertexFan hNT v0)
    (hTL : ThomassenLists hNT p q L cp cq)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hp : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    (hp_ne_v0 : p ≠ M.tail d0) (hq_ne_v0 : q ≠ M.tail d0)
    (γ δ : α) :
    let R :=
      (ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon
    ThomassenLists R.nearTriangulation
      (sectionToDeleted R p hp_ne_v0) (sectionToDeleted R q hq_ne_v0)
      (deleteFanLists M d0 fan.interior.toFinset L γ δ) cp cq := by
  classical
  intro R
  let p' : (M.deleteVertex d0).Vertex := sectionToDeleted R p hp_ne_v0
  let q' : (M.deleteVertex d0).Vertex := sectionToDeleted R q hq_ne_v0
  have hp'_toM : deletedVertexToM M d0 p' = p := by
    simpa [p'] using deletedVertexToM_sectionToDeleted R p hp_ne_v0
  have hq'_toM : deletedVertexToM M d0 q' = q := by
    simpa [q'] using deletedVertexToM_sectionToDeleted R q hq_ne_v0
  have hp_not_fan : deletedVertexToM M d0 p' ∉ fan.interior.toFinset := by
    rw [hp'_toM, List.mem_toFinset]
    intro hpint
    exact (fan.interior_not_boundary_of_chordless hchordless p hpint) hTL.p_boundary
  have hq_not_fan : deletedVertexToM M d0 q' ∉ fan.interior.toFinset := by
    rw [hq'_toM, List.mem_toFinset]
    intro hqint
    exact (fan.interior_not_boundary_of_chordless hchordless q hqint) hTL.q_boundary
  refine
    { p_boundary := ?_
      q_boundary := ?_
      pq_boundary_edge := ?_
      colors_ne := hTL.colors_ne
      list_p := ?_
      list_q := ?_
      boundary_ge_three := ?_
      interior_ge_five := ?_ }
  · simpa [R, p', hp'_toM] using
      (fan_pair_oldBoundary_deleted_boundary_vertex
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi (u' := p') (by simpa [hp'_toM] using hTL.p_boundary))
  · simpa [R, q', hq'_toM] using
      (fan_pair_oldBoundary_deleted_boundary_vertex
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi (u' := q') (by simpa [hq'_toM] using hTL.q_boundary))
  · simpa [R, p', q'] using
      (fan_pair_old_boundary_edge_survives
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi hp_ne_v0 hq_ne_v0 hTL.pq_boundary_edge)
  · rw [deleteFanLists_other M d0 fan.interior.toFinset L γ δ hp_not_fan, hp'_toM]
    exact hTL.list_p
  · rw [deleteFanLists_other M d0 fan.interior.toFinset L γ δ hq_not_fan, hq'_toM]
    exact hTL.list_q
  · intro u' hu' hu'p hu'q
    have hclass :=
      (fan_pair_deleted_boundary_iff_oldBoundary_or_fanInterior
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi u').1 hu'
    rcases hclass with hold | hfan
    · have hu_ne_p : deletedVertexToM M d0 u' ≠ p := by
        intro hup
        apply hu'p
        apply deletedVertexToM_injective M d0
        rw [hup, hp'_toM]
      have hu_ne_q : deletedVertexToM M d0 u' ≠ q := by
        intro huq
        apply hu'q
        apply deletedVertexToM_injective M d0
        rw [huq, hq'_toM]
      have hnotfan : deletedVertexToM M d0 u' ∉ fan.interior.toFinset := by
        rw [List.mem_toFinset]
        intro hint
        exact (fan.interior_not_boundary_of_chordless hchordless
          (deletedVertexToM M d0 u') hint) hold
      rw [deleteFanLists_other M d0 fan.interior.toFinset L γ δ hnotfan]
      exact hTL.boundary_ge_three (deletedVertexToM M d0 u') hold hu_ne_p hu_ne_q
    · have h5 : 5 ≤ (L (deletedVertexToM M d0 u')).card :=
        hTL.interior_ge_five (deletedVertexToM M d0 u')
          (fan.interior_not_boundary_of_chordless hchordless
            (deletedVertexToM M d0 u') (by simpa [List.mem_toFinset] using hfan))
      exact deleteFanLists_card_ge_three M d0 fan.interior.toFinset L hfan h5
  · intro u' hu'
    have hnon :=
      fan_pair_deleted_nonboundary_old_interior
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi hu'
    rw [deleteFanLists_other M d0 fan.interior.toFinset L γ δ hnon.2]
    exact hTL.interior_ge_five (deletedVertexToM M d0 u') hnon.1

/-- The chordless oracle residual is supplied by the canonical endpoint-aware
deletion site, the σ-derived fan data, the closed seam reconstruction, and the
deleted-list transport above. -/
noncomputable def canonicalChordlessOracleResidual :
    ProofsInTheBook.ZinanCh35ChordlessOracle.ChordlessOracleResidual α where
  supply := by
    intro D _ _ M hNT p q L cp cq hbig hTL hchordless
    classical
    let site :=
      ProofsInTheBook.ZinanCh35ChordlessSite.exists_chordlessDeletionSite
        (hNT := hNT) hTL
    have hσ : M.σ site.d0 ≠ site.d0 :=
      ProofsInTheBook.ZinanCh35Chordless.outgoingOuterDart_sigma_ne hNT site.d0_face
    let fanData :
        NearTriangulation.FanIncidenceData hNT site.v0 :=
      ProofsInTheBook.ZinanCh35ChordlessOracle.fanIncidenceData_sigma_derived
        hσ site.d0_tail site.d0_face
        (baseCount_of_outer_spoke (hNT := hNT) hσ site.d0_face)
    let fan : BoundaryVertexFan hNT site.v0 :=
      NearTriangulation.boundaryVertexFan_of_incidenceData fanData
    let bin : D := Classical.choose (hNT.outer_v0_darts_consecutive site.hv0_boundary)
    let bout : D :=
      Classical.choose (Classical.choose_spec
        (hNT.outer_v0_darts_consecutive site.hv0_boundary))
    have hout :=
      Classical.choose_spec (Classical.choose_spec
        (hNT.outer_v0_darts_consecutive site.hv0_boundary))
    rcases hout with ⟨hbin, _hbin_unique, hbout, hbout_unique, hbin_phi⟩
    rcases hbin with ⟨hbin_mem, hbin_head⟩
    rcases hbout with ⟨hbout_mem, hbout_tail⟩
    have hbout_eq_d0 : bout = site.d0 := by
      exact (hbout_unique site.d0 ((hNT.outerCycle.mem_darts_iff site.d0).2 site.d0_face)
        site.d0_tail).symm
    have hphi_bin_d0 : M.φ bin = site.d0 := by
      exact hbin_phi.trans hbout_eq_d0
    have htail_bin_fan_w : M.tail bin = fan.w := by
      have htail_sigma :=
        ProofsInTheBook.ZinanCh35MergedArc.incoming_outer_tail_eq_head_sigma_symm
          (hNT := hNT) site.d0_face site.d0_tail hbin_mem hbin_head hphi_bin_d0
      have hfan_w : fan.w = M.head (M.σ.symm site.d0) := by
        change fanData.w = M.head (M.σ.symm site.d0)
        simp [fanData,
          ProofsInTheBook.ZinanCh35ChordlessOracle.fanIncidenceData_sigma_derived,
          ProofsInTheBook.ZinanCh35ChordlessClose.fanIncidenceData_of_baseCount,
          ProofsInTheBook.ZinanCh35ChordlessFull.fanIncidenceData_of_orientation]
      exact htail_sigma.trans hfan_w.symm
    have htail_bin_boundary : hNT.outerCycle.IsBoundaryVertex (M.tail bin) := by
      show M.tail bin ∈ hNT.outerCycle.vertices
      rw [hNT.outerCycle.vertices_eq]
      exact List.mem_map_of_mem hbin_mem
    let oPre : D := Classical.choose (hNT.outer_v0_darts_consecutive htail_bin_boundary)
    let oPost : D :=
      Classical.choose (Classical.choose_spec
        (hNT.outer_v0_darts_consecutive htail_bin_boundary))
    have houtPre :=
      Classical.choose_spec (Classical.choose_spec
        (hNT.outer_v0_darts_consecutive htail_bin_boundary))
    rcases houtPre with ⟨hoPreIn, _hoPre_unique, hoPostOut, hoPost_unique, hoPre_phi0⟩
    rcases hoPreIn with ⟨hoPre_mem, _hoPre_head⟩
    rcases hoPostOut with ⟨hoPost_mem, hoPost_tail⟩
    have hbin_eq_oPost : bin = oPost := by
      exact hoPost_unique bin hbin_mem rfl
    have hoPre_phi : M.φ oPre = bin := by
      exact hoPre_phi0.trans hbin_eq_oPost.symm
    have hoPre_surv : oPre ∉ M.deleteVertexSet site.d0 :=
      ProofsInTheBook.ZinanCh35MergedArc.old_outer_predecessor_survives
        (hNT := hNT) site.d0_tail hbin_mem hbin_head hbin_phi.symm
        hoPre_mem hoPre_phi
    let aT : M.Vertex :=
      Classical.choose (ProofsInTheBook.ZinanCh35DeletedAssembly.exists_terminal_fan_pair fan)
    have hpT :
        (aT, fan.w) ∈ consecutivePairs fan.path :=
      Classical.choose_spec
        (ProofsInTheBook.ZinanCh35DeletedAssembly.exists_terminal_fan_pair fan)
    have hp_ne_v0 : p ≠ M.tail site.d0 := by
      intro hpv
      exact site.v0_ne_p (by rw [← site.d0_tail, ← hpv])
    have hq_ne_v0 : q ≠ M.tail site.d0 := by
      intro hqv
      exact site.v0_ne_q (by rw [← site.d0_tail, ← hqv])
    let recon : FanSurgeryReconstruction hNT site.d0 :=
      ProofsInTheBook.ZinanCh35DeletedAssembly.chordlessRecon_of_fan_pair_seam
        fan hchordless hbig site.d0_tail hbin_mem hbin_head hpT htail_bin_fan_w
        hbin_phi.symm hoPre_surv hoPre_phi
    have hx_head : fan.x = M.head site.d0 := by
      simpa [fan, fanData] using
        NearTriangulation.fan_first_spoke_head (hNT := hNT) fanData
    let avoidColor : α := if M.head site.d0 = p then cp else cq
    let colorWitness :=
      ProofsInTheBook.ZinanCh35ChordlessSite.exists_two_reserved_colors
        (cp := avoidColor)
        (hTL.boundary_ge_three site.v0 site.hv0_boundary site.v0_ne_p site.v0_ne_q
          : 3 ≤ (L site.v0).card)
    let γ : α := Classical.choose colorWitness
    let δ : α := Classical.choose (Classical.choose_spec colorWitness)
    have hcolors := Classical.choose_spec (Classical.choose_spec colorWitness)
    rcases hcolors with ⟨hγ, hδ, hγδ, havoidγ, havoidδ⟩
    refine
      { chordless := hchordless
        v0 := site.v0
        fanData := fanData
        recon := recon
        hd0 := site.d0_tail
        γ := γ
        δ := δ
        γ_mem := hγ
        δ_mem := hδ
        γδ_ne := hγδ
        x_ne := ?_
        w_ne := ?_
        x_precolored := ?_
        deleted_lists := ?_ }
    · rcases site.d0_head_precolored with hphead | hqhead
      · rw [hx_head, hphead]
        exact site.v0_ne_p.symm
      · rw [hx_head, hqhead]
        exact site.v0_ne_q.symm
    · exact ProofsInTheBook.ZinanCh35ChordlessSite.fan_w_ne_v0 fan
    · by_cases hphead : M.head site.d0 = p
      · left
        have hcpγ : cp ≠ γ := by
          change cp ≠ Classical.choose colorWitness
          simpa [avoidColor, hphead] using havoidγ
        have hcpδ : cp ≠ δ := by
          change cp ≠ Classical.choose (Classical.choose_spec colorWitness)
          simpa [avoidColor, hphead] using havoidδ
        exact ⟨hx_head.trans hphead, hcpγ, hcpδ⟩
      · right
        have hqhead : M.head site.d0 = q := by
          rcases site.d0_head_precolored with hp | hq
          · exact False.elim (hphead hp)
          · exact hq
        have hcqγ : cq ≠ γ := by
          change cq ≠ Classical.choose colorWitness
          simpa [avoidColor, hphead] using havoidγ
        have hcqδ : cq ≠ δ := by
          change cq ≠ Classical.choose (Classical.choose_spec colorWitness)
          simpa [avoidColor, hphead] using havoidδ
        exact ⟨hx_head.trans hqhead, hcqγ, hcqδ⟩
    · refine ⟨sectionToDeleted recon p hp_ne_v0, sectionToDeleted recon q hq_ne_v0,
        cp, cq, ?_⟩
      simpa [recon] using
        (fan_pair_deleted_thomassenLists
          fan hTL hchordless hbig site.d0_tail hbin_mem hbin_head hpT
          htail_bin_fan_w hbin_phi.symm hoPre_surv hoPre_phi
          hp_ne_v0 hq_ne_v0 γ δ)

end ProofsInTheBook.ZinanCh35ChordlessSupplier
