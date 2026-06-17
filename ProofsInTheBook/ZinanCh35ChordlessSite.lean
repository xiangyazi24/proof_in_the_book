import ProofsInTheBook.ThomassenLists
import ProofsInTheBook.PlanarMapFanExistence
import ProofsInTheBook.PlanarMapFanSurgery
import Mathlib.Data.Finset.Basic

/-!
# Independent chordless deletion-site plumbing

This file contains small finset, boundary-dart, and fan facts used by the
chordless branch.  It intentionally does not import any deleted-seam assembly
file.
-/

set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35ChordlessSite

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M}

namespace BoundaryCycle

variable {f : M.Face}

/-- The position of a boundary vertex on the cyclic dart list. -/
private lemma exists_pos_of_isBoundaryVertex (C : BoundaryCycle M f) {a : M.Vertex}
    (ha : C.IsBoundaryVertex a) :
    ∃ p : Fin C.darts.length, M.tail (C.darts[p.1]'p.2) = a := by
  have ha' : a ∈ C.darts.map M.tail := by
    simpa [BoundaryCycle.IsBoundaryVertex, C.vertices_eq] using ha
  rw [List.mem_iff_getElem] at ha'
  obtain ⟨p, hp, hget⟩ := ha'
  rw [List.length_map] at hp
  refine ⟨⟨p, hp⟩, ?_⟩
  rwa [List.getElem_map] at hget

/-- Every listed boundary dart has a cyclic predecessor in the same dart list. -/
private lemma exists_phi_pred (C : BoundaryCycle M f) {bout : D} (hbout : bout ∈ C.darts) :
    ∃ bin : D, bin ∈ C.darts ∧ M.φ bin = bout ∧ M.head bin = M.tail bout := by
  classical
  set L := C.darts.length with hL
  have hLpos : 0 < L := C.darts_length_pos
  rw [List.mem_iff_getElem] at hbout
  obtain ⟨q, hq, hgetq⟩ := hbout
  set p : ℕ := (q + L - 1) % L with hp
  have hpL : p < L := by rw [hp]; exact Nat.mod_lt _ hLpos
  have hcyc : (cyclicNext C.normalized.length_pos ⟨p, hpL⟩ : Fin L) = ⟨q, hq⟩ := by
    apply Fin.ext
    show (p + 1) % L = q
    rw [hp]
    rw [Nat.mod_add_mod, show q + L - 1 + 1 = q + L from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hq]
  refine ⟨C.darts[p]'hpL, List.getElem_mem hpL, ?_, ?_⟩
  · have hcp := C.consecutive_phi ⟨p, hpL⟩
    rw [hcyc] at hcp
    have hq' : C.darts.get ⟨q, hq⟩ = C.darts[q]'hq := rfl
    have hp' : C.darts.get ⟨p, hpL⟩ = C.darts[p]'hpL := rfl
    rw [hq', hp', hgetq] at hcp
    exact hcp.symm
  · have hcv := C.consecutive_vertex ⟨p, hpL⟩
    rw [hcyc] at hcv
    have hq' : C.darts.get ⟨q, hq⟩ = C.darts[q]'hq := rfl
    have hp' : C.darts.get ⟨p, hpL⟩ = C.darts[p]'hpL := rfl
    rw [hq', hp', hgetq] at hcv
    exact hcv.symm

/-- `C.darts` is closed under the face successor. -/
private lemma phi_mem_darts (C : BoundaryCycle M f) {d : D} (hd : d ∈ C.darts) :
    M.φ d ∈ C.darts := by
  rw [C.mem_darts_iff] at hd ⊢
  rw [dartFace_phi, hd]

/-- A boundary edge is represented by a listed dart. -/
private lemma exists_dart_of_boundaryEdge (C : BoundaryCycle M f)
    {a b : M.Vertex} (h : C.IsBoundaryEdge s(a, b)) :
    ∃ d : D, d ∈ C.darts ∧ M.dartEdge d = s(a, b) := by
  rw [BoundaryCycle.IsBoundaryEdge, C.edges_eq, List.mem_map] at h
  exact h

end BoundaryCycle

namespace NearTriangulation

variable {v : M.Vertex}

/-- The unique outer dart with a prescribed boundary tail. -/
private lemma exists_unique_outer_tail (hNT : NearTriangulation M)
    (hv : hNT.outerCycle.IsBoundaryVertex v) :
    ∃! bout : D, bout ∈ hNT.outerCycle.darts ∧ M.tail bout = v := by
  classical
  obtain ⟨p, hp⟩ := hNT.outerCycle.exists_pos_of_isBoundaryVertex hv
  refine ⟨hNT.outerCycle.darts[p.1]'p.2, ⟨List.getElem_mem p.2, hp⟩, ?_⟩
  rintro b ⟨hbmem, hbtail⟩
  exact hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hbmem
    (List.getElem_mem p.2) (by rw [hbtail, hp])

/-- The unique outer dart with a prescribed boundary head. -/
private lemma exists_unique_outer_head (hNT : NearTriangulation M)
    (hv : hNT.outerCycle.IsBoundaryVertex v) :
    ∃! bin : D, bin ∈ hNT.outerCycle.darts ∧ M.head bin = v := by
  classical
  obtain ⟨bout, ⟨hboutmem, hbouttail⟩, _⟩ := exists_unique_outer_tail hNT hv
  obtain ⟨bin, hbinmem, _hphi, hhead⟩ := BoundaryCycle.exists_phi_pred hNT.outerCycle hboutmem
  have hbinhead : M.head bin = v := by rw [hhead, hbouttail]
  refine ⟨bin, ⟨hbinmem, hbinhead⟩, ?_⟩
  rintro b ⟨hbmem, hbhead⟩
  have hφb : M.φ b ∈ hNT.outerCycle.darts := BoundaryCycle.phi_mem_darts hNT.outerCycle hbmem
  have hφbin : M.φ bin ∈ hNT.outerCycle.darts := BoundaryCycle.phi_mem_darts hNT.outerCycle hbinmem
  have htails : M.tail (M.φ b) = M.tail (M.φ bin) := by
    rw [tail_phi, tail_phi, hbhead, hbinhead]
  have hφeq : M.φ b = M.φ bin :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hφb hφbin htails
  exact M.φ.injective hφeq

/-- The two outer darts incident with a boundary vertex, in cyclic order. -/
private theorem outer_darts_consecutive (hNT : NearTriangulation M)
    (hv : hNT.outerCycle.IsBoundaryVertex v) :
    ∃ bin bout : D,
      (bin ∈ hNT.outerCycle.darts ∧ M.head bin = v) ∧
      (∀ b, b ∈ hNT.outerCycle.darts → M.head b = v → b = bin) ∧
      (bout ∈ hNT.outerCycle.darts ∧ M.tail bout = v) ∧
      (∀ b, b ∈ hNT.outerCycle.darts → M.tail b = v → b = bout) ∧
      M.φ bin = bout := by
  classical
  obtain ⟨bout, ⟨hboutmem, hbouttail⟩, hboutuniq⟩ := exists_unique_outer_tail hNT hv
  obtain ⟨bin, ⟨hbinmem, hbinhead⟩, hbinuniq⟩ := exists_unique_outer_head hNT hv
  obtain ⟨bpred, hbpredmem, hphi, hhead⟩ := BoundaryCycle.exists_phi_pred hNT.outerCycle hboutmem
  have hpredhead : M.head bpred = v := by rw [hhead, hbouttail]
  have hpred_eq_bin : bpred = bin := hbinuniq bpred ⟨hbpredmem, hpredhead⟩
  refine ⟨bin, bout, ⟨hbinmem, hbinhead⟩, ?_, ⟨hboutmem, hbouttail⟩, ?_, ?_⟩
  · intro b hbmem hbhead; exact hbinuniq b ⟨hbmem, hbhead⟩
  · intro b hbmem hbtail; exact hboutuniq b ⟨hbmem, hbtail⟩
  · rw [← hpred_eq_bin]; exact hphi

end NearTriangulation

/-- A boundary vertex and an oriented dart into `p` suitable for the chordless
deletion branch. -/
structure ChordlessDeletionSite (hNT : NearTriangulation M) (p q : M.Vertex) where
  v0 : M.Vertex
  d0 : D
  hv0_boundary : hNT.outerCycle.IsBoundaryVertex v0
  d0_tail : M.tail d0 = v0
  d0_head : M.head d0 = p
  v0_ne_p : v0 ≠ p
  v0_ne_q : v0 ≠ q
  edge_v0p : hNT.outerCycle.IsBoundaryEdge s(v0, p)

/-- The predecessor and successor boundary neighbors of `p` are distinct. -/
private lemma boundary_neighbors_distinct {bin bout : D}
    (hbin_mem : bin ∈ hNT.outerCycle.darts) (hbout_mem : bout ∈ hNT.outerCycle.darts)
    (hbin_phi : M.φ bin = bout) :
    M.tail bin ≠ M.head bout := by
  intro hxy
  have hφbout_mem : M.φ bout ∈ hNT.outerCycle.darts :=
    BoundaryCycle.phi_mem_darts hNT.outerCycle hbout_mem
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

/-- A `ThomassenLists` boundary edge at `p q` determines a deletion site at the
other boundary neighbor of `p`. -/
theorem exists_chordlessDeletionSite_nonempty {p q : M.Vertex} {L : M.Vertex → Finset α}
    {cp cq : α} (hTL : ThomassenLists hNT p q L cp cq) :
    Nonempty (ChordlessDeletionSite hNT p q) := by
  classical
  obtain ⟨bin, bout, hbin, hbin_unique, hbout, hbout_unique, hbin_phi⟩ :=
    NearTriangulation.outer_darts_consecutive hNT hTL.p_boundary
  rcases hbin with ⟨hbin_mem, hbin_head⟩
  rcases hbout with ⟨hbout_mem, hbout_tail⟩
  let x : M.Vertex := M.tail bin
  let y : M.Vertex := M.head bout
  have hx_boundary : hNT.outerCycle.IsBoundaryVertex x := by
    show M.tail bin ∈ hNT.outerCycle.vertices
    rw [hNT.outerCycle.vertices_eq]
    exact List.mem_map_of_mem hbin_mem
  have hy_boundary : hNT.outerCycle.IsBoundaryVertex y := by
    have hφbout_mem : M.φ bout ∈ hNT.outerCycle.darts :=
      BoundaryCycle.phi_mem_darts hNT.outerCycle hbout_mem
    show M.head bout ∈ hNT.outerCycle.vertices
    rw [hNT.outerCycle.vertices_eq]
    rw [← M.tail_phi bout]
    exact List.mem_map_of_mem hφbout_mem
  have hx_ne_p : x ≠ p := by
    intro h
    exact hNT.simpleGraph.no_loop bin (by simp [x, h, hbin_head])
  have hy_ne_p : y ≠ p := by
    intro h
    exact hNT.simpleGraph.no_loop bout (by rw [hbout_tail]; exact h.symm)
  have hxy : x ≠ y := by
    simpa [x, y] using
      boundary_neighbors_distinct (hNT := hNT) hbin_mem hbout_mem hbin_phi
  have hedge_xp : hNT.outerCycle.IsBoundaryEdge s(x, p) := by
    show s(x, p) ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    have hedge : M.dartEdge bin = s(x, p) := by
      simp [CombMap.dartEdge, x, hbin_head]
    rw [← hedge]
    exact List.mem_map_of_mem hbin_mem
  have hedge_yp : hNT.outerCycle.IsBoundaryEdge s(y, p) := by
    show s(y, p) ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    have hedge : M.dartEdge bout = s(y, p) := by
      simp [CombMap.dartEdge, y, hbout_tail, Sym2.eq_swap]
    rw [← hedge]
    exact List.mem_map_of_mem hbout_mem
  obtain ⟨e, he_mem, he_edge⟩ :=
    BoundaryCycle.exists_dart_of_boundaryEdge hNT.outerCycle hTL.pq_boundary_edge
  have hq_is_neighbor : x = q ∨ y = q := by
    rw [CombMap.dartEdge, Sym2.eq_iff] at he_edge
    rcases he_edge with ⟨hetail, hehead⟩ | ⟨hetail, hehead⟩
    · have he_eq_bout : e = bout := hbout_unique e he_mem hetail
      right
      rw [← hehead, he_eq_bout]
    · have he_eq_bin : e = bin := hbin_unique e he_mem hehead
      left
      rw [← hetail, he_eq_bin]
  rcases hq_is_neighbor with hxq | hyq
  · refine ⟨
      { v0 := y
        d0 := M.α bout
        hv0_boundary := hy_boundary
        d0_tail := by simp [y]
        d0_head := by simp [hbout_tail]
        v0_ne_p := hy_ne_p
        v0_ne_q := ?_
        edge_v0p := hedge_yp }⟩
    intro hyq
    exact hxy (hxq.trans hyq.symm)
  · refine ⟨
      { v0 := x
        d0 := bin
        hv0_boundary := hx_boundary
        d0_tail := rfl
        d0_head := hbin_head
        v0_ne_p := hx_ne_p
        v0_ne_q := ?_
        edge_v0p := hedge_xp }⟩
    intro hxq
    exact hxy (hxq.trans hyq.symm)

/-- A concrete deletion-site witness, extracted from the nonempty theorem. -/
noncomputable def exists_chordlessDeletionSite {p q : M.Vertex} {L : M.Vertex → Finset α}
    {cp cq : α} (hTL : ThomassenLists hNT p q L cp cq) :
    ChordlessDeletionSite hNT p q :=
  Classical.choice (exists_chordlessDeletionSite_nonempty (hNT := hNT) hTL)

/-- Two colors different from `cp` can be reserved from any list of size at least
three. -/
lemma exists_two_reserved_colors {s : Finset α} {cp : α} (hcard : 3 ≤ s.card) :
    ∃ γ δ : α, γ ∈ s ∧ δ ∈ s ∧ γ ≠ δ ∧ cp ≠ γ ∧ cp ≠ δ := by
  classical
  let S := s.erase cp
  have hScard : 1 < S.card := by
    by_cases hcp : cp ∈ s
    · have hS : S.card = s.card - 1 := by
        simp [S, Finset.card_erase_of_mem hcp]
      omega
    · have hS : S.card = s.card := by
        simp [S, Finset.erase_eq_of_notMem hcp]
      omega
  obtain ⟨γ, hγS, δ, hδS, hγδ⟩ := Finset.one_lt_card.mp hScard
  have hγ : γ ∈ s := (Finset.mem_erase.mp hγS).2
  have hδ : δ ∈ s := (Finset.mem_erase.mp hδS).2
  have hcpγ : cp ≠ γ := by
    exact (Finset.mem_erase.mp hγS).1.symm
  have hcpδ : cp ≠ δ := by
    exact (Finset.mem_erase.mp hδS).1.symm
  exact ⟨γ, δ, hγ, hδ, hγδ, hcpγ, hcpδ⟩

/-- Choose two colors reserved at a boundary vertex different from the precolored
endpoints. -/
lemma choose_two_reserved_colors {p q v0 : M.Vertex} {L : M.Vertex → Finset α}
    {cp cq : α} (hTL : ThomassenLists hNT p q L cp cq)
    (hv0_boundary : hNT.outerCycle.IsBoundaryVertex v0)
    (hv0p : v0 ≠ p) (hv0q : v0 ≠ q) :
    ∃ γ δ : α,
      γ ∈ L v0 ∧ δ ∈ L v0 ∧ γ ≠ δ ∧ cp ≠ γ ∧ cp ≠ δ :=
  exists_two_reserved_colors (hTL.boundary_ge_three v0 hv0_boundary hv0p hv0q)

/-- The fan path has a terminal consecutive pair ending at `fan.w`. -/
private lemma exists_terminal_fan_pair (fan : BoundaryVertexFan hNT v0) :
    ∃ a : M.Vertex, (a, fan.w) ∈ consecutivePairs fan.path := by
  classical
  have hterm : ∀ (x : M.Vertex) (l : List M.Vertex),
      ∃ a : M.Vertex, (a, fan.w) ∈ consecutivePairs (x :: l ++ [fan.w]) := by
    intro x l
    induction l generalizing x with
    | nil =>
        refine ⟨x, ?_⟩
        simp [consecutivePairs]
    | cons z zs ih =>
        rcases ih z with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        simp [consecutivePairs] at ha ⊢
        exact Or.inr ha
  rw [BoundaryVertexFan.path, fanPath]
  exact hterm fan.x fan.interior

/-- The terminal boundary endpoint of a certified fan is not the apex. -/
lemma fan_w_ne_v0 (fan : BoundaryVertexFan hNT v0) : fan.w ≠ v0 := by
  obtain ⟨a, ha⟩ := exists_terminal_fan_pair (hNT := hNT) (v0 := v0) fan
  have T : FanTriangle hNT v0 fan.w a := fan.incident_faces_exact.triangle_of_pair ha
  exact T.vertices_pairwiseDistinct.1.symm

end ProofsInTheBook.ZinanCh35ChordlessSite
