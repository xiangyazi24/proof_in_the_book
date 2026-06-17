import ProofsInTheBook.PlanarMapBoundary

/-!
# Near-triangulations of combinatorial sphere maps

This file packages the boundary-cycle data from `PlanarMapBoundary` into the
near-triangulation invariant used in the Chapter 35 Thomassen route.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A near-triangulation is a simple sphere map with one distinguished simple
outer boundary cycle of length at least three; every other face has length
three. -/
structure NearTriangulation (M : CombMap D) where
  sphere : M.IsSphereMap
  simpleGraph : M.IsSimpleGraph
  outerFace : M.Face
  outerCycle : BoundaryCycle M outerFace
  outer_simple : outerCycle.VertexNodup
  outer_len : 3 ≤ outerCycle.length
  inner_tri : ∀ f : M.Face, f ≠ outerFace → M.faceLen f = 3

@[simp]
lemma dartFace_phi (M : CombMap D) (d : D) :
    M.dartFace (M.φ d) = M.dartFace d := by
  unfold dartFace
  exact Quotient.sound ⟨-1, by simp⟩

@[simp]
lemma dartFace_phi_symm (M : CombMap D) (d : D) :
    M.dartFace (M.φ.symm d) = M.dartFace d := by
  unfold dartFace
  exact Quotient.sound ⟨1, by simp⟩

lemma phi_ne_self_of_isSimpleGraph (M : CombMap D) (hM : M.IsSimpleGraph) (d : D) :
    M.φ d ≠ d := by
  intro h
  have htail : M.head d = M.tail d := by
    calc
      M.head d = M.tail (M.φ d) := (M.tail_phi d).symm
      _ = M.tail d := by rw [h]
  exact hM.no_loop d htail.symm

lemma vertexDegree_tail_eq_card_support_cycleOf (M : CombMap D) {d : D}
    (hσ : M.σ d ≠ d) :
    M.vertexDegree (M.tail d) = (M.σ.cycleOf d).support.card := by
  have hset :
      (Finset.univ.filter
          (fun x => Quotient.mk (cycleSetoid M.σ) x = M.tail d))
        = (M.σ.cycleOf d).support := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, tail,
      Equiv.Perm.mem_support_cycleOf_iff' hσ, Quotient.eq]
    exact Equiv.Perm.sameCycle_comm
  simpa [vertexDegree] using congrArg Finset.card hset

lemma faceLen_dartFace_eq_card_support_cycleOf (M : CombMap D) {d : D}
    (hφ : M.φ d ≠ d) :
    M.faceLen (M.dartFace d) = (M.φ.cycleOf d).support.card := by
  have hset :
      (Finset.univ.filter
          (fun x => Quotient.mk (cycleSetoid M.φ) x = M.dartFace d))
        = (M.φ.cycleOf d).support := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, dartFace,
      Equiv.Perm.mem_support_cycleOf_iff' hφ, Quotient.eq]
    exact Equiv.Perm.sameCycle_comm
  simpa [faceLen] using congrArg Finset.card hset

lemma card_support_cycleOf_eq_two_of_apply_apply_eq_self
    (p : Equiv.Perm D) {d : D} (hp : p d ≠ d) (h2 : p (p d) = d) :
    (p.cycleOf d).support.card = 2 := by
  have hc : Equiv.Perm.IsCycle (p.cycleOf d) :=
    Equiv.Perm.isCycle_cycleOf p hp
  have hcd : p.cycleOf d d = p d :=
    Equiv.Perm.cycleOf_apply_self p d
  have hcpd : p.cycleOf d (p d) = d := by
    have hsc : p.SameCycle d (p d) := by
      simpa using (Equiv.Perm.sameCycle_apply_right (f := p) (x := d) (y := d)).2
        Equiv.Perm.SameCycle.rfl
    simp [h2, hsc.cycleOf_apply]
  have hcd_ne : p.cycleOf d d ≠ d := by
    simpa [hcd] using hp
  have hcycle2 : p.cycleOf d (p.cycleOf d d) = d := by
    simpa [hcd] using hcpd
  have hswap := hc.eq_swap_of_apply_apply_eq_self hcd_ne hcycle2
  rw [hswap, Equiv.Perm.card_support_swap hcd_ne.symm]

namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}

lemma faceLen_eq_length (C : BoundaryCycle M f) :
    M.faceLen f = C.length := by
  have hcard := congrArg Finset.card C.normalized.toFinset_eq
  have horbit : (faceOrbitFinset M f).card = M.faceLen f := by
    rfl
  rw [List.toFinset_card_of_nodup C.normalized.nodup, horbit] at hcard
  exact hcard.symm

lemma tail_injective_on_darts (C : BoundaryCycle M f) (hC : C.VertexNodup)
    {d e : D} (hd : d ∈ C.darts) (he : e ∈ C.darts)
    (htail : M.tail d = M.tail e) :
    d = e := by
  have hmap : (C.darts.map M.tail).Nodup := by
    simpa [BoundaryCycle.VertexNodup, C.vertices_eq] using hC
  exact List.inj_on_of_nodup_map hmap hd he htail

end BoundaryCycle

lemma faceLen_three_phi_cube_eq_self (M : CombMap D) (hM : M.IsSimpleGraph)
    {d : D} (hlen : M.faceLen (M.dartFace d) = 3) :
    (M.φ ^ 3) d = d := by
  have hφ : M.φ d ≠ d := phi_ne_self_of_isSimpleGraph M hM d
  have hcard : (M.φ.cycleOf d).support.card = 3 := by
    rw [← faceLen_dartFace_eq_card_support_cycleOf M hφ, hlen]
  have hpow := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply M.φ 3 d
  rw [hcard] at hpow
  simpa using hpow.symm

lemma faceLen_three_isFaceTriangle (M : CombMap D) (hM : M.IsSimpleGraph)
    {d : D} (hlen : M.faceLen (M.dartFace d) = 3) :
    M.IsFaceTriangle d (M.φ d) (M.φ (M.φ d)) := by
  refine ⟨rfl, rfl, ?_⟩
  have hcube := faceLen_three_phi_cube_eq_self M hM hlen
  simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube

lemma faceLen_three_vertices_pairwiseDistinct (M : CombMap D) (hM : M.IsSimpleGraph)
    {d : D} (hlen : M.faceLen (M.dartFace d) = 3) :
    M.tail d ≠ M.tail (M.φ d) ∧
      M.tail (M.φ d) ≠ M.tail (M.φ (M.φ d)) ∧
      M.tail (M.φ (M.φ d)) ≠ M.tail d := by
  exact M.isFaceTriangle_vertices_pairwiseDistinct hM
    (faceLen_three_isFaceTriangle M hM hlen)

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

lemma outer_faceLen_eq_outerCycle_length :
    M.faceLen hNT.outerFace = hNT.outerCycle.length :=
  hNT.outerCycle.faceLen_eq_length

lemma boundary_dart_no_loop {d : D} (_hd : d ∈ hNT.outerCycle.darts) :
    M.tail d ≠ M.head d :=
  hNT.simpleGraph.no_loop d

lemma boundary_dart_sigma_ne {d : D} (hd : d ∈ hNT.outerCycle.darts) :
    M.σ d ≠ d := by
  intro hσ
  have hdface : M.dartFace d = hNT.outerFace :=
    (hNT.outerCycle.mem_darts_iff d).mp hd
  have hp : M.φ.symm d ∈ hNT.outerCycle.darts := by
    rw [hNT.outerCycle.mem_darts_iff]
    simp [hdface]
  have hq : M.φ d ∈ hNT.outerCycle.darts := by
    rw [hNT.outerCycle.mem_darts_iff]
    simp [hdface]
  have hαp : M.α (M.φ.symm d) = d := by
    apply M.σ.injective
    change M.φ (M.φ.symm d) = M.σ d
    rw [Equiv.apply_symm_apply, hσ]
  have hp_eq_alpha : M.φ.symm d = M.α d := by
    rw [← M.alpha_alpha (M.φ.symm d), hαp]
  have htail : M.tail (M.φ.symm d) = M.tail (M.φ d) := by
    rw [hp_eq_alpha]
    simp
  have hpq : M.φ.symm d = M.φ d :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hp hq htail
  have hφ2 : M.φ (M.φ d) = d := by
    simpa using (congrArg M.φ hpq).symm
  have hφ : M.φ d ≠ d :=
    phi_ne_self_of_isSimpleGraph M hNT.simpleGraph d
  have hcard2 :
      (M.φ.cycleOf d).support.card = 2 :=
    card_support_cycleOf_eq_two_of_apply_apply_eq_self M.φ hφ hφ2
  have hface2 : M.faceLen hNT.outerFace = 2 := by
    have hsupport := faceLen_dartFace_eq_card_support_cycleOf M hφ
    rw [hdface, hcard2] at hsupport
    exact hsupport
  have hlen2 : hNT.outerCycle.length = 2 :=
    hNT.outerCycle.faceLen_eq_length.symm.trans hface2
  have hge : 3 ≤ hNT.outerCycle.length := hNT.outer_len
  omega

lemma boundary_vertex_degree_ge_two {v : M.Vertex}
    (hv : hNT.outerCycle.IsBoundaryVertex v) :
    2 ≤ M.vertexDegree v := by
  have hv' : v ∈ hNT.outerCycle.darts.map M.tail := by
    simpa [BoundaryCycle.IsBoundaryVertex, hNT.outerCycle.vertices_eq] using hv
  rcases List.mem_map.mp hv' with ⟨d, hd, rfl⟩
  have hσ : M.σ d ≠ d := hNT.boundary_dart_sigma_ne hd
  rw [vertexDegree_tail_eq_card_support_cycleOf M hσ]
  exact (Equiv.Perm.two_le_card_support_cycleOf_iff).2 hσ

lemma inner_faceLen_eq_three {f : M.Face} (hf : f ≠ hNT.outerFace) :
    M.faceLen f = 3 :=
  hNT.inner_tri f hf

/-- A near-triangulation has all face lengths at least three: the distinguished
outer face has length at least three, and every other face is triangular. -/
lemma faceLengthGe_three (hNT : NearTriangulation M) : M.FaceLengthGe 3 := by
  intro f
  by_cases hf : f = hNT.outerFace
  · subst f
    rw [hNT.outer_faceLen_eq_outerCycle_length]
    exact hNT.outer_len
  · rw [hNT.inner_faceLen_eq_three hf]

/-- A near-triangulation has at least three vertices, witnessed by the simple
outer boundary cycle. -/
lemma three_le_V (hNT : NearTriangulation M) : 3 ≤ M.V := by
  classical
  have hnodup : hNT.outerCycle.vertices.Nodup := hNT.outer_simple
  have hlen : 3 ≤ hNT.outerCycle.vertices.length := by
    rw [hNT.outerCycle.vertices_length]
    exact hNT.outer_len
  have hcard : 3 ≤ hNT.outerCycle.vertices.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnodup]
    exact hlen
  calc
    3 ≤ hNT.outerCycle.vertices.toFinset.card := hcard
    _ ≤ Fintype.card M.Vertex := Finset.card_le_univ _
    _ = M.V := rfl

/-- Euler's degree seed specialized to near-triangulations. -/
lemma exists_vertexDegree_le_five (hNT : NearTriangulation M) :
    ∃ v : M.Vertex, M.vertexDegree v ≤ 5 :=
  _root_.ProofsInTheBook.PlanarMap.CombMap.exists_vertexDegree_le_five M
    hNT.sphere (faceLengthGe_three hNT) (three_le_V hNT)

lemma inner_face_isFaceTriangle {d : D}
    (hd : M.dartFace d ≠ hNT.outerFace) :
    M.IsFaceTriangle d (M.φ d) (M.φ (M.φ d)) := by
  exact faceLen_three_isFaceTriangle M hNT.simpleGraph (hNT.inner_tri (M.dartFace d) hd)

lemma inner_face_vertices_pairwiseDistinct {d : D}
    (hd : M.dartFace d ≠ hNT.outerFace) :
    M.tail d ≠ M.tail (M.φ d) ∧
      M.tail (M.φ d) ≠ M.tail (M.φ (M.φ d)) ∧
      M.tail (M.φ (M.φ d)) ≠ M.tail d := by
  exact faceLen_three_vertices_pairwiseDistinct M hNT.simpleGraph
    (hNT.inner_tri (M.dartFace d) hd)

lemma chord_endpoints_nonadjacent_on_boundary {u v : M.Vertex}
    (h : hNT.outerCycle.Chord u v) :
    ¬ hNT.outerCycle.IsBoundaryEdge s(u, v) :=
  h.not_boundary_edge

lemma same_face_edge_is_boundary_edge {d : D}
    (hsame : M.dartFace d = M.dartFace (M.α d)) :
    hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) := by
  by_cases houter : M.dartFace d = hNT.outerFace
  · show M.dartEdge d ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    exact List.mem_map_of_mem ((hNT.outerCycle.mem_darts_iff d).mpr houter)
  · exfalso
    have hlen : M.faceLen (M.dartFace d) = 3 :=
      hNT.inner_tri (M.dartFace d) houter
    have hverts := faceLen_three_vertices_pairwiseDistinct M hNT.simpleGraph hlen
    have hφ : M.φ d ≠ d :=
      phi_ne_self_of_isSimpleGraph M hNT.simpleGraph d
    have hcard : (M.φ.cycleOf d).support.card = 3 := by
      rw [← faceLen_dartFace_eq_card_support_cycleOf M hφ, hlen]
    have hcycle : M.φ.SameCycle d (M.α d) := by
      exact Quotient.exact hsame
    have hsupport : d ∈ M.φ.support := by
      simpa [Equiv.Perm.mem_support] using hφ
    obtain ⟨i, hi, hipow⟩ := hcycle.exists_pow_eq_of_mem_support hsupport
    rw [hcard] at hi
    interval_cases i
    · simp at hipow
      exact M.α_no_fixed d hipow.symm
    · have hα : M.φ d = M.α d := by
        simpa using hipow
      have htail : M.tail (M.φ (M.φ d)) = M.tail d := by
        rw [hα]
        simp
      exact hverts.2.2 htail
    · have hα : M.φ (M.φ d) = M.α d := by
        simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hipow
      have htail : M.tail (M.φ d) = M.tail (M.φ (M.φ d)) := by
        rw [hα]
        simp
      exact hverts.2.1 htail

/-- A near-triangulation has no non-boundary bridge: if both darts of an edge
lie on the same face, that edge must occur on the distinguished outer cycle. -/
lemma no_bridges {d : D}
    (hsame : M.dartFace d = M.dartFace (M.α d)) :
    hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) :=
  hNT.same_face_edge_is_boundary_edge hsame

/-- For every edge, the two incident faces are distinct unless the edge belongs
to the distinguished simple outer boundary cycle. -/
lemma edge_faces_distinct_or_boundary_edge (d : D) :
    M.dartFace d ≠ M.dartFace (M.α d) ∨
      hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) := by
  by_cases hsame : M.dartFace d = M.dartFace (M.α d)
  · exact Or.inr (hNT.no_bridges hsame)
  · exact Or.inl hsame

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
