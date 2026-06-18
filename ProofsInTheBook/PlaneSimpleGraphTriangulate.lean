import ProofsInTheBook.PlaneSimpleGraph
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.FaceDiagonalSurgery
import ProofsInTheBook.ZinanCh35BoundaryAssembler
import ProofsInTheBook.ZinanCh35Final

/-!
# Bridges from `PlaneSimpleGraph` to `CombMap`

This file supplies the first route-A bridges needed to use the already-developed
combinatorial-map infrastructure on embedded simple graphs.
-/

set_option linter.unusedSectionVars false

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace PlaneSimpleGraph

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

lemma raw_tail_sigma_pow (P : PlaneSimpleGraph V D) (d : D) (n : ℕ) :
    P.tail ((P.σ ^ n) d) = P.tail d := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, P.σ_preserves_tail, ih]

lemma raw_tail_eq_of_sigma_sameCycle (P : PlaneSimpleGraph V D) {d e : D}
    (h : P.σ.SameCycle d e) :
    P.tail d = P.tail e := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn, P.raw_tail_sigma_pow]

lemma comb_tail_eq_of_raw_tail_eq (P : PlaneSimpleGraph V D) {d e : D}
    (h : P.tail d = P.tail e) :
    P.toCombMap.tail d = P.toCombMap.tail e := by
  unfold PlaneSimpleGraph.toCombMap CombMap.tail
  exact Quotient.sound (P.σ_vertex_cycle d e h)

lemma raw_tail_eq_of_comb_tail_eq (P : PlaneSimpleGraph V D) {d e : D}
    (h : P.toCombMap.tail d = P.toCombMap.tail e) :
    P.tail d = P.tail e := by
  exact P.raw_tail_eq_of_sigma_sameCycle (Quotient.exact h)

lemma raw_head_eq_of_comb_head_eq (P : PlaneSimpleGraph V D) {d e : D}
    (h : P.toCombMap.head d = P.toCombMap.head e) :
    P.head d = P.head e := by
  have ht : P.tail (P.α d) = P.tail (P.α e) :=
    P.raw_tail_eq_of_comb_tail_eq (by simpa [PlaneSimpleGraph.toCombMap, CombMap.head] using h)
  simpa [P.reverse_tail] using ht

/-- The `σ`-orbit vertices of `toCombMap` are the original graph vertices, provided every
graph vertex is incident to some dart. -/
noncomputable def vertexEquiv (P : PlaneSimpleGraph V D)
    (hincident : ∀ v : V, ∃ d : D, P.tail d = v) :
    P.toCombMap.Vertex ≃ V where
  toFun := Quotient.lift P.tail (by
    intro d e h
    exact P.raw_tail_eq_of_sigma_sameCycle (by simpa [PlaneSimpleGraph.toCombMap] using h))
  invFun := fun v => Quotient.mk (CombMap.cycleSetoid P.toCombMap.σ) (Classical.choose (hincident v))
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro d
    change Quotient.mk (CombMap.cycleSetoid P.toCombMap.σ)
        (Classical.choose (hincident (P.tail d))) =
      Quotient.mk (CombMap.cycleSetoid P.toCombMap.σ) d
    exact Quotient.sound
      (P.σ_vertex_cycle _ _ ((Classical.choose_spec (hincident (P.tail d))).trans rfl))
  right_inv := by
    intro v
    exact Classical.choose_spec (hincident v)

theorem toCombMap_V_eq_card (P : PlaneSimpleGraph V D)
    (hincident : ∀ v : V, ∃ d : D, P.tail d = v) :
    P.toCombMap.V = Fintype.card V := by
  exact Fintype.card_congr (P.vertexEquiv hincident)

theorem toCombMap_E_eq_numEdges (P : PlaneSimpleGraph V D) :
    P.toCombMap.E = P.numEdges := by
  unfold PlaneSimpleGraph.numEdges
  have h := P.toCombMap.two_mul_E_eq_card
  omega

@[simp] theorem toCombMap_F_eq_numFaces (P : PlaneSimpleGraph V D) :
    P.toCombMap.F = P.numFaces := rfl

theorem toCombMap_eulerChar_eq (P : PlaneSimpleGraph V D)
    (hincident : ∀ v : V, ∃ d : D, P.tail d = v) :
    P.toCombMap.eulerChar = P.eulerChar := by
  unfold CombMap.eulerChar PlaneSimpleGraph.eulerChar
  rw [P.toCombMap_V_eq_card hincident, P.toCombMap_E_eq_numEdges]
  rfl

lemma comb_connected_of_graph_reachable (P : PlaneSimpleGraph V D)
    {u v : V} (hreach : P.G.Reachable u v)
    {a b : D} (ha : P.tail a = u) (hb : P.tail b = v) :
    Relation.ReflTransGen P.toCombMap.dartStep a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach generalizing a b with
  | refl =>
      apply Relation.ReflTransGen.single
      left
      exact P.σ_vertex_cycle a b (ha.trans hb.symm)
  | tail hpath hadj ih =>
      rename_i w
      rcases P.edge_darts hadj with ⟨d, hd, _huniq⟩
      have h₁ : Relation.ReflTransGen P.toCombMap.dartStep a d :=
        ih ha hd.1
      have h₂ : P.toCombMap.dartStep d (P.α d) := Or.inr rfl
      have htailα : P.tail (P.α d) = w := by simpa [P.reverse_tail] using hd.2
      have h₃ : P.toCombMap.dartStep (P.α d) b :=
        Or.inl (P.σ_vertex_cycle (P.α d) b (htailα.trans hb.symm))
      exact h₁.trans ((Relation.ReflTransGen.single h₂).trans (Relation.ReflTransGen.single h₃))

theorem toCombMap_connected (P : PlaneSimpleGraph V D) :
    P.toCombMap.Connected := by
  intro a b
  exact P.comb_connected_of_graph_reachable (P.connected (P.tail a) (P.tail b)) rfl rfl

theorem toCombMap_isSphereMap (P : PlaneSimpleGraph V D)
    (hsphere : P.IsSphereMap) (hincident : ∀ v : V, ∃ d : D, P.tail d = v) :
    P.toCombMap.IsSphereMap := by
  refine ⟨P.toCombMap_connected, ?_⟩
  rw [P.toCombMap_eulerChar_eq hincident]
  exact hsphere

theorem toCombMap_isSimpleGraph (P : PlaneSimpleGraph V D) :
    P.toCombMap.IsSimpleGraph where
  no_loop d := by
    intro h
    have hrawTail : P.tail d = P.tail (P.α d) :=
      P.raw_tail_eq_of_comb_tail_eq (by simpa [CombMap.head] using h)
    have hraw : P.tail d = P.head d := by
      simpa [P.reverse_tail] using hrawTail
    exact P.G.loopless.irrefl (P.tail d) (by simpa [hraw] using P.dart_edge d)
  no_parallel {d e} h := by
    unfold CombMap.dartEdge at h
    rcases Sym2.eq_iff.1 h with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · have htail : P.tail d = P.tail e := P.raw_tail_eq_of_comb_tail_eq ht
      have hhead : P.head d = P.head e := P.raw_head_eq_of_comb_head_eq hh
      rcases P.edge_darts (P.dart_edge d) with ⟨x, hx, huniq⟩
      have hd : d = x := huniq d ⟨rfl, rfl⟩
      have he : e = x := huniq e ⟨htail.symm, hhead.symm⟩
      rw [hd, he]
    · have htailRaw : P.tail d = P.tail (P.α e) := P.raw_tail_eq_of_comb_tail_eq ht
      have htail : P.tail d = P.head e := by
        simpa [P.reverse_tail] using htailRaw
      have hheadRaw : P.tail (P.α d) = P.tail e :=
        P.raw_tail_eq_of_comb_tail_eq (by simpa [CombMap.head] using hh)
      have hhead : P.head d = P.tail e := by
        simpa [P.reverse_tail] using hheadRaw
      rcases P.edge_darts (P.dart_edge d) with ⟨x, hx, huniq⟩
      have hd : d = x := huniq d ⟨rfl, rfl⟩
      have he : P.α e = x := huniq (P.α e) ⟨by simpa [P.reverse_tail] using htail.symm,
        by simpa [P.reverse_head] using hhead.symm⟩
      have hde : d = P.α e := hd.trans he.symm
      rw [hde]
      exact ((P.toCombMap.alpha_sameCycle_iff e (P.α e)).2 (Or.inr rfl)).symm

theorem toCombMap_adj_embed (P : PlaneSimpleGraph V D)
    (hincident : ∀ v : V, ∃ d : D, P.tail d = v)
    {u v : V} (hadj : P.G.Adj u v) :
    P.toCombMap.toSimpleGraph.Adj
      ((P.vertexEquiv hincident).symm u)
      ((P.vertexEquiv hincident).symm v) := by
  rcases P.edge_darts hadj with ⟨d, hd, _huniq⟩
  have hu : (P.vertexEquiv hincident).symm u = P.toCombMap.tail d := by
    apply (P.vertexEquiv hincident).injective
    rw [Equiv.apply_symm_apply]
    change u = P.tail d
    exact hd.1.symm
  have hv : (P.vertexEquiv hincident).symm v = P.toCombMap.head d := by
    apply (P.vertexEquiv hincident).injective
    rw [Equiv.apply_symm_apply]
    change v = P.tail (P.α d)
    rw [P.reverse_tail, hd.2]
  rw [hu, hv]
  exact P.toCombMap.toSimpleGraph_adj_of_dart P.toCombMap_isSimpleGraph d

end PlaneSimpleGraph

/-! ## The triangle witness -/

abbrev TriV := Fin 3
abbrev TriD := Fin 6

namespace TriangleWitness

open PlaneSimpleGraph

def triTail : TriD → TriV := fun d =>
  if d = 0 then 0 else
  if d = 1 then 1 else
  if d = 2 then 1 else
  if d = 3 then 2 else
  if d = 4 then 2 else
  0

def triHead : TriD → TriV := fun d =>
  if d = 0 then 1 else
  if d = 1 then 0 else
  if d = 2 then 2 else
  if d = 3 then 1 else
  if d = 4 then 0 else
  2

def triAlphaFun : TriD → TriD := fun d =>
  if d = 0 then 1 else
  if d = 1 then 0 else
  if d = 2 then 3 else
  if d = 3 then 2 else
  if d = 4 then 5 else
  4

def triSigmaFun : TriD → TriD := fun d =>
  if d = 0 then 5 else
  if d = 5 then 0 else
  if d = 1 then 2 else
  if d = 2 then 1 else
  if d = 3 then 4 else
  3

def triAlpha : Equiv.Perm TriD where
  toFun := triAlphaFun
  invFun := triAlphaFun
  left_inv := by intro d; fin_cases d <;> simp [triAlphaFun]
  right_inv := by intro d; fin_cases d <;> simp [triAlphaFun]

def triSigma : Equiv.Perm TriD where
  toFun := triSigmaFun
  invFun := triSigmaFun
  left_inv := by intro d; fin_cases d <;> simp [triSigmaFun]
  right_inv := by intro d; fin_cases d <;> simp [triSigmaFun]

lemma triAlpha_invol : triAlpha * triAlpha = 1 := by
  ext d
  fin_cases d <;> simp [triAlpha, triAlphaFun]

lemma triAlpha_no_fixed : ∀ d : TriD, triAlpha d ≠ d := by
  intro d
  fin_cases d <;> simp [triAlpha, triAlphaFun]

lemma triReverse_tail : ∀ d : TriD, triTail (triAlpha d) = triHead d := by
  intro d
  fin_cases d <;> simp [triTail, triHead, triAlpha, triAlphaFun]

lemma triReverse_head : ∀ d : TriD, triHead (triAlpha d) = triTail d := by
  intro d
  fin_cases d <;> simp [triTail, triHead, triAlpha, triAlphaFun]

lemma triSigma_preserves_tail : ∀ d : TriD, triTail (triSigma d) = triTail d := by
  intro d
  fin_cases d <;> simp [triTail, triSigma, triSigmaFun]

lemma triSigma_vertex_cycle : ∀ d e : TriD, triTail d = triTail e → triSigma.SameCycle d e := by
  intro d e h
  fin_cases d <;> fin_cases e <;> simp [triTail] at h
  <;> decide

lemma triangle_dart_edge : ∀ d : TriD, (⊤ : SimpleGraph TriV).Adj (triTail d) (triHead d) := by
  intro d
  fin_cases d <;> simp [triTail, triHead]

lemma triangle_edge_darts :
    ∀ {u v : TriV}, (⊤ : SimpleGraph TriV).Adj u v →
      ∃! d : TriD, triTail d = u ∧ triHead d = v := by
  intro u v h
  fin_cases u <;> fin_cases v <;> simp at h ⊢
  · refine ⟨0, by simp [triTail, triHead], ?_⟩
    intro d hd; fin_cases d <;> simp [triTail, triHead] at hd ⊢
  · refine ⟨5, by simp [triTail, triHead], ?_⟩
    intro d hd; fin_cases d <;> simp [triTail, triHead] at hd ⊢
  · refine ⟨1, by simp [triTail, triHead], ?_⟩
    intro d hd; fin_cases d <;> simp [triTail, triHead] at hd ⊢
  · refine ⟨2, by simp [triTail, triHead], ?_⟩
    intro d hd; fin_cases d <;> simp [triTail, triHead] at hd ⊢
  · refine ⟨4, by simp [triTail, triHead], ?_⟩
    intro d hd; fin_cases d <;> simp [triTail, triHead] at hd ⊢
  · refine ⟨3, by simp [triTail, triHead], ?_⟩
    intro d hd; fin_cases d <;> simp [triTail, triHead] at hd ⊢

/-- The plane simple graph of a triangle, encoded by its six oriented darts. -/
def trianglePlaneSimpleGraph : PlaneSimpleGraph TriV TriD where
  G := ⊤
  tail := triTail
  head := triHead
  α := triAlpha
  σ := triSigma
  α_invol := triAlpha_invol
  α_no_fixed := triAlpha_no_fixed
  reverse_tail := triReverse_tail
  reverse_head := triReverse_head
  dart_edge := triangle_dart_edge
  edge_darts := @triangle_edge_darts
  σ_preserves_tail := triSigma_preserves_tail
  σ_vertex_cycle := triSigma_vertex_cycle
  connected := by
    simpa using (SimpleGraph.connected_top (V := TriV))

lemma triangle_incident : ∀ v : TriV, ∃ d : TriD, trianglePlaneSimpleGraph.tail d = v := by
  intro v
  fin_cases v
  · exact ⟨0, by simp [trianglePlaneSimpleGraph, triTail]⟩
  · exact ⟨1, by simp [trianglePlaneSimpleGraph, triTail]⟩
  · exact ⟨3, by simp [trianglePlaneSimpleGraph, triTail]⟩

lemma triangle_numFaces : trianglePlaneSimpleGraph.numFaces = 2 := by
  unfold PlaneSimpleGraph.numFaces CombMap.F CombMap.cycleSetoid CombMap.φ
    trianglePlaneSimpleGraph triAlpha triSigma triAlphaFun triSigmaFun
  decide

theorem triangle_plane_isSphere : trianglePlaneSimpleGraph.IsSphereMap := by
  unfold PlaneSimpleGraph.IsSphereMap PlaneSimpleGraph.eulerChar PlaneSimpleGraph.numVertices
    PlaneSimpleGraph.numEdges
  rw [triangle_numFaces]
  norm_num

theorem triangle_toCombMap_isSphereMap : trianglePlaneSimpleGraph.toCombMap.IsSphereMap :=
  trianglePlaneSimpleGraph.toCombMap_isSphereMap triangle_plane_isSphere triangle_incident

theorem triangle_toCombMap_isSimpleGraph : trianglePlaneSimpleGraph.toCombMap.IsSimpleGraph :=
  trianglePlaneSimpleGraph.toCombMap_isSimpleGraph

end TriangleWitness

/-! ## End-wiring through a triangulation extension certificate -/

universe u v u'

section Extension

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A certificate that an embedded simple graph `P` is represented as a subgraph of a
near-triangulation `T`.  This is the endpoint wiring interface: phases P2--P4 will produce
such certificates, while this structure only records the data needed for color pullback. -/
structure PlaneTriangulationExtension (P : PlaneSimpleGraph V D) where
  D' : Type u'
  fintypeD' : Fintype D'
  decidableEqD' : DecidableEq D'
  T : @CombMap D' fintypeD' decidableEqD'
  hNT : T.NearTriangulation
  ιV : V → T.Vertex
  adj_embed : ∀ {u v : V}, P.G.Adj u v → T.toSimpleGraph.Adj (ιV u) (ιV v)

/-- Pull a five-colouring of the triangulating near-triangulation back along the embedded
vertex map. -/
theorem colorable_of_triangulationExtension (P : PlaneSimpleGraph V D)
    (E : PlaneTriangulationExtension P) :
    P.G.Colorable 5 := by
  letI := E.fintypeD'
  letI := E.decidableEqD'
  rcases ProofsInTheBook.ZinanCh35Final.fiveColor_planar_canonical E.hNT with ⟨C⟩
  exact ⟨SimpleGraph.Coloring.mk (fun v => C (E.ιV v)) (by
    intro u v huv
    exact C.valid (E.adj_embed huv))⟩

/-- Five-colourability of a plane simple graph from a triangulation-extension certificate.
This is the P5a endpoint; later phases replace the certificate by a producer. -/
theorem fiveColor_planeSimpleGraph_of_extension (P : PlaneSimpleGraph V D)
    (E : PlaneTriangulationExtension P) :
    P.G.Colorable 5 :=
  colorable_of_triangulationExtension P E

end Extension

/-! ## Route-B diagonal existence supplier -/

/-- Uniform supplier of a valid diagonal in every non-triangular face of every simple sphere
combinatorial map.  This is the route-B residual for the maximal-plane-graph theorem; it is
uniform over the current map, so it remains available after each diagonal insertion step. -/
structure FaceDiagonalSupplier : Type (u + 1) where
  exists_choice :
    ∀ {D : Type u} [Fintype D] [DecidableEq D] (M : CombMap D),
      M.IsSphereMap → M.IsSimpleGraph →
        ∀ f : M.Face, 3 < M.faceLen f → Nonempty (M.FaceDiagonalChoice)

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

lemma faceDartList_length_eq_faceLen (M : CombMap D) {root : D}
    (hφ : M.φ root ≠ root) :
    (M.faceDartList root).length = M.faceLen (M.dartFace root) := by
  rw [faceLen_dartFace_eq_card_support_cycleOf M hφ]
  simp [faceDartList, Equiv.Perm.length_toList]

lemma faceDartList_eq_triple_of_faceLen_three (M : CombMap D) (hSimple : M.IsSimpleGraph)
    {root : D} (hlen : M.faceLen (M.dartFace root) = 3) :
    M.faceDartList root = [root, M.φ root, M.φ (M.φ root)] := by
  have hφ : M.φ root ≠ root := phi_ne_self_of_isSimpleGraph M hSimple root
  have hlenList : (M.faceDartList root).length = 3 := by
    rw [M.faceDartList_length_eq_faceLen hφ, hlen]
  apply List.ext_getElem
  · simp [hlenList]
  · intro n hleft hright
    have hn : n < 3 := by
      simpa [hlenList] using hleft
    interval_cases n
    · have hget := M.faceDartList_getElem root 0 hleft
      simpa using hget
    · have hget := M.faceDartList_getElem root 1 hleft
      simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hget
    · have hget := M.faceDartList_getElem root 2 hleft
      simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hget

lemma faceDartList_tail_nodup_of_faceLen_three (M : CombMap D) (hSimple : M.IsSimpleGraph)
    {root : D} (hlen : M.faceLen (M.dartFace root) = 3) :
    ((M.faceDartList root).map M.tail).Nodup := by
  rw [M.faceDartList_eq_triple_of_faceLen_three hSimple hlen]
  have hverts := faceLen_three_vertices_pairwiseDistinct M hSimple hlen
  change [M.tail root, M.tail (M.φ root), M.tail (M.φ (M.φ root))].Nodup
  refine List.nodup_cons.mpr ?_
  constructor
  · intro hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with h | h
    · exact hverts.1 h
    · rcases h with h' | hnil
      · exact hverts.2.2 h'.symm
      · cases hnil
  · refine List.nodup_cons.mpr ?_
    constructor
    · intro hmem
      have h' : M.tail (M.φ root) = M.tail (M.φ (M.φ root)) := by
        simpa only [List.mem_singleton] using hmem
      exact hverts.2.1 h'
    · exact List.nodup_singleton _

/-- A fully triangular simple sphere map is a near-triangulation, with an arbitrary
face chosen as the outer face. -/
noncomputable def buildNearTriangulationFromAllTriangular (M : CombMap D)
    (hS : M.IsSphereMap) (hSimple : M.IsSimpleGraph)
    (htri : ∀ f : M.Face, M.faceLen f = 3) [Nonempty D] :
    M.NearTriangulation := by
  let root : D := Classical.choice inferInstance
  let outerFace : M.Face := M.dartFace root
  have hφ : M.φ root ≠ root := phi_ne_self_of_isSimpleGraph M hSimple root
  have hnodup : ((M.faceDartList root).map M.tail).Nodup :=
    M.faceDartList_tail_nodup_of_faceLen_three hSimple (htri (M.dartFace root))
  let outerCycle : BoundaryCycle M outerFace :=
    M.boundaryCycleOfFace outerFace hφ rfl hnodup
  refine
    { sphere := hS
      simpleGraph := hSimple
      outerFace := outerFace
      outerCycle := outerCycle
      outer_simple := ?_
      outer_len := ?_
      inner_tri := ?_ }
  · change outerCycle.vertices.Nodup
    change ((M.faceDartList root).map M.tail).Nodup
    exact hnodup
  · change 3 ≤ outerCycle.length
    change 3 ≤ (M.faceDartList root).length
    rw [M.faceDartList_length_eq_faceLen hφ, htri (M.dartFace root)]
  · intro f _hf
    exact htri f

/-- A near-triangulating extension of a combinatorial map, retaining an embedding of the
old vertex graph into the final near-triangulation. -/
structure TriangulationExtension (M : CombMap D) where
  D' : Type u'
  fintypeD' : Fintype D'
  decidableEqD' : DecidableEq D'
  T : @CombMap D' fintypeD' decidableEqD'
  hNT : T.NearTriangulation
  ιV : M.Vertex → T.Vertex
  adj_embed :
    ∀ {u v : M.Vertex}, M.toSimpleGraph.Adj u v → T.toSimpleGraph.Adj (ιV u) (ιV v)

attribute [instance] TriangulationExtension.fintypeD' TriangulationExtension.decidableEqD'

/-- Triangulate a simple sphere map by repeatedly inserting supplied face diagonals.  The
measure is the face excess, and the base case is the fully triangular map converted above
into a near-triangulation. -/
noncomputable def triangulate (X : Type u) [Fintype X] [DecidableEq X]
    (M : CombMap X) (hS : M.IsSphereMap)
    (hSimple : M.IsSimpleGraph) (h3 : M.FaceLengthGe 3)
    (sup : FaceDiagonalSupplier) [Nonempty X] :
    M.TriangulationExtension := by
  classical
  by_cases hlong : ∃ f : M.Face, 3 < M.faceLen f
  · let f : M.Face := Classical.choose hlong
    have hf : 3 < M.faceLen f := Classical.choose_spec hlong
    let c : M.FaceDiagonalChoice := Classical.choice (sup.exists_choice M hS hSimple f hf)
    let I := FaceDiagonalInsertion.of_addFaceDiagonal M hS hSimple c
    letI : Fintype I.D' := I.fintypeD'
    letI : DecidableEq I.D' := I.decEqD'
    letI : Nonempty I.D' := ⟨I.includeDart (Classical.choice inferInstance)⟩
    let R := triangulate I.D' I.M' I.sphere' I.simple'
      (FaceDiagonal.faceLengthGe_three_add M c hS hSimple) sup
    exact
      { D' := R.D'
        fintypeD' := R.fintypeD'
        decidableEqD' := R.decidableEqD'
        T := R.T
        hNT := R.hNT
        ιV := fun v => R.ιV (I.includeVertex v)
        adj_embed := by
          intro u v huv
          exact R.adj_embed (I.old_adj_embed huv) }
  · have htri : ∀ f : M.Face, M.faceLen f = 3 := by
      intro f
      have hle : 3 ≤ M.faceLen f := h3 f
      have hnlt : ¬ 3 < M.faceLen f := by
        intro hf
        exact hlong ⟨f, hf⟩
      omega
    exact
      { D' := X
        fintypeD' := inferInstance
        decidableEqD' := inferInstance
        T := M
        hNT := buildNearTriangulationFromAllTriangular M hS hSimple htri
        ιV := id
        adj_embed := by
          intro u v huv
          exact huv }
termination_by faceExcess M
decreasing_by
  exact I.faceExcess_decrease

end CombMap

namespace PlaneSimpleGraph

variable {V : Type v} {D : Type u} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Convert a combinatorial-map triangulation extension of `P.toCombMap` into the
plane-simple-graph extension interface by composing the original vertex equivalence. -/
noncomputable def triangulationExtensionOfCombMap (P : PlaneSimpleGraph V D)
    (hincident : ∀ v : V, ∃ d : D, P.tail d = v)
    (E : P.toCombMap.TriangulationExtension) :
    PlaneTriangulationExtension P where
  D' := E.D'
  fintypeD' := E.fintypeD'
  decidableEqD' := E.decidableEqD'
  T := E.T
  hNT := E.hNT
  ιV := fun v => E.ιV ((P.vertexEquiv hincident).symm v)
  adj_embed := by
    intro u v huv
    exact E.adj_embed (P.toCombMap_adj_embed hincident huv)

/-- Produce a triangulation extension of a plane simple graph from the route-B diagonal
supplier and the small face-length lower-bound side condition. -/
noncomputable def triangulationExtensionOfSupplier (P : PlaneSimpleGraph V D)
    (hsphere : P.IsSphereMap)
    (hincident : ∀ v : V, ∃ d : D, P.tail d = v)
    (h3 : P.toCombMap.FaceLengthGe 3)
    (sup : FaceDiagonalSupplier.{u}) [Nonempty D] :
    PlaneTriangulationExtension P :=
  P.triangulationExtensionOfCombMap hincident
    (CombMap.triangulate D P.toCombMap
      (P.toCombMap_isSphereMap hsphere hincident)
      P.toCombMap_isSimpleGraph h3 sup)

/-- Conditional five-colour theorem for plane simple graphs from the uniform face-diagonal
supplier.  The remaining residual is exactly the supplier; `h3` is the standard
face-length lower bound needed to identify the all-triangular base case. -/
theorem fiveColor_planeSimpleGraph (P : PlaneSimpleGraph V D)
    (hsphere : P.IsSphereMap)
    (hincident : ∀ v : V, ∃ d : D, P.tail d = v)
    (h3 : P.toCombMap.FaceLengthGe 3)
    (sup : FaceDiagonalSupplier.{u}) [Nonempty D] :
    P.G.Colorable 5 :=
  fiveColor_planeSimpleGraph_of_extension P
    (P.triangulationExtensionOfSupplier hsphere hincident h3 sup)

end PlaneSimpleGraph

namespace TriangleWitness

lemma triangle_faceLen_dartFace_three (d : TriD) :
    trianglePlaneSimpleGraph.toCombMap.faceLen
      (trianglePlaneSimpleGraph.toCombMap.dartFace d) = 3 := by
  fin_cases d <;> decide

lemma triangle_toCombMap_faceRegular_three :
    trianglePlaneSimpleGraph.toCombMap.FaceRegular 3 := by
  intro Q
  obtain ⟨d, rfl⟩ := Q.exists_rep
  exact triangle_faceLen_dartFace_three d

/-- On the triangle witness there is no non-triangular face, so a diagonal supplier is
vacuously satisfiable at that map. -/
lemma triangle_no_long_face (f : trianglePlaneSimpleGraph.toCombMap.Face) :
    ¬ 3 < trianglePlaneSimpleGraph.toCombMap.faceLen f := by
  have h : trianglePlaneSimpleGraph.toCombMap.faceLen f = 3 :=
    triangle_toCombMap_faceRegular_three f
  rw [h]
  omega

noncomputable def triangleNearTriangulation :
    trianglePlaneSimpleGraph.toCombMap.NearTriangulation :=
  ProofsInTheBook.ZinanCh35BoundaryAssembler.nearTriangulation_of_explicit_boundary_classification
    trianglePlaneSimpleGraph.toCombMap
    triangle_toCombMap_isSphereMap
    triangle_toCombMap_isSimpleGraph
    (trianglePlaneSimpleGraph.toCombMap.dartFace (0 : TriD))
    (0 : TriD)
    rfl
    (by
      change ((trianglePlaneSimpleGraph.toCombMap.faceDartList (0 : TriD)).map
        trianglePlaneSimpleGraph.toCombMap.tail).Nodup
      decide)
    (by
      change 3 ≤ (trianglePlaneSimpleGraph.toCombMap.faceDartList (0 : TriD)).length
      decide)
    (by
      intro f _hf
      exact triangle_toCombMap_faceRegular_three f)

def triangleVertexToComb : TriV → trianglePlaneSimpleGraph.toCombMap.Vertex := fun v =>
  if v = 0 then trianglePlaneSimpleGraph.toCombMap.tail (0 : TriD) else
  if v = 1 then trianglePlaneSimpleGraph.toCombMap.tail (1 : TriD) else
  trianglePlaneSimpleGraph.toCombMap.tail (3 : TriD)

noncomputable def triangleTriangulationExtension :
    PlaneTriangulationExtension trianglePlaneSimpleGraph where
  D' := TriD
  fintypeD' := inferInstance
  decidableEqD' := inferInstance
  T := trianglePlaneSimpleGraph.toCombMap
  hNT := triangleNearTriangulation
  ιV := (trianglePlaneSimpleGraph.vertexEquiv triangle_incident).symm
  adj_embed := by
    intro u v huv
    exact trianglePlaneSimpleGraph.toCombMap_adj_embed triangle_incident huv

theorem fiveColor_triangle : trianglePlaneSimpleGraph.G.Colorable 5 :=
  fiveColor_planeSimpleGraph_of_extension trianglePlaneSimpleGraph triangleTriangulationExtension

theorem triangle_toCombMap_faceLengthGe_three :
    trianglePlaneSimpleGraph.toCombMap.FaceLengthGe 3 := by
  intro f
  have h := triangle_toCombMap_faceRegular_three f
  simpa [CombMap.faceLen] using (le_of_eq h.symm)

/-- The triangle witness also routes through the general triangulation producer, for any
inhabited uniform diagonal supplier.  The supplier is not consumed because the map is already
triangular. -/
theorem fiveColor_triangle_via_triangulate (sup : FaceDiagonalSupplier.{0}) :
    trianglePlaneSimpleGraph.G.Colorable 5 :=
  trianglePlaneSimpleGraph.fiveColor_planeSimpleGraph triangle_plane_isSphere triangle_incident
    triangle_toCombMap_faceLengthGe_three sup

end TriangleWitness

#print axioms ProofsInTheBook.PlanarMap.PlaneSimpleGraph.toCombMap_isSphereMap
#print axioms ProofsInTheBook.PlanarMap.PlaneSimpleGraph.toCombMap_isSimpleGraph
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.triangle_plane_isSphere
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.triangle_toCombMap_isSphereMap
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.triangle_toCombMap_isSimpleGraph
#print axioms ProofsInTheBook.PlanarMap.colorable_of_triangulationExtension
#print axioms ProofsInTheBook.PlanarMap.fiveColor_planeSimpleGraph_of_extension
#print axioms ProofsInTheBook.PlanarMap.FaceDiagonalSupplier
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.triangle_toCombMap_faceRegular_three
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.triangle_no_long_face
#print axioms ProofsInTheBook.PlanarMap.CombMap.buildNearTriangulationFromAllTriangular
#print axioms ProofsInTheBook.PlanarMap.CombMap.triangulate
#print axioms ProofsInTheBook.PlanarMap.PlaneSimpleGraph.fiveColor_planeSimpleGraph
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.triangleNearTriangulation
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.fiveColor_triangle
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.fiveColor_triangle_via_triangulate

end ProofsInTheBook.PlanarMap
