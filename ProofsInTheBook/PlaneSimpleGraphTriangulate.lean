import ProofsInTheBook.PlaneSimpleGraph
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.FaceDiagonalSurgery
import ProofsInTheBook.Ch13ActiveComponent
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

lemma three_le_of_two_le_choose_two (n : ℕ) (h : 2 ≤ n.choose 2) : 3 ≤ n := by
  cases n with
  | zero => simp at h
  | succ n =>
      cases n with
      | zero => simp at h
      | succ n =>
          cases n with
          | zero => simp at h
          | succ n => omega

lemma three_mul_sub_six_le_choose_two (n : ℕ) (hn : 3 ≤ n) :
    3 * n - 6 ≤ n.choose 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [show 3 + Nat.succ m = (3 + m) + 1 by omega]
      rw [Nat.choose_succ_succ]
      simp [Nat.choose_one_right]
      have hprev : 3 * (3 + m) - 6 ≤ (3 + m).choose 2 := ih (by omega)
      omega

/-- Local constructor for a valid face diagonal from two non-adjacent darts on a common face. -/
def faceDiagonalChoice_of_pair (M : CombMap D) {f : M.Face} {d0 d1 : D}
    (h0 : M.dartFace d0 = f) (h1 : M.dartFace d1 = f)
    (hne : M.tail d0 ≠ M.tail d1)
    (hnoedge : ¬ M.toSimpleGraph.Adj (M.tail d0) (M.tail d1))
    (hsep : M.φ d0 ≠ d1 ∧ M.φ d1 ≠ d0) :
    M.FaceDiagonalChoice where
  f := f
  d0 := d0
  d1 := d1
  same_face := h0
  same_face' := h1
  endpoints_distinct := hne
  no_existing_edge := hnoedge
  nonadjacent_on_face := hsep

/-- If a face admits no diagonal choice, then every cyclically separated pair of distinct boundary
occurrences on that face already has an edge between its endpoint vertices.  This is the local
clique step needed by the Euler-count proof. -/
theorem face_boundary_adj_of_no_diagonal (M : CombMap D) {f : M.Face}
    (hNo : ¬ Nonempty (M.FaceDiagonalChoice))
    {d0 d1 : D} (h0 : M.dartFace d0 = f) (h1 : M.dartFace d1 = f)
    (hne : M.tail d0 ≠ M.tail d1)
    (hsep : M.φ d0 ≠ d1 ∧ M.φ d1 ≠ d0) :
    M.toSimpleGraph.Adj (M.tail d0) (M.tail d1) := by
  by_contra hnoedge
  exact hNo ⟨M.faceDiagonalChoice_of_pair h0 h1 hne hnoedge hsep⟩

/-- The vertices appearing on the boundary of a face. -/
noncomputable def faceVertexSet (M : CombMap D) (f : M.Face) : Finset M.Vertex := by
  classical
  exact Finset.univ.filter (fun v => ∃ d : D, M.dartFace d = f ∧ M.tail d = v)

lemma mem_faceVertexSet_iff (M : CombMap D) (f : M.Face) (v : M.Vertex) :
    v ∈ M.faceVertexSet f ↔ ∃ d : D, M.dartFace d = f ∧ M.tail d = v := by
  classical
  simp [faceVertexSet]

theorem faceVertexSet_clique_of_no_diagonal (M : CombMap D) (hSimple : M.IsSimpleGraph)
    {f : M.Face} (hNo : ¬ Nonempty (M.FaceDiagonalChoice)) :
    ∀ u ∈ M.faceVertexSet f, ∀ v ∈ M.faceVertexSet f,
      u ≠ v → M.toSimpleGraph.Adj u v := by
  intro u hu v hv huv
  rw [M.mem_faceVertexSet_iff] at hu hv
  obtain ⟨d0, h0, ht0⟩ := hu
  obtain ⟨d1, h1, ht1⟩ := hv
  by_cases h01 : M.φ d0 = d1
  · have hadj := M.toSimpleGraph_adj_of_dart hSimple d0
    rw [ht0, ← M.tail_phi d0, h01, ht1] at hadj
    exact hadj
  · by_cases h10 : M.φ d1 = d0
    · have hadj := M.toSimpleGraph_adj_of_dart hSimple d1
      have hadj' : M.toSimpleGraph.Adj (M.tail d0) (M.tail d1) := by
        rw [ht1, ← M.tail_phi d1, h10, ht0] at hadj
        simpa [ht0, ht1] using M.toSimpleGraph.symm hadj
      simpa [ht0, ht1] using hadj'
    · have hne : M.tail d0 ≠ M.tail d1 := by
        intro h
        exact huv (ht0 ▸ ht1 ▸ h)
      have hadj := M.face_boundary_adj_of_no_diagonal hNo h0 h1 hne ⟨h01, h10⟩
      simpa [ht0, ht1] using hadj

/-- Delete exactly the darts whose edge has at least one endpoint outside the selected face-vertex
set.  The kept darts are the edges of the face-vertex induced submap. -/
noncomputable def faceVertexDel (M : CombMap D) (f : M.Face) : Finset D := by
  classical
  exact Finset.univ.filter
    (fun d => M.tail d ∉ M.faceVertexSet f ∨ M.head d ∉ M.faceVertexSet f)

lemma mem_faceVertexDel_iff (M : CombMap D) (f : M.Face) (d : D) :
    d ∈ M.faceVertexDel f ↔
      M.tail d ∉ M.faceVertexSet f ∨ M.head d ∉ M.faceVertexSet f := by
  classical
  simp [faceVertexDel]

/-- The face-vertex deletion set is closed under edge reversal. -/
lemma faceVertexDel_alpha_iff (M : CombMap D) (f : M.Face) (d : D) :
    M.α d ∈ M.faceVertexDel f ↔ d ∈ M.faceVertexDel f := by
  rw [M.mem_faceVertexDel_iff, M.mem_faceVertexDel_iff]
  simp [or_comm]

/-- Every dart of the selected face survives in the face-vertex induced dart set. -/
lemma notMem_faceVertexDel_of_dartFace (M : CombMap D) {f : M.Face} {d : D}
    (hd : M.dartFace d = f) :
    d ∉ M.faceVertexDel f := by
  rw [M.mem_faceVertexDel_iff]
  push_neg
  constructor
  · rw [M.mem_faceVertexSet_iff]
    exact ⟨d, hd, rfl⟩
  · rw [M.mem_faceVertexSet_iff]
    refine ⟨M.φ d, ?_, ?_⟩
    · rw [M.dartFace_phi, hd]
    · rw [M.tail_phi]

lemma faceVertexDel_sub (M : CombMap D) (f : M.Face) :
    ∀ d : D, d ∈ M.faceVertexDel f ↔ M.α d ∈ M.faceVertexDel f := by
  intro d
  exact (M.faceVertexDel_alpha_iff f d).symm

lemma faceVertexDel_closed (M : CombMap D) (f : M.Face) :
    ∀ d : D, d ∈ M.faceVertexDel f → M.α d ∈ M.faceVertexDel f := by
  intro d hd
  exact (M.faceVertexDel_sub f d).1 hd

/-- The kept combinatorial map induced by the vertices on a face boundary. -/
noncomputable def faceVertexKeptMap (M : CombMap D) (f : M.Face) :
    CombMap {d : D // d ∉ M.faceVertexDel f} :=
  ProofsInTheBook.Ch13ActiveComponent.keptMap M (M.faceVertexDel f) (M.faceVertexDel_sub f)

lemma faceVertexKeptMap_simple (M : CombMap D) (hSimple : M.IsSimpleGraph) (f : M.Face) :
    (M.faceVertexKeptMap f).IsSimpleGraph :=
  ProofsInTheBook.Ch13ComponentClose.keptMap_isSimpleGraph M hSimple
    (M.faceVertexDel f) (M.faceVertexDel_sub f)

lemma faceVertexKeptMap_euler_VEF (M : CombMap D) (hS : M.IsSphereMap) (f : M.Face)
    (d : {d : D // d ∉ M.faceVertexDel f})
    (hconn : (M.faceVertexKeptMap f).Connected) :
    ((M.faceVertexKeptMap f).V : ℤ) - (M.faceVertexKeptMap f).E
        + (M.faceVertexKeptMap f).F = 2 :=
  ProofsInTheBook.Ch13ActiveComponent.keptMap_euler_VEF M (M.faceVertexDel f)
    (M.faceVertexDel_sub f) (M.faceVertexDel_closed f) hS d hconn

lemma faceVertexKept_tail_mem (M : CombMap D) (f : M.Face)
    (x : {d : D // d ∉ M.faceVertexDel f}) :
    M.tail x.1 ∈ M.faceVertexSet f := by
  have hx := x.2
  rw [M.mem_faceVertexDel_iff] at hx
  push_neg at hx
  exact hx.1

lemma faceVertexKept_head_mem (M : CombMap D) (f : M.Face)
    (x : {d : D // d ∉ M.faceVertexDel f}) :
    M.head x.1 ∈ M.faceVertexSet f := by
  have hx := x.2
  rw [M.mem_faceVertexDel_iff] at hx
  push_neg at hx
  exact hx.2

lemma notMem_faceVertexDel_of_endpoints (M : CombMap D) (f : M.Face) {d : D}
    (ht : M.tail d ∈ M.faceVertexSet f) (hh : M.head d ∈ M.faceVertexSet f) :
    d ∉ M.faceVertexDel f := by
  rw [M.mem_faceVertexDel_iff]
  push_neg
  exact ⟨ht, hh⟩

lemma exists_dart_tail_head_of_toSimpleGraph_adj (M : CombMap D)
    {u v : M.Vertex} (h : M.toSimpleGraph.Adj u v) :
    ∃ d : D, M.tail d = u ∧ M.head d = v := by
  rcases h.2 with ⟨e, he⟩
  unfold CombMap.dartEdge at he
  rw [Sym2.eq_iff] at he
  rcases he with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · exact ⟨e, ht, hh⟩
  · refine ⟨M.α e, ?_, ?_⟩
    · rw [M.tail_alpha, hh]
    · rw [M.head_alpha, ht]

lemma exists_dart_of_mem_toSimpleGraph_edgeSet (M : CombMap D)
    {e : Sym2 M.Vertex} (he : e ∈ M.toSimpleGraph.edgeSet) :
    ∃ d : D, M.dartEdge d = e := by
  induction e using Sym2.ind with
  | h u v =>
      have hadj : M.toSimpleGraph.Adj u v := by simpa using he
      obtain ⟨d, htail, hhead⟩ := M.exists_dart_tail_head_of_toSimpleGraph_adj hadj
      refine ⟨d, ?_⟩
      simp [CombMap.dartEdge, htail, hhead]

/-- In a simple map, the map-edge quotient is the same finite set as the edge set of the
underlying simple graph. -/
noncomputable def edgeQuotEquivToSimpleGraphEdgeSet (M : CombMap D)
    (hSimple : M.IsSimpleGraph) :
    Quotient (cycleSetoid M.α) ≃ M.toSimpleGraph.edgeSet where
  toFun := Quotient.lift
    (fun d : D =>
      ⟨M.dartEdge d, by
        unfold CombMap.dartEdge
        exact M.toSimpleGraph_adj_of_dart hSimple d⟩)
    (by
      intro d e hde
      apply Subtype.ext
      rcases (M.alpha_sameCycle_iff d e).1 hde with rfl | he
      · rfl
      · subst e
        change M.dartEdge d = M.dartEdge (M.α d)
        rw [M.dartEdge_alpha])
  invFun := fun e =>
    Quotient.mk (cycleSetoid M.α)
      (Classical.choose (M.exists_dart_of_mem_toSimpleGraph_edgeSet e.2))
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro d
    apply Quotient.sound
    have hchosen :
        M.dartEdge (Classical.choose
          (M.exists_dart_of_mem_toSimpleGraph_edgeSet
            (show M.dartEdge d ∈ M.toSimpleGraph.edgeSet by
              unfold CombMap.dartEdge
              exact M.toSimpleGraph_adj_of_dart hSimple d))) = M.dartEdge d :=
      Classical.choose_spec
        (M.exists_dart_of_mem_toSimpleGraph_edgeSet
          (show M.dartEdge d ∈ M.toSimpleGraph.edgeSet by
            unfold CombMap.dartEdge
            exact M.toSimpleGraph_adj_of_dart hSimple d))
    exact hSimple.no_parallel hchosen
  right_inv := by
    intro e
    apply Subtype.ext
    exact Classical.choose_spec (M.exists_dart_of_mem_toSimpleGraph_edgeSet e.2)

lemma E_eq_card_toSimpleGraph_edgeFinset (M : CombMap D) (hSimple : M.IsSimpleGraph) :
    M.E = M.toSimpleGraph.edgeFinset.card := by
  classical
  letI : Fintype M.toSimpleGraph.edgeSet := Fintype.ofFinite M.toSimpleGraph.edgeSet
  calc
    M.E = Fintype.card (Quotient (cycleSetoid M.α)) := rfl
    _ = Fintype.card M.toSimpleGraph.edgeSet :=
        Fintype.card_congr (M.edgeQuotEquivToSimpleGraphEdgeSet hSimple)
    _ = M.toSimpleGraph.edgeFinset.card := by
        simpa using (SimpleGraph.card_edgeSet (G := M.toSimpleGraph))

lemma faceVertexKept_sigma_path_of_same_tail (M : CombMap D) (f : M.Face)
    {x y : {d : D // d ∉ M.faceVertexDel f}} (h : M.tail x.1 = M.tail y.1) :
    Relation.ReflTransGen (M.faceVertexKeptMap f).dartStep x y := by
  apply Relation.ReflTransGen.single
  left
  have ht :
      (M.faceVertexKeptMap f).tail x = (M.faceVertexKeptMap f).tail y := by
    exact (ProofsInTheBook.Ch13ComponentClose.keptMap_tail_eq_iff
      M (M.faceVertexDel f) (M.faceVertexDel_sub f) x y).2 h
  exact Quotient.exact ht

lemma faceVertexKeptMap_connected_of_clique (M : CombMap D) (f : M.Face)
    (hClique : ∀ u ∈ M.faceVertexSet f, ∀ v ∈ M.faceVertexSet f,
      u ≠ v → M.toSimpleGraph.Adj u v) :
    (M.faceVertexKeptMap f).Connected := by
  intro x y
  by_cases htail : M.tail x.1 = M.tail y.1
  · exact M.faceVertexKept_sigma_path_of_same_tail f htail
  · have hxS := M.faceVertexKept_tail_mem f x
    have hyS := M.faceVertexKept_tail_mem f y
    have hadj : M.toSimpleGraph.Adj (M.tail x.1) (M.tail y.1) :=
      hClique (M.tail x.1) hxS (M.tail y.1) hyS htail
    obtain ⟨e, het, heh⟩ := M.exists_dart_tail_head_of_toSimpleGraph_adj hadj
    have hekeep : e ∉ M.faceVertexDel f := by
      apply M.notMem_faceVertexDel_of_endpoints f
      · simpa [het] using hxS
      · simpa [heh] using hyS
    let z : {d : D // d ∉ M.faceVertexDel f} := ⟨e, hekeep⟩
    have hzx : M.tail x.1 = M.tail z.1 := by simpa [z, het]
    have hzy : M.tail ((M.faceVertexKeptMap f).α z).1 = M.tail y.1 := by
      change M.tail (M.α e) = M.tail y.1
      rw [M.tail_alpha, heh]
    have p1 : Relation.ReflTransGen (M.faceVertexKeptMap f).dartStep x z :=
      M.faceVertexKept_sigma_path_of_same_tail f hzx
    have p2 : Relation.ReflTransGen (M.faceVertexKeptMap f).dartStep z
        ((M.faceVertexKeptMap f).α z) :=
      Relation.ReflTransGen.single (Or.inr rfl)
    have p3 : Relation.ReflTransGen (M.faceVertexKeptMap f).dartStep
        ((M.faceVertexKeptMap f).α z) y :=
      M.faceVertexKept_sigma_path_of_same_tail f hzy
    exact p1.trans (p2.trans p3)

/-- Vertices of the face-vertex kept map are exactly the vertices in the selected face-vertex set. -/
noncomputable def faceVertexKeptVertexEquiv (M : CombMap D) (f : M.Face) :
    (M.faceVertexKeptMap f).Vertex ≃ {v : M.Vertex // v ∈ M.faceVertexSet f} where
  toFun := Quotient.lift
    (fun x : {d : D // d ∉ M.faceVertexDel f} =>
      ⟨M.tail x.1, M.faceVertexKept_tail_mem f x⟩)
    (by
      intro x y hxy
      apply Subtype.ext
      have htail :
          (M.faceVertexKeptMap f).tail x = (M.faceVertexKeptMap f).tail y :=
        Quotient.sound hxy
      exact (ProofsInTheBook.Ch13ComponentClose.keptMap_tail_eq_iff
        M (M.faceVertexDel f) (M.faceVertexDel_sub f) x y).1 htail)
  invFun := fun v =>
    Quotient.mk (cycleSetoid (M.faceVertexKeptMap f).σ)
      ⟨Classical.choose ((M.mem_faceVertexSet_iff f v.1).1 v.2),
        M.notMem_faceVertexDel_of_dartFace
          ((Classical.choose_spec ((M.mem_faceVertexSet_iff f v.1).1 v.2)).1)⟩
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    change Quotient.mk (cycleSetoid (M.faceVertexKeptMap f).σ)
        ⟨Classical.choose ((M.mem_faceVertexSet_iff f (M.tail x.1)).1
          (M.faceVertexKept_tail_mem f x)),
          M.notMem_faceVertexDel_of_dartFace
            ((Classical.choose_spec ((M.mem_faceVertexSet_iff f (M.tail x.1)).1
              (M.faceVertexKept_tail_mem f x))).1)⟩
        = Quotient.mk (cycleSetoid (M.faceVertexKeptMap f).σ) x
    apply Quotient.sound
    have htail :
        M.tail (Classical.choose ((M.mem_faceVertexSet_iff f (M.tail x.1)).1
          (M.faceVertexKept_tail_mem f x))) = M.tail x.1 :=
      (Classical.choose_spec ((M.mem_faceVertexSet_iff f (M.tail x.1)).1
        (M.faceVertexKept_tail_mem f x))).2
    let y : {d : D // d ∉ M.faceVertexDel f} :=
      ⟨Classical.choose ((M.mem_faceVertexSet_iff f (M.tail x.1)).1
        (M.faceVertexKept_tail_mem f x)),
        M.notMem_faceVertexDel_of_dartFace
          ((Classical.choose_spec ((M.mem_faceVertexSet_iff f (M.tail x.1)).1
            (M.faceVertexKept_tail_mem f x))).1)⟩
    change (M.faceVertexKeptMap f).σ.SameCycle y x
    exact (Quotient.exact ((ProofsInTheBook.Ch13ComponentClose.keptMap_tail_eq_iff
      M (M.faceVertexDel f) (M.faceVertexDel_sub f) y x).2 htail))
  right_inv := by
    intro v
    apply Subtype.ext
    exact (Classical.choose_spec ((M.mem_faceVertexSet_iff f v.1).1 v.2)).2

lemma faceVertexKeptMap_V_eq_card_faceVertexSet (M : CombMap D) (f : M.Face) :
    (M.faceVertexKeptMap f).V = (M.faceVertexSet f).card := by
  calc
    (M.faceVertexKeptMap f).V
        = Fintype.card {v : M.Vertex // v ∈ M.faceVertexSet f} :=
          Fintype.card_congr (M.faceVertexKeptVertexEquiv f)
    _ = (M.faceVertexSet f).card := Fintype.card_coe _

lemma faceVertexKeptMap_complete_of_clique (M : CombMap D) (f : M.Face)
    (hClique : ∀ u ∈ M.faceVertexSet f, ∀ v ∈ M.faceVertexSet f,
      u ≠ v → M.toSimpleGraph.Adj u v) :
    ∀ u v : (M.faceVertexKeptMap f).Vertex,
      u ≠ v → (M.faceVertexKeptMap f).toSimpleGraph.Adj u v := by
  intro u v huv
  refine Quotient.inductionOn₂ u v ?_ huv
  intro x y huv'
  have htailne : M.tail x.1 ≠ M.tail y.1 := by
    intro htail
    apply huv'
    exact (ProofsInTheBook.Ch13ComponentClose.keptMap_tail_eq_iff
      M (M.faceVertexDel f) (M.faceVertexDel_sub f) x y).2 htail
  have hxS := M.faceVertexKept_tail_mem f x
  have hyS := M.faceVertexKept_tail_mem f y
  have hadj : M.toSimpleGraph.Adj (M.tail x.1) (M.tail y.1) :=
    hClique (M.tail x.1) hxS (M.tail y.1) hyS htailne
  obtain ⟨e, het, heh⟩ := M.exists_dart_tail_head_of_toSimpleGraph_adj hadj
  have hekeep : e ∉ M.faceVertexDel f := by
    apply M.notMem_faceVertexDel_of_endpoints f
    · simpa [het] using hxS
    · simpa [heh] using hyS
  let z : {d : D // d ∉ M.faceVertexDel f} := ⟨e, hekeep⟩
  rw [CombMap.toSimpleGraph_adj]
  refine ⟨huv', ?_⟩
  refine ⟨z, ?_⟩
  unfold CombMap.dartEdge
  rw [Sym2.eq_iff]
  left
  constructor
  · exact (ProofsInTheBook.Ch13ComponentClose.keptMap_tail_eq_iff
      M (M.faceVertexDel f) (M.faceVertexDel_sub f) z x).2 (by simpa [z, het])
  · rw [eq_comm]
    exact (ProofsInTheBook.Ch13ComponentClose.keptMap_tail_eq_head_iff
      M (M.faceVertexDel f) (M.faceVertexDel_sub f) y z).2 (by simpa [z, heh])

lemma faceVertexKeptMap_toSimpleGraph_eq_top_of_clique (M : CombMap D) (f : M.Face)
    (hClique : ∀ u ∈ M.faceVertexSet f, ∀ v ∈ M.faceVertexSet f,
      u ≠ v → M.toSimpleGraph.Adj u v) :
    (M.faceVertexKeptMap f).toSimpleGraph = ⊤ := by
  ext u v
  constructor
  · intro h
    exact (M.faceVertexKeptMap f).toSimpleGraph.ne_of_adj h
  · intro huv
    exact M.faceVertexKeptMap_complete_of_clique f hClique u v huv

lemma faceVertexKeptMap_E_eq_choose_two_of_clique (M : CombMap D)
    (hSimple : M.IsSimpleGraph) (f : M.Face)
    (hClique : ∀ u ∈ M.faceVertexSet f, ∀ v ∈ M.faceVertexSet f,
      u ≠ v → M.toSimpleGraph.Adj u v) :
    (M.faceVertexKeptMap f).E = (M.faceVertexSet f).card.choose 2 := by
  classical
  let H := M.faceVertexKeptMap f
  letI : Fintype H.toSimpleGraph.edgeSet := Fintype.ofFinite H.toSimpleGraph.edgeSet
  have hHsimple : H.IsSimpleGraph := M.faceVertexKeptMap_simple hSimple f
  have htop : H.toSimpleGraph = ⊤ :=
    M.faceVertexKeptMap_toSimpleGraph_eq_top_of_clique f hClique
  have hedgeFinset :
      H.toSimpleGraph.edgeFinset = (⊤ : SimpleGraph H.Vertex).edgeFinset := by
    ext e
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset, htop]
  calc
    H.E = H.toSimpleGraph.edgeFinset.card :=
        H.E_eq_card_toSimpleGraph_edgeFinset hHsimple
    _ = (Fintype.card H.Vertex).choose 2 := by
        rw [hedgeFinset]
        exact SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := H.Vertex)
    _ = (M.faceVertexSet f).card.choose 2 := by
        change H.V.choose 2 = (M.faceVertexSet f).card.choose 2
        rw [M.faceVertexKeptMap_V_eq_card_faceVertexSet f]

lemma faceVertexKept_phi_apply_of_dartFace (M : CombMap D) {f : M.Face} {d : D}
    (hd : M.dartFace d = f) :
    (((M.faceVertexKeptMap f).φ
      ⟨d, M.notMem_faceVertexDel_of_dartFace hd⟩ :
        {d : D // d ∉ M.faceVertexDel f}) : D) = M.φ d := by
  unfold CombMap.φ faceVertexKeptMap ProofsInTheBook.Ch13ActiveComponent.keptMap
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  have hαkeep : M.α d ∉ M.faceVertexDel f := by
    exact fun h => (M.notMem_faceVertexDel_of_dartFace hd) ((M.faceVertexDel_sub f d).2 h)
  change ((Equiv.Perm.deleteSet M.σ (M.faceVertexDel f))
      ⟨M.α d, hαkeep⟩ : {d : D // d ∉ M.faceVertexDel f}).1 = M.φ d
  rw [Equiv.Perm.deleteSet_apply_coe,
    ProofsInTheBook.PlanarMap.FilteredRotation.firstOutside_eq_one_of_next_notMem,
    pow_one]
  rfl
  change M.φ d ∉ M.faceVertexDel f
  exact M.notMem_faceVertexDel_of_dartFace (by rw [M.dartFace_phi, hd])

lemma dartFace_phi_pow (M : CombMap D) (d : D) (n : ℕ) :
    M.dartFace ((M.φ ^ n) d) = M.dartFace d := by
  exact Quotient.sound
    ((Equiv.Perm.sameCycle_pow_left (f := M.φ) (x := d) (y := d) (n := n)).2
      (Equiv.Perm.SameCycle.refl _ _))

lemma faceVertexKept_phi_pow_apply_of_dartFace (M : CombMap D) {f : M.Face} {d : D}
    (hd : M.dartFace d = f) (n : ℕ) :
    (((M.faceVertexKeptMap f).φ ^ n)
      ⟨d, M.notMem_faceVertexDel_of_dartFace hd⟩ :
        {d : D // d ∉ M.faceVertexDel f}).1 = (M.φ ^ n) d := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      have hface : M.dartFace ((M.φ ^ n) d) = f := by
        rw [M.dartFace_phi_pow d n, hd]
      have hy :
          (((M.faceVertexKeptMap f).φ ^ n)
            ⟨d, M.notMem_faceVertexDel_of_dartFace hd⟩ :
              {d : D // d ∉ M.faceVertexDel f}) =
            ⟨(M.φ ^ n) d, M.notMem_faceVertexDel_of_dartFace hface⟩ :=
        Subtype.ext ih
      rw [hy]
      exact M.faceVertexKept_phi_apply_of_dartFace hface

lemma faceVertexKept_sameCycle_to_old_of_dartFace (M : CombMap D) {f : M.Face}
    {d : D} (hd : M.dartFace d = f)
    {x : {d : D // d ∉ M.faceVertexDel f}}
    (h : (M.faceVertexKeptMap f).φ.SameCycle
        ⟨d, M.notMem_faceVertexDel_of_dartFace hd⟩ x) :
    M.φ.SameCycle d x.1 := by
  obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h
  have hnat : (M.φ ^ n) d = x.1 := by
    rw [← hn]
    exact (M.faceVertexKept_phi_pow_apply_of_dartFace hd n).symm
  refine ⟨(n : ℤ), ?_⟩
  simpa [zpow_natCast] using hnat

lemma faceVertexKept_sameCycle_of_old_sameCycle (M : CombMap D) {f : M.Face}
    {d x : D} (hd : M.dartFace d = f) (hx : M.dartFace x = f)
    (h : M.φ.SameCycle d x) :
    (M.faceVertexKeptMap f).φ.SameCycle
      ⟨d, M.notMem_faceVertexDel_of_dartFace hd⟩
      ⟨x, M.notMem_faceVertexDel_of_dartFace hx⟩ := by
  obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h
  have hnat :
      ((M.faceVertexKeptMap f).φ ^ n)
        ⟨d, M.notMem_faceVertexDel_of_dartFace hd⟩ =
        ⟨x, M.notMem_faceVertexDel_of_dartFace hx⟩ := by
    apply Subtype.ext
    rw [M.faceVertexKept_phi_pow_apply_of_dartFace hd n, hn]
  refine ⟨(n : ℤ), ?_⟩
  simpa [zpow_natCast] using hnat

lemma faceLen_eq_card_dartFace_subtype (M : CombMap D) (Q : M.Face) :
    M.faceLen Q = Fintype.card {d : D // M.dartFace d = Q} := by
  classical
  rw [Fintype.card_subtype]
  rfl

noncomputable def faceVertexKeptFaceDartEquiv (M : CombMap D) {f : M.Face}
    {d : D} (hd : M.dartFace d = f) :
    {x : {d : D // d ∉ M.faceVertexDel f} //
        (M.faceVertexKeptMap f).dartFace x =
          (M.faceVertexKeptMap f).dartFace
            ⟨d, M.notMem_faceVertexDel_of_dartFace hd⟩}
      ≃ {x : D // M.dartFace x = f} where
  toFun := fun x =>
    ⟨x.1.1, by
      have hscH : (M.faceVertexKeptMap f).φ.SameCycle
          ⟨d, M.notMem_faceVertexDel_of_dartFace hd⟩ x.1 :=
        (Quotient.exact x.2.symm)
      have hscM := M.faceVertexKept_sameCycle_to_old_of_dartFace hd hscH
      exact (Quotient.sound hscM).symm.trans hd⟩
  invFun := fun x =>
    ⟨⟨x.1, M.notMem_faceVertexDel_of_dartFace x.2⟩, by
      have hEq : M.dartFace d = M.dartFace x.1 := hd.trans x.2.symm
      have hscM : M.φ.SameCycle d x.1 := Quotient.exact hEq
      have hscH := M.faceVertexKept_sameCycle_of_old_sameCycle hd x.2 hscM
      exact (Quotient.sound hscH).symm⟩
  left_inv := by
    intro x
    cases x with
    | mk x hx =>
        rfl
  right_inv := by
    intro x
    cases x
    rfl

lemma faceVertexKept_faceLen_selected_eq (M : CombMap D) {f : M.Face}
    {d : D} (hd : M.dartFace d = f) :
    (M.faceVertexKeptMap f).faceLen
        ((M.faceVertexKeptMap f).dartFace
          ⟨d, M.notMem_faceVertexDel_of_dartFace hd⟩)
      = M.faceLen f := by
  classical
  rw [faceLen_eq_card_dartFace_subtype, M.faceLen_eq_card_dartFace_subtype f]
  exact Fintype.card_congr (M.faceVertexKeptFaceDartEquiv hd)

lemma faceVertexKeptMap_two_le_E_of_long_face (M : CombMap D) {f : M.Face}
    {d : D} (hd : M.dartFace d = f) (hf : 3 < M.faceLen f) :
    2 ≤ (M.faceVertexKeptMap f).E := by
  classical
  let H := M.faceVertexKeptMap f
  let R0 : H.Face := H.dartFace ⟨d, M.notMem_faceVertexDel_of_dartFace hd⟩
  have hlen : 3 < H.faceLen R0 := by
    simpa [H, R0] using hf.trans_eq (M.faceVertexKept_faceLen_selected_eq hd).symm
  have hle : H.faceLen R0 ≤ 2 * H.E := by
    calc
      H.faceLen R0 ≤ ∑ Q : H.Face, H.faceLen Q :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ R0)
      _ = 2 * H.E := H.sum_faceLen
  change 2 ≤ H.E
  omega

lemma faceVertexKeptMap_faceLengthGe_three_of_clique (M : CombMap D)
    (hSimple : M.IsSimpleGraph) {f : M.Face} {d : D}
    (hd : M.dartFace d = f) (hf : 3 < M.faceLen f)
    (hClique : ∀ u ∈ M.faceVertexSet f, ∀ v ∈ M.faceVertexSet f,
      u ≠ v → M.toSimpleGraph.Adj u v) :
    (M.faceVertexKeptMap f).FaceLengthGe 3 := by
  let H := M.faceVertexKeptMap f
  have hHsimple : H.IsSimpleGraph := M.faceVertexKeptMap_simple hSimple f
  have hconn : H.Connected := M.faceVertexKeptMap_connected_of_clique f hClique
  have hE : 2 ≤ H.E := M.faceVertexKeptMap_two_le_E_of_long_face hd hf
  intro R
  simpa [ProofsInTheBook.Ch13ComponentClose.faceDeg_eq_faceLen] using
    ProofsInTheBook.Ch13ComponentClose.three_le_faceDeg_of_connected_simple_twoEdge
      hHsimple hconn hE R

lemma faceVertexKeptMap_E_le_three_mul_V_sub_seven_of_long_face (M : CombMap D)
    (hS : M.IsSphereMap) (hSimple : M.IsSimpleGraph) {f : M.Face} {d : D}
    (hd : M.dartFace d = f) (hf : 3 < M.faceLen f)
    (hClique : ∀ u ∈ M.faceVertexSet f, ∀ v ∈ M.faceVertexSet f,
      u ≠ v → M.toSimpleGraph.Adj u v) :
    (M.faceVertexKeptMap f).E ≤ 3 * (M.faceVertexKeptMap f).V - 7 := by
  classical
  let H := M.faceVertexKeptMap f
  let R0 : H.Face := H.dartFace ⟨d, M.notMem_faceVertexDel_of_dartFace hd⟩
  have hconn : H.Connected := M.faceVertexKeptMap_connected_of_clique f hClique
  have hVEF : (H.V : ℤ) - H.E + H.F = 2 :=
    M.faceVertexKeptMap_euler_VEF hS f
      ⟨d, M.notMem_faceVertexDel_of_dartFace hd⟩ hconn
  have h3 : H.FaceLengthGe 3 :=
    M.faceVertexKeptMap_faceLengthGe_three_of_clique hSimple hd hf hClique
  have hR0 : H.faceLen R0 = M.faceLen f := by
    simpa [H, R0] using M.faceVertexKept_faceLen_selected_eq hd
  have hR0ge4 : 4 ≤ H.faceLen R0 := by
    rw [hR0]
    omega
  have hsumErase :
      3 * (Finset.univ.erase R0).card ≤
        ∑ Q ∈ Finset.univ.erase R0, H.faceLen Q := by
    calc
      3 * (Finset.univ.erase R0).card =
          ∑ Q ∈ Finset.univ.erase R0, 3 := by
            simp [Finset.sum_const, mul_comm]
      _ ≤ ∑ Q ∈ Finset.univ.erase R0, H.faceLen Q :=
          Finset.sum_le_sum (fun Q _ => h3 Q)
  have hcardErase : (Finset.univ.erase R0).card = H.F - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ R0)]
    simp [CombMap.F]
  have hsumLower : H.faceLen R0 + 3 * (H.F - 1) ≤ 2 * H.E := by
    calc
      H.faceLen R0 + 3 * (H.F - 1)
          = H.faceLen R0 + 3 * (Finset.univ.erase R0).card := by rw [hcardErase]
      _ ≤ H.faceLen R0 + ∑ Q ∈ Finset.univ.erase R0, H.faceLen Q :=
          Nat.add_le_add_left hsumErase _
      _ = ∑ Q : H.Face, H.faceLen Q := by
          rw [Finset.add_sum_erase _ _ (Finset.mem_univ R0)]
      _ = 2 * H.E := H.sum_faceLen
  have hFpos : 0 < H.F := by
    change 0 < Fintype.card H.Face
    exact Fintype.card_pos_iff.mpr ⟨R0⟩
  have hsumLowerZ :
      (H.faceLen R0 : ℤ) + 3 * ((H.F : ℤ) - 1) ≤ 2 * (H.E : ℤ) := by
    have hcast : ((H.F - 1 : ℕ) : ℤ) = (H.F : ℤ) - 1 := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt hFpos)]
      norm_num
    have hsumLowerZ0 :
        (H.faceLen R0 : ℤ) + 3 * ((H.F - 1 : ℕ) : ℤ) ≤ 2 * (H.E : ℤ) := by
      exact_mod_cast hsumLower
    rwa [hcast] at hsumLowerZ0
  have hEstrictZ : (H.E : ℤ) ≤ 3 * (H.V : ℤ) - 7 := by
    have hR0z : (4 : ℤ) ≤ (H.faceLen R0 : ℤ) := by exact_mod_cast hR0ge4
    linarith
  change H.E ≤ 3 * H.V - 7
  omega

noncomputable def faceDiagonalSupplier_of_simple_sphere : FaceDiagonalSupplier where
  exists_choice := by
    intro D _ _ M hS hSimple f hf
    obtain ⟨d, rfl⟩ := f.exists_rep
    by_contra hNo
    let f : M.Face := M.dartFace d
    let H := M.faceVertexKeptMap f
    have hClique : ∀ u ∈ M.faceVertexSet f, ∀ v ∈ M.faceVertexSet f,
        u ≠ v → M.toSimpleGraph.Adj u v :=
      M.faceVertexSet_clique_of_no_diagonal hSimple hNo
    have hEchoose : H.E = (M.faceVertexSet f).card.choose 2 :=
      M.faceVertexKeptMap_E_eq_choose_two_of_clique hSimple f hClique
    have hEupper : H.E ≤ 3 * H.V - 7 :=
      M.faceVertexKeptMap_E_le_three_mul_V_sub_seven_of_long_face
        hS hSimple (d := d) rfl hf hClique
    have hE2 : 2 ≤ H.E :=
      M.faceVertexKeptMap_two_le_E_of_long_face (d := d) rfl hf
    let n : ℕ := (M.faceVertexSet f).card
    have hn3 : 3 ≤ n := by
      apply three_le_of_two_le_choose_two
      rw [← hEchoose]
      exact hE2
    have hchooseLower : 3 * n - 6 ≤ n.choose 2 :=
      three_mul_sub_six_le_choose_two n hn3
    have hupperE : H.E ≤ 3 * n - 7 := by
      have h := hEupper
      rw [M.faceVertexKeptMap_V_eq_card_faceVertexSet f] at h
      exact h
    have hupperChoose : n.choose 2 ≤ 3 * n - 7 := by
      rw [← hEchoose]
      exact hupperE
    omega

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
supplier theorem and the small face-length lower-bound side condition. -/
noncomputable def triangulationExtension (P : PlaneSimpleGraph V D)
    (hsphere : P.IsSphereMap)
    (hincident : ∀ v : V, ∃ d : D, P.tail d = v)
    (h3 : P.toCombMap.FaceLengthGe 3)
    [Nonempty D] :
    PlaneTriangulationExtension P :=
  P.triangulationExtensionOfCombMap hincident
    (CombMap.triangulate D P.toCombMap
      (P.toCombMap_isSphereMap hsphere hincident)
      P.toCombMap_isSimpleGraph h3 CombMap.faceDiagonalSupplier_of_simple_sphere)

/-- Five-colour theorem for plane simple graphs after producing face diagonals internally.
`h3` is the standard face-length lower bound needed to identify the all-triangular base case. -/
theorem fiveColor_planeSimpleGraph (P : PlaneSimpleGraph V D)
    (hsphere : P.IsSphereMap)
    (hincident : ∀ v : V, ∃ d : D, P.tail d = v)
    (h3 : P.toCombMap.FaceLengthGe 3)
    [Nonempty D] :
    P.G.Colorable 5 :=
  fiveColor_planeSimpleGraph_of_extension P
    (P.triangulationExtension hsphere hincident h3)

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

/-- The triangle witness also routes through the general triangulation producer. -/
theorem fiveColor_triangle_via_triangulate :
    trianglePlaneSimpleGraph.G.Colorable 5 :=
  trianglePlaneSimpleGraph.fiveColor_planeSimpleGraph triangle_plane_isSphere triangle_incident
    triangle_toCombMap_faceLengthGe_three

end TriangleWitness

#print axioms ProofsInTheBook.PlanarMap.PlaneSimpleGraph.toCombMap_isSphereMap
#print axioms ProofsInTheBook.PlanarMap.PlaneSimpleGraph.toCombMap_isSimpleGraph
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.triangle_plane_isSphere
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.triangle_toCombMap_isSphereMap
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.triangle_toCombMap_isSimpleGraph
#print axioms ProofsInTheBook.PlanarMap.colorable_of_triangulationExtension
#print axioms ProofsInTheBook.PlanarMap.fiveColor_planeSimpleGraph_of_extension
#print axioms ProofsInTheBook.PlanarMap.FaceDiagonalSupplier
#print axioms ProofsInTheBook.PlanarMap.CombMap.faceDiagonalSupplier_of_simple_sphere
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.triangle_toCombMap_faceRegular_three
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.triangle_no_long_face
#print axioms ProofsInTheBook.PlanarMap.CombMap.buildNearTriangulationFromAllTriangular
#print axioms ProofsInTheBook.PlanarMap.CombMap.triangulate
#print axioms ProofsInTheBook.PlanarMap.PlaneSimpleGraph.fiveColor_planeSimpleGraph
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.triangleNearTriangulation
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.fiveColor_triangle
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.fiveColor_triangle_via_triangulate

end ProofsInTheBook.PlanarMap
