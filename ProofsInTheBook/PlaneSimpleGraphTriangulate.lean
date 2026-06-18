import ProofsInTheBook.PlaneSimpleGraph
import ProofsInTheBook.PlanarMapSimple

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

#print axioms ProofsInTheBook.PlanarMap.PlaneSimpleGraph.toCombMap_isSphereMap
#print axioms ProofsInTheBook.PlanarMap.PlaneSimpleGraph.toCombMap_isSimpleGraph
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.triangle_plane_isSphere
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.triangle_toCombMap_isSphereMap
#print axioms ProofsInTheBook.PlanarMap.TriangleWitness.triangle_toCombMap_isSimpleGraph

end ProofsInTheBook.PlanarMap
