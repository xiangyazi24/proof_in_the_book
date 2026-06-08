import ProofsInTheBook.PlanarMapEuler

/-!
# The simple graph carried by a combinatorial map

This file is the thin graph layer over `CombMap`: vertex and face orbit quotients,
dart endpoints, the induced simple graph on vertex quotients, and the local
consequences of excluding loops and parallel edges.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Vertices are `σ`-orbits of darts. -/
abbrev Vertex (M : CombMap D) : Type _ :=
  Quotient (cycleSetoid M.σ)

/-- Faces are `φ`-orbits of darts. -/
abbrev Face (M : CombMap D) : Type _ :=
  Quotient (cycleSetoid M.φ)

/-- The vertex at the tail of a dart. -/
def tail (M : CombMap D) (d : D) : M.Vertex :=
  Quotient.mk (cycleSetoid M.σ) d

/-- The vertex at the head of a dart, i.e. the tail of its reverse dart. -/
def head (M : CombMap D) (d : D) : M.Vertex :=
  Quotient.mk (cycleSetoid M.σ) (M.α d)

/-- The face containing a dart. -/
def dartFace (M : CombMap D) (d : D) : M.Face :=
  Quotient.mk (cycleSetoid M.φ) d

/-- The unoriented graph edge represented by a dart. -/
def dartEdge (M : CombMap D) (d : D) : Sym2 M.Vertex :=
  s(M.tail d, M.head d)

lemma alpha_alpha (M : CombMap D) (d : D) : M.α (M.α d) = d := by
  have h := congrArg (fun f : Equiv.Perm D => f d) M.α_invol
  simpa [Equiv.Perm.coe_mul, Function.comp_apply] using h

@[simp]
lemma tail_sigma (M : CombMap D) (d : D) : M.tail (M.σ d) = M.tail d := by
  exact Quotient.sound ⟨-1, by simp⟩

@[simp]
lemma tail_phi (M : CombMap D) (d : D) : M.tail (M.φ d) = M.head d := by
  unfold tail head
  exact Quotient.sound ⟨-1, by simp [φ, Equiv.Perm.coe_mul, Function.comp_apply]⟩

@[simp]
lemma tail_alpha (M : CombMap D) (d : D) : M.tail (M.α d) = M.head d :=
  rfl

@[simp]
lemma head_alpha (M : CombMap D) (d : D) : M.head (M.α d) = M.tail d := by
  unfold head tail
  rw [M.alpha_alpha d]

@[simp]
lemma dartEdge_alpha (M : CombMap D) (d : D) : M.dartEdge (M.α d) = M.dartEdge d := by
  simp [dartEdge, Sym2.eq_swap]

/-- Vertex adjacency induced by the map darts, before deleting loops. -/
def Adj (M : CombMap D) (u v : M.Vertex) : Prop :=
  ∃ d : D, M.dartEdge d = s(u, v)

lemma adj_symm (M : CombMap D) {u v : M.Vertex} (h : M.Adj u v) : M.Adj v u := by
  rcases h with ⟨d, hd⟩
  exact ⟨d, by simpa [Sym2.eq_swap] using hd⟩

lemma adj_of_dart (M : CombMap D) (d : D) : M.Adj (M.tail d) (M.head d) :=
  ⟨d, rfl⟩

/-- The underlying `SimpleGraph` on vertex quotients.  Its adjacency is dart
adjacency with loops removed. -/
def toSimpleGraph (M : CombMap D) : SimpleGraph M.Vertex where
  Adj u v := u ≠ v ∧ M.Adj u v
  symm := by
    intro u v h
    exact ⟨h.1.symm, M.adj_symm h.2⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩

@[simp]
lemma toSimpleGraph_adj (M : CombMap D) (u v : M.Vertex) :
    M.toSimpleGraph.Adj u v ↔ u ≠ v ∧ M.Adj u v :=
  Iff.rfl

/-- No loops and no parallel edges in the quotient graph carried by the map. -/
structure IsSimpleGraph (M : CombMap D) : Prop where
  /-- No dart has equal endpoint vertices. -/
  no_loop : ∀ d : D, M.tail d ≠ M.head d
  /-- Two darts with the same unordered endpoint pair are the same map edge. -/
  no_parallel : ∀ {d e : D}, M.dartEdge d = M.dartEdge e → M.α.SameCycle d e

lemma toSimpleGraph_adj_of_dart (M : CombMap D) (hM : M.IsSimpleGraph) (d : D) :
    M.toSimpleGraph.Adj (M.tail d) (M.head d) :=
  ⟨hM.no_loop d, M.adj_of_dart d⟩

/-- Quotient-endpoint form of the deletion `NoLoopAt` condition. -/
lemma noLoopAt_of_isSimpleGraph (M : CombMap D) (hM : M.IsSimpleGraph) (v : M.Vertex) :
    ∀ d : D, M.tail d = v → M.head d ≠ v := by
  intro d htail hhead
  exact hM.no_loop d (htail.trans hhead.symm)

/-- Dart-representative form of `NoLoopAt`, compatible with `vertexDarts` from
`PlanarMapDelete` without importing that file here. -/
lemma noLoopAt_dart_of_isSimpleGraph (M : CombMap D) (hM : M.IsSimpleGraph) (v d : D)
    (hd : M.σ.SameCycle v d) :
    ¬ M.σ.SameCycle v (M.α d) := by
  intro hαd
  have htail : M.tail v = M.tail d := Quotient.sound hd
  have hhead : M.tail v = M.head d := Quotient.sound hαd
  exact hM.no_loop d (htail.symm.trans hhead)

lemma alpha_sameCycle_of_dartEdge_eq (M : CombMap D) (hM : M.IsSimpleGraph)
    {d e : D} (h : M.dartEdge d = M.dartEdge e) :
    M.α.SameCycle d e :=
  hM.no_parallel h

lemma alpha_sameCycle_of_same_endpoints (M : CombMap D) (hM : M.IsSimpleGraph)
    {d e : D} (htail : M.tail d = M.tail e) (hhead : M.head d = M.head e) :
    M.α.SameCycle d e := by
  exact hM.no_parallel (by simp [dartEdge, htail, hhead])

lemma alpha_sameCycle_of_same_endpoints_symm (M : CombMap D) (hM : M.IsSimpleGraph)
    {d e : D} (htail : M.tail d = M.head e) (hhead : M.head d = M.tail e) :
    M.α.SameCycle d e := by
  exact hM.no_parallel (by simp [dartEdge, htail, hhead, Sym2.eq_swap])

/-- Three darts form a triangular face boundary in cyclic order. -/
def IsFaceTriangle (M : CombMap D) (d₀ d₁ d₂ : D) : Prop :=
  M.φ d₀ = d₁ ∧ M.φ d₁ = d₂ ∧ M.φ d₂ = d₀

lemma dartEdge_eq_mk_tail_tail_phi (M : CombMap D) (d : D) :
    M.dartEdge d = s(M.tail d, M.tail (M.φ d)) := by
  simp [dartEdge]

lemma isFaceTriangle_vertices_pairwiseDistinct (M : CombMap D) (hM : M.IsSimpleGraph)
    {d₀ d₁ d₂ : D} (htri : M.IsFaceTriangle d₀ d₁ d₂) :
    M.tail d₀ ≠ M.tail d₁ ∧
      M.tail d₁ ≠ M.tail d₂ ∧
      M.tail d₂ ≠ M.tail d₀ := by
  rcases htri with ⟨h₀₁, h₁₂, h₂₀⟩
  constructor
  · intro h
    apply hM.no_loop d₀
    have hnext : M.tail d₁ = M.head d₀ := by
      rw [← h₀₁]
      simp
    exact h.trans hnext
  constructor
  · intro h
    apply hM.no_loop d₁
    have hnext : M.tail d₂ = M.head d₁ := by
      rw [← h₁₂]
      simp
    exact h.trans hnext
  · intro h
    apply hM.no_loop d₂
    have hnext : M.tail d₀ = M.head d₂ := by
      rw [← h₂₀]
      simp
    exact h.trans hnext

/-- The three boundary edges of a simple triangular face are pairwise distinct. -/
lemma isFaceTriangle_boundaryEdges_pairwiseDistinct (M : CombMap D) (hM : M.IsSimpleGraph)
    {d₀ d₁ d₂ : D} (htri : M.IsFaceTriangle d₀ d₁ d₂) :
    M.dartEdge d₀ ≠ M.dartEdge d₁ ∧
      M.dartEdge d₁ ≠ M.dartEdge d₂ ∧
      M.dartEdge d₂ ≠ M.dartEdge d₀ := by
  rcases htri with ⟨h₀₁, h₁₂, h₂₀⟩
  have hverts := M.isFaceTriangle_vertices_pairwiseDistinct hM ⟨h₀₁, h₁₂, h₂₀⟩
  let v₀ := M.tail d₀
  let v₁ := M.tail d₁
  let v₂ := M.tail d₂
  have he₀ : M.dartEdge d₀ = s(v₀, v₁) := by
    rw [M.dartEdge_eq_mk_tail_tail_phi d₀, h₀₁]
  have he₁ : M.dartEdge d₁ = s(v₁, v₂) := by
    rw [M.dartEdge_eq_mk_tail_tail_phi d₁, h₁₂]
  have he₂ : M.dartEdge d₂ = s(v₂, v₀) := by
    rw [M.dartEdge_eq_mk_tail_tail_phi d₂, h₂₀]
  constructor
  · intro h
    have hs : s(v₀, v₁) = s(v₁, v₂) := he₀.symm.trans (h.trans he₁)
    rw [Sym2.eq_iff] at hs
    rcases hs with ⟨hv₀₁, _⟩ | ⟨hv₀₂, _⟩
    · exact hverts.1 hv₀₁
    · exact hverts.2.2 hv₀₂.symm
  constructor
  · intro h
    have hs : s(v₁, v₂) = s(v₂, v₀) := he₁.symm.trans (h.trans he₂)
    rw [Sym2.eq_iff] at hs
    rcases hs with ⟨hv₁₂, _⟩ | ⟨hv₁₀, _⟩
    · exact hverts.2.1 hv₁₂
    · exact hverts.1 hv₁₀.symm
  · intro h
    have hs : s(v₂, v₀) = s(v₀, v₁) := he₂.symm.trans (h.trans he₀)
    rw [Sym2.eq_iff] at hs
    rcases hs with ⟨hv₂₀, _⟩ | ⟨hv₂₁, _⟩
    · exact hverts.2.2 hv₂₀
    · exact hverts.2.1 hv₂₁.symm

end CombMap

end ProofsInTheBook.PlanarMap
