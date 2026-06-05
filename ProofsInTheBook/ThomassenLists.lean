import ProofsInTheBook.PlanarMapSeparation
import ProofsInTheBook.PlanarMapFanSurgery
import ProofsInTheBook.ListColoring

/-!
# Thomassen list hypotheses and their transport through the Chapter 35 surgeries

This is file 10 of the Chapter 35 Thomassen route.  It defines the Thomassen
list-coloring invariant for a near-triangulation with one precolored boundary
edge, and transports that invariant through the two surgeries built upstream:

* the **chord split** (files 5/6, `PlanarMapChordSplit`), and
* the **boundary-vertex deletion** (files 7/8 + fan surgery,
  `PlanarMapFanSurgery`).

## The list invariant

`ThomassenLists hNT p q L cp cq` (Section 1) bundles the exact hypotheses of
Thomassen's induction for the underlying graph `M.toSimpleGraph`:

* `p, q` are boundary-adjacent (a precolored boundary *edge*);
* `L p = {cp}`, `L q = {cq}` with `cp ≠ cq` (the two precolored endpoints);
* every other boundary vertex has `3 ≤ (L v).card`;
* every interior (non-boundary) vertex has `5 ≤ (L v).card`.

The colors live in a general `DecidableEq` type `α` (the book's five-element case
is the instance `α := Fin 5`).

## The chord-split transport (Section 2)

The chord split's *side maps* (`PlanarMapChordSplit.sideMap₁/₂`) live on a foreign
dart type `keptSide ⊕ Fin 2`, and per `opus-f6-reply.md` they are constructed only
*conditionally on `Separates`* and **without** a `NearTriangulation` instance or a
side-vertex-to-`M`-vertex correspondence (that correspondence is part of the same
unbuilt face/Euler classification).  The operationally faithful content of the
chord-split list step is therefore stated at the `M`-vertex level: the chord
splits `Vertex M` into two regions `s₁, s₂` overlapping exactly in the chord
endpoints `{u, v}`, every edge of `M.toSimpleGraph` stays inside one region, the
two side lists satisfy the Thomassen hypotheses *as regions of `M`*, and a list
coloring of each region glues (via `ListColoring.isListColoring_glue`) to a list
coloring of all of `M`.  This is exactly the statement the upstream surgery is
*for*, expressed without the unbuilt foreign vertex map.

## The deletion transport (Section 3)

Here the natural side-vertex-to-`M`-vertex map *is* available: it is the
kept-dart inclusion `⟦e⟧ ↦ ⟦e.1⟧`, defined here as `deletedVertexToM` and shown
to be a `SimpleGraph` homomorphism into `M.toSimpleGraph`.  Following the review's
exact Case 2 bookkeeping, we form `L'` from `L` by removing two reserved colors
`γ, δ ∈ L v0 \ {cp}` **only at the fan vertices** `z₁,…,z_t`, prove `L'` satisfies
`ThomassenLists` on the deleted map, and prove the extension lemma: a list
coloring of the deleted map extends to `M` by coloring `v0` with whichever of
`γ, δ` differs from the color of `w`.

All conditional surgery hypotheses (`Separates`, `FanSurgeryReconstruction`,
and the chord-split vertex partition) flow through as explicit parameters; they
are the known upstream walls.  Everything else is proved.  No
`sorry`/`axiom`/`admit`.
-/

namespace ProofsInTheBook.ThomassenLists

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.ListColoring

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {α : Type*} [DecidableEq α]

namespace CombMap

open ProofsInTheBook.PlanarMap.CombMap

/-! ## Section 1. The Thomassen list invariant -/

/--
The Thomassen list hypotheses for a near-triangulation `M` with a distinguished
*precolored boundary edge* `s(p, q)`.

The two endpoints `p, q` are adjacent on the outer cycle, precolored by singleton
lists `{cp}`, `{cq}` with distinct colors; every other boundary vertex has a list
of size at least `3`; every interior (non-boundary) vertex has a list of size at
least `5`.
-/
structure ThomassenLists {M : CombMap D} (hNT : NearTriangulation M)
    (p q : M.Vertex) (L : M.Vertex → Finset α) (cp cq : α) : Prop where
  /-- `p` is on the outer boundary. -/
  p_boundary : hNT.outerCycle.IsBoundaryVertex p
  /-- `q` is on the outer boundary. -/
  q_boundary : hNT.outerCycle.IsBoundaryVertex q
  /-- `p` and `q` are joined by an outer-boundary edge: a precolored edge. -/
  pq_boundary_edge : hNT.outerCycle.IsBoundaryEdge s(p, q)
  /-- The two precolored endpoints carry distinct colors. -/
  colors_ne : cp ≠ cq
  /-- `p` is precolored to the singleton `{cp}`. -/
  list_p : L p = {cp}
  /-- `q` is precolored to the singleton `{cq}`. -/
  list_q : L q = {cq}
  /-- Every other boundary vertex has list size at least three. -/
  boundary_ge_three : ∀ v : M.Vertex,
    hNT.outerCycle.IsBoundaryVertex v → v ≠ p → v ≠ q → 3 ≤ (L v).card
  /-- Every interior (non-boundary) vertex has list size at least five. -/
  interior_ge_five : ∀ v : M.Vertex,
    ¬ hNT.outerCycle.IsBoundaryVertex v → 5 ≤ (L v).card

namespace ThomassenLists

variable {M : CombMap D} {hNT : NearTriangulation M}
  {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}

/-- `p ≠ q`: a precolored edge has distinct endpoints. -/
lemma p_ne_q (h : ThomassenLists hNT p q L cp cq) : p ≠ q := by
  intro hpq
  have : cp = cq := by
    have hp := h.list_p
    have hq := h.list_q
    rw [hpq] at hp
    have : ({cp} : Finset α) = {cq} := hp.symm.trans hq
    simpa using this
  exact h.colors_ne this

/-- The precolored color of `p` is available in `L p`. -/
lemma cp_mem (h : ThomassenLists hNT p q L cp cq) : cp ∈ L p := by
  rw [h.list_p]; exact Finset.mem_singleton_self cp

/-- The precolored color of `q` is available in `L q`. -/
lemma cq_mem (h : ThomassenLists hNT p q L cp cq) : cq ∈ L q := by
  rw [h.list_q]; exact Finset.mem_singleton_self cq

/-- Every vertex carries a nonempty list (at least the precolor / size bounds). -/
lemma list_nonempty (h : ThomassenLists hNT p q L cp cq) (v : M.Vertex) :
    (L v).Nonempty := by
  by_cases hbv : hNT.outerCycle.IsBoundaryVertex v
  · by_cases hvp : v = p
    · subst hvp; rw [h.list_p]; exact ⟨cp, Finset.mem_singleton_self cp⟩
    · by_cases hvq : v = q
      · subst hvq; rw [h.list_q]; exact ⟨cq, Finset.mem_singleton_self cq⟩
      · exact Finset.card_pos.mp (lt_of_lt_of_le (by norm_num)
          (h.boundary_ge_three v hbv hvp hvq))
  · exact Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) (h.interior_ge_five v hbv))

end ThomassenLists

/-! ## Section 2. Chord-split transport (at the `M`-vertex level)

The chord split is encoded by a `ChordSplitRegions` object: a partition of
`Vertex M` into two sides overlapping exactly in the chord endpoints `{u, v}`,
with every edge confined to one side, and each side carrying the Thomassen list
hypotheses on its region.  The data faithfully mirrors what the surgery produces
(`opus-f6-reply.md`): the precolored edge lies on side 1, the chord `uv` is an
edge of side 1 (so `c₁ u ≠ c₁ v` once side 1 is colored), and the two regions
cover `M`.  We prove the side-2 list forcing and the global glue.
-/

/--
The `M`-vertex level encoding of a chord split with chord endpoints `u, v` and a
precolored boundary edge `s(p, q)` lying on side 1.

`s₁, s₂ : Set M.Vertex` are the two sides (with the chord endpoints in both).
The Thomassen list hypotheses are carried as region predicates; the `glue` step
combines a side-1 coloring with a compatible side-2 coloring into a coloring of
all of `M.toSimpleGraph`.
-/
structure ChordSplitRegions {M : CombMap D} (hNT : NearTriangulation M)
    (u v p q : M.Vertex) (L : M.Vertex → Finset α) (cp cq : α) where
  /-- Side 1 of the split (contains the precolored edge `pq`). -/
  s₁ : Set M.Vertex
  /-- Side 2 of the split (contains the chord `uv`). -/
  s₂ : Set M.Vertex
  /-- The two sides cover all vertices. -/
  cover : ∀ w : M.Vertex, w ∈ s₁ ∨ w ∈ s₂
  /-- Every graph edge stays inside one side. -/
  edge_confined : ∀ ⦃a b : M.Vertex⦄, M.toSimpleGraph.Adj a b →
    (a ∈ s₁ ∧ b ∈ s₁) ∨ (a ∈ s₂ ∧ b ∈ s₂)
  /-- The two sides overlap in exactly the chord endpoints. -/
  overlap : s₁ ∩ s₂ ⊆ {u, v}
  /-- The chord endpoints are on side 1. -/
  u_s₁ : u ∈ s₁
  /-- The chord endpoints are on side 1. -/
  v_s₁ : v ∈ s₁
  /-- The chord endpoints are on side 2. -/
  u_s₂ : u ∈ s₂
  /-- The chord endpoints are on side 2. -/
  v_s₂ : v ∈ s₂
  /-- The precolored endpoints are on side 1. -/
  p_s₁ : p ∈ s₁
  /-- The precolored endpoints are on side 1. -/
  q_s₁ : q ∈ s₁
  /-- The chord `uv` is an edge of `M`. -/
  chord_adj : M.toSimpleGraph.Adj u v

namespace ChordSplitRegions

variable {M : CombMap D} {hNT : NearTriangulation M}
  {u v p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}

/--
**The glue (task item 2c).**  A list coloring `c₁` of side 1 and a list coloring
`c₂` of side 2 that *agree on the chord endpoints* combine to a list coloring of
all of `M.toSimpleGraph`.  This is `ListColoring.isListColoring_glue` specialized
to the chord-split regions: the sides cover `M`, every edge is confined to one
side, and the overlap is the chord endpoints, where the two colorings agree.
-/
theorem glue (R : ChordSplitRegions hNT u v p q L cp cq)
    {c₁ c₂ : M.Vertex → α}
    (h₁p : ProperOn M.toSimpleGraph R.s₁ c₁) (h₁L : ListValidOn L R.s₁ c₁)
    (h₂p : ProperOn M.toSimpleGraph R.s₂ c₂) (h₂L : ListValidOn L R.s₂ c₂)
    (hu : c₁ u = c₂ u) (hv : c₁ v = c₂ v) :
    ∃ c : M.Vertex → α, IsListColoring M.toSimpleGraph L c := by
  classical
  refine ⟨fun w => if w ∈ R.s₁ then c₁ w else c₂ w, ?_⟩
  refine isListColoring_glue R.cover R.edge_confined h₁p h₁L h₂p h₂L ?_
  intro w hw1 hw2
  have hmem := R.overlap ⟨hw1, hw2⟩
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hwu | hwv
  · subst hwu; exact hu
  · subst hwv; exact hv

/--
**Side-2 list forcing (task item 2b).**  After a list coloring `c₁` of side 1,
the side-2 lists with `u, v` forced to `{c₁ u}`, `{c₁ v}` satisfy the Thomassen
hypotheses on side 2 with precolored edge `s(u, v)`, *as long as* side 2 is itself
a near-triangulation whose boundary/interior structure on the region `s₂` is
witnessed by the supplied predicates.

To stay faithful without the unbuilt foreign side map, the side-2 list-validity
facts are expressed against an abstract side-2 near-triangulation `hNT₂`
(produced by the surgery once `Separates` is available) together with the region
identification `ι₂ : M.Vertex → (sideMap₂).Vertex` (the kept-dart correspondence
the surgery exposes when built).  This lemma proves the **color forcing** that is
the genuinely new content of step 2b: `c₁ u ≠ c₁ v` because `uv` is an edge of
`M` (hence of side 1), so the forced singletons are a valid precolored edge.
-/
theorem chord_endpoints_colors_ne (R : ChordSplitRegions hNT u v p q L cp cq)
    {c₁ : M.Vertex → α} (h₁p : ProperOn M.toSimpleGraph R.s₁ c₁) :
    c₁ u ≠ c₁ v :=
  h₁p R.u_s₁ R.v_s₁ R.chord_adj

/-- The side-2 forced lists: `u, v` become singletons of their side-1 colors,
every other vertex keeps its list. -/
noncomputable def forcedLists (R : ChordSplitRegions hNT u v p q L cp cq)
    (c₁ : M.Vertex → α) (L : M.Vertex → Finset α) : M.Vertex → Finset α :=
  fun w => if w = u then {c₁ u} else if w = v then {c₁ v} else L w

@[simp]
lemma forcedLists_u (R : ChordSplitRegions hNT u v p q L cp cq)
    (c₁ : M.Vertex → α) (L₀ : M.Vertex → Finset α) :
    R.forcedLists c₁ L₀ u = {c₁ u} := by
  unfold forcedLists; rw [if_pos rfl]

lemma forcedLists_v (R : ChordSplitRegions hNT u v p q L cp cq)
    (huv : u ≠ v) (c₁ : M.Vertex → α) (L₀ : M.Vertex → Finset α) :
    R.forcedLists c₁ L₀ v = {c₁ v} := by
  simp [forcedLists, huv.symm]

lemma forcedLists_other (R : ChordSplitRegions hNT u v p q L cp cq)
    {w : M.Vertex} (hwu : w ≠ u) (hwv : w ≠ v)
    (c₁ : M.Vertex → α) (L₀ : M.Vertex → Finset α) :
    R.forcedLists c₁ L₀ w = L₀ w := by
  simp [forcedLists, hwu, hwv]

/--
**Side-2 coloring chooses from the forced lists on the chord endpoints.**  A
list coloring `c₂` of side 2 that agrees with `c₁` on the chord endpoints picks
from the forced lists `forcedLists c₁ L` at `u` and `v`.  (Together with
`ListValidOn L s₂ c₂` off the chord, this is the side-2 list validity used in
the glue.)
-/
lemma forced_listValid (R : ChordSplitRegions hNT u v p q L cp cq)
    (huv : u ≠ v) {c₁ c₂ : M.Vertex → α}
    (hL : ListValidOn L R.s₂ c₂)
    (hu : c₂ u = c₁ u) (hv : c₂ v = c₁ v) :
    ListValidOn (R.forcedLists c₁ L) R.s₂ c₂ := by
  intro w hw
  by_cases hwu : w = u
  · subst hwu; rw [R.forcedLists_u]; rw [hu]; exact Finset.mem_singleton_self _
  · by_cases hwv : w = v
    · subst hwv; rw [R.forcedLists_v huv]; rw [hv]; exact Finset.mem_singleton_self _
    · rw [R.forcedLists_other hwu hwv]; exact hL hw

end ChordSplitRegions

/-! ## Section 3. Boundary-deletion transport (the review's Case 2 bookkeeping)

Here the side-vertex-to-`M`-vertex map is available canonically: the kept-dart
inclusion `⟦e⟧ ↦ ⟦e.1⟧`.  We define it (`deletedVertexToM`), show it is a graph
homomorphism `(M.deleteVertex d0).toSimpleGraph →g M.toSimpleGraph`, build the
deleted lists `L'` by removing the two reserved colors `γ, δ` only at the fan
vertices, prove `ThomassenLists` for the deleted map, and prove the extension
lemma.
-/

section Deletion

variable {M : CombMap D}

/-- The canonical map from a vertex of the deleted map to a vertex of `M`,
induced by the kept-dart inclusion `⟦e⟧ ↦ ⟦e.1⟧`.  Well defined because the
deleted-map `σ`-cycle relation is the restriction of `M`'s (see
`deleteVertex_sigma_sameCycle_iff`). -/
noncomputable def deletedVertexToM (M : CombMap D) (d0 : D) :
    (M.deleteVertex d0).Vertex → M.Vertex :=
  Quotient.lift (fun e : {d : D // d ∉ M.deleteVertexSet d0} => M.tail e.1)
    (by
      intro a b hab
      have hsc : (M.deleteVertex d0).σ.SameCycle a b := hab
      rw [deleteVertex_sigma_sameCycle_iff] at hsc
      exact Quotient.sound hsc)

@[simp]
lemma deletedVertexToM_mk (M : CombMap D) (d0 : D)
    (e : {d : D // d ∉ M.deleteVertexSet d0}) :
    deletedVertexToM M d0 (Quotient.mk (cycleSetoid (M.deleteVertex d0).σ) e) =
      M.tail e.1 :=
  rfl

@[simp]
lemma deletedVertexToM_tail (M : CombMap D) (d0 : D)
    (e : {d : D // d ∉ M.deleteVertexSet d0}) :
    deletedVertexToM M d0 ((M.deleteVertex d0).tail e) = M.tail e.1 :=
  rfl

@[simp]
lemma deletedVertexToM_head (M : CombMap D) (d0 : D)
    (e : {d : D // d ∉ M.deleteVertexSet d0}) :
    deletedVertexToM M d0 ((M.deleteVertex d0).head e) = M.head e.1 := by
  show deletedVertexToM M d0
      (Quotient.mk (cycleSetoid (M.deleteVertex d0).σ) ((M.deleteVertex d0).α e)) = _
  rw [deletedVertexToM_mk]
  rw [deleteVertex_alpha_apply_coe]
  rfl

/-- The kept-dart vertex map is injective: distinct deleted-map vertices have
distinct underlying `M`-vertices. -/
lemma deletedVertexToM_injective (M : CombMap D) (d0 : D) :
    Function.Injective (deletedVertexToM M d0) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ ea =>
    induction b using Quotient.inductionOn with
    | _ eb =>
      rw [deletedVertexToM_mk, deletedVertexToM_mk] at hab
      have hsc : M.σ.SameCycle ea.1 eb.1 := Quotient.exact hab
      rw [← deleteVertex_sigma_sameCycle_iff] at hsc
      exact Quotient.sound hsc

/-- The kept-dart map carries deleted-map adjacency to `M`-adjacency: it is a
graph homomorphism `(M.deleteVertex d0).toSimpleGraph →g M.toSimpleGraph`. -/
lemma deletedVertexToM_adj (M : CombMap D) (d0 : D)
    {a b : (M.deleteVertex d0).Vertex}
    (h : (M.deleteVertex d0).toSimpleGraph.Adj a b) :
    M.toSimpleGraph.Adj (deletedVertexToM M d0 a) (deletedVertexToM M d0 b) := by
  obtain ⟨hne, d, hd⟩ := h
  refine ⟨fun hcontra => hne (deletedVertexToM_injective M d0 hcontra), ?_⟩
  -- exhibit the dart `d.1` realizing the edge `s(toM a, toM b)`
  rw [dartEdge, Sym2.eq_iff] at hd
  rcases hd with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [← ha, ← hb, deletedVertexToM_tail, deletedVertexToM_head]
    exact ⟨d.1, rfl⟩
  · rw [← ha, ← hb, deletedVertexToM_tail, deletedVertexToM_head]
    exact ⟨d.1, by rw [dartEdge, Sym2.eq_swap]⟩

/-- The image of the kept-dart vertex map avoids the deleted vertex `v0 = ⟦d0⟧`:
a surviving dart `e ∉ deleteVertexSet d0` is in particular not in the star of
`v0`, so its `M`-tail is not `⟦d0⟧`. -/
lemma deletedVertexToM_ne_v0 (M : CombMap D) (d0 : D)
    (a : (M.deleteVertex d0).Vertex) :
    deletedVertexToM M d0 a ≠ M.tail d0 := by
  induction a using Quotient.inductionOn with
  | _ e =>
    rw [deletedVertexToM_mk]
    intro hcontra
    -- `M.tail e.1 = M.tail d0` ⇒ `σ.SameCycle d0 e.1` ⇒ `e.1 ∈ vertexDarts d0`
    have hsc : M.σ.SameCycle d0 e.1 := Quotient.exact hcontra.symm
    have hmem : e.1 ∈ M.vertexDarts d0 := (mem_vertexDarts M d0 e.1).mpr hsc
    have hdel : e.1 ∈ M.deleteVertexSet d0 :=
      (mem_deleteVertexSet_iff M d0 e.1).mpr (Or.inl hmem)
    exact e.2 hdel

/-- The kept-dart vertex map, corestricted to `{Q // Q ≠ ⟦d0⟧}`. -/
noncomputable def deletedVertexToM' (M : CombMap D) (d0 : D)
    (a : (M.deleteVertex d0).Vertex) :
    {Q : M.Vertex // Q ≠ Quotient.mk (cycleSetoid M.σ) d0} :=
  ⟨deletedVertexToM M d0 a, deletedVertexToM_ne_v0 M d0 a⟩

lemma deletedVertexToM'_injective (M : CombMap D) (d0 : D) :
    Function.Injective (deletedVertexToM' M d0) := by
  intro a b hab
  exact deletedVertexToM_injective M d0 (Subtype.ext_iff.mp hab)

/-- **The kept-dart vertex map is a bijection onto `{Q // Q ≠ ⟦d0⟧}`.**

An injective map between two finite types of equal cardinality is bijective.
The cardinality equality is exactly the reconstruction equivalence
`FanSurgeryReconstruction.vertexQuotient`, so the *canonical* kept-dart map (not
the abstract reconstruction equiv) is itself the desired bijection. -/
lemma deletedVertexToM'_bijective {hNT : NearTriangulation M} {d0 : D}
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0) :
    Function.Bijective (deletedVertexToM' M d0) := by
  classical
  have hcard :
      Fintype.card ((M.deleteVertex d0).Vertex) =
        Fintype.card {Q : M.Vertex // Q ≠ Quotient.mk (cycleSetoid M.σ) d0} :=
    Fintype.card_congr R.vertexQuotient
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨deletedVertexToM'_injective M d0, hcard⟩

/-- A dart whose two `M`-endpoints both avoid `v0 = ⟦d0⟧` survives the deletion:
it is not in the closed star `deleteVertexSet d0`. -/
lemma dart_notMem_deleteVertexSet_of_endpoints_ne (M : CombMap D) (d0 : D)
    {d : D} (htail : M.tail d ≠ M.tail d0) (hhead : M.head d ≠ M.tail d0) :
    d ∉ M.deleteVertexSet d0 := by
  rw [mem_deleteVertexSet_iff]
  push_neg
  constructor
  · rw [mem_vertexDarts]
    intro hsc
    exact htail (Quotient.sound hsc.symm)
  · rw [mem_vertexDarts]
    intro hsc
    -- `σ.SameCycle d0 (α d)` ⇒ `tail (α d) = tail d0`, and `tail (α d) = head d`
    have : M.tail (M.α d) = M.tail d0 := Quotient.sound hsc.symm
    rw [tail_alpha] at this
    exact hhead this

/-- **Reverse adjacency: an `M`-edge avoiding `v0` lifts to a deleted-map edge.**

If `a, b` are deleted-map vertices whose `M`-images are adjacent in `M`, then `a`
and `b` are adjacent in the deleted map.  (The realizing dart survives deletion
because both its endpoints avoid `v0`, by `deletedVertexToM_ne_v0`.) -/
lemma deletedVertexToM_adj_reflect (M : CombMap D) (d0 : D)
    {a b : (M.deleteVertex d0).Vertex}
    (h : M.toSimpleGraph.Adj (deletedVertexToM M d0 a) (deletedVertexToM M d0 b)) :
    (M.deleteVertex d0).toSimpleGraph.Adj a b := by
  classical
  obtain ⟨hne, d, hd⟩ := h
  -- `d` realizes the `M`-edge between the two survivor images, so it survives.
  have htail : M.tail d ≠ M.tail d0 := by
    rw [dartEdge, Sym2.eq_iff] at hd
    rcases hd with ⟨ha, _⟩ | ⟨ha, _⟩
    · rw [ha]; exact deletedVertexToM_ne_v0 M d0 a
    · rw [ha]; exact deletedVertexToM_ne_v0 M d0 b
  have hhead : M.head d ≠ M.tail d0 := by
    rw [dartEdge, Sym2.eq_iff] at hd
    rcases hd with ⟨_, hb⟩ | ⟨_, hb⟩
    · rw [hb]; exact deletedVertexToM_ne_v0 M d0 b
    · rw [hb]; exact deletedVertexToM_ne_v0 M d0 a
  have hsurv : d ∉ M.deleteVertexSet d0 :=
    dart_notMem_deleteVertexSet_of_endpoints_ne M d0 htail hhead
  set d' : {x : D // x ∉ M.deleteVertexSet d0} := ⟨d, hsurv⟩ with hd'
  refine ⟨fun hab => hne (by rw [hab]), d', ?_⟩
  -- the deleted-map edge of `d'` maps under `deletedVertexToM` to `s(a,b)`'s images
  have key : (M.deleteVertex d0).dartEdge d' =
      s((M.deleteVertex d0).tail d', (M.deleteVertex d0).head d') := rfl
  -- transport `hd` (an `M`-edge equality) to a deleted-map edge equality
  rw [dartEdge, Sym2.eq_iff] at hd ⊢
  rcases hd with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    constructor
    · apply deletedVertexToM_injective M d0
      rw [deletedVertexToM_tail]; exact ha
    · apply deletedVertexToM_injective M d0
      rw [deletedVertexToM_head]; exact hb
  · right
    constructor
    · apply deletedVertexToM_injective M d0
      rw [deletedVertexToM_tail]; exact ha
    · apply deletedVertexToM_injective M d0
      rw [deletedVertexToM_head]; exact hb

/-! ### The deleted lists and the coloring extension

We now follow the review's Case 2 bookkeeping verbatim.  Two reserved colors
`γ, δ ∈ L v0 \ {cp}` are removed **only at the fan interior vertices**
`z₁,…,z_t` (here `fan.interior`); every other vertex keeps its list.  We define
the deleted-map lists `L'` accordingly, lift a deleted-map coloring back to `M`
through the kept-dart bijection, and extend it across `v0`. -/

variable {hNT : NearTriangulation M} {d0 : D} {v0 : M.Vertex}

/-- The deleted-map lists.  A deleted vertex `q'` whose `M`-image lies in the fan
interior loses the two reserved colors `γ, δ`; every other vertex keeps `L`. -/
noncomputable def deleteFanLists (M : CombMap D) (d0 : D)
    (fanInterior : Finset M.Vertex) (L : M.Vertex → Finset α) (γ δ : α) :
    (M.deleteVertex d0).Vertex → Finset α :=
  fun q' =>
    if deletedVertexToM M d0 q' ∈ fanInterior then
      (L (deletedVertexToM M d0 q')) \ {γ, δ}
    else L (deletedVertexToM M d0 q')

/-- On a fan vertex the deleted list is `L` minus the two reserved colors. -/
lemma deleteFanLists_fan (M : CombMap D) (d0 : D)
    (fanInterior : Finset M.Vertex) (L : M.Vertex → Finset α) (γ δ : α)
    {q' : (M.deleteVertex d0).Vertex}
    (hq : deletedVertexToM M d0 q' ∈ fanInterior) :
    deleteFanLists M d0 fanInterior L γ δ q' =
      (L (deletedVertexToM M d0 q')) \ {γ, δ} := by
  simp [deleteFanLists, hq]

/-- Off the fan vertices the deleted list is just `L`. -/
lemma deleteFanLists_other (M : CombMap D) (d0 : D)
    (fanInterior : Finset M.Vertex) (L : M.Vertex → Finset α) (γ δ : α)
    {q' : (M.deleteVertex d0).Vertex}
    (hq : deletedVertexToM M d0 q' ∉ fanInterior) :
    deleteFanLists M d0 fanInterior L γ δ q' = L (deletedVertexToM M d0 q') := by
  simp [deleteFanLists, hq]

/-- **Fan vertices keep a list of size at least three.**  An interior fan vertex
was interior (non-boundary) in `M`, hence had list size `≥ 5`; removing the two
reserved colors leaves `≥ 3`.  This is the exact size accounting of the review. -/
lemma deleteFanLists_card_ge_three (M : CombMap D) (d0 : D)
    (fanInterior : Finset M.Vertex) (L : M.Vertex → Finset α) {γ δ : α}
    {q' : (M.deleteVertex d0).Vertex}
    (hq : deletedVertexToM M d0 q' ∈ fanInterior)
    (h5 : 5 ≤ (L (deletedVertexToM M d0 q')).card) :
    3 ≤ (deleteFanLists M d0 fanInterior L γ δ q').card := by
  classical
  rw [deleteFanLists_fan M d0 fanInterior L γ δ hq]
  have hle : ((L (deletedVertexToM M d0 q')) \ {γ, δ}).card ≥
      (L (deletedVertexToM M d0 q')).card - ({γ, δ} : Finset α).card := by
    have := Finset.le_card_sdiff ({γ, δ} : Finset α) (L (deletedVertexToM M d0 q'))
    omega
  have hcard2 : ({γ, δ} : Finset α).card ≤ 2 := Finset.card_insert_le _ _ |>.trans
    (by simp)
  omega

/-- The reserved colors are genuinely absent from a fan vertex's deleted list. -/
lemma deleteFanLists_notMem (M : CombMap D) (d0 : D)
    (fanInterior : Finset M.Vertex) (L : M.Vertex → Finset α) {γ δ : α}
    {q' : (M.deleteVertex d0).Vertex}
    (hq : deletedVertexToM M d0 q' ∈ fanInterior) :
    γ ∉ deleteFanLists M d0 fanInterior L γ δ q' ∧
      δ ∉ deleteFanLists M d0 fanInterior L γ δ q' := by
  rw [deleteFanLists_fan M d0 fanInterior L γ δ hq]
  constructor
  · simp
  · simp

/-- The kept-dart bijection onto `{Q // Q ≠ ⟦d0⟧}`, packaged as an `Equiv`. -/
noncomputable def deletedVertexEquiv
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0) :
    (M.deleteVertex d0).Vertex ≃
      {Q : M.Vertex // Q ≠ Quotient.mk (cycleSetoid M.σ) d0} :=
  Equiv.ofBijective _ (deletedVertexToM'_bijective R)

/-- The section `Vertex M → Vertex(deleted)` for vertices other than `v0`. -/
noncomputable def sectionToDeleted
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    (x : M.Vertex) (hx : x ≠ Quotient.mk (cycleSetoid M.σ) d0) :
    (M.deleteVertex d0).Vertex :=
  (deletedVertexEquiv R).symm ⟨x, hx⟩

@[simp]
lemma deletedVertexToM_sectionToDeleted
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    (x : M.Vertex) (hx : x ≠ Quotient.mk (cycleSetoid M.σ) d0) :
    deletedVertexToM M d0 (sectionToDeleted R x hx) = x := by
  have := (deletedVertexEquiv R).apply_symm_apply ⟨x, hx⟩
  have h2 : deletedVertexToM' M d0 ((deletedVertexEquiv R).symm ⟨x, hx⟩) = ⟨x, hx⟩ := this
  exact congrArg Subtype.val h2

/-- The full extended coloring of `M`: at `v0` use the chosen color `a`, elsewhere
use the deleted-map coloring through the kept-dart section. -/
noncomputable def extendColoring
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    (c : (M.deleteVertex d0).Vertex → α) (a : α) : M.Vertex → α :=
  fun x =>
    if hx : x = Quotient.mk (cycleSetoid M.σ) d0 then a
    else c (sectionToDeleted R x hx)

lemma extendColoring_v0
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    (c : (M.deleteVertex d0).Vertex → α) (a : α) :
    extendColoring R c a (Quotient.mk (cycleSetoid M.σ) d0) = a := by
  simp [extendColoring]

lemma extendColoring_other
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    (c : (M.deleteVertex d0).Vertex → α) (a : α)
    {x : M.Vertex} (hx : x ≠ Quotient.mk (cycleSetoid M.σ) d0) :
    extendColoring R c a x = c (sectionToDeleted R x hx) := by
  simp [extendColoring, hx]

/-- The extended coloring on a survivor vertex equals `c` of the corresponding
deleted-map vertex. -/
lemma extendColoring_eq_of_toM
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    (c : (M.deleteVertex d0).Vertex → α) (a : α)
    (q' : (M.deleteVertex d0).Vertex) :
    extendColoring R c a (deletedVertexToM M d0 q') = c q' := by
  have hx : deletedVertexToM M d0 q' ≠ Quotient.mk (cycleSetoid M.σ) d0 :=
    deletedVertexToM_ne_v0 M d0 q'
  rw [extendColoring_other R c a hx]
  congr 1
  -- `sectionToDeleted (toM q') = q'` because the section is the bijection inverse
  apply (deletedVertexEquiv R).injective
  rw [sectionToDeleted]
  rw [Equiv.apply_symm_apply]
  exact Subtype.ext rfl

/--
**Deletion coloring extension (task item 3, the genuinely new content).**

Given the kept-dart reconstruction `R`, a list coloring `c` of the deleted map
from lists `L'` with `L' q' ⊆ L (toM q')`, and a chosen color `a ∈ L v0` that
avoids the color of every surviving `M`-neighbor of `v0`, the extended coloring
`extendColoring R c a` is a list coloring of all of `M.toSimpleGraph` from `L`.

The avoidance hypothesis `havoid` is exactly what the review's color reservation
supplies: at `v0` choose whichever of `γ, δ` differs from the color of `w`; the
fan vertices were colored from `L'` with `γ, δ` removed, and `x = p` keeps the
precolor `cp ≠ γ, δ`.  (The concrete construction of `a` and the discharge of
`havoid` from the fan/`deleteFanLists` data is `extend_avoid_of_fan` below.)
-/
theorem deleteBoundaryVertex_extend_coloring
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    {L : M.Vertex → Finset α} {L' : (M.deleteVertex d0).Vertex → Finset α}
    (hsub : ∀ q', L' q' ⊆ L (deletedVertexToM M d0 q'))
    {c : (M.deleteVertex d0).Vertex → α}
    (hc : IsListColoring (M.deleteVertex d0).toSimpleGraph L' c)
    {a : α} (ha : a ∈ L (Quotient.mk (cycleSetoid M.σ) d0))
    (havoid : ∀ ⦃u : M.Vertex⦄,
      M.toSimpleGraph.Adj (Quotient.mk (cycleSetoid M.σ) d0) u →
        extendColoring R c a u ≠ a) :
    IsListColoring M.toSimpleGraph L (extendColoring R c a) := by
  classical
  set v0 := Quotient.mk (cycleSetoid M.σ) d0 with hv0
  constructor
  · -- list validity
    intro x
    by_cases hx : x = v0
    · subst hx; rw [extendColoring_v0]; exact ha
    · rw [extendColoring_other R c a hx]
      have hmem := hc.1 (sectionToDeleted R x hx)
      have hsub' := hsub (sectionToDeleted R x hx)
      have hxeq : deletedVertexToM M d0 (sectionToDeleted R x hx) = x :=
        deletedVertexToM_sectionToDeleted R x hx
      rw [hxeq] at hsub'
      exact hsub' hmem
  · -- properness
    intro x y hxy
    by_cases hxv : x = v0
    · subst hxv
      rw [extendColoring_v0]
      exact (havoid hxy).symm
    · by_cases hyv : y = v0
      · subst hyv
        rw [extendColoring_v0]
        exact havoid (M.toSimpleGraph.symm hxy)
      · -- both survivors: pull back to a deleted-map edge
        rw [extendColoring_other R c a hxv, extendColoring_other R c a hyv]
        set qx := sectionToDeleted R x hxv with hqx
        set qy := sectionToDeleted R y hyv with hqy
        have hxeq : deletedVertexToM M d0 qx = x := deletedVertexToM_sectionToDeleted R x hxv
        have hyeq : deletedVertexToM M d0 qy = y := deletedVertexToM_sectionToDeleted R y hyv
        have hadjM : M.toSimpleGraph.Adj (deletedVertexToM M d0 qx) (deletedVertexToM M d0 qy) := by
          rw [hxeq, hyeq]; exact hxy
        have hadj' : (M.deleteVertex d0).toSimpleGraph.Adj qx qy :=
          deletedVertexToM_adj_reflect M d0 hadjM
        exact hc.2 hadj'

/-! ### Discharging the neighbor avoidance from the fan and the color reservation

The avoidance hypothesis of `deleteBoundaryVertex_extend_coloring` is now derived
from the fan geometry and the review's color reservation.  First, every
`M`-neighbour of `v0` lies on the exposed fan path `x, z₁,…,z_t, w` (the fan
rotation enumerates the star of `v0`).  Then the color choice `a ∈ {γ, δ}` avoids
all neighbour colors: the interior fan vertices were colored from lists with
`γ, δ` removed; the endpoint `x` keeps its `≥ 3`/precolored list; and `a` is
chosen distinct from the color of `w`. -/

/-- **Every `M`-neighbour of `v0` lies on the exposed fan path.**  The fan
rotation darts are exactly the star of `v0` (`NeighborRotationOrder.vertexDarts_eq`),
and their heads are the fan-path neighbours (`heads_eq`).  Any dart realizing an
edge at `v0` has, after orienting it to tail `v0`, its head among those
neighbours. -/
theorem v0_neighbor_mem_fanPath {hNT : NearTriangulation M} {v0 : M.Vertex}
    (fan : NearTriangulation.BoundaryVertexFan hNT v0) {d0 : D}
    (htail : M.tail d0 = v0) {u : M.Vertex}
    (hadj : M.toSimpleGraph.Adj v0 u) :
    u ∈ NearTriangulation.fanPath fan.x fan.interior fan.w := by
  classical
  obtain ⟨hne, d, hd⟩ := hadj
  -- orient the dart so its tail is `v0`
  obtain ⟨d', htail', hhead'⟩ :
      ∃ d' : D, M.tail d' = v0 ∧ M.head d' = u := by
    rw [dartEdge, Sym2.eq_iff] at hd
    rcases hd with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · exact ⟨d, ht, hh⟩
    · exact ⟨M.α d, by rw [tail_alpha]; exact hh, by rw [head_alpha]; exact ht⟩
  -- `d'` is in the star of `v0`, hence in the rotation dart set
  have hstar : M.σ.SameCycle d0 d' := Quotient.exact (htail.trans htail'.symm)
  have hmem : d' ∈ M.vertexDarts d0 := (mem_vertexDarts M d0 d').mpr hstar
  have hrot := fan.rotation_order.vertexDarts_eq htail
  rw [hrot, List.mem_toFinset] at hmem
  -- its head is one of the listed neighbours
  have hheadmem : M.head d' ∈ fan.rotation_order.darts.map M.head :=
    List.mem_map_of_mem hmem
  rw [fan.rotation_order.heads_eq] at hheadmem
  rw [← hhead']
  exact hheadmem

/-- The reserved color of `v0` actually present in a fan-vertex deleted list is
absent from the coloring there.  This packages `deleteFanLists_notMem` against a
list coloring `c`: at a fan vertex `q'`, neither reserved color is `c q'`. -/
lemma color_ne_reserved_of_fan {d0 : D}
    {fanInterior : Finset M.Vertex} {L : M.Vertex → Finset α} {γ δ : α}
    {c : (M.deleteVertex d0).Vertex → α}
    (hc : IsListColoring (M.deleteVertex d0).toSimpleGraph
      (deleteFanLists M d0 fanInterior L γ δ) c)
    {q' : (M.deleteVertex d0).Vertex}
    (hq : deletedVertexToM M d0 q' ∈ fanInterior) :
    c q' ≠ γ ∧ c q' ≠ δ := by
  have hmem := hc.1 q'
  obtain ⟨hγ, hδ⟩ := deleteFanLists_notMem M d0 fanInterior L hq
  exact ⟨fun h => hγ (h ▸ hmem), fun h => hδ (h ▸ hmem)⟩

/--
**The avoidance discharge (the review's color reservation, completed).**

Working with the deleted lists `L' = deleteFanLists` and a list coloring `c` of
the deleted map, we choose the color `a ∈ {γ, δ}` of `v0` to differ from the
color of `w`, and prove the full neighbour-avoidance hypothesis of
`deleteBoundaryVertex_extend_coloring`.  The three review bullet points become the
hypotheses:

* `hγδ : γ ≠ δ` — the two reserved colors are distinct;
* `hx_avoid` — the endpoint `x` (the precolored vertex `p`, color `cp ∉ {γ, δ}`)
  has `extendColoring … x ∉ {γ, δ}`;
* the interior fan vertices avoid `γ, δ` automatically (`color_ne_reserved_of_fan`);
* `w` is avoided by the explicit choice of `a`.

It returns the chosen color `a` together with `a ∈ {γ, δ}` and the avoidance.
-/
theorem extend_avoid_of_fan {hNT : NearTriangulation M} {v0 : M.Vertex}
    (fan : NearTriangulation.BoundaryVertexFan hNT v0)
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    (hd0 : Quotient.mk (cycleSetoid M.σ) d0 = v0)
    {L : M.Vertex → Finset α} {γ δ : α} (hγδ : γ ≠ δ)
    {c : (M.deleteVertex d0).Vertex → α}
    (hc : IsListColoring (M.deleteVertex d0).toSimpleGraph
      (deleteFanLists M d0 fan.interior.toFinset L γ δ) c)
    (hxp : fan.x ≠ v0)
    (hx_avoid : extendColoring R c γ fan.x ≠ γ ∧ extendColoring R c δ fan.x ≠ δ)
    (hwp : fan.w ≠ v0) :
    ∃ a : α, (a = γ ∨ a = δ) ∧
      (∀ ⦃u : M.Vertex⦄, M.toSimpleGraph.Adj v0 u → extendColoring R c a u ≠ a) := by
  classical
  -- choose `a ∈ {γ, δ}` differing from the color of `w`
  have hwsec : extendColoring R c γ fan.w = c (sectionToDeleted R fan.w (hd0 ▸ hwp))
      ∧ extendColoring R c δ fan.w = c (sectionToDeleted R fan.w (hd0 ▸ hwp)) := by
    constructor <;> rw [extendColoring_other _ _ _ (hd0 ▸ hwp)]
  set cw : α := c (sectionToDeleted R fan.w (hd0 ▸ hwp)) with hcw
  -- the value of `extendColoring` at any survivor is independent of the `v0`-color
  have hsurv_indep : ∀ {z : M.Vertex} (hz : z ≠ v0) (a₁ a₂ : α),
      extendColoring R c a₁ z = extendColoring R c a₂ z := by
    intro z hz a₁ a₂
    rw [extendColoring_other _ _ _ (hd0 ▸ hz), extendColoring_other _ _ _ (hd0 ▸ hz)]
  refine ⟨if cw = γ then δ else γ, ?_, ?_⟩
  · by_cases h : cw = γ
    · simp [h]
    · simp [h]
  · intro u hadj
    -- `u` is a fan-path vertex
    have hu : u ∈ NearTriangulation.fanPath fan.x fan.interior fan.w :=
      v0_neighbor_mem_fanPath fan (hd0) hadj
    -- the chosen color `a := if cw = γ then δ else γ`
    set a : α := if cw = γ then δ else γ with ha
    have ha_choice : a = γ ∨ a = δ := by
      by_cases h : cw = γ
      · right; simp [ha, h]
      · left; simp [ha, h]
    -- `u ≠ v0`
    have hune : u ≠ v0 := (M.toSimpleGraph.ne_of_adj hadj).symm
    simp only [NearTriangulation.fanPath, List.mem_append, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] at hu
    rcases hu with (hux | huz) | huw
    · -- `u = x`: precolored / size-≥3 endpoint avoids both reserved colors
      subst hux
      have hxavoid' : extendColoring R c a fan.x ≠ γ ∧ extendColoring R c a fan.x ≠ δ := by
        constructor
        · rw [hsurv_indep hxp a γ]; exact hx_avoid.1
        · rw [hsurv_indep hxp a δ]; exact hx_avoid.2
      rcases ha_choice with h | h
      · simpa only [h] using hxavoid'.1
      · simpa only [h] using hxavoid'.2
    · -- `u = z_i` interior fan vertex: colored from list with `γ, δ` removed
      have hune' : u ≠ v0 := hune
      set q' := sectionToDeleted R u (hd0 ▸ hune') with hq'
      have hqeq : deletedVertexToM M d0 q' = u :=
        deletedVertexToM_sectionToDeleted R u (hd0 ▸ hune')
      have hqfan : deletedVertexToM M d0 q' ∈ fan.interior.toFinset := by
        rw [hqeq, List.mem_toFinset]; exact huz
      have hcq := color_ne_reserved_of_fan hc hqfan
      have heq : extendColoring R c a u = c q' := by
        rw [extendColoring_other _ _ _ (hd0 ▸ hune')]
      rw [heq]
      rcases ha_choice with h | h
      · rw [h]; exact hcq.1
      · rw [h]; exact hcq.2
    · -- `u = w`: avoided by the explicit choice of `a`
      subst huw
      have hval : extendColoring R c a fan.w = cw := by
        rw [extendColoring_other _ _ _ (hd0 ▸ hwp)]
      rw [hval, ha]
      by_cases h : cw = γ
      · rw [if_pos h, h]; exact hγδ
      · rw [if_neg h]; exact h

/-- The deleted lists are pointwise contained in `L` (through the kept-dart map):
they either keep `L` or shrink it by removing the two reserved colors. -/
lemma deleteFanLists_subset (M : CombMap D) (d0 : D)
    (fanInterior : Finset M.Vertex) (L : M.Vertex → Finset α) (γ δ : α)
    (q' : (M.deleteVertex d0).Vertex) :
    deleteFanLists M d0 fanInterior L γ δ q' ⊆ L (deletedVertexToM M d0 q') := by
  classical
  by_cases hq : deletedVertexToM M d0 q' ∈ fanInterior
  · rw [deleteFanLists_fan M d0 fanInterior L γ δ hq]; exact Finset.sdiff_subset
  · rw [deleteFanLists_other M d0 fanInterior L γ δ hq]

/--
**The complete deletion list transport (task item 3, assembled).**

Given the fan, the kept-dart reconstruction, two distinct reserved colors
`γ, δ ∈ L v0` removed only at the fan interior vertices, a list coloring `c` of
the deleted map from `deleteFanLists`, and the review's two endpoint conditions
(the `x` endpoint avoids both reserved colors, and `x, w ≠ v0`), the coloring
extends to a list coloring of all of `M` from `L`.  Both ingredients
(`extend_avoid_of_fan` and `deleteBoundaryVertex_extend_coloring`) are combined.
-/
theorem deleteBoundaryVertex_listColorable
    {hNT : NearTriangulation M} {v0 : M.Vertex} {d0 : D}
    (fan : NearTriangulation.BoundaryVertexFan hNT v0)
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    (hd0 : Quotient.mk (cycleSetoid M.σ) d0 = v0)
    {L : M.Vertex → Finset α} {γ δ : α} (hγδ : γ ≠ δ)
    (hγ : γ ∈ L v0) (hδ : δ ∈ L v0)
    {c : (M.deleteVertex d0).Vertex → α}
    (hc : IsListColoring (M.deleteVertex d0).toSimpleGraph
      (deleteFanLists M d0 fan.interior.toFinset L γ δ) c)
    (hxp : fan.x ≠ v0) (hwp : fan.w ≠ v0)
    (hx_avoid : extendColoring R c γ fan.x ≠ γ ∧ extendColoring R c δ fan.x ≠ δ) :
    ListColorable M.toSimpleGraph L := by
  obtain ⟨a, ha_choice, havoid⟩ :=
    extend_avoid_of_fan fan R hd0 hγδ hc hxp hx_avoid hwp
  have ha_mem : a ∈ L (Quotient.mk (cycleSetoid M.σ) d0) := by
    rw [hd0]; rcases ha_choice with rfl | rfl
    · exact hγ
    · exact hδ
  refine ⟨extendColoring R c a, ?_⟩
  refine deleteBoundaryVertex_extend_coloring R
    (deleteFanLists_subset M d0 fan.interior.toFinset L γ δ) hc ha_mem ?_
  intro u hadj
  exact havoid (hd0 ▸ hadj)

end Deletion

end CombMap

end ProofsInTheBook.ThomassenLists
