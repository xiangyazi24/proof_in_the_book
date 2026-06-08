/-
Block decomposition primitives for finite simple graphs.

This file deliberately imports only Mathlib.  Mathlib currently has
connected components for `SimpleGraph`, but not cut vertices, blocks, or
block-cut trees, so this file builds the interface needed by the Chapter 35
five-color bridge directly on plain `SimpleGraph`.

We use the rooted-enumeration form of the block-cut tree theorem, rather than
an explicit tree API.  This is the form needed for coloring: each new block
meets the union of the earlier blocks in exactly one root vertex.
-/
import Mathlib

namespace ProofsInTheBook.SimpleGraphBlocks

open Classical


variable {V α : Type*}

/-- Connectivity after deleting one vertex.  The remaining induced graph may
be empty; therefore this uses `Preconnected`, not `Connected`. -/
def VertexDeletedPreconnected (G : SimpleGraph V) (x : V) : Prop :=
  (G.induce {y : V | y ≠ x}).Preconnected

/-- A cut vertex: deleting it destroys preconnectedness.  The ambient graph is
required to be connected so isolated vertices in disconnected graphs are not
classified as cuts. -/
def IsCutVertex (G : SimpleGraph V) (x : V) : Prop :=
  G.Connected ∧ ¬ VertexDeletedPreconnected G x

/--
Finite-graph 2-connectedness with the usual block convention that one-vertex
and one-edge induced graphs are allowed as degenerate blocks.  Formally, the
graph is nonempty and preconnected, and deleting any vertex leaves a
preconnected induced graph.
-/
def TwoConnected (G : SimpleGraph V) : Prop :=
  Nonempty V ∧ G.Preconnected ∧ ∀ x : V, VertexDeletedPreconnected G x

/--
The induced-set version of `TwoConnected`.  Since the deletion graph can be
empty, the deletion clause again uses `Preconnected`; singleton and edge
blocks are therefore included without a separate special case.
-/
def BlockCore (G : SimpleGraph V) (s : Set V) : Prop :=
  s.Nonempty ∧ (G.induce s).Preconnected ∧
    ∀ x, x ∈ s → (G.induce (s \ {x})).Preconnected

/-- A block is a maximal induced vertex set satisfying `BlockCore`. -/
def IsBlock (G : SimpleGraph V) (s : Set V) : Prop :=
  Maximal (BlockCore G) s

/-- The block-cut incidence relation between a block and a cut vertex. -/
def BlockCutIncidence (G : SimpleGraph V) (B : Set V) (x : V) : Prop :=
  IsBlock G B ∧ IsCutVertex G x ∧ x ∈ B

/-- The bipartite block-cut incidence graph. -/
def blockCutGraph (G : SimpleGraph V) : SimpleGraph ((Set V) ⊕ V) :=
  .fromRel fun a b =>
    match a, b with
    | Sum.inl B, Sum.inr x => BlockCutIncidence G B x
    | Sum.inr x, Sum.inl B => BlockCutIncidence G B x
    | _, _ => False

section Basic

theorem blockCore_nonempty {G : SimpleGraph V} {s : Set V}
    (h : BlockCore G s) : s.Nonempty :=
  h.1

theorem blockCore_preconnected {G : SimpleGraph V} {s : Set V}
    (h : BlockCore G s) : (G.induce s).Preconnected :=
  h.2.1

theorem blockCore_delete_preconnected_of_mem {G : SimpleGraph V} {s : Set V}
    (h : BlockCore G s) {x : V} (hx : x ∈ s) :
    (G.induce (s \ {x})).Preconnected :=
  h.2.2 x hx

theorem blockCore_delete_preconnected {G : SimpleGraph V} {s : Set V}
    (h : BlockCore G s) (x : V) :
    (G.induce (s \ {x})).Preconnected := by
  by_cases hx : x ∈ s
  · exact blockCore_delete_preconnected_of_mem h hx
  · have hs : s \ {x} = s := by
      ext y
      simp [hx]
    rw [hs]
    exact blockCore_preconnected h

theorem singleton_blockCore (G : SimpleGraph V) (x : V) :
    BlockCore G ({x} : Set V) := by
  refine ⟨⟨x, rfl⟩, ?_, ?_⟩
  · exact SimpleGraph.Preconnected.of_subsingleton
  · intro y hy
    haveI : Subsingleton ↑(({x} : Set V) \ {y}) := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have ha : a.1 = x := by simpa using a.2.1
      have hb : b.1 = x := by simpa using b.2.1
      exact ha.trans hb.symm
    exact SimpleGraph.Preconnected.of_subsingleton

theorem pair_blockCore_of_adj {G : SimpleGraph V} {x y : V} (hxy : G.Adj x y) :
    BlockCore G ({x, y} : Set V) := by
  refine ⟨⟨x, by simp⟩, ?_, ?_⟩
  · exact (SimpleGraph.induce_pair_connected_of_adj hxy).preconnected
  · intro z hz
    haveI : Subsingleton ↑(({x, y} : Set V) \ {z}) := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have ha : a.1 = x ∨ a.1 = y := by simpa using a.2.1
      have hb : b.1 = x ∨ b.1 = y := by simpa using b.2.1
      have hz' : z = x ∨ z = y := by simpa using hz
      rcases hz' with hzx | hzy
      · have hay : a.1 = y := by
          rcases ha with hax | hay
          · exfalso
            exact a.2.2 (by simp [hzx, hax])
          · exact hay
        have hby : b.1 = y := by
          rcases hb with hbx | hby
          · exfalso
            exact b.2.2 (by simp [hzx, hbx])
          · exact hby
        exact hay.trans hby.symm
      · have hax : a.1 = x := by
          rcases ha with hax | hay
          · exact hax
          · exfalso
            exact a.2.2 (by simp [hzy, hay])
        have hbx : b.1 = x := by
          rcases hb with hbx | hby
          · exact hbx
          · exfalso
            exact b.2.2 (by simp [hzy, hby])
        exact hax.trans hbx.symm
    exact SimpleGraph.Preconnected.of_subsingleton

theorem isBlock_blockCore {G : SimpleGraph V} {s : Set V}
    (h : IsBlock G s) : BlockCore G s :=
  h.1

end Basic

section Maximal

variable [Finite V]

/-- Every `BlockCore` set is contained in a maximal block. -/
theorem exists_isBlock_superset {G : SimpleGraph V} {s : Set V}
    (hs : BlockCore G s) : ∃ B : Set V, s ⊆ B ∧ IsBlock G B := by
  let candidates : Set (Set V) := {t | BlockCore G t ∧ s ⊆ t}
  have hcand_finite : candidates.Finite := Set.toFinite candidates
  have hcand_nonempty : candidates.Nonempty := ⟨s, hs, subset_rfl⟩
  obtain ⟨B, hBmax⟩ := hcand_finite.exists_maximal hcand_nonempty
  refine ⟨B, hBmax.prop.2, ?_⟩
  refine ⟨hBmax.prop.1, ?_⟩
  intro T hT hBT
  have hTcand : T ∈ candidates := ⟨hT, subset_trans hBmax.prop.2 hBT⟩
  exact hBmax.le_of_ge hTcand hBT

/-- Every vertex is contained in some block. -/
theorem exists_isBlock_mem (G : SimpleGraph V) (x : V) :
    ∃ B : Set V, IsBlock G B ∧ x ∈ B := by
  obtain ⟨B, hsub, hB⟩ := exists_isBlock_superset (G := G) (s := {x})
    (singleton_blockCore G x)
  exact ⟨B, hB, hsub rfl⟩

/-- The vertex set is covered by the blocks. -/
theorem blocks_cover (G : SimpleGraph V) :
    ∀ x : V, ∃ B : Set V, IsBlock G B ∧ x ∈ B :=
  exists_isBlock_mem G

end Maximal

section WholeBlock

/-- A two-connected graph has the whole vertex set as a block. -/
theorem isBlock_univ_of_twoConnected {G : SimpleGraph V} (hG : TwoConnected G) :
    IsBlock G Set.univ := by
  refine ⟨?_, ?_⟩
  · letI : Nonempty V := hG.1
    refine ⟨Set.univ_nonempty, ?_, ?_⟩
    · intro u v
      obtain ⟨p⟩ := hG.2.1 u.1 v.1
      exact ⟨p.induce Set.univ (by intro z hz; simp)⟩
    · intro x hx
      have hset : (Set.univ : Set V) \ {x} = {y : V | y ≠ x} := by
        ext y
        simp
      rw [hset]
      simpa [VertexDeletedPreconnected] using hG.2.2 x
  · intro s hs hsup x hx
    simp

/-- In a connected graph, absence of cut vertices is exactly the deletion
condition needed for `TwoConnected`. -/
theorem twoConnected_of_connected_of_no_cut {G : SimpleGraph V}
    (hG : G.Connected) (hcut : ∀ x : V, ¬ IsCutVertex G x) :
    TwoConnected G := by
  refine ⟨hG.nonempty, hG.preconnected, ?_⟩
  intro x
  by_contra hx
  exact hcut x ⟨hG, hx⟩

end WholeBlock

section DeletionSeparation

/-- The vertices of one connected component of `G - x`, viewed back in `V`. -/
def deleteComponentSet (G : SimpleGraph V) (x : V)
    (C : (G.induce {y : V | y ≠ x}).ConnectedComponent) : Set V :=
  {v | ∃ hv : v ≠ x, (⟨v, hv⟩ : {y : V // y ≠ x}) ∈ C.supp}

/-- A deleted component together with the deleted vertex. -/
def deleteComponentSide (G : SimpleGraph V) (x : V)
    (C : (G.induce {y : V | y ≠ x}).ConnectedComponent) : Set V :=
  {x} ∪ deleteComponentSet G x C

/-- The complementary side: all vertices not in the chosen component of `G - x`.
This includes `x`. -/
def deleteComponentOtherSide (G : SimpleGraph V) (x : V)
    (C : (G.induce {y : V | y ≠ x}).ConnectedComponent) : Set V :=
  (deleteComponentSet G x C)ᶜ

/-- If two vertices are not reachable after deleting `x`, then every walk
between them in the original graph visits `x`. -/
theorem mem_support_of_not_reachable_delete {G : SimpleGraph V} {x u v : V}
    (hu : u ≠ x) (hv : v ≠ x)
    (hnot : ¬ (G.induce {y : V | y ≠ x}).Reachable ⟨u, hu⟩ ⟨v, hv⟩)
    (p : G.Walk u v) :
    x ∈ p.support := by
  by_contra hx
  have hall : ∀ z, z ∈ p.support → z ∈ ({y : V | y ≠ x} : Set V) := by
    intro z hz hzx
    exact hx (hzx ▸ hz)
  exact hnot ⟨p.induce {y : V | y ≠ x} hall⟩

theorem deleteComponentSet_preconnected {G : SimpleGraph V} {x : V}
    (C : (G.induce {y : V | y ≠ x}).ConnectedComponent) :
    (G.induce (deleteComponentSet G x C)).Preconnected := by
  intro u v
  rcases u.2 with ⟨hu, huC⟩
  rcases v.2 with ⟨hv, hvC⟩
  let H : SimpleGraph {y : V // y ≠ x} := G.induce {y : V | y ≠ x}
  let φ : C.toSimpleGraph →g G.induce (deleteComponentSet G x C) :=
    { toFun := fun z =>
        ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
      map_rel' := by
        intro a b hab
        simpa [SimpleGraph.ConnectedComponent.toSimpleGraph, H] using hab }
  have hreach :
      C.toSimpleGraph.Reachable
        ⟨(⟨u.1, hu⟩ : {y : V // y ≠ x}), huC⟩
        ⟨(⟨v.1, hv⟩ : {y : V // y ≠ x}), hvC⟩ :=
    C.reachable_toSimpleGraph huC hvC
  simpa [φ] using hreach.map φ

theorem deleteComponentSet_subset_otherSide_of_ne {G : SimpleGraph V} {x : V}
    {C D : (G.induce {y : V | y ≠ x}).ConnectedComponent} (hDC : D ≠ C) :
    deleteComponentSet G x D ⊆ deleteComponentOtherSide G x C := by
  intro v hvD hvC
  rcases hvD with ⟨hv, hvDmem⟩
  rcases hvC with ⟨_, hvCmem⟩
  exact hDC (SimpleGraph.ConnectedComponent.eq_of_common_vertex hvDmem hvCmem)

/-- Every component of `G - x` in a connected graph has a neighbor of `x`. -/
theorem exists_adj_cut_delete_component {G : SimpleGraph V} (hG : G.Connected)
    (x : V) (C : (G.induce {y : V | y ≠ x}).ConnectedComponent) :
    ∃ y : {y : V // y ≠ x}, y ∈ C.supp ∧ G.Adj x y.1 := by
  classical
  obtain ⟨a, haC⟩ := C.nonempty_supp
  obtain ⟨p, hp⟩ := hG.exists_isPath x a.1
  have hxa : x ≠ a.1 := fun h => a.2 h.symm
  have hpne : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hxa
  have hx_notin_tail : x ∉ p.tail.support := by
    have hnodup : p.support.Nodup := hp.support_nodup
    have hnodup' : (x :: p.tail.support).Nodup := by
      simpa [SimpleGraph.Walk.cons_support_tail hpne] using hnodup
    exact (List.nodup_cons.mp hnodup').1
  have hsnd_ne : p.snd ≠ x := by
    intro hs
    exact hx_notin_tail (by simpa [hs] using p.tail.start_mem_support)
  have hall : ∀ w, w ∈ p.tail.support → w ∈ ({y : V | y ≠ x} : Set V) := by
    intro w hw hwx
    exact hx_notin_tail (hwx ▸ hw)
  have hreach :
      (G.induce {y : V | y ≠ x}).Reachable ⟨p.snd, hsnd_ne⟩ a :=
    ⟨p.tail.induce {y : V | y ≠ x} hall⟩
  have hsndC : (⟨p.snd, hsnd_ne⟩ : {y : V // y ≠ x}) ∈ C.supp := by
    change (G.induce {y : V | y ≠ x}).connectedComponentMk ⟨p.snd, hsnd_ne⟩ = C
    exact (SimpleGraph.ConnectedComponent.sound hreach).trans haC
  exact ⟨⟨p.snd, hsnd_ne⟩, hsndC, p.adj_snd hpne⟩

theorem deleteComponentSide_connected {G : SimpleGraph V} (hG : G.Connected)
    (x : V) (C : (G.induce {y : V | y ≠ x}).ConnectedComponent) :
    (G.induce (deleteComponentSide G x C)).Connected := by
  obtain ⟨y, hyC, hxy⟩ := exists_adj_cut_delete_component hG x C
  have hsingle : (G.induce ({x} : Set V)).Preconnected :=
    SimpleGraph.Preconnected.of_subsingleton
  have hcomp : (G.induce (deleteComponentSet G x C)).Preconnected :=
    deleteComponentSet_preconnected C
  have hySet : y.1 ∈ deleteComponentSet G x C := ⟨y.2, hyC⟩
  have hconn :
      (G.induce (({x} : Set V) ∪ deleteComponentSet G x C)).Connected :=
    SimpleGraph.connected_induce_union hsingle hcomp (by simp) hySet hxy
  simpa [deleteComponentSide] using hconn

theorem deleteComponentOtherSide_connected {G : SimpleGraph V} (hG : G.Connected)
    (x : V) (C : (G.induce {y : V | y ≠ x}).ConnectedComponent) :
    (G.induce (deleteComponentOtherSide G x C)).Connected := by
  classical
  let other := deleteComponentOtherSide G x C
  have hxOther : x ∈ other := by
    intro hxC
    rcases hxC with ⟨hx, -⟩
    exact hx rfl
  have reach_x :
      ∀ u : other,
        (G.induce other).Reachable u ⟨x, hxOther⟩ := by
    intro u
    by_cases hux : u.1 = x
    · have hu_eq : u = ⟨x, hxOther⟩ := Subtype.ext hux
      rw [hu_eq]
    · let H : SimpleGraph {y : V // y ≠ x} := G.induce {y : V | y ≠ x}
      let D : H.ConnectedComponent := H.connectedComponentMk ⟨u.1, hux⟩
      have hDne : D ≠ C := by
        intro hDC
        exact u.2 ⟨hux, by simpa [D, hDC]⟩
      obtain ⟨y, hyD, hxy⟩ := exists_adj_cut_delete_component hG x D
      have hsubset : deleteComponentSet G x D ⊆ other :=
        deleteComponentSet_subset_otherSide_of_ne (G := G) (x := x) hDne
      have huD : u.1 ∈ deleteComponentSet G x D := by
        refine ⟨hux, ?_⟩
        exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      have hyDset : y.1 ∈ deleteComponentSet G x D := ⟨y.2, hyD⟩
      have hyOther : y.1 ∈ other := hsubset hyDset
      have hreachD :
          (G.induce (deleteComponentSet G x D)).Reachable
            ⟨u.1, huD⟩ ⟨y.1, hyDset⟩ :=
        deleteComponentSet_preconnected D ⟨u.1, huD⟩ ⟨y.1, hyDset⟩
      have hreachOther :
          (G.induce other).Reachable u ⟨y.1, hyOther⟩ := by
        simpa [SimpleGraph.induceHomOfLE_apply] using
          hreachD.map (G.induceHomOfLE hsubset).toHom
      have hadjOther : (G.induce other).Adj ⟨y.1, hyOther⟩ ⟨x, hxOther⟩ := by
        simpa using hxy.symm
      exact hreachOther.trans hadjOther.reachable
  exact
    { preconnected := by
        intro u v
        exact (reach_x u).trans (reach_x v).symm
      nonempty := ⟨⟨x, hxOther⟩⟩ }

theorem deleteComponentSet_notMem_self {G : SimpleGraph V} {x : V}
    (C : (G.induce {y : V | y ≠ x}).ConnectedComponent) :
    x ∉ deleteComponentSet G x C := by
  intro hxC
  rcases hxC with ⟨hx, -⟩
  exact hx rfl

theorem deleteComponentSide_union_otherSide {G : SimpleGraph V} {x : V}
    (C : (G.induce {y : V | y ≠ x}).ConnectedComponent) :
    deleteComponentSide G x C ∪ deleteComponentOtherSide G x C = Set.univ := by
  ext v
  by_cases hv : v ∈ deleteComponentSet G x C
  · simp [deleteComponentSide, deleteComponentOtherSide, hv]
  · simp [deleteComponentSide, deleteComponentOtherSide, hv]

theorem deleteComponentSide_inter_otherSide {G : SimpleGraph V} {x : V}
    (C : (G.induce {y : V | y ≠ x}).ConnectedComponent) :
    deleteComponentSide G x C ∩ deleteComponentOtherSide G x C = ({x} : Set V) := by
  ext v
  constructor
  · intro hv
    rcases hv.1 with hvx | hvC
    · simpa using hvx
    · exact False.elim (hv.2 hvC)
  · intro hv
    subst hv
    exact ⟨Or.inl rfl, deleteComponentSet_notMem_self C⟩

theorem not_adj_deleteComponentSide_otherSide {G : SimpleGraph V} {x u v : V}
    {C : (G.induce {y : V | y ≠ x}).ConnectedComponent}
    (hu : u ∈ deleteComponentSide G x C) (hu_ne : u ≠ x)
    (hv : v ∈ deleteComponentOtherSide G x C) (hv_ne : v ≠ x) :
    ¬ G.Adj u v := by
  intro huv
  have huCset : u ∈ deleteComponentSet G x C := by
    rcases hu with hux | huC
    · exact False.elim (hu_ne hux)
    · exact huC
  rcases huCset with ⟨_, huC⟩
  have hAdjDel :
      (G.induce {y : V | y ≠ x}).Adj ⟨u, hu_ne⟩ ⟨v, hv_ne⟩ := by
    simpa using huv
  have hvC : (⟨v, hv_ne⟩ : {y : V // y ≠ x}) ∈ C.supp :=
    C.mem_supp_of_adj_mem_supp huC hAdjDel
  exact hv ⟨hv_ne, hvC⟩

theorem blockCore_subset_deleteComponentSide_of_mem_component {G : SimpleGraph V}
    {x : V} {C : (G.induce {y : V | y ≠ x}).ConnectedComponent}
    {A : Set V} (hA : BlockCore G A) {y : V}
    (hyA : y ∈ A) (hyComp : y ∈ deleteComponentSet G x C) :
    A ⊆ deleteComponentSide G x C := by
  rcases hyComp with ⟨hy_ne, hyC⟩
  intro z hzA
  by_contra hzSide
  have hzOther : z ∈ deleteComponentOtherSide G x C := by
    have hunion := deleteComponentSide_union_otherSide (G := G) (x := x) C
    have : z ∈ deleteComponentSide G x C ∪ deleteComponentOtherSide G x C := by
      simp [hunion]
    exact this.resolve_left hzSide
  have hz_ne : z ≠ x := by
    intro hzx
    exact hzSide (by simp [deleteComponentSide, hzx])
  have hreachA :
      (G.induce (A \ {x})).Reachable
        ⟨y, hyA, by simpa using hy_ne⟩
        ⟨z, hzA, by simpa using hz_ne⟩ :=
    blockCore_delete_preconnected hA x
      ⟨y, hyA, by simpa using hy_ne⟩
      ⟨z, hzA, by simpa using hz_ne⟩
  have hsubset : A \ {x} ⊆ ({v : V | v ≠ x} : Set V) := by
    intro v hv
    exact hv.2
  have hreachDel :
      (G.induce {v : V | v ≠ x}).Reachable
        ⟨y, hy_ne⟩ ⟨z, hz_ne⟩ := by
    simpa [SimpleGraph.induceHomOfLE_apply] using
      hreachA.map (G.induceHomOfLE hsubset).toHom
  have hzC : (⟨z, hz_ne⟩ : {v : V // v ≠ x}) ∈ C.supp := by
    change (G.induce {v : V | v ≠ x}).connectedComponentMk ⟨z, hz_ne⟩ = C
    change (G.induce {v : V | v ≠ x}).connectedComponentMk ⟨y, hy_ne⟩ = C at hyC
    exact (SimpleGraph.ConnectedComponent.sound hreachDel).symm.trans hyC
  exact hzOther ⟨hz_ne, hzC⟩

theorem blockCore_subset_deleteComponentOtherSide_of_mem {G : SimpleGraph V}
    {x : V} {C : (G.induce {y : V | y ≠ x}).ConnectedComponent}
    {A : Set V} (hA : BlockCore G A) {y : V}
    (hyA : y ∈ A) (hyOther : y ∈ deleteComponentOtherSide G x C) (hy_ne : y ≠ x) :
    A ⊆ deleteComponentOtherSide G x C := by
  let H : SimpleGraph {v : V // v ≠ x} := G.induce {v : V | v ≠ x}
  let D : H.ConnectedComponent := H.connectedComponentMk ⟨y, hy_ne⟩
  have hDne : D ≠ C := by
    intro hDC
    exact hyOther ⟨hy_ne, by simpa [D, H, hDC]⟩
  intro z hzA
  by_contra hzOther
  have hzCset : z ∈ deleteComponentSet G x C := by
    simpa [deleteComponentOtherSide] using hzOther
  rcases hzCset with ⟨hz_ne, hzC⟩
  have hreachA :
      (G.induce (A \ {x})).Reachable
        ⟨y, hyA, by simpa using hy_ne⟩
        ⟨z, hzA, by simpa using hz_ne⟩ :=
    blockCore_delete_preconnected hA x
      ⟨y, hyA, by simpa using hy_ne⟩
      ⟨z, hzA, by simpa using hz_ne⟩
  have hsubset : A \ {x} ⊆ ({v : V | v ≠ x} : Set V) := by
    intro v hv
    exact hv.2
  have hreachDel :
      (G.induce {v : V | v ≠ x}).Reachable
        ⟨y, hy_ne⟩ ⟨z, hz_ne⟩ := by
    simpa [SimpleGraph.induceHomOfLE_apply] using
      hreachA.map (G.induceHomOfLE hsubset).toHom
  have hzD : (⟨z, hz_ne⟩ : {v : V // v ≠ x}) ∈ D.supp := by
    change H.connectedComponentMk ⟨z, hz_ne⟩ = D
    exact (SimpleGraph.ConnectedComponent.sound hreachDel).symm
  have hCD : C = D := SimpleGraph.ConnectedComponent.eq_of_common_vertex hzC hzD
  exact hDne hCD.symm

end DeletionSeparation

section InducedBlocks

def subtypeImage {s : Set V} (B : Set s) : Set V :=
  Subtype.val '' B

private def induceBlockImageHom {G : SimpleGraph V} {s : Set V} {B : Set s} :
    (G.induce s).induce B →g G.induce (subtypeImage B) where
  toFun v := ⟨v.1.1, ⟨v.1, v.2, rfl⟩⟩
  map_rel' := by
    intro u v huv
    simpa [subtypeImage] using huv

private def induceBlockDeleteImageHom {G : SimpleGraph V} {s : Set V} {B : Set s}
    {x : s} :
    (G.induce s).induce (B \ {x}) →g
      G.induce (subtypeImage B \ {x.1}) where
  toFun v := ⟨v.1.1, ⟨⟨v.1, v.2.1, rfl⟩, by
    intro hx
    exact v.2.2 (Subtype.ext hx)⟩⟩
  map_rel' := by
    intro u v huv
    simpa [subtypeImage] using huv

private def blockCoreRestrictHom {G : SimpleGraph V} {s A : Set V} (hsub : A ⊆ s) :
    G.induce A →g (G.induce s).induce {v : s | v.1 ∈ A} where
  toFun v := ⟨⟨v.1, hsub v.2⟩, v.2⟩
  map_rel' := by
    intro u v huv
    simpa using huv

private def blockCoreRestrictDeleteHom {G : SimpleGraph V} {s A : Set V}
    (hsub : A ⊆ s) (x : s) :
    G.induce (A \ {x.1}) →g
      (G.induce s).induce ({v : s | v.1 ∈ A} \ {x}) where
  toFun v := ⟨⟨v.1, hsub v.2.1⟩, v.2.1, by
    intro hx
    exact v.2.2 (by simpa using congr_arg Subtype.val hx)⟩
  map_rel' := by
    intro u v huv
    simpa using huv

theorem blockCore_induce_of_subset {G : SimpleGraph V} {s A : Set V}
    (hA : BlockCore G A) (hsub : A ⊆ s) :
    BlockCore (G.induce s) {v : s | v.1 ∈ A} := by
  refine ⟨?_, ?_, ?_⟩
  · rcases hA.1 with ⟨v, hv⟩
    exact ⟨⟨v, hsub hv⟩, hv⟩
  · intro u v
    have hreach : (G.induce A).Reachable ⟨u.1.1, u.2⟩ ⟨v.1.1, v.2⟩ :=
      hA.2.1 ⟨u.1.1, u.2⟩ ⟨v.1.1, v.2⟩
    simpa [blockCoreRestrictHom] using
      hreach.map (blockCoreRestrictHom (G := G) (s := s) (A := A) hsub)
  · intro x hx u v
    have hreach :
        (G.induce (A \ {x.1})).Reachable
          ⟨u.1.1, u.2.1, by
            intro hux
            exact u.2.2 (Subtype.ext hux)⟩
          ⟨v.1.1, v.2.1, by
            intro hvx
            exact v.2.2 (Subtype.ext hvx)⟩ :=
      hA.2.2 x.1 hx
        ⟨u.1.1, u.2.1, by
          intro hux
          exact u.2.2 (Subtype.ext hux)⟩
        ⟨v.1.1, v.2.1, by
          intro hvx
          exact v.2.2 (Subtype.ext hvx)⟩
    simpa [blockCoreRestrictDeleteHom] using
      hreach.map (blockCoreRestrictDeleteHom (G := G) (s := s) (A := A) hsub x)

theorem blockCore_image_of_induce {G : SimpleGraph V} {s : Set V} {B : Set s}
    (hB : BlockCore (G.induce s) B) : BlockCore G (subtypeImage B) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases hB.1 with ⟨v, hv⟩
    exact ⟨v.1, ⟨v, hv, rfl⟩⟩
  · rintro ⟨u, huimg⟩ ⟨v, hvimg⟩
    rcases huimg with ⟨u', hu'B, rfl⟩
    rcases hvimg with ⟨v', hv'B, rfl⟩
    have hreach :
        ((G.induce s).induce B).Reachable ⟨u', hu'B⟩ ⟨v', hv'B⟩ :=
      hB.2.1 ⟨u', hu'B⟩ ⟨v', hv'B⟩
    simpa [induceBlockImageHom] using hreach.map (induceBlockImageHom (G := G) (s := s) (B := B))
  · intro x hx
    rcases hx with ⟨x', hx'B, rfl⟩
    rintro ⟨u, huimg, hu_ne_global⟩ ⟨v, hvimg, hv_ne_global⟩
    rcases huimg with ⟨u', hu'B, rfl⟩
    rcases hvimg with ⟨v', hv'B, rfl⟩
    have hu_ne : u' ≠ x' := by
      intro hux
      exact hu_ne_global (by simp [hux])
    have hv_ne : v' ≠ x' := by
      intro hvx
      exact hv_ne_global (by simp [hvx])
    have hreach :
        ((G.induce s).induce (B \ {x'})).Reachable
          ⟨u', hu'B, by simpa using hu_ne⟩
          ⟨v', hv'B, by simpa using hv_ne⟩ :=
      hB.2.2 x' hx'B
        ⟨u', hu'B, by simpa using hu_ne⟩
        ⟨v', hv'B, by simpa using hv_ne⟩
    have hmapped :=
      hreach.map (induceBlockDeleteImageHom (G := G) (s := s) (B := B) (x := x'))
    simpa [induceBlockDeleteImageHom] using hmapped

theorem isBlock_induce_deleteComponentSide_meets_component {G : SimpleGraph V}
    (hG : G.Connected) {x : V}
    (C : (G.induce {y : V | y ≠ x}).ConnectedComponent)
    {B : Set (deleteComponentSide G x C)}
    (hB : IsBlock (G.induce (deleteComponentSide G x C)) B) :
    ∃ y : V, y ∈ subtypeImage B ∧ y ∈ deleteComponentSet G x C := by
  classical
  by_cases h : ∃ y : V, y ∈ subtypeImage B ∧ y ∈ deleteComponentSet G x C
  · exact h
  push Not at h
  have hall_x : ∀ b : deleteComponentSide G x C, b ∈ B → b.1 = x := by
    intro b hb
    rcases b.2 with hbx | hbComp
    · exact hbx
    · exact False.elim (h b.1 ⟨b, hb, rfl⟩ hbComp)
  obtain ⟨y, hyC, hxy⟩ := exists_adj_cut_delete_component hG x C
  let xs : deleteComponentSide G x C := ⟨x, by simp [deleteComponentSide]⟩
  let ys : deleteComponentSide G x C := ⟨y.1, Or.inr ⟨y.2, hyC⟩⟩
  have hAdj : (G.induce (deleteComponentSide G x C)).Adj xs ys := by
    simpa [xs, ys] using hxy
  have hpair : BlockCore (G.induce (deleteComponentSide G x C)) ({xs, ys} : Set _) :=
    pair_blockCore_of_adj hAdj
  have hBsubset : B ⊆ ({xs, ys} : Set _) := by
    intro b hb
    left
    exact Subtype.ext (hall_x b hb)
  have hyB : ys ∈ B := hB.le_of_ge hpair hBsubset (by simp [ys])
  exact ⟨y.1, ⟨ys, hyB, rfl⟩, ⟨y.2, hyC⟩⟩

theorem isBlock_image_of_induce_deleteComponentSide {G : SimpleGraph V}
    (hG : G.Connected) {x : V}
    (C : (G.induce {y : V | y ≠ x}).ConnectedComponent)
    {B : Set (deleteComponentSide G x C)}
    (hB : IsBlock (G.induce (deleteComponentSide G x C)) B) :
    IsBlock G (subtypeImage B) := by
  refine ⟨blockCore_image_of_induce hB.1, ?_⟩
  intro A hA hBA z hzA
  obtain ⟨y, hyBimg, hyComp⟩ :=
    isBlock_induce_deleteComponentSide_meets_component hG C hB
  have hyA : y ∈ A := hBA hyBimg
  have hAside : A ⊆ deleteComponentSide G x C :=
    blockCore_subset_deleteComponentSide_of_mem_component hA hyA hyComp
  let A' : Set (deleteComponentSide G x C) := {v | v.1 ∈ A}
  have hA' : BlockCore (G.induce (deleteComponentSide G x C)) A' :=
    blockCore_induce_of_subset hA hAside
  have hBsubA' : B ⊆ A' := by
    intro b hb
    exact hBA ⟨b, hb, rfl⟩
  have hA'subB : A' ⊆ B := hB.le_of_ge hA' hBsubA'
  have hzSide : z ∈ deleteComponentSide G x C := hAside hzA
  exact ⟨⟨z, hzSide⟩, hA'subB hzA, rfl⟩

theorem isBlock_induce_deleteComponentOtherSide_meets_noncut {G : SimpleGraph V}
    (hG : G.Connected) {x : V}
    (C : (G.induce {y : V | y ≠ x}).ConnectedComponent)
    (hother : ∃ D : (G.induce {y : V | y ≠ x}).ConnectedComponent, D ≠ C)
    {B : Set (deleteComponentOtherSide G x C)}
    (hB : IsBlock (G.induce (deleteComponentOtherSide G x C)) B) :
    ∃ y : V, y ∈ subtypeImage B ∧ y ∈ deleteComponentOtherSide G x C ∧ y ≠ x := by
  classical
  by_cases h :
      ∃ y : V, y ∈ subtypeImage B ∧ y ∈ deleteComponentOtherSide G x C ∧ y ≠ x
  · exact h
  push Not at h
  have hall_x : ∀ b : deleteComponentOtherSide G x C, b ∈ B → b.1 = x := by
    intro b hb
    exact h b.1 ⟨b, hb, rfl⟩ b.2
  obtain ⟨D, hDne⟩ := hother
  obtain ⟨y, hyD, hxy⟩ := exists_adj_cut_delete_component hG x D
  have hsubset : deleteComponentSet G x D ⊆ deleteComponentOtherSide G x C :=
    deleteComponentSet_subset_otherSide_of_ne (G := G) (x := x) hDne
  let xs : deleteComponentOtherSide G x C :=
    ⟨x, deleteComponentSet_notMem_self C⟩
  let ys : deleteComponentOtherSide G x C :=
    ⟨y.1, hsubset ⟨y.2, hyD⟩⟩
  have hAdj : (G.induce (deleteComponentOtherSide G x C)).Adj xs ys := by
    simpa [xs, ys] using hxy
  have hpair :
      BlockCore (G.induce (deleteComponentOtherSide G x C)) ({xs, ys} : Set _) :=
    pair_blockCore_of_adj hAdj
  have hBsubset : B ⊆ ({xs, ys} : Set _) := by
    intro b hb
    left
    exact Subtype.ext (hall_x b hb)
  have hyB : ys ∈ B := hB.le_of_ge hpair hBsubset (by simp [ys])
  exact ⟨y.1, ⟨ys, hyB, rfl⟩, ys.2, y.2⟩

theorem isBlock_image_of_induce_deleteComponentOtherSide {G : SimpleGraph V}
    (hG : G.Connected) {x : V}
    (C : (G.induce {y : V | y ≠ x}).ConnectedComponent)
    (hother : ∃ D : (G.induce {y : V | y ≠ x}).ConnectedComponent, D ≠ C)
    {B : Set (deleteComponentOtherSide G x C)}
    (hB : IsBlock (G.induce (deleteComponentOtherSide G x C)) B) :
    IsBlock G (subtypeImage B) := by
  refine ⟨blockCore_image_of_induce hB.1, ?_⟩
  intro A hA hBA z hzA
  obtain ⟨y, hyBimg, hyOther, hy_ne⟩ :=
    isBlock_induce_deleteComponentOtherSide_meets_noncut hG C hother hB
  have hyA : y ∈ A := hBA hyBimg
  have hAother : A ⊆ deleteComponentOtherSide G x C :=
    blockCore_subset_deleteComponentOtherSide_of_mem hA hyA hyOther hy_ne
  let A' : Set (deleteComponentOtherSide G x C) := {v | v.1 ∈ A}
  have hA' : BlockCore (G.induce (deleteComponentOtherSide G x C)) A' :=
    blockCore_induce_of_subset hA hAother
  have hBsubA' : B ⊆ A' := by
    intro b hb
    exact hBA ⟨b, hb, rfl⟩
  have hA'subB : A' ⊆ B := hB.le_of_ge hA' hBsubA'
  have hzOther : z ∈ deleteComponentOtherSide G x C := hAother hzA
  exact ⟨⟨z, hzOther⟩, hA'subB hzA, rfl⟩

end InducedBlocks

section Intersections

private theorem blockCore_union_of_two_common {G : SimpleGraph V} {s t : Set V}
    (hs : BlockCore G s) (ht : BlockCore G t)
    {a b : V} (has : a ∈ s) (hat : a ∈ t) (hbs : b ∈ s) (hbt : b ∈ t)
    (hab : a ≠ b) : BlockCore G (s ∪ t) := by
  refine ⟨⟨a, Or.inl has⟩, ?_, ?_⟩
  · exact (SimpleGraph.induce_union_connected (blockCore_preconnected hs)
      (blockCore_preconnected ht) ⟨a, has, hat⟩).preconnected
  · intro x hx
    have hsx : (G.induce (s \ {x})).Preconnected :=
      blockCore_delete_preconnected hs x
    have htx : (G.induce (t \ {x})).Preconnected :=
      blockCore_delete_preconnected ht x
    have hInter : ((s \ {x}) ∩ (t \ {x})).Nonempty := by
      by_cases hxa : x = a
      · refine ⟨b, ?_, ?_⟩
        · exact ⟨hbs, by simpa [hxa] using hab.symm⟩
        · exact ⟨hbt, by simpa [hxa] using hab.symm⟩
      · refine ⟨a, ?_, ?_⟩
        · exact ⟨has, by simpa [eq_comm] using hxa⟩
        · exact ⟨hat, by simpa [eq_comm] using hxa⟩
    have hconn : (G.induce ((s \ {x}) ∪ (t \ {x}))).Connected :=
      SimpleGraph.induce_union_connected hsx htx hInter
    have hset : (s ∪ t) \ {x} = (s \ {x}) ∪ (t \ {x}) := by
      ext y
      simp only [Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact hconn.preconnected

/-- If two blocks share two distinct vertices, maximality forces them to be equal. -/
theorem IsBlock.eq_of_two_common {G : SimpleGraph V} {s t : Set V}
    (hs : IsBlock G s) (ht : IsBlock G t)
    {a b : V} (has : a ∈ s) (hat : a ∈ t) (hbs : b ∈ s) (hbt : b ∈ t)
    (hab : a ≠ b) : s = t := by
  have hcore : BlockCore G (s ∪ t) :=
    blockCore_union_of_two_common (isBlock_blockCore hs) (isBlock_blockCore ht)
      has hat hbs hbt hab
  have hsu : s ∪ t ⊆ s := hs.le_of_ge hcore (by intro x hx; exact Or.inl hx)
  have htu : s ∪ t ⊆ t := ht.le_of_ge hcore (by intro x hx; exact Or.inr hx)
  apply le_antisymm
  · intro x hx
    exact htu (Or.inl hx)
  · intro x hx
    exact hsu (Or.inr hx)

/-- Distinct blocks have subsingleton intersection. -/
theorem IsBlock.inter_subsingleton {G : SimpleGraph V} {s t : Set V}
    (hs : IsBlock G s) (ht : IsBlock G t) (hst : s ≠ t) :
    (s ∩ t).Subsingleton := by
  intro a ha b hb
  by_contra hab
  exact hst (hs.eq_of_two_common ht ha.1 ha.2 hb.1 hb.2 hab)

/-- Cardinal form: two distinct blocks share at most one vertex. -/
theorem IsBlock.encard_inter_le_one {G : SimpleGraph V} {s t : Set V}
    (hs : IsBlock G s) (ht : IsBlock G t) (hst : s ≠ t) :
    (s ∩ t).encard ≤ 1 := by
  rw [Set.encard_le_one_iff_subsingleton]
  exact hs.inter_subsingleton ht hst

end Intersections

section RootedEnumeration

variable (G : SimpleGraph V)

/--
A rooted block enumeration is the rooted-induction replacement for the
block-cut tree.  `blocks i` is the `i`th block, every vertex and every edge is
covered by some block, and every non-root block meets the union of the
previous blocks exactly in its root vertex.
-/
structure RootedBlockEnumeration where
  k : ℕ
  blocks : Fin k → Set V
  roots : Fin k → V
  isBlock : ∀ i, IsBlock G (blocks i)
  vertex_cover : ∀ v : V, ∃ i, v ∈ blocks i
  edge_cover : ∀ ⦃u v : V⦄, G.Adj u v → ∃ i, u ∈ blocks i ∧ v ∈ blocks i
  root_mem : ∀ (i : Fin k), i.1 ≠ 0 → roots i ∈ blocks i
  prev_mem : ∀ (i : Fin k), i.1 ≠ 0 →
    ∃ j : Fin k, j.1 < i.1 ∧ roots i ∈ blocks j
  meet_prev : ∀ (i : Fin k), i.1 ≠ 0 → ∀ v : V,
    v ∈ blocks i →
      ((∃ j : Fin k, j.1 < i.1 ∧ v ∈ blocks j) ↔ v = roots i)

namespace RootedBlockEnumeration

variable {G}

/-- The enumeration starts at a block containing the chosen root vertex. -/
def StartsAt (E : RootedBlockEnumeration G) (r : V) : Prop :=
  ∃ i : Fin E.k, i.1 = 0 ∧ r ∈ E.blocks i

def unionUpTo (E : RootedBlockEnumeration G) (n : ℕ) : Set V :=
  {v | ∃ i : Fin E.k, i.1 < n ∧ v ∈ E.blocks i}

theorem root_in_unionUpTo {E : RootedBlockEnumeration G} {i : Fin E.k}
    (hi : i.1 ≠ 0) : E.roots i ∈ E.unionUpTo i.1 := by
  obtain ⟨j, hji, hj⟩ := E.prev_mem i hi
  exact ⟨j, hji, hj⟩

theorem block_meet_unionUpTo {E : RootedBlockEnumeration G} {i : Fin E.k}
    (hi : i.1 ≠ 0) {v : V} :
    v ∈ E.blocks i → (v ∈ E.unionUpTo i.1 ↔ v = E.roots i) := by
  intro hv
  exact E.meet_prev i hi v hv

end RootedBlockEnumeration

/-- The one-block rooted enumeration. -/
theorem exists_rootedBlockEnumeration_one {G : SimpleGraph V} (r : V)
    (hB : IsBlock G Set.univ) :
    ∃ E : RootedBlockEnumeration G, E.StartsAt r := by
  let E : RootedBlockEnumeration G :=
    { k := 1
      blocks := fun _ => Set.univ
      roots := fun _ => r
      isBlock := fun _ => hB
      vertex_cover := by
        intro v
        exact ⟨⟨0, by decide⟩, by simp⟩
      edge_cover := by
        intro u v huv
        exact ⟨⟨0, by decide⟩, by simp⟩
      root_mem := by
        intro i hi
        omega
      prev_mem := by
        intro i hi
        omega
      meet_prev := by
        intro i hi
        omega }
  refine ⟨E, ?_⟩
  change ∃ i : Fin 1, i.1 = 0 ∧ r ∈ (Set.univ : Set V)
  exact ⟨⟨0, by decide⟩, rfl, by simp⟩

/-- The rooted enumeration in the no-cut case. -/
theorem exists_rootedBlockEnumeration_of_connected_of_no_cut
    {G : SimpleGraph V} [Finite V] (hG : G.Connected)
    (hcut : ∀ x : V, ¬ IsCutVertex G x) (r : V) :
    ∃ E : RootedBlockEnumeration G, E.StartsAt r :=
  exists_rootedBlockEnumeration_one r
    (isBlock_univ_of_twoConnected (twoConnected_of_connected_of_no_cut hG hcut))

theorem mem_subtypeImage_iff {s : Set V} (B : Set s) (v : V) :
    v ∈ subtypeImage B ↔ ∃ h : v ∈ s, (⟨v, h⟩ : s) ∈ B := by
  constructor
  · rintro ⟨⟨w, hw⟩, hwB, rfl⟩
    exact ⟨hw, hwB⟩
  · rintro ⟨h, hB⟩
    exact ⟨⟨v, h⟩, hB, rfl⟩

/--
Concatenation of two rooted block enumerations along a single shared vertex `x`.
The graph splits into two induced sides `S` and `T` that cover everything, meet
exactly in `x`, and have no edge crossing between `S \ {x}` and `T \ {x}`.  The
`S`-enumeration is laid down first (so its start vertex `r` becomes the global
start), then the `T`-enumeration whose first block contains `x`; that first
`T`-block becomes the unique non-root block meeting the union of earlier blocks
exactly at `x`.
-/
theorem concat_rootedBlockEnumeration {G : SimpleGraph V} {S T : Set V} {x : V}
    (hcover : S ∪ T = Set.univ) (hxS : x ∈ S) (hxT : x ∈ T)
    (hinter : S ∩ T = ({x} : Set V))
    (hcross : ∀ u v : V, u ∈ S → u ≠ x → v ∈ T → v ≠ x → ¬ G.Adj u v)
    (liftS : ∀ B : Set S, IsBlock (G.induce S) B → IsBlock G (subtypeImage B))
    (liftT : ∀ B : Set T, IsBlock (G.induce T) B → IsBlock G (subtypeImage B))
    (Es : RootedBlockEnumeration (G.induce S))
    (Et : RootedBlockEnumeration (G.induce T))
    (hstart : Et.StartsAt ⟨x, hxT⟩)
    {r : V} (hrS : r ∈ S) (hr0 : Es.StartsAt ⟨r, hrS⟩) :
    ∃ E : RootedBlockEnumeration G, E.StartsAt r := by
  classical
  -- Membership of `x` in the very first `T`-block.
  obtain ⟨t0, ht0val, ht0mem⟩ := hstart
  -- `x` is the only vertex shared by the two sides.
  have hshared : ∀ v : V, v ∈ S → v ∈ T → v = x := by
    intro v hvS hvT
    have : v ∈ S ∩ T := ⟨hvS, hvT⟩
    rw [hinter] at this
    simpa using this
  -- The global blocks: `S`-images first, then `T`-images.
  let blocks : Fin (Es.k + Et.k) → Set V :=
    Fin.addCases (fun i => subtypeImage (Es.blocks i))
      (fun j => subtypeImage (Et.blocks j))
  let roots : Fin (Es.k + Et.k) → V :=
    Fin.addCases (fun i => (Es.roots i).1)
      (fun j => if j.1 = 0 then x else (Et.roots j).1)
  have blocks_castAdd : ∀ i : Fin Es.k,
      blocks (Fin.castAdd Et.k i) = subtypeImage (Es.blocks i) :=
    fun i => Fin.addCases_left (n := Et.k) i
  have blocks_natAdd : ∀ j : Fin Et.k,
      blocks (Fin.natAdd Es.k j) = subtypeImage (Et.blocks j) :=
    fun j => Fin.addCases_right (m := Es.k) j
  have roots_castAdd : ∀ i : Fin Es.k,
      roots (Fin.castAdd Et.k i) = (Es.roots i).1 :=
    fun i => Fin.addCases_left (n := Et.k) i
  have roots_natAdd : ∀ j : Fin Et.k,
      roots (Fin.natAdd Es.k j) = if j.1 = 0 then x else (Et.roots j).1 :=
    fun j => Fin.addCases_right (m := Es.k) j
  -- A vertex of an `S`-block lies in `S`.
  have hSblock_subset : ∀ (i : Fin Es.k) (v : V),
      v ∈ subtypeImage (Es.blocks i) → v ∈ S := by
    rintro i v ⟨⟨w, hw⟩, _, rfl⟩; exact hw
  have hTblock_subset : ∀ (j : Fin Et.k) (v : V),
      v ∈ subtypeImage (Et.blocks j) → v ∈ T := by
    rintro j v ⟨⟨w, hw⟩, _, rfl⟩; exact hw
  -- `x` is covered by some `S`-block (the start block).
  obtain ⟨s0, hs0val, hs0mem⟩ := hr0
  have hxInSomeS : ∃ i : Fin Es.k, x ∈ subtypeImage (Es.blocks i) := by
    obtain ⟨i, hi⟩ := Es.vertex_cover ⟨x, hxS⟩
    exact ⟨i, ⟨⟨x, hxS⟩, hi, rfl⟩⟩
  -- Key: a vertex of a `T`-block that also lies in some `S`-block must be `x`.
  have hcrossblock : ∀ (j : Fin Et.k) (v : V),
      v ∈ subtypeImage (Et.blocks j) →
      (∃ i : Fin Es.k, v ∈ subtypeImage (Es.blocks i)) → v = x := by
    rintro j v hvT ⟨i, hvS⟩
    exact hshared v (hSblock_subset i v hvS) (hTblock_subset j v hvT)
  -- Decompose membership in a low-index (`S`) global block.
  have blocks_lt : ∀ (q : Fin (Es.k + Et.k)) (hq : q.1 < Es.k) (w : V),
      w ∈ blocks q → w ∈ subtypeImage (Es.blocks ⟨q.1, hq⟩) := by
    intro q hq w hw
    have hcast : Fin.castAdd Et.k ⟨q.1, hq⟩ = q := Fin.ext (by simp)
    have hb := blocks_castAdd ⟨q.1, hq⟩
    rw [hcast] at hb
    rwa [hb] at hw
  -- Decompose membership in a high-index (`T`) global block.
  have blocks_ge : ∀ (q : Fin (Es.k + Et.k)) (hq : Es.k ≤ q.1) (w : V),
      w ∈ blocks q →
      w ∈ subtypeImage (Et.blocks ⟨q.1 - Es.k, by omega⟩) := by
    intro q hq w hw
    have hnat : Fin.natAdd Es.k ⟨q.1 - Es.k, by omega⟩ = q :=
      Fin.ext (by simp; omega)
    have hb := blocks_natAdd ⟨q.1 - Es.k, by omega⟩
    rw [hnat] at hb
    rwa [hb] at hw
  refine ⟨{
    k := Es.k + Et.k
    blocks := blocks
    roots := roots
    isBlock := ?_
    vertex_cover := ?_
    edge_cover := ?_
    root_mem := ?_
    prev_mem := ?_
    meet_prev := ?_ }, ?_⟩
  · -- isBlock
    intro i
    refine Fin.addCases (motive := fun i => IsBlock G (blocks i)) ?_ ?_ i
    · intro i
      rw [blocks_castAdd i]
      exact liftS _ (Es.isBlock i)
    · intro j
      rw [blocks_natAdd j]
      exact liftT _ (Et.isBlock j)
  · -- vertex_cover
    intro v
    have hv : v ∈ S ∪ T := by rw [hcover]; trivial
    rcases hv with hvS | hvT
    · obtain ⟨i, hi⟩ := Es.vertex_cover ⟨v, hvS⟩
      refine ⟨Fin.castAdd Et.k i, ?_⟩
      rw [blocks_castAdd i]
      exact ⟨⟨v, hvS⟩, hi, rfl⟩
    · obtain ⟨j, hj⟩ := Et.vertex_cover ⟨v, hvT⟩
      refine ⟨Fin.natAdd Es.k j, ?_⟩
      rw [blocks_natAdd j]
      exact ⟨⟨v, hvT⟩, hj, rfl⟩
  · -- edge_cover
    intro u v huv
    have hu : u ∈ S ∪ T := by rw [hcover]; trivial
    have hvmem : v ∈ S ∪ T := by rw [hcover]; trivial
    -- Decide which side both endpoints share.
    have hboth : (u ∈ S ∧ v ∈ S) ∨ (u ∈ T ∧ v ∈ T) := by
      rcases hu with huS | huT
      · rcases hvmem with hvS | hvT
        · exact Or.inl ⟨huS, hvS⟩
        · by_cases hux : u = x
          · exact Or.inr ⟨hux ▸ hxT, hvT⟩
          · by_cases hvx : v = x
            · exact Or.inl ⟨huS, hvx ▸ hxS⟩
            · exact absurd huv (hcross u v huS hux hvT hvx)
      · rcases hvmem with hvS | hvT
        · by_cases hvx : v = x
          · exact Or.inr ⟨huT, hvx ▸ hxT⟩
          · by_cases hux : u = x
            · exact Or.inl ⟨hux ▸ hxS, hvS⟩
            · exact absurd huv.symm (hcross v u hvS hvx huT hux)
        · exact Or.inr ⟨huT, hvT⟩
    rcases hboth with ⟨huS, hvS⟩ | ⟨huT, hvT⟩
    · have hadj : (G.induce S).Adj ⟨u, huS⟩ ⟨v, hvS⟩ := by simpa using huv
      obtain ⟨i, hui, hvi⟩ := Es.edge_cover hadj
      refine ⟨Fin.castAdd Et.k i, ?_, ?_⟩ <;>
        · rw [blocks_castAdd i]
          first
            | exact ⟨⟨u, huS⟩, hui, rfl⟩
            | exact ⟨⟨v, hvS⟩, hvi, rfl⟩
    · have hadj : (G.induce T).Adj ⟨u, huT⟩ ⟨v, hvT⟩ := by simpa using huv
      obtain ⟨j, huj, hvj⟩ := Et.edge_cover hadj
      refine ⟨Fin.natAdd Es.k j, ?_, ?_⟩ <;>
        · rw [blocks_natAdd j]
          first
            | exact ⟨⟨u, huT⟩, huj, rfl⟩
            | exact ⟨⟨v, hvT⟩, hvj, rfl⟩
  · -- root_mem
    intro i hi
    refine Fin.addCases
      (motive := fun i => i.1 ≠ 0 → roots i ∈ blocks i) ?_ ?_ i hi
    · intro i hi
      have hival : (Fin.castAdd Et.k i).1 = i.1 := Fin.val_castAdd Et.k i
      have hi0 : i.1 ≠ 0 := by rw [hival] at hi; exact hi
      rw [roots_castAdd i, blocks_castAdd i]
      exact ⟨Es.roots i, Es.root_mem i hi0, rfl⟩
    · intro j hj
      rw [roots_natAdd j, blocks_natAdd j]
      by_cases hj0 : j.1 = 0
      · simp only [hj0, if_pos]
        -- first T-block; need x ∈ it
        have : (⟨x, hxT⟩ : T) ∈ Et.blocks j := by
          have ht0eq : t0 = j := Fin.ext (by rw [ht0val, hj0])
          rw [← ht0eq]; exact ht0mem
        exact ⟨⟨x, hxT⟩, this, rfl⟩
      · simp only [hj0, ite_false]
        exact ⟨Et.roots j, Et.root_mem j hj0, rfl⟩
  · -- prev_mem
    intro i hi
    refine Fin.addCases
      (motive := fun i => i.1 ≠ 0 →
        ∃ j : Fin (Es.k + Et.k), j.1 < i.1 ∧ roots i ∈ blocks j) ?_ ?_ i hi
    · intro i hi
      have hival : (Fin.castAdd Et.k i).1 = i.1 := Fin.val_castAdd Et.k i
      have hi0 : i.1 ≠ 0 := by rw [hival] at hi; exact hi
      obtain ⟨q, hqi, hq⟩ := Es.prev_mem i hi0
      refine ⟨Fin.castAdd Et.k q, ?_, ?_⟩
      · rw [Fin.val_castAdd, Fin.val_castAdd]; exact hqi
      · rw [roots_castAdd i, blocks_castAdd q]
        exact ⟨Es.roots i, hq, rfl⟩
    · intro j hj
      have hjval : (Fin.natAdd Es.k j).1 = Es.k + j.1 := Fin.val_natAdd Es.k j
      by_cases hj0 : j.1 = 0
      · -- root is x; x is in some S-block, which is an earlier block.
        obtain ⟨i, hi⟩ := hxInSomeS
        refine ⟨Fin.castAdd Et.k i, ?_, ?_⟩
        · rw [Fin.val_castAdd, hjval, hj0]; exact Nat.lt_of_lt_of_le i.2 (Nat.le_add_right _ _)
        · rw [roots_natAdd j, blocks_castAdd i]
          simp only [hj0, if_pos]
          exact hi
      · obtain ⟨q, hqj, hq⟩ := Et.prev_mem j hj0
        refine ⟨Fin.natAdd Es.k q, ?_, ?_⟩
        · rw [Fin.val_natAdd, hjval]; exact Nat.add_lt_add_left hqj _
        · rw [roots_natAdd j, blocks_natAdd q]
          simp only [hj0, ite_false]
          exact ⟨Et.roots j, hq, rfl⟩
  · -- meet_prev
    intro i hi v
    refine Fin.addCases
      (motive := fun i => i.1 ≠ 0 → v ∈ blocks i →
        ((∃ q : Fin (Es.k + Et.k), q.1 < i.1 ∧ v ∈ blocks q) ↔ v = roots i))
      ?_ ?_ i hi
    · -- castAdd case: previous blocks that contain `v` (in an `S`-block) must
      -- themselves be `S`-blocks, so this reduces to `Es.meet_prev`.
      intro i hi hvmem
      have hival : (Fin.castAdd Et.k i).1 = i.1 := Fin.val_castAdd Et.k i
      have hi0 : i.1 ≠ 0 := by rw [hival] at hi; exact hi
      have hvmem' : v ∈ subtypeImage (Es.blocks i) := by
        rwa [blocks_castAdd i] at hvmem
      obtain ⟨hvS, hvSb⟩ := (mem_subtypeImage_iff (Es.blocks i) v).mp hvmem'
      rw [roots_castAdd i, hival]
      constructor
      · rintro ⟨q, hqlt, hqv⟩
        have hqcast : q.1 < Es.k := lt_of_lt_of_le hqlt (le_of_lt i.2)
        have hqv' : v ∈ subtypeImage (Es.blocks ⟨q.1, hqcast⟩) :=
          blocks_lt q hqcast v hqv
        obtain ⟨_, hqvb⟩ := (mem_subtypeImage_iff _ v).mp hqv'
        have hex : ∃ q' : Fin Es.k, q'.1 < i.1 ∧ (⟨v, hvS⟩ : S) ∈ Es.blocks q' :=
          ⟨⟨q.1, hqcast⟩, hqlt, by simpa using hqvb⟩
        have := (Es.meet_prev i hi0 ⟨v, hvS⟩ hvSb).mp hex
        exact congrArg Subtype.val this
      · intro hvroot
        have hvSroot : (⟨v, hvS⟩ : S) = Es.roots i := Subtype.ext hvroot
        have hex : ∃ q' : Fin Es.k, q'.1 < i.1 ∧ (⟨v, hvS⟩ : S) ∈ Es.blocks q' := by
          rw [hvSroot]
          obtain ⟨q', hq'i, hq'⟩ := Es.prev_mem i hi0
          exact ⟨q', hq'i, hq'⟩
        obtain ⟨q', hq'i, hq'⟩ := hex
        refine ⟨Fin.castAdd Et.k q', ?_, ?_⟩
        · rw [Fin.val_castAdd]; exact hq'i
        · rw [blocks_castAdd q']
          exact ⟨⟨v, hvS⟩, hq', rfl⟩
    · -- natAdd case: `v` lies in a `T`-block.
      intro j hj hvmem
      have hjval : (Fin.natAdd Es.k j).1 = Es.k + j.1 := Fin.val_natAdd Es.k j
      have hvmemT : v ∈ subtypeImage (Et.blocks j) := by
        rwa [blocks_natAdd j] at hvmem
      obtain ⟨hvT, hvTb⟩ := (mem_subtypeImage_iff (Et.blocks j) v).mp hvmemT
      -- `v` lies in some `S`-block iff `v = x`.
      have hvInS_iff : (∃ i : Fin Es.k, v ∈ subtypeImage (Es.blocks i)) ↔ v = x := by
        constructor
        · intro h; exact hcrossblock j v hvmemT h
        · rintro rfl; exact hxInSomeS
      -- `x ∈ Et.blocks 0`, and block 0 is an earlier `T`-block when `j ≠ 0`.
      have hxprevT : ∀ (hj0 : j.1 ≠ 0),
          ∃ q' : Fin Et.k, q'.1 < j.1 ∧ (⟨x, hxT⟩ : T) ∈ Et.blocks q' :=
        fun _ => ⟨t0, by rw [ht0val]; omega, ht0mem⟩
      by_cases hj0 : j.1 = 0
      · -- root is `x`; only `S`-blocks precede.
        have hroot : roots (Fin.natAdd Es.k j) = x := by
          rw [roots_natAdd j]; simp [hj0]
        rw [hroot]
        constructor
        · rintro ⟨q, hqlt, hqv⟩
          rw [hjval, hj0, Nat.add_zero] at hqlt
          have hqv' : v ∈ subtypeImage (Es.blocks ⟨q.1, hqlt⟩) :=
            blocks_lt q hqlt v hqv
          exact hvInS_iff.mp ⟨⟨q.1, hqlt⟩, hqv'⟩
        · intro hvx
          obtain ⟨i, hi⟩ := hvInS_iff.mpr hvx
          refine ⟨Fin.castAdd Et.k i, ?_, ?_⟩
          · rw [Fin.val_castAdd, hjval, hj0]; exact Nat.lt_of_lt_of_le i.2 (by omega)
          · rw [blocks_castAdd i]
            exact hi
      · -- root is `Et.roots j`.
        have hroot : roots (Fin.natAdd Es.k j) = (Et.roots j).1 := by
          rw [roots_natAdd j]; simp [hj0]
        rw [hroot]
        -- If `v = x` then `x ∈ Et.blocks j` forces `Et.roots j = x`.
        have hx_forces : v = x → v = (Et.roots j).1 := by
          intro hvx
          have hxb : (⟨x, hxT⟩ : T) ∈ Et.blocks j := by
            have heq : (⟨x, hxT⟩ : T) = ⟨v, hvT⟩ := Subtype.ext hvx.symm
            rw [heq]; exact hvTb
          obtain ⟨q', hq'lt, hq'⟩ := hxprevT hj0
          have hxroot : (⟨x, hxT⟩ : T) = Et.roots j :=
            (Et.meet_prev j hj0 ⟨x, hxT⟩ hxb).mp ⟨q', hq'lt, hq'⟩
          rw [hvx]; exact congrArg Subtype.val hxroot
        -- `v` in an earlier `T`-block iff `v = Et.roots j`.
        have hvInPrevT_iff :
            (∃ q' : Fin Et.k, q'.1 < j.1 ∧ (⟨v, hvT⟩ : T) ∈ Et.blocks q')
              ↔ (⟨v, hvT⟩ : T) = Et.roots j :=
          Et.meet_prev j hj0 ⟨v, hvT⟩ hvTb
        constructor
        · rintro ⟨q, hqlt, hqv⟩
          rw [hjval] at hqlt
          by_cases hqcast : q.1 < Es.k
          · -- `v` in an `S`-block ⟹ `v = x` ⟹ `v = Et.roots j`.
            have hqv' : v ∈ subtypeImage (Es.blocks ⟨q.1, hqcast⟩) :=
              blocks_lt q hqcast v hqv
            exact hx_forces (hvInS_iff.mp ⟨⟨q.1, hqcast⟩, hqv'⟩)
          · -- `v` in an earlier `T`-block.
            push Not at hqcast
            have hqlt' : q.1 - Es.k < j.1 := by omega
            have hqv' : v ∈ subtypeImage (Et.blocks ⟨q.1 - Es.k, by omega⟩) :=
              blocks_ge q hqcast v hqv
            obtain ⟨_, hqvb⟩ := (mem_subtypeImage_iff _ v).mp hqv'
            have : (⟨v, hvT⟩ : T) = Et.roots j :=
              hvInPrevT_iff.mp ⟨⟨q.1 - Es.k, by omega⟩, hqlt', by simpa using hqvb⟩
            exact congrArg Subtype.val this
        · intro hvroot
          have hvTroot : (⟨v, hvT⟩ : T) = Et.roots j := Subtype.ext hvroot
          obtain ⟨q', hq'lt, hq'⟩ := hvInPrevT_iff.mpr hvTroot
          refine ⟨Fin.natAdd Es.k q', ?_, ?_⟩
          · rw [Fin.val_natAdd, hjval]; omega
          · rw [blocks_natAdd q']
            exact ⟨⟨v, hvT⟩, hq', rfl⟩
  · -- StartsAt r
    refine ⟨Fin.castAdd Et.k s0, ?_, ?_⟩
    · rw [Fin.val_castAdd]; exact hs0val
    · show r ∈ blocks (Fin.castAdd Et.k s0)
      rw [blocks_castAdd s0]
      exact ⟨⟨r, hrS⟩, hs0mem, rfl⟩

/--
Strong-induction core: every finite connected graph admits a rooted block
enumeration starting at any prescribed root.  Induction is on `Nat.card`.  In
the no-cut case the whole graph is a single block; otherwise a cut vertex `x`
splits the graph into two strictly smaller connected sides meeting only at `x`,
each of which is handled by the induction hypothesis and the two enumerations
are concatenated by `concat_rootedBlockEnumeration`.
-/
theorem exists_rootedBlockEnumeration_startsAt_aux :
    ∀ n : ℕ, ∀ {W : Type*} [Finite W] (H : SimpleGraph W),
      Nat.card W = n → H.Connected → ∀ r : W,
        ∃ E : RootedBlockEnumeration H, E.StartsAt r := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W _ H hcard hH r
    classical
    by_cases hcut : ∀ x : W, ¬ IsCutVertex H x
    · exact exists_rootedBlockEnumeration_of_connected_of_no_cut hH hcut r
    · push Not at hcut
      obtain ⟨x, hxcut⟩ := hcut
      -- `H - x` is not preconnected: extract two non-reachable vertices.
      have hnotpre : ¬ (H.induce {y : W | y ≠ x}).Preconnected := hxcut.2
      obtain ⟨a, b, hab⟩ : ∃ a b : {y : W // y ≠ x},
          ¬ (H.induce {y : W | y ≠ x}).Reachable a b := by
        unfold SimpleGraph.Preconnected at hnotpre
        push Not at hnotpre
        exact hnotpre
      -- Choose the component `C` of `a`; the component `D` of `b` is different.
      set C : (H.induce {y : W | y ≠ x}).ConnectedComponent :=
        (H.induce {y : W | y ≠ x}).connectedComponentMk a with hCdef
      set D : (H.induce {y : W | y ≠ x}).ConnectedComponent :=
        (H.induce {y : W | y ≠ x}).connectedComponentMk b with hDdef
      have hDC : D ≠ C := by
        intro he
        have hmk : (H.induce {y : W | y ≠ x}).connectedComponentMk a
            = (H.induce {y : W | y ≠ x}).connectedComponentMk b :=
          hCdef.symm.trans (he.symm.trans hDdef)
        exact hab (SimpleGraph.ConnectedComponent.exact hmk)
      have hother : ∃ E : (H.induce {y : W | y ≠ x}).ConnectedComponent, E ≠ C := ⟨D, hDC⟩
      -- Abbreviations for the two sides.
      set S₁ : Set W := deleteComponentSide H x C with hS₁
      set S₂ : Set W := deleteComponentOtherSide H x C with hS₂
      have hxS₁ : x ∈ S₁ := by simp [hS₁, deleteComponentSide]
      have hxS₂ : x ∈ S₂ := by
        simp only [hS₂]; exact deleteComponentSet_notMem_self C
      -- Cover, intersection, no cross edge.
      have hcover : S₁ ∪ S₂ = Set.univ :=
        deleteComponentSide_union_otherSide C
      have hinter : S₁ ∩ S₂ = ({x} : Set W) :=
        deleteComponentSide_inter_otherSide C
      have hcross : ∀ u v : W, u ∈ S₁ → u ≠ x → v ∈ S₂ → v ≠ x → ¬ H.Adj u v :=
        fun u v hu hune hv hvne =>
          not_adj_deleteComponentSide_otherSide hu hune hv hvne
      -- Lifts of induced blocks to global blocks.
      have liftS₁ : ∀ B : Set S₁, IsBlock (H.induce S₁) B → IsBlock H (subtypeImage B) :=
        fun B hB => isBlock_image_of_induce_deleteComponentSide hH C hB
      have liftS₂ : ∀ B : Set S₂, IsBlock (H.induce S₂) B → IsBlock H (subtypeImage B) :=
        fun B hB => isBlock_image_of_induce_deleteComponentOtherSide hH C hother hB
      -- Both sides are connected.
      have hconnS₁ : (H.induce S₁).Connected := deleteComponentSide_connected hH x C
      have hconnS₂ : (H.induce S₂).Connected := deleteComponentOtherSide_connected hH x C
      -- Both sides are strictly smaller than `W`.
      have hcardS₁ : Nat.card S₁ < n := by
        rw [← hcard]
        obtain ⟨d, hd⟩ := D.nonempty_supp
        have hd_notmem : (d.1 : W) ∉ S₁ := by
          rw [hS₁]
          intro hmem
          rcases hmem with hdx | hdC
          · exact d.2 hdx
          · rcases hdC with ⟨_, hdCmem⟩
            exact hDC (SimpleGraph.ConnectedComponent.eq_of_common_vertex (by simpa using hd) hdCmem)
        exact Finite.card_subtype_lt (p := (· ∈ S₁)) hd_notmem
      have hcardS₂ : Nat.card S₂ < n := by
        rw [← hcard]
        obtain ⟨c, hc⟩ := C.nonempty_supp
        have hc_notmem : (c.1 : W) ∉ S₂ := by
          rw [hS₂]
          simp only [deleteComponentOtherSide, Set.mem_compl_iff, not_not]
          exact ⟨c.2, by simpa using hc⟩
        exact Finite.card_subtype_lt (p := (· ∈ S₂)) hc_notmem
      -- Apply the induction hypothesis to each side.
      have IH₁ : ∀ r₁ : S₁, ∃ E : RootedBlockEnumeration (H.induce S₁), E.StartsAt r₁ :=
        fun r₁ => ih (Nat.card S₁) hcardS₁ (H.induce S₁) rfl hconnS₁ r₁
      have IH₂ : ∀ r₂ : S₂, ∃ E : RootedBlockEnumeration (H.induce S₂), E.StartsAt r₂ :=
        fun r₂ => ih (Nat.card S₂) hcardS₂ (H.induce S₂) rfl hconnS₂ r₂
      -- `r` is on one side or the other.
      have hrmem : r ∈ S₁ ∪ S₂ := by rw [hcover]; trivial
      rcases hrmem with hrS₁ | hrS₂
      · -- `r ∈ S₁`: lay down `S₁` first, then `S₂` rooted at `x`.
        obtain ⟨Es, hEs⟩ := IH₁ ⟨r, hrS₁⟩
        obtain ⟨Et, hEt⟩ := IH₂ ⟨x, hxS₂⟩
        exact concat_rootedBlockEnumeration hcover hxS₁ hxS₂ hinter hcross
          liftS₁ liftS₂ Es Et hEt hrS₁ hEs
      · -- `r ∈ S₂`: lay down `S₂` first, then `S₁` rooted at `x`.
        obtain ⟨Es, hEs⟩ := IH₂ ⟨r, hrS₂⟩
        obtain ⟨Et, hEt⟩ := IH₁ ⟨x, hxS₁⟩
        refine concat_rootedBlockEnumeration (S := S₂) (T := S₁)
          (by rw [Set.union_comm]; exact hcover) hxS₂ hxS₁
          (by rw [Set.inter_comm]; exact hinter)
          (fun u v hu hune hv hvne => fun hadj =>
            hcross v u hv hvne hu hune hadj.symm)
          liftS₂ liftS₁ Es Et hEt hrS₂ hEs

/-- **Existence of a rooted block enumeration for a finite connected graph.**
Every finite connected simple graph admits a rooted block enumeration. -/
theorem exists_rootedBlockEnumeration_of_connected {G : SimpleGraph V} [Finite V]
    (hG : G.Connected) : Nonempty (RootedBlockEnumeration G) := by
  obtain ⟨r⟩ := hG.nonempty
  obtain ⟨E, _⟩ :=
    exists_rootedBlockEnumeration_startsAt_aux (Nat.card V) G rfl hG r
  exact ⟨E⟩

end RootedEnumeration

section AbstractGlue

variable {G : SimpleGraph V} {Color : Type*}

/-- A plain proper coloring with colors in `Color`. -/
def IsProperColoring (G : SimpleGraph V) (c : V → Color) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v

/--
Rooted colorability of a vertex set: for every chosen root color, the induced
subgraph on the set admits a proper coloring assigning that color to the root.
This is abstract enough to cover ordinary `alpha`-coloring and the 5-color
specialization.
-/
def RootedColorableOn (G : SimpleGraph V) (B : Set V) (Color : Type*) : Prop :=
  ∀ v : V, v ∈ B → ∀ c : Color,
    ∃ f : V → Color,
      IsProperColoring (G.induce B) (fun x : B => f x) ∧ f v = c

private def PrefixAgreement (E : RootedBlockEnumeration G) (n : ℕ)
    (f : V → Color) : Prop :=
  ∀ i : Fin E.k, i.1 < n →
    ∃ c : V → Color,
      IsProperColoring (G.induce (E.blocks i)) (fun x : E.blocks i => c x) ∧
        ∀ v, v ∈ E.blocks i → f v = c v

private theorem exists_prefix_coloring [Nonempty Color]
    (E : RootedBlockEnumeration G)
    (hrooted : ∀ i, RootedColorableOn G (E.blocks i) Color) :
    ∀ n, n ≤ E.k → ∃ f : V → Color, PrefixAgreement (G := G) E n f := by
  classical
  intro n
  induction n with
  | zero =>
      intro _
      refine ⟨fun _ => Classical.choice inferInstance, ?_⟩
      intro i hi
      omega
  | succ n ih =>
      intro hn
      have hnle : n ≤ E.k := Nat.le_of_succ_le hn
      obtain ⟨f, hf⟩ := ih hnle
      let i : Fin E.k := ⟨n, Nat.lt_of_succ_le hn⟩
      have hnew :
          ∃ c : V → Color,
            IsProperColoring (G.induce (E.blocks i)) (fun x : E.blocks i => c x) ∧
              (i.1 ≠ 0 → c (E.roots i) = f (E.roots i)) := by
        by_cases hi0 : i.1 = 0
        · obtain ⟨r, hr⟩ := blockCore_nonempty (isBlock_blockCore (E.isBlock i))
          obtain ⟨c, hc, -⟩ :=
            hrooted i r hr (Classical.choice inferInstance)
          exact ⟨c, hc, fun hi => (hi hi0).elim⟩
        · obtain ⟨c, hc, hroot⟩ :=
            hrooted i (E.roots i) (E.root_mem i hi0) (f (E.roots i))
          exact ⟨c, hc, fun _ => hroot⟩
      obtain ⟨cnew, hcnew, hcroot⟩ := hnew
      let f' : V → Color := fun v => if v ∈ E.blocks i then cnew v else f v
      refine ⟨f', ?_⟩
      intro j hj
      have hlt_or_eq : j.1 < n ∨ j.1 = n := Nat.lt_succ_iff_lt_or_eq.mp hj
      rcases hlt_or_eq with hlt | hval
      · obtain ⟨cj, hcj, hagree⟩ := hf j hlt
        refine ⟨cj, hcj, ?_⟩
        intro v hvj
        by_cases hvnew : v ∈ E.blocks i
        · have hi_ne_zero : i.1 ≠ 0 := by
            dsimp [i]
            omega
          have hprev : ∃ q : Fin E.k, q.1 < i.1 ∧ v ∈ E.blocks q :=
            ⟨j, hlt, hvj⟩
          have hvroot : v = E.roots i :=
            (E.meet_prev i hi_ne_zero v hvnew).mp hprev
          calc
            f' v = cnew v := by simp [f', hvnew]
            _ = cnew (E.roots i) := by rw [hvroot]
            _ = f (E.roots i) := hcroot hi_ne_zero
            _ = f v := by rw [hvroot]
            _ = cj v := hagree v hvj
        · simpa [f', hvnew] using hagree v hvj
      · have hji : j = i := Fin.ext hval
        subst hji
        refine ⟨cnew, hcnew, ?_⟩
        intro v hv
        simp [f', hv]

/--
Rooted coloring glue.  If the graph has a rooted block enumeration and every
block can be colored with any prescribed color at any prescribed root vertex,
then the whole graph has a proper coloring.
-/
theorem exists_properColoring_of_rootedBlockEnumeration [Nonempty Color]
    (E : RootedBlockEnumeration G)
    (hrooted : ∀ i, RootedColorableOn G (E.blocks i) Color) :
    ∃ f : V → Color, IsProperColoring G f := by
  classical
  obtain ⟨f, hf⟩ := exists_prefix_coloring (G := G) (Color := Color) E hrooted E.k le_rfl
  refine ⟨f, ?_⟩
  intro u v huv
  obtain ⟨i, hui, hvi⟩ := E.edge_cover huv
  obtain ⟨c, hc, hagree⟩ := hf i i.2
  have hInd : (G.induce (E.blocks i)).Adj ⟨u, hui⟩ ⟨v, hvi⟩ := by
    simpa using huv
  have hcuv : c u ≠ c v := hc hInd
  exact fun hsame => hcuv (by
    rw [← hagree u hui, ← hagree v hvi]
    exact hsame)

end AbstractGlue

end ProofsInTheBook.SimpleGraphBlocks
