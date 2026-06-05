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
