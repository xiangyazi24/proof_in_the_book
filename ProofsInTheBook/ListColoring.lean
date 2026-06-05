/-
List-coloring primitives (Chapter 35 layer 4).

Design-independent groundwork for the Thomassen five-list-coloring route
(HANDOFF/CH35_DESIGN_ANSWER.md): proper colorings from lists, monotonicity
in the graph and in the lists, and the piecewise gluing lemmas — including
the rooted cut-vertex glue, which is the form that is actually true for
list colorings (naive gluing fails because the two sides may disagree at
the cut vertex).
-/
import Mathlib

namespace ProofsInTheBook.ListColoring

variable {V α : Type*}

/-- `c` is proper on the region `s`: no monochromatic edge inside `s`. -/
def ProperOn (G : SimpleGraph V) (s : Set V) (c : V → α) : Prop :=
  ∀ ⦃u v⦄, u ∈ s → v ∈ s → G.Adj u v → c u ≠ c v

/-- `c` picks from the lists `L` on the region `s`. -/
def ListValidOn (L : V → Finset α) (s : Set V) (c : V → α) : Prop :=
  ∀ ⦃v⦄, v ∈ s → c v ∈ L v

/-- A proper coloring of all of `G` choosing from the lists `L`. -/
def IsListColoring (G : SimpleGraph V) (L : V → Finset α) (c : V → α) : Prop :=
  (∀ v, c v ∈ L v) ∧ ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v

/-- `G` admits a proper coloring from the lists `L`. -/
def ListColorable (G : SimpleGraph V) (L : V → Finset α) : Prop :=
  ∃ c, IsListColoring G L c

theorem isListColoring_iff_on_univ (G : SimpleGraph V) (L : V → Finset α)
    (c : V → α) :
    IsListColoring G L c ↔
      ListValidOn L Set.univ c ∧ ProperOn G Set.univ c := by
  constructor
  · rintro ⟨hL, hp⟩
    exact ⟨fun v _ => hL v, fun u v _ _ h => hp h⟩
  · rintro ⟨hL, hp⟩
    exact ⟨fun v => hL (Set.mem_univ v),
      fun u v h => hp (Set.mem_univ u) (Set.mem_univ v) h⟩

/-- A list coloring of a supergraph (same vertices) is one of the subgraph. -/
theorem IsListColoring.mono_graph {G H : SimpleGraph V} (hHG : H ≤ G)
    {L : V → Finset α} {c : V → α} (hc : IsListColoring G L c) :
    IsListColoring H L c :=
  ⟨hc.1, fun _ _ h => hc.2 (hHG h)⟩

theorem ListColorable.mono_graph {G H : SimpleGraph V} (hHG : H ≤ G)
    {L : V → Finset α} (h : ListColorable G L) : ListColorable H L := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.mono_graph hHG⟩

/-- Enlarging the lists preserves list colorings. -/
theorem IsListColoring.mono_lists {G : SimpleGraph V} {L L' : V → Finset α}
    (hLL : ∀ v, L v ⊆ L' v) {c : V → α} (hc : IsListColoring G L c) :
    IsListColoring G L' c :=
  ⟨fun v => hLL v (hc.1 v), hc.2⟩

theorem ListColorable.mono_lists {G : SimpleGraph V} {L L' : V → Finset α}
    (hLL : ∀ v, L v ⊆ L' v) (h : ListColorable G L) : ListColorable G L' := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.mono_lists hLL⟩

section Glue

variable {G : SimpleGraph V} {L : V → Finset α} {s t : Set V} {c₁ c₂ : V → α}

/--
The piecewise gluing lemma.  If `s` and `t` cover the vertices, every edge
lives inside `s` or inside `t`, the two partial colorings are proper and
list-valid on their regions, and they agree on the overlap, then the
piecewise function is a list coloring of `G`.
-/
theorem isListColoring_glue [DecidablePred (· ∈ s)]
    (hcover : ∀ v, v ∈ s ∨ v ∈ t)
    (hsep : ∀ ⦃u v⦄, G.Adj u v → (u ∈ s ∧ v ∈ s) ∨ (u ∈ t ∧ v ∈ t))
    (h₁p : ProperOn G s c₁) (h₁L : ListValidOn L s c₁)
    (h₂p : ProperOn G t c₂) (h₂L : ListValidOn L t c₂)
    (hagree : ∀ ⦃v⦄, v ∈ s → v ∈ t → c₁ v = c₂ v) :
    IsListColoring G L (fun v => if v ∈ s then c₁ v else c₂ v) := by
  constructor
  · intro v
    by_cases hv : v ∈ s
    · simpa [hv] using h₁L hv
    · have hvt : v ∈ t := (hcover v).resolve_left hv
      simpa [hv] using h₂L hvt
  · intro u v huv
    rcases hsep huv with ⟨hus, hvs⟩ | ⟨hut, hvt⟩
    · simpa [hus, hvs] using h₁p hus hvs huv
    · by_cases hus : u ∈ s
      · by_cases hvs : v ∈ s
        · have hu := hagree hus hut
          have hv := hagree hvs hvt
          simpa [hus, hvs, hu, hv] using h₂p hut hvt huv
        · have hu := hagree hus hut
          simpa [hus, hvs, hu] using h₂p hut hvt huv
      · by_cases hvs : v ∈ s
        · have hv := hagree hvs hvt
          simpa [hus, hvs, hv] using h₂p hut hvt huv
        · simpa [hus, hvs] using h₂p hut hvt huv

/--
Rooted cut-vertex glue: if the regions overlap in exactly the cut vertex
`w` and both sides color `w` with the same prescribed color, the colorings
glue.  This is the form of gluing that is true for list colorings; without
the agreement at `w` it is false.
-/
theorem isListColoring_glue_at_cutvertex [DecidablePred (· ∈ s)] {w : V}
    (hcover : ∀ v, v ∈ s ∨ v ∈ t)
    (hsep : ∀ ⦃u v⦄, G.Adj u v → (u ∈ s ∧ v ∈ s) ∨ (u ∈ t ∧ v ∈ t))
    (hcap : s ∩ t ⊆ {w})
    (h₁p : ProperOn G s c₁) (h₁L : ListValidOn L s c₁)
    (h₂p : ProperOn G t c₂) (h₂L : ListValidOn L t c₂)
    (hw : c₁ w = c₂ w) :
    IsListColoring G L (fun v => if v ∈ s then c₁ v else c₂ v) := by
  refine isListColoring_glue hcover hsep h₁p h₁L h₂p h₂L ?_
  intro v hvs hvt
  have : v = w := hcap ⟨hvs, hvt⟩
  subst this
  exact hw

end Glue

/--
Greedy extension step: a proper list coloring of the region `s` extends to
`s ∪ {v}` whenever some color of `L v` avoids the colors of the neighbors
of `v` inside `s`.
-/
theorem properOn_extend {G : SimpleGraph V} {L : V → Finset α} {s : Set V}
    {c : V → α} {v : V} {a : α} [DecidableEq V]
    (hv : v ∉ s)
    (hp : ProperOn G s c) (hL : ListValidOn L s c)
    (ha : a ∈ L v) (havoid : ∀ ⦃u⦄, u ∈ s → G.Adj v u → c u ≠ a) :
    ProperOn G (insert v s) (Function.update c v a) ∧
      ListValidOn L (insert v s) (Function.update c v a) := by
  constructor
  · intro x y hx hy hxy
    rcases Set.mem_insert_iff.mp hx with hxv | hxs <;>
      rcases Set.mem_insert_iff.mp hy with hyv | hys
    · rw [hxv, hyv] at hxy
      exact (G.irrefl hxy).elim
    · rw [hxv] at hxy ⊢
      have hyne : y ≠ v := fun h => hv (h ▸ hys)
      rw [Function.update_self, Function.update_of_ne hyne]
      exact fun h => havoid hys hxy h.symm
    · rw [hyv] at hxy ⊢
      have hxne : x ≠ v := fun h => hv (h ▸ hxs)
      rw [Function.update_of_ne hxne, Function.update_self]
      exact fun h => havoid hxs (G.symm hxy) h
    · have hxne : x ≠ v := fun h => hv (h ▸ hxs)
      have hyne : y ≠ v := fun h => hv (h ▸ hys)
      rw [Function.update_of_ne hxne, Function.update_of_ne hyne]
      exact hp hxs hys hxy
  · intro z hz
    rcases Set.mem_insert_iff.mp hz with hzv | hzs
    · subst hzv
      rw [Function.update_self]
      exact ha
    · have hzne : z ≠ v := fun h => hv (h ▸ hzs)
      rw [Function.update_of_ne hzne]
      exact hL hzs

end ProofsInTheBook.ListColoring
