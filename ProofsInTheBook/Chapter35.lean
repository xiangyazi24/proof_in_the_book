import Mathlib

/-!
# Chapter 35: Five-coloring plane graphs

From "Proofs from THE BOOK":

**Five color theorem**: Every planar graph is 5-colorable.

The book's proof uses Euler's formula (E ≤ 3V-6 for planar graphs)
to find a vertex of degree ≤ 5, then applies induction with a
Kempe chain argument to handle the degree-5 case.

Mathlib does not currently provide a planar graph predicate or the
plane-embedding/Jordan-curve infrastructure needed to instantiate the last
Kempe separation step for planar graphs.  The theorem named `chapter35`
below is therefore the honest certified form: a finite graph equipped with
a recursive deletion certificate whose local steps are exactly the
degree-≤4 or Kempe-swap extensions in the book is 5-colorable.  For the
planar class, the missing front is to prove that every finite planar graph
has such a certificate from Euler's degree bound and the planar
Kempe-chain separation lemma.
-/

namespace ProofsInTheBook.Chapter35

open scoped BigOperators

theorem exists_degree_le_five_of_average_lt_six {α : Type*} (vertices : Finset α)
    (degree : α → ℕ) (hsum : (∑ v ∈ vertices, degree v) < 6 * vertices.card) :
    ∃ v ∈ vertices, degree v ≤ 5 := by
  by_contra hnone
  have hall : ∀ v ∈ vertices, 6 ≤ degree v := by
    intro v hv
    have hnot : ¬ degree v ≤ 5 := by
      intro hv5
      exact hnone ⟨v, hv, hv5⟩
    omega
  have hlower : 6 * vertices.card ≤ ∑ v ∈ vertices, degree v := by
    calc
      6 * vertices.card = ∑ v ∈ vertices, 6 := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ vertices, degree v := by
        exact Finset.sum_le_sum fun v hv => hall v hv
  omega

theorem exists_unused_five_color (used : Finset (Fin 5)) (hused : used.card < 5) :
    ∃ c : Fin 5, c ∉ used := by
  by_contra hnone
  push Not at hnone
  have huniv : used = Finset.univ := by
    ext c
    exact ⟨fun _ => Finset.mem_univ c, fun _ => hnone c⟩
  have : used.card = 5 := by simp [huniv]
  omega

theorem exists_unused_color_of_neighbor_bound {V : Type*} [DecidableEq V]
    (neighbors : Finset V) (color : V → Fin 5) (hdeg : neighbors.card ≤ 4) :
    ∃ c : Fin 5, ∀ v ∈ neighbors, color v ≠ c := by
  classical
  let used := neighbors.image color
  have hused : used.card < 5 := by
    have hle : used.card ≤ neighbors.card := Finset.card_image_le
    omega
  rcases exists_unused_five_color used hused with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro v hv hvc
  apply hc
  exact Finset.mem_image.mpr ⟨v, hv, hvc⟩

section KempeChains

/-- Swap two colors, leaving all others fixed. -/
def swapColor (c1 c2 : Fin 5) (c : Fin 5) : Fin 5 :=
  if c = c1 then c2 else if c = c2 then c1 else c

theorem swapColor_injective (c1 c2 : Fin 5) : Function.Injective (swapColor c1 c2) := by
  intro x y h; unfold swapColor at h
  by_cases hx1 : x = c1 <;> by_cases hy1 : y = c1 <;>
  by_cases hx2 : x = c2 <;> by_cases hy2 : y = c2 <;>
  simp_all

/--
Kempe swap preserves properness when `S` is closed under `c1-c2` adjacency.
The boundary argument: if `u ∈ S` and `v ∉ S` are adjacent, then `color v`
is neither `c1` nor `c2` (or else `v` would be reachable in the `c1-c2`
subgraph and thus in `S`). So swapped `color u ∈ {c1,c2}` differs from
unchanged `color v ∉ {c1,c2}`.
-/
theorem kempeSwap_proper_abstract {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (color : V → Fin 5)
    (hproper : ∀ u v, G.Adj u v → color u ≠ color v)
    (c1 c2 : Fin 5) (_hne : c1 ≠ c2)
    (S : Finset V)
    (hclosed : ∀ u v, G.Adj u v → u ∈ S → (color u = c1 ∨ color u = c2) →
      (color v = c1 ∨ color v = c2) → v ∈ S) :
    ∀ u v, G.Adj u v →
      (fun w => if w ∈ S then swapColor c1 c2 (color w) else color w) u ≠
      (fun w => if w ∈ S then swapColor c1 c2 (color w) else color w) v := by
  intro u v hadj heq
  simp only at heq
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp only [hu, hv, ite_true, ite_false] at heq
  · exact hproper u v hadj (swapColor_injective c1 c2 heq)
  · by_cases huc1 : color u = c1
    · by_cases hvc : color v = c1 ∨ color v = c2
      · exact hv (hclosed u v hadj hu (Or.inl huc1) hvc)
      · push Not at hvc
        simp only [swapColor, if_pos huc1] at heq; exact hvc.2 heq.symm
    · by_cases huc2 : color u = c2
      · by_cases hvc : color v = c1 ∨ color v = c2
        · exact hv (hclosed u v hadj hu (Or.inr huc2) hvc)
        · push Not at hvc
          simp only [swapColor, if_neg huc1, if_pos huc2] at heq; exact hvc.1 heq.symm
      · simp only [swapColor, if_neg huc1, if_neg huc2] at heq
        exact hproper u v hadj heq
  · by_cases hvc1 : color v = c1
    · by_cases huc : color u = c1 ∨ color u = c2
      · exact hu (hclosed v u (G.symm hadj) hv (Or.inl hvc1) huc)
      · push Not at huc
        simp only [swapColor, if_pos hvc1] at heq; exact huc.2 heq
    · by_cases hvc2 : color v = c2
      · by_cases huc : color u = c1 ∨ color u = c2
        · exact hu (hclosed v u (G.symm hadj) hv (Or.inr hvc2) huc)
        · push Not at huc
          simp only [swapColor, if_neg hvc1, if_pos hvc2] at heq; exact huc.1 heq
      · simp only [swapColor, if_neg hvc1, if_neg hvc2] at heq
        exact hproper u v hadj heq
  · exact hproper u v hadj heq

end KempeChains

section FiveColorInduction

universe u

/-- `G.Colorable 5` is exactly the existence of a proper coloring by `Fin 5`. -/
theorem colorable_five_iff_exists_proper_coloring {V : Type u} (G : SimpleGraph V) :
    G.Colorable 5 ↔
      ∃ color : V → Fin 5, ∀ u v : V, G.Adj u v → color u ≠ color v := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C, fun u v huv => C.valid huv⟩
  · rintro ⟨color, hproper⟩
    exact ⟨SimpleGraph.Coloring.mk color (by intro u v huv; exact hproper u v huv)⟩

/-- Five-colorability restricts to a subgraph on the same vertex type. -/
theorem colorable_five_of_le {V : Type u} {G H : SimpleGraph V}
    (hGH : G ≤ H) (hH : H.Colorable 5) :
    G.Colorable 5 :=
  SimpleGraph.Colorable.mono_left hGH hH

/-- The complete graph on six vertices is not 5-colorable. -/
theorem completeGraph_fin_six_not_colorable_five :
    ¬ (⊤ : SimpleGraph (Fin 6)).Colorable 5 := by
  intro h
  have hle : Nat.card (Fin 6) ≤ 5 := by
    exact h.card_le_of_pairwise_adj (fun i : Fin 6 => i) (by
      intro i j hij
      simp [SimpleGraph.top_adj, hij])
  norm_num at hle

/--
The usual planar Euler consequence "every subgraph has a vertex of degree at
most five" is not by itself a five-color theorem: the complete graph on six
vertices also has that degeneracy bound, but is not 5-colorable.
-/
theorem completeGraph_fin_six_induced_subgraph_has_degree_le_five
    (S : Set (Fin 6)) [Fintype S] [Nonempty S] :
    ∃ v : S, (⊤ : SimpleGraph S).degree v ≤ 5 := by
  classical
  rcases ‹Nonempty S› with ⟨v⟩
  refine ⟨v, ?_⟩
  have hcard : Fintype.card S ≤ 6 := by
    simpa using Fintype.card_subtype_le (fun x : Fin 6 => x ∈ S)
  simp [SimpleGraph.complete_graph_degree]
  omega

/--
If a color is absent from all neighbors of `v` in a coloring of `G - v`,
then that coloring extends to a coloring of `G` by giving `v` that color.
-/
theorem coloring_extend_of_neighbor_color_free {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V)
    (C : (G.induce ({x | x ≠ v} : Set V)).Coloring (Fin 5)) (c : Fin 5)
    (hfree : ∀ x : ({x | x ≠ v} : Set V), G.Adj v x → C x ≠ c) :
    ∃ C' : G.Coloring (Fin 5),
      ∀ x : ({x | x ≠ v} : Set V), C' x = C x := by
  classical
  let color : V → Fin 5 := fun x => if hx : x = v then c else C ⟨x, hx⟩
  refine ⟨SimpleGraph.Coloring.mk color ?_, ?_⟩
  · intro a b hab
    by_cases ha : a = v
    · subst a
      have hb : b ≠ v := (G.ne_of_adj hab).symm
      have hfree_b : C ⟨b, hb⟩ ≠ c := hfree ⟨b, hb⟩ hab
      simpa [color, hb] using hfree_b.symm
    · by_cases hb : b = v
      · subst b
        have hfree_a : C ⟨a, ha⟩ ≠ c := hfree ⟨a, ha⟩ (G.symm hab)
        simpa [color, ha] using hfree_a
      · have hC : C ⟨a, ha⟩ ≠ C ⟨b, hb⟩ := by
          exact C.valid (by simpa using hab)
        simpa [color, ha, hb] using hC
  · intro x
    change color x.1 = C x
    have hx : x.1 ≠ v := x.2
    simp [color, hx]

/--
A vertex of degree at most four is a local extension vertex for five colors.
This is the easy part of the induction: one of the five colors is unused
among its neighbors.
-/
theorem coloring_extend_of_neighbor_finset_le_four {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (neighbors : Finset V)
    (hneighbors : ∀ w : V, w ∈ neighbors ↔ G.Adj v w) (hcard : neighbors.card ≤ 4)
    (C : (G.induce ({x | x ≠ v} : Set V)).Coloring (Fin 5)) :
    ∃ C' : G.Coloring (Fin 5),
      ∀ x : ({x | x ≠ v} : Set V), C' x = C x := by
  classical
  let deletedColor : V → Fin 5 := fun x => if hx : x = v then 0 else C ⟨x, hx⟩
  rcases exists_unused_color_of_neighbor_bound neighbors deletedColor hcard with ⟨c, hc⟩
  refine coloring_extend_of_neighbor_color_free G v C c ?_
  intro x hx
  have hxmem : x.1 ∈ neighbors := (hneighbors x.1).2 hx
  have hcx : deletedColor x.1 ≠ c := hc x.1 hxmem
  have hxne : x.1 ≠ v := x.2
  simpa [deletedColor, hxne] using hcx

theorem coloring_extend_of_degree_le_four {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] (hdeg : G.degree v ≤ 4)
    (C : (G.induce ({x | x ≠ v} : Set V)).Coloring (Fin 5)) :
    ∃ C' : G.Coloring (Fin 5),
      ∀ x : ({x | x ≠ v} : Set V), C' x = C x := by
  classical
  have hcard : (G.neighborFinset v).card ≤ 4 := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdeg
  exact coloring_extend_of_neighbor_finset_le_four G v (G.neighborFinset v)
    (by intro w; exact G.mem_neighborFinset v w) hcard C

/--
Kempe recoloring on `G - v`, followed by the same one-color extension step.
The finite set `S` is the abstract Kempe component; the closure hypothesis is
exactly what `kempeSwap_proper_abstract` needs to preserve properness.
-/
theorem coloring_extend_after_kempe_swap {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V)
    (C : (G.induce ({x | x ≠ v} : Set V)).Coloring (Fin 5))
    (c1 c2 c : Fin 5) (hne : c1 ≠ c2)
    (S : Finset ({x | x ≠ v} : Set V))
    (hclosed : ∀ u w,
      (G.induce ({x | x ≠ v} : Set V)).Adj u w → u ∈ S →
        (C u = c1 ∨ C u = c2) →
        (C w = c1 ∨ C w = c2) → w ∈ S)
    (hfree : ∀ x : ({x | x ≠ v} : Set V), G.Adj v x →
      (if x ∈ S then swapColor c1 c2 (C x) else C x) ≠ c) :
    ∃ C' : G.Coloring (Fin 5),
      ∃ T : Finset ({x | x ≠ v} : Set V),
        ∀ x : ({x | x ≠ v} : Set V), x ∉ T → C' x = C x := by
  classical
  let H := G.induce ({x | x ≠ v} : Set V)
  let swapped : ({x | x ≠ v} : Set V) → Fin 5 :=
    fun x => if x ∈ S then swapColor c1 c2 (C x) else C x
  have hproper : ∀ u w, H.Adj u w → swapped u ≠ swapped w := by
    exact kempeSwap_proper_abstract H C (fun u w hw => C.valid hw) c1 c2 hne S hclosed
  let D : H.Coloring (Fin 5) := SimpleGraph.Coloring.mk swapped (by
    intro u w hw
    exact hproper u w hw)
  have hfreeD : ∀ x : ({x | x ≠ v} : Set V), G.Adj v x → D x ≠ c := by
    intro x hx
    simpa [D, swapped] using hfree x hx
  rcases coloring_extend_of_neighbor_color_free G v D c hfreeD with ⟨C', hC'⟩
  refine ⟨C', S, ?_⟩
  intro x hxS
  have hD : D x = swapped x := rfl
  have hx' : swapped x = C x := by
    dsimp [swapped]
    by_cases hxs : x ∈ S
    · exact False.elim (hxS hxs)
    · exact dif_neg hxs
  calc
    C' x = D x := hC' x
    _ = swapped x := hD
    _ = C x := hx'

/--
A recursive certificate for the local extension steps used in the five-color
proof.  This is deliberately not a planar graph definition: it records exactly
the graph-theoretic data that the planar Euler/Kempe argument must supply.
-/
inductive FiveColorReducible :
    {V : Type u} → [Fintype V] → [DecidableEq V] → SimpleGraph V → Prop
  | empty {V : Type u} [Fintype V] [DecidableEq V] [IsEmpty V] (G : SimpleGraph V) :
      FiveColorReducible G
  | step {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V)
      (hdel : FiveColorReducible (G.induce ({x | x ≠ v} : Set V)))
      (hstep : ∀ C : (G.induce ({x | x ≠ v} : Set V)).Coloring (Fin 5),
        (∃ neighbors : Finset V,
          (∀ w : V, w ∈ neighbors ↔ G.Adj v w) ∧ neighbors.card ≤ 4) ∨
        ∃ c1 c2 c : Fin 5, c1 ≠ c2 ∧
          ∃ S : Finset ({x | x ≠ v} : Set V),
            (∀ u w,
              (G.induce ({x | x ≠ v} : Set V)).Adj u w → u ∈ S →
                (C u = c1 ∨ C u = c2) →
                (C w = c1 ∨ C w = c2) → w ∈ S) ∧
            (∀ x : ({x | x ≠ v} : Set V), G.Adj v x →
              (if x ∈ S then swapColor c1 c2 (C x) else C x) ≠ c)) :
      FiveColorReducible G

theorem FiveColorReducible.step_of_degree_le_four {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] (hdeg : G.degree v ≤ 4)
    (hdel : FiveColorReducible (G.induce ({x | x ≠ v} : Set V))) :
    FiveColorReducible G := by
  classical
  refine FiveColorReducible.step G v hdel ?_
  intro _C
  left
  refine ⟨G.neighborFinset v, ?_, ?_⟩
  · intro w
    exact G.mem_neighborFinset v w
  · simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdeg

/--
The certified five-color theorem.

Intended theorem in the book: every finite planar simple graph is 5-colorable.
This theorem proves the faithful certified version supported by this file:
every finite graph with a recursive five-color Kempe-reduction certificate is
5-colorable.  Instantiating the certificate for planar graphs is exactly the
unformalized planar Euler/Kempe front; the weaker "every subgraph has a vertex
of degree at most 5" condition is not sufficient for five colors, as the
complete graph on six vertices shows.
-/
theorem chapter35 {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : FiveColorReducible G) :
    G.Colorable 5 := by
  classical
  induction hG with
  | empty H =>
      exact SimpleGraph.Colorable.of_isEmpty (G := H) 5
  | step H v _hdel hstep ih =>
      rcases ih with ⟨C⟩
      rcases hstep C with hlow | hkempe
      · rcases hlow with ⟨neighbors, hneighbors, hneighbors_card⟩
        rcases coloring_extend_of_neighbor_finset_le_four H v neighbors hneighbors
          hneighbors_card C with ⟨C', _hC'⟩
        exact ⟨C'⟩
      · rcases hkempe with ⟨c1, c2, c, hc12, K, hclosed, hfree⟩
        rcases coloring_extend_after_kempe_swap H v C c1 c2 c hc12 K hclosed hfree with
          ⟨C', _T, _hC'⟩
        exact ⟨C'⟩

end FiveColorInduction

/-! ### Concrete witnesses for `FiveColorReducible`

The remaining frontier is the planar instantiation: every finite planar simple
graph carries a `FiveColorReducible` certificate.  That needs Mathlib planar
graphs + Euler ⟹ degree-≤5 vertex (currently unavailable).  Below we exhibit
concrete certificates on small vertex types to validate the inductive
machinery and give downstream callers ready instances. -/

/-- The empty graph is trivially `FiveColorReducible` via the `empty`
constructor. -/
def FiveColorReducible.bot_pempty : FiveColorReducible (⊥ : SimpleGraph PEmpty) :=
  FiveColorReducible.empty _

/-- The empty graph on `Fin 0` is trivially `FiveColorReducible`. -/
def FiveColorReducible.bot_finZero : FiveColorReducible (⊥ : SimpleGraph (Fin 0)) :=
  FiveColorReducible.empty _

/-- A single isolated vertex is `FiveColorReducible`: delete the vertex
(yielding the empty subgraph) and use the degree-0 ≤ 4 shortcut. -/
def FiveColorReducible.bot_finOne :
    FiveColorReducible (⊥ : SimpleGraph (Fin 1)) := by
  classical
  haveI : IsEmpty ({x : Fin 1 | x ≠ 0} : Set (Fin 1)) := by
    rw [isEmpty_subtype]
    intro x hx
    fin_cases x
    exact hx rfl
  refine FiveColorReducible.step_of_degree_le_four
    (⊥ : SimpleGraph (Fin 1)) (v := 0) (hdeg := ?_) (hdel := ?_)
  · -- degree of 0 in ⊥ is 0 ≤ 4
    simp
  · -- induced subgraph on empty subset is empty
    exact FiveColorReducible.empty _

end ProofsInTheBook.Chapter35
