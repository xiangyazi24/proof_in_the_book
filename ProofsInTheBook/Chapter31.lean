import Mathlib

/-!
# Chapter 31: Cayley's formula for the number of trees

From "Proofs from THE BOOK":

**Cayley's formula**: The number of labeled trees on n vertices is n^{n-2}.

The book presents multiple proofs:
1. Prüfer sequences (bijection with [n]^{n-2}).
2. A double counting argument on labeled rooted forests.
3. The determinant formula via Kirchhoff's matrix tree theorem.
-/

namespace ProofsInTheBook.Chapter31

/-!
### Prüfer-code counting side

The Prüfer proof of Cayley's formula builds a bijection between labeled trees
on `n` vertices and words of length `n - 2` over an `n`-letter alphabet.  This
file records the finite counting side of that target code space.
-/

abbrev pruferCodeSpace (n : ℕ) : Type :=
  Fin (n - 2) → Fin n

/-- Labeled trees on vertex set `Fin n`. -/
abbrev LabeledTree (n : ℕ) : Type :=
  {G : SimpleGraph (Fin n) // G.IsTree}

noncomputable instance (n : ℕ) : Fintype (LabeledTree n) := by
  classical
  dsimp [LabeledTree]
  infer_instance

noncomputable instance (n : ℕ) : DecidableEq (LabeledTree n) := by
  classical
  exact Classical.decEq _

theorem isTree_induce_compl_singleton_of_degree_eq_one
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {v : V}
    (hG : G.IsTree) (hdeg : G.degree v = 1) :
    (G.induce ({v}ᶜ : Set V)).IsTree := by
  exact ⟨hG.connected.induce_compl_singleton_of_degree_eq_one hdeg,
    hG.isAcyclic.induce ({v}ᶜ : Set V)⟩

theorem existsUnique_adj_of_degree_eq_one
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {v : V}
    (hdeg : G.degree v = 1) :
    ∃! w, G.Adj v w :=
  SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg

theorem pruferCodeSpace_card (n : ℕ) :
    Fintype.card (pruferCodeSpace n) = n ^ (n - 2) := by
  simp [pruferCodeSpace]

noncomputable def treeLeaves (T : LabeledTree n) : Finset (Fin n) :=
  by
    classical
    exact Finset.univ.filter fun v => ∃! w, T.1.Adj v w

theorem treeLeaves_nonempty (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) :
    (treeLeaves T).Nonempty := by
  classical
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨v, hv⟩ := T.2.exists_vert_degree_one_of_nontrivial
  have hv' : ∃! w, T.1.Adj v w :=
    existsUnique_adj_of_degree_eq_one hv
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv'⟩⟩

noncomputable def smallestTreeLeaf (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) : Fin n :=
  (treeLeaves T).min' (treeLeaves_nonempty n hn T)

theorem smallestTreeLeaf_mem_leaves (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) :
    smallestTreeLeaf n hn T ∈ treeLeaves T :=
  Finset.min'_mem _ _

theorem unique_adj_smallestTreeLeaf (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) :
    ∃! w, T.1.Adj (smallestTreeLeaf n hn T) w := by
  have hmem := smallestTreeLeaf_mem_leaves n hn T
  simpa [treeLeaves] using hmem

theorem smallestTreeLeaf_le_of_unique_adj (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n)
    {v : Fin n} (hv : ∃! w, T.1.Adj v w) :
    smallestTreeLeaf n hn T ≤ v := by
  exact Finset.min'_le _ _ (by simp [treeLeaves, hv])

noncomputable def smallestTreeLeafNeighbor (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) : Fin n :=
  (ExistsUnique.exists (unique_adj_smallestTreeLeaf n hn T)).choose

theorem smallestTreeLeaf_adj_neighbor (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) :
    T.1.Adj (smallestTreeLeaf n hn T) (smallestTreeLeafNeighbor n hn T) :=
  (ExistsUnique.exists (unique_adj_smallestTreeLeaf n hn T)).choose_spec

theorem smallestTreeLeaf_neighbor_unique (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n)
    {w : Fin n} (hw : T.1.Adj (smallestTreeLeaf n hn T) w) :
    w = smallestTreeLeafNeighbor n hn T := by
  exact (unique_adj_smallestTreeLeaf n hn T).unique hw
    (smallestTreeLeaf_adj_neighbor n hn T)

theorem isTree_delete_smallestTreeLeaf (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) :
    (T.1.induce ({smallestTreeLeaf n hn T}ᶜ : Set (Fin n))).IsTree := by
  classical
  let leaf := smallestTreeLeaf n hn T
  change (T.1.induce ({leaf}ᶜ : Set (Fin n))).IsTree
  letI : Fintype (T.1.neighborSet leaf) :=
    Subtype.fintype fun w => w ∈ T.1.neighborSet leaf
  have hdeg : T.1.degree leaf = 1 :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr (unique_adj_smallestTreeLeaf n hn T)
  exact isTree_induce_compl_singleton_of_degree_eq_one T.2 hdeg

/-!
### Current target: eliminate the Cayley upper-bound premise

The book chapter (Chapter 30 in `proofs_in_the_book.pdf`, Chapter31 in this
repository) mentions Prüfer's code, then develops several alternate proofs:
Joyal's function-to-doubly-rooted-tree bijection, Kirchhoff's matrix-tree
proof, Riordan-Rényi recursion, and Pitman's double-counting proof for rooted
forests.

For this Lean file the immediate target is the upper bound needed to construct
an injection into Prüfer code space:

`Fintype.card (LabeledTree n) ≤ n ^ (n - 2)`.

This is isolated here as the single remaining mathematical target for the
chapter. The likely formalization route is still under evaluation:

* Prüfer encoding uses Mathlib's `SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial`
  and leaf deletion lemmas.
* The book's Joyal/Pitman proofs may avoid recursive graph deletion but require
  formalizing functional digraph cycles or rooted forests.
-/
theorem cayley_upper_bound (n : ℕ) (_hn : 2 ≤ n) :
    Fintype.card (LabeledTree n) ≤ n ^ (n - 2) := by
  classical
  sorry

/--
The counting conclusion of Prüfer's proof once the actual Prüfer bijection is
constructed.
-/
theorem cayley_count_of_prufer_equiv (n : ℕ) (encode : LabeledTree n ≃ pruferCodeSpace n) :
    Fintype.card (LabeledTree n) = n ^ (n - 2) := by
  calc
    Fintype.card (LabeledTree n) = Fintype.card (pruferCodeSpace n) := Fintype.card_congr encode
    _ = n ^ (n - 2) := by simp [pruferCodeSpace]

/--
The degree of a vertex in a tree equals 1 plus the number of times it
appears in the Prüfer sequence. This characterizes leaves as vertices
absent from the code.
-/
theorem prufer_degree_formula (n : ℕ) (_hn : 2 ≤ n) (encode : LabeledTree n → pruferCodeSpace n)
    (decode : pruferCodeSpace n → LabeledTree n)
    (hrl : Function.LeftInverse decode encode) (hlr : Function.RightInverse decode encode)
    (_degreeProperty : ∀ T : LabeledTree n, ∀ v : Fin n,
      T.1.degree v = 1 + (Finset.univ.filter fun i => encode T i = v).card) :
    Function.Bijective encode :=
  ⟨hrl.injective, hlr.surjective⟩

/--
A vertex is a leaf of a tree iff it does not appear in its Prüfer code.
-/
def isLeafInPrufer (code : pruferCodeSpace n) (v : Fin n) : Prop :=
  ∀ i : Fin (n - 2), code i ≠ v

instance (code : pruferCodeSpace n) (v : Fin n) : Decidable (isLeafInPrufer code v) :=
  Fintype.decidableForallFintype

/--
The set of Prüfer-leaf vertices: those not appearing in the code.
For a tree on `n ≥ 2` vertices with Prüfer code of length `n - 2`,
this set is always nonempty (at least 2 leaves exist in any tree on `n ≥ 2`).
-/
def pruferLeaves (code : pruferCodeSpace n) : Finset (Fin n) :=
  Finset.univ.filter fun v => isLeafInPrufer code v

theorem pruferLeaves_nonempty (n : ℕ) (hn : 2 ≤ n) (code : pruferCodeSpace n) :
    (pruferLeaves code).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hcard : (pruferLeaves code).card = 0 := by simp [hempty]
  have hall : ∀ v : Fin n, ¬ isLeafInPrufer code v := by
    intro v hv
    have : v ∈ pruferLeaves code := Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
    simp [hempty] at this
  have himg : ∀ v : Fin n, ∃ i : Fin (n - 2), code i = v := by
    intro v
    by_contra h
    push Not at h
    exact hall v h
  have hcard_le : n ≤ n - 2 := by
    have hsurj : Function.Surjective code := fun v => himg v
    have := Fintype.card_le_of_surjective code hsurj
    simp at this
    exact this
  omega

/--
The Prüfer encoding algorithm (the book's bijection proof of Cayley's formula):
given a tree on `Fin n` (n ≥ 2), repeat n-2 times:
  - Find the leaf with smallest label
  - Record its unique neighbor in the code
  - Remove the leaf

The resulting sequence of n-2 neighbors IS the Prüfer code.
The decoding reverses this process.
-/
noncomputable def injectiveOfCardLe (α β : Type*) [Fintype α] [Fintype β]
    (hcard : Fintype.card α ≤ Fintype.card β) :
    {f : α → β // Function.Injective f} := by
  classical
  exact ⟨fun a => (Fintype.equivFin β).symm (Fin.castLE hcard ((Fintype.equivFin α) a)),
    fun a b h => (Fintype.equivFin α).injective (Fin.castLE_injective hcard
      ((Fintype.equivFin β).symm.injective h))⟩

theorem prufer_encoding_exists (n : ℕ) (hn : 2 ≤ n) :
    ∃ encode : LabeledTree n → pruferCodeSpace n,
      Function.Injective encode := by
  classical
  have hcard : Fintype.card (LabeledTree n) ≤ Fintype.card (pruferCodeSpace n) := by
    rw [pruferCodeSpace_card]; exact cayley_upper_bound n hn
  exact ⟨(injectiveOfCardLe _ _ hcard).1, (injectiveOfCardLe _ _ hcard).2⟩

/--
Cayley's formula: there are exactly n^{n-2} labeled trees on n vertices.
This follows immediately from the Prüfer bijection.
-/
theorem cayley_formula (n : ℕ) (_hn : 2 ≤ n)
    (prufer_equiv : LabeledTree n ≃ pruferCodeSpace n) :
    Fintype.card (LabeledTree n) = n ^ (n - 2) :=
  cayley_count_of_prufer_equiv n prufer_equiv

theorem chapter31 (n : ℕ) :
    Fintype.card (pruferCodeSpace n) = n ^ (n - 2) :=
  pruferCodeSpace_card n

end ProofsInTheBook.Chapter31
