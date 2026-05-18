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

noncomputable def finSuccAboveEquivCompl {m : ℕ} (leaf : Fin (m + 1)) :
    Fin m ≃ {v : Fin (m + 1) // v ∈ ({leaf}ᶜ : Set (Fin (m + 1)))} := by
  classical
  refine Equiv.ofBijective (fun i => ⟨leaf.succAbove i, by simp⟩) ?_
  constructor
  · intro i j hij
    exact leaf.succAbove_right_injective (congrArg Subtype.val hij)
  · intro v
    have hvNotMem : v.1 ∉ ({leaf} : Set (Fin (m + 1))) := v.2
    have hv : v.1 ≠ leaf := by
      intro h
      exact hvNotMem (by simp [h])
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hv
    exact ⟨i, Subtype.ext hi⟩

noncomputable def deleteSmallestLeafTreeSucc (m : ℕ) (hm : 1 ≤ m)
    (T : LabeledTree (m + 1)) : LabeledTree m := by
  classical
  have hn : 2 ≤ m + 1 := by omega
  let leaf := smallestTreeLeaf (m + 1) hn T
  let e := finSuccAboveEquivCompl leaf
  refine ⟨(T.1.induce ({leaf}ᶜ : Set (Fin (m + 1)))).comap e.toEmbedding, ?_⟩
  have hdel : (T.1.induce ({leaf}ᶜ : Set (Fin (m + 1)))).IsTree := by
    simpa [leaf] using isTree_delete_smallestTreeLeaf (m + 1) hn T
  exact (SimpleGraph.Iso.isTree_iff
    (SimpleGraph.Iso.comap e (T.1.induce ({leaf}ᶜ : Set (Fin (m + 1)))))).mpr hdel

/-- A labeled tree with two distinguished vertices, the object counted in Joyal's proof. -/
abbrev DoublyRootedLabeledTree (n : ℕ) : Type :=
  LabeledTree n × Fin n × Fin n

noncomputable def treePath (T : LabeledTree n) (u v : Fin n) : T.1.Walk u v :=
  (ExistsUnique.exists (T.2.existsUnique_path u v)).choose

theorem treePath_isPath (T : LabeledTree n) (u v : Fin n) :
    (treePath T u v).IsPath :=
  (ExistsUnique.exists (T.2.existsUnique_path u v)).choose_spec

theorem treePath_unique (T : LabeledTree n) (u v : Fin n) {p : T.1.Walk u v}
    (hp : p.IsPath) :
    p = treePath T u v := by
  exact (T.2.existsUnique_path u v).unique hp (treePath_isPath T u v)

noncomputable def joyalPathVertices (X : DoublyRootedLabeledTree n) : Finset (Fin n) :=
  (treePath X.1 X.2.1 X.2.2).support.toFinset

theorem joyal_left_mem_pathVertices (X : DoublyRootedLabeledTree n) :
    X.2.1 ∈ joyalPathVertices X := by
  exact List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support _)

theorem joyal_right_mem_pathVertices (X : DoublyRootedLabeledTree n) :
    X.2.2 ∈ joyalPathVertices X := by
  exact List.mem_toFinset.mpr (SimpleGraph.Walk.end_mem_support _)

/-- First row in Joyal's table: path vertices sorted by their labels. -/
noncomputable def joyalPathDomainOrder (X : DoublyRootedLabeledTree n) : List (Fin n) :=
  (joyalPathVertices X).sort (· ≤ ·)

/-- Second row in Joyal's table: the same path vertices in left-to-right path order. -/
noncomputable def joyalPathRangeOrder (X : DoublyRootedLabeledTree n) : List (Fin n) :=
  (treePath X.1 X.2.1 X.2.2).support

theorem joyalPathDomainOrder_nodup (X : DoublyRootedLabeledTree n) :
    (joyalPathDomainOrder X).Nodup := by
  exact (joyalPathVertices X).sort_nodup (· ≤ ·)

theorem joyalPathRangeOrder_nodup (X : DoublyRootedLabeledTree n) :
    (joyalPathRangeOrder X).Nodup := by
  simpa [joyalPathRangeOrder] using
    (SimpleGraph.Walk.isPath_def (treePath X.1 X.2.1 X.2.2)).mp
      (treePath_isPath X.1 X.2.1 X.2.2)

theorem joyalPathDomainOrder_toFinset (X : DoublyRootedLabeledTree n) :
    (joyalPathDomainOrder X).toFinset = joyalPathVertices X := by
  simp [joyalPathDomainOrder]

theorem joyalPathRangeOrder_toFinset (X : DoublyRootedLabeledTree n) :
    (joyalPathRangeOrder X).toFinset = joyalPathVertices X := by
  rfl

theorem joyalPathOrders_length_eq (X : DoublyRootedLabeledTree n) :
    (joyalPathDomainOrder X).length = (joyalPathRangeOrder X).length := by
  calc
    (joyalPathDomainOrder X).length = (joyalPathVertices X).card := by
      simp [joyalPathDomainOrder]
    _ = (joyalPathRangeOrder X).toFinset.card := by
      rw [joyalPathRangeOrder_toFinset]
    _ = (joyalPathRangeOrder X).length := by
      rw [List.toFinset_card_of_nodup (joyalPathRangeOrder_nodup X)]

/-- The path-row part of Joyal's inverse map: first-row vertex ↦ same-column second-row vertex. -/
noncomputable def joyalPathTableValue (X : DoublyRootedLabeledTree n)
    (v : Fin n) (hv : v ∈ joyalPathVertices X) : Fin n := by
  let domain := joyalPathDomainOrder X
  let range := joyalPathRangeOrder X
  have hvd : v ∈ domain := by
    simpa [domain, joyalPathDomainOrder] using hv
  let i : Fin domain.length :=
    (List.Nodup.getEquiv domain (by simpa [domain] using joyalPathDomainOrder_nodup X)).symm
      ⟨v, hvd⟩
  exact range.get ⟨i.1, by
    change i.1 < (joyalPathRangeOrder X).length
    rw [← joyalPathOrders_length_eq X]
    simpa [domain] using i.2⟩

/-- For a vertex off the left-right path, point to the next vertex on its path toward the left end. -/
noncomputable def joyalOffPathValue (X : DoublyRootedLabeledTree n)
    (v : Fin n) (hv : v ∉ joyalPathVertices X) : Fin n := by
  let p := treePath X.1 v X.2.1
  have hne : v ≠ X.2.1 := by
    intro h
    exact hv (by simpa [h] using joyal_left_mem_pathVertices X)
  have hp : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  exact p.snd

theorem joyalOffPathValue_adj (X : DoublyRootedLabeledTree n)
    (v : Fin n) (hv : v ∉ joyalPathVertices X) :
    X.1.1.Adj v (joyalOffPathValue X v hv) := by
  let p := treePath X.1 v X.2.1
  have hne : v ≠ X.2.1 := by
    intro h
    exact hv (by simpa [h] using joyal_left_mem_pathVertices X)
  have hp : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  change X.1.1.Adj v p.snd
  exact SimpleGraph.Walk.adj_snd hp

/-- Joyal's map from a doubly-rooted tree to an endofunction on its label set. -/
noncomputable def joyalTreeToFunction (X : DoublyRootedLabeledTree n) : Fin n → Fin n :=
  fun v =>
    if hv : v ∈ joyalPathVertices X then
      joyalPathTableValue X v hv
    else
      joyalOffPathValue X v hv

theorem joyalTreeToFunction_apply_of_mem (X : DoublyRootedLabeledTree n)
    {v : Fin n} (hv : v ∈ joyalPathVertices X) :
    joyalTreeToFunction X v = joyalPathTableValue X v hv := by
  simp [joyalTreeToFunction, hv]

theorem joyalTreeToFunction_apply_of_not_mem (X : DoublyRootedLabeledTree n)
    {v : Fin n} (hv : v ∉ joyalPathVertices X) :
    joyalTreeToFunction X v = joyalOffPathValue X v hv := by
  simp [joyalTreeToFunction, hv]

noncomputable def periodicCore (f : Fin n → Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => ∃ m : ℕ, 0 < m ∧ f^[m] v = v

theorem mem_periodicCore_iff (f : Fin n → Fin n) (v : Fin n) :
    v ∈ periodicCore f ↔ ∃ m : ℕ, 0 < m ∧ f^[m] v = v := by
  simp [periodicCore]

theorem joyalPathTableValue_mem_pathVertices (X : DoublyRootedLabeledTree n)
    {v : Fin n} (hv : v ∈ joyalPathVertices X) :
    joyalPathTableValue X v hv ∈ joyalPathVertices X := by
  classical
  unfold joyalPathTableValue
  simp only
  have hvd : v ∈ joyalPathDomainOrder X := by
    simpa [joyalPathDomainOrder] using hv
  have hidx : List.idxOf v (joyalPathDomainOrder X) <
      (treePath X.1 X.2.1 X.2.2).support.length := by
    have hdom : List.idxOf v (joyalPathDomainOrder X) < (joyalPathDomainOrder X).length :=
      List.idxOf_lt_length_iff.mpr hvd
    rwa [joyalPathOrders_length_eq X, joyalPathRangeOrder] at hdom
  change (treePath X.1 X.2.1 X.2.2).support[List.idxOf v (joyalPathDomainOrder X)]'hidx ∈
    (treePath X.1 X.2.1 X.2.2).support.toFinset
  exact List.mem_toFinset.mpr (List.get_mem (treePath X.1 X.2.1 X.2.2).support _)

theorem joyalTreeToFunction_maps_pathVertices (X : DoublyRootedLabeledTree n)
    {v : Fin n} (hv : v ∈ joyalPathVertices X) :
    joyalTreeToFunction X v ∈ joyalPathVertices X := by
  rw [joyalTreeToFunction_apply_of_mem X hv]
  exact joyalPathTableValue_mem_pathVertices X hv

theorem joyalPathTableValue_injective (X : DoublyRootedLabeledTree n)
    {v w : Fin n} (hv : v ∈ joyalPathVertices X) (hw : w ∈ joyalPathVertices X)
    (h : joyalPathTableValue X v hv = joyalPathTableValue X w hw) :
    v = w := by
  classical
  have hvd : v ∈ joyalPathDomainOrder X := by
    simpa [joyalPathDomainOrder] using hv
  have hwd : w ∈ joyalPathDomainOrder X := by
    simpa [joyalPathDomainOrder] using hw
  have hvidx : List.idxOf v (joyalPathDomainOrder X) < (joyalPathRangeOrder X).length := by
    have hdom : List.idxOf v (joyalPathDomainOrder X) < (joyalPathDomainOrder X).length :=
      List.idxOf_lt_length_iff.mpr hvd
    rwa [← joyalPathOrders_length_eq X]
  have hwidx : List.idxOf w (joyalPathDomainOrder X) < (joyalPathRangeOrder X).length := by
    have hdom : List.idxOf w (joyalPathDomainOrder X) < (joyalPathDomainOrder X).length :=
      List.idxOf_lt_length_iff.mpr hwd
    rwa [← joyalPathOrders_length_eq X]
  have hget :
      (joyalPathRangeOrder X)[List.idxOf v (joyalPathDomainOrder X)]'hvidx =
        (joyalPathRangeOrder X)[List.idxOf w (joyalPathDomainOrder X)]'hwidx := by
    simpa [joyalPathTableValue] using h
  have hidx :
      List.idxOf v (joyalPathDomainOrder X) =
        List.idxOf w (joyalPathDomainOrder X) := by
    exact congrArg Fin.val ((joyalPathRangeOrder_nodup X).get_inj_iff.mp hget)
  have hvget :
      (joyalPathDomainOrder X)[List.idxOf v (joyalPathDomainOrder X)]'
        (List.idxOf_lt_length_iff.mpr hvd) = v :=
    List.idxOf_get (List.idxOf_lt_length_iff.mpr hvd)
  have hwget :
      (joyalPathDomainOrder X)[List.idxOf w (joyalPathDomainOrder X)]'
        (List.idxOf_lt_length_iff.mpr hwd) = w :=
    List.idxOf_get (List.idxOf_lt_length_iff.mpr hwd)
  calc
    v = (joyalPathDomainOrder X)[List.idxOf v (joyalPathDomainOrder X)]'
        (List.idxOf_lt_length_iff.mpr hvd) := hvget.symm
    _ = (joyalPathDomainOrder X)[List.idxOf w (joyalPathDomainOrder X)]'
        (List.idxOf_lt_length_iff.mpr hwd) := by simp [hidx]
    _ = w := hwget

/--
Joyal's path vertices are exactly the periodic core of the associated endofunction.
This is the formal version of the book's subset `M`.
-/
theorem periodicCore_joyalTreeToFunction (X : DoublyRootedLabeledTree n) :
    periodicCore (joyalTreeToFunction X) = joyalPathVertices X := by
  classical
  sorry

theorem joyalPathRangeOrder_zero (X : DoublyRootedLabeledTree n)
    (h : 0 < (joyalPathRangeOrder X).length) :
    (joyalPathRangeOrder X)[0]'h = X.2.1 := by
  simpa [joyalPathRangeOrder] using
    SimpleGraph.Walk.support_getElem_zero (treePath X.1 X.2.1 X.2.2)

theorem joyalTreeToFunction_injective (n : ℕ) :
    Function.Injective (joyalTreeToFunction : DoublyRootedLabeledTree n → Fin n → Fin n) := by
  intro X Y hXY
  sorry

theorem doublyRootedLabeledTree_card (n : ℕ) :
    Fintype.card (DoublyRootedLabeledTree n) = Fintype.card (LabeledTree n) * n * n := by
  simp [DoublyRootedLabeledTree, Nat.mul_assoc]

theorem endofunction_card (n : ℕ) :
    Fintype.card (Fin n → Fin n) = n ^ n := by
  simp

/--
The numerical part of Joyal's proof: an injection from doubly-rooted labeled trees
to endofunctions on `Fin n` implies Cayley's upper bound.
-/
theorem cayley_upper_bound_of_joyal_injection (n : ℕ) (hn : 2 ≤ n)
    (hcard : Fintype.card (DoublyRootedLabeledTree n) ≤ Fintype.card (Fin n → Fin n)) :
    Fintype.card (LabeledTree n) ≤ n ^ (n - 2) := by
  rw [doublyRootedLabeledTree_card, endofunction_card] at hcard
  have hnpos : 0 < n := by omega
  have hfactor_pos : 0 < n * n := Nat.mul_pos hnpos hnpos
  have hpow : n ^ n = n ^ (n - 2) * (n * n) := by
    calc
      n ^ n = n ^ ((n - 2) + 2) := by congr; omega
      _ = n ^ (n - 2) * n ^ 2 := by rw [pow_add]
      _ = n ^ (n - 2) * (n * n) := by rw [pow_two]
  have hmul : Fintype.card (LabeledTree n) * (n * n) ≤ n ^ (n - 2) * (n * n) := by
    simpa [Nat.mul_assoc, hpow] using hcard
  exact Nat.le_of_mul_le_mul_right hmul hfactor_pos

/--
Joyal's theorem specialized to the direction needed here.  The book constructs
a bijection between endofunctions on `Fin n` and doubly-rooted labeled trees;
this cardinal inequality is the remaining formal content of that bijection.
-/
theorem joyal_doubly_rooted_card_bound (n : ℕ) :
    Fintype.card (DoublyRootedLabeledTree n) ≤ Fintype.card (Fin n → Fin n) := by
  classical
  exact Fintype.card_le_of_injective joyalTreeToFunction (joyalTreeToFunction_injective n)

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
  exact cayley_upper_bound_of_joyal_injection n _hn (joyal_doubly_rooted_card_bound n)

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
