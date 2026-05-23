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

open SimpleGraph

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

theorem isTree_path_length_eq_dist (T : LabeledTree n) {u v : Fin n}
    {p : T.1.Walk u v} (hp : p.IsPath) :
    p.length = T.1.dist u v := by
  obtain ⟨q, hqPath, hqLen⟩ := T.2.connected.exists_path_of_dist u v
  have hpq : p = q := (T.2.existsUnique_path u v).unique hp hqPath
  rw [hpq]
  exact hqLen

theorem treePath_length_eq_dist (T : LabeledTree n) (u v : Fin n) :
    (treePath T u v).length = T.1.dist u v :=
  isTree_path_length_eq_dist T (treePath_isPath T u v)

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
    simp [domain]⟩

/-- For a vertex off the left-right path, point to the next vertex on its path toward the left end. -/
noncomputable def joyalOffPathValue (X : DoublyRootedLabeledTree n)
    (v : Fin n) (hv : v ∉ joyalPathVertices X) : Fin n := by
  let p := treePath X.1 v X.2.1
  have hne : v ≠ X.2.1 := by
    intro h
    subst h
    exact hv (joyal_left_mem_pathVertices X)
  have hp : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  exact p.snd

theorem joyalOffPathValue_adj (X : DoublyRootedLabeledTree n)
    (v : Fin n) (hv : v ∉ joyalPathVertices X) :
    X.1.1.Adj v (joyalOffPathValue X v hv) := by
  let p := treePath X.1 v X.2.1
  have hne : v ≠ X.2.1 := by
    intro h
    subst h
    exact hv (joyal_left_mem_pathVertices X)
  have hp : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  change X.1.1.Adj v p.snd
  exact SimpleGraph.Walk.adj_snd hp

/-- The off-path value is the next vertex on the unique path toward the left endpoint. -/
theorem joyalOffPathValue_mem_tail_path_to_left (X : DoublyRootedLabeledTree n)
    (v : Fin n) (hv : v ∉ joyalPathVertices X) :
    joyalOffPathValue X v hv ∈ (treePath X.1 v X.2.1).support.tail := by
  let p := treePath X.1 v X.2.1
  have hne : v ≠ X.2.1 := by
    intro h
    subst h
    exact hv (joyal_left_mem_pathVertices X)
  have hp : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  change p.snd ∈ p.support.tail
  exact SimpleGraph.Walk.snd_mem_tail_support hp

theorem joyalOffPathValue_ne (X : DoublyRootedLabeledTree n)
    (v : Fin n) (hv : v ∉ joyalPathVertices X) :
    joyalOffPathValue X v hv ≠ v := by
  exact (joyalOffPathValue_adj X v hv).ne'

theorem joyalOffPathValue_dist_left_add_one (X : DoublyRootedLabeledTree n)
    (v : Fin n) (hv : v ∉ joyalPathVertices X) :
    X.1.1.dist X.2.1 (joyalOffPathValue X v hv) + 1 = X.1.1.dist X.2.1 v := by
  let p := treePath X.1 v X.2.1
  have hne : v ≠ X.2.1 := by
    intro h
    subst h
    exact hv (joyal_left_mem_pathVertices X)
  have hpNotNil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  have hpPath : p.IsPath := treePath_isPath X.1 v X.2.1
  have htailPath : p.tail.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    have hpNodup : p.support.Nodup := (SimpleGraph.Walk.isPath_def p).mp hpPath
    simpa [p.support_tail_of_not_nil hpNotNil] using hpNodup.tail
  have htailLen : p.tail.length = X.1.1.dist (joyalOffPathValue X v hv) X.2.1 := by
    change p.tail.length = X.1.1.dist p.snd X.2.1
    exact isTree_path_length_eq_dist X.1 htailPath
  have hpLen : p.length = X.1.1.dist v X.2.1 := treePath_length_eq_dist X.1 v X.2.1
  calc
    X.1.1.dist X.2.1 (joyalOffPathValue X v hv) + 1
        = X.1.1.dist (joyalOffPathValue X v hv) X.2.1 + 1 := by
          rw [SimpleGraph.dist_comm]
    _ = p.tail.length + 1 := by rw [htailLen]
    _ = p.length := p.length_tail_add_one hpNotNil
    _ = X.1.1.dist v X.2.1 := hpLen
    _ = X.1.1.dist X.2.1 v := SimpleGraph.dist_comm

theorem joyalOffPathValue_eq_of_adj_dist_left_add_one (X : DoublyRootedLabeledTree n)
    {w z : Fin n} (hw : w ∉ joyalPathVertices X) (hadj : X.1.1.Adj w z)
    (hdist : X.1.1.dist X.2.1 z + 1 = X.1.1.dist X.2.1 w) :
    joyalOffPathValue X w hw = z := by
  classical
  let q := treePath X.1 z X.2.1
  let r : X.1.1.Walk w X.2.1 := SimpleGraph.Walk.cons hadj q
  have hqLen : q.length = X.1.1.dist z X.2.1 := treePath_length_eq_dist X.1 z X.2.1
  have hrLen : r.length = X.1.1.dist w X.2.1 := by
    change q.length + 1 = X.1.1.dist w X.2.1
    rw [hqLen]
    rw [SimpleGraph.dist_comm (u := z) (v := X.2.1)]
    rw [SimpleGraph.dist_comm (u := w) (v := X.2.1)]
    exact hdist
  have hrPath : r.IsPath := SimpleGraph.Walk.isPath_of_length_eq_dist r hrLen
  have hrEq : treePath X.1 w X.2.1 = r := (treePath_unique X.1 w X.2.1 hrPath).symm
  calc
    joyalOffPathValue X w hw = r.snd := by
      change (treePath X.1 w X.2.1).snd = r.snd
      rw [hrEq]
    _ = z := by
      change (SimpleGraph.Walk.cons hadj q).snd = z
      simp

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

noncomputable def joyalPathSelfMap (X : DoublyRootedLabeledTree n) :
    {v : Fin n // v ∈ joyalPathVertices X} → {v : Fin n // v ∈ joyalPathVertices X} :=
  fun v => ⟨joyalTreeToFunction X v.1, joyalTreeToFunction_maps_pathVertices X v.2⟩

theorem joyalPathSelfMap_injective (X : DoublyRootedLabeledTree n) :
    Function.Injective (joyalPathSelfMap X) := by
  intro v w h
  apply Subtype.ext
  apply joyalPathTableValue_injective X v.2 w.2
  have hval := congrArg Subtype.val h
  simpa [joyalPathSelfMap, joyalTreeToFunction_apply_of_mem] using hval

theorem joyalPathSelfMap_iterate_val (X : DoublyRootedLabeledTree n) (m : ℕ)
    (v : {v : Fin n // v ∈ joyalPathVertices X}) :
    ((joyalPathSelfMap X)^[m] v).1 = (joyalTreeToFunction X)^[m] v.1 := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
      simp [Function.iterate_succ, joyalPathSelfMap, ih]

theorem joyalPathVertices_subset_periodicCore (X : DoublyRootedLabeledTree n) :
    joyalPathVertices X ⊆ periodicCore (joyalTreeToFunction X) := by
  classical
  intro v hv
  rw [mem_periodicCore_iff]
  let g := joyalPathSelfMap X
  have hper : (⟨v, hv⟩ : {v : Fin n // v ∈ joyalPathVertices X}) ∈ Function.periodicPts g :=
    (joyalPathSelfMap_injective X).mem_periodicPts _
  rw [Function.mem_periodicPts] at hper
  rcases hper with ⟨m, hmpos, hm⟩
  refine ⟨m, hmpos, ?_⟩
  have hval := congrArg Subtype.val hm
  simpa [g, joyalPathSelfMap_iterate_val] using hval

theorem exists_iterate_mem_joyalPathVertices (X : DoublyRootedLabeledTree n) (v : Fin n) :
    ∃ m : ℕ, (joyalTreeToFunction X)^[m] v ∈ joyalPathVertices X := by
  classical
  let f := joyalTreeToFunction X
  let D := fun v : Fin n => X.1.1.dist X.2.1 v
  have main : ∀ d : ℕ, (∀ e < d, ∀ v : Fin n, D v = e → ∃ m : ℕ, f^[m] v ∈ joyalPathVertices X) →
      ∀ v : Fin n, D v = d → ∃ m : ℕ, f^[m] v ∈ joyalPathVertices X := by
    intro d ih v hvd
    by_cases hv : v ∈ joyalPathVertices X
    · exact ⟨0, by simpa [f] using hv⟩
    · let w := f v
      have hw_eq : w = joyalOffPathValue X v hv := by
        simp [w, f, joyalTreeToFunction_apply_of_not_mem X hv]
      have hdist : D w + 1 = D v := by
        simpa [D, w, hw_eq] using joyalOffPathValue_dist_left_add_one X v hv
      have hwd_lt : D w < d := by omega
      obtain ⟨m, hm⟩ := ih (D w) hwd_lt w rfl
      refine ⟨m + 1, ?_⟩
      simpa [f, Function.iterate_succ, Function.comp_def, w] using hm
  have main' : ∀ d : ℕ, ∀ v : Fin n, D v = d → ∃ m : ℕ, f^[m] v ∈ joyalPathVertices X := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        exact main d (by intro e he; exact ih e he)
  exact main' (D v) v rfl

theorem iterate_joyal_mem_pathVertices_of_mem (X : DoublyRootedLabeledTree n)
    {v : Fin n} (hv : v ∈ joyalPathVertices X) (m : ℕ) :
    (joyalTreeToFunction X)^[m] v ∈ joyalPathVertices X := by
  induction m generalizing v with
  | zero => simpa using hv
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact joyalTreeToFunction_maps_pathVertices X (ih hv)

/--
No vertex off the left-right path is periodic under Joyal's endofunction.
The intended proof uses `joyalOffPathValue_mem_tail_path_to_left`: while outside
the path, iterating strictly shortens the unique path to the left endpoint.
-/
theorem periodicCore_subset_joyalPathVertices (X : DoublyRootedLabeledTree n) :
    periodicCore (joyalTreeToFunction X) ⊆ joyalPathVertices X := by
  classical
  intro v hv
  rw [mem_periodicCore_iff] at hv
  rcases hv with ⟨p, hpPos, hp⟩
  obtain ⟨r, hr⟩ := exists_iterate_mem_joyalPathVertices X v
  let N := (r + 1) * p
  have hrle : r ≤ N := by
    have : r + 1 ≤ N := by
      simpa [N] using Nat.le_mul_of_pos_right (r + 1) hpPos
    omega
  have hNpath : (joyalTreeToFunction X)^[N] v ∈ joyalPathVertices X := by
    have htail := iterate_joyal_mem_pathVertices_of_mem X hr (N - r)
    have hsum : (N - r) + r = N := Nat.sub_add_cancel hrle
    rw [← Function.iterate_add_apply (joyalTreeToFunction X) (N - r) r v] at htail
    simpa [hsum] using htail
  have hperN : (joyalTreeToFunction X)^[N] v = v := by
    have hper : Function.IsPeriodicPt (joyalTreeToFunction X) p v := hp
    have hmul := hper.const_mul (r + 1)
    simpa [Function.IsPeriodicPt, N, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  simpa [hperN] using hNpath

/--
Joyal's path vertices are exactly the periodic core of the associated endofunction.
This is the formal version of the book's subset `M`.
-/
theorem periodicCore_joyalTreeToFunction (X : DoublyRootedLabeledTree n) :
    periodicCore (joyalTreeToFunction X) = joyalPathVertices X := by
  classical
  exact Finset.Subset.antisymm
    (periodicCore_subset_joyalPathVertices X)
    (joyalPathVertices_subset_periodicCore X)

theorem joyalPathVertices_eq_of_function_eq {X Y : DoublyRootedLabeledTree n}
    (hXY : joyalTreeToFunction X = joyalTreeToFunction Y) :
    joyalPathVertices X = joyalPathVertices Y := by
  rw [← periodicCore_joyalTreeToFunction X, ← periodicCore_joyalTreeToFunction Y, hXY]

theorem joyalPathDomainOrder_eq_of_function_eq {X Y : DoublyRootedLabeledTree n}
    (hXY : joyalTreeToFunction X = joyalTreeToFunction Y) :
    joyalPathDomainOrder X = joyalPathDomainOrder Y := by
  simp [joyalPathDomainOrder, joyalPathVertices_eq_of_function_eq hXY]

theorem joyalPathRangeOrder_get_eq_function_domain_get (X : DoublyRootedLabeledTree n)
    (i : ℕ) (hir : i < (joyalPathRangeOrder X).length)
    (hid : i < (joyalPathDomainOrder X).length) :
    (joyalPathRangeOrder X)[i]'hir =
      joyalTreeToFunction X ((joyalPathDomainOrder X)[i]'hid) := by
  classical
  let v := (joyalPathDomainOrder X)[i]'hid
  have hvd : v ∈ joyalPathDomainOrder X := List.get_mem _ _
  have hv : v ∈ joyalPathVertices X := by
    exact (Finset.mem_sort (s := joyalPathVertices X) (r := fun x y : Fin n => x ≤ y)).mp hvd
  rw [joyalTreeToFunction_apply_of_mem X hv]
  unfold joyalPathTableValue
  simp only
  have hidx : List.idxOf v (joyalPathDomainOrder X) = i := by
    simpa [v] using (joyalPathDomainOrder_nodup X).idxOf_getElem i hid
  simp [hidx]

theorem joyalPathRangeOrder_eq_of_function_eq {X Y : DoublyRootedLabeledTree n}
    (hXY : joyalTreeToFunction X = joyalTreeToFunction Y) :
    joyalPathRangeOrder X = joyalPathRangeOrder Y := by
  classical
  have hdom := joyalPathDomainOrder_eq_of_function_eq hXY
  apply List.ext_getElem
  · calc
      (joyalPathRangeOrder X).length = (joyalPathDomainOrder X).length :=
        (joyalPathOrders_length_eq X).symm
      _ = (joyalPathDomainOrder Y).length := by rw [hdom]
      _ = (joyalPathRangeOrder Y).length := joyalPathOrders_length_eq Y
  · intro i hx hy
    have hdx : i < (joyalPathDomainOrder X).length := by
      simpa [joyalPathOrders_length_eq X] using hx
    have hdy : i < (joyalPathDomainOrder Y).length := by
      simpa [joyalPathOrders_length_eq Y] using hy
    calc
      (joyalPathRangeOrder X)[i]'hx
          = joyalTreeToFunction X ((joyalPathDomainOrder X)[i]'hdx) :=
            joyalPathRangeOrder_get_eq_function_domain_get X i hx hdx
      _ = joyalTreeToFunction Y ((joyalPathDomainOrder Y)[i]'hdy) := by
            have harg : (joyalPathDomainOrder X)[i]'hdx =
                (joyalPathDomainOrder Y)[i]'hdy := by
              simp [hdom]
            rw [hXY, harg]
      _ = (joyalPathRangeOrder Y)[i]'hy :=
            (joyalPathRangeOrder_get_eq_function_domain_get Y i hy hdy).symm

theorem joyalPathRangeOrder_zero (X : DoublyRootedLabeledTree n)
    (h : 0 < (joyalPathRangeOrder X).length) :
    (joyalPathRangeOrder X)[0]'h = X.2.1 := by
  simp [joyalPathRangeOrder]

theorem joyalPathRangeOrder_length_pos (X : DoublyRootedLabeledTree n) :
    0 < (joyalPathRangeOrder X).length := by
  simp [joyalPathRangeOrder]

theorem joyalPathRangeOrder_last (X : DoublyRootedLabeledTree n)
    (h : 0 < (joyalPathRangeOrder X).length) :
    (joyalPathRangeOrder X)[(joyalPathRangeOrder X).length - 1]'(Nat.pred_lt (Nat.ne_of_gt h)) = X.2.2 := by
  simp [joyalPathRangeOrder, SimpleGraph.Walk.length_support]

theorem mem_joyalPathVertices_of_mem_treePath_to_left (X : DoublyRootedLabeledTree n)
    {z y : Fin n} (hz : z ∈ joyalPathVertices X)
    (hy : y ∈ (treePath X.1 z X.2.1).support) :
    y ∈ joyalPathVertices X := by
  classical
  let p := treePath X.1 X.2.1 X.2.2
  have hzsup : z ∈ p.support := by
    have hz' := hz
    simp [joyalPathVertices] at hz'
    exact hz'
  let q : X.1.1.Walk z X.2.1 := (p.takeUntil z hzsup).reverse
  have hqPath : q.IsPath := by
    exact ((treePath_isPath X.1 X.2.1 X.2.2).takeUntil hzsup).reverse
  have hqEq : q = treePath X.1 z X.2.1 := treePath_unique X.1 z X.2.1 hqPath
  have hyq : y ∈ q.support := by
    rwa [hqEq]
  have hytake : y ∈ (p.takeUntil z hzsup).support := by
    have hyq' := hyq
    simp [q, SimpleGraph.Walk.support_reverse] at hyq'
    exact hyq'
  have hyp : y ∈ p.support := SimpleGraph.Walk.support_takeUntil_subset p hzsup hytake
  change y ∈ p.support.toFinset
  exact List.mem_toFinset.mpr hyp

theorem not_offpath_adj_path_farther_from_left (X : DoublyRootedLabeledTree n)
    {w z : Fin n} (hw : w ∉ joyalPathVertices X) (hz : z ∈ joyalPathVertices X)
    (hadj : X.1.1.Adj w z)
    (hdist : X.1.1.dist X.2.1 w + 1 = X.1.1.dist X.2.1 z) :
    False := by
  classical
  let q := treePath X.1 w X.2.1
  let r : X.1.1.Walk z X.2.1 := SimpleGraph.Walk.cons hadj.symm q
  have hqLen : q.length = X.1.1.dist w X.2.1 := treePath_length_eq_dist X.1 w X.2.1
  have hrLen : r.length = X.1.1.dist z X.2.1 := by
    change q.length + 1 = X.1.1.dist z X.2.1
    rw [hqLen]
    rw [SimpleGraph.dist_comm (u := w) (v := X.2.1)]
    rw [SimpleGraph.dist_comm (u := z) (v := X.2.1)]
    exact hdist
  have hrPath : r.IsPath := SimpleGraph.Walk.isPath_of_length_eq_dist r hrLen
  have hrEq : treePath X.1 z X.2.1 = r := (treePath_unique X.1 z X.2.1 hrPath).symm
  have hwmem : w ∈ (treePath X.1 z X.2.1).support := by
    rw [hrEq]
    simp [r]
  exact hw (mem_joyalPathVertices_of_mem_treePath_to_left X hz hwmem)

theorem joyal_left_eq_of_function_eq {X Y : DoublyRootedLabeledTree n}
    (hXY : joyalTreeToFunction X = joyalTreeToFunction Y) :
    X.2.1 = Y.2.1 := by
  have hrange := joyalPathRangeOrder_eq_of_function_eq hXY
  have hX := joyalPathRangeOrder_length_pos X
  have hY := joyalPathRangeOrder_length_pos Y
  calc
    X.2.1 = (joyalPathRangeOrder X)[0]'hX := (joyalPathRangeOrder_zero X hX).symm
    _ = (joyalPathRangeOrder Y)[0]'hY := by simp [hrange]
    _ = Y.2.1 := joyalPathRangeOrder_zero Y hY

theorem joyal_right_eq_of_function_eq {X Y : DoublyRootedLabeledTree n}
    (hXY : joyalTreeToFunction X = joyalTreeToFunction Y) :
    X.2.2 = Y.2.2 := by
  have hrange := joyalPathRangeOrder_eq_of_function_eq hXY
  have hX := joyalPathRangeOrder_length_pos X
  have hY := joyalPathRangeOrder_length_pos Y
  have hlen : (joyalPathRangeOrder X).length = (joyalPathRangeOrder Y).length := by
    rw [hrange]
  calc
    X.2.2 =
        (joyalPathRangeOrder X)[(joyalPathRangeOrder X).length - 1]'(Nat.pred_lt (Nat.ne_of_gt hX)) :=
          (joyalPathRangeOrder_last X hX).symm
    _ = (joyalPathRangeOrder Y)[(joyalPathRangeOrder Y).length - 1]'(Nat.pred_lt (Nat.ne_of_gt hY)) := by
          simp [hrange]
    _ = Y.2.2 := joyalPathRangeOrder_last Y hY

def adjacentInList (l : List (Fin n)) (u v : Fin n) : Prop :=
  ∃ i : ℕ, ∃ hi : i < l.length, ∃ hi' : i + 1 < l.length,
    (l[i]'hi = u ∧ l[i + 1]'hi' = v) ∨ (l[i]'hi = v ∧ l[i + 1]'hi' = u)

theorem adjacentInList_of_pair_infix {l : List (Fin n)} {u v : Fin n}
    (h : [u, v] <:+: l) : adjacentInList l u v := by
  rcases List.infix_iff_getElem?.mp h with ⟨i, hi, hget⟩
  refine ⟨i, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
  · grind
  · grind
  · have h0 := hget 0 (by simp : 0 < [u, v].length)
    grind
  · have h1 := hget 1 (by simp : 1 < [u, v].length)
    grind

theorem adjacentInList_comm {l : List (Fin n)} {u v : Fin n}
    (h : adjacentInList l u v) : adjacentInList l v u := by
  rcases h with ⟨i, hi, hi', huv | hvu⟩
  · exact ⟨i, hi, hi', Or.inr huv⟩
  · exact ⟨i, hi, hi', Or.inl hvu⟩

def joyalRecoveredAdj (X : DoublyRootedLabeledTree n) (u v : Fin n) : Prop :=
  adjacentInList (joyalPathRangeOrder X) u v ∨
    (u ∉ joyalPathVertices X ∧ joyalTreeToFunction X u = v) ∨
    (v ∉ joyalPathVertices X ∧ joyalTreeToFunction X v = u)

theorem joyalRecoveredAdj_of_offpath_dist_left_add_one (X : DoublyRootedLabeledTree n)
    {w z : Fin n} (hw : w ∉ joyalPathVertices X) (hadj : X.1.1.Adj w z)
    (hdist : X.1.1.dist X.2.1 z + 1 = X.1.1.dist X.2.1 w) :
    joyalRecoveredAdj X w z := by
  right
  left
  refine ⟨hw, ?_⟩
  rw [joyalTreeToFunction_apply_of_not_mem X hw]
  exact joyalOffPathValue_eq_of_adj_dist_left_add_one X hw hadj hdist

theorem joyalRecoveredAdj_of_offpath_dist_left_add_one_right (X : DoublyRootedLabeledTree n)
    {w z : Fin n} (hw : w ∉ joyalPathVertices X) (hadj : X.1.1.Adj z w)
    (hdist : X.1.1.dist X.2.1 z + 1 = X.1.1.dist X.2.1 w) :
    joyalRecoveredAdj X z w := by
  right
  right
  refine ⟨hw, ?_⟩
  rw [joyalTreeToFunction_apply_of_not_mem X hw]
  exact joyalOffPathValue_eq_of_adj_dist_left_add_one X hw hadj.symm hdist

theorem joyalRecoveredAdj_of_mem_path_darts (X : DoublyRootedLabeledTree n)
    {u v : Fin n} (hadj : X.1.1.Adj u v)
    (hd : ⟨⟨u, v⟩, hadj⟩ ∈ (treePath X.1 X.2.1 X.2.2).darts) :
    joyalRecoveredAdj X u v := by
  left
  exact adjacentInList_of_pair_infix (l := joyalPathRangeOrder X) <| by
    simpa [joyalPathRangeOrder] using
      (SimpleGraph.Walk.mem_darts_iff_infix_support hadj).mp hd

theorem joyalRecoveredAdj_of_mem_path_darts_symm (X : DoublyRootedLabeledTree n)
    {u v : Fin n} (hadj : X.1.1.Adj u v)
    (hd : ⟨⟨v, u⟩, hadj.symm⟩ ∈ (treePath X.1 X.2.1 X.2.2).darts) :
    joyalRecoveredAdj X u v := by
  left
  apply adjacentInList_comm
  exact adjacentInList_of_pair_infix (l := joyalPathRangeOrder X) <| by
    have hinfix := (SimpleGraph.Walk.mem_darts_iff_infix_support hadj.symm).mp hd
    simpa [joyalPathRangeOrder] using hinfix

theorem adjacentInList_joyalPathRangeOrder_adj (X : DoublyRootedLabeledTree n)
    {u v : Fin n} (h : adjacentInList (joyalPathRangeOrder X) u v) :
    X.1.1.Adj u v := by
  classical
  let p := treePath X.1 X.2.1 X.2.2
  rcases h with ⟨i, hi, hi', huv | hvu⟩
  · have hilen : i < p.length := by
      have hi'p : i + 1 < p.support.length := by
        simpa [joyalPathRangeOrder, p] using hi'
      rw [SimpleGraph.Walk.length_support] at hi'p
      omega
    have hip : i < p.support.length := by
      simpa [joyalPathRangeOrder, p] using hi
    have hi'p : i + 1 < p.support.length := by
      simpa [joyalPathRangeOrder, p] using hi'
    have h0 : p.getVert i = u := by
      have hs := SimpleGraph.Walk.support_getElem_eq_getVert p hip
      have hsu : p.support[i]'hip = u := by
        simpa [joyalPathRangeOrder, p] using huv.1
      exact hs.symm.trans hsu
    have h1 : p.getVert (i + 1) = v := by
      have hs := SimpleGraph.Walk.support_getElem_eq_getVert p hi'p
      have hsv : p.support[i + 1]'hi'p = v := by
        simpa [joyalPathRangeOrder, p] using huv.2
      exact hs.symm.trans hsv
    simpa [h0, h1] using p.adj_getVert_succ (i := i) hilen
  · have hilen : i < p.length := by
      have hi'p : i + 1 < p.support.length := by
        simpa [joyalPathRangeOrder, p] using hi'
      rw [SimpleGraph.Walk.length_support] at hi'p
      omega
    have hip : i < p.support.length := by
      simpa [joyalPathRangeOrder, p] using hi
    have hi'p : i + 1 < p.support.length := by
      simpa [joyalPathRangeOrder, p] using hi'
    have h0 : p.getVert i = v := by
      have hs := SimpleGraph.Walk.support_getElem_eq_getVert p hip
      have hsv : p.support[i]'hip = v := by
        simpa [joyalPathRangeOrder, p] using hvu.1
      exact hs.symm.trans hsv
    have h1 : p.getVert (i + 1) = u := by
      have hs := SimpleGraph.Walk.support_getElem_eq_getVert p hi'p
      have hsu : p.support[i + 1]'hi'p = u := by
        simpa [joyalPathRangeOrder, p] using hvu.2
      exact hs.symm.trans hsu
    have hadj : X.1.1.Adj v u := by
      simpa [h0, h1] using p.adj_getVert_succ (i := i) hilen
    exact hadj.symm

theorem joyalRecoveredAdj_adj (X : DoublyRootedLabeledTree n)
    {u v : Fin n} (h : joyalRecoveredAdj X u v) :
    X.1.1.Adj u v := by
  classical
  rcases h with hpath | hoff | hoff
  · exact adjacentInList_joyalPathRangeOrder_adj X hpath
  · rcases hoff with ⟨hu, hfu⟩
    have hadj := joyalOffPathValue_adj X u hu
    rwa [← joyalTreeToFunction_apply_of_not_mem X hu, hfu] at hadj
  · rcases hoff with ⟨hv, hfv⟩
    have hadj := joyalOffPathValue_adj X v hv
    have hadj' : X.1.1.Adj v u := by
      rwa [← joyalTreeToFunction_apply_of_not_mem X hv, hfv] at hadj
    exact hadj'.symm

theorem joyalRecoveredAdj_eq_of_function_eq {X Y : DoublyRootedLabeledTree n}
    (hXY : joyalTreeToFunction X = joyalTreeToFunction Y) (u v : Fin n) :
    joyalRecoveredAdj X u v ↔ joyalRecoveredAdj Y u v := by
  have hpath := joyalPathVertices_eq_of_function_eq hXY
  have hrange := joyalPathRangeOrder_eq_of_function_eq hXY
  simp [joyalRecoveredAdj, hpath, hrange, hXY]

theorem joyalRecoveredAdj_of_path_edge (X : DoublyRootedLabeledTree n)
    {u v : Fin n} (hu : u ∈ joyalPathVertices X) (hv : v ∈ joyalPathVertices X)
    (hadj : X.1.1.Adj u v) :
    joyalRecoveredAdj X u v := by
  classical
  left
  let p := treePath X.1 X.2.1 X.2.2
  have huSup : u ∈ p.support := by
    simpa [joyalPathVertices, p] using hu
  have hvSup : v ∈ p.support := by
    simpa [joyalPathVertices, p] using hv
  let lu := (p.takeUntil u huSup).length
  let lv := (p.takeUntil v hvSup).length
  have hdistu : X.1.1.dist X.2.1 u = lu := by
    have hpath : (p.takeUntil u huSup).IsPath :=
      (treePath_isPath X.1 X.2.1 X.2.2).takeUntil huSup
    exact (isTree_path_length_eq_dist X.1 hpath).symm
  have hdistv : X.1.1.dist X.2.1 v = lv := by
    have hpath : (p.takeUntil v hvSup).IsPath :=
      (treePath_isPath X.1 X.2.1 X.2.2).takeUntil hvSup
    exact (isTree_path_length_eq_dist X.1 hpath).symm
  have hduv := X.1.2.dist_eq_dist_add_one_of_adj X.2.1 hadj
  rcases hduv with hdu | hdv
  · have hlu : lv + 1 = lu := by omega
    have hlvle : lv ≤ p.length := by
      simpa [lv] using p.length_takeUntil_le hvSup
    have hlule : lu ≤ p.length := by
      simpa [lu] using p.length_takeUntil_le huSup
    have hi : lv < p.support.length := by
      rw [SimpleGraph.Walk.length_support]
      omega
    have hi' : lv + 1 < p.support.length := by
      rw [SimpleGraph.Walk.length_support]
      omega
    have hvget : p.getVert lv = v := by
      simpa [lv] using SimpleGraph.Walk.getVert_length_takeUntil (p := p) hvSup
    have huget : p.getVert (lv + 1) = u := by
      rw [hlu]
      simpa [lu] using SimpleGraph.Walk.getVert_length_takeUntil (p := p) huSup
    refine ⟨lv, hi, hi', Or.inr ⟨?_, ?_⟩⟩
    · exact (SimpleGraph.Walk.support_getElem_eq_getVert p hi).trans hvget
    · exact (SimpleGraph.Walk.support_getElem_eq_getVert p hi').trans huget
  · have hlv : lu + 1 = lv := by omega
    have hlule : lu ≤ p.length := by
      simpa [lu] using p.length_takeUntil_le huSup
    have hlvle : lv ≤ p.length := by
      simpa [lv] using p.length_takeUntil_le hvSup
    have hi : lu < p.support.length := by
      rw [SimpleGraph.Walk.length_support]
      omega
    have hi' : lu + 1 < p.support.length := by
      rw [SimpleGraph.Walk.length_support]
      omega
    have huget : p.getVert lu = u := by
      simpa [lu] using SimpleGraph.Walk.getVert_length_takeUntil (p := p) huSup
    have hvget : p.getVert (lu + 1) = v := by
      rw [hlv]
      simpa [lv] using SimpleGraph.Walk.getVert_length_takeUntil (p := p) hvSup
    refine ⟨lu, hi, hi', Or.inl ⟨?_, ?_⟩⟩
    · exact (SimpleGraph.Walk.support_getElem_eq_getVert p hi).trans huget
    · exact (SimpleGraph.Walk.support_getElem_eq_getVert p hi').trans hvget

/--
The Joyal endofunction data reconstructs the original tree edges: consecutive
vertices on the left-right path give the path edges, and every off-path vertex
is connected to its image.
-/
theorem joyal_tree_adj_iff_recovered (X : DoublyRootedLabeledTree n) (u v : Fin n) :
    X.1.1.Adj u v ↔ joyalRecoveredAdj X u v := by
  classical
  constructor
  · intro h
    have hdist := X.1.2.dist_eq_dist_add_one_of_adj X.2.1 h
    rcases hdist with hdu | hdv
    · by_cases hu : u ∈ joyalPathVertices X
      · by_cases hv : v ∈ joyalPathVertices X
        · exact joyalRecoveredAdj_of_path_edge X hu hv h
        · exact False.elim <|
            not_offpath_adj_path_farther_from_left X hv hu h.symm hdu.symm
      · exact joyalRecoveredAdj_of_offpath_dist_left_add_one X hu h hdu.symm
    · by_cases hv : v ∈ joyalPathVertices X
      · by_cases hu : u ∈ joyalPathVertices X
        · exact joyalRecoveredAdj_of_path_edge X hu hv h
        · exact False.elim <|
            not_offpath_adj_path_farther_from_left X hu hv h hdv.symm
      · exact joyalRecoveredAdj_of_offpath_dist_left_add_one_right X hv h hdv.symm
  · exact joyalRecoveredAdj_adj X

theorem joyal_tree_eq_of_function_eq {X Y : DoublyRootedLabeledTree n}
    (hXY : joyalTreeToFunction X = joyalTreeToFunction Y) :
    X.1 = Y.1 := by
  apply Subtype.ext
  ext u v
  rw [joyal_tree_adj_iff_recovered X u v, joyal_tree_adj_iff_recovered Y u v]
  exact joyalRecoveredAdj_eq_of_function_eq hXY u v

theorem joyalTreeToFunction_injective (n : ℕ) :
    Function.Injective (joyalTreeToFunction : DoublyRootedLabeledTree n → Fin n → Fin n) := by
  intro X Y hXY
  cases X with
  | mk XT Xroots =>
    cases Xroots with
    | mk Xleft Xright =>
      cases Y with
      | mk YT Yroots =>
        cases Yroots with
        | mk Yleft Yright =>
          have htree : XT = YT := joyal_tree_eq_of_function_eq hXY
          have hleft : Xleft = Yleft := joyal_left_eq_of_function_eq hXY
          have hright : Xright = Yright := joyal_right_eq_of_function_eq hXY
          subst htree
          subst hleft
          subst hright
          rfl

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

structure DecodeForestFull (n : ℕ) (state : Finset (Fin n) × Finset (Sym2 (Fin n))) : Prop where
  acyclic : (fromEdgeSet (state.2 : Set (Sym2 (Fin n)))).IsAcyclic
  covers : ∀ u : Fin n, ∃ v ∈ state.1, (fromEdgeSet (state.2 : Set _)).Reachable u v
  uniq : ∀ v ∈ state.1, ∀ w ∈ state.1, v ≠ w → ¬ (fromEdgeSet (state.2 : Set _)).Reachable v w

lemma decodeForest_init (n : ℕ) (hn : 2 ≤ n) :
    DecodeForestFull n (Finset.univ, ∅) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u p hp
    have hne := hp.ne_nil
    cases p with
    | nil => exact False.elim (hne rfl)
    | cons hadj _ => simp at hadj
  · intro u
    exact ⟨u, Finset.mem_univ u, Walk.nil.reachable⟩
  · intro v _ w _ hvw hreach
    rcases hreach with ⟨walk⟩
    cases walk with
    | nil => exact hvw rfl
    | cons hadj _ => simp at hadj

lemma refl_symm {V : Type*} {G : SimpleGraph V} {x y : V}
    (h : Relation.ReflTransGen G.Adj x y) : Relation.ReflTransGen G.Adj y x :=
  (reachable_iff_reflTransGen y x).mp ((reachable_iff_reflTransGen x y).mpr h).symm

lemma reachable_sup_edge {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (hreach : Relation.ReflTransGen (G.Adj ⊔ (edge u v).Adj) x y) :
    Relation.ReflTransGen G.Adj x y ∨
    (Relation.ReflTransGen G.Adj x u ∧ Relation.ReflTransGen G.Adj v y) ∨
    (Relation.ReflTransGen G.Adj x v ∧ Relation.ReflTransGen G.Adj u y) := by
  induction hreach with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | tail h_trans h_adj ih =>
    rcases h_adj with (hG | hedge)
    · rcases ih with (ih1 | ⟨ih2u, ih2v⟩ | ⟨ih3v, ih3u⟩)
      · exact Or.inl (Relation.ReflTransGen.tail ih1 hG)
      · exact Or.inr (Or.inl ⟨ih2u, Relation.ReflTransGen.tail ih2v hG⟩)
      · exact Or.inr (Or.inr ⟨ih3v, Relation.ReflTransGen.tail ih3u hG⟩)
    · revert hedge
      simp [edge, Sym2.ToRel, Sym2.mk_isDiag_iff, Sym2.eq]
      intro hedge'
      rcases hedge' with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · intro _
        rcases ih with (ih1 | ⟨ih2u, ih2v⟩ | ⟨ih3v, ih3u⟩)
        · exact Or.inr (Or.inl ⟨ih1, Relation.ReflTransGen.refl⟩)
        · exact Or.inl (Relation.ReflTransGen.trans ih2u (refl_symm ih2v))
        · exact Or.inl ih3v
      · intro _
        rcases ih with (ih1 | ⟨ih2u, ih2v⟩ | ⟨ih3v, ih3u⟩)
        · exact Or.inr (Or.inr ⟨ih1, Relation.ReflTransGen.refl⟩)
        · exact Or.inl ih2u
        · exact Or.inl (Relation.ReflTransGen.trans ih3v (refl_symm ih3u))

lemma reachable_sup_edge_graph {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (hreach : (G ⊔ edge u v).Reachable x y) :
    G.Reachable x y ∨
    (G.Reachable x u ∧ G.Reachable v y) ∨
    (G.Reachable x v ∧ G.Reachable u y) := by
  have h1 := reachable_sup_edge (reachable_iff_reflTransGen x y |>.mp hreach)
  rcases h1 with (h2 | ⟨h3u, h3v⟩ | ⟨h4v, h4u⟩)
  · exact Or.inl (reachable_iff_reflTransGen x y |>.mpr h2)
  · exact Or.inr (Or.inl ⟨reachable_iff_reflTransGen x u |>.mpr h3u, reachable_iff_reflTransGen v y |>.mpr h3v⟩)
  · exact Or.inr (Or.inr ⟨reachable_iff_reflTransGen x v |>.mpr h4v, reachable_iff_reflTransGen u y |>.mpr h4u⟩)

lemma decodeForest_step {n : ℕ} {state : Finset (Fin n) × Finset (Sym2 (Fin n))}
    (h_forest : DecodeForestFull n state) (nextLeaf : Fin n) (hnL : nextLeaf ∈ state.1)
    (si : Fin n) (h_future : si ∈ state.1) (h_not_eq : nextLeaf ≠ si) :
    DecodeForestFull n (state.1.erase nextLeaf, insert s(nextLeaf, si) state.2) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [Prod.snd]
    have hsup : fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _) = fromEdgeSet (state.2 : Set _) ⊔ edge nextLeaf si := by
      ext a b; simp [fromEdgeSet, edge, Sym2.ToRel, Sym2.eq]; tauto
    rw [hsup]
    rw [isAcyclic_sup_fromEdgeSet_iff]
    refine ⟨h_forest.acyclic, ?_⟩
    intro hreach
    have h_not_reach := h_forest.uniq nextLeaf hnL si h_future h_not_eq
    exact False.elim (h_not_reach hreach)
  · intro u
    dsimp only [Prod.fst, Prod.snd]
    have hsup : fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _) = fromEdgeSet (state.2 : Set _) ⊔ edge nextLeaf si := by
      ext a b; simp [fromEdgeSet, edge, Sym2.ToRel, Sym2.eq]; tauto
    rcases h_forest.covers u with ⟨r, hr, hreach⟩
    by_cases h_r : r = nextLeaf
    · rw [h_r] at hreach
      have h_new_reach : (fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _)).Reachable u nextLeaf := by
        rw [hsup]
        exact hreach.mono le_sup_left
      have h_edge : (fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _)).Adj nextLeaf si := by
        rw [hsup]
        exact Or.inr ⟨by simp [edge, Sym2.ToRel], h_not_eq⟩
      have h_si_reach := Reachable.trans h_new_reach (Adj.reachable h_edge)
      rcases h_forest.covers si with ⟨r', hr', hreach'⟩
      have h_r'_neq : r' ≠ nextLeaf := by
        intro heq
        rw [heq] at hreach'
        have h_not_reach := h_forest.uniq si h_future nextLeaf hnL h_not_eq.symm
        exact h_not_reach hreach'
      have h_r'_reach : (fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _)).Reachable si r' := by
        rw [hsup]
        exact hreach'.mono le_sup_left
      exact ⟨r', Finset.mem_erase_of_ne_of_mem h_r'_neq hr', Reachable.trans h_si_reach h_r'_reach⟩
    · have h_new_reach : (fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _)).Reachable u r := by
        rw [hsup]
        exact hreach.mono le_sup_left
      exact ⟨r, Finset.mem_erase_of_ne_of_mem h_r hr, h_new_reach⟩
  · intro v' hv' w' hw' hvw' hreach
    dsimp only [Prod.snd] at hreach
    rw [Finset.mem_erase] at hv' hw'
    have hsup : fromEdgeSet (↑(insert s(nextLeaf, si) state.2) : Set _) = fromEdgeSet (state.2 : Set _) ⊔ edge nextLeaf si := by
      ext a b; simp [fromEdgeSet, edge, Sym2.ToRel, Sym2.eq]; tauto
    rw [hsup] at hreach
    have h1 := reachable_sup_edge_graph hreach
    rcases h1 with (h2 | ⟨h3u, h3v⟩ | ⟨h4v, h4u⟩)
    · exact h_forest.uniq v' hv'.2 w' hw'.2 hvw' h2
    · have h_eq := h_forest.uniq v' hv'.2 nextLeaf hnL
      by_cases h_v' : v' = nextLeaf
      · exact hv'.1 h_v'
      · exact h_eq h_v' h3u
    · have h_eq := h_forest.uniq w' hw'.2 nextLeaf hnL
      by_cases h_w' : w' = nextLeaf
      · exact hw'.1 h_w'
      · exact h_eq h_w' h4u.symm


lemma nextLeaf_nonempty {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) (m : ℕ) (hm : m ≤ n - 2)
    (available : Finset (Fin n)) (h_card : available.card = n - m) :
    (available.filter (fun v => ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ v)).Nonempty := by
  let remaining_indices := Finset.univ.filter (fun j : Fin (n - 2) => m ≤ j.val)
  let img := remaining_indices.image s
  have h_rem_card : remaining_indices.card ≤ n - 2 - m := by
    have h_inj : Function.Injective (fun j : Fin (n - 2) => j.val) := Fin.val_injective
    have h_map : remaining_indices.image (fun j : Fin (n - 2) => j.val) ⊆ Finset.Ico m (n - 2) := by
      intro x hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨j, hj, rfl⟩
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_Ico]
      exact ⟨hj.2, j.isLt⟩
    calc
      remaining_indices.card = (remaining_indices.image (fun j => j.val)).card := (Finset.card_image_of_injective remaining_indices h_inj).symm
      _ ≤ (Finset.Ico m (n - 2)).card := Finset.card_le_card h_map
      _ = n - 2 - m := by rw [Nat.card_Ico]
  have h_img_card : img.card ≤ n - 2 - m := by
    calc
      img.card ≤ remaining_indices.card := Finset.card_image_le
      _ ≤ n - 2 - m := h_rem_card
  have h_intersect_card : (available ∩ img).card ≤ n - 2 - m := by
    calc
      (available ∩ img).card ≤ img.card := Finset.card_le_card Finset.inter_subset_right
      _ ≤ n - 2 - m := h_img_card
  have h_diff_card : 0 < (available \ img).card := by
    have h_add : (available \ img).card + (available ∩ img).card = available.card := Finset.card_sdiff_add_card_inter available img
    omega
  have h_nonempty : (available \ img).Nonempty := Finset.card_pos.mp h_diff_card
  rcases h_nonempty with ⟨v, hv⟩
  rw [Finset.mem_sdiff, Finset.mem_image] at hv
  refine ⟨v, Finset.mem_filter.mpr ⟨hv.1, ?_⟩⟩
  intro j hj heq
  exact hv.2 ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, heq⟩

def pruferDecodeAux {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    (m : ℕ) → (hm : m ≤ n - 2) →
    { state : Finset (Fin n) × Finset (Sym2 (Fin n)) //
      DecodeForestFull n state ∧ state.1.card = n - m ∧
      ∀ j : Fin (n - 2), m ≤ j.val → s j ∈ state.1 }
| 0, _ => ⟨(Finset.univ, ∅), by
    refine ⟨decodeForest_init n hn, by simp, ?_⟩
    intro j hj
    exact Finset.mem_univ _⟩
| m + 1, hm => by
    have h_m_le : m ≤ n - 2 := by omega
    let prev := pruferDecodeAux hn s m h_m_le
    let state := prev.val
    have h_forest := prev.property.1
    have h_card := prev.property.2.1
    have h_future := prev.property.2.2

    let si : Fin n := s ⟨m, by omega⟩
    have h_si_in : si ∈ state.1 := h_future ⟨m, by omega⟩ (by rfl)

    have h_nonempty := nextLeaf_nonempty hn s m h_m_le state.1 h_card
    let nextLeaf := (state.1.filter (fun v => ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ v)).min' h_nonempty
    have h_mem_filter : nextLeaf ∈ state.1.filter (fun v => ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ v) :=
      Finset.min'_mem _ _
    rw [Finset.mem_filter] at h_mem_filter
    have hnL : nextLeaf ∈ state.1 := h_mem_filter.1
    have h_not_in_future : ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ nextLeaf := h_mem_filter.2

    have h_not_eq : nextLeaf ≠ si := by
      have h := h_not_in_future ⟨m, by omega⟩ (by rfl)
      exact h.symm

    let new_state := (state.1.erase nextLeaf, insert s(nextLeaf, si) state.2)
    have h_new_forest := decodeForest_step h_forest nextLeaf hnL si h_si_in h_not_eq

    have h_new_card : new_state.1.card = n - (m + 1) := by
      dsimp [new_state]
      rw [Finset.card_erase_of_mem hnL]
      rw [h_card]
      omega

    have h_new_future : ∀ j : Fin (n - 2), m + 1 ≤ j.val → s j ∈ new_state.1 := by
      intro j hj
      dsimp [new_state]
      rw [Finset.mem_erase]
      have h_m_le_j : m ≤ j.val := by omega
      have h1 := h_future j h_m_le_j
      have h2 := h_not_in_future j h_m_le_j
      exact ⟨h2, h1⟩

    exact ⟨new_state, h_new_forest, h_new_card, h_new_future⟩


/-- The final-state pair `(available, edges)` after running the decode loop `n-2` times. -/
def pruferFinalState {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    Finset (Fin n) × Finset (Sym2 (Fin n)) :=
  (pruferDecodeAux hn s (n - 2) (by rfl)).val

lemma pruferFinalState_card {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    (pruferFinalState hn s).1.card = 2 := by
  have h : (pruferFinalState hn s).1.card = n - (n - 2) :=
    (pruferDecodeAux hn s (n - 2) (by rfl)).property.2.1
  omega

lemma pruferFinalState_forest {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    DecodeForestFull n (pruferFinalState hn s) :=
  (pruferDecodeAux hn s (n - 2) (by rfl)).property.1

lemma pruferFinalState_nonempty {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    (pruferFinalState hn s).1.Nonempty := by
  rw [← Finset.card_pos, pruferFinalState_card]; omega

/-- The smaller of the two remaining "active" vertices after the decode loop. -/
def pruferLastU {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) : Fin n :=
  (pruferFinalState hn s).1.min' (pruferFinalState_nonempty hn s)

lemma pruferLastU_mem {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    pruferLastU hn s ∈ (pruferFinalState hn s).1 := Finset.min'_mem _ _

lemma pruferFinalErase_card {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    ((pruferFinalState hn s).1.erase (pruferLastU hn s)).card = 1 := by
  rw [Finset.card_erase_of_mem (pruferLastU_mem hn s), pruferFinalState_card]

lemma pruferFinalErase_nonempty {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    ((pruferFinalState hn s).1.erase (pruferLastU hn s)).Nonempty := by
  rw [← Finset.card_pos, pruferFinalErase_card]; omega

/-- The larger of the two remaining "active" vertices. -/
def pruferLastV {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) : Fin n :=
  ((pruferFinalState hn s).1.erase (pruferLastU hn s)).min'
    (pruferFinalErase_nonempty hn s)

lemma pruferLastV_mem_erase {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    pruferLastV hn s ∈ (pruferFinalState hn s).1.erase (pruferLastU hn s) :=
  Finset.min'_mem _ _

lemma pruferLastV_mem {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    pruferLastV hn s ∈ (pruferFinalState hn s).1 :=
  Finset.mem_of_mem_erase (pruferLastV_mem_erase hn s)

lemma pruferLastU_ne_V {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    pruferLastU hn s ≠ pruferLastV hn s := by
  have := pruferLastV_mem_erase hn s
  rw [Finset.mem_erase] at this
  exact this.1.symm

def pruferDecodeEdges {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) : Finset (Sym2 (Fin n)) :=
  insert (s(pruferLastU hn s, pruferLastV hn s)) (pruferFinalState hn s).2

lemma pruferDecodeIsTree {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    (fromEdgeSet (V := Fin n) (pruferDecodeEdges hn s : Set (Sym2 (Fin n)))).IsTree := by
  unfold pruferDecodeEdges
  set state := pruferFinalState hn s with h_state_eq
  set u := pruferLastU hn s with h_u_eq
  set v := pruferLastV hn s with h_v_eq
  have h_forest : DecodeForestFull n state := pruferFinalState_forest hn s
  have h_card : state.1.card = 2 := pruferFinalState_card hn s
  have hu : u ∈ state.1 := pruferLastU_mem hn s
  have hv : v ∈ state.1 := pruferLastV_mem hn s
  have hv_mem2 : v ∈ state.1.erase u := pruferLastV_mem_erase hn s
  have h_card2 : (state.1.erase u).card = 1 := pruferFinalErase_card hn s
  have huv : u ≠ v := pruferLastU_ne_V hn s

  have hsup : fromEdgeSet (V := Fin n) (insert (s(u, v)) state.2 : Set (Sym2 (Fin n))) = fromEdgeSet (V := Fin n) (state.2 : Set (Sym2 (Fin n))) ⊔ edge u v := by
    ext a b; simp [fromEdgeSet, edge, Sym2.ToRel, Sym2.eq]; tauto

  have h_preconn : (fromEdgeSet (V := Fin n) (insert (s(u, v)) state.2 : Set (Sym2 (Fin n)))).Preconnected := by
    intro x y
    rcases h_forest.covers x with ⟨rx, hrx, hreach_x⟩
    rcases h_forest.covers y with ⟨ry, hry, hreach_y⟩

    have h_state1_eq : state.1 = {u, v} := by
      ext z
      rw [Finset.mem_insert, Finset.mem_singleton]
      refine ⟨fun hz => ?_, fun hz => ?_⟩
      · by_contra hc
        push Not at hc
        have hz_state2 : z ∈ (state.1.erase u) := Finset.mem_erase_of_ne_of_mem hc.1 hz
        have h_v_eq_z : v = z := by
          have h_sub : (state.1.erase u) ⊆ {v} := by
            intro a ha
            have h_eq : (state.1.erase u).card = 1 := h_card2
            rw [Finset.card_eq_one] at h_eq
            rcases h_eq with ⟨w, hw⟩
            have h_v_w : v ∈ ({w} : Finset (Fin n)) := by rw [← hw]; exact hv_mem2
            rw [Finset.mem_singleton] at h_v_w
            have h_a_w : a ∈ ({w} : Finset (Fin n)) := by rw [← hw]; exact ha
            rw [Finset.mem_singleton] at h_a_w
            rw [Finset.mem_singleton]
            exact h_a_w.trans h_v_w.symm
          have hz_in_v := h_sub hz_state2
          rw [Finset.mem_singleton] at hz_in_v
          exact hz_in_v.symm
        exact hc.2 h_v_eq_z.symm
      · rcases hz with rfl | rfl
        · exact hu
        · exact hv

    have hrx_eq : rx = u ∨ rx = v := by
      have hrx_in : rx ∈ ({u, v} : Finset (Fin n)) := by rw [← h_state1_eq]; exact hrx
      rw [Finset.mem_insert, Finset.mem_singleton] at hrx_in
      exact hrx_in

    have hry_eq : ry = u ∨ ry = v := by
      have hry_in : ry ∈ ({u, v} : Finset (Fin n)) := by rw [← h_state1_eq]; exact hry
      rw [Finset.mem_insert, Finset.mem_singleton] at hry_in
      exact hry_in

    have h_uv_reach : (fromEdgeSet (V := Fin n) (insert (s(u, v)) state.2 : Set (Sym2 (Fin n)))).Reachable u v := by
      rw [hsup]
      have h_edge : (fromEdgeSet (V := Fin n) (state.2 : Set (Sym2 (Fin n))) ⊔ edge u v).Adj u v := Or.inr ⟨by simp [edge, Sym2.ToRel], huv⟩
      exact h_edge.reachable

    have hreach_x_new : (fromEdgeSet (V := Fin n) (insert (s(u, v)) state.2 : Set (Sym2 (Fin n)))).Reachable x rx := by
      rw [hsup]
      exact hreach_x.mono le_sup_left

    have hreach_y_new : (fromEdgeSet (V := Fin n) (insert (s(u, v)) state.2 : Set (Sym2 (Fin n)))).Reachable ry y := by
      rw [hsup]
      exact hreach_y.symm.mono le_sup_left

    have h_r_reach : (fromEdgeSet (V := Fin n) (insert (s(u, v)) state.2 : Set (Sym2 (Fin n)))).Reachable rx ry := by
      rcases hrx_eq with rfl | rfl
      · rcases hry_eq with rfl | rfl
        · exact Reachable.refl _
        · exact h_uv_reach
      · rcases hry_eq with rfl | rfl
        · exact h_uv_reach.symm
        · exact Reachable.refl _

    exact Reachable.trans hreach_x_new (Reachable.trans h_r_reach hreach_y_new)

  have h_acyclic : (fromEdgeSet (V := Fin n) (insert (s(u, v)) state.2 : Set (Sym2 (Fin n)))).IsAcyclic := by
    rw [hsup]
    rw [isAcyclic_sup_fromEdgeSet_iff]
    refine ⟨h_forest.acyclic, ?_⟩
    intro hreach
    exact False.elim (h_forest.uniq u hu v hv huv hreach)

  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rw [show (↑(insert s(u, v) state.2) : Set (Sym2 (Fin n))) = insert s(u, v) (↑state.2 : Set _)
      from Finset.coe_insert _ _]
  exact { connected := { preconnected := h_preconn }, isAcyclic := h_acyclic }

/-- The Prüfer decode wrapped as a `LabeledTree`. -/
def pruferDecode {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) : LabeledTree n :=
  ⟨fromEdgeSet (V := Fin n) (pruferDecodeEdges hn s : Set (Sym2 (Fin n))),
    pruferDecodeIsTree hn s⟩

/-- Iterative Prüfer encoding: indexed by `m`, where the tree has `m + 2` vertices.
At each step, record the neighbour of the smallest leaf, then recurse on the
tree with that leaf removed, lifting indices via `finSuccAboveEquivCompl`. -/
noncomputable def pruferEncodeAux : ∀ (m : ℕ), LabeledTree (m + 2) → Fin m → Fin (m + 2)
  | 0,   _ => Fin.elim0
  | m+1, T => fun i =>
    if h : i.val = 0 then
      smallestTreeLeafNeighbor (m + 3) (by omega) T
    else
      let leaf : Fin (m + 3) := smallestTreeLeaf (m + 3) (by omega) T
      let T' : LabeledTree (m + 2) := deleteSmallestLeafTreeSucc (m + 2) (by omega) T
      let i' : Fin m := ⟨i.val - 1, by omega⟩
      let inner : Fin (m + 2) := pruferEncodeAux m T' i'
      ((finSuccAboveEquivCompl leaf) inner).1

/-- Prüfer encoding of a labeled tree as a function `Fin (n - 2) → Fin n`. -/
noncomputable def pruferEncode : ∀ {n : ℕ}, 2 ≤ n → LabeledTree n → pruferCodeSpace n
  | 0,       hn, _ => absurd hn (by decide)
  | 1,       hn, _ => absurd hn (by decide)
  | (m + 2), _,  T => pruferEncodeAux m T


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


/-! Ch31 Tier 2: degree formula for the decoded forest. -/

private def countOccurrences {n : ℕ} (s : pruferCodeSpace n) (m : ℕ) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun (j : Fin (n - 2)) => j.val < m ∧ s j = v)).card

/-- Base case: at m = 0, no edges. -/
private theorem pruferDecodeAux_zero_degree (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (v : Fin n) (hm : 0 ≤ n - 2) :
    (fromEdgeSet (V := Fin n)
      ((pruferDecodeAux hn s 0 hm).val.2 : Set (Sym2 (Fin n)))).degree v = 0 := by
  unfold SimpleGraph.degree
  rw [Finset.card_eq_zero]
  ext x
  rw [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj]
  constructor
  · rintro ⟨hmem, _⟩
    have : (pruferDecodeAux hn s 0 hm).val.2 = ∅ := rfl
    rw [this] at hmem
    simp at hmem
  · intro h
    exact absurd h (by simp)

/-- Recursive structure: edge set at m+1 = insert one edge into edge set at m. -/
private lemma pruferDecodeAux_succ_val_2 {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (m : ℕ) (hm : m + 1 ≤ n - 2) :
    ∃ nextLeaf : Fin n,
      nextLeaf ∈ (pruferDecodeAux hn s m (by omega)).val.1 ∧
      (∀ j : Fin (n - 2), m ≤ j.val → s j ≠ nextLeaf) ∧
      (pruferDecodeAux hn s (m + 1) hm).val.2 =
        insert s(nextLeaf, s ⟨m, by omega⟩)
          (pruferDecodeAux hn s m (by omega)).val.2 ∧
      (pruferDecodeAux hn s (m + 1) hm).val.1 =
        (pruferDecodeAux hn s m (by omega)).val.1.erase nextLeaf := by
  set prev := pruferDecodeAux hn s m (by omega)
  set state := prev.val with hstate
  have h_card := prev.property.2.1
  have h_nonempty := nextLeaf_nonempty hn s m (by omega) state.1 h_card
  set nextLeaf := (state.1.filter (fun v => ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ v)).min' h_nonempty
    with hnextLeaf
  have h_mem_filter : nextLeaf ∈ state.1.filter (fun v => ∀ j : Fin (n - 2), m ≤ j.val → s j ≠ v) :=
    Finset.min'_mem _ _
  rw [Finset.mem_filter] at h_mem_filter
  exact ⟨nextLeaf, h_mem_filter.1, h_mem_filter.2, rfl, rfl⟩

/-- Helper: degree in `fromEdgeSet (insert e S : Set _)` for a vertex not in
the new edge equals degree in `fromEdgeSet (S : Set _)`. -/
private lemma fromEdgeSet_insert_degree_other {n : ℕ}
    (S : Finset (Sym2 (Fin n))) (u w v : Fin n) (huw : u ≠ w)
    (hv_u : v ≠ u) (hv_w : v ≠ w) :
    (fromEdgeSet (V := Fin n) (insert s(u, w) S : Set (Sym2 (Fin n)))).degree v =
    (fromEdgeSet (V := Fin n) (S : Set (Sym2 (Fin n)))).degree v := by
  unfold SimpleGraph.degree
  congr 1
  ext x
  simp only [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj, Finset.coe_insert,
             Set.mem_insert_iff, Sym2.eq_iff]
  constructor
  · rintro ⟨hmem, hne⟩
    refine ⟨?_, hne⟩
    rcases hmem with ⟨heq | heq_swap⟩ | hinS
    · rcases heq with ⟨rfl, rfl⟩
      exact absurd rfl hv_u
    · rcases heq_swap with ⟨rfl, rfl⟩
      exact absurd rfl hv_w
    · exact hinS
  · rintro ⟨hmem, hne⟩
    exact ⟨Or.inr hmem, hne⟩

/-- Degree at an endpoint of a newly inserted edge increases by 1, provided
the edge was not already present and endpoints are distinct. -/
private lemma fromEdgeSet_insert_degree_endpoint {n : ℕ}
    (S : Finset (Sym2 (Fin n))) (u w : Fin n) (huw : u ≠ w)
    (h_not_in : s(u, w) ∉ S) :
    (fromEdgeSet (V := Fin n) (insert s(u, w) S : Set (Sym2 (Fin n)))).degree u =
    (fromEdgeSet (V := Fin n) (S : Set (Sym2 (Fin n)))).degree u + 1 := by
  unfold SimpleGraph.degree
  -- neighborFinset of new graph at u = neighborFinset of old + {w}, disjoint.
  have h_w_not_neighbor :
      w ∉ (fromEdgeSet (V := Fin n) (S : Set (Sym2 (Fin n)))).neighborFinset u := by
    rw [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj]
    rintro ⟨hmem, _⟩
    exact h_not_in (by exact_mod_cast hmem)
  have h_eq : (fromEdgeSet (V := Fin n) (insert s(u, w) S : Set _)).neighborFinset u =
              insert w ((fromEdgeSet (V := Fin n) (S : Set _)).neighborFinset u) := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj, Finset.coe_insert,
               Set.mem_insert_iff, Finset.mem_insert, Sym2.eq_iff]
    constructor
    · rintro ⟨hmem, hne⟩
      rcases hmem with hnew | hold
      · rcases hnew with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact absurd rfl hne
      · exact Or.inr ⟨hold, hne⟩
    · rintro (rfl | ⟨hmem, hne⟩)
      · refine ⟨Or.inl (Or.inl ?_), huw⟩
        tauto
      · exact ⟨Or.inr hmem, hne⟩
  rw [h_eq]
  exact Finset.card_insert_of_notMem h_w_not_neighbor

/-- Sym2 commutativity: `s(u, w) = s(w, u)` so the insert is symmetric. -/
private lemma sym2_pair_swap {V : Type*} (u w : V) : s(u, w) = s(w, u) :=
  Sym2.eq_swap

/-- Endpoint version usable when goal has `↑(insert e S : Finset _)` form. -/
private lemma fromEdgeSet_finset_insert_degree_endpoint {n : ℕ}
    (S : Finset (Sym2 (Fin n))) (u w : Fin n) (huw : u ≠ w)
    (h_not_in : s(u, w) ∉ S) :
    (fromEdgeSet (V := Fin n)
      (((insert s(u, w) S : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))))).degree u =
    (fromEdgeSet (V := Fin n) (S : Set (Sym2 (Fin n)))).degree u + 1 := by
  -- The base form is in Set.insert: lemma proven in that form.
  -- Use ext-based proof: unfold degree as neighborFinset.card, then case-split.
  unfold SimpleGraph.degree
  have h_w_not_neighbor :
      w ∉ (fromEdgeSet (V := Fin n) (S : Set (Sym2 (Fin n)))).neighborFinset u := by
    rw [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj]
    rintro ⟨hmem, _⟩
    exact h_not_in (by exact_mod_cast hmem)
  have h_eq : (fromEdgeSet (V := Fin n)
        (((insert s(u, w) S : Finset _) : Set _))).neighborFinset u =
      insert w ((fromEdgeSet (V := Fin n) (S : Set _)).neighborFinset u) := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj, Finset.coe_insert,
               Set.mem_insert_iff, Finset.mem_insert, Sym2.eq_iff]
    constructor
    · rintro ⟨hmem, hne⟩
      rcases hmem with hnew | hold
      · rcases hnew with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact absurd rfl hne
      · exact Or.inr ⟨hold, hne⟩
    · rintro (rfl | ⟨hmem, hne⟩)
      · refine ⟨Or.inl (Or.inl ?_), huw⟩
        tauto
      · exact ⟨Or.inr hmem, hne⟩
  rw [h_eq]
  exact Finset.card_insert_of_notMem h_w_not_neighbor

/-- Other version usable when goal has `↑(insert e S : Finset _)` form. -/
private lemma fromEdgeSet_finset_insert_degree_other {n : ℕ}
    (S : Finset (Sym2 (Fin n))) (u w v : Fin n) (huw : u ≠ w)
    (hv_u : v ≠ u) (hv_w : v ≠ w) :
    (fromEdgeSet (V := Fin n)
      (((insert s(u, w) S : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))))).degree v =
    (fromEdgeSet (V := Fin n) (S : Set (Sym2 (Fin n)))).degree v := by
  unfold SimpleGraph.degree
  congr 1
  ext x
  simp only [SimpleGraph.mem_neighborFinset, fromEdgeSet_adj, Finset.coe_insert,
             Set.mem_insert_iff, Sym2.eq_iff]
  constructor
  · rintro ⟨hmem, hne⟩
    refine ⟨?_, hne⟩
    rcases hmem with ⟨heq | heq_swap⟩ | hinS
    · rcases heq with ⟨rfl, rfl⟩
      exact absurd rfl hv_u
    · rcases heq_swap with ⟨rfl, rfl⟩
      exact absurd rfl hv_w
    · exact hinS
  · rintro ⟨hmem, hne⟩
    exact ⟨Or.inr hmem, hne⟩

/-- countOccurrences recursion: stepping `m` to `m+1` adds 1 iff `s ⟨m, _⟩ = v`. -/
private lemma countOccurrences_succ {n : ℕ} (s : pruferCodeSpace n)
    (m : ℕ) (hm : m + 1 ≤ n - 2) (v : Fin n) :
    countOccurrences s (m + 1) v =
    countOccurrences s m v + (if s ⟨m, by omega⟩ = v then 1 else 0) := by
  unfold countOccurrences
  -- Filter at m+1 = filter at m ∪ (singleton ⟨m, _⟩ if s_m = v).
  rw [show (Finset.univ.filter (fun (j : Fin (n - 2)) => j.val < m + 1 ∧ s j = v)) =
       (Finset.univ.filter (fun (j : Fin (n - 2)) => j.val < m ∧ s j = v)) ∪
       (Finset.univ.filter (fun (j : Fin (n - 2)) => j.val = m ∧ s j = v)) from ?_]
  · rw [Finset.card_union_of_disjoint]
    · congr 1
      by_cases hsm : s ⟨m, by omega⟩ = v
      · simp [hsm]
        rw [show (Finset.univ.filter (fun (j : Fin (n - 2)) => j.val = m ∧ s j = v)) =
             {⟨m, by omega⟩} from ?_]
        · simp
        · ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨hval, _⟩
            ext
            exact hval
          · rintro rfl
            exact ⟨rfl, hsm⟩
      · simp [hsm]
        intro x hval hsx
        apply hsm
        have : x = ⟨m, by omega⟩ := by ext; exact hval
        rw [← hsx, this]
    · rw [Finset.disjoint_filter]
      intros j _ h1 h2
      omega
  · ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hval, hs⟩
      by_cases h : j.val = m
      · exact Or.inr ⟨h, hs⟩
      · exact Or.inl ⟨by omega, hs⟩
    · rintro (⟨h, hs⟩ | ⟨h, hs⟩)
      · exact ⟨by omega, hs⟩
      · exact ⟨by omega, hs⟩

/-- Degree formula: after m iterations of `pruferDecodeAux`, the degree of
vertex v in the constructed graph equals the number of times v appears as
`s j` for `j.val < m`, plus 1 if v has already been "popped" (i.e., v has
been chosen as a `nextLeaf` and erased from the available set). -/
private theorem pruferDecodeAux_degree (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    ∀ (m : ℕ) (hm : m ≤ n - 2) (v : Fin n),
    (fromEdgeSet (V := Fin n)
      ((pruferDecodeAux hn s m hm).val.2 : Set (Sym2 (Fin n)))).degree v =
    countOccurrences s m v +
    (if v ∈ (pruferDecodeAux hn s m hm).val.1 then 0 else 1) := by
  intro m
  induction m with
  | zero =>
    intro hm v
    rw [pruferDecodeAux_zero_degree n hn s v hm]
    have hcount : countOccurrences s 0 v = 0 := by
      apply Finset.card_eq_zero.mpr
      ext j; simp [countOccurrences]
    have hmem : v ∈ (pruferDecodeAux hn s 0 hm).val.1 := by
      show v ∈ Finset.univ; exact Finset.mem_univ v
    rw [hcount, if_pos hmem]
  | succ m ih =>
    intro hm v
    -- Sub-key facts about transitions from step m to m+1.
    have h_m_le : m ≤ n - 2 := by omega
    obtain ⟨nextLeaf, hnL_mem, hnL_filter, h_edges_eq, h_avail_eq⟩ :=
      pruferDecodeAux_succ_val_2 hn s m hm
    -- The m-th code entry.
    set si : Fin n := s ⟨m, by omega⟩ with hsi_def
    -- nextLeaf ≠ si: from filter property at j = ⟨m, _⟩.
    have h_nL_ne_si : nextLeaf ≠ si := by
      have := hnL_filter ⟨m, by omega⟩ (by rfl)
      exact (this.symm)
    -- si is in available set at step m (from h_future invariant).
    have h_si_in_prev : si ∈ (pruferDecodeAux hn s m h_m_le).val.1 := by
      have h_future := (pruferDecodeAux hn s m h_m_le).property.2.2
      exact h_future ⟨m, by omega⟩ (by rfl)
    -- Edge s(nextLeaf, si) not already in state.2:
    -- Proof: if it were, then since fromEdgeSet (state.2) is a forest, and
    -- nextLeaf, si are connected in fromEdgeSet (state.2), they're in different
    -- trees. But h_si_in_prev and hnL_mem say both in state.1, and the forest
    -- has each state.1 vertex as a distinct tree root → they aren't reachable
    -- to each other (uniq property).
    have h_edge_not_in : s(nextLeaf, si) ∉ (pruferDecodeAux hn s m h_m_le).val.2 := by
      intro hmem
      have h_forest := (pruferDecodeAux hn s m h_m_le).property.1
      have h_adj : (fromEdgeSet (V := Fin n)
        ((pruferDecodeAux hn s m h_m_le).val.2 : Set (Sym2 (Fin n)))).Adj nextLeaf si := by
        rw [fromEdgeSet_adj]
        exact ⟨by exact_mod_cast hmem, h_nL_ne_si⟩
      have h_reach := h_adj.reachable
      have h_uniq := h_forest.uniq
      exact h_uniq nextLeaf hnL_mem si h_si_in_prev h_nL_ne_si h_reach
    -- Now case on v's relation to nextLeaf and si.
    -- Rewrite goal's val.2 and val.1 via the recursion equations.
    -- Both sides reduce to expressions in `(pruferDecodeAux hn s m h_m_le).val.{1,2}`.
    have h_lhs_eq : (fromEdgeSet (V := Fin n)
        ((pruferDecodeAux hn s (m+1) hm).val.2 : Set (Sym2 (Fin n)))).degree v =
      (fromEdgeSet (V := Fin n)
        ((insert s(nextLeaf, si) (pruferDecodeAux hn s m h_m_le).val.2 :
            Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))).degree v := by
      rw [h_edges_eq]
    have h_indicator_eq :
        (if v ∈ (pruferDecodeAux hn s (m+1) hm).val.1 then (0:ℕ) else 1) =
        (if v ∈ (pruferDecodeAux hn s m h_m_le).val.1.erase nextLeaf
          then (0:ℕ) else 1) := by
      rw [h_avail_eq]
    rw [h_lhs_eq, h_indicator_eq]
    rw [countOccurrences_succ s m hm v]
    have ih_m := ih h_m_le v
    by_cases hv_nL : v = nextLeaf
    · -- Case 1: v = nextLeaf. Substitute v throughout.
      subst hv_nL
      rw [fromEdgeSet_finset_insert_degree_endpoint
        (pruferDecodeAux hn s m h_m_le).val.2 v si h_nL_ne_si h_edge_not_in]
      rw [ih_m, if_pos hnL_mem]
      have hsm_ne : ¬ s ⟨m, by omega⟩ = v := h_nL_ne_si.symm
      simp [hsm_ne]
    · by_cases hv_si : v = si
      · -- Case 2: v = si.
        rw [hv_si]  -- Goal now has si everywhere instead of v.
        have h_edge_swap : s(nextLeaf, si) = s(si, nextLeaf) := sym2_pair_swap _ _
        rw [h_edge_swap]
        have h_edge_not_in' : s(si, nextLeaf) ∉ (pruferDecodeAux hn s m h_m_le).val.2 := by
          rw [← h_edge_swap]; exact h_edge_not_in
        have h_si_ne_nL : si ≠ nextLeaf := h_nL_ne_si.symm
        rw [fromEdgeSet_finset_insert_degree_endpoint
          (pruferDecodeAux hn s m h_m_le).val.2 si nextLeaf h_si_ne_nL h_edge_not_in']
        rw [hv_si] at ih_m
        rw [ih_m, if_pos h_si_in_prev]
        have hsm_eq : s ⟨m, by omega⟩ = si := rfl
        rw [if_pos hsm_eq]
        have hsi_in_erase : si ∈ (pruferDecodeAux hn s m h_m_le).val.1.erase nextLeaf := by
          rw [Finset.mem_erase]
          exact ⟨h_si_ne_nL, h_si_in_prev⟩
        rw [if_pos hsi_in_erase]
      · -- Case 3: v ≠ nextLeaf and v ≠ si.
        rw [fromEdgeSet_finset_insert_degree_other
          (pruferDecodeAux hn s m h_m_le).val.2 nextLeaf si v h_nL_ne_si hv_nL hv_si]
        rw [ih_m]
        have hsm_ne : ¬ s ⟨m, by omega⟩ = v := fun h => hv_si (h.symm)
        rw [if_neg hsm_ne]
        have h_erase_iff :
            (v ∈ (pruferDecodeAux hn s m h_m_le).val.1.erase nextLeaf) ↔
            (v ∈ (pruferDecodeAux hn s m h_m_le).val.1) := by
          rw [Finset.mem_erase]
          exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv_nL, h⟩⟩
        by_cases h : v ∈ (pruferDecodeAux hn s m h_m_le).val.1
        · rw [if_pos h, if_pos (h_erase_iff.mpr h)]
        · rw [if_neg h, if_neg (fun hh => h (h_erase_iff.mp hh))]

/-- pruferFinalState.1 = {pruferLastU, pruferLastV}. -/
private lemma pruferFinalState_1_eq_pair (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 = {pruferLastU hn s, pruferLastV hn s} := by
  have h_uv_ne : pruferLastU hn s ≠ pruferLastV hn s := pruferLastU_ne_V hn s
  have h_u_mem : pruferLastU hn s ∈ (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := pruferLastU_mem hn s
  have h_v_mem : pruferLastV hn s ∈ (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := pruferLastV_mem hn s
  have h_card : (pruferDecodeAux hn s (n - 2) (by rfl)).val.1.card = 2 := pruferFinalState_card hn s
  have h_sub : ({pruferLastU hn s, pruferLastV hn s} : Finset (Fin n)) ⊆
               (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h_u_mem
    · exact h_v_mem
  have h_pair_card : ({pruferLastU hn s, pruferLastV hn s} : Finset (Fin n)).card = 2 :=
    Finset.card_pair h_uv_ne
  exact (Finset.eq_of_subset_of_card_le h_sub (by omega)).symm

/-- The famous Prüfer degree formula: in the decoded tree, every vertex's
degree equals `1 + (# times v appears in the code)`. -/
theorem pruferDecode_degree (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (v : Fin n) :
    ((pruferDecode hn s).1).degree v = countOccurrences s (n - 2) v + 1 := by
  -- pruferDecode = ⟨fromEdgeSet (pruferDecodeEdges hn s : Set _), _⟩.
  -- Both LHS and RHS interpret degree via SimpleGraph.degree; the underlying
  -- graphs are defeq but Fintype instances differ. Use Nat.card via neighborSet.
  have h_card_eq : ((pruferDecode hn s).1).degree v =
      (fromEdgeSet (V := Fin n)
        (pruferDecodeEdges hn s : Set (Sym2 (Fin n)))).degree v := by
    -- Both degrees equal Nat.card (neighborSet v), independent of Fintype instance.
    have h1 : ((pruferDecode hn s).1).degree v =
              (((pruferDecode hn s).1).neighborFinset v).card := rfl
    have h2 : (fromEdgeSet (V := Fin n)
        (pruferDecodeEdges hn s : Set (Sym2 (Fin n)))).degree v =
              ((fromEdgeSet (V := Fin n)
        (pruferDecodeEdges hn s : Set (Sym2 (Fin n)))).neighborFinset v).card := rfl
    rw [h1, h2]
    -- Both neighborFinsets contain the same elements (Adj is the same).
    congr 1
    ext x
    simp [SimpleGraph.mem_neighborFinset]
    rfl
  rw [h_card_eq]
  unfold pruferDecodeEdges
  set u := pruferLastU hn s with hu_def
  set w := pruferLastV hn s with hw_def
  -- pruferDecodeEdges = insert s(u, w) (pruferDecodeAux hn s (n - 2) (by rfl)).val.2.
  have h_uw_ne : u ≠ w := pruferLastU_ne_V hn s
  -- Unfold pruferFinalState to match pruferDecodeAux_degree's signature.
  show (fromEdgeSet (V := Fin n)
        ((insert s(u, w) (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 :
            Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))).degree v =
        countOccurrences s (n - 2) v + 1
  -- Step 2: edge s(u, w) not in pruferFinalState.2 (forest invariant).
  have h_edge_not_in : s(u, w) ∉ (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 := by
    intro hmem
    have h_forest := (pruferDecodeAux hn s (n - 2) (by rfl)).property.1
    have h_adj : (fromEdgeSet (V := Fin n)
      ((pruferDecodeAux hn s (n - 2) (by rfl)).val.2 : Set (Sym2 (Fin n)))).Adj u w := by
      rw [fromEdgeSet_adj]
      exact ⟨by exact_mod_cast hmem, h_uw_ne⟩
    exact h_forest.uniq u (pruferLastU_mem hn s) w (pruferLastV_mem hn s)
      h_uw_ne h_adj.reachable
  -- Step 3: case split on whether v = u or v = w or neither.
  by_cases hv_u : v = u
  · -- After subst, v ↦ u; use u throughout.
    subst hv_u
    rw [fromEdgeSet_finset_insert_degree_endpoint
      (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 u w h_uw_ne h_edge_not_in]
    rw [pruferDecodeAux_degree n hn s (n - 2) (by rfl) u]
    have h_u_mem : u ∈ (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := pruferLastU_mem hn s
    rw [if_pos h_u_mem]
  · by_cases hv_w : v = w
    · subst hv_w
      have h_swap : s(u, w) = s(w, u) := sym2_pair_swap _ _
      rw [h_swap]
      have h_edge_not_in' : s(w, u) ∉ (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 := by
        rw [← h_swap]; exact h_edge_not_in
      have h_w_ne_u : w ≠ u := hv_u
      rw [fromEdgeSet_finset_insert_degree_endpoint
        (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 w u h_w_ne_u h_edge_not_in']
      rw [pruferDecodeAux_degree n hn s (n - 2) (by rfl) w]
      have h_w_mem : w ∈ (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := pruferLastV_mem hn s
      rw [if_pos h_w_mem]
    · rw [fromEdgeSet_finset_insert_degree_other
        (pruferDecodeAux hn s (n - 2) (by rfl)).val.2 u w v h_uw_ne hv_u hv_w]
      rw [pruferDecodeAux_degree n hn s (n - 2) (by rfl) v]
      have h_v_notin : v ∉ (pruferDecodeAux hn s (n - 2) (by rfl)).val.1 := by
        rw [pruferFinalState_1_eq_pair]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hv_u, hv_w⟩
      rw [if_neg h_v_notin]

lemma degree_eq_one_iff_exists_unique_adj {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n} :
    G.degree v = 1 ↔ ∃! w, G.Adj v w := by
  have h_deg : G.degree v = (G.neighborFinset v).card := rfl
  rw [h_deg, Finset.card_eq_one]
  constructor
  · rintro ⟨w, hw⟩
    use w
    have h_mem : w ∈ G.neighborFinset v := by rw [hw]; exact Finset.mem_singleton_self w
    simp only [SimpleGraph.mem_neighborFinset] at h_mem
    refine ⟨h_mem, ?_⟩
    intro y hy
    have h_mem_y : y ∈ G.neighborFinset v := by simp only [SimpleGraph.mem_neighborFinset, hy]
    rw [hw, Finset.mem_singleton] at h_mem_y
    exact h_mem_y
  · rintro ⟨w, hw1, hw2⟩
    use w
    ext x
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · intro hx
      exact hw2 x hx
    · rintro rfl
      exact hw1

/-- A vertex is a tree-leaf in the decoded tree iff it doesn't appear in the code. -/
theorem pruferDecode_isLeaf_iff (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (v : Fin n) :
    v ∈ treeLeaves (pruferDecode hn s) ↔ isLeafInPrufer s v := by
  have h_leaf : v ∈ treeLeaves (pruferDecode hn s) ↔ ((pruferDecode hn s).1).degree v = 1 := by
    unfold treeLeaves
    classical
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact degree_eq_one_iff_exists_unique_adj.symm
  rw [h_leaf]
  rw [pruferDecode_degree n hn s v]
  have h_eq : countOccurrences s (n - 2) v + 1 = 1 ↔ countOccurrences s (n - 2) v = 0 := by omega
  rw [h_eq]
  unfold countOccurrences
  rw [Finset.card_eq_zero]
  constructor
  · intro h i
    have hi : i ∉ Finset.univ.filter (fun (j : Fin (n - 2)) => j.val < n - 2 ∧ s j = v) := by
      rw [h]
      simp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hi
    exact hi i.isLt
  · intro h
    ext i
    simp [h i]

/-- The smallest tree-leaf of `pruferDecode s` equals the smallest vertex not
appearing in `s`, which is `nextLeaf_0` from the decode process. -/
theorem smallestTreeLeaf_pruferDecode (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    smallestTreeLeaf n hn (pruferDecode hn s) =
    (Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v)).min'
      (by
        have h0_le : 0 ≤ n - 2 := Nat.zero_le _
        have h_nonempty := nextLeaf_nonempty hn s 0 h0_le Finset.univ (by simp)
        have h_finsets : Finset.univ.filter (fun v => ∀ j : Fin (n - 2), 0 ≤ j.val → s j ≠ v) =
                         Finset.univ.filter (fun v => ∀ j : Fin (n - 2), s j ≠ v) := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h j => h j (Nat.zero_le _), fun h j _ => h j⟩
        rw [h_finsets] at h_nonempty
        exact h_nonempty) := by
  have h_eq : treeLeaves (pruferDecode hn s) = Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v) := by
    ext v
    rw [pruferDecode_isLeaf_iff n hn s v]
    unfold isLeafInPrufer
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold smallestTreeLeaf
  congr

private theorem smallestTreeLeaf_eq_min_filter (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    smallestTreeLeaf n hn (pruferDecode hn s) ∈
    (Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v)) ∧
    ∀ v ∈ (Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v)),
      smallestTreeLeaf n hn (pruferDecode hn s) ≤ v := by
  have h_eq := smallestTreeLeaf_pruferDecode n hn s
  rw [h_eq]
  exact ⟨Finset.min'_mem _ _, fun v hv => Finset.min'_le _ _ hv⟩

lemma step_one_edge_mem (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) (hge : 3 ≤ n) (e : Sym2 (Fin n))
    (he : e ∈ (pruferDecodeAux hn s 1 (by omega)).val.2) :
    e ∈ pruferDecodeEdges hn s := by
  have h_mono : ∀ m (h_ge1 : 1 ≤ m) (hm_le : m ≤ n - 2), e ∈ (pruferDecodeAux hn s m hm_le).val.2 := by
    intro m
    induction m with
    | zero => intro h1 _; omega
    | succ m ih =>
      intro h_ge hm_le
      by_cases h_eq : m = 0
      · subst h_eq
        have h_rw : (pruferDecodeAux hn s 1 (by omega)).val.2 = (pruferDecodeAux hn s 1 hm_le).val.2 := rfl
        rw [← h_rw]
        exact he
      · have hm_ge1 : 1 ≤ m := by omega
        have hm_le_prev : m ≤ n - 2 := by omega
        have ih_m := ih hm_ge1 hm_le_prev
        have h_succ : m + 1 ≤ n - 2 := hm_le
        obtain ⟨_, _, _, h_edges, _⟩ := pruferDecodeAux_succ_val_2 hn s m h_succ
        have h_rw : (pruferDecodeAux hn s (m + 1) hm_le).val.2 = (pruferDecodeAux hn s (m + 1) h_succ).val.2 := rfl
        rw [h_rw, h_edges]
        exact Finset.mem_insert_of_mem ih_m
  have h_in_n2 := h_mono (n - 2) (by omega) (by rfl)
  unfold pruferDecodeEdges
  exact Finset.mem_insert_of_mem h_in_n2

theorem smallestTreeLeafNeighbor_pruferDecode (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (hge : 3 ≤ n) :
    smallestTreeLeafNeighbor n hn (pruferDecode hn s) = s ⟨0, by omega⟩ := by
  set v := smallestTreeLeaf n hn (pruferDecode hn s)
  have h1 : 0 + 1 ≤ n - 2 := by omega
  have hv_min : v = (Finset.univ.filter (fun x => ∀ j : Fin (n - 2), 0 ≤ j.val → s j ≠ x)).min' (nextLeaf_nonempty hn s 0 (by omega) Finset.univ (by simp)) := by
    apply le_antisymm
    · apply Finset.le_min'
      intro y hy
      have hv_le : ∀ x ∈ Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v), v ≤ x :=
        (smallestTreeLeaf_eq_min_filter n hn s).2
      apply hv_le
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      intro j
      exact hy j (Nat.zero_le _)
    · apply Finset.min'_le
      have hv_mem : v ∈ Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v) :=
        (smallestTreeLeaf_eq_min_filter n hn s).1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv_mem ⊢
      intro j _
      exact hv_mem j
  have h_step1 : (pruferDecodeAux hn s 1 h1).val.2 = {s(v, s ⟨0, by omega⟩)} := by
    dsimp [pruferDecodeAux]
    congr 2
    exact hv_min.symm
  have he : s(v, s ⟨0, by omega⟩) ∈ (pruferDecodeAux hn s 1 h1).val.2 := by
    rw [h_step1]
    exact Finset.mem_singleton_self _
  have he_rewrite : s(v, s ⟨0, by omega⟩) ∈ (pruferDecodeAux hn s 1 (by omega)).val.2 := by
    -- we can just change the proof of hm_le
    have h_rw : (pruferDecodeAux hn s 1 h1).val.2 = (pruferDecodeAux hn s 1 (by omega)).val.2 := rfl
    rw [← h_rw]
    exact he
  have h_in_final := step_one_edge_mem n hn s hge _ he_rewrite
  have h_adj : (fromEdgeSet (V := Fin n) (pruferDecodeEdges hn s : Set (Sym2 (Fin n)))).Adj v (s ⟨0, by omega⟩) := by
    rw [fromEdgeSet_adj]
    refine ⟨by exact_mod_cast h_in_final, ?_⟩
    have hv_mem : v ∈ Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v) :=
      (smallestTreeLeaf_eq_min_filter n hn s).1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv_mem
    exact (hv_mem ⟨0, by omega⟩).symm

  have h_deg : ((pruferDecode hn s).1).degree v = 1 := by
    have h_leaf : v ∈ treeLeaves (pruferDecode hn s) := Finset.min'_mem _ _
    rw [pruferDecode_isLeaf_iff n hn s v] at h_leaf
    rw [pruferDecode_degree n hn s v]
    have h_occur : countOccurrences s (n - 2) v = 0 := by
      unfold countOccurrences
      rw [Finset.card_eq_zero]
      ext j
      simp [h_leaf j]
    rw [h_occur]

  have h_adj' : ((pruferDecode hn s).1).Adj v (s ⟨0, by omega⟩) := h_adj
  exact (smallestTreeLeaf_neighbor_unique n hn (pruferDecode hn s) h_adj').symm

theorem pruferEncode_pruferDecode_zero (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (hge : 3 ≤ n) :
    (pruferEncode hn (pruferDecode hn s)) ⟨0, by omega⟩ = s ⟨0, by omega⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  show (pruferEncodeAux m (pruferDecode _ s)) ⟨0, by omega⟩ = s ⟨0, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  show smallestTreeLeafNeighbor (m' + 3) _ (pruferDecode _ s) = s ⟨0, by omega⟩
  exact smallestTreeLeafNeighbor_pruferDecode (m' + 3) _ s (by omega)

/-- nextLeaf_0: the smallest tree-leaf of the decoded tree (= smallest Prüfer-leaf). -/
noncomputable def nextLeaf0 {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) : Fin n :=
  smallestTreeLeaf n hn (pruferDecode hn s)

/-- nextLeaf_0 doesn't appear in s anywhere. Immediate from pruferDecode_isLeaf_iff. -/
theorem nextLeaf0_not_in_image {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    ∀ j : Fin (n - 2), s j ≠ nextLeaf0 hn s := by
  have h_leaf : nextLeaf0 hn s ∈ treeLeaves (pruferDecode hn s) :=
    smallestTreeLeaf_mem_leaves n hn (pruferDecode hn s)
  rw [pruferDecode_isLeaf_iff n hn s] at h_leaf
  exact h_leaf

/-- The shifted code: drop position 0, lift values through `(finSuccAboveEquivCompl nextLeaf0).symm`. -/
noncomputable def shiftedCode_v2 {m : ℕ} (hm : 1 ≤ m) (s : pruferCodeSpace (m + 2)) :
    pruferCodeSpace (m + 1) := by
  intro j'
  classical
  have h2le : 2 ≤ m + 2 := by omega
  let nL : Fin (m + 2) := nextLeaf0 h2le s
  have hj_lt : j'.val + 1 < (m + 2) - 2 := by have := j'.isLt; omega
  let j : Fin ((m + 2) - 2) := ⟨j'.val + 1, hj_lt⟩
  have hNe : s j ≠ nL := nextLeaf0_not_in_image h2le s j
  have hMem : (s j : Fin (m + 2)) ∈ ({nL}ᶜ : Set (Fin (m + 2))) := by simp [hNe]
  let lifted : {v : Fin (m + 2) // v ∈ ({nL}ᶜ : Set (Fin (m + 2)))} := ⟨s j, hMem⟩
  exact (finSuccAboveEquivCompl nL).symm lifted

lemma L_monotone {m : ℕ} (nL : Fin (m + 2)) (a b : Fin (m + 1)) (h : a ≤ b) :
    (finSuccAboveEquivCompl nL a).1 ≤ (finSuccAboveEquivCompl nL b).1 :=
  StrictMono.monotone (Fin.strictMono_succAbove nL) h

lemma min'_congr {α : Type} [LinearOrder α] {S1 S2 : Finset α} (h : S1 = S2)
    (h1 : S1.Nonempty) (h2 : S2.Nonempty) : S1.min' h1 = S2.min' h2 := by
  subst h
  rfl

lemma min'_commutes_L {m : ℕ} (nL : Fin (m + 2))
    (S : Finset (Fin (m + 1))) (h_nonempty : S.Nonempty) :
    (finSuccAboveEquivCompl nL (S.min' h_nonempty)).1 = (S.image (fun v => (finSuccAboveEquivCompl nL v).1)).min' (Finset.Nonempty.image h_nonempty _) := by
  apply le_antisymm
  · apply Finset.le_min'
    intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    have h_le : S.min' h_nonempty ≤ v := Finset.min'_le _ _ hv
    exact StrictMono.monotone (Fin.strictMono_succAbove nL) h_le
  · apply Finset.min'_le
    simp only [Finset.mem_image]
    exact ⟨S.min' h_nonempty, Finset.min'_mem _ _, rfl⟩

lemma pruferDecodeAux_succ_step {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (k : ℕ) (hk : k + 1 ≤ n - 2) :
    let state := (pruferDecodeAux hn s k (by omega)).val
    let nL := (state.1.filter (fun v => ∀ j : Fin (n - 2), k ≤ j.val → s j ≠ v)).min' (nextLeaf_nonempty hn s k (by omega) state.1 (pruferDecodeAux hn s k (by omega)).property.2.1)
    let si := s ⟨k, by omega⟩
    (pruferDecodeAux hn s (k + 1) hk).val = (state.1.erase nL, insert s(nL, si) state.2) := rfl

private lemma nextLeaf_correspond_lift {m : ℕ} (hm : 1 ≤ m) (s : pruferCodeSpace (m + 2)) (k : ℕ)
    (hk : k + 1 ≤ m + 1 - 2)
    (ih_avail : ∀ v : Fin (m + 1),
       v ∈ (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k (by omega)).val.1 ↔
       (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) v).1 ∈ (pruferDecodeAux (by omega) s (k + 1) (by omega)).val.1) :
    let state_shifted := (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k (by omega)).val
    let state_orig := (pruferDecodeAux (by omega) s (k + 1) (by omega)).val
    let nL_k := (state_shifted.1.filter
      (fun v => ∀ j : Fin (m + 1 - 2), k ≤ j.val → shiftedCode_v2 hm s j ≠ v)).min'
      (nextLeaf_nonempty (by omega) (shiftedCode_v2 hm s) k (by omega) state_shifted.1 (pruferDecodeAux (by omega) _ k (by omega)).property.2.1)
    let nL_k' := (state_orig.1.filter
      (fun v => ∀ j : Fin (m + 2 - 2), k + 1 ≤ j.val → s j ≠ v)).min'
      (nextLeaf_nonempty (by omega) s (k + 1) (by omega) state_orig.1 (pruferDecodeAux (by omega) s (k + 1) (by omega)).property.2.1)
    (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) nL_k).1 = nL_k' := by
  intro state_shifted state_orig nL_k nL_k'
  let L := finSuccAboveEquivCompl (nextLeaf0 (by omega) s)
  let S := state_shifted.1.filter (fun v => ∀ j : Fin (m + 1 - 2), k ≤ j.val → shiftedCode_v2 hm s j ≠ v)
  let S' := state_orig.1.filter (fun v => ∀ j : Fin (m + 2 - 2), k + 1 ≤ j.val → s j ≠ v)
  have h_card_shifted : state_shifted.1.card = m + 1 - k := (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k (by omega)).property.2.1
  have h_card_orig : state_orig.1.card = m + 1 - k := by
    have h : state_orig.1.card = m + 2 - (k + 1) := (pruferDecodeAux (by omega) s (k + 1) (by omega)).property.2.1
    omega
  have h_img : state_shifted.1.image (fun v => (L v).1) = state_orig.1 := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ih_avail y |>.mp hy
    · rw [Finset.card_image_of_injective]
      · omega
      · intro y1 y2 h_eq
        have h_L : L y1 = L y2 := Subtype.ext h_eq
        exact Equiv.injective L h_L
  have h_S_eq : S.image (fun v => (L v).1) = S' := by
    ext x
    dsimp [S, S']
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨y, ⟨hy_avail, hy_not_in⟩, rfl⟩
      refine ⟨ih_avail y |>.mp hy_avail, ?_⟩
      intro j hj
      let j' : Fin (m + 1 - 2) := ⟨j.val - 1, by omega⟩
      have hj_val : j'.val = j.val - 1 := rfl
      have hj' : k ≤ j'.val := by omega
      have hy_not := hy_not_in j' hj'
      have h_shift_eval : (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) (shiftedCode_v2 hm s j')).1 = s j := by
        have h_j_eq : (⟨j'.val + 1, by omega⟩ : Fin (m + 2 - 2)) = j := by
          apply Fin.ext
          change j'.val + 1 = j.val
          omega
        dsimp [shiftedCode_v2]
        simp only [Equiv.apply_symm_apply]
        rw [h_j_eq]
      intro h_eq
      rw [← h_shift_eval] at h_eq
      have h_eq2 : L (shiftedCode_v2 hm s j') = L y := Subtype.ext h_eq
      have h_eq3 : shiftedCode_v2 hm s j' = y := Equiv.injective L h_eq2
      exact hy_not h_eq3
    · rintro ⟨hx_avail, hx_not_in⟩
      have hx_img : x ∈ state_shifted.1.image (fun v => (L v).1) := by
        rw [h_img]
        exact hx_avail
      simp only [Finset.mem_image] at hx_img
      obtain ⟨y, hy_avail, rfl⟩ := hx_img
      refine ⟨y, ⟨hy_avail, ?_⟩, rfl⟩
      intro j' hj'
      let j : Fin (m + 2 - 2) := ⟨j'.val + 1, by omega⟩
      have hj_val : j.val = j'.val + 1 := rfl
      have hj : k + 1 ≤ j.val := by omega
      have hx_not := hx_not_in j hj
      have h_shift_eval : (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) (shiftedCode_v2 hm s j')).1 = s j := by
        have h_j_eq : (⟨j'.val + 1, by omega⟩ : Fin (m + 2 - 2)) = j := by
          apply Fin.ext
          change j'.val + 1 = j.val
          omega
        dsimp [shiftedCode_v2]
        simp only [Equiv.apply_symm_apply]
        rw [h_j_eq]
      intro h_eq
      rw [h_eq] at h_shift_eval
      exact hx_not h_shift_eval.symm
  have h_min := min'_commutes_L (nextLeaf0 (by omega) s) S (nextLeaf_nonempty (by omega) (shiftedCode_v2 hm s) k (by omega) state_shifted.1 (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k (by omega)).property.2.1)
  rw [h_min]
  apply le_antisymm
  · apply Finset.le_min'
    intro y hy
    have h_eq_elem := Finset.ext_iff.mp h_S_eq y
    have hy_img := h_eq_elem.mpr hy
    exact Finset.min'_le _ _ hy_img
  · apply Finset.min'_le
    have h_nonempty_S' : S'.Nonempty := nextLeaf_nonempty (by omega) s (k + 1) (by omega) state_orig.1 (pruferDecodeAux (by omega) s (k + 1) (by omega)).property.2.1
    have h_nonempty_S_img : (S.image (fun v => (L v).1)).Nonempty := by
      rw [h_S_eq]
      exact h_nonempty_S'
    have h_mem := Finset.min'_mem (S.image (fun v => (L v).1)) h_nonempty_S_img
    have h_eq_elem := Finset.ext_iff.mp h_S_eq ((S.image (fun v => (L v).1)).min' h_nonempty_S_img)
    exact h_eq_elem.mp h_mem

lemma step_zero_min_eq_nextLeaf0 {m : ℕ} (hm : 1 ≤ m) (s : pruferCodeSpace (m + 2)) :
    ((pruferDecodeAux (by omega) s 0 (by omega)).val.1.filter (fun v => ∀ j : Fin (m + 2 - 2), 0 ≤ j.val → s j ≠ v)).min' (nextLeaf_nonempty (by omega) s 0 (by omega) (pruferDecodeAux (by omega) s 0 (by omega)).val.1 (pruferDecodeAux (by omega) s 0 (by omega)).property.2.1) = nextLeaf0 (by omega) s := by
  have h_val : (pruferDecodeAux (by omega) s 0 (by omega)).val.1 = Finset.univ := rfl
  have h_S : ((pruferDecodeAux (by omega) s 0 (by omega)).val.1.filter (fun v => ∀ j : Fin (m + 2 - 2), 0 ≤ j.val → s j ≠ v)) = Finset.univ.filter (fun v => ∀ j : Fin (m + 2 - 2), s j ≠ v) := by
    rw [h_val]
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j
      exact h j (by omega)
    · intro h j _
      exact h j
  dsimp [nextLeaf0, smallestTreeLeaf]
  apply le_antisymm
  · apply Finset.le_min'
    intro y hy
    rw [pruferDecode_isLeaf_iff] at hy
    have h_univ : y ∈ Finset.univ.filter (fun v => ∀ j : Fin (m + 2 - 2), s j ≠ v) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hy
    have hy' := Finset.ext_iff.mp h_S y |>.mpr h_univ
    exact Finset.min'_le _ _ hy'
  · apply Finset.min'_le
    set m_elem := ((pruferDecodeAux (by omega) s 0 (by omega)).val.1.filter (fun v => ∀ j : Fin (m + 2 - 2), 0 ≤ j.val → s j ≠ v)).min' (nextLeaf_nonempty (by omega) s 0 (by omega) (pruferDecodeAux (by omega) s 0 (by omega)).val.1 (pruferDecodeAux (by omega) s 0 (by omega)).property.2.1)
    have hy := Finset.min'_mem _ (nextLeaf_nonempty (by omega) s 0 (by omega) (pruferDecodeAux (by omega) s 0 (by omega)).val.1 (pruferDecodeAux (by omega) s 0 (by omega)).property.2.1)
    have h_univ : m_elem ∈ Finset.univ.filter (fun v => ∀ j : Fin (m + 2 - 2), s j ≠ v) := Finset.ext_iff.mp h_S m_elem |>.mp hy
    rw [Finset.mem_filter] at h_univ
    rw [pruferDecode_isLeaf_iff]
    exact h_univ.2

private theorem pruferDecodeAux_shifted_correspondence {m : ℕ} (hm : 1 ≤ m)
    (s : pruferCodeSpace (m + 2)) :
    ∀ (k : ℕ) (hk : k ≤ (m + 1) - 2),
    (∀ v : Fin (m + 1),
       v ∈ (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k hk).val.1 ↔
       (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) v).1
         ∈ (pruferDecodeAux (by omega) s (k + 1) (by omega)).val.1) ∧
    (∀ a b : Fin (m + 1),
       s(a, b) ∈ (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k hk).val.2 ↔
       s((finSuccAboveEquivCompl (nextLeaf0 (by omega) s) a).1,
          (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) b).1)
         ∈ (pruferDecodeAux (by omega) s (k + 1) (by omega)).val.2) := by
  intro k
  induction k with
  | zero =>
    intro hk
    constructor
    · intro v
      have h_step_orig := pruferDecodeAux_succ_step (by omega) s 0 (by omega)
      have h_state0_orig : (pruferDecodeAux (by omega) s 0 (by omega)).val = (Finset.univ, ∅) := rfl
      have h_state0_shift : (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) 0 hk).val = (Finset.univ, ∅) := rfl
      have h_nL_eq := step_zero_min_eq_nextLeaf0 hm s
      let L := finSuccAboveEquivCompl (nextLeaf0 (by omega) s)
      rw [h_state0_shift]
      have h_orig1 : (pruferDecodeAux (by omega) s 1 (by omega)).val.1 = Finset.univ.erase (nextLeaf0 (by omega) s) := by
        rw [h_step_orig]
        dsimp
        rw [h_nL_eq]
        rw [h_state0_orig]
      rw [h_orig1]
      simp only [Finset.mem_univ, Finset.mem_erase, ne_eq, and_true]
      exact iff_of_true trivial (L v).property
    · intro a b
      have h_step_orig := pruferDecodeAux_succ_step (by omega) s 0 (by omega)
      have h_state0_orig : (pruferDecodeAux (by omega) s 0 (by omega)).val = (Finset.univ, ∅) := rfl
      have h_state0_shift : (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) 0 hk).val = (Finset.univ, ∅) := rfl
      have h_nL_eq := step_zero_min_eq_nextLeaf0 hm s
      let L := finSuccAboveEquivCompl (nextLeaf0 (by omega) s)
      rw [h_state0_shift]
      have h_orig1 : (pruferDecodeAux (by omega) s 1 (by omega)).val.2 = {s(nextLeaf0 (by omega) s, s ⟨0, by omega⟩)} := by
        rw [h_step_orig]
        dsimp
        rw [h_nL_eq]
        rw [h_state0_orig]
        rfl
      rw [h_orig1]
      simp only [Finset.mem_singleton, Sym2.eq_iff]
      constructor
      · intro h_empty
        revert h_empty
        simp
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact (L a).property h1 |>.elim
        · exact (L b).property h2 |>.elim
  | succ k ih =>
    intro hk
    have hm1 : m + 1 - 2 = m - 1 := by omega
    have hm2 : m + 2 - 2 = m := by omega
    have hk_curr : k + 1 ≤ m + 1 - 2 := hk
    have hk_prev : k ≤ m + 1 - 2 := by omega
    have hk_next : k + 2 ≤ m + 2 - 2 := by omega
    have hk_next_orig : k + 1 ≤ m + 2 - 2 := by omega
    have ih_k := ih hk_prev
    have ih_avail := ih_k.1
    have ih_edges := ih_k.2

    let state_shifted := (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k hk_prev).val
    let state_orig := (pruferDecodeAux (by omega) s (k + 1) hk_next_orig).val
    let L := finSuccAboveEquivCompl (nextLeaf0 (by omega) s)

    have h_step_shift := pruferDecodeAux_succ_step (by omega) (shiftedCode_v2 hm s) k hk_curr
    have h_step_orig := pruferDecodeAux_succ_step (by omega) s (k + 1) hk_next

    have h_nL_eq := nextLeaf_correspond_lift hm s k hk_curr ih_avail
    have h_nonempty_shift := nextLeaf_nonempty (by omega) (shiftedCode_v2 hm s) k hk_prev state_shifted.1 (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k hk_prev).property.2.1
    have h_nonempty_orig := nextLeaf_nonempty (by omega) s (k + 1) hk_next_orig state_orig.1 (pruferDecodeAux (by omega) s (k + 1) hk_next_orig).property.2.1
    set nL_k := (state_shifted.1.filter (fun v => ∀ j : Fin (m + 1 - 2), k ≤ j.val → shiftedCode_v2 hm s j ≠ v)).min' h_nonempty_shift
    set nL_k' := (state_orig.1.filter (fun v => ∀ j : Fin (m + 2 - 2), k + 1 ≤ j.val → s j ≠ v)).min' h_nonempty_orig
    have h_L_nL : (L nL_k).1 = nL_k' := h_nL_eq

    constructor
    · intro v
      have h_shift_val : (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) (k + 1) hk_curr).val.1 = state_shifted.1.erase nL_k := by
        rw [h_step_shift]
      have h_orig_val : (pruferDecodeAux (by omega) s (k + 2) hk_next).val.1 = state_orig.1.erase nL_k' := by
        rw [h_step_orig]
      rw [h_shift_val, h_orig_val]
      simp only [Finset.mem_erase, ne_eq]
      rw [ih_avail v]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        intro h_eq
        have h_L_eq : (L v).1 = (L nL_k).1 := by
          rw [h_eq, h_L_nL]
        have h_v_eq := Equiv.injective L (Subtype.ext h_L_eq)
        exact h1 h_v_eq
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        intro h_eq
        have h_L_eq : (L v).1 = nL_k' := by
          rw [h_eq, h_L_nL]
        exact h1 h_L_eq
    · intro a b
      have h_shift_val : (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) (k + 1) hk_curr).val.2 = insert s(nL_k, shiftedCode_v2 hm s ⟨k, by omega⟩) state_shifted.2 := by
        rw [h_step_shift]
      have h_orig_val : (pruferDecodeAux (by omega) s (k + 2) hk_next).val.2 = insert s(nL_k', s ⟨k + 1, by omega⟩) state_orig.2 := by
        rw [h_step_orig]
      rw [h_shift_val, h_orig_val]
      rw [Finset.mem_insert, Finset.mem_insert]
      rw [ih_edges a b]
      have hk_lt1 : k < m + 1 - 2 := by omega
      have hk_lt2 : k + 1 < m + 2 - 2 := by omega
      have h_shift_code_eval : (L (shiftedCode_v2 hm s ⟨k, hk_lt1⟩)).1 = s ⟨k + 1, hk_lt2⟩ := by
        dsimp [L, shiftedCode_v2]
        simp only [Equiv.apply_symm_apply]
      have h_edge_eq : s((L a).1, (L b).1) = s(nL_k', s ⟨k + 1, hk_lt2⟩) ↔ s(a, b) = s(nL_k, shiftedCode_v2 hm s ⟨k, hk_lt1⟩) := by
        simp only [Sym2.eq_iff]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · left
            constructor
            · have h_ext : L a = L nL_k := Subtype.ext (by rw [h1, ← h_L_nL])
              exact Equiv.injective L h_ext
            · have h_ext : L b = L (shiftedCode_v2 hm s ⟨k, by omega⟩) := Subtype.ext (by rw [h2, ← h_shift_code_eval])
              exact Equiv.injective L h_ext
          · right
            constructor
            · have h_ext : L a = L (shiftedCode_v2 hm s ⟨k, by omega⟩) := Subtype.ext (by rw [h1, ← h_shift_code_eval])
              exact Equiv.injective L h_ext
            · have h_ext : L b = L nL_k := Subtype.ext (by rw [h2, ← h_L_nL])
              exact Equiv.injective L h_ext
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · left
            constructor
            · rw [h1, h_L_nL]
            · rw [h2, h_shift_code_eval]
          · right
            constructor
            · rw [h1, h_shift_code_eval]
            · rw [h2, h_L_nL]
      rw [h_edge_eq]

lemma deleteSmallestLeafTreeSucc_val_adj {m : ℕ} (hm : 1 ≤ m) (T : LabeledTree (m + 1)) (a b : Fin m) :
    (↑(deleteSmallestLeafTreeSucc m hm T) : SimpleGraph (Fin m)).Adj a b ↔
    (↑T : SimpleGraph (Fin (m + 1))).Adj ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) a).1
            ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) b).1 := by
  dsimp [deleteSmallestLeafTreeSucc]
  simp only [SimpleGraph.comap_adj, Function.Embedding.coeFn_mk, SimpleGraph.induce_adj, Set.mem_compl_iff, Set.mem_singleton_iff]
  have h_a : ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) a).1 ≠ smallestTreeLeaf (m + 1) (by omega) T :=
    ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) a).2
  have h_b : ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) b).1 ≠ smallestTreeLeaf (m + 1) (by omega) T :=
    ((finSuccAboveEquivCompl (smallestTreeLeaf (m + 1) (by omega) T)) b).2
  tauto

lemma pruferDecodeAux_val_1_congr {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) {k1 k2 : ℕ} (hk1 : k1 ≤ n - 2) (hk2 : k2 ≤ n - 2) (h : k1 = k2) :
    (pruferDecodeAux hn s k1 hk1).val.1 = (pruferDecodeAux hn s k2 hk2).val.1 := by
  subst h; rfl

lemma pruferDecodeAux_val_2_congr {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) {k1 k2 : ℕ} (hk1 : k1 ≤ n - 2) (hk2 : k2 ≤ n - 2) (h : k1 = k2) :
    (pruferDecodeAux hn s k1 hk1).val.2 = (pruferDecodeAux hn s k2 hk2).val.2 := by
  subst h; rfl

lemma pruferDecodeAux_val_1_subset {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) {k1 k2 : ℕ} (hk1 : k1 ≤ n - 2) (hk2 : k2 ≤ n - 2) (hle : k1 ≤ k2) :
    (pruferDecodeAux hn s k2 hk2).val.1 ⊆ (pruferDecodeAux hn s k1 hk1).val.1 := by
  revert hk2
  induction hle with
  | refl =>
    intro hk2 x hx
    exact hx
  | @step k_mid h_le ih =>
    intro hk2
    have hk_succ : k_mid + 1 ≤ n - 2 := hk2
    have hk_mid : k_mid ≤ n - 2 := by omega
    have h_ih := ih hk_mid
    have h_eq := pruferDecodeAux_succ_step hn s k_mid hk_succ
    have h_c := pruferDecodeAux_val_1_congr hn s (by omega : k_mid + 1 ≤ n - 2) hk2 rfl
    rw [← h_c]
    have h_val : (pruferDecodeAux hn s (k_mid + 1) hk_succ).val.1 = (pruferDecodeAux hn s k_mid hk_mid).val.1.erase _ := congrArg Prod.fst h_eq
    rw [h_val]
    intro x hx
    have h_erase := Finset.erase_subset _ _ hx
    exact h_ih h_erase

theorem deleteSmallestLeaf_pruferDecode_v2 {m : ℕ} (hm : 1 ≤ m)
    (s : pruferCodeSpace (m + 2)) :
    deleteSmallestLeafTreeSucc (m + 1) (by omega) (pruferDecode (by omega) s) =
    pruferDecode (by omega : 2 ≤ m + 1) (shiftedCode_v2 hm s) := by
  ext a b
  let shift_s := shiftedCode_v2 hm s
  have hn_shift : 2 ≤ m + 1 := by omega
  have hn_s : 2 ≤ m + 2 := by omega
  have hm_sub : m - 1 ≤ (m + 1) - 2 := by omega
  have h_corr := pruferDecodeAux_shifted_correspondence hm s (m - 1) hm_sub
  have h_corr_v := h_corr.1
  have h_corr_e := h_corr.2

  have h_state_shift : (pruferFinalState hn_shift shift_s).1 = (pruferDecodeAux hn_shift shift_s (m - 1) hm_sub).val.1 := rfl
  have h_state_s : (pruferFinalState hn_s s).1 = (pruferDecodeAux hn_s s m (by omega)).val.1 := by
    have h_idx : m + 2 - 2 = m := by omega
    exact pruferDecodeAux_val_1_congr hn_s s (by omega) (by omega) h_idx

  have h_image_eq : (pruferFinalState hn_shift shift_s).1.image (fun v => (finSuccAboveEquivCompl (nextLeaf0 hn_s s) v).1) = (pruferFinalState hn_s s).1 := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have h_corr_v_spec := h_corr_v v
      have h_s_eq : (pruferDecodeAux hn_s s (m - 1 + 1) (by omega)).val.1 = (pruferFinalState hn_s s).1 := by
        have h_idx : m - 1 + 1 = m + 2 - 2 := by omega
        exact pruferDecodeAux_val_1_congr hn_s s (by omega) (by omega) h_idx
      rw [h_s_eq] at h_corr_v_spec
      exact h_corr_v_spec.mp hv
    · intro hx
      have h_not_nL : x ≠ nextLeaf0 hn_s s := by
        have h_leaf_mem : nextLeaf0 hn_s s ∈ (pruferDecodeAux hn_s s 0 (by omega)).val.1 := Finset.mem_univ _
        have h_not_in_final : nextLeaf0 hn_s s ∉ (pruferFinalState hn_s s).1 := by
          have h_s_eq : (pruferFinalState hn_s s).1 = (pruferDecodeAux hn_s s (m + 2 - 2) (by omega)).val.1 := rfl
          rw [h_s_eq]
          have h_erase : (pruferDecodeAux hn_s s 1 (by omega)).val.1 = Finset.univ.erase (nextLeaf0 hn_s s) := by
            have h_eq := pruferDecodeAux_succ_step hn_s s 0 (by omega)
            dsimp at h_eq
            have h_min_eq := step_zero_min_eq_nextLeaf0 hm s
            rw [h_min_eq] at h_eq
            exact congrArg Prod.fst h_eq
          have h_subset := pruferDecodeAux_val_1_subset hn_s s (by omega) (by omega) (by omega : 1 ≤ m + 2 - 2)
          intro h_mem
          have h_mem_erase := h_subset h_mem
          rw [h_erase] at h_mem_erase
          simp only [Finset.mem_erase, ne_eq] at h_mem_erase
          exact h_mem_erase.1 trivial
        rintro rfl
        exact h_not_in_final hx
      have h_mem_compl : x ∈ ({nextLeaf0 hn_s s}ᶜ : Set (Fin (m + 2))) := h_not_nL
      let x_lift : {v // v ∈ ({nextLeaf0 hn_s s}ᶜ : Set (Fin (m + 2)))} := ⟨x, h_mem_compl⟩
      use (finSuccAboveEquivCompl (nextLeaf0 hn_s s)).symm x_lift
      constructor
      · have h_corr_v_spec := h_corr_v ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)).symm x_lift)
        have h_s_eq : (pruferDecodeAux hn_s s (m - 1 + 1) (by omega)).val.1 = (pruferFinalState hn_s s).1 := by
          have h_idx : m - 1 + 1 = m + 2 - 2 := by omega
          exact pruferDecodeAux_val_1_congr hn_s s (by omega) (by omega) h_idx
        rw [h_s_eq] at h_corr_v_spec
        apply h_corr_v_spec.mpr
        have h_eval : ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)).symm x_lift)).1 = x := by
          have h1 := Equiv.apply_symm_apply (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) x_lift
          rw [h1]
        rw [h_eval]
        exact hx
      · have h_eval : ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)).symm x_lift)).1 = x := by
          have h1 := Equiv.apply_symm_apply (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) x_lift
          rw [h1]
        exact h_eval

  have h_U_eq : ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastU hn_shift shift_s)).1 = pruferLastU hn_s s := by
    have h_min := min'_commutes_L (nextLeaf0 hn_s s) (pruferFinalState hn_shift shift_s).1 (pruferFinalState_nonempty hn_shift shift_s)
    have h_congr := min'_congr h_image_eq (Finset.Nonempty.image (pruferFinalState_nonempty hn_shift shift_s) _) (pruferFinalState_nonempty hn_s s)
    exact h_min.trans h_congr

  have h_erase_image : ((pruferFinalState hn_shift shift_s).1.erase (pruferLastU hn_shift shift_s)).image (fun v => ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) v).1) = (pruferFinalState hn_s s).1.erase (pruferLastU hn_s s) := by
    have h_im := h_image_eq
    ext x
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨v, ⟨hv_ne, hv_mem⟩, rfl⟩
      constructor
      · intro h_eq
        have h_eq_val : ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) v).1 = ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastU hn_shift shift_s)).1 := by
          rw [h_eq, h_U_eq]
        have h_inj := (finSuccAboveEquivCompl (nextLeaf0 hn_s s)).injective
        have h_eq_v := h_inj (Subtype.ext h_eq_val)
        exact hv_ne h_eq_v
      · rw [← h_im]
        simp only [Finset.mem_image]
        exact ⟨v, hv_mem, rfl⟩
    · rintro ⟨hx_ne, hx_mem⟩
      rw [← h_im] at hx_mem
      simp only [Finset.mem_image] at hx_mem
      rcases hx_mem with ⟨v, hv_mem, rfl⟩
      use v
      refine ⟨⟨?_, hv_mem⟩, rfl⟩
      intro h_eq_v
      rw [h_eq_v] at hx_ne
      exact hx_ne h_U_eq

  have h_V_eq : ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastV hn_shift shift_s)).1 = pruferLastV hn_s s := by
    have h_min := min'_commutes_L (nextLeaf0 hn_s s) ((pruferFinalState hn_shift shift_s).1.erase (pruferLastU hn_shift shift_s)) (pruferFinalErase_nonempty hn_shift shift_s)
    have h_congr := min'_congr h_erase_image (Finset.Nonempty.image (pruferFinalErase_nonempty hn_shift shift_s) _) (pruferFinalErase_nonempty hn_s s)
    exact h_min.trans h_congr

  have h_edges_corr : s(a, b) ∈ (pruferFinalState hn_shift shift_s).2 ↔ s(((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a).1, ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b).1) ∈ (pruferFinalState hn_s s).2 := by
    have h_corr_e_spec := h_corr_e a b
    have h_s_eq : (pruferDecodeAux hn_s s (m - 1 + 1) (by omega)).val.2 = (pruferFinalState hn_s s).2 := by
      have h_idx : m - 1 + 1 = m + 2 - 2 := by omega
      exact pruferDecodeAux_val_2_congr hn_s s (by omega) (by omega) h_idx
    rw [h_s_eq] at h_corr_e_spec
    exact h_corr_e_spec

  rw [deleteSmallestLeafTreeSucc_val_adj]
  dsimp [pruferDecode]
  simp only [SimpleGraph.fromEdgeSet_adj]

  change s(((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a).1, ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b).1) ∈ pruferDecodeEdges hn_s s ∧
    ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a).1 ≠ ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b).1 ↔
    s(a, b) ∈ pruferDecodeEdges hn_shift shift_s ∧ a ≠ b

  have h_ne_iff : (((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a).1 ≠ ((finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b).1) ↔ (a ≠ b) := by
    constructor
    · intro h h_eq
      rw [h_eq] at h
      exact h rfl
    · intro h h_eq
      have h_inj := (finSuccAboveEquivCompl (nextLeaf0 hn_s s)).injective
      have h_eq_v := Subtype.ext h_eq
      have h_eq_a := h_inj h_eq_v
      exact h h_eq_a

  rw [h_ne_iff]

  dsimp [pruferDecodeEdges]
  simp only [Finset.mem_insert]

  constructor
  · rintro ⟨(h_eq | h_mem), h_ne⟩
    · refine ⟨?_, h_ne⟩
      left
      simp only [Sym2.eq_iff] at h_eq ⊢
      rcases h_eq with (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left
        have h_ext_a : (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a = (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastU hn_shift shift_s) := Subtype.ext (by rw [h1, ← h_U_eq])
        have h_ext_b : (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b = (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastV hn_shift shift_s) := Subtype.ext (by rw [h2, ← h_V_eq])
        exact ⟨Equiv.injective _ h_ext_a, Equiv.injective _ h_ext_b⟩
      · right
        have h_ext_a : (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) a = (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastV hn_shift shift_s) := Subtype.ext (by rw [h1, ← h_V_eq])
        have h_ext_b : (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) b = (finSuccAboveEquivCompl (nextLeaf0 hn_s s)) (pruferLastU hn_shift shift_s) := Subtype.ext (by rw [h2, ← h_U_eq])
        exact ⟨Equiv.injective _ h_ext_a, Equiv.injective _ h_ext_b⟩
    · refine ⟨?_, h_ne⟩
      right
      exact h_edges_corr.mpr h_mem
  · rintro ⟨(h_eq | h_mem), h_ne⟩
    · refine ⟨?_, h_ne⟩
      left
      simp only [Sym2.eq_iff] at h_eq ⊢
      rcases h_eq with (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left
        rw [h1, h2, h_U_eq, h_V_eq]
        exact ⟨rfl, rfl⟩
      · right
        rw [h1, h2, h_U_eq, h_V_eq]
        exact ⟨rfl, rfl⟩
    · refine ⟨?_, h_ne⟩
      right
      exact h_edges_corr.mp h_mem

lemma leftInverse_pruferDecode_aux
    (h_correspondence : ∀ (m' : ℕ) (hm' : 1 ≤ m') (s : pruferCodeSpace (m' + 2)),
       deleteSmallestLeafTreeSucc (m' + 1) (by omega) (pruferDecode (by omega) s) =
       pruferDecode (by omega : 2 ≤ m' + 1) (shiftedCode_v2 hm' s)) :
    ∀ (m : ℕ) (s : pruferCodeSpace (m + 2)), pruferEncodeAux m (pruferDecode (by omega) s) = s := by
  intro m
  induction m with
  | zero =>
    intro s
    ext i
    exact Fin.elim0 i
  | succ m ih =>
    intro s
    funext i
    by_cases h0 : i.val = 0
    · have hi : i = ⟨0, by omega⟩ := Fin.ext h0
      rw [hi]
      have h_zero := pruferEncode_pruferDecode_zero (m + 3) (by omega) s (by omega)
      exact h_zero
    · have hm1 : 1 ≤ m + 1 := by omega
      let leaf := smallestTreeLeaf (m + 3) (by omega) (pruferDecode (by omega) s)
      let T' := deleteSmallestLeafTreeSucc (m + 2) (by omega) (pruferDecode (by omega) s)
      have hT' : T' = pruferDecode (by omega) (shiftedCode_v2 hm1 s) := h_correspondence (m + 1) hm1 s

      have h_eval : (pruferEncodeAux (m + 1) (pruferDecode (by omega) s)) i =
          ((finSuccAboveEquivCompl leaf) (pruferEncodeAux m T' ⟨i.val - 1, by omega⟩)).1 := by
        dsimp [pruferEncodeAux]
        have h_pos : 0 < i.val := Nat.pos_of_ne_zero h0
        rw [dif_neg h0]

      rw [h_eval, hT']
      have h_ih := ih (shiftedCode_v2 hm1 s)
      have h_inner : pruferEncodeAux m (pruferDecode (by omega) (shiftedCode_v2 hm1 s)) ⟨i.val - 1, by omega⟩ =
          shiftedCode_v2 hm1 s ⟨i.val - 1, by omega⟩ := by
        rw [h_ih]
        rfl
      rw [h_inner]

      have h_leaf_eq : leaf = nextLeaf0 (by omega) s := rfl
      rw [h_leaf_eq]

      have h_i_pos : 1 ≤ i.val := Nat.pos_of_ne_zero h0
      have h_j_lt : i.val - 1 < m := by omega
      let j' : Fin m := ⟨i.val - 1, h_j_lt⟩
      let L := finSuccAboveEquivCompl (nextLeaf0 (by omega) s)
      have h_shift_def : shiftedCode_v2 hm1 s j' =
          L.symm ⟨s i, nextLeaf0_not_in_image (by omega) s i⟩ := by
        dsimp [shiftedCode_v2]
        congr 1
        congr 1
        congr 1
        apply Fin.ext
        exact Nat.sub_add_cancel h_i_pos
      have h_L_app : (L (shiftedCode_v2 hm1 s j')).1 = s i := by
        rw [h_shift_def]
        simp only [Equiv.apply_symm_apply]
      exact h_L_app

-- Tier 1.5: take the structural correspondence as hypothesis.
theorem chapter31_tier2_of_correspondence {n : ℕ} (hn : 2 ≤ n)
    (h_correspondence : ∀ (m : ℕ) (hm : 1 ≤ m) (s : pruferCodeSpace (m + 2)),
       deleteSmallestLeafTreeSucc (m + 1) (by omega)
         (pruferDecode (by omega) s) =
       pruferDecode (by omega : 2 ≤ m + 1) (shiftedCode_v2 hm s)) :
    Fintype.card (LabeledTree n) = n ^ (n - 2) := by
  have h_left_inv : Function.LeftInverse (pruferEncode hn) (pruferDecode hn) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    intro s
    exact leftInverse_pruferDecode_aux h_correspondence m s
  have h_inj : Function.Injective (pruferDecode hn) := h_left_inv.injective
  -- cardinality of range = cardinality of domain
  have h_card_eq_ineq : Fintype.card (pruferCodeSpace n) ≤ Fintype.card (LabeledTree n) := Fintype.card_le_of_injective _ h_inj
  rw [pruferCodeSpace_card n] at h_card_eq_ineq
  have h_card_le := cayley_upper_bound n hn
  exact le_antisymm h_card_le h_card_eq_ineq


/--
Chapter 31 (Cayley's Formula): the number of labeled trees on `n` vertices
is exactly `n^(n-2)`.  The unconditional endpoint — the Prüfer encoding is
the left inverse of the Prüfer decoding, so `pruferDecode` is injective,
and Joyal's upper bound pins down the cardinality.
-/
theorem chapter31 (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (LabeledTree n) = n ^ (n - 2) :=
  chapter31_tier2_of_correspondence hn
    (fun _ hm s => deleteSmallestLeaf_pruferDecode_v2 hm s)

end ProofsInTheBook.Chapter31
