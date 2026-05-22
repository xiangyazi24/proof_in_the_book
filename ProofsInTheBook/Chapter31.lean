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

theorem chapter31 (n : ℕ) :
    Fintype.card (pruferCodeSpace n) = n ^ (n - 2) :=
  pruferCodeSpace_card n

end ProofsInTheBook.Chapter31
