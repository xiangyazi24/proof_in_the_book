import Mathlib

/-!
# Chapter 39: The chromatic number of Kneser graphs

From "Proofs from THE BOOK":

**Lovász's theorem**: χ(KG(n,k)) = n - 2k + 2.

The book presents Bárány's short proof using the Borsuk-Ulam theorem:
if KG(n,k) were (n-2k+1)-colorable, one could construct a continuous
map S^{n-2k+1} → ℝ^{n-2k} with no antipodal pair mapping to the same
point, contradicting Borsuk-Ulam.

Formalization status: this file closes the graph-combinatorial layer.  It
defines the Kneser graph, proves basic cardinality and edge facts, proves the
explicit `n - 2*k + 2` coloring upper bound, handles the `n = 2*k` lower-bound
edge case, and states `chapter39` from a `KneserChromaticCertificate` carrying
the hard non-colorability direction.

Gap to the full book theorem: the missing upstream theorem can be supplied by
either the analytic Borsuk-Ulam route or the discrete Matoušek/Tucker route.
The local Mathlib checkout has general topological and abstract/geometric
simplicial-complex infrastructure, but no Borsuk-Ulam theorem, Tucker lemma,
Ky Fan lemma, octahedral sphere labeling theorem, or ready-made bridge from
too-small Kneser colorings to a forbidden antipodal/complementary labeling.

The definitions `TuckerLemmaStatement` and
`KneserColoringProducesTuckerCounterexample` below isolate the discrete route:
Tucker's lemma for nonzero sign vectors in `{−1,0,1}^n`, plus Matoušek's
construction of a Tucker counterexample from a hypothetical
`(n - 2*k + 1)`-coloring of `KG(n,k)`.  Proving those two statements is the
honest frontier; the file does not package them as `False`.
-/

namespace ProofsInTheBook.Chapter39

/-- Vertices of the Kneser graph `KG(n,k)`: the `k`-subsets of `[n]`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

instance (n k : ℕ) : Fintype (KneserVertex n k) := by
  dsimp [KneserVertex]
  infer_instance

instance (n k : ℕ) : DecidableEq (KneserVertex n k) := by
  dsimp [KneserVertex]
  infer_instance

/-- The Kneser graph: vertices are `k`-subsets, adjacent when disjoint. -/
def kneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj a b := a ≠ b ∧ Disjoint (a : Finset (Fin n)) (b : Finset (Fin n))
  symm := by
    intro a b h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨by
    intro a h
    exact h.1 rfl⟩

theorem kneserGraph_adj_iff {n k : ℕ} (a b : KneserVertex n k) :
    (kneserGraph n k).Adj a b ↔
      a ≠ b ∧ Disjoint (a : Finset (Fin n)) (b : Finset (Fin n)) :=
  Iff.rfl

/-- Symmetry of Kneser adjacency, exposed as a named theorem
(`SimpleGraph.Adj.symm` already provides this generically). -/
theorem kneserGraph_adj_symm {n k : ℕ} {a b : KneserVertex n k}
    (h : (kneserGraph n k).Adj a b) : (kneserGraph n k).Adj b a :=
  (kneserGraph n k).symm h

/-- Kneser adjacency is irreflexive: no vertex is adjacent to itself. -/
@[simp]
theorem kneserGraph_not_adj_self {n k : ℕ} (a : KneserVertex n k) :
    ¬ (kneserGraph n k).Adj a a := by
  intro h
  exact h.1 rfl

/-- An adjacency in `kneserGraph n k` forces the underlying subsets to be
disjoint (the constructive form of the second conjunct). -/
theorem disjoint_of_kneserGraph_adj {n k : ℕ} {a b : KneserVertex n k}
    (h : (kneserGraph n k).Adj a b) :
    Disjoint (a : Finset (Fin n)) (b : Finset (Fin n)) := h.2

/-- An adjacency in `kneserGraph n k` forces the two vertices to be distinct. -/
theorem ne_of_kneserGraph_adj {n k : ℕ} {a b : KneserVertex n k}
    (h : (kneserGraph n k).Adj a b) : a ≠ b := h.1

/--
Any coloring of a Kneser graph assigns different colors to disjoint
`k`-subsets.
-/
theorem kneser_coloring_separates_disjoint {n k q : ℕ}
    (C : (kneserGraph n k).Coloring (Fin q)) {a b : KneserVertex n k}
    (hne : a ≠ b) (hdisj : Disjoint (a : Finset (Fin n)) (b : Finset (Fin n))) :
    C a ≠ C b := by
  exact C.valid ⟨hne, hdisj⟩

/--
The first finite-counting layer in the Kneser graph proof: `KG(n,k)` has
`n choose k` vertices.
-/
theorem kneserVertex_card (n k : ℕ) :
    Fintype.card (KneserVertex n k) = n.choose k := by
  rw [Fintype.card_subtype]
  have hset :
      ({s | s.card = k} : Finset (Finset (Fin n))) =
        Finset.powersetCard k Finset.univ := by
    ext s
    simp [Finset.mem_powersetCard]
  rw [hset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The Kneser graph has at least one vertex when `k ≤ n`. -/
theorem kneserVertex_nonempty_of_le {n k : ℕ} (h : k ≤ n) :
    Nonempty (KneserVertex n k) := by
  rw [← Fintype.card_pos_iff, kneserVertex_card]
  exact Nat.choose_pos h

/-- The Kneser graph has no vertices when `k > n`. -/
theorem kneserGraph_no_vertices_of_lt {n k : ℕ} (h : n < k) :
    IsEmpty (KneserVertex n k) := by
  rw [← Fintype.card_eq_zero_iff, kneserVertex_card]
  exact Nat.choose_eq_zero_of_lt h

/-- The Kneser graph has no edges when `2k > n` (no two disjoint k-subsets fit). -/
theorem kneserGraph_no_adj_of_lt {n k : ℕ} (_hk : 1 ≤ k) (h : n < 2 * k)
    (a b : KneserVertex n k) :
    ¬ (kneserGraph n k).Adj a b := by
  intro ⟨_, hdisj⟩
  have hcard : (↑a ∪ ↑b : Finset (Fin n)).card = 2 * k := by
    rw [Finset.card_union_of_disjoint hdisj, a.2, b.2, two_mul]
  have hle : (↑a ∪ ↑b : Finset (Fin n)).card ≤ Fintype.card (Fin n) :=
    (↑a ∪ ↑b : Finset (Fin n)).card_le_univ
  rw [Fintype.card_fin] at hle
  omega

/-- For `k = 0`, the Kneser graph has exactly one vertex (the empty set). -/
theorem kneserVertex_card_zero (n : ℕ) :
    Fintype.card (KneserVertex n 0) = 1 := by
  rw [kneserVertex_card, Nat.choose_zero_right]

/-- For `k = n`, the Kneser graph has exactly one vertex (the full set `[n]`). -/
theorem kneserVertex_card_eq_one_of_eq (n : ℕ) :
    Fintype.card (KneserVertex n n) = 1 := by
  rw [kneserVertex_card, Nat.choose_self]

/-- For `k = 0`, the Kneser graph has no edges (only one vertex). -/
theorem kneserGraph_zero_no_adj (n : ℕ) (a b : KneserVertex n 0) :
    ¬ (kneserGraph n 0).Adj a b := by
  intro h
  apply h.1
  have ha : (a.1 : Finset (Fin n)) = ∅ := Finset.card_eq_zero.mp a.2
  have hb : (b.1 : Finset (Fin n)) = ∅ := Finset.card_eq_zero.mp b.2
  exact Subtype.ext (ha.trans hb.symm)

/-- KG(n, 0) is the empty graph (zero edges). -/
theorem kneserGraph_zero_eq_bot (n : ℕ) :
    kneserGraph n 0 = (⊥ : SimpleGraph (KneserVertex n 0)) := by
  ext a b
  simp only [SimpleGraph.bot_adj]
  refine ⟨fun h => kneserGraph_zero_no_adj n a b h, fun h => ?_⟩
  exact (h.elim : (kneserGraph n 0).Adj a b)

/-- KG(n, 1) is the complete graph on n vertices, as a SimpleGraph equality. -/
theorem kneserGraph_one_eq_completeGraph (n : ℕ) :
    kneserGraph n 1 = SimpleGraph.completeGraph (KneserVertex n 1) := by
  ext a b
  rw [kneserGraph_adj_iff]
  simp only [SimpleGraph.completeGraph_eq_top, SimpleGraph.top_adj, ne_eq]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    rw [Finset.disjoint_left]
    intro x hxa hxb
    have ha_card : (a.1 : Finset (Fin n)).card = 1 := a.2
    have hb_card : (b.1 : Finset (Fin n)).card = 1 := b.2
    have ha_eq : (a.1 : Finset (Fin n)) = {x} := by
      rcases Finset.card_eq_one.mp ha_card with ⟨y, hy⟩
      rw [hy] at hxa
      rw [Finset.mem_singleton] at hxa
      rw [hy, hxa]
    have hb_eq : (b.1 : Finset (Fin n)) = {x} := by
      rcases Finset.card_eq_one.mp hb_card with ⟨y, hy⟩
      rw [hy] at hxb
      rw [Finset.mem_singleton] at hxb
      rw [hy, hxb]
    exact h (Subtype.ext (ha_eq.trans hb_eq.symm))

/-- For `k = 1`, the Kneser graph is the complete graph: any two distinct
singleton vertices are adjacent.  (KG(n, 1) ≅ K_n.) -/
theorem kneserGraph_one_adj_of_ne (n : ℕ) (a b : KneserVertex n 1) (h_ne : a ≠ b) :
    (kneserGraph n 1).Adj a b := by
  refine ⟨h_ne, ?_⟩
  rw [Finset.disjoint_left]
  intro x hxa hxb
  -- Both a.1 and b.1 are singletons (card = 1), so x ∈ a.1 ∧ x ∈ b.1 forces a.1 = b.1.
  have ha_card : (a.1 : Finset (Fin n)).card = 1 := a.2
  have hb_card : (b.1 : Finset (Fin n)).card = 1 := b.2
  have ha_eq : (a.1 : Finset (Fin n)) = {x} := by
    rcases Finset.card_eq_one.mp ha_card with ⟨y, hy⟩
    rw [hy] at hxa
    rw [Finset.mem_singleton] at hxa
    rw [hy, hxa]
  have hb_eq : (b.1 : Finset (Fin n)) = {x} := by
    rcases Finset.card_eq_one.mp hb_card with ⟨y, hy⟩
    rw [hy] at hxb
    rw [Finset.mem_singleton] at hxb
    rw [hy, hxb]
  exact h_ne (Subtype.ext (ha_eq.trans hb_eq.symm))

/-- When `2k ≤ n`, the Kneser graph has at least one edge — there exist two
disjoint k-subsets. -/
theorem kneserGraph_exists_adj_of_two_mul_le {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ a b : KneserVertex n k, (kneserGraph n k).Adj a b := by
  -- Build two explicit disjoint k-subsets: {0,...,k-1} and {k,...,2k-1}.
  let A : Finset (Fin n) := (Finset.Ico 0 k).attachFin (fun m hm => by
    rw [Finset.mem_Ico] at hm; omega)
  let B : Finset (Fin n) := (Finset.Ico k (2 * k)).attachFin (fun m hm => by
    rw [Finset.mem_Ico] at hm; omega)
  have hA_card : A.card = k := by
    simp [A, Finset.card_attachFin, Nat.Ico_eq_range']
  have hB_card : B.card = k := by
    simp [B, Finset.card_attachFin, Nat.Ico_eq_range', two_mul]
  refine ⟨⟨A, hA_card⟩, ⟨B, hB_card⟩, ?_, ?_⟩
  · intro h_eq
    have h_eq_set : A = B := by
      have := Subtype.ext_iff.mp h_eq
      simpa using this
    -- 0 ∈ A but 0 ∉ B (since the smallest element of B is k ≥ 1).
    have h0_A : (⟨0, by omega⟩ : Fin n) ∈ A := by
      simp [A, Finset.mem_attachFin]; omega
    have h0_B : (⟨0, by omega⟩ : Fin n) ∉ B := by
      simp [B, Finset.mem_attachFin, Finset.mem_Ico]
    rw [h_eq_set] at h0_A
    exact h0_B h0_A
  · rw [Finset.disjoint_left]
    intro x hxA hxB
    simp [A, B, Finset.mem_attachFin, Finset.mem_Ico] at hxA hxB
    omega

/--
The minimum element of a k-subset (well-defined since k ≥ 1).
-/
noncomputable def KneserVertex.min' {n k : ℕ} (hk : 1 ≤ k) (S : KneserVertex n k) : Fin n :=
  S.1.min' (by rw [Finset.nonempty_iff_ne_empty]; intro h; have := S.2; simp [h] at this; omega)

/--
The Kneser coloring by minimum element: color each k-subset by its minimum
when that minimum is ≤ n-2k, otherwise assign the default color n-2k+1.
-/
noncomputable def kneserColorNat {n k : ℕ} (hk : 1 ≤ k) (S : KneserVertex n k) : ℕ :=
  let m := (KneserVertex.min' hk S).val
  if m ≤ n - 2 * k then m else n - 2 * k + 1

theorem kneserColorNat_lt {n k : ℕ} (_hk : 1 ≤ k) (_h2k : 2 * k ≤ n)
    (S : KneserVertex n k) : kneserColorNat _hk S < n - 2 * k + 2 := by
  unfold kneserColorNat
  simp only
  by_cases h : (KneserVertex.min' _hk S).val ≤ n - 2 * k
  · simp [h]
    omega
  · simp [h]

noncomputable def kneserColor {n k : ℕ} (hk : 1 ≤ k) (h2k : 2 * k ≤ n) :
    KneserVertex n k → Fin (n - 2 * k + 2) :=
  fun S => ⟨kneserColorNat hk S, kneserColorNat_lt hk h2k S⟩

private theorem kneserColor_proper {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (a b : KneserVertex n k) (hadj : (kneserGraph n k).Adj a b) :
    kneserColor hk hn a ≠ kneserColor hk hn b := by
  intro heq
  have hdisj : Disjoint a.1 b.1 := hadj.2
  have hma_mem : KneserVertex.min' hk a ∈ a.1 := Finset.min'_mem _ _
  have hmb_mem : KneserVertex.min' hk b ∈ b.1 := Finset.min'_mem _ _
  have hne_min : (KneserVertex.min' hk a).val ≠ (KneserVertex.min' hk b).val := by
    intro h
    exact Finset.disjoint_left.mp hdisj hma_mem (by rwa [Fin.ext_iff.mpr h])
  simp only [kneserColor, Fin.mk.injEq] at heq
  unfold kneserColorNat at heq
  by_cases ha : (KneserVertex.min' hk a).val ≤ n - 2 * k <;>
    by_cases hb : (KneserVertex.min' hk b).val ≤ n - 2 * k <;>
    simp only [ha, hb, ite_true, ite_false] at heq
  · exact hne_min heq
  · omega
  · omega
  · have ha_neg := ha; have hb_neg := hb
    have ha_sub : ∀ x ∈ (↑a : Finset (Fin n)), n - 2 * k < x.val := by
      intro x hx; by_contra hle; push Not at hle
      exact ha_neg (Nat.le_trans (Finset.min'_le _ _ hx) hle)
    have hb_sub : ∀ x ∈ (↑b : Finset (Fin n)), n - 2 * k < x.val := by
      intro x hx; by_contra hle; push Not at hle
      exact hb_neg (Nat.le_trans (Finset.min'_le _ _ hx) hle)
    have hcard_union : ((↑a : Finset (Fin n)) ∪ ↑b).card = 2 * k := by
      rw [Finset.card_union_of_disjoint hdisj]
      have := a.2; have := b.2; omega
    have hsub : (↑a : Finset (Fin n)) ∪ ↑b ⊆ Finset.univ.filter fun i : Fin n => n - 2 * k < i.val := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rcases Finset.mem_union.mp hx with h | h
        · exact ha_sub x h
        · exact hb_sub x h⟩
    have hle := Finset.card_le_card hsub
    have hfilt_le : (Finset.univ.filter fun i : Fin n => n - 2 * k < i.val).card +
        (Finset.univ.filter fun i : Fin n => i.val ≤ n - 2 * k).card = n := by
      have := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (p := fun i => n - 2 * k < i.val)
      simp at this; omega
    have hlow : (Finset.univ.filter fun i : Fin n => i.val ≤ n - 2 * k).card ≥ n - 2 * k + 1 := by
      have : ∀ j : Fin (n - 2 * k + 1), (⟨j.val, by omega⟩ : Fin n) ∈
          Finset.univ.filter fun i : Fin n => i.val ≤ n - 2 * k := by
        intro j; simp; omega
      calc _ ≥ Fintype.card (Fin (n - 2 * k + 1)) := by
            exact Finset.card_le_card_of_injOn (fun j => ⟨j.val, by omega⟩)
              (fun j _ => this j) (fun a _ b _ h => by simp [Fin.ext_iff] at h; exact Fin.ext h)
        _ = n - 2 * k + 1 := Fintype.card_fin _
    omega

theorem kneser_chromatic_upper_bound (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
      ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b :=
  ⟨kneserColor hk hn, kneserColor_proper hk hn⟩

/-! ### Tucker-lemma route for the hard lower bound -/

/-- A sign vector in `{−1,0,1}^n`, represented by its positive and negative supports. -/
structure SignedSubset (n : ℕ) where
  pos : Finset (Fin n)
  neg : Finset (Fin n)
  disjoint : Disjoint pos neg

namespace SignedSubset

/-- Antipodal sign vector: swap positive and negative supports. -/
def antipode {n : ℕ} (X : SignedSubset n) : SignedSubset n where
  pos := X.neg
  neg := X.pos
  disjoint := X.disjoint.symm

/-- The sign vector is not the origin. -/
def Nonzero {n : ℕ} (X : SignedSubset n) : Prop :=
  X.pos.Nonempty ∨ X.neg.Nonempty

theorem antipode_nonzero {n : ℕ} (X : SignedSubset n) :
    X.antipode.Nonzero ↔ X.Nonzero := by
  simp [Nonzero, antipode, or_comm]

/-- Total support size of a sign vector. -/
def card {n : ℕ} (X : SignedSubset n) : ℕ :=
  X.pos.card + X.neg.card

theorem card_antipode {n : ℕ} (X : SignedSubset n) :
    X.antipode.card = X.card := by
  simp [card, antipode, Nat.add_comm]

theorem card_pos_of_nonzero {n : ℕ} {X : SignedSubset n} (hX : X.Nonzero) :
    0 < X.card := by
  rcases hX with hpos | hneg
  · simp [card, Finset.card_pos.2 hpos]
  · simp [card, Finset.card_pos.2 hneg]

/-- The unsigned support of a sign vector. -/
def support {n : ℕ} (X : SignedSubset n) : Finset (Fin n) :=
  X.pos ∪ X.neg

theorem support_antipode {n : ℕ} (X : SignedSubset n) :
    X.antipode.support = X.support := by
  ext i
  simp [support, antipode, or_comm]

theorem support_nonempty_iff_nonzero {n : ℕ} (X : SignedSubset n) :
    X.support.Nonempty ↔ X.Nonzero := by
  simp [support, Nonzero]

/-- The largest coordinate in the support of a nonzero sign vector. -/
noncomputable def maxSupport {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) : Fin n :=
  X.support.max' ((support_nonempty_iff_nonzero X).mpr hX)

theorem maxSupport_mem_support {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) :
    X.maxSupport hX ∈ X.support := by
  exact Finset.max'_mem _ _

theorem maxSupport_antipode {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) :
    X.antipode.maxSupport ((antipode_nonzero X).mpr hX) = X.maxSupport hX := by
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    have hy' : y ∈ X.support := by
      simpa [support_antipode] using hy
    exact Finset.le_max' _ y hy'
  · apply Finset.max'_le
    intro y hy
    have hy' : y ∈ X.antipode.support := by
      simpa [support_antipode] using hy
    exact Finset.le_max' _ y hy'

/-- The sign of the largest supported coordinate, used in Matoušek's small-support labels. -/
noncomputable def maxSupportPositive {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) : Bool :=
  decide (X.maxSupport hX ∈ X.pos)

theorem maxSupportPositive_antipode {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) :
    X.antipode.maxSupportPositive ((antipode_nonzero X).mpr hX) =
      !(X.maxSupportPositive hX) := by
  unfold maxSupportPositive
  rw [maxSupport_antipode]
  change decide (X.maxSupport hX ∈ X.neg) = !decide (X.maxSupport hX ∈ X.pos)
  by_cases hpos : X.maxSupport hX ∈ X.pos
  · have hnotneg : X.maxSupport hX ∉ X.neg := by
      intro hneg
      exact (Finset.disjoint_left.mp X.disjoint) hpos hneg
    simp [hpos, hnotneg]
  · have hneg : X.maxSupport hX ∈ X.neg := by
      have hmem := X.maxSupport_mem_support hX
      exact (Finset.mem_union.mp hmem).resolve_left hpos
    simp [hpos, hneg]

/-- The face order on the cross-polytope boundary, by support inclusion. -/
def Le {n : ℕ} (X Y : SignedSubset n) : Prop :=
  X.pos ⊆ Y.pos ∧ X.neg ⊆ Y.neg

end SignedSubset

/-- Nonzero sign vectors, i.e. vertices/faces of the deleted origin sign complex. -/
abbrev NonzeroSignedSubset (n : ℕ) :=
  {X : SignedSubset n // X.Nonzero}

namespace NonzeroSignedSubset

/-- Antipodal map on nonzero sign vectors. -/
def antipode {n : ℕ} (X : NonzeroSignedSubset n) : NonzeroSignedSubset n :=
  ⟨X.1.antipode, (SignedSubset.antipode_nonzero X.1).mpr X.2⟩

end NonzeroSignedSubset

/-- A signed label `±i`, with `i : Fin m`. -/
structure SignedLabel (m : ℕ) where
  positive : Bool
  index : Fin m
  deriving DecidableEq, Repr

namespace SignedLabel

/-- Negating a signed label flips its sign and keeps its index. -/
def neg {m : ℕ} (L : SignedLabel m) : SignedLabel m where
  positive := !L.positive
  index := L.index

end SignedLabel

/-- `k`-subsets contained in a fixed finite support. -/
abbrev KneserVertexIn (n k : ℕ) (support : Finset (Fin n)) : Type :=
  {A : KneserVertex n k // (A.1 : Finset (Fin n)) ⊆ support}

instance (n k : ℕ) (support : Finset (Fin n)) :
    Fintype (KneserVertexIn n k support) := by
  dsimp [KneserVertexIn, KneserVertex]
  infer_instance

instance (n k : ℕ) (support : Finset (Fin n)) :
    DecidableEq (KneserVertexIn n k support) := by
  dsimp [KneserVertexIn, KneserVertex]
  infer_instance

theorem KneserVertexIn.nonempty_of_le_card {n k : ℕ} {support : Finset (Fin n)}
    (hcard : k ≤ support.card) :
    Nonempty (KneserVertexIn n k support) := by
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨⟨⟨A, hAcard⟩, hAsub⟩⟩

/-- The set of colors used on `k`-subsets contained in a support. -/
noncomputable def colorsInSupport {n k q : ℕ} (C : KneserVertex n k → Fin q)
    (support : Finset (Fin n)) : Finset (Fin q) :=
  Finset.univ.image fun A : KneserVertexIn n k support => C A.1

theorem colorsInSupport_nonempty {n k q : ℕ} (C : KneserVertex n k → Fin q)
    {support : Finset (Fin n)} (hcard : k ≤ support.card) :
    (colorsInSupport C support).Nonempty := by
  classical
  obtain ⟨A⟩ := KneserVertexIn.nonempty_of_le_card (n := n) (k := k) hcard
  exact ⟨C A.1, by simp [colorsInSupport]⟩

/-- The minimum color appearing on a `k`-subset contained in `support`. -/
noncomputable def minColorInSupport {n k q : ℕ} (C : KneserVertex n k → Fin q)
    (support : Finset (Fin n)) (hcard : k ≤ support.card) : Fin q :=
  (colorsInSupport C support).min' (colorsInSupport_nonempty C hcard)

theorem exists_kneserVertexIn_color_eq_minColorInSupport {n k q : ℕ}
    (C : KneserVertex n k → Fin q) {support : Finset (Fin n)}
    (hcard : k ≤ support.card) :
    ∃ A : KneserVertexIn n k support, C A.1 = minColorInSupport C support hcard := by
  classical
  have hmem :
      minColorInSupport C support hcard ∈ colorsInSupport C support :=
    Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨A, _hA, hAeq⟩
  exact ⟨A, hAeq⟩

/--
Key finite step in Matoušek's Tucker reduction: if two disjoint supports both
contain a `k`-subset, then a proper Kneser coloring gives different minimum
colors on the two supports.
-/
theorem minColorInSupport_ne_of_disjoint {n k q : ℕ} (hk : 1 ≤ k)
    (C : KneserVertex n k → Fin q)
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    {left right : Finset (Fin n)}
    (hdisj : Disjoint left right)
    (hleft : k ≤ left.card) (hright : k ≤ right.card) :
    minColorInSupport C left hleft ≠ minColorInSupport C right hright := by
  classical
  obtain ⟨A, hAcolor⟩ := exists_kneserVertexIn_color_eq_minColorInSupport C hleft
  obtain ⟨B, hBcolor⟩ := exists_kneserVertexIn_color_eq_minColorInSupport C hright
  have hABdisj : Disjoint (A.1.1 : Finset (Fin n)) (B.1.1 : Finset (Fin n)) :=
    Disjoint.mono A.2 B.2 hdisj
  have hABne : A.1 ≠ B.1 := by
    intro h
    have hself : Disjoint (A.1.1 : Finset (Fin n)) (A.1.1 : Finset (Fin n)) := by
      simpa [h] using hABdisj
    have hempty : (A.1.1 : Finset (Fin n)) = ∅ := by
      exact (Finset.disjoint_self_iff_empty _).mp hself
    have hzero : (A.1.1 : Finset (Fin n)).card = 0 := by simp [hempty]
    have hAcard : (A.1.1 : Finset (Fin n)).card = k := A.1.2
    omega
  intro hmin
  exact hC A.1 B.1 ⟨hABne, hABdisj⟩ (hAcolor.trans (hmin.trans hBcolor.symm))

/--
Small-support part of Matoušek's labeling: a nonzero sign vector with total
support at most `2k - 2` receives label index `|X| - 1`.
-/
def matousekSmallSupportIndex {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (X : SignedSubset n) (hX : X.Nonzero) (hsmall : X.card ≤ 2 * k - 2) :
    Fin (n - 1) :=
  ⟨X.card - 1, by
    have hpos : 0 < X.card := SignedSubset.card_pos_of_nonzero hX
    omega⟩

/--
Large-support color labels occupy the range `2k - 2, …, n - 2`, obtained by
adding the color value to the offset `2k - 2`.
-/
def matousekLargeSupportIndex {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (color : Fin (n - 2 * k + 1)) : Fin (n - 1) :=
  ⟨2 * k - 2 + color.val, by
    have hcolor := color.isLt
    omega⟩

/-- If a sign vector has support at least `2k - 1`, then one side has a `k`-subset. -/
theorem signedSubset_large_support_has_k_side {n k : ℕ} {X : SignedSubset n}
    (hlarge : 2 * k - 1 ≤ X.card) :
    k ≤ X.pos.card ∨ k ≤ X.neg.card := by
  by_contra h
  push Not at h
  simp [SignedSubset.card] at hlarge
  omega

/--
In a proper Kneser coloring, if both signs of a signed support contain
`k`-subsets, the minimum colors on the two sides are different.
-/
theorem minColorInSignedSubset_pos_ne_neg {n k q : ℕ} (hk : 1 ≤ k)
    (C : KneserVertex n k → Fin q)
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X : SignedSubset n)
    (hpos : k ≤ X.pos.card) (hneg : k ≤ X.neg.card) :
    minColorInSupport C X.pos hpos ≠ minColorInSupport C X.neg hneg :=
  minColorInSupport_ne_of_disjoint hk C hC X.disjoint hpos hneg

/--
Tucker's lemma in the octahedral/sign-vector form needed for the
Matoušek proof of Lovász's theorem.  Every antipodal labeling of nonzero sign
vectors by `±1, …, ±(n-1)` has a complementary comparable pair.

This is not currently present in Mathlib; it is the missing discrete
replacement for Borsuk-Ulam.
-/
def TuckerLemmaStatement (n : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel (n - 1),
    (∀ X, label X.antipode = (label X).neg) →
      ∃ X Y : NonzeroSignedSubset n,
        SignedSubset.Le X.1 Y.1 ∧ label X = (label Y).neg

/--
Matoušek's bridge from a too-small Kneser coloring to a Tucker counterexample:
given a proper `(n - 2*k + 1)`-coloring, construct an antipodal sign-vector
labeling with no complementary comparable pair.

This construction is finite and combinatorial, but still nontrivial: it must
choose canonical `k`-subsets from large positive/negative supports and verify
the no-complementary-edge property.  It is the other missing component of the
Tucker route.
-/
def KneserColoringProducesTuckerCounterexample (n k : ℕ) : Prop :=
  ∀ C : KneserVertex n k → Fin (n - 2 * k + 1),
    (∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) →
      ∃ label : NonzeroSignedSubset n → SignedLabel (n - 1),
        (∀ X, label X.antipode = (label X).neg) ∧
          ∀ X Y : NonzeroSignedSubset n,
            SignedSubset.Le X.1 Y.1 → label X ≠ (label Y).neg

/--
If Tucker's lemma and Matoušek's coloring-to-labeling bridge are available,
the hard Kneser lower bound follows immediately.
-/
theorem kneser_chromatic_lower_bound_from_tucker (n k : ℕ)
    (htucker : TuckerLemmaStatement n)
    (hbridge : KneserColoringProducesTuckerCounterexample n k) :
    ¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
      ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b := by
  rintro ⟨C, hC⟩
  obtain ⟨label, hantipodal, hno_complementary⟩ := hbridge C hC
  obtain ⟨X, Y, hXY, hcomp⟩ := htucker label hantipodal
  exact hno_complementary X Y hXY hcomp

/--
Kneser graph chromatic number lower bound: `KG(n,k)` is NOT
`(n - 2k + 1)`-colorable. This is the hard direction, proved by Lovász
using the Borsuk-Ulam theorem, or discretely from Tucker's lemma via
Matoušek's labeling construction.
-/
theorem kneser_chromatic_lower_bound (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hhard : n ≠ 2 * k → ¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
      ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) :
    ¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
      ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b := by
  by_cases heq : n = 2 * k
  · subst heq
    intro ⟨C, hC⟩
    have hfin1 : ∀ (a b : Fin (2 * k - 2 * k + 1)), a = b := by intro a b; ext; omega
    have ⟨a, b, hadj⟩ : ∃ a b : KneserVertex (2 * k) k, (kneserGraph (2 * k) k).Adj a b := by
      classical
      let A : Finset (Fin (2 * k)) := (Finset.univ.filter fun i => i.val < k)
      let B : Finset (Fin (2 * k)) := (Finset.univ.filter fun i => k ≤ i.val)
      have hAcard : A.card = k := by
        have : A = (Finset.univ : Finset (Fin (2 * k))).filter (fun i => i.val < k) := rfl
        rw [this]
        convert_to (Finset.Iio (⟨k, by omega⟩ : Fin (2*k))).card = k
        · congr 1; ext i; simp [Finset.mem_Iio, Fin.lt_def]
        · simp [Fin.card_Iio]
      have hBcard : B.card = k := by
        have hAB : A.card + B.card = 2 * k := by
          have := Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin (2*k)))) (p := fun i : Fin (2*k) => i.val < k)
          simp at this; omega
        omega
      have hdisj : Disjoint A B := by
        rw [Finset.disjoint_filter]; intro i _ h1 h2; omega
      have hne : (⟨A, hAcard⟩ : KneserVertex (2*k) k) ≠ ⟨B, hBcard⟩ := by
        intro h; simp at h
        have : (⟨0, by omega⟩ : Fin (2*k)) ∈ A := by simp [A]; omega
        rw [h] at this; simp [B] at this; omega
      exact ⟨⟨A, hAcard⟩, ⟨B, hBcard⟩, hne, hdisj⟩
    exact absurd (hfin1 (C a) (C b)) (hC a b hadj)
  · exact hhard heq

/-- The hard lower bound is elementary for `k = 1`: `KG(n,1)` is complete,
so a proper coloring must inject `n` singleton vertices into the color set. -/
theorem kneser_chromatic_lower_bound_one (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∃ C : KneserVertex n 1 → Fin (n - 2 * 1 + 1),
      ∀ a b, (kneserGraph n 1).Adj a b → C a ≠ C b := by
  rintro ⟨C, hC⟩
  have hC_inj : Function.Injective C := by
    intro a b hCab
    by_contra hne
    exact hC a b (kneserGraph_one_adj_of_ne n a b hne) hCab
  have hcard := Fintype.card_le_of_injective C hC_inj
  rw [kneserVertex_card, Nat.choose_one_right, Fintype.card_fin] at hcard
  omega

/-- The lower bound is also unconditional on the boundary `n = 2k`: the
target color type has one element, while the graph has an edge. -/
theorem kneser_chromatic_lower_bound_two_mul (k : ℕ) (hk : 1 ≤ k) :
    ¬ ∃ C : KneserVertex (2 * k) k → Fin (2 * k - 2 * k + 1),
      ∀ a b, (kneserGraph (2 * k) k).Adj a b → C a ≠ C b := by
  exact kneser_chromatic_lower_bound (2 * k) k hk (by omega) (by
    intro hne
    exact (hne rfl).elim)

/-- Unconditional Chapter 39 for singleton vertices: `KG(n,1)` is the complete
graph on `n` vertices, so it has the expected lower and upper coloring bounds. -/
theorem chapter39_one (n : ℕ) (hn : 2 ≤ n) :
    (∃ C : KneserVertex n 1 → Fin (n - 2 * 1 + 2),
        ∀ a b, (kneserGraph n 1).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex n 1 → Fin (n - 2 * 1 + 1),
        ∀ a b, (kneserGraph n 1).Adj a b → C a ≠ C b) := by
  refine ⟨?_, ?_⟩
  · exact kneser_chromatic_upper_bound n 1 (by omega) (by omega)
  · exact kneser_chromatic_lower_bound_one n hn

/-- Unconditional Chapter 39 on the boundary `n = 2k`. -/
theorem chapter39_two_mul (k : ℕ) (hk : 1 ≤ k) :
    (∃ C : KneserVertex (2 * k) k → Fin (2 * k - 2 * k + 2),
        ∀ a b, (kneserGraph (2 * k) k).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex (2 * k) k → Fin (2 * k - 2 * k + 1),
        ∀ a b, (kneserGraph (2 * k) k).Adj a b → C a ≠ C b) := by
  refine ⟨?_, ?_⟩
  · exact kneser_chromatic_upper_bound (2 * k) k hk (by omega)
  · exact kneser_chromatic_lower_bound_two_mul k hk

/--
Certificate that Kneser graph KG(n,k) is not `(n - 2k + 1)`-colorable.
This is the hard direction of Lovász's theorem.  It may be supplied by
Borsuk-Ulam or by the Tucker/Matoušek route formalized above.
-/
structure KneserChromaticCertificate (n k : ℕ) where
  /-- The non-colorability witness for the n ≠ 2*k case. -/
  hhard : n ≠ 2 * k → ¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
    ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b

namespace KneserChromaticCertificate

/--
Build the hard lower-bound certificate from Tucker's lemma plus Matoušek's
finite coloring-to-labeling bridge.  This keeps the missing theorem precise:
there is no assumed `False`, only the named discrete lemma and bridge.
-/
def of_tucker (n k : ℕ)
    (htucker : TuckerLemmaStatement n)
    (hbridge : n ≠ 2 * k → KneserColoringProducesTuckerCounterexample n k) :
    KneserChromaticCertificate n k where
  hhard := fun hne =>
    kneser_chromatic_lower_bound_from_tucker n k htucker (hbridge hne)

end KneserChromaticCertificate

/--
Chapter 39 (Lovász's theorem on Kneser graph chromatic number, Tier 1
conditional): given the hard direction (no (n-2k+1)-coloring exists when
n ≠ 2k), and combined with the upper bound (n-2k+2 colorable) already proved,
χ(KG(n,k)) = n - 2k + 2.

TODO (Tier 2): construct `hhard` via Borsuk-Ulam or via
`KneserChromaticCertificate.of_tucker`.  The Tucker route requires proving
`TuckerLemmaStatement` and `KneserColoringProducesTuckerCounterexample`.
-/
theorem chapter39 {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (cert : KneserChromaticCertificate n k) :
    (∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) := by
  refine ⟨?_, ?_⟩
  · exact kneser_chromatic_upper_bound n k hk hn
  · exact kneser_chromatic_lower_bound n k hk hn cert.hhard

end ProofsInTheBook.Chapter39
