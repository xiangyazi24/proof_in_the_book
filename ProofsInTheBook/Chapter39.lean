import Mathlib

/-!
# Chapter 39: The chromatic number of Kneser graphs

From "Proofs from THE BOOK":

**Lovász's theorem**: χ(KG(n,k)) = n - 2k + 2.

The book presents Bárány's short proof using the Borsuk-Ulam theorem:
if KG(n,k) were (n-2k+1)-colorable, one could construct a continuous
map S^{n-2k+1} → ℝ^{n-2k} with no antipodal pair mapping to the same
point, contradicting Borsuk-Ulam.
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

theorem kneserColorNat_lt {n k : ℕ} (_hk : 1 ≤ k) (h2k : 2 * k ≤ n)
    (S : KneserVertex n k) : kneserColorNat _hk S < n - 2 * k + 2 := by
  unfold kneserColorNat
  simp only
  by_cases h : (KneserVertex.min' _hk S).val ≤ n - 2 * k <;> simp [h] <;> omega

noncomputable def kneserColor {n k : ℕ} (hk : 1 ≤ k) (h2k : 2 * k ≤ n) :
    KneserVertex n k → Fin (n - 2 * k + 2) :=
  fun S => ⟨kneserColorNat hk S, kneserColorNat_lt hk h2k S⟩

private theorem kneserColor_proper {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (a b : KneserVertex n k) (hadj : (kneserGraph n k).Adj a b) :
    kneserColor hk hn a ≠ kneserColor hk hn b := by
  simp only [kneserColor, Fin.mk.injEq, kneserColorNat]
  set ma := (KneserVertex.min' hk a).val
  set mb := (KneserVertex.min' hk b).val
  have hdisj := hadj.2
  have hma_mem : KneserVertex.min' hk a ∈ a.1 := Finset.min'_mem _ _
  have hmb_mem : KneserVertex.min' hk b ∈ b.1 := Finset.min'_mem _ _
  have hne_min : ma ≠ mb := by
    intro heq
    have : KneserVertex.min' hk a ∈ a.1 ⊓ b.1 := by
      simp [Finset.mem_inf, hma_mem]
      have : KneserVertex.min' hk a = KneserVertex.min' hk b := Fin.ext heq
      rw [this]; exact hmb_mem
    exact Finset.disjoint_left.mp hdisj hma_mem (by
      have : KneserVertex.min' hk a = KneserVertex.min' hk b := Fin.ext heq
      rw [this]; exact hmb_mem)
  by_cases ha : ma ≤ n - 2 * k <;> by_cases hb : mb ≤ n - 2 * k <;> simp [ha, hb]
  · exact hne_min
  · omega
  · omega
  · exfalso
    have ha_sub : ∀ x ∈ a.1, n - 2 * k < x.val := by
      intro x hx
      by_contra hle; push Not at hle
      exact ha (Nat.le_trans (Finset.min'_le _ _ hx) hle)
    have hb_sub : ∀ x ∈ b.1, n - 2 * k < x.val := by
      intro x hx
      by_contra hle; push Not at hle
      exact hb (Nat.le_trans (Finset.min'_le _ _ hx) hle)
    have hunion_sub : ∀ x ∈ a.1 ∪ b.1, n - 2 * k < x.val := by
      intro x hx; rcases Finset.mem_union.mp hx with h | h
      · exact ha_sub x h
      · exact hb_sub x h
    have hcard_union : (a.1 ∪ b.1).card = 2 * k := by
      rw [Finset.card_union_of_disjoint hdisj, a.2, b.2]
    have hcard_range : (Finset.univ.filter fun i : Fin n => n - 2 * k < i.val).card = 2 * k - 1 := by
      simp [Finset.card_filter]; omega
    have hsub : a.1 ∪ b.1 ⊆ Finset.univ.filter fun i : Fin n => n - 2 * k < i.val :=
      fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hunion_sub x hx⟩
    have := Finset.card_le_card hsub
    omega

theorem kneser_chromatic_upper_bound (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
      ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b :=
  ⟨kneserColor hk hn, kneserColor_proper hk hn⟩

/--
Kneser graph chromatic number lower bound: `KG(n,k)` is NOT
`(n - 2k + 1)`-colorable. This is the hard direction, proved by Lovász
using the Borsuk-Ulam theorem (or by Bárány's simplicial argument).
-/
theorem kneser_chromatic_lower_bound (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
      ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b := by
  sorry

theorem chapter39 (n k : ℕ) :
    Fintype.card (KneserVertex n k) = n.choose k :=
  kneserVertex_card n k

end ProofsInTheBook.Chapter39
