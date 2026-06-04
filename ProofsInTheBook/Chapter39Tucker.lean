import ProofsInTheBook.Chapter39

/-!
# Chapter 39 (Kneser) — Tucker lemma, sound foundation

A correct (non-degenerate) reduction for `TuckerLemmaStatement`, replacing the earlier
empty-alternating-chain framework (whose `PositiveAlternatingPrefixLabels` is provably
unsatisfiable: it demands `StrictMono (Fin n → Fin (n-1))`, impossible by pigeonhole).

The genuine combinatorial content: along any maximal chain (a signed-permutation prefix
chain of length `n`), the `n` labels live in `SignedLabel (n-1)` (only `n-1` indices), so two
of them share an index.  If two comparable signed subsets carry same-index, opposite-sign
labels, that *is* a complementary comparable pair — the Tucker conclusion.  So Tucker reduces
to producing one chain with a same-index, opposite-sign pair; the "same index" half is free
(pigeonhole), and the remaining content (forcing opposite signs via antipodality) is the real
path argument, now resting on a sound base.
-/

namespace ProofsInTheBook.Chapter39

open SignedPermutation

/-- **Pigeonhole on a maximal chain.** The `n` labels of a signed-permutation prefix chain,
valued in `SignedLabel (n-1)`, cannot all have distinct indices: two share an index. -/
theorem exists_same_index_in_prefixChain {n : ℕ} (hn : 1 ≤ n)
    (label : NonzeroSignedSubset n → SignedLabel (n - 1)) (P : SignedPermutation n) :
    ∃ i j : Fin n, i ≠ j ∧
      (label (P.prefixChain i)).index = (label (P.prefixChain j)).index := by
  have hcard : Fintype.card (Fin (n - 1)) < Fintype.card (Fin n) := by
    simp only [Fintype.card_fin]; omega
  obtain ⟨i, j, hij, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin n => (label (P.prefixChain i)).index) hcard
  exact ⟨i, j, hij, heq⟩

/-- **Sound reduction for Tucker.** If every antipodal labeling admits a maximal chain with two
positions `i < j` whose labels share an index but differ in sign, then `TuckerLemmaStatement n`
holds.  (Those two prefix subsets are comparable by `prefixChain_le`, and same-index/opposite-sign
means each label is the negation of the other — a complementary comparable pair.) -/
theorem tuckerLemmaStatement_of_chain_complementary {n : ℕ}
    (h : ∀ label : NonzeroSignedSubset n → SignedLabel (n - 1),
          (∀ X, label X.antipode = (label X).neg) →
          ∃ (P : SignedPermutation n) (i j : Fin n), i < j ∧
            (label (P.prefixChain i)).index = (label (P.prefixChain j)).index ∧
            (label (P.prefixChain i)).positive ≠ (label (P.prefixChain j)).positive) :
    TuckerLemmaStatement n := by
  intro label hanti
  obtain ⟨P, i, j, hij, hidx, hsign⟩ := h label hanti
  refine ⟨P.prefixChain i, P.prefixChain j, prefixChain_le P (le_of_lt hij), ?_⟩
  refine SignedLabel.ext ?_ ?_
  · -- positive components are opposite
    simp only [SignedLabel.neg]
    revert hsign
    cases hpi : (label (P.prefixChain i)).positive <;>
      cases hpj : (label (P.prefixChain j)).positive <;> simp
  · -- indices agree (neg keeps the index)
    simp only [SignedLabel.neg]
    exact hidx

theorem tuckerLemmaStatement_of_chain_complementary_of_no_complementary {n : ℕ}
    (h : ∀ label : NonzeroSignedSubset n → SignedLabel (n - 1),
          (∀ X, label X.antipode = (label X).neg) →
          NoComplementaryComparableLabels label →
          ∃ (P : SignedPermutation n) (i j : Fin n), i < j ∧
            (label (P.prefixChain i)).index = (label (P.prefixChain j)).index ∧
            (label (P.prefixChain i)).positive ≠ (label (P.prefixChain j)).positive) :
    TuckerLemmaStatement n := by
  intro label hanti
  by_contra hnone
  have hno : NoComplementaryComparableLabels label := by
    intro X Y hXY hcomp
    exact hnone ⟨X, Y, hXY, hcomp⟩
  obtain ⟨P, i, j, hij, hidx, hsign⟩ := h label hanti hno
  have hcomp : label (P.prefixChain i) = (label (P.prefixChain j)).neg := by
    refine SignedLabel.ext ?_ ?_
    · simp only [SignedLabel.neg]
      revert hsign
      cases hpi : (label (P.prefixChain i)).positive <;>
        cases hpj : (label (P.prefixChain j)).positive <;> simp
    · simp only [SignedLabel.neg]
      exact hidx
  exact hno (P.prefixChain i) (P.prefixChain j)
    (prefixChain_le P (le_of_lt hij)) hcomp

/-! ## Hemisphere and equator model -/

theorem signedSubset_ext_pos_neg {n : ℕ} {X Y : SignedSubset n}
    (hpos : X.pos = Y.pos) (hneg : X.neg = Y.neg) : X = Y := by
  cases X with
  | mk xpos xneg xdisj =>
      cases Y with
      | mk ypos yneg ydisj =>
          dsimp at hpos hneg
          subst ypos
          subst yneg
          simp

/-- The upper hemisphere `B⁺_{r+1}`: the last coordinate is not negative. -/
def UpperHemisphere {r : ℕ} (X : NonzeroSignedSubset (r + 1)) : Prop :=
  Fin.last r ∉ X.1.neg

/-- The equator of `B⁺_{r+1}`: the last coordinate is zero. -/
def Equator {r : ℕ} (X : NonzeroSignedSubset (r + 1)) : Prop :=
  Fin.last r ∉ X.1.pos ∧ Fin.last r ∉ X.1.neg

theorem equator_subset_upperHemisphere {r : ℕ} {X : NonzeroSignedSubset (r + 1)}
    (hX : Equator X) : UpperHemisphere X :=
  hX.2

theorem upperHemisphere_of_le {r : ℕ} {X Y : NonzeroSignedSubset (r + 1)}
    (hXY : SignedSubset.Le X.1 Y.1) (hY : UpperHemisphere Y) :
    UpperHemisphere X := by
  intro hneg
  exact hY (hXY.2 hneg)

/-- Embed a sign vector on the first `r` coordinates into the equator of
`{−1,0,1}^{r+1}`. -/
def signedSubsetEquatorEmbed {r : ℕ} (X : SignedSubset r) : SignedSubset (r + 1) where
  pos := X.pos.image Fin.castSucc
  neg := X.neg.image Fin.castSucc
  disjoint := by
    rw [Finset.disjoint_left]
    intro y hypos hyneg
    rcases Finset.mem_image.mp hypos with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hyneg with ⟨b, hbmem, hb⟩
    have hba : b = a := by
      apply Fin.ext
      simpa using congrArg Fin.val hb
    subst b
    exact (Finset.disjoint_left.mp X.disjoint) ha hbmem

/-- The equator embedding on nonzero sign vectors. -/
def equatorEmbed {r : ℕ} (X : NonzeroSignedSubset r) : NonzeroSignedSubset (r + 1) :=
  ⟨signedSubsetEquatorEmbed X.1, by
    rcases X.2 with hpos | hneg
    · rcases hpos with ⟨i, hi⟩
      left
      exact ⟨Fin.castSucc i, by simp [signedSubsetEquatorEmbed, hi]⟩
    · rcases hneg with ⟨i, hi⟩
      right
      exact ⟨Fin.castSucc i, by simp [signedSubsetEquatorEmbed, hi]⟩⟩

theorem equatorEmbed_mem_equator {r : ℕ} (X : NonzeroSignedSubset r) :
    Equator (equatorEmbed X) := by
  constructor
  · intro hlast
    rcases Finset.mem_image.mp hlast with ⟨i, _hi, hi⟩
    have hval := congrArg Fin.val hi
    simp [Fin.last] at hval
    omega
  · intro hlast
    rcases Finset.mem_image.mp hlast with ⟨i, _hi, hi⟩
    have hval := congrArg Fin.val hi
    simp [Fin.last] at hval
    omega

/-- The predecessor of a non-last coordinate. -/
def finPredOfNotLast {r : ℕ} (i : Fin (r + 1)) (hi : i ≠ Fin.last r) : Fin r :=
  ⟨i.val, by
    have hle : i.val ≤ r := Nat.lt_succ_iff.mp i.isLt
    have hne : i.val ≠ r := by
      intro hval
      exact hi (Fin.ext hval)
    omega⟩

@[simp]
theorem castSucc_finPredOfNotLast {r : ℕ} (i : Fin (r + 1)) (hi : i ≠ Fin.last r) :
    Fin.castSucc (finPredOfNotLast i hi) = i := by
  apply Fin.ext
  rfl

/-- Drop the last zero coordinate from an equatorial sign vector. -/
def equatorDropSignedSubset {r : ℕ} (X : NonzeroSignedSubset (r + 1)) : SignedSubset r where
  pos := Finset.univ.filter fun i : Fin r => Fin.castSucc i ∈ X.1.pos
  neg := Finset.univ.filter fun i : Fin r => Fin.castSucc i ∈ X.1.neg
  disjoint := by
    rw [Finset.disjoint_left]
    intro i hip hin
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hip hin
    exact (Finset.disjoint_left.mp X.1.disjoint) hip hin

theorem equatorDrop_nonzero {r : ℕ} (X : NonzeroSignedSubset (r + 1))
    (hX : Equator X) : (equatorDropSignedSubset X).Nonzero := by
  rcases X.2 with hpos | hneg
  · rcases hpos with ⟨i, hi⟩
    have hine : i ≠ Fin.last r := by
      intro hlast
      exact hX.1 (by simpa [hlast] using hi)
    left
    exact ⟨finPredOfNotLast i hine, by
      simp [equatorDropSignedSubset, hi]⟩
  · rcases hneg with ⟨i, hi⟩
    have hine : i ≠ Fin.last r := by
      intro hlast
      exact hX.2 (by simpa [hlast] using hi)
    right
    exact ⟨finPredOfNotLast i hine, by
      simp [equatorDropSignedSubset, hi]⟩

/-- The inverse map from the equator back to `K_r`. -/
def equatorDrop {r : ℕ} (X : NonzeroSignedSubset (r + 1)) (hX : Equator X) :
    NonzeroSignedSubset r :=
  ⟨equatorDropSignedSubset X, equatorDrop_nonzero X hX⟩

theorem equatorDrop_equatorEmbed {r : ℕ} (X : NonzeroSignedSubset r) :
    equatorDrop (equatorEmbed X) (equatorEmbed_mem_equator X) = X := by
  apply Subtype.ext
  apply signedSubset_ext_pos_neg
  · ext i
    simp [equatorDrop, equatorDropSignedSubset, equatorEmbed, signedSubsetEquatorEmbed]
  · ext i
    simp [equatorDrop, equatorDropSignedSubset, equatorEmbed, signedSubsetEquatorEmbed]

theorem equatorEmbed_equatorDrop {r : ℕ} (X : NonzeroSignedSubset (r + 1))
    (hX : Equator X) :
    equatorEmbed (equatorDrop X hX) = X := by
  apply Subtype.ext
  apply signedSubset_ext_pos_neg
  · ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨i, hi, hiy⟩
      simp only [equatorDrop, equatorDropSignedSubset, Finset.mem_filter, Finset.mem_univ,
        true_and] at hi
      simpa [hiy] using hi
    · intro hy
      by_cases hlast : y = Fin.last r
      · exact False.elim (hX.1 (by simpa [hlast] using hy))
      · refine Finset.mem_image.mpr ⟨finPredOfNotLast y hlast, ?_, ?_⟩
        · simp [equatorDrop, equatorDropSignedSubset, hy]
        · exact castSucc_finPredOfNotLast y hlast
  · ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨i, hi, hiy⟩
      simp only [equatorDrop, equatorDropSignedSubset, Finset.mem_filter, Finset.mem_univ,
        true_and] at hi
      simpa [hiy] using hi
    · intro hy
      by_cases hlast : y = Fin.last r
      · exact False.elim (hX.2 (by simpa [hlast] using hy))
      · refine Finset.mem_image.mpr ⟨finPredOfNotLast y hlast, ?_, ?_⟩
        · simp [equatorDrop, equatorDropSignedSubset, hy]
        · exact castSucc_finPredOfNotLast y hlast

/-- The equator of the upper hemisphere in `K_{r+1}` is canonically `K_r`. -/
noncomputable def equatorEquiv (r : ℕ) :
    NonzeroSignedSubset r ≃ {X : NonzeroSignedSubset (r + 1) // Equator X} where
  toFun X := ⟨equatorEmbed X, equatorEmbed_mem_equator X⟩
  invFun X := equatorDrop X.1 X.2
  left_inv := by
    intro X
    exact equatorDrop_equatorEmbed X
  right_inv := by
    intro X
    cases X with
    | mk X hX =>
        apply Subtype.ext
        exact equatorEmbed_equatorDrop X hX

theorem equatorEmbed_le {r : ℕ} {X Y : NonzeroSignedSubset r}
    (hXY : SignedSubset.Le X.1 Y.1) :
    SignedSubset.Le (equatorEmbed X).1 (equatorEmbed Y).1 := by
  constructor
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, hXY.1 hi, rfl⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, hXY.2 hi, rfl⟩

theorem signedSubsetEquatorEmbed_antipode {r : ℕ} (X : SignedSubset r) :
    signedSubsetEquatorEmbed X.antipode = (signedSubsetEquatorEmbed X).antipode := by
  apply signedSubset_ext_pos_neg
  · ext i
    simp [signedSubsetEquatorEmbed, SignedSubset.antipode]
  · ext i
    simp [signedSubsetEquatorEmbed, SignedSubset.antipode]

theorem equatorEmbed_antipode {r : ℕ} (X : NonzeroSignedSubset r) :
    equatorEmbed X.antipode = (equatorEmbed X).antipode := by
  apply Subtype.ext
  exact signedSubsetEquatorEmbed_antipode X.1

noncomputable def equatorRestrictedLabel {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :
    NonzeroSignedSubset d → SignedLabel d :=
  fun X => label ((equatorEquiv d) X).1

noncomputable def equatorRestrictedLabelOf {r m : ℕ}
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    NonzeroSignedSubset r → SignedLabel m :=
  fun X => label ((equatorEquiv r) X).1

theorem equatorRestrictedLabelOf_antipodal {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ∀ X, equatorRestrictedLabelOf label X.antipode =
      (equatorRestrictedLabelOf label X).neg := by
  intro X
  simpa [equatorRestrictedLabelOf, equatorEquiv, equatorEmbed_antipode] using
    hantipodal (equatorEmbed X)

theorem equatorRestrictedLabelOf_noComplementary {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label) :
    NoComplementaryComparableLabels (equatorRestrictedLabelOf label) := by
  intro X Y hXY hcomp
  have hcomp' : label (equatorEmbed X) = (label (equatorEmbed Y)).neg := by
    simpa [equatorRestrictedLabelOf, equatorEquiv] using hcomp
  exact hno (equatorEmbed X) (equatorEmbed Y) (equatorEmbed_le hXY) hcomp'

theorem equatorRestrictedLabel_antipodal {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ∀ X, equatorRestrictedLabel label X.antipode =
      (equatorRestrictedLabel label X).neg := by
  intro X
  simpa [equatorRestrictedLabel, equatorEquiv, equatorEmbed_antipode] using
    hantipodal (equatorEmbed X)

theorem equatorRestrictedLabel_noComplementary {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hno : NoComplementaryComparableLabels label) :
    NoComplementaryComparableLabels (equatorRestrictedLabel label) := by
  intro X Y hXY hcomp
  have hcomp' : label (equatorEmbed X) = (label (equatorEmbed Y)).neg := by
    simpa [equatorRestrictedLabel, equatorEquiv] using hcomp
  exact hno (equatorEmbed X) (equatorEmbed Y) (equatorEmbed_le hXY) hcomp'

/-- A maximal chain of the equator, transported from a signed permutation of `K_r`. -/
def equatorPrefixChain {r : ℕ} (P : SignedPermutation r) (i : Fin r) :
    NonzeroSignedSubset (r + 1) :=
  equatorEmbed (P.prefixChain i)

theorem equatorPrefixChain_mem_equator {r : ℕ} (P : SignedPermutation r) (i : Fin r) :
    Equator (equatorPrefixChain P i) :=
  equatorEmbed_mem_equator (P.prefixChain i)

theorem equatorPrefixChain_le {r : ℕ} (P : SignedPermutation r) {i j : Fin r}
    (hij : i ≤ j) :
    SignedSubset.Le (equatorPrefixChain P i).1 (equatorPrefixChain P j).1 :=
  equatorEmbed_le (P.prefixChain_le hij)

/-- Under the equator equivalence, the transported equator chain is exactly
the original maximal chain in `K_r`. -/
theorem equatorPrefixChain_projects {r : ℕ} (P : SignedPermutation r) (i : Fin r) :
    (equatorEquiv r).symm
        ⟨equatorPrefixChain P i, equatorPrefixChain_mem_equator P i⟩ =
      P.prefixChain i :=
  equatorDrop_equatorEmbed (P.prefixChain i)

/-! ## Label-set `A` ridges and the local sigma-degree count -/

/-- The alternating label `α_k = (-1)^k(k+1)` in zero-based `Fin d` notation. -/
def alternatingLabel (k : Fin d) : SignedLabel d where
  positive := decide (Even k.val)
  index := k

@[simp]
theorem alternatingLabel_index (k : Fin d) : (alternatingLabel k).index = k := rfl

@[simp]
theorem alternatingLabel_positive (k : Fin d) :
    (alternatingLabel k).positive = decide (Even k.val) := rfl

theorem alternatingLabel_inj {d : ℕ} {a b : Fin d} :
    alternatingLabel a = alternatingLabel b ↔ a = b := by
  constructor
  · intro h
    have hidx := congrArg SignedLabel.index h
    simpa [alternatingLabel] using hidx
  · intro h
    subst h
    rfl

theorem alternatingLabel_neg_ne {d : ℕ} (a b : Fin d) :
    (alternatingLabel a).neg ≠ alternatingLabel b := by
  intro h
  have hidx : a = b := by
    have hidx' := congrArg SignedLabel.index h
    simpa [alternatingLabel, SignedLabel.neg] using hidx'
  subst b
  have hpos := congrArg SignedLabel.positive h
  simp [alternatingLabel, SignedLabel.neg] at hpos

theorem signedLabel_eq_alternating_or_neg {d : ℕ} (L : SignedLabel d) :
    L = alternatingLabel L.index ∨ L = (alternatingLabel L.index).neg := by
  cases L with
  | mk positive index =>
      by_cases h : positive = decide (Even index.val)
      · left
        apply SignedLabel.ext
        · exact h
        · rfl
      · right
        apply SignedLabel.ext
        · cases positive <;> cases hidx : decide (Even index.val) <;>
            simp [hidx, SignedLabel.neg] at h ⊢
        · rfl

/-- The concrete `A = {+1,-2,+3,...}` label set. -/
noncomputable def alternatingLabelSetA (d : ℕ) : Finset (SignedLabel d) :=
  Finset.univ.image fun k : Fin d => alternatingLabel k

theorem alternatingLabelSetA_card (d : ℕ) :
    (alternatingLabelSetA d).card = d := by
  classical
  rw [alternatingLabelSetA, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact alternatingLabel_inj.mp h

/-! ### Alternating labels along an arbitrary increasing index set -/

/-- The alternating label attached to the `a`th element of an index map.  The
sign alternates with the position `a`; the absolute label is `idx a`. -/
def alternatingLabelOf {r m : ℕ} (idx : Fin r → Fin m) (a : Fin r) :
    SignedLabel m where
  positive := decide (Even a.val)
  index := idx a

@[simp]
theorem alternatingLabelOf_index {r m : ℕ} (idx : Fin r → Fin m) (a : Fin r) :
    (alternatingLabelOf idx a).index = idx a := rfl

@[simp]
theorem alternatingLabelOf_positive {r m : ℕ} (idx : Fin r → Fin m) (a : Fin r) :
    (alternatingLabelOf idx a).positive = decide (Even a.val) := rfl

theorem alternatingLabelOf_inj {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) {a b : Fin r} :
    alternatingLabelOf idx a = alternatingLabelOf idx b ↔ a = b := by
  constructor
  · intro h
    apply hidx
    simpa [alternatingLabelOf] using congrArg SignedLabel.index h
  · intro h
    subst h
    rfl

theorem alternatingLabelOf_neg_ne {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) (a b : Fin r) :
    (alternatingLabelOf idx a).neg ≠ alternatingLabelOf idx b := by
  intro h
  have hab : a = b := by
    apply hidx
    have hidx' := congrArg SignedLabel.index h
    simpa [alternatingLabelOf, SignedLabel.neg] using hidx'
  subst b
  have hpos := congrArg SignedLabel.positive h
  simp [alternatingLabelOf, SignedLabel.neg] at hpos

/-- The alternating label set determined by an index map. -/
noncomputable def alternatingLabelSetOf {r m : ℕ} (idx : Fin r → Fin m) :
    Finset (SignedLabel m) :=
  Finset.univ.image fun a : Fin r => alternatingLabelOf idx a

theorem alternatingLabelSetOf_card {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) :
    (alternatingLabelSetOf idx).card = r := by
  classical
  rw [alternatingLabelSetOf, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact (alternatingLabelOf_inj hidx).mp h

/-- The negative-first alternating label set determined by an index map. -/
noncomputable def alternatingNegLabelSetOf {r m : ℕ} (idx : Fin r → Fin m) :
    Finset (SignedLabel m) :=
  Finset.univ.image fun a : Fin r => (alternatingLabelOf idx a).neg

theorem alternatingNegLabelOf_inj {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) {a b : Fin r} :
    (alternatingLabelOf idx a).neg = (alternatingLabelOf idx b).neg ↔ a = b := by
  constructor
  · intro h
    apply hidx
    have hidx' := congrArg SignedLabel.index h
    simpa [alternatingLabelOf, SignedLabel.neg] using hidx'
  · intro h
    subst h
    rfl

theorem alternatingNegLabelSetOf_card {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) :
    (alternatingNegLabelSetOf idx).card = r := by
  classical
  rw [alternatingNegLabelSetOf, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact (alternatingNegLabelOf_inj hidx).mp h

theorem alternatingLabelSetOf_range_eq_of_eq {r m : ℕ}
    {idx eta : Fin r → Fin m}
    (h : alternatingLabelSetOf idx = alternatingLabelSetOf eta) :
    Set.range idx = Set.range eta := by
  classical
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    have hmem : alternatingLabelOf idx a ∈ alternatingLabelSetOf eta := by
      rw [← h]
      simp [alternatingLabelSetOf]
    rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
    exact ⟨b, by
      have hidx := congrArg SignedLabel.index hb.symm
      simpa [alternatingLabelOf] using hidx.symm⟩
  · rintro ⟨a, rfl⟩
    have hmem : alternatingLabelOf eta a ∈ alternatingLabelSetOf idx := by
      rw [h]
      simp [alternatingLabelSetOf]
    rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
    exact ⟨b, by
      have hidx := congrArg SignedLabel.index hb.symm
      simpa [alternatingLabelOf] using hidx.symm⟩

theorem alternatingLabelSetOf_idx_unique {r m : ℕ}
    {idx eta : Fin r → Fin m}
    (hidx : StrictMono idx) (heta : StrictMono eta)
    (h : alternatingLabelSetOf idx = alternatingLabelSetOf eta) :
    idx = eta := by
  exact (StrictMono.range_inj hidx heta).mp (alternatingLabelSetOf_range_eq_of_eq h)

theorem alternatingNegLabelSetOf_range_eq_of_eq {r m : ℕ}
    {idx eta : Fin r → Fin m}
    (h : alternatingNegLabelSetOf idx = alternatingNegLabelSetOf eta) :
    Set.range idx = Set.range eta := by
  classical
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    have hmem : (alternatingLabelOf idx a).neg ∈ alternatingNegLabelSetOf eta := by
      rw [← h]
      simp [alternatingNegLabelSetOf]
    rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
    exact ⟨b, by
      have hidx := congrArg SignedLabel.index hb.symm
      simpa [alternatingLabelOf, SignedLabel.neg] using hidx.symm⟩
  · rintro ⟨a, rfl⟩
    have hmem : (alternatingLabelOf eta a).neg ∈ alternatingNegLabelSetOf idx := by
      rw [h]
      simp [alternatingNegLabelSetOf]
    rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
    exact ⟨b, by
      have hidx := congrArg SignedLabel.index hb.symm
      simpa [alternatingLabelOf, SignedLabel.neg] using hidx.symm⟩

theorem alternatingNegLabelSetOf_idx_unique {r m : ℕ}
    {idx eta : Fin r → Fin m}
    (hidx : StrictMono idx) (heta : StrictMono eta)
    (h : alternatingNegLabelSetOf idx = alternatingNegLabelSetOf eta) :
    idx = eta := by
  exact (StrictMono.range_inj hidx heta).mp (alternatingNegLabelSetOf_range_eq_of_eq h)

/-- The label set carried by an ordered simplex.  The property below does not
use the order except to enumerate the finitely many vertices. -/
noncomputable def simplexLabelSet {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) : Finset (SignedLabel m) :=
  Finset.univ.image fun a : Fin k => label (sigma a)

/-- Positive-first alternating simplex, with its index set read off from the
simplex itself.  The `idx` below is an internal witness, not an external
summation parameter. -/
def IsAltPos {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) : Prop :=
  ∃ idx : Fin k → Fin m,
    StrictMono idx ∧ simplexLabelSet label sigma = alternatingLabelSetOf idx

/-- Negative-first alternating simplex, with the same self-contained indexing
convention as `IsAltPos`. -/
def IsAltNeg {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) : Prop :=
  ∃ idx : Fin k → Fin m,
    StrictMono idx ∧ simplexLabelSet label sigma = alternatingNegLabelSetOf idx

noncomputable instance isAltPos_decidable {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) :
    Decidable (IsAltPos label sigma) := by
  classical
  unfold IsAltPos
  infer_instance

noncomputable instance isAltNeg_decidable {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin k → NonzeroSignedSubset n) :
    Decidable (IsAltNeg label sigma) := by
  classical
  unfold IsAltNeg
  infer_instance

theorem IsAltPos.idx_unique {k m n : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    {sigma : Fin k → NonzeroSignedSubset n}
    {idx eta : Fin k → Fin m}
    (hidx : StrictMono idx) (heta : StrictMono eta)
    (h₁ : simplexLabelSet label sigma = alternatingLabelSetOf idx)
    (h₂ : simplexLabelSet label sigma = alternatingLabelSetOf eta) :
    idx = eta :=
  alternatingLabelSetOf_idx_unique hidx heta (h₁.symm.trans h₂)

theorem IsAltNeg.idx_unique {k m n : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    {sigma : Fin k → NonzeroSignedSubset n}
    {idx eta : Fin k → Fin m}
    (hidx : StrictMono idx) (heta : StrictMono eta)
    (h₁ : simplexLabelSet label sigma = alternatingNegLabelSetOf idx)
    (h₂ : simplexLabelSet label sigma = alternatingNegLabelSetOf eta) :
    idx = eta :=
  alternatingNegLabelSetOf_idx_unique hidx heta (h₁.symm.trans h₂)

/-! ## Ky Fan parity statement on the non-degenerate range -/

/-- Ky Fan parity in the range actually used by Tucker: `r ≥ 1`, `m ≥ r`.
It counts positive-first alternating maximal chains of `K_r`; this is not the
degenerate `Fin r → Fin (r-1)` full-chain pigeonhole setup. -/
def KyFanParityStatement (r m : ℕ) : Prop :=
  1 ≤ r →
    r ≤ m →
      ∀ label : NonzeroSignedSubset r → SignedLabel m,
        (∀ X, label X.antipode = (label X).neg) →
          NoComplementaryComparableLabels label →
            Odd (positiveAlternatingPrefixLabelChains label).card

theorem alternatingPrefixLabelChains_card_one_any {m : ℕ}
    (label : NonzeroSignedSubset 1 → SignedLabel m) :
    (alternatingPrefixLabelChains label).card = 2 := by
  classical
  have huniv : alternatingPrefixLabelChains label = (Finset.univ : Finset (SignedPermutation 1)) := by
    ext P
    simp only [alternatingPrefixLabelChains, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, positiveAlternatingPrefixLabelChains,
      negativeAlternatingPrefixLabelChains, PositiveAlternatingPrefixLabels,
      NegativeAlternatingPrefixLabels]
    constructor
    · intro _
      trivial
    · intro _
      have hstrict : StrictMono fun i : Fin 1 => (label (P.prefixChain i)).index := by
        intro a b hab
        fin_cases a
        fin_cases b
        omega
      cases h : (label (P.prefixChain 0)).positive
      · right
        refine ⟨hstrict, ?_⟩
        intro i
        fin_cases i
        simp [h]
      · left
        refine ⟨hstrict, ?_⟩
        intro i
        fin_cases i
        simp [h]
  rw [huniv]
  calc
    (Finset.univ : Finset (SignedPermutation 1)).card =
        Fintype.card (SignedPermutation 1) := by
      simp
    _ = Fintype.card (Equiv.Perm (Fin 1) × (Fin 1 → Bool)) :=
      Fintype.card_congr (signedPermutationEquiv 1)
    _ = 2 := by simp

/-- Base case of the non-degenerate Ky Fan parity statement: for `r = 1` and
any nonempty label set, the two antipodal vertices have opposite signs, hence
exactly one positive-first chain. -/
theorem kyFanParityStatement_one {m : ℕ} (_hm : 1 ≤ m) :
    KyFanParityStatement 1 m := by
  intro _hr _hm label hantipodal _hno
  have halt := alternatingPrefixLabelChains_card_one_any label
  have htwice := alternatingPrefixLabelChains_card (n := 1) (m := m) (by omega) label hantipodal
  rw [halt] at htwice
  have hpos : (positiveAlternatingPrefixLabelChains label).card = 1 := by
    omega
  rw [hpos]
  exact odd_one

theorem equatorRestrictedLabel_positiveAlternating_odd {d : ℕ}
    (hd : 1 ≤ d) (hKy : KyFanParityStatement d d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (hno : NoComplementaryComparableLabels label) :
    Odd (positiveAlternatingPrefixLabelChains (equatorRestrictedLabel label)).card :=
  hKy hd le_rfl (equatorRestrictedLabel label)
    (equatorRestrictedLabel_antipodal hantipodal)
    (equatorRestrictedLabel_noComplementary hno)

/-- A `d`-vertex ridge whose labels are exactly the label set `A`.  In the
Tucker reduction `d = n - 1`, so this is the dim-`(n-2)` simplex, not a full
`n`-vertex chain. -/
def AlternatingLabelSetARidge {d n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel d)
    (rho : Fin d → NonzeroSignedSubset n) : Prop :=
  (∀ i j, i < j → SignedSubset.Le (rho i).1 (rho j).1) ∧
    Function.Injective rho ∧
      ∀ k : Fin d, label (rho k) = alternatingLabel k

/-- After deleting `j` from a `(d+1)`-vertex sigma, every label in `A` still
appears.  Since exactly `d` vertices remain, this is the label-set-`A` door
condition used in the deletion count. -/
def SigmaDeletionHasAlternatingLabelSet {d : ℕ}
    (sigmaLabel : Fin (d + 1) → SignedLabel d) (j : Fin (d + 1)) : Prop :=
  ∀ a : Fin d, ∃ t : Fin (d + 1), t ≠ j ∧ sigmaLabel t = alternatingLabel a

/-- The door set of a sigma: deletions that leave the alternating label set `A`. -/
noncomputable def sigmaDoorSet {d : ℕ}
    (sigmaLabel : Fin (d + 1) → SignedLabel d) : Finset (Fin (d + 1)) :=
  by
    classical
    exact Finset.univ.filter fun j => SigmaDeletionHasAlternatingLabelSet sigmaLabel j

/-- The parameterized deletion condition: deleting `j` leaves the alternating
label set determined by `idx`. -/
def SigmaDeletionHasAlternatingLabelSetOf {r m : ℕ} (idx : Fin r → Fin m)
    (sigmaLabel : Fin (r + 1) → SignedLabel m) (j : Fin (r + 1)) : Prop :=
  ∀ a : Fin r, ∃ t : Fin (r + 1), t ≠ j ∧
    sigmaLabel t = alternatingLabelOf idx a

/-- Door set for a fixed increasing index set. -/
noncomputable def sigmaDoorSetOf {r m : ℕ} (idx : Fin r → Fin m)
    (sigmaLabel : Fin (r + 1) → SignedLabel m) : Finset (Fin (r + 1)) :=
  by
    classical
    exact Finset.univ.filter fun j => SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j

theorem sigmaDeletionHasAlternatingLabelSetOf_extra {r m : ℕ}
    {idx : Fin r → Fin m} {sigmaLabel : Fin (r + 1) → SignedLabel m}
    {extra : Fin (r + 1)}
    (hridge : ∀ a : Fin r,
      sigmaLabel (extra.succAbove a) = alternatingLabelOf idx a) :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra := by
  intro a
  exact ⟨extra.succAbove a, Fin.succAbove_ne extra a, hridge a⟩

theorem sigmaDeletionHasAlternatingLabelSetOf_duplicate {r m : ℕ}
    {idx : Fin r → Fin m} {sigmaLabel : Fin (r + 1) → SignedLabel m}
    {extra : Fin (r + 1)} {k : Fin r}
    (hridge : ∀ a : Fin r,
      sigmaLabel (extra.succAbove a) = alternatingLabelOf idx a)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k) :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel (extra.succAbove k) := by
  intro a
  by_cases ha : a = k
  · subst a
    exact ⟨extra, Fin.ne_succAbove extra k, hextra⟩
  · exact ⟨extra.succAbove a, by
      intro h
      exact ha (Fin.succAbove_right_injective h), hridge a⟩

theorem sigmaDeletionHasAlternatingLabelSetOf_iff_duplicate {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)} {k : Fin r}
    (hridge : ∀ a : Fin r,
      sigmaLabel (extra.succAbove a) = alternatingLabelOf idx a)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k) (j : Fin (r + 1)) :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j ↔
      j = extra ∨ j = extra.succAbove k := by
  constructor
  · intro hdoor
    by_cases hje : j = extra
    · exact Or.inl hje
    · rcases Fin.exists_succAbove_eq hje with ⟨a, ha⟩
      by_cases hak : a = k
      · subst a
        exact Or.inr ha.symm
      · have hmissing := hdoor a
        rcases hmissing with ⟨t, htne, htlabel⟩
        by_cases htextra : t = extra
        · subst t
          rw [hextra] at htlabel
          exact False.elim (hak ((alternatingLabelOf_inj hidx).mp htlabel).symm)
        · rcases Fin.exists_succAbove_eq htextra with ⟨b, hb⟩
          rw [← hb, hridge b] at htlabel
          have hba : b = a := (alternatingLabelOf_inj hidx).mp htlabel
          exact False.elim (htne (by rw [← hb, hba, ha]))
  · intro h
    rcases h with rfl | rfl
    · exact sigmaDeletionHasAlternatingLabelSetOf_extra hridge
    · exact sigmaDeletionHasAlternatingLabelSetOf_duplicate hridge hextra

theorem sigmaDeletionHasAlternatingLabelSetOf_iff_opposite {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)} {k : Fin r}
    (hridge : ∀ a : Fin r,
      sigmaLabel (extra.succAbove a) = alternatingLabelOf idx a)
    (hextra : sigmaLabel extra = (alternatingLabelOf idx k).neg) (j : Fin (r + 1)) :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j ↔ j = extra := by
  constructor
  · intro hdoor
    by_cases hje : j = extra
    · exact hje
    · rcases Fin.exists_succAbove_eq hje with ⟨a, ha⟩
      rcases hdoor a with ⟨t, htne, htlabel⟩
      by_cases htextra : t = extra
      · subst t
        rw [hextra] at htlabel
        exact False.elim (alternatingLabelOf_neg_ne hidx k a htlabel)
      · rcases Fin.exists_succAbove_eq htextra with ⟨b, hb⟩
        rw [← hb, hridge b] at htlabel
        have hba : b = a := (alternatingLabelOf_inj hidx).mp htlabel
        exact False.elim (htne (by rw [← hb, hba, ha]))
  · intro h
    subst h
    exact sigmaDeletionHasAlternatingLabelSetOf_extra hridge

theorem sigmaDoorSetOf_card_duplicate {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)} {k : Fin r}
    (hridge : ∀ a : Fin r,
      sigmaLabel (extra.succAbove a) = alternatingLabelOf idx a)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k) :
    (sigmaDoorSetOf idx sigmaLabel).card = 2 := by
  classical
  have hset :
      sigmaDoorSetOf idx sigmaLabel = {extra, extra.succAbove k} := by
    ext j
    simp [sigmaDoorSetOf,
      sigmaDeletionHasAlternatingLabelSetOf_iff_duplicate hidx hridge hextra j, eq_comm]
  rw [hset]
  exact Finset.card_pair (Fin.ne_succAbove extra k)

theorem sigmaDoorSetOf_card_opposite {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)} {k : Fin r}
    (hridge : ∀ a : Fin r,
      sigmaLabel (extra.succAbove a) = alternatingLabelOf idx a)
    (hextra : sigmaLabel extra = (alternatingLabelOf idx k).neg) :
    (sigmaDoorSetOf idx sigmaLabel).card = 1 := by
  classical
  have hset : sigmaDoorSetOf idx sigmaLabel = {extra} := by
    ext j
    simp [sigmaDoorSetOf,
      sigmaDeletionHasAlternatingLabelSetOf_iff_opposite hidx hridge hextra j]
  rw [hset]
  simp

theorem sigmaDeletionHasAlternatingLabelSetOf_iff_not_duplicate {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hridge : ∀ a : Fin r,
      sigmaLabel (extra.succAbove a) = alternatingLabelOf idx a)
    (hnot : ∀ k : Fin r, sigmaLabel extra ≠ alternatingLabelOf idx k)
    (j : Fin (r + 1)) :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j ↔ j = extra := by
  constructor
  · intro hdoor
    by_cases hje : j = extra
    · exact hje
    · rcases Fin.exists_succAbove_eq hje with ⟨a, ha⟩
      rcases hdoor a with ⟨t, htne, htlabel⟩
      by_cases htextra : t = extra
      · subst t
        exact False.elim (hnot a htlabel)
      · rcases Fin.exists_succAbove_eq htextra with ⟨b, hb⟩
        rw [← hb, hridge b] at htlabel
        have hba : b = a := (alternatingLabelOf_inj hidx).mp htlabel
        exact False.elim (htne (by rw [← hb, hba, ha]))
  · intro h
    subst h
    exact sigmaDeletionHasAlternatingLabelSetOf_extra hridge

theorem sigmaDoorSetOf_card_not_duplicate {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hridge : ∀ a : Fin r,
      sigmaLabel (extra.succAbove a) = alternatingLabelOf idx a)
    (hnot : ∀ k : Fin r, sigmaLabel extra ≠ alternatingLabelOf idx k) :
    (sigmaDoorSetOf idx sigmaLabel).card = 1 := by
  classical
  have hset : sigmaDoorSetOf idx sigmaLabel = {extra} := by
    ext j
    simp [sigmaDoorSetOf,
      sigmaDeletionHasAlternatingLabelSetOf_iff_not_duplicate hidx hridge hnot j]
  rw [hset]
  simp

theorem sigmaDeletionHasAlternatingLabelSetOf_duplicate_of_door {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra t : Fin (r + 1)} {k : Fin r}
    (hdoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k)
    (htne : t ≠ extra)
    (htlabel : sigmaLabel t = alternatingLabelOf idx k) :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel t := by
  intro a
  by_cases hak : a = k
  · subst a
    exact ⟨extra, by simpa [ne_eq, eq_comm] using htne, hextra⟩
  · rcases hdoor a with ⟨u, hune, hulabel⟩
    refine ⟨u, ?_, hulabel⟩
    intro hut
    subst u
    have hka : k = a := by
      apply (alternatingLabelOf_inj hidx).mp
      exact htlabel.symm.trans hulabel
    exact hak hka.symm

theorem sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra) :
    ((Finset.univ.erase extra).image sigmaLabel) = alternatingLabelSetOf idx := by
  classical
  let retained : Finset (Fin (r + 1)) := Finset.univ.erase extra
  have hA_subset :
      alternatingLabelSetOf idx ⊆ retained.image sigmaLabel := by
    intro L hL
    rcases (by simpa [alternatingLabelSetOf] using hL) with ⟨a, ha⟩
    rcases hdoor a with ⟨t, htne, htlabel⟩
    exact Finset.mem_image.mpr ⟨t, by simp [retained, htne], htlabel.trans ha⟩
  have hcard_le :
      (retained.image sigmaLabel).card ≤ (alternatingLabelSetOf idx).card := by
    have himage_le : (retained.image sigmaLabel).card ≤ retained.card :=
      Finset.card_image_le
    have hretained : retained.card = r := by
      simp [retained]
    simpa [alternatingLabelSetOf_card hidx, hretained] using himage_le
  have hEq : alternatingLabelSetOf idx = retained.image sigmaLabel :=
    Finset.eq_of_subset_of_card_le hA_subset hcard_le
  exact hEq.symm

theorem sigmaDeletionHasAlternatingLabelSetOf_retained_injOn {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra) :
    Set.InjOn sigmaLabel (Finset.univ.erase extra) := by
  classical
  let retained : Finset (Fin (r + 1)) := Finset.univ.erase extra
  have himage := sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
    (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoor
  have hcard :
      (retained.image sigmaLabel).card = retained.card := by
    rw [himage, alternatingLabelSetOf_card hidx]
    simp [retained]
  exact (Finset.card_image_iff).mp hcard

theorem sigmaDoorSetOf_card_duplicate_of_door {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)} {k : Fin r}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k) :
    (sigmaDoorSetOf idx sigmaLabel).card = 2 := by
  classical
  rcases hdoorExtra k with ⟨t, htne, htlabel⟩
  have htDoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel t :=
    sigmaDeletionHasAlternatingLabelSetOf_duplicate_of_door
      (idx := idx) hidx (extra := extra) (t := t) (k := k)
      hdoorExtra hextra htne htlabel
  have hinj :=
    sigmaDeletionHasAlternatingLabelSetOf_retained_injOn
      (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have himage :=
    sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
      (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have hmem_imp :
      ∀ j, j ∈ sigmaDoorSetOf idx sigmaLabel → j = extra ∨ j = t := by
    intro j hj
    have hdoorj : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j := by
      simpa [sigmaDoorSetOf] using hj
    by_cases hjextra : j = extra
    · exact Or.inl hjextra
    · right
      have hjret : j ∈ (Finset.univ.erase extra : Finset (Fin (r + 1))) := by
        simp [hjextra]
      have hjimage : sigmaLabel j ∈ (Finset.univ.erase extra).image sigmaLabel :=
        Finset.mem_image.mpr ⟨j, hjret, rfl⟩
      rw [himage] at hjimage
      rcases (by simpa [alternatingLabelSetOf] using hjimage) with ⟨b, hjlabel⟩
      by_cases hbk : b = k
      · subst b
        exact hinj hjret (by simp [htne]) (hjlabel.symm.trans htlabel.symm)
      · rcases hdoorj b with ⟨u, hune, hulabel⟩
        have huneExtra : u ≠ extra := by
          intro hue
          subst u
          have hkb : k = b := (alternatingLabelOf_inj hidx).mp
            (hextra.symm.trans hulabel)
          exact hbk hkb.symm
        have huret : u ∈ (Finset.univ.erase extra : Finset (Fin (r + 1))) := by
          simp [huneExtra]
        have huj : u = j :=
          hinj huret hjret (hulabel.trans hjlabel)
        exact False.elim (hune huj)
  have hset : sigmaDoorSetOf idx sigmaLabel = {extra, t} := by
    ext j
    constructor
    · intro hj
      rcases hmem_imp j hj with rfl | rfl <;> simp
    · intro hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · simpa [sigmaDoorSetOf] using hdoorExtra
      · simpa [sigmaDoorSetOf] using htDoor
  rw [hset]
  exact Finset.card_pair htne.symm

theorem sigmaDoorSetOf_card_not_duplicate_of_door {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra)
    (hnot : ∀ k : Fin r, sigmaLabel extra ≠ alternatingLabelOf idx k) :
    (sigmaDoorSetOf idx sigmaLabel).card = 1 := by
  classical
  have hinj :=
    sigmaDeletionHasAlternatingLabelSetOf_retained_injOn
      (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have himage :=
    sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
      (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have hmem_imp :
      ∀ j, j ∈ sigmaDoorSetOf idx sigmaLabel → j = extra := by
    intro j hj
    have hdoorj : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j := by
      simpa [sigmaDoorSetOf] using hj
    by_cases hjextra : j = extra
    · exact hjextra
    · have hjret : j ∈ (Finset.univ.erase extra : Finset (Fin (r + 1))) := by
        simp [hjextra]
      have hjimage : sigmaLabel j ∈ (Finset.univ.erase extra).image sigmaLabel :=
        Finset.mem_image.mpr ⟨j, hjret, rfl⟩
      rw [himage] at hjimage
      rcases (by simpa [alternatingLabelSetOf] using hjimage) with ⟨b, hjlabel⟩
      rcases hdoorj b with ⟨u, hune, hulabel⟩
      have huneExtra : u ≠ extra := by
        intro hue
        subst u
        exact hnot b hulabel
      have huret : u ∈ (Finset.univ.erase extra : Finset (Fin (r + 1))) := by
        simp [huneExtra]
      have huj : u = j :=
        hinj huret hjret (hulabel.trans hjlabel)
      exact False.elim (hune huj)
  have hset : sigmaDoorSetOf idx sigmaLabel = {extra} := by
    ext j
    constructor
    · intro hj
      exact by simpa using hmem_imp j hj
    · intro hj
      simp only [Finset.mem_singleton] at hj
      subst j
      simpa [sigmaDoorSetOf] using hdoorExtra
  rw [hset]
  simp

theorem sigmaDoorSetOf_odd_iff_card_one_of_door {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra) :
    Odd (sigmaDoorSetOf idx sigmaLabel).card ↔
      (sigmaDoorSetOf idx sigmaLabel).card = 1 := by
  classical
  by_cases hdup : ∃ k : Fin r, sigmaLabel extra = alternatingLabelOf idx k
  · rcases hdup with ⟨k, hk⟩
    have hcard :=
      sigmaDoorSetOf_card_duplicate_of_door
        (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) (k := k)
        hdoorExtra hk
    rw [hcard]
    simp
  · have hcard :=
      sigmaDoorSetOf_card_not_duplicate_of_door
        (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra)
        hdoorExtra (by intro k hk; exact hdup ⟨k, hk⟩)
    rw [hcard]
    simp

theorem sigmaDeletionHasAlternatingLabelSet_extra {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a) :
    SigmaDeletionHasAlternatingLabelSet sigmaLabel extra := by
  intro a
  exact ⟨extra.succAbove a, Fin.succAbove_ne extra a, hridge a⟩

theorem sigmaDeletionHasAlternatingLabelSet_duplicate {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a)
    (hextra : sigmaLabel extra = alternatingLabel k) :
    SigmaDeletionHasAlternatingLabelSet sigmaLabel (extra.succAbove k) := by
  intro a
  by_cases ha : a = k
  · subst a
    exact ⟨extra, Fin.ne_succAbove extra k, hextra⟩
  · exact ⟨extra.succAbove a, by
      intro h
      exact ha (Fin.succAbove_right_injective h), hridge a⟩

theorem sigmaDeletionHasAlternatingLabelSet_iff_duplicate {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a)
    (hextra : sigmaLabel extra = alternatingLabel k) (j : Fin (d + 1)) :
    SigmaDeletionHasAlternatingLabelSet sigmaLabel j ↔
      j = extra ∨ j = extra.succAbove k := by
  constructor
  · intro hdoor
    by_cases hje : j = extra
    · exact Or.inl hje
    · rcases Fin.exists_succAbove_eq hje with ⟨a, ha⟩
      by_cases hak : a = k
      · subst a
        exact Or.inr ha.symm
      · have hmissing := hdoor a
        rcases hmissing with ⟨t, htne, htlabel⟩
        by_cases htextra : t = extra
        · subst t
          rw [hextra] at htlabel
          exact False.elim (hak ((alternatingLabel_inj.mp htlabel).symm))
        · rcases Fin.exists_succAbove_eq htextra with ⟨b, hb⟩
          rw [← hb, hridge b] at htlabel
          have hba : b = a := alternatingLabel_inj.mp htlabel
          exact False.elim (htne (by rw [← hb, hba, ha]))
  · intro h
    rcases h with rfl | rfl
    · exact sigmaDeletionHasAlternatingLabelSet_extra hridge
    · exact sigmaDeletionHasAlternatingLabelSet_duplicate hridge hextra

theorem sigmaDeletionHasAlternatingLabelSet_iff_opposite {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a)
    (hextra : sigmaLabel extra = (alternatingLabel k).neg) (j : Fin (d + 1)) :
    SigmaDeletionHasAlternatingLabelSet sigmaLabel j ↔ j = extra := by
  constructor
  · intro hdoor
    by_cases hje : j = extra
    · exact hje
    · rcases Fin.exists_succAbove_eq hje with ⟨a, ha⟩
      rcases hdoor a with ⟨t, htne, htlabel⟩
      by_cases htextra : t = extra
      · subst t
        rw [hextra] at htlabel
        exact False.elim (alternatingLabel_neg_ne k a htlabel)
      · rcases Fin.exists_succAbove_eq htextra with ⟨b, hb⟩
        rw [← hb, hridge b] at htlabel
        have hba : b = a := alternatingLabel_inj.mp htlabel
        exact False.elim (htne (by rw [← hb, hba, ha]))
  · intro h
    subst h
    exact sigmaDeletionHasAlternatingLabelSet_extra hridge

theorem sigmaDoorSet_card_duplicate {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a)
    (hextra : sigmaLabel extra = alternatingLabel k) :
    (sigmaDoorSet sigmaLabel).card = 2 := by
  classical
  have hset :
      sigmaDoorSet sigmaLabel = {extra, extra.succAbove k} := by
    ext j
    simp [sigmaDoorSet, sigmaDeletionHasAlternatingLabelSet_iff_duplicate hridge hextra j,
      eq_comm]
  rw [hset]
  exact Finset.card_pair (Fin.ne_succAbove extra k)

theorem sigmaDoorSet_card_opposite {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a)
    (hextra : sigmaLabel extra = (alternatingLabel k).neg) :
    (sigmaDoorSet sigmaLabel).card = 1 := by
  classical
  have hset : sigmaDoorSet sigmaLabel = {extra} := by
    ext j
    simp [sigmaDoorSet, sigmaDeletionHasAlternatingLabelSet_iff_opposite hridge hextra j]
  rw [hset]
  simp

theorem sigmaDoorSet_card_eq_one_iff_extra_opposite {d : ℕ} (_hd : 0 < d)
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a) :
    (sigmaDoorSet sigmaLabel).card = 1 ↔
      ∃ k : Fin d, sigmaLabel extra = (alternatingLabel k).neg := by
  constructor
  · intro hcard
    rcases signedLabel_eq_alternating_or_neg (sigmaLabel extra) with hpos | hneg
    · have htwo := sigmaDoorSet_card_duplicate (extra := extra)
        (k := (sigmaLabel extra).index) hridge hpos
      omega
    · exact ⟨(sigmaLabel extra).index, hneg⟩
  · rintro ⟨k, hk⟩
    exact sigmaDoorSet_card_opposite hridge hk

theorem sigma_opposite_extra_gives_complementary_labels {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a)
    (hextra : sigmaLabel extra = (alternatingLabel k).neg) :
    sigmaLabel extra = (sigmaLabel (extra.succAbove k)).neg := by
  rw [hridge k]
  exact hextra

/-! ## Rho-degree and Fan handshaking interfaces

The next declarations isolate the finite parity core used by the hemisphere
argument.  The geometric degree facts are stated on nonempty, concrete finite
types; the parity theorem itself is the standard bipartite handshaking count
modulo two.
-/

theorem finset_card_filter_cast_zmod_two {α : Type*}
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    ((s.filter p).card : ZMod 2) =
      ∑ x ∈ s, if p x then (1 : ZMod 2) else 0 := by
  rw [Finset.sum_boole]

theorem fintype_card_subtype_cast_zmod_two {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] :
    (Fintype.card {x : α // p x} : ZMod 2) =
      ∑ x : α, if p x then (1 : ZMod 2) else 0 := by
  classical
  rw [← finset_card_filter_cast_zmod_two (Finset.univ : Finset α) p]
  exact congrArg (fun n : ℕ => (n : ZMod 2)) (Fintype.card_subtype p)

/-- In a finite bipartite graph, the number of odd-degree vertices on the
left equals the number of odd-degree vertices on the right modulo two. -/
theorem bipartite_odd_degree_card_eq_mod_two
    {R S : Type*} [Fintype R] [Fintype S]
    (edge : R → S → Prop) [DecidableRel edge] :
    (Fintype.card {r : R // Odd (Fintype.card {s : S // edge r s})} : ZMod 2) =
      (Fintype.card {s : S // Odd (Fintype.card {r : R // edge r s})} : ZMod 2) := by
  classical
  rw [fintype_card_subtype_cast_zmod_two, fintype_card_subtype_cast_zmod_two]
  calc
    (∑ r : R, if Odd (Fintype.card {s : S // edge r s}) then (1 : ZMod 2) else 0)
        = ∑ r : R, (Fintype.card {s : S // edge r s} : ZMod 2) := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          by_cases hodd : Odd (Fintype.card {s : S // edge r s})
          · rw [if_pos hodd]
            exact hodd.natCast_zmod_two.symm
          · rw [if_neg hodd]
            have heven : Even (Fintype.card {s : S // edge r s}) :=
              Nat.not_odd_iff_even.mp hodd
            exact heven.natCast_zmod_two.symm
    _ = ∑ r : R, ∑ s : S, if edge r s then (1 : ZMod 2) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          rw [← fintype_card_subtype_cast_zmod_two (fun s : S => edge r s)]
    _ = ∑ s : S, ∑ r : R, if edge r s then (1 : ZMod 2) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ s : S, (Fintype.card {r : R // edge r s} : ZMod 2) := by
          refine Finset.sum_congr rfl ?_
          intro s _hs
          rw [← fintype_card_subtype_cast_zmod_two (fun r : R => edge r s)]
    _ = ∑ s : S, if Odd (Fintype.card {r : R // edge r s}) then (1 : ZMod 2) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro s _hs
          by_cases hodd : Odd (Fintype.card {r : R // edge r s})
          · rw [if_pos hodd]
            exact hodd.natCast_zmod_two
          · rw [if_neg hodd]
            have heven : Even (Fintype.card {r : R // edge r s}) :=
              Nat.not_odd_iff_even.mp hodd
            exact heven.natCast_zmod_two

theorem bipartite_boundary_top_parity
    {R S : Type*} [Fintype R] [Fintype S]
    (edge : R → S → Prop) [DecidableRel edge]
    (boundary : R → Prop) [DecidablePred boundary]
    (topOdd : S → Prop) [DecidablePred topOdd]
    (hr :
      ∀ r : R,
        (Odd (Fintype.card {s : S // edge r s}) ↔ boundary r))
    (hs :
      ∀ s : S,
        (Odd (Fintype.card {r : R // edge r s}) ↔ topOdd s)) :
    (Fintype.card {r : R // boundary r} : ZMod 2) =
      (Fintype.card {s : S // topOdd s} : ZMod 2) := by
  classical
  have hodd := bipartite_odd_degree_card_eq_mod_two (R := R) (S := S) edge
  have hR :
      Fintype.card {r : R // Odd (Fintype.card {s : S // edge r s})} =
        Fintype.card {r : R // boundary r} := by
    exact Fintype.card_congr
      { toFun := fun r => ⟨r.1, (hr r.1).mp r.2⟩
        invFun := fun r => ⟨r.1, (hr r.1).mpr r.2⟩
        left_inv := by intro r; cases r; rfl
        right_inv := by intro r; cases r; rfl }
  have hS :
      Fintype.card {s : S // Odd (Fintype.card {r : R // edge r s})} =
        Fintype.card {s : S // topOdd s} := by
    exact Fintype.card_congr
      { toFun := fun s => ⟨s.1, (hs s.1).mp s.2⟩
        invFun := fun s => ⟨s.1, (hs s.1).mpr s.2⟩
        left_inv := by intro s; cases s; rfl
        right_inv := by intro s; cases s; rfl }
  simpa [hR, hS] using hodd

/-- A checked, non-degenerate package for the codimension-one rho degree in
the upper hemisphere.  `R` is the finite type of actual `(r-2)`-ridges and `S`
the finite type of upper top simplices incident to them; `nonempty_R` records
that the ridge side has not collapsed to an empty type. -/
structure RhoDegreeManifoldData (R S : Type*) [Fintype R] [Fintype S] where
  edge : R → S → Prop
  edge_decidable : DecidableRel edge
  boundary : R → Prop
  boundary_decidable : DecidablePred boundary
  nonempty_R : Nonempty R
  degree_card :
    ∀ r : R,
      Fintype.card {s : S // edge r s} = if boundary r then 1 else 2

namespace RhoDegreeManifoldData

attribute [instance] edge_decidable boundary_decidable

theorem odd_degree_iff_boundary
    {R S : Type*} [Fintype R] [Fintype S]
    (D : RhoDegreeManifoldData R S) (r : R) :
    Odd (Fintype.card {s : S // D.edge r s}) ↔ D.boundary r := by
  rw [D.degree_card r]
  by_cases hb : D.boundary r <;> simp [hb]

theorem boundary_top_parity
    {R S : Type*} [Fintype R] [Fintype S]
    (D : RhoDegreeManifoldData R S)
    (topOdd : S → Prop) [DecidablePred topOdd]
    (hs :
      ∀ s : S,
        (Odd (Fintype.card {r : R // D.edge r s}) ↔ topOdd s)) :
    (Fintype.card {r : R // D.boundary r} : ZMod 2) =
      (Fintype.card {s : S // topOdd s} : ZMod 2) := by
  classical
  exact bipartite_boundary_top_parity D.edge D.boundary topOdd
    (D.odd_degree_iff_boundary) hs

end RhoDegreeManifoldData

/-- The sigma-degree fact used in the final Tucker reduction: once the ridge
labels are exactly `A`, a one-door top simplex has an extra label opposite to
one ridge label. -/
theorem sigmaDoorSet_card_one_gives_complementary_labels {d : ℕ} (hd : 0 < d)
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hridge : ∀ a : Fin d, sigmaLabel (extra.succAbove a) = alternatingLabel a)
    (hcard : (sigmaDoorSet sigmaLabel).card = 1) :
    ∃ k : Fin d,
      sigmaLabel extra = (sigmaLabel (extra.succAbove k)).neg := by
  rcases (sigmaDoorSet_card_eq_one_iff_extra_opposite hd hridge).mp hcard with ⟨k, hk⟩
  exact ⟨k, sigma_opposite_extra_gives_complementary_labels hridge hk⟩

/-- Final local reduction from a one-door `σ` in the label-set-`A` graph to
the same-index, opposite-sign pair on that chain. -/
theorem sigmaDoorSet_card_one_gives_chain_complementary_pair {d : ℕ} (hd : 0 < d)
    {sigma : Fin (d + 1) → NonzeroSignedSubset n}
    {label : NonzeroSignedSubset n → SignedLabel d}
    {extra : Fin (d + 1)}
    (hridge : ∀ a : Fin d, label (sigma (extra.succAbove a)) = alternatingLabel a)
    (hcard : (sigmaDoorSet (fun i => label (sigma i))).card = 1) :
    ∃ i j : Fin (d + 1), i ≠ j ∧
      (label (sigma i)).index = (label (sigma j)).index ∧
      (label (sigma i)).positive ≠ (label (sigma j)).positive := by
  obtain ⟨k, hk⟩ :=
    sigmaDoorSet_card_one_gives_complementary_labels (d := d) hd
      (sigmaLabel := fun i => label (sigma i)) (extra := extra) hridge hcard
  refine ⟨extra, extra.succAbove k, Fin.ne_succAbove extra k, ?_, ?_⟩
  · have hidx := congrArg SignedLabel.index hk
    simpa [SignedLabel.neg] using hidx
  · have hpos := congrArg SignedLabel.positive hk
    cases h₁ : (label (sigma extra)).positive <;>
      cases h₂ : (label (sigma (extra.succAbove k))).positive <;>
        simp [SignedLabel.neg, h₁, h₂] at hpos ⊢

theorem unordered_chain_complementary_pair_order {N d : ℕ}
    {sigma : Fin N → NonzeroSignedSubset n}
    {label : NonzeroSignedSubset n → SignedLabel d}
    {i j : Fin N}
    (hij : i ≠ j)
    (hidx : (label (sigma i)).index = (label (sigma j)).index)
    (hsign : (label (sigma i)).positive ≠ (label (sigma j)).positive) :
    ∃ a b : Fin N, a < b ∧
      (label (sigma a)).index = (label (sigma b)).index ∧
      (label (sigma a)).positive ≠ (label (sigma b)).positive := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨i, j, hlt, hidx, hsign⟩
  · exact ⟨j, i, hgt, hidx.symm, hsign.symm⟩

theorem sigmaDoorSet_card_one_gives_ordered_chain_complementary_pair {d : ℕ} (hd : 0 < d)
    {sigma : Fin (d + 1) → NonzeroSignedSubset n}
    {label : NonzeroSignedSubset n → SignedLabel d}
    {extra : Fin (d + 1)}
    (hridge : ∀ a : Fin d, label (sigma (extra.succAbove a)) = alternatingLabel a)
    (hcard : (sigmaDoorSet (fun i => label (sigma i))).card = 1) :
    ∃ i j : Fin (d + 1), i < j ∧
      (label (sigma i)).index = (label (sigma j)).index ∧
      (label (sigma i)).positive ≠ (label (sigma j)).positive := by
  obtain ⟨i, j, hij, hidx, hsign⟩ :=
    sigmaDoorSet_card_one_gives_chain_complementary_pair (d := d) hd hridge hcard
  exact unordered_chain_complementary_pair_order hij hidx hsign

theorem sigmaDoorSet_card_one_gives_prefixChain_complementary_pair {d : ℕ} (hd : 0 < d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    {P : SignedPermutation (d + 1)} {extra : Fin (d + 1)}
    (hridge :
      ∀ a : Fin d, label (P.prefixChain (extra.succAbove a)) = alternatingLabel a)
    (hcard : (sigmaDoorSet (fun i => label (P.prefixChain i))).card = 1) :
    ∃ i j : Fin (d + 1), i < j ∧
      (label (P.prefixChain i)).index = (label (P.prefixChain j)).index ∧
      (label (P.prefixChain i)).positive ≠ (label (P.prefixChain j)).positive :=
  sigmaDoorSet_card_one_gives_ordered_chain_complementary_pair
    (n := d + 1) (d := d) hd (sigma := fun i => P.prefixChain i)
    (label := label) (extra := extra) hridge hcard

theorem sigmaDeletionHasAlternatingLabelSet_duplicate_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra t : Fin (d + 1)} {k : Fin d}
    (hdoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabel k)
    (htne : t ≠ extra)
    (htlabel : sigmaLabel t = alternatingLabel k) :
    SigmaDeletionHasAlternatingLabelSet sigmaLabel t := by
  intro a
  by_cases hak : a = k
  · subst a
    exact ⟨extra, by simpa [ne_eq, eq_comm] using htne, hextra⟩
  · rcases hdoor a with ⟨u, hune, hulabel⟩
    refine ⟨u, ?_, hulabel⟩
    intro hut
    subst u
    have hka : k = a := by
      apply alternatingLabel_inj.mp
      exact htlabel.symm.trans hulabel
    exact hak hka.symm

theorem sigmaDeletionHasAlternatingLabelSet_retained_image_eq {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra) :
    ((Finset.univ.erase extra).image sigmaLabel) = alternatingLabelSetA d := by
  classical
  let retained : Finset (Fin (d + 1)) := Finset.univ.erase extra
  have hA_subset :
      alternatingLabelSetA d ⊆ retained.image sigmaLabel := by
    intro L hL
    rcases (by simpa [alternatingLabelSetA] using hL) with ⟨a, ha⟩
    rcases hdoor a with ⟨t, htne, htlabel⟩
    exact Finset.mem_image.mpr ⟨t, by simp [retained, htne], htlabel.trans ha⟩
  have hcard_le :
      (retained.image sigmaLabel).card ≤ (alternatingLabelSetA d).card := by
    have himage_le : (retained.image sigmaLabel).card ≤ retained.card :=
      Finset.card_image_le
    have hretained : retained.card = d := by
      simp [retained]
    simpa [alternatingLabelSetA_card, hretained] using himage_le
  have hEq : alternatingLabelSetA d = retained.image sigmaLabel :=
    Finset.eq_of_subset_of_card_le hA_subset hcard_le
  exact hEq.symm

theorem sigmaDeletionHasAlternatingLabelSet_retained_injOn {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra) :
    Set.InjOn sigmaLabel (Finset.univ.erase extra) := by
  classical
  let retained : Finset (Fin (d + 1)) := Finset.univ.erase extra
  have himage := sigmaDeletionHasAlternatingLabelSet_retained_image_eq
    (sigmaLabel := sigmaLabel) (extra := extra) hdoor
  have hcard :
      (retained.image sigmaLabel).card = retained.card := by
    rw [himage, alternatingLabelSetA_card]
    simp [retained]
  exact (Finset.card_image_iff).mp hcard

theorem sigmaDoorSet_card_duplicate_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabel k) :
    (sigmaDoorSet sigmaLabel).card = 2 := by
  classical
  rcases hdoorExtra k with ⟨t, htne, htlabel⟩
  have htDoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel t :=
    sigmaDeletionHasAlternatingLabelSet_duplicate_of_door
      (extra := extra) (t := t) (k := k) hdoorExtra hextra htne htlabel
  have hinj :=
    sigmaDeletionHasAlternatingLabelSet_retained_injOn
      (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have himage :=
    sigmaDeletionHasAlternatingLabelSet_retained_image_eq
      (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have hmem_imp :
      ∀ j, j ∈ sigmaDoorSet sigmaLabel → j = extra ∨ j = t := by
    intro j hj
    have hdoorj : SigmaDeletionHasAlternatingLabelSet sigmaLabel j := by
      simpa [sigmaDoorSet] using hj
    by_cases hjextra : j = extra
    · exact Or.inl hjextra
    · right
      have hjret : j ∈ (Finset.univ.erase extra : Finset (Fin (d + 1))) := by
        simp [hjextra]
      have hjimage : sigmaLabel j ∈ (Finset.univ.erase extra).image sigmaLabel :=
        Finset.mem_image.mpr ⟨j, hjret, rfl⟩
      rw [himage] at hjimage
      rcases (by simpa [alternatingLabelSetA] using hjimage) with ⟨b, hjlabel⟩
      by_cases hbk : b = k
      · subst b
        exact hinj hjret (by simp [htne]) (hjlabel.symm.trans htlabel.symm)
      · rcases hdoorj b with ⟨u, hune, hulabel⟩
        have huneExtra : u ≠ extra := by
          intro hue
          subst u
          have hkb : k = b := alternatingLabel_inj.mp (hextra.symm.trans hulabel)
          exact hbk hkb.symm
        have huret : u ∈ (Finset.univ.erase extra : Finset (Fin (d + 1))) := by
          simp [huneExtra]
        have huj : u = j :=
          hinj huret hjret (hulabel.trans hjlabel)
        exact False.elim (hune huj)
  have hset : sigmaDoorSet sigmaLabel = {extra, t} := by
    ext j
    constructor
    · intro hj
      rcases hmem_imp j hj with rfl | rfl <;> simp
    · intro hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · simpa [sigmaDoorSet] using hdoorExtra
      · simpa [sigmaDoorSet] using htDoor
  rw [hset]
  exact Finset.card_pair htne.symm

theorem sigmaDoorSet_card_opposite_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hextra : sigmaLabel extra = (alternatingLabel k).neg) :
    (sigmaDoorSet sigmaLabel).card = 1 := by
  classical
  have hinj :=
    sigmaDeletionHasAlternatingLabelSet_retained_injOn
      (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have himage :=
    sigmaDeletionHasAlternatingLabelSet_retained_image_eq
      (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have hmem_imp :
      ∀ j, j ∈ sigmaDoorSet sigmaLabel → j = extra := by
    intro j hj
    have hdoorj : SigmaDeletionHasAlternatingLabelSet sigmaLabel j := by
      simpa [sigmaDoorSet] using hj
    by_cases hjextra : j = extra
    · exact hjextra
    · have hjret : j ∈ (Finset.univ.erase extra : Finset (Fin (d + 1))) := by
        simp [hjextra]
      have hjimage : sigmaLabel j ∈ (Finset.univ.erase extra).image sigmaLabel :=
        Finset.mem_image.mpr ⟨j, hjret, rfl⟩
      rw [himage] at hjimage
      rcases (by simpa [alternatingLabelSetA] using hjimage) with ⟨b, hjlabel⟩
      rcases hdoorj b with ⟨u, hune, hulabel⟩
      have huneExtra : u ≠ extra := by
        intro hue
        subst u
        exact alternatingLabel_neg_ne k b (hextra.symm.trans hulabel)
      have huret : u ∈ (Finset.univ.erase extra : Finset (Fin (d + 1))) := by
        simp [huneExtra]
      have huj : u = j :=
        hinj huret hjret (hulabel.trans hjlabel)
      exact False.elim (hune huj)
  have hset : sigmaDoorSet sigmaLabel = {extra} := by
    ext j
    constructor
    · intro hj
      exact by simpa using hmem_imp j hj
    · intro hj
      simp only [Finset.mem_singleton] at hj
      subst j
      simpa [sigmaDoorSet] using hdoorExtra
  rw [hset]
  simp

theorem sigmaDoorSet_odd_iff_card_one_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra) :
    Odd (sigmaDoorSet sigmaLabel).card ↔ (sigmaDoorSet sigmaLabel).card = 1 := by
  rcases signedLabel_eq_alternating_or_neg (sigmaLabel extra) with hpos | hneg
  · have hcard :=
      sigmaDoorSet_card_duplicate_of_door (sigmaLabel := sigmaLabel)
        (extra := extra) (k := (sigmaLabel extra).index) hdoorExtra hpos
    rw [hcard]
    simp
  · have hcard :=
      sigmaDoorSet_card_opposite_of_door (sigmaLabel := sigmaLabel)
        (extra := extra) (k := (sigmaLabel extra).index) hdoorExtra hneg
    rw [hcard]
    simp

theorem sigmaDoorSet_card_one_gives_chain_complementary_pair_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hcard : (sigmaDoorSet sigmaLabel).card = 1) :
    ∃ i j : Fin (d + 1), i ≠ j ∧
      (sigmaLabel i).index = (sigmaLabel j).index ∧
      (sigmaLabel i).positive ≠ (sigmaLabel j).positive := by
  classical
  have hextra_mem : extra ∈ sigmaDoorSet sigmaLabel := by
    simpa [sigmaDoorSet] using hdoorExtra
  rcases signedLabel_eq_alternating_or_neg (sigmaLabel extra) with hpos | hneg
  · let k : Fin d := (sigmaLabel extra).index
    rcases hdoorExtra k with ⟨t, htne, htlabel⟩
    have htdoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel t :=
      sigmaDeletionHasAlternatingLabelSet_duplicate_of_door
        (extra := extra) (t := t) (k := k) hdoorExtra hpos htne htlabel
    have ht_mem : t ∈ sigmaDoorSet sigmaLabel := by
      simpa [sigmaDoorSet] using htdoor
    have hle : (sigmaDoorSet sigmaLabel).card ≤ 1 := by omega
    have hteq : t = extra :=
      (Finset.card_le_one_iff.mp hle) ht_mem hextra_mem
    exact False.elim (htne hteq)
  · let k : Fin d := (sigmaLabel extra).index
    rcases hdoorExtra k with ⟨t, htne, htlabel⟩
    refine ⟨extra, t, htne.symm, ?_, ?_⟩
    · have hcomp : sigmaLabel extra = (sigmaLabel t).neg := by
        rw [htlabel]
        exact hneg
      have hidx := congrArg SignedLabel.index hcomp
      simpa [SignedLabel.neg] using hidx
    · have hcomp : sigmaLabel extra = (sigmaLabel t).neg := by
        rw [htlabel]
        exact hneg
      have hpos' := congrArg SignedLabel.positive hcomp
      cases h₁ : (sigmaLabel extra).positive <;>
        cases h₂ : (sigmaLabel t).positive <;>
          simp [SignedLabel.neg, h₁, h₂] at hpos' ⊢

theorem sigmaDoorSet_card_one_gives_ordered_chain_complementary_pair_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hcard : (sigmaDoorSet sigmaLabel).card = 1) :
    ∃ i j : Fin (d + 1), i < j ∧
      (sigmaLabel i).index = (sigmaLabel j).index ∧
      (sigmaLabel i).positive ≠ (sigmaLabel j).positive := by
  obtain ⟨i, j, hij, hidx, hsign⟩ :=
    sigmaDoorSet_card_one_gives_chain_complementary_pair_of_door hdoorExtra hcard
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨i, j, hlt, hidx, hsign⟩
  · exact ⟨j, i, hgt, hidx.symm, hsign.symm⟩

theorem sigmaDoorSet_card_one_gives_prefixChain_complementary_pair_of_door {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    {P : SignedPermutation (d + 1)} {extra : Fin (d + 1)}
    (hdoorExtra :
      SigmaDeletionHasAlternatingLabelSet (fun i => label (P.prefixChain i)) extra)
    (hcard : (sigmaDoorSet (fun i => label (P.prefixChain i))).card = 1) :
    ∃ i j : Fin (d + 1), i < j ∧
      (label (P.prefixChain i)).index = (label (P.prefixChain j)).index ∧
      (label (P.prefixChain i)).positive ≠ (label (P.prefixChain j)).positive :=
  sigmaDoorSet_card_one_gives_ordered_chain_complementary_pair_of_door
    (sigmaLabel := fun i => label (P.prefixChain i)) hdoorExtra hcard

namespace SignedPermutation

theorem ext_order_positive {n : ℕ} {P Q : SignedPermutation n}
    (horder : P.order = Q.order) (hpositive : P.positive = Q.positive) : P = Q := by
  cases P
  cases Q
  simp at horder hpositive
  subst horder
  subst hpositive
  rfl

/-- Reindex the positions of a signed permutation, moving the signed atoms
together.  For adjacent swaps this is the second top simplex through a
punctured full flag. -/
def reindexPositions {n : ℕ} (P : SignedPermutation n) (τ : Equiv.Perm (Fin n)) :
    SignedPermutation n where
  order := τ.trans P.order
  positive := fun i => P.positive (τ i)

theorem reindexPositions_reindexPositions {n : ℕ}
    (P : SignedPermutation n) (τ υ : Equiv.Perm (Fin n)) :
    (P.reindexPositions τ).reindexPositions υ =
      P.reindexPositions (υ.trans τ) := by
  apply ext_order_positive
  · apply Equiv.ext
    intro i
    rfl
  · funext i
    rfl

theorem reindexPositions_swap_involutive {n : ℕ}
    (P : SignedPermutation n) (a b : Fin n) :
    (P.reindexPositions (Equiv.swap a b)).reindexPositions (Equiv.swap a b) = P := by
  rw [reindexPositions_reindexPositions]
  apply ext_order_positive
  · apply Equiv.ext
    intro i
    simp [reindexPositions]
  · funext i
    simp [reindexPositions]

theorem reindexPositions_swap_ne_self {n : ℕ}
    (P : SignedPermutation n) {a b : Fin n} (hab : a ≠ b) :
    P.reindexPositions (Equiv.swap a b) ≠ P := by
  intro h
  have horder := congrArg SignedPermutation.order h
  have hfun := congrArg (fun e : Equiv.Perm (Fin n) => e a) horder
  simp [reindexPositions] at hfun
  exact hab hfun.symm

/-- The successor of a non-last deleted rank, as an element of the same `Fin`
type. -/
def gapNext {n : ℕ} (gap : Fin (n + 1)) (hgap : gap.val < n) : Fin (n + 1) :=
  ⟨gap.val + 1, by omega⟩

theorem gapNext_val {n : ℕ} (gap : Fin (n + 1)) (hgap : gap.val < n) :
    (gapNext gap hgap).val = gap.val + 1 :=
  rfl

theorem reindexPositions_swap_gap_ne_self {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n) :
    P.reindexPositions (Equiv.swap gap (gapNext gap hgap)) ≠ P := by
  apply P.reindexPositions_swap_ne_self
  intro h
  have hval := congrArg Fin.val h
  simp [gapNext] at hval

/-- Flip the sign introduced at one position, keeping the order fixed. -/
def flipSignAt {n : ℕ} (P : SignedPermutation n) (j : Fin n) : SignedPermutation n where
  order := P.order
  positive := fun i => if i = j then !P.positive i else P.positive i

theorem flipSignAt_involutive {n : ℕ} (P : SignedPermutation n) (j : Fin n) :
    (P.flipSignAt j).flipSignAt j = P := by
  apply ext_order_positive
  · rfl
  · funext i
    by_cases hij : i = j <;> simp [flipSignAt, hij]

theorem flipSignAt_ne_self {n : ℕ} (P : SignedPermutation n) (j : Fin n) :
    P.flipSignAt j ≠ P := by
  intro h
  have hpositive := congrArg SignedPermutation.positive h
  have hj := congrFun hpositive j
  cases hsign : P.positive j <;> simp [flipSignAt, hsign] at hj

theorem prefixSignedSubset_support {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (P.prefixSignedSubset i).support =
      Finset.univ.filter fun x : Fin n => P.order.symm x ≤ i := by
  ext x
  by_cases hpos : P.positive (P.order.symm x)
  · simp [SignedSubset.support, prefixSignedSubset, prefixPos, prefixNeg, hpos]
  · simp [SignedSubset.support, prefixSignedSubset, prefixPos, prefixNeg, hpos]

theorem prefix_support_eq_order_image_Iic {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (Finset.univ.filter fun x : Fin n => P.order.symm x ≤ i) =
      (Finset.Iic i).map P.order.toEmbedding := by
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine Finset.mem_map.mpr ⟨P.order.symm x, ?_, by simp⟩
    simpa using hx
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨j, hj, rfl⟩
    simpa using hj

theorem prefix_support_card {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (Finset.univ.filter fun x : Fin n => P.order.symm x ≤ i).card = i.val + 1 := by
  rw [prefix_support_eq_order_image_Iic P i, Finset.card_map]
  simp

theorem prefixSignedSubset_card {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (P.prefixSignedSubset i).card = i.val + 1 := by
  have hsupport_card :
      (P.prefixSignedSubset i).support.card = (P.prefixSignedSubset i).card := by
    simp [SignedSubset.support, SignedSubset.card, prefixSignedSubset,
      Finset.card_union_of_disjoint (P.prefix_disjoint i)]
  rw [← hsupport_card, prefixSignedSubset_support, prefix_support_card]

theorem prefixChain_card {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (P.prefixChain i).1.card = i.val + 1 :=
  P.prefixSignedSubset_card i

theorem prefixChain_card_lt_of_lt {n : ℕ} (P : SignedPermutation n) {i j : Fin n}
    (hij : i < j) :
    (P.prefixChain i).1.card < (P.prefixChain j).1.card := by
  rw [P.prefixChain_card i, P.prefixChain_card j]
  omega

theorem prefixChain_ne_of_lt {n : ℕ} (P : SignedPermutation n) {i j : Fin n}
    (hij : i < j) :
    P.prefixChain i ≠ P.prefixChain j := by
  intro h
  have hcard := congrArg (fun X : NonzeroSignedSubset n => X.1.card) h
  have hlt := P.prefixChain_card_lt_of_lt hij
  exact (ne_of_lt hlt) hcard

theorem prefixChain_injective {n : ℕ} (P : SignedPermutation n) :
    Function.Injective P.prefixChain := by
  intro i j hij
  by_cases h : i = j
  · exact h
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · exact (P.prefixChain_ne_of_lt hlt hij).elim
    · exact (P.prefixChain_ne_of_lt hgt hij.symm).elim

theorem prefixChain_eq_iff {n : ℕ} (P : SignedPermutation n) {i j : Fin n} :
    P.prefixChain i = P.prefixChain j ↔ i = j := by
  constructor
  · intro h
    exact P.prefixChain_injective h
  · intro h
    rw [h]

theorem prefixChain_le_iff {n : ℕ} (P : SignedPermutation n) {i j : Fin n} :
    SignedSubset.Le (P.prefixChain i).1 (P.prefixChain j).1 ↔ i ≤ j := by
  constructor
  · intro hle
    have hpos_le : (P.prefixChain i).1.pos.card ≤ (P.prefixChain j).1.pos.card :=
      Finset.card_le_card hle.1
    have hneg_le : (P.prefixChain i).1.neg.card ≤ (P.prefixChain j).1.neg.card :=
      Finset.card_le_card hle.2
    have hcard : (P.prefixChain i).1.card ≤ (P.prefixChain j).1.card := by
      simp [SignedSubset.card]
      omega
    rw [P.prefixChain_card i, P.prefixChain_card j] at hcard
    exact Fin.le_iff_val_le_val.mpr (by omega)
  · intro hij
    exact P.prefixChain_le hij

theorem order_mem_prefixPos_iff {n : ℕ} (P : SignedPermutation n) (i j : Fin n) :
    P.order i ∈ P.prefixPos j ↔ i ≤ j ∧ P.positive i := by
  simp [prefixPos]

theorem order_mem_prefixNeg_iff {n : ℕ} (P : SignedPermutation n) (i j : Fin n) :
    P.order i ∈ P.prefixNeg j ↔ i ≤ j ∧ !P.positive i := by
  simp [prefixNeg]

theorem order_mem_prefix_support_iff {n : ℕ} (P : SignedPermutation n) (i j : Fin n) :
    P.order i ∈ (P.prefixSignedSubset j).support ↔ i ≤ j := by
  by_cases hpos : P.positive i
  · simp [SignedSubset.support, prefixSignedSubset, order_mem_prefixPos_iff,
      order_mem_prefixNeg_iff, hpos]
  · simp [SignedSubset.support, prefixSignedSubset, order_mem_prefixPos_iff,
      order_mem_prefixNeg_iff, hpos]

theorem prefix_support_mem_order_iff {n : ℕ} (P : SignedPermutation n)
    (x : Fin n) (j : Fin n) :
    x ∈ (P.prefixSignedSubset j).support ↔ P.order.symm x ≤ j := by
  simpa using
    (order_mem_prefix_support_iff P (P.order.symm x) j :
      P.order (P.order.symm x) ∈ (P.prefixSignedSubset j).support ↔
        P.order.symm x ≤ j)

theorem order_positive_eq_of_prefixChain_eq_of_prev_eq {n : ℕ}
    (P Q : SignedPermutation n) (i : Fin n)
    (hcur : Q.prefixChain i = P.prefixChain i)
    (hprev :
      ∀ j : Fin n, j.val + 1 = i.val →
        Q.prefixChain j = P.prefixChain j) :
    Q.order i = P.order i ∧ Q.positive i = P.positive i := by
  let x : Fin n := Q.order i
  have hxQ : x ∈ (Q.prefixSignedSubset i).support := by
    simpa [x, prefixChain] using
      ((order_mem_prefix_support_iff Q i i).mpr le_rfl)
  have hsupport_cur :
      (Q.prefixSignedSubset i).support = (P.prefixSignedSubset i).support := by
    simpa [prefixChain] using
      congrArg (fun X : NonzeroSignedSubset n => X.1.support) hcur
  have hxP : x ∈ (P.prefixSignedSubset i).support := by
    simpa [hsupport_cur] using hxQ
  have hle : P.order.symm x ≤ i :=
    (prefix_support_mem_order_iff P x i).mp hxP
  have hnotlt : ¬ P.order.symm x < i := by
    intro hlt
    have hi_pos : 0 < i.val := by
      have hvlt := Fin.lt_iff_val_lt_val.mp hlt
      omega
    let ipred : Fin n := ⟨i.val - 1, by omega⟩
    have hipred_val : ipred.val + 1 = i.val := by
      dsimp [ipred]
      omega
    have hlePred : P.order.symm x ≤ ipred := by
      exact Fin.le_iff_val_le_val.mpr (by
        have hvlt := Fin.lt_iff_val_lt_val.mp hlt
        dsimp [ipred]
        omega)
    have hxPprev : x ∈ (P.prefixSignedSubset ipred).support :=
      (prefix_support_mem_order_iff P x ipred).mpr hlePred
    have hsupport_prev :
        (Q.prefixSignedSubset ipred).support =
          (P.prefixSignedSubset ipred).support := by
      simpa [prefixChain] using
        congrArg (fun X : NonzeroSignedSubset n => X.1.support)
          (hprev ipred hipred_val)
    have hxQprev : x ∈ (Q.prefixSignedSubset ipred).support := by
      simpa [hsupport_prev] using hxPprev
    have hqle : i ≤ ipred := by
      simpa [x] using (prefix_support_mem_order_iff Q x ipred).mp hxQprev
    have hvle := Fin.le_iff_val_le_val.mp hqle
    dsimp [ipred] at hvle
    omega
  have hsymm : P.order.symm x = i := le_antisymm hle (le_of_not_gt hnotlt)
  have horder : Q.order i = P.order i := by
    change x = P.order i
    simpa [x] using congrArg P.order hsymm
  have hsign : Q.positive i = P.positive i := by
    by_cases hqpos : Q.positive i
    · have hxQpos : x ∈ Q.prefixPos i := by
        simpa [x, order_mem_prefixPos_iff, hqpos]
      have hpos_cur : Q.prefixPos i = P.prefixPos i := by
        simpa [prefixChain, prefixSignedSubset] using
          congrArg (fun X : NonzeroSignedSubset n => X.1.pos) hcur
      have hxPpos : P.order i ∈ P.prefixPos i := by
        simpa [x, horder, hpos_cur] using hxQpos
      have hppos : P.positive i := (order_mem_prefixPos_iff P i i).mp hxPpos |>.2
      simp [hqpos, hppos]
    · have hxQneg : x ∈ Q.prefixNeg i := by
        simpa [x, order_mem_prefixNeg_iff, hqpos]
      have hneg_cur : Q.prefixNeg i = P.prefixNeg i := by
        simpa [prefixChain, prefixSignedSubset] using
          congrArg (fun X : NonzeroSignedSubset n => X.1.neg) hcur
      have hxPneg : P.order i ∈ P.prefixNeg i := by
        simpa [x, horder, hneg_cur] using hxQneg
      have hpneg : !P.positive i := (order_mem_prefixNeg_iff P i i).mp hxPneg |>.2
      cases hp : P.positive i <;> simp [hqpos, hp] at hpneg ⊢
  exact ⟨horder, hsign⟩

theorem positive_eq_of_order_eq_of_prefixChain_eq {n : ℕ}
    (P Q : SignedPermutation n) {i p j : Fin n}
    (horder : Q.order i = P.order p) (hij : i ≤ j) (hpj : p ≤ j)
    (hprefix : Q.prefixChain j = P.prefixChain j) :
    Q.positive i = P.positive p := by
  by_cases hqpos : Q.positive i
  · have hxQpos : Q.order i ∈ Q.prefixPos j := by
      simpa [order_mem_prefixPos_iff, hij, hqpos]
    have hpos_eq : Q.prefixPos j = P.prefixPos j := by
      simpa [prefixChain, prefixSignedSubset] using
        congrArg (fun X : NonzeroSignedSubset n => X.1.pos) hprefix
    have hxPpos : P.order p ∈ P.prefixPos j := by
      simpa [horder, hpos_eq] using hxQpos
    have hppos : P.positive p := (order_mem_prefixPos_iff P p j).mp hxPpos |>.2
    simp [hqpos, hppos]
  · have hxQneg : Q.order i ∈ Q.prefixNeg j := by
      simpa [order_mem_prefixNeg_iff, hij, hqpos]
    have hneg_eq : Q.prefixNeg j = P.prefixNeg j := by
      simpa [prefixChain, prefixSignedSubset] using
        congrArg (fun X : NonzeroSignedSubset n => X.1.neg) hprefix
    have hxPneg : P.order p ∈ P.prefixNeg j := by
      simpa [horder, hneg_eq] using hxQneg
    have hpneg : !P.positive p := (order_mem_prefixNeg_iff P p j).mp hxPneg |>.2
    cases hp : P.positive p <;> simp [hqpos, hp] at hpneg ⊢

theorem prefixPos_reindexPositions_of_symm_le_iff {n : ℕ}
    (P : SignedPermutation n) (τ : Equiv.Perm (Fin n)) (i : Fin n)
    (hτ : ∀ k : Fin n, τ.symm k ≤ i ↔ k ≤ i) :
    (P.reindexPositions τ).prefixPos i = P.prefixPos i := by
  ext x
  simp [prefixPos, reindexPositions, hτ (P.order.symm x)]

theorem prefixNeg_reindexPositions_of_symm_le_iff {n : ℕ}
    (P : SignedPermutation n) (τ : Equiv.Perm (Fin n)) (i : Fin n)
    (hτ : ∀ k : Fin n, τ.symm k ≤ i ↔ k ≤ i) :
    (P.reindexPositions τ).prefixNeg i = P.prefixNeg i := by
  ext x
  simp [prefixNeg, reindexPositions, hτ (P.order.symm x)]

theorem prefixSignedSubset_reindexPositions_of_symm_le_iff {n : ℕ}
    (P : SignedPermutation n) (τ : Equiv.Perm (Fin n)) (i : Fin n)
    (hτ : ∀ k : Fin n, τ.symm k ≤ i ↔ k ≤ i) :
    (P.reindexPositions τ).prefixSignedSubset i = P.prefixSignedSubset i := by
  cases P with
  | mk order positive =>
      simp [prefixSignedSubset, prefixPos, prefixNeg, reindexPositions, hτ]

theorem prefixChain_reindexPositions_of_symm_le_iff {n : ℕ}
    (P : SignedPermutation n) (τ : Equiv.Perm (Fin n)) (i : Fin n)
    (hτ : ∀ k : Fin n, τ.symm k ≤ i ↔ k ≤ i) :
    (P.reindexPositions τ).prefixChain i = P.prefixChain i := by
  apply Subtype.ext
  exact P.prefixSignedSubset_reindexPositions_of_symm_le_iff τ i hτ

theorem swap_adjacent_symm_le_iff_of_ne_left {n : ℕ} {a b i : Fin n}
    (hab : b.val = a.val + 1) (hi : i ≠ a) :
    ∀ k : Fin n, (Equiv.swap a b).symm k ≤ i ↔ k ≤ i := by
  have habne : a ≠ b := by
    intro h
    have hval := congrArg Fin.val h
    omega
  intro k
  by_cases hka : k = a
  · subst k
    have hswap : (Equiv.swap a b).symm a = b := by
      simp
    rw [hswap]
    constructor
    · intro h
      exact le_trans (Fin.le_iff_val_le_val.mpr (by omega)) h
    · intro h
      exact Fin.le_iff_val_le_val.mpr (by
        have hle : a.val ≤ i.val := Fin.le_iff_val_le_val.mp h
        have hne : i.val ≠ a.val := by
          intro hval
          exact hi (Fin.ext hval)
        omega)
  · by_cases hkb : k = b
    · subst k
      have hswap : (Equiv.swap a b).symm b = a := by
        simp
      rw [hswap]
      constructor
      · intro h
        exact Fin.le_iff_val_le_val.mpr (by
          have hle : a.val ≤ i.val := Fin.le_iff_val_le_val.mp h
          have hne : i.val ≠ a.val := by
            intro hval
            exact hi (Fin.ext hval)
          omega)
      · intro h
        exact le_trans (Fin.le_iff_val_le_val.mpr (by omega)) h
    · have hswap : (Equiv.swap a b).symm k = k := by
        simp [Equiv.swap_apply_def, hka, hkb]
      rw [hswap]

theorem prefixChain_reindexPositions_swap_adjacent_of_ne_left {n : ℕ}
    (P : SignedPermutation n) {a b i : Fin n}
    (hab : b.val = a.val + 1) (hi : i ≠ a) :
    (P.reindexPositions (Equiv.swap a b)).prefixChain i = P.prefixChain i :=
  P.prefixChain_reindexPositions_of_symm_le_iff (Equiv.swap a b) i
    (swap_adjacent_symm_le_iff_of_ne_left hab hi)

theorem prefixChain_reindexPositions_swap_gap_succAbove {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n)
    (i : Fin n) :
    (P.reindexPositions (Equiv.swap gap (gapNext gap hgap))).prefixChain (gap.succAbove i) =
      P.prefixChain (gap.succAbove i) := by
  apply P.prefixChain_reindexPositions_swap_adjacent_of_ne_left
  · exact gapNext_val gap hgap
  · exact Fin.succAbove_ne gap i

theorem prefixPos_flipSignAt_of_lt {n : ℕ}
    (P : SignedPermutation n) {i j : Fin n} (hij : i < j) :
    (P.flipSignAt j).prefixPos i = P.prefixPos i := by
  ext x
  by_cases hle : P.order.symm x ≤ i
  · have hne : P.order.symm x ≠ j := by
      intro hxj
      have hji : j ≤ i := by
        simpa [hxj] using hle
      exact (not_le_of_gt hij) hji
    simp [prefixPos, flipSignAt, hle, hne]
  · simp [prefixPos, flipSignAt, hle]

theorem prefixNeg_flipSignAt_of_lt {n : ℕ}
    (P : SignedPermutation n) {i j : Fin n} (hij : i < j) :
    (P.flipSignAt j).prefixNeg i = P.prefixNeg i := by
  ext x
  by_cases hle : P.order.symm x ≤ i
  · have hne : P.order.symm x ≠ j := by
      intro hxj
      have hji : j ≤ i := by
        simpa [hxj] using hle
      exact (not_le_of_gt hij) hji
    simp [prefixNeg, flipSignAt, hle, hne]
  · simp [prefixNeg, flipSignAt, hle]

theorem prefixSignedSubset_flipSignAt_of_lt {n : ℕ}
    (P : SignedPermutation n) {i j : Fin n} (hij : i < j) :
    (P.flipSignAt j).prefixSignedSubset i = P.prefixSignedSubset i := by
  exact signedSubset_ext_pos_neg
    (P.prefixPos_flipSignAt_of_lt hij)
    (P.prefixNeg_flipSignAt_of_lt hij)

theorem prefixChain_flipSignAt_of_lt {n : ℕ}
    (P : SignedPermutation n) {i j : Fin n} (hij : i < j) :
    (P.flipSignAt j).prefixChain i = P.prefixChain i := by
  apply Subtype.ext
  exact P.prefixSignedSubset_flipSignAt_of_lt hij

theorem prefixChain_flipSignAt_last_succAbove {n : ℕ}
    (P : SignedPermutation (n + 1)) (i : Fin n) :
    (P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove i) =
      P.prefixChain ((Fin.last n).succAbove i) := by
  simpa [Fin.succAbove_last] using
    (P.prefixChain_flipSignAt_of_lt (j := Fin.last n) (Fin.castSucc_lt_last i))

end SignedPermutation

/-- Maximal chains lying in the upper hemisphere. -/
def UpperPrefixChain {n : ℕ} (P : SignedPermutation (n + 1)) : Prop :=
  ∀ i : Fin (n + 1), UpperHemisphere (P.prefixChain i)

/-- A represented codimension-one ridge of the upper hemisphere is boundary
exactly when the deleted rank is the top rank and the last coordinate has not
appeared in the retained punctured flag. -/
def RepresentedUpperRidgeBoundary {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) : Prop :=
  gap = Fin.last n ∧ P.order.symm (Fin.last n) = Fin.last n

noncomputable instance representedUpperRidgeBoundary_decidable {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    Decidable (RepresentedUpperRidgeBoundary P gap) := by
  classical
  exact inferInstance

/-- The second local top coface of a represented full-rank punctured flag in
the cross-polytope order complex: swap adjacent ranks when the missing rank is
internal, and flip the final inserted sign when the missing rank is top. -/
noncomputable def representedRidgePartner {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    SignedPermutation (n + 1) :=
  if hgap : gap.val < n then
    P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap))
  else
    P.flipSignAt (Fin.last n)

theorem representedRidgePartner_ne_self {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    representedRidgePartner P gap ≠ P := by
  unfold representedRidgePartner
  by_cases hgap : gap.val < n
  · simpa [hgap] using SignedPermutation.reindexPositions_swap_gap_ne_self P gap hgap
  · simpa [hgap] using SignedPermutation.flipSignAt_ne_self P (Fin.last n)

theorem representedRidgePartner_deletion_eq {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (i : Fin n) :
    (representedRidgePartner P gap).prefixChain (gap.succAbove i) =
      P.prefixChain (gap.succAbove i) := by
  unfold representedRidgePartner
  by_cases hgap : gap.val < n
  · simpa [hgap] using
      P.prefixChain_reindexPositions_swap_gap_succAbove gap hgap i
  · have hlast : gap = Fin.last n := by
      apply Fin.ext
      have hle : gap.val ≤ n := Nat.lt_succ_iff.mp gap.isLt
      simp [Fin.last]
      omega
    subst gap
    simpa [hgap] using P.prefixChain_flipSignAt_last_succAbove i

theorem deletion_gap_eq_of_prefixChain_eq {d : ℕ} (hd : 0 < d)
    {P Q : SignedPermutation (d + 1)} {gap eta : Fin (d + 1)}
    (hdel :
      ∀ a : Fin d,
        Q.prefixChain (eta.succAbove a) =
          P.prefixChain (gap.succAbove a)) :
    eta = gap := by
  apply Fin.succAbove_left_injective
  funext a
  apply Fin.ext
  have hcard :=
    congrArg (fun X : NonzeroSignedSubset (d + 1) => X.1.card) (hdel a)
  have hcard' :
      (eta.succAbove a).val + 1 = (gap.succAbove a).val + 1 := by
    simpa [SignedPermutation.prefixChain_card] using hcard
  omega

theorem eq_or_flipSignAt_last_of_deletion_eq {n : ℕ}
    (P Q : SignedPermutation (n + 1))
    (hdel :
      ∀ a : Fin n,
        Q.prefixChain ((Fin.last n).succAbove a) =
          P.prefixChain ((Fin.last n).succAbove a)) :
    Q = P ∨ Q = P.flipSignAt (Fin.last n) := by
  have hprefix_ne_last :
      ∀ i : Fin (n + 1), i ≠ Fin.last n → Q.prefixChain i = P.prefixChain i := by
    intro i hi
    rcases Fin.exists_succAbove_eq hi with ⟨a, ha⟩
    simpa [← ha] using hdel a
  have hatom_ne_last :
      ∀ i : Fin (n + 1), i ≠ Fin.last n →
        Q.order i = P.order i ∧ Q.positive i = P.positive i := by
    intro i hi
    apply order_positive_eq_of_prefixChain_eq_of_prev_eq P Q i
    · exact hprefix_ne_last i hi
    · intro j hj
      apply hprefix_ne_last
      intro hjlast
      have hivallast : i.val = n + 1 := by
        rw [← hj, hjlast]
        simp [Fin.last]
      exact Nat.ne_of_lt i.isLt hivallast
  have horder_last : Q.order (Fin.last n) = P.order (Fin.last n) := by
    let k : Fin (n + 1) := P.order.symm (Q.order (Fin.last n))
    by_cases hk : k = Fin.last n
    · change Q.order (Fin.last n) = P.order (Fin.last n)
      calc
        Q.order (Fin.last n) = P.order k := by
          dsimp [k]
          simp
        _ = P.order (Fin.last n) := congrArg P.order hk
    · have hkorder : Q.order k = P.order k := (hatom_ne_last k hk).1
      have hPk : P.order k = Q.order (Fin.last n) := by
        dsimp [k]
        simp
      have hQeq : Q.order k = Q.order (Fin.last n) := hkorder.trans hPk
      exact False.elim (hk (Q.order.injective hQeq))
  by_cases hlastSign : Q.positive (Fin.last n) = P.positive (Fin.last n)
  · left
    apply SignedPermutation.ext_order_positive
    · apply Equiv.ext
      intro i
      by_cases hi : i = Fin.last n
      · subst i
        exact horder_last
      · exact (hatom_ne_last i hi).1
    · funext i
      by_cases hi : i = Fin.last n
      · subst i
        exact hlastSign
      · exact (hatom_ne_last i hi).2
  · right
    apply SignedPermutation.ext_order_positive
    · apply Equiv.ext
      intro i
      by_cases hi : i = Fin.last n
      · subst i
        exact horder_last
      · exact (hatom_ne_last i hi).1
    · funext i
      by_cases hi : i = Fin.last n
      · subst i
        cases hq : Q.positive (Fin.last n) <;>
          cases hp : P.positive (Fin.last n) <;>
            simp [flipSignAt, hq, hp] at hlastSign ⊢
      · simp [flipSignAt, hi, (hatom_ne_last i hi).2]

theorem eq_or_reindex_swap_of_internal_deletion_eq {n : ℕ}
    (P Q : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n)
    (hdel :
      ∀ a : Fin n,
        Q.prefixChain (gap.succAbove a) =
          P.prefixChain (gap.succAbove a)) :
    Q = P ∨
      Q = P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap)) := by
  let next : Fin (n + 1) := SignedPermutation.gapNext gap hgap
  have hnext_val : next.val = gap.val + 1 := rfl
  have hnext_ne_gap : next ≠ gap := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [next, SignedPermutation.gapNext] at hval
    omega
  have hgap_le_next : gap ≤ next := by
    exact Fin.le_iff_val_le_val.mpr (by dsimp [next, SignedPermutation.gapNext]; omega)
  have hprefix_ne_gap :
      ∀ i : Fin (n + 1), i ≠ gap → Q.prefixChain i = P.prefixChain i := by
    intro i hi
    rcases Fin.exists_succAbove_eq hi with ⟨a, ha⟩
    simpa [← ha] using hdel a
  have hprefix_next : Q.prefixChain next = P.prefixChain next :=
    hprefix_ne_gap next hnext_ne_gap
  have hatom_fixed :
      ∀ i : Fin (n + 1), i ≠ gap → i ≠ next →
        Q.order i = P.order i ∧ Q.positive i = P.positive i := by
    intro i hig hinext
    apply order_positive_eq_of_prefixChain_eq_of_prev_eq P Q i
    · exact hprefix_ne_gap i hig
    · intro j hj
      apply hprefix_ne_gap
      intro hjgap
      apply hinext
      apply Fin.ext
      rw [← hj, hjgap]
      dsimp [next, SignedPermutation.gapNext]
  let xgap : Fin (n + 1) := Q.order gap
  have hxQnext : xgap ∈ (Q.prefixSignedSubset next).support := by
    exact (prefix_support_mem_order_iff Q xgap next).mpr (by
      change Q.order.symm (Q.order gap) ≤ next
      simpa [xgap] using hgap_le_next)
  have hsupport_next :
      (Q.prefixSignedSubset next).support = (P.prefixSignedSubset next).support := by
    simpa [prefixChain] using
      congrArg (fun X : NonzeroSignedSubset (n + 1) => X.1.support) hprefix_next
  have hxPnext : xgap ∈ (P.prefixSignedSubset next).support := by
    simpa [hsupport_next] using hxQnext
  have hPgap_le_next : P.order.symm xgap ≤ next :=
    (prefix_support_mem_order_iff P xgap next).mp hxPnext
  have hnot_lt_gap : ¬ P.order.symm xgap < gap := by
    intro hlt
    let j : Fin (n + 1) := P.order.symm xgap
    have hjne : j ≠ gap := by
      intro hj
      exact (ne_of_lt hlt) hj
    have hxPj : xgap ∈ (P.prefixSignedSubset j).support := by
      exact (prefix_support_mem_order_iff P xgap j).mpr (by simp [j])
    have hsupport_j :
        (Q.prefixSignedSubset j).support = (P.prefixSignedSubset j).support := by
      simpa [prefixChain] using
        congrArg (fun X : NonzeroSignedSubset (n + 1) => X.1.support)
          (hprefix_ne_gap j hjne)
    have hxQj : xgap ∈ (Q.prefixSignedSubset j).support := by
      simpa [hsupport_j] using hxPj
    have hqle : gap ≤ j := by
      simpa [xgap, j] using (prefix_support_mem_order_iff Q xgap j).mp hxQj
    exact not_lt_of_ge hqle hlt
  have hgap_le_Pgap : gap ≤ P.order.symm xgap := le_of_not_gt hnot_lt_gap
  have hPgap_cases :
      P.order.symm xgap = gap ∨ P.order.symm xgap = next := by
    have hge := Fin.le_iff_val_le_val.mp hgap_le_Pgap
    have hle := Fin.le_iff_val_le_val.mp hPgap_le_next
    have hnextv : next.val = gap.val + 1 := by
      dsimp [next, SignedPermutation.gapNext]
    by_cases hv : (P.order.symm xgap).val = gap.val
    · left
      exact Fin.ext hv
    · right
      apply Fin.ext
      omega
  have horder_gap_cases : Q.order gap = P.order gap ∨ Q.order gap = P.order next := by
    rcases hPgap_cases with hsymm | hsymm
    · left
      change xgap = P.order gap
      calc
        xgap = P.order (P.order.symm xgap) := by simp [xgap]
        _ = P.order gap := congrArg P.order hsymm
    · right
      change xgap = P.order next
      calc
        xgap = P.order (P.order.symm xgap) := by simp [xgap]
        _ = P.order next := congrArg P.order hsymm
  rcases horder_gap_cases with hgapOrder | hgapOrder
  · have hnextOrder : Q.order next = P.order next := by
      let k : Fin (n + 1) := P.order.symm (Q.order next)
      by_cases hknext : k = next
      · calc
          Q.order next = P.order k := by dsimp [k]; simp
          _ = P.order next := congrArg P.order hknext
      · by_cases hkgap : k = gap
        · have hPk : P.order k = Q.order next := by dsimp [k]; simp
          have hQeq : Q.order gap = Q.order next := by
            calc
              Q.order gap = P.order gap := hgapOrder
              _ = P.order k := by rw [hkgap]
              _ = Q.order next := hPk
          exact False.elim (hnext_ne_gap.symm (Q.order.injective hQeq))
        · have hkfixed : Q.order k = P.order k := (hatom_fixed k hkgap hknext).1
          have hPk : P.order k = Q.order next := by dsimp [k]; simp
          have hQeq : Q.order k = Q.order next := hkfixed.trans hPk
          exact False.elim (hknext (Q.order.injective hQeq))
    have hgapSign : Q.positive gap = P.positive gap :=
      positive_eq_of_order_eq_of_prefixChain_eq P Q hgapOrder hgap_le_next hgap_le_next
        hprefix_next
    have hnextSign : Q.positive next = P.positive next :=
      positive_eq_of_order_eq_of_prefixChain_eq P Q hnextOrder le_rfl le_rfl hprefix_next
    left
    apply SignedPermutation.ext_order_positive
    · apply Equiv.ext
      intro i
      by_cases hig : i = gap
      · subst i
        exact hgapOrder
      · by_cases hin : i = next
        · subst i
          exact hnextOrder
        · exact (hatom_fixed i hig hin).1
    · funext i
      by_cases hig : i = gap
      · subst i
        exact hgapSign
      · by_cases hin : i = next
        · subst i
          exact hnextSign
        · exact (hatom_fixed i hig hin).2
  · have hnextOrder : Q.order next = P.order gap := by
      let k : Fin (n + 1) := P.order.symm (Q.order next)
      by_cases hkgap : k = gap
      · calc
          Q.order next = P.order k := by dsimp [k]; simp
          _ = P.order gap := congrArg P.order hkgap
      · by_cases hknext : k = next
        · have hPk : P.order k = Q.order next := by dsimp [k]; simp
          have hQeq : Q.order gap = Q.order next := by
            calc
              Q.order gap = P.order next := hgapOrder
              _ = P.order k := by rw [hknext]
              _ = Q.order next := hPk
          exact False.elim (hnext_ne_gap (Q.order.injective hQeq).symm)
        · have hkfixed : Q.order k = P.order k := (hatom_fixed k hkgap hknext).1
          have hPk : P.order k = Q.order next := by dsimp [k]; simp
          have hQeq : Q.order k = Q.order next := hkfixed.trans hPk
          exact False.elim (hknext (Q.order.injective hQeq))
    have hgapSign : Q.positive gap = P.positive next :=
      positive_eq_of_order_eq_of_prefixChain_eq P Q hgapOrder hgap_le_next le_rfl
        hprefix_next
    have hnextSign : Q.positive next = P.positive gap :=
      positive_eq_of_order_eq_of_prefixChain_eq P Q hnextOrder le_rfl hgap_le_next
        hprefix_next
    right
    apply SignedPermutation.ext_order_positive
    · apply Equiv.ext
      intro i
      by_cases hig : i = gap
      · subst i
        simp [SignedPermutation.reindexPositions, hgapOrder, next]
      · by_cases hin : i = next
        · subst i
          simp [SignedPermutation.reindexPositions, hnextOrder, next]
        · have hswap : Equiv.swap gap next i = i := by
            simp [Equiv.swap_apply_def, hig, hin]
          rw [(hatom_fixed i hig hin).1]
          change P.order i = P.order ((Equiv.swap gap next) i)
          rw [hswap]
    · funext i
      by_cases hig : i = gap
      · subst i
        simp [SignedPermutation.reindexPositions, hgapSign, next]
      · by_cases hin : i = next
        · subst i
          simp [SignedPermutation.reindexPositions, hnextSign, next]
        · have hswap : Equiv.swap gap next i = i := by
            simp [Equiv.swap_apply_def, hig, hin]
          rw [(hatom_fixed i hig hin).2]
          change P.positive i = P.positive ((Equiv.swap gap next) i)
          rw [hswap]

theorem eq_or_representedRidgePartner_of_deletion_eq {n : ℕ}
    (P Q : SignedPermutation (n + 1)) (gap : Fin (n + 1))
    (hdel :
      ∀ a : Fin n,
        Q.prefixChain (gap.succAbove a) =
          P.prefixChain (gap.succAbove a)) :
    Q = P ∨ Q = representedRidgePartner P gap := by
  unfold representedRidgePartner
  by_cases hgap : gap.val < n
  · rcases eq_or_reindex_swap_of_internal_deletion_eq P Q gap hgap hdel with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [hgap] using h)
  · have hlast : gap = Fin.last n := by
      apply Fin.ext
      have hle : gap.val ≤ n := Nat.lt_succ_iff.mp gap.isLt
      simp [Fin.last]
      omega
    subst gap
    rcases eq_or_flipSignAt_last_of_deletion_eq P Q hdel with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [hgap] using h)

theorem reindex_swap_gap_prefix_le_next {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n) :
    SignedSubset.Le
      ((P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap))).prefixChain gap).1
      (P.prefixChain (SignedPermutation.gapNext gap hgap)).1 := by
  let next : Fin (n + 1) := SignedPermutation.gapNext gap hgap
  have hgap_le_next : gap ≤ next := by
    exact Fin.le_iff_val_le_val.mpr (by dsimp [next, SignedPermutation.gapNext]; omega)
  have hswap_le :
      ∀ k : Fin (n + 1), (Equiv.swap gap next) k ≤ gap → k ≤ next := by
    intro k hk
    by_cases hkg : k = gap
    · subst k
      exact hgap_le_next
    · by_cases hkn : k = next
      · subst k
        exact le_rfl
      · have hswap : (Equiv.swap gap next) k = k := by
          simp [Equiv.swap_apply_def, hkg, hkn]
        exact le_trans (by simpa [hswap] using hk) hgap_le_next
  constructor
  · intro x hx
    simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
      SignedPermutation.prefixPos, SignedPermutation.reindexPositions, next] at hx ⊢
    exact ⟨hswap_le (P.order.symm x) hx.1, hx.2⟩
  · intro x hx
    simp [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
      SignedPermutation.prefixNeg, SignedPermutation.reindexPositions, next] at hx ⊢
    exact ⟨hswap_le (P.order.symm x) hx.1, hx.2⟩

theorem flipSignAt_last_upperPrefixChain_of_not_boundary {n : ℕ}
    (P : SignedPermutation (n + 1)) (hP : UpperPrefixChain P)
    (hnot : ¬ RepresentedUpperRidgeBoundary P (Fin.last n)) :
    UpperPrefixChain (P.flipSignAt (Fin.last n)) := by
  have hcoord : P.order.symm (Fin.last n) ≠ Fin.last n := by
    intro hcoord
    exact hnot ⟨rfl, hcoord⟩
  intro i
  by_cases hi : i = Fin.last n
  · subst i
    intro hneg
    exact hP (Fin.last n) (by
      simpa [UpperHemisphere, SignedPermutation.prefixChain,
        SignedPermutation.prefixSignedSubset, SignedPermutation.prefixNeg,
        SignedPermutation.flipSignAt, hcoord] using hneg)
  · have hlt : i < Fin.last n := Fin.lt_last_iff_ne_last.mpr hi
    have heq :
        (P.flipSignAt (Fin.last n)).prefixChain i = P.prefixChain i :=
      P.prefixChain_flipSignAt_of_lt (j := Fin.last n) hlt
    simpa [heq] using hP i

theorem flipSignAt_last_not_upperPrefixChain_of_boundary {n : ℕ}
    (P : SignedPermutation (n + 1)) (hP : UpperPrefixChain P)
    (hcoord : P.order.symm (Fin.last n) = Fin.last n) :
    ¬ UpperPrefixChain (P.flipSignAt (Fin.last n)) := by
  have hposLast : P.positive (Fin.last n) := by
    by_contra hpos
    exact hP (Fin.last n) (by
      simpa [UpperHemisphere, SignedPermutation.prefixChain,
        SignedPermutation.prefixSignedSubset, SignedPermutation.prefixNeg, hcoord] using hpos)
  intro hflip
  exact hflip (Fin.last n) (by
    simp [UpperHemisphere, SignedPermutation.prefixChain,
      SignedPermutation.prefixSignedSubset, SignedPermutation.prefixNeg,
      SignedPermutation.flipSignAt, hcoord, hposLast])

theorem representedRidgePartner_upperPrefixChain {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1))
    (hP : UpperPrefixChain P) (hnot : ¬ RepresentedUpperRidgeBoundary P gap) :
    UpperPrefixChain (representedRidgePartner P gap) := by
  unfold representedRidgePartner
  by_cases hgap : gap.val < n
  · intro i
    by_cases hi : i = gap
    · subst i
      simpa [hgap] using
        upperHemisphere_of_le (reindex_swap_gap_prefix_le_next P gap hgap)
          (hP (SignedPermutation.gapNext gap hgap))
    · have heq :
          (P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap))).prefixChain i =
            P.prefixChain i := by
        apply P.prefixChain_reindexPositions_swap_adjacent_of_ne_left
        · exact SignedPermutation.gapNext_val gap hgap
        · exact hi
      simpa [hgap, heq] using hP i
  · have hlast : gap = Fin.last n := by
      apply Fin.ext
      have hle : gap.val ≤ n := Nat.lt_succ_iff.mp gap.isLt
      simp [Fin.last]
      omega
    subst gap
    simpa [hgap] using flipSignAt_last_upperPrefixChain_of_not_boundary P hP hnot

theorem representedRidgePartner_not_upperPrefixChain_of_boundary {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1))
    (hP : UpperPrefixChain P) (hb : RepresentedUpperRidgeBoundary P gap) :
    ¬ UpperPrefixChain (representedRidgePartner P gap) := by
  rcases hb with ⟨hgapEq, hcoord⟩
  subst gap
  unfold representedRidgePartner
  have hgapLast : ¬ (Fin.last n).val < n := by
    simp [Fin.last]
  simpa [hgapLast] using flipSignAt_last_not_upperPrefixChain_of_boundary P hP hcoord

theorem last_mem_prefixPos_of_upper_of_order_le {n : ℕ}
    (P : SignedPermutation (n + 1)) (i : Fin (n + 1))
    (hupper : UpperHemisphere (P.prefixChain i))
    (hle : P.order.symm (Fin.last n) ≤ i) :
    Fin.last n ∈ (P.prefixChain i).1.pos := by
  by_cases hpos : P.positive (P.order.symm (Fin.last n))
  · simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
      SignedPermutation.prefixPos, hle, hpos]
  · have hneg : Fin.last n ∈ (P.prefixChain i).1.neg := by
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, hle, hpos]
    exact False.elim (hupper hneg)

/-- The local upper cofaces of a represented rho.  Boundary ridges retain only
the upper coface; interior ridges retain both local cofaces. -/
noncomputable def representedUpperRidgeLocalCofaces {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    Finset (SignedPermutation (n + 1)) :=
  by
    classical
    exact
      if RepresentedUpperRidgeBoundary P gap then
        {P}
      else
        {P, representedRidgePartner P gap}

theorem representedUpperRidgeLocalCofaces_card {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    (representedUpperRidgeLocalCofaces P gap).card =
      if RepresentedUpperRidgeBoundary P gap then 1 else 2 := by
  classical
  by_cases hb : RepresentedUpperRidgeBoundary P gap
  · rw [representedUpperRidgeLocalCofaces, if_pos hb, if_pos hb]
    simp
  · rw [representedUpperRidgeLocalCofaces, if_neg hb, if_neg hb]
    exact Finset.card_pair (representedRidgePartner_ne_self P gap).symm

theorem representedUpperRidgeLocalCofaces_nonempty {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    (representedUpperRidgeLocalCofaces P gap).Nonempty := by
  classical
  unfold representedUpperRidgeLocalCofaces
  by_cases hb : RepresentedUpperRidgeBoundary P gap
  · rw [if_pos hb]
    simp
  · rw [if_neg hb]
    simp

/-! ## Actual upper-hemisphere label-set-`A` graph -/

noncomputable instance signedSubset_fintype (n : ℕ) : Fintype (SignedSubset n) := by
  classical
  refine Fintype.ofInjective (fun X : SignedSubset n => (X.pos, X.neg)) ?_
  intro X Y h
  exact signedSubset_ext_pos_neg (congrArg Prod.fst h) (congrArg Prod.snd h)

noncomputable instance nonzeroSignedSubset_fintype (n : ℕ) :
    Fintype (NonzeroSignedSubset n) := by
  classical
  refine Fintype.ofInjective
    (fun X : NonzeroSignedSubset n => (X.1.pos, X.1.neg)) ?_
  intro X Y h
  apply Subtype.ext
  exact signedSubset_ext_pos_neg (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- A concrete ordered codimension-one ridge in the upper hemisphere whose
retained labels are exactly `A`.  The ridge is an actual ordered chain of
vertices; the existential signed-permutation/gap field only certifies that it
is a genuine punctured maximal chain. -/
def ActualHemisphereARidge {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :=
  {rho : Fin d → NonzeroSignedSubset (d + 1) //
    (∀ a : Fin d, UpperHemisphere (rho a)) ∧
      (∃ P : SignedPermutation (d + 1), UpperPrefixChain P ∧
        ∃ gap : Fin (d + 1), ∀ a : Fin d,
          rho a = P.prefixChain (gap.succAbove a)) ∧
      ∀ a : Fin d, ∃ t : Fin d, label (rho t) = alternatingLabel a}

noncomputable instance actualHemisphereARidge_fintype {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :
    Fintype (ActualHemisphereARidge label) := by
  classical
  dsimp [ActualHemisphereARidge]
  infer_instance

/-- Upper-hemisphere maximal chains which contain at least one label-set-`A`
ridge. -/
def ActualHemisphereAChain {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :=
  {P : SignedPermutation (d + 1) //
    UpperPrefixChain P ∧
      ∃ gap : Fin (d + 1), ∀ a : Fin d,
        ∃ t : Fin d, label (P.prefixChain (gap.succAbove t)) = alternatingLabel a}

noncomputable instance actualHemisphereAChain_fintype {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :
    Fintype (ActualHemisphereAChain label) := by
  classical
  dsimp [ActualHemisphereAChain]
  infer_instance

/-- Incidence between an actual ridge and an upper maximal chain: deleting one
rank of the chain gives exactly the ordered ridge. -/
def actualHemisphereAEdge {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label) (sigma : ActualHemisphereAChain label) : Prop :=
  ∃ gap : Fin (d + 1), ∀ a : Fin d,
    rho.1 a = sigma.1.prefixChain (gap.succAbove a)

noncomputable instance actualHemisphereAEdge_decidable {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d} :
    DecidableRel (actualHemisphereAEdge (label := label)) := by
  classical
  exact inferInstance

/-- Boundary ridges are exactly those whose retained vertices all lie in the
equator. -/
def actualHemisphereABoundary {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label) : Prop :=
  ∀ a : Fin d, Equator (rho.1 a)

noncomputable instance actualHemisphereABoundary_decidable {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d} :
    DecidablePred (actualHemisphereABoundary (label := label)) := by
  classical
  exact inferInstance

/-- Unordered maximal label-set-`A` objects on the equator, expressed in the
same data language as `ActualHemisphereARidge`: the vertices are transported
through `equatorEquiv`, and the maximal-equator witness is a boundary punctured
flag in the upper hemisphere. -/
def EquatorActualARidge {d : ℕ}
    (label : NonzeroSignedSubset d → SignedLabel d) :=
  {rho : Fin d → NonzeroSignedSubset d //
    (∃ P : SignedPermutation (d + 1), UpperPrefixChain P ∧
      RepresentedUpperRidgeBoundary P (Fin.last d) ∧
        ∀ a : Fin d,
          equatorEmbed (rho a) = P.prefixChain ((Fin.last d).succAbove a)) ∧
      ∀ a : Fin d, ∃ t : Fin d, label (rho t) = alternatingLabel a}

noncomputable instance equatorActualARidge_fintype {d : ℕ}
    (label : NonzeroSignedSubset d → SignedLabel d) :
    Fintype (EquatorActualARidge label) := by
  classical
  dsimp [EquatorActualARidge]
  infer_instance

theorem actualHemisphereABoundary_iff_represented {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label)
    (P : SignedPermutation (d + 1)) (hP : UpperPrefixChain P) (gap : Fin (d + 1))
    (hrho : ∀ a : Fin d, rho.1 a = P.prefixChain (gap.succAbove a)) :
    actualHemisphereABoundary rho ↔ RepresentedUpperRidgeBoundary P gap := by
  constructor
  · intro hb
    have hgap_last : gap = Fin.last d := by
      by_contra hne
      have hlast_ne_gap : Fin.last d ≠ gap := by
        intro h
        exact hne h.symm
      rcases Fin.exists_succAbove_eq hlast_ne_gap with ⟨a, ha⟩
      have hposTop :
          Fin.last d ∈ (P.prefixChain (Fin.last d)).1.pos :=
        last_mem_prefixPos_of_upper_of_order_le P (Fin.last d) (hP (Fin.last d))
          (Fin.le_last _)
      exact (hb a).1 (by
        rw [hrho a]
        simpa [← ha] using hposTop)
    subst gap
    have hcoord : P.order.symm (Fin.last d) = Fin.last d := by
      by_contra hcoord
      rcases Fin.exists_succAbove_eq hcoord with ⟨a, ha⟩
      have hpos :
          Fin.last d ∈ (P.prefixChain (P.order.symm (Fin.last d))).1.pos :=
        last_mem_prefixPos_of_upper_of_order_le P (P.order.symm (Fin.last d))
          (hP (P.order.symm (Fin.last d))) le_rfl
      exact (hb a).1 (by
        rw [hrho a]
        simpa [← ha] using hpos)
    exact ⟨rfl, hcoord⟩
  · rintro ⟨hgap, hcoord⟩ a
    subst gap
    constructor
    · intro hpos
      rw [hrho a] at hpos
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixPos, hcoord] using hpos
    · intro hneg
      rw [hrho a] at hneg
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, hcoord] using hneg

noncomputable def equatorBoundaryARidgeEquiv {d : ℕ}
    (label : NonzeroSignedSubset (d + 1) → SignedLabel d) :
    {rho : ActualHemisphereARidge label // actualHemisphereABoundary rho} ≃
      EquatorActualARidge (equatorRestrictedLabel label) where
  toFun rho := by
    classical
    let dropped : Fin d → NonzeroSignedSubset d :=
      fun a => (equatorEquiv d).symm ⟨rho.1.1 a, rho.2 a⟩
    have hrepr :
        ∃ P : SignedPermutation (d + 1), UpperPrefixChain P ∧
          RepresentedUpperRidgeBoundary P (Fin.last d) ∧
            ∀ a : Fin d,
              equatorEmbed (dropped a) =
                P.prefixChain ((Fin.last d).succAbove a) := by
      rcases rho.1.2.2.1 with ⟨P, hP, gap, hrho⟩
      have hb := (actualHemisphereABoundary_iff_represented rho.1 P hP gap hrho).mp rho.2
      rcases hb with ⟨hgap, hcoord⟩
      subst gap
      refine ⟨P, hP, ⟨rfl, hcoord⟩, ?_⟩
      intro a
      calc
        equatorEmbed (dropped a) = rho.1.1 a := by
          dsimp [dropped, equatorEquiv]
          exact equatorEmbed_equatorDrop (rho.1.1 a) (rho.2 a)
        _ = P.prefixChain ((Fin.last d).succAbove a) := hrho a
    refine ⟨dropped, hrepr, ?_⟩
    intro a
    rcases rho.1.2.2.2 a with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    dsimp [dropped, equatorRestrictedLabel, equatorEquiv]
    simpa [equatorEmbed_equatorDrop (rho.1.1 t) (rho.2 t)] using ht
  invFun rho := by
    classical
    let lifted : Fin d → NonzeroSignedSubset (d + 1) := fun a => equatorEmbed (rho.1 a)
    have hupper : ∀ a : Fin d, UpperHemisphere (lifted a) := by
      intro a
      exact equator_subset_upperHemisphere (equatorEmbed_mem_equator (rho.1 a))
    let hactual : ActualHemisphereARidge label :=
      ⟨lifted, by
        refine ⟨hupper, ?_, ?_⟩
        · rcases rho.2.1 with ⟨P, hP, _hb, hrepr⟩
          exact ⟨P, hP, ⟨Fin.last d, hrepr⟩⟩
        · intro a
          rcases rho.2.2 a with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          dsimp [lifted, equatorRestrictedLabel, equatorEquiv] at ht ⊢
          simpa using ht⟩
    refine ⟨hactual, ?_⟩
    intro a
    change Equator (equatorEmbed (rho.1 a))
    exact equatorEmbed_mem_equator (rho.1 a)
  left_inv := by
    intro rho
    apply Subtype.ext
    apply Subtype.ext
    funext a
    dsimp
    exact equatorEmbed_equatorDrop (rho.1.1 a) (rho.2 a)
  right_inv := by
    intro rho
    apply Subtype.ext
    funext a
    dsimp
    exact equatorDrop_equatorEmbed (rho.1 a)

def KyFanUnorderedParityStatement (d : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset d → SignedLabel d,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Odd (Fintype.card (EquatorActualARidge label))

theorem equatorRestrictedLabel_unordered_odd {d : ℕ}
    (hKy : KyFanUnorderedParityStatement d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (hno : NoComplementaryComparableLabels label) :
    Odd (Fintype.card (EquatorActualARidge (equatorRestrictedLabel label))) :=
  hKy (equatorRestrictedLabel label)
    (equatorRestrictedLabel_antipodal hantipodal)
    (equatorRestrictedLabel_noComplementary hno)

/-- A top chain is one-door when deleting exactly one of its vertices leaves
the alternating label set `A`. -/
def actualHemisphereAOneDoor {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label) : Prop :=
  (sigmaDoorSet (fun i => label (sigma.1.prefixChain i))).card = 1

noncomputable instance actualHemisphereAOneDoor_decidable {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d} :
    DecidablePred (actualHemisphereAOneDoor (label := label)) := by
  classical
  exact inferInstance

noncomputable def actualHemisphereAIncidentRepresentedCofaceEquiv {d : ℕ} (hd : 0 < d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label)
    (P : SignedPermutation (d + 1)) (hP : UpperPrefixChain P) (gap : Fin (d + 1))
    (hrho : ∀ a : Fin d, rho.1 a = P.prefixChain (gap.succAbove a)) :
    {sigma : ActualHemisphereAChain label // actualHemisphereAEdge rho sigma} ≃
      {Q : SignedPermutation (d + 1) // Q ∈ representedUpperRidgeLocalCofaces P gap} where
  toFun sigma := by
    classical
    let eta : Fin (d + 1) := Classical.choose sigma.2
    have heta : ∀ a : Fin d, rho.1 a = sigma.1.1.prefixChain (eta.succAbove a) :=
      Classical.choose_spec sigma.2
    have heta_eq_gap : eta = gap := by
      apply deletion_gap_eq_of_prefixChain_eq hd (P := P) (Q := sigma.1.1)
      intro a
      exact (heta a).symm.trans (hrho a)
    have hdel :
        ∀ a : Fin d,
          sigma.1.1.prefixChain (gap.succAbove a) =
            P.prefixChain (gap.succAbove a) := by
      intro a
      have ha := heta a
      rw [heta_eq_gap] at ha
      exact ha.symm.trans (hrho a)
    have hcases :=
      eq_or_representedRidgePartner_of_deletion_eq P sigma.1.1 gap hdel
    refine ⟨sigma.1.1, ?_⟩
    by_cases hb : RepresentedUpperRidgeBoundary P gap
    · rcases hcases with hQ | hQ
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
      · exact False.elim
          (representedRidgePartner_not_upperPrefixChain_of_boundary P gap hP hb
            (by simpa [hQ] using sigma.1.2.1))
    · rcases hcases with hQ | hQ
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
  invFun Q := by
    classical
    have hQcases : Q.1 = P ∨ Q.1 = representedRidgePartner P gap := by
      by_cases hb : RepresentedUpperRidgeBoundary P gap
      · left
        simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
      · simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
    have hQupper : UpperPrefixChain Q.1 := by
      by_cases hb : RepresentedUpperRidgeBoundary P gap
      · have hQ : Q.1 = P := by
          simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
        simpa [hQ] using hP
      · rcases hQcases with hQ | hQ
        · simpa [hQ] using hP
        · simpa [hQ] using representedRidgePartner_upperPrefixChain P gap hP hb
    have hQdel :
        ∀ a : Fin d, Q.1.prefixChain (gap.succAbove a) = rho.1 a := by
      intro a
      rcases hQcases with hQ | hQ
      · simpa [hQ] using (hrho a).symm
      · simpa [hQ, representedRidgePartner_deletion_eq P gap a] using (hrho a).symm
    let sigma : ActualHemisphereAChain label :=
      ⟨Q.1, hQupper, ⟨gap, fun a => by
        rcases rho.2.2.2 a with ⟨t, ht⟩
        exact ⟨t, by simpa [hQdel t] using ht⟩⟩⟩
    exact ⟨sigma, ⟨gap, fun a => (hQdel a).symm⟩⟩
  left_inv := by
    intro sigma
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro Q
    apply Subtype.ext
    rfl

theorem actualHemisphereA_rho_degree_card {d : ℕ} (hd : 0 < d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (rho : ActualHemisphereARidge label) :
    Fintype.card
        {sigma : ActualHemisphereAChain label //
          actualHemisphereAEdge rho sigma} =
      if actualHemisphereABoundary rho then 1 else 2 := by
  classical
  rcases rho.2.2.1 with ⟨P, hP, gap, hrho⟩
  have hcongr :=
    Fintype.card_congr
      (actualHemisphereAIncidentRepresentedCofaceEquiv hd rho P hP gap hrho)
  have hlocal :
      Fintype.card
          {Q : SignedPermutation (d + 1) // Q ∈ representedUpperRidgeLocalCofaces P gap} =
        (representedUpperRidgeLocalCofaces P gap).card := by
    rw [Fintype.card_subtype]
    simp
  have hbiff := actualHemisphereABoundary_iff_represented rho P hP gap hrho
  rw [hcongr, hlocal, representedUpperRidgeLocalCofaces_card]
  by_cases hb : actualHemisphereABoundary rho
  · have hbr : RepresentedUpperRidgeBoundary P gap := hbiff.mp hb
    simp [hb, hbr]
  · have hbr : ¬ RepresentedUpperRidgeBoundary P gap := by
      intro h
      exact hb (hbiff.mpr h)
    simp [hb, hbr]

def actualRidgeOfChainGap {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label)
    (gap : {j : Fin (d + 1) //
      SigmaDeletionHasAlternatingLabelSet (fun i => label (sigma.1.prefixChain i)) j}) :
    ActualHemisphereARidge label :=
  ⟨fun a : Fin d => sigma.1.prefixChain (gap.1.succAbove a),
    ⟨fun a => sigma.2.1 (gap.1.succAbove a),
      ⟨sigma.1, sigma.2.1, ⟨gap.1, fun a => rfl⟩⟩,
      fun a => by
        rcases gap.2 a with ⟨t, htne, htlabel⟩
        rcases Fin.exists_succAbove_eq htne with ⟨b, hb⟩
        exact ⟨b, by simpa [← hb] using htlabel⟩⟩⟩

theorem actualRidgeOfChainGap_edge {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label)
    (gap : {j : Fin (d + 1) //
      SigmaDeletionHasAlternatingLabelSet (fun i => label (sigma.1.prefixChain i)) j}) :
    actualHemisphereAEdge (actualRidgeOfChainGap sigma gap) sigma := by
  exact ⟨gap.1, fun a => rfl⟩

theorem actualHemisphereAEdge_gives_door {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    {rho : ActualHemisphereARidge label} {sigma : ActualHemisphereAChain label}
    (hedge : actualHemisphereAEdge rho sigma) :
    ∃ gap : {j : Fin (d + 1) //
      SigmaDeletionHasAlternatingLabelSet (fun i => label (sigma.1.prefixChain i)) j},
      rho = actualRidgeOfChainGap sigma gap := by
  rcases hedge with ⟨gap, hgap⟩
  have hdoor : SigmaDeletionHasAlternatingLabelSet
      (fun i => label (sigma.1.prefixChain i)) gap := by
    intro a
    rcases rho.2.2.2 a with ⟨b, hb⟩
    exact ⟨gap.succAbove b, Fin.succAbove_ne gap b, by
      simpa [← hgap b] using hb⟩
  refine ⟨⟨gap, hdoor⟩, ?_⟩
  apply Subtype.ext
  funext a
  exact hgap a

theorem actualRidgeOfChainGap_injective {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label) :
    Function.Injective (actualRidgeOfChainGap sigma) := by
  intro gap eta heq
  apply Subtype.ext
  apply Fin.succAbove_left_injective
  funext a
  apply sigma.1.prefixChain_injective
  have hfun := congrArg Subtype.val heq
  exact congrFun hfun a

noncomputable def actualHemisphereAIncidentDoorEquiv {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label) :
    {rho : ActualHemisphereARidge label // actualHemisphereAEdge rho sigma} ≃
      {j : Fin (d + 1) //
        SigmaDeletionHasAlternatingLabelSet
          (fun i => label (sigma.1.prefixChain i)) j} where
  toFun rho :=
    Classical.choose (actualHemisphereAEdge_gives_door rho.2)
  invFun gap :=
    ⟨actualRidgeOfChainGap sigma gap, actualRidgeOfChainGap_edge sigma gap⟩
  left_inv := by
    intro rho
    have hspec := Classical.choose_spec (actualHemisphereAEdge_gives_door rho.2)
    apply Subtype.ext
    exact hspec.symm
  right_inv := by
    intro gap
    have hspec :=
      Classical.choose_spec
        (actualHemisphereAEdge_gives_door (actualRidgeOfChainGap_edge sigma gap))
    apply actualRidgeOfChainGap_injective sigma
    exact hspec.symm

theorem actualHemisphereA_sigma_degree_card {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label) :
    Fintype.card
        {rho : ActualHemisphereARidge label // actualHemisphereAEdge rho sigma} =
      (sigmaDoorSet (fun i => label (sigma.1.prefixChain i))).card := by
  classical
  have hcongr :=
    Fintype.card_congr (actualHemisphereAIncidentDoorEquiv sigma)
  have hdoor :
      Fintype.card
          {j : Fin (d + 1) //
            SigmaDeletionHasAlternatingLabelSet
              (fun i => label (sigma.1.prefixChain i)) j} =
        (sigmaDoorSet (fun i => label (sigma.1.prefixChain i))).card := by
    rw [Fintype.card_subtype]
    rfl
  exact hcongr.trans hdoor

theorem actualHemisphereA_sigma_odd_degree_iff_oneDoor {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label) :
    Odd
        (Fintype.card
          {rho : ActualHemisphereARidge label // actualHemisphereAEdge rho sigma}) ↔
      actualHemisphereAOneDoor sigma := by
  rcases sigma.2.2 with ⟨gap, hgap⟩
  have hdoorExtra :
      SigmaDeletionHasAlternatingLabelSet (fun i => label (sigma.1.prefixChain i)) gap := by
    intro a
    rcases hgap a with ⟨t, ht⟩
    exact ⟨gap.succAbove t, Fin.succAbove_ne gap t, ht⟩
  rw [actualHemisphereA_sigma_degree_card sigma, actualHemisphereAOneDoor]
  exact sigmaDoorSet_odd_iff_card_one_of_door hdoorExtra

theorem actualHemisphereA_sigma_degree_one_gives_prefixChain_complementary_pair {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label)
    (hdegree :
      Fintype.card
          {rho : ActualHemisphereARidge label // actualHemisphereAEdge rho sigma} = 1) :
    ∃ i j : Fin (d + 1), i < j ∧
      (label (sigma.1.prefixChain i)).index = (label (sigma.1.prefixChain j)).index ∧
      (label (sigma.1.prefixChain i)).positive ≠
        (label (sigma.1.prefixChain j)).positive := by
  have hdoorCard :
      (sigmaDoorSet (fun i => label (sigma.1.prefixChain i))).card = 1 := by
    simpa [actualHemisphereA_sigma_degree_card sigma] using hdegree
  rcases sigma.2.2 with ⟨gap, hgap⟩
  have hdoorExtra :
      SigmaDeletionHasAlternatingLabelSet (fun i => label (sigma.1.prefixChain i)) gap := by
    intro a
    rcases hgap a with ⟨t, ht⟩
    exact ⟨gap.succAbove t, Fin.succAbove_ne gap t, ht⟩
  exact sigmaDoorSet_card_one_gives_prefixChain_complementary_pair_of_door
    (label := label) (P := sigma.1) (extra := gap)
    hdoorExtra hdoorCard

theorem actualHemisphereARidge_nonempty_of_boundary_odd {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hboundaryOdd :
      Odd (Fintype.card
        {rho : ActualHemisphereARidge label //
          actualHemisphereABoundary rho})) :
    Nonempty (ActualHemisphereARidge label) := by
  rcases hboundaryOdd with ⟨k, hk⟩
  have hpos :
      0 < Fintype.card
        {rho : ActualHemisphereARidge label //
          actualHemisphereABoundary rho} := by
    omega
  obtain ⟨rho⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨rho.1⟩

noncomputable def actualHemisphereRhoDegreeDataOfDegreeCard {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hR : Nonempty (ActualHemisphereARidge label))
    (hdegree :
      ∀ rho : ActualHemisphereARidge label,
        Fintype.card
            {sigma : ActualHemisphereAChain label //
              actualHemisphereAEdge rho sigma} =
          if actualHemisphereABoundary rho then 1 else 2) :
    RhoDegreeManifoldData
      (ActualHemisphereARidge label) (ActualHemisphereAChain label) where
  edge := actualHemisphereAEdge
  edge_decidable := actualHemisphereAEdge_decidable
  boundary := actualHemisphereABoundary
  boundary_decidable := actualHemisphereABoundary_decidable
  nonempty_R := hR
  degree_card := hdegree

noncomputable def actualHemisphereRhoDegreeData {d : ℕ} (hd : 0 < d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hR : Nonempty (ActualHemisphereARidge label)) :
    RhoDegreeManifoldData
      (ActualHemisphereARidge label) (ActualHemisphereAChain label) :=
  actualHemisphereRhoDegreeDataOfDegreeCard hR
    (actualHemisphereA_rho_degree_card hd)

/-! ## Actual upper-hemisphere graph for an arbitrary alternating index set -/

def ActualHemisphereIdxRidge {r m : ℕ} (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :=
  {rho : Fin r → NonzeroSignedSubset (r + 1) //
    (∀ a : Fin r, UpperHemisphere (rho a)) ∧
      (∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
        ∃ gap : Fin (r + 1), ∀ a : Fin r,
          rho a = P.prefixChain (gap.succAbove a)) ∧
      ∀ a : Fin r, ∃ t : Fin r, label (rho t) = alternatingLabelOf idx a}

noncomputable instance actualHemisphereIdxRidge_fintype {r m : ℕ}
    (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    Fintype (ActualHemisphereIdxRidge idx label) := by
  classical
  dsimp [ActualHemisphereIdxRidge]
  infer_instance

def ActualHemisphereIdxChain {r m : ℕ} (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :=
  {P : SignedPermutation (r + 1) //
    UpperPrefixChain P ∧
      ∃ gap : Fin (r + 1), ∀ a : Fin r,
        ∃ t : Fin r,
          label (P.prefixChain (gap.succAbove t)) = alternatingLabelOf idx a}

noncomputable instance actualHemisphereIdxChain_fintype {r m : ℕ}
    (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    Fintype (ActualHemisphereIdxChain idx label) := by
  classical
  dsimp [ActualHemisphereIdxChain]
  infer_instance

def actualHemisphereIdxEdge {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereIdxRidge idx label)
    (sigma : ActualHemisphereIdxChain idx label) : Prop :=
  ∃ gap : Fin (r + 1), ∀ a : Fin r,
    rho.1 a = sigma.1.prefixChain (gap.succAbove a)

noncomputable instance actualHemisphereIdxEdge_decidable {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidableRel (actualHemisphereIdxEdge (idx := idx) (label := label)) := by
  classical
  exact inferInstance

def actualHemisphereIdxBoundary {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereIdxRidge idx label) : Prop :=
  ∀ a : Fin r, Equator (rho.1 a)

noncomputable instance actualHemisphereIdxBoundary_decidable {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidablePred (actualHemisphereIdxBoundary (idx := idx) (label := label)) := by
  classical
  exact inferInstance

def EquatorActualIdxRidge {r m : ℕ} (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset r → SignedLabel m) :=
  {rho : Fin r → NonzeroSignedSubset r //
    (∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
      RepresentedUpperRidgeBoundary P (Fin.last r) ∧
        ∀ a : Fin r,
          equatorEmbed (rho a) = P.prefixChain ((Fin.last r).succAbove a)) ∧
      ∀ a : Fin r, ∃ t : Fin r, label (rho t) = alternatingLabelOf idx a}

noncomputable instance equatorActualIdxRidge_fintype {r m : ℕ}
    (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset r → SignedLabel m) :
    Fintype (EquatorActualIdxRidge idx label) := by
  classical
  dsimp [EquatorActualIdxRidge]
  infer_instance

theorem actualHemisphereIdxBoundary_iff_represented {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereIdxRidge idx label)
    (P : SignedPermutation (r + 1)) (hP : UpperPrefixChain P) (gap : Fin (r + 1))
    (hrho : ∀ a : Fin r, rho.1 a = P.prefixChain (gap.succAbove a)) :
    actualHemisphereIdxBoundary rho ↔ RepresentedUpperRidgeBoundary P gap := by
  constructor
  · intro hb
    have hgap_last : gap = Fin.last r := by
      by_contra hne
      have hlast_ne_gap : Fin.last r ≠ gap := by
        intro h
        exact hne h.symm
      rcases Fin.exists_succAbove_eq hlast_ne_gap with ⟨a, ha⟩
      have hposTop :
          Fin.last r ∈ (P.prefixChain (Fin.last r)).1.pos :=
        last_mem_prefixPos_of_upper_of_order_le P (Fin.last r) (hP (Fin.last r))
          (Fin.le_last _)
      exact (hb a).1 (by
        rw [hrho a]
        simpa [← ha] using hposTop)
    subst gap
    have hcoord : P.order.symm (Fin.last r) = Fin.last r := by
      by_contra hcoord
      rcases Fin.exists_succAbove_eq hcoord with ⟨a, ha⟩
      have hpos :
          Fin.last r ∈ (P.prefixChain (P.order.symm (Fin.last r))).1.pos :=
        last_mem_prefixPos_of_upper_of_order_le P (P.order.symm (Fin.last r))
          (hP (P.order.symm (Fin.last r))) le_rfl
      exact (hb a).1 (by
        rw [hrho a]
        simpa [← ha] using hpos)
    exact ⟨rfl, hcoord⟩
  · rintro ⟨hgap, hcoord⟩ a
    subst gap
    constructor
    · intro hpos
      rw [hrho a] at hpos
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixPos, hcoord] using hpos
    · intro hneg
      rw [hrho a] at hneg
      simpa [SignedPermutation.prefixChain, SignedPermutation.prefixSignedSubset,
        SignedPermutation.prefixNeg, hcoord] using hneg

noncomputable def equatorBoundaryIdxRidgeToEquator {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : {rho : ActualHemisphereIdxRidge idx label //
      actualHemisphereIdxBoundary rho}) :
    EquatorActualIdxRidge idx (equatorRestrictedLabelOf label) := by
  classical
  let dropped : Fin r → NonzeroSignedSubset r :=
    fun a => (equatorEquiv r).symm ⟨rho.1.1 a, rho.2 a⟩
  have hrepr :
      ∃ P : SignedPermutation (r + 1), UpperPrefixChain P ∧
        RepresentedUpperRidgeBoundary P (Fin.last r) ∧
          ∀ a : Fin r,
            equatorEmbed (dropped a) =
              P.prefixChain ((Fin.last r).succAbove a) := by
    rcases rho.1.2.2.1 with ⟨P, hP, gap, hrho⟩
    have hb := (actualHemisphereIdxBoundary_iff_represented rho.1 P hP gap hrho).mp rho.2
    rcases hb with ⟨hgap, hcoord⟩
    subst gap
    refine ⟨P, hP, ⟨rfl, hcoord⟩, ?_⟩
    intro a
    calc
      equatorEmbed (dropped a) = rho.1.1 a := by
        dsimp [dropped, equatorEquiv]
        exact equatorEmbed_equatorDrop (rho.1.1 a) (rho.2 a)
      _ = P.prefixChain ((Fin.last r).succAbove a) := hrho a
  refine ⟨dropped, hrepr, ?_⟩
  intro a
  rcases rho.1.2.2.2 a with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  dsimp [dropped, equatorRestrictedLabelOf, equatorEquiv]
  simpa [equatorEmbed_equatorDrop (rho.1.1 t) (rho.2 t)] using ht

noncomputable def equatorBoundaryIdxRidgeFromEquator {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : EquatorActualIdxRidge idx (equatorRestrictedLabelOf label)) :
    {rho : ActualHemisphereIdxRidge idx label // actualHemisphereIdxBoundary rho} := by
  classical
  let lifted : Fin r → NonzeroSignedSubset (r + 1) := fun a => equatorEmbed (rho.1 a)
  have hupper : ∀ a : Fin r, UpperHemisphere (lifted a) := by
    intro a
    exact equator_subset_upperHemisphere (equatorEmbed_mem_equator (rho.1 a))
  let hactual : ActualHemisphereIdxRidge idx label :=
    ⟨lifted, by
      refine ⟨hupper, ?_, ?_⟩
      · rcases rho.2.1 with ⟨P, hP, _hb, hrepr⟩
        exact ⟨P, hP, ⟨Fin.last r, hrepr⟩⟩
      · intro a
        rcases rho.2.2 a with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        dsimp [lifted, equatorRestrictedLabelOf, equatorEquiv] at ht ⊢
        simpa using ht⟩
  refine ⟨hactual, ?_⟩
  intro a
  change Equator (equatorEmbed (rho.1 a))
  exact equatorEmbed_mem_equator (rho.1 a)

noncomputable def equatorBoundaryIdxRidgeEquiv {r m : ℕ}
    (idx : Fin r → Fin m)
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    {rho : ActualHemisphereIdxRidge idx label // actualHemisphereIdxBoundary rho} ≃
      EquatorActualIdxRidge idx (equatorRestrictedLabelOf label) where
  toFun := equatorBoundaryIdxRidgeToEquator
  invFun := equatorBoundaryIdxRidgeFromEquator
  left_inv := by
    intro rho
    apply Subtype.ext
    apply Subtype.ext
    funext a
    dsimp [equatorBoundaryIdxRidgeToEquator, equatorBoundaryIdxRidgeFromEquator]
    exact equatorEmbed_equatorDrop (rho.1.1 a) (rho.2 a)
  right_inv := by
    intro rho
    apply Subtype.ext
    funext a
    dsimp [equatorBoundaryIdxRidgeToEquator, equatorBoundaryIdxRidgeFromEquator]
    exact equatorDrop_equatorEmbed (rho.1 a)

abbrev StrictIndexMap (r m : ℕ) :=
  {idx : Fin r → Fin m // StrictMono idx}

@[implicit_reducible]
noncomputable def strictIndexMapFintype (r m : ℕ) :
    Fintype (StrictIndexMap r m) := by
  classical
  exact Fintype.ofFinset
    ((Finset.univ : Finset (Fin r → Fin m)).filter fun idx => StrictMono idx)
    (by
      intro idx
      change idx ∈
          ((Finset.univ : Finset (Fin r → Fin m)).filter fun idx => StrictMono idx) ↔
        StrictMono idx
      simp)

abbrev EquatorActualAnyIdxRidge {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :=
  Σ idx : StrictIndexMap r m, EquatorActualIdxRidge idx.1 label

@[implicit_reducible]
noncomputable def equatorActualAnyIdxRidgeFintype {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :
    Fintype (EquatorActualAnyIdxRidge label) := by
  classical
  letI : Fintype (StrictIndexMap r m) := strictIndexMapFintype r m
  infer_instance

noncomputable def equatorActualAnyIdxRidgeCard {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) : ℕ :=
  @Fintype.card (EquatorActualAnyIdxRidge label) (equatorActualAnyIdxRidgeFintype label)

def KyFanUnorderedParityStatement2 (r m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset r → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Odd (equatorActualAnyIdxRidgeCard label)

def actualHemisphereIdxOneDoor {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereIdxChain idx label) : Prop :=
  (sigmaDoorSetOf idx (fun i => label (sigma.1.prefixChain i))).card = 1

noncomputable instance actualHemisphereIdxOneDoor_decidable {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m} :
    DecidablePred (actualHemisphereIdxOneDoor (idx := idx) (label := label)) := by
  classical
  exact inferInstance

noncomputable def actualHemisphereIdxIncidentRepresentedCofaceEquiv {r m : ℕ}
    (hr : 0 < r)
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereIdxRidge idx label)
    (P : SignedPermutation (r + 1)) (hP : UpperPrefixChain P) (gap : Fin (r + 1))
    (hrho : ∀ a : Fin r, rho.1 a = P.prefixChain (gap.succAbove a)) :
    {sigma : ActualHemisphereIdxChain idx label // actualHemisphereIdxEdge rho sigma} ≃
      {Q : SignedPermutation (r + 1) // Q ∈ representedUpperRidgeLocalCofaces P gap} where
  toFun sigma := by
    classical
    let eta : Fin (r + 1) := Classical.choose sigma.2
    have heta : ∀ a : Fin r, rho.1 a = sigma.1.1.prefixChain (eta.succAbove a) :=
      Classical.choose_spec sigma.2
    have heta_eq_gap : eta = gap := by
      apply deletion_gap_eq_of_prefixChain_eq hr (P := P) (Q := sigma.1.1)
      intro a
      exact (heta a).symm.trans (hrho a)
    have hdel :
        ∀ a : Fin r,
          sigma.1.1.prefixChain (gap.succAbove a) =
            P.prefixChain (gap.succAbove a) := by
      intro a
      have ha := heta a
      rw [heta_eq_gap] at ha
      exact ha.symm.trans (hrho a)
    have hcases :=
      eq_or_representedRidgePartner_of_deletion_eq P sigma.1.1 gap hdel
    refine ⟨sigma.1.1, ?_⟩
    by_cases hb : RepresentedUpperRidgeBoundary P gap
    · rcases hcases with hQ | hQ
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
      · exact False.elim
          (representedRidgePartner_not_upperPrefixChain_of_boundary P gap hP hb
            (by simpa [hQ] using sigma.1.2.1))
    · rcases hcases with hQ | hQ
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
      · simpa [representedUpperRidgeLocalCofaces, hb, hQ]
  invFun Q := by
    classical
    have hQcases : Q.1 = P ∨ Q.1 = representedRidgePartner P gap := by
      by_cases hb : RepresentedUpperRidgeBoundary P gap
      · left
        simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
      · simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
    have hQupper : UpperPrefixChain Q.1 := by
      by_cases hb : RepresentedUpperRidgeBoundary P gap
      · have hQ : Q.1 = P := by
          simpa [representedUpperRidgeLocalCofaces, hb] using Q.2
        simpa [hQ] using hP
      · rcases hQcases with hQ | hQ
        · simpa [hQ] using hP
        · simpa [hQ] using representedRidgePartner_upperPrefixChain P gap hP hb
    have hQdel :
        ∀ a : Fin r, Q.1.prefixChain (gap.succAbove a) = rho.1 a := by
      intro a
      rcases hQcases with hQ | hQ
      · simpa [hQ] using (hrho a).symm
      · simpa [hQ, representedRidgePartner_deletion_eq P gap a] using (hrho a).symm
    let sigma : ActualHemisphereIdxChain idx label :=
      ⟨Q.1, hQupper, ⟨gap, fun a => by
        rcases rho.2.2.2 a with ⟨t, ht⟩
        exact ⟨t, by simpa [hQdel t] using ht⟩⟩⟩
    exact ⟨sigma, ⟨gap, fun a => (hQdel a).symm⟩⟩
  left_inv := by
    intro sigma
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro Q
    apply Subtype.ext
    rfl

theorem actualHemisphereIdx_rho_degree_card {r m : ℕ} (hr : 0 < r)
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (rho : ActualHemisphereIdxRidge idx label) :
    Fintype.card
        {sigma : ActualHemisphereIdxChain idx label //
          actualHemisphereIdxEdge rho sigma} =
      if actualHemisphereIdxBoundary rho then 1 else 2 := by
  classical
  rcases rho.2.2.1 with ⟨P, hP, gap, hrho⟩
  have hcongr :=
    Fintype.card_congr
      (actualHemisphereIdxIncidentRepresentedCofaceEquiv hr rho P hP gap hrho)
  have hlocal :
      Fintype.card
          {Q : SignedPermutation (r + 1) // Q ∈ representedUpperRidgeLocalCofaces P gap} =
        (representedUpperRidgeLocalCofaces P gap).card := by
    rw [Fintype.card_subtype]
    simp
  have hbiff := actualHemisphereIdxBoundary_iff_represented rho P hP gap hrho
  rw [hcongr, hlocal, representedUpperRidgeLocalCofaces_card]
  by_cases hb : actualHemisphereIdxBoundary rho
  · have hbr : RepresentedUpperRidgeBoundary P gap := hbiff.mp hb
    simp [hb, hbr]
  · have hbr : ¬ RepresentedUpperRidgeBoundary P gap := by
      intro h
      exact hb (hbiff.mpr h)
    simp [hb, hbr]

def actualIdxRidgeOfChainGap {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereIdxChain idx label)
    (gap : {j : Fin (r + 1) //
      SigmaDeletionHasAlternatingLabelSetOf idx
        (fun i => label (sigma.1.prefixChain i)) j}) :
    ActualHemisphereIdxRidge idx label :=
  ⟨fun a : Fin r => sigma.1.prefixChain (gap.1.succAbove a),
    ⟨fun a => sigma.2.1 (gap.1.succAbove a),
      ⟨sigma.1, sigma.2.1, ⟨gap.1, fun a => rfl⟩⟩,
      fun a => by
        rcases gap.2 a with ⟨t, htne, htlabel⟩
        rcases Fin.exists_succAbove_eq htne with ⟨b, hb⟩
        exact ⟨b, by simpa [← hb] using htlabel⟩⟩⟩

theorem actualIdxRidgeOfChainGap_edge {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereIdxChain idx label)
    (gap : {j : Fin (r + 1) //
      SigmaDeletionHasAlternatingLabelSetOf idx
        (fun i => label (sigma.1.prefixChain i)) j}) :
    actualHemisphereIdxEdge (actualIdxRidgeOfChainGap sigma gap) sigma := by
  exact ⟨gap.1, fun a => rfl⟩

theorem actualHemisphereIdxEdge_gives_door {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    {rho : ActualHemisphereIdxRidge idx label}
    {sigma : ActualHemisphereIdxChain idx label}
    (hedge : actualHemisphereIdxEdge rho sigma) :
    ∃ gap : {j : Fin (r + 1) //
      SigmaDeletionHasAlternatingLabelSetOf idx
        (fun i => label (sigma.1.prefixChain i)) j},
      rho = actualIdxRidgeOfChainGap sigma gap := by
  rcases hedge with ⟨gap, hgap⟩
  have hdoor : SigmaDeletionHasAlternatingLabelSetOf idx
      (fun i => label (sigma.1.prefixChain i)) gap := by
    intro a
    rcases rho.2.2.2 a with ⟨b, hb⟩
    exact ⟨gap.succAbove b, Fin.succAbove_ne gap b, by
      simpa [← hgap b] using hb⟩
  refine ⟨⟨gap, hdoor⟩, ?_⟩
  apply Subtype.ext
  funext a
  exact hgap a

theorem actualIdxRidgeOfChainGap_injective {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereIdxChain idx label) :
    Function.Injective (actualIdxRidgeOfChainGap sigma) := by
  intro gap eta heq
  apply Subtype.ext
  apply Fin.succAbove_left_injective
  funext a
  apply sigma.1.prefixChain_injective
  have hfun := congrArg Subtype.val heq
  exact congrFun hfun a

noncomputable def actualHemisphereIdxIncidentDoorEquiv {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereIdxChain idx label) :
    {rho : ActualHemisphereIdxRidge idx label // actualHemisphereIdxEdge rho sigma} ≃
      {j : Fin (r + 1) //
        SigmaDeletionHasAlternatingLabelSetOf idx
          (fun i => label (sigma.1.prefixChain i)) j} where
  toFun rho :=
    Classical.choose (actualHemisphereIdxEdge_gives_door rho.2)
  invFun gap :=
    ⟨actualIdxRidgeOfChainGap sigma gap, actualIdxRidgeOfChainGap_edge sigma gap⟩
  left_inv := by
    intro rho
    have hspec := Classical.choose_spec (actualHemisphereIdxEdge_gives_door rho.2)
    apply Subtype.ext
    exact hspec.symm
  right_inv := by
    intro gap
    have hspec :=
      Classical.choose_spec
        (actualHemisphereIdxEdge_gives_door (actualIdxRidgeOfChainGap_edge sigma gap))
    apply actualIdxRidgeOfChainGap_injective sigma
    exact hspec.symm

theorem actualHemisphereIdx_sigma_degree_card {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereIdxChain idx label) :
    Fintype.card
        {rho : ActualHemisphereIdxRidge idx label // actualHemisphereIdxEdge rho sigma} =
      (sigmaDoorSetOf idx (fun i => label (sigma.1.prefixChain i))).card := by
  classical
  have hcongr :=
    Fintype.card_congr (actualHemisphereIdxIncidentDoorEquiv sigma)
  have hdoor :
      Fintype.card
          {j : Fin (r + 1) //
            SigmaDeletionHasAlternatingLabelSetOf idx
              (fun i => label (sigma.1.prefixChain i)) j} =
        (sigmaDoorSetOf idx (fun i => label (sigma.1.prefixChain i))).card := by
    rw [Fintype.card_subtype]
    rfl
  exact hcongr.trans hdoor

theorem actualHemisphereIdx_sigma_odd_degree_iff_oneDoor {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereIdxChain idx label) :
    Odd
        (Fintype.card
          {rho : ActualHemisphereIdxRidge idx label //
            actualHemisphereIdxEdge rho sigma}) ↔
      actualHemisphereIdxOneDoor sigma := by
  rcases sigma.2.2 with ⟨gap, hgap⟩
  have hdoorExtra :
      SigmaDeletionHasAlternatingLabelSetOf idx
        (fun i => label (sigma.1.prefixChain i)) gap := by
    intro a
    rcases hgap a with ⟨t, ht⟩
    exact ⟨gap.succAbove t, Fin.succAbove_ne gap t, ht⟩
  rw [actualHemisphereIdx_sigma_degree_card sigma, actualHemisphereIdxOneDoor]
  exact sigmaDoorSetOf_odd_iff_card_one_of_door hidx hdoorExtra

theorem actualHemisphereIdxRidge_nonempty_of_boundary_odd {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hboundaryOdd :
      Odd (Fintype.card
        {rho : ActualHemisphereIdxRidge idx label //
          actualHemisphereIdxBoundary rho})) :
    Nonempty (ActualHemisphereIdxRidge idx label) := by
  rcases hboundaryOdd with ⟨k, hk⟩
  have hpos :
      0 < Fintype.card
        {rho : ActualHemisphereIdxRidge idx label //
          actualHemisphereIdxBoundary rho} := by
    omega
  obtain ⟨rho⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨rho.1⟩

noncomputable def actualHemisphereIdxRhoDegreeDataOfDegreeCard {r m : ℕ}
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hR : Nonempty (ActualHemisphereIdxRidge idx label))
    (hdegree :
      ∀ rho : ActualHemisphereIdxRidge idx label,
        Fintype.card
            {sigma : ActualHemisphereIdxChain idx label //
              actualHemisphereIdxEdge rho sigma} =
          if actualHemisphereIdxBoundary rho then 1 else 2) :
    RhoDegreeManifoldData
      (ActualHemisphereIdxRidge idx label) (ActualHemisphereIdxChain idx label) where
  edge := actualHemisphereIdxEdge
  edge_decidable := actualHemisphereIdxEdge_decidable
  boundary := actualHemisphereIdxBoundary
  boundary_decidable := actualHemisphereIdxBoundary_decidable
  nonempty_R := hR
  degree_card := hdegree

noncomputable def actualHemisphereIdxRhoDegreeData {r m : ℕ} (hr : 0 < r)
    {idx : Fin r → Fin m}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hR : Nonempty (ActualHemisphereIdxRidge idx label)) :
    RhoDegreeManifoldData
      (ActualHemisphereIdxRidge idx label) (ActualHemisphereIdxChain idx label) :=
  actualHemisphereIdxRhoDegreeDataOfDegreeCard hR
    (actualHemisphereIdx_rho_degree_card hr)

/-! ## Fan parity induction and Tucker reduction, as explicit data interfaces -/

/-- One induction step of Ky Fan parity from the equator count and the two
degree facts.  This is the formal handshaking step; the remaining geometric
work is to instantiate `RhoDegreeManifoldData` for actual hemisphere ridges
and prove the corresponding sigma degree classifier. -/
theorem kyFan_parity_step_from_rho_sigma_data
    {R S : Type*} [Fintype R] [Fintype S]
    (D : RhoDegreeManifoldData R S)
    (topAlternating : S → Prop) [DecidablePred topAlternating]
    (hs :
      ∀ s : S,
        (Odd (Fintype.card {r : R // D.edge r s}) ↔ topAlternating s))
    (hboundary :
      Odd (Fintype.card {r : R // D.boundary r})) :
    Odd (Fintype.card {s : S // topAlternating s}) := by
  have hmod := D.boundary_top_parity topAlternating hs
  have hb : (Fintype.card {r : R // D.boundary r} : ZMod 2) = 1 :=
    hboundary.natCast_zmod_two
  have ht : (Fintype.card {s : S // topAlternating s} : ZMod 2) = 1 := by
    simpa [hb] using hmod.symm
  exact (ZMod.natCast_eq_one_iff_odd).mp ht

/-- The final reduction data from the Chapter 39 proof note: the boundary
label-set-`A` ridges are odd, rho degrees are `1/2`, and sigma degree one is
classified by the local `sigmaDoorSet` lemma above.  This theorem is deliberately
not an empty-type shortcut: it requires an explicit `Nonempty R`. -/
theorem final_reduction_from_label_set_A_graph
    {R M : Type*} [Fintype R] [Fintype M]
    (D : RhoDegreeManifoldData R M)
    (oneDoor : M → Prop) [DecidablePred oneDoor]
    (hm :
      ∀ m : M,
        (Odd (Fintype.card {r : R // D.edge r m}) ↔ oneDoor m))
    (hboundaryOdd : Odd (Fintype.card {r : R // D.boundary r})) :
    ∃ m : M, oneDoor m := by
  have hodd : Odd (Fintype.card {m : M // oneDoor m}) :=
    kyFan_parity_step_from_rho_sigma_data D oneDoor hm hboundaryOdd
  have hpos : 0 < Fintype.card {m : M // oneDoor m} := by
    rcases hodd with ⟨a, ha⟩
    omega
  obtain ⟨m⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨m.1, m.2⟩

theorem actualHemisphereA_boundary_odd_gives_prefixChain_complementary_pair {d : ℕ}
    (hd : 0 < d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hboundaryOdd :
      Odd (Fintype.card
        {rho : ActualHemisphereARidge label //
          actualHemisphereABoundary rho})) :
    ∃ P : SignedPermutation (d + 1), ∃ i j : Fin (d + 1), i < j ∧
      (label (P.prefixChain i)).index = (label (P.prefixChain j)).index ∧
      (label (P.prefixChain i)).positive ≠ (label (P.prefixChain j)).positive := by
  classical
  let D : RhoDegreeManifoldData
      (ActualHemisphereARidge label) (ActualHemisphereAChain label) :=
    actualHemisphereRhoDegreeData hd
      (actualHemisphereARidge_nonempty_of_boundary_odd hboundaryOdd)
  obtain ⟨sigma, hsigmaOneDoor⟩ :=
    final_reduction_from_label_set_A_graph
      (D := D)
      (oneDoor := actualHemisphereAOneDoor (label := label))
      (hm := actualHemisphereA_sigma_odd_degree_iff_oneDoor)
      hboundaryOdd
  rcases sigma.2.2 with ⟨gap, hgap⟩
  have hdoorExtra :
      SigmaDeletionHasAlternatingLabelSet
        (fun i => label (sigma.1.prefixChain i)) gap := by
    intro a
    rcases hgap a with ⟨t, ht⟩
    exact ⟨gap.succAbove t, Fin.succAbove_ne gap t, ht⟩
  have hdoorCard :
      (sigmaDoorSet (fun i => label (sigma.1.prefixChain i))).card = 1 := by
    simpa [actualHemisphereAOneDoor] using hsigmaOneDoor
  obtain ⟨i, j, hij, hidx, hsign⟩ :=
    sigmaDoorSet_card_one_gives_prefixChain_complementary_pair_of_door
      (label := label) (P := sigma.1) (extra := gap)
      hdoorExtra hdoorCard
  exact ⟨sigma.1, i, j, hij, hidx, hsign⟩

def ActualHemisphereBoundaryOddStatement (d : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset (d + 1) → SignedLabel d,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Odd (Fintype.card
          {rho : ActualHemisphereARidge label //
            actualHemisphereABoundary rho})

def EquatorBoundaryCardBridgeStatement (d : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset (d + 1) → SignedLabel d,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Fintype.card
            {rho : ActualHemisphereARidge label //
              actualHemisphereABoundary rho} =
          Fintype.card (EquatorActualARidge (equatorRestrictedLabel label))

theorem equatorBoundaryCardBridge (d : ℕ) :
    EquatorBoundaryCardBridgeStatement d := by
  intro label _hantipodal _hno
  exact Fintype.card_congr (equatorBoundaryARidgeEquiv label)

theorem actualHemisphereBoundaryOdd_of_equator_card_bridge {d : ℕ}
    (hKy : KyFanUnorderedParityStatement d)
    (hbridge : EquatorBoundaryCardBridgeStatement d) :
    ActualHemisphereBoundaryOddStatement d := by
  intro label hantipodal hno
  have hodd :=
    equatorRestrictedLabel_unordered_odd hKy hantipodal hno
  have hcard := hbridge label hantipodal hno
  simpa [hcard] using hodd

theorem tuckerLemmaStatement_succ_of_actualHemisphere_boundary_odd {d : ℕ}
    (hd : 0 < d)
    (hboundaryOdd : ActualHemisphereBoundaryOddStatement d) :
    TuckerLemmaStatement (d + 1) := by
  apply tuckerLemmaStatement_of_chain_complementary_of_no_complementary
  intro label hantipodal hno
  exact actualHemisphereA_boundary_odd_gives_prefixChain_complementary_pair hd
    (hboundaryOdd label hantipodal hno)

theorem tuckerLemmaStatement_succ_of_equator_boundary_card_bridge {d : ℕ}
    (hd : 1 ≤ d) (hKy : KyFanUnorderedParityStatement d)
    (hbridge : EquatorBoundaryCardBridgeStatement d) :
    TuckerLemmaStatement (d + 1) :=
  tuckerLemmaStatement_succ_of_actualHemisphere_boundary_odd hd
    (actualHemisphereBoundaryOdd_of_equator_card_bridge hKy hbridge)

theorem tuckerLemma_pos_of_kyFanUnordered
    (hKy : ∀ d : ℕ, 1 ≤ d → KyFanUnorderedParityStatement d) :
    ∀ n : ℕ, 1 ≤ n → TuckerLemmaStatement n := by
  intro n hn
  cases n with
  | zero =>
      omega
  | succ d =>
      cases d with
      | zero =>
          exact tuckerLemmaStatement_one
      | succ e =>
          exact tuckerLemmaStatement_succ_of_equator_boundary_card_bridge
            (d := e + 1) (by omega) (hKy (e + 1) (by omega))
            (equatorBoundaryCardBridge (e + 1))

/-- Fan parity induction, separated from the geometric hemisphere step.  The
step is intended to be supplied by `kyFan_parity_step_from_rho_sigma_data`
after transporting the equator by `equatorEquiv`. -/
theorem kyFanParityStatement_of_induction_steps
    (hstep :
      ∀ r m : ℕ,
        1 ≤ r →
          r + 1 ≤ m →
            KyFanParityStatement r m →
              KyFanParityStatement (r + 1) m) :
    ∀ r m : ℕ, 1 ≤ r → r ≤ m → KyFanParityStatement r m := by
  intro r
  induction r with
  | zero =>
      intro m hr _hm
      omega
  | succ r ih =>
      cases r with
      | zero =>
          intro m _hr hm
          exact kyFanParityStatement_one hm
      | succ r =>
          intro m _hr hm
          apply hstep (r + 1) m
          · omega
          · simpa [Nat.succ_eq_add_one, add_assoc] using hm
          · exact ih m (by omega) (by omega)

/-- The final label-set-`A` graph reduction, with the graph-theoretic parity
and the local sigma-door classifier separated.  This is the precise output
needed by `tuckerLemmaStatement_of_chain_complementary`. -/
theorem final_reduction_graph_gives_prefixChain_complementary_pair {d : ℕ} (hd : 0 < d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    {R M : Type*} [Fintype R] [Fintype M]
    (D : RhoDegreeManifoldData R M)
    (oneDoor : M → Prop) [DecidablePred oneDoor]
    (hm :
      ∀ m : M,
        (Odd (Fintype.card {r : R // D.edge r m}) ↔ oneDoor m))
    (hboundaryOdd : Odd (Fintype.card {r : R // D.boundary r}))
    (chainOf : M → SignedPermutation (d + 1))
    (extraOf : M → Fin (d + 1))
    (hridge :
      ∀ m : M,
        oneDoor m →
          ∀ a : Fin d,
            label ((chainOf m).prefixChain ((extraOf m).succAbove a)) = alternatingLabel a)
    (hdoor :
      ∀ m : M,
        oneDoor m →
          (sigmaDoorSet (fun i => label ((chainOf m).prefixChain i))).card = 1) :
    ∃ P : SignedPermutation (d + 1), ∃ i j : Fin (d + 1), i < j ∧
      (label (P.prefixChain i)).index = (label (P.prefixChain j)).index ∧
      (label (P.prefixChain i)).positive ≠ (label (P.prefixChain j)).positive := by
  obtain ⟨m, hmone⟩ :=
    final_reduction_from_label_set_A_graph D oneDoor hm hboundaryOdd
  obtain ⟨i, j, hij, hidx, hsign⟩ :=
    sigmaDoorSet_card_one_gives_prefixChain_complementary_pair (d := d) hd
      (label := label) (P := chainOf m) (extra := extraOf m)
      (hridge m hmone) (hdoor m hmone)
  exact ⟨chainOf m, i, j, hij, hidx, hsign⟩

end ProofsInTheBook.Chapter39
