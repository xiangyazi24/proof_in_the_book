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
