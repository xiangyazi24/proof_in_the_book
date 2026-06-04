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

end ProofsInTheBook.Chapter39
