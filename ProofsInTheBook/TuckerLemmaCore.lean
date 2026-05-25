import Mathlib

/-!
# Tucker/Ky Fan core parity layer

This file is intentionally independent of `Chapter39.lean`: Chapter 39 can
import it without creating an import cycle.

The first part records the sign-vector model used for the octahedral Tucker
lemma and the signed-permutation maximal chains used in the Ky Fan frontier.
The second part isolates the finite parity step in the Prescott-Su/Fan path
argument: paths have two endpoints, antipodal paths have no fixed path, so the
total endpoint count is a multiple of four; after removing the two zero-
dimensional hemisphere endpoints and pairing positive with negative top
endpoints, the positive top endpoints are odd.
-/

namespace ProofsInTheBook.TuckerLemmaCore

/-! ## Sign-vector model -/

/-- A sign vector in `{−1,0,1}^n`, represented by its positive and negative
supports. -/
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

theorem maxSupport_congr_proof {n : ℕ} (X : SignedSubset n)
    (h₁ h₂ : X.Nonzero) : X.maxSupport h₁ = X.maxSupport h₂ := by
  unfold maxSupport
  congr

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

/-- The sign of the largest supported coordinate; this is the carrier
hemisphere sign for the standard octahedral flag. -/
noncomputable def maxSupportPositive {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) :
    Bool :=
  decide (X.maxSupport hX ∈ X.pos)

theorem maxSupportPositive_congr_proof {n : ℕ} (X : SignedSubset n)
    (h₁ h₂ : X.Nonzero) : X.maxSupportPositive h₁ = X.maxSupportPositive h₂ := by
  unfold maxSupportPositive
  rw [maxSupport_congr_proof X h₁ h₂]

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

/-- The face order on the cross-polytope boundary, by signed support inclusion. -/
def Le {n : ℕ} (X Y : SignedSubset n) : Prop :=
  X.pos ⊆ Y.pos ∧ X.neg ⊆ Y.neg

theorem eq_of_le_card_eq {n : ℕ} {X Y : SignedSubset n}
    (hXY : Le X Y) (hcard : X.card = Y.card) : X = Y := by
  have hpos_le : X.pos.card ≤ Y.pos.card := Finset.card_le_card hXY.1
  have hneg_le : X.neg.card ≤ Y.neg.card := Finset.card_le_card hXY.2
  have hsum : X.pos.card + X.neg.card = Y.pos.card + Y.neg.card := by
    simpa [card] using hcard
  have hpos_ge : Y.pos.card ≤ X.pos.card := by omega
  have hneg_ge : Y.neg.card ≤ X.neg.card := by omega
  have hpos_eq : X.pos = Y.pos := Finset.eq_of_subset_of_card_le hXY.1 hpos_ge
  have hneg_eq : X.neg = Y.neg := Finset.eq_of_subset_of_card_le hXY.2 hneg_ge
  cases X with
  | mk xpos xneg xdisj =>
      cases Y with
      | mk ypos yneg ydisj =>
          dsimp at hpos_eq hneg_eq
          subst ypos
          subst yneg
          simp

end SignedSubset

/-- Nonzero sign vectors, i.e. vertices/faces of the deleted origin sign
complex. -/
abbrev NonzeroSignedSubset (n : ℕ) :=
  {X : SignedSubset n // X.Nonzero}

namespace NonzeroSignedSubset

/-- Antipodal map on nonzero sign vectors. -/
def antipode {n : ℕ} (X : NonzeroSignedSubset n) : NonzeroSignedSubset n :=
  ⟨X.1.antipode, (SignedSubset.antipode_nonzero X.1).mpr X.2⟩

theorem antipode_involutive {n : ℕ} : Function.Involutive (@antipode n) := by
  intro X
  apply Subtype.ext
  cases X with
  | mk X hX =>
      cases X
      rfl

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

theorem ext {m : ℕ} {L M : SignedLabel m}
    (hpositive : L.positive = M.positive) (hindex : L.index = M.index) : L = M := by
  cases L
  cases M
  simp at hpositive hindex
  subst hpositive
  subst hindex
  rfl

end SignedLabel

/-- Octahedral Tucker's lemma in sign-vector form. -/
def TuckerLemmaStatement (n : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel (n - 1),
    (∀ X, label X.antipode = (label X).neg) →
      ∃ X Y : NonzeroSignedSubset n,
        SignedSubset.Le X.1 Y.1 ∧ label X = (label Y).neg

/-- A sign-vector labeling has no complementary comparable pair. -/
def NoComplementaryComparableLabels {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Prop :=
  ∀ X Y : NonzeroSignedSubset n,
    SignedSubset.Le X.1 Y.1 → label X ≠ (label Y).neg

theorem positive_eq_of_le_of_same_index_of_no_complement {n m : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    {X Y : NonzeroSignedSubset n}
    (hXY : SignedSubset.Le X.1 Y.1)
    (hindex : (label X).index = (label Y).index) :
    (label X).positive = (label Y).positive := by
  by_contra hne
  have hbool : (label X).positive = !((label Y).positive) := by
    cases hx : (label X).positive <;> cases hy : (label Y).positive <;>
      simp [hx, hy] at hne ⊢
  exact hno X Y hXY (SignedLabel.ext hbool (by simpa [SignedLabel.neg] using hindex))

/--
Ky Fan's alternating-chain form for the sign-vector/cross-polytope complex.
The chain order is the face-inclusion order.
-/
def KyFanAlternatingChainStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        ∃ chain : Fin n → NonzeroSignedSubset n,
          (∀ i j, i < j → SignedSubset.Le (chain i).1 (chain j).1) ∧
            StrictMono fun i => (label (chain i)).index

theorem not_strictMono_fin_pred (n : ℕ) (hn : 1 ≤ n) :
    ¬ ∃ f : Fin n → Fin (n - 1), StrictMono f := by
  rintro ⟨f, hf⟩
  have hinj : Function.Injective f := by
    intro i j hij
    by_cases hij' : i = j
    · exact hij'
    · have hlt_or_gt : i < j ∨ j < i := lt_or_gt_of_ne hij'
      rcases hlt_or_gt with hlt | hgt
      · exact (ne_of_lt (hf hlt) hij).elim
      · exact (ne_of_gt (hf hgt) hij).elim
  have hcard := Fintype.card_le_of_injective f hinj
  simp [Fintype.card_fin] at hcard
  omega

theorem tuckerLemmaStatement_of_kyFan {n : ℕ} (hn : 1 ≤ n)
    (hfan : KyFanAlternatingChainStatement n (n - 1)) :
    TuckerLemmaStatement n := by
  intro label hantipodal
  by_contra hnone
  have hno : NoComplementaryComparableLabels label := by
    intro X Y hXY hcomp
    exact hnone ⟨X, Y, hXY, hcomp⟩
  obtain ⟨chain, _hchain, hstrict⟩ := hfan label hantipodal hno
  exact not_strictMono_fin_pred n hn ⟨fun i => (label (chain i)).index, hstrict⟩

/-! ## Signed-permutation maximal chains -/

/-- A signed permutation, i.e. a maximal chain in the face lattice of the
cross-polytope boundary. -/
structure SignedPermutation (n : ℕ) where
  order : Equiv.Perm (Fin n)
  positive : Fin n → Bool
  deriving DecidableEq

def signedPermutationEquiv (n : ℕ) :
    SignedPermutation n ≃ Equiv.Perm (Fin n) × (Fin n → Bool) where
  toFun P := (P.order, P.positive)
  invFun data := { order := data.1, positive := data.2 }
  left_inv := by
    intro P
    cases P
    rfl
  right_inv := by
    intro data
    cases data
    rfl

noncomputable instance (n : ℕ) : Fintype (SignedPermutation n) :=
  Fintype.ofEquiv (Equiv.Perm (Fin n) × (Fin n → Bool)) (signedPermutationEquiv n).symm

namespace SignedPermutation

/-- Antipodal signed permutation: keep the order and flip every sign. -/
def antipode {n : ℕ} (P : SignedPermutation n) : SignedPermutation n where
  order := P.order
  positive := fun i => !P.positive i

theorem antipode_involutive {n : ℕ} : Function.Involutive (@antipode n) := by
  intro P
  cases P
  simp [antipode]

theorem antipode_ne_self {n : ℕ} (hn : 0 < n) (P : SignedPermutation n) :
    P.antipode ≠ P := by
  intro h
  let i : Fin n := ⟨0, hn⟩
  have hfun := congrArg SignedPermutation.positive h
  have hi := congrFun hfun i
  simp [antipode] at hi

/-- Positive coordinates in the `i`th prefix face of a signed permutation. -/
def prefixPos {n : ℕ} (P : SignedPermutation n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x => P.order.symm x ≤ i ∧ P.positive (P.order.symm x)

/-- Negative coordinates in the `i`th prefix face of a signed permutation. -/
def prefixNeg {n : ℕ} (P : SignedPermutation n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x => P.order.symm x ≤ i ∧ !P.positive (P.order.symm x)

theorem prefix_disjoint {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    Disjoint (P.prefixPos i) (P.prefixNeg i) := by
  rw [Finset.disjoint_left]
  intro x hxpos hxneg
  simp [prefixPos, prefixNeg] at hxpos hxneg
  cases h : P.positive (P.order.symm x) <;> simp [h] at hxpos hxneg

theorem prefixPos_antipode {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    P.antipode.prefixPos i = P.prefixNeg i := by
  ext x
  simp [antipode, prefixPos, prefixNeg]

theorem prefixNeg_antipode {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    P.antipode.prefixNeg i = P.prefixPos i := by
  ext x
  simp [antipode, prefixPos, prefixNeg]

/-- The `i`th prefix face as a sign vector. -/
def prefixSignedSubset {n : ℕ} (P : SignedPermutation n) (i : Fin n) : SignedSubset n where
  pos := P.prefixPos i
  neg := P.prefixNeg i
  disjoint := P.prefix_disjoint i

theorem prefix_nonzero {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    (P.prefixSignedSubset i).Nonzero := by
  let x : Fin n := P.order i
  have hxuniv : x ∈ (Finset.univ : Finset (Fin n)) := by simp
  have hsymm : P.order.symm x = i := by simp [x]
  have hle : P.order.symm x ≤ i := le_of_eq hsymm
  by_cases hpos : P.positive (P.order.symm x) = true
  · left
    exact ⟨x, by simp [prefixSignedSubset, prefixPos, hxuniv, hle, hpos]⟩
  · right
    exact ⟨x, by simp [prefixSignedSubset, prefixNeg, hxuniv, hle, hpos]⟩

/-- The maximal chain associated to a signed permutation. -/
def prefixChain {n : ℕ} (P : SignedPermutation n) (i : Fin n) : NonzeroSignedSubset n :=
  ⟨P.prefixSignedSubset i, P.prefix_nonzero i⟩

theorem prefixSignedSubset_antipode {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    P.antipode.prefixSignedSubset i = (P.prefixSignedSubset i).antipode := by
  cases P with
  | mk order positive =>
      simp [antipode, prefixSignedSubset, prefixPos, prefixNeg, SignedSubset.antipode]

theorem prefixChain_antipode {n : ℕ} (P : SignedPermutation n) (i : Fin n) :
    P.antipode.prefixChain i = (P.prefixChain i).antipode := by
  apply Subtype.ext
  exact P.prefixSignedSubset_antipode i

theorem prefixChain_le {n : ℕ} (P : SignedPermutation n) {i j : Fin n} (hij : i ≤ j) :
    SignedSubset.Le (P.prefixChain i).1 (P.prefixChain j).1 := by
  constructor
  · intro x hx
    simp [prefixChain, prefixSignedSubset, prefixPos] at hx ⊢
    exact ⟨hx.1.trans hij, hx.2⟩
  · intro x hx
    simp [prefixChain, prefixSignedSubset, prefixNeg] at hx ⊢
    exact ⟨hx.1.trans hij, hx.2⟩

theorem prefixChain_strictly_ordered {n : ℕ} (P : SignedPermutation n) :
    ∀ i j, i < j → SignedSubset.Le (P.prefixChain i).1 (P.prefixChain j).1 := by
  intro i j hij
  exact P.prefixChain_le hij.le

end SignedPermutation

/--
Positive-first alternating prefix labels: the absolute label indices strictly
increase along the signed-permutation prefix chain, and the signs alternate
`+,-,+,-,...`.
-/
def PositiveAlternatingPrefixLabels {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) (P : SignedPermutation n) : Prop :=
  (StrictMono fun i => (label (P.prefixChain i)).index) ∧
    ∀ i : Fin n, (label (P.prefixChain i)).positive = decide (Even i.val)

/-- Negative-first alternating prefix labels. -/
def NegativeAlternatingPrefixLabels {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) (P : SignedPermutation n) : Prop :=
  (StrictMono fun i => (label (P.prefixChain i)).index) ∧
    ∀ i : Fin n, (label (P.prefixChain i)).positive = !decide (Even i.val)

theorem label_prefixChain_antipode {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : SignedPermutation n) (i : Fin n) :
    label (P.antipode.prefixChain i) = (label (P.prefixChain i)).neg := by
  rw [SignedPermutation.prefixChain_antipode]
  exact hantipodal (P.prefixChain i)

theorem prefix_strictMono_antipode_iff {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : SignedPermutation n) :
    (StrictMono fun i => (label (P.antipode.prefixChain i)).index) ↔
      StrictMono fun i => (label (P.prefixChain i)).index := by
  simp [label_prefixChain_antipode label hantipodal P, SignedLabel.neg]

theorem positiveAlternatingPrefixLabels_antipode_iff {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : SignedPermutation n) :
    PositiveAlternatingPrefixLabels label P.antipode ↔
      NegativeAlternatingPrefixLabels label P := by
  constructor
  · intro h
    refine ⟨(prefix_strictMono_antipode_iff label hantipodal P).mp h.1, ?_⟩
    intro i
    have hsign := h.2 i
    rw [label_prefixChain_antipode label hantipodal P i] at hsign
    simpa [NegativeAlternatingPrefixLabels, PositiveAlternatingPrefixLabels, SignedLabel.neg]
      using hsign
  · intro h
    refine ⟨(prefix_strictMono_antipode_iff label hantipodal P).mpr h.1, ?_⟩
    intro i
    have hsign := h.2 i
    rw [label_prefixChain_antipode label hantipodal P i]
    simp [SignedLabel.neg, hsign]

/-- Signed permutations whose prefix labels are positive-first alternating. -/
noncomputable def positiveAlternatingPrefixLabelChains {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Finset (SignedPermutation n) :=
  by
    classical
    exact Finset.univ.filter fun P => PositiveAlternatingPrefixLabels label P

/-- Signed permutations whose prefix labels are negative-first alternating. -/
noncomputable def negativeAlternatingPrefixLabelChains {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Finset (SignedPermutation n) :=
  by
    classical
    exact Finset.univ.filter fun P => NegativeAlternatingPrefixLabels label P

theorem positiveAlternatingPrefixLabelChains_card_eq_negative {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    (positiveAlternatingPrefixLabelChains label).card =
      (negativeAlternatingPrefixLabelChains label).card := by
  classical
  refine Finset.card_bij (fun P _ => SignedPermutation.antipode P) ?mem ?inj ?surj
  · intro P hP
    have hpos : PositiveAlternatingPrefixLabels label P := by
      simpa [positiveAlternatingPrefixLabelChains] using hP
    have hneg : NegativeAlternatingPrefixLabels label P.antipode := by
      have hiff := positiveAlternatingPrefixLabels_antipode_iff label hantipodal P.antipode
      have hpos' : PositiveAlternatingPrefixLabels label P.antipode.antipode := by
        simpa [SignedPermutation.antipode_involutive P] using hpos
      exact hiff.mp hpos'
    simpa [negativeAlternatingPrefixLabelChains] using hneg
  · intro P hP Q hQ hPQ
    have h := congrArg SignedPermutation.antipode hPQ
    simpa [SignedPermutation.antipode_involutive P, SignedPermutation.antipode_involutive Q] using h
  · intro Q hQ
    have hneg : NegativeAlternatingPrefixLabels label Q := by
      simpa [negativeAlternatingPrefixLabelChains] using hQ
    refine ⟨Q.antipode, ?_, ?_⟩
    · have hpos : PositiveAlternatingPrefixLabels label Q.antipode := by
        exact (positiveAlternatingPrefixLabels_antipode_iff label hantipodal Q).mpr hneg
      simpa [positiveAlternatingPrefixLabelChains] using hpos
    · exact SignedPermutation.antipode_involutive Q

/-- The explicit maximal-chain version of the Ky Fan frontier. -/
def KyFanPrefixChainStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        ∃ P : SignedPermutation n,
          StrictMono fun i => (label (P.prefixChain i)).index

theorem kyFanAlternatingChainStatement_of_prefix {n m : ℕ}
    (hprefix : KyFanPrefixChainStatement n m) :
    KyFanAlternatingChainStatement n m := by
  intro label hantipodal hno
  obtain ⟨P, hstrict⟩ := hprefix label hantipodal hno
  exact ⟨P.prefixChain, P.prefixChain_strictly_ordered, hstrict⟩

theorem tuckerLemmaStatement_of_kyFanPrefix {n : ℕ} (hn : 1 ≤ n)
    (hprefix : KyFanPrefixChainStatement n (n - 1)) :
    TuckerLemmaStatement n :=
  tuckerLemmaStatement_of_kyFan hn (kyFanAlternatingChainStatement_of_prefix hprefix)

/-- The Ky Fan signed-permutation parity frontier. -/
def KyFanPrefixParityStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Odd (positiveAlternatingPrefixLabelChains label).card

theorem kyFanPrefixChainStatement_of_parity {n m : ℕ}
    (hparity : KyFanPrefixParityStatement n m) :
    KyFanPrefixChainStatement n m := by
  intro label hantipodal hno
  have hodd := hparity label hantipodal hno
  have hpos : 0 < (positiveAlternatingPrefixLabelChains label).card := by
    rcases hodd with ⟨r, hr⟩
    omega
  obtain ⟨P, hP⟩ := Finset.card_pos.mp hpos
  exact ⟨P, (by
    have hP' : PositiveAlternatingPrefixLabels label P := by
      simpa [positiveAlternatingPrefixLabelChains] using hP
    exact hP'.1)⟩

theorem tuckerLemmaStatement_of_kyFanPrefixParity {n : ℕ} (hn : 1 ≤ n)
    (hparity : KyFanPrefixParityStatement n (n - 1)) :
    TuckerLemmaStatement n :=
  tuckerLemmaStatement_of_kyFanPrefix hn (kyFanPrefixChainStatement_of_parity hparity)

/-! ## Abstract path parity core -/

theorem even_card_of_fixedPointFree_involution {α : Type*} [Fintype α]
    (e : Equiv.Perm α) (he2 : e ^ 2 = 1) (hfree : ∀ x : α, e x ≠ x) :
    Even (Fintype.card α) := by
  classical
  have hsupp : e.support = Finset.univ := by
    ext x
    simp [Equiv.Perm.mem_support, hfree x]
  have htwo : 2 ∣ Fintype.card α := by
    simpa [hsupp] using Equiv.Perm.two_dvd_card_support (σ := e) he2
  exact even_iff_two_dvd.mpr htwo

theorem even_card_of_fixedPointFree_involutive {α : Type*} [Fintype α]
    (e : α ≃ α) (hinv : Function.Involutive e) (hfree : ∀ x : α, e x ≠ x) :
    Even (Fintype.card α) := by
  classical
  let p : Equiv.Perm α := e
  have hp2 : p ^ 2 = 1 := by
    ext x
    exact hinv x
  exact even_card_of_fixedPointFree_involution p hp2 hfree

/--
The numerical endpoint count used in the Ky Fan path proof.

If paths have two endpoints, the path set has a fixed-point-free antipodal
involution, and the endpoint set consists of the two `H₀` endpoints plus
equally many positive and negative top-dimensional endpoints, then the positive
top endpoints are odd.
-/
theorem odd_positive_endpoints_of_antipodal_path_count
    (positive negative pathCount : ℕ)
    (hneg : negative = positive)
    (hpath_even : Even pathCount)
    (hendpoints : 2 + positive + negative = 2 * pathCount) :
    Odd positive := by
  rcases hpath_even with ⟨r, hr⟩
  rw [Nat.odd_iff]
  omega

/--
Finite-type version of `odd_positive_endpoints_of_antipodal_path_count`.

The hypothesis `hendpoints` is the formal place where a later instantiation
supplies the graph-local facts: every path component has exactly two endpoints,
and the endpoint components are precisely the two `H₀` endpoints plus the
positive and negative top alternating simplices.
-/
theorem odd_card_positive_endpoints_of_path_involution
    {Path Positive Negative : Type*}
    [Fintype Path] [Fintype Positive] [Fintype Negative]
    (pathAntipode : Path ≃ Path)
    (hinv : Function.Involutive pathAntipode)
    (hfree : ∀ p : Path, pathAntipode p ≠ p)
    (hneg : Fintype.card Negative = Fintype.card Positive)
    (hendpoints :
      2 + Fintype.card Positive + Fintype.card Negative = 2 * Fintype.card Path) :
    Odd (Fintype.card Positive) := by
  exact odd_positive_endpoints_of_antipodal_path_count
    (Fintype.card Positive) (Fintype.card Negative) (Fintype.card Path)
    hneg (even_card_of_fixedPointFree_involutive pathAntipode hinv hfree) hendpoints

/--
Ky Fan prefix parity from a Prescott-Su/Fan path decomposition count.

This theorem is deliberately phrased so Chapter 39 can instantiate only the
remaining local geometry: construct the path type for the octahedral flag and
prove its endpoint count.  The antipodal pairing of positive and negative top
endpoints is already the signed-permutation antipode proved above.
-/
theorem kyFanPrefixParity_of_path_endpoint_count {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    {Path : Type*} [Fintype Path]
    (pathAntipode : Path ≃ Path)
    (hinv : Function.Involutive pathAntipode)
    (hfree : ∀ p : Path, pathAntipode p ≠ p)
    (hendpoints :
      2 + (positiveAlternatingPrefixLabelChains label).card +
          (negativeAlternatingPrefixLabelChains label).card =
        2 * Fintype.card Path) :
    Odd (positiveAlternatingPrefixLabelChains label).card := by
  exact odd_positive_endpoints_of_antipodal_path_count
    (positiveAlternatingPrefixLabelChains label).card
    (negativeAlternatingPrefixLabelChains label).card
    (Fintype.card Path)
    (positiveAlternatingPrefixLabelChains_card_eq_negative label hantipodal).symm
    (even_card_of_fixedPointFree_involutive pathAntipode hinv hfree)
    hendpoints

end ProofsInTheBook.TuckerLemmaCore
