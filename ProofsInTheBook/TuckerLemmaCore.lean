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

theorem support_card {n : ℕ} (X : SignedSubset n) :
    X.support.card = X.card := by
  simp [support, card, Finset.card_union_of_disjoint X.disjoint]

theorem nonzero_iff_card_pos {n : ℕ} (X : SignedSubset n) :
    X.Nonzero ↔ 0 < X.card := by
  constructor
  · exact card_pos_of_nonzero
  · intro hcard
    have hsupp : 0 < X.support.card := by
      simpa [support_card] using hcard
    exact (support_nonempty_iff_nonzero X).mp (Finset.card_pos.mp hsupp)

theorem card_eq_zero_iff_not_nonzero {n : ℕ} (X : SignedSubset n) :
    X.card = 0 ↔ ¬ X.Nonzero := by
  rw [nonzero_iff_card_pos]
  omega

theorem card_le_univ {n : ℕ} (X : SignedSubset n) :
    X.card ≤ n := by
  have hle : X.support.card ≤ Fintype.card (Fin n) := X.support.card_le_univ
  rwa [support_card, Fintype.card_fin] at hle

/-- The largest coordinate in the support of a nonzero sign vector. -/
noncomputable def maxSupport {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) : Fin n :=
  X.support.max' ((support_nonempty_iff_nonzero X).mpr hX)

theorem maxSupport_mem_support {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) :
    X.maxSupport hX ∈ X.support := by
  exact Finset.max'_mem _ _

theorem maxSupport_le_of_support_subset {n : ℕ} {X Y : SignedSubset n}
    (hX : X.Nonzero) (hY : Y.Nonzero) (hsub : X.support ⊆ Y.support) :
    X.maxSupport hX ≤ Y.maxSupport hY := by
  exact Finset.le_max' _ _ (hsub (maxSupport_mem_support X hX))

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

theorem le_refl {n : ℕ} (X : SignedSubset n) : Le X X :=
  ⟨fun _ hi => hi, fun _ hi => hi⟩

theorem le_trans {n : ℕ} {X Y Z : SignedSubset n} (hXY : Le X Y) (hYZ : Le Y Z) :
    Le X Z :=
  ⟨fun _ hi => hYZ.1 (hXY.1 hi), fun _ hi => hYZ.2 (hXY.2 hi)⟩

theorem le_antisymm {n : ℕ} {X Y : SignedSubset n} (hXY : Le X Y) (hYX : Le Y X) :
    X = Y := by
  have hpos : X.pos = Y.pos := Finset.Subset.antisymm hXY.1 hYX.1
  have hneg : X.neg = Y.neg := Finset.Subset.antisymm hXY.2 hYX.2
  cases X with
  | mk xpos xneg xdisj =>
      cases Y with
      | mk ypos yneg ydisj =>
          dsimp at hpos hneg
          subst ypos
          subst yneg
          simp

theorem ext_pos_neg {n : ℕ} {X Y : SignedSubset n}
    (hpos : X.pos = Y.pos) (hneg : X.neg = Y.neg) : X = Y := by
  cases X with
  | mk xpos xneg xdisj =>
      cases Y with
      | mk ypos yneg ydisj =>
          dsimp at hpos hneg
          subst ypos
          subst yneg
          simp

theorem antipode_le_antipode_iff {n : ℕ} {X Y : SignedSubset n} :
    Le X.antipode Y.antipode ↔ Le X Y := by
  simp [Le, antipode, and_comm]

theorem support_subset_of_le {n : ℕ} {X Y : SignedSubset n} (hXY : Le X Y) :
    X.support ⊆ Y.support := by
  intro i hi
  rcases Finset.mem_union.mp hi with hpos | hneg
  · exact Finset.mem_union_left _ (hXY.1 hpos)
  · exact Finset.mem_union_right _ (hXY.2 hneg)

theorem nonzero_of_le {n : ℕ} {X Y : SignedSubset n} (hXY : Le X Y)
    (hX : X.Nonzero) : Y.Nonzero := by
  have hxne : X.support.Nonempty := (support_nonempty_iff_nonzero X).mpr hX
  exact (support_nonempty_iff_nonzero Y).mp (hxne.mono (support_subset_of_le hXY))

theorem maxSupport_le_of_le {n : ℕ} {X Y : SignedSubset n}
    (hX : X.Nonzero) (hY : Y.Nonzero) (hXY : Le X Y) :
    X.maxSupport hX ≤ Y.maxSupport hY :=
  maxSupport_le_of_support_subset hX hY (support_subset_of_le hXY)

theorem maxSupport_le_of_le' {n : ℕ} {X Y : SignedSubset n}
    (hX : X.Nonzero) (hXY : Le X Y) :
    X.maxSupport hX ≤ Y.maxSupport (nonzero_of_le hXY hX) :=
  maxSupport_le_of_le hX (nonzero_of_le hXY hX) hXY

theorem maxSupportPositive_eq_of_le_of_maxSupport_eq {n : ℕ} {X Y : SignedSubset n}
    (hX : X.Nonzero) (hY : Y.Nonzero) (hXY : Le X Y)
    (hmax : X.maxSupport hX = Y.maxSupport hY) :
    X.maxSupportPositive hX = Y.maxSupportPositive hY := by
  unfold maxSupportPositive
  by_cases hxpos : X.maxSupport hX ∈ X.pos
  · have hypos : Y.maxSupport hY ∈ Y.pos := by
      rw [← hmax]
      exact hXY.1 hxpos
    simp [hxpos, hypos]
  · have hypos : Y.maxSupport hY ∉ Y.pos := by
      intro hypos
      have hxmem := X.maxSupport_mem_support hX
      rcases Finset.mem_union.mp hxmem with hxpos' | hxneg
      · exact hxpos hxpos'
      · have hyneg : Y.maxSupport hY ∈ Y.neg := by
          rw [← hmax]
          exact hXY.2 hxneg
        exact (Finset.disjoint_left.mp Y.disjoint) hypos hyneg
    simp [hxpos, hypos]

theorem card_le_card_of_le {n : ℕ} {X Y : SignedSubset n} (hXY : Le X Y) :
    X.card ≤ Y.card := by
  have hpos_le : X.pos.card ≤ Y.pos.card := Finset.card_le_card hXY.1
  have hneg_le : X.neg.card ≤ Y.neg.card := Finset.card_le_card hXY.2
  simp [card]
  omega

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

theorem support_ssubset_of_le_ne {n : ℕ} {X Y : SignedSubset n}
    (hXY : Le X Y) (hne : X ≠ Y) : X.support ⊂ Y.support := by
  refine ssubset_iff_subset_ne.mpr ⟨support_subset_of_le hXY, ?_⟩
  intro hsupport
  apply hne
  apply eq_of_le_card_eq hXY
  rw [← support_card X, hsupport, support_card Y]

theorem card_lt_card_of_le_ne {n : ℕ} {X Y : SignedSubset n}
    (hXY : Le X Y) (hne : X ≠ Y) : X.card < Y.card := by
  have hsupp := support_ssubset_of_le_ne hXY hne
  simpa [support_card] using Finset.card_lt_card hsupp

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

/-- Face inclusion order restricted to nonzero sign vectors. -/
def Le {n : ℕ} (X Y : NonzeroSignedSubset n) : Prop :=
  SignedSubset.Le X.1 Y.1

theorem le_refl {n : ℕ} (X : NonzeroSignedSubset n) : Le X X :=
  SignedSubset.le_refl X.1

theorem le_trans {n : ℕ} {X Y Z : NonzeroSignedSubset n} (hXY : Le X Y) (hYZ : Le Y Z) :
    Le X Z :=
  SignedSubset.le_trans hXY hYZ

theorem le_antisymm {n : ℕ} {X Y : NonzeroSignedSubset n} (hXY : Le X Y) (hYX : Le Y X) :
    X = Y := by
  exact Subtype.ext (SignedSubset.le_antisymm hXY hYX)

theorem antipode_le_antipode_iff {n : ℕ} {X Y : NonzeroSignedSubset n} :
    Le X.antipode Y.antipode ↔ Le X Y :=
  SignedSubset.antipode_le_antipode_iff

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

theorem neg_involutive {m : ℕ} : Function.Involutive (@neg m) := by
  intro L
  cases L
  simp [neg]

theorem neg_ne_self {m : ℕ} (L : SignedLabel m) : L.neg ≠ L := by
  intro h
  have hpositive := congrArg SignedLabel.positive h
  cases L.positive <;> simp [neg] at hpositive

theorem neg_injective {m : ℕ} : Function.Injective (@neg m) := by
  intro L M h
  have h' := congrArg (@neg m) h
  simpa [neg_involutive L, neg_involutive M] using h'

theorem neg_eq_neg_iff {m : ℕ} {L M : SignedLabel m} :
    L.neg = M.neg ↔ L = M :=
  ⟨fun h => neg_injective h, fun h => by rw [h]⟩

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

theorem label_eq_of_le_of_same_index_of_no_complement {n m : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    {X Y : NonzeroSignedSubset n}
    (hXY : SignedSubset.Le X.1 Y.1)
    (hindex : (label X).index = (label Y).index) :
    label X = label Y := by
  exact SignedLabel.ext
    (positive_eq_of_le_of_same_index_of_no_complement hno hXY hindex)
    hindex

theorem index_ne_of_le_of_positive_ne_of_no_complement {n m : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    {X Y : NonzeroSignedSubset n}
    (hXY : SignedSubset.Le X.1 Y.1)
    (hpositive : (label X).positive ≠ (label Y).positive) :
    (label X).index ≠ (label Y).index := by
  intro hindex
  exact hpositive
    (positive_eq_of_le_of_same_index_of_no_complement hno hXY hindex)

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

theorem not_strictMono_fin_of_lt {n m : ℕ} (hmn : m < n) :
    ¬ ∃ f : Fin n → Fin m, StrictMono f := by
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

theorem ext_order_positive {n : ℕ} {P Q : SignedPermutation n}
    (horder : P.order = Q.order) (hpositive : P.positive = Q.positive) : P = Q := by
  cases P with
  | mk porder ppositive =>
      cases Q with
      | mk qorder qpositive =>
          dsimp at horder hpositive
          subst qorder
          subst qpositive
          rfl

theorem card_zero : Fintype.card (SignedPermutation 0) = 1 := by
  calc
    Fintype.card (SignedPermutation 0) =
        Fintype.card (Equiv.Perm (Fin 0) × (Fin 0 → Bool)) :=
      Fintype.card_congr (signedPermutationEquiv 0)
    _ = 1 := by
      simp

theorem card_one : Fintype.card (SignedPermutation 1) = 2 := by
  calc
    Fintype.card (SignedPermutation 1) =
        Fintype.card (Equiv.Perm (Fin 1) × (Fin 1 → Bool)) :=
      Fintype.card_congr (signedPermutationEquiv 1)
    _ = 2 := by
      simp

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

theorem prefixChain_card_strictMono {n : ℕ} (P : SignedPermutation n) :
    StrictMono fun i : Fin n => (P.prefixChain i).1.card := by
  intro i j hij
  exact P.prefixChain_card_lt_of_lt hij

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

theorem prefixChain_le_iff {n : ℕ} (P : SignedPermutation n) {i j : Fin n} :
    SignedSubset.Le (P.prefixChain i).1 (P.prefixChain j).1 ↔ i ≤ j := by
  constructor
  · intro hle
    have hcard := SignedSubset.card_le_card_of_le hle
    rw [P.prefixChain_card i, P.prefixChain_card j] at hcard
    exact Fin.le_iff_val_le_val.mpr (by omega)
  · intro hij
    exact P.prefixChain_le hij

theorem prefixChain_eq_iff {n : ℕ} (P : SignedPermutation n) {i j : Fin n} :
    P.prefixChain i = P.prefixChain j ↔ i = j := by
  constructor
  · intro h
    exact P.prefixChain_injective h
  · intro h
    rw [h]

theorem prefixChain_le_and_ne_iff_lt {n : ℕ} (P : SignedPermutation n) {i j : Fin n} :
    SignedSubset.Le (P.prefixChain i).1 (P.prefixChain j).1 ∧
        P.prefixChain i ≠ P.prefixChain j ↔
      i < j := by
  constructor
  · rintro ⟨hle, hne⟩
    have hij : i ≤ j := (P.prefixChain_le_iff).mp hle
    have hij_ne : i ≠ j := by
      intro h
      exact hne ((P.prefixChain_eq_iff).mpr h)
    exact lt_of_le_of_ne hij hij_ne
  · intro hij
    exact ⟨P.prefixChain_le hij.le, P.prefixChain_ne_of_lt hij⟩

/-- Reindex the positions of a signed permutation, moving the signed atoms
together.  If `τ` swaps two adjacent positions, this is the other maximal chain
through the punctured flag which omits one of those two positions. -/
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

theorem antipode_reindexPositions {n : ℕ}
    (P : SignedPermutation n) (τ : Equiv.Perm (Fin n)) :
    (P.reindexPositions τ).antipode = P.antipode.reindexPositions τ := by
  apply ext_order_positive
  · rfl
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

/-- The successor of a non-last gap, as an element of the same `Fin` type. -/
def gapNext {n : ℕ} (gap : Fin (n + 1)) (hgap : gap.val < n) : Fin (n + 1) :=
  ⟨gap.val + 1, by omega⟩

theorem gapNext_val {n : ℕ} (gap : Fin (n + 1)) (hgap : gap.val < n) :
    (gapNext gap hgap).val = gap.val + 1 :=
  rfl

theorem reindexPositions_swap_gap_involutive {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n) :
    ((P.reindexPositions (Equiv.swap gap (gapNext gap hgap))).reindexPositions
        (Equiv.swap gap (gapNext gap hgap))) = P := by
  exact P.reindexPositions_swap_involutive gap (gapNext gap hgap)

theorem reindexPositions_swap_gap_ne_self {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n) :
    P.reindexPositions (Equiv.swap gap (gapNext gap hgap)) ≠ P := by
  apply P.reindexPositions_swap_ne_self
  intro h
  have hval := congrArg Fin.val h
  simp [gapNext] at hval

theorem reindexPositions_swap_gap_ne_antipode {n : ℕ}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n) :
    P.reindexPositions (Equiv.swap gap (gapNext gap hgap)) ≠ P.antipode := by
  intro h
  have horder := congrArg SignedPermutation.order h
  have hfun := congrArg (fun order : Equiv.Perm (Fin (n + 1)) => order gap) horder
  simp [reindexPositions, antipode] at hfun
  have hval := congrArg Fin.val hfun
  simp [gapNext] at hval

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

/-- Flip the sign of one position of a signed permutation, keeping the order. -/
def flipSignAt {n : ℕ} (P : SignedPermutation n) (j : Fin n) : SignedPermutation n where
  order := P.order
  positive := fun i => if i = j then !P.positive i else P.positive i

theorem flipSignAt_involutive {n : ℕ} (P : SignedPermutation n) (j : Fin n) :
    (P.flipSignAt j).flipSignAt j = P := by
  apply ext_order_positive
  · rfl
  · funext i
    by_cases hij : i = j <;> simp [flipSignAt, hij]

theorem antipode_flipSignAt {n : ℕ} (P : SignedPermutation n) (j : Fin n) :
    (P.flipSignAt j).antipode = P.antipode.flipSignAt j := by
  apply ext_order_positive
  · rfl
  · funext i
    by_cases hij : i = j <;> simp [antipode, flipSignAt, hij]

theorem flipSignAt_last_ne_antipode {n : ℕ} (hn : 0 < n)
    (P : SignedPermutation (n + 1)) :
    P.flipSignAt (Fin.last n) ≠ P.antipode := by
  intro h
  have hpositive := congrArg SignedPermutation.positive h
  let i : Fin (n + 1) := ⟨0, by omega⟩
  have hi : i ≠ Fin.last n := by
    intro hi
    have hval := congrArg Fin.val hi
    simp [i, Fin.last] at hval
    omega
  have hsign := congrFun hpositive i
  simp [flipSignAt, antipode, hi] at hsign

theorem flipSignAt_ne_self {n : ℕ} (P : SignedPermutation n) (j : Fin n) :
    P.flipSignAt j ≠ P := by
  intro h
  have hpositive := congrArg SignedPermutation.positive h
  have hj := congrFun hpositive j
  cases hsign : P.positive j <;> simp [flipSignAt, hsign] at hj

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
  exact SignedSubset.ext_pos_neg
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

theorem positiveAlternatingPrefixLabels_zero {m : ℕ}
    (label : NonzeroSignedSubset 0 → SignedLabel m) (P : SignedPermutation 0) :
    PositiveAlternatingPrefixLabels label P := by
  constructor
  · intro i _j _hij
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

theorem negativeAlternatingPrefixLabels_zero {m : ℕ}
    (label : NonzeroSignedSubset 0 → SignedLabel m) (P : SignedPermutation 0) :
    NegativeAlternatingPrefixLabels label P := by
  constructor
  · intro i _j _hij
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

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

/--
Positive-first alternating labels on the prefix chain of a signed permutation
after deleting one prefix position.  This is the codimension-one chain type used
by the Fan/Prescott-Su path graph.
-/
def PositiveAlternatingPuncturedPrefixLabels {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) : Prop :=
  (StrictMono fun i : Fin n => (label (P.prefixChain (gap.succAbove i))).index) ∧
    ∀ i : Fin n, (label (P.prefixChain (gap.succAbove i))).positive = decide (Even i.val)

/-- Negative-first version of `PositiveAlternatingPuncturedPrefixLabels`. -/
def NegativeAlternatingPuncturedPrefixLabels {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) : Prop :=
  (StrictMono fun i : Fin n => (label (P.prefixChain (gap.succAbove i))).index) ∧
    ∀ i : Fin n, (label (P.prefixChain (gap.succAbove i))).positive = !decide (Even i.val)

theorem punctured_prefix_strictMono_antipode_iff {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    (StrictMono fun i : Fin n =>
      (label (P.antipode.prefixChain (gap.succAbove i))).index) ↔
      StrictMono fun i : Fin n => (label (P.prefixChain (gap.succAbove i))).index := by
  simp [label_prefixChain_antipode label hantipodal P, SignedLabel.neg]

theorem positiveAlternatingPuncturedPrefixLabels_antipode_iff {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    PositiveAlternatingPuncturedPrefixLabels label P.antipode gap ↔
      NegativeAlternatingPuncturedPrefixLabels label P gap := by
  constructor
  · intro h
    refine ⟨(punctured_prefix_strictMono_antipode_iff label hantipodal P gap).mp h.1, ?_⟩
    intro i
    have hsign := h.2 i
    rw [label_prefixChain_antipode label hantipodal P (gap.succAbove i)] at hsign
    simpa [NegativeAlternatingPuncturedPrefixLabels, PositiveAlternatingPuncturedPrefixLabels,
      SignedLabel.neg] using hsign
  · intro h
    refine ⟨(punctured_prefix_strictMono_antipode_iff label hantipodal P gap).mpr h.1, ?_⟩
    intro i
    have hsign := h.2 i
    rw [label_prefixChain_antipode label hantipodal P (gap.succAbove i)]
    simp [SignedLabel.neg, hsign]

theorem positiveAlternatingPuncturedPrefixLabels_reindexPositions_swap_gap_iff {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n) :
    PositiveAlternatingPuncturedPrefixLabels label
        (P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap)))
        gap ↔
      PositiveAlternatingPuncturedPrefixLabels label P gap := by
  constructor
  · intro h
    constructor
    · intro i j hij
      have hmono := h.1 hij
      dsimp at hmono
      rw [P.prefixChain_reindexPositions_swap_gap_succAbove gap hgap i,
        P.prefixChain_reindexPositions_swap_gap_succAbove gap hgap j] at hmono
      exact hmono
    · intro i
      have hsign := h.2 i
      rw [P.prefixChain_reindexPositions_swap_gap_succAbove gap hgap i] at hsign
      exact hsign
  · intro h
    constructor
    · intro i j hij
      have hmono := h.1 hij
      dsimp
      rw [P.prefixChain_reindexPositions_swap_gap_succAbove gap hgap i,
        P.prefixChain_reindexPositions_swap_gap_succAbove gap hgap j]
      exact hmono
    · intro i
      have hsign := h.2 i
      rw [P.prefixChain_reindexPositions_swap_gap_succAbove gap hgap i]
      exact hsign

theorem negativeAlternatingPuncturedPrefixLabels_reindexPositions_swap_gap_iff {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n) :
    NegativeAlternatingPuncturedPrefixLabels label
        (P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap)))
        gap ↔
      NegativeAlternatingPuncturedPrefixLabels label P gap := by
  constructor
  · intro h
    constructor
    · intro i j hij
      have hmono := h.1 hij
      dsimp at hmono
      rw [P.prefixChain_reindexPositions_swap_gap_succAbove gap hgap i,
        P.prefixChain_reindexPositions_swap_gap_succAbove gap hgap j] at hmono
      exact hmono
    · intro i
      have hsign := h.2 i
      rw [P.prefixChain_reindexPositions_swap_gap_succAbove gap hgap i] at hsign
      exact hsign
  · intro h
    constructor
    · intro i j hij
      have hmono := h.1 hij
      dsimp
      rw [P.prefixChain_reindexPositions_swap_gap_succAbove gap hgap i,
        P.prefixChain_reindexPositions_swap_gap_succAbove gap hgap j]
      exact hmono
    · intro i
      have hsign := h.2 i
      rw [P.prefixChain_reindexPositions_swap_gap_succAbove gap hgap i]
      exact hsign

theorem positiveAlternatingPuncturedPrefixLabels_flipSignAt_last_iff {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (P : SignedPermutation (n + 1)) :
    PositiveAlternatingPuncturedPrefixLabels label (P.flipSignAt (Fin.last n)) (Fin.last n) ↔
      PositiveAlternatingPuncturedPrefixLabels label P (Fin.last n) := by
  constructor
  · intro h
    constructor
    · intro i j hij
      have hmono := h.1 hij
      have hi :
          (P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove i) =
            P.prefixChain ((Fin.last n).succAbove i) :=
        P.prefixChain_flipSignAt_last_succAbove i
      have hj :
          (P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove j) =
            P.prefixChain ((Fin.last n).succAbove j) :=
        P.prefixChain_flipSignAt_last_succAbove j
      change (label ((P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove i))).index <
        (label ((P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove j))).index at hmono
      rw [hi, hj] at hmono
      exact hmono
    · intro i
      have hsign := h.2 i
      have hi :
          (P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove i) =
            P.prefixChain ((Fin.last n).succAbove i) :=
        P.prefixChain_flipSignAt_last_succAbove i
      rw [hi] at hsign
      exact hsign
  · intro h
    constructor
    · intro i j hij
      have hmono := h.1 hij
      have hi :
          (P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove i) =
            P.prefixChain ((Fin.last n).succAbove i) :=
        P.prefixChain_flipSignAt_last_succAbove i
      have hj :
          (P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove j) =
            P.prefixChain ((Fin.last n).succAbove j) :=
        P.prefixChain_flipSignAt_last_succAbove j
      change (label ((P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove i))).index <
        (label ((P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove j))).index
      rw [hi, hj]
      exact hmono
    · intro i
      have hsign := h.2 i
      have hi :
          (P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove i) =
            P.prefixChain ((Fin.last n).succAbove i) :=
        P.prefixChain_flipSignAt_last_succAbove i
      rw [hi]
      exact hsign

theorem negativeAlternatingPuncturedPrefixLabels_flipSignAt_last_iff {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (P : SignedPermutation (n + 1)) :
    NegativeAlternatingPuncturedPrefixLabels label (P.flipSignAt (Fin.last n)) (Fin.last n) ↔
      NegativeAlternatingPuncturedPrefixLabels label P (Fin.last n) := by
  constructor
  · intro h
    constructor
    · intro i j hij
      have hmono := h.1 hij
      have hi :
          (P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove i) =
            P.prefixChain ((Fin.last n).succAbove i) :=
        P.prefixChain_flipSignAt_last_succAbove i
      have hj :
          (P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove j) =
            P.prefixChain ((Fin.last n).succAbove j) :=
        P.prefixChain_flipSignAt_last_succAbove j
      change (label ((P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove i))).index <
        (label ((P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove j))).index at hmono
      rw [hi, hj] at hmono
      exact hmono
    · intro i
      have hsign := h.2 i
      have hi :
          (P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove i) =
            P.prefixChain ((Fin.last n).succAbove i) :=
        P.prefixChain_flipSignAt_last_succAbove i
      rw [hi] at hsign
      exact hsign
  · intro h
    constructor
    · intro i j hij
      have hmono := h.1 hij
      have hi :
          (P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove i) =
            P.prefixChain ((Fin.last n).succAbove i) :=
        P.prefixChain_flipSignAt_last_succAbove i
      have hj :
          (P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove j) =
            P.prefixChain ((Fin.last n).succAbove j) :=
        P.prefixChain_flipSignAt_last_succAbove j
      change (label ((P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove i))).index <
        (label ((P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove j))).index
      rw [hi, hj]
      exact hmono
    · intro i
      have hsign := h.2 i
      have hi :
          (P.flipSignAt (Fin.last n)).prefixChain ((Fin.last n).succAbove i) =
            P.prefixChain ((Fin.last n).succAbove i) :=
        P.prefixChain_flipSignAt_last_succAbove i
      rw [hi]
      exact hsign

theorem positiveAlternatingPrefixLabels_punctured_last {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {P : SignedPermutation (n + 1)}
    (h : PositiveAlternatingPrefixLabels label P) :
    PositiveAlternatingPuncturedPrefixLabels label P (Fin.last n) := by
  constructor
  · intro i j hij
    have hcast : (Fin.castSucc i : Fin (n + 1)) < Fin.castSucc j := by
      exact Fin.castSucc_lt_castSucc_iff.mpr hij
    simpa [Fin.succAbove_last] using h.1 hcast
  · intro i
    have hsign := h.2 (Fin.castSucc i)
    simpa [Fin.succAbove_last] using hsign

theorem negativeAlternatingPrefixLabels_punctured_last {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {P : SignedPermutation (n + 1)}
    (h : NegativeAlternatingPrefixLabels label P) :
    NegativeAlternatingPuncturedPrefixLabels label P (Fin.last n) := by
  constructor
  · intro i j hij
    have hcast : (Fin.castSucc i : Fin (n + 1)) < Fin.castSucc j := by
      exact Fin.castSucc_lt_castSucc_iff.mpr hij
    simpa [Fin.succAbove_last] using h.1 hcast
  · intro i
    have hsign := h.2 (Fin.castSucc i)
    simpa [Fin.succAbove_last] using hsign

theorem positiveAlternatingPrefixLabels_punctured_zero {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {P : SignedPermutation (n + 1)}
    (h : PositiveAlternatingPrefixLabels label P) :
    NegativeAlternatingPuncturedPrefixLabels label P 0 := by
  constructor
  · intro i j hij
    have hsucc : (Fin.succ i : Fin (n + 1)) < Fin.succ j := by
      exact Fin.succ_lt_succ_iff.mpr hij
    simpa [Fin.succAbove_zero] using h.1 hsucc
  · intro i
    calc
      (label (P.prefixChain ((0 : Fin (n + 1)).succAbove i))).positive =
          decide (Even (Fin.succ i).val) := by
        simpa [Fin.succAbove_zero] using h.2 (Fin.succ i)
      _ = !decide (Even i.val) := by
        by_cases hi : Even i.val
        · simp [Fin.val_succ, Nat.even_add_one, hi]
        · simp [Fin.val_succ, Nat.even_add_one, hi]

theorem negativeAlternatingPrefixLabels_punctured_zero {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {P : SignedPermutation (n + 1)}
    (h : NegativeAlternatingPrefixLabels label P) :
    PositiveAlternatingPuncturedPrefixLabels label P 0 := by
  constructor
  · intro i j hij
    have hsucc : (Fin.succ i : Fin (n + 1)) < Fin.succ j := by
      exact Fin.succ_lt_succ_iff.mpr hij
    simpa [Fin.succAbove_zero] using h.1 hsucc
  · intro i
    calc
      (label (P.prefixChain ((0 : Fin (n + 1)).succAbove i))).positive =
          !decide (Even (Fin.succ i).val) := by
        simpa [Fin.succAbove_zero] using h.2 (Fin.succ i)
      _ = decide (Even i.val) := by
        by_cases hi : Even i.val
        · simp [Fin.val_succ, Nat.even_add_one, hi]
        · simp [Fin.val_succ, Nat.even_add_one, hi]

def puncturedPrefixAntipode {n : ℕ} :
    SignedPermutation (n + 1) × Fin (n + 1) ≃ SignedPermutation (n + 1) × Fin (n + 1) where
  toFun data := (data.1.antipode, data.2)
  invFun data := (data.1.antipode, data.2)
  left_inv := by
    intro data
    cases data with
    | mk P gap =>
        simp [SignedPermutation.antipode_involutive P]
  right_inv := by
    intro data
    cases data with
    | mk P gap =>
        simp [SignedPermutation.antipode_involutive P]

def puncturedPrefixPartnerData {n : ℕ}
    (data : SignedPermutation (n + 1) × Fin (n + 1)) :
    SignedPermutation (n + 1) × Fin (n + 1) :=
  if hgap : data.2.val < n then
    (data.1.reindexPositions (Equiv.swap data.2 (SignedPermutation.gapNext data.2 hgap)),
      data.2)
  else
    (data.1.flipSignAt (Fin.last n), Fin.last n)

theorem puncturedPrefixPartnerData_antipode {n : ℕ}
    (data : SignedPermutation (n + 1) × Fin (n + 1)) :
    puncturedPrefixPartnerData (puncturedPrefixAntipode data) =
      puncturedPrefixAntipode (puncturedPrefixPartnerData data) := by
  rcases data with ⟨P, gap⟩
  by_cases hgap : gap.val < n
  · simp [puncturedPrefixPartnerData, puncturedPrefixAntipode, hgap,
      SignedPermutation.antipode_reindexPositions]
  · simp [puncturedPrefixPartnerData, puncturedPrefixAntipode, hgap,
      SignedPermutation.antipode_flipSignAt]

theorem puncturedPrefixPartnerData_ne_antipode {n : ℕ} (hn : 0 < n)
    (data : SignedPermutation (n + 1) × Fin (n + 1)) :
    puncturedPrefixPartnerData data ≠ puncturedPrefixAntipode data := by
  rcases data with ⟨P, gap⟩
  by_cases hgap : gap.val < n
  · intro h
    have hP := congrArg Prod.fst h
    exact SignedPermutation.reindexPositions_swap_gap_ne_antipode P gap hgap
      (by simpa [puncturedPrefixPartnerData, puncturedPrefixAntipode, hgap] using hP)
  · have hlast : gap = Fin.last n := by
      apply Fin.ext
      have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
      simp [Fin.last]
      omega
    intro h
    have hP := congrArg Prod.fst h
    exact SignedPermutation.flipSignAt_last_ne_antipode hn P
      (by simpa [puncturedPrefixPartnerData, puncturedPrefixAntipode, hgap, hlast] using hP)

noncomputable def positiveAlternatingPuncturedPrefixLabelChains {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Finset (SignedPermutation (n + 1) × Fin (n + 1)) :=
  by
    classical
    exact Finset.univ.filter fun data =>
      PositiveAlternatingPuncturedPrefixLabels label data.1 data.2

noncomputable def negativeAlternatingPuncturedPrefixLabelChains {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Finset (SignedPermutation (n + 1) × Fin (n + 1)) :=
  by
    classical
    exact Finset.univ.filter fun data =>
      NegativeAlternatingPuncturedPrefixLabels label data.1 data.2

theorem mem_positiveAlternatingPuncturedPrefixLabelChains_iff {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {data : SignedPermutation (n + 1) × Fin (n + 1)} :
    data ∈ positiveAlternatingPuncturedPrefixLabelChains label ↔
      PositiveAlternatingPuncturedPrefixLabels label data.1 data.2 := by
  simp [positiveAlternatingPuncturedPrefixLabelChains]

theorem mem_negativeAlternatingPuncturedPrefixLabelChains_iff {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {data : SignedPermutation (n + 1) × Fin (n + 1)} :
    data ∈ negativeAlternatingPuncturedPrefixLabelChains label ↔
      NegativeAlternatingPuncturedPrefixLabels label data.1 data.2 := by
  simp [negativeAlternatingPuncturedPrefixLabelChains]

theorem mem_positiveAlternatingPuncturedPrefixLabelChains_reindexPositions_swap_gap_iff
    {n m : ℕ} {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n) :
    (P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap)), gap) ∈
        positiveAlternatingPuncturedPrefixLabelChains label ↔
      (P, gap) ∈ positiveAlternatingPuncturedPrefixLabelChains label := by
  rw [mem_positiveAlternatingPuncturedPrefixLabelChains_iff,
    mem_positiveAlternatingPuncturedPrefixLabelChains_iff]
  exact positiveAlternatingPuncturedPrefixLabels_reindexPositions_swap_gap_iff
    label P gap hgap

theorem mem_negativeAlternatingPuncturedPrefixLabelChains_reindexPositions_swap_gap_iff
    {n m : ℕ} {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) (hgap : gap.val < n) :
    (P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap)), gap) ∈
        negativeAlternatingPuncturedPrefixLabelChains label ↔
      (P, gap) ∈ negativeAlternatingPuncturedPrefixLabelChains label := by
  rw [mem_negativeAlternatingPuncturedPrefixLabelChains_iff,
    mem_negativeAlternatingPuncturedPrefixLabelChains_iff]
  exact negativeAlternatingPuncturedPrefixLabels_reindexPositions_swap_gap_iff
    label P gap hgap

theorem mem_positiveAlternatingPuncturedPrefixLabelChains_flipSignAt_last_iff
    {n m : ℕ} {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (P : SignedPermutation (n + 1)) :
    (P.flipSignAt (Fin.last n), Fin.last n) ∈
        positiveAlternatingPuncturedPrefixLabelChains label ↔
      (P, Fin.last n) ∈ positiveAlternatingPuncturedPrefixLabelChains label := by
  rw [mem_positiveAlternatingPuncturedPrefixLabelChains_iff,
    mem_positiveAlternatingPuncturedPrefixLabelChains_iff]
  exact positiveAlternatingPuncturedPrefixLabels_flipSignAt_last_iff label P

theorem mem_negativeAlternatingPuncturedPrefixLabelChains_flipSignAt_last_iff
    {n m : ℕ} {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (P : SignedPermutation (n + 1)) :
    (P.flipSignAt (Fin.last n), Fin.last n) ∈
        negativeAlternatingPuncturedPrefixLabelChains label ↔
      (P, Fin.last n) ∈ negativeAlternatingPuncturedPrefixLabelChains label := by
  rw [mem_negativeAlternatingPuncturedPrefixLabelChains_iff,
    mem_negativeAlternatingPuncturedPrefixLabelChains_iff]
  exact negativeAlternatingPuncturedPrefixLabels_flipSignAt_last_iff label P

abbrev PositiveNonlastPuncturedPrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :=
  {data : SignedPermutation (n + 1) × Fin (n + 1) //
    data ∈ positiveAlternatingPuncturedPrefixLabelChains label ∧ data.2.val < n}

abbrev NegativeNonlastPuncturedPrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :=
  {data : SignedPermutation (n + 1) × Fin (n + 1) //
    data ∈ negativeAlternatingPuncturedPrefixLabelChains label ∧ data.2.val < n}

noncomputable def positiveNonlastPuncturedPrefixChainSwap {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    PositiveNonlastPuncturedPrefixChainType label ≃
      PositiveNonlastPuncturedPrefixChainType label where
  toFun := fun data => by
    refine
      ⟨(data.1.1.reindexPositions
          (Equiv.swap data.1.2 (SignedPermutation.gapNext data.1.2 data.2.2)), data.1.2), ?_⟩
    exact ⟨(mem_positiveAlternatingPuncturedPrefixLabelChains_reindexPositions_swap_gap_iff
      data.1.1 data.1.2 data.2.2).2 data.2.1, data.2.2⟩
  invFun := fun data => by
    refine
      ⟨(data.1.1.reindexPositions
          (Equiv.swap data.1.2 (SignedPermutation.gapNext data.1.2 data.2.2)), data.1.2), ?_⟩
    exact ⟨(mem_positiveAlternatingPuncturedPrefixLabelChains_reindexPositions_swap_gap_iff
      data.1.1 data.1.2 data.2.2).2 data.2.1, data.2.2⟩
  left_inv := by
    rintro ⟨⟨P, gap⟩, hmem, hgap⟩
    apply Subtype.ext
    apply Prod.ext
    · exact SignedPermutation.reindexPositions_swap_involutive P gap
        (SignedPermutation.gapNext gap hgap)
    · rfl
  right_inv := by
    rintro ⟨⟨P, gap⟩, hmem, hgap⟩
    apply Subtype.ext
    apply Prod.ext
    · exact SignedPermutation.reindexPositions_swap_involutive P gap
        (SignedPermutation.gapNext gap hgap)
    · rfl

theorem positiveNonlastPuncturedPrefixChainSwap_involutive {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Function.Involutive (positiveNonlastPuncturedPrefixChainSwap label) := by
  intro data
  exact (positiveNonlastPuncturedPrefixChainSwap label).left_inv data

theorem positiveNonlastPuncturedPrefixChainSwap_fixedPointFree {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (data : PositiveNonlastPuncturedPrefixChainType label) :
    positiveNonlastPuncturedPrefixChainSwap label data ≠ data := by
  intro h
  rcases data with ⟨⟨P, gap⟩, hmem, hgap⟩
  have hP := congrArg (fun data : PositiveNonlastPuncturedPrefixChainType label => data.1.1) h
  have hP' :
      P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap)) = P := by
    simpa [positiveNonlastPuncturedPrefixChainSwap] using hP
  exact SignedPermutation.reindexPositions_swap_gap_ne_self P gap hgap hP'

noncomputable def negativeNonlastPuncturedPrefixChainSwap {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    NegativeNonlastPuncturedPrefixChainType label ≃
      NegativeNonlastPuncturedPrefixChainType label where
  toFun := fun data => by
    refine
      ⟨(data.1.1.reindexPositions
          (Equiv.swap data.1.2 (SignedPermutation.gapNext data.1.2 data.2.2)), data.1.2), ?_⟩
    exact ⟨(mem_negativeAlternatingPuncturedPrefixLabelChains_reindexPositions_swap_gap_iff
      data.1.1 data.1.2 data.2.2).2 data.2.1, data.2.2⟩
  invFun := fun data => by
    refine
      ⟨(data.1.1.reindexPositions
          (Equiv.swap data.1.2 (SignedPermutation.gapNext data.1.2 data.2.2)), data.1.2), ?_⟩
    exact ⟨(mem_negativeAlternatingPuncturedPrefixLabelChains_reindexPositions_swap_gap_iff
      data.1.1 data.1.2 data.2.2).2 data.2.1, data.2.2⟩
  left_inv := by
    rintro ⟨⟨P, gap⟩, hmem, hgap⟩
    apply Subtype.ext
    apply Prod.ext
    · exact SignedPermutation.reindexPositions_swap_involutive P gap
        (SignedPermutation.gapNext gap hgap)
    · rfl
  right_inv := by
    rintro ⟨⟨P, gap⟩, hmem, hgap⟩
    apply Subtype.ext
    apply Prod.ext
    · exact SignedPermutation.reindexPositions_swap_involutive P gap
        (SignedPermutation.gapNext gap hgap)
    · rfl

theorem negativeNonlastPuncturedPrefixChainSwap_involutive {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Function.Involutive (negativeNonlastPuncturedPrefixChainSwap label) := by
  intro data
  exact (negativeNonlastPuncturedPrefixChainSwap label).left_inv data

theorem negativeNonlastPuncturedPrefixChainSwap_fixedPointFree {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (data : NegativeNonlastPuncturedPrefixChainType label) :
    negativeNonlastPuncturedPrefixChainSwap label data ≠ data := by
  intro h
  rcases data with ⟨⟨P, gap⟩, hmem, hgap⟩
  have hP := congrArg (fun data : NegativeNonlastPuncturedPrefixChainType label => data.1.1) h
  have hP' :
      P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap)) = P := by
    simpa [negativeNonlastPuncturedPrefixChainSwap] using hP
  exact SignedPermutation.reindexPositions_swap_gap_ne_self P gap hgap hP'

abbrev PositiveLastPuncturedPrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :=
  {P : SignedPermutation (n + 1) //
    (P, Fin.last n) ∈ positiveAlternatingPuncturedPrefixLabelChains label}

abbrev NegativeLastPuncturedPrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :=
  {P : SignedPermutation (n + 1) //
    (P, Fin.last n) ∈ negativeAlternatingPuncturedPrefixLabelChains label}

abbrev PositivePuncturedPrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :=
  {data : SignedPermutation (n + 1) × Fin (n + 1) //
    data ∈ positiveAlternatingPuncturedPrefixLabelChains label}

abbrev NegativePuncturedPrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :=
  {data : SignedPermutation (n + 1) × Fin (n + 1) //
    data ∈ negativeAlternatingPuncturedPrefixLabelChains label}

noncomputable def positiveLastPuncturedPrefixChainFlip {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    PositiveLastPuncturedPrefixChainType label ≃ PositiveLastPuncturedPrefixChainType label where
  toFun := fun data => by
    refine ⟨data.1.flipSignAt (Fin.last n), ?_⟩
    exact (mem_positiveAlternatingPuncturedPrefixLabelChains_flipSignAt_last_iff data.1).2 data.2
  invFun := fun data => by
    refine ⟨data.1.flipSignAt (Fin.last n), ?_⟩
    exact (mem_positiveAlternatingPuncturedPrefixLabelChains_flipSignAt_last_iff data.1).2 data.2
  left_inv := by
    rintro ⟨P, hP⟩
    apply Subtype.ext
    exact SignedPermutation.flipSignAt_involutive P (Fin.last n)
  right_inv := by
    rintro ⟨P, hP⟩
    apply Subtype.ext
    exact SignedPermutation.flipSignAt_involutive P (Fin.last n)

theorem positiveLastPuncturedPrefixChainFlip_involutive {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Function.Involutive (positiveLastPuncturedPrefixChainFlip label) := by
  intro data
  exact (positiveLastPuncturedPrefixChainFlip label).left_inv data

theorem positiveLastPuncturedPrefixChainFlip_fixedPointFree {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (data : PositiveLastPuncturedPrefixChainType label) :
    positiveLastPuncturedPrefixChainFlip label data ≠ data := by
  intro h
  rcases data with ⟨P, hP⟩
  have hP' := congrArg (fun data : PositiveLastPuncturedPrefixChainType label => data.1) h
  simp only [positiveLastPuncturedPrefixChainFlip] at hP'
  exact SignedPermutation.flipSignAt_ne_self P (Fin.last n) hP'

noncomputable def negativeLastPuncturedPrefixChainFlip {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    NegativeLastPuncturedPrefixChainType label ≃ NegativeLastPuncturedPrefixChainType label where
  toFun := fun data => by
    refine ⟨data.1.flipSignAt (Fin.last n), ?_⟩
    exact (mem_negativeAlternatingPuncturedPrefixLabelChains_flipSignAt_last_iff data.1).2 data.2
  invFun := fun data => by
    refine ⟨data.1.flipSignAt (Fin.last n), ?_⟩
    exact (mem_negativeAlternatingPuncturedPrefixLabelChains_flipSignAt_last_iff data.1).2 data.2
  left_inv := by
    rintro ⟨P, hP⟩
    apply Subtype.ext
    exact SignedPermutation.flipSignAt_involutive P (Fin.last n)
  right_inv := by
    rintro ⟨P, hP⟩
    apply Subtype.ext
    exact SignedPermutation.flipSignAt_involutive P (Fin.last n)

theorem negativeLastPuncturedPrefixChainFlip_involutive {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Function.Involutive (negativeLastPuncturedPrefixChainFlip label) := by
  intro data
  exact (negativeLastPuncturedPrefixChainFlip label).left_inv data

theorem negativeLastPuncturedPrefixChainFlip_fixedPointFree {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (data : NegativeLastPuncturedPrefixChainType label) :
    negativeLastPuncturedPrefixChainFlip label data ≠ data := by
  intro h
  rcases data with ⟨P, hP⟩
  have hP' := congrArg (fun data : NegativeLastPuncturedPrefixChainType label => data.1) h
  simp only [negativeLastPuncturedPrefixChainFlip] at hP'
  exact SignedPermutation.flipSignAt_ne_self P (Fin.last n) hP'

noncomputable def positivePuncturedPrefixChainPartner {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    PositivePuncturedPrefixChainType label ≃ PositivePuncturedPrefixChainType label where
  toFun := fun data => by
    rcases data with ⟨⟨P, gap⟩, hmem⟩
    by_cases hgap : gap.val < n
    · refine
        ⟨(P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap)), gap), ?_⟩
      exact (mem_positiveAlternatingPuncturedPrefixLabelChains_reindexPositions_swap_gap_iff
        P gap hgap).2 hmem
    · have hlast : gap = Fin.last n := by
        apply Fin.ext
        have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
        simp [Fin.last]
        omega
      refine ⟨(P.flipSignAt (Fin.last n), Fin.last n), ?_⟩
      have hmemlast : (P, Fin.last n) ∈
          positiveAlternatingPuncturedPrefixLabelChains label := by
        simpa [hlast] using hmem
      exact (mem_positiveAlternatingPuncturedPrefixLabelChains_flipSignAt_last_iff P).2
        hmemlast
  invFun := fun data => by
    rcases data with ⟨⟨P, gap⟩, hmem⟩
    by_cases hgap : gap.val < n
    · refine
        ⟨(P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap)), gap), ?_⟩
      exact (mem_positiveAlternatingPuncturedPrefixLabelChains_reindexPositions_swap_gap_iff
        P gap hgap).2 hmem
    · have hlast : gap = Fin.last n := by
        apply Fin.ext
        have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
        simp [Fin.last]
        omega
      refine ⟨(P.flipSignAt (Fin.last n), Fin.last n), ?_⟩
      have hmemlast : (P, Fin.last n) ∈
          positiveAlternatingPuncturedPrefixLabelChains label := by
        simpa [hlast] using hmem
      exact (mem_positiveAlternatingPuncturedPrefixLabelChains_flipSignAt_last_iff P).2
        hmemlast
  left_inv := by
    rintro ⟨⟨P, gap⟩, hmem⟩
    by_cases hgap : gap.val < n
    · apply Subtype.ext
      simp [hgap,
        SignedPermutation.reindexPositions_swap_gap_involutive P gap hgap]
    · have hlast : gap = Fin.last n := by
        apply Fin.ext
        have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
        simp [Fin.last]
        omega
      apply Subtype.ext
      simp [hlast,
        SignedPermutation.flipSignAt_involutive P (Fin.last n)]
  right_inv := by
    rintro ⟨⟨P, gap⟩, hmem⟩
    by_cases hgap : gap.val < n
    · apply Subtype.ext
      simp [hgap,
        SignedPermutation.reindexPositions_swap_gap_involutive P gap hgap]
    · have hlast : gap = Fin.last n := by
        apply Fin.ext
        have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
        simp [Fin.last]
        omega
      apply Subtype.ext
      simp [hlast,
        SignedPermutation.flipSignAt_involutive P (Fin.last n)]

theorem positivePuncturedPrefixChainPartner_involutive {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Function.Involutive (positivePuncturedPrefixChainPartner label) := by
  intro data
  exact (positivePuncturedPrefixChainPartner label).left_inv data

theorem positivePuncturedPrefixChainPartner_fixedPointFree {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (data : PositivePuncturedPrefixChainType label) :
    positivePuncturedPrefixChainPartner label data ≠ data := by
  intro h
  rcases data with ⟨⟨P, gap⟩, hmem⟩
  by_cases hgap : gap.val < n
  · have hP := congrArg (fun data : PositivePuncturedPrefixChainType label => data.1.1) h
    have hP' :
        P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap)) = P := by
      simpa [positivePuncturedPrefixChainPartner, hgap] using hP
    exact SignedPermutation.reindexPositions_swap_gap_ne_self P gap hgap hP'
  · have hlast : gap = Fin.last n := by
      apply Fin.ext
      have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
      simp [Fin.last]
      omega
    have hP := congrArg (fun data : PositivePuncturedPrefixChainType label => data.1.1) h
    have hP' : P.flipSignAt (Fin.last n) = P := by
      simpa [positivePuncturedPrefixChainPartner, hgap, hlast] using hP
    exact SignedPermutation.flipSignAt_ne_self P (Fin.last n) hP'

noncomputable def negativePuncturedPrefixChainPartner {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    NegativePuncturedPrefixChainType label ≃ NegativePuncturedPrefixChainType label where
  toFun := fun data => by
    rcases data with ⟨⟨P, gap⟩, hmem⟩
    by_cases hgap : gap.val < n
    · refine
        ⟨(P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap)), gap), ?_⟩
      exact (mem_negativeAlternatingPuncturedPrefixLabelChains_reindexPositions_swap_gap_iff
        P gap hgap).2 hmem
    · have hlast : gap = Fin.last n := by
        apply Fin.ext
        have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
        simp [Fin.last]
        omega
      refine ⟨(P.flipSignAt (Fin.last n), Fin.last n), ?_⟩
      have hmemlast : (P, Fin.last n) ∈
          negativeAlternatingPuncturedPrefixLabelChains label := by
        simpa [hlast] using hmem
      exact (mem_negativeAlternatingPuncturedPrefixLabelChains_flipSignAt_last_iff P).2
        hmemlast
  invFun := fun data => by
    rcases data with ⟨⟨P, gap⟩, hmem⟩
    by_cases hgap : gap.val < n
    · refine
        ⟨(P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap)), gap), ?_⟩
      exact (mem_negativeAlternatingPuncturedPrefixLabelChains_reindexPositions_swap_gap_iff
        P gap hgap).2 hmem
    · have hlast : gap = Fin.last n := by
        apply Fin.ext
        have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
        simp [Fin.last]
        omega
      refine ⟨(P.flipSignAt (Fin.last n), Fin.last n), ?_⟩
      have hmemlast : (P, Fin.last n) ∈
          negativeAlternatingPuncturedPrefixLabelChains label := by
        simpa [hlast] using hmem
      exact (mem_negativeAlternatingPuncturedPrefixLabelChains_flipSignAt_last_iff P).2
        hmemlast
  left_inv := by
    rintro ⟨⟨P, gap⟩, hmem⟩
    by_cases hgap : gap.val < n
    · apply Subtype.ext
      simp [hgap,
        SignedPermutation.reindexPositions_swap_gap_involutive P gap hgap]
    · have hlast : gap = Fin.last n := by
        apply Fin.ext
        have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
        simp [Fin.last]
        omega
      apply Subtype.ext
      simp [hlast,
        SignedPermutation.flipSignAt_involutive P (Fin.last n)]
  right_inv := by
    rintro ⟨⟨P, gap⟩, hmem⟩
    by_cases hgap : gap.val < n
    · apply Subtype.ext
      simp [hgap,
        SignedPermutation.reindexPositions_swap_gap_involutive P gap hgap]
    · have hlast : gap = Fin.last n := by
        apply Fin.ext
        have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
        simp [Fin.last]
        omega
      apply Subtype.ext
      simp [hlast,
        SignedPermutation.flipSignAt_involutive P (Fin.last n)]

theorem negativePuncturedPrefixChainPartner_involutive {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Function.Involutive (negativePuncturedPrefixChainPartner label) := by
  intro data
  exact (negativePuncturedPrefixChainPartner label).left_inv data

theorem negativePuncturedPrefixChainPartner_fixedPointFree {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (data : NegativePuncturedPrefixChainType label) :
    negativePuncturedPrefixChainPartner label data ≠ data := by
  intro h
  rcases data with ⟨⟨P, gap⟩, hmem⟩
  by_cases hgap : gap.val < n
  · have hP := congrArg (fun data : NegativePuncturedPrefixChainType label => data.1.1) h
    have hP' :
        P.reindexPositions (Equiv.swap gap (SignedPermutation.gapNext gap hgap)) = P := by
      simpa [negativePuncturedPrefixChainPartner, hgap] using hP
    exact SignedPermutation.reindexPositions_swap_gap_ne_self P gap hgap hP'
  · have hlast : gap = Fin.last n := by
      apply Fin.ext
      have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
      simp [Fin.last]
      omega
    have hP := congrArg (fun data : NegativePuncturedPrefixChainType label => data.1.1) h
    have hP' : P.flipSignAt (Fin.last n) = P := by
      simpa [negativePuncturedPrefixChainPartner, hgap, hlast] using hP
    exact SignedPermutation.flipSignAt_ne_self P (Fin.last n) hP'

theorem positivePuncturedPrefixChainPartner_val {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (data : PositivePuncturedPrefixChainType label) :
    (positivePuncturedPrefixChainPartner label data).1 =
      puncturedPrefixPartnerData data.1 := by
  rcases data with ⟨⟨P, gap⟩, hmem⟩
  by_cases hgap : gap.val < n
  · simp [positivePuncturedPrefixChainPartner, puncturedPrefixPartnerData, hgap]
  · have hlast : gap = Fin.last n := by
      apply Fin.ext
      have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
      simp [Fin.last]
      omega
    simp [positivePuncturedPrefixChainPartner, puncturedPrefixPartnerData, hlast]

theorem negativePuncturedPrefixChainPartner_val {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (data : NegativePuncturedPrefixChainType label) :
    (negativePuncturedPrefixChainPartner label data).1 =
      puncturedPrefixPartnerData data.1 := by
  rcases data with ⟨⟨P, gap⟩, hmem⟩
  by_cases hgap : gap.val < n
  · simp [negativePuncturedPrefixChainPartner, puncturedPrefixPartnerData, hgap]
  · have hlast : gap = Fin.last n := by
      apply Fin.ext
      have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
      simp [Fin.last]
      omega
    simp [negativePuncturedPrefixChainPartner, puncturedPrefixPartnerData, hlast]

theorem positiveAlternatingPuncturedPrefixLabelChains_card_eq_negative {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    (positiveAlternatingPuncturedPrefixLabelChains label).card =
      (negativeAlternatingPuncturedPrefixLabelChains label).card := by
  classical
  let e : SignedPermutation (n + 1) × Fin (n + 1) ≃
      SignedPermutation (n + 1) × Fin (n + 1) := puncturedPrefixAntipode
  refine Finset.card_bij (fun data _ => e data) ?mem ?inj ?surj
  · rintro ⟨P, gap⟩ hP
    have hpos : PositiveAlternatingPuncturedPrefixLabels label P gap := by
      simpa [positiveAlternatingPuncturedPrefixLabelChains] using hP
    have hneg : NegativeAlternatingPuncturedPrefixLabels label P.antipode gap := by
      have hiff := positiveAlternatingPuncturedPrefixLabels_antipode_iff label hantipodal
        P.antipode gap
      have hpos' : PositiveAlternatingPuncturedPrefixLabels label P.antipode.antipode gap := by
        simpa [SignedPermutation.antipode_involutive P] using hpos
      exact hiff.mp hpos'
    simpa [negativeAlternatingPuncturedPrefixLabelChains, e, puncturedPrefixAntipode] using hneg
  · intro data _ other _ hdata
    exact e.injective hdata
  · rintro ⟨P, gap⟩ hP
    have hneg : NegativeAlternatingPuncturedPrefixLabels label P gap := by
      simpa [negativeAlternatingPuncturedPrefixLabelChains] using hP
    refine ⟨e (P, gap), ?_, ?_⟩
    · have hpos : PositiveAlternatingPuncturedPrefixLabels label P.antipode gap := by
        exact (positiveAlternatingPuncturedPrefixLabels_antipode_iff label hantipodal P gap).mpr hneg
      simpa [positiveAlternatingPuncturedPrefixLabelChains, e, puncturedPrefixAntipode] using hpos
    · simp [e, puncturedPrefixAntipode, SignedPermutation.antipode_involutive P]

theorem positive_negative_punctured_alternating_disjoint {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    PositiveAlternatingPuncturedPrefixLabels label P gap →
      NegativeAlternatingPuncturedPrefixLabels label P gap → False := by
  intro hpos hneg
  let i : Fin n := ⟨0, hn⟩
  have hp := hpos.2 i
  have hn' := hneg.2 i
  simp [i] at hp hn'
  rw [hp] at hn'
  simp at hn'

theorem positive_negativeAlternatingPuncturedPrefixLabelChains_disjoint {n m : ℕ}
    (hn : 0 < n) (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Disjoint (positiveAlternatingPuncturedPrefixLabelChains label)
      (negativeAlternatingPuncturedPrefixLabelChains label) := by
  classical
  rw [Finset.disjoint_left]
  rintro ⟨P, gap⟩ hpos hneg
  exact positive_negative_punctured_alternating_disjoint hn label P gap
    (by simpa [positiveAlternatingPuncturedPrefixLabelChains] using hpos)
    (by simpa [negativeAlternatingPuncturedPrefixLabelChains] using hneg)

noncomputable def alternatingPuncturedPrefixLabelChains {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Finset (SignedPermutation (n + 1) × Fin (n + 1)) :=
  positiveAlternatingPuncturedPrefixLabelChains label ∪
    negativeAlternatingPuncturedPrefixLabelChains label

theorem positiveAlternatingPuncturedPrefixLabelChains_eq_empty_of_lt {n m : ℕ} (hmn : m < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    positiveAlternatingPuncturedPrefixLabelChains label = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨P, gap⟩ hP
  have hpos : PositiveAlternatingPuncturedPrefixLabels label P gap := by
    simpa [positiveAlternatingPuncturedPrefixLabelChains] using hP
  exact not_strictMono_fin_of_lt hmn
    ⟨fun i => (label (P.prefixChain (gap.succAbove i))).index, hpos.1⟩

theorem negativeAlternatingPuncturedPrefixLabelChains_eq_empty_of_lt {n m : ℕ} (hmn : m < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    negativeAlternatingPuncturedPrefixLabelChains label = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨P, gap⟩ hP
  have hneg : NegativeAlternatingPuncturedPrefixLabels label P gap := by
    simpa [negativeAlternatingPuncturedPrefixLabelChains] using hP
  exact not_strictMono_fin_of_lt hmn
    ⟨fun i => (label (P.prefixChain (gap.succAbove i))).index, hneg.1⟩

theorem alternatingPuncturedPrefixLabelChains_eq_empty_of_lt {n m : ℕ} (hmn : m < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    alternatingPuncturedPrefixLabelChains label = ∅ := by
  rw [alternatingPuncturedPrefixLabelChains,
    positiveAlternatingPuncturedPrefixLabelChains_eq_empty_of_lt hmn,
    negativeAlternatingPuncturedPrefixLabelChains_eq_empty_of_lt hmn, Finset.empty_union]

theorem positiveAlternatingPuncturedPrefixLabelChains_card_eq_zero_of_lt {n m : ℕ}
    (hmn : m < n) (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    (positiveAlternatingPuncturedPrefixLabelChains label).card = 0 := by
  rw [positiveAlternatingPuncturedPrefixLabelChains_eq_empty_of_lt hmn label]
  simp

theorem alternatingPuncturedPrefixLabelChains_card_eq_zero_of_lt {n m : ℕ}
    (hmn : m < n) (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    (alternatingPuncturedPrefixLabelChains label).card = 0 := by
  rw [alternatingPuncturedPrefixLabelChains_eq_empty_of_lt hmn label]
  simp

theorem alternatingPuncturedPrefixLabelChains_card {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    (alternatingPuncturedPrefixLabelChains label).card =
      2 * (positiveAlternatingPuncturedPrefixLabelChains label).card := by
  classical
  rw [alternatingPuncturedPrefixLabelChains,
    Finset.card_union_of_disjoint
      (positive_negativeAlternatingPuncturedPrefixLabelChains_disjoint hn label),
    positiveAlternatingPuncturedPrefixLabelChains_card_eq_negative label hantipodal]
  omega

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

theorem mem_positiveAlternatingPuncturedPrefixLabelChains_last_of_prefix {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {P : SignedPermutation (n + 1)}
    (hP : P ∈ positiveAlternatingPrefixLabelChains label) :
    (P, Fin.last n) ∈ positiveAlternatingPuncturedPrefixLabelChains label := by
  exact mem_positiveAlternatingPuncturedPrefixLabelChains_iff.mpr
    (positiveAlternatingPrefixLabels_punctured_last
      (by simpa [positiveAlternatingPrefixLabelChains] using hP))

theorem mem_negativeAlternatingPuncturedPrefixLabelChains_last_of_prefix {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {P : SignedPermutation (n + 1)}
    (hP : P ∈ negativeAlternatingPrefixLabelChains label) :
    (P, Fin.last n) ∈ negativeAlternatingPuncturedPrefixLabelChains label := by
  exact mem_negativeAlternatingPuncturedPrefixLabelChains_iff.mpr
    (negativeAlternatingPrefixLabels_punctured_last
      (by simpa [negativeAlternatingPrefixLabelChains] using hP))

theorem mem_negativeAlternatingPuncturedPrefixLabelChains_zero_of_positive_prefix {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {P : SignedPermutation (n + 1)}
    (hP : P ∈ positiveAlternatingPrefixLabelChains label) :
    (P, (0 : Fin (n + 1))) ∈ negativeAlternatingPuncturedPrefixLabelChains label := by
  exact mem_negativeAlternatingPuncturedPrefixLabelChains_iff.mpr
    (positiveAlternatingPrefixLabels_punctured_zero
      (by simpa [positiveAlternatingPrefixLabelChains] using hP))

theorem mem_positiveAlternatingPuncturedPrefixLabelChains_zero_of_negative_prefix {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {P : SignedPermutation (n + 1)}
    (hP : P ∈ negativeAlternatingPrefixLabelChains label) :
    (P, (0 : Fin (n + 1))) ∈ positiveAlternatingPuncturedPrefixLabelChains label := by
  exact mem_positiveAlternatingPuncturedPrefixLabelChains_iff.mpr
    (negativeAlternatingPrefixLabels_punctured_zero
      (by simpa [negativeAlternatingPrefixLabelChains] using hP))

theorem positiveAlternatingPrefixLabelChains_zero_eq_univ {m : ℕ}
    (label : NonzeroSignedSubset 0 → SignedLabel m) :
    positiveAlternatingPrefixLabelChains label = Finset.univ := by
  classical
  ext P
  constructor
  · intro _hP
    simp
  · intro _hP
    simpa [positiveAlternatingPrefixLabelChains] using
      positiveAlternatingPrefixLabels_zero label P

theorem negativeAlternatingPrefixLabelChains_zero_eq_univ {m : ℕ}
    (label : NonzeroSignedSubset 0 → SignedLabel m) :
    negativeAlternatingPrefixLabelChains label = Finset.univ := by
  classical
  ext P
  constructor
  · intro _hP
    simp
  · intro _hP
    simpa [negativeAlternatingPrefixLabelChains] using
      negativeAlternatingPrefixLabels_zero label P

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

theorem positiveAlternatingPrefixLabelChains_card_le_punctured_last {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    (positiveAlternatingPrefixLabelChains label).card ≤
      (positiveAlternatingPuncturedPrefixLabelChains label).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun P : SignedPermutation (n + 1) =>
      (P, Fin.last n)) ?mem ?inj
  · intro P hP
    have hpos : PositiveAlternatingPrefixLabels label P := by
      simpa [positiveAlternatingPrefixLabelChains] using hP
    simpa [positiveAlternatingPuncturedPrefixLabelChains] using
      positiveAlternatingPrefixLabels_punctured_last hpos
  · intro P _ Q _ hPQ
    exact congrArg Prod.fst hPQ

theorem negativeAlternatingPrefixLabelChains_card_le_punctured_last {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    (negativeAlternatingPrefixLabelChains label).card ≤
      (negativeAlternatingPuncturedPrefixLabelChains label).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun P : SignedPermutation (n + 1) =>
      (P, Fin.last n)) ?mem ?inj
  · intro P hP
    have hneg : NegativeAlternatingPrefixLabels label P := by
      simpa [negativeAlternatingPrefixLabelChains] using hP
    simpa [negativeAlternatingPuncturedPrefixLabelChains] using
      negativeAlternatingPrefixLabels_punctured_last hneg
  · intro P _ Q _ hPQ
    exact congrArg Prod.fst hPQ

theorem positiveAlternatingPrefixLabelChains_card_le_negative_punctured_zero {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    (positiveAlternatingPrefixLabelChains label).card ≤
      (negativeAlternatingPuncturedPrefixLabelChains label).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun P : SignedPermutation (n + 1) =>
      (P, (0 : Fin (n + 1)))) ?mem ?inj
  · intro P hP
    have hpos : PositiveAlternatingPrefixLabels label P := by
      simpa [positiveAlternatingPrefixLabelChains] using hP
    simpa [negativeAlternatingPuncturedPrefixLabelChains] using
      positiveAlternatingPrefixLabels_punctured_zero hpos
  · intro P _ Q _ hPQ
    exact congrArg Prod.fst hPQ

theorem negativeAlternatingPrefixLabelChains_card_le_positive_punctured_zero {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    (negativeAlternatingPrefixLabelChains label).card ≤
      (positiveAlternatingPuncturedPrefixLabelChains label).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun P : SignedPermutation (n + 1) =>
      (P, (0 : Fin (n + 1)))) ?mem ?inj
  · intro P hP
    have hneg : NegativeAlternatingPrefixLabels label P := by
      simpa [negativeAlternatingPrefixLabelChains] using hP
    simpa [positiveAlternatingPuncturedPrefixLabelChains] using
      negativeAlternatingPrefixLabels_punctured_zero hneg
  · intro P _ Q _ hPQ
    exact congrArg Prod.fst hPQ

theorem positive_negative_alternating_disjoint {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset n → SignedLabel m) (P : SignedPermutation n) :
    PositiveAlternatingPrefixLabels label P →
      NegativeAlternatingPrefixLabels label P → False := by
  intro hpos hneg
  let i : Fin n := ⟨0, hn⟩
  have hp := hpos.2 i
  have hn' := hneg.2 i
  simp [i] at hp hn'
  rw [hp] at hn'
  simp at hn'

theorem positive_negativeAlternatingPrefixLabelChains_disjoint {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset n → SignedLabel m) :
    Disjoint (positiveAlternatingPrefixLabelChains label)
      (negativeAlternatingPrefixLabelChains label) := by
  classical
  rw [Finset.disjoint_left]
  intro P hpos hneg
  exact positive_negative_alternating_disjoint hn label P
    (by simpa [positiveAlternatingPrefixLabelChains] using hpos)
    (by simpa [negativeAlternatingPrefixLabelChains] using hneg)

/-- Positive- or negative-first alternating prefix-label chains. -/
noncomputable def alternatingPrefixLabelChains {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) : Finset (SignedPermutation n) :=
  positiveAlternatingPrefixLabelChains label ∪ negativeAlternatingPrefixLabelChains label

theorem positiveAlternatingPrefixLabelChains_eq_empty_of_lt {n m : ℕ} (hmn : m < n)
    (label : NonzeroSignedSubset n → SignedLabel m) :
    positiveAlternatingPrefixLabelChains label = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro P hP
  have hpos : PositiveAlternatingPrefixLabels label P := by
    simpa [positiveAlternatingPrefixLabelChains] using hP
  exact not_strictMono_fin_of_lt hmn ⟨fun i => (label (P.prefixChain i)).index, hpos.1⟩

theorem negativeAlternatingPrefixLabelChains_eq_empty_of_lt {n m : ℕ} (hmn : m < n)
    (label : NonzeroSignedSubset n → SignedLabel m) :
    negativeAlternatingPrefixLabelChains label = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro P hP
  have hneg : NegativeAlternatingPrefixLabels label P := by
    simpa [negativeAlternatingPrefixLabelChains] using hP
  exact not_strictMono_fin_of_lt hmn ⟨fun i => (label (P.prefixChain i)).index, hneg.1⟩

theorem alternatingPrefixLabelChains_eq_empty_of_lt {n m : ℕ} (hmn : m < n)
    (label : NonzeroSignedSubset n → SignedLabel m) :
    alternatingPrefixLabelChains label = ∅ := by
  rw [alternatingPrefixLabelChains, positiveAlternatingPrefixLabelChains_eq_empty_of_lt hmn,
    negativeAlternatingPrefixLabelChains_eq_empty_of_lt hmn, Finset.empty_union]

theorem positiveAlternatingPrefixLabelChains_card_eq_zero_of_lt {n m : ℕ} (hmn : m < n)
    (label : NonzeroSignedSubset n → SignedLabel m) :
    (positiveAlternatingPrefixLabelChains label).card = 0 := by
  rw [positiveAlternatingPrefixLabelChains_eq_empty_of_lt hmn label]
  simp

theorem alternatingPrefixLabelChains_card_eq_zero_of_lt {n m : ℕ} (hmn : m < n)
    (label : NonzeroSignedSubset n → SignedLabel m) :
    (alternatingPrefixLabelChains label).card = 0 := by
  rw [alternatingPrefixLabelChains_eq_empty_of_lt hmn label]
  simp

theorem alternatingPrefixLabelChains_card {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    (alternatingPrefixLabelChains label).card =
      2 * (positiveAlternatingPrefixLabelChains label).card := by
  classical
  rw [alternatingPrefixLabelChains,
    Finset.card_union_of_disjoint (positive_negativeAlternatingPrefixLabelChains_disjoint hn label),
    positiveAlternatingPrefixLabelChains_card_eq_negative label hantipodal]
  omega

theorem alternatingPrefixLabelChains_card_le_punctured_last {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    (alternatingPrefixLabelChains label).card ≤
      (alternatingPuncturedPrefixLabelChains label).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun P : SignedPermutation (n + 1) =>
      (P, Fin.last n)) ?mem ?inj
  · intro P hP
    rw [alternatingPrefixLabelChains] at hP
    rw [alternatingPuncturedPrefixLabelChains]
    rcases Finset.mem_union.mp hP with hpos | hneg
    · exact Finset.mem_union_left _
        (by
          have hpos' : PositiveAlternatingPrefixLabels label P := by
            simpa [positiveAlternatingPrefixLabelChains] using hpos
          simpa [positiveAlternatingPuncturedPrefixLabelChains] using
            positiveAlternatingPrefixLabels_punctured_last hpos')
    · exact Finset.mem_union_right _
        (by
          have hneg' : NegativeAlternatingPrefixLabels label P := by
            simpa [negativeAlternatingPrefixLabelChains] using hneg
          simpa [negativeAlternatingPuncturedPrefixLabelChains] using
            negativeAlternatingPrefixLabels_punctured_last hneg')
  · intro P _ Q _ hPQ
    exact congrArg Prod.fst hPQ

theorem alternatingPrefixLabelChains_card_le_punctured_zero {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    (alternatingPrefixLabelChains label).card ≤
      (alternatingPuncturedPrefixLabelChains label).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun P : SignedPermutation (n + 1) =>
      (P, (0 : Fin (n + 1)))) ?mem ?inj
  · intro P hP
    rw [alternatingPrefixLabelChains] at hP
    rw [alternatingPuncturedPrefixLabelChains]
    rcases Finset.mem_union.mp hP with hpos | hneg
    · exact Finset.mem_union_right _
        (by
          have hpos' : PositiveAlternatingPrefixLabels label P := by
            simpa [positiveAlternatingPrefixLabelChains] using hpos
          simpa [negativeAlternatingPuncturedPrefixLabelChains] using
            positiveAlternatingPrefixLabels_punctured_zero hpos')
    · exact Finset.mem_union_left _
        (by
          have hneg' : NegativeAlternatingPrefixLabels label P := by
            simpa [negativeAlternatingPrefixLabelChains] using hneg
          simpa [positiveAlternatingPuncturedPrefixLabelChains] using
            negativeAlternatingPrefixLabels_punctured_zero hneg')
  · intro P _ Q _ hPQ
    exact congrArg Prod.fst hPQ

/-- In dimension one, every signed-permutation prefix chain is alternating
in exactly one of the two possible first signs. -/
theorem alternatingPrefixLabelChains_card_one
    (label : NonzeroSignedSubset 1 → SignedLabel 0) :
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
  simp [SignedPermutation.card_one]

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

/--
Equivalent mod-four form of the Ky Fan prefix-chain frontier: after both
orientations are counted, the number of alternating maximal chains is `2`
modulo `4`.
-/
def KyFanPrefixModFourStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        ∃ r, (alternatingPrefixLabelChains label).card = 4 * r + 2

theorem kyFanPrefixParityStatement_iff_modFour {n m : ℕ} (hn : 0 < n) :
    KyFanPrefixParityStatement n m ↔ KyFanPrefixModFourStatement n m := by
  constructor
  · intro hparity label hantipodal hno
    rcases hparity label hantipodal hno with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [alternatingPrefixLabelChains_card hn label hantipodal, hr]
    omega
  · intro hmodFour label hantipodal hno
    obtain ⟨r, hcard⟩ := hmodFour label hantipodal hno
    have htwo := alternatingPrefixLabelChains_card hn label hantipodal
    refine ⟨r, ?_⟩
    omega

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

theorem kyFanPrefixChainStatement_of_modFour {n m : ℕ} (hn : 0 < n)
    (hmodFour : KyFanPrefixModFourStatement n m) :
    KyFanPrefixChainStatement n m :=
  kyFanPrefixChainStatement_of_parity
    ((kyFanPrefixParityStatement_iff_modFour hn).mpr hmodFour)

theorem tuckerLemmaStatement_of_kyFanPrefixModFour {n : ℕ} (hn : 1 ≤ n)
    (hmodFour : KyFanPrefixModFourStatement n (n - 1)) :
    TuckerLemmaStatement n :=
  tuckerLemmaStatement_of_kyFanPrefix hn
    (kyFanPrefixChainStatement_of_modFour (by omega) hmodFour)

theorem not_nonzeroSignedSubset_zero (X : NonzeroSignedSubset 0) : False := by
  rcases X with ⟨X, hX⟩
  have hpos : X.pos = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x _hx
    exact Fin.elim0 x
  have hneg : X.neg = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x _hx
    exact Fin.elim0 x
  simp [SignedSubset.Nonzero, hpos, hneg] at hX

theorem not_tuckerLemmaStatement_zero : ¬ TuckerLemmaStatement 0 := by
  intro htucker
  let label : NonzeroSignedSubset 0 → SignedLabel (0 - 1) :=
    fun X => False.elim (not_nonzeroSignedSubset_zero X)
  have hantipodal : ∀ X, label X.antipode = (label X).neg := by
    intro X
    exact False.elim (not_nonzeroSignedSubset_zero X)
  obtain ⟨X, _Y, _hXY, _hcomp⟩ := htucker label hantipodal
  exact not_nonzeroSignedSubset_zero X

theorem tuckerLemmaStatement_one : TuckerLemmaStatement 1 := by
  intro label _
  let z : Fin 1 := ⟨0, by omega⟩
  let X : NonzeroSignedSubset 1 :=
    ⟨{ pos := {z}, neg := ∅, disjoint := by simp },
      by simp [SignedSubset.Nonzero]⟩
  exact Fin.elim0 (label X).index

theorem tuckerLemmaStatement_two : TuckerLemmaStatement 2 := by
  classical
  intro label hantipodal
  by_contra hnone
  have hno :
      ∀ X Y : NonzeroSignedSubset 2,
        SignedSubset.Le X.1 Y.1 → label X ≠ (label Y).neg := by
    intro X Y hXY hcomp
    exact hnone ⟨X, Y, hXY, hcomp⟩
  have hsame :
      ∀ {X Y : NonzeroSignedSubset 2},
        SignedSubset.Le X.1 Y.1 → (label X).positive = (label Y).positive := by
    intro X Y hXY
    apply positive_eq_of_le_of_same_index_of_no_complement hno hXY
    apply Fin.ext
    omega
  let z : Fin 2 := ⟨0, by omega⟩
  let o : Fin 2 := ⟨1, by omega⟩
  let P0 : NonzeroSignedSubset 2 :=
    ⟨{ pos := {z}, neg := ∅, disjoint := by simp },
      by simp [SignedSubset.Nonzero]⟩
  let P1 : NonzeroSignedSubset 2 :=
    ⟨{ pos := {o}, neg := ∅, disjoint := by simp },
      by simp [SignedSubset.Nonzero]⟩
  let N1 : NonzeroSignedSubset 2 := P1.antipode
  let PP : NonzeroSignedSubset 2 :=
    ⟨{ pos := {z, o}, neg := ∅, disjoint := by simp },
      by simp [SignedSubset.Nonzero]⟩
  let PN : NonzeroSignedSubset 2 :=
    ⟨{ pos := {z}, neg := {o}, disjoint := by
        simp [z, o] },
      by simp [SignedSubset.Nonzero]⟩
  have hP0PP : (label P0).positive = (label PP).positive :=
    hsame (X := P0) (Y := PP) (by simp [SignedSubset.Le, P0, PP])
  have hP1PP : (label P1).positive = (label PP).positive :=
    hsame (X := P1) (Y := PP) (by simp [SignedSubset.Le, P1, PP])
  have hP0PN : (label P0).positive = (label PN).positive :=
    hsame (X := P0) (Y := PN) (by simp [SignedSubset.Le, P0, PN])
  have hN1PN : (label N1).positive = (label PN).positive :=
    hsame (X := N1) (Y := PN) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, N1, P1, PN])
  have hP0P1 : (label P0).positive = (label P1).positive :=
    hP0PP.trans hP1PP.symm
  have hP0N1 : (label P0).positive = (label N1).positive :=
    hP0PN.trans hN1PN.symm
  have hN1neg : (label N1).positive = !((label P1).positive) := by
    have := congrArg SignedLabel.positive (hantipodal P1)
    simpa [N1, SignedLabel.neg] using this
  have hself : (label P1).positive = !((label P1).positive) :=
    hP0P1.symm.trans (hP0N1.trans hN1neg)
  cases (label P1).positive <;> simp at hself

/-- Tucker's lemma is unconditional in dimensions one and two. -/
theorem tuckerLemmaStatement_le_two {n : ℕ} (hnpos : 1 ≤ n) (hnle : n ≤ 2) :
    TuckerLemmaStatement n := by
  interval_cases n
  · exact tuckerLemmaStatement_one
  · exact tuckerLemmaStatement_two

theorem kyFanPrefixParityStatement_zero : KyFanPrefixParityStatement 0 0 := by
  intro label _hantipodal _hno
  classical
  rw [positiveAlternatingPrefixLabelChains_zero_eq_univ label]
  have hcard : (Finset.univ : Finset (SignedPermutation 0)).card = 1 := by
    simp [SignedPermutation.card_zero]
  rw [hcard]
  exact odd_one

theorem kyFanPrefixParityStatement_one : KyFanPrefixParityStatement 1 0 := by
  intro label _hantipodal _hno
  let z : Fin 1 := ⟨0, by omega⟩
  let X : NonzeroSignedSubset 1 :=
    ⟨{ pos := {z}, neg := ∅, disjoint := by simp },
      by simp [SignedSubset.Nonzero]⟩
  exact Fin.elim0 (label X).index

/--
The two-dimensional Ky Fan prefix-parity statement follows because the
`NoComplementaryComparableLabels` hypothesis is already impossible.
-/
theorem kyFanPrefixParityStatement_two : KyFanPrefixParityStatement 2 1 := by
  intro label hantipodal hno
  obtain ⟨X, Y, hXY, hcomp⟩ := tuckerLemmaStatement_two label hantipodal
  exact False.elim (hno X Y hXY hcomp)

theorem tuckerLemmaStatement_one_of_kyFanPrefixParity : TuckerLemmaStatement 1 :=
  tuckerLemmaStatement_of_kyFanPrefixParity (by omega) kyFanPrefixParityStatement_one

theorem tuckerLemmaStatement_two_of_kyFanPrefixParity : TuckerLemmaStatement 2 :=
  tuckerLemmaStatement_of_kyFanPrefixParity (by omega) kyFanPrefixParityStatement_two

theorem kyFanPrefixParityStatement_sub_one_le_two {n : ℕ} (hnle : n ≤ 2) :
    KyFanPrefixParityStatement n (n - 1) := by
  interval_cases n
  · exact kyFanPrefixParityStatement_zero
  · exact kyFanPrefixParityStatement_one
  · exact kyFanPrefixParityStatement_two

theorem kyFanPrefixModFourStatement_sub_one_le_two {n : ℕ} (hnpos : 0 < n) (hnle : n ≤ 2) :
    KyFanPrefixModFourStatement n (n - 1) :=
  (kyFanPrefixParityStatement_iff_modFour hnpos).mp
    (kyFanPrefixParityStatement_sub_one_le_two hnle)

theorem kyFanPrefixModFourStatement_one : KyFanPrefixModFourStatement 1 0 := by
  intro label _hantipodal _hno
  exact ⟨0, by simpa using alternatingPrefixLabelChains_card_one label⟩

theorem exists_complementaryComparable_of_kyFanPrefixParity_of_lt {n m : ℕ}
    (hmn : m < n) (hparity : KyFanPrefixParityStatement n m)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ∃ X Y : NonzeroSignedSubset n,
      SignedSubset.Le X.1 Y.1 ∧ label X = (label Y).neg := by
  by_contra hnone
  have hno : NoComplementaryComparableLabels label := by
    intro X Y hXY hcomp
    exact hnone ⟨X, Y, hXY, hcomp⟩
  have hchain := kyFanPrefixChainStatement_of_parity hparity label hantipodal hno
  obtain ⟨P, hstrict⟩ := hchain
  exact not_strictMono_fin_of_lt hmn ⟨fun i => (label (P.prefixChain i)).index, hstrict⟩

theorem not_noComplementaryComparableLabels_of_kyFanPrefixParity_of_lt {n m : ℕ}
    (hmn : m < n) (hparity : KyFanPrefixParityStatement n m)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ¬ NoComplementaryComparableLabels label := by
  intro hno
  have hodd := hparity label hantipodal hno
  have hzero := positiveAlternatingPrefixLabelChains_card_eq_zero_of_lt hmn label
  rw [hzero] at hodd
  rcases hodd with ⟨r, hr⟩
  omega

theorem exists_complementaryComparable_of_kyFanPrefixModFour_of_lt {n m : ℕ}
    (hmn : m < n) (hmodFour : KyFanPrefixModFourStatement n m)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ∃ X Y : NonzeroSignedSubset n,
      SignedSubset.Le X.1 Y.1 ∧ label X = (label Y).neg :=
  exists_complementaryComparable_of_kyFanPrefixParity_of_lt hmn
    ((kyFanPrefixParityStatement_iff_modFour (Nat.zero_lt_of_lt hmn)).mpr hmodFour)
    label hantipodal

theorem not_noComplementaryComparableLabels_of_kyFanPrefixModFour_of_lt {n m : ℕ}
    (hmn : m < n) (hmodFour : KyFanPrefixModFourStatement n m)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ¬ NoComplementaryComparableLabels label := by
  intro hno
  obtain ⟨r, hcard⟩ := hmodFour label hantipodal hno
  have hzero := alternatingPrefixLabelChains_card_eq_zero_of_lt hmn label
  rw [hzero] at hcard
  omega

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

theorem even_card_positiveNonlastPuncturedPrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Even (Fintype.card (PositiveNonlastPuncturedPrefixChainType label)) :=
  even_card_of_fixedPointFree_involutive
    (positiveNonlastPuncturedPrefixChainSwap label)
    (positiveNonlastPuncturedPrefixChainSwap_involutive label)
    (positiveNonlastPuncturedPrefixChainSwap_fixedPointFree label)

theorem even_card_negativeNonlastPuncturedPrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Even (Fintype.card (NegativeNonlastPuncturedPrefixChainType label)) :=
  even_card_of_fixedPointFree_involutive
    (negativeNonlastPuncturedPrefixChainSwap label)
    (negativeNonlastPuncturedPrefixChainSwap_involutive label)
    (negativeNonlastPuncturedPrefixChainSwap_fixedPointFree label)

theorem even_card_positiveLastPuncturedPrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Even (Fintype.card (PositiveLastPuncturedPrefixChainType label)) :=
  even_card_of_fixedPointFree_involutive
    (positiveLastPuncturedPrefixChainFlip label)
    (positiveLastPuncturedPrefixChainFlip_involutive label)
    (positiveLastPuncturedPrefixChainFlip_fixedPointFree label)

theorem even_card_positivePuncturedPrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Even (Fintype.card (PositivePuncturedPrefixChainType label)) :=
  even_card_of_fixedPointFree_involutive
    (positivePuncturedPrefixChainPartner label)
    (positivePuncturedPrefixChainPartner_involutive label)
    (positivePuncturedPrefixChainPartner_fixedPointFree label)

theorem even_card_negativeLastPuncturedPrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Even (Fintype.card (NegativeLastPuncturedPrefixChainType label)) :=
  even_card_of_fixedPointFree_involutive
    (negativeLastPuncturedPrefixChainFlip label)
    (negativeLastPuncturedPrefixChainFlip_involutive label)
    (negativeLastPuncturedPrefixChainFlip_fixedPointFree label)

theorem even_card_negativePuncturedPrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Even (Fintype.card (NegativePuncturedPrefixChainType label)) :=
  even_card_of_fixedPointFree_involutive
    (negativePuncturedPrefixChainPartner label)
    (negativePuncturedPrefixChainPartner_involutive label)
    (negativePuncturedPrefixChainPartner_fixedPointFree label)

theorem positivePuncturedPrefixChainType_card {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Fintype.card (PositivePuncturedPrefixChainType label) =
      (positiveAlternatingPuncturedPrefixLabelChains label).card := by
  classical
  exact Fintype.card_of_subtype (positiveAlternatingPuncturedPrefixLabelChains label)
    (fun _ => Iff.rfl)

theorem negativePuncturedPrefixChainType_card {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Fintype.card (NegativePuncturedPrefixChainType label) =
      (negativeAlternatingPuncturedPrefixLabelChains label).card := by
  classical
  exact Fintype.card_of_subtype (negativeAlternatingPuncturedPrefixLabelChains label)
    (fun _ => Iff.rfl)

theorem positiveAlternatingPuncturedPrefixLabelChains_card_even {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Even (positiveAlternatingPuncturedPrefixLabelChains label).card := by
  simpa [positivePuncturedPrefixChainType_card label] using
    even_card_positivePuncturedPrefixChainType label

theorem negativeAlternatingPuncturedPrefixLabelChains_card_even {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Even (negativeAlternatingPuncturedPrefixLabelChains label).card := by
  simpa [negativePuncturedPrefixChainType_card label] using
    even_card_negativePuncturedPrefixChainType label

theorem alternatingPuncturedPrefixLabelChains_card_even {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Even (alternatingPuncturedPrefixLabelChains label).card := by
  classical
  rw [alternatingPuncturedPrefixLabelChains,
    Finset.card_union_of_disjoint
      (positive_negativeAlternatingPuncturedPrefixLabelChains_disjoint hn label)]
  rcases positiveAlternatingPuncturedPrefixLabelChains_card_even label with ⟨a, ha⟩
  rcases negativeAlternatingPuncturedPrefixLabelChains_card_even label with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  omega

theorem alternatingPuncturedPrefixLabelChains_card_eq_four_mul {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ∃ r, (alternatingPuncturedPrefixLabelChains label).card = 4 * r := by
  rcases positiveAlternatingPuncturedPrefixLabelChains_card_even label with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  rw [alternatingPuncturedPrefixLabelChains_card hn label hantipodal, hr]
  omega

theorem four_dvd_alternatingPuncturedPrefixLabelChains_card {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    4 ∣ (alternatingPuncturedPrefixLabelChains label).card := by
  rcases alternatingPuncturedPrefixLabelChains_card_eq_four_mul hn label hantipodal with ⟨r, hr⟩
  exact ⟨r, hr⟩

abbrev AlternatingPuncturedPrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :=
  {data : SignedPermutation (n + 1) × Fin (n + 1) //
    data ∈ alternatingPuncturedPrefixLabelChains label}

theorem alternatingPuncturedPrefixChainType_card {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Fintype.card (AlternatingPuncturedPrefixChainType label) =
      (alternatingPuncturedPrefixLabelChains label).card := by
  classical
  exact Fintype.card_of_subtype (alternatingPuncturedPrefixLabelChains label)
    (fun _ => Iff.rfl)

theorem four_dvd_alternatingPuncturedPrefixChainType_card {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    4 ∣ Fintype.card (AlternatingPuncturedPrefixChainType label) := by
  rw [alternatingPuncturedPrefixChainType_card label]
  exact four_dvd_alternatingPuncturedPrefixLabelChains_card hn label hantipodal

noncomputable def alternatingPuncturedPrefixChainTypeEquivSum {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    AlternatingPuncturedPrefixChainType label ≃
      PositivePuncturedPrefixChainType label ⊕ NegativePuncturedPrefixChainType label := by
  classical
  let p : SignedPermutation (n + 1) × Fin (n + 1) → Prop :=
    fun data => data ∈ positiveAlternatingPuncturedPrefixLabelChains label
  let q : SignedPermutation (n + 1) × Fin (n + 1) → Prop :=
    fun data => data ∈ negativeAlternatingPuncturedPrefixLabelChains label
  have hdisj : Disjoint p q := by
    rw [disjoint_iff]
    funext data
    apply propext
    constructor
    · intro hdata
      exact False.elim
        ((Finset.disjoint_left.mp
          (positive_negativeAlternatingPuncturedPrefixLabelChains_disjoint hn label))
          hdata.1 hdata.2)
    · intro hfalse
      exact False.elim hfalse
  have heq :
      (fun data : SignedPermutation (n + 1) × Fin (n + 1) =>
        data ∈ alternatingPuncturedPrefixLabelChains label) =
        fun data => p data ∨ q data := by
    funext data
    apply propext
    simp [alternatingPuncturedPrefixLabelChains, p, q]
  exact (Equiv.subtypeEquivProp heq).trans (subtypeOrEquiv p q hdisj)

noncomputable def alternatingPuncturedPrefixChainPartner {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    AlternatingPuncturedPrefixChainType label ≃ AlternatingPuncturedPrefixChainType label :=
  (alternatingPuncturedPrefixChainTypeEquivSum hn label).trans
    ((Equiv.sumCongr (positivePuncturedPrefixChainPartner label)
      (negativePuncturedPrefixChainPartner label)).trans
      (alternatingPuncturedPrefixChainTypeEquivSum hn label).symm)

theorem alternatingPuncturedPrefixChainPartner_involutive {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Function.Involutive (alternatingPuncturedPrefixChainPartner hn label) := by
  intro data
  apply (alternatingPuncturedPrefixChainTypeEquivSum hn label).injective
  cases hdata : (alternatingPuncturedPrefixChainTypeEquivSum hn label) data with
  | inl positive =>
      simp [alternatingPuncturedPrefixChainPartner, hdata,
        positivePuncturedPrefixChainPartner_involutive label positive]
  | inr negative =>
      simp [alternatingPuncturedPrefixChainPartner, hdata,
        negativePuncturedPrefixChainPartner_involutive label negative]

theorem alternatingPuncturedPrefixChainPartner_fixedPointFree {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (data : AlternatingPuncturedPrefixChainType label) :
    alternatingPuncturedPrefixChainPartner hn label data ≠ data := by
  intro h
  have hsum := congrArg (alternatingPuncturedPrefixChainTypeEquivSum hn label) h
  cases hdata : (alternatingPuncturedPrefixChainTypeEquivSum hn label) data with
  | inl positive =>
      exact positivePuncturedPrefixChainPartner_fixedPointFree label positive
        (by simpa [alternatingPuncturedPrefixChainPartner, hdata] using hsum)
  | inr negative =>
      exact negativePuncturedPrefixChainPartner_fixedPointFree label negative
        (by simpa [alternatingPuncturedPrefixChainPartner, hdata] using hsum)

theorem alternatingPuncturedPrefixChainTypeEquivSum_symm_inl_val {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (positive : PositivePuncturedPrefixChainType label) :
    ((alternatingPuncturedPrefixChainTypeEquivSum hn label).symm
        (Sum.inl positive)).1 = positive.1 := by
  classical
  simp [alternatingPuncturedPrefixChainTypeEquivSum, Equiv.subtypeEquivProp]

theorem alternatingPuncturedPrefixChainTypeEquivSum_symm_inr_val {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (negative : NegativePuncturedPrefixChainType label) :
    ((alternatingPuncturedPrefixChainTypeEquivSum hn label).symm
        (Sum.inr negative)).1 = negative.1 := by
  classical
  simp [alternatingPuncturedPrefixChainTypeEquivSum, Equiv.subtypeEquivProp]

theorem alternatingPuncturedPrefixChainPartner_val {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (data : AlternatingPuncturedPrefixChainType label) :
    (alternatingPuncturedPrefixChainPartner hn label data).1 =
      puncturedPrefixPartnerData data.1 := by
  cases hdata : (alternatingPuncturedPrefixChainTypeEquivSum hn label) data with
  | inl positive =>
      have hdata_val : data.1 = positive.1 := by
        have h := congrArg
          (fun endpoint =>
            ((alternatingPuncturedPrefixChainTypeEquivSum hn label).symm endpoint).1)
          hdata
        simpa [alternatingPuncturedPrefixChainTypeEquivSum_symm_inl_val hn label positive]
          using h
      calc
        ((alternatingPuncturedPrefixChainPartner hn label data).1) =
            ((alternatingPuncturedPrefixChainTypeEquivSum hn label).symm
              (Sum.inl ((positivePuncturedPrefixChainPartner label) positive))).1 := by
          simp [alternatingPuncturedPrefixChainPartner, hdata]
        _ = ((positivePuncturedPrefixChainPartner label) positive).1 := by
          exact alternatingPuncturedPrefixChainTypeEquivSum_symm_inl_val hn label
            ((positivePuncturedPrefixChainPartner label) positive)
        _ = puncturedPrefixPartnerData positive.1 := by
          exact positivePuncturedPrefixChainPartner_val label positive
        _ = puncturedPrefixPartnerData data.1 := by
          rw [hdata_val]
  | inr negative =>
      have hdata_val : data.1 = negative.1 := by
        have h := congrArg
          (fun endpoint =>
            ((alternatingPuncturedPrefixChainTypeEquivSum hn label).symm endpoint).1)
          hdata
        simpa [alternatingPuncturedPrefixChainTypeEquivSum_symm_inr_val hn label negative]
          using h
      calc
        ((alternatingPuncturedPrefixChainPartner hn label data).1) =
            ((alternatingPuncturedPrefixChainTypeEquivSum hn label).symm
              (Sum.inr ((negativePuncturedPrefixChainPartner label) negative))).1 := by
          simp [alternatingPuncturedPrefixChainPartner, hdata]
        _ = ((negativePuncturedPrefixChainPartner label) negative).1 := by
          exact alternatingPuncturedPrefixChainTypeEquivSum_symm_inr_val hn label
            ((negativePuncturedPrefixChainPartner label) negative)
        _ = puncturedPrefixPartnerData negative.1 := by
          exact negativePuncturedPrefixChainPartner_val label negative
        _ = puncturedPrefixPartnerData data.1 := by
          rw [hdata_val]

/-- Statement-level API for the codimension-one alternating facet count. -/
def KyFanPuncturedPrefixDivisibilityStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset (n + 1) → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      4 ∣ (alternatingPuncturedPrefixLabelChains label).card

theorem kyFanPuncturedPrefixDivisibilityStatement {n m : ℕ} (hn : 0 < n) :
    KyFanPuncturedPrefixDivisibilityStatement n m := by
  intro label hantipodal
  exact four_dvd_alternatingPuncturedPrefixLabelChains_card hn label hantipodal

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
Endpoint count with an explicit punctured-endpoint class.  This is the
counting core used once the path graph's endpoints have been partitioned into
punctured endpoints, the two base endpoints, and positive/negative top
alternating chains.
-/
theorem odd_positive_endpoints_of_antipodal_path_count_with_punctured
    (punctured positive negative pathCount : ℕ)
    (hneg : negative = positive)
    (hpath_even : Even pathCount)
    (hpunctured : 4 ∣ punctured)
    (hendpoints : punctured + 2 + positive + negative = 2 * pathCount) :
    Odd positive := by
  rcases hpath_even with ⟨r, hr⟩
  rcases hpunctured with ⟨s, hs⟩
  rw [Nat.odd_iff]
  omega

theorem odd_card_positive_endpoints_of_path_involution_with_punctured
    {Path Punctured Positive Negative : Type*}
    [Fintype Path] [Fintype Punctured] [Fintype Positive] [Fintype Negative]
    (pathAntipode : Path ≃ Path)
    (hinv : Function.Involutive pathAntipode)
    (hfree : ∀ p : Path, pathAntipode p ≠ p)
    (hneg : Fintype.card Negative = Fintype.card Positive)
    (hpunctured : 4 ∣ Fintype.card Punctured)
    (hendpoints :
      Fintype.card Punctured + 2 + Fintype.card Positive + Fintype.card Negative =
        2 * Fintype.card Path) :
    Odd (Fintype.card Positive) := by
  exact odd_positive_endpoints_of_antipodal_path_count_with_punctured
    (Fintype.card Punctured) (Fintype.card Positive) (Fintype.card Negative)
    (Fintype.card Path) hneg
    (even_card_of_fixedPointFree_involutive pathAntipode hinv hfree)
    hpunctured hendpoints

theorem sigma_endpoint_card_eq_two_mul_paths
    {Path : Type*} [Fintype Path]
    (Endpoint : Path → Type*) [∀ p : Path, Fintype (Endpoint p)]
    (htwo : ∀ p : Path, Fintype.card (Endpoint p) = 2) :
    Fintype.card (Σ p : Path, Endpoint p) = 2 * Fintype.card Path := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ p : Path, Fintype.card (Endpoint p)) = ∑ _p : Path, 2 := by
      exact Finset.sum_congr rfl fun p _ => htwo p
    _ = 2 * Fintype.card Path := by
      simp [mul_comm]

theorem endpoint_card_eq_base_add_positive_add_negative
    {Endpoint Base Positive Negative : Type*}
    [Fintype Endpoint] [Fintype Base] [Fintype Positive] [Fintype Negative]
    (classify : Endpoint ≃ Base ⊕ (Positive ⊕ Negative)) :
    Fintype.card Endpoint =
      Fintype.card Base + Fintype.card Positive + Fintype.card Negative := by
  have hcard := Fintype.card_congr classify
  rw [hcard]
  simp [Fintype.card_sum]
  omega

theorem endpoint_card_eq_punctured_add_base_add_positive_add_negative
    {Endpoint Punctured Base Positive Negative : Type*}
    [Fintype Endpoint] [Fintype Punctured] [Fintype Base]
    [Fintype Positive] [Fintype Negative]
    (classify : Endpoint ≃ Punctured ⊕ (Base ⊕ (Positive ⊕ Negative))) :
    Fintype.card Endpoint =
      Fintype.card Punctured + Fintype.card Base +
        Fintype.card Positive + Fintype.card Negative := by
  have hcard := Fintype.card_congr classify
  rw [hcard]
  simp [Fintype.card_sum]
  omega

theorem endpoint_count_eq_two_mul_paths_of_endpoint_equiv
    {Path Base Positive Negative : Type*}
    [Fintype Path] [Fintype Base] [Fintype Positive] [Fintype Negative]
    (Endpoint : Path → Type*) [∀ p : Path, Fintype (Endpoint p)]
    (htwo : ∀ p : Path, Fintype.card (Endpoint p) = 2)
    (classify : (Σ p : Path, Endpoint p) ≃ Base ⊕ (Positive ⊕ Negative))
    (hbase : Fintype.card Base = 2) :
    2 + Fintype.card Positive + Fintype.card Negative = 2 * Fintype.card Path := by
  have hpath := sigma_endpoint_card_eq_two_mul_paths Endpoint htwo
  have hclass := endpoint_card_eq_base_add_positive_add_negative classify
  rw [hbase] at hclass
  omega

theorem endpoint_count_eq_two_mul_paths_of_endpoint_equiv_with_punctured
    {Path Punctured Base Positive Negative : Type*}
    [Fintype Path] [Fintype Punctured] [Fintype Base]
    [Fintype Positive] [Fintype Negative]
    (Endpoint : Path → Type*) [∀ p : Path, Fintype (Endpoint p)]
    (htwo : ∀ p : Path, Fintype.card (Endpoint p) = 2)
    (classify :
      (Σ p : Path, Endpoint p) ≃ Punctured ⊕ (Base ⊕ (Positive ⊕ Negative)))
    (hbase : Fintype.card Base = 2) :
    Fintype.card Punctured + 2 + Fintype.card Positive + Fintype.card Negative =
      2 * Fintype.card Path := by
  have hpath := sigma_endpoint_card_eq_two_mul_paths Endpoint htwo
  have hclass := endpoint_card_eq_punctured_add_base_add_positive_add_negative classify
  rw [hbase] at hclass
  omega

/--
Structured endpoint-count version of the abstract path parity theorem.

Instead of passing the endpoint-count equality directly, it is enough to give:
each path has two endpoints, and all endpoints are classified as the two base
endpoints, positive top endpoints, or negative top endpoints.
-/
theorem odd_card_positive_endpoints_of_path_endpoint_equiv
    {Path Base Positive Negative : Type*}
    [Fintype Path] [Fintype Base] [Fintype Positive] [Fintype Negative]
    (Endpoint : Path → Type*) [∀ p : Path, Fintype (Endpoint p)]
    (pathAntipode : Path ≃ Path)
    (hinv : Function.Involutive pathAntipode)
    (hfree : ∀ p : Path, pathAntipode p ≠ p)
    (htwo : ∀ p : Path, Fintype.card (Endpoint p) = 2)
    (classify : (Σ p : Path, Endpoint p) ≃ Base ⊕ (Positive ⊕ Negative))
    (hbase : Fintype.card Base = 2)
    (hneg : Fintype.card Negative = Fintype.card Positive) :
    Odd (Fintype.card Positive) := by
  exact odd_card_positive_endpoints_of_path_involution pathAntipode hinv hfree hneg
    (endpoint_count_eq_two_mul_paths_of_endpoint_equiv Endpoint htwo classify hbase)

/--
Structured endpoint-count version with a punctured-endpoint class.

The endpoint classification has four pieces: punctured endpoints, the two base
endpoints, positive top chains, and negative top chains.  The only additional
numeric input is that the punctured endpoint class has cardinality divisible by
four.
-/
theorem odd_card_positive_endpoints_of_path_endpoint_equiv_with_punctured
    {Path Punctured Base Positive Negative : Type*}
    [Fintype Path] [Fintype Punctured] [Fintype Base]
    [Fintype Positive] [Fintype Negative]
    (Endpoint : Path → Type*) [∀ p : Path, Fintype (Endpoint p)]
    (pathAntipode : Path ≃ Path)
    (hinv : Function.Involutive pathAntipode)
    (hfree : ∀ p : Path, pathAntipode p ≠ p)
    (htwo : ∀ p : Path, Fintype.card (Endpoint p) = 2)
    (classify :
      (Σ p : Path, Endpoint p) ≃ Punctured ⊕ (Base ⊕ (Positive ⊕ Negative)))
    (hbase : Fintype.card Base = 2)
    (hpunctured : 4 ∣ Fintype.card Punctured)
    (hneg : Fintype.card Negative = Fintype.card Positive) :
    Odd (Fintype.card Positive) := by
  exact odd_card_positive_endpoints_of_path_involution_with_punctured
    pathAntipode hinv hfree hneg hpunctured
    (endpoint_count_eq_two_mul_paths_of_endpoint_equiv_with_punctured
      Endpoint htwo classify hbase)

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

/--
Ky Fan prefix parity from a structured path endpoint decomposition.

The target endpoint classes are exactly the positive- and negative-first
alternating signed-permutation prefix chains.  A later octahedral-path
construction only has to provide `Endpoint`, the antipodal involution on paths,
the two-endpoints-per-path proof, and the endpoint classification equivalence.
-/
theorem kyFanPrefixParity_of_path_endpoint_equiv {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    {Path Base : Type*} [Fintype Path] [Fintype Base]
    (Endpoint : Path → Type*) [∀ p : Path, Fintype (Endpoint p)]
    (pathAntipode : Path ≃ Path)
    (hinv : Function.Involutive pathAntipode)
    (hfree : ∀ p : Path, pathAntipode p ≠ p)
    (htwo : ∀ p : Path, Fintype.card (Endpoint p) = 2)
    (classify :
      (Σ p : Path, Endpoint p) ≃
        Base ⊕
          ({P : SignedPermutation n // P ∈ positiveAlternatingPrefixLabelChains label} ⊕
            {P : SignedPermutation n // P ∈ negativeAlternatingPrefixLabelChains label}))
    (hbase : Fintype.card Base = 2) :
    Odd (positiveAlternatingPrefixLabelChains label).card := by
  classical
  let Positive := {P : SignedPermutation n // P ∈ positiveAlternatingPrefixLabelChains label}
  let Negative := {P : SignedPermutation n // P ∈ negativeAlternatingPrefixLabelChains label}
  have hneg : Fintype.card Negative = Fintype.card Positive := by
    simp [Positive, Negative, positiveAlternatingPrefixLabelChains_card_eq_negative label hantipodal]
  have hodd :
      Odd (Fintype.card Positive) :=
    odd_card_positive_endpoints_of_path_endpoint_equiv
      (Path := Path) (Base := Base) (Positive := Positive) (Negative := Negative)
      Endpoint pathAntipode hinv hfree htwo classify hbase hneg
  simpa [Positive] using hodd

/--
Packaged endpoint data for the Prescott-Su/Fan path proof.  The parameters
`Positive` and `Negative` are the two top-dimensional endpoint classes.
-/
structure PathEndpointDecomposition (Positive Negative : Type) [Fintype Positive]
    [Fintype Negative] where
  Path : Type
  Base : Type
  Endpoint : Path → Type
  instPath : Fintype Path
  instBase : Fintype Base
  instEndpoint : ∀ p : Path, Fintype (Endpoint p)
  pathAntipode : Path ≃ Path
  pathAntipode_involutive : Function.Involutive pathAntipode
  pathAntipode_fixedPointFree : ∀ p : Path, pathAntipode p ≠ p
  endpoint_card_two : ∀ p : Path, Fintype.card (Endpoint p) = 2
  classify : (Σ p : Path, Endpoint p) ≃ Base ⊕ (Positive ⊕ Negative)
  base_card : Fintype.card Base = 2

namespace PathEndpointDecomposition

theorem positive_card_odd {Positive Negative : Type} [Fintype Positive] [Fintype Negative]
    (D : PathEndpointDecomposition Positive Negative)
    (hneg : Fintype.card Negative = Fintype.card Positive) :
    Odd (Fintype.card Positive) := by
  letI := D.instPath
  letI := D.instBase
  letI : ∀ p : D.Path, Fintype (D.Endpoint p) := D.instEndpoint
  exact odd_card_positive_endpoints_of_path_endpoint_equiv
    D.Endpoint D.pathAntipode D.pathAntipode_involutive D.pathAntipode_fixedPointFree
    D.endpoint_card_two D.classify D.base_card hneg

end PathEndpointDecomposition

/--
Path endpoint data with the punctured-endpoint class kept explicit.  This is
the finite combinatorial shape of the Ky Fan path graph before the punctured
endpoints are discarded modulo four.
-/
structure PathEndpointDecompositionWithPunctured
    (Punctured Positive Negative : Type) [Fintype Punctured]
    [Fintype Positive] [Fintype Negative] where
  Path : Type
  Base : Type
  Endpoint : Path → Type
  instPath : Fintype Path
  instBase : Fintype Base
  instEndpoint : ∀ p : Path, Fintype (Endpoint p)
  pathAntipode : Path ≃ Path
  pathAntipode_involutive : Function.Involutive pathAntipode
  pathAntipode_fixedPointFree : ∀ p : Path, pathAntipode p ≠ p
  endpoint_card_two : ∀ p : Path, Fintype.card (Endpoint p) = 2
  classify : (Σ p : Path, Endpoint p) ≃ Punctured ⊕ (Base ⊕ (Positive ⊕ Negative))
  base_card : Fintype.card Base = 2

namespace PathEndpointDecompositionWithPunctured

theorem positive_card_odd {Punctured Positive Negative : Type}
    [Fintype Punctured] [Fintype Positive] [Fintype Negative]
    (D : PathEndpointDecompositionWithPunctured Punctured Positive Negative)
    (hpunctured : 4 ∣ Fintype.card Punctured)
    (hneg : Fintype.card Negative = Fintype.card Positive) :
    Odd (Fintype.card Positive) := by
  letI := D.instPath
  letI := D.instBase
  letI : ∀ p : D.Path, Fintype (D.Endpoint p) := D.instEndpoint
  exact odd_card_positive_endpoints_of_path_endpoint_equiv_with_punctured
    D.Endpoint D.pathAntipode D.pathAntipode_involutive D.pathAntipode_fixedPointFree
    D.endpoint_card_two D.classify D.base_card hpunctured hneg

end PathEndpointDecompositionWithPunctured

/--
The path represented by the two endpoint orbit `{x, partner x}` of a
fixed-point-free endpoint pairing.
-/
abbrev TwoCyclePath {α : Type*} [DecidableEq α] (partner : α ≃ α) :=
  {s : Finset α // ∃ x, s = {x, partner x}}

abbrev TwoCycleEndpoint {α : Type*} [DecidableEq α] {partner : α ≃ α}
    (path : TwoCyclePath partner) :=
  {x : α // x ∈ path.1}

def twoCyclePathOf {α : Type*} [DecidableEq α] (partner : α ≃ α) (x : α) :
    TwoCyclePath partner :=
  ⟨{x, partner x}, ⟨x, rfl⟩⟩

theorem twoCycle_pair_eq_of_mem {α : Type*} [DecidableEq α] {partner : α ≃ α}
    (hinv : Function.Involutive partner) {root x : α}
    (hx : x ∈ ({root, partner root} : Finset α)) :
    ({x, partner x} : Finset α) = {root, partner root} := by
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | hx
  · rfl
  · subst x
    ext y
    simp [hinv root, eq_comm, or_comm]

theorem twoCyclePathOf_eq_of_mem {α : Type*} [DecidableEq α] {partner : α ≃ α}
    (hinv : Function.Involutive partner) {path : TwoCyclePath partner} {x : α}
    (hx : x ∈ path.1) :
    twoCyclePathOf partner x = path := by
  rcases path with ⟨s, root, rfl⟩
  apply Subtype.ext
  exact twoCycle_pair_eq_of_mem hinv hx

theorem twoCycleEndpoint_card {α : Type*} [Fintype α] [DecidableEq α]
    {partner : α ≃ α} (hfree : ∀ x : α, partner x ≠ x)
    (path : TwoCyclePath partner) :
    Fintype.card (TwoCycleEndpoint path) = 2 := by
  classical
  rcases path with ⟨s, x, rfl⟩
  have hne : x ≠ partner x := by
    intro h
    exact hfree x h.symm
  simpa [TwoCycleEndpoint, Finset.mem_insert, Finset.mem_singleton, eq_comm] using
    (Fintype.card_subtype_eq_or_eq_of_ne (α := α) (a := x) (b := partner x) hne)

noncomputable def twoCycleEndpointClassify {α : Type*} [Fintype α] [DecidableEq α]
    {partner : α ≃ α} (hinv : Function.Involutive partner) :
    (Σ path : TwoCyclePath partner, TwoCycleEndpoint path) ≃ α :=
  Equiv.ofBijective (fun endpoint => endpoint.2.1) ⟨by
    rintro ⟨path, endpoint⟩ ⟨path', endpoint'⟩ hendpoint
    change endpoint.1 = endpoint'.1 at hendpoint
    have endpoint'_mem : endpoint.1 ∈ path'.1 := by
      rw [hendpoint]
      exact endpoint'.2
    have hpath : path = path' := by
      have hleft : twoCyclePathOf partner endpoint.1 = path :=
        twoCyclePathOf_eq_of_mem hinv endpoint.2
      have hright : twoCyclePathOf partner endpoint.1 = path' :=
        twoCyclePathOf_eq_of_mem hinv endpoint'_mem
      exact hleft.symm.trans hright
    cases hpath
    have hendpoint' : endpoint = endpoint' := Subtype.ext hendpoint
    cases hendpoint'
    rfl, by
    intro x
    refine ⟨⟨twoCyclePathOf partner x, ⟨x, ?_⟩⟩, rfl⟩
    simp [twoCyclePathOf]⟩

noncomputable def twoCyclePathAntipode {α : Type*} [Fintype α] [DecidableEq α]
    {partner endpointAntipode : α ≃ α}
    (hendpointAntipode_involutive : Function.Involutive endpointAntipode)
    (hcomm : ∀ x : α, endpointAntipode (partner x) = partner (endpointAntipode x)) :
    TwoCyclePath partner ≃ TwoCyclePath partner where
  toFun path := by
    refine ⟨path.1.image endpointAntipode, ?_⟩
    rcases path with ⟨s, hs⟩
    rcases hs with ⟨x, hx⟩
    subst s
    refine ⟨endpointAntipode x, ?_⟩
    ext y
    simp [hcomm x]
  invFun path := by
    refine ⟨path.1.image endpointAntipode, ?_⟩
    rcases path with ⟨s, hs⟩
    rcases hs with ⟨x, hx⟩
    subst s
    refine ⟨endpointAntipode x, ?_⟩
    ext y
    simp [hcomm x]
  left_inv := by
    rintro ⟨s, hs⟩
    rcases hs with ⟨x, hx⟩
    subst s
    apply Subtype.ext
    ext y
    simp [hendpointAntipode_involutive x, hendpointAntipode_involutive (partner x)]
  right_inv := by
    rintro ⟨s, hs⟩
    rcases hs with ⟨x, hx⟩
    subst s
    apply Subtype.ext
    ext y
    simp [hendpointAntipode_involutive x, hendpointAntipode_involutive (partner x)]

theorem twoCyclePathAntipode_involutive {α : Type*} [Fintype α] [DecidableEq α]
    {partner endpointAntipode : α ≃ α}
    (hendpointAntipode_involutive : Function.Involutive endpointAntipode)
    (hcomm : ∀ x : α, endpointAntipode (partner x) = partner (endpointAntipode x)) :
    Function.Involutive
      (twoCyclePathAntipode (partner := partner) (endpointAntipode := endpointAntipode)
        hendpointAntipode_involutive hcomm) := by
  intro path
  exact (twoCyclePathAntipode (partner := partner) (endpointAntipode := endpointAntipode)
    hendpointAntipode_involutive hcomm).left_inv path

theorem twoCyclePathAntipode_fixedPointFree {α : Type*} [Fintype α] [DecidableEq α]
    {partner endpointAntipode : α ≃ α}
    (hendpointAntipode_involutive : Function.Involutive endpointAntipode)
    (hcomm : ∀ x : α, endpointAntipode (partner x) = partner (endpointAntipode x))
    (hendpointAntipode_fixedPointFree : ∀ x : α, endpointAntipode x ≠ x)
    (hendpointAntipode_not_partner : ∀ x : α, endpointAntipode x ≠ partner x)
    (path : TwoCyclePath partner) :
    twoCyclePathAntipode (partner := partner) (endpointAntipode := endpointAntipode)
      hendpointAntipode_involutive hcomm path ≠ path := by
  intro hpath
  rcases path with ⟨s, hs⟩
  rcases hs with ⟨x, hx⟩
  subst s
  have hcarrier := congrArg Subtype.val hpath
  have hxmem :
      endpointAntipode x ∈ ({x, partner x} : Finset α) := by
    have hximage :
        endpointAntipode x ∈
          Finset.image endpointAntipode ({x, partner x} : Finset α) := by
      simp
    have hcarrier' :
        Finset.image endpointAntipode ({x, partner x} : Finset α) =
          {x, partner x} := by
      simpa [twoCyclePathAntipode] using hcarrier
    rw [hcarrier'] at hximage
    exact hximage
  rw [Finset.mem_insert, Finset.mem_singleton] at hxmem
  rcases hxmem with hx | hx
  · exact hendpointAntipode_fixedPointFree x hx
  · exact hendpointAntipode_not_partner x hx

noncomputable def pathEndpointDecompositionWithPunctured_of_endpointPartner
    {Punctured Base Positive Negative : Type}
    [Fintype Punctured] [Fintype Base] [Fintype Positive] [Fintype Negative]
    [DecidableEq (Punctured ⊕ (Base ⊕ (Positive ⊕ Negative)))]
    (endpointPartner :
      Punctured ⊕ (Base ⊕ (Positive ⊕ Negative)) ≃
        Punctured ⊕ (Base ⊕ (Positive ⊕ Negative)))
    (endpointPartner_involutive : Function.Involutive endpointPartner)
    (endpointPartner_fixedPointFree : ∀ endpoint, endpointPartner endpoint ≠ endpoint)
    (endpointAntipode :
      Punctured ⊕ (Base ⊕ (Positive ⊕ Negative)) ≃
        Punctured ⊕ (Base ⊕ (Positive ⊕ Negative)))
    (endpointAntipode_involutive : Function.Involutive endpointAntipode)
    (endpointAntipode_fixedPointFree : ∀ endpoint, endpointAntipode endpoint ≠ endpoint)
    (endpointAntipode_comm :
      ∀ endpoint, endpointAntipode (endpointPartner endpoint) =
        endpointPartner (endpointAntipode endpoint))
    (endpointAntipode_not_partner :
      ∀ endpoint, endpointAntipode endpoint ≠ endpointPartner endpoint)
    (hbase : Fintype.card Base = 2) :
    PathEndpointDecompositionWithPunctured Punctured Positive Negative where
  Path := TwoCyclePath endpointPartner
  Base := Base
  Endpoint := fun path => TwoCycleEndpoint path
  instPath := inferInstance
  instBase := inferInstance
  instEndpoint := fun _ => inferInstance
  pathAntipode :=
    twoCyclePathAntipode
      (partner := endpointPartner) (endpointAntipode := endpointAntipode)
      endpointAntipode_involutive endpointAntipode_comm
  pathAntipode_involutive :=
    twoCyclePathAntipode_involutive
      (partner := endpointPartner) (endpointAntipode := endpointAntipode)
      endpointAntipode_involutive endpointAntipode_comm
  pathAntipode_fixedPointFree :=
    twoCyclePathAntipode_fixedPointFree
      (partner := endpointPartner) (endpointAntipode := endpointAntipode)
      endpointAntipode_involutive endpointAntipode_comm
      endpointAntipode_fixedPointFree endpointAntipode_not_partner
  endpoint_card_two :=
    twoCycleEndpoint_card endpointPartner_fixedPointFree
  classify :=
    twoCycleEndpointClassify endpointPartner_involutive
  base_card := hbase

abbrev PositivePrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) :=
  {P : SignedPermutation n // P ∈ positiveAlternatingPrefixLabelChains label}

abbrev NegativePrefixChainType {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) :=
  {P : SignedPermutation n // P ∈ negativeAlternatingPrefixLabelChains label}

theorem positivePrefixChainType_card_zero {m : ℕ}
    (label : NonzeroSignedSubset 0 → SignedLabel m) :
    Fintype.card (PositivePrefixChainType label) = 1 := by
  change Fintype.card {P : SignedPermutation 0 // P ∈ positiveAlternatingPrefixLabelChains label} = 1
  rw [positiveAlternatingPrefixLabelChains_zero_eq_univ label]
  simp [SignedPermutation.card_zero]

theorem negativePrefixChainType_card_zero {m : ℕ}
    (label : NonzeroSignedSubset 0 → SignedLabel m) :
    Fintype.card (NegativePrefixChainType label) = 1 := by
  change Fintype.card {P : SignedPermutation 0 // P ∈ negativeAlternatingPrefixLabelChains label} = 1
  rw [negativeAlternatingPrefixLabelChains_zero_eq_univ label]
  simp [SignedPermutation.card_zero]

abbrev KyFanPrefixPathEndpointDecomposition {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) :=
  PathEndpointDecomposition (PositivePrefixChainType label) (NegativePrefixChainType label)

abbrev KyFanPrefixPathEndpointDecompositionWithPunctured {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :=
  PathEndpointDecompositionWithPunctured
    (AlternatingPuncturedPrefixChainType label)
    (PositivePrefixChainType label)
    (NegativePrefixChainType label)

abbrev KyFanPathEndpointClass {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :=
  AlternatingPuncturedPrefixChainType label ⊕
    (Bool ⊕ (PositivePrefixChainType label ⊕ NegativePrefixChainType label))

theorem kyFanPathEndpointClass_card {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Fintype.card (KyFanPathEndpointClass label) =
      Fintype.card (AlternatingPuncturedPrefixChainType label) + 2 +
        Fintype.card (PositivePrefixChainType label) +
          Fintype.card (NegativePrefixChainType label) := by
  simp [KyFanPathEndpointClass, Fintype.card_sum]
  omega

theorem kyFanPathEndpointClass_card_finset {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    Fintype.card (KyFanPathEndpointClass label) =
      (alternatingPuncturedPrefixLabelChains label).card + 2 +
        (positiveAlternatingPrefixLabelChains label).card +
          (negativeAlternatingPrefixLabelChains label).card := by
  rw [kyFanPathEndpointClass_card label,
    alternatingPuncturedPrefixChainType_card label]
  simp [PositivePrefixChainType, NegativePrefixChainType]

theorem mem_alternatingPuncturedPrefixLabelChains_antipode {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    {data : SignedPermutation (n + 1) × Fin (n + 1)}
    (hmem : data ∈ alternatingPuncturedPrefixLabelChains label) :
    puncturedPrefixAntipode data ∈ alternatingPuncturedPrefixLabelChains label := by
  classical
  rcases data with ⟨P, gap⟩
  rw [alternatingPuncturedPrefixLabelChains] at hmem ⊢
  rcases Finset.mem_union.mp hmem with hpos | hneg
  · have hposLabels : PositiveAlternatingPuncturedPrefixLabels label P gap := by
      simpa [positiveAlternatingPuncturedPrefixLabelChains] using hpos
    have hnegLabels : NegativeAlternatingPuncturedPrefixLabels label P.antipode gap := by
      have hiff := positiveAlternatingPuncturedPrefixLabels_antipode_iff label hantipodal
        P.antipode gap
      have hpos' :
          PositiveAlternatingPuncturedPrefixLabels label P.antipode.antipode gap := by
        simpa [SignedPermutation.antipode_involutive P] using hposLabels
      exact hiff.mp hpos'
    exact Finset.mem_union_right _
      (by simpa [negativeAlternatingPuncturedPrefixLabelChains, puncturedPrefixAntipode]
        using hnegLabels)
  · have hnegLabels : NegativeAlternatingPuncturedPrefixLabels label P gap := by
      simpa [negativeAlternatingPuncturedPrefixLabelChains] using hneg
    have hposLabels : PositiveAlternatingPuncturedPrefixLabels label P.antipode gap :=
      (positiveAlternatingPuncturedPrefixLabels_antipode_iff label hantipodal P gap).mpr
        hnegLabels
    exact Finset.mem_union_left _
      (by simpa [positiveAlternatingPuncturedPrefixLabelChains, puncturedPrefixAntipode]
        using hposLabels)

noncomputable def alternatingPuncturedPrefixChainAntipode {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    AlternatingPuncturedPrefixChainType label ≃ AlternatingPuncturedPrefixChainType label where
  toFun data :=
    ⟨puncturedPrefixAntipode data.1,
      mem_alternatingPuncturedPrefixLabelChains_antipode hantipodal data.2⟩
  invFun data :=
    ⟨puncturedPrefixAntipode data.1,
      mem_alternatingPuncturedPrefixLabelChains_antipode hantipodal data.2⟩
  left_inv := by
    rintro ⟨⟨P, gap⟩, hmem⟩
    apply Subtype.ext
    simp [puncturedPrefixAntipode, SignedPermutation.antipode_involutive P]
  right_inv := by
    rintro ⟨⟨P, gap⟩, hmem⟩
    apply Subtype.ext
    simp [puncturedPrefixAntipode, SignedPermutation.antipode_involutive P]

theorem alternatingPuncturedPrefixChainAntipode_fixedPointFree {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (data : AlternatingPuncturedPrefixChainType label) :
    alternatingPuncturedPrefixChainAntipode label hantipodal data ≠ data := by
  intro h
  rcases data with ⟨⟨P, gap⟩, hmem⟩
  have hP := congrArg (fun data : AlternatingPuncturedPrefixChainType label => data.1.1) h
  simp [alternatingPuncturedPrefixChainAntipode, puncturedPrefixAntipode] at hP
  exact SignedPermutation.antipode_ne_self (by omega) P hP

theorem alternatingPuncturedPrefixChainAntipode_involutive {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    Function.Involutive (alternatingPuncturedPrefixChainAntipode label hantipodal) := by
  intro data
  exact (alternatingPuncturedPrefixChainAntipode label hantipodal).left_inv data

theorem alternatingPuncturedPrefixChainPartner_antipode_comm {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (data : AlternatingPuncturedPrefixChainType label) :
    alternatingPuncturedPrefixChainAntipode label hantipodal
        (alternatingPuncturedPrefixChainPartner hn label data) =
      alternatingPuncturedPrefixChainPartner hn label
        (alternatingPuncturedPrefixChainAntipode label hantipodal data) := by
  apply Subtype.ext
  change puncturedPrefixAntipode ((alternatingPuncturedPrefixChainPartner hn label data).1) =
    (alternatingPuncturedPrefixChainPartner hn label
      (alternatingPuncturedPrefixChainAntipode label hantipodal data)).1
  rw [alternatingPuncturedPrefixChainPartner_val hn label data,
    alternatingPuncturedPrefixChainPartner_val hn label
      (alternatingPuncturedPrefixChainAntipode label hantipodal data)]
  exact (puncturedPrefixPartnerData_antipode data.1).symm

theorem alternatingPuncturedPrefixChainPartner_not_antipodal {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (data : AlternatingPuncturedPrefixChainType label) :
    alternatingPuncturedPrefixChainAntipode label hantipodal data ≠
      alternatingPuncturedPrefixChainPartner hn label data := by
  intro h
  have hval := congrArg Subtype.val h
  change puncturedPrefixAntipode data.1 =
    (alternatingPuncturedPrefixChainPartner hn label data).1 at hval
  rw [alternatingPuncturedPrefixChainPartner_val hn label data] at hval
  exact puncturedPrefixPartnerData_ne_antipode hn data.1 hval.symm

noncomputable def positivePrefixChainAntipode {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    PositivePrefixChainType label ≃ NegativePrefixChainType label where
  toFun P := by
    classical
    refine ⟨P.1.antipode, ?_⟩
    have hpos : PositiveAlternatingPrefixLabels label P.1 := by
      have hmem := P.2
      unfold positiveAlternatingPrefixLabelChains at hmem
      exact (Finset.mem_filter.mp hmem).2
    have hneg : NegativeAlternatingPrefixLabels label P.1.antipode := by
      have hiff := positiveAlternatingPrefixLabels_antipode_iff label hantipodal P.1.antipode
      have hpos' : PositiveAlternatingPrefixLabels label P.1.antipode.antipode := by
        simpa [SignedPermutation.antipode_involutive P.1] using hpos
      exact hiff.mp hpos'
    simpa [negativeAlternatingPrefixLabelChains] using hneg
  invFun N := by
    classical
    refine ⟨N.1.antipode, ?_⟩
    have hneg : NegativeAlternatingPrefixLabels label N.1 := by
      have hmem := N.2
      unfold negativeAlternatingPrefixLabelChains at hmem
      exact (Finset.mem_filter.mp hmem).2
    have hpos : PositiveAlternatingPrefixLabels label N.1.antipode :=
      (positiveAlternatingPrefixLabels_antipode_iff label hantipodal N.1).mpr hneg
    simpa [positiveAlternatingPrefixLabelChains] using hpos
  left_inv := by
    intro P
    apply Subtype.ext
    exact SignedPermutation.antipode_involutive P.1
  right_inv := by
    intro N
    apply Subtype.ext
    exact SignedPermutation.antipode_involutive N.1

noncomputable def negativePrefixChainAntipode {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    NegativePrefixChainType label ≃ PositivePrefixChainType label :=
  (positivePrefixChainAntipode label hantipodal).symm

noncomputable def topPrefixChainEndpointAntipode {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    (PositivePrefixChainType label ⊕ NegativePrefixChainType label) ≃
      (PositivePrefixChainType label ⊕ NegativePrefixChainType label) where
  toFun endpoint :=
    match endpoint with
    | Sum.inl P => Sum.inr (positivePrefixChainAntipode label hantipodal P)
    | Sum.inr N => Sum.inl (negativePrefixChainAntipode label hantipodal N)
  invFun endpoint :=
    match endpoint with
    | Sum.inl P => Sum.inr (positivePrefixChainAntipode label hantipodal P)
    | Sum.inr N => Sum.inl (negativePrefixChainAntipode label hantipodal N)
  left_inv := by
    rintro (P | N) <;> simp [negativePrefixChainAntipode]
  right_inv := by
    rintro (P | N) <;> simp [negativePrefixChainAntipode]

theorem topPrefixChainEndpointAntipode_involutive {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    Function.Involutive (topPrefixChainEndpointAntipode label hantipodal) := by
  intro endpoint
  exact (topPrefixChainEndpointAntipode label hantipodal).left_inv endpoint

noncomputable def kyFanPathEndpointClassAntipode {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    KyFanPathEndpointClass label ≃ KyFanPathEndpointClass label :=
  Equiv.sumCongr
    (alternatingPuncturedPrefixChainAntipode label hantipodal)
    (Equiv.sumCongr Equiv.boolNot (topPrefixChainEndpointAntipode label hantipodal))

theorem kyFanPathEndpointClassAntipode_fixedPointFree {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (endpoint : KyFanPathEndpointClass label) :
    kyFanPathEndpointClassAntipode label hantipodal endpoint ≠ endpoint := by
  intro h
  rcases endpoint with punctured | rest
  · exact alternatingPuncturedPrefixChainAntipode_fixedPointFree label hantipodal punctured
      (by simpa [kyFanPathEndpointClassAntipode] using h)
  · rcases rest with base | top
    · cases base <;> simp [kyFanPathEndpointClassAntipode] at h
    · rcases top with positive | negative <;> simp [kyFanPathEndpointClassAntipode,
        topPrefixChainEndpointAntipode] at h

theorem kyFanPathEndpointClassAntipode_involutive {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    Function.Involutive (kyFanPathEndpointClassAntipode label hantipodal) := by
  intro endpoint
  rcases endpoint with punctured | rest
  · simpa [kyFanPathEndpointClassAntipode] using
      congrArg
        (fun x : AlternatingPuncturedPrefixChainType label =>
          (Sum.inl x : KyFanPathEndpointClass label))
        (alternatingPuncturedPrefixChainAntipode_involutive label hantipodal punctured)
  · rcases rest with base | top
    · cases base <;> rfl
    · change
        Sum.inr (Sum.inr
            (topPrefixChainEndpointAntipode label hantipodal
              (topPrefixChainEndpointAntipode label hantipodal top))) =
          Sum.inr (Sum.inr top)
      rw [topPrefixChainEndpointAntipode_involutive label hantipodal top]

structure KyFanConcretePathEndpointDecomposition {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) where
  Path : Type
  Endpoint : Path → Type
  instPath : Fintype Path
  instEndpoint : ∀ p : Path, Fintype (Endpoint p)
  pathAntipode : Path ≃ Path
  pathAntipode_involutive : Function.Involutive pathAntipode
  pathAntipode_fixedPointFree : ∀ p : Path, pathAntipode p ≠ p
  endpoint_card_two : ∀ p : Path, Fintype.card (Endpoint p) = 2
  classify : (Σ p : Path, Endpoint p) ≃ KyFanPathEndpointClass label

/--
The remaining local graph datum in the Ky Fan path proof, after the endpoint
classes and antipodal action have been formalized.  It is a fixed-point-free
pairing of endpoints into two-ended paths, commuting with antipodes, with no
path fixed by the antipodal action.
-/
structure KyFanEndpointPairing {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) where
  endpointPartner : KyFanPathEndpointClass label ≃ KyFanPathEndpointClass label
  endpointPartner_involutive : Function.Involutive endpointPartner
  endpointPartner_fixedPointFree : ∀ endpoint, endpointPartner endpoint ≠ endpoint
  endpointPartner_comm :
    ∀ endpoint,
      kyFanPathEndpointClassAntipode label hantipodal (endpointPartner endpoint) =
        endpointPartner (kyFanPathEndpointClassAntipode label hantipodal endpoint)
  endpointPartner_not_antipodal :
    ∀ endpoint,
      kyFanPathEndpointClassAntipode label hantipodal endpoint ≠ endpointPartner endpoint

theorem four_dvd_card_of_commuting_endpoint_pairing
    {α : Type*} [Fintype α] [DecidableEq α]
    {endpointPartner endpointAntipode : α ≃ α}
    (hpartner_involutive : Function.Involutive endpointPartner)
    (hpartner_fixedPointFree : ∀ endpoint, endpointPartner endpoint ≠ endpoint)
    (hantipode_involutive : Function.Involutive endpointAntipode)
    (hantipode_fixedPointFree : ∀ endpoint, endpointAntipode endpoint ≠ endpoint)
    (hcomm :
      ∀ endpoint, endpointAntipode (endpointPartner endpoint) =
        endpointPartner (endpointAntipode endpoint))
    (hnot_antipodal : ∀ endpoint, endpointAntipode endpoint ≠ endpointPartner endpoint) :
    4 ∣ Fintype.card α := by
  classical
  have hpath_even : Even (Fintype.card (TwoCyclePath endpointPartner)) :=
    even_card_of_fixedPointFree_involutive
      (twoCyclePathAntipode
        (partner := endpointPartner) (endpointAntipode := endpointAntipode)
        hantipode_involutive hcomm)
      (twoCyclePathAntipode_involutive
        (partner := endpointPartner) (endpointAntipode := endpointAntipode)
        hantipode_involutive hcomm)
      (twoCyclePathAntipode_fixedPointFree
        (partner := endpointPartner) (endpointAntipode := endpointAntipode)
        hantipode_involutive hcomm
        hantipode_fixedPointFree hnot_antipodal)
  rcases hpath_even with ⟨r, hr⟩
  have htwice :
      Fintype.card (Σ path : TwoCyclePath endpointPartner, TwoCycleEndpoint path) =
        2 * Fintype.card (TwoCyclePath endpointPartner) :=
    sigma_endpoint_card_eq_two_mul_paths
      (fun path : TwoCyclePath endpointPartner => TwoCycleEndpoint path)
      (twoCycleEndpoint_card hpartner_fixedPointFree)
  have hclass :
      Fintype.card (Σ path : TwoCyclePath endpointPartner, TwoCycleEndpoint path) =
        Fintype.card α :=
    Fintype.card_congr (twoCycleEndpointClassify hpartner_involutive)
  refine ⟨r, ?_⟩
  omega

theorem four_dvd_kyFanPathEndpointClass_card_of_endpointPairing
    {n m : ℕ} {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {hantipodal : ∀ X, label X.antipode = (label X).neg}
    (pairing : KyFanEndpointPairing label hantipodal) :
    4 ∣ Fintype.card (KyFanPathEndpointClass label) :=
  four_dvd_card_of_commuting_endpoint_pairing
    pairing.endpointPartner_involutive
    pairing.endpointPartner_fixedPointFree
    (kyFanPathEndpointClassAntipode_involutive label hantipodal)
    (kyFanPathEndpointClassAntipode_fixedPointFree label hantipodal)
    pairing.endpointPartner_comm
    pairing.endpointPartner_not_antipodal

theorem kyFanPrefixParity_of_endpointPairing_direct {n m : ℕ}
    (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (pairing : KyFanEndpointPairing label hantipodal) :
    Odd (positiveAlternatingPrefixLabelChains label).card := by
  classical
  rcases four_dvd_kyFanPathEndpointClass_card_of_endpointPairing pairing with ⟨r, hr⟩
  rcases four_dvd_alternatingPuncturedPrefixChainType_card hn label hantipodal with ⟨s, hs⟩
  have hneg :
      Fintype.card (NegativePrefixChainType label) =
        Fintype.card (PositivePrefixChainType label) := by
    simp [PositivePrefixChainType, NegativePrefixChainType,
      positiveAlternatingPrefixLabelChains_card_eq_negative label hantipodal]
  have hodd :
      Odd (Fintype.card (PositivePrefixChainType label)) := by
    rw [Nat.odd_iff]
    rw [kyFanPathEndpointClass_card label, hs, hneg] at hr
    omega
  simpa [PositivePrefixChainType] using hodd

noncomputable def kyFanConcretePathEndpointDecomposition_of_endpointPairing
    {n m : ℕ} {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {hantipodal : ∀ X, label X.antipode = (label X).neg}
    (pairing : KyFanEndpointPairing label hantipodal) :
    KyFanConcretePathEndpointDecomposition label := by
  classical
  exact
    { Path := TwoCyclePath pairing.endpointPartner
      Endpoint := fun path => TwoCycleEndpoint path
      instPath := inferInstance
      instEndpoint := fun _ => inferInstance
      pathAntipode :=
        twoCyclePathAntipode
          (partner := pairing.endpointPartner)
          (endpointAntipode := kyFanPathEndpointClassAntipode label hantipodal)
          (kyFanPathEndpointClassAntipode_involutive label hantipodal)
          pairing.endpointPartner_comm
      pathAntipode_involutive :=
        twoCyclePathAntipode_involutive
          (partner := pairing.endpointPartner)
          (endpointAntipode := kyFanPathEndpointClassAntipode label hantipodal)
          (kyFanPathEndpointClassAntipode_involutive label hantipodal)
          pairing.endpointPartner_comm
      pathAntipode_fixedPointFree :=
        twoCyclePathAntipode_fixedPointFree
          (partner := pairing.endpointPartner)
          (endpointAntipode := kyFanPathEndpointClassAntipode label hantipodal)
          (kyFanPathEndpointClassAntipode_involutive label hantipodal)
          pairing.endpointPartner_comm
          (kyFanPathEndpointClassAntipode_fixedPointFree label hantipodal)
          pairing.endpointPartner_not_antipodal
      endpoint_card_two :=
        twoCycleEndpoint_card pairing.endpointPartner_fixedPointFree
      classify :=
        twoCycleEndpointClassify pairing.endpointPartner_involutive }

theorem kyFanPrefixParity_of_pathEndpointDecomposition {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (D : KyFanPrefixPathEndpointDecomposition label) :
    Odd (positiveAlternatingPrefixLabelChains label).card := by
  classical
  have hneg :
      Fintype.card (NegativePrefixChainType label) =
        Fintype.card (PositivePrefixChainType label) := by
    simp [PositivePrefixChainType, NegativePrefixChainType,
      positiveAlternatingPrefixLabelChains_card_eq_negative label hantipodal]
  have hodd := D.positive_card_odd hneg
  simpa [PositivePrefixChainType] using hodd

theorem kyFanPrefixParity_of_pathEndpointDecompositionWithPunctured {n m : ℕ}
    (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (D : KyFanPrefixPathEndpointDecompositionWithPunctured label) :
    Odd (positiveAlternatingPrefixLabelChains label).card := by
  classical
  have hpunctured :
      4 ∣ Fintype.card (AlternatingPuncturedPrefixChainType label) :=
    four_dvd_alternatingPuncturedPrefixChainType_card hn label hantipodal
  have hneg :
      Fintype.card (NegativePrefixChainType label) =
        Fintype.card (PositivePrefixChainType label) := by
    simp [PositivePrefixChainType, NegativePrefixChainType,
      positiveAlternatingPrefixLabelChains_card_eq_negative label hantipodal]
  have hodd := D.positive_card_odd hpunctured hneg
  simpa [PositivePrefixChainType] using hodd

theorem kyFanPrefixParity_of_concretePathEndpointDecomposition {n m : ℕ}
    (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (D : KyFanConcretePathEndpointDecomposition label) :
    Odd (positiveAlternatingPrefixLabelChains label).card := by
  classical
  letI := D.instPath
  letI : ∀ p : D.Path, Fintype (D.Endpoint p) := D.instEndpoint
  have hpunctured :
      4 ∣ Fintype.card (AlternatingPuncturedPrefixChainType label) :=
    four_dvd_alternatingPuncturedPrefixChainType_card hn label hantipodal
  have hneg :
      Fintype.card (NegativePrefixChainType label) =
        Fintype.card (PositivePrefixChainType label) := by
    simp [PositivePrefixChainType, NegativePrefixChainType,
      positiveAlternatingPrefixLabelChains_card_eq_negative label hantipodal]
  have hodd :
      Odd (Fintype.card (PositivePrefixChainType label)) :=
    odd_card_positive_endpoints_of_path_endpoint_equiv_with_punctured
      (Path := D.Path)
      (Punctured := AlternatingPuncturedPrefixChainType label)
      (Base := Bool)
      (Positive := PositivePrefixChainType label)
      (Negative := NegativePrefixChainType label)
      D.Endpoint D.pathAntipode D.pathAntipode_involutive D.pathAntipode_fixedPointFree
      D.endpoint_card_two D.classify (by simp) hpunctured hneg
  simpa [PositivePrefixChainType] using hodd

/--
The remaining geometric/local-combinatorial obligation for the octahedral Ky
Fan lemma: for every admissible labeling, construct the path decomposition.
-/
def KyFanPrefixPathEndpointDecompositionStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Nonempty (KyFanPrefixPathEndpointDecomposition label)

/--
The refined path-construction obligation with punctured endpoints retained in
the endpoint classification.  For dimension `n + 1`, the punctured endpoint
type is the already formalized alternating punctured prefix-chain finset.
-/
def KyFanPrefixPathEndpointDecompositionWithPuncturedStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset (n + 1) → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Nonempty (KyFanPrefixPathEndpointDecompositionWithPunctured label)

def KyFanConcretePathEndpointDecompositionStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset (n + 1) → SignedLabel m,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Nonempty (KyFanConcretePathEndpointDecomposition label)

def KyFanEndpointPairingStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset (n + 1) → SignedLabel m,
    (hantipodal : ∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Nonempty (KyFanEndpointPairing label hantipodal)

theorem kyFanConcretePathEndpointDecompositionStatement_of_endpointPairing
    {n m : ℕ} (hpairing : KyFanEndpointPairingStatement n m) :
    KyFanConcretePathEndpointDecompositionStatement n m := by
  intro label hantipodal hno
  rcases hpairing label hantipodal hno with ⟨pairing⟩
  exact ⟨kyFanConcretePathEndpointDecomposition_of_endpointPairing pairing⟩

noncomputable def kyFanPrefixPathEndpointDecomposition_zero {m : ℕ}
    (label : NonzeroSignedSubset 0 → SignedLabel m) :
    KyFanPrefixPathEndpointDecomposition label where
  Path := Bool
  Base := Bool
  Endpoint := fun _ => Bool
  instPath := inferInstance
  instBase := inferInstance
  instEndpoint := fun _ => inferInstance
  pathAntipode := Equiv.boolNot
  pathAntipode_involutive := by
    intro b
    cases b <;> rfl
  pathAntipode_fixedPointFree := by
    intro b h
    cases b <;> simp [Equiv.boolNot] at h
  endpoint_card_two := by
    intro _p
    simp
  classify := Fintype.equivOfCardEq (by
    simp [Fintype.card_sigma, positivePrefixChainType_card_zero label,
      negativePrefixChainType_card_zero label])
  base_card := by
    simp

theorem kyFanPrefixPathEndpointDecompositionStatement_zero :
    KyFanPrefixPathEndpointDecompositionStatement 0 0 := by
  intro label _hantipodal _hno
  exact ⟨kyFanPrefixPathEndpointDecomposition_zero label⟩

theorem kyFanPrefixPathEndpointDecompositionStatement_one :
    KyFanPrefixPathEndpointDecompositionStatement 1 0 := by
  intro label hantipodal hno
  obtain ⟨X, Y, hXY, hcomp⟩ := tuckerLemmaStatement_one label hantipodal
  exact False.elim (hno X Y hXY hcomp)

theorem kyFanPrefixPathEndpointDecompositionStatement_two :
    KyFanPrefixPathEndpointDecompositionStatement 2 1 := by
  intro label hantipodal hno
  obtain ⟨X, Y, hXY, hcomp⟩ := tuckerLemmaStatement_two label hantipodal
  exact False.elim (hno X Y hXY hcomp)

theorem kyFanPrefixPathEndpointDecompositionStatement_sub_one_le_two {n : ℕ} (hnle : n ≤ 2) :
    KyFanPrefixPathEndpointDecompositionStatement n (n - 1) := by
  interval_cases n
  · exact kyFanPrefixPathEndpointDecompositionStatement_zero
  · exact kyFanPrefixPathEndpointDecompositionStatement_one
  · exact kyFanPrefixPathEndpointDecompositionStatement_two

theorem kyFanPrefixParityStatement_of_pathEndpointDecomposition {n m : ℕ}
    (hpaths : KyFanPrefixPathEndpointDecompositionStatement n m) :
    KyFanPrefixParityStatement n m := by
  intro label hantipodal hno
  rcases hpaths label hantipodal hno with ⟨D⟩
  exact kyFanPrefixParity_of_pathEndpointDecomposition label hantipodal D

theorem kyFanPrefixParityStatement_succ_of_pathEndpointDecompositionWithPunctured
    {n m : ℕ} (hn : 0 < n)
    (hpaths : KyFanPrefixPathEndpointDecompositionWithPuncturedStatement n m) :
    KyFanPrefixParityStatement (n + 1) m := by
  intro label hantipodal hno
  rcases hpaths label hantipodal hno with ⟨D⟩
  exact kyFanPrefixParity_of_pathEndpointDecompositionWithPunctured hn label hantipodal D

theorem kyFanPrefixModFourStatement_succ_of_pathEndpointDecompositionWithPunctured
    {n m : ℕ} (hn : 0 < n)
    (hpaths : KyFanPrefixPathEndpointDecompositionWithPuncturedStatement n m) :
    KyFanPrefixModFourStatement (n + 1) m :=
  (kyFanPrefixParityStatement_iff_modFour (by omega)).mp
    (kyFanPrefixParityStatement_succ_of_pathEndpointDecompositionWithPunctured hn hpaths)

theorem tuckerLemmaStatement_succ_of_pathEndpointDecompositionWithPunctured
    {n : ℕ} (hn : 0 < n)
    (hpaths : KyFanPrefixPathEndpointDecompositionWithPuncturedStatement n n) :
    TuckerLemmaStatement (n + 1) :=
  tuckerLemmaStatement_of_kyFanPrefixParity (by omega)
    (kyFanPrefixParityStatement_succ_of_pathEndpointDecompositionWithPunctured hn hpaths)

theorem kyFanPrefixParityStatement_succ_of_concretePathEndpointDecomposition
    {n m : ℕ} (hn : 0 < n)
    (hpaths : KyFanConcretePathEndpointDecompositionStatement n m) :
    KyFanPrefixParityStatement (n + 1) m := by
  intro label hantipodal hno
  rcases hpaths label hantipodal hno with ⟨D⟩
  exact kyFanPrefixParity_of_concretePathEndpointDecomposition hn label hantipodal D

theorem kyFanPrefixModFourStatement_succ_of_concretePathEndpointDecomposition
    {n m : ℕ} (hn : 0 < n)
    (hpaths : KyFanConcretePathEndpointDecompositionStatement n m) :
    KyFanPrefixModFourStatement (n + 1) m :=
  (kyFanPrefixParityStatement_iff_modFour (by omega)).mp
    (kyFanPrefixParityStatement_succ_of_concretePathEndpointDecomposition hn hpaths)

theorem tuckerLemmaStatement_succ_of_concretePathEndpointDecomposition
    {n : ℕ} (hn : 0 < n)
    (hpaths : KyFanConcretePathEndpointDecompositionStatement n n) :
    TuckerLemmaStatement (n + 1) :=
  tuckerLemmaStatement_of_kyFanPrefixParity (by omega)
    (kyFanPrefixParityStatement_succ_of_concretePathEndpointDecomposition hn hpaths)

theorem kyFanPrefixParityStatement_succ_of_endpointPairing
    {n m : ℕ} (hn : 0 < n)
    (hpairing : KyFanEndpointPairingStatement n m) :
    KyFanPrefixParityStatement (n + 1) m :=
  kyFanPrefixParityStatement_succ_of_concretePathEndpointDecomposition hn
    (kyFanConcretePathEndpointDecompositionStatement_of_endpointPairing hpairing)

theorem kyFanPrefixModFourStatement_succ_of_endpointPairing
    {n m : ℕ} (hn : 0 < n)
    (hpairing : KyFanEndpointPairingStatement n m) :
    KyFanPrefixModFourStatement (n + 1) m :=
  (kyFanPrefixParityStatement_iff_modFour (by omega)).mp
    (kyFanPrefixParityStatement_succ_of_endpointPairing hn hpairing)

theorem tuckerLemmaStatement_succ_of_endpointPairing
    {n : ℕ} (hn : 0 < n)
    (hpairing : KyFanEndpointPairingStatement n n) :
    TuckerLemmaStatement (n + 1) :=
  tuckerLemmaStatement_of_kyFanPrefixParity (by omega)
    (kyFanPrefixParityStatement_succ_of_endpointPairing hn hpairing)

theorem exists_complementaryComparable_of_pathEndpointDecomposition_of_lt {n m : ℕ}
    (hmn : m < n) (hpaths : KyFanPrefixPathEndpointDecompositionStatement n m)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ∃ X Y : NonzeroSignedSubset n,
      SignedSubset.Le X.1 Y.1 ∧ label X = (label Y).neg :=
  exists_complementaryComparable_of_kyFanPrefixParity_of_lt hmn
    (kyFanPrefixParityStatement_of_pathEndpointDecomposition hpaths) label hantipodal

theorem not_noComplementaryComparableLabels_of_pathEndpointDecomposition_of_lt {n m : ℕ}
    (hmn : m < n) (hpaths : KyFanPrefixPathEndpointDecompositionStatement n m)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ¬ NoComplementaryComparableLabels label :=
  not_noComplementaryComparableLabels_of_kyFanPrefixParity_of_lt hmn
    (kyFanPrefixParityStatement_of_pathEndpointDecomposition hpaths) label hantipodal

theorem tuckerLemmaStatement_of_pathEndpointDecomposition {n : ℕ} (hn : 1 ≤ n)
    (hpaths : KyFanPrefixPathEndpointDecompositionStatement n (n - 1)) :
    TuckerLemmaStatement n :=
  tuckerLemmaStatement_of_kyFanPrefixParity hn
    (kyFanPrefixParityStatement_of_pathEndpointDecomposition hpaths)

/--
If Tucker's lemma is already known in dimension `n`, then every antipodal
labeling with fewer than `n` absolute labels has a complementary comparable
pair.  This isolates the reason the `n = 1, 2` path-decomposition statements
above are vacuous: their `NoComplementaryComparableLabels` hypothesis is
inconsistent.
-/
theorem exists_complementaryComparable_of_tuckerLemmaStatement_of_lt {n m : ℕ}
    (htucker : TuckerLemmaStatement n) (hmn : m < n)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ∃ X Y : NonzeroSignedSubset n,
      SignedSubset.Le X.1 Y.1 ∧ label X = (label Y).neg := by
  let liftIndex : Fin m → Fin (n - 1) := fun i => ⟨i.val, by omega⟩
  let lifted : NonzeroSignedSubset n → SignedLabel (n - 1) :=
    fun X => { positive := (label X).positive, index := liftIndex (label X).index }
  have hlifted :
      ∀ X, lifted X.antipode = (lifted X).neg := by
    intro X
    apply SignedLabel.ext
    · have hpositive := congrArg SignedLabel.positive (hantipodal X)
      simpa [lifted, SignedLabel.neg] using hpositive
    · apply Fin.ext
      have hindex := congrArg SignedLabel.index (hantipodal X)
      have hindex_val := congrArg Fin.val hindex
      simpa [lifted, liftIndex, SignedLabel.neg] using hindex_val
  obtain ⟨X, Y, hXY, hcomp⟩ := htucker lifted hlifted
  refine ⟨X, Y, hXY, ?_⟩
  apply SignedLabel.ext
  · have hpositive := congrArg SignedLabel.positive hcomp
    simpa [lifted, SignedLabel.neg] using hpositive
  · apply Fin.ext
    have hindex := congrArg SignedLabel.index hcomp
    have hindex_val := congrArg Fin.val hindex
    simpa [lifted, liftIndex, SignedLabel.neg] using hindex_val

theorem not_noComplementaryComparableLabels_of_tuckerLemmaStatement_of_lt {n m : ℕ}
    (htucker : TuckerLemmaStatement n) (hmn : m < n)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ¬ NoComplementaryComparableLabels label := by
  intro hno
  obtain ⟨X, Y, hXY, hcomp⟩ :=
    exists_complementaryComparable_of_tuckerLemmaStatement_of_lt htucker hmn label hantipodal
  exact hno X Y hXY hcomp

theorem kyFanPrefixPathEndpointDecompositionStatement_of_tuckerLemmaStatement_of_lt
    {n m : ℕ} (htucker : TuckerLemmaStatement n) (hmn : m < n) :
    KyFanPrefixPathEndpointDecompositionStatement n m := by
  intro label hantipodal hno
  exact False.elim
    ((not_noComplementaryComparableLabels_of_tuckerLemmaStatement_of_lt
      htucker hmn label hantipodal) hno)

theorem kyFanPrefixParityStatement_of_tuckerLemmaStatement_of_lt {n m : ℕ}
    (htucker : TuckerLemmaStatement n) (hmn : m < n) :
    KyFanPrefixParityStatement n m := by
  intro label hantipodal hno
  exact False.elim
    ((not_noComplementaryComparableLabels_of_tuckerLemmaStatement_of_lt
      htucker hmn label hantipodal) hno)

theorem kyFanPrefixModFourStatement_of_tuckerLemmaStatement_of_lt {n m : ℕ}
    (htucker : TuckerLemmaStatement n) (hmn : m < n) :
    KyFanPrefixModFourStatement n m :=
  (kyFanPrefixParityStatement_iff_modFour (Nat.zero_lt_of_lt hmn)).mp
    (kyFanPrefixParityStatement_of_tuckerLemmaStatement_of_lt htucker hmn)

/--
If Tucker's lemma is already known in the ambient dimension `n + 1`, then the
endpoint-pairing obligation in that ambient dimension is vacuous for every
label range `m < n + 1`.
-/
theorem kyFanEndpointPairingStatement_of_tuckerLemmaStatement_succ_of_lt
    {n m : ℕ} (htucker : TuckerLemmaStatement (n + 1)) (hmn : m < n + 1) :
    KyFanEndpointPairingStatement n m := by
  intro label hantipodal hno
  exact False.elim
    ((not_noComplementaryComparableLabels_of_tuckerLemmaStatement_of_lt
      htucker hmn label hantipodal) hno)

/--
The endpoint-pairing frontier in the Tucker-critical range is exactly Tucker's
lemma in the next dimension.  The forward direction is the path-count pipeline;
the reverse direction is vacuity from Tucker's lemma itself.
-/
theorem kyFanEndpointPairingStatement_iff_tuckerLemmaStatement_succ (n : ℕ) :
    KyFanEndpointPairingStatement n n ↔ TuckerLemmaStatement (n + 1) := by
  constructor
  · intro hpairing
    by_cases hn : 0 < n
    · exact tuckerLemmaStatement_succ_of_endpointPairing hn hpairing
    · have hzero : n = 0 := by omega
      subst n
      exact tuckerLemmaStatement_one
  · intro htucker
    exact kyFanEndpointPairingStatement_of_tuckerLemmaStatement_succ_of_lt
      htucker (by omega)

/-- Same equivalence, indexed by the ambient Tucker dimension. -/
theorem tuckerLemmaStatement_iff_kyFanEndpointPairingStatement_pred
    {n : ℕ} (hn : 1 ≤ n) :
    TuckerLemmaStatement n ↔ KyFanEndpointPairingStatement (n - 1) (n - 1) := by
  have hsucc : n - 1 + 1 = n := by omega
  rw [← hsucc]
  exact (kyFanEndpointPairingStatement_iff_tuckerLemmaStatement_succ (n - 1)).symm

/--
For the Tucker-critical label range `m = n - 1`, the abstract path-endpoint
obligation is equivalent to Tucker's lemma itself.  The forward direction is
the parity chain; the reverse direction is the vacuity observed in dimensions
one and two.
-/
theorem kyFanPrefixPathEndpointDecompositionStatement_iff_tuckerLemmaStatement
    {n : ℕ} (hn : 1 ≤ n) :
    KyFanPrefixPathEndpointDecompositionStatement n (n - 1) ↔ TuckerLemmaStatement n := by
  constructor
  · intro hpaths
    exact tuckerLemmaStatement_of_pathEndpointDecomposition hn hpaths
  · intro htucker
    exact kyFanPrefixPathEndpointDecompositionStatement_of_tuckerLemmaStatement_of_lt
      htucker (by omega)

theorem kyFanPrefixParityStatement_iff_tuckerLemmaStatement {n : ℕ} (hn : 1 ≤ n) :
    KyFanPrefixParityStatement n (n - 1) ↔ TuckerLemmaStatement n := by
  constructor
  · intro hparity
    exact tuckerLemmaStatement_of_kyFanPrefixParity hn hparity
  · intro htucker
    exact kyFanPrefixParityStatement_of_tuckerLemmaStatement_of_lt htucker (by omega)

theorem kyFanPrefixModFourStatement_iff_tuckerLemmaStatement {n : ℕ} (hn : 1 ≤ n) :
    KyFanPrefixModFourStatement n (n - 1) ↔ TuckerLemmaStatement n := by
  constructor
  · intro hmodFour
    exact tuckerLemmaStatement_of_kyFanPrefixModFour hn hmodFour
  · intro htucker
    exact kyFanPrefixModFourStatement_of_tuckerLemmaStatement_of_lt htucker (by omega)

/-- Encode the four labels `±0, ±1` as two-bit words:
low bit is sign, high bit is index. -/
private def signedLabelTwoCode (L : SignedLabel 2) : BitVec 2 :=
  BitVec.ofNat 2 (2 * L.index.val + if L.positive then 1 else 0)

private theorem signedLabelTwoCode_neg (L : SignedLabel 2) :
    signedLabelTwoCode L.neg = signedLabelTwoCode L ^^^ (1#2) := by
  cases L with
  | mk positive index =>
      cases positive <;> fin_cases index <;> native_decide

@[simp] private theorem signedLabelTwoCode_neg_mk (L : SignedLabel 2) :
    signedLabelTwoCode { positive := !L.positive, index := L.index } =
      signedLabelTwoCode L ^^^ (1#2) := by
  simpa [SignedLabel.neg] using signedLabelTwoCode_neg L

private theorem signedLabelTwoCode_injective : Function.Injective signedLabelTwoCode := by
  intro L M h
  cases L with
  | mk lp li =>
      cases M with
      | mk mp mi =>
          cases lp <;> cases mp <;> fin_cases li <;> fin_cases mi <;>
            simp [signedLabelTwoCode] at h ⊢

private theorem signedLabelTwoCode_noComplement
    {label : NonzeroSignedSubset 3 → SignedLabel 2}
    (hno : NoComplementaryComparableLabels label)
    {X Y : NonzeroSignedSubset 3} (hXY : SignedSubset.Le X.1 Y.1) :
    signedLabelTwoCode (label X) ≠ signedLabelTwoCode (label Y).neg := by
  intro hcode
  exact hno X Y hXY (signedLabelTwoCode_injective hcode)

/-- The finite unsatisfiable core for the three-dimensional Tucker step. -/
private theorem tuckerLemmaStatement_three_core_unsat
    (L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 : BitVec 2) :
    ¬ (
      L0 ≠ L10 ∧
      L0 ≠ L7 ∧
      L0 ≠ L4 ∧
      L0 ≠ L1 ∧
      L0 ≠ (L3 ^^^ (1#2)) ∧
      L0 ≠ (L6 ^^^ (1#2)) ∧
      L0 ≠ (L9 ^^^ (1#2)) ∧
      L0 ≠ (L12 ^^^ (1#2)) ∧
      L1 ≠ L6 ∧
      L1 ≠ (L10 ^^^ (1#2)) ∧
      L2 ≠ L6 ∧
      L2 ≠ L5 ∧
      L2 ≠ L4 ∧
      L2 ≠ (L1 ^^^ (1#2)) ∧
      L2 ≠ (L3 ^^^ (1#2)) ∧
      L2 ≠ (L10 ^^^ (1#2)) ∧
      L2 ≠ (L11 ^^^ (1#2)) ∧
      L2 ≠ (L12 ^^^ (1#2)) ∧
      L3 ≠ L4 ∧
      L3 ≠ (L12 ^^^ (1#2)) ∧
      L5 ≠ (L4 ^^^ (1#2)) ∧
      L5 ≠ (L6 ^^^ (1#2)) ∧
      L7 ≠ (L4 ^^^ (1#2)) ∧
      L7 ≠ (L10 ^^^ (1#2)) ∧
      L8 ≠ (L4 ^^^ (1#2)) ∧
      L8 ≠ (L5 ^^^ (1#2)) ∧
      L8 ≠ (L6 ^^^ (1#2)) ∧
      L8 ≠ (L7 ^^^ (1#2)) ∧
      L8 ≠ (L9 ^^^ (1#2)) ∧
      L8 ≠ (L10 ^^^ (1#2)) ∧
      L8 ≠ (L11 ^^^ (1#2)) ∧
      L8 ≠ (L12 ^^^ (1#2)) ∧
      L9 ≠ (L6 ^^^ (1#2)) ∧
      L9 ≠ (L12 ^^^ (1#2)) ∧
      L11 ≠ (L10 ^^^ (1#2)) ∧
      L11 ≠ (L12 ^^^ (1#2))) := by
  bv_decide

set_option linter.unusedSimpArgs false in
private theorem not_noComplementaryComparableLabels_three
    (label : NonzeroSignedSubset 3 → SignedLabel 2)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (hno : NoComplementaryComparableLabels label) : False := by
  classical
  let z : Fin 3 := ⟨0, by omega⟩
  let o : Fin 3 := ⟨1, by omega⟩
  let t : Fin 3 := ⟨2, by omega⟩
  let R0 : NonzeroSignedSubset 3 :=
    ⟨{ pos := {t}, neg := ∅, disjoint := by
        simp [z, o, t] },
      by simp [SignedSubset.Nonzero]⟩
  let R1 : NonzeroSignedSubset 3 :=
    ⟨{ pos := {o}, neg := {t}, disjoint := by
        simp [z, o, t] },
      by simp [SignedSubset.Nonzero]⟩
  let R2 : NonzeroSignedSubset 3 :=
    ⟨{ pos := {o}, neg := ∅, disjoint := by
        simp [z, o, t] },
      by simp [SignedSubset.Nonzero]⟩
  let R3 : NonzeroSignedSubset 3 :=
    ⟨{ pos := {o, t}, neg := ∅, disjoint := by
        simp [z, o, t] },
      by simp [SignedSubset.Nonzero]⟩
  let R4 : NonzeroSignedSubset 3 :=
    ⟨{ pos := {z}, neg := {o, t}, disjoint := by
        simp [z, o, t] },
      by simp [SignedSubset.Nonzero]⟩
  let R5 : NonzeroSignedSubset 3 :=
    ⟨{ pos := {z}, neg := {o}, disjoint := by
        simp [z, o, t] },
      by simp [SignedSubset.Nonzero]⟩
  let R6 : NonzeroSignedSubset 3 :=
    ⟨{ pos := {z, t}, neg := {o}, disjoint := by
        simp [z, o, t] },
      by simp [SignedSubset.Nonzero]⟩
  let R7 : NonzeroSignedSubset 3 :=
    ⟨{ pos := {z}, neg := {t}, disjoint := by
        simp [z, o, t] },
      by simp [SignedSubset.Nonzero]⟩
  let R8 : NonzeroSignedSubset 3 :=
    ⟨{ pos := {z}, neg := ∅, disjoint := by
        simp [z, o, t] },
      by simp [SignedSubset.Nonzero]⟩
  let R9 : NonzeroSignedSubset 3 :=
    ⟨{ pos := {z, t}, neg := ∅, disjoint := by
        simp [z, o, t] },
      by simp [SignedSubset.Nonzero]⟩
  let R10 : NonzeroSignedSubset 3 :=
    ⟨{ pos := {z, o}, neg := {t}, disjoint := by
        simp [z, o, t] },
      by simp [SignedSubset.Nonzero]⟩
  let R11 : NonzeroSignedSubset 3 :=
    ⟨{ pos := {z, o}, neg := ∅, disjoint := by
        simp [z, o, t] },
      by simp [SignedSubset.Nonzero]⟩
  let R12 : NonzeroSignedSubset 3 :=
    ⟨{ pos := {z, o, t}, neg := ∅, disjoint := by
        simp [z, o, t] },
      by simp [SignedSubset.Nonzero]⟩
  let B0 : BitVec 2 := signedLabelTwoCode (label R0)
  let B1 : BitVec 2 := signedLabelTwoCode (label R1)
  let B2 : BitVec 2 := signedLabelTwoCode (label R2)
  let B3 : BitVec 2 := signedLabelTwoCode (label R3)
  let B4 : BitVec 2 := signedLabelTwoCode (label R4)
  let B5 : BitVec 2 := signedLabelTwoCode (label R5)
  let B6 : BitVec 2 := signedLabelTwoCode (label R6)
  let B7 : BitVec 2 := signedLabelTwoCode (label R7)
  let B8 : BitVec 2 := signedLabelTwoCode (label R8)
  let B9 : BitVec 2 := signedLabelTwoCode (label R9)
  let B10 : BitVec 2 := signedLabelTwoCode (label R10)
  let B11 : BitVec 2 := signedLabelTwoCode (label R11)
  let B12 : BitVec 2 := signedLabelTwoCode (label R12)
  have h49 : B0 ≠ B10 := by
    have h := signedLabelTwoCode_noComplement hno (X := R0) (Y := R10.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R10,
        z, o, t])
    simpa [B0, B10, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h50 : B0 ≠ B7 := by
    have h := signedLabelTwoCode_noComplement hno (X := R0) (Y := R7.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R7,
        z, o, t])
    simpa [B0, B7, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h51 : B0 ≠ B4 := by
    have h := signedLabelTwoCode_noComplement hno (X := R0) (Y := R4.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R4,
        z, o, t])
    simpa [B0, B4, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h52 : B0 ≠ B1 := by
    have h := signedLabelTwoCode_noComplement hno (X := R0) (Y := R1.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R1,
        z, o, t])
    simpa [B0, B1, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h54 : B0 ≠ (B3 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R0) (Y := R3) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R3,
        z, o, t])
    simpa [B0, B3, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h55 : B0 ≠ (B6 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R0) (Y := R6) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R6,
        z, o, t])
    simpa [B0, B6, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h56 : B0 ≠ (B9 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R0) (Y := R9) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R9,
        z, o, t])
    simpa [B0, B9, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h57 : B0 ≠ (B12 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R0) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R12,
        z, o, t])
    simpa [B0, B12, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h58 : B1 ≠ B6 := by
    have h := signedLabelTwoCode_noComplement hno (X := R1) (Y := R6.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R1, R6,
        z, o, t])
    simpa [B1, B6, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h60 : B1 ≠ (B10 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R1) (Y := R10) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R1, R10,
        z, o, t])
    simpa [B1, B10, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h61 : B2 ≠ B6 := by
    have h := signedLabelTwoCode_noComplement hno (X := R2) (Y := R6.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R6,
        z, o, t])
    simpa [B2, B6, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h62 : B2 ≠ B5 := by
    have h := signedLabelTwoCode_noComplement hno (X := R2) (Y := R5.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R5,
        z, o, t])
    simpa [B2, B5, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h63 : B2 ≠ B4 := by
    have h := signedLabelTwoCode_noComplement hno (X := R2) (Y := R4.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R4,
        z, o, t])
    simpa [B2, B4, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h64 : B2 ≠ (B1 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R2) (Y := R1) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R1,
        z, o, t])
    simpa [B2, B1, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h66 : B2 ≠ (B3 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R2) (Y := R3) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R3,
        z, o, t])
    simpa [B2, B3, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h67 : B2 ≠ (B10 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R2) (Y := R10) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R10,
        z, o, t])
    simpa [B2, B10, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h68 : B2 ≠ (B11 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R2) (Y := R11) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R11,
        z, o, t])
    simpa [B2, B11, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h69 : B2 ≠ (B12 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R2) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R12,
        z, o, t])
    simpa [B2, B12, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h70 : B3 ≠ B4 := by
    have h := signedLabelTwoCode_noComplement hno (X := R3) (Y := R4.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R3, R4,
        z, o, t])
    simpa [B3, B4, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h72 : B3 ≠ (B12 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R3) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R3, R12,
        z, o, t])
    simpa [B3, B12, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h74 : B5 ≠ (B4 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R5) (Y := R4) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R5, R4,
        z, o, t])
    simpa [B5, B4, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h76 : B5 ≠ (B6 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R5) (Y := R6) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R5, R6,
        z, o, t])
    simpa [B5, B6, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h78 : B7 ≠ (B4 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R7) (Y := R4) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R7, R4,
        z, o, t])
    simpa [B7, B4, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h80 : B7 ≠ (B10 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R7) (Y := R10) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R7, R10,
        z, o, t])
    simpa [B7, B10, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h81 : B8 ≠ (B4 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R8) (Y := R4) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R4,
        z, o, t])
    simpa [B8, B4, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h82 : B8 ≠ (B5 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R8) (Y := R5) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R5,
        z, o, t])
    simpa [B8, B5, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h83 : B8 ≠ (B6 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R8) (Y := R6) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R6,
        z, o, t])
    simpa [B8, B6, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h84 : B8 ≠ (B7 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R8) (Y := R7) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R7,
        z, o, t])
    simpa [B8, B7, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h86 : B8 ≠ (B9 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R8) (Y := R9) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R9,
        z, o, t])
    simpa [B8, B9, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h87 : B8 ≠ (B10 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R8) (Y := R10) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R10,
        z, o, t])
    simpa [B8, B10, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h88 : B8 ≠ (B11 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R8) (Y := R11) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R11,
        z, o, t])
    simpa [B8, B11, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h89 : B8 ≠ (B12 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R8) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R12,
        z, o, t])
    simpa [B8, B12, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h90 : B9 ≠ (B6 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R9) (Y := R6) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R9, R6,
        z, o, t])
    simpa [B9, B6, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h92 : B9 ≠ (B12 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R9) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R9, R12,
        z, o, t])
    simpa [B9, B12, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h94 : B11 ≠ (B10 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R11) (Y := R10) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R11, R10,
        z, o, t])
    simpa [B11, B10, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h96 : B11 ≠ (B12 ^^^ (1#2)) := by
    have h := signedLabelTwoCode_noComplement hno (X := R11) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R11, R12,
        z, o, t])
    simpa [B11, B12, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  exact tuckerLemmaStatement_three_core_unsat
    B0 B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12
    ⟨h49, h50, h51, h52, h54, h55, h56, h57, h58, h60, h61, h62, h63, h64,
      h66, h67, h68, h69, h70, h72, h74, h76, h78, h80, h81, h82, h83, h84,
      h86, h87, h88, h89, h90, h92, h94, h96⟩

theorem kyFanEndpointPairingStatement_two_two : KyFanEndpointPairingStatement 2 2 := by
  intro label hantipodal hno
  exact False.elim (not_noComplementaryComparableLabels_three label hantipodal hno)

theorem tuckerLemmaStatement_three : TuckerLemmaStatement 3 :=
  tuckerLemmaStatement_succ_of_endpointPairing (by omega)
    kyFanEndpointPairingStatement_two_two

end ProofsInTheBook.TuckerLemmaCore
