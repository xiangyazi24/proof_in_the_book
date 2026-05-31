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

/-- A signed-label word with the local rigidity forced by the no-complement
hypothesis along one chain: if two comparable positions carry the same absolute
label, then they carry the same sign. -/
structure AlternatingWordContext (len m : ℕ) where
  word : Fin len → SignedLabel m
  same_index_same_sign :
    ∀ i j : Fin len, i ≤ j → (word i).index = (word j).index →
      (word i).positive = (word j).positive

namespace AlternatingWordContext

def PositiveAlternating {len m : ℕ} (C : AlternatingWordContext len m) : Prop :=
  (StrictMono fun i : Fin len => (C.word i).index) ∧
    ∀ i : Fin len, (C.word i).positive = decide (Even i.val)

def NegativeAlternating {len m : ℕ} (C : AlternatingWordContext len m) : Prop :=
  (StrictMono fun i : Fin len => (C.word i).index) ∧
    ∀ i : Fin len, (C.word i).positive = !decide (Even i.val)

def PositivePunctured {n m : ℕ}
    (C : AlternatingWordContext (n + 1) m) (gap : Fin (n + 1)) : Prop :=
  (StrictMono fun i : Fin n => (C.word (gap.succAbove i)).index) ∧
    ∀ i : Fin n, (C.word (gap.succAbove i)).positive = decide (Even i.val)

def NegativePunctured {n m : ℕ}
    (C : AlternatingWordContext (n + 1) m) (gap : Fin (n + 1)) : Prop :=
  (StrictMono fun i : Fin n => (C.word (gap.succAbove i)).index) ∧
    ∀ i : Fin n, (C.word (gap.succAbove i)).positive = !decide (Even i.val)

theorem index_ne_of_positive_ne {len m : ℕ} (C : AlternatingWordContext len m)
    {i j : Fin len} (hij : i ≤ j)
    (hpositive : (C.word i).positive ≠ (C.word j).positive) :
    (C.word i).index ≠ (C.word j).index := by
  intro hindex
  exact hpositive (C.same_index_same_sign i j hij hindex)

theorem punctured_strictMono_of_strictMono {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m}
    (hstrict : StrictMono fun i : Fin (n + 1) => (C.word i).index)
    (gap : Fin (n + 1)) :
    StrictMono fun i : Fin n => (C.word (gap.succAbove i)).index := by
  intro i j hij
  exact hstrict (Fin.strictMono_succAbove gap hij)

theorem positive_negativePunctured_same_false {n m : ℕ} (hn : 0 < n)
    {C : AlternatingWordContext (n + 1) m} {gap : Fin (n + 1)}
    (hpositive : C.PositivePunctured gap) (hnegative : C.NegativePunctured gap) :
    False := by
  let i : Fin n := ⟨0, hn⟩
  have hpos := hpositive.2 i
  have hneg := hnegative.2 i
  rw [hpos] at hneg
  simp [i] at hneg

/-- Flip every sign in a word.  This exchanges positive- and negative-first
alternating deletion gaps while preserving absolute labels. -/
def negate {len m : ℕ} (C : AlternatingWordContext len m) :
    AlternatingWordContext len m where
  word := fun i => (C.word i).neg
  same_index_same_sign := by
    intro i j hij hindex
    have hindex' : (C.word i).index = (C.word j).index := by
      simpa [SignedLabel.neg] using hindex
    have hsign := C.same_index_same_sign i j hij hindex'
    cases hi : (C.word i).positive <;> cases hj : (C.word j).positive <;>
      simp [SignedLabel.neg, hi, hj] at hsign ⊢

theorem negate_strictMono_iff {len m : ℕ} {C : AlternatingWordContext len m} :
    (StrictMono fun i : Fin len => (C.negate.word i).index) ↔
      StrictMono fun i : Fin len => (C.word i).index := by
  simp [negate, SignedLabel.neg]

theorem negate_positivePunctured_iff {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} {gap : Fin (n + 1)} :
    C.negate.PositivePunctured gap ↔ C.NegativePunctured gap := by
  constructor
  · rintro ⟨hmono, hsign⟩
    constructor
    · simpa [negate, SignedLabel.neg] using hmono
    · intro i
      have h := hsign i
      cases hp : (C.word (gap.succAbove i)).positive <;>
        cases he : decide (Even i.val) <;>
          simp [negate, SignedLabel.neg, hp, he] at h ⊢
  · rintro ⟨hmono, hsign⟩
    constructor
    · simpa [negate, SignedLabel.neg] using hmono
    · intro i
      have h := hsign i
      cases hp : (C.word (gap.succAbove i)).positive <;>
        cases he : decide (Even i.val) <;>
          simp [negate, SignedLabel.neg, hp, he] at h ⊢

theorem negate_negativePunctured_iff {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} {gap : Fin (n + 1)} :
    C.negate.NegativePunctured gap ↔ C.PositivePunctured gap := by
  constructor
  · rintro ⟨hmono, hsign⟩
    constructor
    · simpa [negate, SignedLabel.neg] using hmono
    · intro i
      have h := hsign i
      cases hp : (C.word (gap.succAbove i)).positive <;>
        cases he : decide (Even i.val) <;>
          simp [negate, SignedLabel.neg, hp, he] at h ⊢
  · rintro ⟨hmono, hsign⟩
    constructor
    · simpa [negate, SignedLabel.neg] using hmono
    · intro i
      have h := hsign i
      cases hp : (C.word (gap.succAbove i)).positive <;>
        cases he : decide (Even i.val) <;>
          simp [negate, SignedLabel.neg, hp, he] at h ⊢

private theorem decide_even_pred_eq_not (k : ℕ) (hk : 0 < k) :
    decide (Even (k - 1)) = !decide (Even k) := by
  have hk' : k = (k - 1) + 1 := by omega
  rw [hk']
  by_cases h : Even (k - 1) <;> simp [Nat.even_add_one, h]

private theorem not_decide_even_pred_eq (k : ℕ) (hk : 0 < k) :
    (!decide (Even (k - 1))) = decide (Even k) := by
  rw [decide_even_pred_eq_not k hk]
  cases decide (Even k) <;> rfl

private theorem Bool.eq_not_of_ne {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp at h ⊢

private def nextGap {n : ℕ} (gap : Fin (n + 1)) (hgap : gap.val < n) :
    Fin (n + 1) :=
  ⟨gap.val + 1, by omega⟩

private def prevGap {n : ℕ} (gap : Fin (n + 1)) (hgap : 0 < gap.val) :
    Fin (n + 1) :=
  ⟨gap.val - 1, by omega⟩

theorem positivePunctured_sign_of_lt {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} {gap i : Fin (n + 1)}
    (hgap : C.PositivePunctured gap) (hi : i < gap) :
    (C.word i).positive = decide (Even i.val) := by
  let j : Fin n := ⟨i.val, by
    have hi' : i.val < gap.val := Fin.lt_def.mp hi
    have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
    omega⟩
  have hcast : (Fin.castSucc j : Fin (n + 1)) < gap := by
    rw [Fin.lt_def]
    simp [j]
    exact Fin.lt_def.mp hi
  have hsucc : gap.succAbove j = i := by
    rw [Fin.succAbove_of_castSucc_lt gap j hcast]
    apply Fin.ext
    simp [j]
  have hsign := hgap.2 j
  rw [hsucc] at hsign
  simpa [j] using hsign

theorem positivePunctured_sign_of_gt {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} {gap i : Fin (n + 1)}
    (hgap : C.PositivePunctured gap) (hi : gap < i) :
    (C.word i).positive = !decide (Even i.val) := by
  have hival_pos : 0 < i.val := by
    have hi' : gap.val < i.val := Fin.lt_def.mp hi
    omega
  let j : Fin n := ⟨i.val - 1, by
    have hle : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    omega⟩
  have hle_cast : gap ≤ (Fin.castSucc j : Fin (n + 1)) := by
    rw [Fin.le_def]
    simp [j]
    exact Nat.le_sub_one_of_lt (Fin.lt_def.mp hi)
  have hsucc : gap.succAbove j = i := by
    rw [Fin.succAbove_of_le_castSucc gap j hle_cast]
    apply Fin.ext
    simp [j]
    omega
  have hsign := hgap.2 j
  rw [hsucc] at hsign
  calc
    (C.word i).positive = decide (Even (i.val - 1)) := by
      simpa [j] using hsign
    _ = !decide (Even i.val) := decide_even_pred_eq_not i.val hival_pos

theorem negativePunctured_sign_of_lt {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} {gap i : Fin (n + 1)}
    (hgap : C.NegativePunctured gap) (hi : i < gap) :
    (C.word i).positive = !decide (Even i.val) := by
  let j : Fin n := ⟨i.val, by
    have hi' : i.val < gap.val := Fin.lt_def.mp hi
    have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
    omega⟩
  have hcast : (Fin.castSucc j : Fin (n + 1)) < gap := by
    rw [Fin.lt_def]
    simp [j]
    exact Fin.lt_def.mp hi
  have hsucc : gap.succAbove j = i := by
    rw [Fin.succAbove_of_castSucc_lt gap j hcast]
    apply Fin.ext
    simp [j]
  have hsign := hgap.2 j
  rw [hsucc] at hsign
  simpa [j] using hsign

theorem negativePunctured_sign_of_gt {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} {gap i : Fin (n + 1)}
    (hgap : C.NegativePunctured gap) (hi : gap < i) :
    (C.word i).positive = decide (Even i.val) := by
  have hival_pos : 0 < i.val := by
    have hi' : gap.val < i.val := Fin.lt_def.mp hi
    omega
  let j : Fin n := ⟨i.val - 1, by
    have hle : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    omega⟩
  have hle_cast : gap ≤ (Fin.castSucc j : Fin (n + 1)) := by
    rw [Fin.le_def]
    simp [j]
    exact Nat.le_sub_one_of_lt (Fin.lt_def.mp hi)
  have hsucc : gap.succAbove j = i := by
    rw [Fin.succAbove_of_le_castSucc gap j hle_cast]
    apply Fin.ext
    simp [j]
    omega
  have hsign := hgap.2 j
  rw [hsucc] at hsign
  calc
    (C.word i).positive = (!decide (Even (i.val - 1))) := by
      simpa [j] using hsign
    _ = decide (Even i.val) := not_decide_even_pred_eq i.val hival_pos

theorem positivePunctured_sign_of_ne {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} {gap i : Fin (n + 1)}
    (hgap : C.PositivePunctured gap) (hi : i ≠ gap) :
    (C.word i).positive =
      if i < gap then decide (Even i.val) else !decide (Even i.val) := by
  by_cases hlt : i < gap
  · simp [hlt, positivePunctured_sign_of_lt hgap hlt]
  · have hgt : gap < i := lt_of_le_of_ne (le_of_not_gt hlt) hi.symm
    simp [hlt, positivePunctured_sign_of_gt hgap hgt]

theorem negativePunctured_sign_of_ne {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} {gap i : Fin (n + 1)}
    (hgap : C.NegativePunctured gap) (hi : i ≠ gap) :
    (C.word i).positive =
      if i < gap then !decide (Even i.val) else decide (Even i.val) := by
  by_cases hlt : i < gap
  · simp [hlt, negativePunctured_sign_of_lt hgap hlt]
  · have hgt : gap < i := lt_of_le_of_ne (le_of_not_gt hlt) hi.symm
    simp [hlt, negativePunctured_sign_of_gt hgap hgt]

private theorem positivePunctured_next_of_expected {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m}
    (hstrict : StrictMono fun i : Fin (n + 1) => (C.word i).index)
    {gap : Fin (n + 1)} (hgap : C.PositivePunctured gap)
    (hgaplt : gap.val < n)
    (hsign : (C.word gap).positive = decide (Even gap.val)) :
    C.PositivePunctured (nextGap gap hgaplt) := by
  constructor
  · exact punctured_strictMono_of_strictMono hstrict (nextGap gap hgaplt)
  · intro i
    by_cases hlt : i.val < gap.val
    · have hcast : (Fin.castSucc i : Fin (n + 1)) < nextGap gap hgaplt := by
        rw [Fin.lt_def]
        simp [nextGap]
        omega
      have hsucc : (nextGap gap hgaplt).succAbove i = Fin.castSucc i :=
        Fin.succAbove_of_castSucc_lt (nextGap gap hgaplt) i hcast
      have hi_old : (Fin.castSucc i : Fin (n + 1)) < gap := by
        rw [Fin.lt_def]
        simpa using hlt
      have hsign_old := positivePunctured_sign_of_lt hgap hi_old
      rw [hsucc]
      simpa using hsign_old
    · by_cases heq : i.val = gap.val
      · have hcast : (Fin.castSucc i : Fin (n + 1)) < nextGap gap hgaplt := by
          rw [Fin.lt_def]
          simp [nextGap, heq]
        have hsucc : (nextGap gap hgaplt).succAbove i = Fin.castSucc i :=
          Fin.succAbove_of_castSucc_lt (nextGap gap hgaplt) i hcast
        have hcast_eq : (Fin.castSucc i : Fin (n + 1)) = gap := by
          apply Fin.ext
          simpa using heq
        rw [hsucc, hcast_eq]
        simpa [heq] using hsign
      · have hgt : gap.val < i.val := by omega
        have hle_cast : nextGap gap hgaplt ≤ (Fin.castSucc i : Fin (n + 1)) := by
          rw [Fin.le_def]
          simp [nextGap]
          omega
        have hsucc : (nextGap gap hgaplt).succAbove i = Fin.succ i :=
          Fin.succAbove_of_le_castSucc (nextGap gap hgaplt) i hle_cast
        have hgap_lt_succ : gap < (Fin.succ i : Fin (n + 1)) := by
          rw [Fin.lt_def]
          simp [Fin.val_succ]
          omega
        have hsign_old := positivePunctured_sign_of_gt hgap hgap_lt_succ
        rw [hsucc]
        calc
          (C.word (Fin.succ i : Fin (n + 1))).positive =
              !decide (Even (Fin.succ i : Fin (n + 1)).val) := hsign_old
          _ = decide (Even i.val) := by
            by_cases heven : Even i.val <;> simp [Fin.val_succ, Nat.even_add_one, heven]

private theorem positivePunctured_prev_of_unexpected {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m}
    (hstrict : StrictMono fun i : Fin (n + 1) => (C.word i).index)
    {gap : Fin (n + 1)} (hgap : C.PositivePunctured gap)
    (hgappos : 0 < gap.val)
    (hsign : (C.word gap).positive ≠ decide (Even gap.val)) :
    C.PositivePunctured (prevGap gap hgappos) := by
  have hgap_sign_not : (C.word gap).positive = !decide (Even gap.val) :=
    Bool.eq_not_of_ne hsign
  have hgap_sign_pred : (C.word gap).positive = decide (Even (gap.val - 1)) := by
    rw [decide_even_pred_eq_not gap.val hgappos]
    exact hgap_sign_not
  constructor
  · exact punctured_strictMono_of_strictMono hstrict (prevGap gap hgappos)
  · intro i
    by_cases hlt : i.val < gap.val - 1
    · have hcast : (Fin.castSucc i : Fin (n + 1)) < prevGap gap hgappos := by
        rw [Fin.lt_def]
        simp [prevGap]
        exact hlt
      have hsucc : (prevGap gap hgappos).succAbove i = Fin.castSucc i :=
        Fin.succAbove_of_castSucc_lt (prevGap gap hgappos) i hcast
      have hi_old : (Fin.castSucc i : Fin (n + 1)) < gap := by
        rw [Fin.lt_def]
        simp
        omega
      have hsign_old := positivePunctured_sign_of_lt hgap hi_old
      rw [hsucc]
      simpa using hsign_old
    · by_cases heq : i.val = gap.val - 1
      · have hle_cast : prevGap gap hgappos ≤ (Fin.castSucc i : Fin (n + 1)) := by
          rw [Fin.le_def]
          simp [prevGap, heq]
        have hsucc : (prevGap gap hgappos).succAbove i = Fin.succ i :=
          Fin.succAbove_of_le_castSucc (prevGap gap hgappos) i hle_cast
        have hsucc_eq : (Fin.succ i : Fin (n + 1)) = gap := by
          apply Fin.ext
          simp [Fin.val_succ, heq]
          omega
        rw [hsucc, hsucc_eq]
        simpa [heq] using hgap_sign_pred
      · have hgt : gap.val - 1 < i.val := by omega
        have hle_cast : prevGap gap hgappos ≤ (Fin.castSucc i : Fin (n + 1)) := by
          rw [Fin.le_def]
          simp [prevGap]
          omega
        have hsucc : (prevGap gap hgappos).succAbove i = Fin.succ i :=
          Fin.succAbove_of_le_castSucc (prevGap gap hgappos) i hle_cast
        have hgap_lt_succ : gap < (Fin.succ i : Fin (n + 1)) := by
          rw [Fin.lt_def]
          simp [Fin.val_succ]
          omega
        have hsign_old := positivePunctured_sign_of_gt hgap hgap_lt_succ
        rw [hsucc]
        calc
          (C.word (Fin.succ i : Fin (n + 1))).positive =
              !decide (Even (Fin.succ i : Fin (n + 1)).val) := hsign_old
          _ = decide (Even i.val) := by
            by_cases heven : Even i.val <;> simp [Fin.val_succ, Nat.even_add_one, heven]

private theorem positiveAlternating_of_positivePunctured_last_expected {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m}
    (hstrict : StrictMono fun i : Fin (n + 1) => (C.word i).index)
    {gap : Fin (n + 1)} (hgap : C.PositivePunctured gap)
    (hgaplast : gap.val = n)
    (hsign : (C.word gap).positive = decide (Even gap.val)) :
    C.PositiveAlternating := by
  have hlast : gap = Fin.last n := by
    apply Fin.ext
    simpa [Fin.last] using hgaplast
  subst gap
  constructor
  · exact hstrict
  · intro i
    by_cases hi : i = Fin.last n
    · subst i
      simpa [Fin.last] using hsign
    · have hlt : i < Fin.last n := by
        rw [Fin.lt_def]
        have hle : i.val ≤ n := Nat.le_of_lt_succ i.isLt
        simp [Fin.last]
        omega
      exact positivePunctured_sign_of_lt hgap hlt

private theorem negativeAlternating_of_positivePunctured_zero_unexpected {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m}
    (hstrict : StrictMono fun i : Fin (n + 1) => (C.word i).index)
    {gap : Fin (n + 1)} (hgap : C.PositivePunctured gap)
    (hgapzero : gap.val = 0)
    (hsign : (C.word gap).positive ≠ decide (Even gap.val)) :
    C.NegativeAlternating := by
  have hgap_sign_not : (C.word gap).positive = !decide (Even gap.val) :=
    Bool.eq_not_of_ne hsign
  have hzero : gap = 0 := by
    apply Fin.ext
    simpa using hgapzero
  subst gap
  constructor
  · exact hstrict
  · intro i
    by_cases hi : i = (0 : Fin (n + 1))
    · subst i
      simpa using hgap_sign_not
    · have hgt : (0 : Fin (n + 1)) < i := by
        rw [Fin.lt_def]
        have hne : i.val ≠ 0 := by
          intro hval
          exact hi (Fin.ext hval)
        omega
      exact positivePunctured_sign_of_gt hgap hgt

theorem positivePunctured_gaps_val_close {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} {gap gap' : Fin (n + 1)}
    (hgap : C.PositivePunctured gap) (hgap' : C.PositivePunctured gap') :
    gap.val ≤ gap'.val + 1 ∧ gap'.val ≤ gap.val + 1 := by
  constructor
  · by_contra hle
    have hlt : gap'.val + 1 < gap.val := by omega
    let i : Fin (n + 1) := ⟨gap'.val + 1, by omega⟩
    have hgap'_lt_i : gap' < i := by
      rw [Fin.lt_def]
      simp [i]
    have hi_lt_gap : i < gap := by
      rw [Fin.lt_def]
      simp [i]
      omega
    have hleft := positivePunctured_sign_of_gt hgap' hgap'_lt_i
    have hright := positivePunctured_sign_of_lt hgap hi_lt_gap
    rw [hleft] at hright
    cases decide (Even i.val) <;> simp at hright
  · by_contra hle
    have hlt : gap.val + 1 < gap'.val := by omega
    let i : Fin (n + 1) := ⟨gap.val + 1, by omega⟩
    have hgap_lt_i : gap < i := by
      rw [Fin.lt_def]
      simp [i]
    have hi_lt_gap' : i < gap' := by
      rw [Fin.lt_def]
      simp [i]
      omega
    have hleft := positivePunctured_sign_of_gt hgap hgap_lt_i
    have hright := positivePunctured_sign_of_lt hgap' hi_lt_gap'
    rw [hleft] at hright
    cases decide (Even i.val) <;> simp at hright

theorem negativePunctured_gaps_val_close {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} {gap gap' : Fin (n + 1)}
    (hgap : C.NegativePunctured gap) (hgap' : C.NegativePunctured gap') :
    gap.val ≤ gap'.val + 1 ∧ gap'.val ≤ gap.val + 1 := by
  constructor
  · by_contra hle
    have hlt : gap'.val + 1 < gap.val := by omega
    let i : Fin (n + 1) := ⟨gap'.val + 1, by omega⟩
    have hgap'_lt_i : gap' < i := by
      rw [Fin.lt_def]
      simp [i]
    have hi_lt_gap : i < gap := by
      rw [Fin.lt_def]
      simp [i]
      omega
    have hleft := negativePunctured_sign_of_gt hgap' hgap'_lt_i
    have hright := negativePunctured_sign_of_lt hgap hi_lt_gap
    rw [hleft] at hright
    cases decide (Even i.val) <;> simp at hright
  · by_contra hle
    have hlt : gap.val + 1 < gap'.val := by omega
    let i : Fin (n + 1) := ⟨gap.val + 1, by omega⟩
    have hgap_lt_i : gap < i := by
      rw [Fin.lt_def]
      simp [i]
    have hi_lt_gap' : i < gap' := by
      rw [Fin.lt_def]
      simp [i]
      omega
    have hleft := negativePunctured_sign_of_gt hgap hgap_lt_i
    have hright := negativePunctured_sign_of_lt hgap' hi_lt_gap'
    rw [hleft] at hright
    cases decide (Even i.val) <;> simp at hright

theorem positive_negativePunctured_endpoints_of_lt {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} {positive negative : Fin (n + 1)}
    (hpositive : C.PositivePunctured positive) (hnegative : C.NegativePunctured negative)
    (hgap : positive < negative) :
    positive = 0 ∧ negative = Fin.last n := by
  have hpos_zero : positive.val = 0 := by
    by_contra hpos
    have hpos_pos : 0 < positive.val := by omega
    let i : Fin (n + 1) := ⟨positive.val - 1, by omega⟩
    have hi_lt_positive : i < positive := by
      rw [Fin.lt_def]
      change positive.val - 1 < positive.val
      omega
    have hi_lt_negative : i < negative := lt_trans hi_lt_positive hgap
    have hleft := positivePunctured_sign_of_lt hpositive hi_lt_positive
    have hright := negativePunctured_sign_of_lt hnegative hi_lt_negative
    rw [hleft] at hright
    cases decide (Even i.val) <;> simp at hright
  have hneg_last : negative.val = n := by
    by_contra hneg
    have hneg_lt : negative.val < n := by
      have hle : negative.val ≤ n := Nat.le_of_lt_succ negative.isLt
      omega
    let i : Fin (n + 1) := ⟨negative.val + 1, by omega⟩
    have hpositive_lt_i : positive < i := lt_trans hgap (by
      rw [Fin.lt_def]
      simp [i])
    have hnegative_lt_i : negative < i := by
      rw [Fin.lt_def]
      simp [i]
    have hleft := positivePunctured_sign_of_gt hpositive hpositive_lt_i
    have hright := negativePunctured_sign_of_gt hnegative hnegative_lt_i
    rw [hleft] at hright
    cases decide (Even i.val) <;> simp at hright
  constructor
  · exact Fin.ext hpos_zero
  · apply Fin.ext
    simpa [Fin.last] using hneg_last

theorem negative_positivePunctured_endpoints_of_lt {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} {negative positive : Fin (n + 1)}
    (hnegative : C.NegativePunctured negative) (hpositive : C.PositivePunctured positive)
    (hgap : negative < positive) :
    negative = 0 ∧ positive = Fin.last n := by
  have hneg_zero : negative.val = 0 := by
    by_contra hneg
    have hneg_pos : 0 < negative.val := by omega
    let i : Fin (n + 1) := ⟨negative.val - 1, by omega⟩
    have hi_lt_negative : i < negative := by
      rw [Fin.lt_def]
      change negative.val - 1 < negative.val
      omega
    have hi_lt_positive : i < positive := lt_trans hi_lt_negative hgap
    have hleft := negativePunctured_sign_of_lt hnegative hi_lt_negative
    have hright := positivePunctured_sign_of_lt hpositive hi_lt_positive
    rw [hleft] at hright
    cases decide (Even i.val) <;> simp at hright
  have hpos_last : positive.val = n := by
    by_contra hpos
    have hpos_lt : positive.val < n := by
      have hle : positive.val ≤ n := Nat.le_of_lt_succ positive.isLt
      omega
    let i : Fin (n + 1) := ⟨positive.val + 1, by omega⟩
    have hnegative_lt_i : negative < i := lt_trans hgap (by
      rw [Fin.lt_def]
      simp [i])
    have hpositive_lt_i : positive < i := by
      rw [Fin.lt_def]
      simp [i]
    have hleft := negativePunctured_sign_of_gt hnegative hnegative_lt_i
    have hright := positivePunctured_sign_of_gt hpositive hpositive_lt_i
    rw [hleft] at hright
    cases decide (Even i.val) <;> simp at hright
  constructor
  · exact Fin.ext hneg_zero
  · apply Fin.ext
    simpa [Fin.last] using hpos_last

theorem positiveAlternating_positivePunctured_iff {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} (hC : C.PositiveAlternating)
    (gap : Fin (n + 1)) :
    C.PositivePunctured gap ↔ gap = Fin.last n := by
  constructor
  · intro hgapP
    by_cases hgap : gap.val < n
    · let i : Fin n := ⟨gap.val, hgap⟩
      have hp := hgapP.2 i
      have hf := hC.2 (gap.succAbove i)
      have hle : gap ≤ i.castSucc := by
        rw [Fin.le_def]
        simp [i]
      have hval : (gap.succAbove i).val = gap.val + 1 := by
        rw [Fin.succAbove_of_le_castSucc gap i hle]
        simp [i]
      rw [hf] at hp
      have hpar : decide (Even (gap.val + 1)) = !decide (Even gap.val) := by
        by_cases he : Even gap.val <;> simp [Nat.even_add_one, he]
      simp [i, hval, hpar] at hp
    · apply Fin.ext
      have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
      simp [Fin.last]
      omega
  · intro hlast
    subst gap
    constructor
    · intro i j hij
      have hcast : (Fin.castSucc i : Fin (n + 1)) < Fin.castSucc j :=
        Fin.castSucc_lt_castSucc_iff.mpr hij
      simpa [Fin.succAbove_last] using hC.1 hcast
    · intro i
      simpa [Fin.succAbove_last] using hC.2 (Fin.castSucc i)

theorem positiveAlternating_negativePunctured_iff {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} (hC : C.PositiveAlternating)
    (gap : Fin (n + 1)) :
    C.NegativePunctured gap ↔ gap = 0 := by
  constructor
  · intro hgapP
    by_cases hzero : gap.val = 0
    · apply Fin.ext
      simpa using hzero
    · let i : Fin n := ⟨gap.val - 1, by omega⟩
      have hp := hgapP.2 i
      have hf := hC.2 (gap.succAbove i)
      have hlt : i.castSucc < gap := by
        rw [Fin.lt_def]
        change gap.val - 1 < gap.val
        omega
      have hval : (gap.succAbove i).val = gap.val - 1 := by
        rw [Fin.succAbove_of_castSucc_lt gap i hlt]
        simp [i]
      rw [hf] at hp
      simp [i, hval] at hp
  · intro hzero
    subst gap
    constructor
    · intro i j hij
      have hsucc : (Fin.succ i : Fin (n + 1)) < Fin.succ j :=
        Fin.succ_lt_succ_iff.mpr hij
      simpa [Fin.succAbove_zero] using hC.1 hsucc
    · intro i
      have hf := hC.2 (Fin.succ i : Fin (n + 1))
      calc
        (C.word ((0 : Fin (n + 1)).succAbove i)).positive =
            decide (Even (Fin.succ i).val) := by
          simpa [Fin.succAbove_zero] using hf
        _ = !decide (Even i.val) := by
          by_cases hi : Even i.val <;> simp [Fin.val_succ, Nat.even_add_one, hi]

theorem negativeAlternating_positivePunctured_iff {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} (hC : C.NegativeAlternating)
    (gap : Fin (n + 1)) :
    C.PositivePunctured gap ↔ gap = 0 := by
  constructor
  · intro hgapP
    by_cases hzero : gap.val = 0
    · apply Fin.ext
      simpa using hzero
    · let i : Fin n := ⟨gap.val - 1, by omega⟩
      have hp := hgapP.2 i
      have hf := hC.2 (gap.succAbove i)
      have hlt : i.castSucc < gap := by
        rw [Fin.lt_def]
        change gap.val - 1 < gap.val
        omega
      have hval : (gap.succAbove i).val = gap.val - 1 := by
        rw [Fin.succAbove_of_castSucc_lt gap i hlt]
        simp [i]
      rw [hf] at hp
      simp [i, hval] at hp
  · intro hzero
    subst gap
    constructor
    · intro i j hij
      have hsucc : (Fin.succ i : Fin (n + 1)) < Fin.succ j :=
        Fin.succ_lt_succ_iff.mpr hij
      simpa [Fin.succAbove_zero] using hC.1 hsucc
    · intro i
      have hf := hC.2 (Fin.succ i : Fin (n + 1))
      calc
        (C.word ((0 : Fin (n + 1)).succAbove i)).positive =
            !decide (Even (Fin.succ i).val) := by
          simpa [Fin.succAbove_zero] using hf
        _ = decide (Even i.val) := by
          by_cases hi : Even i.val <;> simp [Fin.val_succ, Nat.even_add_one, hi]

theorem negativeAlternating_negativePunctured_iff {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} (hC : C.NegativeAlternating)
    (gap : Fin (n + 1)) :
    C.NegativePunctured gap ↔ gap = Fin.last n := by
  constructor
  · intro hgapP
    by_cases hgap : gap.val < n
    · let i : Fin n := ⟨gap.val, hgap⟩
      have hp := hgapP.2 i
      have hf := hC.2 (gap.succAbove i)
      have hle : gap ≤ i.castSucc := by
        rw [Fin.le_def]
        simp [i]
      have hval : (gap.succAbove i).val = gap.val + 1 := by
        rw [Fin.succAbove_of_le_castSucc gap i hle]
        simp [i]
      rw [hf] at hp
      have hpar : decide (Even (gap.val + 1)) = !decide (Even gap.val) := by
        by_cases he : Even gap.val <;> simp [Nat.even_add_one, he]
      simp [i, hval, hpar] at hp
    · apply Fin.ext
      have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
      simp [Fin.last]
      omega
  · intro hlast
    subst gap
    constructor
    · intro i j hij
      have hcast : (Fin.castSucc i : Fin (n + 1)) < Fin.castSucc j :=
        Fin.castSucc_lt_castSucc_iff.mpr hij
      simpa [Fin.succAbove_last] using hC.1 hcast
    · intro i
      simpa [Fin.succAbove_last] using hC.2 (Fin.castSucc i)

noncomputable def alternatingDeletionGaps {n m : ℕ}
    (C : AlternatingWordContext (n + 1) m) : Finset (Fin (n + 1)) :=
  by
    classical
    exact Finset.univ.filter fun gap => C.PositivePunctured gap ∨ C.NegativePunctured gap

theorem mem_alternatingDeletionGaps_iff {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} {gap : Fin (n + 1)} :
    gap ∈ C.alternatingDeletionGaps ↔ C.PositivePunctured gap ∨ C.NegativePunctured gap := by
  classical
  simp [alternatingDeletionGaps]

theorem alternatingDeletionGaps_negate {n m : ℕ}
    (C : AlternatingWordContext (n + 1) m) :
    C.negate.alternatingDeletionGaps = C.alternatingDeletionGaps := by
  classical
  ext gap
  rw [mem_alternatingDeletionGaps_iff, mem_alternatingDeletionGaps_iff]
  simp [negate_positivePunctured_iff, negate_negativePunctured_iff, or_comm]

theorem alternatingDeletionGaps_eq_endpoints_of_positiveAlternating {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} (hC : C.PositiveAlternating) :
    C.alternatingDeletionGaps = {0, Fin.last n} := by
  classical
  ext gap
  rw [mem_alternatingDeletionGaps_iff]
  simp [positiveAlternating_positivePunctured_iff hC gap,
    positiveAlternating_negativePunctured_iff hC gap, or_comm]

theorem alternatingDeletionGaps_eq_endpoints_of_negativeAlternating {n m : ℕ}
    {C : AlternatingWordContext (n + 1) m} (hC : C.NegativeAlternating) :
    C.alternatingDeletionGaps = {0, Fin.last n} := by
  classical
  ext gap
  rw [mem_alternatingDeletionGaps_iff]
  simp [negativeAlternating_positivePunctured_iff hC gap,
    negativeAlternating_negativePunctured_iff hC gap, or_comm]

theorem alternatingDeletionGaps_card_eq_two_of_positiveAlternating {n m : ℕ}
    (hn : 0 < n) {C : AlternatingWordContext (n + 1) m} (hC : C.PositiveAlternating) :
    C.alternatingDeletionGaps.card = 2 := by
  classical
  rw [alternatingDeletionGaps_eq_endpoints_of_positiveAlternating hC]
  have hne : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have hval := congrArg Fin.val h
    simp [Fin.last] at hval
    omega
  simp [hne]

theorem alternatingDeletionGaps_card_eq_two_of_negativeAlternating {n m : ℕ}
    (hn : 0 < n) {C : AlternatingWordContext (n + 1) m} (hC : C.NegativeAlternating) :
    C.alternatingDeletionGaps.card = 2 := by
  classical
  rw [alternatingDeletionGaps_eq_endpoints_of_negativeAlternating hC]
  have hne : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have hval := congrArg Fin.val h
    simp [Fin.last] at hval
    omega
  simp [hne]

private theorem alternatingDeletionGaps_eq_pair_of_positivePunctured_next {n m : ℕ}
    (hn : 0 < n) {C : AlternatingWordContext (n + 1) m}
    (hstrict : StrictMono fun i : Fin (n + 1) => (C.word i).index)
    {gap : Fin (n + 1)} (hgap : C.PositivePunctured gap)
    (hgaplt : gap.val < n)
    (hsign : (C.word gap).positive = decide (Even gap.val)) :
    C.alternatingDeletionGaps = {gap, nextGap gap hgaplt} := by
  classical
  have hnext : C.PositivePunctured (nextGap gap hgaplt) :=
    positivePunctured_next_of_expected hstrict hgap hgaplt hsign
  ext x
  rw [mem_alternatingDeletionGaps_iff]
  constructor
  · intro hx
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases hx with hxpos | hxneg
    · have hclose := positivePunctured_gaps_val_close hgap hxpos
      have hnot_prev : ¬ x.val + 1 = gap.val := by
        intro hprev
        have hx_lt_gap : x < gap := by
          rw [Fin.lt_def]
          omega
        have hsign_x := positivePunctured_sign_of_gt hxpos hx_lt_gap
        rw [hsign] at hsign_x
        cases decide (Even gap.val) <;> simp at hsign_x
      have hxval : x.val = gap.val ∨ x.val = gap.val + 1 := by omega
      rcases hxval with hxval | hxval
      · exact Or.inl (Fin.ext hxval)
      · exact Or.inr (Fin.ext (by simpa [nextGap] using hxval))
    · have hxne : x ≠ gap := by
        intro hxeq
        subst x
        exact positive_negativePunctured_same_false hn hgap hxneg
      by_cases hlt : gap < x
      · have hsign_x := negativePunctured_sign_of_lt hxneg hlt
        rw [hsign] at hsign_x
        cases decide (Even gap.val) <;> simp at hsign_x
      · have hx_lt_gap : x < gap := lt_of_le_of_ne (le_of_not_gt hlt) hxne
        have hend := negative_positivePunctured_endpoints_of_lt hxneg hgap hx_lt_gap
        have hlast := congrArg Fin.val hend.2
        simp [Fin.last] at hlast
        omega
  · intro hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · exact Or.inl (by simpa [hx] using hgap)
    · exact Or.inl (by simpa [hx] using hnext)

private theorem alternatingDeletionGaps_eq_pair_of_positivePunctured_prev {n m : ℕ}
    (hn : 0 < n) {C : AlternatingWordContext (n + 1) m}
    (hstrict : StrictMono fun i : Fin (n + 1) => (C.word i).index)
    {gap : Fin (n + 1)} (hgap : C.PositivePunctured gap)
    (hgappos : 0 < gap.val)
    (hsign : (C.word gap).positive ≠ decide (Even gap.val)) :
    C.alternatingDeletionGaps = {prevGap gap hgappos, gap} := by
  classical
  have hprev : C.PositivePunctured (prevGap gap hgappos) :=
    positivePunctured_prev_of_unexpected hstrict hgap hgappos hsign
  ext x
  rw [mem_alternatingDeletionGaps_iff]
  constructor
  · intro hx
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases hx with hxpos | hxneg
    · have hclose := positivePunctured_gaps_val_close hgap hxpos
      have hnot_next : ¬ x.val = gap.val + 1 := by
        intro hnext
        have hgap_lt_x : gap < x := by
          rw [Fin.lt_def]
          omega
        have hsign_x := positivePunctured_sign_of_lt hxpos hgap_lt_x
        exact hsign hsign_x
      have hxval : x.val = gap.val - 1 ∨ x.val = gap.val := by omega
      rcases hxval with hxval | hxval
      · exact Or.inl (Fin.ext (by simpa [prevGap] using hxval))
      · exact Or.inr (Fin.ext hxval)
    · have hxne : x ≠ gap := by
        intro hxeq
        subst x
        exact positive_negativePunctured_same_false hn hgap hxneg
      by_cases hlt : x < gap
      · have hsign_x := negativePunctured_sign_of_gt hxneg hlt
        exact False.elim (hsign hsign_x)
      · have hgap_lt_x : gap < x := lt_of_le_of_ne (le_of_not_gt hlt) hxne.symm
        have hend := positive_negativePunctured_endpoints_of_lt hgap hxneg hgap_lt_x
        have hzero : gap.val = 0 := by
          simpa using congrArg Fin.val hend.1
        omega
  · intro hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · exact Or.inl (by simpa [hx] using hprev)
    · exact Or.inl (by simpa [hx] using hgap)

private theorem alternatingDeletionGaps_card_eq_two_of_positivePunctured {n m : ℕ}
    (hn : 0 < n) {C : AlternatingWordContext (n + 1) m}
    (hstrict : StrictMono fun i : Fin (n + 1) => (C.word i).index)
    {gap : Fin (n + 1)} (hgap : C.PositivePunctured gap) :
    C.alternatingDeletionGaps.card = 2 := by
  classical
  by_cases hsign : (C.word gap).positive = decide (Even gap.val)
  · by_cases hlast : gap.val = n
    · exact alternatingDeletionGaps_card_eq_two_of_positiveAlternating hn
        (positiveAlternating_of_positivePunctured_last_expected
          hstrict hgap hlast hsign)
    · have hgaplt : gap.val < n := by
        have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
        omega
      rw [alternatingDeletionGaps_eq_pair_of_positivePunctured_next
        hn hstrict hgap hgaplt hsign]
      have hne : gap ≠ nextGap gap hgaplt := by
        intro h
        have hval := congrArg Fin.val h
        simp [nextGap] at hval
      simp [hne]
  · by_cases hzero : gap.val = 0
    · exact alternatingDeletionGaps_card_eq_two_of_negativeAlternating hn
        (negativeAlternating_of_positivePunctured_zero_unexpected
          hstrict hgap hzero hsign)
    · have hgappos : 0 < gap.val := by omega
      rw [alternatingDeletionGaps_eq_pair_of_positivePunctured_prev
        hn hstrict hgap hgappos hsign]
      have hne : prevGap gap hgappos ≠ gap := by
        intro h
        have hval := congrArg Fin.val h
        simp [prevGap] at hval
        omega
      simp [hne]

theorem alternatingDeletionGaps_card_eq_two {n m : ℕ}
    (hn : 0 < n) {C : AlternatingWordContext (n + 1) m}
    (hstrict : StrictMono fun i : Fin (n + 1) => (C.word i).index)
    (hactive : C.alternatingDeletionGaps.Nonempty) :
    C.alternatingDeletionGaps.card = 2 := by
  rcases hactive with ⟨gap, hgapmem⟩
  rw [mem_alternatingDeletionGaps_iff] at hgapmem
  rcases hgapmem with hpositive | hnegative
  · exact alternatingDeletionGaps_card_eq_two_of_positivePunctured hn hstrict hpositive
  · have hstrict_neg :
        StrictMono fun i : Fin (n + 1) => (C.negate.word i).index :=
      negate_strictMono_iff.mpr hstrict
    have hpositive_neg : C.negate.PositivePunctured gap :=
      negate_positivePunctured_iff.mpr hnegative
    have hcard :=
      alternatingDeletionGaps_card_eq_two_of_positivePunctured
        (C := C.negate) hn hstrict_neg hpositive_neg
    rwa [alternatingDeletionGaps_negate C] at hcard

end AlternatingWordContext

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

theorem prefixChain_same_index_same_sign_of_no_complement {n m : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation n) {i j : Fin n} (hij : i ≤ j)
    (hindex : (label (P.prefixChain i)).index =
      (label (P.prefixChain j)).index) :
    (label (P.prefixChain i)).positive =
      (label (P.prefixChain j)).positive := by
  exact positive_eq_of_le_of_same_index_of_no_complement
    hno (P.prefixChain_le hij) hindex

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

/-- The dimension-free label word carried by a signed-permutation prefix
chain under the no-complement hypothesis. -/
def prefixChainWordContext {n m : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation n) : AlternatingWordContext n m where
  word := fun i => label (P.prefixChain i)
  same_index_same_sign := by
    intro i j hij hindex
    exact SignedPermutation.prefixChain_same_index_same_sign_of_no_complement
      hno P hij hindex

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

theorem prefixChainWordContext_positiveAlternating_iff {n m : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation n) :
    (prefixChainWordContext hno P).PositiveAlternating ↔
      PositiveAlternatingPrefixLabels label P := by
  rfl

theorem prefixChainWordContext_negativeAlternating_iff {n m : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation n) :
    (prefixChainWordContext hno P).NegativeAlternating ↔
      NegativeAlternatingPrefixLabels label P := by
  rfl

theorem prefixChainWordContext_positivePunctured_iff {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    (prefixChainWordContext hno P).PositivePunctured gap ↔
      PositiveAlternatingPuncturedPrefixLabels label P gap := by
  rfl

theorem prefixChainWordContext_negativePunctured_iff {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    (prefixChainWordContext hno P).NegativePunctured gap ↔
      NegativeAlternatingPuncturedPrefixLabels label P gap := by
  rfl

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

private lemma unique_ne_of_card_eq_two {β : Type*} [Fintype β] [DecidableEq β]
    (hcard : Fintype.card β = 2) (x y z : β) (hy : y ≠ x) (hz : z ≠ x) : y = z := by
  by_contra hyz
  have hle : ({x, y, z} : Finset β).card ≤ Fintype.card β := Finset.card_le_univ _
  have hxy : x ≠ y := fun h => hy h.symm
  have hxz : x ≠ z := fun h => hz h.symm
  have hcard3 : ({x, y, z} : Finset β).card = 3 := by
    simp [hxy, hxz, hyz]
  omega

private lemma relationClassPartner_exists {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R]
    (_hrefl : ∀ x, R x x)
    (hcard : ∀ x, Fintype.card {y : α // R x y} = 2)
    (x : α) : ∃ y, R x y ∧ y ≠ x := by
  by_contra h
  have hsubsingleton : Subsingleton {y : α // R x y} := by
    refine ⟨fun a b => ?_⟩
    apply Subtype.ext
    have ha : a.1 = x := by
      by_contra hne
      exact h ⟨a.1, a.2, hne⟩
    have hb : b.1 = x := by
      by_contra hne
      exact h ⟨b.1, b.2, hne⟩
    exact ha.trans hb.symm
  have hle : Fintype.card {y : α // R x y} ≤ 1 :=
    Fintype.card_le_one_iff_subsingleton.mpr hsubsingleton
  rw [hcard x] at hle
  omega

noncomputable def relationClassPartner {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R]
    (hrefl : ∀ x, R x x)
    (hcard : ∀ x, Fintype.card {y : α // R x y} = 2)
    (x : α) : α :=
  Classical.choose (relationClassPartner_exists R hrefl hcard x)

theorem relationClassPartner_rel {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R]
    (hrefl : ∀ x, R x x)
    (hcard : ∀ x, Fintype.card {y : α // R x y} = 2)
    (x : α) : R x (relationClassPartner R hrefl hcard x) :=
  (Classical.choose_spec (relationClassPartner_exists R hrefl hcard x)).1

theorem relationClassPartner_ne {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R]
    (hrefl : ∀ x, R x x)
    (hcard : ∀ x, Fintype.card {y : α // R x y} = 2)
    (x : α) : relationClassPartner R hrefl hcard x ≠ x :=
  (Classical.choose_spec (relationClassPartner_exists R hrefl hcard x)).2

theorem relationClassPartner_involutive {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R]
    (hrefl : ∀ x, R x x)
    (hsymm : ∀ {x y}, R x y → R y x)
    (hcard : ∀ x, Fintype.card {y : α // R x y} = 2) :
    Function.Involutive (relationClassPartner R hrefl hcard) := by
  intro x
  let y := relationClassPartner R hrefl hcard x
  have hxy : R x y := relationClassPartner_rel R hrefl hcard x
  have hyx : R y x := hsymm hxy
  have hy_partner : R y (relationClassPartner R hrefl hcard y) :=
    relationClassPartner_rel R hrefl hcard y
  have hfirst_ne : (⟨x, hyx⟩ : {z : α // R y z}) ≠ ⟨y, hrefl y⟩ := by
    intro h
    have hval := congrArg Subtype.val h
    exact relationClassPartner_ne R hrefl hcard x hval.symm
  have hsecond_ne :
      (⟨relationClassPartner R hrefl hcard y, hy_partner⟩ : {z : α // R y z}) ≠
        ⟨y, hrefl y⟩ := by
    intro h
    have hval := congrArg Subtype.val h
    exact relationClassPartner_ne R hrefl hcard y hval
  have hsub := unique_ne_of_card_eq_two (β := {z : α // R y z}) (hcard y)
    ⟨y, hrefl y⟩ ⟨x, hyx⟩ ⟨relationClassPartner R hrefl hcard y, hy_partner⟩
    hfirst_ne hsecond_ne
  simpa [y] using (congrArg Subtype.val hsub).symm

theorem relationClassPartner_map {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R]
    (hrefl : ∀ x, R x x)
    (hcard : ∀ x, Fintype.card {y : α // R x y} = 2)
    (e : α ≃ α) (hmap : ∀ x y, R (e x) (e y) ↔ R x y)
    (x : α) :
    e (relationClassPartner R hrefl hcard x) =
      relationClassPartner R hrefl hcard (e x) := by
  have hleft_rel :
      R (e x) (e (relationClassPartner R hrefl hcard x)) :=
    (hmap x (relationClassPartner R hrefl hcard x)).mpr
      (relationClassPartner_rel R hrefl hcard x)
  have hright_rel :
      R (e x) (relationClassPartner R hrefl hcard (e x)) :=
    relationClassPartner_rel R hrefl hcard (e x)
  have hleft_ne :
      (⟨e (relationClassPartner R hrefl hcard x), hleft_rel⟩ :
          {y : α // R (e x) y}) ≠ ⟨e x, hrefl (e x)⟩ := by
    intro h
    exact relationClassPartner_ne R hrefl hcard x (e.injective (congrArg Subtype.val h))
  have hright_ne :
      (⟨relationClassPartner R hrefl hcard (e x), hright_rel⟩ :
          {y : α // R (e x) y}) ≠ ⟨e x, hrefl (e x)⟩ := by
    intro h
    exact relationClassPartner_ne R hrefl hcard (e x) (congrArg Subtype.val h)
  have hsub := unique_ne_of_card_eq_two (β := {y : α // R (e x) y}) (hcard (e x))
    ⟨e x, hrefl (e x)⟩
    ⟨e (relationClassPartner R hrefl hcard x), hleft_rel⟩
    ⟨relationClassPartner R hrefl hcard (e x), hright_rel⟩
    hleft_ne hright_ne
  exact congrArg Subtype.val hsub

theorem relationClassPartner_not_map {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R]
    (hrefl : ∀ x, R x x)
    (hcard : ∀ x, Fintype.card {y : α // R x y} = 2)
    (e : α ≃ α) (hnot : ∀ x, ¬ R x (e x))
    (x : α) :
    e x ≠ relationClassPartner R hrefl hcard x := by
  intro h
  have hrel : R x (relationClassPartner R hrefl hcard x) :=
    relationClassPartner_rel R hrefl hcard x
  exact hnot x (by simpa [← h] using hrel)

noncomputable def relationClassPartnerEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R]
    (hrefl : ∀ x, R x x)
    (hsymm : ∀ {x y}, R x y → R y x)
    (hcard : ∀ x, Fintype.card {y : α // R x y} = 2) : α ≃ α where
  toFun := relationClassPartner R hrefl hcard
  invFun := relationClassPartner R hrefl hcard
  left_inv := relationClassPartner_involutive R hrefl hsymm hcard
  right_inv := relationClassPartner_involutive R hrefl hsymm hcard

noncomputable def endpointPartnerOfReachableCardTwo {Vertex Endpoint : Type*}
    [Fintype Endpoint] [DecidableEq Endpoint]
    (G : SimpleGraph Vertex) (endpointVertex : Endpoint ↪ Vertex)
    [DecidableRel fun e e' : Endpoint => G.Reachable (endpointVertex e) (endpointVertex e')]
    (hcard :
      ∀ e : Endpoint,
        Fintype.card {e' : Endpoint // G.Reachable (endpointVertex e) (endpointVertex e')} = 2) :
    Endpoint ≃ Endpoint :=
  relationClassPartnerEquiv
    (fun e e' : Endpoint => G.Reachable (endpointVertex e) (endpointVertex e'))
    (fun e => by exact SimpleGraph.Reachable.refl (G := G) (endpointVertex e))
    (fun h => h.symm)
    hcard

theorem endpointPartnerOfReachableCardTwo_reachable {Vertex Endpoint : Type*}
    [Fintype Endpoint] [DecidableEq Endpoint]
    (G : SimpleGraph Vertex) (endpointVertex : Endpoint ↪ Vertex)
    [DecidableRel fun e e' : Endpoint => G.Reachable (endpointVertex e) (endpointVertex e')]
    (hcard :
      ∀ e : Endpoint,
        Fintype.card {e' : Endpoint // G.Reachable (endpointVertex e) (endpointVertex e')} = 2)
    (e : Endpoint) :
    G.Reachable (endpointVertex e)
      (endpointVertex (endpointPartnerOfReachableCardTwo G endpointVertex hcard e)) :=
  relationClassPartner_rel
    (fun e e' : Endpoint => G.Reachable (endpointVertex e) (endpointVertex e'))
    (fun e => by exact SimpleGraph.Reachable.refl (G := G) (endpointVertex e))
    hcard e

theorem endpointPartnerOfReachableCardTwo_involutive {Vertex Endpoint : Type*}
    [Fintype Endpoint] [DecidableEq Endpoint]
    (G : SimpleGraph Vertex) (endpointVertex : Endpoint ↪ Vertex)
    [DecidableRel fun e e' : Endpoint => G.Reachable (endpointVertex e) (endpointVertex e')]
    (hcard :
      ∀ e : Endpoint,
        Fintype.card {e' : Endpoint // G.Reachable (endpointVertex e) (endpointVertex e')} = 2) :
    Function.Involutive (endpointPartnerOfReachableCardTwo G endpointVertex hcard) :=
  relationClassPartner_involutive
    (fun e e' : Endpoint => G.Reachable (endpointVertex e) (endpointVertex e'))
    (fun e => by exact SimpleGraph.Reachable.refl (G := G) (endpointVertex e))
    (fun h => h.symm)
    hcard

theorem endpointPartnerOfReachableCardTwo_fixedPointFree {Vertex Endpoint : Type*}
    [Fintype Endpoint] [DecidableEq Endpoint]
    (G : SimpleGraph Vertex) (endpointVertex : Endpoint ↪ Vertex)
    [DecidableRel fun e e' : Endpoint => G.Reachable (endpointVertex e) (endpointVertex e')]
    (hcard :
      ∀ e : Endpoint,
        Fintype.card {e' : Endpoint // G.Reachable (endpointVertex e) (endpointVertex e')} = 2)
    (e : Endpoint) :
    endpointPartnerOfReachableCardTwo G endpointVertex hcard e ≠ e :=
  relationClassPartner_ne
    (fun e e' : Endpoint => G.Reachable (endpointVertex e) (endpointVertex e'))
    (fun e => by exact SimpleGraph.Reachable.refl (G := G) (endpointVertex e))
    hcard e

theorem endpointPartnerOfReachableCardTwo_comm {Vertex Endpoint : Type*}
    [Fintype Endpoint] [DecidableEq Endpoint]
    (G : SimpleGraph Vertex) (endpointVertex : Endpoint ↪ Vertex)
    [DecidableRel fun e e' : Endpoint => G.Reachable (endpointVertex e) (endpointVertex e')]
    (hcard :
      ∀ e : Endpoint,
        Fintype.card {e' : Endpoint // G.Reachable (endpointVertex e) (endpointVertex e')} = 2)
    (endpointAntipode : Endpoint ≃ Endpoint)
    (hreachable :
      ∀ e e' : Endpoint,
        G.Reachable (endpointVertex (endpointAntipode e))
            (endpointVertex (endpointAntipode e')) ↔
          G.Reachable (endpointVertex e) (endpointVertex e'))
    (e : Endpoint) :
    endpointAntipode (endpointPartnerOfReachableCardTwo G endpointVertex hcard e) =
      endpointPartnerOfReachableCardTwo G endpointVertex hcard (endpointAntipode e) :=
  relationClassPartner_map
    (fun e e' : Endpoint => G.Reachable (endpointVertex e) (endpointVertex e'))
    (fun e => by exact SimpleGraph.Reachable.refl (G := G) (endpointVertex e))
    hcard endpointAntipode hreachable e

theorem endpointPartnerOfReachableCardTwo_not_antipodal {Vertex Endpoint : Type*}
    [Fintype Endpoint] [DecidableEq Endpoint]
    (G : SimpleGraph Vertex) (endpointVertex : Endpoint ↪ Vertex)
    [DecidableRel fun e e' : Endpoint => G.Reachable (endpointVertex e) (endpointVertex e')]
    (hcard :
      ∀ e : Endpoint,
        Fintype.card {e' : Endpoint // G.Reachable (endpointVertex e) (endpointVertex e')} = 2)
    (endpointAntipode : Endpoint ≃ Endpoint)
    (hnot :
      ∀ e : Endpoint,
        ¬ G.Reachable (endpointVertex e) (endpointVertex (endpointAntipode e)))
    (e : Endpoint) :
    endpointAntipode e ≠ endpointPartnerOfReachableCardTwo G endpointVertex hcard e :=
  relationClassPartner_not_map
    (fun e e' : Endpoint => G.Reachable (endpointVertex e) (endpointVertex e'))
    (fun e => by exact SimpleGraph.Reachable.refl (G := G) (endpointVertex e))
    hcard endpointAntipode hnot e

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

theorem alternatingPuncturedPrefixChainPartner_gap {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (data : AlternatingPuncturedPrefixChainType label) :
    (alternatingPuncturedPrefixChainPartner hn label data).1.2 = data.1.2 := by
  rw [alternatingPuncturedPrefixChainPartner_val hn label data]
  rcases data with ⟨⟨P, gap⟩, hmem⟩
  by_cases hgap : gap.val < n
  · simp [puncturedPrefixPartnerData, hgap]
  · have hlast : gap = Fin.last n := by
      apply Fin.ext
      have hle : gap.val ≤ n := Nat.le_of_lt_succ gap.isLt
      simp [Fin.last]
      omega
    simp [puncturedPrefixPartnerData, hlast]

theorem alternatingPuncturedPrefixChainPartner_perm_ne {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (data : AlternatingPuncturedPrefixChainType label) :
    (alternatingPuncturedPrefixChainPartner hn label data).1.1 ≠ data.1.1 := by
  intro hperm
  have hgap := alternatingPuncturedPrefixChainPartner_gap hn label data
  have hval : (alternatingPuncturedPrefixChainPartner hn label data).1 = data.1 := by
    exact Prod.ext hperm hgap
  exact alternatingPuncturedPrefixChainPartner_fixedPointFree hn label data
    (Subtype.ext hval)

/-- The two maximal flags containing the punctured flag represented by `data`. -/
noncomputable def kyFanPuncturedIncidentPermSet {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (data : AlternatingPuncturedPrefixChainType label) :
    Finset (SignedPermutation (n + 1)) :=
  {data.1.1, (alternatingPuncturedPrefixChainPartner hn label data).1.1}

theorem mem_kyFanPuncturedIncidentPermSet_iff {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (data : AlternatingPuncturedPrefixChainType label)
    (P : SignedPermutation (n + 1)) :
    P ∈ kyFanPuncturedIncidentPermSet hn label data ↔
      P = data.1.1 ∨
        P = (alternatingPuncturedPrefixChainPartner hn label data).1.1 := by
  simp [kyFanPuncturedIncidentPermSet]

theorem kyFanPuncturedIncidentPermSet_card {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m)
    (data : AlternatingPuncturedPrefixChainType label) :
    (kyFanPuncturedIncidentPermSet hn label data).card = 2 := by
  have hne :
      data.1.1 ≠ (alternatingPuncturedPrefixChainPartner hn label data).1.1 := by
    intro h
    exact alternatingPuncturedPrefixChainPartner_perm_ne hn label data h.symm
  simp [kyFanPuncturedIncidentPermSet, hne]

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

theorem mem_alternatingPuncturedPrefixLabelChains_iff {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {data : SignedPermutation (n + 1) × Fin (n + 1)} :
    data ∈ alternatingPuncturedPrefixLabelChains label ↔
      PositiveAlternatingPuncturedPrefixLabels label data.1 data.2 ∨
        NegativeAlternatingPuncturedPrefixLabels label data.1 data.2 := by
  classical
  simp [alternatingPuncturedPrefixLabelChains,
    positiveAlternatingPuncturedPrefixLabelChains,
    negativeAlternatingPuncturedPrefixLabelChains]

noncomputable def kyFanDeletionGaps {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation (n + 1)) : Finset (Fin (n + 1)) :=
  (prefixChainWordContext hno P).alternatingDeletionGaps

theorem mem_kyFanDeletionGaps_iff {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1)) :
    gap ∈ kyFanDeletionGaps hno P ↔
      (P, gap) ∈ alternatingPuncturedPrefixLabelChains label := by
  rw [kyFanDeletionGaps, AlternatingWordContext.mem_alternatingDeletionGaps_iff,
    prefixChainWordContext_positivePunctured_iff hno P gap,
    prefixChainWordContext_negativePunctured_iff hno P gap,
    mem_alternatingPuncturedPrefixLabelChains_iff]

theorem kyFanDeletionGaps_nonempty_iff {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation (n + 1)) :
    (kyFanDeletionGaps hno P).Nonempty ↔
      ∃ gap : Fin (n + 1), (P, gap) ∈ alternatingPuncturedPrefixLabelChains label := by
  constructor
  · rintro ⟨gap, hgap⟩
    exact ⟨gap, (mem_kyFanDeletionGaps_iff hno P gap).mp hgap⟩
  · rintro ⟨gap, hgap⟩
    exact ⟨gap, (mem_kyFanDeletionGaps_iff hno P gap).mpr hgap⟩

theorem kyFanDeletionGaps_card_eq_two_of_strict {n m : ℕ} (hn : 0 < n)
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    {P : SignedPermutation (n + 1)}
    (hstrict : StrictMono fun i : Fin (n + 1) => (label (P.prefixChain i)).index)
    (hactive : (kyFanDeletionGaps hno P).Nonempty) :
    (kyFanDeletionGaps hno P).card = 2 := by
  exact AlternatingWordContext.alternatingDeletionGaps_card_eq_two
    (C := prefixChainWordContext hno P) hn hstrict hactive

theorem kyFan_flag_punctured_incidence_card_eq_deletionGaps {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation (n + 1)) :
    Fintype.card {gap : Fin (n + 1) //
      (P, gap) ∈ alternatingPuncturedPrefixLabelChains label} =
        (kyFanDeletionGaps hno P).card := by
  classical
  let e :
      {gap : Fin (n + 1) // (P, gap) ∈ alternatingPuncturedPrefixLabelChains label} ≃
        {gap : Fin (n + 1) // gap ∈ kyFanDeletionGaps hno P} :=
    Equiv.subtypeEquivProp (by
      funext gap
      exact propext (mem_kyFanDeletionGaps_iff hno P gap).symm)
  calc
    Fintype.card {gap : Fin (n + 1) //
      (P, gap) ∈ alternatingPuncturedPrefixLabelChains label} =
        Fintype.card {gap : Fin (n + 1) // gap ∈ kyFanDeletionGaps hno P} :=
      Fintype.card_congr e
    _ = (kyFanDeletionGaps hno P).card := by
      exact Fintype.card_of_subtype (kyFanDeletionGaps hno P) (fun _ => Iff.rfl)

theorem kyFan_flag_punctured_incidence_card_eq_two_of_strict {n m : ℕ} (hn : 0 < n)
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    {P : SignedPermutation (n + 1)}
    (hstrict : StrictMono fun i : Fin (n + 1) => (label (P.prefixChain i)).index)
    (hactive : ∃ gap : Fin (n + 1),
      (P, gap) ∈ alternatingPuncturedPrefixLabelChains label) :
    Fintype.card {gap : Fin (n + 1) //
      (P, gap) ∈ alternatingPuncturedPrefixLabelChains label} = 2 := by
  rw [kyFan_flag_punctured_incidence_card_eq_deletionGaps hno P]
  exact kyFanDeletionGaps_card_eq_two_of_strict hn hno hstrict
    ((kyFanDeletionGaps_nonempty_iff hno P).mpr hactive)

/-- The endpoint represented by a concrete alternating deletion gap of `P`. -/
noncomputable def kyFanDeletionGapEndpoint {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation (n + 1)) (gap : Fin (n + 1))
    (hgap : gap ∈ kyFanDeletionGaps hno P) :
    KyFanPathEndpointClass label :=
  Sum.inl
    ⟨(P, gap), (mem_kyFanDeletionGaps_iff hno P gap).mp hgap⟩

theorem kyFanDeletionGapEndpoint_injective {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation (n + 1)) :
    Function.Injective
      (fun gap : {gap : Fin (n + 1) // gap ∈ kyFanDeletionGaps hno P} =>
        kyFanDeletionGapEndpoint hno P gap.1 gap.2) := by
  intro gap gap' h
  apply Subtype.ext
  have hgap := congrArg
    (fun endpoint : KyFanPathEndpointClass label =>
      match endpoint with
      | Sum.inl data => data.1.2
      | Sum.inr _ => (0 : Fin (n + 1))) h
  simpa [kyFanDeletionGapEndpoint] using hgap

/--
The two endpoint vertices cut out by the alternating deletion gaps of a signed
permutation.  This is the flag-side adjacency datum; each element is the
punctured endpoint `(P, gap)` for one alternating deletion gap.
-/
noncomputable def kyFanDeletionGapEndpointSet {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation (n + 1)) :
    Finset (KyFanPathEndpointClass label) :=
  (kyFanDeletionGaps hno P).attach.image fun gap =>
    kyFanDeletionGapEndpoint hno P gap.1 gap.2

theorem mem_kyFanDeletionGapEndpointSet_iff {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation (n + 1)) (endpoint : KyFanPathEndpointClass label) :
    endpoint ∈ kyFanDeletionGapEndpointSet hno P ↔
      ∃ (gap : Fin (n + 1)) (hgap : gap ∈ kyFanDeletionGaps hno P),
        endpoint = kyFanDeletionGapEndpoint hno P gap hgap := by
  classical
  constructor
  · intro hendpoint
    rcases Finset.mem_image.mp hendpoint with ⟨gap, _hgapmem, hgap⟩
    exact ⟨gap.1, gap.2, hgap.symm⟩
  · rintro ⟨gap, hgap, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨gap, hgap⟩, by simp, rfl⟩

theorem kyFanDeletionGapEndpointSet_card {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation (n + 1)) :
    (kyFanDeletionGapEndpointSet hno P).card = (kyFanDeletionGaps hno P).card := by
  classical
  rw [kyFanDeletionGapEndpointSet,
    Finset.card_image_of_injective _ (kyFanDeletionGapEndpoint_injective hno P),
    Finset.card_attach]

theorem kyFanDeletionGapEndpointSet_card_eq_two_of_strict {n m : ℕ} (hn : 0 < n)
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    {P : SignedPermutation (n + 1)}
    (hstrict : StrictMono fun i : Fin (n + 1) => (label (P.prefixChain i)).index)
    (hactive : ∃ gap : Fin (n + 1),
      (P, gap) ∈ alternatingPuncturedPrefixLabelChains label) :
    (kyFanDeletionGapEndpointSet hno P).card = 2 := by
  rw [kyFanDeletionGapEndpointSet_card hno P]
  exact kyFanDeletionGaps_card_eq_two_of_strict hn hno hstrict
    ((kyFanDeletionGaps_nonempty_iff hno P).mpr hactive)

private theorem finset_eq_pair_of_card_eq_two_of_mem {α : Type*} [DecidableEq α]
    {s : Finset α} {a b : α} (hcard : s.card = 2)
    (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b) :
    s = {a, b} := by
  classical
  have hpair_subset : ({a, b} : Finset α) ⊆ s := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hpair_card : ({a, b} : Finset α).card = 2 := by
    simp [hne]
  have hle : s.card ≤ ({a, b} : Finset α).card := by
    rw [hcard, hpair_card]
  exact (Finset.eq_of_subset_of_card_le hpair_subset hle).symm

/--
Flag-side Ky Fan adjacency: two endpoint vertices are adjacent when they are
exactly the two alternating deletion-gap endpoints of one signed permutation.
-/
noncomputable def KyFanDeletionGapGraph {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label) :
    SimpleGraph (KyFanPathEndpointClass label) where
  Adj endpoint endpoint' :=
    endpoint ≠ endpoint' ∧
      ∃ P : SignedPermutation (n + 1),
        kyFanDeletionGapEndpointSet hno P = {endpoint, endpoint'}
  symm := by
    intro endpoint endpoint' h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with ⟨P, hP⟩
    refine ⟨P, ?_⟩
    rw [hP]
    ext x
    simp [or_comm]
  loopless := ⟨fun endpoint h => h.1 rfl⟩

theorem kyFanDeletionGapGraph_adj_iff {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {hno : NoComplementaryComparableLabels label}
    {endpoint endpoint' : KyFanPathEndpointClass label} :
    (KyFanDeletionGapGraph hno).Adj endpoint endpoint' ↔
      endpoint ≠ endpoint' ∧
        ∃ P : SignedPermutation (n + 1),
          kyFanDeletionGapEndpointSet hno P = {endpoint, endpoint'} := by
  rfl

theorem kyFanDeletionGapGraph_adj_of_mem_of_card_eq_two {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {hno : NoComplementaryComparableLabels label}
    {P : SignedPermutation (n + 1)}
    {endpoint endpoint' : KyFanPathEndpointClass label}
    (hcard : (kyFanDeletionGapEndpointSet hno P).card = 2)
    (hendpoint : endpoint ∈ kyFanDeletionGapEndpointSet hno P)
    (hendpoint' : endpoint' ∈ kyFanDeletionGapEndpointSet hno P)
    (hne : endpoint ≠ endpoint') :
    (KyFanDeletionGapGraph hno).Adj endpoint endpoint' := by
  exact
    ⟨hne, P,
      finset_eq_pair_of_card_eq_two_of_mem hcard hendpoint hendpoint' hne⟩

theorem kyFanDeletionGapGraph_adj_of_strict {n m : ℕ} (hn : 0 < n)
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {hno : NoComplementaryComparableLabels label}
    {P : SignedPermutation (n + 1)}
    (hstrict : StrictMono fun i : Fin (n + 1) => (label (P.prefixChain i)).index)
    (hactive : ∃ gap : Fin (n + 1),
      (P, gap) ∈ alternatingPuncturedPrefixLabelChains label)
    {endpoint endpoint' : KyFanPathEndpointClass label}
    (hendpoint : endpoint ∈ kyFanDeletionGapEndpointSet hno P)
    (hendpoint' : endpoint' ∈ kyFanDeletionGapEndpointSet hno P)
    (hne : endpoint ≠ endpoint') :
    (KyFanDeletionGapGraph hno).Adj endpoint endpoint' := by
  exact kyFanDeletionGapGraph_adj_of_mem_of_card_eq_two
    (kyFanDeletionGapEndpointSet_card_eq_two_of_strict hn hno hstrict hactive)
    hendpoint hendpoint' hne

/--
In the Tucker-critical range `m = n`, no signed-permutation prefix word of
length `n + 1` can have strictly increasing label indices.  Thus the current
Layer-A theorem with a full-word `StrictMono` hypothesis cannot be instantiated
there for active punctured flags.
-/
theorem not_strictMono_prefixLabel_indices_critical {n : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel n}
    (P : SignedPermutation (n + 1)) :
    ¬ StrictMono fun i : Fin (n + 1) => (label (P.prefixChain i)).index := by
  intro hstrict
  exact not_strictMono_fin_of_lt (n := n + 1) (m := n) (by omega)
    ⟨fun i => (label (P.prefixChain i)).index, hstrict⟩

/--
Raw flag-incidence predicate for the "same maximal flag" side of the Ky Fan
path graph.  Base endpoints are not flagged by this projection; they need the
separate boundary-incidence data of the full path construction.
-/
def kyFanEndpointCarriesFlag {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (P : SignedPermutation (n + 1)) :
    KyFanPathEndpointClass label → Prop
  | Sum.inl punctured => punctured.1.1 = P
  | Sum.inr (Sum.inl _) => False
  | Sum.inr (Sum.inr (Sum.inl positive)) => positive.1 = P
  | Sum.inr (Sum.inr (Sum.inr negative)) => negative.1 = P

def KyFanPathGraph {n m : ℕ}
    (label : NonzeroSignedSubset (n + 1) → SignedLabel m) :
    SimpleGraph (KyFanPathEndpointClass label) where
  Adj endpoint endpoint' :=
    endpoint ≠ endpoint' ∧
      ∃ P : SignedPermutation (n + 1),
        kyFanEndpointCarriesFlag P endpoint ∧
          kyFanEndpointCarriesFlag P endpoint'
  symm := by
    intro endpoint endpoint' h
    exact ⟨h.1.symm, by
      rcases h.2 with ⟨P, hP, hP'⟩
      exact ⟨P, hP', hP⟩⟩
  loopless := ⟨fun endpoint h => h.1 rfl⟩

theorem kyFanPathGraph_adj_iff {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    {endpoint endpoint' : KyFanPathEndpointClass label} :
    (KyFanPathGraph label).Adj endpoint endpoint' ↔
      endpoint ≠ endpoint' ∧
        ∃ P : SignedPermutation (n + 1),
          kyFanEndpointCarriesFlag P endpoint ∧
            kyFanEndpointCarriesFlag P endpoint' := by
  rfl

theorem kyFanPathGraph_base_not_adj {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (base : Bool) (endpoint : KyFanPathEndpointClass label) :
    ¬ (KyFanPathGraph label).Adj (Sum.inr (Sum.inl base)) endpoint := by
  intro h
  rcases (kyFanPathGraph_adj_iff.mp h).2 with ⟨P, hbase, _hendpoint⟩
  simp [kyFanEndpointCarriesFlag] at hbase

theorem kyFanPathGraph_base_isolated {n m : ℕ}
    {label : NonzeroSignedSubset (n + 1) → SignedLabel m}
    (base : Bool) :
    (KyFanPathGraph label).IsIsolated (Sum.inr (Sum.inl base)) := by
  intro endpoint
  exact kyFanPathGraph_base_not_adj base endpoint

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

/-- The sign-flip involution on the four labels encoded as `Fin 4`. -/
private def fin4Flip (x : Fin 4) : Fin 4 :=
  match x.val with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | _ => 2

/-- Encode the four labels `±0, ±1` as `Fin 4`:
the low bit is sign, the high bit is index. -/
private def signedLabelTwoCode (L : SignedLabel 2) : Fin 4 :=
  ⟨2 * L.index.val + if L.positive then 1 else 0, by
    have hidx : L.index.val < 2 := L.index.isLt
    cases L.positive <;> simp <;> omega⟩

private theorem signedLabelTwoCode_neg (L : SignedLabel 2) :
    signedLabelTwoCode L.neg = fin4Flip (signedLabelTwoCode L) := by
  cases L with
  | mk positive index =>
      cases positive <;> fin_cases index <;> decide

@[simp] private theorem signedLabelTwoCode_neg_mk (L : SignedLabel 2) :
    signedLabelTwoCode { positive := !L.positive, index := L.index } =
      fin4Flip (signedLabelTwoCode L) := by
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

open Lean Elab Tactic in
private structure Fin4Constraint where
  num : Nat
  left : Nat
  right : Nat
  same : Bool

open Lean Elab Tactic in
private def fin4Constraints : List Fin4Constraint :=
  [
    ⟨49, 0, 10, true⟩,
    ⟨50, 0, 7, true⟩,
    ⟨51, 0, 4, true⟩,
    ⟨52, 0, 1, true⟩,
    ⟨54, 0, 3, false⟩,
    ⟨55, 0, 6, false⟩,
    ⟨56, 0, 9, false⟩,
    ⟨57, 0, 12, false⟩,
    ⟨58, 1, 6, true⟩,
    ⟨60, 1, 10, false⟩,
    ⟨61, 2, 6, true⟩,
    ⟨62, 2, 5, true⟩,
    ⟨63, 2, 4, true⟩,
    ⟨64, 2, 1, false⟩,
    ⟨66, 2, 3, false⟩,
    ⟨67, 2, 10, false⟩,
    ⟨68, 2, 11, false⟩,
    ⟨69, 2, 12, false⟩,
    ⟨70, 3, 4, true⟩,
    ⟨72, 3, 12, false⟩,
    ⟨74, 5, 4, false⟩,
    ⟨76, 5, 6, false⟩,
    ⟨78, 7, 4, false⟩,
    ⟨80, 7, 10, false⟩,
    ⟨81, 8, 4, false⟩,
    ⟨82, 8, 5, false⟩,
    ⟨83, 8, 6, false⟩,
    ⟨84, 8, 7, false⟩,
    ⟨86, 8, 9, false⟩,
    ⟨87, 8, 10, false⟩,
    ⟨88, 8, 11, false⟩,
    ⟨89, 8, 12, false⟩,
    ⟨90, 9, 6, false⟩,
    ⟨92, 9, 12, false⟩,
    ⟨94, 11, 10, false⟩,
    ⟨96, 11, 12, false⟩
  ]

open Lean Elab Tactic in
private def fin4FlipNat : Nat → Nat
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | _ => 2

open Lean Elab Tactic in
private def assignmentGet (assignment : Array (Option Nat)) (i : Nat) : Option Nat :=
  match assignment[i]? with
  | some value => value
  | none => none

open Lean Elab Tactic in
private def violatesConstraint (assignment : Array (Option Nat)) (c : Fin4Constraint) : Bool :=
  match assignmentGet assignment c.left, assignmentGet assignment c.right with
  | some x, some y => x == if c.same then y else fin4FlipNat y
  | _, _ => false

open Lean Elab Tactic in
private def findViolation (assignment : Array (Option Nat)) : Option Fin4Constraint :=
  fin4Constraints.find? (violatesConstraint assignment)

open Lean Elab Tactic in
private def validCount (assignment : Array (Option Nat)) (v : Nat) : Nat :=
  ([0, 1, 2, 3].filter fun value =>
    (findViolation (assignment.set! v (some value))).isNone).length

open Lean Elab Tactic in
private def constraintDegree (v : Nat) : Nat :=
  (fin4Constraints.filter fun c => c.left = v ∨ c.right = v).length

open Lean Elab Tactic in
private def assignedTouch (assignment : Array (Option Nat)) (v : Nat) : Nat :=
  (fin4Constraints.filter fun c =>
    (c.left = v ∧ (assignmentGet assignment c.right).isSome) ∨
      (c.right = v ∧ (assignmentGet assignment c.left).isSome)).length

open Lean Elab Tactic in
private def betterVar (assignment : Array (Option Nat)) (v best : Nat) : Bool :=
  let vv := validCount assignment v
  let bv := validCount assignment best
  if vv < bv then true
  else if bv < vv then false
  else
    let vt := assignedTouch assignment v
    let bt := assignedTouch assignment best
    if bt < vt then true
    else if vt < bt then false
    else constraintDegree best < constraintDegree v

open Lean Elab Tactic in
private def chooseVar? (assignment : Array (Option Nat)) : Option Nat :=
  let vars := (List.range 13).filter fun v => (assignmentGet assignment v).isNone
  match vars with
  | [] => none
  | v :: vs => some (vs.foldl (fun best w => if betterVar assignment w best then w else best) v)

open Lean Elab Tactic in
private partial def dpllFin4Tac (assignment : Array (Option Nat)) : TacticM Unit := do
  match findViolation assignment with
  | some c =>
      let hstx := mkIdent (Name.mkSimple s!"h{c.num}")
      if c.same then
        evalTactic (← `(tactic| simp at $hstx:ident))
      else
        evalTactic (← `(tactic| simp [fin4Flip] at $hstx:ident))
      unless (← getUnsolvedGoals).isEmpty do
        throwError "DPLL leaf did not close"
  | none =>
      match chooseVar? assignment with
      | none => throwError "DPLL reached a satisfying assignment"
      | some v =>
          let stx := mkIdent (Name.mkSimple s!"L{v}")
          evalTactic (← `(tactic| fin_cases $stx:term))
          let goals ← getUnsolvedGoals
          let mut remaining : List MVarId := []
          let mut value := 0
          for goal in goals do
            setGoals [goal]
            dpllFin4Tac (assignment.set! v (some value))
            remaining := remaining ++ (← getUnsolvedGoals)
            value := value + 1
          setGoals remaining

elab "dpll_fin4" : tactic => dpllFin4Tac (Array.replicate 13 none)

/-- The finite unsatisfiable core for the three-dimensional Tucker step. -/
private theorem tuckerLemmaStatement_three_core_unsat
    (L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 : Fin 4) :
    ¬ (
      L0 ≠ L10 ∧
      L0 ≠ L7 ∧
      L0 ≠ L4 ∧
      L0 ≠ L1 ∧
      L0 ≠ fin4Flip L3 ∧
      L0 ≠ fin4Flip L6 ∧
      L0 ≠ fin4Flip L9 ∧
      L0 ≠ fin4Flip L12 ∧
      L1 ≠ L6 ∧
      L1 ≠ fin4Flip L10 ∧
      L2 ≠ L6 ∧
      L2 ≠ L5 ∧
      L2 ≠ L4 ∧
      L2 ≠ fin4Flip L1 ∧
      L2 ≠ fin4Flip L3 ∧
      L2 ≠ fin4Flip L10 ∧
      L2 ≠ fin4Flip L11 ∧
      L2 ≠ fin4Flip L12 ∧
      L3 ≠ L4 ∧
      L3 ≠ fin4Flip L12 ∧
      L5 ≠ fin4Flip L4 ∧
      L5 ≠ fin4Flip L6 ∧
      L7 ≠ fin4Flip L4 ∧
      L7 ≠ fin4Flip L10 ∧
      L8 ≠ fin4Flip L4 ∧
      L8 ≠ fin4Flip L5 ∧
      L8 ≠ fin4Flip L6 ∧
      L8 ≠ fin4Flip L7 ∧
      L8 ≠ fin4Flip L9 ∧
      L8 ≠ fin4Flip L10 ∧
      L8 ≠ fin4Flip L11 ∧
      L8 ≠ fin4Flip L12 ∧
      L9 ≠ fin4Flip L6 ∧
      L9 ≠ fin4Flip L12 ∧
      L11 ≠ fin4Flip L10 ∧
      L11 ≠ fin4Flip L12) := by
  intro h
  rcases h with ⟨h49, h50, h51, h52, h54, h55, h56, h57, h58, h60, h61, h62,
    h63, h64, h66, h67, h68, h69, h70, h72, h74, h76, h78, h80, h81, h82,
    h83, h84, h86, h87, h88, h89, h90, h92, h94, h96⟩
  dpll_fin4

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
  let B0 : Fin 4 := signedLabelTwoCode (label R0)
  let B1 : Fin 4 := signedLabelTwoCode (label R1)
  let B2 : Fin 4 := signedLabelTwoCode (label R2)
  let B3 : Fin 4 := signedLabelTwoCode (label R3)
  let B4 : Fin 4 := signedLabelTwoCode (label R4)
  let B5 : Fin 4 := signedLabelTwoCode (label R5)
  let B6 : Fin 4 := signedLabelTwoCode (label R6)
  let B7 : Fin 4 := signedLabelTwoCode (label R7)
  let B8 : Fin 4 := signedLabelTwoCode (label R8)
  let B9 : Fin 4 := signedLabelTwoCode (label R9)
  let B10 : Fin 4 := signedLabelTwoCode (label R10)
  let B11 : Fin 4 := signedLabelTwoCode (label R11)
  let B12 : Fin 4 := signedLabelTwoCode (label R12)
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
  have h54 : B0 ≠ fin4Flip B3 := by
    have h := signedLabelTwoCode_noComplement hno (X := R0) (Y := R3) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R3,
        z, o, t])
    simpa [B0, B3, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h55 : B0 ≠ fin4Flip B6 := by
    have h := signedLabelTwoCode_noComplement hno (X := R0) (Y := R6) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R6,
        z, o, t])
    simpa [B0, B6, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h56 : B0 ≠ fin4Flip B9 := by
    have h := signedLabelTwoCode_noComplement hno (X := R0) (Y := R9) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R9,
        z, o, t])
    simpa [B0, B9, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h57 : B0 ≠ fin4Flip B12 := by
    have h := signedLabelTwoCode_noComplement hno (X := R0) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R12,
        z, o, t])
    simpa [B0, B12, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h58 : B1 ≠ B6 := by
    have h := signedLabelTwoCode_noComplement hno (X := R1) (Y := R6.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R1, R6,
        z, o, t])
    simpa [B1, B6, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h60 : B1 ≠ fin4Flip B10 := by
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
  have h64 : B2 ≠ fin4Flip B1 := by
    have h := signedLabelTwoCode_noComplement hno (X := R2) (Y := R1) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R1,
        z, o, t])
    simpa [B2, B1, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h66 : B2 ≠ fin4Flip B3 := by
    have h := signedLabelTwoCode_noComplement hno (X := R2) (Y := R3) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R3,
        z, o, t])
    simpa [B2, B3, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h67 : B2 ≠ fin4Flip B10 := by
    have h := signedLabelTwoCode_noComplement hno (X := R2) (Y := R10) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R10,
        z, o, t])
    simpa [B2, B10, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h68 : B2 ≠ fin4Flip B11 := by
    have h := signedLabelTwoCode_noComplement hno (X := R2) (Y := R11) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R11,
        z, o, t])
    simpa [B2, B11, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h69 : B2 ≠ fin4Flip B12 := by
    have h := signedLabelTwoCode_noComplement hno (X := R2) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R12,
        z, o, t])
    simpa [B2, B12, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h70 : B3 ≠ B4 := by
    have h := signedLabelTwoCode_noComplement hno (X := R3) (Y := R4.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R3, R4,
        z, o, t])
    simpa [B3, B4, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h72 : B3 ≠ fin4Flip B12 := by
    have h := signedLabelTwoCode_noComplement hno (X := R3) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R3, R12,
        z, o, t])
    simpa [B3, B12, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h74 : B5 ≠ fin4Flip B4 := by
    have h := signedLabelTwoCode_noComplement hno (X := R5) (Y := R4) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R5, R4,
        z, o, t])
    simpa [B5, B4, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h76 : B5 ≠ fin4Flip B6 := by
    have h := signedLabelTwoCode_noComplement hno (X := R5) (Y := R6) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R5, R6,
        z, o, t])
    simpa [B5, B6, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h78 : B7 ≠ fin4Flip B4 := by
    have h := signedLabelTwoCode_noComplement hno (X := R7) (Y := R4) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R7, R4,
        z, o, t])
    simpa [B7, B4, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h80 : B7 ≠ fin4Flip B10 := by
    have h := signedLabelTwoCode_noComplement hno (X := R7) (Y := R10) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R7, R10,
        z, o, t])
    simpa [B7, B10, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h81 : B8 ≠ fin4Flip B4 := by
    have h := signedLabelTwoCode_noComplement hno (X := R8) (Y := R4) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R4,
        z, o, t])
    simpa [B8, B4, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h82 : B8 ≠ fin4Flip B5 := by
    have h := signedLabelTwoCode_noComplement hno (X := R8) (Y := R5) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R5,
        z, o, t])
    simpa [B8, B5, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h83 : B8 ≠ fin4Flip B6 := by
    have h := signedLabelTwoCode_noComplement hno (X := R8) (Y := R6) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R6,
        z, o, t])
    simpa [B8, B6, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h84 : B8 ≠ fin4Flip B7 := by
    have h := signedLabelTwoCode_noComplement hno (X := R8) (Y := R7) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R7,
        z, o, t])
    simpa [B8, B7, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h86 : B8 ≠ fin4Flip B9 := by
    have h := signedLabelTwoCode_noComplement hno (X := R8) (Y := R9) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R9,
        z, o, t])
    simpa [B8, B9, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h87 : B8 ≠ fin4Flip B10 := by
    have h := signedLabelTwoCode_noComplement hno (X := R8) (Y := R10) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R10,
        z, o, t])
    simpa [B8, B10, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h88 : B8 ≠ fin4Flip B11 := by
    have h := signedLabelTwoCode_noComplement hno (X := R8) (Y := R11) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R11,
        z, o, t])
    simpa [B8, B11, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h89 : B8 ≠ fin4Flip B12 := by
    have h := signedLabelTwoCode_noComplement hno (X := R8) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R12,
        z, o, t])
    simpa [B8, B12, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h90 : B9 ≠ fin4Flip B6 := by
    have h := signedLabelTwoCode_noComplement hno (X := R9) (Y := R6) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R9, R6,
        z, o, t])
    simpa [B9, B6, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h92 : B9 ≠ fin4Flip B12 := by
    have h := signedLabelTwoCode_noComplement hno (X := R9) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R9, R12,
        z, o, t])
    simpa [B9, B12, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h94 : B11 ≠ fin4Flip B10 := by
    have h := signedLabelTwoCode_noComplement hno (X := R11) (Y := R10) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R11, R10,
        z, o, t])
    simpa [B11, B10, signedLabelTwoCode_neg, SignedLabel.neg, hantipodal] using h
  have h96 : B11 ≠ fin4Flip B12 := by
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

/-! ### Four-dimensional finite Tucker step -/

/-- Encode the six labels `±0, ±1, ±2` as three-bit words.
The low bit is sign and the remaining bits are the index. -/
private def signedLabelThreeCode (L : SignedLabel 3) : BitVec 3 :=
  BitVec.ofNat 3 (2 * L.index.val + if L.positive then 1 else 0)

private theorem signedLabelThreeCode_lt (L : SignedLabel 3) :
    signedLabelThreeCode L < (6#3) := by
  cases L with
  | mk positive index =>
      cases positive <;> fin_cases index <;> native_decide

private theorem signedLabelThreeCode_neg (L : SignedLabel 3) :
    signedLabelThreeCode L.neg = signedLabelThreeCode L ^^^ (1#3) := by
  cases L with
  | mk positive index =>
      cases positive <;> fin_cases index <;> native_decide

@[simp] private theorem signedLabelThreeCode_neg_mk (L : SignedLabel 3) :
    signedLabelThreeCode { positive := !L.positive, index := L.index } =
      signedLabelThreeCode L ^^^ (1#3) := by
  simpa [SignedLabel.neg] using signedLabelThreeCode_neg L

private theorem signedLabelThreeCode_injective : Function.Injective signedLabelThreeCode := by
  intro L M h
  cases L with
  | mk lp li =>
      cases M with
      | mk mp mi =>
          cases lp <;> cases mp <;> fin_cases li <;> fin_cases mi <;>
            simp [signedLabelThreeCode] at h ⊢

private theorem signedLabelThreeCode_noComplement
    {label : NonzeroSignedSubset 4 → SignedLabel 3}
    (hno : NoComplementaryComparableLabels label)
    {X Y : NonzeroSignedSubset 4} (hXY : SignedSubset.Le X.1 Y.1) :
    signedLabelThreeCode (label X) ≠ signedLabelThreeCode (label Y).neg := by
  intro hcode
  exact hno X Y hXY (signedLabelThreeCode_injective hcode)

set_option maxHeartbeats 0 in
set_option maxRecDepth 2000 in
set_option linter.unusedVariables false in
/-- The finite unsatisfiable core for the four-dimensional Tucker step. -/
private theorem tuckerLemmaStatement_four_core_unsat
    (L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 L16 L17 L18 L19 L20 L21 L22 L23 L24 L25 L26 L27 L28 L29 L30 L31 L32 L33 L34 L35 L36 L37 L38 L39 : BitVec 3)
    (hdom0 : L0 < (6#3))
    (hdom1 : L1 < (6#3))
    (hdom2 : L2 < (6#3))
    (hdom3 : L3 < (6#3))
    (hdom4 : L4 < (6#3))
    (hdom5 : L5 < (6#3))
    (hdom6 : L6 < (6#3))
    (hdom7 : L7 < (6#3))
    (hdom8 : L8 < (6#3))
    (hdom9 : L9 < (6#3))
    (hdom10 : L10 < (6#3))
    (hdom11 : L11 < (6#3))
    (hdom12 : L12 < (6#3))
    (hdom13 : L13 < (6#3))
    (hdom14 : L14 < (6#3))
    (hdom15 : L15 < (6#3))
    (hdom16 : L16 < (6#3))
    (hdom17 : L17 < (6#3))
    (hdom18 : L18 < (6#3))
    (hdom19 : L19 < (6#3))
    (hdom20 : L20 < (6#3))
    (hdom21 : L21 < (6#3))
    (hdom22 : L22 < (6#3))
    (hdom23 : L23 < (6#3))
    (hdom24 : L24 < (6#3))
    (hdom25 : L25 < (6#3))
    (hdom26 : L26 < (6#3))
    (hdom27 : L27 < (6#3))
    (hdom28 : L28 < (6#3))
    (hdom29 : L29 < (6#3))
    (hdom30 : L30 < (6#3))
    (hdom31 : L31 < (6#3))
    (hdom32 : L32 < (6#3))
    (hdom33 : L33 < (6#3))
    (hdom34 : L34 < (6#3))
    (hdom35 : L35 < (6#3))
    (hdom36 : L36 < (6#3))
    (hdom37 : L37 < (6#3))
    (hdom38 : L38 < (6#3))
    (hdom39 : L39 < (6#3))
    (h0 : L0 ≠ L1)
    (h1 : L0 ≠ (L3 ^^^ (1#3)))
    (h2 : L0 ≠ L4)
    (h3 : L0 ≠ (L6 ^^^ (1#3)))
    (h4 : L0 ≠ L7)
    (h5 : L0 ≠ (L9 ^^^ (1#3)))
    (h6 : L0 ≠ L10)
    (h7 : L0 ≠ (L12 ^^^ (1#3)))
    (h8 : L0 ≠ L13)
    (h9 : L0 ≠ (L15 ^^^ (1#3)))
    (h10 : L0 ≠ L16)
    (h11 : L0 ≠ (L18 ^^^ (1#3)))
    (h12 : L0 ≠ L19)
    (h13 : L0 ≠ (L21 ^^^ (1#3)))
    (h14 : L0 ≠ L22)
    (h15 : L0 ≠ (L24 ^^^ (1#3)))
    (h16 : L0 ≠ L25)
    (h17 : L0 ≠ (L27 ^^^ (1#3)))
    (h18 : L0 ≠ L28)
    (h19 : L0 ≠ (L30 ^^^ (1#3)))
    (h20 : L0 ≠ L31)
    (h21 : L0 ≠ (L33 ^^^ (1#3)))
    (h22 : L0 ≠ L34)
    (h23 : L0 ≠ (L36 ^^^ (1#3)))
    (h24 : L0 ≠ L37)
    (h25 : L0 ≠ (L39 ^^^ (1#3)))
    (h26 : L2 ≠ (L1 ^^^ (1#3)))
    (h27 : L1 ≠ L6)
    (h28 : L1 ≠ (L10 ^^^ (1#3)))
    (h29 : L1 ≠ L15)
    (h30 : L1 ≠ (L19 ^^^ (1#3)))
    (h31 : L1 ≠ L24)
    (h32 : L1 ≠ (L28 ^^^ (1#3)))
    (h33 : L1 ≠ L33)
    (h34 : L1 ≠ (L37 ^^^ (1#3)))
    (h35 : L2 ≠ (L3 ^^^ (1#3)))
    (h36 : L2 ≠ L4)
    (h37 : L2 ≠ L5)
    (h38 : L2 ≠ L6)
    (h39 : L2 ≠ (L10 ^^^ (1#3)))
    (h40 : L2 ≠ (L11 ^^^ (1#3)))
    (h41 : L2 ≠ (L12 ^^^ (1#3)))
    (h42 : L2 ≠ L13)
    (h43 : L2 ≠ L14)
    (h44 : L2 ≠ L15)
    (h45 : L2 ≠ (L19 ^^^ (1#3)))
    (h46 : L2 ≠ (L20 ^^^ (1#3)))
    (h47 : L2 ≠ (L21 ^^^ (1#3)))
    (h48 : L2 ≠ L22)
    (h49 : L2 ≠ L23)
    (h50 : L2 ≠ L24)
    (h51 : L2 ≠ (L28 ^^^ (1#3)))
    (h52 : L2 ≠ (L29 ^^^ (1#3)))
    (h53 : L2 ≠ (L30 ^^^ (1#3)))
    (h54 : L2 ≠ L31)
    (h55 : L2 ≠ L32)
    (h56 : L2 ≠ L33)
    (h57 : L2 ≠ (L37 ^^^ (1#3)))
    (h58 : L2 ≠ (L38 ^^^ (1#3)))
    (h59 : L2 ≠ (L39 ^^^ (1#3)))
    (h60 : L3 ≠ L4)
    (h61 : L3 ≠ (L12 ^^^ (1#3)))
    (h62 : L3 ≠ L13)
    (h63 : L3 ≠ (L21 ^^^ (1#3)))
    (h64 : L3 ≠ L22)
    (h65 : L3 ≠ (L30 ^^^ (1#3)))
    (h66 : L3 ≠ L31)
    (h67 : L3 ≠ (L39 ^^^ (1#3)))
    (h68 : L5 ≠ (L4 ^^^ (1#3)))
    (h69 : L7 ≠ (L4 ^^^ (1#3)))
    (h70 : L8 ≠ (L4 ^^^ (1#3)))
    (h71 : L4 ≠ L21)
    (h72 : L4 ≠ (L31 ^^^ (1#3)))
    (h73 : L5 ≠ (L6 ^^^ (1#3)))
    (h74 : L8 ≠ (L5 ^^^ (1#3)))
    (h75 : L5 ≠ L19)
    (h76 : L5 ≠ L20)
    (h77 : L5 ≠ L21)
    (h78 : L5 ≠ (L31 ^^^ (1#3)))
    (h79 : L5 ≠ (L32 ^^^ (1#3)))
    (h80 : L5 ≠ (L33 ^^^ (1#3)))
    (h81 : L8 ≠ (L6 ^^^ (1#3)))
    (h82 : L9 ≠ (L6 ^^^ (1#3)))
    (h83 : L6 ≠ L19)
    (h84 : L6 ≠ (L33 ^^^ (1#3)))
    (h85 : L8 ≠ (L7 ^^^ (1#3)))
    (h86 : L7 ≠ (L10 ^^^ (1#3)))
    (h87 : L7 ≠ L15)
    (h88 : L7 ≠ L18)
    (h89 : L7 ≠ L21)
    (h90 : L7 ≠ (L31 ^^^ (1#3)))
    (h91 : L7 ≠ (L34 ^^^ (1#3)))
    (h92 : L7 ≠ (L37 ^^^ (1#3)))
    (h93 : L8 ≠ (L9 ^^^ (1#3)))
    (h94 : L8 ≠ (L10 ^^^ (1#3)))
    (h95 : L8 ≠ (L11 ^^^ (1#3)))
    (h96 : L8 ≠ (L12 ^^^ (1#3)))
    (h97 : L8 ≠ L13)
    (h98 : L8 ≠ L14)
    (h99 : L8 ≠ L15)
    (h100 : L8 ≠ L16)
    (h101 : L8 ≠ L17)
    (h102 : L8 ≠ L18)
    (h103 : L8 ≠ L19)
    (h104 : L8 ≠ L20)
    (h105 : L8 ≠ L21)
    (h106 : L8 ≠ (L31 ^^^ (1#3)))
    (h107 : L8 ≠ (L32 ^^^ (1#3)))
    (h108 : L8 ≠ (L33 ^^^ (1#3)))
    (h109 : L8 ≠ (L34 ^^^ (1#3)))
    (h110 : L8 ≠ (L35 ^^^ (1#3)))
    (h111 : L8 ≠ (L36 ^^^ (1#3)))
    (h112 : L8 ≠ (L37 ^^^ (1#3)))
    (h113 : L8 ≠ (L38 ^^^ (1#3)))
    (h114 : L8 ≠ (L39 ^^^ (1#3)))
    (h115 : L9 ≠ (L12 ^^^ (1#3)))
    (h116 : L9 ≠ L13)
    (h117 : L9 ≠ L16)
    (h118 : L9 ≠ L19)
    (h119 : L9 ≠ (L33 ^^^ (1#3)))
    (h120 : L9 ≠ (L36 ^^^ (1#3)))
    (h121 : L9 ≠ (L39 ^^^ (1#3)))
    (h122 : L11 ≠ (L10 ^^^ (1#3)))
    (h123 : L10 ≠ L15)
    (h124 : L10 ≠ (L37 ^^^ (1#3)))
    (h125 : L11 ≠ (L12 ^^^ (1#3)))
    (h126 : L11 ≠ L13)
    (h127 : L11 ≠ L14)
    (h128 : L11 ≠ L15)
    (h129 : L11 ≠ (L37 ^^^ (1#3)))
    (h130 : L11 ≠ (L38 ^^^ (1#3)))
    (h131 : L11 ≠ (L39 ^^^ (1#3)))
    (h132 : L12 ≠ L13)
    (h133 : L12 ≠ (L39 ^^^ (1#3)))
    (h134 : L14 ≠ (L13 ^^^ (1#3)))
    (h135 : L16 ≠ (L13 ^^^ (1#3)))
    (h136 : L17 ≠ (L13 ^^^ (1#3)))
    (h137 : L22 ≠ (L13 ^^^ (1#3)))
    (h138 : L23 ≠ (L13 ^^^ (1#3)))
    (h139 : L25 ≠ (L13 ^^^ (1#3)))
    (h140 : L26 ≠ (L13 ^^^ (1#3)))
    (h141 : L14 ≠ (L15 ^^^ (1#3)))
    (h142 : L17 ≠ (L14 ^^^ (1#3)))
    (h143 : L23 ≠ (L14 ^^^ (1#3)))
    (h144 : L26 ≠ (L14 ^^^ (1#3)))
    (h145 : L17 ≠ (L15 ^^^ (1#3)))
    (h146 : L18 ≠ (L15 ^^^ (1#3)))
    (h147 : L23 ≠ (L15 ^^^ (1#3)))
    (h148 : L24 ≠ (L15 ^^^ (1#3)))
    (h149 : L26 ≠ (L15 ^^^ (1#3)))
    (h150 : L27 ≠ (L15 ^^^ (1#3)))
    (h151 : L17 ≠ (L16 ^^^ (1#3)))
    (h152 : L16 ≠ (L19 ^^^ (1#3)))
    (h153 : L25 ≠ (L16 ^^^ (1#3)))
    (h154 : L26 ≠ (L16 ^^^ (1#3)))
    (h155 : L17 ≠ (L18 ^^^ (1#3)))
    (h156 : L17 ≠ (L19 ^^^ (1#3)))
    (h157 : L17 ≠ (L20 ^^^ (1#3)))
    (h158 : L17 ≠ (L21 ^^^ (1#3)))
    (h159 : L26 ≠ (L17 ^^^ (1#3)))
    (h160 : L18 ≠ (L21 ^^^ (1#3)))
    (h161 : L26 ≠ (L18 ^^^ (1#3)))
    (h162 : L27 ≠ (L18 ^^^ (1#3)))
    (h163 : L20 ≠ (L19 ^^^ (1#3)))
    (h164 : L25 ≠ (L19 ^^^ (1#3)))
    (h165 : L26 ≠ (L19 ^^^ (1#3)))
    (h166 : L28 ≠ (L19 ^^^ (1#3)))
    (h167 : L29 ≠ (L19 ^^^ (1#3)))
    (h168 : L20 ≠ (L21 ^^^ (1#3)))
    (h169 : L26 ≠ (L20 ^^^ (1#3)))
    (h170 : L29 ≠ (L20 ^^^ (1#3)))
    (h171 : L26 ≠ (L21 ^^^ (1#3)))
    (h172 : L27 ≠ (L21 ^^^ (1#3)))
    (h173 : L29 ≠ (L21 ^^^ (1#3)))
    (h174 : L30 ≠ (L21 ^^^ (1#3)))
    (h175 : L23 ≠ (L22 ^^^ (1#3)))
    (h176 : L25 ≠ (L22 ^^^ (1#3)))
    (h177 : L26 ≠ (L22 ^^^ (1#3)))
    (h178 : L22 ≠ (L31 ^^^ (1#3)))
    (h179 : L23 ≠ (L24 ^^^ (1#3)))
    (h180 : L26 ≠ (L23 ^^^ (1#3)))
    (h181 : L23 ≠ (L31 ^^^ (1#3)))
    (h182 : L23 ≠ (L32 ^^^ (1#3)))
    (h183 : L23 ≠ (L33 ^^^ (1#3)))
    (h184 : L26 ≠ (L24 ^^^ (1#3)))
    (h185 : L27 ≠ (L24 ^^^ (1#3)))
    (h186 : L24 ≠ (L33 ^^^ (1#3)))
    (h187 : L26 ≠ (L25 ^^^ (1#3)))
    (h188 : L25 ≠ (L28 ^^^ (1#3)))
    (h189 : L25 ≠ (L31 ^^^ (1#3)))
    (h190 : L25 ≠ (L34 ^^^ (1#3)))
    (h191 : L25 ≠ (L37 ^^^ (1#3)))
    (h192 : L26 ≠ (L27 ^^^ (1#3)))
    (h193 : L26 ≠ (L28 ^^^ (1#3)))
    (h194 : L26 ≠ (L29 ^^^ (1#3)))
    (h195 : L26 ≠ (L30 ^^^ (1#3)))
    (h196 : L26 ≠ (L31 ^^^ (1#3)))
    (h197 : L26 ≠ (L32 ^^^ (1#3)))
    (h198 : L26 ≠ (L33 ^^^ (1#3)))
    (h199 : L26 ≠ (L34 ^^^ (1#3)))
    (h200 : L26 ≠ (L35 ^^^ (1#3)))
    (h201 : L26 ≠ (L36 ^^^ (1#3)))
    (h202 : L26 ≠ (L37 ^^^ (1#3)))
    (h203 : L26 ≠ (L38 ^^^ (1#3)))
    (h204 : L26 ≠ (L39 ^^^ (1#3)))
    (h205 : L27 ≠ (L30 ^^^ (1#3)))
    (h206 : L27 ≠ (L33 ^^^ (1#3)))
    (h207 : L27 ≠ (L36 ^^^ (1#3)))
    (h208 : L27 ≠ (L39 ^^^ (1#3)))
    (h209 : L29 ≠ (L28 ^^^ (1#3)))
    (h210 : L28 ≠ (L37 ^^^ (1#3)))
    (h211 : L29 ≠ (L30 ^^^ (1#3)))
    (h212 : L29 ≠ (L37 ^^^ (1#3)))
    (h213 : L29 ≠ (L38 ^^^ (1#3)))
    (h214 : L29 ≠ (L39 ^^^ (1#3)))
    (h215 : L30 ≠ (L39 ^^^ (1#3)))
    (h216 : L32 ≠ (L31 ^^^ (1#3)))
    (h217 : L34 ≠ (L31 ^^^ (1#3)))
    (h218 : L35 ≠ (L31 ^^^ (1#3)))
    (h219 : L32 ≠ (L33 ^^^ (1#3)))
    (h220 : L35 ≠ (L32 ^^^ (1#3)))
    (h221 : L35 ≠ (L33 ^^^ (1#3)))
    (h222 : L36 ≠ (L33 ^^^ (1#3)))
    (h223 : L35 ≠ (L34 ^^^ (1#3)))
    (h224 : L34 ≠ (L37 ^^^ (1#3)))
    (h225 : L35 ≠ (L36 ^^^ (1#3)))
    (h226 : L35 ≠ (L37 ^^^ (1#3)))
    (h227 : L35 ≠ (L38 ^^^ (1#3)))
    (h228 : L35 ≠ (L39 ^^^ (1#3)))
    (h229 : L36 ≠ (L39 ^^^ (1#3)))
    (h230 : L38 ≠ (L37 ^^^ (1#3)))
    (h231 : L38 ≠ (L39 ^^^ (1#3)))
    : False := by
  bv_decide

set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
private theorem not_noComplementaryComparableLabels_four
    (label : NonzeroSignedSubset 4 → SignedLabel 3)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (hno : NoComplementaryComparableLabels label) : False := by
  classical
  let a : Fin 4 := ⟨0, by omega⟩
  let b : Fin 4 := ⟨1, by omega⟩
  let c : Fin 4 := ⟨2, by omega⟩
  let d : Fin 4 := ⟨3, by omega⟩
  let R0 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {d}, neg := ∅, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R1 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {c}, neg := {d}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R2 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {c}, neg := ∅, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R3 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {c, d}, neg := ∅, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R4 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {b}, neg := {c, d}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R5 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {b}, neg := {c}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R6 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {b, d}, neg := {c}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R7 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {b}, neg := {d}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R8 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {b}, neg := ∅, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R9 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {b, d}, neg := ∅, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R10 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {b, c}, neg := {d}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R11 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {b, c}, neg := ∅, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R12 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {b, c, d}, neg := ∅, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R13 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a}, neg := {b, c, d}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R14 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a}, neg := {b, c}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R15 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, d}, neg := {b, c}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R16 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a}, neg := {b, d}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R17 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a}, neg := {b}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R18 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, d}, neg := {b}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R19 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, c}, neg := {b, d}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R20 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, c}, neg := {b}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R21 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, c, d}, neg := {b}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R22 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a}, neg := {c, d}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R23 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a}, neg := {c}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R24 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, d}, neg := {c}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R25 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a}, neg := {d}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R26 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a}, neg := ∅, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R27 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, d}, neg := ∅, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R28 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, c}, neg := {d}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R29 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, c}, neg := ∅, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R30 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, c, d}, neg := ∅, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R31 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, b}, neg := {c, d}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R32 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, b}, neg := {c}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R33 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, b, d}, neg := {c}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R34 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, b}, neg := {d}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R35 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, b}, neg := ∅, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R36 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, b, d}, neg := ∅, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R37 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, b, c}, neg := {d}, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R38 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, b, c}, neg := ∅, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let R39 : NonzeroSignedSubset 4 :=
    ⟨{ pos := {a, b, c, d}, neg := ∅, disjoint := by decide },
      by simp [SignedSubset.Nonzero]⟩
  let B0 : BitVec 3 := signedLabelThreeCode (label R0)
  let B1 : BitVec 3 := signedLabelThreeCode (label R1)
  let B2 : BitVec 3 := signedLabelThreeCode (label R2)
  let B3 : BitVec 3 := signedLabelThreeCode (label R3)
  let B4 : BitVec 3 := signedLabelThreeCode (label R4)
  let B5 : BitVec 3 := signedLabelThreeCode (label R5)
  let B6 : BitVec 3 := signedLabelThreeCode (label R6)
  let B7 : BitVec 3 := signedLabelThreeCode (label R7)
  let B8 : BitVec 3 := signedLabelThreeCode (label R8)
  let B9 : BitVec 3 := signedLabelThreeCode (label R9)
  let B10 : BitVec 3 := signedLabelThreeCode (label R10)
  let B11 : BitVec 3 := signedLabelThreeCode (label R11)
  let B12 : BitVec 3 := signedLabelThreeCode (label R12)
  let B13 : BitVec 3 := signedLabelThreeCode (label R13)
  let B14 : BitVec 3 := signedLabelThreeCode (label R14)
  let B15 : BitVec 3 := signedLabelThreeCode (label R15)
  let B16 : BitVec 3 := signedLabelThreeCode (label R16)
  let B17 : BitVec 3 := signedLabelThreeCode (label R17)
  let B18 : BitVec 3 := signedLabelThreeCode (label R18)
  let B19 : BitVec 3 := signedLabelThreeCode (label R19)
  let B20 : BitVec 3 := signedLabelThreeCode (label R20)
  let B21 : BitVec 3 := signedLabelThreeCode (label R21)
  let B22 : BitVec 3 := signedLabelThreeCode (label R22)
  let B23 : BitVec 3 := signedLabelThreeCode (label R23)
  let B24 : BitVec 3 := signedLabelThreeCode (label R24)
  let B25 : BitVec 3 := signedLabelThreeCode (label R25)
  let B26 : BitVec 3 := signedLabelThreeCode (label R26)
  let B27 : BitVec 3 := signedLabelThreeCode (label R27)
  let B28 : BitVec 3 := signedLabelThreeCode (label R28)
  let B29 : BitVec 3 := signedLabelThreeCode (label R29)
  let B30 : BitVec 3 := signedLabelThreeCode (label R30)
  let B31 : BitVec 3 := signedLabelThreeCode (label R31)
  let B32 : BitVec 3 := signedLabelThreeCode (label R32)
  let B33 : BitVec 3 := signedLabelThreeCode (label R33)
  let B34 : BitVec 3 := signedLabelThreeCode (label R34)
  let B35 : BitVec 3 := signedLabelThreeCode (label R35)
  let B36 : BitVec 3 := signedLabelThreeCode (label R36)
  let B37 : BitVec 3 := signedLabelThreeCode (label R37)
  let B38 : BitVec 3 := signedLabelThreeCode (label R38)
  let B39 : BitVec 3 := signedLabelThreeCode (label R39)
  have hdom0 : B0 < (6#3) := by
    simpa [B0] using signedLabelThreeCode_lt (label R0)
  have hdom1 : B1 < (6#3) := by
    simpa [B1] using signedLabelThreeCode_lt (label R1)
  have hdom2 : B2 < (6#3) := by
    simpa [B2] using signedLabelThreeCode_lt (label R2)
  have hdom3 : B3 < (6#3) := by
    simpa [B3] using signedLabelThreeCode_lt (label R3)
  have hdom4 : B4 < (6#3) := by
    simpa [B4] using signedLabelThreeCode_lt (label R4)
  have hdom5 : B5 < (6#3) := by
    simpa [B5] using signedLabelThreeCode_lt (label R5)
  have hdom6 : B6 < (6#3) := by
    simpa [B6] using signedLabelThreeCode_lt (label R6)
  have hdom7 : B7 < (6#3) := by
    simpa [B7] using signedLabelThreeCode_lt (label R7)
  have hdom8 : B8 < (6#3) := by
    simpa [B8] using signedLabelThreeCode_lt (label R8)
  have hdom9 : B9 < (6#3) := by
    simpa [B9] using signedLabelThreeCode_lt (label R9)
  have hdom10 : B10 < (6#3) := by
    simpa [B10] using signedLabelThreeCode_lt (label R10)
  have hdom11 : B11 < (6#3) := by
    simpa [B11] using signedLabelThreeCode_lt (label R11)
  have hdom12 : B12 < (6#3) := by
    simpa [B12] using signedLabelThreeCode_lt (label R12)
  have hdom13 : B13 < (6#3) := by
    simpa [B13] using signedLabelThreeCode_lt (label R13)
  have hdom14 : B14 < (6#3) := by
    simpa [B14] using signedLabelThreeCode_lt (label R14)
  have hdom15 : B15 < (6#3) := by
    simpa [B15] using signedLabelThreeCode_lt (label R15)
  have hdom16 : B16 < (6#3) := by
    simpa [B16] using signedLabelThreeCode_lt (label R16)
  have hdom17 : B17 < (6#3) := by
    simpa [B17] using signedLabelThreeCode_lt (label R17)
  have hdom18 : B18 < (6#3) := by
    simpa [B18] using signedLabelThreeCode_lt (label R18)
  have hdom19 : B19 < (6#3) := by
    simpa [B19] using signedLabelThreeCode_lt (label R19)
  have hdom20 : B20 < (6#3) := by
    simpa [B20] using signedLabelThreeCode_lt (label R20)
  have hdom21 : B21 < (6#3) := by
    simpa [B21] using signedLabelThreeCode_lt (label R21)
  have hdom22 : B22 < (6#3) := by
    simpa [B22] using signedLabelThreeCode_lt (label R22)
  have hdom23 : B23 < (6#3) := by
    simpa [B23] using signedLabelThreeCode_lt (label R23)
  have hdom24 : B24 < (6#3) := by
    simpa [B24] using signedLabelThreeCode_lt (label R24)
  have hdom25 : B25 < (6#3) := by
    simpa [B25] using signedLabelThreeCode_lt (label R25)
  have hdom26 : B26 < (6#3) := by
    simpa [B26] using signedLabelThreeCode_lt (label R26)
  have hdom27 : B27 < (6#3) := by
    simpa [B27] using signedLabelThreeCode_lt (label R27)
  have hdom28 : B28 < (6#3) := by
    simpa [B28] using signedLabelThreeCode_lt (label R28)
  have hdom29 : B29 < (6#3) := by
    simpa [B29] using signedLabelThreeCode_lt (label R29)
  have hdom30 : B30 < (6#3) := by
    simpa [B30] using signedLabelThreeCode_lt (label R30)
  have hdom31 : B31 < (6#3) := by
    simpa [B31] using signedLabelThreeCode_lt (label R31)
  have hdom32 : B32 < (6#3) := by
    simpa [B32] using signedLabelThreeCode_lt (label R32)
  have hdom33 : B33 < (6#3) := by
    simpa [B33] using signedLabelThreeCode_lt (label R33)
  have hdom34 : B34 < (6#3) := by
    simpa [B34] using signedLabelThreeCode_lt (label R34)
  have hdom35 : B35 < (6#3) := by
    simpa [B35] using signedLabelThreeCode_lt (label R35)
  have hdom36 : B36 < (6#3) := by
    simpa [B36] using signedLabelThreeCode_lt (label R36)
  have hdom37 : B37 < (6#3) := by
    simpa [B37] using signedLabelThreeCode_lt (label R37)
  have hdom38 : B38 < (6#3) := by
    simpa [B38] using signedLabelThreeCode_lt (label R38)
  have hdom39 : B39 < (6#3) := by
    simpa [B39] using signedLabelThreeCode_lt (label R39)
  have h0 : B0 ≠ B1 := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R1.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R1,
        a, b, c, d] <;> decide)
    simpa [B0, B1, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h1 : B0 ≠ B3 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R3) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R3,
        a, b, c, d] <;> decide)
    simpa [B0, B3, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h2 : B0 ≠ B4 := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R4.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R4,
        a, b, c, d] <;> decide)
    simpa [B0, B4, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h3 : B0 ≠ B6 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R6) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R6,
        a, b, c, d] <;> decide)
    simpa [B0, B6, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h4 : B0 ≠ B7 := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R7.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R7,
        a, b, c, d] <;> decide)
    simpa [B0, B7, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h5 : B0 ≠ B9 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R9) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R9,
        a, b, c, d] <;> decide)
    simpa [B0, B9, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h6 : B0 ≠ B10 := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R10.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R10,
        a, b, c, d] <;> decide)
    simpa [B0, B10, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h7 : B0 ≠ B12 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R12,
        a, b, c, d] <;> decide)
    simpa [B0, B12, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h8 : B0 ≠ B13 := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R13.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R13,
        a, b, c, d] <;> decide)
    simpa [B0, B13, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h9 : B0 ≠ B15 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R15) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R15,
        a, b, c, d] <;> decide)
    simpa [B0, B15, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h10 : B0 ≠ B16 := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R16.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R16,
        a, b, c, d] <;> decide)
    simpa [B0, B16, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h11 : B0 ≠ B18 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R18) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R18,
        a, b, c, d] <;> decide)
    simpa [B0, B18, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h12 : B0 ≠ B19 := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R19.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R19,
        a, b, c, d] <;> decide)
    simpa [B0, B19, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h13 : B0 ≠ B21 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R21) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R21,
        a, b, c, d] <;> decide)
    simpa [B0, B21, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h14 : B0 ≠ B22 := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R22.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R22,
        a, b, c, d] <;> decide)
    simpa [B0, B22, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h15 : B0 ≠ B24 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R24) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R24,
        a, b, c, d] <;> decide)
    simpa [B0, B24, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h16 : B0 ≠ B25 := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R25.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R25,
        a, b, c, d] <;> decide)
    simpa [B0, B25, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h17 : B0 ≠ B27 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R27) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R27,
        a, b, c, d] <;> decide)
    simpa [B0, B27, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h18 : B0 ≠ B28 := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R28.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R28,
        a, b, c, d] <;> decide)
    simpa [B0, B28, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h19 : B0 ≠ B30 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R30) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R30,
        a, b, c, d] <;> decide)
    simpa [B0, B30, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h20 : B0 ≠ B31 := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R31.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R31,
        a, b, c, d] <;> decide)
    simpa [B0, B31, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h21 : B0 ≠ B33 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R33) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R33,
        a, b, c, d] <;> decide)
    simpa [B0, B33, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h22 : B0 ≠ B34 := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R34.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R34,
        a, b, c, d] <;> decide)
    simpa [B0, B34, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h23 : B0 ≠ B36 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R36) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R36,
        a, b, c, d] <;> decide)
    simpa [B0, B36, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h24 : B0 ≠ B37 := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R37.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R37,
        a, b, c, d] <;> decide)
    simpa [B0, B37, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h25 : B0 ≠ B39 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R0) (Y := R39) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R0, R39,
        a, b, c, d] <;> decide)
    simpa [B0, B39, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h26 : B2 ≠ B1 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R1) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R1,
        a, b, c, d] <;> decide)
    simpa [B2, B1, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h27 : B1 ≠ B6 := by
    have h := signedLabelThreeCode_noComplement hno (X := R1) (Y := R6.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R1, R6,
        a, b, c, d] <;> decide)
    simpa [B1, B6, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h28 : B1 ≠ B10 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R1) (Y := R10) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R1, R10,
        a, b, c, d] <;> decide)
    simpa [B1, B10, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h29 : B1 ≠ B15 := by
    have h := signedLabelThreeCode_noComplement hno (X := R1) (Y := R15.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R1, R15,
        a, b, c, d] <;> decide)
    simpa [B1, B15, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h30 : B1 ≠ B19 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R1) (Y := R19) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R1, R19,
        a, b, c, d] <;> decide)
    simpa [B1, B19, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h31 : B1 ≠ B24 := by
    have h := signedLabelThreeCode_noComplement hno (X := R1) (Y := R24.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R1, R24,
        a, b, c, d] <;> decide)
    simpa [B1, B24, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h32 : B1 ≠ B28 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R1) (Y := R28) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R1, R28,
        a, b, c, d] <;> decide)
    simpa [B1, B28, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h33 : B1 ≠ B33 := by
    have h := signedLabelThreeCode_noComplement hno (X := R1) (Y := R33.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R1, R33,
        a, b, c, d] <;> decide)
    simpa [B1, B33, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h34 : B1 ≠ B37 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R1) (Y := R37) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R1, R37,
        a, b, c, d] <;> decide)
    simpa [B1, B37, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h35 : B2 ≠ B3 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R3) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R3,
        a, b, c, d] <;> decide)
    simpa [B2, B3, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h36 : B2 ≠ B4 := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R4.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R4,
        a, b, c, d] <;> decide)
    simpa [B2, B4, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h37 : B2 ≠ B5 := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R5.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R5,
        a, b, c, d] <;> decide)
    simpa [B2, B5, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h38 : B2 ≠ B6 := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R6.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R6,
        a, b, c, d] <;> decide)
    simpa [B2, B6, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h39 : B2 ≠ B10 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R10) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R10,
        a, b, c, d] <;> decide)
    simpa [B2, B10, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h40 : B2 ≠ B11 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R11) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R11,
        a, b, c, d] <;> decide)
    simpa [B2, B11, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h41 : B2 ≠ B12 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R12,
        a, b, c, d] <;> decide)
    simpa [B2, B12, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h42 : B2 ≠ B13 := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R13.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R13,
        a, b, c, d] <;> decide)
    simpa [B2, B13, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h43 : B2 ≠ B14 := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R14.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R14,
        a, b, c, d] <;> decide)
    simpa [B2, B14, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h44 : B2 ≠ B15 := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R15.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R15,
        a, b, c, d] <;> decide)
    simpa [B2, B15, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h45 : B2 ≠ B19 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R19) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R19,
        a, b, c, d] <;> decide)
    simpa [B2, B19, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h46 : B2 ≠ B20 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R20) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R20,
        a, b, c, d] <;> decide)
    simpa [B2, B20, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h47 : B2 ≠ B21 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R21) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R21,
        a, b, c, d] <;> decide)
    simpa [B2, B21, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h48 : B2 ≠ B22 := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R22.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R22,
        a, b, c, d] <;> decide)
    simpa [B2, B22, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h49 : B2 ≠ B23 := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R23.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R23,
        a, b, c, d] <;> decide)
    simpa [B2, B23, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h50 : B2 ≠ B24 := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R24.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R24,
        a, b, c, d] <;> decide)
    simpa [B2, B24, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h51 : B2 ≠ B28 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R28) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R28,
        a, b, c, d] <;> decide)
    simpa [B2, B28, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h52 : B2 ≠ B29 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R29) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R29,
        a, b, c, d] <;> decide)
    simpa [B2, B29, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h53 : B2 ≠ B30 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R30) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R30,
        a, b, c, d] <;> decide)
    simpa [B2, B30, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h54 : B2 ≠ B31 := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R31.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R31,
        a, b, c, d] <;> decide)
    simpa [B2, B31, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h55 : B2 ≠ B32 := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R32.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R32,
        a, b, c, d] <;> decide)
    simpa [B2, B32, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h56 : B2 ≠ B33 := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R33.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R33,
        a, b, c, d] <;> decide)
    simpa [B2, B33, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h57 : B2 ≠ B37 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R37) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R37,
        a, b, c, d] <;> decide)
    simpa [B2, B37, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h58 : B2 ≠ B38 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R38) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R38,
        a, b, c, d] <;> decide)
    simpa [B2, B38, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h59 : B2 ≠ B39 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R2) (Y := R39) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R2, R39,
        a, b, c, d] <;> decide)
    simpa [B2, B39, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h60 : B3 ≠ B4 := by
    have h := signedLabelThreeCode_noComplement hno (X := R3) (Y := R4.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R3, R4,
        a, b, c, d] <;> decide)
    simpa [B3, B4, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h61 : B3 ≠ B12 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R3) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R3, R12,
        a, b, c, d] <;> decide)
    simpa [B3, B12, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h62 : B3 ≠ B13 := by
    have h := signedLabelThreeCode_noComplement hno (X := R3) (Y := R13.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R3, R13,
        a, b, c, d] <;> decide)
    simpa [B3, B13, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h63 : B3 ≠ B21 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R3) (Y := R21) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R3, R21,
        a, b, c, d] <;> decide)
    simpa [B3, B21, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h64 : B3 ≠ B22 := by
    have h := signedLabelThreeCode_noComplement hno (X := R3) (Y := R22.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R3, R22,
        a, b, c, d] <;> decide)
    simpa [B3, B22, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h65 : B3 ≠ B30 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R3) (Y := R30) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R3, R30,
        a, b, c, d] <;> decide)
    simpa [B3, B30, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h66 : B3 ≠ B31 := by
    have h := signedLabelThreeCode_noComplement hno (X := R3) (Y := R31.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R3, R31,
        a, b, c, d] <;> decide)
    simpa [B3, B31, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h67 : B3 ≠ B39 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R3) (Y := R39) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R3, R39,
        a, b, c, d] <;> decide)
    simpa [B3, B39, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h68 : B5 ≠ B4 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R5) (Y := R4) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R5, R4,
        a, b, c, d] <;> decide)
    simpa [B5, B4, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h69 : B7 ≠ B4 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R7) (Y := R4) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R7, R4,
        a, b, c, d] <;> decide)
    simpa [B7, B4, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h70 : B8 ≠ B4 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R4) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R4,
        a, b, c, d] <;> decide)
    simpa [B8, B4, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h71 : B4 ≠ B21 := by
    have h := signedLabelThreeCode_noComplement hno (X := R4) (Y := R21.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R4, R21,
        a, b, c, d] <;> decide)
    simpa [B4, B21, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h72 : B4 ≠ B31 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R4) (Y := R31) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R4, R31,
        a, b, c, d] <;> decide)
    simpa [B4, B31, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h73 : B5 ≠ B6 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R5) (Y := R6) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R5, R6,
        a, b, c, d] <;> decide)
    simpa [B5, B6, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h74 : B8 ≠ B5 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R5) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R5,
        a, b, c, d] <;> decide)
    simpa [B8, B5, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h75 : B5 ≠ B19 := by
    have h := signedLabelThreeCode_noComplement hno (X := R5) (Y := R19.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R5, R19,
        a, b, c, d] <;> decide)
    simpa [B5, B19, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h76 : B5 ≠ B20 := by
    have h := signedLabelThreeCode_noComplement hno (X := R5) (Y := R20.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R5, R20,
        a, b, c, d] <;> decide)
    simpa [B5, B20, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h77 : B5 ≠ B21 := by
    have h := signedLabelThreeCode_noComplement hno (X := R5) (Y := R21.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R5, R21,
        a, b, c, d] <;> decide)
    simpa [B5, B21, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h78 : B5 ≠ B31 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R5) (Y := R31) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R5, R31,
        a, b, c, d] <;> decide)
    simpa [B5, B31, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h79 : B5 ≠ B32 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R5) (Y := R32) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R5, R32,
        a, b, c, d] <;> decide)
    simpa [B5, B32, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h80 : B5 ≠ B33 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R5) (Y := R33) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R5, R33,
        a, b, c, d] <;> decide)
    simpa [B5, B33, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h81 : B8 ≠ B6 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R6) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R6,
        a, b, c, d] <;> decide)
    simpa [B8, B6, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h82 : B9 ≠ B6 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R9) (Y := R6) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R9, R6,
        a, b, c, d] <;> decide)
    simpa [B9, B6, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h83 : B6 ≠ B19 := by
    have h := signedLabelThreeCode_noComplement hno (X := R6) (Y := R19.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R6, R19,
        a, b, c, d] <;> decide)
    simpa [B6, B19, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h84 : B6 ≠ B33 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R6) (Y := R33) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R6, R33,
        a, b, c, d] <;> decide)
    simpa [B6, B33, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h85 : B8 ≠ B7 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R7) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R7,
        a, b, c, d] <;> decide)
    simpa [B8, B7, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h86 : B7 ≠ B10 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R7) (Y := R10) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R7, R10,
        a, b, c, d] <;> decide)
    simpa [B7, B10, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h87 : B7 ≠ B15 := by
    have h := signedLabelThreeCode_noComplement hno (X := R7) (Y := R15.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R7, R15,
        a, b, c, d] <;> decide)
    simpa [B7, B15, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h88 : B7 ≠ B18 := by
    have h := signedLabelThreeCode_noComplement hno (X := R7) (Y := R18.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R7, R18,
        a, b, c, d] <;> decide)
    simpa [B7, B18, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h89 : B7 ≠ B21 := by
    have h := signedLabelThreeCode_noComplement hno (X := R7) (Y := R21.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R7, R21,
        a, b, c, d] <;> decide)
    simpa [B7, B21, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h90 : B7 ≠ B31 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R7) (Y := R31) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R7, R31,
        a, b, c, d] <;> decide)
    simpa [B7, B31, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h91 : B7 ≠ B34 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R7) (Y := R34) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R7, R34,
        a, b, c, d] <;> decide)
    simpa [B7, B34, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h92 : B7 ≠ B37 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R7) (Y := R37) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R7, R37,
        a, b, c, d] <;> decide)
    simpa [B7, B37, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h93 : B8 ≠ B9 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R9) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R9,
        a, b, c, d] <;> decide)
    simpa [B8, B9, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h94 : B8 ≠ B10 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R10) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R10,
        a, b, c, d] <;> decide)
    simpa [B8, B10, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h95 : B8 ≠ B11 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R11) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R11,
        a, b, c, d] <;> decide)
    simpa [B8, B11, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h96 : B8 ≠ B12 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R12,
        a, b, c, d] <;> decide)
    simpa [B8, B12, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h97 : B8 ≠ B13 := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R13.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R13,
        a, b, c, d] <;> decide)
    simpa [B8, B13, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h98 : B8 ≠ B14 := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R14.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R14,
        a, b, c, d] <;> decide)
    simpa [B8, B14, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h99 : B8 ≠ B15 := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R15.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R15,
        a, b, c, d] <;> decide)
    simpa [B8, B15, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h100 : B8 ≠ B16 := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R16.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R16,
        a, b, c, d] <;> decide)
    simpa [B8, B16, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h101 : B8 ≠ B17 := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R17.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R17,
        a, b, c, d] <;> decide)
    simpa [B8, B17, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h102 : B8 ≠ B18 := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R18.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R18,
        a, b, c, d] <;> decide)
    simpa [B8, B18, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h103 : B8 ≠ B19 := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R19.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R19,
        a, b, c, d] <;> decide)
    simpa [B8, B19, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h104 : B8 ≠ B20 := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R20.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R20,
        a, b, c, d] <;> decide)
    simpa [B8, B20, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h105 : B8 ≠ B21 := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R21.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R21,
        a, b, c, d] <;> decide)
    simpa [B8, B21, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h106 : B8 ≠ B31 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R31) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R31,
        a, b, c, d] <;> decide)
    simpa [B8, B31, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h107 : B8 ≠ B32 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R32) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R32,
        a, b, c, d] <;> decide)
    simpa [B8, B32, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h108 : B8 ≠ B33 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R33) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R33,
        a, b, c, d] <;> decide)
    simpa [B8, B33, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h109 : B8 ≠ B34 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R34) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R34,
        a, b, c, d] <;> decide)
    simpa [B8, B34, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h110 : B8 ≠ B35 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R35) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R35,
        a, b, c, d] <;> decide)
    simpa [B8, B35, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h111 : B8 ≠ B36 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R36) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R36,
        a, b, c, d] <;> decide)
    simpa [B8, B36, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h112 : B8 ≠ B37 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R37) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R37,
        a, b, c, d] <;> decide)
    simpa [B8, B37, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h113 : B8 ≠ B38 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R38) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R38,
        a, b, c, d] <;> decide)
    simpa [B8, B38, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h114 : B8 ≠ B39 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R8) (Y := R39) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R8, R39,
        a, b, c, d] <;> decide)
    simpa [B8, B39, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h115 : B9 ≠ B12 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R9) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R9, R12,
        a, b, c, d] <;> decide)
    simpa [B9, B12, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h116 : B9 ≠ B13 := by
    have h := signedLabelThreeCode_noComplement hno (X := R9) (Y := R13.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R9, R13,
        a, b, c, d] <;> decide)
    simpa [B9, B13, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h117 : B9 ≠ B16 := by
    have h := signedLabelThreeCode_noComplement hno (X := R9) (Y := R16.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R9, R16,
        a, b, c, d] <;> decide)
    simpa [B9, B16, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h118 : B9 ≠ B19 := by
    have h := signedLabelThreeCode_noComplement hno (X := R9) (Y := R19.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R9, R19,
        a, b, c, d] <;> decide)
    simpa [B9, B19, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h119 : B9 ≠ B33 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R9) (Y := R33) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R9, R33,
        a, b, c, d] <;> decide)
    simpa [B9, B33, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h120 : B9 ≠ B36 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R9) (Y := R36) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R9, R36,
        a, b, c, d] <;> decide)
    simpa [B9, B36, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h121 : B9 ≠ B39 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R9) (Y := R39) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R9, R39,
        a, b, c, d] <;> decide)
    simpa [B9, B39, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h122 : B11 ≠ B10 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R11) (Y := R10) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R11, R10,
        a, b, c, d] <;> decide)
    simpa [B11, B10, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h123 : B10 ≠ B15 := by
    have h := signedLabelThreeCode_noComplement hno (X := R10) (Y := R15.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R10, R15,
        a, b, c, d] <;> decide)
    simpa [B10, B15, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h124 : B10 ≠ B37 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R10) (Y := R37) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R10, R37,
        a, b, c, d] <;> decide)
    simpa [B10, B37, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h125 : B11 ≠ B12 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R11) (Y := R12) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R11, R12,
        a, b, c, d] <;> decide)
    simpa [B11, B12, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h126 : B11 ≠ B13 := by
    have h := signedLabelThreeCode_noComplement hno (X := R11) (Y := R13.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R11, R13,
        a, b, c, d] <;> decide)
    simpa [B11, B13, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h127 : B11 ≠ B14 := by
    have h := signedLabelThreeCode_noComplement hno (X := R11) (Y := R14.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R11, R14,
        a, b, c, d] <;> decide)
    simpa [B11, B14, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h128 : B11 ≠ B15 := by
    have h := signedLabelThreeCode_noComplement hno (X := R11) (Y := R15.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R11, R15,
        a, b, c, d] <;> decide)
    simpa [B11, B15, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h129 : B11 ≠ B37 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R11) (Y := R37) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R11, R37,
        a, b, c, d] <;> decide)
    simpa [B11, B37, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h130 : B11 ≠ B38 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R11) (Y := R38) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R11, R38,
        a, b, c, d] <;> decide)
    simpa [B11, B38, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h131 : B11 ≠ B39 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R11) (Y := R39) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R11, R39,
        a, b, c, d] <;> decide)
    simpa [B11, B39, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h132 : B12 ≠ B13 := by
    have h := signedLabelThreeCode_noComplement hno (X := R12) (Y := R13.antipode) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R12, R13,
        a, b, c, d] <;> decide)
    simpa [B12, B13, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h133 : B12 ≠ B39 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R12) (Y := R39) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R12, R39,
        a, b, c, d] <;> decide)
    simpa [B12, B39, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h134 : B14 ≠ B13 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R14) (Y := R13) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R14, R13,
        a, b, c, d] <;> decide)
    simpa [B14, B13, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h135 : B16 ≠ B13 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R16) (Y := R13) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R16, R13,
        a, b, c, d] <;> decide)
    simpa [B16, B13, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h136 : B17 ≠ B13 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R17) (Y := R13) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R17, R13,
        a, b, c, d] <;> decide)
    simpa [B17, B13, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h137 : B22 ≠ B13 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R22) (Y := R13) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R22, R13,
        a, b, c, d] <;> decide)
    simpa [B22, B13, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h138 : B23 ≠ B13 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R23) (Y := R13) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R23, R13,
        a, b, c, d] <;> decide)
    simpa [B23, B13, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h139 : B25 ≠ B13 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R25) (Y := R13) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R25, R13,
        a, b, c, d] <;> decide)
    simpa [B25, B13, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h140 : B26 ≠ B13 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R13) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R13,
        a, b, c, d] <;> decide)
    simpa [B26, B13, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h141 : B14 ≠ B15 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R14) (Y := R15) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R14, R15,
        a, b, c, d] <;> decide)
    simpa [B14, B15, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h142 : B17 ≠ B14 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R17) (Y := R14) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R17, R14,
        a, b, c, d] <;> decide)
    simpa [B17, B14, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h143 : B23 ≠ B14 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R23) (Y := R14) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R23, R14,
        a, b, c, d] <;> decide)
    simpa [B23, B14, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h144 : B26 ≠ B14 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R14) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R14,
        a, b, c, d] <;> decide)
    simpa [B26, B14, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h145 : B17 ≠ B15 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R17) (Y := R15) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R17, R15,
        a, b, c, d] <;> decide)
    simpa [B17, B15, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h146 : B18 ≠ B15 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R18) (Y := R15) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R18, R15,
        a, b, c, d] <;> decide)
    simpa [B18, B15, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h147 : B23 ≠ B15 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R23) (Y := R15) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R23, R15,
        a, b, c, d] <;> decide)
    simpa [B23, B15, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h148 : B24 ≠ B15 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R24) (Y := R15) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R24, R15,
        a, b, c, d] <;> decide)
    simpa [B24, B15, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h149 : B26 ≠ B15 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R15) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R15,
        a, b, c, d] <;> decide)
    simpa [B26, B15, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h150 : B27 ≠ B15 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R27) (Y := R15) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R27, R15,
        a, b, c, d] <;> decide)
    simpa [B27, B15, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h151 : B17 ≠ B16 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R17) (Y := R16) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R17, R16,
        a, b, c, d] <;> decide)
    simpa [B17, B16, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h152 : B16 ≠ B19 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R16) (Y := R19) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R16, R19,
        a, b, c, d] <;> decide)
    simpa [B16, B19, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h153 : B25 ≠ B16 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R25) (Y := R16) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R25, R16,
        a, b, c, d] <;> decide)
    simpa [B25, B16, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h154 : B26 ≠ B16 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R16) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R16,
        a, b, c, d] <;> decide)
    simpa [B26, B16, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h155 : B17 ≠ B18 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R17) (Y := R18) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R17, R18,
        a, b, c, d] <;> decide)
    simpa [B17, B18, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h156 : B17 ≠ B19 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R17) (Y := R19) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R17, R19,
        a, b, c, d] <;> decide)
    simpa [B17, B19, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h157 : B17 ≠ B20 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R17) (Y := R20) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R17, R20,
        a, b, c, d] <;> decide)
    simpa [B17, B20, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h158 : B17 ≠ B21 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R17) (Y := R21) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R17, R21,
        a, b, c, d] <;> decide)
    simpa [B17, B21, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h159 : B26 ≠ B17 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R17) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R17,
        a, b, c, d] <;> decide)
    simpa [B26, B17, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h160 : B18 ≠ B21 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R18) (Y := R21) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R18, R21,
        a, b, c, d] <;> decide)
    simpa [B18, B21, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h161 : B26 ≠ B18 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R18) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R18,
        a, b, c, d] <;> decide)
    simpa [B26, B18, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h162 : B27 ≠ B18 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R27) (Y := R18) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R27, R18,
        a, b, c, d] <;> decide)
    simpa [B27, B18, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h163 : B20 ≠ B19 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R20) (Y := R19) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R20, R19,
        a, b, c, d] <;> decide)
    simpa [B20, B19, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h164 : B25 ≠ B19 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R25) (Y := R19) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R25, R19,
        a, b, c, d] <;> decide)
    simpa [B25, B19, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h165 : B26 ≠ B19 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R19) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R19,
        a, b, c, d] <;> decide)
    simpa [B26, B19, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h166 : B28 ≠ B19 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R28) (Y := R19) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R28, R19,
        a, b, c, d] <;> decide)
    simpa [B28, B19, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h167 : B29 ≠ B19 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R29) (Y := R19) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R29, R19,
        a, b, c, d] <;> decide)
    simpa [B29, B19, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h168 : B20 ≠ B21 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R20) (Y := R21) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R20, R21,
        a, b, c, d] <;> decide)
    simpa [B20, B21, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h169 : B26 ≠ B20 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R20) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R20,
        a, b, c, d] <;> decide)
    simpa [B26, B20, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h170 : B29 ≠ B20 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R29) (Y := R20) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R29, R20,
        a, b, c, d] <;> decide)
    simpa [B29, B20, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h171 : B26 ≠ B21 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R21) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R21,
        a, b, c, d] <;> decide)
    simpa [B26, B21, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h172 : B27 ≠ B21 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R27) (Y := R21) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R27, R21,
        a, b, c, d] <;> decide)
    simpa [B27, B21, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h173 : B29 ≠ B21 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R29) (Y := R21) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R29, R21,
        a, b, c, d] <;> decide)
    simpa [B29, B21, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h174 : B30 ≠ B21 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R30) (Y := R21) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R30, R21,
        a, b, c, d] <;> decide)
    simpa [B30, B21, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h175 : B23 ≠ B22 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R23) (Y := R22) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R23, R22,
        a, b, c, d] <;> decide)
    simpa [B23, B22, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h176 : B25 ≠ B22 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R25) (Y := R22) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R25, R22,
        a, b, c, d] <;> decide)
    simpa [B25, B22, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h177 : B26 ≠ B22 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R22) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R22,
        a, b, c, d] <;> decide)
    simpa [B26, B22, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h178 : B22 ≠ B31 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R22) (Y := R31) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R22, R31,
        a, b, c, d] <;> decide)
    simpa [B22, B31, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h179 : B23 ≠ B24 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R23) (Y := R24) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R23, R24,
        a, b, c, d] <;> decide)
    simpa [B23, B24, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h180 : B26 ≠ B23 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R23) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R23,
        a, b, c, d] <;> decide)
    simpa [B26, B23, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h181 : B23 ≠ B31 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R23) (Y := R31) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R23, R31,
        a, b, c, d] <;> decide)
    simpa [B23, B31, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h182 : B23 ≠ B32 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R23) (Y := R32) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R23, R32,
        a, b, c, d] <;> decide)
    simpa [B23, B32, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h183 : B23 ≠ B33 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R23) (Y := R33) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R23, R33,
        a, b, c, d] <;> decide)
    simpa [B23, B33, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h184 : B26 ≠ B24 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R24) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R24,
        a, b, c, d] <;> decide)
    simpa [B26, B24, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h185 : B27 ≠ B24 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R27) (Y := R24) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R27, R24,
        a, b, c, d] <;> decide)
    simpa [B27, B24, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h186 : B24 ≠ B33 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R24) (Y := R33) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R24, R33,
        a, b, c, d] <;> decide)
    simpa [B24, B33, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h187 : B26 ≠ B25 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R25) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R25,
        a, b, c, d] <;> decide)
    simpa [B26, B25, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h188 : B25 ≠ B28 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R25) (Y := R28) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R25, R28,
        a, b, c, d] <;> decide)
    simpa [B25, B28, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h189 : B25 ≠ B31 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R25) (Y := R31) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R25, R31,
        a, b, c, d] <;> decide)
    simpa [B25, B31, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h190 : B25 ≠ B34 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R25) (Y := R34) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R25, R34,
        a, b, c, d] <;> decide)
    simpa [B25, B34, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h191 : B25 ≠ B37 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R25) (Y := R37) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R25, R37,
        a, b, c, d] <;> decide)
    simpa [B25, B37, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h192 : B26 ≠ B27 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R27) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R27,
        a, b, c, d] <;> decide)
    simpa [B26, B27, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h193 : B26 ≠ B28 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R28) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R28,
        a, b, c, d] <;> decide)
    simpa [B26, B28, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h194 : B26 ≠ B29 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R29) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R29,
        a, b, c, d] <;> decide)
    simpa [B26, B29, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h195 : B26 ≠ B30 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R30) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R30,
        a, b, c, d] <;> decide)
    simpa [B26, B30, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h196 : B26 ≠ B31 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R31) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R31,
        a, b, c, d] <;> decide)
    simpa [B26, B31, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h197 : B26 ≠ B32 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R32) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R32,
        a, b, c, d] <;> decide)
    simpa [B26, B32, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h198 : B26 ≠ B33 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R33) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R33,
        a, b, c, d] <;> decide)
    simpa [B26, B33, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h199 : B26 ≠ B34 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R34) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R34,
        a, b, c, d] <;> decide)
    simpa [B26, B34, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h200 : B26 ≠ B35 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R35) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R35,
        a, b, c, d] <;> decide)
    simpa [B26, B35, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h201 : B26 ≠ B36 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R36) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R36,
        a, b, c, d] <;> decide)
    simpa [B26, B36, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h202 : B26 ≠ B37 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R37) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R37,
        a, b, c, d] <;> decide)
    simpa [B26, B37, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h203 : B26 ≠ B38 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R38) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R38,
        a, b, c, d] <;> decide)
    simpa [B26, B38, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h204 : B26 ≠ B39 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R26) (Y := R39) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R26, R39,
        a, b, c, d] <;> decide)
    simpa [B26, B39, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h205 : B27 ≠ B30 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R27) (Y := R30) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R27, R30,
        a, b, c, d] <;> decide)
    simpa [B27, B30, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h206 : B27 ≠ B33 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R27) (Y := R33) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R27, R33,
        a, b, c, d] <;> decide)
    simpa [B27, B33, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h207 : B27 ≠ B36 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R27) (Y := R36) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R27, R36,
        a, b, c, d] <;> decide)
    simpa [B27, B36, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h208 : B27 ≠ B39 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R27) (Y := R39) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R27, R39,
        a, b, c, d] <;> decide)
    simpa [B27, B39, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h209 : B29 ≠ B28 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R29) (Y := R28) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R29, R28,
        a, b, c, d] <;> decide)
    simpa [B29, B28, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h210 : B28 ≠ B37 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R28) (Y := R37) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R28, R37,
        a, b, c, d] <;> decide)
    simpa [B28, B37, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h211 : B29 ≠ B30 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R29) (Y := R30) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R29, R30,
        a, b, c, d] <;> decide)
    simpa [B29, B30, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h212 : B29 ≠ B37 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R29) (Y := R37) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R29, R37,
        a, b, c, d] <;> decide)
    simpa [B29, B37, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h213 : B29 ≠ B38 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R29) (Y := R38) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R29, R38,
        a, b, c, d] <;> decide)
    simpa [B29, B38, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h214 : B29 ≠ B39 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R29) (Y := R39) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R29, R39,
        a, b, c, d] <;> decide)
    simpa [B29, B39, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h215 : B30 ≠ B39 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R30) (Y := R39) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R30, R39,
        a, b, c, d] <;> decide)
    simpa [B30, B39, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h216 : B32 ≠ B31 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R32) (Y := R31) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R32, R31,
        a, b, c, d] <;> decide)
    simpa [B32, B31, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h217 : B34 ≠ B31 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R34) (Y := R31) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R34, R31,
        a, b, c, d] <;> decide)
    simpa [B34, B31, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h218 : B35 ≠ B31 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R35) (Y := R31) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R35, R31,
        a, b, c, d] <;> decide)
    simpa [B35, B31, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h219 : B32 ≠ B33 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R32) (Y := R33) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R32, R33,
        a, b, c, d] <;> decide)
    simpa [B32, B33, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h220 : B35 ≠ B32 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R35) (Y := R32) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R35, R32,
        a, b, c, d] <;> decide)
    simpa [B35, B32, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h221 : B35 ≠ B33 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R35) (Y := R33) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R35, R33,
        a, b, c, d] <;> decide)
    simpa [B35, B33, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h222 : B36 ≠ B33 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R36) (Y := R33) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R36, R33,
        a, b, c, d] <;> decide)
    simpa [B36, B33, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h223 : B35 ≠ B34 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R35) (Y := R34) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R35, R34,
        a, b, c, d] <;> decide)
    simpa [B35, B34, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h224 : B34 ≠ B37 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R34) (Y := R37) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R34, R37,
        a, b, c, d] <;> decide)
    simpa [B34, B37, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h225 : B35 ≠ B36 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R35) (Y := R36) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R35, R36,
        a, b, c, d] <;> decide)
    simpa [B35, B36, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h226 : B35 ≠ B37 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R35) (Y := R37) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R35, R37,
        a, b, c, d] <;> decide)
    simpa [B35, B37, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h227 : B35 ≠ B38 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R35) (Y := R38) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R35, R38,
        a, b, c, d] <;> decide)
    simpa [B35, B38, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h228 : B35 ≠ B39 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R35) (Y := R39) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R35, R39,
        a, b, c, d] <;> decide)
    simpa [B35, B39, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h229 : B36 ≠ B39 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R36) (Y := R39) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R36, R39,
        a, b, c, d] <;> decide)
    simpa [B36, B39, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h230 : B38 ≠ B37 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R38) (Y := R37) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R38, R37,
        a, b, c, d] <;> decide)
    simpa [B38, B37, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  have h231 : B38 ≠ B39 ^^^ (1#3) := by
    have h := signedLabelThreeCode_noComplement hno (X := R38) (Y := R39) (by
      simp [SignedSubset.Le, NonzeroSignedSubset.antipode, SignedSubset.antipode, R38, R39,
        a, b, c, d] <;> decide)
    simpa [B38, B39, signedLabelThreeCode_neg, SignedLabel.neg, hantipodal] using h
  exact tuckerLemmaStatement_four_core_unsat
    B0 B1 B2 B3 B4 B5 B6 B7
    B8 B9 B10 B11 B12 B13 B14 B15
    B16 B17 B18 B19 B20 B21 B22 B23
    B24 B25 B26 B27 B28 B29 B30 B31
    B32 B33 B34 B35 B36 B37 B38 B39
    hdom0 hdom1 hdom2 hdom3 hdom4 hdom5 hdom6 hdom7
    hdom8 hdom9 hdom10 hdom11 hdom12 hdom13 hdom14 hdom15
    hdom16 hdom17 hdom18 hdom19 hdom20 hdom21 hdom22 hdom23
    hdom24 hdom25 hdom26 hdom27 hdom28 hdom29 hdom30 hdom31
    hdom32 hdom33 hdom34 hdom35 hdom36 hdom37 hdom38 hdom39
    h0 h1 h2 h3 h4 h5 h6 h7
    h8 h9 h10 h11 h12 h13 h14 h15
    h16 h17 h18 h19 h20 h21 h22 h23
    h24 h25 h26 h27 h28 h29 h30 h31
    h32 h33 h34 h35 h36 h37 h38 h39
    h40 h41 h42 h43 h44 h45 h46 h47
    h48 h49 h50 h51 h52 h53 h54 h55
    h56 h57 h58 h59 h60 h61 h62 h63
    h64 h65 h66 h67 h68 h69 h70 h71
    h72 h73 h74 h75 h76 h77 h78 h79
    h80 h81 h82 h83 h84 h85 h86 h87
    h88 h89 h90 h91 h92 h93 h94 h95
    h96 h97 h98 h99 h100 h101 h102 h103
    h104 h105 h106 h107 h108 h109 h110 h111
    h112 h113 h114 h115 h116 h117 h118 h119
    h120 h121 h122 h123 h124 h125 h126 h127
    h128 h129 h130 h131 h132 h133 h134 h135
    h136 h137 h138 h139 h140 h141 h142 h143
    h144 h145 h146 h147 h148 h149 h150 h151
    h152 h153 h154 h155 h156 h157 h158 h159
    h160 h161 h162 h163 h164 h165 h166 h167
    h168 h169 h170 h171 h172 h173 h174 h175
    h176 h177 h178 h179 h180 h181 h182 h183
    h184 h185 h186 h187 h188 h189 h190 h191
    h192 h193 h194 h195 h196 h197 h198 h199
    h200 h201 h202 h203 h204 h205 h206 h207
    h208 h209 h210 h211 h212 h213 h214 h215
    h216 h217 h218 h219 h220 h221 h222 h223
    h224 h225 h226 h227 h228 h229 h230 h231

theorem kyFanEndpointPairingStatement_three_three : KyFanEndpointPairingStatement 3 3 := by
  intro label hantipodal hno
  exact False.elim (not_noComplementaryComparableLabels_four label hantipodal hno)

theorem tuckerLemmaStatement_four : TuckerLemmaStatement 4 :=
  tuckerLemmaStatement_succ_of_endpointPairing (by omega)
    kyFanEndpointPairingStatement_three_three

/-- Tucker's lemma is now available unconditionally in dimensions one through four. -/
theorem tuckerLemmaStatement_le_four {n : ℕ} (hnpos : 1 ≤ n) (hnle : n ≤ 4) :
    TuckerLemmaStatement n := by
  interval_cases n
  · exact tuckerLemmaStatement_one
  · exact tuckerLemmaStatement_two
  · exact tuckerLemmaStatement_three
  · exact tuckerLemmaStatement_four

end ProofsInTheBook.TuckerLemmaCore
