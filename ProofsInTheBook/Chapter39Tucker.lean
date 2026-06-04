import ProofsInTheBook.Chapter39

/-!
# Chapter 39 Tucker skeleton

This file keeps the new Tucker work out of `Chapter39.lean`.  It records the
closed low-dimensional cases and isolates the general successor obstruction as
a concrete finite-combinatorial construction.
-/

namespace ProofsInTheBook.Chapter39

/-- Re-export the closed one-dimensional base case in the new Tucker file. -/
theorem tuckerLemmaStatement_one_base : TuckerLemmaStatement 1 :=
  tuckerLemmaStatement_one

/-- Re-export the closed two-dimensional base case in the new Tucker file. -/
theorem tuckerLemmaStatement_two_base : TuckerLemmaStatement 2 :=
  tuckerLemmaStatement_two

/--
The direct induction-step obstruction in label-collapse form.

Given an antipodal label on dimension `n + 1` with no complementary comparable
pair, a last-coordinate collapse would have to build an antipodal
no-complement label in dimension `n`, where the induction hypothesis
contradicts it.
-/
def TuckerLastCoordinateCollapse (n : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset (n + 1) → SignedLabel n,
    (∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        ∃ reduced : NonzeroSignedSubset n → SignedLabel (n - 1),
          (∀ X, reduced X.antipode = (reduced X).neg) ∧
            NoComplementaryComparableLabels reduced

/--
If the last-coordinate collapse is available, the Tucker successor step is
formal.
-/
theorem tuckerLemmaStatement_succ_of_lastCoordinateCollapse {n : ℕ}
    (hcollapse : TuckerLastCoordinateCollapse n)
    (htucker : TuckerLemmaStatement n) :
    TuckerLemmaStatement (n + 1) := by
  intro label hantipodal
  by_contra hnone
  have hno : NoComplementaryComparableLabels label := by
    intro X Y hXY hcomp
    exact hnone ⟨X, Y, hXY, hcomp⟩
  obtain ⟨reduced, hred_antipodal, hred_no⟩ := hcollapse label hantipodal hno
  obtain ⟨X, Y, hXY, hcomp⟩ := htucker reduced hred_antipodal
  exact hred_no X Y hXY hcomp

/--
Induction skeleton for all positive dimensions, parameterized by the collapse
lemma in every successor dimension starting from the proved two-dimensional
case.
-/
theorem tuckerLemmaStatement_of_lastCoordinateCollapses
    (hcollapse : ∀ n : ℕ, 2 ≤ n → TuckerLastCoordinateCollapse n) :
    ∀ n : ℕ, 1 ≤ n → TuckerLemmaStatement n := by
  intro n hn
  by_cases hn_one : n = 1
  · subst n
    exact tuckerLemmaStatement_one_base
  · have hn_two : 2 ≤ n := by omega
    refine Nat.le_induction tuckerLemmaStatement_two_base ?_ n hn_two
    intro k hk ih
    exact tuckerLemmaStatement_succ_of_lastCoordinateCollapse (hcollapse k hk) ih

/--
The same successor obstruction in the path-following/Ky Fan endpoint package
already used by `Chapter39.lean`.
-/
def TuckerPathEndpointStep (n : ℕ) : Prop :=
  KyFanPrefixPathEndpointDecompositionStatement (n + 1) n

/-- Endpoints in the non-punctured Ky Fan path package: the two base endpoints
plus the positive/negative alternating top chains. -/
abbrev KyFanEndpointClass {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m) :=
  Bool ⊕ (PositivePrefixChainType label ⊕ NegativePrefixChainType label)

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

theorem topPrefixChainEndpointAntipode_fixedPointFree {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (top : PositivePrefixChainType label ⊕ NegativePrefixChainType label) :
    topPrefixChainEndpointAntipode label hantipodal top ≠ top := by
  rcases top with positive | negative <;>
    simp [topPrefixChainEndpointAntipode]

noncomputable def kyFanEndpointClassAntipode {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    KyFanEndpointClass label ≃ KyFanEndpointClass label :=
  Equiv.sumCongr Equiv.boolNot (topPrefixChainEndpointAntipode label hantipodal)

theorem kyFanEndpointClassAntipode_involutive {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    Function.Involutive (kyFanEndpointClassAntipode label hantipodal) := by
  intro endpoint
  rcases endpoint with base | top
  · cases base <;> rfl
  · change
      Sum.inr
          (topPrefixChainEndpointAntipode label hantipodal
            (topPrefixChainEndpointAntipode label hantipodal top)) =
        Sum.inr top
    rw [topPrefixChainEndpointAntipode_involutive label hantipodal top]

theorem kyFanEndpointClassAntipode_fixedPointFree {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (endpoint : KyFanEndpointClass label) :
    kyFanEndpointClassAntipode label hantipodal endpoint ≠ endpoint := by
  intro h
  rcases endpoint with base | top
  · cases base <;> simp [kyFanEndpointClassAntipode] at h
  · exact topPrefixChainEndpointAntipode_fixedPointFree label hantipodal top
      (by simpa [kyFanEndpointClassAntipode] using h)

/-- A path represented by the two endpoint orbit `{x, partner x}`.  The
missing Ky Fan graph construction is exactly the concrete fixed-point-free
partner on endpoint classes. -/
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

/--
The exact remaining graph-local datum: pair endpoint classes into two-ended
Ky Fan paths, compatibly with the antipodal endpoint action, and not by
antipodal pairing itself.
-/
structure KyFanEndpointPairing {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) where
  endpointPartner : KyFanEndpointClass label ≃ KyFanEndpointClass label
  endpointPartner_involutive : Function.Involutive endpointPartner
  endpointPartner_fixedPointFree : ∀ endpoint, endpointPartner endpoint ≠ endpoint
  endpointPartner_comm :
    ∀ endpoint,
      kyFanEndpointClassAntipode label hantipodal (endpointPartner endpoint) =
        endpointPartner (kyFanEndpointClassAntipode label hantipodal endpoint)
  endpointPartner_not_antipodal :
    ∀ endpoint,
      kyFanEndpointClassAntipode label hantipodal endpoint ≠ endpointPartner endpoint

noncomputable def kyFanPrefixPathEndpointDecomposition_of_endpointPairing
    {n m : ℕ} {label : NonzeroSignedSubset n → SignedLabel m}
    {hantipodal : ∀ X, label X.antipode = (label X).neg}
    (pairing : KyFanEndpointPairing label hantipodal) :
    KyFanPrefixPathEndpointDecomposition label := by
  classical
  exact
    { Path := TwoCyclePath pairing.endpointPartner
      Base := Bool
      Endpoint := fun path => TwoCycleEndpoint path
      instPath := inferInstance
      instBase := inferInstance
      instEndpoint := fun _ => inferInstance
      pathAntipode :=
        twoCyclePathAntipode
          (partner := pairing.endpointPartner)
          (endpointAntipode := kyFanEndpointClassAntipode label hantipodal)
          (kyFanEndpointClassAntipode_involutive label hantipodal)
          pairing.endpointPartner_comm
      pathAntipode_involutive :=
        twoCyclePathAntipode_involutive
          (partner := pairing.endpointPartner)
          (endpointAntipode := kyFanEndpointClassAntipode label hantipodal)
          (kyFanEndpointClassAntipode_involutive label hantipodal)
          pairing.endpointPartner_comm
      pathAntipode_fixedPointFree :=
        twoCyclePathAntipode_fixedPointFree
          (partner := pairing.endpointPartner)
          (endpointAntipode := kyFanEndpointClassAntipode label hantipodal)
          (kyFanEndpointClassAntipode_involutive label hantipodal)
          pairing.endpointPartner_comm
          (kyFanEndpointClassAntipode_fixedPointFree label hantipodal)
          pairing.endpointPartner_not_antipodal
      endpoint_card_two :=
        twoCycleEndpoint_card pairing.endpointPartner_fixedPointFree
      classify :=
        twoCycleEndpointClassify pairing.endpointPartner_involutive
      base_card := by
        simp }

def KyFanEndpointPairingStatement (n m : ℕ) : Prop :=
  ∀ label : NonzeroSignedSubset n → SignedLabel m,
    (hantipodal : ∀ X, label X.antipode = (label X).neg) →
      NoComplementaryComparableLabels label →
        Nonempty (KyFanEndpointPairing label hantipodal)

theorem kyFanPrefixPathEndpointDecompositionStatement_of_endpointPairing
    {n m : ℕ} (hpairing : KyFanEndpointPairingStatement n m) :
    KyFanPrefixPathEndpointDecompositionStatement n m := by
  intro label hantipodal hno
  rcases hpairing label hantipodal hno with ⟨pairing⟩
  exact ⟨kyFanPrefixPathEndpointDecomposition_of_endpointPairing pairing⟩

theorem kyFanPrefixParityStatement_of_endpointPairing
    {n m : ℕ} (hpairing : KyFanEndpointPairingStatement n m) :
    KyFanPrefixParityStatement n m :=
  kyFanPrefixParityStatement_of_pathEndpointDecomposition
    (kyFanPrefixPathEndpointDecompositionStatement_of_endpointPairing hpairing)

theorem tuckerLemmaStatement_of_endpointPairing {n : ℕ} (hn : 1 ≤ n)
    (hpairing : KyFanEndpointPairingStatement n (n - 1)) :
    TuckerLemmaStatement n :=
  tuckerLemmaStatement_of_kyFanPrefixParity hn
    (kyFanPrefixParityStatement_of_endpointPairing hpairing)

/--
The endpoint-decomposition step is sufficient for the Tucker successor.
-/
theorem tuckerLemmaStatement_succ_of_pathEndpointStep {n : ℕ} (hn : 0 < n)
    (hstep : TuckerPathEndpointStep n) :
    TuckerLemmaStatement (n + 1) :=
  tuckerLemmaStatement_of_kyFanPrefixParity (n := n + 1) (by omega)
    (kyFanPrefixParityStatement_of_pathEndpointDecomposition hstep)

/--
An induction-shaped wrapper around the endpoint-decomposition successor
obligation.  The induction hypothesis is intentionally unused: the remaining
work is the finite Ky Fan path construction in each successor dimension.
-/
theorem tuckerLemmaStatement_of_pathEndpointSteps
    (hstep : ∀ n : ℕ, 2 ≤ n → TuckerPathEndpointStep n) :
    ∀ n : ℕ, 1 ≤ n → TuckerLemmaStatement n := by
  intro n hn
  by_cases hn_one : n = 1
  · subst n
    exact tuckerLemmaStatement_one_base
  · have hn_two : 2 ≤ n := by omega
    refine Nat.le_induction tuckerLemmaStatement_two_base ?_ n hn_two
    intro k hk _ih
    exact tuckerLemmaStatement_succ_of_pathEndpointStep (by omega) (hstep k hk)

def TuckerEndpointPairingStep (n : ℕ) : Prop :=
  KyFanEndpointPairingStatement (n + 1) n

theorem tuckerLemmaStatement_succ_of_endpointPairingStep {n : ℕ} (hn : 0 < n)
    (hstep : TuckerEndpointPairingStep n) :
    TuckerLemmaStatement (n + 1) :=
  tuckerLemmaStatement_of_endpointPairing (by omega) hstep

theorem tuckerLemmaStatement_of_endpointPairingSteps
    (hstep : ∀ n : ℕ, 2 ≤ n → TuckerEndpointPairingStep n) :
    ∀ n : ℕ, 1 ≤ n → TuckerLemmaStatement n := by
  intro n hn
  by_cases hn_one : n = 1
  · subst n
    exact tuckerLemmaStatement_one_base
  · have hn_two : 2 ≤ n := by omega
    refine Nat.le_induction tuckerLemmaStatement_two_base ?_ n hn_two
    intro k hk _ih
    exact tuckerLemmaStatement_succ_of_endpointPairingStep (by omega) (hstep k hk)

end ProofsInTheBook.Chapter39
