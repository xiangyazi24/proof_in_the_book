import Mathlib

open Classical

universe u

variable {V : Type u} [Fintype V]

def compSetoid (r : V → V → Prop) : Setoid V :=
  ⟨Relation.EqvGen r, Relation.EqvGen.is_equivalence r⟩

noncomputable def numComp (r : V → V → Prop) : ℕ :=
  Nat.card (Quotient (compSetoid r))

def addEdge (r : V → V → Prop) (a b : V) : V → V → Prop :=
  fun x y => r x y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)

private def pairRel {α : Type u} (a b : α) (x y : α) : Prop :=
  x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)

private theorem pairRel_refl {α : Type u} (a b : α) (x : α) :
    pairRel a b x x := by
  exact Or.inl rfl

private theorem pairRel_symm {α : Type u} (a b : α) {x y : α} :
    pairRel a b x y → pairRel a b y x := by
  intro h
  rcases h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

private theorem pairRel_trans {α : Type u} (a b : α) {x y z : α} :
    pairRel a b x y → pairRel a b y z → pairRel a b x z := by
  intro hxy hyz
  rcases hxy with hEq | hAB | hBA
  · subst y
    exact hyz
  · rcases hAB with ⟨rfl, rfl⟩
    rcases hyz with hEq | hAB' | hBA'
    · subst z
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hAB' with ⟨_, hz⟩
      subst z
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hBA' with ⟨_, hz⟩
      subst z
      exact Or.inl rfl
  · rcases hBA with ⟨rfl, rfl⟩
    rcases hyz with hEq | hAB' | hBA'
    · subst z
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · rcases hAB' with ⟨_, hz⟩
      subst z
      exact Or.inl rfl
    · rcases hBA' with ⟨_, hz⟩
      subst z
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)

private def pairSetoid {α : Type u} (a b : α) : Setoid α where
  r := pairRel a b
  iseqv :=
    ⟨pairRel_refl a b, fun h => pairRel_symm a b h,
      fun h₁ h₂ => pairRel_trans a b h₁ h₂⟩

omit [Fintype V] in
private theorem eqvGen_mono {r s : V → V → Prop}
    (h : ∀ ⦃x y : V⦄, r x y → s x y) {x y : V} :
    Relation.EqvGen r x y → Relation.EqvGen s x y := by
  intro hxy
  induction hxy with
  | rel x y hxy =>
      exact Relation.EqvGen.rel x y (h hxy)
  | refl x =>
      exact Relation.EqvGen.refl x
  | symm x y _ ih =>
      exact Relation.EqvGen.symm x y ih
  | trans x y z _ _ ihxy ihyz =>
      exact Relation.EqvGen.trans x y z ihxy ihyz

omit [Fintype V] in
private theorem eqvGen_le_addEdge (r : V → V → Prop) (a b : V) {x y : V} :
    Relation.EqvGen r x y → Relation.EqvGen (addEdge r a b) x y := by
  intro hxy
  exact eqvGen_mono (s := addEdge r a b) (fun {x y} hr => Or.inl hr) hxy

omit [Fintype V] in
private theorem eqvGen_addEdge_iff_pairRel (r : V → V → Prop) (a b x y : V) :
    Relation.EqvGen (addEdge r a b) x y ↔
      pairRel (Quotient.mk (compSetoid r) a) (Quotient.mk (compSetoid r) b)
        (Quotient.mk (compSetoid r) x) (Quotient.mk (compSetoid r) y) := by
  constructor
  · intro hxy
    induction hxy with
    | rel x y hxy =>
        rcases hxy with hr | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl (Quotient.sound (Relation.EqvGen.rel x y hr))
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    | refl x =>
        exact pairRel_refl _ _ _
    | symm x y _ ih =>
        exact pairRel_symm _ _ ih
    | trans x y z _ _ ihxy ihyz =>
        exact pairRel_trans _ _ ihxy ihyz
  · intro hxy
    rcases hxy with hxy | hxab | hxba
    · exact eqvGen_le_addEdge r a b (Quotient.exact hxy)
    · rcases hxab with ⟨hxa, hyb⟩
      have hxa' : Relation.EqvGen (addEdge r a b) x a :=
        eqvGen_le_addEdge r a b (Quotient.exact hxa)
      have hby' : Relation.EqvGen (addEdge r a b) b y :=
        Relation.EqvGen.symm y b (eqvGen_le_addEdge r a b (Quotient.exact hyb))
      have hab' : Relation.EqvGen (addEdge r a b) a b :=
        Relation.EqvGen.rel a b (Or.inr (Or.inl ⟨rfl, rfl⟩))
      exact Relation.EqvGen.trans x a y hxa'
        (Relation.EqvGen.trans a b y hab' hby')
    · rcases hxba with ⟨hxb, hya⟩
      have hxb' : Relation.EqvGen (addEdge r a b) x b :=
        eqvGen_le_addEdge r a b (Quotient.exact hxb)
      have hay' : Relation.EqvGen (addEdge r a b) a y :=
        Relation.EqvGen.symm y a (eqvGen_le_addEdge r a b (Quotient.exact hya))
      have hba' : Relation.EqvGen (addEdge r a b) b a :=
        Relation.EqvGen.rel b a (Or.inr (Or.inr ⟨rfl, rfl⟩))
      exact Relation.EqvGen.trans x b y hxb'
        (Relation.EqvGen.trans b a y hba' hay')

omit [Fintype V] in
private theorem eqvGen_addEdge_iff (r : V → V → Prop) (a b x y : V) :
    Relation.EqvGen (addEdge r a b) x y ↔
      Relation.EqvGen r x y
        ∨ (Relation.EqvGen r x a ∧ Relation.EqvGen r y b)
        ∨ (Relation.EqvGen r x b ∧ Relation.EqvGen r y a) := by
  rw [eqvGen_addEdge_iff_pairRel]
  constructor
  · intro hxy
    rcases hxy with hxy | hxab | hxba
    · exact Or.inl (Quotient.exact hxy)
    · exact Or.inr (Or.inl ⟨Quotient.exact hxab.1, Quotient.exact hxab.2⟩)
    · exact Or.inr (Or.inr ⟨Quotient.exact hxba.1, Quotient.exact hxba.2⟩)
  · intro hxy
    rcases hxy with hxy | hxab | hxba
    · exact Or.inl (Quotient.sound hxy)
    · exact Or.inr (Or.inl ⟨Quotient.sound hxab.1, Quotient.sound hxab.2⟩)
    · exact Or.inr (Or.inr ⟨Quotient.sound hxba.1, Quotient.sound hxba.2⟩)

private def quotientEquivOfRelIff {α : Type u} (s t : Setoid α)
    (h : ∀ x y : α, s.r x y ↔ t.r x y) :
    Quotient s ≃ Quotient t where
  toFun := Quotient.map id (by
    intro x y hxy
    exact (h x y).1 hxy)
  invFun := Quotient.map id (by
    intro x y hxy
    exact (h x y).2 hxy)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rfl

private def pairRep {α : Type u} [DecidableEq α] {a b : α} (hab : a ≠ b)
    (x : α) : {x : α // x ≠ b} :=
  if hx : x = b then ⟨a, hab⟩ else ⟨x, hx⟩

private def pairQuotEquivSubtypeNe {α : Type u} [DecidableEq α] {a b : α}
    (hab : a ≠ b) :
    Quotient (pairSetoid a b) ≃ {x : α // x ≠ b} where
  toFun := Quotient.lift (pairRep hab) (by
    intro x y hxy
    change pairRel a b x y at hxy
    rcases hxy with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · simp [pairRep, hab]
    · simp [pairRep, hab])
  invFun := fun x => Quotient.mk (pairSetoid a b) x.1
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    dsimp
    by_cases hx : x = b
    · subst x
      simp [pairRep]
      exact Quotient.sound (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · simp [pairRep, hx]
  right_inv := by
    intro x
    ext
    simp [pairRep, x.2]

private theorem pairSetoid_card_add_one {α : Type u} [Fintype α] [DecidableEq α]
    {a b : α} (hab : a ≠ b) :
    Nat.card (Quotient (pairSetoid a b)) + 1 = Nat.card α := by
  classical
  haveI : Fintype (Quotient (pairSetoid a b)) := Quotient.fintype (pairSetoid a b)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hcardEquiv :
      Fintype.card (Quotient (pairSetoid a b)) = Fintype.card {x : α // x ≠ b} :=
    Fintype.card_congr (pairQuotEquivSubtypeNe hab)
  rw [hcardEquiv]
  have hcompl := Fintype.card_subtype_compl (fun x : α => x = b)
  have hsingle : Fintype.card {x : α // x = b} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨b, rfl⟩, ?_⟩
    intro y
    ext
    exact y.2
  rw [hcompl, hsingle]
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨b⟩
  omega

private def compAddQuotEquivPairQuot (r : V → V → Prop) (a b : V) :
    Quotient (compSetoid (addEdge r a b)) ≃
      Quotient
        (pairSetoid (Quotient.mk (compSetoid r) a) (Quotient.mk (compSetoid r) b)) where
  toFun := Quotient.lift
    (fun x =>
      Quotient.mk
        (pairSetoid (Quotient.mk (compSetoid r) a) (Quotient.mk (compSetoid r) b))
        (Quotient.mk (compSetoid r) x))
    (by
      intro x y hxy
      exact Quotient.sound ((eqvGen_addEdge_iff_pairRel r a b x y).1 hxy))
  invFun :=
    Quotient.lift
      (Quotient.map id (by
        intro x y hxy
        exact eqvGen_le_addEdge r a b hxy))
      (by
        intro x y hxy
        change pairRel (Quotient.mk (compSetoid r) a) (Quotient.mk (compSetoid r) b) x y
          at hxy
        rcases hxy with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Quotient.sound (Relation.EqvGen.rel a b (Or.inr (Or.inl ⟨rfl, rfl⟩)))
        · exact Quotient.sound (Relation.EqvGen.rel b a (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    refine Quotient.inductionOn x ?_
    intro v
    rfl

omit [Fintype V] in
theorem numComp_addEdge_of_eqvGen (r : V → V → Prop) {a b : V}
    (h : Relation.EqvGen r a b) :
    numComp (addEdge r a b) = numComp r := by
  unfold numComp
  apply Nat.card_congr
  refine quotientEquivOfRelIff (compSetoid (addEdge r a b)) (compSetoid r) ?_
  intro x y
  constructor
  · intro hxy
    change Relation.EqvGen (addEdge r a b) x y at hxy
    rw [eqvGen_addEdge_iff] at hxy
    rcases hxy with hxy | hxab | hxba
    · exact hxy
    · exact Relation.EqvGen.trans x a y hxab.1
        (Relation.EqvGen.trans a b y h (Relation.EqvGen.symm y b hxab.2))
    · exact Relation.EqvGen.trans x b y hxba.1
        (Relation.EqvGen.trans b a y (Relation.EqvGen.symm a b h)
          (Relation.EqvGen.symm y a hxba.2))
  · intro hxy
    exact eqvGen_le_addEdge r a b hxy

theorem numComp_addEdge_of_not_eqvGen (r : V → V → Prop) {a b : V}
    (h : ¬ Relation.EqvGen r a b) :
    numComp (addEdge r a b) + 1 = numComp r := by
  classical
  let Q := Quotient (compSetoid r)
  let A : Q := Quotient.mk (compSetoid r) a
  let B : Q := Quotient.mk (compSetoid r) b
  haveI : Fintype Q := Quotient.fintype (compSetoid r)
  have hAB : A ≠ B := by
    intro hq
    exact h (Quotient.exact hq)
  unfold numComp
  change Nat.card (Quotient (compSetoid (addEdge r a b))) + 1 = Nat.card Q
  have hcard :
      Nat.card
          (Quotient
            (pairSetoid (Quotient.mk (compSetoid r) a) (Quotient.mk (compSetoid r) b)))
          + 1 =
        Nat.card Q := by
    simpa [Q, A, B] using pairSetoid_card_add_one hAB
  rw [Nat.card_congr (compAddQuotEquivPairQuot r a b)]
  exact hcard
