import ProofsInTheBook.PlanarMapEuler
import ProofsInTheBook.PermTranspositionCycleCount
import ProofsInTheBook.RelationComponentCount

/-!
# Euler inequality for connected combinatorial maps (`χ ≤ 2`)

This file proves the load-bearing inequality of the Chapter 35 Jordan argument:

```
theorem chi_le_two_of_connected (M : CombMap D) (hconn : M.Connected) :
    M.eulerChar ≤ 2
```

i.e. `V - E + F ≤ 2` for every *connected* combinatorial map.  This is the
minimal genus-theory fragment (`genus ≥ 0`); no topology is used.

## Method (pure permutation / orbit-counting route)

We work with **raw permutation pairs** `(σ, α)` where `α` is an involution
(`α * α = 1`) but is allowed to have fixed points.  For such a pair we set

* `V = #orbits σ`,
* `F = #orbits (σ * α)`,
* `Ehalf = (support α).card / 2` (number of `α`-transpositions),
* `c = #components` of the symmetric relation `dartStepRel σ α` (the
  `⟨σ, α⟩`-orbit count of the map),

and prove the **genus inequality** `V - Ehalf + F ≤ 2 * c` for *all* such pairs,
by strong induction on `(support α).card`.  Removing one `α`-transposition
`{a, b}` (replacing `α` by `α * swap a b`, which fixes `a` and `b`) decreases
`Ehalf` by `1` and changes `F` by exactly `±1`
(`PlanarMapEulerInequality` crux, the transposition cycle-count fact) and changes
`c` by `0` or `+1`.  A short case analysis on whether `a` and `b` lie in the same
`(σ, α')`-component keeps the slack `2c - V + Ehalf - F` nonnegative.

For a genuine `CombMap` (fixed-point-free `α`) `Ehalf = E`, and connectivity
gives `c = 1`, whence `V - E + F ≤ 2`.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Orbit counting for a single permutation -/

open scoped Classical in
/-- The repo's orbit count (`Fintype.card (Quotient (cycleSetoid p))`) agrees with
`_root_.numCycles p` (built from `SameCycle.setoid`): the two setoids
carry the identical relation `p.SameCycle`. -/
lemma card_cycleSetoid_eq_numCycles (p : Equiv.Perm D) :
    Fintype.card (Quotient (cycleSetoid p)) = _root_.numCycles p := by
  classical
  unfold _root_.numCycles
  exact Fintype.card_congr
    (Quotient.congr (Equiv.refl D) (fun x y => by rfl))

lemma V_eq_numCycles (M : CombMap D) : M.V = _root_.numCycles M.σ :=
  card_cycleSetoid_eq_numCycles M.σ
lemma E_eq_numCycles (M : CombMap D) : M.E = _root_.numCycles M.α :=
  card_cycleSetoid_eq_numCycles M.α
lemma F_eq_numCycles (M : CombMap D) : M.F = _root_.numCycles M.φ :=
  card_cycleSetoid_eq_numCycles M.φ

/-! ## Raw permutation pairs

We carry the genus argument over *raw* pairs `(σ, α)` with `α * α = 1`, allowing
`α` to have fixed points.  This lets us delete one `α`-transposition at a time
inside an induction. -/

/-- The dart-incidence relation of a raw pair `(σ, α)`: two darts are adjacent if
they share a `σ`-orbit (same vertex) or are joined by the `α`-edge. -/
def dartStepRel (σ α : Equiv.Perm D) (a b : D) : Prop :=
  σ.SameCycle a b ∨ b = α a

omit [Fintype D] [DecidableEq D] in
lemma dartStepRel_symm {σ α : Equiv.Perm D} (hα : α * α = 1) {a b : D}
    (h : dartStepRel σ α a b) : dartStepRel σ α b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · refine Or.inr ?_
    subst h
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ.symm

/-! ### Symmetric relations: `EqvGen` coincides with `ReflTransGen` -/

omit [Fintype D] [DecidableEq D] in
/-- `ReflTransGen` of a symmetric relation is symmetric. -/
lemma reflTransGen_symm {r : D → D → Prop} (hsymm : ∀ a b, r a b → r b a)
    {a b : D} (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hsymm _ _ hbc) ih

omit [Fintype D] [DecidableEq D] in
/-- For a symmetric relation, the equivalence closure is the reflexive-transitive
closure (the repo's `Connected` is phrased with `ReflTransGen`). -/
lemma eqvGen_iff_reflTransGen {r : D → D → Prop} (hsymm : ∀ a b, r a b → r b a)
    (a b : D) :
    Relation.EqvGen r a b ↔ Relation.ReflTransGen r a b := by
  constructor
  · intro h
    induction h with
    | rel x y hxy => exact Relation.ReflTransGen.single hxy
    | refl x => exact Relation.ReflTransGen.refl
    | symm x y _ ih => exact reflTransGen_symm hsymm ih
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    induction h with
    | refl => exact Relation.EqvGen.refl a
    | tail _ hbc ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hbc)

/-! ### Edge count of a raw pair

`Ehalf α = (support α).card / 2` is the number of `α`-transpositions.  Deleting a
transposition `{a, b}` of `α` (replacing `α` by `α * swap a b`, which then fixes
`a` and `b`) removes exactly those two darts from the support. -/

/-- Number of `α`-transpositions. -/
noncomputable def Ehalf (α : Equiv.Perm D) : ℕ := (Equiv.Perm.support α).card / 2

omit [Fintype D] in
lemma swap_mul_self_cancel (a b : D) (p : Equiv.Perm D) :
    p * Equiv.swap a b * Equiv.swap a b = p := by
  rw [mul_assoc, Equiv.swap_mul_self, mul_one]

/-- Removing the transposition `{a, b}` (with `α a = b`, `a ≠ b`) from an
involution `α`: the support loses exactly `a` and `b`. -/
lemma support_mul_swap_of_apply (α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (hab : a ≠ b) (hαa : α a = b) :
    Equiv.Perm.support (α * Equiv.swap a b) = (Equiv.Perm.support α) \ {a, b} := by
  classical
  have hαb : α b = a := by
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    have : α (α a) = a := by
      simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
    rw [hαa] at this; exact this
  ext x
  simp only [Equiv.Perm.mem_support, Finset.mem_sdiff, Finset.mem_insert,
    Finset.mem_singleton, ne_eq]
  constructor
  · intro hx
    rcases eq_or_ne x a with rfl | hxa
    · exact absurd (by rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hαb]) hx
    · rcases eq_or_ne x b with rfl | hxb
      · exact absurd (by rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, hαa]) hx
      · refine ⟨?_, fun h => by rcases h with h | h <;> simp_all⟩
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb] at hx
        exact hx
  · rintro ⟨hx, hx2⟩
    push_neg at hx2
    obtain ⟨hxa, hxb⟩ := hx2
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb]
    exact hx

/-- `a` and `b` are distinct elements of `support α` when `α a = b`. -/
lemma mem_support_of_apply_ne {α : Equiv.Perm D} {a b : D} (hab : a ≠ b)
    (hαa : α a = b) : a ∈ Equiv.Perm.support α ∧ b ∈ Equiv.Perm.support α := by
  classical
  constructor
  · rw [Equiv.Perm.mem_support, hαa]; exact hab.symm
  · rw [Equiv.Perm.mem_support]
    intro hb
    -- if `α b = b` then `α a = b` and injectivity force `a = b`
    exact hab (α.injective (by rw [hαa, hb]))

/-- Deleting one transposition drops `Ehalf` by exactly one. -/
lemma Ehalf_mul_swap (α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (hab : a ≠ b) (hαa : α a = b) :
    Ehalf (α * Equiv.swap a b) + 1 = Ehalf α := by
  classical
  have hαb : α b = a := by
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    have : α (α a) = a := by
      simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
    rw [hαa] at this; exact this
  have hsupp := support_mul_swap_of_apply α hα hab hαa
  obtain ⟨ha, hb⟩ := mem_support_of_apply_ne hab hαa
  have hpair : ({a, b} : Finset D) ⊆ Equiv.Perm.support α := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard2 : ({a, b} : Finset D).card = 2 := by
    rw [Finset.card_pair hab]
  have hinter : ({a, b} : Finset D) ∩ Equiv.Perm.support α = {a, b} :=
    Finset.inter_eq_left.mpr hpair
  have hcards : (Equiv.Perm.support (α * Equiv.swap a b)).card
      = (Equiv.Perm.support α).card - 2 := by
    rw [hsupp, Finset.card_sdiff, hinter, hcard2]
  -- `support α` has even cardinality (involution), and contains the 2-element pair.
  have heven : 2 ∣ (Equiv.Perm.support α).card :=
    Equiv.Perm.two_dvd_card_support (by
      have : α ^ 2 = 1 := by rw [pow_two]; exact hα
      exact this)
  have h2le : 2 ≤ (Equiv.Perm.support α).card := by
    have := Finset.card_le_card hpair
    rwa [hcard2] at this
  unfold Ehalf
  rw [hcards]
  omega

/-! ## Component count of a raw pair -/

open Relation in
/-- One application of `σ * α` is a 2-step `dartStepRel` walk `x → α x → σ(α x)`. -/
lemma reflTransGen_dartStepRel_mul_apply (σ α : Equiv.Perm D) (x : D) :
    ReflTransGen (dartStepRel σ α) x ((σ * α) x) := by
  have h1 : dartStepRel σ α x (α x) := Or.inr rfl
  have h2 : dartStepRel σ α (α x) ((σ * α) x) := by
    refine Or.inl ?_
    have hmul : (σ * α) x = σ (α x) := rfl
    rw [hmul]
    exact ⟨1, by simp⟩
  exact (ReflTransGen.single h1).tail h2

open Relation in
/-- A `σα`-power walk lifts to a `dartStepRel` reflexive-transitive walk. -/
lemma reflTransGen_dartStepRel_of_pow (σ α : Equiv.Perm D) :
    ∀ (k : ℕ) (x : D), ReflTransGen (dartStepRel σ α) x (((σ * α) ^ k) x) := by
  intro k
  induction k with
  | zero => intro x; simpa using ReflTransGen.refl
  | succ k ih =>
      intro x
      have hstep := reflTransGen_dartStepRel_mul_apply σ α (((σ * α) ^ k) x)
      have hpow : ((σ * α) ^ (k + 1)) x = (σ * α) (((σ * α) ^ k) x) := by
        rw [pow_succ']; rfl
      rw [hpow]
      exact (ih x).trans hstep

open Relation in
/-- Same `σα`-cycle implies the two darts are `dartStepRel`-connected. -/
lemma eqvGen_dartStepRel_of_sameCycle_mul (σ α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (h : (σ * α).SameCycle a b) :
    EqvGen (dartStepRel σ α) a b := by
  rw [eqvGen_iff_reflTransGen (fun x y => dartStepRel_symm hα)]
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rw [← hk]
  exact reflTransGen_dartStepRel_of_pow σ α k a

/-! ## The pointwise relation identity for one edge deletion -/

/-- With `α a = b`, `α b = a`, `a ≠ b`, the dart relation of `α` is the dart
relation of `α' = α * swap a b` (which fixes `a, b`) with the single edge `{a, b}`
re-added. -/
lemma dartStepRel_eq_addEdge (σ α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (hab : a ≠ b) (hαa : α a = b) :
    dartStepRel σ α
      = _root_.addEdge (dartStepRel σ (α * Equiv.swap a b)) a b := by
  have hαb : α b = a := by
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    have hh : α (α a) = a := by simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
    rw [hαa] at hh; exact hh
  funext x y
  simp only [dartStepRel, _root_.addEdge, eq_iff_iff]
  have hrefl : σ.SameCycle x x := Equiv.Perm.SameCycle.refl σ x
  rcases eq_or_ne x a with rfl | hxa
  · -- `x = a`: `a` is eliminated, the surviving name is `x`
    have hα' : (α * Equiv.swap x b) x = x := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hαb]
    rw [hαa, hα']
    constructor
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · subst h; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rintro ((h | h) | ⟨_, h⟩ | ⟨hxb, _⟩)
      · exact Or.inl h
      · exact Or.inl (h ▸ hrefl)
      · exact Or.inr h
      · exact absurd hxb hab
  · rcases eq_or_ne x b with rfl | hxb
    · -- `x = b`: surviving name is `x`
      have hα' : (α * Equiv.swap a x) x = x := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, hαa]
      rw [hαb, hα']
      constructor
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · subst h; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · rintro ((h | h) | ⟨hxa', _⟩ | ⟨_, h⟩)
        · exact Or.inl h
        · exact Or.inl (h ▸ hrefl)
        · exact absurd hxa' hxa
        · exact Or.inr h
    · have hα' : (α * Equiv.swap a b) x = α x := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb]
      rw [hα']
      constructor
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
      · rintro ((h | h) | ⟨hxa', _⟩ | ⟨hxb', _⟩)
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd hxa' hxa
        · exact absurd hxb' hxb

/-! ## Involution after deleting one transposition -/

/-- Removing one transposition from an involution leaves an involution. -/
lemma mul_swap_involutive (α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (hαa : α a = b) (hαb : α b = a) :
    (α * Equiv.swap a b) * (α * Equiv.swap a b) = 1 := by
  ext x
  simp only [Equiv.Perm.coe_one, id_eq]
  have hαα : ∀ z, α (α z) = z := by
    intro z
    have happ := congrArg (fun f : Equiv.Perm D => f z) hα
    simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
  rcases eq_or_ne x a with rfl | hxa
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hαb, Equiv.swap_apply_right,
      hαa]
  · rcases eq_or_ne x b with rfl | hxb
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right, hαa, Equiv.swap_apply_left,
        hαb]
    · have hαxa : α x ≠ a := by
        intro h
        apply hxb
        have : x = α a := by rw [← hαα x, h]
        rw [this, hαa]
      have hαxb : α x ≠ b := by
        intro h
        apply hxa
        have : x = α b := by rw [← hαα x, h]
        rw [this, hαb]
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb,
        Equiv.swap_apply_of_ne_of_ne hαxa hαxb, hαα]

/-! ## The genus slack and its nonnegativity -/

/-- Component count of the raw pair `(σ, α)`. -/
noncomputable def numComponents (σ α : Equiv.Perm D) : ℕ :=
  _root_.numComp (dartStepRel σ α)

lemma numComponents_def (σ α : Equiv.Perm D) :
    numComponents σ α = _root_.numComp (dartStepRel σ α) := rfl

/-- Genus slack `2c - V + Ehalf - F` of a raw involution pair.  It is `≥ 0`; for a
connected fixed-point-free map this yields `χ ≤ 2`. -/
noncomputable def genusSlack (σ α : Equiv.Perm D) : ℤ :=
  2 * (numComponents σ α : ℤ) - (numCycles σ : ℤ) + (Ehalf α : ℤ)
    - (numCycles (σ * α) : ℤ)


open scoped Classical in
/-- For `α = 1` the dart relation is just `σ.SameCycle`. -/
lemma dartStepRel_one (σ : Equiv.Perm D) :
    dartStepRel σ 1 = fun x y => σ.SameCycle x y := by
  funext x y
  simp only [dartStepRel, Equiv.Perm.coe_one, id_eq, eq_iff_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact h ▸ Equiv.Perm.SameCycle.refl σ x
  · intro h; exact Or.inl h

open scoped Classical in
/-- For `α = 1` the components are exactly the `σ`-orbits. -/
lemma numComponents_one (σ : Equiv.Perm D) :
    numComponents σ 1 = numCycles σ := by
  classical
  rw [numComponents_def, dartStepRel_one]
  unfold _root_.numComp _root_.numCycles
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine Quotient.congr (Equiv.refl D) ?_
  intro x y
  simp only [Equiv.refl_apply]
  have hrel : Relation.EqvGen (fun x y => σ.SameCycle x y) x y ↔ σ.SameCycle x y :=
    Equivalence.eqvGen_iff (Equiv.Perm.SameCycle.equivalence σ)
  exact hrel

/-! ## Genus nonnegativity -/

/-- **Genus nonnegativity.** For every involution `α`, `genusSlack σ α ≥ 0`. -/
lemma genusSlack_nonneg (σ : Equiv.Perm D) :
    ∀ α : Equiv.Perm D, α * α = 1 → 0 ≤ genusSlack σ α := by
  intro α
  induction hn : (Equiv.Perm.support α).card using Nat.strong_induction_on
    generalizing α with
  | _ n ih =>
    intro hα
    rcases eq_or_ne (Equiv.Perm.support α) ∅ with hemp | hemp
    · -- base case: α = 1
      have hα1 : α = 1 := Equiv.Perm.support_eq_empty_iff.mp hemp
      subst hα1
      have hEhalf : Ehalf (1 : Equiv.Perm D) = 0 := by simp [Ehalf]
      have hmul : (σ * 1) = σ := mul_one σ
      have hcomp : numComponents σ 1 = numCycles σ := numComponents_one σ
      unfold genusSlack
      rw [hEhalf, hmul, hcomp]
      push_cast
      ring_nf
      positivity
    · -- inductive step: delete one transposition {a, b}
      obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      have hane : α a ≠ a := Equiv.Perm.mem_support.mp ha
      obtain ⟨b, hαa⟩ : ∃ b, α a = b := ⟨α a, rfl⟩
      have hab : a ≠ b := fun h => hane (by rw [hαa, ← h])
      have hαb : α b = a := by
        have happ := congrArg (fun f : Equiv.Perm D => f a) hα
        have hh : α (α a) = a := by
          simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
        rw [hαa] at hh; exact hh
      set α' := α * Equiv.swap a b with hα'def
      have hα'invol : α' * α' = 1 := mul_swap_involutive α hα hαa hαb
      have hsupp' : Equiv.Perm.support α' = (Equiv.Perm.support α) \ {a, b} :=
        support_mul_swap_of_apply α hα hab hαa
      have hcard' : (Equiv.Perm.support α').card < n := by
        rw [← hn, hsupp']
        apply Finset.card_lt_card
        refine (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr ⟨a, ha, ?_⟩
        simp
      have IHα' := ih _ hcard' α' rfl hα'invol
      have hEhalf : Ehalf α' + 1 = Ehalf α := Ehalf_mul_swap α hα hab hαa
      have hface : σ * α = (σ * α') * Equiv.swap a b := by
        rw [hα'def, mul_assoc, mul_assoc, Equiv.swap_mul_self, mul_one]
      have hrel : dartStepRel σ α = _root_.addEdge (dartStepRel σ α') a b :=
        dartStepRel_eq_addEdge σ α hα hab hαa
      have hcompEq : numComponents σ α
          = _root_.numComp (_root_.addEdge (dartStepRel σ α') a b) := by
        rw [numComponents_def, hrel]
      have hdich := _root_.numCycles_mul_swap_dichotomy (σ * α') hab
      rw [← hface] at hdich
      have hEz : (Ehalf α : ℤ) = (Ehalf α' : ℤ) + 1 := by
        have h := hEhalf; push_cast [← h]; ring
      by_cases hsame : Relation.EqvGen (dartStepRel σ α') a b
      · -- same component: numComponents unchanged
        have hC : numComponents σ α = numComponents σ α' := by
          rw [hcompEq, numComponents_def]
          exact _root_.numComp_addEdge_of_eqvGen _ hsame
        unfold genusSlack at IHα' ⊢
        rw [hC, hEz]
        rcases hdich with hd | hd
        · rw [hd]; push_cast; linarith [IHα']
        · have hF : (numCycles (σ * α) : ℤ) = (numCycles (σ * α') : ℤ) - 1 := by
            have h := hd; push_cast [← h]; ring
          rw [hF]; linarith [IHα']
      · -- different components: merge, count drops by 1; faces also merge
        have hC : numComponents σ α + 1 = numComponents σ α' := by
          rw [hcompEq, numComponents_def]
          exact _root_.numComp_addEdge_of_not_eqvGen _ hsame
        have hnsc : ¬ (σ * α').SameCycle a b := fun h =>
          hsame (eqvGen_dartStepRel_of_sameCycle_mul σ α' hα'invol h)
        have hmerge : numCycles (σ * α) + 1 = numCycles (σ * α') := by
          have h := _root_.numCycles_mul_swap_of_not_sameCycle
            (σ * α') hab hnsc
          rw [← hface] at h; exact h
        unfold genusSlack at IHα' ⊢
        have hCz : (numComponents σ α : ℤ) = (numComponents σ α' : ℤ) - 1 := by
          have h := hC; push_cast [← h]; ring
        have hFz : (numCycles (σ * α) : ℤ) = (numCycles (σ * α') : ℤ) - 1 := by
          have h := hmerge; push_cast [← h]; ring
        rw [hCz, hEz, hFz]
        linarith [IHα']

/-! ## From the genus slack to `χ ≤ 2` -/

/-- For a fixed-point-free involution, every dart is in the support. -/
lemma support_eq_univ_of_no_fixed (M : CombMap D) :
    Equiv.Perm.support M.α = Finset.univ := by
  classical
  rw [Finset.eq_univ_iff_forall]
  intro d
  rw [Equiv.Perm.mem_support]
  exact M.α_no_fixed d

/-- For the (fixed-point-free) edge involution of a `CombMap`, `Ehalf = E`. -/
lemma Ehalf_eq_E (M : CombMap D) : Ehalf M.α = M.E := by
  classical
  have h2E : 2 * M.E = Fintype.card D := two_mul_E_eq_card M
  unfold Ehalf
  rw [support_eq_univ_of_no_fixed M, Finset.card_univ]
  omega

/-- `M.dartStep` is exactly `dartStepRel M.σ M.α`. -/
lemma dartStep_eq_dartStepRel (M : CombMap D) :
    M.dartStep = dartStepRel M.σ M.α := rfl

open scoped Classical in
/-- A connected map on a nonempty dart set has exactly one component. -/
lemma numComponents_eq_one_of_connected (M : CombMap D) (hconn : M.Connected)
    (d₀ : D) : numComponents M.σ M.α = 1 := by
  classical
  rw [numComponents_def]
  unfold _root_.numComp
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨?_, ⟨Quotient.mk (_root_.compSetoid (dartStepRel M.σ M.α)) d₀⟩⟩
  -- subsingleton: any two quotient points are equal
  constructor
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a c
  apply Quotient.sound
  show Relation.EqvGen (dartStepRel M.σ M.α) a c
  rw [eqvGen_iff_reflTransGen (fun u v => dartStepRel_symm M.α_invol)]
  have h := hconn a c
  rw [dartStep_eq_dartStepRel] at h
  exact h

/-- **Euler inequality for connected combinatorial maps.** Every connected map
has Euler characteristic at most `2` (the genus-zero bound `genus ≥ 0`). -/
theorem chi_le_two_of_connected (M : CombMap D) (hconn : M.Connected) :
    M.eulerChar ≤ 2 := by
  classical
  rcases isEmpty_or_nonempty D with hD | hD
  · -- no darts: V = E = F = 0
    have hV : M.V = 0 := by simp [V, Fintype.card_eq_zero_iff]
    have hE : M.E = 0 := by simp [E, Fintype.card_eq_zero_iff]
    have hF : M.F = 0 := by simp [F, Fintype.card_eq_zero_iff]
    simp [eulerChar, hV, hE, hF]
  · obtain ⟨d₀⟩ := hD
    have hgs : 0 ≤ genusSlack M.σ M.α := genusSlack_nonneg M.σ M.α M.α_invol
    have hc : numComponents M.σ M.α = 1 :=
      numComponents_eq_one_of_connected M hconn d₀
    -- φ = σ * α
    have hφ : M.φ = M.σ * M.α := rfl
    have hVc : (M.V : ℤ) = (numCycles M.σ : ℤ) := by
      rw [V_eq_numCycles]
    have hEc : (M.E : ℤ) = (Ehalf M.α : ℤ) := by
      rw [Ehalf_eq_E]
    have hFc : (M.F : ℤ) = (numCycles (M.σ * M.α) : ℤ) := by
      rw [F_eq_numCycles, hφ]
    unfold genusSlack at hgs
    rw [hc] at hgs
    unfold eulerChar
    rw [hVc, hEc, hFc]
    push_cast at hgs ⊢
    linarith [hgs]


end CombMap

end ProofsInTheBook.PlanarMap
