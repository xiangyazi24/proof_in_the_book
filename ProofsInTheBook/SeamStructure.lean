import ProofsInTheBook.TouchCert

/-!
# The abstract seam/orbit structure of `faceCorr₂` (Chapter 35, the convergent layer)

This file builds the **symbolic, position-free characterisation** of the `faceCorr₂`
orbit structure that `TouchCert.lean` left as the single isolated topological residue
(`BankComponentCert.same_component`).  Everything in `TouchCert.lean` reduced the
F-side touch certificate to the statement "every `faceCorr₂`-cycle's darts lie in one
bank component"; but that statement was only ever *kernel-`#eval`-anchored* per concrete
cut.  Here we extract the genuinely abstract content from the **proven per-class closed
forms** of `φ'₂` (`PlanarMapCutCap2Counts.lean` / `PlanarMapCutCap2F.lean`):

* **The symbolic step action of `faceCorr₂ = phiLift⁻¹ · φ'₂` on the caps**
  (`faceCorr2_capP_cases`, `faceCorr2_capM_cases`): every cap is sent, *symbolically*,
  to a reverse cycle dart `inl (α (dart i))` (the bank-end), or to another cap of either
  sign.  Derived purely from the proven `cutCapPhi2_capP_action` / `cutCapPhi2_capM_action`
  by post-composing the explicit `phiLift⁻¹` (`phiLift⁻¹ (inl d) = inl (φ⁻¹ d)`,
  `phiLift⁻¹ (inr c) = inr c`).

* **The abstract orbit-induction discharge** (`eqvGen_of_sameCycle_step`): a fully
  position-free, reusable lemma.  Given *any* symmetric generator relation `r` on the
  `p`-orbits such that **one `q`-step stays within one `r`-component** —
  `∀ x, EqvGen r (pOrbOf p x) (pOrbOf p (q x))` — every two `q.SameCycle` points have
  `r`-reachable `p`-orbits.  Specialised to `q := faceCorr₂`, `p := phiLift`, this is
  *exactly* the orbit-induction route flagged in the task: **if every `faceCorr₂` step
  stays within one bank component, then `same_component` follows.**

* **`BankStepCert`** — the position-free certificate whose single isolated field is the
  per-step containment `step_component` (one `faceCorr₂` step ⟹ one bank component),
  together with the `2·len − 2` bank generator edges.  `BankStepCert.toBankComponentCert`
  runs `eqvGen_of_sameCycle_step` to discharge `same_component`, and the whole
  `TouchCert.lean` downstream (`cutCapMap2_F_lower`, the Jordan / chord-separation
  theorem) is re-exported from it.

## What is genuinely abstract here vs. what remains the genus-0 joint

The orbit-induction discharge and the symbolic cap action are **unconditional** — they
hold for every abstract `SimplePrimalCycle`, with no reference to the computable mirror.
This is the new symbolic layer the repository previously lacked: the residue is no longer
"each cycle's darts share a bank component" (a global, per-cut, kernel-anchored fact) but
the strictly local **per-step** fact `step_component`.

`step_component` itself still carries the one genuinely cut-dependent piece: it asserts
that the `2·len − 2` bank generator edges already connect the `phiLift`-orbit of `x` to
that of `faceCorr₂ x` for *every* `x`.  For the caps this is forced by the symbolic cap
action above (a cap's image is a bank-end or a cap, both adjacent to the cap's own
generator-edge endpoint); for the bank-end / cycle darts it is the genus-0 seam incidence
`phiLift vᵢ = u_{i+1}` (`PlanarMapSeamSpec.lean`), which `SimplePrimalCycle` does not
constrain abstractly (the forward darts' `σ`-arrangement is embedding-dependent).  So
`step_component` is the honest minimal joint — strictly smaller than the prior
`same_component` (one step, not a whole orbit), and it is isolated as the single cert
field, not faked.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function

namespace ProofsInTheBook

namespace SeamStructure

open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.PlanarMap.SeamChain

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## The abstract orbit-induction reachability framework

A reusable, position-free fact about any two permutations `p`, `q` of a finite type and
any symmetric relation `r` on the `p`-orbits: if one `q`-step always stays within one
`r`-component of the `p`-orbits, then `q.SameCycle` points have `r`-reachable
`p`-orbits.  This is the engine that turns "every `faceCorr₂` step stays in one bank
component" into "every `faceCorr₂`-cycle's darts lie in one bank component". -/

/-- **One `q`-step stays within one `r`-component ⟹ every `q`-power does.**  If for every
`x` the `p`-orbit of `q x` is `EqvGen r`-reachable from that of `x`, then so is the
`p`-orbit of `q^[n] x` for every `n`. -/
lemma eqvGen_of_iterate_step {p q : Equiv.Perm X}
    {r : POrb p → POrb p → Prop}
    (hstep : ∀ x, Relation.EqvGen r (pOrbOf p x) (pOrbOf p (q x))) :
    ∀ (n : ℕ) (x : X),
      Relation.EqvGen r (pOrbOf p x) (pOrbOf p ((q ^ n) x)) := by
  intro n
  induction n with
  | zero => intro x; simpa using Relation.EqvGen.refl (pOrbOf p x)
  | succ k ih =>
      intro x
      have h1 : Relation.EqvGen r (pOrbOf p x) (pOrbOf p ((q ^ k) x)) := ih x
      have h2 : Relation.EqvGen r (pOrbOf p ((q ^ k) x))
          (pOrbOf p (q ((q ^ k) x))) := hstep ((q ^ k) x)
      have hpow : (q ^ (k + 1)) x = q ((q ^ k) x) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [hpow]
      exact Relation.EqvGen.trans _ _ _ h1 h2

/-- **The orbit-induction discharge.**  If one `q`-step always stays within one
`r`-component of the `p`-orbits, then any two `q.SameCycle` points have `EqvGen r`-reachable
`p`-orbits.  Position-free; the abstract engine behind `same_component`. -/
theorem eqvGen_of_sameCycle_step {p q : Equiv.Perm X}
    {r : POrb p → POrb p → Prop}
    (hstep : ∀ x, Relation.EqvGen r (pOrbOf p x) (pOrbOf p (q x)))
    {x y : X} (hxy : q.SameCycle x y) :
    Relation.EqvGen r (pOrbOf p x) (pOrbOf p y) := by
  obtain ⟨i, hi, hxy'⟩ := hxy.exists_pow_eq'
  rw [← hxy']
  exact eqvGen_of_iterate_step hstep i x

/-! ## The cycle-decomposition lists with their `SameCycle` certificate

To run `eqvGen_of_sameCycle_step` against `faceCorr₂` we need, for each cycle list `L`,
that any two of its darts are `faceCorr₂.SameCycle`.  We strengthen the nodup
cycle-decomposition existence (`TouchCert.exists_cycleListProd_nodup`) to also carry this
`SameCycle` clause, via `Equiv.Perm.toList` (`mem_toList_iff`) and a disjoint-`SameCycle`
bridge for the disjoint-product induction step. -/

/-- **Disjoint-`SameCycle` bridge.**  If `σ`, `τ` are disjoint and `σ.SameCycle x y`, then
`(σ * τ).SameCycle x y`: on `σ`'s support `τ` is the identity, so the `σ`-power transports
`x` to `y` under `σ * τ` as well. -/
lemma sameCycle_mul_left_of_disjoint {σ τ : Equiv.Perm X} (h : Equiv.Perm.Disjoint σ τ)
    {x y : X} (hxy : σ.SameCycle x y) : (σ * τ).SameCycle x y := by
  obtain ⟨i, hi⟩ := hxy
  rcases (Equiv.Perm.disjoint_iff_eq_or_eq.mp h x) with hx | hx
  · -- σ x = x ⟹ (σ^i) x = x = y, so x = y
    have : (σ ^ i) x = x := Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx i
    rw [this] at hi
    exact hi ▸ SameCycle.refl _ x
  · -- τ x = x ⟹ τ^i x = x, and σ*τ commute
    refine ⟨i, ?_⟩
    have hcomm : (σ * τ) ^ i = σ ^ i * τ ^ i := h.commute.mul_zpow i
    rw [hcomm, Equiv.Perm.mul_apply,
      Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx i, hi]

/-- Symmetric form: `(σ * τ).SameCycle x y` from `τ.SameCycle x y`. -/
lemma sameCycle_mul_right_of_disjoint {σ τ : Equiv.Perm X} (h : Equiv.Perm.Disjoint σ τ)
    {x y : X} (hxy : τ.SameCycle x y) : (σ * τ).SameCycle x y := by
  rw [h.commute.eq]
  exact sameCycle_mul_left_of_disjoint h.symm hxy

/-- **Every finite permutation is a `cycleListProd` of nodup lists of length `≥ 2` whose
members are pairwise `SameCycle`.**  Strengthens `exists_cycleListProd_nodup` with the
`mem_sameCycle` clause needed by the orbit-induction discharge. -/
theorem exists_cycleListProd_sameCycle (q : Equiv.Perm X) :
    ∃ Ls : List (List X),
      (∀ L ∈ Ls, 2 ≤ L.length) ∧ (∀ L ∈ Ls, L.Nodup) ∧
      (∀ L ∈ Ls, ∀ x ∈ L, ∀ y ∈ L, q.SameCycle x y) ∧
      cycleListProd Ls = q := by
  classical
  induction q using Equiv.Perm.cycle_induction_on with
  | base_one => exact ⟨[], by simp, by simp, by simp, rfl⟩
  | base_cycles σ hσ =>
      obtain ⟨x, hx, -⟩ := id hσ
      have hxs : x ∈ σ.support := by rw [Equiv.Perm.mem_support]; exact hx
      refine ⟨[Equiv.Perm.toList σ x], ?_, ?_, ?_, ?_⟩
      · intro L hL
        simp only [List.mem_singleton] at hL; subst hL
        exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hxs
      · intro L hL
        simp only [List.mem_singleton] at hL; subst hL
        exact Equiv.Perm.nodup_toList σ x
      · intro L hL a ha b hb
        simp only [List.mem_singleton] at hL; subst hL
        have hax := (Equiv.Perm.mem_toList_iff.mp ha).1   -- SameCycle σ x a
        have hbx := (Equiv.Perm.mem_toList_iff.mp hb).1   -- SameCycle σ x b
        exact hax.symm.trans hbx
      · simp only [cycleListProd, mul_one, cycleOfList]
        rw [Equiv.Perm.formPerm_toList, Equiv.Perm.IsCycle.cycleOf_eq hσ hx]
  | induction_disjoint σ τ hdisj hσ hστ hτ =>
      obtain ⟨Lσ, hLσpos, hLσnd, hLσsc, hLσ⟩ := hστ
      obtain ⟨Lτ, hLτpos, hLτnd, hLτsc, hLτ⟩ := hτ
      refine ⟨Lσ ++ Lτ, ?_, ?_, ?_, ?_⟩
      · intro L hL
        rcases List.mem_append.mp hL with h | h
        · exact hLσpos L h
        · exact hLτpos L h
      · intro L hL
        rcases List.mem_append.mp hL with h | h
        · exact hLσnd L h
        · exact hLτnd L h
      · intro L hL a ha b hb
        rcases List.mem_append.mp hL with h | h
        · -- L is a σ-cycle list: SameCycle σ a b ⟹ SameCycle (σ*τ) a b
          exact sameCycle_mul_left_of_disjoint hdisj (hLσsc L h a ha b hb)
        · -- L is a τ-cycle list: SameCycle τ a b ⟹ SameCycle (σ*τ) a b
          exact sameCycle_mul_right_of_disjoint hdisj (hLτsc L h a ha b hb)
      · rw [cycleListProd_append, hLσ, hLτ]

end SeamStructure

/-! ## The symbolic per-class action of `faceCorr₂`

`faceCorr₂ = phiLift⁻¹ · φ'₂` (`PlanarMapCutCap2FWalk.faceCorr2`).  `phiLift = φ ⊕ 1`,
so `phiLift⁻¹` is `φ⁻¹ ⊕ 1`: it fixes the caps and sends `inl d ↦ inl (φ⁻¹ d)`.  Composing
with the proven closed forms of `φ'₂` gives the symbolic step action of `faceCorr₂` on the
caps. -/

namespace PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount

/-- `phiLift⁻¹` fixes the `+`-caps (`phiLift` does, so does its inverse). -/
@[simp] lemma phiLift_symm_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.phiLift⁻¹ (C.capP i) = C.capP i := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, phiLift_capP]

/-- `phiLift⁻¹` fixes the `−`-caps. -/
@[simp] lemma phiLift_symm_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.phiLift⁻¹ (C.capM i) = C.capM i := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, phiLift_capM]

/-- `phiLift⁻¹` fixes every `inr`-cap. -/
@[simp] lemma phiLift_symm_inr (C : SimplePrimalCycle M) (c : Fin C.len ⊕ Fin C.len) :
    C.phiLift⁻¹ (Sum.inr c) = Sum.inr c := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, phiLift_inr]

/-- `phiLift⁻¹` on an `inl` dart is `inl (φ⁻¹ d)`. -/
@[simp] lemma phiLift_symm_inl (C : SimplePrimalCycle M) (d : D) :
    C.phiLift⁻¹ (Sum.inl d) = Sum.inl (M.φ⁻¹ d) := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, phiLift_inl, Equiv.Perm.inv_def,
    M.φ.apply_symm_apply]

/-- `faceCorr₂ x = phiLift⁻¹ (φ'₂ x)`, the working unfolding. -/
lemma faceCorr2_apply (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.faceCorr2 x = C.phiLift⁻¹ ((C.cutCapMap2).φ x) := by
  rw [faceCorr2, Equiv.Perm.mul_apply]

/-- `α (α d) = d` (involution, in applied form). -/
lemma alpha_alpha (C : SimplePrimalCycle M) (d : D) : M.α (M.α d) = d := by
  rw [show M.α (M.α d) = (M.α * M.α) d from rfl, M.α_invol, Equiv.Perm.one_apply]

/-- `φ⁻¹ (σ d) = α d` (since `φ = σ α` and `α` is an involution). -/
lemma phi_inv_sigma (C : SimplePrimalCycle M) (d : D) :
    M.φ⁻¹ (M.σ d) = M.α d := by
  have hφ : M.φ (M.α d) = M.σ d := by
    rw [CombMap.φ, Equiv.Perm.mul_apply, C.alpha_alpha]
  rw [← hφ, Equiv.Perm.inv_def, M.φ.symm_apply_apply]

/-- **The symbolic `+`-cap action of `faceCorr₂`** (three-way).  `faceCorr₂ (capP i)` is
the reverse cycle dart `inl (α (dart i))` (the `−`-bank end), or the previous `+`-cap
`capP (prevIdx j)`, or the `−`-cap `capM j` — read off from the proven `φ'₂` cap action by
applying `phiLift⁻¹` (which fixes caps and sends `inl (σ (dart i)) ↦ inl (α (dart i))`). -/
theorem faceCorr2_capP_cases (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.faceCorr2 (C.capP i) = Sum.inl (M.α (C.dart i)) ∨
      (∃ j, M.σ (C.dart i) = C.pDart j ∧
        C.faceCorr2 (C.capP i) = C.capP (C.prevIdx j)) ∨
      (∃ j, M.σ (C.dart i) = C.qDart j ∧
        C.faceCorr2 (C.capP i) = C.capM j) := by
  rw [faceCorr2_apply]
  rcases C.cutCapPhi2_capP_cases i with h | ⟨j, hj, h⟩ | ⟨j, hj, h⟩
  · left
    rw [h, phiLift_symm_inl, C.phi_inv_sigma]
  · right; left
    exact ⟨j, hj, by rw [h]; rfl⟩
  · right; right
    exact ⟨j, hj, by rw [h]; rfl⟩

/-- **The symbolic `−`-cap action of `faceCorr₂`** (three-way), analogous to the `+`-cap:
`faceCorr₂ (capM i)` is the forward dart `inl (α (α (dart i))) = inl (dart i)`, or a `+`-cap
`capP (prevIdx j)`, or a `−`-cap `capM j`. -/
theorem faceCorr2_capM_cases (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.faceCorr2 (C.capM i) = Sum.inl (C.dart i) ∨
      (∃ j, M.σ (M.α (C.dart i)) = C.pDart j ∧
        C.faceCorr2 (C.capM i) = C.capP (C.prevIdx j)) ∨
      (∃ j, M.σ (M.α (C.dart i)) = C.qDart j ∧
        C.faceCorr2 (C.capM i) = C.capM j) := by
  rw [faceCorr2_apply]
  rcases C.cutCapPhi2_capM_cases i with h | ⟨j, hj, h⟩ | ⟨j, hj, h⟩
  · left
    rw [h, phiLift_symm_inl, C.phi_inv_sigma, C.alpha_alpha]
  · right; left
    exact ⟨j, hj, by rw [h]; rfl⟩
  · right; right
    exact ⟨j, hj, by rw [h]; rfl⟩

/-! ## The per-step bank certificate and the `same_component` discharge

`BankStepCert` packages the position-free residue at its **smallest** form: the cycle
lists of `faceCorr₂` (with their nodup / `SameCycle` data, all provable by
`SeamStructure.exists_cycleListProd_sameCycle`), the `2·len − 2` bank generator edges,
and the **single isolated local field** `step_component` — *one* `faceCorr₂` step keeps
the `phiLift`-orbit within one bank component.  From it, `same_component` (an orbit-wide
statement) is discharged by `SeamStructure.eqvGen_of_sameCycle_step`: two darts of one
cycle list are `faceCorr₂.SameCycle` (the `mem_sameCycle` data), and orbit-induction
threads the per-step containment along the whole cycle. -/

open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord

/-- **The per-step bank certificate for `faceCorr₂`.**  The strictly local residue: the
cycle-decomposition data (always available) plus the single isolated topological field
`step_component` — every `faceCorr₂` step stays within one bank component. -/
structure BankStepCert (C : SimplePrimalCycle M) where
  /-- The cycle-decomposition support lists of `faceCorr₂`. -/
  Ls : List (List C.CutDart)
  /-- Each cycle list has length `≥ 2`. -/
  Ls_len : ∀ L ∈ Ls, 2 ≤ L.length
  /-- Each cycle list is nodup. -/
  Ls_nodup : ∀ L ∈ Ls, L.Nodup
  /-- Any two darts of one cycle list are `faceCorr₂.SameCycle`. -/
  Ls_sameCycle : ∀ L ∈ Ls, ∀ x ∈ L, ∀ y ∈ L, C.faceCorr2.SameCycle x y
  /-- The cycle-decomposition product reconstructs `faceCorr₂`. -/
  factor : cycleListProd Ls = C.faceCorr2
  /-- The `2·len − 2` bank generator edges on `phiLift`-orbits. -/
  gen : Fin (2 * C.len - 2) → POrb C.phiLift × POrb C.phiLift
  /-- **The single isolated local residue.**  One `faceCorr₂` step keeps the
  `phiLift`-orbit within one bank component: for every dart `x`, the `phiLift`-orbit of
  `faceCorr₂ x` is `gen`-reachable from that of `x`. -/
  step_component : ∀ x : C.CutDart,
    Relation.EqvGen (genRel gen) (pOrbOf C.phiLift x) (pOrbOf C.phiLift (C.faceCorr2 x))

/-- **The orbit-wide bank-component certificate from the per-step one.**  `same_component`
follows from `step_component` by `SeamStructure.eqvGen_of_sameCycle_step`: each cycle list's
darts are `faceCorr₂.SameCycle`, and the per-step containment threads along the orbit. -/
def BankStepCert.toBankComponentCert {C : SimplePrimalCycle M}
    (cert : C.BankStepCert) : C.BankComponentCert where
  Ls := cert.Ls
  Ls_len := cert.Ls_len
  Ls_nodup := cert.Ls_nodup
  factor := cert.factor
  gen := cert.gen
  same_component := by
    intro L hL x hx y hy
    exact ProofsInTheBook.SeamStructure.eqvGen_of_sameCycle_step
      cert.step_component (cert.Ls_sameCycle L hL x hx y hy)

/-- **The corrected face-count lower bound from a per-step bank certificate**
(`(cutCapMap2).F ≥ M.F + 2`), through `toBankComponentCert` and the `TouchCert.lean`
downstream. -/
theorem cutCapMap2_F_lower_of_stepCert (C : SimplePrimalCycle M)
    (cert : C.BankStepCert) :
    (C.cutCapMap2).F ≥ M.F + 2 :=
  C.cutCapMap2_F_lower_of_bankCert cert.toBankComponentCert

/-- **The lower-bound Jordan / chord-separation theorem from a per-step bank certificate.**
No cut edge of a simple primal cycle on a sphere is straddled by a cycle-avoiding dual
path. -/
theorem jordan_simple_cycle2_lower_of_stepCert (C : SimplePrimalCycle M)
    (cert : C.BankStepCert)
    (hchi : M.eulerChar = 2)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  C.jordan_simple_cycle2_lower_of_bankCert cert.toBankComponentCert hchi hconn i

end SimplePrimalCycle

end CombMap

end PlanarMap

/-! ## Non-vacuity: the orbit-induction engine fires non-degenerately

The genuinely topological residue (`step_component`) cannot be exhibited unconditionally —
the repository carries no concrete abstract `SimplePrimalCycle` instance (see the file
header and `TouchCert.lean`).  We instead exercise the **abstract orbit-induction engine**
on a concrete permutation, ruling out the "vacuous reduction" failure mode for this layer:

* `eqvGen_of_sameCycle_step` is run on `q := (0 1 2)` of `Fin 3`, with `p := 1` (so every
  `pOrbOf p` is a singleton orbit and the generator relation is the full step graph).  The
  two non-trivially-`SameCycle` elements `0` and `2` of the `3`-cycle land in one
  `EqvGen`-component, confirming the engine threads a genuine multi-step orbit.

* `exists_cycleListProd_sameCycle` is exercised on `(0 1 2)`: it returns a cycle list whose
  members are pairwise `SameCycle`, the `Ls_sameCycle` data the discharge consumes. -/

namespace SeamStructure

open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.PlanarMap.SeamChain

/-- The strengthened cycle-decomposition existence fires on `(0 1 2)` of `Fin 3`, carrying
the `SameCycle` clause. -/
example : ∃ Ls : List (List (Fin 3)),
    (∀ L ∈ Ls, 2 ≤ L.length) ∧ (∀ L ∈ Ls, L.Nodup) ∧
    (∀ L ∈ Ls, ∀ x ∈ L, ∀ y ∈ L, (cycleOfList ([0, 1, 2] : List (Fin 3))).SameCycle x y) ∧
    cycleListProd Ls = cycleOfList ([0, 1, 2] : List (Fin 3)) :=
  exists_cycleListProd_sameCycle (cycleOfList ([0, 1, 2] : List (Fin 3)))

/-- The orbit-induction engine threads a genuine multi-step orbit: with the per-step graph
on the singleton `1`-orbits of `Fin 3`, the `SameCycle` endpoints `0`, `2` of `(0 1 2)` are
`EqvGen`-reachable.  Confirms `eqvGen_of_sameCycle_step` is not vacuous. -/
example :
    let q : Equiv.Perm (Fin 3) := cycleOfList ([0, 1, 2] : List (Fin 3))
    let r : POrb (1 : Equiv.Perm (Fin 3)) → POrb (1 : Equiv.Perm (Fin 3)) → Prop :=
      fun u v => ∃ x : Fin 3, u = pOrbOf 1 x ∧ v = pOrbOf 1 (q x)
    q.SameCycle 0 2 →
      Relation.EqvGen r (pOrbOf (1 : Equiv.Perm (Fin 3)) 0) (pOrbOf 1 2) := by
  intro q r hsc
  exact eqvGen_of_sameCycle_step (q := q) (p := 1) (r := r)
    (fun x => Relation.EqvGen.rel _ _ ⟨x, rfl, rfl⟩) hsc

end SeamStructure

end ProofsInTheBook

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.SeamStructure.eqvGen_of_sameCycle_step
#print axioms ProofsInTheBook.SeamStructure.exists_cycleListProd_sameCycle
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.faceCorr2_capP_cases
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.faceCorr2_capM_cases
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.BankStepCert.toBankComponentCert
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.cutCapMap2_F_lower_of_stepCert
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.jordan_simple_cycle2_lower_of_stepCert
