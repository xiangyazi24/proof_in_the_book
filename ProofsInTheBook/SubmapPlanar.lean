import ProofsInTheBook.ChordDisk

/-!
# Sub-map planarity / genus monotonicity for combinatorial maps (Chapter 35, the no-handle inequality)

This file supplies the single remaining fact of Chapter 35's Five Color Theorem chord branch:
the reverse Euler inequality `2 ≤ eulerChar(keptSide)` — *the kept side of a chord split has
no handle (genus 0)* — which `ChordDisk.lean` isolated as the `≥ 2` half of `KeptSideIsDisk`.

## The structural genus-0 certificate (NOT counting)

The kept side of a chord split is obtained from the genus-0 sphere map `M` (`eulerChar M = 2`)
by **deleting darts** (the darts on the other side of the chord) and re-splicing the rotation
(`filteredRotation`).  The independent genus-0 certificate is the *monotonicity of the genus
slack under edge deletion*, run against `M`'s own `eulerChar = 2`:

* The repository's `genusSlack σ α := 2·c − V + Ehalf − F` (`PlanarMapEulerInequality`) is
  `≥ 0` for **every** involution pair (`genusSlack_nonneg`), giving the free `χ ≤ 2` half.
* **`genusSlack_remove_le`** (this file) — deleting one edge (replacing `α` by
  `α * swap a b`, which fixes `a, b`) does **not increase** the slack:
  `genusSlack σ (α * swap a b) ≤ genusSlack σ α`.  This is the structural core, proved from
  the repository's transposition cycle-count dichotomy + the component `addEdge` dichotomy,
  exactly the bookkeeping of `genusSlack_nonneg`'s inductive step read as an inequality.
* **`genusSlack_le_of_subInvolution`** — iterating the single-edge step: any sub-involution
  obtained by deleting a set of edges from `α` has slack `≤ genusSlack σ α`.
* **`genusSlack_sphere_eq_zero`** — a genus-0 connected map (`IsSphereMap`, `eulerChar = 2`)
  has `genusSlack σ α = 0` exactly (`c = 1`, `χ = 2 ⟹ slack = 0`).

Composing: a sub-involution of a genus-0 `M` has `0 ≤ genusSlack ≤ 0`, hence `genusSlack = 0`,
i.e. `χ_raw = 2·c`.  For a connected sub-map (`c = 1`) this gives `χ = 2`: **no handle**.

This is genuinely genus-0-*essential* (numerically: a genus-1 base produces sub-maps with
`χ < 2`), so it is **not** free counting — the same conclusion the `CutFaceLabel` kernel
campaign reached for the per-side count is honoured here: the value comes from `M`'s genus 0
flowing through the *monotone* slack, not from an orbit-uniform face label (which does not
exist, kernel-decided).

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.SubmapPlanar

open Equiv
open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]

/-! ## Section 1.  Single-edge-removal monotonicity of the genus slack

Removing one edge `{a, b}` from an involution `α` (replacing `α` by `α * swap a b`, which then
fixes `a` and `b`) does not increase `genusSlack`.  We prove it directly with the same case
analysis as `genusSlack_nonneg`'s step, but as the inequality `slack (removed) ≤ slack`. -/

/-- **Single-edge removal does not increase the genus slack.**  If `α a = b` with `a ≠ b`
(so `{a, b}` is an edge of the involution `α`), then deleting it
(`α' = α * swap a b`, which fixes `a, b`) gives `genusSlack σ α' ≤ genusSlack σ α`. -/
theorem genusSlack_remove_le (σ α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (hab : a ≠ b) (hαa : α a = b) :
    genusSlack σ (α * Equiv.swap a b) ≤ genusSlack σ α := by
  classical
  have hαb : α b = a := by
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    have hh : α (α a) = a := by simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
    rw [hαa] at hh; exact hh
  set α' := α * Equiv.swap a b with hα'def
  have hα'invol : α' * α' = 1 := mul_swap_involutive α hα hαa hαb
  -- Edge count: `Ehalf α' + 1 = Ehalf α`.
  have hEhalf : Ehalf α' + 1 = Ehalf α := Ehalf_mul_swap α hα hab hαa
  have hEz : (Ehalf α : ℤ) = (Ehalf α' : ℤ) + 1 := by
    have h := hEhalf; push_cast [← h]; ring
  -- Face permutation: `σ * α = (σ * α') * swap a b`.
  have hface : σ * α = (σ * α') * Equiv.swap a b := by
    rw [hα'def, mul_assoc, mul_assoc, Equiv.swap_mul_self, mul_one]
  -- Component relation via `addEdge`.
  have hrel : dartStepRel σ α = _root_.addEdge (dartStepRel σ α') a b :=
    dartStepRel_eq_addEdge σ α hα hab hαa
  have hcompEq : numComponents σ α
      = _root_.numComp (_root_.addEdge (dartStepRel σ α') a b) := by
    rw [numComponents_def, hrel]
  -- Face cycle-count dichotomy.
  have hdich := _root_.numCycles_mul_swap_dichotomy (σ * α') hab
  rw [← hface] at hdich
  by_cases hsame : Relation.EqvGen (dartStepRel σ α') a b
  · -- Same component: `c` unchanged; `F` either unchanged (slack +1) or drops (slack +2).
    have hC : numComponents σ α = numComponents σ α' := by
      rw [hcompEq, numComponents_def]
      exact _root_.numComp_addEdge_of_eqvGen _ hsame
    unfold genusSlack at *
    rw [hC, hEz]
    rcases hdich with hd | hd
    · rw [hd]; push_cast; linarith
    · have hF : (numCycles (σ * α) : ℤ) = (numCycles (σ * α') : ℤ) - 1 := by
        have h := hd; push_cast [← h]; ring
      rw [hF]; linarith
  · -- Different components: `c` drops by one; faces merge (`F` drops by one); slack unchanged.
    have hC : numComponents σ α + 1 = numComponents σ α' := by
      rw [hcompEq, numComponents_def]
      exact _root_.numComp_addEdge_of_not_eqvGen _ hsame
    have hnsc : ¬ (σ * α').SameCycle a b := fun h =>
      hsame (eqvGen_dartStepRel_of_sameCycle_mul σ α' hα'invol h)
    have hmerge : numCycles (σ * α) + 1 = numCycles (σ * α') := by
      have h := _root_.numCycles_mul_swap_of_not_sameCycle (σ * α') hab hnsc
      rw [← hface] at h; exact h
    unfold genusSlack at *
    have hCz : (numComponents σ α : ℤ) = (numComponents σ α' : ℤ) - 1 := by
      have h := hC; push_cast [← h]; ring
    have hFz : (numCycles (σ * α) : ℤ) = (numCycles (σ * α') : ℤ) - 1 := by
      have h := hmerge; push_cast [← h]; ring
    rw [hCz, hEz, hFz]; linarith

/-! ## Section 2.  Iterated monotonicity: a sub-involution has no larger slack

`α'` is a **sub-involution** of `α` (an edge-deletion sub-map) if it is an involution whose
edges form a subset of `α`'s edges, i.e. `α'` agrees with `α` wherever `α'` moves a dart.
We iterate `genusSlack_remove_le` to conclude `genusSlack σ α' ≤ genusSlack σ α`. -/

/-- `α'` is an **edge-deletion sub-involution** of `α`: an involution that agrees with `α` on
its own support (so its edge set is a subset of `α`'s edge set). -/
def SubInvolution (α α' : Equiv.Perm D) : Prop :=
  α' * α' = 1 ∧ ∀ x, α' x ≠ x → α' x = α x

/-- A sub-involution's support is contained in `α`'s support. -/
lemma SubInvolution.support_subset {α α' : Equiv.Perm D} (h : SubInvolution α α') :
    Equiv.Perm.support α' ⊆ Equiv.Perm.support α := by
  classical
  intro x hx
  rw [Equiv.Perm.mem_support] at hx ⊢
  rw [h.2 x hx] at hx
  exact hx

/-- **Removing one edge from `α` keeps `α'` a sub-involution** when that edge is disjoint from
`α'`'s support.  This is the inductive step bridge. -/
lemma SubInvolution.remove_edge {α α' : Equiv.Perm D} (hα : α * α = 1)
    (h : SubInvolution α α') {a b : D} (hab : a ≠ b) (hαa : α a = b)
    (ha : a ∉ Equiv.Perm.support α') (hb : b ∉ Equiv.Perm.support α') :
    SubInvolution (α * Equiv.swap a b) α' := by
  classical
  have hαb : α b = a := by
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    have hh : α (α a) = a := by simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
    rw [hαa] at hh; exact hh
  rw [Equiv.Perm.notMem_support] at ha hb
  refine ⟨h.1, ?_⟩
  intro x hx
  have hax : x ≠ a := by rintro rfl; exact hx ha
  have hbx : x ≠ b := by rintro rfl; exact hx hb
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hax hbx]
  exact h.2 x hx

/-- **Iterated monotonicity.**  Every edge-deletion sub-involution `α'` of an involution `α`
has genus slack at most that of `α`.  Proved by strong induction on the number of deleted
edges (`(support α).card`), peeling one `α`-edge disjoint from `support α'` at a time. -/
theorem genusSlack_le_of_subInvolution (σ : Equiv.Perm D) :
    ∀ α : Equiv.Perm D, α * α = 1 → ∀ α' : Equiv.Perm D, SubInvolution α α' →
      genusSlack σ α' ≤ genusSlack σ α := by
  intro α
  induction hn : (Equiv.Perm.support α).card using Nat.strong_induction_on
    generalizing α with
  | _ n ih =>
    intro hα α' hsub
    classical
    -- Either `α'` already equals `α` (no edge left to delete) or there is an `α`-edge
    -- disjoint from `support α'`.
    by_cases hdone : Equiv.Perm.support α ⊆ Equiv.Perm.support α'
    · -- supports equal ⇒ `α = α'` ⇒ slacks equal.
      have hsupp_eq : Equiv.Perm.support α = Equiv.Perm.support α' :=
        le_antisymm hdone hsub.support_subset
      have heq : α = α' := by
        ext x
        by_cases hx : x ∈ Equiv.Perm.support α
        · have hx' : x ∈ Equiv.Perm.support α' := hsupp_eq ▸ hx
          rw [Equiv.Perm.mem_support] at hx'
          exact (hsub.2 x hx').symm
        · have hx' : x ∉ Equiv.Perm.support α' := hsupp_eq ▸ hx
          rw [Equiv.Perm.notMem_support] at hx hx'
          rw [hx, hx']
      rw [heq]
    · -- there is `a ∈ support α \ support α'`; let `b = α a` (also outside `support α'`).
      obtain ⟨a, ha_in, ha_out⟩ := Finset.not_subset.mp hdone
      have hane : α a ≠ a := Equiv.Perm.mem_support.mp ha_in
      set b := α a with hbdef
      have hab : a ≠ b := fun h => hane h.symm
      have hαa : α a = b := hbdef.symm
      have hαb : α b = a := by
        have happ := congrArg (fun f : Equiv.Perm D => f a) hα
        have hh : α (α a) = a := by simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
        rw [hαa] at hh; exact hh
      have hb_in : b ∈ Equiv.Perm.support α := by
        rw [Equiv.Perm.mem_support, hαb]; exact hab
      -- `b` is also outside `support α'` (else `α' b = b'` would force the edge `{a,b}` into `α'`).
      have hb_out : b ∉ Equiv.Perm.support α' := by
        intro hb'
        rw [Equiv.Perm.mem_support] at hb'
        have := hsub.2 b hb'
        rw [hαb] at this
        -- `α' b = a`, so `α' a = b ≠ a` by the involution, putting `a` in `support α'`.
        have hα'a : α' a = b := by
          have happ := congrArg (fun f : Equiv.Perm D => f b) hsub.1
          have hh : α' (α' b) = b := by
            simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
          rw [this] at hh; exact hh
        exact ha_out (Equiv.Perm.mem_support.mpr (by rw [hα'a]; exact hab.symm))
      -- Delete `{a, b}` from `α`.
      set α'' := α * Equiv.swap a b with hα''def
      have hα''invol : α'' * α'' = 1 := mul_swap_involutive α hα hαa hαb
      have hsub'' : SubInvolution α'' α' :=
        hsub.remove_edge hα hab hαa ha_out hb_out
      have hsupp'' : Equiv.Perm.support α'' = (Equiv.Perm.support α) \ {a, b} :=
        support_mul_swap_of_apply α hα hab hαa
      have hcard'' : (Equiv.Perm.support α'').card < n := by
        rw [← hn, hsupp'']
        apply Finset.card_lt_card
        refine (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr ⟨a, ha_in, ?_⟩
        simp
      -- Recurse: slack α' ≤ slack α'' ≤ slack α.
      have hstep : genusSlack σ α'' ≤ genusSlack σ α :=
        genusSlack_remove_le σ α hα hab hαa
      have hrec : genusSlack σ α' ≤ genusSlack σ α'' :=
        ih _ hcard'' α'' rfl hα''invol α' hsub''
      exact le_trans hrec hstep

/-! ## Section 3.  The genus slack of a sphere map is exactly zero

A connected genus-0 map (`IsSphereMap`: `eulerChar = 2`) on a nonempty dart set has exactly
one `(σ, α)`-component, so its genus slack `2·1 − V + E − F = 2 − eulerChar = 0`. -/

/-- **A sphere map has genus slack zero.**  For a connected map with `eulerChar = 2` and at
least one dart, `genusSlack M.σ M.α = 0` (`c = 1`, `χ = 2`). -/
theorem genusSlack_sphere_eq_zero (M : CombMap D) (hsphere : M.IsSphereMap) (d₀ : D) :
    genusSlack M.σ M.α = 0 := by
  classical
  have hc : numComponents M.σ M.α = 1 :=
    numComponents_eq_one_of_connected M hsphere.1 d₀
  have hVc : (M.V : ℤ) = (numCycles M.σ : ℤ) := by rw [V_eq_numCycles]
  have hEc : (M.E : ℤ) = (Ehalf M.α : ℤ) := by rw [Ehalf_eq_E]
  have hFc : (M.F : ℤ) = (numCycles (M.σ * M.α) : ℤ) := by
    rw [F_eq_numCycles]; rfl
  have heuler : (M.V : ℤ) - (M.E : ℤ) + (M.F : ℤ) = 2 := hsphere.2
  unfold genusSlack
  rw [hc]
  rw [hVc, hEc, hFc] at heuler
  push_cast
  linarith

/-! ## Section 4.  Orbit-count splitting under dart deletion

For a permutation `p : Perm D` and a deleted set `S`, the kept subtype carries the deleted
permutation `deleteSet p S` (the filtered rotation), whose `SameCycle` on kept darts coincides
with `p.SameCycle` (`Equiv.Perm.sameCycle_deleteSet_iff`).  Every `p`-orbit either contains a
kept dart (and corresponds to a unique `deleteSet`-orbit) or is entirely deleted.  Hence

  `numCycles p = numCycles (deleteSet p S) + #(p-orbits ⊆ S)`.

We prove the cardinality identity via an explicit equiv of orbit quotients.  This is the
single workhorse used for both the vertex (`σ`) and face (`σα`) counts. -/

section OrbitSplit

variable (p : Equiv.Perm D) (S : Finset D)

open scoped Classical

/-- A `p`-orbit is **deleted** if all its darts lie in `S`. -/
def DeletedOrbit (q : Quotient (cycleSetoid p)) : Prop :=
  ∀ x : D, Quotient.mk (cycleSetoid p) x = q → x ∈ S

/-- The kept subtype's filtered orbit quotient, as `p`-orbits via the `SameCycle` coincidence. -/
noncomputable def keptToFull :
    Quotient (cycleSetoid (Equiv.Perm.deleteSet p S)) → Quotient (cycleSetoid p) :=
  Quotient.lift (fun x => Quotient.mk (cycleSetoid p) (x.1 : D)) (by
    intro x y hxy
    apply Quotient.sound
    exact (Equiv.Perm.sameCycle_deleteSet_iff p S x y).1 hxy)

@[simp] lemma keptToFull_mk (x : {d : D // d ∉ S}) :
    keptToFull p S (Quotient.mk (cycleSetoid (Equiv.Perm.deleteSet p S)) x)
      = Quotient.mk (cycleSetoid p) (x.1 : D) := rfl

/-- `keptToFull` is injective: two filtered orbits mapping to the same `p`-orbit are equal. -/
lemma keptToFull_injective : Function.Injective (keptToFull p S) := by
  classical
  intro a b hab
  refine Quotient.inductionOn₂ a b (fun x y hxy => ?_) hab
  simp only [keptToFull_mk] at hxy
  apply Quotient.sound
  have hsc : p.SameCycle x.1 y.1 := Quotient.exact hxy
  exact (Equiv.Perm.sameCycle_deleteSet_iff p S x y).2 hsc

/-- The image of `keptToFull` is exactly the non-deleted `p`-orbits. -/
lemma keptToFull_range_iff (q : Quotient (cycleSetoid p)) :
    (∃ a, keptToFull p S a = q) ↔ ¬ DeletedOrbit p S q := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    refine Quotient.inductionOn a (fun x => ?_)
    simp only [keptToFull_mk, DeletedOrbit, not_forall]
    exact ⟨x.1, rfl, x.2⟩
  · intro hq
    -- some dart of the orbit is kept; lift it.
    simp only [DeletedOrbit, not_forall] at hq
    obtain ⟨x, hxq, hxS⟩ := hq
    refine ⟨Quotient.mk (cycleSetoid (Equiv.Perm.deleteSet p S)) ⟨x, hxS⟩, ?_⟩
    rw [keptToFull_mk]; exact hxq

/-- The number of **deleted** `p`-orbits (orbits entirely inside `S`). -/
noncomputable def numDeletedOrbits : ℕ :=
  Fintype.card {q : Quotient (cycleSetoid p) // DeletedOrbit p S q}

/-- **Orbit-count splitting.**  `numCycles p = numCycles (deleteSet p S) + numDeletedOrbits`.
Every `p`-orbit is either deleted or has a kept representative; the kept ones biject with the
filtered orbits via `keptToFull`. -/
theorem numCycles_eq_kept_add_deleted :
    _root_.numCycles p
      = _root_.numCycles (Equiv.Perm.deleteSet p S) + numDeletedOrbits p S := by
  classical
  -- `keptToFull` is a bijection onto the non-deleted orbits.
  have hbij : Function.Bijective
      (fun a => (⟨keptToFull p S a, by
        rw [← keptToFull_range_iff]; exact ⟨a, rfl⟩⟩ :
        {q : Quotient (cycleSetoid p) // ¬ DeletedOrbit p S q})) := by
    constructor
    · intro a b hab
      exact keptToFull_injective p S (Subtype.ext_iff.mp hab)
    · rintro ⟨q, hq⟩
      obtain ⟨a, ha⟩ := (keptToFull_range_iff p S q).2 hq
      exact ⟨a, Subtype.ext ha⟩
  have hcard_kept : _root_.numCycles (Equiv.Perm.deleteSet p S)
      = Fintype.card {q : Quotient (cycleSetoid p) // ¬ DeletedOrbit p S q} := by
    rw [← card_cycleSetoid_eq_numCycles]
    exact Fintype.card_of_bijective hbij
  have hcompl : Fintype.card {q : Quotient (cycleSetoid p) // ¬ DeletedOrbit p S q}
      = Fintype.card (Quotient (cycleSetoid p))
        - Fintype.card {q : Quotient (cycleSetoid p) // DeletedOrbit p S q} :=
    Fintype.card_subtype_compl _
  have hle : Fintype.card {q : Quotient (cycleSetoid p) // DeletedOrbit p S q}
      ≤ Fintype.card (Quotient (cycleSetoid p)) := Fintype.card_subtype_le _
  rw [← card_cycleSetoid_eq_numCycles p, hcard_kept, numDeletedOrbits, hcompl]
  omega

end OrbitSplit

/-- **`numCycles` depends only on the `SameCycle` relation.**  Two permutations on the same
type whose `SameCycle` relations coincide have the same number of cycles. -/
theorem numCycles_congr_sameCycle {E : Type u} [Fintype E] [DecidableEq E]
    (p q : Equiv.Perm E) (h : ∀ x y, p.SameCycle x y ↔ q.SameCycle x y) :
    _root_.numCycles p = _root_.numCycles q := by
  classical
  rw [← card_cycleSetoid_eq_numCycles, ← card_cycleSetoid_eq_numCycles]
  exact Fintype.card_congr (Quotient.congr (Equiv.refl E) (fun x y => by
    simpa using h x y))

/-! ## Section 5.  The raw restricted involution and the face-permutation bridge

For an ambient `M : CombMap D` and an `α`-closed deleted set `Del`, the kept subtype's edge
involution is `M.α.subtypePerm`, and the kept face permutation is
`(deleteSet M.σ Del) * (M.α.subtypePerm)`.  We compare against the **raw** pair on `D`: the
rotation `M.σ` (unchanged) and the **raw restricted involution** `rawAlpha` that fixes every
deleted dart and equals `M.α` elsewhere.  The key bridge is that the kept face permutation
equals `deleteSet (M.σ * rawAlpha) Del`, so `sameCycle_deleteSet_iff` applies to faces too. -/

section RawRestrict

variable (M : CombMap D) (Del : Finset D)

open scoped Classical

/-- The raw restricted function: identity on deleted darts, `M.α` elsewhere. -/
noncomputable def rawAlphaFun : D → D := fun d => if d ∈ Del then d else M.α d

/-- `rawAlphaFun` is an involution (uses `α`-closedness of `Del`). -/
lemma rawAlphaFun_involutive (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) :
    Function.Involutive (rawAlphaFun M Del) := by
  classical
  intro d
  unfold rawAlphaFun
  by_cases hd : d ∈ Del
  · simp [hd]
  · have hαd : M.α d ∉ Del := by
      intro h
      apply hd
      have := hclosed _ h
      rwa [M.alpha_alpha] at this
    simp [hd, hαd, M.alpha_alpha]

/-- The **raw restricted involution**: fixes every deleted dart, equals `M.α` on kept darts. -/
noncomputable def rawAlpha (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) : Equiv.Perm D :=
  Function.Involutive.toPerm (rawAlphaFun M Del) (rawAlphaFun_involutive M Del hclosed)

@[simp] lemma rawAlpha_apply (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) (d : D) :
    rawAlpha M Del hclosed d = if d ∈ Del then d else M.α d := rfl

/-- `rawAlpha` is an involution as a permutation. -/
lemma rawAlpha_invol (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) :
    rawAlpha M Del hclosed * rawAlpha M Del hclosed = 1 := by
  ext d
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id_eq]
  exact rawAlphaFun_involutive M Del hclosed d

/-- `rawAlpha` fixes deleted darts. -/
lemma rawAlpha_eq_self_of_mem (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {d : D}
    (hd : d ∈ Del) : rawAlpha M Del hclosed d = d := by simp [rawAlpha_apply, hd]

/-- `rawAlpha` equals `M.α` on kept darts. -/
lemma rawAlpha_eq_alpha_of_notMem (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {d : D}
    (hd : d ∉ Del) : rawAlpha M Del hclosed d = M.α d := by simp [rawAlpha_apply, hd]

/-- **Trajectory identity.**  Starting from a kept dart `x`, applying `M.α` and then iterating
`M.σ` through a run of deleted darts matches iterating `p := M.σ * rawAlpha`: for every `k`,
if the intermediate `σ`-iterates `(M.σ)^j (M.α x)` (`1 ≤ j ≤ k`) are all deleted, then
`p^(k+1) x = (M.σ)^(k+1) (M.α x)`.  (`rawAlpha` fixes the deleted darts visited.) -/
lemma rawFace_traj (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (x : {d : D // d ∉ Del}) :
    ∀ k : ℕ, (∀ j : ℕ, 1 ≤ j → j ≤ k → ((M.σ ^ j) (M.α x.1)) ∈ Del) →
      ((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x.1 = (M.σ ^ (k+1)) (M.α x.1) := by
  classical
  set p := M.σ * rawAlpha M Del hclosed with hp
  intro k
  induction k with
  | zero =>
      intro _
      simp only [zero_add, pow_one, hp]
      rw [Equiv.Perm.mul_apply, rawAlpha_eq_alpha_of_notMem M Del hclosed x.2]
  | succ k ih =>
      intro hdel
      have ihk : (p ^ (k+1)) x.1 = (M.σ ^ (k+1)) (M.α x.1) :=
        ih (fun j hj1 hjk => hdel j hj1 (by omega))
      have hmemk : (M.σ ^ (k+1)) (M.α x.1) ∈ Del := hdel (k+1) (by omega) (by omega)
      have hstep : ((p ^ (k+1+1)) x.1) = p ((p ^ (k+1)) x.1) := by
        rw [pow_succ']; rfl
      rw [hstep, ihk, hp, Equiv.Perm.mul_apply,
        rawAlpha_eq_self_of_mem M Del hclosed hmemk, ← Equiv.Perm.mul_apply, ← pow_succ']

/-- **One kept-face step is a `p`-power step.**  For a kept dart `x` (with `M.α x` also kept,
by `α`-closure), the value `(deleteSet M.σ Del)(M.α x)` is `(M.σ * rawAlpha)`-`SameCycle` to
`x` on the underlying darts. -/
lemma keptFaceStep_sameCycle_rawFace (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (x : {d : D // d ∉ Del}) (hαx : M.α x.1 ∉ Del) :
    (M.σ * rawAlpha M Del hclosed).SameCycle x.1
      ((Equiv.Perm.deleteSet M.σ Del ⟨M.α x.1, hαx⟩ : {d : D // d ∉ Del}) : D) := by
  classical
  set y : {d : D // d ∉ Del} := ⟨M.α x.1, hαx⟩ with hy
  -- firstOutside of `M.σ` at the kept dart `y = ⟨M.α x⟩`.
  set m := Equiv.Perm.DeleteSet.firstOutside M.σ Del y with hm
  have hmpos : 0 < m := Equiv.Perm.DeleteSet.firstOutside_pos M.σ Del y
  -- the deleteSet value is `(M.σ ^ m) (M.α x)`.
  have hval : (Equiv.Perm.deleteSet M.σ Del y : {d : D // d ∉ Del}).1 = (M.σ ^ m) (M.α x.1) :=
    Equiv.Perm.deleteSet_apply_coe M.σ Del y
  -- intermediate σ-iterates `(M.σ ^ j) (M.α x)`, `1 ≤ j < m`, are deleted (firstOutside min).
  have hinter : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → ((M.σ ^ j) (M.α x.1)) ∈ Del := by
    intro j hj1 hjm
    by_contra hnot
    have hjlt : j < m := by omega
    exact Equiv.Perm.DeleteSet.firstOutside_min M.σ Del y hjlt ⟨by omega, by
      show (M.σ ^ j) y.1 ∉ Del; rw [hy]; exact hnot⟩
  -- apply the trajectory identity at `k = m - 1`.
  have htraj := rawFace_traj M Del hclosed x (m - 1) hinter
  have hmsucc : (m - 1) + 1 = m := by omega
  rw [hmsucc] at htraj
  -- so `p^m x = (M.σ ^ m) (M.α x) = deleteSet value`.
  refine ⟨(m : ℤ), ?_⟩
  rw [zpow_natCast, hval, ← htraj]

/-- Abbreviation: the kept combinatorial map's face permutation is
`(deleteSet M.σ Del) * (M.α.subtypePerm)`. -/
noncomputable def keptFacePerm (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) : Equiv.Perm {d : D // d ∉ Del} :=
  (Equiv.Perm.deleteSet M.σ Del) * (M.α.subtypePerm (fun d => by
    rw [← hsub d]))

/-- **Forward face bridge.**  Each `keptFacePerm`-step preserves the
`(M.σ * rawAlpha)`-cycle of the underlying dart; hence `keptFacePerm.SameCycle` implies
`(M.σ * rawAlpha).SameCycle` on coercions. -/
lemma keptFacePerm_sameCycle_imp (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)
    {x y : {d : D // d ∉ Del}}
    (h : (keptFacePerm M Del hclosed hsub).SameCycle x y) :
    (M.σ * rawAlpha M Del hclosed).SameCycle x.1 y.1 := by
  classical
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn]
  clear hn
  induction n with
  | zero => simpa using Equiv.Perm.SameCycle.rfl
  | succ n ih =>
      have hpow : ((keptFacePerm M Del hclosed hsub) ^ (n+1)) x
          = (keptFacePerm M Del hclosed hsub) (((keptFacePerm M Del hclosed hsub) ^ n) x) := by
        rw [pow_succ']; rfl
      rw [hpow]
      refine ih.trans ?_
      -- one `keptFacePerm`-step from `z := (keptFacePerm)^n x`.
      set z : {d : D // d ∉ Del} := ((keptFacePerm M Del hclosed hsub) ^ n) x with hz
      have hαz : M.α z.1 ∉ Del := fun hc => z.2 ((hsub z.1).2 hc)
      have hstep : ((keptFacePerm M Del hclosed hsub) z).1
          = (Equiv.Perm.deleteSet M.σ Del ⟨M.α z.1, hαz⟩ : {d : D // d ∉ Del}).1 := rfl
      rw [hstep]
      exact keptFaceStep_sameCycle_rawFace M Del hclosed z hαz

/-- **The kept face permutation equals the deleted raw face permutation.**  As permutations on
the kept subtype, `keptFacePerm = deleteSet (M.σ * rawAlpha) Del`.  Both send a kept dart `x`
to the first kept dart reached from `M.α x` by iterating `M.σ` through the deleted run; the raw
face permutation `M.σ * rawAlpha` walks the same trajectory because `rawAlpha` fixes the deleted
darts it passes through. -/
theorem keptFacePerm_eq_deleteSet_rawFace (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) :
    keptFacePerm M Del hclosed hsub = Equiv.Perm.deleteSet (M.σ * rawAlpha M Del hclosed) Del := by
  classical
  ext x
  -- It suffices to prove the underlying dart values agree.
  set y : {d : D // d ∉ Del} := ⟨M.α x.1, fun hc => x.2 ((hsub x.1).2 hc)⟩ with hy
  -- LHS value: `(deleteSet M.σ Del) y = (M.σ)^m (M.α x)` with `m = firstOutside M.σ Del y`.
  set m := Equiv.Perm.DeleteSet.firstOutside M.σ Del y with hm
  have hmpos : 0 < m := Equiv.Perm.DeleteSet.firstOutside_pos M.σ Del y
  have hlhs : ((keptFacePerm M Del hclosed hsub) x : {d : D // d ∉ Del}).1
      = (M.σ ^ m) (M.α x.1) := by
    show ((Equiv.Perm.deleteSet M.σ Del) y : {d : D // d ∉ Del}).1 = _
    rw [Equiv.Perm.deleteSet_apply_coe]
  -- intermediate σ-iterates of `M.α x` (before step `m`) are deleted (firstOutside min).
  have hinter : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → ((M.σ ^ j) (M.α x.1)) ∈ Del := by
    intro j hj1 hjm
    by_contra hnot
    exact Equiv.Perm.DeleteSet.firstOutside_min M.σ Del y (by omega : j < m)
      ⟨by omega, by show (M.σ ^ j) y.1 ∉ Del; rw [hy]; exact hnot⟩
  -- the `m`-th σ-iterate is kept.
  have hmkept : (M.σ ^ m) (M.α x.1) ∉ Del := by
    have := Equiv.Perm.DeleteSet.firstOutside_notMem M.σ Del y
    rwa [hy] at this
  -- trajectory: `(M.σ * rawAlpha)^m x = (M.σ)^m (M.α x)`.
  have htraj := rawFace_traj M Del hclosed x (m - 1) hinter
  have hmsucc : (m - 1) + 1 = m := by omega
  rw [hmsucc] at htraj
  -- RHS value: `deleteSet (M.σ*rawAlpha) Del x = (M.σ*rawAlpha)^M x`, `M = firstOutside …`.
  set P := M.σ * rawAlpha M Del hclosed with hP
  have hrhs : ((Equiv.Perm.deleteSet P Del) x : {d : D // d ∉ Del}).1
      = (P ^ (Equiv.Perm.DeleteSet.firstOutside P Del x)) x.1 :=
    Equiv.Perm.deleteSet_apply_coe P Del x
  -- The firstOutside of `P` at `x` is exactly `m`: the `P`-trajectory equals the σ-trajectory
  -- of `M.α x`, deleted before step `m`, kept at step `m`.
  have hPtraj : ∀ j : ℕ, 1 ≤ j → j ≤ m → (P ^ j) x.1 = (M.σ ^ j) (M.α x.1) := by
    intro j hj1 hjm
    have hjsub : ∀ i : ℕ, 1 ≤ i → i ≤ j - 1 → ((M.σ ^ i) (M.α x.1)) ∈ Del :=
      fun i hi1 hij => hinter i hi1 (by omega)
    have := rawFace_traj M Del hclosed x (j - 1) hjsub
    rwa [Nat.sub_add_cancel hj1] at this
  have hPm_kept : (P ^ m) x.1 ∉ Del := by rw [hPtraj m hmpos le_rfl]; exact hmkept
  have hPm_min : ∀ i : ℕ, i < m → ¬ (0 < i ∧ (P ^ i) x.1 ∉ Del) := by
    intro i him ⟨hipos, hinotmem⟩
    rw [hPtraj i hipos (by omega)] at hinotmem
    exact hinotmem (hinter i hipos (by omega))
  have hMeq : Equiv.Perm.DeleteSet.firstOutside P Del x = m := by
    apply le_antisymm
    · exact Nat.find_min' _ ⟨hmpos, hPm_kept⟩
    · by_contra hlt
      rw [not_le] at hlt
      exact hPm_min _ hlt
        ⟨Equiv.Perm.DeleteSet.firstOutside_pos P Del x,
         Equiv.Perm.DeleteSet.firstOutside_notMem P Del x⟩
  rw [hlhs, hrhs, hMeq, hPtraj m hmpos le_rfl]

/-- **The face SameCycle bridge.**  On the kept subtype, the kept face permutation and the raw
face permutation `M.σ * rawAlpha` have the same `SameCycle` relation (via the coercion). -/
theorem keptFacePerm_sameCycle_iff (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) (x y : {d : D // d ∉ Del}) :
    (keptFacePerm M Del hclosed hsub).SameCycle x y
      ↔ (M.σ * rawAlpha M Del hclosed).SameCycle x.1 y.1 := by
  rw [keptFacePerm_eq_deleteSet_rawFace M Del hclosed hsub]
  exact Equiv.Perm.sameCycle_deleteSet_iff _ Del x y

/-! ### The face-count bridge `F_raw = F_kept + (deleted faces)`

Applying the orbit-count splitting to `p = M.σ * rawAlpha` and translating the kept
combinatorial map's face count `numCycles (keptFacePerm)` via `keptFacePerm_sameCycle_iff`
and `numCycles_congr_sameCycle`. -/

/-- The face count of the kept map equals `numCycles (deleteSet (M.σ * rawAlpha) Del)`. -/
lemma numCycles_keptFacePerm_eq (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) :
    _root_.numCycles (keptFacePerm M Del hclosed hsub)
      = _root_.numCycles (Equiv.Perm.deleteSet (M.σ * rawAlpha M Del hclosed) Del) := by
  rw [keptFacePerm_eq_deleteSet_rawFace M Del hclosed hsub]

/-! ### `DV = DF`: deleted `σ`-orbits coincide with deleted `(σ·rawAlpha)`-orbits

On the deleted set, `rawAlpha = id`, so `M.σ * rawAlpha = M.σ` there; hence a deleted orbit of
one is a deleted orbit of the other.  We obtain this at the level of the `numDeletedOrbits`
counts through the equality of the `DeletedOrbit` predicates after transporting along the
`SameCycle` coincidence on deleted darts. -/

/-- On the deleted set, `M.σ` and `M.σ * rawAlpha` agree, hence have the same `SameCycle`
relation among deleted darts; combined with the kept-orbit splitting this forces the deleted
orbit counts to be equal. -/
lemma sameCycle_sigma_rawFace_of_mem (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    {x : D} (hx : x ∈ Del) :
    (M.σ * rawAlpha M Del hclosed) x = M.σ x := by
  rw [Equiv.Perm.mul_apply, rawAlpha_eq_self_of_mem M Del hclosed hx]

/-! ### The component-count bridge

The kept combinatorial map's component relation `dartStepRel (deleteSet M.σ Del) (M.α|)`
matches the raw relation `dartStepRel M.σ (rawAlpha)` restricted to kept darts.  Hence
`numComponents M.σ rawAlpha = numComp (dartStepRel of the kept map) + (#deleted clusters)`. -/

variable (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
  (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)

open scoped Classical

/-- The kept edge involution: `M.α` restricted to the kept subtype. -/
noncomputable def keptAlpha : Equiv.Perm {d : D // d ∉ Del} :=
  M.α.subtypePerm (p := fun d => d ∉ Del) (fun d => by
    constructor
    · intro hd hc; exact hd ((hsub d).1 hc)
    · intro hd hc; exact hd ((hsub d).2 hc))

@[simp] lemma keptAlpha_apply_coe (d : {d : D // d ∉ Del}) :
    (keptAlpha M Del hsub d : D) = M.α d.1 := rfl

lemma keptAlpha_invol : keptAlpha M Del hsub * keptAlpha M Del hsub = 1 := by
  ext z
  simp only [Equiv.Perm.coe_mul, Equiv.Perm.coe_one, Function.comp_apply, id_eq,
    keptAlpha_apply_coe]
  exact M.alpha_alpha z.1

/-- The kept combinatorial map's dart-step relation, on the kept subtype. -/
noncomputable def keptStepRel : {d : D // d ∉ Del} → {d : D // d ∉ Del} → Prop :=
  dartStepRel (Equiv.Perm.deleteSet M.σ Del) (keptAlpha M Del hsub)

/-- **A kept dart-step lifts to a raw dart-step on the underlying darts.** -/
lemma keptStepRel_imp_raw {x y : {d : D // d ∉ Del}}
    (h : keptStepRel M Del hsub x y) :
    dartStepRel M.σ (rawAlpha M Del hclosed) x.1 y.1 := by
  classical
  rcases h with hσ | hα
  · -- same `deleteSet M.σ`-cycle ⇒ same `M.σ`-cycle on coercions.
    exact Or.inl ((Equiv.Perm.sameCycle_deleteSet_iff M.σ Del x y).1 hσ)
  · -- α-edge: `y = (M.α.subtypePerm) x`, so `y.1 = M.α x.1 = rawAlpha x.1` (x kept).
    refine Or.inr ?_
    have hxval : (rawAlpha M Del hclosed) x.1 = M.α x.1 :=
      rawAlpha_eq_alpha_of_notMem M Del hclosed x.2
    rw [hxval]
    have := congrArg Subtype.val hα
    simpa using this

/-- **A raw dart-step between two kept darts descends to a kept dart-step.** -/
lemma raw_imp_keptStepRel {x y : {d : D // d ∉ Del}}
    (h : dartStepRel M.σ (rawAlpha M Del hclosed) x.1 y.1) :
    keptStepRel M Del hsub x y := by
  classical
  rcases h with hσ | hα
  · exact Or.inl ((Equiv.Perm.sameCycle_deleteSet_iff M.σ Del x y).2 hσ)
  · -- `y.1 = rawAlpha x.1 = M.α x.1` (x kept) ⇒ `y = (M.α.subtypePerm) x`.
    refine Or.inr ?_
    rw [rawAlpha_eq_alpha_of_notMem M Del hclosed x.2] at hα
    apply Subtype.ext
    simpa using hα

/-- `EqvGen` of the kept dart-step relation lifts to `EqvGen` of the raw relation. -/
lemma eqvGen_keptStepRel_imp_raw {x y : {d : D // d ∉ Del}}
    (h : Relation.EqvGen (keptStepRel M Del hsub) x y) :
    Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x.1 y.1 := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (keptStepRel_imp_raw M Del hclosed hsub hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- The raw dart-step relation is symmetric (`rawAlpha` is an involution). -/
lemma rawStepRel_symm {a b : D}
    (h : dartStepRel M.σ (rawAlpha M Del hclosed) a b) :
    dartStepRel M.σ (rawAlpha M Del hclosed) b a :=
  dartStepRel_symm (rawAlpha_invol M Del hclosed) h

/-- **Descent witness (forward walk).**  Every dart `z` raw-reachable from a kept dart `x`
(via `ReflTransGen`) is `M.σ`-`SameCycle` to a kept dart `w` in the same *kept* component as
`x`.  The only raw steps that can land in `Del` are `M.σ`-`SameCycle` steps; `M.σ`-`SameCycle`
is transitive, so deleted intermediates collapse, and the `rawAlpha`-edge from a kept dart lands
kept (`α`-closure), giving a genuine kept dart-step. -/
lemma raw_reach_kept_witness {x : {d : D // d ∉ Del}} {z : D}
    (h : Relation.ReflTransGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x.1 z) :
    ∃ w : {d : D // d ∉ Del},
      Relation.ReflTransGen (keptStepRel M Del hsub) x w ∧ M.σ.SameCycle w.1 z := by
  classical
  induction h with
  | refl => exact ⟨x, Relation.ReflTransGen.refl, Equiv.Perm.SameCycle.rfl⟩
  | @tail b c hxb hbc ih =>
      obtain ⟨w, hwkept, hwb⟩ := ih
      -- one more raw step `b → c`; combine with `w ~σ b`.
      rcases hbc with hσ | hαe
      · -- `c` in same `M.σ`-cycle as `b`, hence as `w`.
        exact ⟨w, hwkept, hwb.trans hσ⟩
      · -- `c = rawAlpha b`.
        by_cases hbDel : b ∈ Del
        · -- `rawAlpha b = b`, so `c = b`; nothing changes.
          rw [rawAlpha_eq_self_of_mem M Del hclosed hbDel] at hαe
          exact ⟨w, hwkept, hαe ▸ hwb⟩
        · -- `b` kept, `c = M.α b` kept (α-closure); `w ~σ b` gives a kept σ-step `w → ⟨b⟩`,
          -- then the kept α-edge `⟨b⟩ → ⟨c⟩`.
          have hck : c ∉ Del := by
            rw [rawAlpha_eq_alpha_of_notMem M Del hclosed hbDel] at hαe
            rw [hαe]; intro hc; exact hbDel ((hsub b).2 hc)
          have hbw : M.σ.SameCycle w.1 b := hwb
          -- kept σ-step `w → ⟨b, hbDel⟩`:
          have hstep1 : keptStepRel M Del hsub w ⟨b, hbDel⟩ :=
            Or.inl ((Equiv.Perm.sameCycle_deleteSet_iff M.σ Del w ⟨b, hbDel⟩).2 hbw)
          -- kept α-edge `⟨b⟩ → ⟨c⟩`:
          have hstep2 : keptStepRel M Del hsub ⟨b, hbDel⟩ ⟨c, hck⟩ := by
            refine Or.inr (Subtype.ext ?_)
            show c = M.α b
            rw [rawAlpha_eq_alpha_of_notMem M Del hclosed hbDel] at hαe
            exact hαe
          exact ⟨⟨c, hck⟩, (hwkept.tail hstep1).tail hstep2, Equiv.Perm.SameCycle.rfl⟩

/-- **Descent.**  Two kept darts that are raw-`EqvGen` are kept-`EqvGen`.  (From the descent
witness: the witness `w` for `y` is `M.σ`-`SameCycle` to `y`, both kept, hence kept-connected
by a single kept `σ`-step.) -/
lemma raw_eqvGen_descends {x y : {d : D // d ∉ Del}}
    (h : Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x.1 y.1) :
    Relation.EqvGen (keptStepRel M Del hsub) x y := by
  classical
  -- pass to `ReflTransGen` (symmetric relation), apply the witness, close with a kept σ-step.
  have hsymm : ∀ a b, dartStepRel M.σ (rawAlpha M Del hclosed) a b →
      dartStepRel M.σ (rawAlpha M Del hclosed) b a :=
    fun a b => rawStepRel_symm M Del hclosed
  rw [eqvGen_iff_reflTransGen hsymm] at h
  obtain ⟨w, hwkept, hwy⟩ := raw_reach_kept_witness M Del hclosed hsub h
  -- `w ~σ y` (both kept) ⇒ kept σ-step `w → y`.
  have hstep : keptStepRel M Del hsub w y :=
    Or.inl ((Equiv.Perm.sameCycle_deleteSet_iff M.σ Del w y).2 hwy)
  have hksymm : ∀ a b, keptStepRel M Del hsub a b → keptStepRel M Del hsub b a :=
    fun a b h => dartStepRel_symm (keptAlpha_invol M Del hsub) h
  rw [eqvGen_iff_reflTransGen hksymm]
  exact hwkept.tail hstep

/-- The lifted map `⟦x⟧_kept ↦ ⟦x.1⟧_raw` of component quotients. -/
noncomputable def keptCompToRaw :
    Quotient (_root_.compSetoid (keptStepRel M Del hsub))
      → Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed))) :=
  Quotient.lift (fun x => Quotient.mk _ (x.1 : D)) (by
    intro x y hxy
    apply Quotient.sound
    show Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x.1 y.1
    exact eqvGen_keptStepRel_imp_raw M Del hclosed hsub hxy)

/-- `keptCompToRaw` is injective: by the descent lemma, kept darts raw-`EqvGen` are
kept-`EqvGen`. -/
lemma keptCompToRaw_injective : Function.Injective (keptCompToRaw M Del hclosed hsub) := by
  classical
  intro a b hab
  refine Quotient.inductionOn₂ a b (fun x y hxy => ?_) hab
  apply Quotient.sound
  show Relation.EqvGen (keptStepRel M Del hsub) x y
  exact raw_eqvGen_descends M Del hclosed hsub (Quotient.exact hxy)

/-- **Component count: kept ≤ raw.**  The kept combinatorial map has at most as many components
as the raw pair on `D`. -/
theorem numComp_kept_le_raw :
    _root_.numComp (keptStepRel M Del hsub)
      ≤ numComponents M.σ (rawAlpha M Del hclosed) := by
  classical
  rw [numComponents_def]
  unfold _root_.numComp
  exact Nat.card_le_card_of_injective _ (keptCompToRaw_injective M Del hclosed hsub)

/-! ### The component-count split `c_raw = c_kept + (deleted clusters)`

A raw component is **deleted** if all its darts lie in `Del`.  The image of `keptCompToRaw` is
exactly the non-deleted raw components, so `c_raw = c_kept + #(deleted raw components)`. -/

/-- A raw component is **deleted** if all its darts lie in `Del`. -/
def DeletedComp (q : Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))) :
    Prop :=
  ∀ x : D, Quotient.mk _ x = q → x ∈ Del

/-- The image of `keptCompToRaw` is exactly the non-deleted raw components. -/
lemma keptCompToRaw_range_iff
    (q : Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))) :
    (∃ a, keptCompToRaw M Del hclosed hsub a = q) ↔ ¬ DeletedComp M Del hclosed q := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    refine Quotient.inductionOn a (fun x => ?_)
    simp only [DeletedComp, not_forall]
    exact ⟨x.1, rfl, x.2⟩
  · intro hq
    simp only [DeletedComp, not_forall] at hq
    obtain ⟨x, hxq, hxD⟩ := hq
    exact ⟨Quotient.mk _ ⟨x, hxD⟩, hxq⟩

/-- The number of deleted raw components. -/
noncomputable def numDeletedComp : ℕ :=
  Fintype.card {q : Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))
    // DeletedComp M Del hclosed q}

/-- **Component split.**  `numComponents M.σ rawAlpha = numComp (keptStepRel) + numDeletedComp`. -/
theorem numComponents_raw_split :
    numComponents M.σ (rawAlpha M Del hclosed)
      = _root_.numComp (keptStepRel M Del hsub) + numDeletedComp M Del hclosed := by
  classical
  rw [numComponents_def]
  have hbij : Function.Bijective
      (fun a => (⟨keptCompToRaw M Del hclosed hsub a, by
        rw [← keptCompToRaw_range_iff M Del hclosed hsub]; exact ⟨a, rfl⟩⟩ :
        {q // ¬ DeletedComp M Del hclosed q})) := by
    constructor
    · intro a b hab
      exact keptCompToRaw_injective M Del hclosed hsub (Subtype.ext_iff.mp hab)
    · rintro ⟨q, hq⟩
      obtain ⟨a, ha⟩ := (keptCompToRaw_range_iff M Del hclosed hsub q).2 hq
      exact ⟨a, Subtype.ext ha⟩
  have hcard_kept : _root_.numComp (keptStepRel M Del hsub)
      = Fintype.card {q // ¬ DeletedComp M Del hclosed q} := by
    unfold _root_.numComp
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_of_bijective hbij
  have hcompl : Fintype.card {q // ¬ DeletedComp M Del hclosed q}
      = Fintype.card (Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed))))
        - Fintype.card {q // DeletedComp M Del hclosed q} :=
    Fintype.card_subtype_compl _
  have hle : Fintype.card {q // DeletedComp M Del hclosed q}
      ≤ Fintype.card (Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))) :=
    Fintype.card_subtype_le _
  have hraw : _root_.numComp (dartStepRel M.σ (rawAlpha M Del hclosed))
      = Fintype.card (Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))) := by
    unfold _root_.numComp; rw [Nat.card_eq_fintype_card]
  rw [hraw, hcard_kept, numDeletedComp, hcompl]
  omega

/-! ### Final assembly: the kept combinatorial map's genus slack is `≤ 0`

We assemble the count bridges.  With `Ehalf` equal on both sides and the deleted-class counts
`numDeletedComp = numDeletedOrbits M.σ Del` and `numDeletedOrbits (M.σ·rawAlpha) Del =
numDeletedOrbits M.σ Del`, the kept slack equals the raw slack, which is `0` on a genus-0 `M`.
The two deleted-class equalities are the *last* structural facts; on `Del` the rotation
`rawAlpha` is the identity, so all three deleted-class structures coincide with the
`M.σ`-orbits among deleted darts. -/

/-- **A deleted-component dart has its whole `M.σ`-orbit deleted.**  If every dart in `x`'s
`dartStepRel`-component lies in `Del`, then in particular `M.σ x` lies in `Del` (it is a
`dartStepRel`-step away), and inductively the whole `M.σ`-orbit of `x` is deleted. -/
lemma sigma_sameCycle_imp_eqvGen_dartStepRel {a b : D} (h : M.σ.SameCycle a b) :
    Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) a b :=
  Relation.EqvGen.rel _ _ (Or.inl h)

/-- On `Del`, a `dartStepRel`-step keeps you in the same `M.σ`-orbit (the `rawAlpha`-edge fixes
deleted darts).  Hence within a deleted component the relation collapses to `M.σ.SameCycle`. -/
lemma dartStepRel_of_mem_del {a b : D} (ha : a ∈ Del)
    (h : dartStepRel M.σ (rawAlpha M Del hclosed) a b) : M.σ.SameCycle a b := by
  rcases h with hσ | hαe
  · exact hσ
  · rw [rawAlpha_eq_self_of_mem M Del hclosed ha] at hαe
    exact hαe ▸ Equiv.Perm.SameCycle.rfl

/-- **DeletedComp ⟺ DeletedOrbit (`M.σ`).**  The `dartStepRel`-class of a dart is entirely
deleted iff its `M.σ`-orbit is entirely deleted.  (`⟸`: a deleted `M.σ`-orbit admits no
`rawAlpha`-edge leaving `Del`, so the component stays in `Del`; `⟹`: `M.σ.SameCycle` is a
`dartStepRel`-step, so a deleted component contains the whole `M.σ`-orbit.) -/
lemma deletedComp_iff_deletedOrbit (x : D) :
    DeletedComp M Del hclosed (Quotient.mk _ x)
      ↔ DeletedOrbit M.σ Del (Quotient.mk (cycleSetoid M.σ) x) := by
  classical
  constructor
  · -- DeletedComp ⇒ DeletedOrbit: any `M.σ`-cycle dart is `dartStepRel`-related, hence deleted.
    intro hC y hy
    apply hC y
    apply Quotient.sound
    show Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) y x
    have hsc : M.σ.SameCycle y x := Quotient.exact hy
    exact sigma_sameCycle_imp_eqvGen_dartStepRel M Del hclosed hsc
  · -- DeletedOrbit ⇒ DeletedComp: every `dartStepRel`-related dart stays in the deleted σ-orbit.
    intro hO y hy
    have hxy : Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x y :=
      (Quotient.exact hy).symm
    have hxDel : x ∈ Del := hO x rfl
    -- pass to ReflTransGen and carry the invariant `M.σ.SameCycle x z ∧ z ∈ Del` forward.
    have hsymm : ∀ a b, dartStepRel M.σ (rawAlpha M Del hclosed) a b →
        dartStepRel M.σ (rawAlpha M Del hclosed) b a :=
      fun a b => rawStepRel_symm M Del hclosed
    rw [eqvGen_iff_reflTransGen hsymm] at hxy
    have hinv : ∀ z, Relation.ReflTransGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x z →
        M.σ.SameCycle x z ∧ z ∈ Del := by
      intro z hz
      induction hz with
      | refl => exact ⟨Equiv.Perm.SameCycle.rfl, hxDel⟩
      | @tail b c hxb hbc ih =>
          obtain ⟨hxb_sc, hbDel⟩ := ih
          have hbc_sc : M.σ.SameCycle b c := dartStepRel_of_mem_del M Del hclosed hbDel hbc
          have hxc_sc : M.σ.SameCycle x c := hxb_sc.trans hbc_sc
          refine ⟨hxc_sc, ?_⟩
          -- `c` is in `x`'s σ-orbit, which is deleted.
          exact hO c (Quotient.sound hxc_sc.symm)
    exact (hinv y hxy).2

/-- Within a deleted component, `dartStepRel`-`EqvGen` collapses to `M.σ.SameCycle`. -/
lemma comp_eqvGen_imp_sigma_of_deleted {x y : D} (hxDel : x ∈ Del)
    (hdel : ∀ z, Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x z → z ∈ Del)
    (h : Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x y) :
    M.σ.SameCycle x y := by
  classical
  have hsymm : ∀ a b, dartStepRel M.σ (rawAlpha M Del hclosed) a b →
      dartStepRel M.σ (rawAlpha M Del hclosed) b a :=
    fun a b => rawStepRel_symm M Del hclosed
  rw [eqvGen_iff_reflTransGen hsymm] at h
  have hinv : ∀ z, Relation.ReflTransGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x z →
      M.σ.SameCycle x z := by
    intro z hz
    induction hz with
    | refl => exact Equiv.Perm.SameCycle.rfl
    | @tail b c hxb hbc ih =>
        have hbDel : b ∈ Del :=
          hdel b ((eqvGen_iff_reflTransGen hsymm x b).2 hxb)
        exact ih.trans (dartStepRel_of_mem_del M Del hclosed hbDel hbc)
  exact hinv y h

/-- A deleted `dartStepRel`-class's representative `out` is deleted, and its whole component is
deleted (every dart `EqvGen`-related to it). -/
lemma deletedComp_out_props
    {q : Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))}
    (hq : DeletedComp M Del hclosed q) :
    q.out ∈ Del ∧ ∀ z, Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) q.out z →
      z ∈ Del := by
  classical
  have hout : q.out ∈ Del := hq q.out (Quotient.out_eq q)
  refine ⟨hout, fun z hz => ?_⟩
  apply hq z
  rw [← Quotient.out_eq q]
  exact Quotient.sound (Relation.EqvGen.symm _ _ hz)

/-- **`numDeletedComp = numDeletedOrbits M.σ Del`.**  Both count the same family of deleted
`M.σ`-orbits; the equiv sends a deleted component to the `M.σ`-orbit of its representative and
back, well-defined by the within-deleted collapse `comp_eqvGen_imp_sigma_of_deleted`. -/
theorem numDeletedComp_eq_numDeletedOrbits :
    numDeletedComp M Del hclosed = numDeletedOrbits M.σ Del := by
  classical
  unfold numDeletedComp numDeletedOrbits
  refine Fintype.card_congr ?_
  refine
    { toFun := fun q => ⟨Quotient.mk (cycleSetoid M.σ) q.1.out,
        (deletedComp_iff_deletedOrbit M Del hclosed q.1.out).1 (by
          intro z hz
          obtain ⟨hout, hcomp⟩ := deletedComp_out_props M Del hclosed q.2
          exact q.2 z (by rw [hz]; exact Quotient.out_eq q.1))⟩,
      invFun := fun o => ⟨Quotient.mk _ o.1.out,
        (deletedComp_iff_deletedOrbit M Del hclosed o.1.out).2 (by
          intro z hz
          exact o.2 z (by rw [hz]; exact Quotient.out_eq o.1))⟩,
      left_inv := ?_, right_inv := ?_ }
  · -- `[ [qc].out ]_σ` then `[ · ]_comp` returns `qc`.
    rintro ⟨qc, hqc⟩
    apply Subtype.ext
    dsimp only
    obtain ⟨hout, hcomp⟩ := deletedComp_out_props M Del hclosed hqc
    -- the σ-orbit of `qc.out`'s out is σ-SameCycle to `qc.out`, hence same comp-class.
    nth_rewrite 2 [← Quotient.out_eq qc]
    apply Quotient.sound
    show Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) _ qc.out
    have hsc : M.σ.SameCycle (Quotient.mk (cycleSetoid M.σ) qc.out).out qc.out := by
      have := Quotient.out_eq (Quotient.mk (cycleSetoid M.σ) qc.out)
      exact Quotient.exact this
    exact sigma_sameCycle_imp_eqvGen_dartStepRel M Del hclosed hsc
  · -- `[ [o].out ]_comp` then `[ · ]_σ` returns `o`.
    rintro ⟨o, ho⟩
    apply Subtype.ext
    dsimp only
    nth_rewrite 2 [← Quotient.out_eq o]
    apply Quotient.sound
    show M.σ.SameCycle _ o.out
    -- the comp-class of `o.out` is deleted; its out is σ-SameCycle to `o.out` by the collapse.
    have hodel : o.out ∈ Del := ho o.out (Quotient.out_eq o)
    -- `o`'s σ-orbit is deleted ⇒ `o.out`'s comp-class is deleted (`deletedComp_iff_deletedOrbit`).
    have hDOrbit : DeletedOrbit M.σ Del (Quotient.mk (cycleSetoid M.σ) o.out) := by
      intro z hz
      exact ho z (by rw [hz]; exact Quotient.out_eq o)
    have hDComp : DeletedComp M Del hclosed
        (Quotient.mk (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed))) o.out) :=
      (deletedComp_iff_deletedOrbit M Del hclosed o.out).2 hDOrbit
    obtain ⟨_, hcompdel⟩ := deletedComp_out_props M Del hclosed hDComp
    have hsc : M.σ.SameCycle
        (Quotient.mk (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed))) o.out).out
        o.out := by
      apply comp_eqvGen_imp_sigma_of_deleted M Del hclosed
        (hcompdel _ (Relation.EqvGen.refl _)) hcompdel
      have := Quotient.out_eq
        (Quotient.mk (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed))) o.out)
      exact Quotient.exact this
    exact hsc

/-! ### `numDeletedOrbits (M.σ * rawAlpha) Del = numDeletedOrbits M.σ Del`

On `Del`, `M.σ * rawAlpha` and `M.σ` agree; a `SameCycle` chain that stays in `Del` for one is a
`SameCycle` chain for the other.  Hence a deleted orbit of one is a deleted orbit of the
other. -/

/-- For a deleted dart `d`, a `(M.σ * rawAlpha)`-step equals an `M.σ`-step, and conversely; a
`SameCycle` for one whose darts are all deleted is a `SameCycle` for the other. -/
lemma sigmaRaw_sameCycle_of_deleted {x y : D}
    (hx : x ∈ Del)
    (hstay : ∀ z, M.σ.SameCycle x z → z ∈ Del)
    (h : M.σ.SameCycle x y) : (M.σ * rawAlpha M Del hclosed).SameCycle x y := by
  classical
  -- trace the `M.σ`-power; each visited dart is deleted, where the two perms agree.
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  rw [← hn]
  -- `(M.σ * rawAlpha)^n x = M.σ^n x` since all intermediate darts are deleted.
  clear hn
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : ((M.σ * rawAlpha M Del hclosed) ^ (n+1)) x
          = (M.σ * rawAlpha M Del hclosed) (((M.σ * rawAlpha M Del hclosed) ^ n) x) := by
        rw [pow_succ']; rfl
      rw [hstep, ih]
      -- `M.σ^n x` is deleted (in `x`'s σ-cycle), so `rawAlpha` fixes it.
      have hmemn : (M.σ ^ n) x ∈ Del := hstay _ ⟨(n : ℤ), by rw [zpow_natCast]⟩
      rw [Equiv.Perm.mul_apply, rawAlpha_eq_self_of_mem M Del hclosed hmemn]
      rw [← Equiv.Perm.mul_apply, ← pow_succ']

/-- Conversely, a `(M.σ * rawAlpha)`-cycle whose darts are all deleted is an `M.σ`-cycle. -/
lemma sigma_sameCycle_of_deleted_sigmaRaw {x y : D}
    (hx : x ∈ Del)
    (hstay : ∀ z, (M.σ * rawAlpha M Del hclosed).SameCycle x z → z ∈ Del)
    (h : (M.σ * rawAlpha M Del hclosed).SameCycle x y) : M.σ.SameCycle x y := by
  classical
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast, ← hn]
  clear hn
  induction n with
  | zero => simp
  | succ n ih =>
      have hmemn : ((M.σ * rawAlpha M Del hclosed) ^ n) x ∈ Del :=
        hstay _ ⟨(n : ℤ), by rw [zpow_natCast]⟩
      have hLHS : (M.σ ^ (n+1)) x = M.σ (((M.σ * rawAlpha M Del hclosed) ^ n) x) := by
        rw [pow_succ', Equiv.Perm.mul_apply, ih]
      have hRHS : ((M.σ * rawAlpha M Del hclosed) ^ (n+1)) x
          = M.σ (((M.σ * rawAlpha M Del hclosed) ^ n) x) := by
        rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          rawAlpha_eq_self_of_mem M Del hclosed hmemn]
      rw [hLHS, hRHS]

/-- **`DeletedOrbit`s coincide** for `M.σ` and `M.σ * rawAlpha`. -/
lemma deletedOrbit_sigmaRaw_iff (x : D) :
    DeletedOrbit (M.σ * rawAlpha M Del hclosed) Del
        (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) x)
      ↔ DeletedOrbit M.σ Del (Quotient.mk (cycleSetoid M.σ) x) := by
  classical
  -- Trajectory: if `x`'s `σRaw`-orbit is deleted then `σ^k x = σRaw^k x ∈ Del` for all `k`,
  -- and symmetrically; this collapses each orbit-deletion predicate to the other.
  have key : ∀ (p q : Equiv.Perm D),
      (∀ d : D, d ∈ Del → p d = q d) →
      ∀ (hpx : DeletedOrbit p Del (Quotient.mk (cycleSetoid p) x)),
      ∀ k : ℕ, (p ^ k) x = (q ^ k) x ∧ (q ^ k) x ∈ Del := by
    intro p q hpq hpx k
    have hxDel : x ∈ Del := hpx x rfl
    induction k with
    | zero => exact ⟨by simp, by simpa using hxDel⟩
    | succ k ih =>
        obtain ⟨ihEq, ihDel⟩ := ih
        have hqk_del : (q ^ k) x ∈ Del := ihDel
        have hpk_del : (p ^ k) x ∈ Del := ihEq ▸ ihDel
        have heq : (p ^ (k+1)) x = (q ^ (k+1)) x := by
          rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ihEq,
            hpq _ hqk_del]
        refine ⟨heq, ?_⟩
        -- `q^(k+1) x = p^(k+1) x` is in `x`'s `p`-orbit, hence deleted by `hpx`.
        apply hpx
        apply Quotient.sound
        show p.SameCycle ((q ^ (k+1)) x) x
        exact ⟨-((k+1 : ℕ) : ℤ), by
          rw [← heq, zpow_neg, zpow_natCast, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.coe_pow]⟩
  constructor
  · intro hP y hy
    have hsc : M.σ.SameCycle y x := Quotient.exact hy
    have hagree : ∀ d : D, d ∈ Del → (M.σ * rawAlpha M Del hclosed) d = M.σ d :=
      fun d hd => sameCycle_sigma_rawFace_of_mem M Del hclosed hd
    -- `y` is in `x`'s σ-orbit; show deleted via the trajectory of `M.σ` matching `σRaw`.
    obtain ⟨n, hn⟩ := hsc.symm.exists_nat_pow_eq  -- `σ^n x = y`
    have := key (M.σ * rawAlpha M Del hclosed) M.σ hagree hP n
    rw [hn] at this
    exact this.2
  · intro hO y hy
    have hsc : (M.σ * rawAlpha M Del hclosed).SameCycle y x := Quotient.exact hy
    have hagree : ∀ d : D, d ∈ Del → M.σ d = (M.σ * rawAlpha M Del hclosed) d :=
      fun d hd => (sameCycle_sigma_rawFace_of_mem M Del hclosed hd).symm
    obtain ⟨n, hn⟩ := hsc.symm.exists_nat_pow_eq  -- `σRaw^n x = y`
    have := key M.σ (M.σ * rawAlpha M Del hclosed) hagree hO n
    rw [hn] at this
    exact this.2

/-- A `σ`-`SameCycle` within a deleted `σRaw`-orbit is a `σRaw`-`SameCycle` (and conversely),
since the two rotations agree on `Del` and the orbit stays in `Del`. -/
lemma sigmaRaw_sameCycle_iff_sigma_of_deletedOrbit {x : D}
    (hP : DeletedOrbit (M.σ * rawAlpha M Del hclosed) Del
      (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) x)) {y : D}
    (h : M.σ.SameCycle x y) : (M.σ * rawAlpha M Del hclosed).SameCycle x y := by
  classical
  have hxDel : x ∈ Del := hP x rfl
  -- trajectory: `σ^k x = σRaw^k x ∈ Del`.
  have key : ∀ k : ℕ, ((M.σ * rawAlpha M Del hclosed) ^ k) x = (M.σ ^ k) x
      ∧ (M.σ ^ k) x ∈ Del := by
    intro k
    induction k with
    | zero => exact ⟨by simp, by simpa using hxDel⟩
    | succ k ih =>
        obtain ⟨ihEq, ihDel⟩ := ih
        have hraw_del : ((M.σ * rawAlpha M Del hclosed) ^ k) x ∈ Del := ihEq ▸ ihDel
        have heq : ((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x = (M.σ ^ (k+1)) x := by
          have e1 : ((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x
              = M.σ (((M.σ * rawAlpha M Del hclosed) ^ k) x) := by
            rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
              rawAlpha_eq_self_of_mem M Del hclosed hraw_del]
          have e2 : (M.σ ^ (k+1)) x = M.σ ((M.σ ^ k) x) := by rw [pow_succ']; rfl
          rw [e1, e2, ihEq]
        refine ⟨heq, ?_⟩
        apply hP
        apply Quotient.sound
        show (M.σ * rawAlpha M Del hclosed).SameCycle ((M.σ ^ (k+1)) x) x
        exact ⟨-((k+1 : ℕ) : ℤ), by
          rw [← heq, zpow_neg, zpow_natCast, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.coe_pow]⟩
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  exact ⟨(n : ℤ), by rw [zpow_natCast, (key n).1, hn]⟩

/-- The converse: a `σRaw`-`SameCycle` within a deleted `σ`-orbit is a `σ`-`SameCycle`. -/
lemma sigma_sameCycle_iff_sigmaRaw_of_deletedOrbit {x : D}
    (hO : DeletedOrbit M.σ Del (Quotient.mk (cycleSetoid M.σ) x)) {y : D}
    (h : (M.σ * rawAlpha M Del hclosed).SameCycle x y) : M.σ.SameCycle x y := by
  classical
  have hxDel : x ∈ Del := hO x rfl
  have key : ∀ k : ℕ, (M.σ ^ k) x = ((M.σ * rawAlpha M Del hclosed) ^ k) x
      ∧ ((M.σ * rawAlpha M Del hclosed) ^ k) x ∈ Del := by
    intro k
    induction k with
    | zero => exact ⟨by simp, by simpa using hxDel⟩
    | succ k ih =>
        obtain ⟨ihEq, ihDel⟩ := ih
        have hσ_del : (M.σ ^ k) x ∈ Del := ihEq ▸ ihDel
        have heq : (M.σ ^ (k+1)) x = ((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x := by
          have e1 : ((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x
              = M.σ (((M.σ * rawAlpha M Del hclosed) ^ k) x) := by
            rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
              rawAlpha_eq_self_of_mem M Del hclosed ihDel]
          have e2 : (M.σ ^ (k+1)) x = M.σ ((M.σ ^ k) x) := by rw [pow_succ']; rfl
          rw [e1, e2, ihEq]
        refine ⟨heq, ?_⟩
        apply hO
        apply Quotient.sound
        show M.σ.SameCycle (((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x) x
        exact ⟨-((k+1 : ℕ) : ℤ), by
          rw [← heq, zpow_neg, zpow_natCast, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.coe_pow]⟩
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  exact ⟨(n : ℤ), by rw [zpow_natCast, (key n).1, hn]⟩

/-- **`numDeletedOrbits (M.σ * rawAlpha) Del = numDeletedOrbits M.σ Del`.** -/
theorem numDeletedOrbits_sigmaRaw_eq :
    numDeletedOrbits (M.σ * rawAlpha M Del hclosed) Del = numDeletedOrbits M.σ Del := by
  classical
  unfold numDeletedOrbits
  refine Fintype.card_congr ?_
  refine
    { toFun := fun q => ⟨Quotient.mk (cycleSetoid M.σ) q.1.out,
        (deletedOrbit_sigmaRaw_iff M Del hclosed q.1.out).1 (by
          intro z hz; exact q.2 z (by rw [hz]; exact Quotient.out_eq q.1))⟩,
      invFun := fun o => ⟨Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) o.1.out,
        (deletedOrbit_sigmaRaw_iff M Del hclosed o.1.out).2 (by
          intro z hz; exact o.2 z (by rw [hz]; exact Quotient.out_eq o.1))⟩,
      left_inv := ?_, right_inv := ?_ }
  · rintro ⟨q, hq⟩
    apply Subtype.ext
    dsimp only
    nth_rewrite 2 [← Quotient.out_eq q]
    apply Quotient.sound
    show (M.σ * rawAlpha M Del hclosed).SameCycle
      (Quotient.mk (cycleSetoid M.σ) q.out).out q.out
    -- `(mk_σ q.out).out` is `σ`-SameCycle to `q.out`; convert to `σRaw` via deletedness.
    have hsc : M.σ.SameCycle (Quotient.mk (cycleSetoid M.σ) q.out).out q.out :=
      Quotient.exact (Quotient.out_eq (Quotient.mk (cycleSetoid M.σ) q.out))
    -- `q.out`'s `σRaw`-orbit is deleted (q is a deleted `σRaw`-class).
    have hqDel : DeletedOrbit (M.σ * rawAlpha M Del hclosed) Del
        (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) q.out) := by
      intro z hz; exact hq z (by rw [hz]; exact Quotient.out_eq q)
    exact (sigmaRaw_sameCycle_iff_sigma_of_deletedOrbit M Del hclosed hqDel hsc.symm).symm
  · rintro ⟨o, ho⟩
    apply Subtype.ext
    dsimp only
    nth_rewrite 2 [← Quotient.out_eq o]
    apply Quotient.sound
    show M.σ.SameCycle (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) o.out).out o.out
    have hsc : (M.σ * rawAlpha M Del hclosed).SameCycle
        (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) o.out).out o.out :=
      Quotient.exact (Quotient.out_eq
        (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) o.out))
    -- `o.out`'s `σ`-orbit is deleted (o is a deleted `σ`-class); convert via the converse lemma.
    have hoDel : DeletedOrbit M.σ Del (Quotient.mk (cycleSetoid M.σ) o.out) := by
      intro z hz; exact ho z (by rw [hz]; exact Quotient.out_eq o)
    exact (sigma_sameCycle_iff_sigmaRaw_of_deletedOrbit M Del hclosed hoDel hsc.symm).symm

/-! ### Master assembly: the kept combinatorial map's genus slack is zero on a genus-0 `M`

We now have all the bridges.  `rawAlpha` is an edge-deletion sub-involution of `M.α`, so on a
genus-0 (`IsSphereMap`) `M` the raw slack is `0` (`genusSlack_sphere_eq_zero` +
`genusSlack_le_of_subInvolution` + `genusSlack_nonneg`).  The V/F/component splits with the
deleted-class equalities transfer this to the kept slack. -/

/-- `rawAlpha` is an edge-deletion sub-involution of `M.α`. -/
lemma rawAlpha_subInvolution : SubInvolution M.α (rawAlpha M Del hclosed) := by
  refine ⟨rawAlpha_invol M Del hclosed, fun x hx => ?_⟩
  -- where `rawAlpha` moves `x`, it equals `M.α x` (so `x ∉ Del`).
  by_cases hxD : x ∈ Del
  · exact absurd (rawAlpha_eq_self_of_mem M Del hclosed hxD) hx
  · exact rawAlpha_eq_alpha_of_notMem M Del hclosed hxD

/-- **The raw slack of a genus-0 `M` after deleting `Del` is zero** (`d₀` a witness dart). -/
theorem genusSlack_rawAlpha_eq_zero (hsphere : M.IsSphereMap) (d₀ : D) :
    genusSlack M.σ (rawAlpha M Del hclosed) = 0 := by
  have hle : genusSlack M.σ (rawAlpha M Del hclosed) ≤ genusSlack M.σ M.α :=
    genusSlack_le_of_subInvolution M.σ M.α M.α_invol _ (rawAlpha_subInvolution M Del hclosed)
  have hM0 : genusSlack M.σ M.α = 0 := genusSlack_sphere_eq_zero M hsphere d₀
  have hge : 0 ≤ genusSlack M.σ (rawAlpha M Del hclosed) :=
    genusSlack_nonneg M.σ _ (rawAlpha_invol M Del hclosed)
  rw [hM0] at hle
  exact le_antisymm hle hge

/-- The kept edge involution has the same number of edges (transpositions) as `rawAlpha`:
both have support exactly the kept darts. -/
lemma Ehalf_keptAlpha_eq_rawAlpha :
    Ehalf (keptAlpha M Del hsub) = Ehalf (rawAlpha M Del hclosed) := by
  classical
  -- `2 * Ehalf = card support`.  `keptAlpha` is fixed-point-free on the kept subtype, so its
  -- support is all kept darts; `rawAlpha`'s support is exactly the kept darts of `D`.
  have hk : (keptAlpha M Del hsub) ∈ Set.univ := ⟨⟩
  -- `keptAlpha` fixed-point-free:
  have hkff : ∀ d, keptAlpha M Del hsub d ≠ d := by
    intro d hd
    apply M.α_no_fixed d.1
    have := congrArg Subtype.val hd
    rwa [keptAlpha_apply_coe] at this
  have hksupp : Equiv.Perm.support (keptAlpha M Del hsub) = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]; intro d; rw [Equiv.Perm.mem_support]; exact hkff d
  -- `rawAlpha` support = kept darts (its complement is `Del`).
  have hrsupp : Equiv.Perm.support (rawAlpha M Del hclosed) = Finset.univ.filter (· ∉ Del) := by
    ext d
    simp only [Equiv.Perm.mem_support, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [rawAlpha_apply]
    by_cases hd : d ∈ Del
    · simp [hd]
    · simp only [hd, if_false, not_false_iff, iff_true]
      exact fun hc => M.α_no_fixed d hc
  unfold Ehalf
  rw [hksupp, hrsupp, Finset.card_univ]
  -- both cardinalities are `|kept darts|`.
  have : (Finset.univ.filter (· ∉ Del) : Finset D).card
      = Fintype.card {d : D // d ∉ Del} := by
    rw [Fintype.card_subtype]
  rw [this]

/-- **The kept combinatorial map's genus slack is zero** on a genus-0 `M`.  This is the
structural genus-0 certificate: the kept side (an edge-deletion sub-map of the sphere `M`) has
genus slack `0`, hence — when connected — Euler characteristic `2` (no handle). -/
theorem keptMap_genusSlack_eq_zero (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsphere : M.IsSphereMap) (d₀ : D) :
    genusSlack (Equiv.Perm.deleteSet M.σ Del) (keptAlpha M Del hsub) = 0 := by
  classical
  have hraw0 : genusSlack M.σ (rawAlpha M Del hclosed) = 0 :=
    genusSlack_rawAlpha_eq_zero M Del hclosed hsphere d₀
  -- expand both slacks via the count bridges.
  unfold genusSlack at hraw0 ⊢
  -- raw: `2c_raw - numCycles σ + Ehalf rawAlpha - numCycles (σ rawAlpha)`.
  -- kept: `2c_kept - numCycles(deleteSet σ) + Ehalf keptAlpha - numCycles(keptFacePerm)`.
  -- bridges:
  have hcsplit : numComponents M.σ (rawAlpha M Del hclosed)
      = _root_.numComp (keptStepRel M Del hsub) + numDeletedComp M Del hclosed :=
    numComponents_raw_split M Del hclosed hsub
  have hkeptStep_eq : _root_.numComp (keptStepRel M Del hsub)
      = numComponents (Equiv.Perm.deleteSet M.σ Del) (keptAlpha M Del hsub) := by
    rw [numComponents_def]; rfl
  have hDC : numDeletedComp M Del hclosed = numDeletedOrbits M.σ Del :=
    numDeletedComp_eq_numDeletedOrbits M Del hclosed
  have hVsplit : _root_.numCycles M.σ
      = _root_.numCycles (Equiv.Perm.deleteSet M.σ Del) + numDeletedOrbits M.σ Del :=
    numCycles_eq_kept_add_deleted M.σ Del
  have hFsplit : _root_.numCycles (M.σ * rawAlpha M Del hclosed)
      = _root_.numCycles (Equiv.Perm.deleteSet (M.σ * rawAlpha M Del hclosed) Del)
        + numDeletedOrbits (M.σ * rawAlpha M Del hclosed) Del :=
    numCycles_eq_kept_add_deleted (M.σ * rawAlpha M Del hclosed) Del
  have hFbridge : _root_.numCycles (keptFacePerm M Del hclosed hsub)
      = _root_.numCycles (Equiv.Perm.deleteSet (M.σ * rawAlpha M Del hclosed) Del) :=
    numCycles_keptFacePerm_eq M Del hclosed hsub
  have hDF : numDeletedOrbits (M.σ * rawAlpha M Del hclosed) Del = numDeletedOrbits M.σ Del :=
    numDeletedOrbits_sigmaRaw_eq M Del hclosed
  have hEh : Ehalf (keptAlpha M Del hsub) = Ehalf (rawAlpha M Del hclosed) :=
    Ehalf_keptAlpha_eq_rawAlpha M Del hclosed hsub
  -- the kept face permutation is the σα of the kept CombMap.
  have hkeptFace : (Equiv.Perm.deleteSet M.σ Del) * (keptAlpha M Del hsub)
      = keptFacePerm M Del hclosed hsub := rfl
  -- assemble: rewrite `hraw0` (raw slack = 0) into kept quantities.
  rw [hkeptStep_eq] at hcsplit
  rw [hcsplit, hVsplit, ← hEh, hFsplit, hDF, hDC] at hraw0
  -- hraw0 now: `2(c_kept + DV) - (V_kept + DV) + Ehalf keptAlpha
  --   - (numCycles(deleteSet(σ*rawAlpha)) + DV) = 0`.
  -- goal: `2 c_kept - V_kept + Ehalf keptAlpha - numCycles(keptFacePerm) = 0`.
  rw [hkeptFace, hFbridge]
  push_cast at hraw0 ⊢
  linarith

/-- **The kept combinatorial map of a chord-split side of a genus-0 `M` is a disk
(no handle).**  Given a `CombMap K` whose rotation is `deleteSet M.σ Del` and whose edge
involution is `keptAlpha`, if it is connected and has a dart, then its Euler characteristic is
exactly `2`.  This is the reverse inequality `2 ≤ eulerChar` (in fact equality), supplied by the
structural genus monotonicity — the genus-0 certificate that the chord side has no handle. -/
theorem keptMap_eulerChar_eq_two (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsphere : M.IsSphereMap)
    (K : CombMap {d : D // d ∉ Del})
    (hKσ : K.σ = Equiv.Perm.deleteSet M.σ Del) (hKα : K.α = keptAlpha M Del hsub)
    (d : {d : D // d ∉ Del}) (hconn : K.Connected) :
    K.eulerChar = 2 := by
  classical
  have hslack0 : genusSlack (Equiv.Perm.deleteSet M.σ Del) (keptAlpha M Del hsub) = 0 :=
    keptMap_genusSlack_eq_zero M Del hsub hclosed hsphere d.1
  have hc : numComponents K.σ K.α = 1 :=
    numComponents_eq_one_of_connected K hconn d
  have hVc : (K.V : ℤ) = (_root_.numCycles K.σ : ℤ) := by rw [V_eq_numCycles]
  have hEc : (K.E : ℤ) = (Ehalf K.α : ℤ) := by rw [Ehalf_eq_E]
  have hFc : (K.F : ℤ) = (_root_.numCycles (K.σ * K.α) : ℤ) := by rw [F_eq_numCycles]; rfl
  have hslack : genusSlack K.σ K.α = 0 := by rw [hKσ, hKα]; exact hslack0
  unfold genusSlack at hslack
  rw [hc] at hslack
  unfold CombMap.eulerChar
  rw [hVc, hEc, hFc]
  push_cast at hslack ⊢
  linarith

end RawRestrict

/-! ## Section 6.  Threading to the chord-split side maps and `KeptSideIsDisk`

We instantiate the structural certificate at the genuine chord-split side of a near-
triangulation `M` (which carries `M.IsSphereMap` as `hNT.sphere`).  The kept side map
`sideKeptMap₁` is exactly `keptCombMap (sideAlpha₁) (sideSigma₁)` with
`sideSigma₁ = deleteSet M.σ keptDel₁` and `sideAlpha₁ = keptAlpha`, so its Euler characteristic
is `2` whenever it is connected — discharging the `≥ 2` half of `KeptSideIsDisk`. -/

section ChordThreading

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordSideRecon

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- `keptDel₁` is `M.α`-closed (membership is `α`-invariant), the input to the structural
certificate. -/
lemma keptDel₁_sub (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ d, d ∈ data.keptDel₁ ↔ M.α d ∈ data.keptDel₁ := by
  intro d
  have h1 : d ∉ data.keptDel₁ ↔ d ∈ data.keptSet₁ := data.mem_keptDel₁_iff d
  have h2 : M.α d ∉ data.keptDel₁ ↔ M.α d ∈ data.keptSet₁ := data.mem_keptDel₁_iff (M.α d)
  have hkept : M.α d ∈ data.keptSet₁ ↔ d ∈ data.keptSet₁ :=
    data.mem_keptSet₁_alpha_iff hsep d
  classical
  -- `d ∈ Del ↔ ¬ d ∈ keptSet`, similarly for `M.α d`; then use `hkept`.
  have h1' : d ∈ data.keptDel₁ ↔ ¬ d ∈ data.keptSet₁ := by
    rw [← h1]; exact (not_not).symm
  have h2' : M.α d ∈ data.keptDel₁ ↔ ¬ M.α d ∈ data.keptSet₁ := by
    rw [← h2]; exact (not_not).symm
  rw [h1', h2']
  exact (not_congr hkept).symm

lemma keptDel₁_closed (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ d, d ∈ data.keptDel₁ → M.α d ∈ data.keptDel₁ :=
  fun d hd => (keptDel₁_sub data hsep d).1 hd

/-- `sideAlpha₁` equals the abstract `keptAlpha` of `keptDel₁` (both are `M.α` restricted). -/
lemma sideAlpha₁_eq_keptAlpha (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideAlpha₁ hsep
      = SubmapPlanar.keptAlpha M data.keptDel₁ (keptDel₁_sub data hsep) := by
  ext d
  rw [data.sideAlpha₁_apply_coe]
  rfl

/-- **The `≥ 2` no-handle half of `KeptSideIsDisk` at side 1, discharged structurally.**  If the
kept side-1 map is connected and has a dart, its Euler characteristic is `2` — the genus-0
certificate from sub-map planarity (`M` is a sphere via `hNT.sphere`). -/
theorem side₁_keptMap_eulerChar_eq_two (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : {d : D // d ∉ data.keptDel₁})
    (hconn : (sideKeptMap₁ data hsep).Connected) :
    (sideKeptMap₁ data hsep).eulerChar = 2 := by
  refine SubmapPlanar.keptMap_eulerChar_eq_two M data.keptDel₁ (keptDel₁_sub data hsep)
    (keptDel₁_closed data hsep) hNT.sphere (sideKeptMap₁ data hsep) ?_ ?_ d hconn
  · -- `(sideKeptMap₁).σ = sideSigma₁ = filteredRotation M.σ keptDel₁ = deleteSet M.σ keptDel₁`.
    show data.sideSigma₁ = Equiv.Perm.deleteSet M.σ data.keptDel₁
    rfl
  · -- `(sideKeptMap₁).α = sideAlpha₁ = keptAlpha`.
    show data.sideAlpha₁ hsep = SubmapPlanar.keptAlpha M data.keptDel₁ (keptDel₁_sub data hsep)
    exact sideAlpha₁_eq_keptAlpha data hsep

/-- **`Side₁IsDisk` reduces to connectivity of the kept side.**  Given the structural genus-0
certificate, side 1 is a disk (`IsSphereMap`) *iff* its kept map is connected (the `eulerChar`
half is discharged).  This removes the no-handle inequality `2 ≤ eulerChar` from the residue —
its `≤ 2` half is `chi_le_two_of_connected`, its `≥ 2` half is now proved. -/
theorem side₁IsDisk_of_connected (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : {d : D // d ∉ data.keptDel₁})
    (hconn : (sideKeptMap₁ data hsep).Connected) :
    ChordDisk.Side₁IsDisk data hsep :=
  ⟨hconn, side₁_keptMap_eulerChar_eq_two data hsep d hconn⟩

/-- **Headline (the no-handle inequality, structural certificate).**  For a chord split of a
genus-0 near-triangulation `M`, the kept side's Euler characteristic is *at least* `2` (in fact
exactly `2`) whenever the kept side is connected and nonempty — the reverse inequality
`2 ≤ eulerChar(side)` that `ChordDisk` isolated as the only missing half of `KeptSideIsDisk`.
This is supplied here by genus monotonicity under edge deletion, run against `hNT.sphere`
(`eulerChar M = 2`); it is the genus-0-essential certificate, not orbit counting. -/
theorem keptSide_no_handle (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : {d : D // d ∉ data.keptDel₁})
    (hconn : (sideKeptMap₁ data hsep).Connected) :
    2 ≤ (sideKeptMap₁ data hsep).eulerChar :=
  le_of_eq (side₁_keptMap_eulerChar_eq_two data hsep d hconn).symm

end ChordThreading

end ProofsInTheBook.SubmapPlanar

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.SubmapPlanar.genusSlack_remove_le
#print axioms ProofsInTheBook.SubmapPlanar.genusSlack_le_of_subInvolution
#print axioms ProofsInTheBook.SubmapPlanar.genusSlack_sphere_eq_zero
#print axioms ProofsInTheBook.SubmapPlanar.numCycles_eq_kept_add_deleted
#print axioms ProofsInTheBook.SubmapPlanar.keptFacePerm_eq_deleteSet_rawFace
#print axioms ProofsInTheBook.SubmapPlanar.numComponents_raw_split
#print axioms ProofsInTheBook.SubmapPlanar.numDeletedComp_eq_numDeletedOrbits
#print axioms ProofsInTheBook.SubmapPlanar.numDeletedOrbits_sigmaRaw_eq
#print axioms ProofsInTheBook.SubmapPlanar.keptMap_genusSlack_eq_zero
#print axioms ProofsInTheBook.SubmapPlanar.keptMap_eulerChar_eq_two
#print axioms ProofsInTheBook.SubmapPlanar.side₁_keptMap_eulerChar_eq_two
#print axioms ProofsInTheBook.SubmapPlanar.side₁IsDisk_of_connected
#print axioms ProofsInTheBook.SubmapPlanar.keptSide_no_handle
