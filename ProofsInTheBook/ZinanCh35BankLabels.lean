import ProofsInTheBook.ZinanCh35CycleBank
import ProofsInTheBook.ZinanCh35Gates

/-!
# Chapter 35, Step 2′: the BANK LABELS of `SimpleCycleBankTheorem` (the last gap)

`ZinanCh35CycleBank.lean` proved the unconditional count core (`numComp = 2`, the bank orbit
count, `genusSlack = 0`) and the σ-star classifier
`not_mem_edgeSet_of_star_not_cycleDart`.  This file discharges the three residual *label*
fields of `SimpleCycleBankTheorem` — `left_bank`, `right_bank`, `left_right_sep` — so that the
full structure `SimpleCycleBankTheorem M C` is constructible from a sphere simple-graph map.

## The σ-arc walker (the engine)

The local move is the **partial σ-arc walk**.  At the cycle vertex
`w = head (C.dart i) = tail (C.dart (nextIdx i))` the σ-orbit's *only* two cycle darts are
`α (C.dart i)` (reverse, the "right" anchor) and `C.dart (nextIdx i)` (forward, the "left"
anchor); this is exactly `not_mem_edgeSet_of_star_not_cycleDart`.  Walking σ-forward from
`α (C.dart i)` to `C.dart (nextIdx i)` — through powers `1 … p−1` that are strictly between the
two cycle anchors, hence non-cycle by the classifier — produces a
`DualAvoidsCycleStep`-walk.  Its endpoints are:

* `dartFace (σ (α (C.dart i))) = dartFace (α (α (C.dart i))) = dartFace (C.dart i) = faceLeft i`,
* `dartFace (C.dart (nextIdx i)) = faceLeft (nextIdx i)`.

So **`faceLeft i ↝ faceLeft (nextIdx i)`** (one bank), and the mirror walk (from
`C.dart (nextIdx i)` to `α (C.dart i)`) gives **`faceRight (nextIdx i) ↝ faceRight i`** (the
other bank).  Chaining around the cyclic index set connects every `faceLeft i` to `faceLeft j`
and every `faceRight i` to `faceRight j`.

## Separation

`left_right_sep` is then immediate from the discharged Jordan gate
`jordan_simple_cycle2_unconditional` (`¬ faceLeft i₀ ↝ faceRight i₀`): if
`faceLeft i ↝ faceRight j`, chaining through `left_bank` and `right_bank` yields
`faceLeft i ↝ faceRight i`, contradicting the gate.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35BankLabels

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35CycleBank
open Equiv Equiv.Perm

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
variable (C : SimplePrimalCycle M)

/-! ## 0. The σ-arc reachability engine.

`Forbidden e := e ∈ C.edgeSet`.  A single σ-step `dartFace z → dartFace (σ z)` whose dart `z`
has a non-forbidden edge is a `DualAvoidsCycleStep` step. -/

/-- One σ-step is a `DualAvoidsCycleStep` step when `dartEdge z ∉ C.edgeSet`. -/
lemma dualStep_sigma (hsimple : M.IsSimpleGraph) {z : D}
    (hz : M.dartEdge z ∉ C.edgeSet) :
    DualAvoidsCycleStep M C (M.dartFace z) (M.dartFace (M.σ z)) := by
  refine ⟨z, hz, rfl, ?_⟩
  rw [ZinanCh35StarConn.dartFace_sigma_eq_alpha]

/-- **The σ-arc walker.**  If every dart `σ^j a` for `0 ≤ j < p` is non-cycle, then
`dartFace a` reaches `dartFace ((σ^p) a)` by a `DualAvoidsCycleStep`-walk. -/
lemma reflTransGen_dualStep_sigma_pow (hsimple : M.IsSimpleGraph) (a : D) :
    ∀ p : ℕ, (∀ j : ℕ, j < p → M.dartEdge ((M.σ ^ j) a) ∉ C.edgeSet) →
      Relation.ReflTransGen (DualAvoidsCycleStep M C)
        (M.dartFace a) (M.dartFace ((M.σ ^ p) a)) := by
  intro p
  induction p with
  | zero => intro _; simpa using Relation.ReflTransGen.refl
  | succ k ih =>
      intro havoid
      have hreach := ih (fun j hj => havoid j (by omega))
      refine hreach.tail ?_
      have heq : M.σ ((M.σ ^ k) a) = (M.σ ^ (k + 1)) a := by rw [pow_succ']; rfl
      have hstep := dualStep_sigma C hsimple (z := (M.σ ^ k) a) (havoid k (by omega))
      rwa [heq] at hstep

/-! ## 1. Orbit-distinctness at a cycle vertex.

For the avoidance hypothesis we need: the σ-powers strictly between the two cycle anchors are
distinct from both anchors.  Distinctness from the *base* anchor is `sigma_pow_ne_self`
(reused from `ZinanCh35StarConn`); distinctness from the *target* anchor is "first occurrence is
unique within one orbit period". -/

/-- `(σ^m) b ≠ b` for `0 < m < L` (`L = #(σ.cycleOf b).support`), `b ∈ σ.support`. -/
lemma sigma_pow_ne_self {b : D} (hb : b ∈ M.σ.support) {m : ℕ}
    (hm0 : 0 < m) (hmL : m < (M.σ.cycleOf b).support.card) : (M.σ ^ m) b ≠ b :=
  ZinanCh35StarConn.sigma_pow_ne_self_of_lt hb hm0 hmL

/-- Within one orbit period the powers are injective: `(σ^j) b = (σ^p) b` with `j, p < L`
forces `j = p`. -/
lemma sigma_pow_inj_of_lt {b : D} (hb : b ∈ M.σ.support) {j p : ℕ}
    (hjL : j < (M.σ.cycleOf b).support.card) (hpL : p < (M.σ.cycleOf b).support.card)
    (h : (M.σ ^ j) b = (M.σ ^ p) b) : j = p := by
  -- `cycleOf` and support card are invariant along the orbit; reduce to `sigma_pow_ne_self`
  -- on the element `c := (σ^j) b`, which `(σ^(p-j))` (resp. `(σ^(j-p))`) fixes.
  by_contra hne
  rcases le_or_gt j p with hjp | hjp
  · -- `(σ^(p-j))` fixes `c = (σ^j) b`.
    set c := (M.σ ^ j) b with hc
    have hscbc : M.σ.SameCycle b c := ⟨(j : ℤ), by rw [zpow_natCast]⟩
    have hcsupp : c ∈ M.σ.support := (SameCycle.mem_support_iff hscbc).mp hb
    have hcard : (M.σ.cycleOf c).support.card = (M.σ.cycleOf b).support.card := by
      rw [hscbc.cycleOf_eq]
    have hpos : 0 < p - j := by omega
    have hlt : p - j < (M.σ.cycleOf c).support.card := by rw [hcard]; omega
    apply sigma_pow_ne_self (M := M) hcsupp hpos hlt
    rw [hc, ← Equiv.Perm.mul_apply, ← pow_add, show p - j + j = p by omega, ← h]
  · set c := (M.σ ^ p) b with hc
    have hscbc : M.σ.SameCycle b c := ⟨(p : ℤ), by rw [zpow_natCast]⟩
    have hcsupp : c ∈ M.σ.support := (SameCycle.mem_support_iff hscbc).mp hb
    have hcard : (M.σ.cycleOf c).support.card = (M.σ.cycleOf b).support.card := by
      rw [hscbc.cycleOf_eq]
    have hpos : 0 < j - p := by omega
    have hlt : j - p < (M.σ.cycleOf c).support.card := by rw [hcard]; omega
    apply sigma_pow_ne_self (M := M) hcsupp hpos hlt
    rw [hc, ← Equiv.Perm.mul_apply, ← pow_add, show j - p + p = j by omega, h]

/-! ## 2. The two cycle anchors at vertex `v_{nextIdx i}` and their σ-relation. -/

/-- The reverse anchor `α (C.dart i)` is in `σ.support`: its σ-orbit also contains the distinct
forward dart `C.dart (nextIdx i)` (same tail), so the orbit is nontrivial. -/
lemma rev_mem_support (i : Fin C.len) : M.α (C.dart i) ∈ M.σ.support := by
  rw [Equiv.Perm.mem_support]
  intro hfix
  -- if `σ (α (C.dart i)) = α (C.dart i)`, the σ-orbit of `α (C.dart i)` is a singleton, but it
  -- must also contain `C.dart (nextIdx i)` (same tail), which is distinct.
  have hsc : M.σ.SameCycle (M.α (C.dart i)) (C.dart (C.nextIdx i)) :=
    sigma_sameCycle_alphaDart_dart_next C i
  obtain ⟨n, hn⟩ := hsc
  -- `σ` fixes `α (C.dart i)`, so `(σ^n) (α (C.dart i)) = α (C.dart i)`.
  have hpow : ∀ k : ℤ, (M.σ ^ k) (M.α (C.dart i)) = M.α (C.dart i) := by
    intro k
    have : ∀ m : ℕ, (M.σ ^ m) (M.α (C.dart i)) = M.α (C.dart i) := by
      intro m
      induction m with
      | zero => simp
      | succ t iht => rw [pow_succ', Equiv.Perm.mul_apply, iht, hfix]
    rcases k with k | k
    · simpa using this k
    · -- negative powers: `σ⁻¹` also fixes it.
      have hinv : M.σ⁻¹ (M.α (C.dart i)) = M.α (C.dart i) := by
        rw [Equiv.Perm.inv_eq_iff_eq, hfix]
      have : ∀ m : ℕ, (M.σ⁻¹ ^ m) (M.α (C.dart i)) = M.α (C.dart i) := by
        intro m
        induction m with
        | zero => simp
        | succ t iht => rw [pow_succ', Equiv.Perm.mul_apply, iht, hinv]
      have hk := this (k + 1)
      rw [zpow_negSucc, ← inv_pow]
      exact hk
  have : C.dart (C.nextIdx i) = M.α (C.dart i) := by rw [← hn]; exact hpow n
  exact (dart_ne_alphaDart C (C.nextIdx i) i) this

/-! ## 3. The bank-step lemmas. -/

/-- **Left-bank step.**  `faceLeft i ↝ faceLeft (nextIdx i)` via the σ-arc from
`α (C.dart i)` to `C.dart (nextIdx i)`. -/
lemma left_bank_step (hsimple : M.IsSimpleGraph) (i : Fin C.len) :
    Relation.ReflTransGen (DualAvoidsCycleStep M C)
      (C.faceLeft i) (C.faceLeft (C.nextIdx i)) := by
  set b := M.α (C.dart i) with hb
  have hbsupp : b ∈ M.σ.support := rev_mem_support C i
  set L := (M.σ.cycleOf b).support.card with hL
  -- `fwd = C.dart (nextIdx i)` is in the σ-orbit of `b`, at some power `p`, `0 < p < L`.
  have hsc : M.σ.SameCycle b (C.dart (C.nextIdx i)) := sigma_sameCycle_alphaDart_dart_next C i
  obtain ⟨p, hpL, hp⟩ := hsc.exists_pow_eq_of_mem_support hbsupp
  have hpos : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · exfalso; rw [h0, pow_zero] at hp; simp only [Equiv.Perm.coe_one, id] at hp
      exact (dart_ne_alphaDart C (C.nextIdx i) i) hp.symm
    · exact h0
  -- the walk from `σ b` to `(σ^p) b = fwd`: re-anchor at `σ b = (σ^1) b`.
  -- Express as: `dartFace (σ b) ↝ dartFace ((σ^p) b)` using powers `1..p-1` of `b` from `σ b`.
  -- We walk `(σ^j) (σ b) = (σ^(j+1)) b` for `0 ≤ j < p-1`.
  have hwalk :
      Relation.ReflTransGen (DualAvoidsCycleStep M C)
        (M.dartFace (M.σ b)) (M.dartFace ((M.σ ^ (p - 1)) (M.σ b))) := by
    apply reflTransGen_dualStep_sigma_pow C hsimple (M.σ b)
    intro j hj
    -- `(σ^j) (σ b) = (σ^(j+1)) b`, a non-cycle dart (strictly between the two anchors).
    have hjp1 : j + 1 < p := by omega
    have heq : (M.σ ^ j) (M.σ b) = (M.σ ^ (j + 1)) b := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ]
    rw [heq]
    -- non-cycle via the classifier: same σ-cycle as `b`, ≠ `b`, ≠ `fwd`.
    apply not_mem_edgeSet_of_star_not_cycleDart C hsimple (i := i)
    · -- `σ.SameCycle (α (C.dart i)) ((σ^(j+1)) b)`
      exact ⟨(j + 1 : ℕ), by rw [zpow_natCast]⟩
    · -- `(σ^(j+1)) b ≠ b = α (C.dart i)`
      exact sigma_pow_ne_self (M := M) hbsupp (by omega) (by omega)
    · -- `(σ^(j+1)) b ≠ C.dart (nextIdx i) = (σ^p) b`
      intro hcon
      have : j + 1 = p := sigma_pow_inj_of_lt (M := M) hbsupp (by omega) hpL (by rw [hcon, hp])
      omega
  -- rewrite both endpoints.
  have hstart : M.dartFace (M.σ b) = C.faceLeft i := by
    rw [ZinanCh35StarConn.dartFace_sigma_eq_alpha, hb, M.alpha_alpha]; rfl
  have hend : M.dartFace ((M.σ ^ (p - 1)) (M.σ b)) = C.faceLeft (C.nextIdx i) := by
    have heq : (M.σ ^ (p - 1)) (M.σ b) = (M.σ ^ p) b := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ, show (p - 1) + 1 = p by omega]
    rw [heq, hp]; rfl
  rw [hstart, hend] at hwalk
  exact hwalk

/-- **Right-bank step.**  `faceRight (nextIdx i) ↝ faceRight i` via the σ-arc from
`C.dart (nextIdx i)` to `α (C.dart i)`. -/
lemma right_bank_step (hsimple : M.IsSimpleGraph) (i : Fin C.len) :
    Relation.ReflTransGen (DualAvoidsCycleStep M C)
      (C.faceRight (C.nextIdx i)) (C.faceRight i) := by
  set b := C.dart (C.nextIdx i) with hb
  -- `b ∈ σ.support`: its orbit contains `α (C.dart i) ≠ b` (same tail).
  have hbsupp : b ∈ M.σ.support := by
    rw [Equiv.Perm.mem_support]
    intro hfix
    have hsc : M.σ.SameCycle b (M.α (C.dart i)) :=
      (sigma_sameCycle_alphaDart_dart_next C i).symm
    obtain ⟨n, hn⟩ := hsc
    have hpow : ∀ k : ℤ, (M.σ ^ k) b = b := by
      intro k
      have hnat : ∀ m : ℕ, (M.σ ^ m) b = b := by
        intro m; induction m with
        | zero => simp
        | succ t iht => rw [pow_succ', Equiv.Perm.mul_apply, iht, hfix]
      rcases k with k | k
      · simpa using hnat k
      · have hinv : M.σ⁻¹ b = b := by rw [Equiv.Perm.inv_eq_iff_eq, hfix]
        have hinvm : ∀ m : ℕ, (M.σ⁻¹ ^ m) b = b := by
          intro m; induction m with
          | zero => simp
          | succ t iht => rw [pow_succ', Equiv.Perm.mul_apply, iht, hinv]
        have hk := hinvm (k + 1); rw [zpow_negSucc, ← inv_pow]; exact hk
    have : M.α (C.dart i) = b := by rw [← hn]; exact hpow n
    exact (dart_ne_alphaDart C (C.nextIdx i) i) (hb ▸ this.symm)
  set L := (M.σ.cycleOf b).support.card with hL
  have hsc : M.σ.SameCycle b (M.α (C.dart i)) :=
    (sigma_sameCycle_alphaDart_dart_next C i).symm
  obtain ⟨p, hpL, hp⟩ := hsc.exists_pow_eq_of_mem_support hbsupp
  have hpos : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · exfalso; rw [h0, pow_zero] at hp; simp only [Equiv.Perm.coe_one, id] at hp
      exact (dart_ne_alphaDart C (C.nextIdx i) i) (hb ▸ hp)
    · exact h0
  have hwalk :
      Relation.ReflTransGen (DualAvoidsCycleStep M C)
        (M.dartFace (M.σ b)) (M.dartFace ((M.σ ^ (p - 1)) (M.σ b))) := by
    apply reflTransGen_dualStep_sigma_pow C hsimple (M.σ b)
    intro j hj
    have hjp1 : j + 1 < p := by omega
    have heq : (M.σ ^ j) (M.σ b) = (M.σ ^ (j + 1)) b := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ]
    rw [heq]
    -- non-cycle: `(σ^(j+1)) b` is in σ-orbit of `α (C.dart i)`, distinct from both anchors.
    apply not_mem_edgeSet_of_star_not_cycleDart C hsimple (i := i)
    · -- `σ.SameCycle (α (C.dart i)) ((σ^(j+1)) b)`: both same-cycle as `b`.
      have h1 : M.σ.SameCycle (M.α (C.dart i)) b :=
        (sigma_sameCycle_alphaDart_dart_next C i)
      exact h1.trans ⟨(j + 1 : ℕ), by rw [zpow_natCast]⟩
    · -- `(σ^(j+1)) b ≠ α (C.dart i) = (σ^p) b`
      intro hcon
      have : j + 1 = p := sigma_pow_inj_of_lt (M := M) hbsupp (by omega) hpL (by rw [hcon, hp])
      omega
    · -- `(σ^(j+1)) b ≠ C.dart (nextIdx i) = b`
      have hne : (M.σ ^ (j + 1)) b ≠ b :=
        sigma_pow_ne_self (M := M) hbsupp (by omega) (by omega)
      rw [hb]; exact hne
  have hstart : M.dartFace (M.σ b) = C.faceRight (C.nextIdx i) := by
    rw [ZinanCh35StarConn.dartFace_sigma_eq_alpha, hb]; rfl
  have hend : M.dartFace ((M.σ ^ (p - 1)) (M.σ b)) = C.faceRight i := by
    have heq : (M.σ ^ (p - 1)) (M.σ b) = (M.σ ^ p) b := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ, show (p - 1) + 1 = p by omega]
    rw [heq, hp]; rfl
  rw [hstart, hend] at hwalk
  exact hwalk

/-! ## 4. Chaining around the cyclic index set.

`nextIdx` is a cyclic permutation; chaining the per-edge bank steps connects every index to
index `0`, hence every pair.  We prove the "all reach index 0" form by induction on the index
value, walking `i → prevIdx i → … → 0` via `prevIdx`. -/

/-- The forward face at any index reaches the forward face at index `0`. -/
lemma left_reaches_zero (hsimple : M.IsSimpleGraph) (i : Fin C.len) :
    Relation.ReflTransGen (DualAvoidsCycleStep M C)
      (C.faceLeft i) (C.faceLeft ⟨0, C.len_pos⟩) := by
  -- strong induction on the index value, quantified over the bound.
  suffices H : ∀ n : ℕ, ∀ hn : n < C.len,
      Relation.ReflTransGen (DualAvoidsCycleStep M C)
        (C.faceLeft ⟨n, hn⟩) (C.faceLeft ⟨0, C.len_pos⟩) from H i.1 i.2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; exact Relation.ReflTransGen.refl
    · set i : Fin C.len := ⟨n, hn⟩ with hi
      have hprev : (C.prevIdx i).1 = n - 1 := by
        rw [SimplePrimalCycle.prevIdx_val, hi]
        have : n + (C.len - 1) = (n - 1) + C.len := by have := C.len_pos; omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hnext : C.nextIdx (C.prevIdx i) = i := C.nextIdx_prevIdx i
      have hstep := left_bank_step C hsimple (C.prevIdx i)
      rw [hnext] at hstep
      have hih := ih (n - 1) (by omega) (by omega)
      have hsymm : Relation.ReflTransGen (DualAvoidsCycleStep M C)
          (C.faceLeft i) (C.faceLeft (C.prevIdx i)) :=
        Relation.ReflTransGen.symmetric (fun _ _ h => dualAvoidsCycleStep_symm C h) hstep
      have hih' : Relation.ReflTransGen (DualAvoidsCycleStep M C)
          (C.faceLeft (C.prevIdx i)) (C.faceLeft ⟨0, C.len_pos⟩) := by
        have hpe : (C.prevIdx i) = ⟨n - 1, by omega⟩ := Fin.ext hprev
        rw [hpe]; exact hih
      exact hsymm.trans hih'

/-- The reverse face at any index reaches the reverse face at index `0`. -/
lemma right_reaches_zero (hsimple : M.IsSimpleGraph) (i : Fin C.len) :
    Relation.ReflTransGen (DualAvoidsCycleStep M C)
      (C.faceRight i) (C.faceRight ⟨0, C.len_pos⟩) := by
  suffices H : ∀ n : ℕ, ∀ hn : n < C.len,
      Relation.ReflTransGen (DualAvoidsCycleStep M C)
        (C.faceRight ⟨n, hn⟩) (C.faceRight ⟨0, C.len_pos⟩) from H i.1 i.2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; exact Relation.ReflTransGen.refl
    · set i : Fin C.len := ⟨n, hn⟩ with hi
      have hprev : (C.prevIdx i).1 = n - 1 := by
        rw [SimplePrimalCycle.prevIdx_val, hi]
        have : n + (C.len - 1) = (n - 1) + C.len := by have := C.len_pos; omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hnext : C.nextIdx (C.prevIdx i) = i := C.nextIdx_prevIdx i
      have hstep := right_bank_step C hsimple (C.prevIdx i)
      rw [hnext] at hstep
      have hih := ih (n - 1) (by omega) (by omega)
      have hih' : Relation.ReflTransGen (DualAvoidsCycleStep M C)
          (C.faceRight (C.prevIdx i)) (C.faceRight ⟨0, C.len_pos⟩) := by
        have hpe : (C.prevIdx i) = ⟨n - 1, by omega⟩ := Fin.ext hprev
        rw [hpe]; exact hih
      exact hstep.trans hih'

/-! ## 5. The bank label fields. -/

/-- **`left_bank`.**  Any two forward faces are `DualAvoidsCycleStep`-connected. -/
theorem left_bank_holds (hsimple : M.IsSimpleGraph) (i j : Fin C.len) :
    Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceLeft i) (C.faceLeft j) := by
  have hi := left_reaches_zero C hsimple i
  have hj := left_reaches_zero C hsimple j
  exact hi.trans
    (Relation.ReflTransGen.symmetric (fun _ _ h => dualAvoidsCycleStep_symm C h) hj)

/-- **`right_bank`.**  Any two reverse faces are `DualAvoidsCycleStep`-connected. -/
theorem right_bank_holds (hsimple : M.IsSimpleGraph) (i j : Fin C.len) :
    Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceRight i) (C.faceRight j) := by
  have hi := right_reaches_zero C hsimple i
  have hj := right_reaches_zero C hsimple j
  exact hi.trans
    (Relation.ReflTransGen.symmetric (fun _ _ h => dualAvoidsCycleStep_symm C h) hj)

/-! ## 6. Separation via the discharged Jordan gate. -/

/-- **`left_right_sep`.**  No forward face reaches any reverse face avoiding the cycle.  If it
did, chaining through the two bank classes yields `faceLeft j ↝ faceRight j`, contradicting the
discharged Jordan gate `jordan_simple_cycle2_unconditional`. -/
theorem left_right_sep_holds (hsphere : M.IsSphereMap) (hsimple : M.IsSimpleGraph)
    (i j : Fin C.len) :
    ¬ Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceLeft i) (C.faceRight j) := by
  intro hreach
  -- `faceLeft j ↝ faceLeft i ↝ faceRight j ↝ faceRight j` (j↝j trivial), giving the forbidden pair.
  have hLj : Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceLeft j) (C.faceLeft i) :=
    left_bank_holds C hsimple j i
  have hchain : Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceLeft j) (C.faceRight j) :=
    hLj.trans hreach
  -- this IS `DualReachableAvoidingCycle M C (faceLeft j) (faceRight j)`.
  have hbad : DualReachableAvoidingCycle M C (C.faceLeft j) (C.faceRight j) := hchain
  exact (C.jordan_simple_cycle2_unconditional hsphere.2 hsphere.1 j) hbad

/-! ## 7. Assembly: the full `SimpleCycleBankTheorem`, all six fields. -/

/-- **The full general simple-cycle bank theorem.**  For an arbitrary `SimplePrimalCycle` on a
sphere simple-graph map, all six fields of `SimpleCycleBankTheorem` are discharged: the count
core (`numComp = 2`, the bank orbit count, `genusSlack = 0`) unconditionally from
`ZinanCh35CycleBank`, and the three bank labels (`left_bank`, `right_bank`, `left_right_sep`)
from the σ-arc walker + the discharged Jordan gate. -/
def simpleCycleBankTheorem_holds (hsphere : M.IsSphereMap) (hsimple : M.IsSimpleGraph) :
    SimpleCycleBankTheorem M C where
  dual_numComp_two := dualAvoidsCycle_numComp_two C hsphere hsimple
  bankOrbitCount := bankCount_holds C
  slack_zero := genusSlack_cycleDualAlpha_eq_zero C hsphere
  left_bank := left_bank_holds C hsimple
  right_bank := right_bank_holds C hsimple
  left_right_sep := left_right_sep_holds C hsphere hsimple

end ProofsInTheBook.ZinanCh35BankLabels

/-! ## Axiom audit (expect clean-3: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35BankLabels.left_bank_holds
#print axioms ProofsInTheBook.ZinanCh35BankLabels.right_bank_holds
#print axioms ProofsInTheBook.ZinanCh35BankLabels.left_right_sep_holds
#print axioms ProofsInTheBook.ZinanCh35BankLabels.simpleCycleBankTheorem_holds
