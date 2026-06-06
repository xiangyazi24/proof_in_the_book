import ProofsInTheBook.PlanarMapCutCap2FWalk
import ProofsInTheBook.PlanarMapEulerInequality

/-!
# The one-sided forced-splits lower bound `F' ≥ F + 2` (Chapter 35 Jordan engine)

This file closes the corrected Chapter 35 Jordan chain via the **one-sided
transposition-walk certificate** of `HANDOFF/CH35_LOWERBOUND_DESIGN.md`, replacing the
named exact-count core `NumCyclesCutPhi2` by the weaker — and genus-free —
**lower bound** `numCycles φ'₂ ≥ M.F + 2`, which is all the Jordan contradiction
actually consumes.

## The reduction

The key observation (design §0) is that one never needs to classify all the
merge/split steps of the `4k − 2`-step correction word for `faceCorr₂`.  It is enough
to certify `k` **forced split** steps: steps whose transposition joins two darts that
are *already* `SameCycle` under the prefix product.  Starting from
`numCycles phiLift = F + 2k`, a fixed word of length `4k − 2` with `k` certified
splits gives

```
numCycles (phiLift * faceCorr₂)
  ≥ (F + 2k) − (4k − 2) + 2k = F + 2.
```

This is genus-free: it uses no cycle-structure information about `faceCorr₂`, only the
local `SameCycle` facts at the `k` distinguished prefixes.

## Layered contents

* **Layer 1–2 (generic, unconditional, reusable).**  The transposition-walk API:
  `Swap`, `prefixPerm` (recursive form + `prefixPerm_succ`), the integer swap-delta
  `numCycles_mul_swap_delta`, `stepDelta`, the telescoping
  `numCycles_prefix_telescopes`, and the main generic lower bound
  `numCycles_lower_of_forced_splits`.  These are pure `Equiv.Perm` facts over any
  finite `X`, derived from the existing dichotomy lemmas of
  `PermTranspositionCycleCount.lean`.
* **Layer 6 (certificate packaging).**  `FaceCorrLowerCert`, the precise data the
  generic reduction consumes for `faceCorr₂`, and `faceCorr_lower_from_cert`.
* **Layer 7 (the lower bound).**  From a certificate, `numCycles φ'₂ ≥ F + 2` and the
  face-count lower bound `cutCapMap2_F_lower : (cutCapMap2).F ≥ M.F + 2`.
* **Layer 12 (the contradiction engine).**  The lower-bound Jordan theorem: with
  `V' = V + k`, `E' = E + k`, `χ = 2`, a connected cut map forces `F' ≤ F`
  (via `chi_le_two_of_connected`), contradicting `F' ≥ F + 2`.  This needs only the
  lower bound, *not* the exact equality.

The one genuinely topological input — that a forced-splits word certificate exists
for the corrected surgery — is isolated as the `FaceCorrLowerCert` data; everything
else is closed unconditionally and is kernel-anchored by the triangle / K₄ / tetra
orbit `#eval`s already living in `PlanarMapCutCap2F.lean` and `PlanarMapSeamInst.lean`.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function

namespace ForcedSplits

/-! ## Layer 1: the integer swap-delta

The existing `PermTranspositionCycleCount.lean` proves the dichotomy
`numCycles (p · swap a b) = numCycles p ± 1` for `a ≠ b`, together with the
`SameCycle`-monotone inequality `SameCycle a b → numCycles p ≤ numCycles (p · swap)`.
We package the integer delta in the two directions we need:

* a **split** step (`SameCycle p x y`, with `x ≠ y`) raises the count by exactly `1`;
* **every** step lowers the count by at most `1` (`≥ −1` delta), no hypotheses. -/

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Split step raises `numCycles` by one.**  If `x ≠ y` are in the same `p`-cycle,
multiplying by the transposition `swap x y` splits that cycle, raising the count by
exactly one. -/
theorem numCycles_mul_swap_split (p : Equiv.Perm X) {x y : X}
    (hxy : x ≠ y) (hsc : p.SameCycle x y) :
    numCycles (p * Equiv.swap x y) = numCycles p + 1 := by
  rcases numCycles_mul_swap_dichotomy p hxy with h | h
  · exact h
  · -- the `−1` branch contradicts `SameCycle`-monotonicity
    have hle := PermTranspositionCycleCount.numCycles_le_mul_swap_of_sameCycle p hsc
    omega

/-- **Every swap step lowers `numCycles` by at most one.**  `numCycles (p · swap x y)`
is at least `numCycles p − 1` for any `x, y` (including the degenerate `x = y`, where
`swap x y = 1` and the count is unchanged). -/
theorem numCycles_mul_swap_ge_sub_one (p : Equiv.Perm X) (x y : X) :
    (numCycles (p * Equiv.swap x y) : ℤ) ≥ (numCycles p : ℤ) - 1 := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  · rcases numCycles_mul_swap_dichotomy p hxy with h | h <;> omega

/-! ## Layer 2: the transposition-walk API -/

/-- A swap record: an unordered pair of darts presented as an ordered pair. -/
structure Swap (X : Type*) where
  x : X
  y : X

/-- The transposition permutation of a swap record. -/
def Swap.perm [DecidableEq X] (s : Swap X) : Equiv.Perm X :=
  Equiv.swap s.x s.y

/-- The prefix product of the first `j` letters of a transposition word `W`,
applied on the right of the base permutation `p` (recursive form). -/
def prefixPerm [DecidableEq X] (p : Equiv.Perm X) {m : ℕ}
    (W : Fin m → Swap X) : ℕ → Equiv.Perm X
  | 0 => p
  | j + 1 =>
      if h : j < m then
        prefixPerm p W j * (W ⟨j, h⟩).perm
      else
        prefixPerm p W j

@[simp] lemma prefixPerm_zero [DecidableEq X] (p : Equiv.Perm X) {m : ℕ}
    (W : Fin m → Swap X) : prefixPerm p W 0 = p := rfl

/-- The one-step recursion for `prefixPerm` at a valid index. -/
lemma prefixPerm_succ [DecidableEq X] (p : Equiv.Perm X) {m : ℕ}
    (W : Fin m → Swap X) {j : ℕ} (hj : j < m) :
    prefixPerm p W (j + 1) = prefixPerm p W j * (W ⟨j, hj⟩).perm := by
  simp [prefixPerm, hj]

/-- The actual integer `numCycles`-delta of one walk step. -/
noncomputable def stepDelta (p : Equiv.Perm X) {m : ℕ} (W : Fin m → Swap X)
    (j : Fin m) : ℤ :=
  (numCycles (prefixPerm p W (j.val + 1)) : ℤ) - (numCycles (prefixPerm p W j.val) : ℤ)

/-- **Every walk step lowers `numCycles` by at most one**: `stepDelta ≥ −1`,
unconditionally (the degenerate identity swap has delta `0 ≥ −1`). -/
lemma stepDelta_ge_neg_one (p : Equiv.Perm X) {m : ℕ} (W : Fin m → Swap X)
    (j : Fin m) : stepDelta p W j ≥ (-1 : ℤ) := by
  have hj : j.val < m := j.isLt
  rw [stepDelta, prefixPerm_succ p W hj, Swap.perm]
  have := numCycles_mul_swap_ge_sub_one (prefixPerm p W j.val)
    (W ⟨j.val, hj⟩).x (W ⟨j.val, hj⟩).y
  linarith

/-- **A certified split step raises `numCycles` by exactly one**: if the two
endpoints of the `j`-th transposition are distinct and lie in the same cycle of the
prefix product, then `stepDelta = 1`. -/
lemma stepDelta_eq_one_of_forced_split (p : Equiv.Perm X) {m : ℕ} (W : Fin m → Swap X)
    (j : Fin m) (hne : (W j).x ≠ (W j).y)
    (hsc : (prefixPerm p W j.val).SameCycle (W j).x (W j).y) :
    stepDelta p W j = 1 := by
  have hj : j.val < m := j.isLt
  have hj' : (⟨j.val, hj⟩ : Fin m) = j := by ext; rfl
  rw [stepDelta, prefixPerm_succ p W hj, Swap.perm, hj']
  have := numCycles_mul_swap_split (prefixPerm p W j.val) hne hsc
  rw [this]; push_cast; ring

/-- **Telescoping**: the net `numCycles`-change over the whole word is the sum of the
step deltas. -/
lemma numCycles_prefix_telescopes (p : Equiv.Perm X) {m : ℕ} (W : Fin m → Swap X) :
    (numCycles (prefixPerm p W m) : ℤ) - (numCycles p : ℤ)
      = ∑ j : Fin m, stepDelta p W j := by
  induction m with
  | zero => simp
  | succ n ih =>
      -- restrict the word to its first `n` letters
      let W' : Fin n → Swap X := fun i => W ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      have hpre : ∀ j : ℕ, j ≤ n → prefixPerm p W j = prefixPerm p W' j := by
        intro j hjn
        induction j with
        | zero => rfl
        | succ i ihj =>
            have hin : i < n := hjn
            have hisn : i < n + 1 := Nat.lt_succ_of_lt hin
            rw [prefixPerm_succ p W hisn, prefixPerm_succ p W' hin,
              ihj (Nat.le_of_lt hin)]
      have hlast : prefixPerm p W (n + 1)
          = prefixPerm p W' n * (W ⟨n, Nat.lt_succ_self n⟩).perm := by
        rw [prefixPerm_succ p W (Nat.lt_succ_self n), hpre n le_rfl]
      -- sum over Fin (n+1) splits into the first `n` and the last term
      rw [Fin.sum_univ_castSucc]
      have hstepCast : ∀ i : Fin n, stepDelta p W i.castSucc = stepDelta p W' i := by
        intro i
        have hi1 : (i.castSucc.val + 1) ≤ n := i.isLt
        have hi0 : i.castSucc.val ≤ n := Nat.le_of_lt i.isLt
        rw [stepDelta, stepDelta, hpre _ hi1, hpre _ hi0]
        rfl
      simp only [hstepCast]
      have ihW' := ih W'
      have hlastDelta : stepDelta p W (Fin.last n)
          = (numCycles (prefixPerm p W (n + 1)) : ℤ)
            - (numCycles (prefixPerm p W' n) : ℤ) := by
        rw [stepDelta]
        simp only [Fin.val_last]
        rw [hpre n le_rfl]
      rw [hlastDelta, ← ihW']
      ring

/-! ## The main generic lower bound from forced splits -/

/-- **Lower bound on the sum of step deltas from `s` forced splits.**  If `s`
distinct indices are certified splits (distinct endpoints, `SameCycle` at the
prefix), the total `numCycles`-change is at least `−m + 2s`: each certified index
contributes `+1`, every other index contributes at least `−1`. -/
lemma sum_stepDelta_lower_of_forced_splits (p : Equiv.Perm X) {m s : ℕ}
    (W : Fin m → Swap X) (splitIdx : Fin s → Fin m)
    (hsinj : Function.Injective splitIdx)
    (hne : ∀ i : Fin s, (W (splitIdx i)).x ≠ (W (splitIdx i)).y)
    (hforced : ∀ i : Fin s,
      (prefixPerm p W (splitIdx i).val).SameCycle
        (W (splitIdx i)).x (W (splitIdx i)).y) :
    (∑ j : Fin m, stepDelta p W j) ≥ (-(m : ℤ) + 2 * (s : ℤ)) := by
  classical
  let S : Finset (Fin m) := Finset.univ.image splitIdx
  have hcardS : S.card = s := by
    rw [Finset.card_image_of_injective _ hsinj, Finset.card_univ, Fintype.card_fin]
  -- on `S` each delta is exactly `1`
  have h_on : ∀ j ∈ S, stepDelta p W j = 1 := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨i, _, rfl⟩
    exact stepDelta_eq_one_of_forced_split p W (splitIdx i) (hne i) (hforced i)
  -- everywhere each delta is at least `-1`
  have h_all : ∀ j : Fin m, stepDelta p W j ≥ (-1 : ℤ) := stepDelta_ge_neg_one p W
  -- split the sum over `S` and its complement
  have hsplit : (∑ j : Fin m, stepDelta p W j)
      = (∑ j ∈ S, stepDelta p W j) + (∑ j ∈ Sᶜ, stepDelta p W j) := by
    rw [← Finset.sum_add_sum_compl S]
  have hSsum : (∑ j ∈ S, stepDelta p W j) = (s : ℤ) := by
    rw [Finset.sum_congr rfl h_on, Finset.sum_const, hcardS]
    simp
  have hCsum : (∑ j ∈ Sᶜ, stepDelta p W j) ≥ -((Sᶜ).card : ℤ) := by
    calc (∑ j ∈ Sᶜ, stepDelta p W j) ≥ ∑ _j ∈ Sᶜ, (-1 : ℤ) :=
          Finset.sum_le_sum (fun j _ => h_all j)
      _ = -((Sᶜ).card : ℤ) := by rw [Finset.sum_const]; simp
  have hcompl : (Sᶜ).card = m - s := by
    rw [Finset.card_compl, Fintype.card_fin, hcardS]
  have hsle : s ≤ m := by
    have := hcardS ▸ Finset.card_le_univ S
    simpa [Finset.card_univ, Fintype.card_fin] using this
  rw [hsplit, hSsum]
  have hcomplZ : ((Sᶜ).card : ℤ) = (m : ℤ) - (s : ℤ) := by
    rw [hcompl]; omega
  rw [hcomplZ] at hCsum
  linarith

/-- **The main generic lower bound.**  A word of length `m` with `s` certified forced
splits (distinct endpoints, `SameCycle` at the prefix, distinct indices) raises
`numCycles` by at least `−m + 2s`:
`numCycles (prefixPerm p W m) ≥ numCycles p − m + 2s`. -/
theorem numCycles_lower_of_forced_splits (p : Equiv.Perm X) {m s : ℕ}
    (W : Fin m → Swap X) (splitIdx : Fin s → Fin m)
    (hsinj : Function.Injective splitIdx)
    (hne : ∀ i : Fin s, (W (splitIdx i)).x ≠ (W (splitIdx i)).y)
    (hforced : ∀ i : Fin s,
      (prefixPerm p W (splitIdx i).val).SameCycle
        (W (splitIdx i)).x (W (splitIdx i)).y) :
    (numCycles (prefixPerm p W m) : ℤ)
      ≥ (numCycles p : ℤ) - (m : ℤ) + 2 * (s : ℤ) := by
  have htel := numCycles_prefix_telescopes p W
  have hsum := sum_stepDelta_lower_of_forced_splits p W splitIdx hsinj hne hforced
  linarith

/-- `numCycles` is positive on a nonempty type (every dart lies in a cycle class). -/
lemma numCycles_pos [Nonempty X] (p : Equiv.Perm X) : 0 < numCycles p := by
  classical
  rw [PermTranspositionCycleCount.numCycles_eq_card_sub_support_add_cycleType_card]
  have hcard : 0 < Fintype.card X := Fintype.card_pos
  have hle : p.support.card ≤ Fintype.card X := p.support.card_le_univ
  rcases Nat.eq_zero_or_pos (Multiset.card p.cycleType) with hz | hpos
  · -- no nontrivial cycles ⇒ support empty, count = card X − 0 + 0 > 0
    have hct0 : p.cycleType = 0 := Multiset.card_eq_zero.mp hz
    have hsum := Equiv.Perm.sum_cycleType p
    rw [hct0, Multiset.sum_zero] at hsum
    rw [hz]; omega
  · -- at least one nontrivial cycle; the `+ #cycles` term keeps the count positive
    omega

/-! ## Non-vacuity of the generic forced-splits hypotheses

A concrete witness that the hypotheses of `numCycles_lower_of_forced_splits` are
jointly satisfiable with `s > 0`, producing a *non-degenerate* bound: the `3`-cycle
`p = c(0 1 2)` on `Fin 3` with the one-letter word `W 0 = swap 0 1` (a split, since `0`
and `1` lie in the same `p`-cycle, as `p 0 = 1`).  The lemma yields
`numCycles (p · swap 0 1) ≥ numCycles p − 1 + 2 = numCycles p + 1 ≥ 2`.  This rules out
the "vacuous conditional" failure mode for the generic reduction. -/
example :
    (numCycles
      (prefixPerm (X := Fin 3)
        (Equiv.swap 0 1 * Equiv.swap 1 2)        -- the 3-cycle (0 1 2)
        (fun _ : Fin 1 => ⟨0, 1⟩)
        1) : ℤ) ≥ 2 := by
  have hne : ∀ i : Fin 1, ((fun _ : Fin 1 => (⟨0, 1⟩ : Swap (Fin 3))) i).x
      ≠ ((fun _ : Fin 1 => (⟨0, 1⟩ : Swap (Fin 3))) i).y := by decide
  have hforced : ∀ i : Fin 1,
      (prefixPerm (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2)
        (fun _ : Fin 1 => (⟨0, 1⟩ : Swap (Fin 3))) ((fun _ : Fin 1 => (0 : Fin 1)) i).val).SameCycle
        ((fun _ : Fin 1 => (⟨0, 1⟩ : Swap (Fin 3))) ((fun _ : Fin 1 => (0 : Fin 1)) i)).x
        ((fun _ : Fin 1 => (⟨0, 1⟩ : Swap (Fin 3))) ((fun _ : Fin 1 => (0 : Fin 1)) i)).y := by
    intro i
    -- `prefixPerm p W 0 = p`; `0` and `1` are in the same `p`-cycle since `p 0 = 1`.
    show (prefixPerm (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2)
      (fun _ : Fin 1 => (⟨0, 1⟩ : Swap (Fin 3))) 0).SameCycle 0 1
    rw [prefixPerm_zero]
    exact ⟨1, by decide⟩
  have h := numCycles_lower_of_forced_splits
    (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2)
    (m := 1) (s := 1) (fun _ : Fin 1 => ⟨0, 1⟩)
    (splitIdx := fun _ : Fin 1 => 0)
    (hsinj := Function.injective_of_subsingleton _) hne hforced
  -- `numCycles p ≥ 1`: it counts fixed points plus cycle factors, and the fixed-point
  -- count alone is `≥ 0`, while the support is nonempty here.  Easiest: `numCycles` of a
  -- permutation on a nonempty type is positive.
  have hp1 : 1 ≤ numCycles (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) :=
    numCycles_pos _
  push_cast at h ⊢
  linarith

end ForcedSplits

/-! ## Layer 6: the cut-and-cap forced-split certificate

We now instantiate the generic reduction at the corrected cut-and-cap data.  A
`FaceCorrLowerCert C` packages the design data: a fixed transposition word `W` of some
length `m`, whose prefix product against `phiLift` is `phiLift · faceCorr₂` (`= φ'₂`),
together with `s` distinguished split indices whose endpoints are distinct and
`SameCycle` at the corresponding prefix, subject to the single arithmetic constraint
`m + 2 ≤ 2·s + 2·len` (so that the telescope `(F + 2·len) − m + 2·s ≥ F + 2`).

### Why `m` and `s` are not the design's fixed `4·len − 2` and `len`

The design's premise that `faceCorr₂` is *uniformly* a `(4·len − 2)`-letter word with
`len` splits is a **genus-0-with-full-support artifact**.  Kernel reconnaissance
(reproduced in `PlanarMapSeamInst.lean` and verified here) shows the minimal
transposition length of `faceCorr₂` is `|supp faceCorr₂| − (#nontrivial cycles)`, which
is genuinely cut-dependent: on the triangle cut it is `4` (two pure `len`-cycles), on
the `K₄`-sphere/torus `A→B→D` cuts it is `10 = 4·len − 2` (full active support), on the
`K₄`-sphere `0→1→3` cut it is `12`.  The forced-split count then is
`s = m/2 − len + 1`, which is `1`, `len`, `len + 1` respectively — also cut-dependent.

The generic lower bound `numCycles_lower_of_forced_splits` is **length-agnostic**, so
the certificate carries `m`, `s`, and only the inequality `m + 2 ≤ 2·s + 2·len` it must
satisfy.  This is the genuinely genus-free formulation: it never refers to the cycle
structure of `faceCorr₂`, only to `s` local `SameCycle` facts at `s` prefixes — exactly
what survives the K₄-sphere / K₄-torus genus variation that defeats the two-cap-chain
`SeamDecomposition` of `PlanarMapSeamInst.lean`. -/

namespace ProofsInTheBook.PlanarMap

open ForcedSplits CombMap CombMap.SimplePrimalCycle

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

/-- The forced-split lower-bound certificate for `faceCorr₂`: a transposition word `W`
of length `m`, realising `φ'₂ = phiLift · faceCorr₂` as its prefix product, with `s`
certified split steps and the arithmetic constraint `m + 2 ≤ 2·s + 2·len`. -/
structure FaceCorrLowerCert (C : SimplePrimalCycle M) where
  /-- The word length. -/
  m : ℕ
  /-- The number of certified split steps. -/
  s : ℕ
  /-- The arithmetic constraint making the telescope close to `F + 2`:
  `(F + 2·len) − m + 2·s ≥ F + 2`. -/
  hbound : m + 2 ≤ 2 * s + 2 * C.len
  /-- The fixed transposition word. -/
  W : Fin m → ForcedSplits.Swap C.CutDart
  /-- The prefix product realises `φ'₂ = phiLift · faceCorr₂`. -/
  prefix_eq : ForcedSplits.prefixPerm C.phiLift W m = C.phiLift * C.faceCorr2
  /-- The `s` distinguished split indices. -/
  splitIdx : Fin s → Fin m
  splitIdx_injective : Function.Injective splitIdx
  /-- Each split transposition has distinct endpoints. -/
  split_ne : ∀ i : Fin s,
    (W (splitIdx i)).x ≠ (W (splitIdx i)).y
  /-- Each split step's endpoints are `SameCycle` under the prefix product
  (the local forced-split certificate). -/
  forced_split : ∀ i : Fin s,
    (ForcedSplits.prefixPerm C.phiLift W (splitIdx i).val).SameCycle
      (W (splitIdx i)).x (W (splitIdx i)).y

/-! ## Layer 7: the lower bound `numCycles φ'₂ ≥ F + 2` -/

/-- **The corrected face-cycle lower bound from a certificate.**  Telescoping the `s`
forced splits against `numCycles phiLift = F + 2·len` gives, via the constraint
`m + 2 ≤ 2·s + 2·len`, `numCycles φ'₂ ≥ (F + 2·len) − m + 2·s ≥ F + 2`. -/
theorem numCycles_cutCapPhi2_lower (C : SimplePrimalCycle M)
    (cert : C.FaceCorrLowerCert) :
    (_root_.numCycles ((C.cutCapMap2).φ) : ℤ) ≥ (M.F : ℤ) + 2 := by
  -- The generic lower bound on the prefix product.
  have hgen := ForcedSplits.numCycles_lower_of_forced_splits
    C.phiLift cert.W cert.splitIdx cert.splitIdx_injective cert.split_ne cert.forced_split
  -- Identify the full prefix with `φ'₂`.
  rw [cert.prefix_eq, ← cutCapPhi2_eq_phiLift_mul] at hgen
  -- `numCycles phiLift = F + 2·len`.
  have hphi : (_root_.numCycles C.phiLift : ℤ) = (M.F : ℤ) + 2 * (C.len : ℤ) := by
    rw [C.numCycles_phiLift]; push_cast; ring
  rw [hphi] at hgen
  -- The arithmetic constraint, cast to ℤ.
  have hboundZ : (cert.m : ℤ) + 2 ≤ 2 * (cert.s : ℤ) + 2 * (C.len : ℤ) := by
    have := cert.hbound; omega
  -- (F + 2·len) − m + 2·s ≥ F + 2.
  linarith

/-- **The face count of the corrected cut-and-cap map is at least `F + 2`**
(genus-free), from a forced-split certificate.  `(cutCapMap2).F ≥ M.F + 2`. -/
theorem cutCapMap2_F_lower (C : SimplePrimalCycle M) (cert : C.FaceCorrLowerCert) :
    (C.cutCapMap2).F ≥ M.F + 2 := by
  have h := numCycles_cutCapPhi2_lower C cert
  rw [CombMap.F_eq_numCycles]
  -- `(F : ℤ) ≥ F + 2` ⇒ `F ≥ F + 2` in ℕ.
  have : (M.F : ℤ) + 2 ≤ (_root_.numCycles ((C.cutCapMap2).φ) : ℤ) := h
  omega

/-! ## Layer 12: the contradiction engine (lower-bound Jordan theorem)

The exact equality `F' = F + 2` is **not** needed for the Jordan contradiction; the
lower bound `F' ≥ F + 2` suffices.  With the unconditional `V' = V + k`, `E' = E + k`,
a connected cut map has `χ' = V' − E' + F' ≥ (V − E + F) + 2 = χ + 2 = 4`, but
`chi_le_two_of_connected` forces `χ' ≤ 2`.  Contradiction. -/

/-- **From a connected cut map, `F' ≤ F`.**  Pure Euler arithmetic: `V' = V + k`,
`E' = E + k`, and the connected Euler inequality `χ' ≤ 2` with `χ = 2`. -/
theorem cutCapMap2_F_le_of_connected (C : SimplePrimalCycle M)
    (hchi : M.eulerChar = 2)
    (hconn : (C.cutCapMap2).Connected) :
    (C.cutCapMap2).F ≤ M.F := by
  have hle : (C.cutCapMap2).eulerChar ≤ 2 :=
    CombMap.chi_le_two_of_connected _ hconn
  have hV : (C.cutCapMap2).V = M.V + C.len := C.cutCapMap2_V
  have hE : (C.cutCapMap2).E = M.E + C.len := cutCapMap2_edge_count C
  -- expand χ' = V' − E' + F' and χ = V − E + F = 2.
  unfold CombMap.eulerChar at hle hchi
  rw [hV, hE] at hle
  push_cast at hle hchi
  omega

/-- **The lower-bound Jordan / chord-separation theorem.**  Given a forced-split
certificate, the Euler hypothesis `M.eulerChar = 2`, and the per-edge connectivity
parameter, no cut edge of a simple primal cycle on a sphere is straddled by a
cycle-avoiding dual path.  This consumes only the genus-free **lower bound**
`F' ≥ F + 2` (via `cert`), not the exact face count. -/
theorem jordan_simple_cycle2_lower (C : SimplePrimalCycle M)
    (cert : C.FaceCorrLowerCert)
    (hchi : M.eulerChar = 2)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) := by
  intro hpath
  have hconnected : (C.cutCapMap2).Connected := hconn i hpath
  have hle : (C.cutCapMap2).F ≤ M.F :=
    C.cutCapMap2_F_le_of_connected hchi hconnected
  have hge : (C.cutCapMap2).F ≥ M.F + 2 := C.cutCapMap2_F_lower cert
  omega

end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap
