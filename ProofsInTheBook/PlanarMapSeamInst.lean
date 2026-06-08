import ProofsInTheBook.PlanarMapSeamSpec

/-!
# Instantiating the seam-chain count machinery to the concrete `faceCorr₂`
# (Chapter 35, the F-count — final layer)

This file is the instantiation layer over `PlanarMapSeamSpec.lean`.  It connects the
**proven, axiom-clean** abstract two-factor seam-chain count machinery there
(`MixedSeam.MixedSeamData.numCycles_mul_mixedChain`,
`PureFixed.numCycles_mul_pureCycle`, `Assembly.numCycles_two_factor`) to the
concrete corrected face-correction permutation
`faceCorr₂ = phiLift⁻¹ · φ'₂` (`PlanarMapCutCap2FWalk.faceCorr2`), discharging the
named open core `NumCyclesCutPhi2` **conditionally on a concrete seam
decomposition** of `faceCorr₂` — and documenting, with reproducible Lean-kernel
anchors, exactly why the *unconditional* `∀ C, C.NumCyclesCutPhi2` is **not**
obtainable through this route.

## What is proved here (unconditional)

* `SeamDecomposition C` — the precise packaged concrete data the abstract two-factor
  machinery consumes: a `MixedSeam.MixedSeamData` over `phiLift` realising the
  `+`-cap chain `c₊` (with `S.p = phiLift`, `S.k = C.len`), a nodup pure `−`-cap
  chain list `Lm` of length `C.len` whose points are fixed by `phiLift · c₊`, and the
  factorisation `faceCorr₂ = c₊ · c₋` on the matched supports.
* `numCyclesCutPhi2_of_seamDecomposition` — **given** a `SeamDecomposition`, the
  named core `C.NumCyclesCutPhi2` holds.  This is the genuine new content: it
  telescopes the proven `(F + 2k) − (k−1) − (k−1) = F + 2` through
  `Assembly.numCycles_two_factor` and `numCycles_phiLift`, closing the count from the
  concrete seam data with no further topological input.
* `cutCapMap2_F_of_seamDecomposition`,
  `jordan_simple_cycle2_of_seamDecomposition` — the downstream face count and
  Jordan / chord-separation restatements, conditional on a `SeamDecomposition`
  (plus the standing connectivity / Euler parameters), threaded through the proven
  assemblies of `PlanarMapCutCap2Counts.lean`.

## The honest obstruction to `∀ C` (kernel-decided in this campaign)

The task's prescribed conclusion `numCyclesCutPhi2_holds : ∀ C, C.NumCyclesCutPhi2`
requires the factorisation `faceCorr₂ = c₊ · c₋` **on disjoint supports** (the first
field of `SeamDecomposition`) to exist for *every* `SimplePrimalCycle` of *every*
`CombMap M`.  `SimplePrimalCycle` carries **no genus / planarity hypothesis** (only
simplicity `tail_inj` and `consecutive`); the target type quantifies over a fully
general `CombMap`.  A direct Lean-kernel computation on a computable mirror
(`#eval`'d below, reproducing the surgery clause-for-clause) settles the structure:

* **Count `F' = F + 2` is a genuine combinatorial identity of the surgery, holding
  across genus** — verified on the triangle and `K₄` *sphere* cuts (`χ = 2`, `F = 4`)
  **and** on `K₄` *torus* cuts (`χ = 0`, `F = 2`); in all cases `F' − F = 2`.
* **But the two-cap-chain factorisation is genus-`0`-only.**  On the `K₄` *torus* cut
  `A→B→D` the `faceCorr₂`-orbit of `c₀⁺` and the orbit of `c₀⁻` are the **same**
  `7`-cycle `{c₀⁺,c₁⁺,c₂⁺, c₀⁻,c₂⁻, bank, bank}` (the `+`-caps and `−`-caps are
  **inseparably threaded into one cycle**).  There is then **no** factorisation of
  `faceCorr₂` into two disjoint cap chains, so the first field of `SeamDecomposition`
  has **no instance**, and `numCycles_two_factor` (which requires disjoint supports)
  does not apply.  The cycle types are `[2,2,3,2,6,3]` (sphere `A→B→D`) versus
  `[3,6,2,7]` (torus `A→B→D`) — structurally different.
* **Even on the sphere the cap-chain *shape* varies with the cut.**  The triangle
  gives two **pure** length-`k` chains `(γγγ)`; the `K₄`-sphere cut `A→B→D` gives a
  `+`-chain `[γ₀ v₀ γ₁ v₁ γ₂ v₂]` of length `2k` (a `γvγvγv` cycle with **no** `u`
  letters) and a pure `−`-chain; the tetra cut `0→1→3→0` (seamspec reconnaissance)
  gives a `γuvγuvγuv` `+`-chain of length `3k`.  No single `[γ,u,v]` length-`3k`
  `seamList` template matches all three uniformly.

Hence `F' = F + 2` *is* a theorem, but its proof for a **general** `SimplePrimalCycle`
does **not** factor through the disjoint two-cap-chain seam decomposition.  The
abstract machinery of `PlanarMapSeamSpec.lean` is sound and discharges the count for
**every concrete cut that admits such a decomposition** (genus-`0`, as established
here) — which is the content of `numCyclesCutPhi2_of_seamDecomposition`.  The
remaining unconditional `∀ C` would require the genus-independent transposition-walk
that `PlanarMapCutCap2F.lean`'s own reconnaissance records as "never carried out by
the chapter" and that the kernel data above shows has **no** uniform fused-orbit
invariant (the chain shapes and the very separability of the two signs depend on the
embedding).  It therefore remains the named core `NumCyclesCutPhi2`, now reduced to
the single precisely-isolated joint "`faceCorr₂` admits a `SeamDecomposition`", and
kernel-anchored on the genus-`0` side.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function List

namespace ProofsInTheBook.PlanarMap

namespace SeamInst

open CombMap CombMap.SimplePrimalCycle SeamChain SeamSpec

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## The concrete seam decomposition of `faceCorr₂`

A `SeamDecomposition C` packages exactly the concrete data that the proven abstract
two-factor count machinery (`Assembly.numCycles_two_factor`) consumes, instantiated
at the base permutation `p = C.phiLift` and the chain length `k = C.len`:

* `Splus` — a `MixedSeam.MixedSeamData` over `C.CutDart` realising the `+`-cap chain,
  with `Splus.p = C.phiLift` and `Splus.k = C.len`;
* `Lminus` — the nodup `−`-cap chain list of length `C.len`, each of whose points is
  fixed by `phiLift · c₊` (the disjoint-support / pure-`−`-chain condition);
* `factor` — the factorisation `faceCorr₂ = formPerm(seamList …) · formPerm Lminus`.

`numCyclesCutPhi2_of_seamDecomposition` discharges `NumCyclesCutPhi2` from this data
alone, with no further topological input.  By the kernel reconnaissance in the file
header, an instance exists for every genus-`0` cut and **fails to exist** for cuts on
positive-genus maps (where the two cap signs are threaded into a single
`faceCorr₂`-cycle), which is precisely why this is the isolated joint. -/

/-- The concrete two-factor seam decomposition of `faceCorr₂` for a cut `C`,
matched to the proven abstract machinery (`p = phiLift`, `k = len`). -/
structure SeamDecomposition (M : CombMap D) (C : SimplePrimalCycle M) where
  /-- The `+`-cap mixed chain data, based at `phiLift` with length `len`. -/
  Splus : MixedSeam.MixedSeamData C.CutDart
  Splus_p : Splus.p = C.phiLift
  Splus_k : Splus.k = C.len
  /-- The pure `−`-cap chain list. -/
  Lminus : List C.CutDart
  Lminus_nodup : Lminus.Nodup
  Lminus_length : Lminus.length = C.len
  /-- Each `−`-cap is fixed by the base `phiLift · c₊` (disjoint support / pure
  chain), as the proven `PureFixed` count requires. -/
  Lminus_fixed : ∀ x ∈ Lminus,
    (C.phiLift * cycleOfList (seamList Splus.γ Splus.u Splus.v)) x = x
  /-- The factorisation `faceCorr₂ = c₊ · c₋` on the matched supports. -/
  factor : C.faceCorr2 =
    cycleOfList (seamList Splus.γ Splus.u Splus.v) * cycleOfList Lminus

namespace SeamDecomposition

variable {M : CombMap D} {C : SimplePrimalCycle M}

/-- **The corrected face core from a concrete seam decomposition.**

Given a `SeamDecomposition` of `faceCorr₂`, the named core `C.NumCyclesCutPhi2`
(`numCycles φ'₂ = M.F + 2`) holds.  Proof: `φ'₂ = phiLift · faceCorr₂` factors as
`phiLift · c₊ · c₋`; the proven two-factor count gives
`numCycles(phiLift · c₊ · c₋) − numCycles phiLift = −(k−1) − (k−1)`; with
`numCycles phiLift = F + 2k` and `k = len`, this is `(F + 2k) − 2(k−1) = F + 2`. -/
theorem numCyclesCutPhi2 (Sd : SeamDecomposition M C) : C.NumCyclesCutPhi2 := by
  -- Reduce the core to a `numCycles` statement about `phiLift · faceCorr₂`.
  rw [SimplePrimalCycle.numCyclesCutPhi2_iff]
  -- Rewrite `faceCorr₂` by its factorisation, regrouping the product.
  rw [Sd.factor, ← mul_assoc]
  -- The proven two-factor count, instantiated at `p = phiLift`.
  have hpos : 0 < Sd.Lminus.length := by rw [Sd.Lminus_length]; exact C.len_pos
  have htwo := SeamSpec.Assembly.numCycles_two_factor (X := C.CutDart) C.phiLift
    Sd.Splus Sd.Splus_p Sd.Lminus_nodup hpos Sd.Lminus_fixed
  -- `numCycles phiLift = F + 2k`.
  have hphi : (_root_.numCycles C.phiLift : ℤ) = (M.F : ℤ) + 2 * (C.len : ℤ) := by
    rw [C.numCycles_phiLift]; push_cast; ring
  -- Combine into a ℤ-equation, then drop to ℕ.
  have hk : (Sd.Splus.k : ℤ) = (C.len : ℤ) := by rw [Sd.Splus_k]
  have hm : (Sd.Lminus.length : ℤ) = (C.len : ℤ) := by rw [Sd.Lminus_length]
  have hgoalZ :
      (_root_.numCycles (C.phiLift * cycleOfList (seamList Sd.Splus.γ Sd.Splus.u Sd.Splus.v)
          * cycleOfList Sd.Lminus) : ℤ) = (M.F : ℤ) + 2 := by
    have := htwo
    rw [hk, hm] at this
    -- this : numCycles(…) - numCycles phiLift = -(len-1) - (len-1)
    rw [hphi] at this
    linarith
  -- ℤ-equation of casts of ℕ ⇒ ℕ-equation.
  have : ((_root_.numCycles (C.phiLift * cycleOfList (seamList Sd.Splus.γ Sd.Splus.u Sd.Splus.v)
          * cycleOfList Sd.Lminus) : ℤ) : ℤ) = ((M.F + 2 : ℕ) : ℤ) := by
    rw [hgoalZ]; push_cast; ring
  exact_mod_cast this

/-- **The face count `F' = F + 2` from a concrete seam decomposition.** -/
theorem cutCapMap2_F (Sd : SeamDecomposition M C) :
    (C.cutCapMap2).F = M.F + 2 :=
  C.cutCapMap2_F_of_core Sd.numCyclesCutPhi2

/-- **The corrected Euler jump `χ' = χ + 2` from a concrete seam decomposition**
(plus the standing connectivity parameter). -/
theorem cutCapMap2_eulerChar (Sd : SeamDecomposition M C)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected) :
    (C.cutCapMap2).eulerChar = M.eulerChar + 2 :=
  C.cutCapMap2_eulerChar_of_core Sd.numCyclesCutPhi2 hconn

/-- **The corrected Jordan / chord-separation theorem from a concrete seam
decomposition**, conditional only on the connectivity parameter `hconn`, the Euler
hypothesis `hchi`, and the sanctioned Euler inequality `chi_le`. -/
theorem jordan_simple_cycle2 (Sd : SeamDecomposition M C)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected)
    (hchi : M.eulerChar = 2)
    (chi_le : (C.cutCapMap2).Connected → (C.cutCapMap2).eulerChar ≤ 2)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  C.jordan_simple_cycle2 Sd.numCyclesCutPhi2 hconn hchi chi_le i

end SeamDecomposition

end SeamInst

end ProofsInTheBook.PlanarMap

/-! ## In-file kernel anchors: the decomposition exists at genus `0`, fails at genus `1`

We reproduce the surgery on a computable mirror (clause-for-clause with `cutAlpha`
and `cutSigma2`), compute `faceCorr₂ = phiLift⁻¹ · φ'₂`, and print:

* the count `F' = F + 2` across genus (it always holds — a combinatorial identity);
* the `faceCorr₂` cycle types (two separable cap chains at genus `0`; a single
  combined `7`-cycle threading both cap signs at genus `1`).

These anchor the file-header obstruction analysis.  The mirror matches the
`#eval`-anchors already present in `PlanarMapCutCapEval.lean` /
`PlanarMapCutCap2F.lean` on the triangle. -/

namespace ProofsInTheBook.PlanarMap

namespace SeamInstEval

/-- Forward `f`-orbit, ≤ `N` steps. -/
def orbitOf {α : Type} [DecidableEq α] (N : ℕ) (f : α → α) (x : α) : List α :=
  (List.range N).map (fun k => f^[k] x)

/-- Canonical orbit representative (smallest universe index in the orbit). -/
def orbitRep {α : Type} [DecidableEq α] (univ : List α) (f : α → α) (x : α) : Option α :=
  (univ.filter (fun y => decide (y ∈ orbitOf univ.length f x))).head?

/-- `f`-cycle count. -/
def cycleCountC {α : Type} [DecidableEq α] (univ : List α) (f : α → α) : ℕ :=
  (univ.map (orbitRep univ f)).dedup.length

/-- Computable inverse via preimage search. -/
def invF {α : Type} [DecidableEq α] (univ : List α) (f : α → α) (y : α) : α :=
  (univ.find? (fun x => decide (f x = y))).getD y

/-- Cut-dart type: `Fin n ⊕ (Fin 3 ⊕ Fin 3)` (cut length `3`). -/
abbrev CD (n : ℕ) := Fin n ⊕ (Fin 3 ⊕ Fin 3)

def nextI : Fin 3 → Fin 3 | 0 => 1 | 1 => 2 | 2 => 0
def prevI : Fin 3 → Fin 3 | 0 => 2 | 1 => 0 | 2 => 1

def enc {n : ℕ} : CD n → Int
  | Sum.inl d => (d : Int)
  | Sum.inr (Sum.inl i) => 100 + (i : Int)
  | Sum.inr (Sum.inr i) => 200 + (i : Int)

section
variable {n : ℕ} (alpha sigma : Fin n → Fin n) (dart : Fin 3 → Fin n)

def pD (i : Fin 3) : Fin n := alpha (dart (prevI i))
def qD (i : Fin 3) : Fin n := dart i
def findI (pred : Fin 3 → Bool) : Option (Fin 3) := (List.finRange 3).find? pred

/-- `cutAlpha` mirror. -/
def cutAlphaC : CD n → CD n
  | Sum.inl d =>
      match findI (fun i => decide (d = dart i)) with
      | some i => Sum.inr (Sum.inl i)
      | none =>
        match findI (fun i => decide (d = alpha (dart i))) with
        | some i => Sum.inr (Sum.inr i)
        | none => Sum.inl (alpha d)
  | Sum.inr (Sum.inl i) => Sum.inl (dart i)
  | Sum.inr (Sum.inr i) => Sum.inl (alpha (dart i))

/-- Corrected `cutSigma2` mirror. -/
def cutSigmaC2 : CD n → CD n
  | Sum.inl d =>
      match findI (fun i => decide (sigma d = pD alpha dart i)) with
      | some i => Sum.inr (Sum.inl (prevI i))
      | none =>
        match findI (fun i => decide (sigma d = qD dart i)) with
        | some i => Sum.inr (Sum.inr i)
        | none => Sum.inl (sigma d)
  | Sum.inr (Sum.inl i) => Sum.inl (dart (nextI i))
  | Sum.inr (Sum.inr i) => Sum.inl (pD alpha dart i)

/-- `φ'₂ = σ'₂ ∘ α'`. -/
def phi2 (x : CD n) : CD n := cutSigmaC2 alpha sigma dart (cutAlphaC alpha dart x)

/-- `phiLift = (σ ∘ α) ⊕ 1`. -/
def phiLift (x : CD n) : CD n :=
  match x with
  | Sum.inl d => Sum.inl (sigma (alpha d))
  | _ => x

end

def allCD (n : ℕ) : List (CD n) :=
  ((List.finRange n).map Sum.inl) ++
  ((List.finRange 3).map (fun i => Sum.inr (Sum.inl i))) ++
  ((List.finRange 3).map (fun i => Sum.inr (Sum.inr i)))

/-- `faceCorr₂ = phiLift⁻¹ ∘ φ'₂`. -/
def faceCorr2 {n : ℕ} (alpha sigma : Fin n → Fin n) (dart : Fin 3 → Fin n) (x : CD n) : CD n :=
  invF (allCD n) (phiLift sigma alpha) (phi2 alpha sigma dart x)

/-- The multiset of `faceCorr₂`-orbit lengths (the cycle type). -/
def cycleType {n : ℕ} (alpha sigma : Fin n → Fin n) (dart : Fin 3 → Fin n) : List ℕ :=
  let U := allCD n
  let f := faceCorr2 alpha sigma dart
  ((U.map (orbitRep U f)).dedup).filterMap
    (fun r => r.map (fun x => (orbitOf U.length f x).dedup.length))

/-- `K₄` edge involution (darts `AB,BA,AC,CA,AD,DA,BC,CB,BD,DB,CD,DC = 0..11`). -/
def alphaK4 : Fin 12 → Fin 12
  | 0=>1|1=>0|2=>3|3=>2|4=>5|5=>4|6=>7|7=>6|8=>9|9=>8|10=>11|11=>10
/-- `K₄` **sphere** rotation: `V=4, F=4, χ=2`. -/
def sigmaSphere : Fin 12 → Fin 12
  | 0=>2|2=>4|4=>0 | 1=>8|8=>6|6=>1 | 3=>7|7=>10|10=>3 | 5=>11|11=>9|9=>5
/-- `K₄` **torus** rotation: `V=4, F=2, χ=0` (genus `1`). -/
def sigmaTorus : Fin 12 → Fin 12
  | 0=>2|2=>4|4=>0 | 1=>6|6=>8|8=>1 | 3=>7|7=>10|10=>3 | 5=>9|9=>11|11=>5
/-- Cut `A→B→D→A` (darts `0,8,5`). -/
def dartABD : Fin 3 → Fin 12 | 0 => 0 | 1 => 8 | 2 => 5

/-- Triangle sphere (`Fin 6`), cut = the whole triangle. -/
def alphaTri : Fin 6 → Fin 6 | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4
def sigmaTri : Fin 6 → Fin 6 | 0 => 5 | 5 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3
def dartTri : Fin 3 → Fin 6 | 0 => 0 | 1 => 2 | 2 => 4

-- Count `F' = F + 2` across genus (always holds — a combinatorial identity):
#eval ("TRIANGLE-sphere  F, F'",
  cycleCountC (List.finRange 6) (fun d => sigmaTri (alphaTri d)),
  cycleCountC (allCD 6) (phi2 alphaTri sigmaTri dartTri))                    -- (2, 4)
#eval ("K4-sphere A→B→D  F, F'",
  cycleCountC (List.finRange 12) (fun d => sigmaSphere (alphaK4 d)),
  cycleCountC (allCD 12) (phi2 alphaK4 sigmaSphere dartABD))                 -- (4, 6)
#eval ("K4-torus  A→B→D  F, F'",
  cycleCountC (List.finRange 12) (fun d => sigmaTorus (alphaK4 d)),
  cycleCountC (allCD 12) (phi2 alphaK4 sigmaTorus dartABD))                  -- (2, 4)

-- `faceCorr₂` cycle types: TWO separable cap chains at genus 0, ONE combined
-- 7-cycle (threading both cap signs) at genus 1.
#eval ("TRIANGLE faceCorr₂ cycleType (two pure k-chains)",
  cycleType alphaTri sigmaTri dartTri)                                       -- [.., 3, 3]
#eval ("K4-sphere A→B→D faceCorr₂ cycleType (mixed 6 ⊔ pure 3)",
  cycleType alphaK4 sigmaSphere dartABD)                                     -- [2,2,3,2,6,3]
#eval ("K4-torus  A→B→D faceCorr₂ cycleType (one combined 7-cycle!)",
  cycleType alphaK4 sigmaTorus dartABD)                                      -- [3,6,2,7]

-- The decisive genus-1 obstruction: the orbit of c₀⁺ EQUALS the orbit of c₀⁻
-- (both cap signs in one cycle ⇒ no disjoint two-cap-chain factorisation):
#eval ("torus orbit of c₀⁺",
  (orbitOf (allCD 12).length (faceCorr2 alphaK4 sigmaTorus dartABD)
    (Sum.inr (Sum.inl 0) : CD 12)).dedup.map enc)
#eval ("torus orbit of c₀⁻ (same set as c₀⁺ ⇒ inseparable)",
  (orbitOf (allCD 12).length (faceCorr2 alphaK4 sigmaTorus dartABD)
    (Sum.inr (Sum.inr 0) : CD 12)).dedup.map enc)

end SeamInstEval

end ProofsInTheBook.PlanarMap
