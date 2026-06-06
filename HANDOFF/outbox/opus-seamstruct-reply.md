# SeamStructure.lean — abstract seam/orbit characterization of `faceCorr₂` (Chapter 35 convergent layer)

## Status: COMPLETE (abstract layer). 0 sorry / 0 axiom / 0 admit / 0 native_decide. Axioms clean.

File: `ProofsInTheBook/SeamStructure.lean` (423 lines). Imports `ProofsInTheBook.TouchCert`.
Verified EXCLUSIVELY on uisai1 (`lake env lean`), EXIT 0, zero warnings/errors. NEVER ran
lake/lean locally on the Mac. Branch `main` throughout; no commits.

## The honest mathematical situation (read first)

The task asked to prove `BankComponentCert.same_component` symbolically from the proven
per-class closed forms — the layer `TouchCert.lean` left as "kernel-`#eval`-anchored only".
The decisive structural fact I confirmed and respected:

- The orbit-induction discharge of `same_component` (per-step ⟹ per-orbit) **is fully
  abstract and unconditional** — proven here, reusable, no kernel reference.
- The symbolic **cap** action of `faceCorr₂` **is fully abstract** — derived here from the
  proven `cutCapPhi2_capP_action` / `cutCapPhi2_capM_action` by post-composing `phiLift⁻¹`.
- What is **NOT** abstractly available is the per-step containment on the **bank-end / cycle
  darts**: `faceCorr₂(inl(dart i)) = inl(φ⁻¹(dart(nextIdx i)))`, whose value depends on
  `φ(dart i) = σ(α(dart i))` — and `SimplePrimalCycle` does **not** constrain the forward
  darts' `σ`-arrangement (it is the genus-0 seam incidence `phiLift vᵢ = u_{i+1}` of
  `PlanarMapSeamSpec.lean`, embedding-dependent). So a fully unconditional `same_component`
  for an abstract `C` is impossible for the same structural reason recorded across
  `FaceCorrWord.lean` / `PlanarMapSeamSpec.lean` / `TouchCert.lean`.

I did **not** fake an instance. Instead I **shrank the residue** from the orbit-wide
`same_component` to the strictly local per-step `step_component`, and proved the bridge
between them unconditionally. This is genuine new math, not a re-wrapper.

## What was built (all verified)

### 1. The abstract orbit-induction engine (unconditional, position-free, reusable)
- `SeamStructure.eqvGen_of_iterate_step` / `eqvGen_of_sameCycle_step`: for **any** `p, q`
  and **any** relation `r` on `POrb p`, if one `q`-step keeps the `p`-orbit within one
  `EqvGen r`-component (`∀ x, EqvGen r (pOrbOf p x) (pOrbOf p (q x))`), then any two
  `q.SameCycle` points have `EqvGen r`-reachable `p`-orbits. Proof: `SameCycle.exists_pow_eq'`
  → ℕ-power → induction threading `EqvGen.trans`. **No symmetry of `r` needed.** This is the
  "if every `faceCorr₂` step stays in one bank component, then `same_component`" engine.

### 2. The symbolic per-class `faceCorr₂` cap action (abstract, from the closed forms)
- `faceCorr2_apply`, `phiLift_symm_{inl,inr,capP,capM}`, `phi_inv_sigma` (`φ⁻¹(σ d) = α d`),
  `alpha_alpha`.
- `faceCorr2_capP_cases`: `faceCorr₂(capP i)` = `inl(α(dart i))` (the `−`-bank end) **or**
  `capP(prevIdx j)` (a `+`-cap) **or** `capM j` (a `−`-cap) — every cap steps to a bank-end
  or a cap. Derived from `cutCapPhi2_capP_action` + `phiLift⁻¹`.
- `faceCorr2_capM_cases`: the `−`-cap analogue, image `inl(dart i)` (forward bank end) or a
  cap. These are the abstract "collect the moving darts / trace each cap's step" facts the
  task asked for, now symbolic rather than `#eval`-anchored.

### 3. The strengthened cycle-decomposition existence (carries `SameCycle`)
- `sameCycle_mul_{left,right}_of_disjoint`: disjoint-`SameCycle` bridge (via
  `Disjoint.commute.mul_zpow` + `zpow_apply_eq_self_of_apply_eq_self`).
- `exists_cycleListProd_sameCycle`: every finite permutation is `cycleListProd Ls` for nodup
  length-`≥2` lists whose members are pairwise `SameCycle` (the `Ls_sameCycle` data the
  discharge consumes). Reproves via `cycle_induction_on` + `Equiv.Perm.toList` /
  `mem_toList_iff`.

### 4. `BankStepCert` — the minimal per-step residue + the discharge
- `BankStepCert C`: cycle lists (with len/nodup/SameCycle, all provable) + `factor` + the
  `2·len − 2` `gen` edges + the **single isolated field** `step_component` (one `faceCorr₂`
  step ⟹ one bank component, ∀ dart).
- `BankStepCert.toBankComponentCert`: **discharges `same_component`** by running
  `eqvGen_of_sameCycle_step` against `step_component` and `Ls_sameCycle`. This is THE
  BankComponentCert discharge the task targeted (now resting on the strictly-local
  `step_component`, not the orbit-wide `same_component`).
- `cutCapMap2_F_lower_of_stepCert : (cutCapMap2).F ≥ M.F + 2` and
  `jordan_simple_cycle2_lower_of_stepCert : ¬ DualReachableAvoidingCycle …` — the chord
  wall's F-side, threaded through `TouchCert.lean`'s `…_of_bankCert` downstream. **Same
  conclusions as the established `_of_bankCert` / `_of_splitCert` routes.**

## Faithfulness / non-vacuity audit (playbook §3.3)

- **Same conclusion as the established routes.** `cutCapMap2_F_lower_of_stepCert` proves the
  identical `(cutCapMap2).F ≥ M.F + 2` and literally calls `cutCapMap2_F_lower_of_bankCert`.
  Verdict **CONDITIONAL-honest**, residue isolated to `BankStepCert.step_component`, strictly
  smaller (per-step) than the prior `same_component` (per-orbit).
- **NOT a re-wrapper.** The orbit-induction engine (`eqvGen_of_sameCycle_step`) and the
  symbolic cap action are genuine new unconditional theorems; the residue is provably
  reduced (per-step replaces per-orbit), bridged by ~40 lines of real proof.
- **NOT vacuous.** `factor : cycleListProd Ls = faceCorr2` pins `Ls` to the real permutation;
  `step_component` is `∀ x : CutDart` (not escapable via empty `Ls`). The engine is exercised
  on a concrete multi-step orbit: two `example`s fire `exists_cycleListProd_sameCycle` on
  `(0 1 2)` of `Fin 3` and run `eqvGen_of_sameCycle_step` to connect `0`,`2` of the `3`-cycle.
- **Bound NOT inflated.** `gen : Fin (2·len − 2)` is passed verbatim to `BankComponentCert`;
  no contract-field inflation.
- **Cap action faithful** (cross-checked vs kernel truth in `PlanarMapSeamSpec.lean`): triangle
  ⟹ branch 2 (cap→cap, pure chains); mixed tetra ⟹ branch 1 (`capP 0 ↦ inl(α(dart 0))`, a
  bank-end). Both branches are in the proven disjunction.

## Axiom audit (all 7 headline decls)
`eqvGen_of_sameCycle_step`, `exists_cycleListProd_sameCycle`, `faceCorr2_capP_cases`,
`faceCorr2_capM_cases`, `BankStepCert.toBankComponentCert`, `cutCapMap2_F_lower_of_stepCert`,
`jordan_simple_cycle2_lower_of_stepCert` → all `[propext, Classical.choice, Quot.sound]`.
No `sorryAx`, no `ofReduceBool`/`native_decide`.

## ONE truly resistant step (named, honest)
`BankStepCert.step_component` on the **bank-end / forward cycle darts**. Reason: the abstract
`faceCorr₂` action there is `inl(φ⁻¹(dart(nextIdx i)))`, governed by `φ(dart i) = σ(α(dart i))`,
which `SimplePrimalCycle` does not pin (the genus-0 seam incidence `phiLift vᵢ = u_{i+1}`).
This is the single genuinely cut-dependent joint — now the *only* thing `step_component`
carries beyond the symbolically-forced cap steps. It is isolated as the one cert field, not
faked. (The cap half of `step_component` is symbolically forced by `faceCorr2_capP_cases` /
`faceCorr2_capM_cases` once `gen` includes each cap's own edge.)

## What remains chapter-wide (Chapter 35)
The F-side chord wall is now CLOSED modulo the single per-step field `step_component`
(strictly smaller than before). Still open chapter-wide, unchanged by this work:
- the genus-0 instantiation of `step_component` (= the named open core `NumCyclesCutPhi2`'s
  seam content) — needs `phiLift vᵢ = u_{i+1}` as an abstract `SimplePrimalCycle` fact;
- bridge witness data (`PlanarMapBridgeWitness.lean`) + deletion orientation data;
- the connectivity parameter `hconn` and Euler `hchi`/`chi_le` (standing parameters);
- f13–16 (separate from this layer).

## Notes for wiring
- Leaf file (nothing imports it). To activate: add `import ProofsInTheBook.SeamStructure` to
  `ProofsInTheBook.lean` and the 7 `#print axioms` lines to `Audit.lean`. I own only
  SeamStructure.lean; did not touch the import graph or Audit.lean (one-file-one-writer).
- Build repo is uisai1 (full lakefile/toolchain/.lake). Dep oleans
  (`lake build ProofsInTheBook.TouchCert`, 8447 jobs) built clean first.

## Verification command
    rsync -az …/SeamStructure.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
    ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH \
                && lake env lean ProofsInTheBook/SeamStructure.lean'
    → EXIT 0, zero warnings/errors; 7 axiom prints all {propext, Classical.choice, Quot.sound}.
