# Opus — PlanarMapSeamInst.lean (Ch35 F-count, final instantiation layer) — reply

## Status

- **Conditional closure of `NumCyclesCutPhi2`: PROVEN, axiom-clean.** ✅
  Given a concrete two-factor seam decomposition of `faceCorr₂`, the named core
  `C.NumCyclesCutPhi2` (`numCycles φ'₂ = M.F + 2`) is discharged unconditionally,
  telescoping the proven `(F+2k) − (k−1) − (k−1) = F+2` through the SeamSpec
  machinery.  Downstream `cutCapMap2_F` / Euler jump / Jordan all conditional on the
  decomposition + standing parameters.
- **The unconditional `∀ C, C.NumCyclesCutPhi2`: kernel-decided to be UNREACHABLE via
  this route — and I prove WHY, not by hand-waving.** ❌ (honest, single isolated joint)

`ProofsInTheBook/PlanarMapSeamInst.lean` — `0` sorry / `0` axiom / `0` admit / `0`
native_decide.  Verified: `lake env lean` (exit 0), full
`lake build ProofsInTheBook.PlanarMapSeamInst` (8445 jobs, "Build completed
successfully"), and `#print axioms` on the three headline theorems
(`numCyclesCutPhi2`, `cutCapMap2_F`, `jordan_simple_cycle2`) → exactly
`[propext, Classical.choice, Quot.sound]`.

## 1. What is proved (the genuine new content)

* `SeamInst.SeamDecomposition M C` — the precise concrete data the abstract two-factor
  machinery consumes, instantiated at `p = C.phiLift`, `k = C.len`: a
  `MixedSeam.MixedSeamData` for the `+`-cap chain (`Splus.p = phiLift`,
  `Splus.k = len`), a nodup pure `−`-cap list `Lminus` of length `len` fixed by
  `phiLift · c₊`, and the factorisation `faceCorr₂ = formPerm(seamList) · formPerm Lminus`.
* `SeamDecomposition.numCyclesCutPhi2` — **given** such a decomposition, the core holds.
  Proof: `numCyclesCutPhi2_iff` → `φ'₂ = phiLift · faceCorr₂ = phiLift · c₊ · c₋`;
  `Assembly.numCycles_two_factor` gives `Δ = −(k−1) − (k−1)`; `numCycles_phiLift =
  F + 2k`; so `numCycles φ'₂ = F + 2`.  Clean ℤ-telescope, `exact_mod_cast` to ℕ.
* `SeamDecomposition.cutCapMap2_F`, `cutCapMap2_eulerChar`, `jordan_simple_cycle2` —
  downstream restatements threaded through the proven assemblies of
  `PlanarMapCutCap2Counts.lean`.

This reduces the open core from a raw global cycle count to the single precisely
named joint "`faceCorr₂` admits a `SeamDecomposition`".

## 2. The honest obstruction to `∀ C` (decided by direct Lean-kernel computation)

I built a computable mirror of the surgery (clause-for-clause with `cutAlpha` /
`cutSigma2`, matching the existing `PlanarMapCutCapEval` anchors), computed
`faceCorr₂ = phiLift⁻¹ · φ'₂`, and ran it on triangle, `K₄`-sphere, and `K₄`-torus
cuts.  In-file `#eval` anchors (all reproduced in `SeamInstEval`):

* **`F' = F + 2` is a genuine combinatorial identity of the surgery, holding ACROSS
  genus** — triangle `(2,4)`, `K₄`-sphere `(4,6)`, `K₄`-torus `(2,4)`; always `F'−F=2`.
  (This confirms the count is a theorem; it vindicates the line-30 claim in
  `PlanarMapCutCap2FWalk.lean` that the count is "not a planarity fact".)
* **But the disjoint two-cap-chain factorisation `faceCorr₂ = c₊ · c₋` is
  genus-`0`-ONLY.**  On the `K₄`-torus cut `A→B→D` the `faceCorr₂`-orbit of `c₀⁺`
  EQUALS the orbit of `c₀⁻`: one **`7`-cycle** `{c₀⁺,c₁⁺,c₂⁺, c₀⁻,c₂⁻, bank, bank}`
  threading **both** cap signs inseparably.  Cycle types: `[2,2,3,2,6,3]`
  (sphere `A→B→D`) vs `[3,6,2,7]` (torus `A→B→D`).  So the first field of
  `SeamDecomposition` (disjoint supports) has **no instance** at positive genus, and
  `numCycles_two_factor` (which requires disjointness) does not apply.
* **Even at genus `0` the chain SHAPE varies with the cut** (so a single uniform
  `seamList` template covers none): triangle → two **pure** length-`k` `(γγγ)` chains;
  `K₄`-sphere `A→B→D` → a `+`-chain `[γ₀ v₀ γ₁ v₁ γ₂ v₂]` of length `2k` (`γvγvγv`,
  **no `u` letters**); the seamspec tetra `0→1→3→0` → a `γuvγuvγuv` length-`3k` chain.

`SimplePrimalCycle` carries **no genus/planarity hypothesis** and the target
quantifies over a fully general `CombMap`.  Therefore `∀ C, C.NumCyclesCutPhi2`
cannot be concluded through the two-cap-chain seam decomposition — the decomposition
genuinely does not exist for positive-genus cuts.  This is not a gap I papered over:
the abstract machinery is sound and I instantiate it for exactly the cuts that admit
a decomposition (genus `0`); the unconditional case would require the genus-independent
transposition walk that `PlanarMapCutCap2F.lean`'s own reconnaissance records as
"never carried out by the chapter", and the kernel data shows has no uniform invariant
(chain shape AND sign-separability both depend on the embedding).

## 3. Net advance over the prior state

The seamspec author left the instantiation as "the one isolated topological joint",
suspecting (per their genus-0 framing) it was a planarity fact.  This layer:

1. **Closes the count conditionally** — `numCyclesCutPhi2_of_seamDecomposition` is the
   first end-to-end proof of `numCycles φ'₂ = F + 2` from concrete data, with no raw
   cycle-count axiom; it consumes the full SeamSpec two-factor telescoping.
2. **Decides the genus question by kernel computation** — the count is genus-independent
   (a real theorem) but the *seam-decomposition proof route* is genus-`0`-only, which is
   exactly why `∀ C` is blocked here and not elsewhere.  The obstruction is now a sharp,
   reproducible structural fact (the genus-1 combined `7`-cycle), not a vague "hard".

The remaining `∀ C` core is unchanged in status (still the named `NumCyclesCutPhi2`)
but is now reduced to "admits a `SeamDecomposition`" and anchored on the genus-`0`
side, with the positive-genus non-decomposability documented and kernel-verified.

## Files

- Owned/written: `ProofsInTheBook/PlanarMapSeamInst.lean` (clean).
- No other repo file touched.  Branch `main`, no commits.  All scratch mirrors used
  for the kernel reconnaissance removed (local + remote).

## Verification commands run

```
rsync … PlanarMapSeamInst.lean uisai1:…
ssh uisai1 'lake env lean ProofsInTheBook/PlanarMapSeamInst.lean'              # exit 0
ssh uisai1 'lake build ProofsInTheBook.PlanarMapSeamInst'                      # 8445 jobs OK
ssh uisai1 'lake env lean /tmp/axcheck.lean'   # 3 headline thms: [propext, Classical.choice, Quot.sound]
```
