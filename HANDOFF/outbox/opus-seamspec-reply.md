# Opus — PlanarMapSeamSpec.lean (Ch35 F-count specialisation) — reply

## Status

- **Kernel truth re-derived (verbatim, corrected).** ✅
- **Abstract count machinery for the TRUE structure: PROVEN, unconditional, axioms-clean.** ✅
- **Concrete `numCyclesCutPhi2_holds`: reduced to one sharply-isolated topological joint, NOT faked.**

`ProofsInTheBook/PlanarMapSeamSpec.lean` — 530 lines, `0` sorry / `0` axiom / `0`
admit / `0` native_decide. Verified with `lake env lean` (exit 0) and a full
`lake build ProofsInTheBook.PlanarMapSeamSpec` (8444 jobs, "Build completed
successfully"). All four headline theorems `#print axioms` clean
(`[propext, Classical.choice, Quot.sound]`).

## 1. Kernel truth (re-derived myself — corrected a model mismatch)

Computed `faceCorr₂ = phiLift⁻¹ · φ'₂` directly on the computable mirror
`cutSigmaC2 ∘ cutAlphaC` and on a hand-built tetra cut `0→1→3→0` (the mixed cut the
prior recon flagged). Encoding `inl d ↦ d`, `c_i^+ ↦ 100+i`, `c_i^- ↦ 200+i`:

* **Triangle (k=3):** `faceCorr₂ = (100 102 101)(200 201 202)`, six base darts fixed.
  **Both** cap chains are **pure** `k`-cycles of `phiLift`-fixed caps. `F' = 4 = F+2`.
* **Tetra cut `0→1→3→0` (k=3, mixed):** `faceCorr₂ = (100 1 3 102 4 10 101 9 7)(200 201 202)`.
  `−`-chain `(200 201 202)` **pure**; `+`-chain a **mixed** 9-cycle
  `γ u v γ u v γ u v` with `γ=100,102,101`, `u=1,4,9`, `v=3,10,7`.

**Decisive correction:** the kernel-true seam incidence is `phiLift vᵢ = u_{i+1}`
(inter-block, across a cap; verified `3↦4, 10↦9, 7↦1`), **not** the prior design's
`phiLift uᵢ = vᵢ` (intra-block). The two are not interconvertible by rotation/reversal,
so the previously-proven `SeamChainData` theorem (assuming `p uᵢ = vᵢ`) genuinely does
**not** apply to the `+`-chain. The per-step signed walk over the 9-cycle is
`−,−,−,+,−,−,+,+` (5 merges, 3 splits) = `−2 = −(k−1)` — kernel-verified.

## 2. What is proven (unconditional, axioms-clean)

* `PureFixed.numCycles_mul_pureCycle` — a cycle of `m` pure `p`-fixed points drops
  `numCycles` by exactly `m−1`. Handles the pure `−`-chain and the all-pure triangle.
* `MixedSeam.MixedSeamData.numCycles_mul_mixedChain` — the **NEW** abstract theorem for
  the kernel-true mixed normal form (`p γᵢ=γᵢ`, `p vᵢ=u_{i+1}`): drop is exactly
  `−(k−1)`, via the signed walk with the mixed `−,−,−,+,−,−,+,+` pattern and the
  block-sum telescoping `block_sum`/`stepSign_{A,B,C}`. This is the reusable content the
  prior agent's `SeamChainData` could not cover.
* `MixedSeam.mkFromCore` — reduced constructor that **derives** the two singleton merges
  (`merge_gamma0_u0`, `merge_v_gamma`) from `cap_fixed` + `Nodup` (the merge-target is a
  `p`-fixed cap off the prefix ⇒ a `P`-singleton), so the only non-mechanical inputs are
  `merge_u_v` + the two split links.
* `Assembly.numCycles_two_factor` — telescopes a mixed `+`-chain and a pure `−`-chain on
  disjoint supports to the total `(k−1)+(m−1)`. Resolves the task's order subtlety: the
  second factor is evaluated against the **correct** base `p·c₊`, against which the pure
  `−`-caps stay singleton fixed points — no transport gap. Gives `(F+2k)−(k−1)−(k−1)=F+2`.

## 3. The one isolated topological joint (honest, named)

Concluding `numCyclesCutPhi2_holds : ∀ C, C.NumCyclesCutPhi2` unconditionally still
needs the **concrete instantiation** for every cut: the factorisation
`faceCorr₂ = c₊ · c₋` on disjoint supports (absent from the repo), the `+`-chain's
`MixedSeamData` over `phiLift`, and in particular its `merge_u_v` (one gap-face
exclusion) and the **two split `SameCycle` links** `split_gamma_u` / `split_last_uv`.
These splits are the genuinely cut-dependent, genus-`0` advances for which `φ'₂` has
**no projection semiconjugacy** (kernel-confirmed: the active `P`-cycle absorbs whole
gap-face orbits of external darts). This is the `F`-analogue of the 963-line `V'`
machinery; it remains the named open core `NumCyclesCutPhi2`
(`PlanarMapCutCap2Counts.lean`). I did **not** paper it over with a vacuous conditional.

**Net advance over the prior blocked state:** the prior reply correctly diagnosed the
model mismatch but left the entire `−(k−1)` per-chain count open. Here the mismatch is
*resolved* (correct `p vᵢ=u_{i+1}` normal form), the full mixed signed-walk count is
*proven* and axiom-clean, the two-factor assembly is *proven*, and the remaining work is
compressed to exactly `merge_u_v` + two split `SameCycle` links per chain on the concrete
map. Downstream (`cutCapMap2_F_walk`, `jordan_simple_cycle2_walk` family) stays
conditional on `NumCyclesCutPhi2`, exactly as documented upstream.

## Files

- Owned/written: `ProofsInTheBook/PlanarMapSeamSpec.lean` (530 lines, clean).
- No other repo file touched. Scratch `#eval` files used for the kernel recon were
  removed (local + remote). Branch `main`, no commits.

## Verification commands run

```
rsync … PlanarMapSeamSpec.lean uisai1:…
ssh uisai1 'lake env lean ProofsInTheBook/PlanarMapSeamSpec.lean'        # exit 0, clean
ssh uisai1 'lake build ProofsInTheBook.PlanarMapSeamSpec'                # 8444 jobs OK
ssh uisai1 'lake env lean /tmp/axall.lean'   # all 4 headline theorems: [propext, Classical.choice, Quot.sound]
```
