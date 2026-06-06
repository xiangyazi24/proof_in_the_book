# ForcedSplits.lean — reply (Opus)

## Status: PARTIAL — generic engine + contradiction assembly CLOSED unconditionally;
## the forced-splits word certificate isolated as ONE named structure (honest).

New file: `ProofsInTheBook/ForcedSplits.lean` (463 lines). I own only this file; no
other file touched, no commit, branch `main` (remote is an rsync target, not a git
checkout — synced source + built deps via `lake exe cache get`).

Verified EXCLUSIVELY on uisai2 (uisai1 down):
`lake env lean ProofsInTheBook/ForcedSplits.lean` → **EXIT 0**, and
`lake build ProofsInTheBook.ForcedSplits` → **8443 jobs, success**.

## What is CLOSED unconditionally (genus-free, clean-3 axioms)

**Layer 1–2 — the generic transposition-walk API** (pure `Equiv.Perm` over any finite
`X`, derived from the existing dichotomy in `PermTranspositionCycleCount.lean`):
- `Swap`, `Swap.perm`, `prefixPerm` (recursive) + `prefixPerm_zero`/`prefixPerm_succ`
- `numCycles_mul_swap_split` (SameCycle + x≠y ⇒ +1), `numCycles_mul_swap_ge_sub_one`
- `stepDelta`, `stepDelta_ge_neg_one`, `stepDelta_eq_one_of_forced_split`
- `numCycles_prefix_telescopes` (full telescoping, induction on m)
- `sum_stepDelta_lower_of_forced_splits`, **`numCycles_lower_of_forced_splits`** (the
  main generic reduction: word of length m with s certified splits ⇒
  `numCycles(prefix m) ≥ numCycles p − m + 2s`)
- `numCycles_pos` (helper) + a concrete **non-vacuity `example`** (3-cycle on Fin 3,
  s=1, yields a real `≥2` bound) ruling out the vacuous-conditional failure mode.

**Layer 12 — the contradiction engine** (consumes only the LOWER bound, as the design
intended — the exact equality is no longer needed):
- `cutCapMap2_F_le_of_connected` : connected cut map + χ=2 ⇒ `F' ≤ F`
  (pure Euler arithmetic over the unconditional `V'=V+k`, `E'=E+k` +
  `chi_le_two_of_connected`)
- **`jordan_simple_cycle2_lower`** : the narrowest Jordan/chord-separation theorem;
  hypotheses are exactly `{cert, M.eulerChar=2, per-edge connectivity hconn}` — no
  `chi_le` parameter needed (it is discharged internally via the proven Euler
  inequality), and **no exact face-count core**.

All 8 headline lemmas: `#print axioms` = `[propext, Classical.choice, Quot.sound]`
only. **0 sorry / 0 axiom / 0 admit / 0 native_decide** in the file.

## The single isolated core: `FaceCorrLowerCert`

`cutCapMap2_F_lower : (cutCapMap2).F ≥ M.F + 2` and `jordan_simple_cycle2_lower` are
**conditional on a `FaceCorrLowerCert C`** — the genus-free, *local* word data
(a word `W : Fin m → Swap CutDart`, the prefix identity `prefixPerm phiLift W m =
phiLift·faceCorr₂`, `s` injective split indices with distinct endpoints + SameCycle at
the prefix, and the arithmetic constraint `m+2 ≤ 2s+2·len`).

This is **strictly weaker and more local** than the prior named core
`NumCyclesCutPhi2` (the exact count): it references no cycle structure of `faceCorr₂`,
no old-face labels, no genus — only `s` local SameCycle facts. It survives the
K₄-sphere/torus genus variation that defeats the two-cap-chain `SeamDecomposition`.

I did NOT discharge `FaceCorrLowerCert` for a general `SimplePrimalCycle`. Building it
requires discovering the uniform closed-form transposition word for `faceCorr₂` plus
the per-class SameCycle path proofs — the genuinely topological core the chapter has
circled. After genuine exhaustion (numeric reconnaissance across triangle / K₄-sphere
/ K₄-torus / tetra cuts), this is the one truly resistant certificate; named honestly,
not faked with sorry/axiom.

## IMPORTANT CORRECTION to the design (verified numerically + by parity)

The design's premise that `faceCorr₂` is a **uniform** `(4k−2)`-letter word with
**exactly `k`** splits is a **genus-0-with-full-support artifact and is FALSE in
general**. The minimal transposition length of `faceCorr₂` is
`|supp faceCorr₂| − (#nontrivial cycles)`, which is genuinely cut-dependent:
- triangle cut: **4** (two pure len-cycles), s = 1
- K₄-sphere & K₄-torus `A→B→D`: **10 = 4k−2** (full active support), s = k = 3
- K₄-sphere `0→1→3`: **12**, s = k+1 = 4

(Note sphere AND torus ABD both give 10 — the *machinery* is genus-free; the variation
is by cut geometry, not genus.) Hardcoding `m=4k−2, s=k` is unsound (impossible for the
triangle: you cannot place 3 splits in a 4-letter word). I therefore generalised the
certificate to carry `(m, s)` with the single inequality `m+2 ≤ 2s+2·len`, which is the
correct length-agnostic genus-free formulation; the generic lemma is already
length-agnostic so this is clean.

## Wiring note (for whoever integrates)

`jordan_simple_cycle2_lower` is a drop-in tightening of
`PlanarMapCutCap2F.jordan_simple_cycle2` once a `FaceCorrLowerCert` is produced: it
drops both the exact `NumCyclesCutPhi2` core AND the external `chi_le` parameter. To
wire into `Audit.lean`, add `import ProofsInTheBook.ForcedSplits` there.

## Verification commands (reproduce)

```
rsync -az .../ForcedSplits.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai2 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH && \
  lake env lean ProofsInTheBook/ForcedSplits.lean'        # EXIT 0
# #print axioms on all 8 headline lemmas → {propext, Classical.choice, Quot.sound}
```
