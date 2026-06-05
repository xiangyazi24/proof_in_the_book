# opus-cc2fwalk reply — corrected face count `F' = F + 2`, the transposition-walk layer

**File (sole owner):** `ProofsInTheBook/PlanarMapCutCap2FWalk.lean` (new leaf).
Imports only `PlanarMapCutCap2F` (which re-exports `PlanarMapCutCap2Counts`,
`PlanarMapCutCapF`, `PlanarMapCutCapEval`). No other file touched.

**Branch:** main. No commits. No codex / OpenAI tooling. Verified EXCLUSIVELY on
uisai1 via rsync + `lake env lean` (never on the Mac). Dep
`lake build ProofsInTheBook.PlanarMapCutCap2F` ran to completion first
(`Build completed successfully (8441 jobs)`).

## Status — HONEST

| Target | Status |
|--------|--------|
| `numCyclesCutPhi2_holds : C.NumCyclesCutPhi2` (`numCycles φ'₂ = F+2`) | **NOT proved.** After genuinely exhaustive structural reconnaissance (≈ 24 kernel experiments, see below), this is the single irreducible per-chain topological count. NOT faked as a `sorry`/trivial theorem. |
| `cutCapPhi2_eq_phiLift_mul` (`φ'₂ = phiLift · faceCorr₂`) | **PROVED unconditionally** (new). |
| `numCyclesCutPhi2_iff` (target ⟺ `numCycles(phiLift·faceCorr₂)=F+2`) | **PROVED unconditionally** (new). |
| `phiLift_capP`, `phiLift_capM`, `phiLift_fixed_of_cap` (caps = `phiLift`-fixed pts) | **PROVED unconditionally** (new). |
| `cutCapMap2_F_walk` (`F'=F+2`) | PROVED, conditional on the one named core. |
| `cutCapMap2_eulerChar_walk` (`χ'=χ+2`) | PROVED, conditional on core + connectivity. |
| `jordan_simple_cycle2_walk` | PROVED, conditional on core + conn + sanctioned Euler ineq. |
| In-file kernel anchors (`F'=4` triangle, `phiLift`-ref `=8`, the two cap chains) | `#eval`, EXIT 0. |

I did **not** commit a `sorry`-bearing `numCyclesCutPhi2_holds`; that would violate
the repo's 0-sorry standard and the playbook's "axiom = renamed sorry" rule.

## What the walk layer adds (all unconditional, clean-3)

1. **Free factorisation** `φ'₂ = phiLift · faceCorr₂`, `faceCorr₂ := phiLift⁻¹·φ'₂`,
   mirroring the buggy `cutCapPhi_eq_phiLift_mul`. With `numCycles phiLift = F+2k`
   (already proved upstream), the target is now exactly the `F`-analogue of the `V'`
   walk over a reference of *known* count.
2. **Caps = `phiLift`-fixed points** (`phiLift_capP/capM/fixed_of_cap`) — the fact the
   per-chain count `−(k−1)` (caps-in-chain minus one) is stated against.
3. **Reduction** `numCyclesCutPhi2_iff` packaging the target as
   `numCycles(phiLift·faceCorr₂)=F+2`.
4. Restated walk-layer assemblies (`cutCapMap2_F_walk`,
   `cutCapMap2_eulerChar_walk`, `jordan_simple_cycle2_walk`).
5. In-file kernel anchors for the corrected `φ'₂` directly.

## The decisive new reconnaissance (kernel-verified, the exact shape of the core)

Ran `faceCorr₂ = phiLift⁻¹·φ'₂` through the Lean-kernel mirror on: the triangle, two
distinct proper tetra cuts, polygon cuts `k=3..7`, and a **genus-1** `K₄` embedding.
Uniform verdict (pins the proof shape precisely, and sharpens the previous round):

* `faceCorr₂` is **exactly two** non-trivial cycles — the `+`-cap chain and the
  `−`-cap chain — and **each chain contains all `k` caps of one sign** (every cap is a
  `phiLift`-fixed point).
* Multiplying `phiLift` by one chain `c` changes `numCycles` by **exactly `−(m−1)`**,
  `m = #(phiLift-fixed pts in supp c) = k`. So each chain gives `−(k−1)`, total
  `−(2k−2)`, hence `numCycles φ'₂ = (F+2k) − (2k−2) = F+2`. **Verified for every cut
  above, including genus 1** — so `F'=F+2` is a purely combinatorial identity of the
  surgery, NOT a planarity fact (important faithfulness point: `NumCyclesCutPhi2` is
  stated for an arbitrary `CombMap`, with no planarity hypothesis, and that is
  correct).
* The per-chain count `−(k−1)` is **not** an unconditional permutation fact: a random
  single cycle through `m` fixed points changes `numCycles` by `−(m−1)` only ~40% of
  the time (kernel-checked, 3000 random instances). What forces it here is the
  genus-0-per-component *arrangement* of the chain's movable (`inl`) darts relative to
  the `phiLift`-face orbits.

**Why no shortcut closes it (ruled out with kernel evidence this round):**
(1) chain factorisation — per-step merge/split pattern is cut-dependent (triangle all
merges; tetra mixes 5 merges + 3 splits); (2) star factorisation — same mixed pattern;
(3) merge-then-split / merge-only order — none exists (movable runs are mutually
co-cyclic, so no ordering makes every step a merge); (4) conjugation to a pure-cap
residual (`capShift·φ'₂·capShift⁻¹`) — stays pure-cap only on the triangle/polygons,
NOT on the tetra (inl darts are intrinsic to the chains); (5) genus/commutator
invariant `cyc a + cyc b − cyc ab` — not constant. **Decisively: `φ'₂` admits no
projection semiconjugacy** (caps stall while movable runs advance), so the `V'`
projection-reduction does not port; the count needs an adaptive *fused-orbit*
invariant whose state depends on the cut's face-adjacency combinatorics.

## Verification (on uisai1)

- `lake env lean ProofsInTheBook/PlanarMapCutCap2FWalk.lean` → **EXIT 0**, zero
  errors/warnings. `#eval`s print `4` (=F+2), `8` (=F+2k phiLift ref), and the
  4-rep orbit partition (two faces + two cap chains).
- `#print axioms` on `cutCapPhi2_eq_phiLift_mul`, `numCyclesCutPhi2_iff`,
  `phiLift_capP`, `cutCapMap2_F_walk`, `jordan_simple_cycle2_walk` → all exactly
  `{propext, Classical.choice, Quot.sound}` (clean-3). No `sorryAx`, no
  `ofReduceBool`/`native_decide`.
- `grep -nE '\bsorry\b|\badmit\b|\bnative_decide\b|^\s*axiom '` → matches only in
  doc-comment prose (lines 57, 62); none in code.
- Leaf module (nothing imports it); no other file touched; no commit; on `main`.

## Remaining open (next round)

`numCyclesCutPhi2_holds : C.NumCyclesCutPhi2`. The reduction, reference count `F+2k`,
caps = fixed-points characterisation, and the exact two-chain structure are all in
place. What remains is the single per-chain lemma:

> for `faceCorr₂`'s `+`-cap (resp. `−`-cap) chain `c`,
> `numCycles(phiLift·c) = numCycles(phiLift) − (k−1)`,

i.e. the genus-0-per-component arrangement of the chain's movable darts. This is a
dedicated multi-hundred-line single-writer development (the `F`-analogue of the
963-line `V'` machinery, but strictly harder — no projection semiconjugacy, requires
an adaptive fused-orbit `SameCycle`-transport invariant indexed along each chain).
Kernel anchors in place: triangle `F'=4`, tetra `F'=6`, polygon `k`, genus-1 `K₄`.
