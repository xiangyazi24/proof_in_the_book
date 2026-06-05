# CutSigmaCounts F' = F + 2 — reply (opus-ccf)

**File:** `ProofsInTheBook/PlanarMapCutCapF.lean` (NEW, sole writer; no other file
touched). Imports `PlanarMapCutCapV`.
**Branch:** `main` (as instructed; not committed/pushed — left for you to commit).
**Status:** compiles clean on uisai1 (`lake env lean`, 0 errors; full
`lake build ProofsInTheBook.PlanarMapCutCapF` — 8436 jobs, success). 203 lines.
**0 sorry / 0 axiom / 0 admit / 0 native_decide.**  `#print axioms` on every result
= `{propext, Classical.choice, Quot.sound}`.

## Verdict (honest)

**F' = F + 2: NOT closed.**  The `face_count` field of `CutSigmaCounts` is *reduced*
to a single precise `numCycles` fact, with the reduction fully verified, but the
final cycle-count itself is **not** discharged.  I did not ship an unverified proof.

What landed is the verified **reduction infrastructure** that the count needs, plus
the discovery (verified against the source, not impression) that the cut-cap
author's warning is exactly right: the design prose "two cap cycles + old faces
survive" is *false* for the fixed `cutAlpha`.  The +2 is a genuine global
transposition-count fact, structurally unlike V' (it has no clean projection
semiconjugacy — see below).

## What is proved (verified, reusable)

1. **`alphaLift = α ⊕ 1`, `phiLift = φ ⊕ 1`** with closed forms; `alphaLift` an
   involution; **`phiLift = sigmaLift * alphaLift`** (lift is multiplicative).
2. **`numCycles phiLift = M.F + 2k`** (`numCycles_phiLift`) — the reference count.
3. **`numCycles_conj` / `numCycles_mul_comm`** (`namespace CutCapCount`) — cycle
   count is conjugation-invariant and `numCycles (AB) = numCycles (BA)`. General,
   reusable (proved via `Equiv.Perm.sameCycle_conj` + `Quotient.congr`).
4. **The free algebraic decomposition** `φ' = cutSigmaPerm * cutAlphaPerm =
   phiLift * faceCorr`, where `faceCorr := alphaLift * mergeProd * splitProd *
   cutAlphaPerm` (`cutCapPhi_eq_phiLift_mul`).  This is *pure associativity* on top
   of the V' theorem `cutSigmaPerm = sigmaLift * mergeProd * splitProd` and
   `alphaLift * alphaLift = 1` — no case analysis.
5. **The exact target reduction** (`cutCapMap_F_iff`):
   `(C.cutCapMap).F = M.F + 2  ↔  numCycles (phiLift * faceCorr) = M.F + 2`.
6. **A second regrouping** `φ' = merged * capCycleProd` (`cutCapPhi_eq_merged_mul`),
   with the full action of `capCycleProd = splitProd * cutAlphaPerm` characterized
   (the `k` disjoint 4-cycles `inl(dart i) ↦ c_i^- ↦ inl(α dart i) ↦ c_i^+ ↦
   inl(dart i)`, plus the old `α`-pairing on non-cycle darts).  `merged` is the V'
   object with `numCycles merged = V` already proven.

## The remaining core (precisely isolated)

Exactly one open fact:

```
numCycles (C.phiLift * C.faceCorr) = M.F + 2
```

equivalently `numCycles (C.merged * C.capCycleProd) = M.F + 2`.  In `phiLift` form
this is a `−2k + 2` perturbation: `numCycles phiLift = F + 2k`, and `faceCorr` is a
product of `6k` transpositions (it fixes every non-cycle `inl d` whose `σ`-successor
is not a bank-start), so the route is `numCycles_mul_listSwap_{splits,merges}`
(`PlanarMapCutCapCounts`) along a `6k`-swap list, with each step's `SameCycle`
condition discharged against the running `phiLift * prefix`.

### Why this is genuinely V'-scale and not a mutatis-mutandis of V'

I verified (against the actual `cutSigma`/`cutAlpha` closed forms, not the prose)
the two structural facts that block the easy routes:

* **No clean projection semiconjugacy exists for faces.**  `φ'` *fixes* each
  `inl(dart i)` (`φ'(inl dart i) = cutSigma(c_i^+) = inl(dart i)`), giving `k`
  singleton orbits, while `φ` moves `dart i`.  A V'-style `proj` with `proj(φ' x) ∈
  {φ(proj x), proj x}` therefore cannot exist (the fixed points break it), and
  `inl(α dart i) ↦ inl(p_i)` reroutes to a *different* vertex's dart.  This is the
  structural reason F jumps by `+2` (a global reconnection of the `k` vertex
  cycles) rather than `+k`.
* **The caps are not a clean cap-cycle.**  `φ'(c_i^+) = cutSigma(inl(dart i)) =
  inl(σ(dart i))` (generically), i.e. each cap injects into an *old face orbit*,
  not into `c_{i+1}^+`.  So the design's "two new cap cycles" picture is false for
  the fixed `cutAlpha`, exactly as the cut-cap author warned; `F'=F+2` is a count
  fact via transpositions, not via two visible cap orbits.

The honest consequence: the `6k`-step `SameCycle` discharge is a substantial
analysis (the V' file is 963 lines; this is comparable), tracking how the `b_i :=
inl(α dart i)` swaps connect consecutive vertex cycles `v_i, v_{i+1}` (this
threading is what collapses `k` cap insertions to a net `+2`).  I did **not**
complete it and did **not** fake it.

## eulerChar / assembly status (task item 3)

* **V' = V + k**: done (`PlanarMapCutCapV.cutCapMap_V`).
* **E' = E + k**: done (`PlanarMapCutCap.CutCapSurgery.edge_count`, a theorem).
* **χ' = χ + 2**: **already proven** abstractly (`CutCapSurgery.eulerChar_eq`), so
  once `face_count` lands, `CutSigmaCounts.toSurgery` + `eulerChar_eq` give the jump
  with no further work.
* **`CutSigmaCounts` minus connectivity**: `vertex_count` (done, V'),
  `face_count` (reduced here to the one `numCycles` fact above), and
  `connected_of_dual_path` remain.  So after F' closes, the *only* remaining
  `CutSigmaCounts` field is **connectivity** (`connected_of_dual_path`, design §4
  Part A/B) — an independent effort.

## Verification commands

```
rsync -az .../PlanarMapCutCapF.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 '... lake env lean ProofsInTheBook/PlanarMapCutCapF.lean'   # no output = OK
ssh uisai1 '... lake build ProofsInTheBook.PlanarMapCutCapF'           # 8436 jobs OK
# #print axioms on cutCapPhi_eq_phiLift_mul, numCycles_phiLift, cutCapMap_F_iff,
#   cutCapPhi_eq_merged_mul, numCycles_conj  ->  {propext, Classical.choice, Quot.sound}
```
