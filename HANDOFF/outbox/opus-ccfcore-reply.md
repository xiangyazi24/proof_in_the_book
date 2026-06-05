# F' = F + 2 pinned core — reply (opus-ccfcore)

**File:** `ProofsInTheBook/PlanarMapCutCapFCore.lean` (NEW, sole writer; no other
file touched). Imports `PlanarMapCutCapF`.
**Branch:** `main` (not committed/pushed — left for you).
**Build:** clean on uisai1 — `lake env lean` 0 errors; full
`lake build ProofsInTheBook.PlanarMapCutCapFCore` = 8437 jobs, success.
**0 axiom / 0 admit / 0 native_decide.**  Exactly **one** isolated `sorry` (the
pinned core), per the task's "isolate at most ONE truly resistant invariant step"
clause.

## Verdict (honest)

**F' = F + 2 is NOT fully closed.**  I did **not** ship a fake proof.  What landed:

1. **The complete per-class action of `φ' = cutCapMap.φ`** — proved
   unconditionally (`#print axioms` = `{propext, Classical.choice, Quot.sound}` on
   every action lemma).  This is the full orbit structure the count needs.
2. **The conclusion `cutCapMap_F : (C.cutCapMap).F = M.F + 2`**, wired through the
   already-verified reduction `cutCapMap_F_iff` from `PlanarMapCutCapF.lean`.
3. **One isolated open fact:** `numCycles_phiLift_faceCorr :
   numCycles (phiLift * faceCorr) = M.F + 2` (carries the single `sorry`;
   `cutCapMap_F` therefore inherits `sorryAx`, nothing else does).

## What is proved (verified, reusable)

* `cutCapPhi_apply` : `φ' x = cutSigma (cutAlpha x)`.
* `cutCapPhi_dart` : **`φ' (inl (dart i)) = inl (dart i)`** — each forward cycle
  dart is a `φ'`-**fixed point** (the `k` singleton orbits; the structural reason
  no projection semiconjugacy onto `φ` exists).
* `cutCapPhi_alpha_dart` : `φ' (inl (α (dart i))) = inl (p_i)`.
* `cutSigma_inl_cases` : the generic 3-way action of `σ'` on `inl e`
  (clean `inl (σ e)` / `+`-cap divert when `σ e = p_j` / `−`-cap divert when
  `σ e = q_j`).
* `cutCapPhi_capP_cases`, `cutCapPhi_capM_cases`, `cutCapPhi_inl_other_cases` :
  the full 3-way action of `φ'` on the `+`-cap, the `−`-cap, and a non-cycle
  `inl d`.  Together these pin down every `φ'`-orbit transition.

## The remaining core (precisely isolated) and why it is hard

`numCycles (phiLift * faceCorr) = F + 2`, with `numCycles phiLift = F + 2k`
(proved in `PlanarMapCutCapF.lean`).  The correction `faceCorr = phiLift⁻¹ φ'`
was computed class-by-class (generic, no diverts):

```
faceCorr (capM i)        = inl (dart i)
faceCorr (capP i)        = inl (α dart i)            -- = inl(φ⁻¹ σ dart i)
faceCorr (inl (dart i))  = inl (α σ⁻¹ dart i)        -- = inl(φ⁻¹ dart i)
faceCorr (inl (α dart i))= inl (α σ⁻¹ p_i)           -- = inl(φ⁻¹ p_i)
faceCorr (inl d)         = inl d                      -- non-cycle, non-bank: FIXED
```

so `faceCorr` is the identity off the cycle/cap darts **except** at the φ-bank-end
darts (those `e` with `σ e` a bank-start), which are exactly the darts that map
*into* the caps.  Consequently `faceCorr` is **not** a fixed product of pairwise
disjoint transpositions: its non-trivial orbits are the **face-boundary chains**
`(φ-bank-end → cap → inl(dart/α-dart) → … → next φ-bank-end → …)`.  The `+2` is
the two per-bank closing steps where such a chain first returns onto an
already-merged face orbit.

I confirmed from four independent decomposition attempts (phiLift·faceCorr,
merged·capCycleProd, sigmaLift·…·cutAlphaPerm, and direct `numCycles_conj`/
`mul_comm` manipulation) that **no map-independent disjoint-swap list and no clean
projection semiconjugacy onto `φ` exists** — exactly as the ccf author warned.
The faithful route is therefore the connected per-face-boundary traversal with a
running orbit-partition invariant (the `numCycles_mul_listSwap_{splits,merges}`
toolkit applies, but the swap list must be built adaptively via the φ-bank-end
classifier `divertKind`, mirroring how `cutSigmaPerm_eq_sigmaLift_mul` handled
diverts in V').  This is the `V'`-scale grind (the V' file is 963 lines and *had*
a clean projection; this one does not), and I did not complete it.

Numerically the statement checks out (triangle on the sphere, `k=3`:
`V'=6, E'=6, F'=4`, `χ'=4=χ+2`), so the residual is a genuine open proof, not a
formalization bug.

## Next-pass plan (for the closer)

Define φ-merge / φ-split swap lists indexed by the φ-bank-ends, prove
`φ' = phiLift * mergeProdF * splitProdF` by `ext` (5 dart classes, diverts via
`divertKind`, as in `cutSigmaPerm_eq_sigmaLift_mul`), then walk with
`numCycles_mul_listSwap_{merges,splits}`; the per-step `SameCycle`/¬`SameCycle`
side conditions reduce to **face** (`phiLift`) co-cyclicity, discharged from the
action lemmas already in this file.  The two split steps are the per-bank chain
closures.

## Verification commands

```
rsync -az .../PlanarMapCutCapFCore.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 '... lake env lean ProofsInTheBook/PlanarMapCutCapFCore.lean'   # only the 1 sorry warning
ssh uisai1 '... lake build ProofsInTheBook.PlanarMapCutCapFCore'           # 8437 jobs OK
# #print axioms cutCapPhi_{apply,dart,alpha_dart,capP_cases,capM_cases,inl_other_cases},
#   cutSigma_inl_cases  ->  {propext, Classical.choice, Quot.sound}
# #print axioms cutCapMap_F, numCycles_phiLift_faceCorr  ->  + sorryAx (the single residual)
```
