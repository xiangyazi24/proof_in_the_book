# Kernel Arbitration — Ch35 Jordan cut-and-cap surgery (opus-arbitration)

**Files (sole writer, branch `main`, untracked, no commit):**
`ProofsInTheBook/PlanarMapCutCapEval.lean` (arbitration), `ProofsInTheBook/PlanarMapCutCapSigma2.lean` (fix).
Verified EXCLUSIVELY via rsync→uisai1→`lake env lean` (never ran lake locally — kernel-panic rule honored).

## VERDICT (kernel numbers, verbatim from `lake env lean PlanarMapCutCapEval.lean`)

Base triangle sphere map (Fin 6, α=(01)(23)(45), σ=(05)(12)(34), C = full 3-cycle dart 0→2→4):
```
V=3  E=3  F=2  χ=2  components=1     ✓ valid sphere map
```

IMPLEMENTED cutSigma (mirrored clause-for-clause from PlanarMapCutCapSigma.lean):
```
E'=6   V'=6   F'=8   χ'=8   c=4 components      F+2c-2 = 2+8-2 = 8  (matches F'=8)
```
φ' table (encoded inl d↦d, c_i^+↦100+i, c_i^-↦200+i):
`[(0,0),(2,2),(4,4)] three inl singletons; (1,5,3) reverse face; (100),(101),(102) three +cap FIXED POINTS; (200,201,202) one -cap 3-cycle = 8 orbits.`

CORRECTED cutSigma2:
```
E'=6   V'=6   F'=4   χ'=4   c=2 components      ✓ design intent F'=F+2
```
corrected φ' table: `{0,2,4} forward face; {1,5,3} reverse face; {100,102,101} +cap; {200,201,202} -cap = 4 orbits.`

## ARBITRATION

- **facewalk2 is CORRECT** about the *implemented* map: c=4, F'=8, F'=F+2c-2. The "k=3 anchor F'=4"
  cited by earlier passes was wrong **for the implemented σ'**.
- **dps's c=2** is CORRECT for the *design/corrected* surgery — dps's Python enumerated the intended
  wiring, not what `PlanarMapCutCapSigma.lean` actually implements. Both are right about different maps.
- Root cause: the **implemented cutSigma deviates from the design** (cutcapsigma's "caps are not pure
  cap cycles" flag was the true early signal). It is an off-by-one cap-splice bug, NOT a design flaw.

## DIAGNOSIS (off-by-one +cap splice)

`cutAlpha` pairs `c_i^+` with `q_i = dart i` (α' c_i^+ = dart i). The implemented `cutSigma` then set
`σ'(c_i^+) = q_i = dart i` and `σ'(ℓ_i^+) = c_i^+` (ℓ_i^+ = σ⁻¹ p_i). Because α'(c_i^+) and σ'(c_i^+)
BOTH target index i, φ'(c_i^+)=σ'(α'(c_i^+)) closes immediately ⇒ each +cap is a φ'-FIXED POINT.
The k +caps never thread across indices ⇒ k singletons instead of one +cap k-cycle ⇒ map shatters,
c=4, F' inflated by 2(c-2). The −bank (design reversal) was already correct (one −cap k-cycle).

## FIX (PlanarMapCutCapSigma2.lean — compiles clean on uisai1, axioms = {propext, Classical.choice, Quot.sound})

Shift the +cap wiring by one index so the +cap forms a genuine k-cycle threading all indices:
```
σ'(ℓ_i^+) = c_{prevIdx i}^+      σ'(c_i^+) = dart(nextIdx i) = q_{nextIdx i}    -- +cap FIXED
σ'(ℓ_i^-) = c_i^-               σ'(c_i^-) = p_i                                -- −cap unchanged
σ'(inl d) = inl(σ d)            otherwise
```
Delivered (all proved, 0 sorry/axiom/admit/native_decide):
- `cutSigma2 / cutSigmaInv2` corrected forward+inverse, full 5-case `cutSigma2_leftInv`/`_rightInv`
  bijection bash mirroring the original; `cutSigmaPerm2 : Equiv.Perm`.
- `cutCapMap2 : CombMap C.CutDart` (same cutAlphaPerm, corrected σ').
- seam closed-forms `cutSigma2_capPlus_eq / capMinus_eq / plusEnd / minusEnd / clean`.
- `cutCapMap2_edge_count : E' = E + k` PROVED UNCONDITIONALLY (α' unchanged, card argument).
- `cutCapMap2_eulerChar_eq` (χ'=χ+2 from the corrected V'/F') and `jordan_simple_cycle_of_counts2`
  (same χ'=4 vs χ≤2 contradiction, now on the corrected surgery whose F'=F+2 is the genuine number).
- `CutSigmaCounts2` restates V'/F'/connectivity targets for the corrected map; kernel-confirmed on the
  triangle (6/6/4/2). General V'=V+k, F'=F+2 proofs are the next-round genus-0-per-component target.

## STATUS

Conflict SETTLED inside Lean. facewalk2's numbers are the truth for the *implemented* map (c=4, F'=8);
the implementation, not the design, was wrong (off-by-one +cap splice). The fix is implemented,
permutation-proved, and kernel-rechecked to the design numbers (6/6/4/2, c=2). Downstream files keying
off the OLD `cutCapMap`/`cutSigmaPerm` must switch to `cutCapMap2`/`cutSigmaPerm2`; the conditional
`F'=F+2` hypothesis (facewalk2/dps) becomes genuinely achievable on the corrected map.
