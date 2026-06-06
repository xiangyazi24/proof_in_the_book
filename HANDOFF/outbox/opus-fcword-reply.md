# FaceCorrWord.lean — reply (Opus)

## Status: PARTIAL — the `faceCorr₂` WORD + `prefix_eq` field closed UNCONDITIONALLY and
## GENUS-FREELY; the residue strictly localised to the split `SameCycle` data alone.

New file: `ProofsInTheBook/FaceCorrWord.lean` (~540 lines). I own only this file; no other
file touched, no commit, branch `main` (remote `uisai2` is an rsync target, not a git
checkout — uisai1 is DOWN as noted).

Verified EXCLUSIVELY on uisai2:
`lake env lean ProofsInTheBook/FaceCorrWord.lean` → **EXIT 0**, and the integrated
`lake build ProofsInTheBook.FaceCorrWord` → **8445 jobs, Build completed successfully**.
All 6 headline lemmas `#print axioms` = `[propext, Classical.choice, Quot.sound]` only.
**0 sorry / 0 axiom / 0 admit / 0 native_decide** (grep-clean; only doc/`#print` mentions).

## What is CLOSED here (new, unconditional, genus-free, clean-3 axioms)

**Layer A — the universal list→transposition-word bridge** (pure `Equiv.Perm`, any finite X):
- `wordOfList L` — the consecutive-transposition word `(L[j], L[j+1])` of a list.
- `prefixPerm_wordOfList` / `prefixPerm_wordOfList_full` :
  `prefixPerm p (wordOfList L) (L.length−1) = p · formPerm L`.  The `Swap`/`prefixPerm`
  shadow of `SeamChain.formPerm_take_succ`.
- `appendWord` + `prefixPerm_appendWord` — concatenation composes prefix products.
- `concatWord` + `prefixPerm_concatWord` :
  `prefixPerm p (concatWord Ls) (concatLen Ls) = p · cycleListProd Ls` (a list-of-lists
  realises its cycle-decomposition product).
- **`exists_cycleListProd`** : **EVERY** finite permutation `q` is `cycleListProd Ls` for
  some list-of-lists `Ls` of nonempty nodup cycle lists.  Proven by Mathlib
  `cycle_induction_on` + `Equiv.Perm.toList` (`formPerm_toList`, `IsCycle.cycleOf_eq`).
  → the word for `faceCorr₂` **exists unconditionally**, so `FaceCorrLowerCert.prefix_eq`
  reduces to pure Mathlib cycle theory.

**Layer B — the split-only certificate** (instantiated at `phiLift`, `faceCorr₂`, `len`):
- `FaceCorrSplitCert C` — carries the cycle-decomposition `Ls` + `factor :
  cycleListProd Ls = faceCorr₂` (always available, by `exists_cycleListProd`) + the split
  data `(s, splitIdx, injective, split_ne, forced_split)` + `hbound`.
- **`FaceCorrSplitCert.toLowerCert`** — builds a full `ForcedSplits…FaceCorrLowerCert`:
  `W := concatWord Ls`, **`prefix_eq` discharged** via `prefixPerm_concatWord` + `factor`.
  Only the split `SameCycle` facts are supplied.
- `cutCapMap2_F_lower_of_splitCert` : `(cutCapMap2).F ≥ M.F + 2` (genus-free).
- `jordan_simple_cycle2_lower_of_splitCert` : the Jordan / chord-wall contradiction
  (hypotheses `{splitCert, M.eulerChar = 2, per-edge connectivity}`), the chord wall's
  final lower-bound form — `chi_le` discharged internally (it is `jordan_simple_cycle2_lower`
  of `ForcedSplits.lean` fed through `toLowerCert`).
- A non-vacuity `example` exercising `prefixPerm_concatWord` on `Fin 3` (the `prefix_eq`
  identity is real, not vacuous).

## The DECISIVE finding (corrects the prior reconnaissance)

The prior `ForcedSplits` handoff recorded the *word / `prefix_eq`* as part of the
irreducible core.  **It is not.**  In-file kernel `#eval` anchors (computable mirror,
clause-for-clause with `SeamInstEval`) verify the **cycle-list word realises
`phiLift · faceCorr₂` = `true` on the triangle, the K₄-SPHERE, AND the K₄-TORUS (genus 1)**:

```
("TRIANGLE word realises prefix_eq?", true)
("K4-sphere ABD word realises prefix_eq?", true)
("K4-torus  ABD word realises prefix_eq? (GENUS 1)", true)
```

So the WORD is genus-free and now closed for all C.  What is NOT genus-free is the SPLIT
COUNT: the constraint `m + 2 ≤ 2·s + 2·len` holds with **slack 0** (because the exact
identity `F' = F + 2` is itself genus-free), so the split count is forced to be exactly
`s_actual = (m − 2·len + 2)/2` and *every* split must be certified.  The split positions
have no uniform symbolic rule (kernel-checked, cut/genus-dependent: triangle s=0;
K₄-sphere ABD s=3 @ positions 2,5,6; K₄-torus s=3 @ 2,3 + 0; sphere alt cut s=4 @ 3,6,7,8).
Cycle shapes likewise vary (`[3,3,3,3]` / `[2,2,3,2,6,3]` / `[3,6,2,7]` — last = torus caps
threaded into combined cycles, no two-chain factorisation).

## The SINGLE isolated residue (named, honest, after genuine exhaustion)

Only the **`s` split `SameCycle` fields of `FaceCorrSplitCert`** remain open in general.
This is strictly smaller than the prior `FaceCorrLowerCert` residue (word + prefix_eq +
splits) and far smaller than the refuted two-cap-chain `SeamDecomposition` (which fails at
genus 1).  Reason it is irreducible: slack-0 forces certifying all `s_actual` splits, and
their positions encode the cut's gap-face threading with no projection semiconjugacy — the
genuine topological core the chapter has circled.  Named, not faked.

## Honest scope notes (NOT done, with reasons)

- **No unconditional triangle `FaceCorrLowerCert` instance.**  The repo carries **no**
  concrete abstract `SimplePrimalCycle` instance — the triangle/K₄ data live only on the
  computable mirror (`#eval`). An abstract instance would require building a whole abstract
  triangle map + cycle from scratch (out of scope, separate file). The triangle's `s = 0`
  is anchored numerically, not as an abstract instance.  Docstring states this plainly.
- **NearTriangulation `separates` corollary not re-wired through the lower-bound path.**
  The existing `PlanarMapBridgeWitness.separates2_of_core` is keyed on the OLD interface
  (`hcore : NumCyclesCutPhi2` exact count + external `chi_le` + `CutBridgeWitness2`).  The
  new lower-bound path deliberately drops `NumCyclesCutPhi2` and `chi_le`, and uses a
  different connectivity hypothesis shape, so re-deriving the separates corollary would
  require editing `PlanarMapBridgeWitness.lean` (another owner's file).  Not touched.
  `jordan_simple_cycle2_lower_of_splitCert` IS the chord-wall final form in the new
  interface.

## Wiring note (for whoever integrates)

`FaceCorrWord.lean` imports `ProofsInTheBook.ForcedSplits` + `…PlanarMapSeamChain` (both
already built). To audit, add `import ProofsInTheBook.FaceCorrWord` to `Audit.lean`.
`FaceCorrSplitCert.toLowerCert` is the drop-in producer of `ForcedSplits`'
`FaceCorrLowerCert`: feed it the cycle-decomposition `Ls` (existence is `exists_cycleListProd`)
and the `s` split certificates.

## Verification commands (reproduce)

```
rsync -az .../FaceCorrWord.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai2 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH && \
  lake env lean ProofsInTheBook/FaceCorrWord.lean'        # EXIT 0
ssh uisai2 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH && \
  lake build ProofsInTheBook.FaceCorrWord'                # 8445 jobs, success
# 6 headline #print axioms → {propext, Classical.choice, Quot.sound}
# 3 kernel #eval → wordRealisesPrefix = true on triangle / K4-sphere / K4-torus
```
