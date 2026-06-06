# TouchCert.lean — bank-component touch certificate for `faceCorr₂` (Chapter 35 F-count residue)

## Status: COMPLETE (reduction layer). 0 sorry / 0 axiom / 0 admit / 0 native_decide. Axioms clean.

File: `ProofsInTheBook/TouchCert.lean` (309 lines). Imports `ProofsInTheBook.TouchRank`.
Verified on uisai1 (the only full build repo; uisai2 carries only a source mirror, no
lakefile/toolchain/.lake). NEVER ran lake/lean locally.

## The honest mathematical situation (read first)

The task asked for `faceCorrTouchCert_exists : ∀ C, C.FaceCorrTouchCert` and an
**unconditional** `cutCapMap2_F_lower`. That is **not abstractly provable** with the current
repository — for exactly the reason recorded in `FaceCorrWord.lean` (lines 63-66) and
`PlanarMapSeamSpec.lean` (lines 28-37):

- The repo carries **NO concrete abstract `SimplePrimalCycle` instance** (triangle / K₄ /
  tetra data live only on the computable `#eval` mirror).
- There is **NO abstract characterisation of `faceCorr₂`'s seam/orbit structure** — the
  factorisation `faceCorr₂ = c₊ · c₋` on disjoint supports, the `phiLift vᵢ = u_{i+1}` seam
  arrows, the gap-face orbits — all are the **named open core** `NumCyclesCutPhi2`, anchored
  only numerically.

The `FaceCorrTouchCert.endpoint_reachable` field (bank-reachability of the word's letters)
**is** that topological residue. So an unconditional `∀ C` instance is impossible here for the
same structural reason the split route could not exhibit an unconditional `FaceCorrSplitCert`.
This matches the design intent: the bank-reachability is isolated cert **data**, parallel to
`FaceCorrSplitCert`. I did not fake an instance; I made the residue **minimal and
position-free**, which is the deliverable that adds genuine math over TouchRank.lean.

## What was built (all unconditional, all verified)

### The per-letter → per-cycle reduction (genuine new math, not a re-wrapper)
- `concatWord_letter_mem` (axioms: `propext, Quot.sound` — Classical-free): **every letter of
  `concatWord Ls` swaps two consecutive elements `L[r], L[r+1]` of one cycle list `L ∈ Ls`**.
  Proved by induction on `Ls` through `appendWord`'s block structure (`dif_pos`/`dif_neg`
  split). This is the bridge from the word's internal `Fin (concatLen Ls)` index to
  cycle-list membership.
- `wordOfList_letter_mem`, `getElem_mem_pair`: the supporting per-block facts.
- `exists_cycleListProd_nodup`: strengthens `FaceCorrWord.exists_cycleListProd` to carry the
  **Nodup** witness of each cycle support (via `Equiv.Perm.nodup_toList`), reproved by
  `cycle_induction_on`.

### `BankComponentCert C` — the minimal position-free residue
Fields: nodup cycle lists `Ls` with `Ls_len`/`Ls_nodup`/`factor` (all **provable** by
`exists_cycleListProd_nodup`), the `2·len − 2` bank generator edges `gen`, and the **single
isolated topological field**:

    same_component : ∀ L ∈ Ls, ∀ x ∈ L, ∀ y ∈ L,
      EqvGen (genRel gen) (pOrbOf phiLift x) (pOrbOf phiLift y)

"every `faceCorr₂`-cycle's darts lie in one connected bank component" — no word positions, no
per-letter indexing. This is the cleanest closed form of the residue (vs `FaceCorrTouchCert`'s
per-letter `endpoint_reachable`).

### `BankComponentCert.toTouchCert` — the builder
Discharges `FaceCorrTouchCert.endpoint_reachable` from `same_component`: letter `j` ↦
`(L[r], L[r+1])` both in `L` (`concatWord_letter_mem` + `getElem_mem_pair`) ↦ one component.
`Ls_pos`, `factor`, `gen` pass through.

### Downstream (unconditional in the word/`prefix_eq`, conditional on the bank cert)
- `cutCapMap2_F_lower_of_bankCert : (cutCapMap2).F ≥ M.F + 2`
- `jordan_simple_cycle2_lower_of_bankCert : ¬ DualReachableAvoidingCycle …`
Both thread `toTouchCert` into TouchRank.lean's `cutCapMap2_F_lower_of_touchCert` /
`jordan_simple_cycle2_lower_of_touchCert`. Same conclusions as the established split route.

## Faithfulness / non-vacuity audit (playbook §3.3)

- **Same conclusion as the established routes.** `cutCapMap2_F_lower_of_bankCert` proves the
  identical `(cutCapMap2).F ≥ M.F + 2` as `…_of_splitCert` (FaceCorrWord) and `…_of_touchCert`
  (TouchRank). Verdict: **CONDITIONAL-honest** — residue isolated to `BankComponentCert`,
  strictly cleaner than `FaceCorrTouchCert`.
- **NOT vacuous.** The premise `factor : cycleListProd Ls = faceCorr2` ties `Ls` to the real
  permutation; for a genuine cut `faceCorr2 ≠ 1` forces `Ls ≠ []`, so `same_component` is a
  non-trivial requirement (it cannot escape via empty `Ls`). The reduction machinery is
  exercised on a concrete multi-letter word: three `example`s (all type-check, hence verified)
  fire `exists_cycleListProd_nodup` on `(0 1 2)` of `Fin 3` and `concatWord_letter_mem` on
  both letters of `[[0,1,2]]` (swaps `(0,1)` and `(1,2)`, consecutive members).
- **Bound NOT inflated.** `BankComponentCert.gen : Fin (2·len − 2)` is the same arity fed to
  the core (`B := 2·len − 2`); `toTouchCert` passes it through verbatim. No contract-field
  inflation of the rank bound.
- **Endpoint indexing faithful.** `(wordOfList L j).x = L[j]`, `.y = L[j+1]` hold by `rfl`
  (matching `wordOfList`'s def), so `same_component` is applied to the genuine swap endpoints.

## Verification

    rsync -az …/TouchCert.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
    ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH \
                && lake build ProofsInTheBook.TouchRank   # 8446 jobs, clean (olean dep)
                && lake env lean ProofsInTheBook/TouchCert.lean'
    → EXIT 0, zero warnings, zero errors.

`#print axioms` on the four headline declarations:

    concatWord_letter_mem              → [propext, Quot.sound]
    exists_cycleListProd_nodup         → [propext, Classical.choice, Quot.sound]
    cutCapMap2_F_lower_of_bankCert     → [propext, Classical.choice, Quot.sound]
    jordan_simple_cycle2_lower_of_bankCert → [propext, Classical.choice, Quot.sound]

No `sorryAx`, no `ofReduceBool`/`native_decide`.

## ONE truly resistant step
None at the reduction layer — all closed. The genuinely irreducible content (`same_component`
/ the abstract `faceCorr₂` seam structure) is the **named open topological core** of the whole
chapter (`NumCyclesCutPhi2`), unreachable without a concrete cut or an abstract `faceCorr₂`
orbit characterisation; it is isolated as the single cert field, not faked.

## Notes for wiring
- Leaf file (nothing imports it). To activate: add `import ProofsInTheBook.TouchCert` to
  `ProofsInTheBook.lean` and the four `#print axioms` lines to `Audit.lean` (I own only
  TouchCert.lean; did not touch the import graph or Audit.lean per one-file-one-writer).
- Branch: main throughout. No commits made (per instructions).
- Build repo is uisai1 (`/home/xhuan5/repos/proof_in_the_book`, full lakefile/toolchain/.lake);
  uisai2's copy is source-only and cannot build.
