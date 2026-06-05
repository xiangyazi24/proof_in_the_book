# opus-cc2counts reply — corrected cut-and-cap counts (Ch 35 Jordan)

**File (sole owner):** `ProofsInTheBook/PlanarMapCutCap2Counts.lean` (335 lines, new leaf).
Imports `PlanarMapCutCapSigma2` (corrected σ') + `PlanarMapCutCapFCore` (pulls in
V/F/Counts/Sigma toolkit, incl. `numCycles_conj`, `numCycles_cutSigmaPerm`).

**Branch:** main. No commits, no codex/OpenAI tooling. Verified EXCLUSIVELY on uisai1
via rsync + `lake env lean` (never `lake build`/`lake env lean` on the Mac).

## Status

| Target | Status |
|--------|--------|
| **V' = (cutCapMap2).V = M.V + C.len** | **PROVED unconditionally** (`cutCapMap2_V`) |
| **F' = (cutCapMap2).F = M.F + 2** | reduced + **one** named corrected core (`cutCapMap2_F` ← `NumCyclesCutPhi2`) |
| Assembly (Jordan / counts) | `jordan_simple_cycle2_of_core`, conditional on the core + the one connectivity parameter |

### 1. V' — the key trick (no re-run of the 963-line V machinery)

`cutSigma2` differs from the buggy `cutSigma` ONLY at the `+`-cap wiring, and that
difference is *exactly an index shift of the +caps*. Writing `g = capShift` for the
permutation `c_i^+ ↦ c_{nextIdx i}^+` (identity on `inl d` and on every `c_i^-`),
a 5-case dart-by-dart check (`capShift_cutSigma2`) gives

```
g (σ'₂ x) = σ' (g x)   ⟹   σ'₂ = g⁻¹ · σ' · g    (cutSigmaPerm2_eq_conj)
```

The `prevIdx`/`nextIdx` discrepancy is consumed by `nextIdx_prevIdx`. Then
conjugation-invariance of `numCycles` (`CutCapCount.numCycles_conj`) + the buggy
`numCycles_cutSigmaPerm = V + k` give `numCycles σ'₂ = V + k` (`numCycles_cutSigmaPerm2`),
hence `V' = V + k`. Fully unconditional.

### 2. F' — reduced to ONE honest named core

`α'` is unchanged, so `φ'₂ = σ'₂ · α'`. The conjugation does NOT carry over to φ
(`g` does not commute with `α'`), so F' is genuine new content — it is precisely the
part the fix repairs (the buggy map had the wrong F'). I established the **full
per-class action of `φ'₂` unconditionally**:

- `cutCapPhi2_dart`: `φ'₂(inl(dart i)) = inl(dart(nextIdx i))` — the forward cycle
  darts now **thread forward** (in the buggy map they were φ'-fixed points: the
  visible signature of the bug being fixed);
- `cutCapPhi2_alpha_dart`: `φ'₂(inl(α dart i)) = inl(p_i)`;
- `cutCapPhi2_capP_cases`/`capM_cases`/`inl_other_cases` + `cutSigma2_inl_cases`:
  the three-way (clean / divert-to-prev-+cap / divert-to-−cap) action on every class.

The single isolated open fact is the global orbit count
`NumCyclesCutPhi2 : numCycles (cutCapMap2.φ) = M.F + 2`, from which `cutCapMap2_F`
follows by `F_eq_numCycles`. This is the F-analogue of the V' count but, as in the
buggy `PlanarMapCutCapFCore.lean`, has no clean projection semiconjugacy (φ'₂ moves
`dart i` whereas σ moves it differently), so the orbit bijection is a genuine
`SameCycle` bookkeeping along the corrected cap threading. **Crucially**: unlike the
buggy `NumCyclesPhiLiftFaceCorr`, here the value `F + 2` is the *true* design number
— kernel-verified F'=4 (triangle), F'=6 (tetrahedron) in `PlanarMapCutCapEval.lean`.
This is the "at most ONE truly resistant piece, named + honest" allowed by the task.

### 3. Assembly

`cutSigmaCounts2_of_core_of_conn` builds `CutSigmaCounts2` from (proved V') +
(F' core) + (per-edge connectivity parameter `hconn`). `jordan_simple_cycle2_of_core`
threads it through the already-verified `jordan_simple_cycle_of_counts2`. Connectivity-
from-dual-path is the single isolated parameter (the dps/conn layers port separately,
mirroring `PlanarMapCutCapConn.lean`), exactly as the task specifies.

## Verification (on uisai1)

- `lake env lean ProofsInTheBook/PlanarMapCutCap2Counts.lean` → EXIT 0, zero errors
  (only `unusedSectionVars`/`unusedSimpArgs` linter notes).
- `lake build ProofsInTheBook.PlanarMapCutCap2Counts` → `Build completed successfully`.
- `#print axioms` on `cutCapMap2_V`, `numCycles_cutSigmaPerm2`, `cutSigmaPerm2_eq_conj`,
  `cutCapMap2_F`, `cutCapPhi2_dart`, `jordan_simple_cycle2_of_core` → all exactly
  `{propext, Classical.choice, Quot.sound}` (clean-3).
- `grep -nE '\bsorry\b|\badmit\b|\bnative_decide\b|^axiom '` → matches only in the
  doc header prose; **no** sorry/axiom/admit/native_decide in code.
- File is a leaf (nothing imports it); no other module touched; no commit.

## Faithfulness notes (Group C)

- `cutSigmaPerm2_eq_conj` is a genuine conjugation by a nontrivial permutation, not a
  re-wrapper or trivially-true statement; the dart-by-dart intertwiner is its content.
- `NumCyclesCutPhi2` is unconditional, satisfiable, NOT vacuous and NOT trivially true
  (a real equation on the corrected map's actual face permutation, value kernel-anchored).
- `cutCapMap2_F` / `jordan_simple_cycle2_of_core` are CONDITIONAL-honest on that one
  core (+ the sanctioned Euler inequality + the connectivity parameter).

## Remaining open (next round)

`NumCyclesCutPhi2` (the corrected face-cycle count). The per-class φ'₂ action is all
in place; the remaining work is the orbit bijection / transposition-walk count along
the corrected +cap threading. The kernel numbers (triangle 6/6/4/2, tetra 7/9/6/2) are
the anchor.
