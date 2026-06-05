# Face-walk core — reply (opus-facewalk)

**File:** `ProofsInTheBook/PlanarMapFaceWalk.lean` (NEW, sole writer). Imports
`ProofsInTheBook.PlanarMapCutCapFCore`. **Branch:** `main` (not committed/pushed).
Did **not** touch `PlanarMapDualPathSep.lean` (another agent's untracked file).

**Build (uisai1):** `lake env lean` → 0 errors; `lake build
ProofsInTheBook.PlanarMapFaceWalk` → 8438 jobs, success. **0 axiom / 0 admit /
0 native_decide.** Exactly **one** isolated `sorry` (`face_chain_closure_count`),
per the "isolate at most ONE truly resistant invariant step" clause.

## Verdict (honest)

`numCycles (phiLift * faceCorr) = F + 2` is **NOT fully closed**. No fake proof.
What landed is genuine new structure that strictly advances the FCore residual,
plus the same single open count, now precisely localized.

## What is proved here (verified, `#print axioms` = clean-3)

The **exact action of the correction `faceCorr = alphaLift · mergeProd · splitProd
· cutAlphaPerm`** on every dart class, computed *directly from the closed forms*
(not via `φ⁻¹`):

```
faceCorr (capP i)         = inl (α (dart i))          -- faceCorr_capP_generic
faceCorr (capM i)         = inl (dart i)              -- faceCorr_capM_generic
faceCorr (inl (dart i))   = inl (α (σ⁻¹ (dart i)))    -- faceCorr_dart  (= fEndMinus i)
faceCorr (inl (α dart i)) = inl (α (σ⁻¹ p_i))         -- faceCorr_alpha_dart (= fEndPlus i)
faceCorr (inl d)          = inl d                     -- faceCorr_inl_other_generic (non-cycle, non-bank)
faceCorr (fEndMinus i)    = capM i                    -- faceCorr_fEndMinus  (divert closure)
faceCorr (fEndPlus i)     = capP i                    -- faceCorr_fEndPlus   (divert closure)
```

**Key new finding (beyond the FCore handoff):** these close up into **`2k`
pairwise-disjoint 3-cycles** of `faceCorr` (on the generic / no-σ-divert part):

```
(capM i ↦ inl (dart i) ↦ fEndMinus i ↦ capM i)     -- − 3-cycle
(capP i ↦ inl (α dart i) ↦ fEndPlus i ↦ capP i)    -- + 3-cycle
```

where `fEndMinus i = inl (φ⁻¹ q_i)`, `fEndPlus i = inl (φ⁻¹ p_i)`.  The closure is
genuine: each face-end is a **σ-bank-end** (`σ (α (fEnd)) = bank-start`), so
`faceCorr` routes it back to its cap.  Each face-end is **`phiLift`-co-cyclic with
its cycle dart** (one `φ`-step apart on the same old face).  This is the localized
3-cycle picture the FCore handoff said did not exist as "`k` local 4-cycles" — it
exists as `2k` local **3-cycles** (one cap + one cycle dart + one face-end each).

`numCyclesPhiLiftFaceCorr_holds` and the unconditional `cutCapMap_F' :
(C.cutCapMap).F = M.F + 2` are wired through the isolated count.

## The remaining core (precisely isolated) and why it resists

Writing each 3-cycle as `swap(cap,cycle)·swap(cycle,faceEnd)` and walking the
`4k`-transposition product against `phiLift` (`numCycles phiLift = F + 2k`, proved),
each step's `SameCycle` side-condition is a **face co-cyclicity of `M.φ`**.  Target
net is `−2k + 2` ⟹ of the `4k` steps, `k+1` split / `3k−1` merge.  The split/merge
status is **adaptive**: it depends on which face-ends/caps have already been
threaded by *prior* 3-cycles, i.e. on **which cycle indices lie on the same
incident face** — and on the σ-divert coupling between adjacent 3-cycles (when
`σ(dart i)` is itself a bank-start, two 3-cycles fuse into a longer chain). The
`+2` is the two cut faces' chain closures.

Pinning this down needs the **face-incidence data** `faceLeft`/`faceRight` (the two
faces of a cycle edge) from `PlanarMapCutCapConn.lean` — outside this σ/φ-only
layer.  This is consistent with the FCore handoff's independent four-decomposition
finding (no clean projection semiconjugacy: `φ'` fixes each `inl (dart i)` while
`φ` moves it; the `inl (α dart i) ↦ inl p_i` jump is a non-`φ` step). I separately
ruled out the Euler shortcut: `eulerChar_eq` (`χ' = χ + 2`) is proved *from*
`face_count` in `PlanarMapCutCap.lean`, so it is **circular** for this purpose;
`F' = F + 2` is a primitive input, not derivable from `V'=V+k`, `E'=E+k`, `χ'`.

Numerically verified at `k = 3` (triangle on the sphere): `F + 2k − 2k + 2 = F + 2
= 4`, `V'=6, E'=6, F'=4, χ'=4=χ+2`.

## Net advance over the FCore handoff

- The `2k`-disjoint-3-cycle structure of `faceCorr` is **new, explicit, and fully
  verified** (7 closed-form action lemmas, clean-3). The residual is reduced from
  "the whole `faceCorr` walk" to purely the **adaptive face-orbit split/merge
  count** (the `±` bookkeeping over the two cut faces / divert-coupled chains).
- Reconfirmed via the Euler-circularity check that the count is genuinely
  primitive at this layer, and via direct projection attempts that no `φ`-side
  semiconjugacy exists.

## Next-pass plan (for the closer)

Import the face-incidence layer (`faceLeft`/`faceRight`, `dartFace`,
`DualReachable…` of `PlanarMapCutCapConn.lean`). Partition the `k` cycle indices by
incident face; show the `2k` cap-threads merge the caps onto exactly those two
faces; handle σ-divert coupling (when `σ(dart i)` is a bank-start, fuse the two
3-cycles before counting). Then the `4k`-step walk via
`numCycles_mul_listSwap_{splits,merges}` closes with net `−2k+2`. The per-step face
co-cyclicities reduce to `M.φ.SameCycle` facts on `inl`-darts (analogue of the
`σ`-side `sameCycle_merged_*` family in `PlanarMapCutCapV.lean`).

## Verification commands

```
rsync -az .../PlanarMapFaceWalk.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 '... lake env lean ProofsInTheBook/PlanarMapFaceWalk.lean'   # only the 1 sorry warning
ssh uisai1 '... lake build ProofsInTheBook.PlanarMapFaceWalk'           # 8438 jobs OK
# #print axioms faceCorr_{capP_generic,capM_generic,dart,alpha_dart,fEndMinus,fEndPlus,
#   dart',alpha_dart',inl_other_generic}  ->  {propext, Classical.choice, Quot.sound}
# #print axioms cutCapMap_F', numCyclesPhiLiftFaceCorr_holds  ->  + sorryAx (the single residual)
```
