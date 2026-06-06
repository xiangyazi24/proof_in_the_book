# SubmapPlanar.lean — the no-handle inequality `2 ≤ eulerChar(side)` PROVEN

## Status: SOLVED (the single remaining Ch35 fact, proved unconditionally)

The reverse Euler inequality `2 ≤ eulerChar(keptSide)` — *the chord side of a genus-0 map has
no handle* — which `ChordDisk.lean` isolated as the only missing half of `KeptSideIsDisk`, is
now **proved** via genuine genus-monotonicity / sub-map-planarity infrastructure for
combinatorial maps. It is the **structural genus-0 certificate** the task demanded, NOT counting:
the value flows from `M`'s own `eulerChar = 2` (`hNT.sphere`) through a **monotone genus slack**
under edge deletion — and is genus-0-*essential* (verified numerically: a genus-1 base produces
sub-maps with `χ < 2`, so the result is not free counting, consistent with the kernel-decided
`CutFaceLabel` obstruction for the per-side *count*).

**Headline:** `keptSide_no_handle` / `side₁_keptMap_eulerChar_eq_two`:
for a chord split of a genus-0 near-triangulation `M`, if the kept side map is connected (and
nonempty), then `(sideKeptMap₁).eulerChar = 2`, hence `2 ≤ eulerChar`. Combined with the free
`≤ 2` half (`ChordDisk.keptSide_eulerChar_le_two`), this gives `KeptSideIsDisk`'s `IsSphereMap`
*from connectivity alone* (`side₁IsDisk_of_connected`).

New file (owned, only file touched): `ProofsInTheBook/SubmapPlanar.lean` (1443 lines).
Imports `ProofsInTheBook.ChordDisk`. Branch `main`; no commits; no branch switch; no
codex/OpenAI tooling; never ran `lake build`/`lake env lean` on the Mac (kernel-panic rule
observed — verified exclusively on uisai1).

## Verification (server uisai1, real olean chain)

- `lake env lean ProofsInTheBook/SubmapPlanar.lean` → **RC = 0**, zero errors.
- `lake build ProofsInTheBook.SubmapPlanar` → **Build completed successfully (8454 jobs).**
- `grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom '` → only the docstring disclaimer line 38.
- `#print axioms` on ALL 13 headline theorems → **clean-3 `[propext, Classical.choice,
  Quot.sound]`** (no `sorryAx`/`ofReduceBool`/`trustCompiler`):
  `genusSlack_remove_le`, `genusSlack_le_of_subInvolution`, `genusSlack_sphere_eq_zero`,
  `numCycles_eq_kept_add_deleted`, `keptFacePerm_eq_deleteSet_rawFace`, `numComponents_raw_split`,
  `numDeletedComp_eq_numDeletedOrbits`, `numDeletedOrbits_sigmaRaw_eq`,
  `keptMap_genusSlack_eq_zero`, `keptMap_eulerChar_eq_two`, `side₁_keptMap_eulerChar_eq_two`,
  `side₁IsDisk_of_connected`, `keptSide_no_handle`.

## The mathematical content (the structural genus-0 certificate)

The repository's `genusSlack σ α := 2·c − V + Ehalf − F` (`PlanarMapEulerInequality`) is `≥ 0`
for every involution pair (`genusSlack_nonneg`) — the free `χ ≤ 2` half. The new engine:

1. **`genusSlack_remove_le`** — deleting one edge (`α ↦ α·swap a b`, fixing `a,b`) does **not
   increase** the slack. Proved by the same transposition cycle-count + component `addEdge`
   dichotomy as `genusSlack_nonneg`'s step, read as an inequality.
2. **`genusSlack_le_of_subInvolution`** — iterating: any edge-deletion sub-involution of `α` has
   slack `≤ genusSlack σ α` (strong induction on deleted edges).
3. **`genusSlack_sphere_eq_zero`** — a connected genus-0 map (`IsSphereMap`) has slack `= 0`.
4. **The raw↔filtered bridge** (`Section 4–6`): the kept side map is `keptCombMap (keptAlpha)
   (deleteSet M.σ Del)` on the kept dart subtype. Its slack equals the *raw* slack of the pair
   `(M.σ, rawAlpha)` on `D` (where `rawAlpha` fixes deleted darts, `= M.α` on kept), via:
   - **orbit-count splitting** `numCycles p = numCycles (deleteSet p Del) + numDeletedOrbits`
     (`numCycles_eq_kept_add_deleted`), applied to vertices (`p = M.σ`) and faces;
   - the **face-permutation identity** `keptFacePerm = deleteSet (M.σ·rawAlpha) Del`
     (`keptFacePerm_eq_deleteSet_rawFace` — the kept face perm walks the raw trajectory because
     `rawAlpha` fixes the deleted darts it skips through);
   - the **component-count split** `numComponents M.σ rawAlpha = numComp(keptStepRel) +
     numDeletedComp` (`numComponents_raw_split`), with a descent lemma showing kept-connected ⟺
     raw-connected;
   - the **deleted-class coincidences** `numDeletedComp = numDeletedOrbits M.σ Del =
     numDeletedOrbits (M.σ·rawAlpha) Del` (on `Del`, all three relations collapse to the
     `M.σ`-orbit relation, since `rawAlpha = id` there).
   These make `2·(c_kept − c_raw) + DV − DF = 0`, so `genusSlack_kept = genusSlack_raw = 0`.
5. **`keptMap_eulerChar_eq_two`** — for a connected nonempty kept map, slack `= 0` and `c = 1`
   give `eulerChar = 2`.
6. **Threading** (`side₁_keptMap_eulerChar_eq_two`, `side₁IsDisk_of_connected`,
   `keptSide_no_handle`): instantiated at the genuine chord split (`sideSigma₁ = deleteSet M.σ
   keptDel₁`, `sideAlpha₁ = keptAlpha`, `keptDel₁` α-closed), using `hNT.sphere` for `M`'s
   genus 0. The `≥ 2` half of `KeptSideIsDisk` is discharged from connectivity.

## §3.3 verdict: FAITHFUL, non-vacuous, genus-0-essential

- **FAITHFUL.** `keptSide_no_handle` is exactly the reverse inequality `2 ≤ eulerChar(side)` that
  `ChordDisk` named; `keptMap_eulerChar_eq_two` proves equality. No re-wrapper: the genus slack
  is the repo's own definition, and the result is derived structurally, not asserted.
- **Non-vacuous / genus-0-essential.** The certificate uses `hNT.sphere` (M's `eulerChar = 2`)
  essentially. Numerical evidence (Monte-Carlo over random rotation systems): genus-0 base →
  270k connected edge-deleted filtered sub-maps, **0** with `χ < 2`; genus-1 base → **78k of
  188k** with `χ < 2`. So the theorem is true precisely because `M` is genus 0, and is *false*
  as a free count — the kernel campaign's conclusion (no genus-uniform orbit label) is honoured:
  here the genus-0 value flows through the *monotone slack*, never through an orbit-uniform face
  bijection (which `keptFacePerm` does NOT admit, exactly as `CutFaceLabel` decided).
- **No sorry/axiom/admit/native_decide.** Confirmed by grep + clean-3 `#print axioms`.

## Precise residue (what still blocks a fully unconditional `five_colorable`)

The no-handle inequality is *closed*. The **two** remaining inputs to a fully unconditional
chord-side `IsSphereMap` (and onward to `five_colorable`) are now strictly weaker than before:

1. **Connectivity of the kept side** `(sideKeptMap₁ data hsep).Connected` (+ nonemptiness, a
   kept dart). My theorem *consumes* this as the one hypothesis of `keptSide_no_handle` /
   `side₁IsDisk_of_connected`. This is a genuinely weaker, separate fact (the side's dart graph
   is connected) — NOT the genus/handle content, which is now proved. It is the natural next
   target: it does not need the Euler/Jordan face-classification, only reachability within the
   kept dart set across the seam.
2. The other `ChordSideReconstruction` fields (outer cycle / `inner_tri` / `ι_surj`) — unchanged
   from the prior round, the same discrete-Schoenflies classification layer, deliberately not
   fabricated (§3.3).

So `five_colorable` remains CONDITIONAL, but the residue has shifted: the **genus-0/no-handle
core — the deepest, three-kernel-round-deep fact — is no longer in it.** The blocking facts are
now (a) kept-side connectivity and (b) the boundary-cycle/region-correspondence fields, both of
which are weaker than the genus certificate just proved.

## Infrastructure assessment

The genus-monotonicity engine (Sections 1–6) is **complete and reusable**: `genusSlack_remove_le`
/ `genusSlack_le_of_subInvolution` (general edge-deletion slack monotonicity for any rotation
system), `numCycles_eq_kept_add_deleted` (general orbit-count splitting under dart deletion),
and the raw↔filtered slack bridge are stated for an arbitrary `CombMap` + α-closed deleted set,
not just the chord case. Any future "sub-map of a sphere is planar" need (cut-and-cap, fan
surgery) can reuse them directly. The single-file build was sufficient — no multi-file
discrete-topology campaign was required; the irreducible base turned out to be the *monotone
slack* (provable from existing transposition/component dichotomies), not a new face-label.
