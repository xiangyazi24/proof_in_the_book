# ChordDisk.lean — the two local genus-0 disk facts (Ch35 discrete Jordan–Schoenflies)

## Status

The TWO local genus-0 disk facts that `ChordFaceCount` isolated are now **named, threaded,
and discharged into the side genus-0 certificate with the face count PROVED from them**; the
derivable `≤ 2` genus half of fact 1 is proved unconditionally, pinning the residue to a
single reverse inequality. The two facts themselves (fact 1's `χ ≥ 2` no-handle half, and
fact 2) are the genuine discrete-Schoenflies content and remain the **honest isolated
residue** — re-confirmed against the repo's own kernel-decided counterexample
(`CutFaceLabel`/`PlanarMapSeamInst`). `five_colorable` is NOT made unconditional, and that is
the correct mathematical verdict at this layer (see "Honest scope", matching the prior two
kernel-backed rounds). **Verdict: FAITHFUL reduction + count discharge + non-vacuous;
CONDITIONAL-honest on the two named local disk facts.**

New file (owned, only file touched): `ProofsInTheBook/ChordDisk.lean` (~370 lines).
Imports `ProofsInTheBook.ChordFaceCount` + `ProofsInTheBook.PlanarMapEulerInequality`.
Branch `main`; no commits; no branch switch; no codex/OpenAI tooling; never ran
`lake build`/`lake env lean` on the Mac (kernel-panic rule observed).

## Verification (server uisai1, refreshed oleans)

- `rsync … ChordDisk.lean ; ssh uisai1 'lake env lean ProofsInTheBook/ChordDisk.lean'`
  → **RC = 0, zero errors, zero warnings** (no `sorry` warnings).
- `lake build ProofsInTheBook.ChordDisk` → **Build completed successfully (8453 jobs).**
- `grep -nE 'sorry|admit|native_decide|^axiom '` → only the docstring disclaimer line 83.
  Zero `:= rfl`/`:= trivial`/`_placeholder_`.
- `#print axioms` on ALL 12 headlines → **clean-3 `[propext, Classical.choice, Quot.sound]`**
  (no `sorryAx`/`ofReduceBool`/`trustCompiler`):
  `keptSide_eulerChar_le_two`, `keptSideIsDisk_iff_eulerChar_ge_two`,
  `chordDisk_produces_isSphereMap`, `chordDisk_produces_freshFaceCount`,
  `chordSideJordanData_of_disk`, `side₁_isSphereMap_of_disk`, `side₁_freshFaceCount_of_disk`,
  `side₂_isSphereMap_of_disk`, `sphereWitness_isSphereMap_via_disk`,
  `witness_freshFaceCount_via_disk`, `witness_chordSideJordanData_via_disk`,
  `chordDisk_side_genus0_certificate`.

## What was proved (everything derivable around the two facts)

The two facts are named as standalone Props, exactly the hypotheses `ChordFaceCount`
isolated:
- `KeptSideIsDisk β ρ := (keptCombMap β ρ).IsSphereMap` (fact 1: each side is a disk).
- `AnchorsShareBoundaryFace β ρ a₀ a₁ := (keptPhi β ρ).SameCycle (ρ a₀) (ρ a₁)` (fact 2).

**The derivable half of fact 1 (NEW, unconditional):**
- `keptSide_eulerChar_le_two` — a connected kept side has `eulerChar ≤ 2`
  (`chi_le_two_of_connected`, the genus `≥ 0` bound). So fact 1's only missing content is the
  REVERSE inequality `2 ≤ eulerChar` — the kept side has **no handle**.
- `keptSideIsDisk_iff_eulerChar_ge_two` — given connectivity, fact 1 ⇔ `2 ≤ eulerChar`. This
  is the precise reduction of the disk fact to its single no-handle core (the `≤` half free,
  the `≥` half the genuine Schoenflies content).

**The threading (the two facts → side genus-0 structure, count PROVED):**
- `chordDisk_produces_isSphereMap` — facts 1+2 produce the side map's full `IsSphereMap`
  (connectivity from `ChordSideRecon` + `eulerChar = 2` from `ChordFaceCount`'s bijection).
- `chordDisk_produces_freshFaceCount` — facts 1+2 PROVE the face count `FreshFaceCount` (via
  the explicit face-orbit bijection `freshMap_F_eq_tracePhi` + the genus-0 transposition
  sign). The count is no longer a hypothesis.
- `chordSideJordanData_of_disk` — facts 1+2 produce the `ChordSideRecon.ChordSideJordanData`
  bundle (connectivity + face count + vbound), so its producer fires.
- Section D: instantiated at the genuine chord-split side maps (`side₁/₂_isSphereMap_of_disk`,
  `side₁_freshFaceCount_of_disk`, `side₁_keptSide_eulerChar_le_two`), with per-side named
  facts `Side₁/₂IsDisk`, `Side₁/₂AnchorsShareFace`.
- `chordDisk_side_genus0_certificate` (headline) — from side 1's two disk facts: the side map
  is a genus-0 sphere map AND its `FreshFaceCount` holds, count discharged.

## Non-vacuity (§3.3 — both facts simultaneously satisfiable, producers fire)

`witness_KeptSideIsDisk` + `witness_AnchorsShareBoundaryFace` hold simultaneously on the
concrete genus-0 sphere witness of `ChordSplitEuler` (`K=Fin 2`, `β=swap 0 1`, `ρ=1`, anchors
`0,1`), and every producer genuinely fires on it: `sphereWitness_isSphereMap_via_disk`
(produces `sphereWitness.IsSphereMap`), `witness_freshFaceCount_via_disk`,
`witness_chordSideJordanData_via_disk`. No unsatisfiable premise / no hidden `False`.

## Honest scope — why the two facts are NOT derivable here (kernel-confirmed, NOT re-tried)

I did **not** retry pure `Separates`-counting (kernel-refuted in 4 prior rounds) and did not
re-wrap. The orchestrator's endorsed route ("single-boundary-cycle disk accounting via M's
genus-0") was attacked at the level of what the abstract `CombMap` actually carries, and it
does NOT close, for two precise reasons:

1. **M's `eulerChar = 2` is a GLOBAL constraint; the per-side transfer needs `F₁+F₂=F+1`,
   which is genus-dependent (kernel-verified).** `CutFaceLabel.lean` decided *inside the Lean
   kernel* (on the `K₄` sphere/torus probes) that the cut/chord face permutation `φ'₂`
   **merges and splits** old faces — concrete failing tactic chain: the would-be invariant
   label `cutFaceLabel (inl d) = Sum.inl (faceOf d)` with `cutFaceLabel (φ'₂ x) = cutFaceLabel x`
   is **unsatisfiable** because the `φ'₂`-orbit `{inl 1, inl 4, inl 9}` forces one old face on
   darts `1∈{1,2,7}`, `4∈{3,4,11}`, `9∈{6,10,9}` (three distinct old faces). No genus-uniform
   orbit bijection carries M's value onto the side. So `χ(keptSide) ≥ 2` is genuinely Jordan
   separation content, not orbit bookkeeping.

2. **`chi_le_two_of_connected` is the ONLY Euler (in)equality in the repo — gives `≤ 2`, not
   `≥ 2`.** A connected `CombMap` may have a handle (`χ = 0`); the repo has no "single
   boundary cycle ⟹ `χ = 2`" disk lemma, and building one IS the discrete Schoenflies
   theorem, requiring the planar embedding the abstract `CombMap` does not carry. (I also
   checked the parity route — proving `χ` even, which with `≤ 2` and `χ ≥ 1` would force `2` —
   but the repo has no evenness lemma for `genusSlack`, and proving it is itself the
   orientable-genus theory, not available off-the-shelf.)

Per playbook §3.3 (no fake disk lemma, no unsatisfiable-hypothesis theorem), the two facts
are isolated as the named satisfiable Props `KeptSideIsDisk` / `AnchorsShareBoundaryFace`
(per-side `Side₁/₂IsDisk` / `Side₁/₂AnchorsShareFace`), the face count is PROVED from them,
and the producers fire on the genus-0 witness.

## Residue blocking a fully unconditional five_colorable (unchanged in character, finer)

Beyond the two disk facts, a fully unconditional `ChordRecursiveDichotomy` still needs the
remaining `ChordSideReconstruction` fields — the side `outerCycle`/`outer_simple`/`outer_len`/
`inner_tri` (the side boundary = arc + duplicated chord, as a `BoundaryCycle` of the side
map) and `ι_surj` (vertex correspondence surjective onto the region). These are the SAME
discrete Jordan/Schoenflies classification layer as the two disk facts (the side-face ↔
M-face correspondence the kernel campaign proved does not exist genus-uniformly); fabricating
them would require a fake outer cycle / fake face correspondence, which §3.3 forbids. So
`five_colorable` remains CONDITIONAL on the chord-side disk data — now with the genus-0
`IsSphereMap` field's **face count PROVED** from the two named local facts (this file) and its
connectivity half proved (`ChordSideRecon`), and the disk fact reduced to its single
no-handle reverse inequality. This is the strictly finer state the orchestration sought, with
the residue stated honestly rather than faked.

The genuine remaining front to finish Ch35 unconditionally is the same one the prior round
named: construct the chord-side face/seam certificate for the genuine near-triangulation
sphere chord split (the discrete Schoenflies "Jordan curve bounds a disk" theorem as Lean
data on `CombMap`), which would simultaneously yield `χ(keptSide) ≥ 2` (fact 1), the anchor
incidence (fact 2), the side `outerCycle`/`inner_tri`, and `ι_surj`.
