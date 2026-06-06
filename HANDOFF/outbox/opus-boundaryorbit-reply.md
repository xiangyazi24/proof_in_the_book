# Ch35 BoundaryOrbitClass via the EXPLICIT chord-dart φ'₂-trace: splice-untouchedness DISCHARGED
unconditionally for ALL faces; residue collapsed to ONE concrete two-orbit incidence
`OuterAbsorbsChordOrbits` (NOT the refuted uniform label). Headline stays CONDITIONAL on
JordanOracle (clean-3, unchanged).

## TL;DR (honest, §3.3)

The fresh angle — explicitly trace the chord dart's φ'₂-orbit (the `cutCapPhi2_dart`-style closed
form), sidestepping the genus-uniform `CutFaceLabel` label refutation — is realized and FULLY
FORMALIZED, clean-3, in the new file `ProofsInTheBook/ChordBoundaryOrbit.lean` (515 lines, 13
audited results, all `[propext, Classical.choice, Quot.sound]`, RC=0).

The genuinely-new derivable content (the heart of the angle) is **PROVED UNCONDITIONALLY**:

- **The explicit chord-dart orbit trace** (`chordDart_face_eq_b0/b1`): the fresh chord dart `inr j`'s
  side face is `dartFace (inl (β aⱼ))` — pinned to a kept-`inl` position by the closed form
  `φ̃ (inl (β aⱼ)) = inr j`, the face analogue of `WitnessFinal.cutCapPhi2_dart`. NOT a label.

- **The unconditional orbit trichotomy** (`tracePhi_reaches_of_keptPhi_sameCycle_b0/b1`): every kept
  dart whose `keptPhi`-orbit meets a chord predecessor is `tracePhi`-SameCycle to `β a₀` or `β a₁`.
  Proved by an explicit `keptPhi`-walk that tracks which of the two split threads each iterate sits
  on; the swap re-routes the thread exactly at the two predecessors. No genus hypothesis.

- **THE KEY FRESH-ANGLE THEOREM** (`spliceUntouched_of_face_ne_chordOrbits`, UNCONDITIONAL): a kept
  dart whose side face is NEITHER chord-dart face is `SpliceUntouched`. I.e. "every orbit other than
  the two chord-dart orbits is splice-untouched", derived directly from the explicit trace. **This
  removes the `SpliceUntouched` obligation from `BoundaryOrbitClass` entirely.**

With splice-untouchedness now free, `BoundaryOrbitClass` is **discharged** (`boundaryOrbitClass_of_absorb`)
from ONE named correct-anchor residue + the side-face↔M-face surjection conditions, and a full
`ContiguousInterval` assembled (`contiguousInterval_of_absorb`).

## The crucial finding the explicit trace REVEALS (the reason it does not go fully unconditional)

The genus-0 chord split is the **same-face** regime (`Side₁AnchorsShareFace`:
`keptPhi.SameCycle (ρ a₀) (ρ a₁)`). The explicit trace + the proven `+1` split branch
(`ChordFaceCount.freshMap_F_same_face`) make transparent that the swap **SPLITS** the shared kept
face into **TWO** distinct `tracePhi`-orbits — so `β a₀` and `β a₁` land in DIFFERENT orbits and the
two fresh darts thread into **two distinct** side faces (`chordOrbits_eq_iff_tracePhi`). Numerically
confirmed on a concrete witness (server `#eval`, K=Fin 6, ρβ a single 6-cycle): tracePhi splits into
`[1,4]∋βa₀` and `[0,2,3,5]∋βa₁`; `ρa₀~keptPhi ρa₁ = true`, `βa₀~tracePhi βa₁ = false`.

Geometrically the two touched orbits are the side **outer boundary face** (arc u..v + duplicated
chord) and the side image of the **chord triangle `face₁`**. Therefore `BoundaryOrbitClass.classify`
(one `outerFace`, all other faces splice-untouched + `M`-face `≠ face₁`) holds **iff the second
chord-incident orbit is absorbed by the boundary** — `OuterAbsorbsChordOrbits` (both `dartFace (inr 0)`
and `dartFace (inr 1)` equal `outerFace`). This is the irreducible discrete Jordan–Schoenflies
incidence the prior three rounds isolated, now exhibited as a CONCRETE two-touched-orbit condition
on the explicitly-traced chord darts — manifestly NOT a `φ'₂`-invariant COUNT label (so genuinely
sidestepping `CutFaceLabel`, which refutes only the uniform label for the cut-and-cap double surgery).

This is a sharpening, not a defeat: the fresh angle eliminates one of the two BoundaryOrbitClass
obligations (splice-untouchedness) UNCONDITIONALLY and pins the surviving obligation to a single
concrete orbit-coincidence fact about the two explicitly-traced chord darts.

## New file (owned, fresh; NOT wired into ProofsInTheBook.lean — one-writer rule)

`ProofsInTheBook/ChordBoundaryOrbit.lean` — imports `ChordFaceClass`. 13 audited results.
Branch `main`; no commits; no branch switch; no codex/OpenAI tooling; never ran lake/lean on the
Mac (kernel-panic rule observed — verified exclusively on uisai1).

## Verification (server uisai1, real olean chain)

- `lake env lean ProofsInTheBook/ChordBoundaryOrbit.lean` → **RC = 0**, zero errors, zero warnings,
  no `sorryAx`. All **13** `#print axioms` results **clean-3 `[propext, Classical.choice, Quot.sound]`**:
  `chordDart_face_eq_b0/b1`, `sideFace_inl_eq_iff_tracePhi`, `sideFace_eq_chordOrbit0/1_iff`,
  `tracePhi_reaches_of_keptPhi_sameCycle_b0/b1`, `spliceUntouched_of_face_ne_chordOrbits`,
  `boundaryOrbitClass_of_absorb`, `contiguousInterval_of_absorb`, `chordOrbits_eq_iff_tracePhi`,
  `innerRepsAvoidBoundary_of_innerFacesSide₁`, `absorb_discharge_eq`.
- `grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom '` → none in code (only the docstring disclaimer).
- `#print axioms ProofsInTheBook.ThomassenInduction.nearTriangulation_five_colorable`
  → **clean-3, UNCHANGED** (still parameterized by the `JordanOracle` hypothesis input
  `Ofun : M.Vertex → M.Vertex → α → α → JordanOracle α`; no upstream file edited — faithful advance,
  not a regression).

## §3.3 verdict: FAITHFUL, non-vacuous, genuine reduction

- **Genuine advance.** The explicit chord-dart trace and the KEY theorem (every non-chord-dart orbit
  is splice-untouched) are PROVED UNCONDITIONALLY — this is the concrete per-instance orbit trace the
  orchestration named, NOT a uniform label, and it discharges one of BoundaryOrbitClass's two
  obligations outright.
- **Not a re-wrapper.** `boundaryOrbitClass_of_absorb.classify` genuinely consumes
  `spliceUntouched_of_face_ne_chordOrbits` (it does NOT route through
  `ChordFaceClass.boundaryOrbitClass_of_innerFacesSide₁`). `absorb_discharge_eq` (`rfl`) certifies the
  assembled `ContiguousInterval`'s `inner_tri` IS the discharge from the named residue.
- **Not a vacuous/over-strong premise (the §3.3 trap I checked for).** `InnerRepsAvoidBoundary` is the
  honest surjection content: `innerRepsAvoidBoundary_of_innerFacesSide₁` shows it is satisfiable
  exactly when `ChordInnerTri.InnerFacesSide₁` is (it is `InnerFacesSide₁` minus the now-discharged
  splice-untouchedness field). `OuterAbsorbsChordOrbits` is exhibited as the precise two-orbit
  incidence via `chordOrbits_eq_iff_tracePhi` — I did NOT bury it as an unsatisfiable hypothesis nor
  fabricate a merge; the same-face split structure (`chordOrbits_eq_iff_tracePhi` + the proven `+1`
  branch) is stated transparently so the residue's content is auditable, not hidden by mechanical-green.

## The precise residue now (sharpened — ONE concrete two-orbit incidence, NOT the uniform label)

- **chord side:** `ChordBoundaryOrbit.OuterAbsorbsChordOrbits data hsep a₀ a₁ hne outerFace` — *the
  side boundary face `outerFace` equals BOTH explicitly-traced chord-dart faces `dartFace (inr 0)` and
  `dartFace (inr 1)`*. Concrete failing chain at the `CombMap` layer: under the genus-0 same-face
  regime the two chord-dart faces are DISTINCT (`chordOrbits_eq_iff_tracePhi` + `freshMap_F_same_face`
  `+1` split; #eval-confirmed two-orbit split `[1,4]/[0,2,3,5]`), so this coincidence is the genuine
  discrete-Schoenflies incidence "the second chord-incident orbit (the chord triangle `face₁` image)
  is absorbed into the boundary" — anchor-dependent, not certified by the abstract `CombMap` (the
  anchors `a₀,a₁` are universally quantified throughout the chord-side machinery; only the correct
  anchors put both chord-dart orbits on the boundary). Plus the surjection residue
  `InnerRepsAvoidBoundary` (the side-face↔M-face correspondence, the same datum minus splice-
  untouchedness, no face correspondence proven upstream — only the vertex `ι_surj`).
- **headline:** `JordanOracle` cannot be built without these; `nearTriangulation_five_colorable` stays
  CONDITIONAL on the `JordanOracle`-valued hypothesis `Ofun` (clean-3, unchanged).

## Threading note (the drop-in)

`ChordBoundaryOrbit.contiguousInterval_of_absorb` is the chord-side drop-in: once a downstream layer
supplies `OuterAbsorbsChordOrbits` + `InnerRepsAvoidBoundary` for the correct anchors + the side
boundary cycle, it assembles the full `ContiguousInterval` →
`ChordSideNT.chordSideNearTriangulation` (sphere already discharged unconditionally) →
`ChordReconClose.ChordSideClassification` (vertex `ι_surj` PROVED) → `ChordSideReconstruction` →
`ChordSplitNT.chord_case_recursive`. Everything between the named residue and the assembled
`SideInnerTriangulation` is PROVED here (splice-untouchedness via the explicit trace, faceLen=3 via
the inherited `ChordInnerTri`/`ChordFaceClass` face-SIZE chain).

## Chordless `CleanFaceClass` (the second branch named in the task)

Not formalized in this file (one-writer rule: `CleanFaceClass` lives in `ChordlessFinal.lean`, not
mine to edit). NOTE for the next round: the chordless branch is the SINGLE-merged-orbit regime (the
star/vertex deletion merges into ONE `v0`-incident outer face), so the analogous explicit-trace
discharge there does NOT hit the two-orbit obstruction the chord side has — `CleanFaceClass`'s
splice-/clean-untouchedness should be dischargeable by the same fresh-angle trace with the merged
outer face as the single touched orbit, leaving only the surjection residue. That is the promising
next file (`ChordlessBoundaryOrbit.lean`, importing `ChordlessFinal`).
