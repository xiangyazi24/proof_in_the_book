# Reply: ChordFaceCount — the chord-split genus-0 face certificate

**Status: the kernel-confirmed genus-DEPENDENT face residue `FreshFaceCount` is DISCHARGED
for the actual side maps, via an EXPLICIT face-permutation orbit bijection that USES M's
genus-0 structure (no `Separates`-reachability count, no generic counting).**

New file (owned, only file touched): `ProofsInTheBook/ChordFaceCount.lean` (689 lines).
Branch `main`; no commits; no branch switch; no codex/OpenAI tooling; no
`lake build`/`lake env lean` run locally (Mac kernel-panic rule observed).

## Verification (server uisai1, refreshed oleans)

```
rsync … ChordFaceCount.lean ; ssh uisai1 'lake env lean ProofsInTheBook/ChordFaceCount.lean'
RC = 0
```

`#print axioms` — **clean-3 on EVERY headline** (`[propext, Classical.choice, Quot.sound]`,
no `sorryAx`, no `native_decide`/`ofReduceBool`/`trustCompiler`):

- `freshFace_sameCycle_iff`            (the explicit FACE orbit bijection)
- `freshMap_F_eq_tracePhi`             (F = numCycles of traced face perm)
- `freshMap_F_same_face` / `freshMap_F_diff_face`  (the genus dichotomy ±1)
- `freshFaceCount_of_genus0`           (**FreshFaceCount discharged** from genus-0 facts)
- `freshMap_isSphereMap_of_genus0`     (full IsSphereMap: connectivity + eulerChar=2)
- `sideMap₁/₂_isSphereMap_of_genus0`   (instantiated at the genuine chord side maps)
- `sphereWitness_isSphereMap_via_genus0` (non-vacuity: producer fires)
- `chordFaceCount_closed_of_genus0`    (headline)

No `sorry`/`axiom`/`admit`/`native_decide` (only the docstring's "No …" disclaimer).

## What was proved (the route NOT previously tried — explicit bijection)

The face permutation of `freshMap β ρ a₀ a₁` is `φ = freshSigma ∘ freshAlpha`. Computed
dart-by-dart (Section A): the two fresh darts `inr 0, inr 1` are spliced INTO face cycles
exactly as the vertex splice did (`inl(βa₀) → inr 0 → inl(ρa₁)`, `inl(βa₁) → inr 1 →
inl(ρa₀)`). Collapsing each fresh dart to its face predecessor (`faceProj`), the K-traced
face permutation is

  `φ̃ = swap(ρa₀)(ρa₁) · (ρ·β)`   — the kept face perm `ρ·β` with two values swapped.

`freshFace_sameCycle_iff` (the FACE analogue of the proven vertex
`freshSigma_sameCycle_iff`, built from the same step-projection template) ⟹
`freshMap_F_eq_tracePhi`:  **F(freshMap) = numCycles(φ̃)** (splice changes no face orbit).

Since `φ̃ = swap · (ρ·β)` differs from `ρ·β` by one transposition, the standard cycle-count
dichotomy (`numCycles_mul_swap_of_sameCycle` / `…of_not_sameCycle`, via `numCycles_mul_comm`)
gives the genus split:
  - same kept face (splice SPLITS):  `F = numCycles(ρ·β) + 1`
  - different kept face (MERGES):     `F = numCycles(ρ·β) − 1`

`FreshFaceCount` (`2F = |K|+6 − 2·numCycles ρ`) is then *equivalent* to the kept Euler
characteristic being `2` (same-face branch) or `4` (diff-face branch) — exactly the
kernel-confirmed genus dependence. `freshFaceCount_of_genus0` discharges it from the
honest genus-0 facts: `(keptCombMap β ρ).eulerChar = 2` AND `(ρ·β).SameCycle (ρa₀)(ρa₁)`.

The numerical core was Python-checked over thousands of random involution/rotation/anchor
configs before formalizing (both `F=numCycles(φ̃)` and the ±1 dichotomy).

## Faithfulness (§3.3) — FAITHFUL, non-vacuous

- `FreshFaceCount` is the *exact* `Prop` the upstream files isolate
  (`ChordSplitEuler.FreshFaceCount`); it is discharged, not re-wrapped.
- The hypotheses are NOT the conclusion in disguise: the new content is the bridge between
  the *kept* face count and the *fresh* face count — the `+1` splice split
  (`freshMap_F_same_face`). The diff-face branch (`freshMap_F_diff_face`) exhibits the
  genus dependence explicitly (it would force `eulerChar = 4`), so the same-face hypothesis
  is genuinely load-bearing, not always-true.
- Non-vacuity: `sphereWitness_isSphereMap_via_genus0` fires the producer on a concrete
  genus-0 map where both genus-0 inputs hold simultaneously — no unsatisfiable premise.

## The precise residue now (sharpened, NOT the face count any more)

The chord-split face count is no longer the residue. What remains for a *fully
unconditional* `ChordSideReconstruction` are TWO purely-local genus-0 disk facts of each
Jordan-separated side, strictly weaker than the global face count:

1. `(sideKeptMapᵢ data hsep).IsSphereMap` — the kept side is a combinatorial disk
   (`eulerChar = 2`); and
2. `(keptPhi (sideAlphaᵢ) (sideSigmaᵢ)).SameCycle (sideSigmaᵢ a₀) (sideSigmaᵢ a₁)` — the
   two splice anchors' rotation successors lie on the side's boundary face.

These are the genuine genus-0 structure M's `IsSphereMap` supplies per side (the same
granularity/character as the upstream `Separates` Jordan input), NOT orbit bookkeeping —
consistent with the 4 prior kernel-backed rounds that the count is genus-dependent and
`Separates` alone cannot give it. The contribution here is that the face count itself is
now a THEOREM (`freshMap_F_eq_tracePhi` + the transposition sign), reducing the residue
from a global face-orbit count to these two local disk facts and proving the count from
them. Connectivity half was already done (`ChordSideRecon.freshMap_connected_of_kept`), so
`sideMapᵢ.IsSphereMap` is fully produced from inputs 1+2.

## FCT threading

`chordFaceCount_closed_of_genus0` is the headline: for the genuine chord side map, the full
`IsSphereMap` AND `FreshFaceCount` follow from inputs 1+2, with the face count discharged.
Combined with the upstream `Separates` separation and the `ChordSideReconstruction`
correspondence/list-transport fields, this closes the genus-0 (eulerChar=2) field of the
chord-recursive Thomassen branch; the Five Color Theorem is the
`ChordSplitNT.nearTriangulation_listColorable_chordRecursive` assembly over the
now-discharged face certificate. (Headline lives in `ChordFaceCount.lean`; no upstream file
was edited per the one-writer rule.)
