# Chapter 13 Static WPC Report

## Deliverables

- Added `ProofsInTheBook/ZinanFFCT74.lean`.
- Did not modify the import aggregator.
- Did not commit.

## Result

`ZinanFFCT74` implements the Chapter 13 static weak-positive-cut surface by threading non-repeat information through the opening recursion.

The old unqualified `WeakPositiveCutReady -> CutReadyPlus` route is not recovered, because weak interval arms may repeat. Instead, the new surface uses an NR-threaded motive:

- `MainPlusNR`
- `SZOpeningStepPlusNR`
- `WeakPositiveCutReadyNR`

This lets the static b-trichotomy discharge the weak positive cut entry without using axioms or skipping the repeat obstruction.

## Main Theorem

The final theorem added is:

```lean
spherical_arm_mono_final_ch13_v8
```

Its remaining Chapter 13 surface is:

```lean
structure Ch13FinalSurface74 where
  hweakWrapSeed : WeakVanishingWrapSeedResidue
  hwrapSeed : SupportStuckWBSWrapSeedResidue
  hcross : CrossPieceNoCollisionAtSup
  hbpos_aneg_tail : BPosANegTailCornerResidue
```

Interpretation:

- Raw weak vanishing support is closed by `WeakPositiveCutReadyNR`, modulo the isolated wrap seed residue and the tail corner residue.
- Non-wrap weak supports are normalized using `orientationNormalized`; the reversed branch is routed to `mirrorArm`.
- Wrap weak supports are isolated as `WeakVanishingWrapSeedResidue`.
- The WBS stuck branch still uses the existing `SupportStuckWBSWrapSeedResidue` and `CrossPieceNoCollisionAtSup` residues.

## Verification

Commands run:

```bash
ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && lake build ProofsInTheBook.ZinanFFCT73 && lake env lean ProofsInTheBook/ZinanFFCT74.lean'
ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && lake build ProofsInTheBook.ZinanFFCT74'
rg -n "\bsorry\b|\badmit\b|\baxiom\b|native_decide" ProofsInTheBook/ZinanFFCT74.lean
```

Results:

- `ProofsInTheBook.ZinanFFCT73` builds on `uisai2`.
- `lake env lean ProofsInTheBook/ZinanFFCT74.lean` passes on `uisai2`.
- `lake build ProofsInTheBook.ZinanFFCT74` passes on `uisai2`.
- The `#print axioms` guards for the new surface report only Lean/classical foundations: `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
- Forbidden-token grep found no `sorry`, `admit`, `axiom`, or `native_decide` in `ZinanFFCT74`.

Note: `uisai1` timed out during the remote route, so verification used the handoff-specified direct `uisai2` path.
