# Chapter 13 step-level assembly report

## Deliverable

Added `ProofsInTheBook/ZinanFFCT72.lean`.

The new file rewrites the final assembly at the `SZOpeningStepPlus` level:

```lean
structure Ch13FinalSurface72 : Prop where
  hwpc : WeakPositiveCutReady
  hffct : FoldedFlatCutTransportPlus
  hwrapSeed : SupportStuckWBSWrapSeedResidue
  hcross : CrossPieceNoCollisionAtSup
  hbpos_aneg_tail : BPosANegTailCornerResidue
```

The old `hbpos_apos : BPosAPosEndpointCase` surface field is gone.

## What changed

`supportStuckWBS_endpoint_dispatch_at_level` now receives the live
`ihdim : ∀ m, m < n → MainPlus m`.

The normalized vanishing-support path now closes by:

1. extracting a span from the zero support orientation,
2. dispatching on the coefficient signs at the same induction level,
3. sending the `b > 0, a > 0` branch through
   `bpos_apos_endpoint_of_weakCut_at_level`,
4. constructing `CutReadyPlus` via `WeakPositiveCutReady`, then using
   `cut_step_from_stuckAtK_plus` with the live `ihdim`.

This is the structural removal requested in the brief: the positive-positive
endpoint case is no longer supplied as a headline field.

## Surface note

The brief's target surface `{hwrapSeed, hcross, hbpos_aneg_tail}` does not
honestly type for the full `MainPlus` assembly in the current library.  The
weak-entry branch of `SZOpeningStepPlus` still has only
`WeakConvexSphArm A + PositiveJoints A` and a vanishing support witness, so it
needs:

- `WeakPositiveCutReady` to build `CutReadyPlus`,
- `FoldedFlatCutTransportPlus` for the endpoint transport consumed by
  `cut_step_from_stuckAtK_plus`.

The v6 surface therefore removes `hbpos_apos` while retaining those two
previously isolated CUT inputs.

## Secondary endpoint

The `hbpos_aneg_tail` endpoint remains named.  I did not find a shape-aligned
bridge from the WBS-pinned mirror tail machinery to the bare
`BPosANegTailCornerResidue` statement without adding a new general residue.

## Verification

Remote check used:

```bash
scp ProofsInTheBook/ZinanFFCT72.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT72.lean
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake build ProofsInTheBook.ZinanFFCT71 && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT72.lean'
```

Result: `ZinanFFCT71` built successfully, and `ZinanFFCT72.lean` checked with
0 errors.  The printed dependency sets for the new v6 declarations are clean-3.
