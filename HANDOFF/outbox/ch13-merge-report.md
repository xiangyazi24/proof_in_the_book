# Ch13 merge report -- ZinanFFCT73

Delivered:

- `ProofsInTheBook/ZinanFFCT73.lean`
- this report

No commit was made.

## What landed

`ZinanFFCT73` creates the requested public three-field surface:

```lean
structure Ch13FinalSurface73 : Prop where
  hwrapSeed : SupportStuckWBSWrapSeedResidue
  hcross : CrossPieceNoCollisionAtSup
  hbpos_aneg_tail : BPosANegTailCornerResidue
```

The file proves the WBS support-stuck branch at a live induction level without
`WeakPositiveCutReady` and without a public `FoldedFlatCutTransportPlus` field:

```lean
supportStuckWBS_endpoint_dispatch_at_level_v7
open_step_wbs_v7
```

The positive-positive branch is no longer routed through `CutReadyPlus`.  It now:

1. converts `P i = a * P (i+1) + b * P j`, `a > 0`, `b > 0` to NNReal betweenness;
2. kills the adjacent case `j = i + 2` by `foldedFlat_adjacent_contradiction`;
3. in the non-adjacent case, derives the A-side interval wrap data by row expansion;
4. derives the B-side strict interval wrap data from `cyclicTriplePos_unconditional`;
5. uses `ear_chord_le_of_MainPlus` at the live lower dimension to get the diagonal inequality;
6. closes through `bpos_apos_endpointConsumer_forward_holds foldedFlatCutTransportPlusForward_v3`.

New main names:

```lean
cutReadyPlus_level_two_false
det3_rowExpand_edge
intervalWrapData_of_positive_span
intervalWrapDataStrict_of_cyclicTriple
diag_le_of_positive_span_at_level
bpos_apos_endpoint_at_level_v7
endpoint_of_span_at_level_v7
endpoint_of_normalized_vanishing_support_at_level_v7
supportStuckWBS_endpoint_dispatch_at_level_v7
open_step_wbs_v7
```

## Refutation check on `WeakPositiveCutReady`

No full formal refutation of `WeakPositiveCutReady` was found.

The strongest landed obstruction is:

```lean
theorem cutReadyPlus_level_two_false {A B : Fin (2 + 1) -> S2} :
    not (CutReadyPlus A B)
```

At level `2`, `CutReadyPlus` cannot be inhabited because its ear certificate would require
`WeakConvexSphArm` on a one-edge interval.  This would refute `WeakPositiveCutReady` if one also had a
level-2 instance satisfying its weak-positive, strict-comparison, same-side, joint-bound, and vanishing
support premises.  I did not find such a witness in the current library.  The check therefore downgrades
`hwpc` from "refuted" to "still unproved and structurally suspect", consistent with
`ch13-cut-replacement.md` section 8.

## Exact final target status

The requested surface-only theorem

```lean
spherical_arm_mono_final_ch13_v7
```

with only `Ch13FinalSurface73` is not honestly derivable from the current library.

Reason: the new positive-positive WBS branch still needs a lower-dimensional
`MainPlus (j - (i + 1))` to compare the ear chord and produce the diagonal inequality.  The v7 local
step receives this as the live `ihdim` argument.  FFCT62's public strict-only endpoint-dispatch recursion,
however, has type `SupportStuckWBSEndpointDispatch` and does not pass `ihdim` into the support-stuck
consumer.  The only existing recursion that does pass `ihdim` is `SZOpeningStepPlus`, but rebuilding that
full step reopens the arbitrary weak-entry `strict_or_vanishing` branch and again requires
`WeakPositiveCutReady`.

So the merge succeeds at the strict WBS step level:

```lean
Ch13FinalSurface73 -> live-ihdim WBS support-stuck endpoint dispatch
```

but the surface-only final headline remains blocked by the mismatch:

```text
strict-only final recursion: no ihdim in support dispatch
full step recursion: ihdim available, but arbitrary weak-entry branch needs hwpc
```

Adding a final theorem by assuming lower `MainPlus`, reintroducing `WeakPositiveCutReady`, or hiding a
global `BPosAPosEndpointCase` would be a co-extensive or stronger surface, not the requested exact
three-field surface.

## Verification

Remote check used:

```bash
scp ProofsInTheBook/ZinanFFCT73.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT73.lean
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake build ProofsInTheBook.ZinanFFCT72 && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT73.lean'
```

Result: `ZinanFFCT72` built successfully on `uisai2`, and `ZinanFFCT73.lean` checked with 0 errors.
The printed dependency sets for the new FFCT73 declarations are clean-3:

```text
[propext, Classical.choice, Quot.sound]
```

Local forbidden-placeholder scan on `ProofsInTheBook/ZinanFFCT73.lean`: no matches.
