# Ch13 last-three report -- ZinanFFCT68

Delivered:

- `ProofsInTheBook/ZinanFFCT68.lean` (247 lines)

## What landed

1. Cross-piece no-collision replaces the opened-WBS no-repeat surface.

   New names:

   ```lean
   strictConvex_noNonadjacentRepeat
   CrossPieceNoCollisionAtSup
   openedWBS_noNonadjacentRepeat_of_crossPiece
   openedWBSNoNonadjacentRepeatSupply_of_crossPiece
   ```

   Same-piece repeats are discharged from the original strict arm:

   - fixed/fixed repeats reduce directly to `StrictConvexSphArm.closed_convex.strict_nonincident`;
   - rotated/rotated repeats reduce by `rotS2_injective`;
   - fixed/rotated repeats are exactly the named `CrossPieceNoCollisionAtSup` residue.

2. The `b > 0, a > 0` endpoint interface is replumbed with its real missing data.

   New names:

   ```lean
   BPosAPosFFCTPlusV3EndpointConsumer
   bpos_apos_endpointConsumer_v3_holds
   BPosAPosFFCTPlusForwardEndpointConsumer
   bpos_apos_endpointConsumer_forward_holds
   ```

   The forward version uses `FoldedFlatCutTransportPlusForward`, so it does not reintroduce
   `BackwardFoldCase`.  Both adapters require exactly the data identified in the handoff:

   - `ihdim : ∀ m < n, MainPlus m`
   - the diagonal inequality
     `sDist (P i) (P j) <= sDist (B i) (B j)`

3. Final wrapper with no-repeat replaced.

   New names:

   ```lean
   Ch13FinalSurface68
   final67_of_final68
   spherical_arm_mono_final_ch13_v2
   spherical_arm_mono_final_ch13_v2_of_supplies
   ```

   The v2 headline removes `OpenedWBSNoNonadjacentRepeatSupply` from the public surface and replaces it
   with `CrossPieceNoCollisionAtSup`.

## What still remains

The requested "mod at most CrossPieceNoCollisionAtSup" headline did not land honestly from the current
library.

Remaining inputs in `Ch13FinalSurface68`:

```lean
hspanSeed : SupportStuckWBSVanishingSpanSeedSupply
hcross : CrossPieceNoCollisionAtSup
hcases : BTrichotomyEndpointCases
```

Reasons:

- The old FFCT64 span surface is forward-only.  The `orientationNormalized` reversed branch produces a
  normalized binding on `revArm`/`mirrorArm`; transporting the resulting span back gives a predecessor
  relation on the original arm, not the forward `P i = a * P (i+1) + b * P j` datum that
  `SupportStuckWBSSpanSupply` expects.  Closing this needs a mirror-aware endpoint dispatcher, not just a
  proof of the old forward span-supply field.
- The existing strict-only recursion in FFCT62 does not pass `ihdim` into support-stuck endpoint
  dispatch.  FFCT68 proves the endpoint adapter that consumes `ihdim + hdiag`, but does not rewrite the
  recursion spine in earlier files.
- `BPosANegEndpointConsumer` is still not discharged by a landed theorem.  I found no existing global
  kill for the `b > 0, a < 0` endpoint case.

## Verification

Remote command:

```bash
scp ProofsInTheBook/ZinanFFCT68.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT68.lean
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake build ProofsInTheBook.ZinanFFCT67 && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT68.lean'
```

Result:

- `ProofsInTheBook.ZinanFFCT67` built successfully on `uisai2`.
- `ZinanFFCT68.lean` checked successfully.
- The five printed declarations are clean-3:

```text
[propext, Classical.choice, Quot.sound]
```

Text grep on `ProofsInTheBook/ZinanFFCT68.lean` for forbidden proof placeholders was clean.

No commit was made.
