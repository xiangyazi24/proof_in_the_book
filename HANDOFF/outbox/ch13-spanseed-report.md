# Ch13 spanseed report -- ZinanFFCT69

Delivered:

- `ProofsInTheBook/ZinanFFCT69.lean`

## What landed

1. Mirror-aware normalized seed surface.

   New names:

   ```lean
   SupportStuckWBSMirrorVanishingSpanSeedSupply
   SupportStuckWBSNonWrapVanishingSupportSupply
   mirrorSeed_of_forwardSeed
   mirrorArm_sOrient_zero_of_revArm_zero
   mirrorSeed_of_nonWrapVanishingSupport
   ```

   `SupportStuckWBSMirrorVanishingSpanSeedSupply` is the seed-on-mirror disjunct requested in the
   brief: the normalized vanishing support can live either on `openedWBS A B k` or on
   `mirrorArm (openedWBS A B k)`.

2. The reversed branch is wired through `mirrorArm`.

   `mirrorSeed_of_nonWrapVanishingSupport` runs FFCT52's `orientationNormalized` on a raw non-wrap
   support witness.  The direct branch is kept on `openedWBS`; the reversed `revArm` branch is converted
   to `mirrorArm` by `mirrorArm_sOrient_zero_of_revArm_zero`, using FFCT61's reflection sign flip.

3. Endpoint dispatch no longer consumes the old forward-only seed.

   New names:

   ```lean
   endpoint_of_normalized_vanishing_support
   supportStuckWBS_endpoint_dispatch_mirrorSeed
   Ch13FinalSurface69
   final69_of_final68
   spherical_arm_mono_final_ch13_v3
   spherical_arm_mono_final_ch13_v3_of_supplies
   ```

   The dispatch extracts the real span from the normalized zero support exactly as FFCT65 did, then calls
   FFCT64's `endpoint_of_btrichotomy_cases`.  In the mirror branch it supplies the transported
   certificates:

   - `weakConvex_mirrorArm`
   - `positiveJoints_mirrorArm`
   - `strictConvex_mirrorArm`
   - `sameSides_mirrorArm`
   - `jointLe_mirrorArm`
   - `noNonadjacentRepeat_mirrorArm`
   - `endpt_mirrorArm`

## Exact remaining surface

The new headline is:

```lean
structure Ch13FinalSurface69 : Prop where
  hmirrorSeed : SupportStuckWBSMirrorVanishingSpanSeedSupply
  hcross : CrossPieceNoCollisionAtSup
  hcases : BTrichotomyEndpointCases
```

So FFCT69 removes the old forward-only `SupportStuckWBSVanishingSpanSeedSupply` from the dispatch path,
but the final theorem is not yet modulo only `CrossPieceNoCollisionAtSup`.

## What still resists

1. Raw `SupportStuckWBS` still does not guarantee a non-wrap support witness.

   FFCT52's `orientationNormalized` requires `a.val + 1 < n + 1`.  FFCT45 explicitly documents and proves
   that the base-stuck route produces the wrap-edge witness `(last, K)`.  FFCT69 therefore exposes
   `SupportStuckWBSNonWrapVanishingSupportSupply` as the honest bridge into the mirror-aware seed; it does
   not pretend the wrap-base case is covered by `orientationNormalized`.

2. `BTrichotomyEndpointCases` is still a public input.

   The exact fields remain FFCT64's:

   ```lean
   bneg_tail
   bpos_apos
   bpos_aneg
   ```

   `bneg_tail` is arithmetically empty in FFCT65.  `bpos_apos` still needs the missing IH and diagonal
   inequality identified in FFCT68's repaired consumer.  `bpos_aneg` still has no landed global kill in
   the current library.

3. The requested "modulo only `CrossPieceNoCollisionAtSup`" headline therefore does not land honestly
   from the current files.

## Verification

Remote commands:

```bash
scp ProofsInTheBook/ZinanFFCT69.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT69.lean
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake build ProofsInTheBook.ZinanFFCT68 && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT69.lean'
```

Result:

- `ProofsInTheBook.ZinanFFCT68` built successfully on `uisai2`.
- `ZinanFFCT69.lean` checked successfully on `uisai2`.
- The four printed declarations are clean-3:

```text
[propext, Classical.choice, Quot.sound]
```

No commit was made.

