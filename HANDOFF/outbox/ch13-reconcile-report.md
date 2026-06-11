# Ch13 reconcile report -- ZinanFFCT67

Delivered:

- `ProofsInTheBook/ZinanFFCT67.lean`

## What closed

`ZinanFFCT67` removes `BackwardFoldCase` from the final public headline surface.  It does this by
bypassing `BTrichotomyEndpointSurfaceV2` and feeding the direct `BTrichotomyEndpointCases` surface into
FFCT64's dispatcher:

```lean
structure Ch13FinalSurface67 : Prop where
  hspanSeed : SupportStuckWBSVanishingSpanSeedSupply
  hnorepeat : NoRepeatSupply
  hcases : BTrichotomyEndpointCases
```

Main theorem:

```lean
theorem spherical_arm_mono_final_ch13 (res : Ch13FinalSurface67) ...
```

The unpacked corollary is also stated under the public no-repeat name:

```lean
def NoRepeatSupply : Prop := OpenedWBSNoNonadjacentRepeatSupply

theorem spherical_arm_mono_final_ch13_of_supplies
    (hspanSeed : SupportStuckWBSVanishingSpanSeedSupply)
    (hnorepeat : NoRepeatSupply)
    (hcases : BTrichotomyEndpointCases) ...
```

## What still survives

1. `SupportStuckWBSVanishingSpanSeedSupply`.

   The landed raw source is `supportStuckWBS_vanishingSupport`, and FFCT52's
   `orientationNormalized` splits it into a normalized branch on `openedWBS` or a normalized branch on
   `revArm (openedWBS)`.  The existing FFCT65 field accepts only the `openedWBS` branch.  A real
   discharge needs either a mirror-aware b-trichotomy dispatcher or a proof that the reversed branch
   cannot occur.

2. `BTrichotomyEndpointCases`.

   The old `BPosAPosFFCTPlusV2EndpointConsumer` interface does not carry the dimension IH or the
   diagonal inequality needed by `FoldedFlatCutTransportPlusNR`.  In particular the `(0,n-1)` boundary
   close in FFCT66 still used an incoming diagonal bound.  That datum is not present in the FFCT64
   endpoint-case signature.  `bpos_aneg` also remains a named endpoint case; I found no landed
   plane-accumulation kill with the required endpoint signature.

3. `NoRepeatSupply`.

   This remains the accepted opened-WBS no-repeat input.  The same-piece repeat argument from a strict
   original arm is plausible, but the cross-piece collision at the WBS supremum is not excluded by the
   existing library surface.

## Verification

Remote command:

```bash
scp ProofsInTheBook/ZinanFFCT67.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT67.lean
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake build ProofsInTheBook.ZinanFFCT66 && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT67.lean'
```

Result: `ProofsInTheBook.ZinanFFCT66` built, then `ZinanFFCT67.lean` checked successfully.  The three
new printed theorem dependencies are exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No commit was made.
