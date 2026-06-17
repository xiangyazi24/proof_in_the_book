# Ch13 hcross report -- ZinanFFCT86

Delivered:

- `ProofsInTheBook/ZinanFFCT86.lean` (395 lines)

## What landed

`ZinanFFCT86` removes `CrossPieceNoCollisionAtSup` from the checked headline path by localizing the
WBS support-stuck dispatch.

New names:

```lean
CrossPieceCollisionEndpointAtSup
crossPieceCollisionEndpointAtSup_of_noCollision
openedWBS_noNonadjacentRepeat_of_localNoCross
supportStuckWBS_boundaryProgress_of_noRepeat_firstStep
supportStuckWBS_endpoint_dispatch_at_level_nr_v11
open_step_wbs_nr_v11
szOpeningStepPlusNR_v11
mainPlusNR_at_level_v11
mainPlusNR_all_v11
spherical_arm_mono_final_ch13_v11
spherical_arm_mono_final_ch13_v11_of_hcross
```

The new final surface is strictly weaker than the old hcross input:

```lean
def CrossPieceCollisionEndpointAtSup : Prop := ...

theorem spherical_arm_mono_final_ch13_v11
    (hcollision : CrossPieceCollisionEndpointAtSup) :
    SphericalArmMonotone
```

`CrossPieceNoCollisionAtSup` implies the new residue vacuously:

```lean
theorem crossPieceCollisionEndpointAtSup_of_noCollision
    (hcross : CrossPieceNoCollisionAtSup) :
    CrossPieceCollisionEndpointAtSup
```

## Route

The WBS endpoint dispatch now splits on the local fixed/tail collision predicate for the current
support-stuck branch.

- No local collision: `openedWBS_noNonadjacentRepeat_of_localNoCross` reconstructs the opened-arm
  `NoNonadjacentRepeat`, and the FFCT85 first-step wrap machinery supplies the same v9
  mirror-aware boundary progress as before.
- Collision exists: the branch is routed to the exact endpoint payload
  `CrossPieceCollisionEndpointAtSup`.

This avoids requiring global `CrossPieceNoCollisionAtSup` in the recursion.  The actual collision-to-
endpoint geometry remains the remaining sharp residue.

## Verification

Commands run:

```bash
export PATH=$HOME/.elan/bin:$PATH && lake build ProofsInTheBook.ZinanFFCT85
export PATH=$HOME/.elan/bin:$PATH && lake env lean ProofsInTheBook/ZinanFFCT86.lean
rg -n "\bsorry\b|\badmit\b|\baxiom\b|native_decide" ProofsInTheBook/ZinanFFCT86.lean
```

Results:

- `ProofsInTheBook.ZinanFFCT85` built successfully.
- `ZinanFFCT86.lean` checked successfully.
- The six printed declarations are clean-3:

```text
[propext, Classical.choice, Quot.sound]
```

- Placeholder/unsafe grep was clean.
- No git commit was made.
