# Ch13 unconditional report (FFCT89)

Created `ProofsInTheBook/ZinanFFCT89.lean`.

## What landed

1. `weakConvex_boundedJoints_no_consecutive_det3_zero`
   - Direct local bounded-joint flat-triple contradiction:
     `WeakConvexSphArm P -> PositiveJoints P -> (jointAngle P i < pi) ->
      det3(P r)(P (r+1))(P (r+2)) = 0 -> False`.
   - This is the final contradiction brick in the bounded route: FFCT21 gives angle `0` or `pi`;
     positivity kills `0`, and the new upper bound kills `pi`.

2. `BoundedWeakPositiveSimplicity`
   - The exact remaining residue, as a `Prop`, not an unsafe theorem:
     `WeakConvexSphArm P -> PositiveJoints P ->
      (forall i, jointAngle P i < pi) -> NoNonadjacentRepeat P`.

3. `openedWBS_jointLe_at_sup`
   - Reconstructs the landed WBS `JointLe (openedWBS A B k) B` at the support-stuck supremum.

4. `openedWBS_jointAngle_lt_pi`
   - Proves the opened WBS arm has all interior joints `< pi`, by chaining
     `openedWBS_jointLe_at_sup` with `strict_jointAngle_lt_pi hB`.

5. `openedWBS_noNonadjacentRepeat_of_boundedWeakPositiveSimplicity`
   - Uses `BoundedWeakPositiveSimplicity` plus the landed opened-WBS weak convexity and positivity
     reconstruction to produce `NoNonadjacentRepeat (openedWBS A B k)`.

6. `crossPieceCollisionEndpointAtSup_of_boundedWeakPositiveSimplicity`
   - The collision branch closes immediately from the bounded no-repeat residue.

7. `spherical_arm_mono_ch13_of_boundedWeakPositiveSimplicity`
   - Composes through `spherical_arm_mono_final_ch13_v11`.

## Why the unconditional theorem did not land

The missing step is not the `pi` branch anymore; that branch is closed by
`weakConvex_boundedJoints_no_consecutive_det3_zero` and `openedWBS_jointAngle_lt_pi`.

The remaining missing theorem is the global face-run propagation:

```lean
WeakConvexSphArm P ->
PositiveJoints P ->
(forall i, jointAngle P i < Real.pi) ->
NoNonadjacentRepeat P
```

From a nonadjacent repeat one can get initial zero supports by determinant algebra, but the current
landed library does not expose a theorem that propagates that arbitrary zero support along the
weak face-run until it yields a consecutive vanishing determinant.  FFCT83/84/85 land first-step
and endpoint-specific wrap/tail residues, but they do not provide the reusable global propagation
needed for arbitrary `r + 2 <= s`.

## Verification

Commands run successfully:

```bash
lake build ProofsInTheBook.ZinanFFCT88
lake env lean ProofsInTheBook/ZinanFFCT89.lean
```

`lake env lean ProofsInTheBook/ZinanFFCT89.lean` was run three times.  The `#print axioms` guards
reported only `propext`, `Classical.choice`, and `Quot.sound`.
