# Ch13 simplicity report (FFCT88)

Created `ProofsInTheBook/ZinanFFCT88.lean`.

## What landed

1. `weakConvex_positiveJoints_no_gap_two_repeat`
   - Proves the digon base case from the brief:
     `WeakConvexSphArm P -> PositiveJoints P -> P r != P (r+2)`.
   - The repeated endpoints make the joint at `r+1` equal to `0`, contradicting `PositiveJoints`.

2. `weakConvex_positiveJoints_noNonadjacentRepeat_gap_two`
   - Same base case in the nat-indexed `NoNonadjacentRepeat` calling convention.

3. `WeakPositiveSimplicity`
   - The exact remaining residue:
     `WeakConvexSphArm P -> PositiveJoints P -> NoNonadjacentRepeat P`.
   - This is a `def`, not an assumed theorem.

4. `crossPieceCollisionEndpointAtSup_of_weakPositiveSimplicity`
   - Shows the WBS cross-piece collision endpoint residue is vacuous once the remaining
     weak-positive simplicity theorem is supplied.

5. `spherical_arm_mono_ch13_of_weakPositiveSimplicity`
   - Composes the residue through `spherical_arm_mono_final_ch13_v11`.

## Why the unconditional theorem did not land

The requested theorem

```lean
theorem weakConvex_positiveJoints_noNonadjacentRepeat
    {n : ℕ} {P : Fin (n+1) -> S2}
    (hweak : WeakConvexSphArm P) (hpos : PositiveJoints P) :
    NoNonadjacentRepeat P
```

does not match the currently landed flat-joint kill interface.  In the repo,
`PositiveJoints` is only

```lean
def PositiveJoints {n : ℕ} (A : Fin (n + 1) -> S2) : Prop :=
  ∀ k : Fin (n - 1), 0 < jointAngle A k
```

The landed contradiction lemmas for a vanishing consecutive determinant produce
`jointAngle = 0 ∨ jointAngle = Real.pi`.  They kill the `0` branch with
`PositiveJoints`, but kill the `pi` branch using the separate non-flat bound
`jointAngle < Real.pi`, normally supplied by `jointAngle_lt_pi hB hangle` or by
strict convexity.

That `< pi` hypothesis is not present in the requested general theorem, and the
existing FFCT21/22/44-style machinery consistently expects it for flat-joint
refutations.

## Verification

`lake env lean ProofsInTheBook/ZinanFFCT88.lean` succeeds.  The `#print axioms`
guards report only the standard `propext`, `Classical.choice`, and `Quot.sound`.
