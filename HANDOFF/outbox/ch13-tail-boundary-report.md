# Ch13 Tail-Boundary Audit — Report (ZinanFFCT60)

**File:** `ProofsInTheBook/ZinanFFCT60.lean` (new).  Verified on `uisai2` after building
`ProofsInTheBook.ZinanFFCT59`:

```text
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake build ProofsInTheBook.ZinanFFCT59 && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT60.lean'
```

`ZinanFFCT60.lean` checks with 0 errors.  The printed axioms for the new declarations are clean-3:
`[propext, Classical.choice, Quot.sound]`.  No `sorry`, `admit`, `native_decide`, or new axioms are
introduced.

## Verdict

The tail-boundary residue is **not unconditionally empty** from the currently committed substrate.
The attempted reversal route needs `WeakConvexSphArm (revArm P)` and
`StrictConvexSphArm (revArm B)`.  Those are not available: reversing the vertex order flips the
`sOrient` support sign, and FFCT54 only transports side lengths, joint angles, `PositiveJoints`,
`JointLe`, endpoint distance, and no-repeat.

What FFCT60 proves is the sharp conditional result:

* Under explicit `TailBoundaryReversalConvexity`, a tail mid-fold forces `j = 0 ∨ j = 1`.
* Therefore every tail-boundary residue with `2 ≤ j` is impossible under that same input.

Lean names:

```text
rev_tail_midFold_forces_endpoint_j
nonAxisTailBoundaryResidue_forces_endpoint_j_under_reversal
nonAxisTailBoundaryResidue_false_of_two_le_j_under_reversal
```

## Remaining Surface

The surviving honest surface is:

```text
NonAxisTailBoundaryResidue
  + TailBoundaryReversalConvexity (reversed weak/strict convexity)
  ⇒ j = 0 ∨ j = 1
```

The endpoint cases `j = 0` and `j = 1` are the boundary-transport cases anticipated in the brief, not
local contradictions.  They still need the appropriate endpoint transport hypotheses to conclude an
endpoint inequality.  Separately, FFCT59's earlier warning remains: raw `SupportStuckWBS` still needs
the sign-supply route to the `b < 0` `NonAxisMixedBindingResidue`.

## Consequence Chain

`SupportStuckWBSImpossible` is still not proved unconditionally.  The sharpest honest status is:

```text
non-axis mixed support-stuck
  = successor-edge cases killed by FFCT59
  + tail cases with j ≥ 2 killed by FFCT60, conditional on reversed convexity
  + endpoint tail cases j ∈ {0,1} requiring boundary transport
  + raw sign-supply still required before this applies to arbitrary SupportStuckWBS.
```

Accordingly, the final `spherical_arm_mono` headline remains the FFCT59 reach-only conditional chain:
it becomes available once `SupportStuckWBSImpossible` is supplied, but FFCT60 does not by itself supply
that global elimination.
