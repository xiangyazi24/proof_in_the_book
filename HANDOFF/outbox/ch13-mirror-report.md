# Ch13 Mirror Tail-Boundary Report — ZinanFFCT61

**File:** `ProofsInTheBook/ZinanFFCT61.lean` (new).  Verified on `uisai2` after building
`ProofsInTheBook.ZinanFFCT60`:

```text
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake build ProofsInTheBook.ZinanFFCT60 && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT61.lean'
```

`ZinanFFCT61.lean` checks with 0 errors.  The printed axioms for the new load-bearing declarations are
clean-3:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, `native_decide`, or new logical postulates are introduced.

## What Landed

FFCT61 defines the coordinate reflection

```text
reflectZ (x,y,z) = (x,y,-z)
```

and the mirror-reversed arm

```text
mirrorArm P m = mirrorS2 (revArm P m).
```

The reflection is proved to preserve inner products, norms, `sDist`, `sphAngle`, `sideLen`,
`jointAngle`, `endpt`, `SameSides`, `JointLe`, `PositiveJoints`, and `NoNonadjacentRepeat`, while
flipping `sOrient`:

```text
sOrient (mirrorS2 a) (mirrorS2 b) (mirrorS2 c) = -sOrient a b c.
```

Composed with index reversal, the two sign flips cancel.  Therefore convexity transports from the
original arm, not from the bare reversed arm:

```text
weakConvex_mirrorArm
strictConvex_mirrorArm
```

## Tail Boundary Discharge

The FFCT60 conditional tail classifier is replaced by the direct mirror-arm route:

```text
mirror_tail_midFold_forces_endpoint_j
```

Given the ordinary inputs

```text
WeakConvexSphArm P
PositiveJoints P
StrictConvexSphArm Q
JointLe P Q
NoNonadjacentRepeat P
```

a tail mid-fold

```text
P n = c • P (n-1) + d • P j,    c,d > 0,    j + 2 ≤ n
```

forces

```text
j = 0 ∨ j = 1.
```

For the FFCT59 WBS tail residue this gives:

```text
nonAxisTailBoundaryResidue_forces_endpoint_j_mirror
nonAxisTailBoundaryResidue_false_of_two_le_j_mirror
```

So every non-axis tail-boundary residue with `2 ≤ j` is now impossible without the old
`TailBoundaryReversalConvexity` input.

## Remaining Ch13 Surface

The mirror transform removes the reversed-convexity gap for the tail `j ≥ 2` branch.  It does not by
itself prove `SupportStuckWBSImpossible`, because two surfaces remain:

```text
1. tail endpoint cases j ∈ {0,1} still need the boundary-transport route;
2. raw SupportStuckWBS still needs the sign-supply path into FFCT56's NonAxisMixedBindingResidue.
```

Thus the sharp honest Ch13 status is:

```text
non-axis mixed support-stuck
  = successor-edge cases killed by FFCT59
  + tail cases j ≥ 2 killed by FFCT61 unconditionally from the standard convex/metric inputs
  + endpoint tail cases j ∈ {0,1} still requiring boundary transport
  + raw sign-supply still required before arbitrary SupportStuckWBS enters this residue analysis.
```

The reach-only headline remains the FFCT59 conditional chain until those two surfaces are supplied.
