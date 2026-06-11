# CH13 v9 interface report (`ZinanFFCT77`)

## Status

Created `ProofsInTheBook/ZinanFFCT77.lean`.

Remote verification:

```bash
scp ProofsInTheBook/ZinanFFCT77.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT77.lean
ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && lake build ProofsInTheBook.ZinanFFCT76 && lake env lean ProofsInTheBook/ZinanFFCT77.lean'
```

Result: 0 errors.  The printed declarations are clean-3:

```text
endpoint_of_boundaryZeroProgress_at_level_nr
endpoint_of_mirrorBoundaryZeroProgress_at_level_nr
endpoint_of_normalized_vanishing_support_at_level_nr_v9
weakBoundaryProgress_of_wrapSeedResidueV9
weakPositiveCutReadyNR_v9_holds
supportStuckWBS_boundaryProgress_of_wrapSeedResidueV9
supportStuckWBS_endpoint_dispatch_at_level_nr_v9
szOpeningStepPlusNR_v9
mainPlusNR_all_v9
spherical_arm_mono_final_ch13_v9
```

Each depends only on:

```text
[propext, Classical.choice, Quot.sound]
```

## Landed interface

`ZinanFFCT77` adds endpoint-aware residue forms:

```lean
def MirrorBoundaryZeroProgress {n : ℕ} (P B : Fin (n + 1) → S2) : Prop :=
  BoundaryZeroProgress P B ∨ BoundaryZeroProgress (mirrorArm P) (mirrorArm B)

def WeakVanishingWrapSeedResidueV9 : Prop := ...

def SupportStuckWBSWrapSeedResidueV9 : Prop := ...

def BPosANegTailCornerResidueV9 : Prop := ...
```

The two wrap residues now return `BoundaryZeroProgress` directly, so their endpoint branch is
accepted by the FFCT74 NR consumer chain instead of being forced into the old normalized-only v8
shape.  The signed tail residue is also v9-shaped: it is consumed at the live NR induction level and
therefore carries the dimension IH that the v8 tail field lacked.

The bridges are:

```lean
endpoint_of_span_at_level_nr_v9
endpoint_of_normalized_vanishing_support_at_level_nr_v9
endpoint_of_boundaryZeroProgress_at_level_nr
endpoint_of_mirrorBoundaryZeroProgress_at_level_nr
weakBoundaryProgress_of_wrapSeedResidueV9
weakPositiveCutReadyNR_v9_holds
supportStuckWBS_boundaryProgress_of_wrapSeedResidueV9
supportStuckWBS_endpoint_dispatch_at_level_nr_v9
szOpeningStepPlusNR_v9
mainPlusNR_all_v9
```

## Exact final surface

The checked final surface is:

```lean
structure Ch13FinalSurface77 : Prop where
  hweakWrapSeed : WeakVanishingWrapSeedResidueV9
  hwrapSeed : SupportStuckWBSWrapSeedResidueV9
  hcross : CrossPieceNoCollisionAtSup
  hbpos_aneg_tail : BPosANegTailCornerResidueV9
```

The checked v9 statement is:

```lean
theorem spherical_arm_mono_final_ch13_v9 (res : Ch13FinalSurface77)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤
      sDist (B 0) (B (Fin.last n))
```

## Why this is not `{hcross}`-only

The requested `{hcross}`-only theorem is still not honestly typable from the landed source.

The two wrap residues can now carry endpoint progress, and FFCT77 consumes that progress directly.
The tail corner is no longer the old v8 type; it is now a live-IH v9 endpoint residue:

```lean
hbpos_aneg_tail : BPosANegTailCornerResidueV9
```

This fixes the exact FFCT76/FFCT74 interface mismatch for all three old residues.  What remains
unproved is not a type mismatch but the generation of these v9 residues from `hcross` alone.  In
particular, changing the tail payload to `BoundaryZeroProgress P B` is not enough by itself: in the
normalized branch, the endpoint dispatch re-enters the same `b > 0, a < 0, j = n` tail case.  Without
a kernel-checked decreasing propagation theorem such as `wrapPlanePropagation` /
`apexNBoundaryZeroPropagation`, that route is circular.

FFCT76 supplies the worker bricks:

```lean
flat_interior_joint_absurd_public
boundaryPlane_step_sameSign
normalized_zero_of_wrap_probe_one
```

but not the induction wrapper that turns arbitrary wrap/apex boundary zeroes into non-circular
endpoint progress.  Therefore `CrossPieceNoCollisionAtSup` alone still cannot construct the full
`Ch13FinalSurface77`.
