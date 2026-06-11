# CH13 final v10 report (`ZinanFFCT79`)

## Status

Created `ProofsInTheBook/ZinanFFCT79.lean`.

The requested hcross-only theorem was **not** landed.  No proof placeholders or
unsafe declarations were introduced.

Remote verification:

```bash
scp ProofsInTheBook/ZinanFFCT79.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT79.lean
ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && lake build ProofsInTheBook.ZinanFFCT78 && lake env lean ProofsInTheBook/ZinanFFCT79.lean'
```

Result: 0 errors.  The printed declarations are clean-3:

```text
spherical_arm_mono_final_ch13_v10_of_hcross_and_boundaryResidues
spherical_arm_mono_final_ch13_v10_from_surface77
wrapPlanePropagationGeneral_probe_one_satisfies_shape
```

Each depends only on:

```text
[propext, Classical.choice, Quot.sound]
```

## Checked wrapper added

`ZinanFFCT79` adds the exact checked wrapper currently available at the v10
interface:

```lean
theorem spherical_arm_mono_final_ch13_v10_of_hcross_and_boundaryResidues
    (hcross : CrossPieceNoCollisionAtSup)
    (res : V10BoundaryResidues) :
    SphericalArmMonotone
```

where the remaining non-cross fields are exactly:

```lean
structure V10BoundaryResidues : Prop where
  hweakWrapSeed : WeakVanishingWrapSeedResidueV9
  hwrapSeed : SupportStuckWBSWrapSeedResidueV9
  hbpos_aneg_tail : BPosANegTailCornerResidueV9
```

It also records the requested general-probe theorem shape as a `Prop`, not as an
assumption:

```lean
def WrapPlanePropagationGeneral : Prop := ...
```

## Target v10 statement

The requested statement remains:

```lean
theorem spherical_arm_mono_final_ch13_v10
    (hcross : CrossPieceNoCollisionAtSup) :
    SphericalArmMonotone
```

Equivalently, expanded:

```lean
theorem spherical_arm_mono_final_ch13_v10
    (hcross : CrossPieceNoCollisionAtSup)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤
      sDist (B 0) (B (Fin.last n))
```

## Blocking point

The arbitrary wrap-probe propagation is still not available:

```lean
WrapPlanePropagationGeneral
```

The probe-`1` case is checked through `wrapPlanePropagation_probe_one`, and the
apex-`n` normalized-zero wrapper is checked in `ZinanFFCT78`, but those do not
break the signed tail-corner cycle.  Feeding the apex normalized zero into
`endpoint_of_boundaryZeroProgress_at_level_nr` re-enters
`BPosANegTailCornerResidueV9` in the same `b > 0, a < 0, j = n` branch.

The missing proof content is therefore still the sign-carrying decreasing
propagation for an arbitrary wrap probe, with the opposite-sign branches routed
to endpoint progress rather than back into the same tail residue.
