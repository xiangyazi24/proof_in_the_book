# CH13 v10 stall-progress report (`ZinanFFCT84`)

## Status

Created `ProofsInTheBook/ZinanFFCT84.lean`.

The stall-progress refinement for the signed tail corner is landed and
kernel-checked.  The exact hcross-only headline

```lean
theorem spherical_arm_mono_final_ch13_v10
    (hcross : CrossPieceNoCollisionAtSup) :
    SphericalArmMonotone
```

is **not** landed: after the tail residue is closed, the checked assembly still
requires the separate wrap-edge propagation theorem
`WrapPlanePropagationGeneral`.  That theorem is not supplied by
`CrossPieceNoCollisionAtSup` and is not present in the current library.

No `sorry`, `admit`, `axiom`, or `native_decide` was introduced.

Remote verification used the requested path:

```bash
scp ProofsInTheBook/ZinanFFCT84.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT84.lean
ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && lake build ProofsInTheBook.ZinanFFCT83 && lake env lean ProofsInTheBook/ZinanFFCT84.lean'
ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && lake build ProofsInTheBook.ZinanFFCT84'
```

Result: 0 errors for both checks.  The new declarations are clean-3:

```text
normalizedStrictInteriorSupportZero_of_tail_firstStep
bpos_aneg_tailCornerResidueV9_of_firstStepInteriorZero
spherical_arm_mono_final_ch13_v10_of_hcross_wrapGeneral_ffct84
```

Each depends only on:

```text
[propext, Classical.choice, Quot.sound]
```

## Landed content

The first-step witness production is checked:

```lean
theorem normalizedStrictInteriorSupportZero_of_tail_firstStep :
    ... →
    OpenCone (P i) (P (i+1)) (P n) →
    NormalizedStrictInteriorSupportZero P
```

In the non-adjacent case `i + 2 < n`, the open tail cone plus the weak supports
of edge `(n-1,n)` at `P i` and `P (i+1)` feed FFCT83's
`edgeAnchor_prev_plane_of_next_openCone`, producing

```lean
sOrient (P i) (P (i+1)) (P (n-1)) = 0
```

This is exactly the no-tail normalized witness `(i, n-1)`.

The live signed-tail residue is closed:

```lean
theorem bpos_aneg_tailCornerResidueV9_of_firstStepInteriorZero :
    BPosANegTailCornerResidueV9
```

The adjacent case `i + 2 = n` is discharged by FFCT83's
`bpos_aneg_tail_adjacent_forbidden`; the non-adjacent case is consumed by
FFCT81's `endpoint_of_normalizedInteriorZero_noTail`.

The final checked wrapper now needs only the wrap propagation theorem:

```lean
theorem spherical_arm_mono_final_ch13_v10_of_hcross_wrapGeneral_ffct84
    (hcross : CrossPieceNoCollisionAtSup)
    (hwrap : WrapPlanePropagationGeneral) :
    SphericalArmMonotone
```

## Remaining gap

`CrossPieceNoCollisionAtSup` is only the no-repeat supply for opened WBS arms.
It does not produce `WrapPlanePropagationGeneral`, and the existing v10
assembly still needs that propagation to discharge the two wrap-edge residues:

```lean
weakWrapSeed_v9_of_wrapPropagationGeneral
supportStuckWBSWrapSeed_v9_of_wrapPropagationGeneral
```

Therefore the hcross-only statement cannot be asserted honestly from the current
checked interfaces without first landing `WrapPlanePropagationGeneral` or an
equivalent direct replacement for both wrap residues.
