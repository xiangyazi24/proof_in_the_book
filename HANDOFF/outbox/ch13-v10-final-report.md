# CH13 v10 final report (`ZinanFFCT80`)

## Status

Created `ProofsInTheBook/ZinanFFCT80.lean`.

The requested hcross-only theorem was **not** landed.  No proof placeholders or
unsafe declarations were introduced.

Remote verification:

```bash
scp ProofsInTheBook/ZinanFFCT80.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT80.lean
ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && lake build ProofsInTheBook.ZinanFFCT80'
```

Result: 0 errors.  The new declarations are clean-3:

```text
WrapPlaneState.sOrient_zero
wrapPlaneState_step_sameSign
wrap_next_real_span_of_sameSign
wrap_next_real_span_of_sameSign_context
wrap_zero_real_span
wrap_anchor_nonAntipodal_of_hemisphere
wrap_anchor_distinct_of_noRepeat
wrap_zero_real_span_of_context
s2_eq_of_real_smul_with_positive_inner
wrap_head_distinct_of_noRepeat
wrap_last_head_distinct_of_weak
wrap_initial_last_coeff_zero_absurd
wrap_initial_probe_coeff_zero_absurd
wrap_initial_both_negative_absurd
wrap_initial_state_of_sameSign
bpos_aneg_tail_span_forces_wrap_zero
weakWrapSeed_v9_of_wrapPropagationGeneral
supportStuckWBSWrapSeed_v9_of_wrapPropagationGeneral
spherical_arm_mono_final_ch13_v10_of_hcross_wrap_and_tail
```

Each depends only on:

```text
[propext, Classical.choice, Quot.sound]
```

## Landed content

`ZinanFFCT80` lands the sign-carrying state and worker bricks:

```lean
structure WrapPlaneState {n : ℕ} (A : Fin (n + 1) → S2)
    (j : Fin (n + 1)) (k : ℕ)
```

It proves the same-sign determinant step specialized to that state, re-extracts
real coefficients for the next vertex, closes the initial zero-coefficient and
double-negative cases, and proves that the signed tail branch forces a wrap-edge
zero.

It also proves conditional wrappers:

```lean
theorem weakWrapSeed_v9_of_wrapPropagationGeneral
    (hwrap : WrapPlanePropagationGeneral) :
    WeakVanishingWrapSeedResidueV9

theorem supportStuckWBSWrapSeed_v9_of_wrapPropagationGeneral
    (hcross : CrossPieceNoCollisionAtSup)
    (hwrap : WrapPlanePropagationGeneral) :
    SupportStuckWBSWrapSeedResidueV9
```

and the checked conditional assembly:

```lean
theorem spherical_arm_mono_final_ch13_v10_of_hcross_wrap_and_tail
    (hcross : CrossPieceNoCollisionAtSup)
    (hwrap : WrapPlanePropagationGeneral)
    (htail : BPosANegTailCornerResidueV9) :
    SphericalArmMonotone
```

## Target statement

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

The remaining gap is not the same-sign propagation or real-span extraction.
Those are now checked.  The hard missing step is still the non-circular endpoint
closure for the signed tail branch.

`bpos_aneg_tail_span_forces_wrap_zero` shows that the `b > 0, a < 0, j = n`
tail span produces a wrap-edge zero from the wrap supports.  Feeding that through
`WrapPlanePropagationGeneral` gives only `BoundaryZeroProgress`.  The existing
consumer `endpoint_of_boundaryZeroProgress_at_level_nr` needs
`BPosANegTailCornerResidueV9`, so using it inside the proof of that same tail
residue is exactly the circular path identified in the earlier reports.

