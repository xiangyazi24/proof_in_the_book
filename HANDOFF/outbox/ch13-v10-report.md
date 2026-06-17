# CH13 v10 wrapper report (`ZinanFFCT78`)

## Status

Created `ProofsInTheBook/ZinanFFCT78.lean`.

Remote verification:

```bash
scp ProofsInTheBook/ZinanFFCT78.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT78.lean
ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && lake build ProofsInTheBook.ZinanFFCT77 && lake env lean ProofsInTheBook/ZinanFFCT78.lean'
```

Result: 0 errors.  The printed declarations are clean-3:

```text
wrapPlanePropagation_probe_one
apexNBoundaryZeroPropagation
apexNBoundaryZeroProgress
```

Each depends only on:

```text
[propext, Classical.choice, Quot.sound]
```

## Landed declarations

`ZinanFFCT78` adds the v10 headline predicate:

```lean
def SphericalArmMonotone : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ A B : Fin (n + 1) → S2,
    StrictConvexSphArm A → StrictConvexSphArm B →
    (∀ i : Fin n, sideLen A i = sideLen B i) →
    (∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) →
      sDist (A 0) (A (Fin.last n)) ≤
        sDist (B 0) (B (Fin.last n))
```

It also lands the directly normalizing wrapper cases:

```lean
theorem wrapPlanePropagation_probe_one
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (_hA : WeakConvexSphArm A)
    (_hpos : PositiveJoints A)
    (_hB : StrictConvexSphArm B)
    (_hside : SameSides A B)
    (_hangle : JointLe A B)
    (_hnr : NoNonadjacentRepeat A)
    (_hhem :
      ∃ h : E3, ‖h‖ = 1 ∧
        ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    {j : Fin (n + 1)}
    (hjval : j.val = 1)
    (hzero : sOrient (A (Fin.last n)) (A 0) (A j) = 0) :
    BoundaryZeroProgress A B

theorem apexNBoundaryZeroPropagation
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (_hn : 2 ≤ n)
    (_hA : WeakConvexSphArm A)
    (_hpos : PositiveJoints A)
    (_hB : StrictConvexSphArm B)
    (_hside : SameSides A B)
    (_hangle : JointLe A B)
    (_hnr : NoNonadjacentRepeat A)
    (_hhem :
      ∃ h : E3, ‖h‖ = 1 ∧
        ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    {i : ℕ}
    (hi : i < n + 1)
    (hi1 : i + 1 < n + 1)
    (hfar : i + 1 < n)
    (hzero :
      sOrient (A ⟨i, hi⟩)
        (A ⟨i + 1, hi1⟩)
        (A ⟨n, by omega⟩) = 0) :
    BoundaryZeroProgress A B
```

## Target v10 statement

The requested hcross-only statement was not landed:

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

The full induction wrapper

```lean
wrapPlanePropagation
```

is still missing.  FFCT76 supplies only the worker bricks:

```lean
flat_interior_joint_absurd_public
boundaryPlane_step_sameSign
normalized_zero_of_wrap_probe_one
```

Those close the probe-`1` wrap case and the already-normalized apex case, but they do not provide the
global decreasing propagation needed for an arbitrary interior wrap probe.  The missing pieces are the
design-level `PlaneState.next_or_progress` / `PlaneState.progress_until_exit` layer and the zero- and
opposite-sign routing into the FFCT56/70/61 endpoint/collapse branches.

Consequently the three v9 residue fields are still not constructible as theorems:

```lean
WeakVanishingWrapSeedResidueV9
SupportStuckWBSWrapSeedResidueV9
BPosANegTailCornerResidueV9
```

In particular, `apexNBoundaryZeroPropagation` returning the left normalized branch is not enough to
prove `BPosANegTailCornerResidueV9`: consuming that normalized branch through
`endpoint_of_boundaryZeroProgress_at_level_nr` re-enters the same `b > 0, a < 0, j = n` tail corner.
That is the circularity already identified in the v9 report.

