# CH13 final wave report

## Status

Created `ProofsInTheBook/ZinanFFCT76.lean` and verified the worker layer that can be honestly
kernel-checked against `ZinanFFCT75`.

Remote check:

```bash
ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && lake env lean ProofsInTheBook/ZinanFFCT76.lean'
```

Result: 0 errors.  The three printed declarations are clean-3:

```text
flat_interior_joint_absurd_public : [propext, Classical.choice, Quot.sound]
boundaryPlane_step_sameSign       : [propext, Classical.choice, Quot.sound]
normalized_zero_of_wrap_probe_one : [propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, `axiom`, or `native_decide` was added.

## Landed in `ZinanFFCT76`

* `NormalizedInteriorSupportZero`
* `BoundaryZeroProgress`
* `flat_interior_joint_absurd_public`
* `boundaryPlane_step_sameSign`
* `normalized_zero_of_wrap_probe_one`

The design's written `NormalizedInteriorSupportZero` shape used `by omega` inside a Prop definition
where the preceding conjunct bounds are not in scope.  The implemented version stores the bound
witnesses explicitly, matching the existing FFCT71/74 residue shape.

## Why v9 is not landed

The requested `{hcross}`-only final surface cannot be assembled from the current checked interfaces
without changing earlier residue types or adding an unsound placeholder.

Concrete blockers:

1. `WeakVanishingWrapSeedResidue` in `ZinanFFCT74` returns only a normalized zero on `P` or on
   `mirrorArm P`.  It has no endpoint branch.  Therefore a theorem whose output is
   `BoundaryZeroProgress A B` cannot discharge this residue when it returns `endpt A ≤ endpt B`.

2. `SupportStuckWBSWrapSeedResidue` in `ZinanFFCT71` has the same issue: its conclusion is only the
   mirror-aware normalized seed, not endpoint progress.

3. `BPosANegTailCornerResidue` must return `endpt P ≤ endpt B`, but the normalized-zero endpoint
   consumer currently available at the NR level,
   `endpoint_of_normalized_vanishing_support_at_level_nr`, requires the live dimension IH
   `∀ m < n, MainPlusNR m`.  `BPosANegTailCornerResidue` has no IH argument.

Thus the design's `BoundaryZeroProgress := NormalizedInteriorSupportZero A ∨ endpt A ≤ endpt B`
is useful as an endpoint-progress API, but it is not type-compatible with the three old residues it
is supposed to discharge.

## Requested v9 statement

```lean
theorem spherical_arm_mono_final_ch13_v9
    (res : Ch13FinalSurface76)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤
      sDist (B 0) (B (Fin.last n))
```

This theorem is not declared in `ZinanFFCT76.lean`, because the current source does not provide a
sound way to construct the required `Ch13FinalSurface74` fields from only `CrossPieceNoCollisionAtSup`.
