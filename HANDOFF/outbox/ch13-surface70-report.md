# Ch13 surface-70 report -- ZinanFFCT71

Delivered:

- `ProofsInTheBook/ZinanFFCT71.lean`
- `HANDOFF/outbox/ch13-surface70-report.md`

## What landed

### Wrap seed shrink

FFCT71 replaces FFCT70's full mirror-aware seed supply with the exact raw wrap-base
residue:

```lean
def SupportStuckWBSWrapSeedResidue : Prop := ...

theorem mirrorSeed_of_wrapSeedResidue
    (hwrap : SupportStuckWBSWrapSeedResidue) :
    SupportStuckWBSMirrorVanishingSpanSeedSupply := ...
```

The proof opens the raw `SupportStuckWBS` witness via
`supportStuckWBS_vanishingSupport`.  If the binding edge has an ordinary successor,
`orientationNormalized` supplies the normalized forward seed; the reversed branch is
converted to the mirror seed with `mirrorArm_sOrient_zero_of_revArm_zero`.  Only the
`¬ a.val + 1 < n + 1` wrap binding is left to the new residue.

### `bpos_apos` step adapter

FFCT71 records the strong step-site version of the positive-positive branch:

```lean
def BPosAPosDiagonalSupply : Prop := ...

theorem bpos_apos_endpoint_of_diagonalSupply_at_level
    (hdiagSupply : BPosAPosDiagonalSupply) ... :
    endpt P ≤ endpt B := ...
```

This adapter uses `foldedFlatCutTransportPlusForward_v3` and the FFCT68 forward
consumer.  It is intentionally not used to remove the headline `BPosAPosEndpointCase`,
because the live FFCT69/70 final route has already gone through the strict-only
recursion and no longer exposes the strong `ihdim` hypothesis at the branch site.

### FFCT71 final wrapper

The exact new surface is:

```lean
structure Ch13FinalSurface71 : Prop where
  hwrapSeed : SupportStuckWBSWrapSeedResidue
  hcross : CrossPieceNoCollisionAtSup
  hbpos_apos : BPosAPosEndpointCase
  hbpos_aneg_tail : BPosANegTailCornerResidue
```

The new wrapper maps into FFCT70:

```lean
theorem final70_of_final71 (res : Ch13FinalSurface71) : Ch13FinalSurface70 := ...
```

and gives the requested headline:

```lean
theorem spherical_arm_mono_final_ch13_v5
    (res : Ch13FinalSurface71) :
    SphericalArmMonotone := ...
```

## What still resists

### `hbpos_apos`

The FFCT68 transport closes the branch when `ihdim` and the diagonal inequality are
available.  FFCT71 landed this as `BPosAPosDiagonalSupply` plus
`bpos_apos_endpoint_of_diagonalSupply_at_level`.

The current final recursion, however, enters through the FFCT62 strict-only endpoint
dispatch and does not expose the strong-induction `ihdim` at the `bpos_apos` binding.
Moving the headline back to the raw `SZOpeningStepPlus` level would be a larger
assembly rewrite and would reintroduce the cut-ready/StuckAtK plumbing at the surface.
So `BPosAPosEndpointCase` remains in the final surface.

### `hbpos_aneg_tail`

FFCT70 already closes the successor case by `not_both_witness_zero`; that theorem
needs a genuine successor edge `j + 1 < n + 1`.  The surviving tail case is the
endpoint `j = n`, where the normalized arm has no ordinary successor.

The FFCT60/61/65 mirror-tail machinery is WBS-specific through
`NonAxisTailBoundaryResidue` and does not currently imply the bare
`BPosANegTailCornerResidue` used by the trichotomy endpoint surface.  No honest
general tail contradiction is exposed yet.

### `hwrapSeed`

Non-wrap raw `SupportStuckWBS` support witnesses are now discharged.  The remaining
seed item is exactly the raw wrap binding
`¬ a.val + 1 < n + 1` from `SupportStuckWBSWrapSeedResidue`.

I did not find a landed theorem that converts an arbitrary wrap-edge
`SupportStuckWBS` witness into a normalized forward in-arm support seed.  Existing
wrap/base support facts are tied to base-stuck or WBS-specific hypotheses, not this
generic raw support witness.

### `hcross`

`CrossPieceNoCollisionAtSup` remains explicit.  The derivative-at-collision route is
not sign-definite with the currently available WBS context: FFCT62 records both
`nonAxis_derivative_inequality_not_force_bneg` and
`nonAxis_derivative_factor_has_all_signs`, so the attempted sign kill would be
dishonest without an additional hypothesis.

## Refutation checks

The new residues are not vacuous `True` placeholders.  FFCT71 includes target guards
for the concrete zero-support and diagonal inequalities:

```lean
theorem wrapSeedResidue_target_real : ...
theorem bpos_apos_diagonal_target_satisfiable : ...
```

The final surface is still a real proof surface, not an axiom-based closure.

## Verification

Local placeholder scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" ProofsInTheBook/ZinanFFCT71.lean
```

No matches.

Remote verification on `uisai2`:

```bash
scp ProofsInTheBook/ZinanFFCT71.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT71.lean
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake build ProofsInTheBook.ZinanFFCT70 && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT71.lean'
```

Result:

- `ProofsInTheBook.ZinanFFCT70` built successfully on `uisai2`.
- `ProofsInTheBook/ZinanFFCT71.lean` checked successfully on `uisai2`.
- `#print axioms` for the new main theorems is clean-3 only:
  `[propext, Classical.choice, Quot.sound]`.

No commit was made.
