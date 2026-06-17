# Ch13 Bundle Report - ZinanFFCT62

**File:** `ProofsInTheBook/ZinanFFCT62.lean` (new).  Verified on `uisai2`:

```text
scp ProofsInTheBook/ZinanFFCT62.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT62.lean
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake build ProofsInTheBook.ZinanFFCT61 && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT62.lean'
```

Result: `ZinanFFCT61` olean built; `ZinanFFCT62.lean` checks with 0 errors.  All new `#print axioms`
outputs are clean-3:

```text
[propext, Classical.choice, Quot.sound]
```

No new postulates or proof placeholders were introduced.

## Bundle Minimization

The existing `ZinanFFCT59.Ch13ReachOnlyResidues` is **not** minimal as a `SZOpeningStepPlus` bundle:
`szOpeningStepPlus_reachOnly_honest` explicitly consumes `hwpc` and `hffct` in the weak-entry
vanishing-support branch.  FFCT57's `mainPlus_of_supportStuckImpossible` similarly consumes
`SpliceBodyDiagMono` and `SpliceStructuralData` for that weak-entry branch.

However, the strict-arm reach-only headline can avoid `SZOpeningStepPlus` entirely.  `ZinanFFCT62`
adds a custom strict-only deficit induction:

```text
spherical_arm_mono_reachOnly_v2 :
  SupportStuckWBSImpossible -> strict endpoint monotonicity
```

The recursion never passes a weak arm: in the deficient case it calls `reachOnly_outcome`, which returns
a strict opened arm `A'` plus `deficitCount A' B < deficitCount A B`; the induction recurses only on
that strict `A'`.

## True Step Surface

Tail endpoint cases do not prove `False`; they prove `endpt (openedWBS A B k) <= endpt B`.  So the
true strict-step consumer is endpoint dispatch, not pure support-stuck impossibility:

```text
SupportStuckWBSEndpointDispatch
spherical_arm_mono_of_supportStuckEndpointDispatch
Ch13VNextSurface
spherical_arm_mono_vNext
```

`SupportStuckWBSImpossible` is still a special case:

```text
supportStuckEndpointDispatch_of_impossible
spherical_arm_mono_vNext_of_reachOnlyStrictSurface
```

## Non-Axis Raw Sign Supply

The raw one-sided derivative ledger does **not** supply the needed `b < 0` sign.  After substituting
`x = a*y + b*z`, with `G = <y,z>`, `p = <y,k>`, and `q = <z,k>`, the determinant derivative expression is:

```text
(a*p + b*q)*G - (a*G + b)*p = b*(q*G - p)
```

Lean anchors:

```text
nonAxis_singleRotation_substitution_algebra
nonAxis_derivative_inequality_not_force_bneg
nonAxis_derivative_factor_has_all_signs
```

The factor `q*G - p` is not sign-definite from these ledger variables, and the inequality
`b*(q*G - p) <= 0` does not imply `b < 0`.  Thus the raw sign supply into
`NonAxisMixedBindingResidue` remains the named irreducible obstruction.

## Tail Endpoint Transport

The mirror route now has theorem-shaped endpoint transports:

```text
mirror_tail_midFold_collinearity
nonAxisTailBoundaryResidue_mirror_collinearity
tailBoundary_j0_endpoint_transport_mirror
tailBoundary_j1_endpoint_transport_mirror
```

`j = 0` mirrors to FFCT53's `(0,n)` boundary transport and still needs the boundary interval
certificates (`hAe`, `hBe`).  `j = 1` mirrors to FFCT53's `(0,n-1)` transport and still needs the
mirrored diagonal inequality plus `TailFoldBoundary`.  These are endpoint transports, not eliminations.

## Final Surface

The honest final strict headline is:

```text
spherical_arm_mono_vNext : Ch13VNextSurface -> strict endpoint monotonicity
```

where `Ch13VNextSurface` is exactly endpoint dispatch for WBS support-stuck branches.  To discharge that
surface from raw geometry, the remaining work is:

1. supply or bypass the raw non-axis `b < 0` sign;
2. connect the `j = 0` endpoint case to the required interval certificates;
3. connect the `j = 1` endpoint case to the required diagonal inequality and `TailFoldBoundary`.
