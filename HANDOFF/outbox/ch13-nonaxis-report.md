# Ch13 Non-Axis Mixed Binding Audit — Report (ZinanFFCT59)

**File:** `ProofsInTheBook/ZinanFFCT59.lean` (new).  Verified on `uisai2`:

```text
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT59.lean'
```

Result: 0 errors.  All new printed theorem axioms are clean-3:
`[propext, Classical.choice, Quot.sound]`.  No proof placeholders or extra logical postulates.

## Verdict

`NonAxisMixedBindingResidue` is **not globally discharged** from the currently committed data.
The precise reason is structural: FFCT56's residue already assumes the sign datum `b < 0`; it does
not derive that datum from a raw `SupportStuckWBS` witness.  Once `b < 0` is present, the FFCT56
mid-fold kill refutes every case whose apex `i+1` has a successor edge (`i+2 < n+1`).

The two non-axis mixed patterns reduce as follows.

1. **Pattern (a): `i,i+1` fixed and `j` rotated.**  Discharged.  The hypotheses
   `i+1 ≤ K < j` plus the non-axis guard force `i+1 < K`; since `K < n`, the successor edge exists.
   Lean theorem: `nonAxis_fixedFixed_rotated_false`.

2. **Pattern (c): `i,i+1` rotated and `j` fixed.**  Discharged away from the tail.  If `i+1 ≠ n`,
   the successor edge exists and the same mid-fold kill fires.
   Lean theorem: `nonAxis_rotatedRotated_fixed_false_of_not_tail`.

3. **Remaining exact survivor:** pattern (c) at the tail boundary `i+1 = n`.
   Lean theorem: `nonAxis_rotatedRotated_fixed_forces_tail`, packaged as
   `NonAxisTailBoundaryResidue`.

So the honest final status is:

```text
NonAxisMixedBindingResidue
  = killed in fixed-fixed-rotated
  + killed in rotated-rotated-fixed when i+1 ≠ n
  + tail-boundary residue when i+1 = n.
```

## Final Headline Status

`SupportStuckWBSImpossible` is **not proved** in FFCT59, because raw support-stuck still lacks a
proved route to the `b < 0` non-axis sign datum and the tail-boundary case is still explicit.

FFCT59 adds a splice-free reach-only endpoint chain:

* `Ch13ReachOnlyResidues` =
  `WeakPositiveCutReady` + `FoldedFlatCutTransportPlus` + `SupportStuckWBSImpossible`.
* `szOpeningStepPlus_reachOnly_honest` uses the modern weak-entry cut and FFCT57's reach-only WBS
  step.
* `spherical_arm_mono_reachOnly_honest` gives the strict-arm endpoint theorem from that honest
  bundle, with no `SpliceBodyDiagMono` or `SpliceStructuralData`.

This is the correct non-vacuous endpoint chain once the remaining support-stuck elimination is
actually supplied.
