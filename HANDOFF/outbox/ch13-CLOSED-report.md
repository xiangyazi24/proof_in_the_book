# CH13 FFCT82 composition audit (`ZinanFFCT82`)

## Status

Created `ProofsInTheBook/ZinanFFCT82.lean`.

The requested hcross-only theorem

```lean
theorem spherical_arm_mono_final_ch13_v10
    (hcross : CrossPieceNoCollisionAtSup) :
    SphericalArmMonotone
```

is **not** landed.  The composition brief's proposed apex route is not compatible
with the checked FFCT81 interface.

No proof placeholders or unsafe declarations were introduced.

Remote verification:

```bash
scp ProofsInTheBook/ZinanFFCT82.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT82.lean
ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && lake env lean ProofsInTheBook/ZinanFFCT82.lean'
```

Result: 0 errors.  The new declarations are clean-3:

```text
normalizedInteriorSupportZero_of_apexNBoundaryZero
boundaryZeroProgress_of_apexNBoundaryZero
normalizedInteriorSupportZero_of_wrap_probe_one
boundaryZeroProgress_of_wrap_probe_one
normalizedStrictInteriorSupportZero_probe_lt_n
apex_far_probe_not_noTail_witness
boundaryZeroProgressNoTail_cases_probe_lt_n
spherical_arm_mono_final_ch13_v10_of_hcross_wrapNoTail_ffct82
```

Each depends only on:

```text
[propext, Classical.choice, Quot.sound]
```

## What FFCT82 proves

The apex boundary zero has the old normalized shape:

```lean
theorem normalizedInteriorSupportZero_of_apexNBoundaryZero :
    NormalizedInteriorSupportZero A
```

and the probe-`1` wrap zero also normalizes to the old apex witness `(0,n)`:

```lean
theorem normalizedInteriorSupportZero_of_wrap_probe_one :
    NormalizedInteriorSupportZero A
```

The no-tail payload from FFCT81 has a strictly stronger invariant:

```lean
theorem normalizedStrictInteriorSupportZero_probe_lt_n :
    NormalizedStrictInteriorSupportZero A →
      ∃ i j, ... ∧ j < n ∧ ...
```

Thus a no-tail normalized witness cannot have far probe `j = n`:

```lean
theorem apex_far_probe_not_noTail_witness : False
```

## Blocking point

`NormalizedStrictInteriorSupportZero` is defined with the extra side condition

```lean
j + 1 < n + 1
```

so every no-tail normalized witness has `j < n`.  The probe-`1`/apex route
produces exactly `j = n`.  Therefore the route

```text
probe-one wrap output -> apex theorem -> normalized interior zero -> FFCT81 no-tail consumer
```

does not type-check against the current definitions.  It yields only old
`BoundaryZeroProgress`, and feeding that through the old generic endpoint
consumer is the circular path already identified in `ch13-v10-report.md` and
`ch13-v10-final-report.md`.

The still-missing honest content remains a real strengthened propagation theorem
or a new non-circular endpoint consumer for the apex/tail case:

```lean
WrapPlanePropagationNoTail
```

or an equivalent direct closure of the `j = n` signed tail branch.

