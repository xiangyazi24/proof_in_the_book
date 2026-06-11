# Ch13 b-trichotomy dispatch report — ZinanFFCT64

**File:** `ProofsInTheBook/ZinanFFCT64.lean` (new).  It imports `ZinanFFCT62` only; it does not import
or touch the parallel-worker `ZinanFFCT63.lean`.

Verified on `uisai2`:

```text
scp ProofsInTheBook/ZinanFFCT64.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT64.lean
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake build ProofsInTheBook.ZinanFFCT62 && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT64.lean'
```

Result: `ZinanFFCT62` built; `ZinanFFCT64.lean` checks with 0 errors.  The five printed declarations
are clean-3:

```text
[propext, Classical.choice, Quot.sound]
```

## What landed

`ZinanFFCT64` formalizes the b-trichotomy control path for a normalized real-span binding

```text
P i = a • P (i+1) + b • P j,     i+1 < j.
```

The locally closed branches are:

1. `b = 0`: `span_bzero_false_of_weak`, using the opened edge `ShortArc`.
2. `b < 0` with successor edge `i+2 < n+1`: closed by FFCT56 `midFold_bneg_false`.
3. `b > 0, a = 0`: `span_azero_bpos_false_of_noRepeat`, forcing a nonadjacent repeat `P i = P j`.

The main coefficient dispatcher is:

```text
endpoint_of_btrichotomy_cases :
  BTrichotomyEndpointCases -> normalized span datum -> endpt P <= endpt B
```

## Exact final surface

The endpoint dispatch theorem is:

```text
supportStuckWBS_endpoint_dispatch_final :
  BTrichotomyDispatchSurface -> SupportStuckWBSEndpointDispatch
```

where `BTrichotomyDispatchSurface` consists of exactly:

1. `SupportStuckWBSSpanSupply`: every raw `SupportStuckWBS` branch supplies a normalized `i+1<j`
   real-span witness with coefficients `a b`.
2. `OpenedWBSNoNonadjacentRepeatSupply`: the accepted opened-arm `NoNonadjacentRepeat` surface.
3. `BTrichotomyEndpointCases`, whose remaining consumers are:
   - `b < 0` tail endpoint after the successor-edge kill;
   - `b > 0, a > 0` boundary-fold endpoint;
   - `b > 0, a < 0` opposite-mid-fold endpoint.

The FFCT62 headline is plugged as:

```text
spherical_arm_mono_vNext_btrichotomy :
  BTrichotomyDispatchSurface -> strict endpoint monotonicity
```

## Honest status

This does not claim raw `SupportStuckWBS` already contains the span witness.  Existing FFCT56/59/61
data only cover the `b < 0` residue once that sign-bearing span datum has been supplied.  FFCT64
therefore exposes the raw span-supply bridge explicitly rather than hiding it inside the dispatch.

The parallel `ZinanFFCT63.lean` file exists locally and was not imported.  Its tail-ray / tail-fold
refinements can later shrink the `b < 0` tail endpoint surface, but this file intentionally keeps that
as a named input.
