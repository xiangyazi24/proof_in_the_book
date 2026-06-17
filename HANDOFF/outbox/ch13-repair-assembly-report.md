# Ch13 repair assembly report — ZinanFFCT65

**File:** `ProofsInTheBook/ZinanFFCT65.lean` (new).  It imports `ZinanFFCT63` and `ZinanFFCT64`; it
does not edit `ZinanFFCT53`.

Verified on `uisai2`:

```text
scp ProofsInTheBook/ZinanFFCT65.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT65.lean
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT65.lean'
```

Result: 0 errors / 0 warnings.  All printed declarations are clean-3:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, new `axiom`, or `native_decide` was introduced.  No commit was made.

## Job 1 — corrected FFCTPlus assembly

Landed:

```text
StrictDiagonalInteriorCore
strictDiagonalSupport_of_interiorCore
intervalCerts_of_betweenness_and_interiorCore
foldedFlatCutTransportPlusForward_v2
foldedFlatCutTransportPlusNR_v2
foldedFlatCutTransportPlus_v2
```

`foldedFlatCutTransportPlusForward_v2` replays the FFCT53/54 forward assembly but replaces the old
free universal `htfb` with FFCT63's real `BoundaryTailRay` supplier in the actual `(0,n-1)` branch:

```text
tailFoldBoundary_supply_in_context hbtr ...
```

The `(0,n)` branch no longer takes an opaque global `hivl`: it builds the interval certificates in
place from the fold betweenness.  The B-side strict interval certificate uses FFCT63's shrink:

* if `n < 5` under `3 ≤ n`, the strict-interior range is empty;
* if `5 ≤ n`, the only remaining input is `StrictDiagonalInteriorCore`.

## Job 2 — b-trichotomy wiring

Landed raw span extraction:

```text
SupportStuckWBSVanishingSpanSeedSupply
supportStuckWBSSpanSupply_of_vanishingSeed
openedWBSNoNonadjacentRepeat_pass
```

The span proof uses the normalized vanishing `sOrient`, cyclically rotates it to
`det3 A'(i+1) A'j A'i = 0`, and applies FFCT25's `lin_indep_span_of_det3_zero`.  Independence is from
`distinctNormalized_of_noRepeat` plus the WBS open hemisphere (`hemisphere_nonAntipodal`).

Endpoint case wiring:

```text
BPosAPosFFCTPlusV2EndpointConsumer
BPosANegEndpointConsumer
BTrichotomyEndpointSurfaceV2
bneg_tail_closed_by_normalization
btrichotomyEndpointCases_of_v2
```

The normalized `b < 0` tail field in FFCT64 is arithmetically empty: `i+1<j` and `j<n+1` imply
`i+2<n+1`.  The two remaining FFCT64 endpoint consumers are named sharply:

* `BPosAPosFFCTPlusV2EndpointConsumer`: the missing adapter from the corrected FFCTPlus theorem to
  FFCT64's `b>0, a>0` endpoint signature.
* `BPosANegEndpointConsumer`: the still-open `b>0, a<0` edge-between-vertex endpoint case.

Tail mirror wrappers landed:

```text
TailJ0MirrorIHSupply
TailJ1MirrorDiagSupply
tailBoundary_j0_endpoint_transport_mirror_v2
tailBoundary_j1_endpoint_transport_mirror_v2
nonAxisTailBoundary_endpoint_transport_v2
```

`j=0` now gets the mirror interval certificates from `StrictDiagonalInteriorCore`, but still honestly
needs the dimension-IH supply for FFCT53's `(0,n)` close.  `j=1` gets `TailFoldBoundary` from
`BoundaryTailRay`; its remaining input is the mirrored diagonal inequality.

## Job 3 — consolidated headline

Landed:

```text
Ch13ConsolidatedSurface
btrichotomyDispatchSurface_of_consolidated
spherical_arm_mono_consolidated
```

Exact current surface of `Ch13ConsolidatedSurface`:

1. `BackwardFoldCase`
2. `StrictDiagonalInteriorCore`
3. `BoundaryTailRay`
4. `SupportStuckWBSVanishingSpanSeedSupply`
5. `OpenedWBSNoNonadjacentRepeatSupply`
6. `BTrichotomyEndpointSurfaceV2`
7. `TailJ0MirrorIHSupply`
8. `TailJ1MirrorDiagSupply`

The headline threads these into FFCT64's `BTrichotomyDispatchSurface` and then into
`spherical_arm_mono_vNext_btrichotomy`.

