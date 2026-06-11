# Ch13 two-core discharge report

File delivered: `ProofsInTheBook/ZinanFFCT66.lean`.

## Core 1: Strict diagonal support

Closed.

New supplied statements:

- `strictDiagonal_arcInterior_of_cyclicTriple`
- `StrictDiagonalInteriorSupport_holds`
- `StrictDiagonalSupport_wrap_holds`
- `StrictDiagonalInteriorCore_holds`

Route: `PlanarConvexDiag.cyclicTriplePos_unconditional` on the increasing triple
`1 < 1+v < n`, followed by cyclic rotation of `sOrient` to the wrap diagonal orientation
`(B n, B 1, B (1+v))`.

This removes FFCT65's `StrictDiagonalInteriorCore` field.

## Core 2: Tail ray membership

Closed in the actual comparison context.

New supplied statements:

- `tail_rayMembership_of_coeff_signs`
- `TailRayMembership_holds_context`
- `TailFoldBoundary_holds_context`

Route: for the `(0,n-1)` fold, extract `A0 = a*A1 + b*A(n-1)` with `a,b > 0`; use the `A2` witness
and the non-flat comparison bound (`StrictConvexSphArm B`, `JointLe A B`) to get the strict witness
orientation; use weak supports of `(n-1,n)` and `(n,0)` at `A2` to prove the two real coefficient
signs; convert those signs into

```lean
(A (Fin.last n) : E3) ∈
  Submodule.span NNReal ({(A 0 : E3), (A ⟨n-1⟩ : E3)} : Set E3)
```

Then `tailFoldBoundary_of_rayMembership` gives the metric tail boundary.  The `n = 3` case is killed
by `foldedFlat_adjacent_contradiction`.

Important interface note: the old FFCT63 field `BoundaryTailRay` is too weak as a standalone theorem:
it does not include the comparison-arm non-flat upper bound needed to rule out the `jointAngle = pi`
case in the `A2` witness proof.  FFCT66 therefore wires the tail proof directly into the forward
transport where `hB` and `hangle` are actually in scope.

## Final wiring

New supplied statements:

- `foldedFlatCutTransportPlusForward_v3`
- `foldedFlatCutTransportPlusNR_v3`
- `btrichotomyDispatchSurface_of_consolidated66`
- `spherical_arm_mono_consolidated66`

Final headline:

```lean
theorem spherical_arm_mono_consolidated66 (res : Ch13ConsolidatedSurface66)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n))
```

Exact remaining surface in `Ch13ConsolidatedSurface66`:

- `hback : BackwardFoldCase`
- `hspanSeed : SupportStuckWBSVanishingSpanSeedSupply`
- `hnorepeat : OpenedWBSNoNonadjacentRepeatSupply`
- `hendpoint : BTrichotomyEndpointSurfaceV2`

Expanding `hendpoint`, the endpoint consumers still retained are:

- `bpos_apos : BPosAPosFFCTPlusV2EndpointConsumer`
- `bpos_aneg : BPosANegEndpointConsumer`

Removed from FFCT65's surface:

- `hdiagCore : StrictDiagonalInteriorCore`
- `hbtr : BoundaryTailRay`
- the unused `hj0ih` / `hj1diag` fields are not part of the FFCT66 headline surface.

## Verification

Remote verification on `uisai2`:

```bash
cd ~/repos/proof_in_the_book
~/.elan/bin/lake build ProofsInTheBook.ZinanFFCT65
~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT66.lean
~/.elan/bin/lake build ProofsInTheBook.ZinanFFCT66
```

All completed successfully.  `#print axioms` for the new FFCT66 theorems reports only the standard
Lean/Mathlib foundations: `propext`, `Classical.choice`, and `Quot.sound`.
