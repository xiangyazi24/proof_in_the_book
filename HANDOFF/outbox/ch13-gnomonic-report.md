# Ch13 gnomonic simplicity report

File added: `ProofsInTheBook/ZinanFFCT92.lean`.

## Status

The full unconditional theorem

```lean
WeakConvexSphArm P ->
PositiveJoints P ->
(∀ i : Fin (n - 1), jointAngle P i < Real.pi) ->
NoNonadjacentRepeat P
```

did not close in this pass.  The work landed the gnomonic reduction without
using `ZinanFFCT91.FaceContiguityPropagation` and isolated the remaining
purely planar closed-chain no-repeat theorem as:

```lean
PlanarClosedWeakStrictNoRepeat
```

This planar core is stronger and more directly targeted than the rejected
face-contiguity surface: it speaks only about the gnomonic planar image, cyclic
weak edge supports, nonzero cyclic edges, and strict non-wrapping interior
turns.

## Landed in `ZinanFFCT92`

* `gproj_eq_imp_eq` and `gproj_eq_iff_eq`: gnomonic projection is injective on a
  fixed open hemisphere.
* `gproj_ne_of_short`: short spherical edges project to nonzero planar edges.
* `consecutive_sOrient_pos`: weak convexity plus `PositiveJoints` and
  `jointAngle < pi` force every consecutive interior spherical orientation to
  be strictly positive.
* `gnomonic_consecutive_turn_pos`: the same strict turn transported to the
  gnomonic plane.
* `weakConvex_boundedJoints_noNonadjacentRepeat_of_planarClosed`: the requested
  no-repeat theorem follows from `PlanarClosedWeakStrictNoRepeat`.
* `boundedWeakPositiveSimplicity_of_planarClosed`,
  `crossPieceCollisionEndpointAtSup_of_planarClosed`, and
  `spherical_arm_mono_ch13_of_planarClosed`: FFCT89/Ch13 downstream wrappers
  from the planar core.

## Remaining planar core

`PlanarClosedWeakStrictNoRepeat` states:

* `f : Fin (n+1) -> E3` lies in one affine plane `⟪h, f i⟫ = 1`;
* every cyclic edge weakly supports every vertex;
* every cyclic edge is nonzero;
* every non-wrapping interior consecutive turn is strict;
* then no two nonadjacent vertices repeat.

This is the exact point where the gnomonic route now stops.

## Verification

Commands run:

```bash
export PATH=$HOME/.elan/bin:$PATH
lake build ProofsInTheBook.ZinanFFCT91
lake env lean ProofsInTheBook/ZinanFFCT92.lean
```

Both completed successfully.  The `ZinanFFCT91` build emits existing upstream
warnings and audit info; `ZinanFFCT92.lean` itself checks without errors.
