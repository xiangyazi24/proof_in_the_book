# Ch13 collision structure report

Created `ProofsInTheBook/ZinanFFCT87.lean`.

## Landed structural facts

* `predFin`: cyclic predecessor on `Fin (n+1)`, used so the `r = 0` predecessor support is a wrap predecessor rather than a bogus natural subtraction.
* `collision_identicalZeroSupport_succ`: from `openedWBS A B k r = openedWBS A B k s`,
  `sOrient (A' s) (A' (s+1)) (A' r) = 0`, with `s+1` the cyclic `Fin` successor.
* `collision_identicalZeroSupport_predFin`: from the same collision,
  `sOrient (A' (predFin r)) (A' r) (A' s) = 0`.
* `collision_identicalZeroSupports`: packages the two zero-support readouts for the collision shape.
* `openedWBS_fixed_vertex` and `openedWBS_fixed_sDist`: the fixed prefix `p <= openingAxis k` is pointwise fixed, hence fixed-prefix distances are preserved.
* `openedWBS_tail_vertex`, `openedWBS_tail_sDist`, and `openedWBS_tail_sphAngle`: the post-axis tail is a common `rotS2 (A (openingAxis k)) (-(monitoredSupWBS A B k))` image, so tail distances and tail spherical angles are preserved by the existing rotation isometry lemmas.
* `openedWBS_zero_to_fixed_sDist`, `openedWBS_tail_to_last_sDist`, and `openedWBS_endpt_eq_sDist`: endpoint-facing corollaries for the fixed piece, rotated tail, and definition of `endpt`.
* `deleteLoopArm`: the loop-deleted arm `[0..r] ++ [s+1..n]`, typed as an arm with `n - (s-r)` edges.
* `deleteLoopArm_zero`, `deleteLoopArm_last_eq_last_of_collision`, `deleteLoopArm_endpt_eq_of_collision`: the deleted arm has the same first and last vertices as the original arm after the collision identifies `P r = P s`; therefore its endpoint equals the original endpoint.
* `deleteLoopOpenedWBS` and `deleteLoopOpenedWBS_endpt_eq`: the WBS-specialized deletion and endpoint preservation.
* `deleteLoopArm_glue_left_eq`, `deleteLoopArm_glue_right_eq_of_lt`, `deleteLoopArm_glue_edge_short`: in the non-wrap case `s < n`, the glue edge is exactly the original short edge `(P s, P (s+1))`.

## Residuals

`DeleteLoopGlueResidual` records the two convexity obligations that are not discharged by the structural deletion:

* the incoming glue-joint support
  `0 <= sOrient (Ahat (r-1)) (Ahat r) (Ahat (r+1))`;
* the new closed-arm wrap support family based at `(Ahat last, Ahat 0)`.

The proved glue edge is short, but these two support facts are not consequences of the collision equality plus inherited old edges alone. This is the exact Ahat-side obstruction for a future route to `WeakConvexSphArm Ahat`.

No `Bhat` or `SameSides Ahat Bhat` construction was attempted.

## Minimal loop case

When `s = r + 2`, the deleted loop removes the two vertices `r+1` and `s`, leaving the glue edge from the collision vertex `Ahat r = A' r = A' s` directly to `A' (s+1)` (cyclically, if `s = n`). The removed loop itself is the two-edge chain `A' r -> A' (r+1) -> A' s` plus the identified chord `A' s = A' r`, so it is a degenerate digon in the sense relevant here: two surviving old edges enclose a collapsed endpoint pair, not a new weak-convex polygonal ear.

## Verification

Commands run:

* `export PATH=$HOME/.elan/bin:$PATH && lake build ProofsInTheBook.ZinanFFCT86`
* `export PATH=$HOME/.elan/bin:$PATH && lake env lean ProofsInTheBook/ZinanFFCT87.lean`
* placeholder/unsafe keyword scan on `ProofsInTheBook/ZinanFFCT87.lean`

The build and Lean check pass. The new `#print axioms` guards report only `[propext, Classical.choice, Quot.sound]`.
