# opus-szstep-reply — Chapter 13 inductive step `SZStepGeom`

Status: **TARGET NOT CLOSED.** `szStepGeom_holds : SZStepGeom` is NOT proved unconditionally.
Genuine sub-content banked; the irreducible residue is precisely isolated (3 named, satisfiable Props).
File: `ProofsInTheBook/SphericalSZStep.lean` (compiles, RC=0, no sorry/axiom/admit/native_decide).

## Verification

- `lake env lean ProofsInTheBook/SphericalSZStep.lean` → RC=0.
- `lake build ProofsInTheBook.SphericalSZStep` → Built (8434 jobs), Build completed successfully.
- `grep -nE '\bsorry\b|\badmit\b|^axiom |native_decide'` → only two hits, both inside doc comments
  (the prose "No sorry, axiom, admit"); zero in code.
- `#print axioms` (rebuilt oleans) — clean-3 on every proved theorem:
  - `reach_base_endpoint_mono`   : [propext, Classical.choice, Quot.sound]
  - `reach_base_endpoint_strict` : [propext, Classical.choice, Quot.sound]
  - `equalAngleCut_step`         : [propext, Classical.choice, Quot.sound]
  - `cyclicTriplePos_step`       : [propext, Classical.choice, Quot.sound]

## Honest correction to the task premise (verified against source, not impression)

The brief said the cut/stuck branch is "now UNCONDITIONAL" and "only the reach (opening) case remains".
That is **not** the actual Lean state. Verified by reading every spherical file:

- `SZStepGeom` (SphericalSZChain.lean:193) is **definitionally co-extensive** with the whole chain of
  isolated primitives `SZGeom` / `SZOpeningCore` / `OpenedArmReachOrStuck` / `OpeningData` /
  `HingeConvexPosition`. It is the ENTIRE §8.4 inductive step (reach + stuck + equal-angle cut), one
  `Prop` quantified over all inputs — all-or-nothing. Because `openingData_of_szStepGeom` always routes
  `Or.inr`, proving `SZStepGeom` is exactly proving the level reduction
  `SZComparison n → SZComparison (n+1)` — the heart of Cauchy's arm lemma.
- `cyclicTriplePos_unconditional` (PlanarConvexDiag) supplies only the convex-position **input**
  (diagonal positivity). There is **no** cut construction anywhere: `grep` confirms
  `convex_stuck_gives_cut`, `hinge_endpoint_mono`, `hinge_increases_joint`, `convex_hinge_open_small`,
  and any oriented `rotAbout_tangent_angle_add` / `oangle` are **absent** from all Spherical*.lean.
- Every "cut" arm lemma (`spherical_arm_mono_cut_unconditional`, `..._cut_holds`, `..._cut`) STILL
  takes `hcut : SZStepGeom` as a hypothesis — i.e. it is conditional on the very thing to prove, not a
  reusable cut. The substrate deliberately isolated `SZStepGeom` because it is the chapter's explicitly
  named single hardest layer (design §8.4, "THE hard theorem").

So the real work is the full §8.2–§8.5 (reach + convexity persistence + stuck/cut), not a reach-only
finish, and it cannot be assembled from the present substrate in this round.

## What is BANKED (genuine new, unconditional, clean-3)

1. `reach_base_endpoint_mono` / `reach_base_endpoint_strict` — design §8.2 `hinge_endpoint_mono` on the
   base triangle `(a0, axis, tail)`: opening about `axis` preserves the two base sides (`a0–axis` fixed;
   `axis–tail` by the axis-isometry, via `rotS2 axis θ axis = axis` + `sDist_rotS2`), and
   `spherical_hinge_mono`/`_strict` turn the base-angle increase into the endpoint increase. Reduced to
   the single hypothesis `sphAngle a0 axis tail ≤/< sphAngle a0 axis (rotS2 axis θ tail)`.
2. `equalAngleCut_step` — the equal-angle-cut endpoint transport for the step, from the unconditional
   `cut_endpt_transport` (consumes `SZComparison n`; cut-arm convexity = `cyclicTriplePos_unconditional`,
   diagonal length = `diag_len_eq`).
3. `cyclicTriplePos_step` — re-export of `cyclicTriplePos_unconditional`.

## The precise residue — 3 named, satisfiable obligations (verified blockers)

Stated in the file as `def ... : Prop` with non-vacuity witnesses; `SZStepGeom` is NOT re-wrapped into
them (the full assembly needs all three PLUS the IVT joint-matching `openedJointAngle_surjOn`
simultaneously — strictly more than any one, so no co-extensive impostor).

1. **`OpenedBaseAngleMono`** — opening about `axis` by admissible `θ ≥ 0` increases the base angle.
   The substrate gives only the cosine sinusoid `cos_openedJointAngle =
   (cos θ·⟪u,w⟫ + sin θ·⟪u, axis×w⟫)/‖·‖`; its monotonicity direction is fixed only by the **sign of
   `⟪tangentTo axis a0, axis × tangentTo axis tail⟫`** — the oriented datum the open-hemisphere convex
   position supplies but unoriented `sphAngle` discards. This is design §8.1's oriented additivity
   `rotAbout_tangent_angle_add`, explicitly "introduced ONLY inside the rotation module" — **absent**.
   Non-vacuity: `openedBaseAngleMono_base` (holds at θ=0).
2. **`OpenArmConvexPersist`** — `openArm A θ` stays `StrictConvexSphArm` while the mixed supports are
   ≥0. `arm_reach_or_stuck` constrains only the *mixed* family, not the full polygon (closing edges,
   `open_hemisphere`). Design §8.3 `convex_hinge_open_small` — **absent**.
   Non-vacuity: `openArmConvexPersist_base` (openArm A 0 = A).
3. **`StuckGivesCut`** — a vanishing non-incident support cuts the arm into two `StrictConvexSphArm`s
   (re-indexed `Fin` sub-families), new-edge supports = the unconditional `cyclicTriplePos`. Design §8.4
   `convex_stuck_gives_cut` — input unconditional, **cut construction unbuilt**.
   Non-vacuity: `stuckGivesCut_realisable`.

## Recommended next step

This is a multi-file analytic build, not a one-file finish. The cleanest first brick is residue 1
(`OpenedBaseAngleMono`): prove the oriented tangent-angle additivity inside the rotation module using
`inner_rot_tangent` + the open-hemisphere `sOrient` sign to pin `⟪u, axis×w⟫ ≥ 0`, giving
`cos (opened) ≤ cos (orig)` on the admissible θ-range, hence the angle inequality `reach_base_endpoint_*`
already consume. Then residue 2 (continuity persistence of finitely many strict `sOrient` inequalities),
then residue 3 (the `Fin`-subfamily cut + IH glue via the now-available `cut_endpt_transport`). Each is
self-contained and bankable; only their conjunction (with `openedJointAngle_surjOn`) closes `SZStepGeom`.
