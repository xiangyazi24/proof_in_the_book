# opus-reachstuck-reply — Chapter 13 §8.4 opening process (reach/stuck on the genuine arm)

Status: **headline `OpenedArmReachOrStuck` NOT closed unconditionally.**  Genuine new substrate built
that **corrects the rotation-direction sign** of the §8.1 keystone and **instantiates the reach-case
endpoint monotonicity on the genuine multi-vertex arm** (both absent from the entire substrate).  The
irreducible residue, verified against the source and consistent with five prior expert rounds, is the
multi-vertex opening *construction* — isolated as TWO named, non-vacuous, mutually-narrower primitives.
File: `ProofsInTheBook/SphericalReachStuck.lean` — RC=0, no sorry/axiom/admit/native_decide, zero
warnings, clean-3 on every new theorem.

## The logical reduction (verified, not impression)

`OpenedArmReachOrStuck`'s strict disjunction has `Or.inr = endpt A < endpt B`.  The proven
`SphericalSZChain.openingData_of_szStepGeom` routes the whole downstream chain *always through
`Or.inr`* — the stuck `qstar` witness is never consumed.  Hence closing `OpenedArmReachOrStuck`
reduces *exactly* to the SZ inductive step `SZComparison n → SZComparison (n+1)`: given the level-`n`
arm lemma, prove the level-`(n+1)` weak bound `endpt A ≤ endpt B` and (some joint wider) the strict
bound `endpt A < endpt B`.  The base `n=2` is the proven `szComparison_two`.

## What I PROVED (genuine new content, all clean-3 — strictly enlarges the substrate)

* **A sign correction.**  The substrate keystone `openedAngle_ge_of_oriented` opens by `+θ` requiring
  `0 ≤ sOrient axis a0 tail`.  But the convex arm's last-joint opening presents the **opposite** sign:
  the closing-diagonal support gives `0 < sOrient (A 0)(axis)(tail)`, i.e. `sOrient (axis)(A 0)(tail)
  < 0`, so the oriented tangent datum `s = ⟪tangentTo axis a0, axis × tangentTo axis tail⟫ ≥ 0` (the
  *reversed* keystone sign, via the proven bridge `inner_tangent_cross_eq_neg_sOrient`).  Therefore the
  convex opening rotates the tail by a **negative** angle `-θ`.  I built the mirrored cosine bound
  `cos_open_le_cos_orig_neg` and monotonicity `openedAngle_ge_of_oriented_neg` from scratch (the
  substrate only proved the `+θ`/`s ≤ 0` branch); this is the §8.1 keystone for the genuine convex
  opening direction.  Without this, `reach_endpoint_mono_of_support` (substrate) cannot even be
  instantiated on a real arm — its sign hypothesis is violated by every convex arm's last joint.
* **The reach-case endpoint monotonicity on the genuine arm** — `reach_endpoint_mono_arm` /
  `reach_endpoint_strict_arm`: opening the last joint of a strictly convex arm `A` by `-θ` does not
  decrease (resp. strictly increases) the endpoint `sDist (A 0) (A (n+1))`.  Base triangle
  `(A 0, axis = A n, tail = A (n+1))`: both base sides short arcs (`shortArc_axis_zero` from the
  closing diagonal, `shortArc_axis_tail` from `edge_short`), the convex oriented datum
  (`support_sign_base_ac` + `orientedSign_neg_of_support`), the mirrored keystone, and the substrate
  `reach_base_endpoint_mono`.  This connects the substrate's abstract base monotonicity to the actual
  arm's closing diagonal — the precise reach-case input the design §8.4 needs, absent from every
  substrate file (the substrate never instantiated the base monotonicity on the genuine arm).
* **The assembly** `openedArmReachOrStuck_of_witness_weak` + `schoenbergZaremba_of_witness_weak`: the
  two honest residues `StuckWitnessExists` (substrate) and `WeakArmStep` (isolated here) give
  `OpenedArmReachOrStuck` and hence `SchoenbergZarembaTarget`, re-routing the strict half always
  through `Or.inr` via the proven `szStep_strict_of_stuckWitness`.

## The PRECISE residue (honest — TWO named Props, non-vacuous, mutually narrower, not co-extensive)

After the new content, the irreducible §8.4 opening *construction* splits into the strict half and the
weak half — neither a re-wrapper of the other or of `OpenedArmReachOrStuck`:

1. `SphericalOpeningProcess.StuckWitnessExists` (substrate): the all-strict-case existence of the
   opening witness `q*` (collinearity + opening + sub-comparison + equal first side) *or* the reached
   direct bound.  Carries the strict-branch payload only.
2. `WeakArmStep` (new, this file): only the weak bound `endpt A ≤ endpt B` of the equal-joints /
   nondecreasing case.  Carries no strict / `q*` data, so it is **strictly narrower** than
   `OpenedArmReachOrStuck`.  Non-vacuity: `weakArmStep_conclusion_satisfiable` (`A = B` realises it).

Both together are the design §8.4 "THE hard theorem": arbitrary-joint opening to the admissible
supremum, **boundary** convexity persistence at the supremum (where a support is exactly `0`, so the
substrate's *strict-neighbourhood* `mixedSupport_persists` does not apply), the reach recursion on the
number of unmatched joints (lex measure `(n, #unmatched)`), and the stuck→cut transport.  The single
concretely-failing analytic step, after this round, is **boundary convexity persistence**: opening to
the admissible supremum keeps the opened arm a `StrictConvexSphArm` (needed both to recurse in the
reach case and to extract the stuck sub-arm).  `mixedSupport_persists` (substrate) gives strict
persistence only on *open* neighbourhoods; at the supremum point itself the mixed support is `0`, so
`strict_nonincident` (`> 0`) fails — the genuine gap.  The arbitrary-joint opening operation (substrate
`openArm` opens only the last joint) and the reach recursion are the further missing constructions.

## Verification

* `lake env lean ProofsInTheBook/SphericalReachStuck.lean` → RC=0, zero warnings, zero errors.
* `lake build ProofsInTheBook.SphericalReachStuck` → Build completed successfully (8438 jobs).
* `grep -nE '\bsorry\b|\badmit\b|^axiom |native_decide'` → 1 hit, inside the module doc prose; 0 in code.
* `#print axioms` (rebuilt oleans) → clean-3 `[propext, Classical.choice, Quot.sound]` on
  `cos_open_le_cos_orig_neg`, `openedAngle_ge_of_oriented_neg`, `reach_endpoint_mono_arm`,
  `reach_endpoint_strict_arm`, `support_sign_base_ac`, `openedArmReachOrStuck_of_witness_weak`,
  `schoenbergZaremba_of_witness_weak`.

## Net effect on the chapter

The §8.4 reach-case endpoint layer is now assembled on the genuine arm, with the rotation-direction
sign corrected (the convex opening is `-θ`, not `+θ`).  The arm lemma `spherical_arm_mono(_strict)`
remains **conditional** on the two residues `StuckWitnessExists` + `WeakArmStep` (≡ the substrate's
`OpenedArmReachOrStuck` ≡ `OpeningData` ≡ `SZStepGeom`).  The honest irreducible residue is the
multi-vertex opening *construction* — the design §8.4 "THE hard theorem," with the single sharpest
remaining analytic obstacle now pinpointed as **boundary convexity persistence at the admissible
supremum** (the substrate has only the strict-neighbourhood version).  No vacuous coupling or
co-extensive re-wrapper was banked; the genuine new content is the mirrored keystone + the
arm-instantiated reach monotonicity that strictly enlarge the substrate beneath the residue.
