# opus-openingprocess-reply — Chapter 13 §8.4 opening process (reach-or-stuck assembly)

Status: **headline `szStepGeom_holds : SZStepGeom` NOT delivered unconditionally.**  Genuine new
substrate built that **strictly narrows the residue's strict half to pure opening-witness existence**;
the irreducible residue (the multi-vertex opening *construction* + the weak monotone bound) is, verified
against the source, the substrate's already-named primitive `OpenedArmReachOrStuck` (≡ `OpeningData` ≡
`SZStepGeom`).  File: `ProofsInTheBook/SphericalOpeningProcess.lean` — compiles, RC=0, no
sorry/axiom/admit/native_decide, clean-3 on every new theorem.

## CORRECTION to the task premise (verified, not impression)

The task states "EVERY sub-ingredient is now proved; your job is the admissible-supremum opening
argument that assembles them," and that an `OpenedArmReachOrStuck` assembly exists.  Reading the source
line by line confirms the prior round's (`opus-diagcut-reply`) verdict: **no such assembly skeleton
exists, and the assembly is not mere wiring.**  Three sub-ingredients the design §8.4 needs are
genuinely absent from the entire substrate (verified by `grep`):

1. **Arbitrary-joint opening + the opening chain.**  `SphericalCore.openArm` opens only the **last**
   joint (about axis `A n`); there is no hinge at an arbitrary internal joint `k`, and no
   `spherical_SZ_opening_chain` (the design §8.4 finite sequence of HingeMoves `A → … → B`).
2. **The specific-support identification.**  `arm_reach_or_stuck` yields *some* vanishing mixed support
   `mixedSupport A (i,j) s = 0`, **not** the closing one `det3 (A 0)(A 1)(q*) = 0`; the stuck
   betweenness `A 0 ∈ span≥0 {A 1, q*}` requires that *specific* support to be the tight one with the
   §8.3 near-side orientation — the multi-vertex convex-position fact the engine does not mechanise.
3. **The reach-case recursion** on the number of unmatched joints (lex measure `(n, #unmatched)`).

The weak monotone bound `endpt A ≤ endpt B` in the all-joints-equal case additionally needs an arm
**congruence/reconstruction** lemma (equal sides + equal joints ⟹ equal endpoint), present only at
`n = 2` (`diagonal_eq_of_angle_eq`), absent for general `n`.

## What I PROVED (genuine new content, all clean-3 — strictly enlarges the substrate)

* **`tailArm` + full convexity transport** — the **first-vertex-drop** sub-arm `tailArm A := A ∘ Fin.succ`
  (keep `A 1, …, A (n+1)`), with `tailArm_endpt : endpt (tailArm A) = sDist (A 1) (A (last))` and the
  load-bearing `tailArm_strictConvexArm` / `tailArm_strictConvexPolygon` transporting ALL FOUR
  `StrictConvexSphPolygon` fields across `Fin.succ` (the closing backward diagonal `A (n+1) → A 1`
  handled via `cut_diagonal_supports` + cyclic `sOrient`).  This is the **endpoint-preserving** sub-arm
  `cut_endpt_transport` requires — `SphericalDiagCut.cutArm` drops the *last* vertex and loses the
  endpoint (`endpt (cutArm A) = sDist (A 0)(A n) ≠ endpt A`), the exact gap `opus-diagcut-reply` flagged.
  This dual was absent from the substrate; it is the stuck-case sub-arm `(A 1, …, A n, q*)`.
* **The `sOrient` ↔ oriented-tangent bridge** `inner_tangent_cross_eq_neg_sOrient`:
  `⟪tangentTo k a, k × tangentTo k b⟫ = -sOrient k a b` (since `k × tangentTo k b = k × b` and the
  `k`-component drops).  Hence `orientedSign_of_support_nonneg`: the §8.1 keystone's oriented-sign
  hypothesis `⟪…⟫ ≤ 0` is **exactly** the convex-position support sign `0 ≤ sOrient axis a0 tail` — so
  the keystone's hypothesis is discharged from convexity, not assumed.
* **The fully-assembled reach-case base monotonicity** `reach_endpoint_mono_of_support`
  (= keystone `openedAngle_ge_of_oriented` + sign bridge + `reach_base_endpoint_mono`): opening the base
  triangle about the axis with the convex-position support sign and within the great-semicircle range
  does not decrease the endpoint distance.
* **The stuck-case endpoint glue** `stuck_endpoint_strict` — the *entire* stuck reduction modulo `q*`:
  given the raw stuck data (collinearity, opening bound, tail sub-comparison, equal first side) it
  derives `endpt A < endpt B` via `szChain_stuck_nondegenerate`.
* **`szStep_strict_of_stuckWitness`** — the load-bearing reduction showing **the strict half of
  `SZStepGeom` is now reducible to the pure geometric existence of `q*`**: every endpoint inequality,
  the betweenness→distance conversion, the `tailArm` sub-arm reduction, and the IH glue are *proved*.

## The PRECISE residue (honest, after genuine assembly — ONE named Prop, non-vacuous, non-co-extensive)

`StuckWitnessExists` (file): the all-strict-case raw geometric output of the §8.4 opening — a moved tail
`q*` with `A 0 ∈ span≥0 {A 1, q*}`, `endpt A < sDist (A 0) q*`, the tail sub-comparison
`sDist (A 1) q* ≤ sDist (B 1)(B (last))`, and the equal first side — *or* the reached direct bound.
It is **strictly narrower** than `SZStepGeom`'s strict branch (it omits the weak bound and carries RAW
collinearity rather than the converted `endpt A < endpt B`, both *derived* by
`szStep_strict_of_stuckWitness`), so it is **not** a co-extensive re-wrapper.  Non-vacuity:
`stuckWitness_payload_satisfiable` (the membership is realised by every great-circle betweenness).

For the FULL `SZStepGeom` two things remain, and they are exactly the substrate's already-named
primitive `SphericalOpening.OpenedArmReachOrStuck` (≡ `OpeningData` ≡ `SZStepGeom`): (1) the geometric
**existence** of the opening witness (= `StuckWitnessExists`, the §8.4 "THE hard theorem" — arbitrary-
joint opening to the admissible supremum + specific-support identification + §8.3 near-side orientation
+ reach recursion), and (2) the **weak monotone bound** (the non-strict arm lemma / arm congruence).
I did **not** introduce a fresh co-extensive `Prop` for these; the headline `spherical_arm_mono` /
`_strict` remain conditional on the substrate's `OpenedArmReachOrStuck`, with their strict-endpoint
assembly now fully discharged by this module.

## Verification

* `lake env lean ProofsInTheBook/SphericalOpeningProcess.lean` → RC=0.
* `lake build ProofsInTheBook.SphericalOpeningProcess` → Build completed successfully (8437 jobs).
* `grep -nE '\bsorry\b|\badmit\b|^axiom |native_decide'` → 1 hit, inside the module doc comment prose;
  0 in code.
* `#print axioms` (rebuilt oleans) — clean-3 `[propext, Classical.choice, Quot.sound]` on
  `tailArm_strictConvexArm`, `tailArm_endpt`, `inner_tangent_cross_eq_neg_sOrient`,
  `reach_endpoint_mono_of_support`, `stuck_endpoint_strict`, `szStep_strict_of_stuckWitness`.

## Net effect on the chapter

The §8.4 opening process's *endpoint-inequality layer* is now fully assembled: the keystone's sign is
discharged from convex position, the endpoint-preserving first-vertex-drop sub-arm `tailArm` is built
with its complete convexity transport, the reach-case base monotonicity is assembled, and the stuck-case
endpoint glue reduces the strict half of `SZStepGeom` to the pure geometric *existence* of the opening
witness.  The arm lemma `spherical_arm_mono(_strict)` is therefore **not** yet unconditional: the honest
irreducible residue is the multi-vertex opening *construction* (`OpenedArmReachOrStuck` ≡
`StuckWitnessExists` + the weak/congruence bound) — the design §8.4 "THE hard theorem," consistent with
four prior expert rounds.  No vacuous coupling or co-extensive re-wrapper was banked; the genuine new
content is the four proved lemmas that strictly enlarge the substrate beneath the residue.
