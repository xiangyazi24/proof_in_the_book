# opus-armfinal-reply — Chapter 13 §8.4–§8.5 final assembly (spherical arm lemma)

Status: **`spherical_arm_mono(_strict)` is NOT made fully unconditional.**  One of the two named
residues is **discharged** (`BoundaryConvexPersist` PROVED), the §8.3 hemisphere obstacle the prior
round (`opus-armclose`) isolated is **closed** via the requested upstream augmentation, and the
headline now hangs on a **single** residue: `OpeningStructuralAssembly` (the §8.4 multi-vertex opening
*construction* — the design's "THE hard theorem"), which I confirm is genuinely irreducible without
substantial new multi-vertex geometry that does not exist in the substrate.

Files: edited `ProofsInTheBook/SphericalAdmissibleSup.lean` (hemisphere augmentation), created
`ProofsInTheBook/SphericalArmFinal.lean` (final assembly).  `SphericalArmClose.lean` also gained one
proved theorem (`boundaryConvexPersist`).  RC=0 throughout; no sorry/axiom/admit/native_decide; clean-3.

## What I BANKED (genuine new content, UNCONDITIONAL, clean-3)

1. **`BoundaryConvexPersist` — PROVED** (`SphericalArmClose.boundaryConvexPersist`, re-exported as
   `SphericalArmFinal.boundaryConvexPersist`).  The corrected, interval-true boundary persistence
   (hypothesis = strict convexity on all of `[0,δ]`, `δ ∈ [0,δ]`) holds outright; the genuine analytic
   realisability is the unconditional `openArm_strictConvex_nhds` (the prior round's full §8.3
   persistence).  This discharges residue (1) of `opus-armclose-reply.md`.

2. **The §8.3 hemisphere obstacle is CLOSED (the requested upstream edit).**  Per spec, I edited
   `SphericalAdmissibleSup.lean` to **add the `open_hemisphere` functional at the rotated tail** to the
   monitored admissible family:
   - `hemiMargin A h := fun θ => ⟪h, rot (openAxis A) θ (A last)⟫`, `continuous_hemiMargin`,
     `hemiMargin_zero`;
   - `augmentedSupport A T h : Option (Fin _ × Fin _) ⊕ Unit → ℝ → ℝ` — the combined family
     (`inl o`) plus the hemisphere margin (`inr ()`); `continuous_augmentedSupport`,
     `sSup_augmented_mem`, `augmented_reach_or_stuck`;
   - `augmented_reachOrStuck_at_sup` — the §8.4 trichotomy now surfacing a vanishing **hemisphere
     margin** in the STUCK branch (`… ∨ (∃ ij, mixedSupport = 0) ∨ hemiMargin = 0`), the constraint
     `combinedSupport` was blind to;
   - **`reach_strictConvex_at_sup`** — the payoff: in the REACH branch (no support/hemisphere tight),
     given strict opened-arm data (`hedge`/`hmix`/`hhem` + unit `h`), `openArm A δ*` is a genuine
     `StrictConvexSphArm`.  This is the substrate's unsound `BoundaryConvexPersistAtSup`, now **true
     and proved** on the branch where it holds — the §8.3→§8.4 boundary gap is closed.

   Reassembled in `SphericalArmFinal.reachBoundaryConvex_of_strictData`.  Non-vacuity verified: the
   hypotheses of `reach_strictConvex_at_sup` are jointly satisfiable (realised at `δ = 0`, where
   `openArm A 0 = A`; checked by a scratch `example`, RC=0).

3. **The arm lemma, conditional only on `OpeningStructuralAssembly`**
   (`spherical_arm_mono_final`/`_strict_final`, `schoenbergZaremba_of_opening`).  Because
   `BoundaryConvexPersist` is now proved, the two-hypothesis conditional lemmas of `SphericalArmClose`
   collapse to a **single** hypothesis.

## The SINGLE remaining residue (honest — ONE named non-vacuous Prop + concrete failing chain)

`SphericalArmClose.OpeningStructuralAssembly := BoundaryConvexPersist → StuckWitnessExists ∧
WeakArmStep`.  Since `BoundaryConvexPersist` is now trivially true, this is operationally
`StuckWitnessExists ∧ WeakArmStep` — the design `CH13_CAUCHY_FULL_DESIGN` §8.4 "THE hard theorem"
(`spherical_SZ_opening_chain`).  **Concrete failing chain (verified by `grep` against the substrate):**

1. **Arbitrary-joint opening unavailable.**  `openArm` opens only the *last* joint; the §8.4 step opens
   the (generically interior) joint where `B` is strictly wider.  Relabelling needs a
   `StrictConvexSphArm`-preserving arm reflection/cyclic relabelling that also preserves all sides and
   joint angles — **no such lemma exists** (only the single-field `open_hemisphere_reindex`; no
   five-field `StrictConvexSphArm` reindexing).
2. **Reach recursion unmechanised.**  Case 1 opens until `jointAngle A' k = jointAngle B k`, reducing
   `#unmatched` on the lex measure `(n, #unmatched)`.  The boundary convexity at `δ*` is now available
   (`reach_strictConvex_at_sup`), but the well-founded `#unmatched` recursion + construction of the
   matched arm `A'` is absent.
3. **Matched-data cut has no `B`-side construction.**  Case 2 yields the `A`-side diagonal cut
   (`diagonalCutArm_holds`, present), but `cut_endpt_transport` needs the *matching* `B`-side cut with
   equal sides/nondecreasing joints — **no `B`-side cut construction exists** (only `A`-side `cutArm`).

This residue is genuinely the chapter frontier (design doc: discharging it = implementing §8.4; five
prior expert rounds isolated it as irreducible).  I did **not** fabricate it.  Non-vacuity:
`OpeningStructuralAssembly`'s hypothesis is *proved* (`boundaryConvexPersist`); its target
`StuckWitnessExists ∧ WeakArmStep` is the pair of substrate residues, each satisfiable
(`openingStructuralAssembly_target_satisfiable`) — not a vacuous-hypothesis impostor.

## Verification

* `lake build ProofsInTheBook.SphericalArmFinal` → **Build completed successfully (8441 jobs).**
  Rebuilds `SphericalAdmissibleSup` (edited) + `SphericalArmClose` + `SphericalArmFinal` on the
  unchanged substrate oleans.  `SphericalAdmissibleSup` still builds clean after the edit (its only
  downstream consumers, `SphericalArmClose`/`SphericalArmFinal`, both rebuilt; `grep` confirms no other
  importer).
* `grep -nE '\bsorry\b|\badmit\b|^axiom |native_decide'` over the three files → only module-doc prose
  hits (the literal sentence "No `sorry`, `axiom`, ..."); **0 in code**.  No `:= rfl`/`:= trivial`/
  `_placeholder_`.
* `#print axioms` (rebuilt oleans) → **clean-3 `[propext, Classical.choice, Quot.sound]`** on
  `boundaryConvexPersist` (both `SphericalArmClose` and `SphericalArmFinal`), `reach_strictConvex_at_sup`,
  `augmented_reachOrStuck_at_sup`, `reachBoundaryConvex_of_strictData`, `spherical_arm_mono_final`,
  `spherical_arm_mono_strict_final`.  (The `_final` lemmas remain conditional on the
  `OpeningStructuralAssembly` *hypothesis parameter* — axioms clean, statement honestly conditional.)

## Honest verdict

FRAGMENT (toward FAITHFUL).  The headline `spherical_arm_mono(_strict)` is **NOT** unconditional.
Net progress over `opus-armclose`: residue (1) `BoundaryConvexPersist` is **proved**; the §8.3
hemisphere boundary obstacle is **closed** by the requested admissible-family augmentation
(`reach_strictConvex_at_sup`, REACH-case strict convexity at `δ*`).  The chapter frontier is now a
**single** residue — `OpeningStructuralAssembly`, the §8.4 multi-vertex opening *construction*
(arbitrary-joint opening + `#unmatched` reach recursion + `B`-side matched cut), each leg with a
concrete missing-substrate-lemma certificate above.  No vacuous coupling or co-extensive re-wrapper
banked.
