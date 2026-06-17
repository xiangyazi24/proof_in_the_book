# Ch13 Endpoint Audit Report (`ZinanFFCT58`)

## Verdict

`SphericalSpliceTransport.SpliceBodyDiagMono` is **false as stated**.

`ProofsInTheBook/ZinanFFCT58.lean` now contains a kernel-anchored `m = 3` counterexample:

* `Ab = [V0A, V1, V2, V3]`, `Bb = [V0B, V1, V2, V3]`, all explicit rational points on `S²`.
* `Ab` is weakly convex and `Bb` is strictly convex.
* The splice side satisfies `sideLen Ab 0 ≤ sideLen Bb 0`.
* The real sides match and the matched joints satisfy `JointLe Ab Bb` (in fact equality at both joints).
* The endpoint conclusion fails: `¬ (endpt Ab ≤ endpt Bb)`.

Formal theorem:

```lean
theorem spliceBodyDiagMono_false : ¬ SpliceBodyDiagMono
```

Consequently the FFCT57 route-(b) bundle is uninhabited:

```lean
theorem ch13Residues_uninhabited : ¬ Nonempty Ch13Residues
```

because `Ch13Residues` carries `hcore : SpliceBodyDiagMono`.

## Repair

`ZinanFFCT58.lean` repairs the route-(b) endpoint by removing the legacy splice residuals from the final route.

Removed from the repaired bundle:

* `SpliceBodyDiagMono`
* `SpliceStructuralData`

Added/rethreaded through the modern CUT route:

* `WeakPositiveCutReady`
* `SupportStuckWBS_CutReadyBridge`
* `FoldedFlatCutTransportPlus`

Formal repaired bundle:

```lean
structure Ch13ResiduesHonest : Prop where
  hwpc : WeakPositiveCutReady
  hbridge : SupportStuckWBS_CutReadyBridge
  hffct : FoldedFlatCutTransportPlus
```

Formal repaired endpoint:

```lean
theorem spherical_arm_mono_final_v2 (res : Ch13ResiduesHonest) ...
```

The proof mirrors the FFCT19/57 double-induction assembly:

* weak-entry vanishing support now goes through `res.hwpc` to `CutReadyPlus`, then `cut_step_from_stuckAtK_plus`;
* WBS support-stuck goes through `res.hbridge`, then `cut_step_from_stuckAtK_plus`;
* REACH uses the same deficit-drop recursion as FFCT57.

## Expanded Honest Surface

The formal bundle in this file is the immediate consumer surface. Expanded through the campaign reports, it corresponds to:

* FFCT49/51/56 WBS sign/normalization surface, including the surviving `NonAxisMixedBindingResidue` non-axis sign supply.
* FFCT53/54 folded-flat transport surface:
  `StrictDiagonalSupport`, `TailFoldBoundary`, and `NoNonadjacentRepeat`.
* The new weak-entry bridge `WeakPositiveCutReady`, replacing the false legacy splice body comparison on arbitrary weak-positive vanishing-support entries.

No repaired theorem assumes `SpliceBodyDiagMono` or `SpliceStructuralData`.

## Verification

Remote check performed on `uisai2`:

```bash
scp ProofsInTheBook/ZinanFFCT57.lean ProofsInTheBook/ZinanFFCT58.lean \
  uisai2:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake build ProofsInTheBook.ZinanFFCT57'
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT58.lean'
```

Result: `ZinanFFCT58.lean` compiles with 0 errors.

Main theorem axioms:

```text
spliceBodyDiagMono_false:        [propext, Classical.choice, Quot.sound]
ch13Residues_uninhabited:        [propext, Classical.choice, Quot.sound]
open_step_honest:                [propext, Classical.choice, Quot.sound]
szOpeningStepPlus_honest:        [propext, Classical.choice, Quot.sound]
spherical_arm_mono_final_v2:     [propext, Classical.choice, Quot.sound]
```

Text audit:

```bash
rg -n "\bsorry\b|\badmit\b|\baxiom\b|native_decide" ProofsInTheBook/ZinanFFCT58.lean
```

Only the header sentence naming the banned constructs matches; there are no proof placeholders, no new axioms, and no `native_decide`.
