# Ch13 FINAL ENDPOINT — the chapter's public honest state (`ZinanFFCT57`)

**File:** `ProofsInTheBook/ZinanFFCT57.lean` (NEW, single-writer; imports only `ZinanFFCT48` +
`ZinanFFCT56`). 433 lines. **Status:** 0 errors, 0 warnings, clean-3 on all 7 `#print axioms`
(`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no custom `axiom`, no `native_decide`).
No `sorry`/`admit`/`axiom`/`native_decide`. NOT committed.

**Verify:**
```
scp ProofsInTheBook/ZinanFFCT57.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ \
  && ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT57.lean'
```
(The full build `fb8.log` reported `Build completed successfully (8766 jobs)` first; all FFCT37–56
oleans are clean-3.)

## The verified logical spine

The **double induction is already closed upstream** in FFCT19: `spherical_arm_mono_of_stepPlus` proves the
strict-arm headline conditional only on the per-step predicate `SZOpeningStepPlus`, via
`mainPlus_all` (outer strong induction on `n`) ∘ `mainPlus_at_level` (inner strong induction on
`deficitCount`) — FFCT48's `ihdef` skeleton. So the entire remaining content was the **per-step**
`SZOpeningStepPlus` (the FFCT48 brick 5/6 the cut-ready report left to the assembly wave). FFCT57 lands it.

Per-step assembly (`szOpeningStepPlus_of_residues`, mirroring `interiorOpenAndSpliceStep_of_inputs`):
a weak `PositiveJoints` entry `A` splits (`strict_or_vanishing`) into the weak-entry vanishing CUT
(substrate `cut_step`, mod the splice residues) or strict; strict + `deficitCount = 0` ⟹ congruence;
strict + deficient joint ⟹ `open_step_wbs_final`.

The OPEN step (`open_step_wbs_final`) **inlines** the WBS opening `A' = openTail A (openingAxis k)
(-(monitoredSupWBS A B k))` (instead of the opaque-`A'` `interiorOpeningOutcomePlus_of_bridge`), so `A'`
is concrete and its `PositiveJoints A'` is the genuine FFCT46 `openedJoints_in_Ioo_at_supWBS.1` — **not a
fabricated field** (a soundness gap caught: `StuckAtKData` has NO `hpos` field, so the positivity the CUT
consumer needs had to come from the WBS opened-arm joint positivity, not the cut datum). It dispatches:
REACH (`¬ SupportStuckWBS` + base-stuck collapse) ⟹ inner deficit IH; CUT (`SupportStuckWBS`) ⟹
`res.hbridge` builds `CutReadyPlus A' B`, then `cut_step_from_stuckAtK_plus res.hffct`.

## The (a) vs (b) status

### (b) — `spherical_arm_mono_final_honest` (the unconditional-so-far headline) — LANDED, clean-3

```
spherical_arm_mono_final_honest (res : Ch13Residues) {n} (hn : 2 ≤ n) (A B) (hA hB : StrictConvexSphArm)
    (hside : ∀ i, sideLen A i = sideLen B i) (hangle : ∀ i, jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n))
```
The strict-arm chord-endpoint monotonicity, modulo the surviving residue bundle `Ch13Residues`. Pure
assembly: `szOpeningStepPlus_of_residues res` ∘ FFCT19 `spherical_arm_mono_of_stepPlus`.

### (a) — `mainPlus_of_supportStuckImpossible` (the REACH-only route) — LANDED, clean-3, CONDITIONAL

```
mainPlus_of_supportStuckImpossible (helim : SupportStuckWBSImpossible)
    (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData) {n} (hn : 2 ≤ n) (A B) (hA hB) … :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n))
```
**Soundness verified.** Under `SupportStuckWBSImpossible` (the FFCT56 elimination input, carried
EXPLICITLY — axis-edge eliminated in-campaign by `wbs_axisEdge_supportStuck_false`, residual exactly
`NonAxisMixedBindingResidue`), the WBS trichotomy (`glueWBS_clause_ii` + `BaseStuckProgressWBS_holds`)
forces **REACH always** (`reachOnly_outcome`: support-stuck excluded ⟹ strict `A'` + deficit drop every
OPEN step). The CUT branch never fires — **`FoldedFlatCutTransportPlus` and the bridge
`SupportStuckWBS_CutReadyBridge` are GONE**. The only OPEN-side residue vanishes; the cut machinery
(FFCT48–54) is unused. The (a)-route's "REACH always" promise is **NOT** stated as an unconditional
theorem: `helim` is carried explicitly (honesty contract), since its non-axis residue is open.

The weak-entry vanishing CUT (the bare vanishing-support path, distinct from the OPEN-produced stuck arm)
still consumes the substrate splice residues `SpliceBodyDiagMono` + `SpliceStructuralData` in BOTH routes
— it is the `strict_or_vanishing` left branch, not part of the WBS opening.

## The EXACT final input surface (the chapter's "mod" list, for the audit wave)

**Route (b)** `spherical_arm_mono_final_honest` is mod `Ch13Residues` (a `structure ... : Prop`):

| conjunct | type | FFCT origin | discharge route / residual |
|---|---|---|---|
| `hbridge` | `SupportStuckWBS_CutReadyBridge` | FFCT48 §3 / FFCT49 `cutReadyData_of_supportStuckWBS` | mod `WBSGramSigns` ⟶ `WBSBetaSign` + `¬ NearSidePredDegenerate` (FFCT49/51/55); sign supply = FFCT56 `NonAxisMixedBindingResidue` |
| `hffct` | `FoldedFlatCutTransportPlus` | FFCT18; → `FoldedFlatCutTransportPlusNR` (FFCT53/54) | mod `StrictDiagonalSupport` + `TailFoldBoundary` + `BackwardFoldCase` (consumer-excluded) + `NoNonadjacentRepeat` |
| `hcore` | `SpliceBodyDiagMono` | SphericalArmAssembly / FFCT38-era | weak-entry CUT; substrate splice geometry |
| `hstruct` | `SpliceStructuralData` | SphericalArmAssembly | weak-entry CUT; §8.4 sub-arm convexity preservation |

**Route (a)** `mainPlus_of_supportStuckImpossible` is mod **`SupportStuckWBSImpossible` + `SpliceBodyDiagMono`
+ `SpliceStructuralData`** ONLY (no `hbridge`, no `hffct`). `SupportStuckWBSImpossible := ∀ A B (strict)
k, jointAngle A k < jointAngle B k → ¬ SupportStuckWBS A B k` — the FFCT56 elimination's honest endpoint;
its remaining residual is exactly `NonAxisMixedBindingResidue` (axis-edge already done).

So the two routes share `{SpliceBodyDiagMono, SpliceStructuralData}` (the weak-entry CUT, untouched by the
WBS work); (a) trades `{hbridge, hffct}` for the single elimination input `SupportStuckWBSImpossible`. Per
WBS support-stuck binding, the disjunctive consumer needs **only one** of {sign-eliminate (a),
cut-transport (b)}.

## Per-step + helper theorems landed (all clean-3)

`open_step_wbs_final`, `szOpeningStepPlus_of_residues`, `reachOnly_outcome`, `open_step_reachOnly`,
`szOpeningStepPlus_of_elimination`. Non-vacuity guards: `spherical_arm_mono_final_honest_conclusion_satisfiable`
(genuine `sDist ≤ sDist`, reflexive at `A=B`), `supportStuckWBSImpossible_is_real` (the elimination input
unfolds to the genuine `¬ ∃ c, supportConstraint … = 0`, a failable predicate — not vacuous),
`ch13Residues_cut_conclusion_satisfiable`.

## Honesty audit (playbook §3.3)

- **No vacuous statement.** Both headlines conclude a real `sDist ≤ sDist` chord bound; the (a) premise
  `SupportStuckWBSImpossible` is the genuine negation of FFCT45's `SupportStuckWBS` (refutable), carried
  explicitly. The "REACH always" promise is gated behind `helim`, never asserted unconditionally.
- **Soundness gap caught + fixed honestly.** The CUT consumer's `PositiveJoints A'` is NOT a `StuckAtKData`
  field (verified: `StuckAtKData` has fields `hij1/hj/hsupp/hsa/hα/hβ/hside` only); it is supplied from the
  concrete WBS opened arm's joint positivity (`openedJoints_in_Ioo_at_supWBS`), which forced the inline of
  the WBS opening rather than the opaque-`A'` outcome.
- **No upstream file weakened** (single-writer; FFCT57 only adds). All inputs trace to committed FFCT files.
