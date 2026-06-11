# Ch13 CUT-replacement — bricks 1/2/4 report (ZinanFFCT48.lean)

**Status:** COMPILING, clean-3, zero errors. File: `ProofsInTheBook/ZinanFFCT48.lean` (~310 lines).
Both load-bearing theorems verified `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
No `sorry`/`axiom`/`admit`/`native_decide`. NOT committed.

## What landed

### Brick 1 — `CutReadyPlus` (§5)
The cut-ready datum. **Design wrote it as `structure ... : Prop where i j : ℕ` — this does NOT
compile**: a `Prop`-valued structure cannot generate data projections (`field must be a proof, but
it has type ℕ`). Landed instead as an **existential `def`**:
```
def CutReadyPlus {N} (A B : Fin (N+1) → S2) : Prop :=
  ∃ (i j : ℕ) (hsk : StuckAtKData A B i j),
    WeakConvexSphArm (intervalArm A (i+1) (j-(i+1)) _) ∧
    StrictConvexSphArm (intervalArm B (i+1) (j-(i+1)) _)
```
The `intervalArm` bound `(i+1)+(j-(i+1)) ≤ N` is discharged by `omega` from `hsk.hij1 : i+1<j` and
`hsk.hj : j≤N` (StuckAtKData's real fields). Consumers destruct via `obtain ⟨i,j,hsk,hAe,hBe⟩`.
Helpers: `cutReadyPlus_intro` (constructor for the bridge), `cutReadyPlus_yields_stuckData`
(non-vacuity guard).

### Brick 2 — `cut_step_from_stuckAtK_plus` (§4)
The CUT consumer, replacing `SphericalArmAssembly.cut_step`. Takes `FoldedFlatCutTransportPlus`
(named Prop residue), `hn : 2≤n`, `ih : ∀ m<n, MainPlus m`, weak-positive `A`, strict `B`, matched
sides/joints, and `CutReadyPlus A B`; produces `endpt A ≤ endpt B`. Chain:
`stuckAtK_betweenness` → betweenness; `stuckAtK_diag_le_plus` → diagonal inequality (ear comparison
via `MainPlus (j-(i+1))`, `j-(i+1) < n` by omega); both fed to `FoldedFlatCutTransportPlus`.
`SameSides`/`JointLe` unfold definitionally to the `∀ k` forms `stuckAtK_diag_le_plus` consumes
(`hsideAll`/`hangleAll`) — no conversion lemma needed.

### Brick 4 — `InteriorOpeningOutcomePlus` + `interiorOpeningOutcomePlus_of_bridge` (§5/§6)
- `InteriorOpeningOutcomePlus`: the outcome `def`, RIGHT disjunct upgraded from bare vanishing
  support to `WeakConvexSphArm A' ∧ CutReadyPlus A' B`.
- `interiorOpeningOutcomePlus_of_bridge (hbridge) : InteriorOpeningOutcomePlus` — mirrors
  `ZinanFFCT46.interiorOpeningOutcomeWBS` exactly (verbatim side/joint bookkeeping, REACH/BASE-stuck
  dispatch), but the SUPPORT-stuck branch calls the brick-3 bridge to emit `CutReadyPlus A' B`.
  The wrap residual is supplied **unconditionally** by `ZinanFFCT47.openedWrapShortArcAtSupWBS_holds`,
  so `hbridge` is the ONLY input.

## Real names found (quote-first)

- `StuckAtKData {N} (A B) (i j)` — `SphericalStuckGeneral`. Fields: `hij1 : i+1<j`, `hj : j≤N`,
  `hsupp`, `hsa`, `hα`, `hβ`, `hside`. (i, j are EXPLICIT index PARAMETERS, not fields — this is the
  pattern brick 1 had to follow.)
- `stuckAtK_betweenness (hij1) (hj) (hsk)` — `SphericalStuckGeneral`. Gives span≥0 membership.
- `stuckAtK_diag_le_plus (hij1) (hj) (hsk) (hMm : MainPlus (j-(i+1))) (hposA) (hAe) (hBe) (hsideAll)
  (hangleAll)` — `ZinanFFCT19` (NOT `SphericalStuckGeneral`; the design's name was right, the
  `_plus`/MainPlus variant is the one to use since it threads `PositiveJoints`). The non-plus
  `stuckAtK_diag_le` lives in `SphericalStuckGeneral` and needs plain `Main`.
- `FoldedFlatCutTransportPlus` — `ZinanFFCT18`, **a named `Prop` (def, UNPROVEN residue)**, carries
  the betweenness `hcol` explicitly. Binders: `n, 2≤n, (∀m<n,MainPlus m), A, B, hA, hApos, hB,
  hside, hangle, i, j, j≠i, j≠i+1, hi1, hj, span-membership, diag≤ → endpt A ≤ endpt B`.
- `intervalArm A a m hb` — `SphericalSZStepClose` (needed an explicit `open`).
- `interiorOpeningOutcomeWBS (hwrapres) : InteriorOpeningOutcome` — `ZinanFFCT46`. The proof brick 4
  mirrors. `openedWrapShortArcAtSupWBS_holds : OpenedWrapShortArcAtSupWBS` — `ZinanFFCT47`,
  unconditional, so the WBS outcome is now unconditional.
- WBS dispatch lemmas (all `ZinanFFCT45`/`46`): `shortArcs_of_strict`,
  `openedInteriorJoint_le_at_supWBS`, `jointAngle_openTail_eq_openedInterior`,
  `jointAngle_openTail_eq_of_ne`, `openTail_preserves_sides`, `glueWBS_clause_i`,
  `glueWBS_clause_ii`, `BaseStuckProgressWBS_holds`, `reachWBS_strictConvex`,
  `supportStuckWBS_weakConvex`, `deficitCount_openTail_reach_lt`, `supportConstraint_apply`
  (`SphericalMonitoredSup`, needed an explicit `open`).

## Remaining input surface (after this file)

1. **`SupportStuckWBS_CutReadyBridge`** (brick 3, sibling-owned ZinanFFCT49). Declared here as a
   named `def`/hypothesis in the design §6 shape, specialized to the WBS support-stuck context:
   ```
   ∀ {n A B} (hA hB) {k} (hka hkt hkdef),
     SupportStuckWBS A B k →
     WeakConvexSphArm (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) →
     SameSides (openTail …) B → JointLe (openTail …) B →
     CutReadyPlus (openTail …) B
   ```
   The sibling's `CutReadyPlus_of_supportStuckWBS` must produce exactly this. NOTE the design §6
   sketch used `openTailW`/`monitoredSupWB` (the WB variant); the WBS branch uses
   `openTail`/`monitoredSupWBS` — the bridge must match the WBS forms (this is what FFCT46 uses).
   If the sibling's bridge signature differs in argument order/implicitness, `interiorOpeningOutcomePlus_of_bridge`'s
   call site `hbridge hA hB hka hkt hkdef hstuck hweak hside' hangle'` may need realignment — but the
   `def` here pins the exact shape to target.

2. **`FoldedFlatCutTransportPlus`** — still an UNPROVEN named Prop residue (FFCT18). Threaded as a
   hypothesis through brick 2. This is the genuine remaining CUT-geometry residue (the body/splice
   glue), per design §13.

## NOT done (bricks 5/6 — file budget)
`open_step_plus` (§9) and `mainPlus_at_level_plus`/`spherical_arm_mono_final` (§11) NOT attempted —
bricks 1/2/4 landed solid + verified first. `open_step_plus` would chain brick 2 (CUT) with the
deficit IH (REACH) on `InteriorOpeningOutcomePlus`; the double strong induction follows
`ZinanFFCT19.mainPlus_at_level`/`mainPlus_all`'s banked shape. Recommend the strict-arm headline
(design §11, no WeakPositiveCutReady) as the honest target — `WeakPositiveCutReady` was NOT
manufactured.
