# Ch13 FFCTPlus discharge — report (ZinanFFCT53)

**File:** `ProofsInTheBook/ZinanFFCT53.lean` (NEW; imports only `ZinanFFCT25` + `ZinanFFCT48`).
**Status:** compiles 0 errors / 0 warnings; all 6 headline results clean-3
(`[propext, Classical.choice, Quot.sound]` only — no `sorryAx`, no custom axiom, no `native_decide`).
**Verify:** `scp … uisai2 && ssh uisai2 'lake env lean ProofsInTheBook/ZinanFFCT53.lean'`.

## What closed UNCONDITIONALLY (real math, axiom-free)

1. **`FoldedFlatCutTransportPlusNR`** — the honest `NR`-threaded residue (def): as
   `ZinanFFCT18.FoldedFlatCutTransportPlus` but with `NoNonadjacentRepeat A` threaded (the FFCT25
   boundary classification needs it; the original NR-free Prop is unreachable from FFCT25, design §4).

2. **`foldedFlat_adjacent_contradiction`** (Brick 2) — the `j = i + 2` adjacent fold forces the
   interior joint at index `i` to `0` (`ZinanFFCT19.lastCorner_hcol_forces_joint_zero` + the reversed
   short edge), contradicting `PositiveJoints A`. Fully discharged.

3. **`foldedFlat_boundary_j_eq_n`** (Brick 3, the `(0,n)` close) — design §7 chain, fully discharged:
   betweenness additivity (`sDist_betweenness_of_collinear`, which needs ONLY the NNReal span
   membership — no hemisphere input) + interval-arm `[1..n]` IH (`ear_chord_le_of_MainPlus` at
   `a=1, m=n-1`, `MainPlus (n-1)` from the dim IH) + `SameSides` first edge + reverse triangle on B +
   `linarith`. The interval-convexity certs are taken as named inputs (see below).

4. **`foldedFlat_boundary_j_eq_n_minus_one`** (Brick 5, the `(0,n-1)` close) — design §8: from the
   named tail-fold premise + the diagonal inequality + the equal last side (`SameSides` at `n-1`),
   `ZinanFFCT18.endpoint_le_of_tail_fold` closes it. Fully discharged **modulo** `TailFoldBoundary`.

5. **`foldedFlatCutTransportPlusNR_holds`** (Brick 6, the assembly) — orientation trichotomy on the cut
   indices: `j < i` → `BackwardFoldCase`; `j = i` excluded; forward `i < j` splits `j = i+2` (the §3
   contradiction) vs `i + 2 < j` (FFCT23 `far_fold_nondeg_datum_of_no_repeat` + FFCT25
   `far_fold_boundary_classification_final` → `i = 0 ∧ (j = n ∨ j = n-1)`, routed to §4 / §5).

6. **`foldedFlatCutTransportPlus_of_NR`** (Brick 7, the bridge) — recovers the original
   `ZinanFFCT18.FoldedFlatCutTransportPlus` (the Prop `cut_step_from_stuckAtK_plus` consumes) by
   supplying `NoNonadjacentRepeat A` for the quantified left arm. Honest plug: the original NR-free
   Prop is NOT reachable from FFCT25 (design §4 warning); the NR supply is the documented honest cost.

## Key structural finding (cleaner than the design anticipated)

The **only** consumer of `FoldedFlatCutTransportPlus` is `ZinanFFCT48.cut_step_from_stuckAtK_plus`,
which cuts at a `StuckAtKData A B i j` whose field **`hij1 : i + 1 < j` fixes the forward
orientation** (and `j ≠ i`, `j ≠ i+1` are derived there). So the backward `j < i` binding NEVER fires
at the real consumer; the entire forward case (`i + 1 < j` = adjacent ∪ far) is discharged here in
full. The design's worried-about j<i case is purely a tax of the *general* Prop shape.

## Surviving named inputs (honest, satisfiable, NOT faked)

* **`BackwardFoldCase`** — the `j < i` orientation. Never reached by the forward `StuckAtKData`
  consumer; FFCT52's reversed-arm suite (`revArm`/`revArm_sideLen`/`revArm_jointAngle`, `det3`
  antisymmetry) is the intended sibling-owned discharge (NOT imported, per the no-shared-file rule).
  Stated with the exact backward binder shape; non-vacuity guard provided.

* **`TailFoldBoundary A`** — the `(0,n-1)` tail-fold premise
  `sDist (A 0)(A⟨n-1⟩) = endpt A + sDist (A last)(A⟨n-1⟩)` (last vertex folded onto the ray). This is
  the design §8 "master, 250-450 lines" residue: the `(0,n-1)` betweenness in hand
  (`A 0 ∈ span≥0 {A 1, A⟨n-1⟩}`) does NOT yield it — forcing the last vertex onto the folded ray needs
  the two boundary edge supports + the positive-coeff fold datum, genuinely beyond the betweenness.
  Exposed honestly; `tailFoldBoundary_is_betweenness` witnesses it as a real betweenness constraint.

* **`hivl` (interval `[1..n]` convexity certs)** for the `(0,n)` branch — there is NO unconditional
  interval-convexity producer in the substrate (the ear's closure adds a *diagonal* wrap edge;
  `SphericalSZStepClose §R`, FFCT52 §4; every consumer — CutTransport/StuckGeneral/FFCT49 — carries
  `hAe`/`hBe` as data). Carried as the named hypothesis in exactly that established shape.

* **`hsupply` (NR supply)** in the bridge — `NoNonadjacentRepeat A` for the left arm; satisfiable on
  strict/injective arms (FFCT23 `noNonadjacentRepeat_of_injective`); the documented honest cost of the
  FFCT25 route.

## Non-vacuity guards (playbook §3.3)

`backwardFoldCase_conclusion_satisfiable`, `tailFoldBoundary_is_betweenness`,
`foldedFlatCutTransportPlusNR_conclusion_satisfiable`, `foldedFlat_boundary_betweenness_inhabited`,
`foldedFlat_adjacent_premises_satisfiable` — every new Prop carries a refutation/inhabitation guard.

## Not done / out of scope (by the one-file rule)

- Wiring `foldedFlatCutTransportPlusNR_holds` into `cut_step_from_stuckAtK_plus` (touches FFCT48 — not
  permitted). The bridge `foldedFlatCutTransportPlus_of_NR` is the ready plug.
- Discharging `BackwardFoldCase` / `TailFoldBoundary` (FFCT52 reversal + the §8 master brick — separate
  files / waves).
