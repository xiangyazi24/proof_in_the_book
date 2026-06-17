# Ch13 — `OpenedClosingEdgeDistinctAtSupWB` discharged (FFCT43)

**File:** `ProofsInTheBook/ZinanFFCT43.lean` (NEW, single writer). Touches no other file.
**Status:** FULLY CLOSED. clean-3, 0 sorry/axiom/admit/native_decide.

## What was proved

The FFCT41-scoped residual `ZinanFFCT41.OpenedClosingEdgeDistinctAtSupWB` (consumed by
`ZinanFFCT42.mainPlus_headline_basestuck_free`) is discharged via the master's **endpoint-positivity**
route — ~110 lines including docs/guards.

The residual demands: at a `StuckWB` supremum, the wraparound *closing* edge `(last, 0)` of the opened
arm `A'_WB := openTail A K (-δ*_WB)` is distinct, i.e.
`openTail A K (-δ*_WB) (Fin.last n) ≠ openTail A K (-δ*_WB) (Fin.last n + 1)`.

### Route (3 steps, exactly as the master specified)

1. `strict_arm_endpt_pos` : `0 < endpt A` for `StrictConvexSphArm A`.
   `endpt A = sDist (A 0)(A last)`; the closed polygon's wraparound edge `(last, last+1)` is short
   (`StrictConvexSphArm.edge_short` ⟹ `ZinanFFCT39.base_consecutive_ne`), and `last+1 = 0`
   (`ZinanFFCT42.lastAddOne_eq_zero`), so `A 0 ≠ A last`, whence `sDist (A 0)(A last) > 0`
   (`sDist_pos_of_ne`). No `noncollinear_consecutive` needed — the wrap edge being short is direct.

2. `closing_distinct_at_supWB` : `A'_WB 0 ≠ A'_WB last`.
   `ZinanFFCT41.glueWB_clause_i` (NOW UNCONDITIONAL, the cap discharged in FFCT41) gives
   `endpt A ≤ endpt A'_WB`. Chain with step 1: `0 < endpt A ≤ endpt A'_WB = sDist (A'_WB 0)(A'_WB last)`,
   so `A'_WB 0 ≠ A'_WB last` (`sDist_eq_zero_iff`).

3. `OpenedClosingEdgeDistinctAtSupWB_holds : ZinanFFCT41.OpenedClosingEdgeDistinctAtSupWB`.
   The residual in its EXACT shape. Glue-context inputs of clause (i) (`hka`/`hkt`/`h0`) derived inside
   the scoped binders via `shortArcs_of_strict` + `monitoredFamily_init_admissible`. The goal's
   `Fin.last n + 1` rewrites to `0`; conclusion is `A'_WB last ≠ A'_WB 0` = `(step 2).symm`.

### Re-threading

`mainPlus_headline_closing_free` = `ZinanFFCT42.mainPlus_headline_basestuck_free` with
`OpenedClosingEdgeDistinctAtSupWB` ALSO discharged. Genuine headline inequality
`sDist (A 0)(A last) ≤ sDist (B 0)(B last)` for strict convex arms (equal sides, `A`'s joints ≤ `B`'s).

**Remaining residue surface** (now drops the closing-edge clause):
`SpliceBodyDiagMono`, `SpliceStructuralData`, `SupportStuckMarginsPosAtSupWB`, `PureHemiProgressWB`.
GONE from the surface: `GlueWBaseCap` (FFCT41), `BaseStuckProgressW` (FFCT42), and now
`OpenedClosingEdgeDistinctAtSupWB` (FFCT43).

## Faithfulness notes (§3.3 self-audit)

- The `StuckWB` premise of the residual is **unused** — the closing edge is distinct at *any* `WB`
  supremum (stuck or not), because the endpoint never collapses (discharged cap ⟹ `endpt A ≤ endpt A'_WB`,
  base endpoint positive). Carried as an unused binder, faithful to the consumer's exact shape. This is
  a genuinely-stronger fact, NOT a vacuity dodge.
- Statement fidelity confirmed by Lean: `OpenedClosingEdgeDistinctAtSupWB_holds` type-checks against
  `: ZinanFFCT41.OpenedClosingEdgeDistinctAtSupWB`, so the proved statement equals the residual verbatim.
- Non-vacuity guards included: `strict_arm_endpt_pos_unfolds` (`endpt A = sDist (A 0)(A last)`, real
  geometric quantity) and `openedClosingEdgeDistinctAtSupWB_conclusion_real` (`A last ≠ A 0` at δ=0,
  the genuine base endpoint pair). The only `:= rfl` is the unfold guard, not a banked result.

## Verification

`ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT43.lean'`
→ 0 errors. `#print axioms` for all five theorems: `[propext, Classical.choice, Quot.sound]` only.
No `sorryAx`, no `ofReduceBool`/`trustCompiler`.

Not committed (per instructions). Wiring into `ProofsInTheBook.lean` / `Audit.lean` left to the master.
