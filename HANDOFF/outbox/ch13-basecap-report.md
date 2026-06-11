# Ch13 `GlueWBaseCap` discharge — base-capped widening family `WB` (FFCT41)

**File:** `ProofsInTheBook/ZinanFFCT41.lean` (966 lines, clean-3, 0 `sorry`/`axiom`/`admit`/`native_decide`).
Verified: `lake env lean ProofsInTheBook/ZinanFFCT41.lean` → 0 errors; `#print axioms` on all 11 audited
theorems → `{propext, Classical.choice, Quot.sound}` (no `sorryAx`/`ofReduceBool`/`trustCompiler`).

## What was done (route (a) of the archived design, fully implemented)

The central obligation — **`GlueWBaseCap` is now a THEOREM, not a residual** — is discharged via
`GlueWBaseCap_at_supWB`:

    monitoredSupWB A B k h₀ + sphAngle (A 0)(A K)(A last) ≤ Real.pi

proved unconditionally (hypotheses: `hA` strict, `hka/hkt` ShortArc, `h0` init-admissibility — all
original-data-derivable), by adding the base support as a monitored family member and reading the cap off
admissibility. The pipeline:

1. **§1** `baseCapSupportW`, `monitoredFamilyWB` (= `W` family `⊕ Unit`), continuity, `monitoredSupWB`,
   membership, and the **`W`-admissibility bridge** `monitoredSupWB_mem_W` (the WB sup is W-admissible, so
   every W-closure / deficit fact holds verbatim at `δ*_WB` — the reuse hinge that avoids re-proving the W
   machinery).
2. **§2** `baseSupport_openNeg_eq_sin` — the base sinusoid `baseCapSupportW A k θ = N · sin(γbase + θ)`,
   mirror of FFCT37's `support_openNeg_eq_sin`. Sign source: the **positive** convex base support
   `orientedDatum_interior` / strict `cut_diagonal_supports` (vs FFCT37's negative `joint_axis_support_neg`)
   gives the identical `+N sin γ` orientation. Base ShortArc hyps `(K,0)`/`(K,last)` ARE available from
   `shortArc_interior_base hA` (interior axis) — no new assumption needed.
3. **§3** `admissibleWB_baseCap` (admissible ⟹ `sin(γbase+θ)≥0` ⟹ `γbase+θ≤π` via `γbase<π` from
   `base_sphAngle_lt_pi`) + `GlueWBaseCap_at_supWB`. **The central new content.**
4. **§4-§5** W-closure facts at `δ*_WB` (via the bridge), `δ*_WB < π`, the predicates
   `ReachWB`/`StuckWB`/`BaseStuckWB`, and the WB tetrachotomy `opening_boundary_trichotomyWB`
   (CAP ∨ Reach ∨ Stuck ∨ **BaseStuck**).
5. **§6-§7** clause (i) UNCONDITIONAL (`glueWB_clause_i`, cap discharged); clause (ii)
   `¬StuckWB → ReachWB ∨ BaseStuckWB` (`glueWB_clause_ii`); repaired clause (iii) `stuckOutcomeWB_repaired`
   (generic `hemiStuck_dichotomy_tangentFree` + `reach_strictConvex_interior` +
   `weakConvex_of_supportStuckW_of_hemiPos_anyH`; a δ-generic edge-distinctness helper
   `openedEdgesDistinct_at_d` replicates FFCT39's closing→all-edges assembly at `δ*_WB`).
6. **§8-§9** `interiorOpeningOutcomeWB_basecapped : InteriorOpeningOutcome` and
   `mainPlus_headline_basecapped` — the headline with **`GlueWBaseCap` GONE** from its argument list.

## Final residue surface after this wave (scoped to the WB binders)

`mainPlus_headline_basecapped` consumes:

| Residual | Status | Note |
|---|---|---|
| `SpliceBodyDiagMono`, `SpliceStructuralData` | unchanged (pre-existing) | pre-B1 splice geometry |
| `OpenedClosingEdgeDistinctAtSupWB` | scoped, refutation-resistant | constant arm excluded by `StrictConvexSphArm` (`openedClosingEdgeDistinctAtSupWB_constantArm_excluded`) |
| `SupportStuckMarginsPosAtSupWB` | scoped to the **support** branch | never asserts strictness at a hemi-stuck vertex (FFCT38's §3.3 self-contradiction structurally avoided) |
| `PureHemiProgressWB` | mirror of FFCT40's `PureHemiProgressW` | pure-hemi strict ⟹ Reach ∨ vanishing support |
| `BaseStuckProgressW` | **NEW — the one genuine open obligation** | see below |

**`GlueWBaseCap` is DISCHARGED** (was the load-bearing clause-(i) residual; now `GlueWBaseCap_at_supWB`).

## The base-stuck resolution (the genuinely-new design question)

`BaseStuckWB` (`baseCapSupportW A k δ*_WB = 0`, i.e. `γbase + δ*_WB = π`, the base triangle straightens) is
a real fourth trichotomy branch the W family never saw. Honest finding:

- For clause (i) / the cap: base-stuck **needs no separate payload** — the cap holds with equality
  (`δ*_WB + γbase = π ≤ π`), so `glueWB_clause_i` is unconditional even there. ✓
- For the recursion payload (`InteriorOpeningOutcome` needs deficit-drop OR vanishing-support): a base-stuck
  supremum with the joint NOT reached and NO W-support vanishing **is geometrically realizable** (the base
  cap binds first). There the original `InteriorOpeningOutcome` payload is genuinely absent.

The design's straightening-completion (route (b), `baseStraight_completion_by_IH`) would discharge this but
needs sub-arm IH plumbing the W-glue spine lacks; the design explicitly says route (a) must NOT open it.
**Per the honesty contract, base-stuck is therefore carried as the single named residual `BaseStuckProgressW`
(base-stuck ⟹ ReachWB ∨ vanishing-support), NOT faked away.** It is the honest analogue of FFCT40's
`PureHemiProgressW`. Critically it is NOT a vacuous-conditional impostor (its hypothesis `BaseStuckWB` is
satisfiable, `baseStuckWB_def_real`; conclusion is real geometric data) — it is a `CONDITIONAL-honest`
OPEN obligation, flagged as such in its docstring, never proved/banked. The geometrically-true content
behind it is route (b)'s straightening completion (next-wave target if base-stuck is to be closed without a
named residual).

## Adversarial self-checks passed

- `GlueWBaseCap_at_supWB` discharges the real cap inequality with only original-data-derivable hypotheses
  (no hard half hidden in a hypothesis). The headline no longer takes `GlueWBaseCap`.
- All `*ProgressW*` residuals are `def : Prop` consumed as hypotheses, **never proved** — verified by grep.
- Refutation-resistance guards present for every new Prop (`baseCap_nonvacuous`,
  `openedClosingEdgeDistinctAtSupWB_constantArm_excluded`, `baseStuckWB_def_real`, `reachWB_def_real`,
  `baseSupport_openNeg_eq_sin_zero`, headline conclusion satisfiable).
- The base-stuck residual was specifically NOT collapsed into `ReachWB` (which would be a false/vacuous
  bank, since base-stuck-non-reach is realizable).

Not committed (per instructions).
