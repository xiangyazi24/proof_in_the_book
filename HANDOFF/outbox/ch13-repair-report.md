# Ch13 — §3.3 REPAIR of the vacuously-conditional clause-(iii) half (`ZinanFFCT40`)

**File:** `ProofsInTheBook/ZinanFFCT40.lean` (NEW, single writer, ~480 lines).
**Status:** Compiles 0 errors on uisai2 (`lake env lean ProofsInTheBook/ZinanFFCT40.lean` against the
committed FFCT37/38 oleans + FFCT39's freshly-built olean). All 8 `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (clean-3; no `sorryAx`, no `native_decide`/`ofReduceBool`).
No `sorry`/`axiom`/`admit`/`native_decide`. **Not committed** (per instructions).

## What was wrong (the vacuity FFCT39 audited, now repaired)

FFCT38's `glueWClauseIII_of_residues` consumed two FALSE `Prop`s:
- `OpenedEdgesDistinctW` over **all** arms — refuted by the constant arm;
- `HemiMarginStrictPosAtSupW` over **all** of `StuckW` — self-contradictory on the hemi disjunct.

`stuckOutcomeW_weakConvex_of_residues` hid the breakage by `exfalso`-ing its pure-hemi (all-supports-
strict) sub-case **using the false `hhemstrict r`** — the textbook §3.3 "vacuous conditional via an
unsatisfiable hypothesis" mode (invisible to `#print axioms`).

## The pure-hemi resolution (the real finding)

The honest dichotomy at a `StuckW` supremum is FFCT36's `hemiStuck_dichotomy_tangentFree`, which is

    (∃ vanishing non-incident support) ∨ WeakConvexSphArm A'_W

with **no hemi-strictness residual at all** (the equator residual is already discharged by FFCT36's
Hahn–Banach/Riesz separation). The second branch is the **pure-hemi** outcome: a hemisphere margin
vanished, but ALL non-incident supports are strict, so `A'_W` is in fact **`StrictConvexSphArm`** (a
tilted hemisphere normal exists, via FFCT30 tilt + FFCT36 separation — `pureHemi_strictConvexW`).

Crucially, the pure-hemi arm has **no vanishing support** and **no guaranteed deficit drop** (the joint
need not have reached `B`'s value). So the ORIGINAL clause (iii) conclusion — `WeakConvex ∧ ∃ vanishing
support`, unconditionally — is **genuinely false** in the pure-hemi case. This is exactly the gap
`SphericalOpeningOutcome`'s own docstring flagged ("a pure hemisphere-stuck supremum ... must still be
shown to force a vanishing non-incident support"), which FFCT38 papered over with the false strict-margin
Prop.

## The corrected residue surface

| FFCT38 (FALSE as demanded) | FFCT40 honest replacement | Why true / refutation-resistant |
|---|---|---|
| `OpenedEdgesDistinctW` ∀ all arms | `OpenedClosingEdgeDistinctAtSupW` (scoped to glue binders) | constant arm excluded by `StrictConvexSphArm` (`openedClosingEdgeDistinctAtSupW_constantArm_excluded`); all non-closing edges proved unconditionally (FFCT39) |
| `HemiMarginStrictPosAtSupW` ∀ all `StuckW` | `SupportStuckMarginsPosAtSupW` (scoped to the **support** disjunct) | premise is the support branch, never asserted at a hemi-stuck vertex, so the FFCT38 self-contradiction is structurally avoided |
| (silently assumed: hemi forces a vanishing support) | `PureHemiProgressW` (NEW, named, non-vacuous) | the genuine hemi-branch content: a pure-hemi sup forces `ReachW` (deficit drops) ∨ a vanishing support |

All three carry non-vacuity / refutation-resistance guards (`§4`).

## Key theorems (all clean-3)

- `weakConvex_of_supportStuckW_of_hemiPos_anyH` (§1) — the `∃ h'` sibling of
  `weakConvex_of_supportStuck_of_hemiPos`; near-verbatim copy with the fixed `h₀` generalised to an
  existential unit witness (since `open_hemisphere` is itself `∃`-quantified).
- `pureHemi_strictConvexW` (§3) — the pure-hemi strict-convexity certificate (FFCT30 tilt + FFCT36
  separation → `reach_strictConvex_interior` at `-δ*_W`).
- `stuckOutcomeW_repaired` (§3) — the honest STUCK core: `WeakConvex ∧ ((∃ vanishing support) ∨
  StrictConvexSphArm A'_W)`, **no `exfalso` on pure-hemi, no false Prop**.
- `glueWClauseIII_repaired : OpenedClosingEdgeDistinctAtSupW → SupportStuckMarginsPosAtSupW →
  GlueWClauseIII'` — the repaired clause (iii), where `GlueWClauseIII'` is the corrected shape with the
  explicit pure-hemi disjunct.
- `InteriorOpeningOutcomeW'` + `interiorOpeningOutcomeW'_repaired` — the corrected family-agnostic
  outcome (three alternatives: REACH-drop, STUCK-weak-vanishing, pure-hemi-strict), proved inhabited.
- `interiorOpeningOutcomeW_repaired : GlueWBaseCap → OpenedClosingEdgeDistinctAtSupW →
  SupportStuckMarginsPosAtSupW → PureHemiProgressW → InteriorOpeningOutcome` — collapses the pure-hemi
  alternative back into the ORIGINAL termination-ready `SphericalArmAssembly.InteriorOpeningOutcome` via
  `PureHemiProgressW` (ReachW → `deficitCount_openTail_reach_lt`; or vanishing support → STUCK disjunct).
- `mainPlus_headline_repaired` — the headline `sDist (A 0)(A last) ≤ sDist (B 0)(B last)`, now resting on
  the HONEST residue list.

## What the headline now honestly says

`mainPlus_headline_repaired` proves the same inequality as FFCT38's `mainPlus_headline_final`, but its
clause-(iii) residue surface is:

    SpliceBodyDiagMono, SpliceStructuralData, GlueWBaseCap,
    OpenedClosingEdgeDistinctAtSupW   (scoped Brick 1 — one wraparound edge),
    SupportStuckMarginsPosAtSupW      (scoped Brick 2 — support branch only),
    PureHemiProgressW                 (the genuine hemi-branch residual)

The two FALSE FFCT38 names are gone. Every remaining clause-(iii) hypothesis is a named, satisfiable,
refutation-checked `Prop` that survives the constant-arm and hemi-stuck adversarial checks that killed
FFCT38's shapes. The headline is now **non-vacuously** conditional on its clause-(iii) half.

## Honest scope note

`PureHemiProgressW` is the new, genuinely-irreducible content this repair surfaces (it is NOT a
re-packaging of the false FFCT38 Prop — it is the geometric fact that a hemisphere-blocked opening still
makes recursion progress). It is named and non-vacuous, not faked. Whether it can itself be discharged
from the substrate (e.g. via a finer monitored-family argument showing pure-hemi-without-reach forces a
support to vanish) is the genuine next clause-(iii) frontier — flagged, not faked.
