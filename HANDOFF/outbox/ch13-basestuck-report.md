# Ch13 `BaseStuckProgressW` discharge — report

**File:** `ProofsInTheBook/ZinanFFCT42.lean` (new, the only file touched).
**Status:** compiles, 0 errors, clean-3 (`#print axioms` → `propext, Classical.choice, Quot.sound`
on every theorem; no `sorryAx`, no custom `axiom`, no `native_decide`).
**Verdict: the cyclic-identity shortcut CLOSES it. `BaseStuckProgressW` is now a THEOREM.**

## The shortcut works — the design's 250-450 line estimate collapses to ~20 lines of real content

The master prompt's §9 insight is correct and the consumer payload **does** admit the wrap edge.
Two facts make `BaseStuckProgressW` a near-triviality:

1. **Base-stuck's zero IS the opened diagonal.**  `baseCapSupportW A k δ =
   sOrient (A 0)(A K)(rotS2 (A K)(-δ)(A last))` by definition.  `openTail A K (-δ)` fixes vertices
   `≤ K` and rotates `> K` (`openTail_zero` / `openTail_axis` / `openTail_rot`, with `K.val < n`
   from `openingAxis_interior`), so this is literally
   `sOrient (A'_WB 0)(A'_WB K)(A'_WB last)` — the diagonal support of the *opened* arm at the triple
   `(0, K, last)`.  (`baseStuck_eq_openedDiagonal`.)

2. **The diagonal IS the wrap-edge non-incident support.**  In `Fin (n+1)`, `Fin.last n + 1 = 0`
   (`lastAddOne_eq_zero`), so the closed polygon `A'_WB` has the wraparound edge `(last, 0)`.  Its
   support at the interior vertex `K` is `sOrient (A'_WB last)(A'_WB 0)(A'_WB K)`, which equals the
   diagonal by the `det3` cyclic rotation `sOrient a b c = sOrient c a b` (`sOrient_cyc_rot`, pure
   `ring`).  (`baseDiagonal_zero_is_wrapEdgeSupport_zero`.)

So the payload of `BaseStuckProgressW` is produced at the pair `(i, j) = (Fin.last n, K)`:
`i = last`, `i + 1 = last + 1 = 0` (Fin wrap), `j = K`.  The two `NonIncident` side conditions
`j ≠ i` (`K ≠ last`) and `j ≠ i + 1` (`K ≠ 0`) hold because `K` is an interior axis
(`1 ≤ K.val < n`).  No `ReachWB` disjunct is ever needed — base-stuck always takes the
vanishing-support branch.

## The consumer-payload check (the prompt's CAVEAT) — RESOLVED in favor of the shortcut

`ZinanFFCT41.BaseStuckProgressW`'s payload quantifies `∃ i j : Fin (n+1), j ≠ i ∧ j ≠ i + 1 ∧
sOrient (A'_WB i)(A'_WB (i+1))(A'_WB j) = 0` with **`i + 1` in Fin arithmetic**.  Cross-checked
against `SphericalMonitoredSup.NonIncident n = {c // c.2 ≠ c.1 ∧ c.2 ≠ c.1 + 1}` (Fin-add) and
against `ZinanFFCT41.interiorOpeningOutcomeWB_basecapped`, which feeds exactly this payload into
`StuckWB` via `supportConstraint_apply` at the same `i+1`-Fin form (the `Or.inl ⟨⟨(i,j),…⟩, …⟩`
absorption at FFCT41:869-871).  The wrap edge therefore genuinely qualifies as a `NonIncident`
support — the consumer does **not** exclude the closure edge.  So the honest content really is the
one-line cyclic identity, not the design §13 convex-position master brick.

## What was NOT needed (design over-estimate)

- No `baseStraight_dist_add` / `greatCircle_openHemisphere_arc_sum_lt_pi` (the sign-audited
  straightening route — correctly flagged directionally wrong in the design §6/§7, and simply
  unnecessary).
- No sub-arm `MainPlus` IH comparisons.
- No `pureHemi_strictConvexW` strict-convex-position argument, no gnomonic projection, no
  "three vertices on a great circle ⟹ middle non-extreme" lemma.
- No `StrictConvexSphArm A'_WB` hypothesis at all — the bridge is purely the `openTail` index
  identity + `det3` cyclic algebra, valid for any `δ`.

## Deliverables in the file

- `det3_cyc_rot`, `sOrient_cyc_rot`, `lastAddOne_eq_zero` — algebra/index micro-lemmas.
- `baseStuck_eq_openedDiagonal` — base-stuck = opened diagonal `(0,K,last)`.
- `baseDiagonal_zero_is_wrapEdgeSupport_zero` (Brick 1, the bridge), `baseStuck_forces_vanishingSupport`.
- `BaseStuckProgressW_holds : ZinanFFCT41.BaseStuckProgressW` — the residual in its EXACT shape.
- `mainPlus_headline_basestuck_free` — `ZinanFFCT41.mainPlus_headline_basecapped` with
  `BaseStuckProgressW` discharged.
- Non-vacuity guards: `baseStuck_eq_openedDiagonal_at_zero`,
  `baseStuckProgressW_payload_indices_nondegenerate`.

## Final residue surface (after this module)

`mainPlus_headline_basestuck_free` consumes:
- `SpliceBodyDiagMono`, `SpliceStructuralData` — pre-B1 splice geometry (unchanged, FFCT38 era).
- `OpenedClosingEdgeDistinctAtSupWB` — the single wraparound closing-edge distinctness (scoped,
  refutation-resistant).
- `SupportStuckMarginsPosAtSupWB` — strict ambient-`h₀` margins on the support branch (scoped).
- `PureHemiProgressWB` — the pure-hemi progress residual.

**`GlueWBaseCap` (FFCT41) and `BaseStuckProgressW` (FFCT42) are both GONE.**  The base-stuck branch
no longer carries any open obligation; the residue is back to the four splice/edge/pure-hemi
residuals that predate the base-monitor work.
