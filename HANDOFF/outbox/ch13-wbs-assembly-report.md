# Ch13 WBS ASSEMBLY report — `ZinanFFCT46` (bricks 4–6, 8–9)

**Status:** COMPLETE, clean-3, 578 lines, `lake build ProofsInTheBook.ZinanFFCT46` succeeds.
Every theorem depends only on `[propext, Classical.choice, Quot.sound]` — no `sorry`/`sorryAx`/`admit`/
`axiom`/`native_decide`.

## The load-bearing margins finding (settled FIRST, per the honesty contract)

`ZinanFFCT44.openHemisphere_of_weakSupports_jointOpen` **DOES require** an `hmargin : ∀ r, 0 ≤ ⟪h₀, A'_WBS r⟫`
— a base normal `h₀` with weak hemisphere margins on EVERY opened-arm vertex. It feeds this to FFCT30's
tilt (`exists_unit_perturbed_normal_of_tangent`, whose `hnn` argument is exactly those weak margins) at
FFCT44 line 393. Note: the **upstream** `equatorTangentExists_of_weakSupports_jointOpen` carries the
margin binder as `_hmargin` (UNUSED — the tangent is margins-free), but brick 2 re-introduces it for the
tilt base.

The WBS family (`ZinanFFCT45`) **deliberately dropped the hemisphere monitor** (design route (c)). So
there is no `hemiW_inner_nonneg` analogue: the opened arm's margins w.r.t. any fixed `h₀` are unmonitored
and **can go negative**. The original arm `A`'s `open_hemisphere` normal is strict on `A`'s vertices but
gives no guarantee on the OPENED vertices. **The design §9 route through the tilt has a genuine gap — there
is no margins source in WBS.** This was confirmed by inspecting `hemiMargin_nonneg_at_sup` (holds only
because WB *monitors* it) and FFCT40's `pureHemi_strictConvexW` (gets its `hhemnn` from `hemiW_inner_nonneg`,
a WB monitor).

## The honest fix (the keystone, NOT a workaround)

The tilt is not the only hemisphere-production mechanism. **`openHemisphere_of_weakSupports_jointOpen_full`**
produces the strict open hemisphere **margins-free** by finite separation on the FULL opened-vertex set
(the full-set sibling of FFCT44's equator-subset lemma, with `Finset.univ` for the filter):

* `0 ∉ convexHull(all vertices)` → `ZinanFFCT36.exists_inner_pos_of_zero_notMem_convexHull` gives the
  strict common normal **directly**, normalized to unit length. No base `h₀`, no tilt.
* `0 ∈ convexHull` → every edge functional pushed through the convex combination vanishes (weak supports),
  a positive-weight vertex is a common edge-plane axis → FFCT44's exported
  `commonLine_collapse_forces_flat_joint` contradicts joints-in-`(0,π)`.

**No margins hypothesis is consumed.** This is the genuine replacement closing the hemisphere line.

## Bricks delivered

| Brick | Theorem | Notes |
|-------|---------|-------|
| (mechanism) | `openHemisphere_of_weakSupports_jointOpen_full` | margins-free full-set separation — the keystone |
| 4 | `openHemisphere_at_WBS_sup` | hemisphere at A'_WBS from WBS closure supports + opened ShortArc edges + joints-(0,π) |
| 5 | `supportStuckWBS_weakConvex` | weak supports + brick 4 → `weakConvex_of_supportStuckW_of_hemiPos_anyH` |
| 6 | `reachWBS_strictConvex` | ¬support-stuck upgrades supports to strict → `reach_strictConvex_interior` |
| 8 | `interiorOpeningOutcomeWBS` | WBS trichotomy → `SphericalArmAssembly.InteriorOpeningOutcome` |
| 9 | `mainPlus_headline_wbs` | re-threaded FFCT43 headline on the WBS outcome |

Supporting (margins-free): `shortArc_of_sDist_pos_lt_pi`, `openTail_nonwrap_shortArc` (non-wrap opened
edges short via the `sDist`-preserving isometry), `openedJoints_in_Ioo_at_supWBS`,
`openedWrap_distinct_at_supWBS` (FFCT43 endpoint-positivity route at the WBS sup).

## The opened ShortArc edges (the one structural input) and the SINGLE sharp residual

Brick 4 (and FFCT44's collapse) need the opened arm's edges to be short arcs.

* **Interior/seam/tail edges** (every edge except the wraparound): short **margins-free** — they have the
  same `sDist` as the base arm's edges under the opening isometry (`openTail_fixed`/`_axis`/`sDist_openTail_tail`),
  and `A` is strict.
* **Wraparound edge `(last, 0)`:** distinctness is margins-free (`openedWrap_distinct_at_supWBS`, the FFCT43
  endpoint route via `glueWBS_clause_i` + `strict_arm_endpt_pos`). Its **non-antipodality** is the ONE fact
  the weak-support branch cannot conclude margins-free. The **reach branch closes it** via
  `ZinanFFCT34.antipodal_pair_excluded_of_strict` (so brick 6 needs no residual). The **support-stuck branch**
  exposes it as the single named residual:

      OpenedWrapShortArcAtSupWBS  (the opened wraparound edge of A'_WBS is a ShortArc)

  Refutation-resistant (constant arm excluded by `StrictConvexSphArm A`); realised at δ=0 as `A`'s own short
  closing edge. Non-vacuity guards: `openedWrapShortArcAtSupWBS_conclusion_real`,
  `openedWrapShortArcAtSupWBS_constantArm_excluded`.

## The FINAL Ch13 residue surface (brick 9 headline `mainPlus_headline_wbs`)

| Residue | Status |
|---------|--------|
| `SpliceBodyDiagMono` | named (pre-B1 splice geometry) |
| `SpliceStructuralData` | named (pre-B1 splice geometry) |
| `OpenedWrapShortArcAtSupWBS` | **the single sharp NEW residual** — opened wrap edge non-antipodal |

**GONE from the surface** (vs FFCT43's `mainPlus_headline_closing_free`): the two hemisphere residuals
`SupportStuckMarginsPosAtSupWB` and `PureHemiProgressWB` — they never arise on the hemisphere-free WBS
family. Also already discharged upstream: `GlueWBaseCap`, `BaseStuckProgressW`, `OpenedClosingEdgeDistinctAtSupWB`.

So the hemisphere residual LINE is closed: the two fixed-`h₀`/pure-hemi residuals are eliminated, replaced
by the single geometric fact that the opened wraparound edge is non-degenerate.

## Net assessment

The hemisphere-production mechanism is genuinely new and margins-free; bricks 4–8 are unconditional given
the opened ShortArc edges; brick 9's surface is `2 splice residuals + 1 sharp wrap-edge residual`. The
margins gap flagged in the prompt was real (confirmed against FFCT44/FFCT30/FFCT40/FFCT45) and is resolved
by the full-set separation, not papered over. The only honestly-exposed new residual is the wrap-edge
non-antipodality in the weak-support branch — a strictly smaller, true, refutation-checked surface than the
hemisphere residuals it replaces.

Not committed (per instructions).
