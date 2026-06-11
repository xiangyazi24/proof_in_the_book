# Ch13 WRAP-SHORTARC report — `ZinanFFCT47` (the cycle-breaking discharge)

**Status:** COMPLETE, clean-3. `~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT47.lean` succeeds
with **0 errors** (only `push_neg` deprecation warnings, mirroring FFCT44/46). Every theorem depends
only on `[propext, Classical.choice, Quot.sound]` — no `sorry`/`sorryAx`/`admit`/`axiom`/`native_decide`.

The single sharp residual `OpenedWrapShortArcAtSupWBS` from `ZinanFFCT46` is **discharged
unconditionally** (`openedWrapShortArcAtSupWBS_holds : OpenedWrapShortArcAtSupWBS`). The final Ch13
WBS surface is now `SpliceBodyDiagMono` + `SpliceStructuralData` ONLY.

## The circularity, confirmed and broken

`ShortArc p q` is *exactly* `p ≠ q ∧ (p : E3) ≠ -(q : E3)` (SphericalKernel.lean:159) — distinct AND
non-antipodal, nothing stronger (no `⟪⟫`-bound, no arc ≤ π/2). The master's brick-3 forecast holds:
two vertices strictly inside an open hemisphere are non-antipodal, and distinctness is already
margins-free (`openedWrap_distinct_at_supWBS`), so **the hemisphere alone is sufficient** — no sharp gap.

The circularity was: FFCT46's keystone `openHemisphere_of_weakSupports_jointOpen_full` takes
`hside : ∀ i, ShortArc (P i)(P (i+1))` over **all `n+1` edges incl. the wrap edge** — the very fact
under proof. Broken by re-running the full-set separation with the wrap edge dropped.

## What was built (5 sections, ~470 lines)

| § | Theorem | Role |
|---|---------|------|
| §1 | `openChain_collapse_forces_flat_joint_ge3` | open-chain collapse kernel, `3 ≤ n`, real edges only |
| §2 | `openHemisphere_full_openChain` | margins-free + **wrap-free** hemisphere; n=2 corner handled |
| §3 | `wrap_shortArc_of_hemisphere` | hemisphere-interior ⟹ non-antipodal ⟹ `ShortArc` |
| §4 | `openedWrapShortArc_at_supWBS`, `openedWrapShortArcAtSupWBS_holds` | the residual discharged |
| §5 | `mainPlus_headline_wrap_free` | FFCT46 headline, wrap residual GONE |

**§1 open-chain kernel (`3 ≤ n`).** Faithful copy of FFCT44's `commonLine_collapse_forces_flat_joint`,
with `hside`/`hallplanes` quantified only over `i ≠ Fin.last n` (the `n` real edges). The pencil
argument fires on interior apexes `1..n-1` whose two adjacent edges have base indices `r.val`,
`r.val+1`, both `< n` (proved by `jIdx_ne_last`, `jIdx_succ_ne_last`), so always real — the wrap edge
is never touched. The all-pole corner uses joints `0`,`1` → adjacent interior poles `P 1`,`P 2` sharing
the **real** edge `(P 1,P 2)` → ShortArc kill. Restricted to `3 ≤ n` because the `n=2` single-apex
case genuinely cannot fire from a single axis (master's analysis confirmed: with `z = ±P 1` both
`det3 P0 P1 z`, `det3 P1 P2 z` are trivially `0`).

**§2 the n=2 corner — implemented faithfully (the riskiest brick).** In the `0 ∈ hull` branch the
edge-functional collapse forces every positive-weight vertex to be a common real-edge axis. For
`3 ≤ n` this contradicts §1. For `n = 2`:
- A single positive-weight vertex is impossible (`0 = w•v`, `‖v‖=1`). So **some positive-weight vertex
  `v₀ ≠ (P 1 : E3)`** exists — proved directly: if every positive-weight vertex equalled `P 1`, then
  `0 = Σ w_v•v = (Σ w_v)•(P 1) = 1•(P 1) = P 1`, contradicting `‖P 1‖ = 1`.
- Its index `r₀ ∈ {0, 2}` (≠ 1, by `fin_cases`). If `r₀ = 2`, the real edge `0 = (P 0,P 1)` axis fact
  gives `det3 (P 0)(P 1)(P 2) = 0` **directly**. If `r₀ = 0`, the real edge `1 = (P 1,P 2)` axis fact
  gives `det3 (P 1)(P 2)(P 0) = 0`, equal to `det3 (P 0)(P 1)(P 2)` by cyclic det3.
- Either way the single interior joint is flat → contradicts joints-in-`(0,π)`.

This is *simpler* than the master's plane-intersection sketch: among `{P 0,P 1,P 2}` the one
positive-weight common-axis vertex `≠ P 1` is automatically `P 0` or `P 2`, and the consecutive triple
`det3` falls out by cyclic rotation of the matching real-edge functional — no second-vertex
plane-coincidence / antipodal split needed. (The `P 0 = P 2` degeneracy is absorbed: then the triple
trivially has `det3 = 0`, still a genuine flat joint — honest, not vacuous.)

**§3–§4.** `wrap_shortArc_of_hemisphere`: `(P last : E3) = -(P 0 : E3)` ⟹
`0 < ⟪h', P last⟫ = -⟪h', P 0⟫ < 0`, impossible. Assembled at the WBS sup from FFCT46's real-edge
inputs (`openTail_nonwrap_shortArc`, `supportWBS_sOrient_nonneg` restricted to real `i`,
`openedJoints_in_Ioo_at_supWBS`) + the margins-free distinctness `openedWrap_distinct_at_supWBS`.
`openedWrapShortArcAtSupWBS_holds` closes the residual via `shortArcs_of_strict`.

## Honesty contract

- The n=2 corner is implemented in full (§2), not skipped or axiomatised. No vacuous statements
  (non-vacuity guards: `..._conclusion_real` realises the conclusion at δ=0 as `A`'s own short closing
  edge; `..._satisfiable` for the headline).
- **No residual exposed.** The wrap-edge non-antipodality — the one fact the weak-support branch
  previously could not conclude margins-free — is now produced unconditionally by the wrap-free
  hemisphere. The Ch13 WBS surface collapses to the two pre-B1 splice residuals.

## Files
- Created: `ProofsInTheBook/ZinanFFCT47.lean` (only file touched). Not committed (per instructions).
- Verify: `scp ... uisai2:... && ssh uisai2 '~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT47.lean'`
