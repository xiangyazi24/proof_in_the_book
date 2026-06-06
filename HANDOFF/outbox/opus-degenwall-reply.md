# opus-degenwall — Chapter 36 degenerate-wall parity transport for TRIANGLES (DONE)

**Status: COMPLETE / UNCONDITIONAL for `n = 3`.** New file
`ProofsInTheBook/PolygonDegenerateWall.lean` (≈ 730 lines, 0 sorry / 0 axiom / 0 admit /
0 native_decide). Verifies clean on uisai1 (`lake env lean … PolygonDegenerateWall.lean`
→ RC=0, no errors). `#print axioms` clean-3 `[propext, Classical.choice, Quot.sound]` on
every headline result. Branch `main`, no commits, only the new file touched.

## What was proved (all UNCONDITIONAL, clean-3)

The generic-stratum gap (`GenericWallSeg`, provably false on the on-edge-line stratum)
is **removed for triangles**, closing the last residue.

- `unconditionalRayIndepInput_triangle :`
  `∀ Q : StrictSimplePolygon 3, PolygonFinish.UnconditionalRayIndepInput Q` — the TARGET,
  proved with **no ray/genericity hypothesis** (handles on-edge-line, off-boundary `x`).
- `triangleExteriorEven_unconditional : PolygonLeaf.TriangleExteriorEven` — the triangle
  leaf's exterior-even atom, ray-choice oracle fully discharged.
- `artGallery_strict_unconditional` — `PolygonSeparation.chapter36_headline_separation`
  with its kept ray-choice input `∀ Q, UnconditionalRayIndepInput Q` now *produced*
  unconditionally; gives the `⌊n/3⌋` guard bound for **any** ray direction, no
  ray/genericity hypothesis. Remaining inputs are exactly the genuinely-planar residuals
  the design already isolates (uniform residual geometry `D`, convex-vertex leaf primitive
  `hconv`, diagonal-attach peel `M`) — identical strength/signature to the prior headline,
  no weakening.

## The mechanism (as in the brief, now formalized)

`PolygonWallGlobal.rcrossSum_parity_eventually_const` used its global `GenericWallSeg`
hypothesis **only at the single parameter `t₀`**, and only to prove the R-event pairing
partners are non-wall. I re-derived it under a *local* hypothesis
(`rcrossSum_parity_eventually_const_local`, any `n`), then handled the degenerate wall
directly for `n = 3`:

- **At-most-one-wall** (`n=3`): the three edge directions are pairwise non-parallel
  (consecutive noncollinearity), so a nonzero direction is parallel to ≤ 1 edge
  (`dirDen_ne_zero_of_wall_of_nonpar`, `det2_edgeVec_next/prev_ne_zero`).
- **Degenerate-wall pair lemma** (`rfcount_pair_eventually_eq_of_degenerateWall_tri`):
  at a degenerate wall of edge `w` off the boundary, the wall edge contributes `0`
  (`PolygonWall.rfcount_eventually_zero_of_wall`, already unconditional) and the two
  adjacent edges `cyclicNext w`, `cyclicNext (cyclicNext w)` carry **equal** crossing
  counts near `t₀` (numerically confirmed: not just equal parity — equal). Two ingredients,
  both from the positive proportionality `P.q w − x = μ • (P.q (cyclicNext w) − x)`, `μ>0`
  (`x` outside the wall segment, off boundary), reusing
  `PolygonWall.exists_smul_of_det2_zero`:
  - **Span agreement**: the two outer side functions (the wall-edge endpoints, both on the
    ray line at `t₀`) are positively proportional; `Span` is sign-only and symmetric, so
    `Span(ds0 j, ds1 j) ↔ Span(ds0 p, ds1 p)` pointwise.
  - **Forward agreement**: at `t₀` the ray reaches `P.q (cyclicNext w)` (edge `j`'s start,
    via `ds0 j = 0 ⇒ rU j = 0`) and `P.q w` (edge `p`'s end, via `rU_eq_one_of_event`) at
    forward parameters with `dirTau p t₀ = μ • dirTau j t₀` (`μ>0`), both nonzero
    (off boundary), so `0 ≤ dirTau j ↔ 0 ≤ dirTau p` in a neighbourhood.
  Hence `rcrossSum % 2 = 0` in a whole neighbourhood of a degenerate wall
  (`rcrossSum_eventually_zero_of_degenerateWall_tri`).
- **Per-`t₀` dispatch** (`rcrossSum_parity_eventually_const_tri`, no hypothesis): case
  split on existence of a degenerate wall at `t₀` (degenerate → eventually 0; otherwise
  `LocalGenericWall` holds → the local generic assembly). Glued on the preconnected
  `Icc 0 1` (`rParity_locallyConstant_tri`, `rcrossSum_parity_endpoints_tri`), giving
  `closedRegion'_wallGlobal_tri` (SegAvoidsZero only). Two arbitrary directions are joined
  through one antiparallel-avoiding intermediate `μ = mkPt 1 s`
  (`closedRegion'_chain_tri`, reusing `PolygonGenericRay.segAvoidsZero_to_mkPt`).

## Verification (uisai1)

- `lake env lean ProofsInTheBook/PolygonDegenerateWall.lean` → RC=0, no errors (only
  benign warnings: one unused `ht₀` mirroring the upstream signature, deprecated
  `push_neg`).
- Dep oleans: `lake build ProofsInTheBook.PolygonGenericRay` → "Build completed
  successfully (8440 jobs)".
- `#print axioms` clean-3 `[propext, Classical.choice, Quot.sound]` on:
  `unconditionalRayIndepInput_triangle`, `triangleExteriorEven_unconditional`,
  `artGallery_strict_unconditional`, `rfcount_pair_eventually_eq_of_degenerateWall_tri`,
  `rcrossSum_parity_eventually_const_tri`. No `sorryAx`, no `ofReduceBool`/`native_decide`.
- Never ran `lake build` / `lake env lean` on the local Mac.

## Faithfulness verdict (playbook Group C)

- `unconditionalRayIndepInput_triangle` : **FAITHFUL**, unconditional, non-vacuous. It is
  exactly `PolygonFinish.UnconditionalRayIndepInput Q` (the region/off-boundary parity
  form downstream consumes), with the only hypotheses being the raw objects `ρ σ : RayDirection`
  and `¬ OnBoundary P x`. Covers the previously-open on-edge-line stratum (the
  degenerate-wall case is the new content); no hypothesis was added to dodge it.
- `artGallery_strict_unconditional` : **FAITHFUL** — identical signature/strength to
  `PolygonSeparation.chapter36_headline_separation`, with the kept ray-choice oracle
  *produced* rather than assumed. The surviving `D`/`hconv`/`M` inputs are the design's
  pre-existing genuinely-planar residuals (unchanged), not a weakening of this result.
- No vacuous conditional, no re-wrapper, no too-strong predicate: the degenerate pairing
  was derived (not assumed), and its non-vacuity is witnessed by the concrete numerical
  trace (triangle `A,B,C`, `x` on line `CA`) that motivated it.

## Residue

**None for the triangle case** (`n = 3`), which is all `triangleExteriorEven_of_rayIndep`
/ the downstream `artGallery_strict` requires. General-polygon degenerate-wall transport
(`n ≥ 4`) was not needed and is not attempted here; `LocalGenericWall` +
`rcrossSum_parity_eventually_const_local` are proved for general `n` and could seed it,
but the at-most-one-wall enumeration that closes the pairing is `n = 3`-specific.
