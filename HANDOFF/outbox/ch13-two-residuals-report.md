# Ch13 — the two `-δ` headline residuals (`OpenedEdgesDistinctW`, `HemiMarginStrictPosAtSupW`), audited

**File:** `ProofsInTheBook/ZinanFFCT39.lean` (354 lines, NEW, single writer).
**Status:** Compiles 0 errors on uisai2 (`lake env lean ProofsInTheBook/ZinanFFCT39.lean` against the
committed FFCT37/FFCT38 oleans). All 8 `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(clean-3; no `sorryAx`, no `ofReduceBool`/`native_decide`). No `sorry`/`axiom`/`admit`/`native_decide`.
**Not committed** (per instructions).

## TL;DR

Applying the §3.3 adversarial audit to *how FFCT38 consumes the two names* turned up that **both
residuals, as `ZinanFFCT38.glueWClauseIII_of_residues` demands them, are FALSE `Prop`s** — so the FFCT38
headline is `clean-3` but **vacuously conditional** on its clause-(iii) half (the §3.3 "VACUOUS
conditional theorem via an unsatisfiable hypothesis" failure mode, invisible to `#print axioms`). This
module:

1. **Proves the genuine, satisfiable positive content** of each (the parts a faithful clause-(iii) must
   actually rest on), unconditionally where possible.
2. **Refutes the over-strong FFCT38-demanded forms** with explicit, unconditional `¬`-theorems.
3. **Isolates the one true irreducible remnant** of Brick 1 (the wraparound closing edge) as a single
   named, satisfiable, *strictly smaller* sub-residual.

## Brick 1 — `OpenedEdgesDistinctW`: closed except the one cyclic-closing edge

`OpenedEdgesDistinctW A B k h₀ := ∀ i : Fin (n+1), openTailW A K δ*_W i ≠ openTailW A K δ*_W (i+1)`,
`K = openingAxis k` interior (`1 ≤ K.val < n`), `openTailW A K δ*_W = openTail A K (-δ*_W)` (`rfl`),
`d := -δ*_W`. The cyclic polygon has its `n+1` edges; an interior axis `K` splits the vertices into a
**fixed** head `≤ K` and a **rotated** tail `> K` (rotation `rotS2 (A K) d`). Exactly two edges cross
the partition: the **seam** `(K, K+1)` and the **wraparound** `(last, 0)`.

**Proved UNCONDITIONALLY (strict convexity of `A` only; `A`'s cyclic `edge_short` ⟹ `A i ≠ A (i+1)`):**

| Theorem | Edge | Mechanism |
|---------|------|-----------|
| `openedEdgeDistinctW_fixed` | both endpoints `≤ K` | `openTail` fixes `≤ K` ⟹ base distinctness |
| `openedEdgeDistinctW_tail`  | both endpoints `> K`  | single isometry `rotS2 (A K) d`; `sDist_rotS2` cancels |
| `openedEdgeDistinctW_seam`  | `(K, K+1)` | `rotS2_axis` (axis fixed) rewrites `A K = rotS2 (A K) d (A K)`, then `sDist_rotS2` reduces to `A K ≠ A (K+1)` |

`openedEdgesDistinctW_of_closing` assembles these via the trichotomy on `i.val` vs `K.val` (with the
no-wrap fact `(i+1).val = i.val+1` for `i ≠ last`), reducing the **full** `OpenedEdgesDistinctW` to the
single wraparound edge.

**The one honest sub-residual** — `OpenedClosingEdgeDistinctW A B k h₀` (the lone edge `(last, 0)`):
`openTail last = rotS2 (A K) d (A last)` (rotated) vs `openTail 0 = A 0` (fixed). This pair is **not**
related to a base edge by the rotation isometry, and — the load-bearing point — **the closure `≥ 0`
supports do not force it distinct**: if `openTail last = openTail 0 =: v`, then every support
`sOrient v v (openTail j) = det3 v v · = 0 ≥ 0`, *consistent* with closure. A repeated wraparound vertex
is invisible to the `≥ 0` data — exactly the `no_repeat` family's global obstruction
(`ch13-no-repeat-report.md`: closing/non-adjacent distinctness needs the out-of-plane/global argument,
carried campaign-wide as the named satisfiable input `NoNonadjacentRepeat`). I follow that established
honest CONDITIONAL pattern: `OpenedClosingEdgeDistinctW` is named, **satisfiable** (realised at `δ*_W=0`
as the base `A last ≠ A 0`, guard `openedClosingEdgeDistinctW_nonvacuous`), and strictly smaller than the
original (one edge, not all). Even the strict hemi margins available in the stuck context do **not**
close it (open-hemisphere ⟹ non-antipodal, **not** non-equal — two equal vertices can sit in one open
hemisphere).

**Audit — the FFCT38-demanded form is FALSE:** `glueWClauseIII_of_residues` (FFCT38 l.289–298) takes
`hdist : ∀ {n} A B k h₀, OpenedEdgesDistinctW A B k h₀` — distinctness for **every** arm, no convexity
premise. `not_openedEdgesDistinctW_constant` refutes it unconditionally: a constant arm `A ≡ p` has every
opened vertex `= p` (fixed or rotated, `rotS2 p d p = p`), so no edge is distinct. The FFCT38 `hdist`
hypothesis is unsatisfiable.

## Brick 2 — `HemiMarginStrictPosAtSupW`: the global form is self-contradictory; the support branch is the truth

`HemiMarginStrictPosAtSupW` asserts (under `StuckW`) `0 < ⟪h₀, A'_W r⟫` at **every** vertex `r`. But
`StuckW`'s **hemi** disjunct (a genuine branch of `opening_boundary_trichotomyW`) is
`∃ r, hemiMargin A K h₀ r (-δ*_W) = 0`, i.e. `⟪h₀, A'_W r⟫ = 0`. These are a direct contradiction.

**Audit (unconditional):**
- `hemiMarginStrictPosAtSupW_self_contradictory_on_hemiStuck` — `HemiMarginStrictPosAtSupW` + any
  hemi-stuck datum (`hemiMargin … r (-δ*_W) = 0`) ⟹ `False` (the residual forces `0 < x`, the datum is
  `x = 0`, `linarith`).
- `not_hemiMarginStrictPosAtSupW_of_hemiStuck_witness` — therefore any realised hemi-stuck supremum gives
  `¬ HemiMarginStrictPosAtSupW`. The residual is **false exactly where `StuckW`'s hemi disjunct lives**.

This is *also* why FFCT38's `stuckOutcomeW_weakConvex_of_residues` (l.272–281) can `exfalso` the
hemi-stuck weak-convex sub-case "using the residual to refute it": it is leaning on a false premise to
declare the case impossible. The mathematically faithful resolution of that sub-case is a **tilted**
normal `h'` (FFCT30 `exists_perturbed_normal_of_tangent`), not `h₀`; but the consumer
`weakConvex_of_supportStuck_of_hemiPos` is hard-wired to `h₀` (`open_hemisphere := ⟨h₀, hnorm, hhem⟩`,
`SphericalOpeningGlue` l.227), so the FFCT38 wiring cannot accept a tilt without a consumer rewrite. That
rewrite (route the hemi-stuck branch through the FFCT30 tilt + FFCT36 separation, supplying *some* unit
`h'` to `open_hemisphere`) is the genuine next step for a faithful clause-(iii); flagged, not faked.

**The genuine, satisfiable positive content (support-stuck branch):**
- `SupportStuckMarginsPos A B k h₀ := ∀ r, hemiMargin A K h₀ r (-δ*_W) ≠ 0` — the honest premise, now
  correctly scoped to the support branch (where no `h₀`-margin need vanish). Satisfiable (at `δ*_W=0`
  it is `⟪h₀, A r⟫ ≠ 0`; guard `supportStuckMarginsPos_nonvacuous`).
- `hemiMarginStrictPos_supportStuck` — from the closure `≥ 0` (`FFCT38.hemiMarginW_nonneg_at_sup`) +
  `SupportStuckMarginsPos`, the fixed-`h₀` margin is *strictly* `> 0` at every vertex — the exact
  per-vertex shape `FFCT38.stuckOutcomeW_of_supportVanish` consumes. This is the correctly-scoped
  replacement for the false global `HemiMarginStrictPosAtSupW`.

## What is now the honest clause-(iii) residue surface

Replacing the two false FFCT38 names with their faithful counterparts:

| Old (FFCT38, **FALSE as demanded**) | Honest replacement (this file) | Status |
|---|---|---|
| `OpenedEdgesDistinctW` ∀ all arms | `OpenedClosingEdgeDistinctW` (one wraparound edge) | named, satisfiable, strictly smaller; all other edges proved unconditionally |
| `HemiMarginStrictPosAtSupW` over all `StuckW` | `SupportStuckMarginsPos` (support branch) ⟹ `hemiMarginStrictPos_supportStuck` | support branch proved; **hemi branch needs the FFCT30 tilt + a consumer rewrite to `∃ h'`** (flagged) |

## Honesty contract compliance

- **Brick 1:** every non-closing edge closes fully and unconditionally; the single wraparound edge is the
  one named, satisfiable, strictly-smaller sub-residual (`OpenedClosingEdgeDistinctW`), with the precise
  reason it is irreducible from local data. The FFCT38-demanded all-arms form is *refuted*
  (`not_openedEdgesDistinctW_constant`), not silently passed.
- **Brick 2:** the global residual is proved **self-contradictory** on the hemi branch (so it cannot be
  closed — it is false); the support-branch truth is proved in full
  (`hemiMarginStrictPos_supportStuck`); the faithful hemi-branch fix (FFCT30 tilt + consumer rewrite to
  `∃ h'`) is identified and flagged, not faked.
- No vacuous statements: every named `Prop` carries a non-vacuity guard
  (`openedClosingEdgeDistinctW_nonvacuous`, `supportStuckMarginsPos_nonvacuous`,
  `hemiMarginStrictPos_supportStuck_conclusion_real`).

## Wiring note for the integrator

The FFCT38 headline `mainPlus_headline_final` remains `clean-3` (conditional). To make its clause-(iii)
half **non-vacuously** conditional, FFCT38's `glueWClauseIII_of_residues` should be re-stated to consume
(a) `openedEdgesDistinctW_of_closing` (taking `OpenedClosingEdgeDistinctW` + `StrictConvexSphArm A`, both
already in hand at the call site) in place of the all-arms `hdist`, and (b) per-branch hemi data:
`hemiMarginStrictPos_supportStuck` (support branch) + the FFCT30-tilt rewrite (hemi branch) in place of
the global `HemiMarginStrictPosAtSupW`. That rewrite is a consumer change to `SphericalOpeningGlue`'s
`weakConvex_of_supportStuck_of_hemiPos` (accept `∃ h'` for `open_hemisphere` rather than the fixed `h₀`)
and is the genuine remaining clause-(iii) work.

To surface in the audit: `import ProofsInTheBook.ZinanFFCT39` in `Audit.lean` (+ its own import list) and
`#print axioms` for the 8 theorems above (they already self-report clean-3 in-file).
