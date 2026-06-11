# Ch13 hemi-stuck — the FINAL kill of the last equator residual (ZinanFFCT36)

**File:** `ProofsInTheBook/ZinanFFCT36.lean`. Compiles **0 errors, 0 warnings**, clean-3.
`#print axioms` on all six results: `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`,
no custom axioms, no `native_decide`. Only edit: this one new file. No other file touched
(`ZinanFFCT35.lean`, the sibling worker's, was neither imported nor modified).

## What landed: the residue is KILLED OUTRIGHT

The master's convex-combination argument is fully formalized. In the strict-support branch,
`EquatorTangentExists` now holds **unconditionally** — there is **no surviving spread residual**, no
2D-winding wave needed. The last config (`|Z| ≥ 3`, pairwise non-antipodal, no consecutive pair,
spread > half-circle) is discharged.

### §1 Separation core (pure Mathlib)
- `exists_inner_pos_of_zero_notMem_convexHull` : for a **finite** set `s ⊆ E3`, if
  `0 ∉ convexHull ℝ s` then `∃ t, ∀ v ∈ s, 0 < ⟪t, v⟫`. Route: `Set.Finite.isClosed_convexHull`
  (hull of a finite set is compact ⟹ closed) + `geometric_hahn_banach_point_closed` gives a
  `StrongDual ℝ E3` functional `f` with `f 0 < u < f v` on the hull; `f 0 = 0` so `0 < f v` for
  `v ∈ s ⊆ hull`; Riesz `InnerProductSpace.toDual_symm_apply` converts `f` to `⟪t, ·⟫` with
  `t := (toDual ℝ E3).symm f`. The duality route went through cleanly — no fallback needed.

### §2 The `det3` edge functional over a finite convex combination
- `det3_edge_centerSum` : `det3 a b (∑ y ∈ t, w y • y) = ∑ y ∈ t, w y * det3 a b y` (Finset
  induction on the third-slot linearity `ZinanFFCT10.det3_add_right`/`det3_smul_right`).

### §3 The convex-combination kill (abstract) — `0 ∉ convexHull ℝ Z`
- `zero_notMem_convexHull_edge` : for a fixed edge `(a, b)` of unit vectors with `a ≠ b` and
  `a ≠ -b`, if every member `y` of a finite vector set `s` is either incident
  (`det3 a b y = 0`, and then `y ∈ {a, b}`) or non-incident (`0 < det3 a b y`), then
  `0 ∉ convexHull ℝ s`.

  Proof = the master's argument, made fully uniform (no case split on the support shape):
  1. `0 ∈ convexHull` gives weights `w ≥ 0`, `∑ w = 1`, `∑ w y • y = 0` (`Finset.mem_convexHull'`).
  2. Apply `det3 a b (·)`: `0 = ∑ w y · det3 a b y`, a sum of **nonnegatives**
     (`Finset.sum_eq_zero_iff_of_nonneg`) ⟹ every non-incident weight is `0`. Weight is supported on
     `{a, b}` (filter `F`).
  3. Take `⟪·, a + b⟫` of `0 = ∑_F w y • y`: `0 = ∑_F w y · ⟪y, a+b⟫`. For each `y ∈ F`
     (`y = a` or `y = b`), `⟪y, a+b⟫ = 1 + ⟪a,b⟫ > 0` because `⟪a,b⟫ > -1`
     (unit + non-antipodal, Cauchy–Schwarz equality kill). Again a sum of nonnegatives `= 0` ⟹
     **every** `w y = 0` on `F` ⟹ `∑_F w = 0`, contradicting `∑_F w = 1`.

  This `⟪·, a+b⟫` symmetrization replaces the master's `{a,b}`-support sub-casework (single vertex /
  antipodal pair) with one uniform positivity argument — strictly cleaner, same content. **Any**
  fixed short-arc edge `(a,b)` works; the endpoints landing in `Z` is handled by the same step.

### §4 The complete kill for the opened arm
- `equatorTangentExists_of_strictSupports` : in the strict branch (`hmix`), for **any** arm edge
  `(k, k+1)` that is a `ShortArc`, `EquatorTangentExists A K h₀ δ` holds outright. The equator
  vectors `s := (Z).image (A' ·)` satisfy `hsign`/`hincident`: a vertex `A' m` on the equator with
  `m ∉ {k, k+1}` has `det3 (A' k)(A' (k+1))(A' m) > 0` (`hmix`), and with `m ∈ {k, k+1}` has
  `det3 = 0` (`det3_self_right`/`det3_self_mid`) and equals `A' k` or `A' (k+1)`.

### §5 Tangent-free dichotomy (the downstream wiring)
- `shortArc_edge_zero_of_strict` : on an arm with `3 ≤ n + 1` (every strictly-convex polygon, `≥ 3`
  vertices), the edge `(0, 1)` of the opened arm is a `ShortArc` in the strict branch —
  `A' 0 ≠ A' 1` from `openTail_edge_ne_of_strict` (FFCT30), `A' 0 ≠ -A' 1` from FFCT34's
  `antipodal_pair_excluded_of_strict` with `r = 0`, `s = 1` (`0 ≠ 1`, `0 ≠ 2` via `3 ≤ n+1`).
- `hemiStuck_dichotomy_tangentFree` : the FFCT30 dichotomy with the `EquatorTangentExists` hypothesis
  **DISCHARGED** (for `3 ≤ n + 1`): either some non-incident support vanishes, OR
  `WeakConvexSphArm (openTail A K δ)`. The strict branch produces its own tangent internally via
  §4 + §5. This is the FFCT30 input wired shut.

## Status table (final)

| equator configuration | status |
|---|---|
| `|Z| ≤ 1`                                          | proven (FFCT33) |
| `|Z| = 2`, non-antipodal                           | proven (FFCT33) |
| `|Z| = 2`, antipodal                               | excluded (FFCT34 LEVER 1) |
| `|Z| ≥ 3` with any consecutive pair                | excluded (FFCT34 LEVER 2a) |
| `|Z| ≥ 3`, pairwise non-antipodal, no consec. pair (**spread**) | **KILLED (FFCT36 §3–§4)** |

There is **no remaining residual**. The previously-flagged 2D-winding wave is unnecessary: the
separation argument (the master's convex-combination kill) closes the spread config directly.

## Downstream wiring

In FFCT30's hemi-stuck consumer, replace the call to `hemiStuck_dichotomy_of_glue` (which demands an
`EquatorTangentExists` input) by `ZinanFFCT36.hemiStuck_dichotomy_tangentFree` (which needs only
`3 ≤ n + 1`, automatic for a strictly-convex polygon). For a bespoke edge, use
`equatorTangentExists_of_strictSupports hmix hshort` with any short-arc edge supplied by the arm's
`edge_short`.

No `sorry`, `axiom`, `admit`, or `native_decide`. Independently re-verified: clean-3 on all six
results, 0 errors, 0 warnings.
