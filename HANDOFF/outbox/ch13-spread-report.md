# Ch13 hemi-stuck — the two support-sign levers (ZinanFFCT34)

**File:** `ProofsInTheBook/ZinanFFCT34.lean`. Compiles 0 errors, 0 warnings, clean-3.
`#print axioms` on all 6 results: `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`, no
custom axioms, no `native_decide`. Only edit: this one new file. No other file touched.

## What landed

Both levers from the report's two-lever sketch are now formalized and axiom-free. They live exactly in
the **strict-support branch** of FFCT30's `hemiStuck_dichotomy_of_glue` (`by_cases hsome` right
disjunct), where `hmix : ∀ i j, j ≠ i → j ≠ i+1 → 0 < sOrient (A' i) (A' (i+1)) (A' j)` is derived from
`¬(∃ support = 0)`. Each lever takes that exact `hmix` signature as a hypothesis, so they are
non-vacuous and directly consumable from that branch (honesty contract verified: the strict context
genuinely carries `¬(∃ support = 0)`).

### §1 The antipodal `det3` algebra (def-independent of `ShortArc`)
- `det3_antipodal_third_eq_zero (x y : E3) : det3 x y (-x) = 0` — one `ring` line after `PiLp.neg_apply`
  (repeated column up to sign).
- `sOrient_antipodal_third_eq_zero` : `(c : E3) = -(a : E3) → sOrient a b c = 0`.

### §2 LEVER 1 — antipodal equator pair is impossible (closes config (a))
- `antipodal_pair_excluded_of_strict` : in the strict-support branch, an antipodal opened-arm pair
  `(A' r : E3) = -(A' s : E3)` with `r ≠ s`, `r ≠ s+1` makes the non-incident support
  `sOrient (A' s) (A' (s+1)) (A' r)` vanish *identically* (the antipodal `det3`), contradicting its
  strict positivity. **The antipodal equator pair is dead in the strict branch.**

### §3 LEVER 2a — consecutive equator pair + any third member is impossible
- `equator_consecutive_triple_excluded_of_strict` : if a consecutive pair `(k, k+1)` and a third index
  `m` (`m ≠ k`, `m ≠ k+1`) all lie on the `h₀`-equator (`h₀ ≠ 0`), the three are `⟂ h₀` hence coplanar,
  so `sOrient (A' k) (A' (k+1)) (A' m) = det3 = 0` (`FFCT33.det3_zero_of_three_on_equator`),
  contradicting strict positivity. **An equator edge cannot coexist with a third equator vertex in the
  strict branch.** (Note this is sharper than FFCT33's `equator_no_three_consecutive`, which only
  excluded *three consecutive*; here the third member can be anywhere.)

### §4 The strict-branch structural residue
- `equatorSet_no_antipodal_pair_of_strict`, `equatorSet_no_consecutive_triple_of_strict` — the two
  levers restated against FFCT33's `equatorSet` membership predicate, ready to thread into the
  dichotomy consumer.

## Status table (updated)

| equator configuration | status |
|---|---|
| `|Z| ≤ 1`                                          | proven (FFCT33) |
| `|Z| = 2`, non-antipodal                           | proven (FFCT33) |
| `|Z| = 2`, **antipodal**                           | **excluded (FFCT34 LEVER 1)** |
| `|Z| ≥ 3` with any consecutive pair                | **excluded (FFCT34 LEVER 2a)** |
| `|Z| ≥ 3`, three consecutive                       | excluded (FFCT33 + FFCT34) |
| `|Z| ≥ 3`, pairwise non-antipodal, no consec. pair | **open (final spread residue)** |

## Honest residual

The single surviving configuration is: `|Z| ≥ 3` equator vertices, **pairwise non-antipodal**,
**no two consecutive arm vertices**, spread across more than an open half of the equator circle. For
this config none of the available `det3` vanishings fire: the non-incident supports at MIXED triples
(a consecutive off-equator pair against an equator vertex) do not vanish identically, so the strict
supports give no contradiction, and the sum functional `EquatorSpreadExcluded` genuinely fails when
`0 ∈ convexHull Z`.

This is the genuine 2D-convexity endpoint flagged in the report: it needs the dipped-chain / winding
argument (the chain between two non-consecutive equator vertices dips strictly off the equator, the
chain crosses the equator `≥ 2|Z|` times, and the gaps confine `Z` to a half-plane — equivalently a
`Mathlib.Analysis.Convex.Separation` argument on the 2D unit circle in `h₀^⟂`). It is NOT dischargeable
from `det3`-vanishing alone and is the honest next wave. No vacuous statements were introduced.

## Downstream wiring

In FFCT30's `hemiStuck_dichotomy_of_glue` strict branch (`¬hsome`, where `hmix` is in scope), invoke
`ZinanFFCT34.antipodal_pair_excluded_of_strict` to kill the antipodal pair and
`ZinanFFCT34.equator_consecutive_triple_excluded_of_strict` to kill any equator edge with a third
member. After these, `equatorTangent_of_sum_pos` need only be supplied for the final
pairwise-non-antipodal, non-consecutive spread, whose separating functional the next wave provides.
