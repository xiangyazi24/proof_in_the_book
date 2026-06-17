# Ch13 B1 hemi-stuck — sharpening `EquatorTangentExists` (ZinanFFCT33)

**File:** `ProofsInTheBook/ZinanFFCT33.lean`. Compiles 0 errors, 0 warnings, clean-3.
`#print axioms` on all 9 main results: `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`,
no custom axioms, no `native_decide`. Only edits: this one new file. No other file touched.

## The exact residual (from FFCT30)

```
EquatorTangentExists A K h₀ δ :=
  ∃ t : E3, ∀ r, ⟪h₀, A' r⟫ = 0 → 0 < ⟪t, A' r⟫,   A' := openTail A K δ.
```

**Key fact read off the statement:** `t` carries NO tangent-plane constraint — it is an arbitrary
`E3` vector. This is decisive. The consumer (`hemiStuck_dichotomy_of_glue`) feeds `t` into
`exists_unit_perturbed_normal_of_tangent`, which only needs `⟪t, A' r⟫ > 0` on the equator set; it does
NOT need `⟪t, h₀⟫ = 0`. So a unit vertex `v ∈ Z` already self-separates (`⟪v,v⟫ = 1 > 0`), and the
generic cases are trivial.

## What landed (all unconditional, axiom-free)

### §1 Abstract positive-functional core (pure inner product, reusable for any finite family)
- `exists_pos_functional_of_sum_pos` — the clean separation reduction: for ANY `P : Fin m → E3` and
  ANY predicate `Z`, the **equator sum** `t := Σ_{i∈Z} P i` is a common strictly-positive functional
  for `Z` as soon as it is positive against each member. (Witness is literally the sum.)
- `exists_pos_functional_of_card_le_one` — `|Z| ≤ 1` on UNIT vectors: sum is `0` (empty, vacuous) or
  the single vertex `v` (`⟪v,v⟫ = 1`). **Discharged.**
- `exists_pos_functional_of_pair_not_antipodal` — `Z = {a,b}`, `P a ≠ -(P b)` on UNIT vectors:
  `t = P a + P b`, since `⟪t, P a⟫ = 1 + ⟪P a,P b⟫` and `⟪P a,P b⟫ > -1 ⟺ ¬antipodal` (Cauchy–Schwarz
  equality ⟹ antipodal). **Discharged.**

### §2 No-3-consecutive structure (unconditional)
- `det3_zero_of_three_on_equator` — three vectors `⟂ h₀` (`h₀ ≠ 0`) in `E3` are coplanar:
  `det3 x y z = 0`. Proved by the **Cramer/Plücker cofactor identity**
  `⟪h₀,h₀⟫·det3 x y z = ⟪h₀,x⟫·det3 h₀ y z − ⟪h₀,y⟫·det3 h₀ x z + ⟪h₀,z⟫·det3 h₀ x y`
  (pure `ring` after coordinate expansion), with the RHS vanishing and `⟪h₀,h₀⟫ > 0`. No basis,
  no case split.
- `equator_no_three_consecutive` — on a weakly-convex `PositiveJoints` arm with the non-flat bound
  (`StrictConvexSphArm B`, `JointLe A' B`), three CONSECUTIVE interior vertices on the `h₀`-equator give
  `det3 = 0`, which `ZinanFFCT22.far_fold_tail_not_interior` collapses to a flat apex joint —
  excluded. So the equator set has no three consecutive members.

### §3 Reduction to a strictly smaller named residual
- `equatorSet`, `equatorTangent_of_sum_pos`, `equatorTangent_of_card_le_one`,
  `equatorTangent_of_pair_not_antipodal` — §1 instantiated with `P r := openTail A K δ r` (unit via
  `S2.inner_self`), discharging `EquatorTangentExists` outright for `|Z| ≤ 1` and non-antipodal pairs.
- `EquatorSpreadExcluded A K h₀ δ` — the **strictly smaller** named residual: the equator-vertex sum is
  strictly positive against every equator vertex. `equatorTangent_of_spreadExcluded` shows it entails
  `EquatorTangentExists`. `equatorSpreadExcluded_base` proves non-vacuity at `δ = 0` (empty equator).

## Honest assessment of what remains

`EquatorSpreadExcluded` is genuinely smaller than `EquatorTangentExists`:

| equator configuration | status |
|---|---|
| `|Z| ≤ 1` | **proven** (`equatorTangent_of_card_le_one`) |
| `|Z| = 2`, non-antipodal | **proven** (`equatorTangent_of_pair_not_antipodal`) |
| `|Z| = 2`, antipodal | open — sum `v + (−v) = 0`, the sum criterion fails |
| `|Z| ≥ 3`, spread > half-circle | open — sum criterion can fail |
| `|Z| ≥ 3`, three consecutive | **impossible** (`equator_no_three_consecutive`) |

So the surviving content is: an antipodal equator pair, or a `≥ 3`-vertex equator pattern spread across
more than an open half of the equator circle (and necessarily non-consecutive, by §2).

### Sketch for the next wave (why the spread configs should be killable)

The sum criterion `EquatorSpreadExcluded` is *sufficient* but not necessary: the true iff is
"`Z` lies in an open half-circle ⟺ `0 ∉ convexHull Z`" (standard finite-dimensional separation,
`Mathlib.Analysis.Convex.Separation`). The sum-of-vertices is one explicit separating functional that
works exactly when `Z` is not too spread. Two mathematical levers for the spread case, not yet wired:

1. **Antipodal pair `v_r = −v_s` on the equator.** At `δ*` all WeakConvex edge supports are `≥ 0`
   (admissibility closure). An edge `(A' i, A' i+1)` whose great circle is the equator plane itself
   would have to support both `v_r` and `−v_r` on the `≥ 0` side — forcing the support `= 0` on a
   genuine antipode, i.e. a degenerate (great-circle) edge. The opened arm's edges are short arcs
   (`edge_short`, not antipodal), and the global support sign should pin the equator vertices to one
   side of SOME non-equatorial supporting edge, breaking the antipodal symmetry. This is the
   `WeakConvex edge supports vs equator plane` sign obstruction flagged in the prompt — it needs the
   support functionals at `δ*` threaded in, which is the next file's input.

2. **`≥ 3` non-consecutive spread.** Between two non-consecutive equator vertices `j, j+m` (`m ≥ 2`),
   the intermediate chain `A'(j+1), …, A'(j+m−1)` is NOT on the equator (by §2 no-3-consecutive, at
   least the interior ones dip off it), and weak convexity forces them strictly to one side. The
   supporting edge of such a dipped vertex is a great circle distinct from the equator plane; its `≥ 0`
   support constraint, combined with the equator vertices lying on it, should confine all equator
   vertices to a half-plane of the equator — exactly `0 ∉ convexHull Z`. Formalizing this is the real
   2D-convexity work (circular gaps / `convexHull` separation); it is NOT dischargeable from the §1–§2
   facts alone and is the honest endpoint for today.

## Downstream wiring

`EquatorSpreadExcluded` now replaces `EquatorTangentExists` as the sole hemi-stuck input: substitute
`equatorTangent_of_spreadExcluded` wherever FFCT30's `hemiStuck_dichotomy_of_glue` /
`hemiStuck_forces_supportStuck_or_weakConvex` consume `EquatorTangentExists`. The generic configurations
(`|Z| ≤ 2` non-antipodal) are then fully closed in-line via the §3 discharges; only the antipodal/spread
residue survives, sharply named and with a concrete attack vector for the next wave.
