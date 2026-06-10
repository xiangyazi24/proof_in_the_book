# Ch36 Interior-Value Package — Worker Report

File: `ProofsInTheBook/ZinanCh36InteriorValue.lean` (NEW, ~250 lines incl. docs).
Verified on uisai2: **0 errors, 0 warnings, 0 sorry/admit/axiom/native_decide.**
All six `#print axioms` are clean-3 (`propext`, `Classical.choice`, `Quot.sound`).

## What was implemented

All four requested bricks compiled, plus two consequence wrappers.

### Brick 1 — the value package + odd consequence
- `def WindValuesWithSign (P : StrictSimplePolygon n) (s : ℤ) : Prop` :=
  `(s = 1 ∨ s = -1) ∧ ∀ (ρ : RayDirection P) (x : Pt), ¬ OnBoundary P x → (∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) → windCross P ρ x = 0 ∨ windCross P ρ x = s`.
  The two off-boundary guards are EXACTLY those of `ZinanCh36Interval.windCross_mem_final`
  (`hoff : ¬ OnBoundary P x`, `hvert : ∀ k, side ρ.r x (P.q k) ≠ 0`).
- `WindValuesWithSign.sign_unit`, `WindValuesWithSign.values` (accessor lemmas).
- `wind_eq_sign_of_odd` (the consequence lemma): under the package, `Odd (CrossingNumber' P ρ x)`
  ⟹ `windCross P ρ x = s`. Proof: `windCross_ne_zero_of_odd_crossing` rules out `0` from `{0,s}`.

### Brick 2 — signed exterior route
- `earDeletedExterior_winding_route_sign`: generalizes
  `PolygonWindingBound.earDeleted_exterior_of_bound` from the hard-coded value `1` to the sign `s`.
  Statement: `windCross_L = s`, `windCross_P = s`, `x` off `R`'s boundary ⟹ `¬ ClosedRegion' R σR x`.
  Proof: `windCross_split_common` gives `L + R = P`; substitute `L = s`, `P = s`, `omega` ⟹ `R = 0`;
  feed `outside_of_subWinding_zero` (= `PolygonWindingPath.notClosedRegion'_of_windZero`).
  ~12 lines — the split identity is sign-agnostic, so the adaptation is verbatim with `1 → s`.

### Brick 3 — split distribution
- `windValues_split_offAll`: at a diagonal, for `x` off ALL THREE boundaries (P, L, R) with the
  three vertex guards, under `WindValuesWithSign L s` and `WindValuesWithSign R s`, exactly one of
  `(L=0,R=0,P=0)`, `(L=s,R=0,P=s)`, `(L=0,R=s,P=s)` holds. The both-interior `L=R=s` state is
  excluded because it forces `P = 2s ∈ {2,-2}`, outside the unconditional kernel bound
  `windCross_P ∈ {0,1,-1}` (`windCross_mem_final`). Proof: collect the three winding facts
  (package on L, package on R, bound on P) + the split identity, then one
  `rcases ... <;> ... <;> omega` over all value/sign cases.
- `windValues_parent_of_split` (consequence): parent inherits `windCross_P ∈ {0,s}` — the package
  value propagates to the parent.

### Brick 4 — ear-interior value
- `earInterior_values_of_rightValues`: under the package on both sub-polygons, at a point off all
  three boundaries with ODD left (ear-triangle) crossing number, returns
  `windCross_L = s ∧ windCross_R = 0 ∧ windCross_P = s`. Proof: `wind_eq_sign_of_odd` on L gives
  `L = s`; then the split distribution's `L=s` branch is the unique consistent one.
- `earDeletedExterior_of_package_interior` (consequence): the `¬ ClosedRegion' R σR x` exterior
  conclusion derived purely from the package + ear-interior point (Brick 4 ⟹ Brick 2), no
  half-plane anchor.

## Hypothesis-shape decisions (documented, no silent strengthening)

1. **Three-boundary off-conditions for the split.** The split bricks require `x` off ALL THREE
   boundaries — `¬ OnBoundary` and the vertex guard `∀ k, side σ.r x (Q.q k) ≠ 0` — for P, L, and
   R independently. This is the WEAKEST set under which: (a) the package dichotomy fires on L and R
   (`WindValuesWithSign.values` needs each polygon's own off-guards), and (b) `windCross_mem_final`
   fires on P. The guards are stated per-polygon over each polygon's own vertex tuple
   (`(buildLeftPoly h lax).q k`, etc.) and ray (`σL.r`, `σR.r`, `ρ.r`), matching the exact shapes
   in `Harvest.sub_regions_not_both_inside_kernel`. They are satisfiable simultaneously off a
   measure-zero set (the union of the three boundaries + the three vertex-ray exceptional sets), so
   the hypothesis set is NOT vacuous.

2. **`s` is carried as a free `{1,-1}` parameter**, per the design's sign-discipline directive; the
   `=1` consumers of the harvest are recovered by instantiating `s := 1`. No global shoelace /
   orientation computation is performed here (that is the SIGN SYNCHRONIZATION master brick, out of
   scope for this worker file).

3. **Brick 4 interiority is encoded as `Odd (CrossingNumber' L σL x)`** (left-crossing parity),
   which is the region-membership form `ClosedRegion'`/`InteriorOddSeed` use off the boundary. This
   matches the existing `seed_forces_odd_crossing` interface and avoids importing a `closedTri`
   geometric-interior hypothesis the value engine cannot consume directly. The connection
   "geometric ear-interior ⟹ odd left crossing" is the seed/triangle-base content (master bricks
   `triangle_windValuesWithSign` / the seed), deliberately left as the caller's obligation — this
   file consumes the parity form, does not manufacture it.

## Nothing blocked

All four bricks + two consequences closed cleanly. The masters' remaining work (per the design):
the TRIANGLE SIGNED BASE (`triangle_windValuesWithSign`), the SIGN SYNCHRONIZATION through the peel
tree, the `orientedWindData_all` induction, and the on-diagonal PERTURB wrapper — none of which are
worker bricks. This file supplies the algebraic core they compose over: the package definition, the
split that propagates the sign, and the exterior route at the propagated value.

## Names grepped/used (no inventions)
- `windCross`, `windCross_split_common`, `windCross_ne_zero_of_odd_crossing` (PolygonWinding)
- `windCross_mem_final` (ZinanCh36Interval)
- `outside_of_subWinding_zero` (PolygonWindingBound) → `notClosedRegion'_of_windZero` (PolygonWindingPath)
- `OnBoundary`, `side`, `ClosedRegion'`, `CrossingNumber'`, `IsDiagonal'`, `buildLeftPoly`,
  `buildRightPoly`, `LeftStrictAxioms`, `RightStrictAxioms` (substrate / cut oracle)
