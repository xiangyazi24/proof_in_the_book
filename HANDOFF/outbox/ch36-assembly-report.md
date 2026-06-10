# Ch36 Final Assembly — Report

**File:** `ProofsInTheBook/ZinanCh36Assembly.lean` (NEW, sole file created/edited).
**Status:** 0 errors, clean-3 (`propext, Classical.choice, Quot.sound`) on every named result.
No `sorry` / `admit` / `axiom` / `native_decide`. Verified with both
`lake env lean` and full `lake build ProofsInTheBook.ZinanCh36Assembly` (8533 jobs).

## What closed — all 9 bricks of the archived design

The design's `Htube` input was **dropped everywhere** (per the prompt's update):
`ZinanCh36Straddle.split_child_signs_eq_final` discharges the sibling sign sync
UNCONDITIONALLY, so the master induction takes no diagonal-tube hypothesis.

1. **Adapter A** — `exists_near_point_off_generic` (single-polygon off-boundary +
   vertex-generic selector, the one-polygon specialization of the three-polygon perturb
   selector) + `triangle_rayWindValuesWithSign` (triangle guard-ful → ray-indexed
   guard-free via local constancy).
2. **`EarValueSplitData`** — the non-circular split-data structure. **Made `Type`-valued**
   (not the design's `: Prop`) because it carries `σL/σR : RayDirection (child)` as data.
   It never mentions `earDeletedExterior`, so it is non-circular as the induction premise.
3. **`leftEar_rayOrientedWindData`** — the left child IS a 3-gon (`leftLength_earBase`),
   transported via the clean cast helper `rayOrientedWindData_of_eq_three` (a `subst he`
   on `m = 3`, no `Eq.mpr` gymnastics — the size cast was NOT a blocker).
4. **`rayOrientedWindData_of_split`** — the split assembly step: sync the two child signs
   with `split_child_signs_eq_final`, rewrite the right package to the left sign, call
   `rayWindValues_split`. (`def`, since `RayOrientedWindData` is `Type`-valued.)
5. **`rayOrientedWindData_all_of_earValueSplits`** — the strong induction over vertex
   count, no `Htube`. `def` using `Nat.strongRecOn` (the Prop-valued
   `Nat.strong_induction_on` cannot carry a `Type`-valued motive). Right-child descent
   `m ↦ m−1` via `rightLength_earBase`; base `m = 3` via Adapter A.
6. **`earInterior_values_ray`** — the ray-indexed value distribution: `windCross_L = s`
   (left package + odd crossing), `windCross_P = s`, `windCross_R = 0`, all by `omega` on
   the split identity with `s = ±1`. Parent package `HVP` supplied as a hypothesis.
7. **`earDeletedExterior_of_values`** — wires brick 6 into the committed
   `earDeletedExterior_winding_route_sign`.
8. **`EarCutData_of_interiorValues`** — the `EarCutData` builder. Read the REAL fields:
   `hdiag, lax, rax, leftRayEq (∃σL), rightRayEq (∃σR), earOrient, earDeletedExterior`.
   - `earOrient` derived from `lax.noncollinear ⟨1⟩` (new helper `earOrient_of_lax`) —
     NOT taken as an extra input.
   - `earDeletedExterior` produced for an ARBITRARY common-ray `σR` (the field quantifies
     over all of them, not just `D.σR`): the master induction packages L / (given σR) R / P,
     re-synced and re-assembled at the common sign; left-child oddness is **guard-free**
     (`leftEar_interior_odd` via `interior_mem_region`, no vertex-ray side guards needed,
     which the field does not provide); `hRoff` from the unconditional
     `interiorEar_offBoundary_earDeleted`; `hLoff` from `not_onBoundary_of_interior`
     (transported across `m = 3`).
9. **`polygonGeomResidue_of_interiorValues`** + **`artGallery_strict_mod_M`** — plugged the
   builder into the landed `PolygonEarExistence.isConvexVertex'_holds` /
   `artGallery_strict_of_residue`, matching the exact landed signatures.

## Headline statement and exact remaining inputs

```lean
theorem artGallery_strict_mod_M {n : ℕ}
    (ear   : ∀ {m} (_P : StrictSimplePolygon m), Fin m)
    (Esplit: ∀ {m} (P : StrictSimplePolygon m) (ρ : RayDirection P),
               4 ≤ m → EarValueSplitData P ρ (ear P))
    (rest  : ∀ {m} (P : StrictSimplePolygon m) (ρ : RayDirection P),
               PolygonJordan.RemainingResidualData P ρ (ear P))
    (M     : PolygonLast.DiagonalAttachInput (… triangle leaf …))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, PolygonRayIndep.Sees P ρ (P.q v) x
```

**Remaining genuine inputs (honesty contract):**
- **`Esplit`** — the ear-diagonal supply (`EarValueSplitData`). GENUINE architectural input;
  design §3 confirms no unconditional producer of the ear diagonal is landed. NOT manufactured.
- **`rest`** — standard combinatorial cut data (`RemainingResidualData`).
- **`M`** — the peel oracle (`DiagonalAttachInput`).

The base-`n=3` parameter and the convex-vertex containment are **discharged** (proved from the
interior-value ear induction down to the triangle leaf).

## Cast residuals

**None.** The two size casts flagged as the main risk (bricks 3 and 5) both closed cleanly via
`subst` on the `m = 3` / `m − 1` Nat equalities, packaged as the reusable helpers
`rayOrientedWindData_of_eq_three`, `tri_interior_odd_of_eq_three`, `offBoundary_left_of_interior`.
No named cast lemma is left as a residual.
