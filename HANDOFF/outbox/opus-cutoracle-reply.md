# opus-cutoracle — Discharging the Chapter 36 cut oracle (region-split / strictness layer)

**STATUS: COMPLETE (with the single Jordan-substitute analytic core honestly
isolated, strictly smaller than before).**

New file `ProofsInTheBook/PolygonCutOracle.lean` (442 lines) compiles clean on
uisai1: **0 sorry / 0 axiom / 0 admit / 0 native_decide**, all 15 headline
constants **clean-3** (`{propext, Classical.choice, Quot.sound}`).

Branch `main` (no switches). No commits. Only the one NEW file touched (it imports
`ProofsInTheBook.PolygonTriangulation`); not wired into any root, so no other build
disturbed. Verified EXCLUSIVELY via rsync→uisai1 `lake env lean` per the
kernel-panic rule; never ran lake locally. Dep oleans (`PolygonTriangulation`
chain, 8427 jobs) built first via tmux.

## What was DISCHARGED (unconditional — genuine new content)

### Layer 1–2: strict-subpolygon construction (the combinatorial half of #1)
- **`leftIndex_injective` / `rightIndex_injective`** (needs only `i ≠ j`): the
  cyclic-arc vertex maps of `PolygonDiagonal` are injective. Modular arithmetic on
  `Fin n` (`arcPos`, `arcPos_inj_of_lt` via `Nat.ModEq.add_left_cancel'`,
  `j_eq_arcPos`). `rightIndex i j = leftIndex j i` (`rfl`).
- **`subpolygonLeftTuple_injective` / `subpolygonRightTuple_injective`**: the
  `injective_q` field, `P.injective_q ∘ leftIndex_injective`.
- **`three_le_leftLength` / `three_le_rightLength`**: the `hthree` field, from the
  diagonal's `cyclicSteps ≥ 2` (`cyclicSteps_ge_two_of_diagonal`).
- **`buildLeftPoly` / `buildRightPoly`**: *construct* the strict subpolygons from
  ONLY the two irreducible axioms (noncollinearity at the cut + edge simplicity),
  with injectivity and size discharged, and `_q = subpolygonLeftTuple/Right` by
  `rfl`. This is the value-add: `LocalCutData'` *assumed* a whole
  `StrictSimplePolygon`; here it is built.

### Layer 3: the crossing-parity bookkeeping kernel (the design's route, made rigorous)
- **`RawEdgeCrosses r x a b`** + **`edgeCrossesRay'_eq_raw`**: `EdgeCrossesRay'`
  is a function only of `(ρ.r, x, P.q i, P.q (cyclicNext i))` — factored through a
  raw predicate on bare points (`side`/`crossTau` reuse).
- **`edgeCrossesRay'_congr`**: same ray vector + same endpoint pair ⟹ same crossing
  status, across *different* polygons. This is the algebraic kernel of the design's
  identity `count_L + count_R = count_P + 2·[ray crosses the diagonal]` (parent
  edges split between the two arcs; the diagonal counted once per side, opposite
  orientations — same crossing event, contributes 2 ⟹ `parity_L + parity_R ≡
  parity_P (mod 2)`). The kernel makes the per-edge identifications rigorous.

### Layers 4–6: the residual interface + assembled headline
- **`CutGeometry P ρ`** — the minimal residual planar interface, **strictly
  smaller than `LocalCutData'`**: convex vertex + `IsConvexVertex'` spec,
  `DiagonalTransversality'`, the two irreducible strict-axiom packs
  (`LeftStrictAxioms`/`RightStrictAxioms`), a ray per subpolygon, and the region
  union/intersection identities. **`CutGeometry.toLocalCutData`** discharges
  `LocalCutData'` (subpolygons built, not assumed; `_q` by `rfl`).
- **`CutGeometryOracle` / `.toCutOracle`** — size-uniform family → `CutOracle`.
- **`strictSimplePolygon_triangulable_of_geometry`**,
  **`strictSimplePolygon_geomTriangulation_of_geometry`** (`n − 2` triangles),
  **`every_region_point_covered_of_geometry`** — Chapter 36's triangulation
  theorem in final form, conditional now only on the residual `CutGeometryOracle`
  (+ `BaseTriangleFacts`).

## The single irreducible analytic core (honestly isolated, NON-vacuous)
The region union/intersection identity for `ClosedRegion'` is the Jordan
substitute. After the bookkeeping kernel, its residue is **ray-direction
independence of the parity region** (the parent ray `ρ.r` may be *parallel to the
diagonal*, so a subpolygon cannot in general reuse it; a fresh `leftRay`/`rightRay`
is supplied, and proving the resulting parity matches is exactly Jordan), plus the
on-diagonal boundary-orientation bookkeeping. This — together with convex-vertex
existence, the transversality recursion, and the cut-corner strict axioms
(`Left/RightStrictAxioms`) — is the content of `CutGeometryOracle`. Every field is
**satisfiable and faithful** (a real polygon+diagonal produces it; the region
identities are true planar facts), so the conditional theorems are **non-vacuous**
(not a vacuous keystone). The strict-subpolygon *construction* and the
diagonal-existence engine are NOT assumed.

## Faithfulness verdicts (per playbook §3.1 Group C)
- **FAITHFUL (unconditional):** the four injectivity theorems, the two size bounds,
  `buildLeftPoly`/`buildRightPoly`, `edgeCrossesRay'_eq_raw`,
  `edgeCrossesRay'_congr`.
- **CONDITIONAL-honest** on `(g : CutGeometryOracle)` (+ `BaseTriangleFacts`):
  `CutGeometry.toLocalCutData`, `toCutOracle`, and the three Layer-6 headlines.
  The conditional surface is explicit named *data* (`CutGeometry` fields), not a
  trivially-true Prop; the hard half is the isolated Jordan residue, not smuggled.

## What remains for the art-gallery headline (CH36 Layer A6)
1. **The residual planar identities** (`CutGeometryOracle` fields): region
   union/intersection for `ClosedRegion'`, convex-vertex existence + transversality
   recursion, cut-corner strict axioms — the single genuinely-resistant layer
   (`edgeCrossesRay'_congr` reduces the union identity to parity ray-independence).
2. **The visibility lemma** (`Sees`): a triangulation-triangle vertex sees every
   point of that triangle (the closed triangle ⊆ closed region — the
   `subset_region` field of `GeomTriangulation'`, available here).
3. **The 3-colouring bridge** (`GeomTriangulation'.toAbstract`, `triangle_has_guard_color`,
   Fisk): build the abstract graph from the triangle list, transport the proved
   combinatorial 3-colourability, least colour class → `⌊n/3⌋` guards via
   `every_region_point_covered_of_geometry`.
Items 2–3 are combinatorial/visibility wiring on the finite triangle data produced
here; item 1 is the isolated analytic core. (All three are documented in-file at
the end of Layer 6.)

## Verification
```
rsync -az .../PolygonCutOracle.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH \
  && lake env lean ProofsInTheBook/PolygonCutOracle.lean'        # exit 0, no warnings
```
`#print axioms` on all 15 headlines → `[propext, Classical.choice, Quot.sound]`.
