# Ch36 ExteriorWindingZero residue — CLOSED (signed local constancy + half-plane escape)

**Status: DONE.** The ChatGPT-Pro design (`HANDOFF/CH36_WINDING_DESIGN.md`) is fully mechanized
in the new file `ProofsInTheBook/PolygonWindingExterior.lean` (≈870 lines). Both headline parts
are proved unconditionally; `ExteriorWindingZero` / `WindZeroExterior` are discharged from a
single named, non-vacuous geometric residue (the ear half-plane containment). No
sorry/axiom/admit/native_decide; no re-wrapper.

## What was proved (faithful to the design)

**(A) `windCross_locally_constant_off_boundary`** — UNCONDITIONAL signed local constancy:
`x ∉ boundary Q → ∀ᶠ y in 𝓝 x, windCross Q σ y = windCross Q σ x` (2D base-point form, stronger
than the design's path-only need; subsumes the prior generic-stratum
`windCross_eventually_eq_basepoint_generic`).
- **Key correction mechanized** (`signed_vertex_transfer` / `vTransfer_const`): at a vertex on the
  ray line the two signed contributions *transfer* (same-side → 0, opposite → ±1), NOT always
  cancel. Proved as an integer (not just mod-2) truth table — the genuine sharpening over the
  unsigned `span_mod_two_through_vertex`.
- **Ray-block collapse**: the substrate's `RayDirection` forbids any edge parallel to the ray
  (`no_adjacent_vertices_both_on_rayLine`), so every maximal ray-block is a SINGLETON vertex —
  the design's general block machinery (`ray_block_signed_sum`, §A2/§A3 block decomposition)
  reduces to the singleton event `signedPair_eventually_eq`. Generic edges:
  `sEdge_eventually_eq_rest` (lifting `rawInd_eventually_eq_basepoint_generic` to signed).
- **Assembly** (`windCross_locally_constant_off_boundary`): R/N/Rest edge split with
  `N = cyclicNext '' R`, mirroring `crossingNumber'_parity_eventually_const`, now signed-integer.

**(B) `ExteriorWindingZero_halfplane`** — the half-plane escape, NO Jordan:
boundary of Q in `hp ≤ 0`, `0 < hp x` ⟹ `windCross Q σ x = 0`.
- `exists_escape_vec`: `v` with `0 < det2 dDir v` AND `det2 σ.r v ≠ 0` (I use the latter rather
  than the design's `v.x ≠ 0` — it directly yields the far-point one-sidedness w.r.t. the actual
  ray `σ.r`, cleaner than the vertical-ray "x-range" argument).
- `escape_avoids_boundary`: `hp(γ t) = hp x + t·det2 dDir v > 0` on `t ≥ 0` ⟹ off boundary.
- `exists_far_T_windCross_zero`: large `T` puts every vertex on one strict side of the ray line
  through `γ T`, so `windCross(γ T)=0` (via existing `windCross_eq_zero_of_all_strictSide`).
- `windCross_constant_on_ray`: ℤ-valued local-constancy (Part A) on the connected `Icc 0 T`
  (clopen fibers) transports `0` back to `x`.

## Discharge of the named residue + the precise conditionality

- `exteriorWindingZero_of_earHalfPlane` : `EarHalfPlaneContainment g → ExteriorWindingZero g`.
- `windZeroExterior_left/right_of_earHalfPlane` : the two `WindZeroExterior` data (the exact
  `PolygonWindingZero.exteriorWindingZero_of_windZeroExterior` interface), PROVED.
- `offDiagDisjoint_via_windingExterior` : `OffDiagDisjoint g` through the signed-winding route
  (ExteriorWindingZero + `offDiagDisjoint_of_cutGeometry` → `WindingSeparates` → OffDiagDisjoint).

**PRECISE HEADLINE CONDITIONALITY.** `ExteriorWindingZero` (and the signed-winding route to
`OffDiagDisjoint`) is closed **conditional on `EarHalfPlaneContainment g`** — the geometric fact
that each ear's boundary lies in the closed half-plane on its own side of the cutting diagonal
line (LEFT in `wDiagSide ≥ 0`, RIGHT in `wDiagSide ≤ 0`). This is the SOLE remaining input: the
abstract `CutGeometry` interface carries the convex vertex, transversality, strict axioms, rays,
and region union/intersection identities, but NOT this ear-sidedness. The residue is named,
non-vacuous (`earHalfPlane_endpoints_on_line`: the shared diagonal endpoints lie on the line, so
both clauses are co-satisfiable along the cut), and faithful (each clause is a real containment,
not an unsatisfiable conjunction).

NOTE: `OffDiagDisjoint` is ALSO available repo-wide UNCONDITIONALLY via
`PolygonContainment.offDiagDisjoint_of_cutGeometry` (from `split_region_intersection`). So the
signed-winding development is an independent, self-contained Jordan-substitute proof — it is not
the only route to disjointness, but it is the route the design targeted and it is now complete.
`artGallery_strict` retains its other oracle inputs (split_region_union, convexVertex,
BaseTriangleFacts, DiagonalAttachInput, and now EarHalfPlaneContainment for the signed route);
closing `ExteriorWindingZero` was the targeted one and is done.

## Verification

- RC: `lake env lean ProofsInTheBook/PolygonWindingExterior.lean` → clean (0 errors).
- FULL build: `lake build` → **Build completed successfully (8651 jobs)**, 0 errors.
- `#print axioms` (from rebuilt oleans), clean-3 on all headlines:
  - `windCross_locally_constant_off_boundary` → [propext, Classical.choice, Quot.sound]
  - `ExteriorWindingZero_halfplane`           → [propext, Classical.choice, Quot.sound]
  - `exteriorWindingZero_of_earHalfPlane`     → [propext, Classical.choice, Quot.sound]
  - `offDiagDisjoint_via_windingExterior`     → [propext, Classical.choice, Quot.sound]
  (no sorryAx, no ofReduceBool/native_decide)
- `rg sorry|admit|native_decide|^axiom` on the new file → none (only the docstring mention).

## Files

- NEW: `ProofsInTheBook/PolygonWindingExterior.lean` (sole writer).
- EDITED: `ProofsInTheBook.lean` (added `import ProofsInTheBook.PolygonWindingExterior` after
  `PolygonWindingZero`). The new file additionally imports `ProofsInTheBook.PolygonContainment`
  (no cycle: both reach down to `PolygonCutClose`).
- Substrate files (`PolygonWinding.lean`, `PolygonWindingZero.lean`) were NOT modified — the new
  results are added in the leaf module and consume the existing `windCross` / `ExteriorWindingZero`
  / `WindZeroExterior` definitions verbatim.

## Residue (precise, non-vacuous)

`EarHalfPlaneContainment g` — per diagonal, left-ear boundary in `wDiagSide ≥ 0`, right-ear
boundary in `wDiagSide ≤ 0`. This is the one geometric datum the abstract cut interface omits;
it is the honest boundary of the signed-winding closure of `ExteriorWindingZero`.

(2 cosmetic linter warnings remain: `unnecessarySeqFocus` at the `vTransfer_const` finisher and
one `<;>`-vs-`;` note. Non-blocking; build is green.)

Branch main; no commits made (per instructions).
