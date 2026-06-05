# TetVolume.lean — COMPLETE

## Status: DONE. `theorem volumeTetFormula : VolumeTetFormula` proved, 0 sorry/axiom/admit.

New file: `ProofsInTheBook/TetVolume.lean` (425 lines, imports `ProofsInTheBook.TetPearls`).
No other file touched.

## Verification
- `lake env lean ProofsInTheBook/TetVolume.lean` → clean (no errors, no warnings).
- `lake build ProofsInTheBook.TetVolume` → `✔ Built ... Build completed successfully`.
- `#print axioms volumeTetFormula` (from rebuilt oleans) →
  `[propext, Classical.choice, Quot.sound]`.  No `sorryAx`, no `ofReduceBool`/`trustCompiler`.

(TetPearls.olean was rebuilt first per instructions — built clean before this file was verified.)

## Proof route (as specified in the brief)
1. **Corner-simplex volume, built from scratch** (Mathlib has no simplex-volume lemma).
   `volume_cornerSimplex (n) (c ≥ 0) : volume {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ x i ≤ c}
   = ofReal (cⁿ / n!)`, by induction on `n`:
   - split `Fin (n+1) → ℝ ≃ᵐ ℝ × (Fin n → ℝ)` via `volume_preserving_piFinSuccAbove 0`;
   - Tonelli (`Measure.prod_apply`): the prod measure of the (measurable) product-shaped set is
     `∫⁻ t, volume(slice at t)`;
   - each slice is `cornerSimplex n (c−t)`; its volume is `ofReal((c−t)ⁿ/n!)` for `t ≤ c` by IH and
     `0` for `t > c` (corner simplex empty when size `< 0`, valid for all `n` incl. `0`);
   - integrand `= indicator [0,c] (ofReal((c−t)ⁿ/n!))`; convert lintegral→`ofReal` of a Bochner
     interval integral; substitute `u = c−t` and `integral_pow` ⇒ `c^(n+1)/(n+1)!`.
2. **Transport to `EuclideanSpace ℝ (Fin 3)`**: `cornerSimplexE` is the preimage of `cornerSimplex 3 1`
   under the volume-preserving `(MeasurableEquiv.toLp 2).symm`
   (`EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`) ⇒ `volume cornerSimplexE = 1/6`.
3. **Standard simplex = convex hull of `{0, e₀, e₁, e₂}`**:
   `convexHull_stdVerts_eq_cornerSimplexE` — `⊆` by `convexHull_min` + convexity of the half-space
   intersection; `⊇` by exhibiting each point as a `Finset.centerMass` with weights
   `(1−∑x, x₀, x₁, x₂)`.
4. **Affine parametrization** `edgeAffine T x = v0 + edgeLin T x`, `edgeLin T = toEuclideanLin (edgeMatrixᵀ)`.
   - `edgeLin_single`: `edgeLin (eⱼ) = v(j.succ) − v0` (so `edgeAffine` maps the 4 std vertices onto
     `range T.v`); via `AffineMap.image_convexHull` ⇒ `T.carrier = edgeAffine '' cornerSimplexE`.
   - `det_edgeLin`: `LinearMap.det (edgeLin T) = det edgeMatrix` (`det_toLin` over the `basisFun` basis
     + `det_transpose`).
   - `volume_edgeAffine_image`: translation invariance (`measurePreserving_add_left`) +
     `Measure.addHaar_image_linearMap` (scales by `|det|`).  Note: works even if det = 0.
5. **`volumeTetFormula`**: chain the above ⇒
   `volume T.carrier = ofReal|det edgeLin| * ofReal(1/6) = ofReal(|det edgeMatrix|/6)`.

## Notes
- `affIndep` is NOT needed (the change-of-variables lemma handles the singular case 0 = 0), so the
  proof is unconditional over all `Tet`.
- To wire into the root module / Audit, add `import ProofsInTheBook.TetVolume` (and a
  `#print axioms volumeTetFormula` line in Audit.lean if desired) — I did not touch those files.
