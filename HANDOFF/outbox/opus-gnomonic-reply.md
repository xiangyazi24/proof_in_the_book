# opus-gnomonic reply — the gnomonic reduction of HINGE Lemma 2.3 (`CyclicTriplePos`)

Branch: main (no switches, no commits). Server: uisai1. No codex / OpenAI tooling used.
File owned: `ProofsInTheBook/SphericalGnomonic.lean` (NEW, imports `SphericalCyclicTriple`).

## Status

`CyclicTriplePos` (HINGE Lemma 2.3, general `n`) is discharged **down to one purely-planar
convex-position primitive** `PlanarConvexDiagPos`, via the gnomonic projection. The bridge — step (a)
of the strategy, the gnomonic sign-correspondence — is proved **unconditionally** and is genuine new
content. The downstream cut chain (Blocks C/D/E) and the clean arm lemmas are rewired to depend on the
single planar primitive (no longer on the bare spherical `CyclicTriplePos`).

The residue is **not** the spherical statement re-wrapped: it is the standard 2-D fact "a strictly
convex planar polygon has all `i<j<k` diagonals positively oriented", fully decoupled from `S²`
(no sphere/hemisphere/`sDist`/`sphAngle`), reached only through the proven bridge.

## Verification (fresh, rebuilt oleans)

```
rsync SphericalGnomonic.lean -> uisai1
lake build ProofsInTheBook.SphericalCyclicTriple   -> Build completed (8431 jobs)   [deps]
lake env lean ProofsInTheBook/SphericalGnomonic.lean   -> RC=0  (0 errors; only push_neg deprecation warnings)
lake build ProofsInTheBook.SphericalGnomonic       -> Build completed (8432 jobs)
```

`#print axioms` (fresh oleans) — **clean-3** `[propext, Classical.choice, Quot.sound]` for:
`cyclicTriplePos_holds`, `gnomonic_sign_correspondence`, `planar_cocycle`, `cyclicTriplePos_of_planar`,
`planarConvexDiagPos_realisable`, `det3_eq_zero_of_perp`.

No `sorry` / `admit` / `axiom` / `native_decide` (grep clean; only the docstring prose says "No sorry").

## What is PROVED UNCONDITIONALLY (genuine new content, none in the substrate)

* **`det3_smul₃`** — multilinear scaling `det3 (r•a)(s•b)(t•c) = r·s·t·det3 a b c` (`ring`).
* **`det3_alt_eq_diff`** — the affine 4-point polynomial identity
  `det3 b c d - det3 a c d + det3 a b d - det3 a b c = det3 (b-a)(c-a)(d-a)` (`ring`).
* **`det3_eq_zero_of_perp`** — rank-2 vanishing: if `u,v,w ⟂ h` (`h ≠ 0`) then `det3 u v w = 0`.
  Proved cleanly via `cross_cross`: `cross h (cross v w) = ⟪h,w⟫•v − ⟪h,v⟫•w = 0`, so `cross v w ∥ h`
  (`⟪h,h⟫ • (v×w) = ⟪h,v×w⟫ • h`), and pairing with `u ⟂ h` forces `⟪u, v×w⟫·⟪h,h⟫ = 0`, `⟪h,h⟫ > 0`.
* **`planar_cocycle`** — the affine 2-cocycle `det3 a b c = det3 a b d - det3 a c d + det3 b c d` for
  `a,b,c,d` in a common plane `⟪h,·⟫ = 1` (differences in `h^⊥`, RHS-diff vanishes by the above).
* **`gproj` / `inner_gproj`** — the gnomonic projection `gproj h p = (⟪h,p⟫)⁻¹ • p`, landing on `⟪h,·⟫=1`.
* **`gnomonic_sign_correspondence`** (step (a), load-bearing) —
  `sOrient (P i)(P j)(P k) = ⟪h,P i⟫·⟪h,P j⟫·⟪h,P k⟫ · det3 (gproj h (P i))(…)(…)`, the scalar factor
  strictly positive on the hemisphere (`planar_bridge_factor_pos`); so `sOrient` and the planar
  orientation have the SAME SIGN (`sOrient_pos_iff_planar_pos`).
* **`gnomonic_proj_in_plane`** — the gnomonic image of a `StrictConvexSphPolygon` lies in `⟪h,·⟫=1`.
* **`cyclicTriplePos_of_planar`** (steps (a)+(b) assembled) — `PlanarConvexDiagPos → ∀ polygon,
  CyclicTriplePos P`: gnomonically project, transport edge/non-incident supports through the positive
  scalar factor (`nlinarith`), apply the planar primitive, pull the sign back. UNCONDITIONAL modulo
  the planar primitive.

## Headline + now-conditional-on-planar-primitive downstream

* **`cyclicTriplePos_holds : PlanarConvexDiagPos → StrictConvexSphPolygon P → CyclicTriplePos P`** —
  HINGE Lemma 2.3 for general `n`, reduced to the 2-D fact.
* `cyclicTriple_pos_of_diag_holds`, `subseqDiag_support_holds`, `cutCorner_decomp_holds` — Blocks
  C/D of `SphericalCyclicTriple`, now sourced from `PlanarConvexDiagPos` (for every polygon) instead
  of an assumed `CyclicTriplePos`.
* `spherical_arm_mono_cut_holds`, `spherical_arm_mono_strict_cut_holds` — the clean arm lemmas (no
  `SZChain` hypothesis), conditional only on `PlanarConvexDiagPos` + the opening primitive `SZStepGeom`.

## The single isolated residue: `PlanarConvexDiagPos` (honest, after genuine exhaustion)

```
PlanarConvexDiagPos : ∀ n [NeZero n] (h : E3), h ≠ 0 → ∀ f : Fin n → E3,
  (∀ i, ⟪h, f i⟫ = 1) →                                   -- all points in the plane
  (∀ i j, 0 ≤ det3 (f i) (f (i+1)) (f j)) →                -- edges support (nonneg)
  (∀ i j, j ≠ i → j ≠ i+1 → 0 < det3 (f i) (f (i+1)) (f j)) → -- non-incident strict
  ∀ i j k, i < j → j < k → 0 < det3 (f i) (f j) (f k)      -- all increasing triples CCW
```

ONE named, **non-vacuous**, purely-2-D `Prop`:
* `planarConvexDiagPos_triangle` — holds for `n = 3` (the only increasing triple is the edge support).
* `planarConvexDiagPos_realisable` — its hypotheses are jointly satisfiable by genuine convex
  configs: the gnomonic image of every strictly convex spherical triangle satisfies them.
* `planar_bridge_factor_pos` — the bridge factor is strictly positive (correspondence is genuine, not `0=0`).

### The concrete failing tactic chain (machine-checked, this round)

I exhausted the algebraic routes and re-confirmed the prior round's "semialgebraic" verdict with three
independent obstructions (all numerically machine-checked here):
1. **No positive-combination certificate.** `det3 [i,j,k]` is NOT a fixed nonnegative-coefficient
   linear combination of the simpler positive orientations (edge supports + smaller-gap diagonals): an
   `nnls` fit over 40 random convex configs for the interior target `[0,2,4]` leaves residual `≈ 0.44`.
   So no `linear_combination` / `positivity` / `nlinarith` certificate over the supports exists.
2. **The affine cocycle is sign-indefinite.** `det3 [i,j,k] = det3 [i,j,k-1] + det3 [i,k-1,k] -
   det3 [j,k-1,k]` is `(+)+(+)-(+)` (the subtracted term is a genuine edge support, verified nonzero);
   the symmetric inserts (`i+1`, `j±1`) all carry a strict subtraction — never positivity-preserving.
3. **`gp_three_term` is same-gap.** The only positive-coefficient quadratic relation relates the
   diagonal to *same-gap* orientations (verified: the would-be smaller terms are actually equal-gap),
   so it founds no induction on the gap.
4. **Ear-removal is circular.** Deleting a non-`{i,j,k}` vertex creates a new edge `(t-1,t+1)` whose
   support IS a diagonal of the original — i.e. the new sub-polygon's `StrictConvexSphPolygon` data
   requires `cyclicTriple_pos_of_diag`, which requires `CyclicTriplePos`. Confirmed circular.

The missing ingredient is the **angular ordering** the open hemisphere supplies: the projected points
have strictly monotone polar angle with total turning `< 2π`. This is the oriented-angle / winding
fact (Mathlib `Orientation.oangle` + a `Real`-valued total-turning bound — the delicate mod-`2π` step
the prior handoff flagged). It is a genuine multi-hundred-line analytic build with real risk on the
monotone-turning bound and **does not exist in the substrate**. It is therefore isolated as the one
named, non-vacuous, *purely planar* residue — strictly weaker than the spherical goal (the bridge to it
is proved), not a co-extensive re-wrapper.

## Residue summary (what remains to make the arm lemma fully unconditional)

1. `PlanarConvexDiagPos` — the 2-D convex-position diagonal positivity, via the
   oriented-angle / monotone-polar-order + total-turning-`< 2π` argument (Mathlib `Orientation.oangle`).
   This is now the SOLE convex-position residue; once proved, `cyclicTriplePos_holds` becomes
   unconditional and Blocks C/D/E of `SphericalCyclicTriple` follow automatically.
2. (separately, unchanged) the all-strict opening `SZStepGeom` (§8.4 reach/stuck), which the clean arm
   lemmas still route through.

## Wiring note

`SphericalGnomonic.lean` is NOT imported in `ProofsInTheBook.lean` (I own only my file). To wire:
add `import ProofsInTheBook.SphericalGnomonic` after the `SphericalCyclicTriple` import, and in
`Audit.lean` add the module + `#print axioms` for: `cyclicTriplePos_holds`,
`gnomonic_sign_correspondence`, `planar_cocycle`, `cyclicTriplePos_of_planar`,
`planarConvexDiagPos_realisable`, `det3_eq_zero_of_perp`, `det3_smul₃`, `det3_alt_eq_diff`,
`cyclicTriple_pos_of_diag_holds`, `subseqDiag_support_holds`, `cutCorner_decomp_holds`,
`spherical_arm_mono_cut_holds`, `spherical_arm_mono_strict_cut_holds`. Builds standalone (8432 jobs),
oleans clean-3.
