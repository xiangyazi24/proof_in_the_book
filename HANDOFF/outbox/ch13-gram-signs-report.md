# Ch13 — `GramSignsAtInteriorBinding` discharge via FRAME-NORMALIZATION (`ZinanFFCT29.lean`)

Opus Lean worker. New file: `ProofsInTheBook/ZinanFFCT29.lean`. Compiles 0 errors, clean-3 on all
main results. No `sorry`/`axiom`/`admit`/`native_decide`. No other file touched. NOT committed.

## The R4 finding (settled FIRST, by inventory of the consumer — per honesty contract)

**The consumer needs BOTH Gram signs, and they are genuinely non-redundant; the one-sided derivative
supplies EXACTLY ONE.**

I inventoried `interior_support_betweenness_of_gramSigns` (FFCT28) and traced the two Gram signs
through the substrate's algebraic core (`SphericalFinish`, `ZinanFFCT27`). The decisive facts:

1. **The two Gram signs ARE the two span coefficients.** Over an independent base `(mid, q)`
   (`ShortArc mid q`), writing the coplanar `p = a•mid + b•q`, FFCT27's `halpha_iff_acoef_nonneg` /
   `hbeta_iff_bcoef_nonneg` give `hα ⟺ a ≥ 0` and `hβ ⟺ b ≥ 0`. So `hα ∧ hβ ⟺ a,b ≥ 0 ⟺ p ∈ span≥0
   {mid,q}` — the two signs together ARE the folded-flat betweenness the consumer produces. The
   residue is therefore **load-bearing**, not free (formalized as `gramSigns_iff_nonneg_coords`).

2. **What the derivative gives = ONE sign (`hβ`).** The monitored family has ONE opening axis `A K`.
   The one-sided extremum `deriv_nonpos_of_left_nonneg_zero` (FFCT26) at a binding `f(δ*) = 0` reads
   out the single axis direction: `f'(δ*) = det3 p (A K) (axis × rot…) = −hβ ≤ 0`
   (`det3_axis_cross_eq_neg_gram`), giving `hβ ≥ 0`, i.e. `b ≥ 0`. This is fully closed
   (`hbeta_at_interior_axis_edge`), unconditionally.

3. **What the derivative CANNOT give = the companion `hα ⟺ a ≥ 0` (the "near side").** The first
   coefficient `a` is not visible to the axis derivative. FFCT27 already records this honestly:
   `halpha_of_acoef_nonneg` takes `a ≥ 0` as a hypothesis, and `design_halpha_hyps_unsatisfiable`
   proves the naive "positive-joint" route to `hα` is **vacuous**. So `hα` is genuinely separate
   content — the B5-B1 no-repeat / positive-joints near-side fact.

**Conclusion of the inventory:** the residue shrinks to EXACTLY the near-side coefficient sign,
named `NearSideCoeffNonneg p mid q := ∀ a b, p = a•mid + b•q → 0 ≤ a`. Everything else — the frame
normalization, the `hβ` sign, the assembly, and the dispatch — is discharged.

## The frame-normalization resolution of the inventory's "multi-rotation" block

The FFCT28 dispatch report flagged the real obstruction: for a GENERAL interior binding, MULTIPLE
`openTail` vertices rotate, so FFCT26's single-rotation `hasDerivAt_mixedSupport` does not apply.

**R1 is the master key and it is already LANDED.** Every rotated `openTail` vertex uses the *same*
axis `A K` and *same* angle θ, so the common-rotation invariance `sOrient_rotS2` /
`det3_rot_rot_rot` (`SphericalCore`) applies to any jointly-rotated slots. This drives:

- **R2 (`constant_binding_false_allRotated` / `_allFixed`):** an ALL-ROTATED or ALL-FIXED binding
  triple has a θ-CONSTANT support (by R1), so binding at δ* forces the ORIGINAL strict support to
  vanish — contradiction with `StrictConvexSphArm.strict_nonincident`. Closed.
- **R3 (`axisEdge_support_single_rot`):** in the dispatch's AXIS-EDGE branch (`c.i+1 = K`, the edge's
  second vertex is the axis), the first vertex `c.i` is fixed (`≤ K`) and the axis `A K` is fixed,
  so EXACTLY the far vertex `c.j` rotates. The support collapses to the single-rotation form
  `sOrient (A i)(A K)(rotS2 (A K) θ (A j))` — the axis in slot 2, moving point in slot 3 — which IS
  the FFCT26 `det3 _ axis (axis × ·)` shape. The multi-rotation worry evaporates in exactly the
  branch the dispatch routes to.

## What CLOSED (unconditional, clean-3)

| theorem | content |
|--|--|
| `sOrient_rot_invariant` | R1 re-export (common-rotation `sOrient` invariance) |
| `supportConstant_allRotated` / `_allFixed` | R2: constant support off the moving frame |
| `constant_binding_false_allRotated` / `_allFixed` | R2: constant binding ⟹ False (strict convexity) |
| `axisEdge_support_single_rot`, `axisEdgeSupport_eq` | R3: axis-edge slot normalization |
| `hasDerivAt_axisEdgeSupport` | the axis-edge support derivative (FFCT26 `hasDerivAt_rot` ∘ det3) |
| `hbeta_at_interior_axis_edge` | **R4 (the ONE sign): `hβ` from the one-sided extremum** |
| `halpha_of_nearSide` | R4 companion: `hα` from the named near-side residue |
| `gramSigns_iff_nonneg_coords` | the completeness check: both signs ⟺ nonneg-cone (residue is load-bearing) |
| `gramSigns_of_nearSide_axisEdge` | **R5: full `GramSignsAtInteriorBinding` at the axis-edge binding** |
| `interiorAxisEdge_stuck_betweenness` | **R5: STUCK → folded-flat betweenness (sharpest honest dispatch)** |

`#print axioms` on all main results → `[propext, Classical.choice, Quot.sound]` (clean-3).

## The named residue (the honest block)

`NearSideCoeffNonneg p mid q : Prop` — the near-side coefficient sign `a ≥ 0` of the span
decomposition `p = a•mid + b•q`. This is EXACTLY the `hα` content (`halpha_iff_acoef_nonneg`), the
single piece the axis derivative cannot read out. It is satisfiable and non-vacuous: over an
independent base the decomposition is unique, so it is a genuine single-real-sign condition,
equivalent to the `hα` Gram inequality (guard `example` at end of file).

The dispatch `interiorAxisEdge_stuck_betweenness` consumes `NearSideCoeffNonneg` plus the standard
opening inputs (the binding `supportConstraint = 0` at δ*, the opened edge short arc, the
admissible-nonneg-on-`[0,δ*]` one-sided input, and `ShortArc mid p`) and produces the
`FoldedFlatCutTransportPlus` betweenness through FFCT28's `supportStuck_dispatch_partial`.

## Residues / next bricks (out of this file's scope)

- **Producing `NearSideCoeffNonneg` for the binding** — the near-side / no-repeat positive-joints
  geometric fact. This is the genuine remaining mathematical content, now isolated to a SINGLE real
  sign (down from the original two-Gram-sign "master").
- The non-axis-edge dispatch branch (`c.i+1 ≠ K`): either reduces to R2 (constant binding ⟹ False
  when the far vertex is not the sole rotator) or to another single-rotation normalization via R1 —
  the frame-normalization bricks (R1/R2/R3) are in place to handle it; only the slot-permutation
  sign-tracking for the non-axis far vertex remains.
- The admissible-nonneg-on-`[0,δ*]` hypothesis (`hadm`) is taken as input; it is the standard
  monitored-path admissibility supplied upstream by `admissibleSet` (the path from 0 to δ* stays
  admissible by the closure structure).

## Verification

- `lake env lean ProofsInTheBook/ZinanFFCT29.lean` → 0 errors.
- `lake build ProofsInTheBook.ZinanFFCT29` → built (8488 jobs).
- `#print axioms` on all main results → clean-3.
- No forbidden tokens (`sorry`/`admit`/`axiom`/`native_decide`) outside the docstring.
