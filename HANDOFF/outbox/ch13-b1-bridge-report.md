# Ch13 CUT-replacement brick 3 — B1 → CutReady bridge at the WBS support-stuck sup

**File:** `ProofsInTheBook/ZinanFFCT49.lean` (321 lines, clean-3, 0 errors).
**Verify:** `lake env lean ProofsInTheBook/ZinanFFCT49.lean` on uisai2 — every `#print axioms` reports
only `[propext, Classical.choice, Quot.sound]`. No `sorry`/`admit`/`axiom`/`native_decide`.

## What was built

`cutReadyData_of_supportStuckWBS`: the bridge from the landed B1 Gram line to a `StuckAtKData`-carrying
cut-ready datum at the **support-stuck** supremum of the hemisphere-free monitored family `WBS`
(FFCT45/46/47). Target is a LOCAL `CutReadyData A' B` (structural twin of the sibling-owned
`CutReadyPlus`; assembly wave identifies them). The opened arm is `A' := openedWBS A B k =
openTail A K (-δ*_WBS) = openTailW A K δ*_WBS`.

`CutReadyData` was defined as a `Prop`-valued **existential** over the cut `(i, j)`, not a bare
`structure ... : Prop`. Finding: the design §5 shape `structure CutReadyPlus : Prop where i j : ℕ; …`
does **not** elaborate — a `Prop`-structure cannot project its non-`Prop` data fields `i, j` (Lean rejects
`failed to generate projection … field must be a proof`). The sibling `ZinanFFCT48` will hit the same wall;
the existential bundling (`∃ i j (hsk : StuckAtKData A B i j), hAe ∧ hBe`) is the correct `Prop` form and
is what the assembly wave should identify with.

## What closed (discharged in-bridge, no residue)

- **`hsupp`** (the binding) — threaded from the normalization datum's vanishing support at the normalized
  triple.
- **non-antipodal half of `hsa`** — `(A'(i+1) : E3) ≠ -(A' j : E3)` from the open hemisphere
  (`openHemisphere_at_WBS_sup`, FFCT46, margins-free), via the re-instantiated separating-normal argument
  `hemisphere_nonAntipodal` / `shortArc_of_hemisphere`. The hemisphere itself is now **unconditional** at
  the WBS sup: FFCT47 discharged the wrap-edge residual, so `openedEdges_short_at_supWBS_of_wrap
  (openedWrapShortArc_at_supWBS …)` and `openedJoints_in_Ioo_at_supWBS` feed brick 4 with no hypothesis.
- **`hside`** (equal first side) — `sDist (B(i+1))(B i) = sDist (A'(i+1))(A' i)` from `SameSides A' B` via
  the `sideLen`/`sDist` bridge at the consecutive pair (`hside_of_sameSides`, proved from
  `openTail_preserves_sides`-style side equality + `sDist_comm`).

## The TWO surviving named residues (satisfiable, refutation-checked)

1. **`WBSGramSigns`** — the two Gram inequalities `hα`, `hβ` of the opened triple `(A' i, A'(i+1), A' j)`.
   This is the genuine B1 residue, exactly `ZinanFFCT28.GramSignsAtInteriorBinding`'s two Gram conjuncts.
   FFCT28's inventory finding is decisive: a GENERAL interior binding has two-or-three rotating slots under
   `openTail` (any of `c.i, c.i+1, c.j` with value `> K`), so the banked single-rotation derivative
   (FFCT26's `hasDerivAt_mixedSupport`, the `openArm` last-joint vocabulary) does **not** apply. FFCT29
   discharges `hβ` only in the *axis-edge* sub-case `c.i+1 = K` (where exactly the far vertex rotates), and
   even there leaves `hα` as `NearSideCoeffNonneg`. **The pred-degenerate corner is subsumed here:** it is
   the `hα`/near-side coefficient sign, the one the one-sided extremum cannot read out. Not killable in this
   brick — for a general (non-axis-edge) binding both `hα` and `hβ` survive. Named, not faked. Non-vacuity:
   guarded `wbsGramSigns_alpha`; it is exactly the betweenness-coordinate pair (FFCT29
   `gramSigns_iff_nonneg_coords`), so load-bearing.

2. **`WBSCutNormalization`** — the structural inputs the design §5 outcome assembler supplies: the
   ℕ-orientation `i+1 < j ≤ n`, the vanishing support at the *normalized* triple, the distinctness half of
   `hsa` (`A'(i+1) ≠ A' j`, the no-nonadjacent-repeat fact), and the ear interval-arm convexity certificates
   `hAe`/`hBe`. Non-vacuity: guarded `wbsCutNormalization_orientation`.

## The orientation-gap resolution (the real structural finding)

`StuckAtKData.hij1 : i+1 < j` is a hard ℕ-ordering constraint. `NonIncident n` supplies only the *Fin*
disequalities `c.j ≠ c.i ∧ c.j ≠ c.i+1` — the ℕ-value order `c.i+1 < c.j` is **not** implied, and
`c.j < c.i` is possible. Since `sOrient = det3` is slot-antisymmetric, a `c.j < c.i` binding is the same
planar collinearity read with the opposite sign/role convention. **The gap is not silently reversed:** the
cut normalization (which endpoint is the near one, hence the ℕ-order and the matching signed support) is
part of the design §5 outcome assembler's job, performed upstream when it selects the cut `(i,j)` with
`i+1 < j` from the produced vanishing triple. The bridge therefore exposes the normalized `(i,j)` + the
matching `hsupp` as fields of `WBSCutNormalization` and consumes them verbatim. This is the honest place
for the gap — naming it, not faking a Fin→ℕ reversal lemma that the substrate does not have
(`SphericalLastCornerStuck` records: "No reversal-invariance lemma for `StrictConvexSphArm` exists").

## The `hsa`-distinctness / no-repeat finding

`ShortArc = distinct ∧ non-antipodal` (FFCT47). The open hemisphere forces **non-antipodal** for any two
opened vertices but does **not** force *distinct* at non-adjacent indices (two distinct indices can map to
the same point — a nonadjacent vertex repeat, NoNonadjacentRepeat territory). So the distinctness half is
genuinely separate content; it is bundled into `WBSCutNormalization.hrepeat` rather than fabricated.

## Interval convexity (`hAe`/`hBe`)

There is **no banked interval-convexity preservation theorem** in the substrate — every consumer
(`SphericalCutTransport`, `ZinanFFCT19`, `SphericalStuckGeneral.stuckAtK_endpt_le`) carries `hAe`/`hBe` as
*data*. So the bridge carries them too (in `WBSCutNormalization`). Deriving "the interval of a weak arm is
weak" would be a separate brick; it is correctly left as a supplied certificate here.

## Bottom line

The bridge wiring is complete and clean-3. The B1 line's conditional corner surfaces exactly as predicted:
the multi-rotation Gram signs (`WBSGramSigns`, subsuming the pred-degenerate/near-side corner) are the one
genuine geometric residue; the orientation gap + no-repeat distinctness + interval convexity are the
structural normalization inputs (`WBSCutNormalization`). Both are named, satisfiable, and non-vacuity
guarded. Everything the WBS support-stuck context + open hemisphere + SameSides genuinely supplies is
discharged in-bridge.
