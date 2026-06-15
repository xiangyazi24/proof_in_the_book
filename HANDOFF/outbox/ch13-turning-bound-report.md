# Ch13 planar turning bound + oriented single-wind residue — report (`ZinanFFCT96`)

**File:** `ProofsInTheBook/ZinanFFCT96.lean` (imports `ZinanFFCT95` +
`Mathlib.Analysis.SpecialFunctions.Complex.Arg`).
**Status:** clean full `lake build ProofsInTheBook.ZinanFFCT96` on uisai2
(HEAD cf30857), 8551 jobs, 0 errors. Every theorem `#print axioms` =
`[propext, Classical.choice, Quot.sound]`. No `sorry`/`admit`/`axiom`/`native_decide`
(verified by proof-term grep). File LEFT in place; not committed.

## Load-bearing finding: the FFCT95 residue is over-quantified (and unprovable as stated)

`ZinanFFCT95.StrictPlanarChainLiftedTurnSpanExists` quantifies over **every**
orthonormal frame `(u,v) ⊥ h`. This is **FALSE for the wrong-handed frame** and
therefore not provable as written:

- For a strictly convex chain `Q` (intrinsic left turns, `det3(Qᵢ)(Qᵢ₊₁)(Qⱼ)>0`)
  and a frame with `det3 h u v < 0`, the edge directions rotate **clockwise** in
  `(u,v)` coordinates ⟹ every signed per-joint turn is **negative** ⟹ no lift
  can satisfy `turn_pos` (θ strictly increasing) with all gaps `< π` (a clockwise
  turn by `α∈(0,π)` is a CCW turn by `2π−α > π`, violating `turn_lt_pi`).
- Swapping `u ↔ v` preserves *every* hypothesis of the residue (the inner-product
  conditions are swap-symmetric; the `det3`/in-plane conditions don't mention
  `u,v`) but flips `sign(det3 h u v)`. So the residue must hold for both frames or
  neither — and it provably fails for one. **Numerically confirmed** (CCW convex
  chain: frame `det=+1` gives turns all `> 0`; frame `det=−1` gives turns all `< 0`).

The repair is the **oriented** residue adding `0 < det3 h u v`. This is exactly
the orientation the real application always supplies: `exists_orthoFrame`'s frame
has `v = cross h u`, for which `det3 h u v = ⟪h, cross u v⟫ = ⟪h,h⟫ = 1`
(`exists_orthoFrame_oriented`, proved here).

## What landed UNCONDITIONALLY (the full construction)

- `det3_frame_coord` — `det3 h (a•u+b•v)(c•u+d•v) = (a*d−b*c)·det3 h u v` (the
  multilinear shadow: planar `det3` signs ↔ `2×2` frame-coordinate determinants).
- `exists_orthoFrame_oriented` — oriented orthonormal frame with `det3 h u v = 1`.
- `det3_eq_det3_h_diff` — in-plane `det3 a b c = det3 h (b−a)(c−a)`.
- `perp_decomp` — in-plane vector `= ⟪·,u⟫•u + ⟪·,v⟫•v` (via `normsq_smul_b`).
- `liftedAngle` / `liftedAngle_succ` / `liftedAngle_exp` / `liftedAngle_cos_sin` —
  the **analytic lift**: θₘ = arg(z₀) + Σ arg(conj zₖ·zₖ₊₁), with the
  angle-addition induction proving `‖z m‖·exp(θₘ I) = z m` and extracting
  `cos θₘ = (z m).re/‖z m‖`, `sin θₘ = (z m).im/‖z m‖`.
- `arg_mem_Ioo_of_im_pos` — `Im z > 0 ⟹ arg z ∈ (0,π)`.
- `edgeZ` / `edgeZ_arm` / `edgeZ_turn_im_pos` — the edge complex sequence and the
  strict-turn sign: `det3(Qₘ)(Qₘ₊₁)(Qₘ₊₂) > 0 ⟹ Im(conj zₘ·zₘ₊₁) > 0`.
- **`oriented_residue_of_turningBound`** — the full `PlanarLiftedTurnSpan`:
  `θ` (geometric lift on the arm + a slack linear continuation `δ=(2π−S)/3` past
  the open arm), `ρ = ‖z·‖`, `ρ_pos`, `edge_eq`, `turn_pos∈(0,π)`,
  `turn_lt_pi`, and `one_wind = S + 2δ = (S+4π)/3 < 2π ⟺ S < 2π`. **Modulo the one
  residual below.**
- **`strictConvexSphArm_gnomonicSingleWind'`** — `ZinanFFCT95.GnomonicSingleWind A`
  for any strictly convex spherical arm, built with the *oriented* frame
  (repairing FFCT95's orientation gap). **Modulo the one residual.**

## The single isolated residual

`OpenConvexArmTurningLtTwoPi : Prop` — the total turning of the open arm
(`liftedAngle (edgeZ Q u v) (n−1) − liftedAngle (edgeZ Q u v) 0 < 2π`) of a
strictly convex *cyclic* planar chain in convex position. This is the genuine
analytic core not reduced to first-order data.

**Why it is the real residual (not a fake/vacuous one):**
- **TRUE and tight** — numerically the bound is approached but never reached by
  convex arms (max observed 6.2246 vs 2π=6.2832 over 2×10⁵ random convex arms).
  Not a false/unsatisfiable hypothesis (so the conditional is not vacuous).
- **The global cyclic support is essential** — the single-covector pairing
  against edge `0` alone is INSUFFICIENT: an explicit configuration with arm
  turning `> 2π` and all edge-`0` partial supports `≥ 0` exists (found in 2×10⁵
  trials). This matches `ZinanFFCT94`'s recorded obstruction precisely: a convex
  *sub*-run can span `[π,2π)`; only the global cyclic convexity forbids the open
  arm from completing a full turn. The clean proof is the closed-convex-polygon
  total-turning identity (sum of exterior angles `= 2π`, the open arm omits the
  two wrap turns, both in `(0,π)`), or equivalently the apex-`0` diagonal
  positivity (`det3_diag_pos_nat`, already in `PlanarConvexDiag`) bounding the
  apex-direction span `< π`. Reducible to `det3_diag_pos_nat` next round.

## Honest verdict

- `oriented_residue_of_turningBound`, `strictConvexSphArm_gnomonicSingleWind'`:
  **CONDITIONAL-honest** on `OpenConvexArmTurningLtTwoPi` (a true, non-vacuous,
  numerically-tight planar real-analysis statement; everything else proved).
- All supporting lemmas (frame shadow, oriented frame, lift, cos/sin, strict-turn
  sign, plane decomposition): **FAITHFUL / unconditional, clean-3.**
- Orientation finding: surfaced, not faked. The FFCT95 residue name
  `StrictPlanarChainLiftedTurnSpanExists` cannot be discharged as written; the
  oriented version is what is true and what the spherical application needs.

## Verify

```
scp .../ZinanFFCT96.lean uisai2:.../ProofsInTheBook/ &&
ssh uisai2 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH &&
  lake build ProofsInTheBook.ZinanFFCT96'
```
