# Ch36 Diagonal-Tube Straddle — `DiagTubeStraddle` DISCHARGED (report)

**File:** `ProofsInTheBook/ZinanCh36Straddle.lean` (927 lines, 0 errors, 0 warnings, clean-3).
**Status:** The ONE remaining named geometric residue of the Ch36 diagonal-tube chain —
`ZinanCh36DiagTube.DiagTubeStraddle` — is now PROVED unconditionally. No `sorry` / `admit` / `axiom`
/ `native_decide`.

`#print axioms` for all three public results = `[propext, Classical.choice, Quot.sound]` (clean-3,
no `sorryAx`):
* `diagTubeStraddle` — the discharged primitive itself;
* `exists_two_sided_diag_points_final` — unconditional sibling of the brick-5 output;
* `split_child_signs_eq_final` — unconditional sibling of the brick-7 master (sign synchronization).

## The geometry that closed it

The crucial computation: anchor a point `c` on the OPEN diagonal segment. The diagonal edge `d` of
each child has its two endpoints (the diagonal endpoints) STRADDLING the ray line through `c`
(`σ.r` is non-parallel to the diagonal, which is a child edge — `σ.no_edge_parallel`), so the SPAN of
the diagonal edge is TRUE and stable. Meanwhile `crossTau(c, d) = 0` IDENTICALLY along the whole
diagonal line (the ray from a diagonal point hits the diagonal line at parameter 0). So the flip of
the diagonal edge as the basepoint crosses the diagonal LINE is entirely in the FORWARD guard
`0 ≤ crossTau`, NOT in the span — exactly as the attack sketch's step 2 predicted, and the cleanest
possible realization.

Setting `zp = c + t•w`, `zm = c − t•w` with `w = sweepDir ρ.r λ` transverse to the diagonal edge,
`crossTau(zp,d)` and `crossTau(zm,d)` are `∓ t·(slope)` — OPPOSITE nonzero signs — so the diagonal
edge is crossed at exactly one of `zp`, `zm`. That is the singleton in the symmetric difference.

### Non-diagonal edges are stable — the key structural lemma

For a non-diagonal child edge `k`, the two endpoint side-coordinates are nonzero at `c`
(ray-genericity) and sign-stable across `zp`,`zm`, so the span agrees. If the span is FALSE the edge
is uncrossed at both. If TRUE, then `c` is OFF edge `k`: `c` is interior to the diagonal closing
edge, and two distinct child edges meet only at a shared vertex (`EdgeIntersectionCondition`) — `c`
is not a vertex (the diagonal meets the parent boundary only at its endpoints). Hence
`crossTau(c,k) ≠ 0` (via `crossTau_eq_zero_span_imp_onEdge`), so the forward guard is sign-stable
too. Either way the crossing status agrees at `zp`,`zm`. This is precisely the
`PolygonLocalJump` header §1 keystone, now LANDED — not assumed.

## Structure of the file (10 sections + payoff)

1. **§1 Affine algebra** — `side_step`, `crossTau_step` (affine-in-`s` along `c + s•w`), and
   `exists_lambda_transverse_family` (a STRENGTHENING of `Perturb.exists_lambda_transverse_edges`
   that drops the `det2 r v ≠ 0` hypothesis: `sweepDir r λ` is non-parallel to ANY fixed nonzero
   vector for cofinitely many `λ`, handling the `v ∥ r` case via `(r0²+r1²)(v0²+v1²) > 0`).
2. **§2** — right-child closing-edge helpers (`rightLastIndex`, `diag_eq_right_closing_edge`, mirrors
   of the committed `PolygonContainment` left-child versions, which did not exist for the right
   child).
3. **§3** — `openDiag_off_nondiag_child_edge`: an interior diagonal point lies on no non-diagonal
   child edge (the structural separation lemma above).
4. **§4–§7** — sign-preservation (`side_sign_stable`, `crossTau_sign_stable`, threshold dominance
   `abs_mul_lt_of_lt_threshold`), per-edge crossing-status equality (`edgeCrosses_eq_nondiag`), the
   diagonal flip (`edgeCrosses_flip_diag`), and the singleton-symmDiff assembly
   (`symmDiff_crossingEdges_eq_singleton`).
5. **§8** — diagonal-edge facts at the anchor (`diag_edge_data`: `crossTau = 0` + span true).
6. **§8.5/8.7/8.8** — selection toolkit: per-child amplitude threshold `δ_Q`
   (`exists_child_threshold`, via `Finset.min'` over per-vertex side and per-nondiagonal-edge
   crossTau thresholds, the latter filtered to nonzero anchor values), ray-generic anchor cofiniteness
   (`exists_anchor_bad`), and the nhds box capture (`exists_box_in_nhds`).
7. **§9** — `per_child_symmDiff`: the per-child singleton symmetric difference at a good anchor.
8. **§10** — `diagTubeStraddle`: the assembly. Picks `w` transverse to every edge of P/L/R, a
   ray-generic interior diagonal anchor `c` near `diagMid` (via Ioo-infinite avoidance), and a small
   `t` below the per-child thresholds and avoiding the off-boundary bad-`t` sets of P/L/R (at both
   `±t`, via `Perturb.exists_badt_polygon`). Lands both child symmDiffs and all off-boundary facts.
9. **§11** — payoff: `exists_two_sided_diag_points_final`, `split_child_signs_eq_final`.

## Notes / deviations from the sketch

* `DiagTubeStraddle` is RAY-AGNOSTIC (its committed definition imposes no `σL.r = ρ.r` /
  `σR.r = ρ.r`). The construction respects this: each child's symmDiff uses that child's OWN ray
  `σL`/`σR` for the crossing predicate; the shared perturbation direction `w` only needs to be
  transverse to the EDGES of all three polygons (an edge-orientation condition independent of the
  rays), which the strengthened `exists_lambda_transverse_family` guarantees.
* The off-boundary facts could be folded in cleanly because `exists_badt_polygon`'s off-boundary
  output is ray-independent; only its `hrw` requirement consults `ρ.r`, satisfied by
  `det2 ρ.r (sweepDir ρ.r λ) > 0`.
* I did NOT need to move the anchor off `diagMid` for the parent winding (the consumer
  `exists_two_sided_diag_points` extracts the parent equality from local constancy on the nhds `U`,
  and our `zp,zm ∈ U` for any `U`), so the committed `ZinanCh36DiagTube` wiring is untouched.

## Build / verify

```
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake build ProofsInTheBook.ZinanCh36DiagTube ProofsInTheBook.ZinanCh36Perturb'
scp ProofsInTheBook/ZinanCh36Straddle.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanCh36Straddle.lean'
```
→ 0 errors, 0 warnings; all three `#print axioms` = clean-3. `lake build ProofsInTheBook.ZinanCh36Straddle`
completes (8529 jobs).
