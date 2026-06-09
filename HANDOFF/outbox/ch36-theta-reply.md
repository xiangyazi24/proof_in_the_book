# Ch36-theta reply (worker, 2026-06-09)

## STATUS

**Banked, verified, no fake.** `ProofsInTheBook/ZinanCh36Theta.lean` (~1090 lines) compiles
on uisai2 with **0 errors, 0 warnings**; **27 theorems** audited, every one
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `ofReduceBool`/`trustCompiler`).
No file other than the new one was touched. Not committed (per spec).

Headline outcome, in one line: **Brick 1 fully banked; Brick 2 (unconditional alternation)
is NOT closable by the monotone squeeze — machine-refuted in-file — and is instead reduced
EXACTLY to a single sharpened residue, the ray winding dichotomy; Brick 3 wired to
`windCross_mem_of_alternation`.** Additionally the kernel `RayCrossingAlternation` as stated
is machine-refuted at non-generic base points (equal-`crossTau` double crossing through a
vertex), which every future consumer must know.

## What is proven (all clean-3; `#print axioms` at end of file)

### Brick 1 — the port (DONE, unconditional)
- §0–§1: full 2D angle layer on `Pt`: `ncos2/nsin2/theta2`, `lagrange2`, `cos_add_id2`,
  `sin_add_id2` (in 2D the whole FFCT9 cross-product layer collapses to coordinate `ring`),
  `mono_ncos2`, **`mono_theta2`** (driven by the imported `ZinanFFCT9.mono_abstract` crux),
  `branch_squeeze_theta2_ne_zero`, `det2_pos_of_theta2_mem`, `forward_strict_support2` —
  the verbatim 2D images of FFCT9 §0–§5.
- §2: **`thetaPos r x p := theta2 r (p − x)`** (the position-vector branch-cut angle);
  `det2_posVec_lineMap` (exact single-edge turning identity
  `det2(pos s, pos t) = (t−s)·orient x a b`); `mono_thetaPos_edge` (the specced single-edge
  monotone lemma); `thetaPos_eq_zero_at_forward` (angle = 0 exactly at forward ray points).

### Structure bricks (new, unconditional — the load-bearing supply for any future closer)
- §3 ray-translate laws: `side_translate`, `crossTau_translate`,
  `crossingEdges'_translate` (the crossing set at `x + c•ρ.r` is the `τ ≥ c` filter), and
  **`windCross_translate`** — the SUFFIX-SUM LAW: `windCross(x + c•ρ.r) = ∑_{τᵢ ≥ c} eSign i`.
- §4 simplicity ⟹ order: `crossU_mem_Ioo` (crossings are open-interior under the
  genericity guard), **`crossTau_injOn_crossingEdges`** (distinct crossings have distinct
  `crossTau` — this is where `EdgeIntersectionCondition` enters), `crossTau_ne_zero_of_offBoundary`,
  `not_onBoundary_at_cut` (cut points between crossings are off-boundary).
- §5 `exists_sorted_enum` (generic sorted enumeration along an injective real key) —
  discharges every clause of `RayCrossingAlternation` except `Alt`.
- §6 **`alt_of_cut_dichotomy`** (pure combinatorics): if all `τ ≥ c` filtered ±1-sums lie
  in `{0, s}` for one fixed `s = ±1`, the sorted enumeration alternates (two equal
  consecutive signs would put two suffix sums 2 apart).

### The headline reduction (Brick 2 in its honest form) + Brick 3 wiring
- §7 **`rayCrossingAlternation_of_ray_dichotomy`**: for off-boundary `x` with no vertex on
  its ray line, IF `windCross` takes at most the two values `{0, s}` at every off-boundary
  point of the forward ray, THEN `RayCrossingAlternation P ρ x`. And
  `windCross_mem_of_ray_dichotomy` = wiring through the proven
  `windCross_mem_of_alternation`. The reduction is *exact* (converse holds by the
  suffix-sum law; noted in-file as a remark, not formalized).
- §9 **`lineCrossing_eSign_sum_zero`** (unconditional): over the whole ray LINE the eSign
  sum telescopes to 0 (ups = downs, no Jordan content; cyclic reindex via
  `cyclicNext_injective`), and `windCross_eq_neg_backwardSum` (forward sum = − backward sum).
  This is the global budget any future alternation proof distributes.

### The two machine refutations (§8, on a genuine `StrictSimplePolygon` via `earTri`)
- **`rayCrossingAlternation_not_universal`**: triangle `(0,0),(2,1),(1,3)`, ray `r=(1,0)`,
  `x=(−1,0)` (off-boundary): the forward ray passes through vertex `(0,0)` with BOTH
  neighbours strictly above the line; the two incident edges are both forward crossings
  with EQUAL `crossTau = 1`, so NO strictly-sorted enumeration exists —
  `¬ RayCrossingAlternation P ρ x`. **The kernel as stated is false without a
  vertex-genericity guard.** Consumers must perturb `x` off the finitely many vertex rays
  (harmless: `windCross` is locally constant off the boundary) before invoking any kernel
  supply.
- **`posVec_turn_support_fails`**: same polygon/point: the consecutive position-vector turn
  `det2(B−x, A−x) = −3 < 0`. The blanket turn-support hypothesis that `mono_theta2`/the
  squeeze needs along the whole boundary is therefore unsatisfiable in general (at every
  exterior point winding 0 *forces* a negative turn; at reflex polygons even interior
  points fail — exactly the dead-ended `InteriorOddSeed ≡ allConvex` shape).

## The honest mathematical verdict on the briefed route

The brief's hope — "the alternation of eSign falls out of the monotone squeeze" — is
**unsalvageable as a blanket strategy**, and the file proves why, not just claims it:

1. The squeeze needs all consecutive position-vector turns weakly supported
   (`0 ≤ det2 (P t − x)(P t' − x)`), i.e. `x` sees the boundary in convex cyclic order.
   That is the already-refuted `allConvex`/`InteriorOddSeed` shape; `posVec_turn_support_fails`
   pins it concretely. The squeeze survives only per-edge / per-supported-subchain
   (`mono_thetaPos_edge`), which cannot order crossings of DIFFERENT edges.
2. What alternation actually IS (made exact by the suffix-sum law `windCross_translate`):
   the suffix sums of the crossing-sign sequence are precisely the `windCross` values along
   the ray, so alternation ⟺ `windCross ∈ {0, s}` along the ray ⟺ "every ray point is
   inside-with-one-consistent-sign or outside". That is the planar-Jordan
   interior/exterior dichotomy itself, restricted to one ray. **No local/monotone argument
   can produce it; it is exactly the chapter's irreducible kernel, now in its minimal form.**

## The sharpened residue (recommended next target)

`RayWindingDichotomy P ρ x s` :=
`∀ c ≥ 0, ¬OnBoundary P (x + c•ρ.r) → windCross P ρ (x + c•ρ.r) ∈ {0, s}` —
one fixed `s = ±1` per `(P, ρ, x)`. By §7 it closes `RayCrossingAlternation` at generic
`x`; it is strictly weaker-looking than full Jordan (one ray only, values only), and it is
the exact two-value strengthening of the proven three-value bound. Note the dead-end list's
"any route needing a known winding value" does NOT apply verbatim: the dichotomy needs the
two-value *range*, not a known value at a known point. Possible attack: induct along the
ray outward (far end gives `0` unconditionally — `rayCrossingAlternation_far` /
`exists_far_point_windCross_zero`), using §9's forward/backward balance plus the
local ±1 jump structure; the remaining content is sign-consistency of the nonzero values,
which is where the genuine Jordan work (excursion non-crossing) lives.

## Exact blockers (nothing hidden)

- The unconditional `RayCrossingAlternation` (equivalently the dichotomy above) — genuine
  planar-Jordan content, NOT closable by mono_theta/squeeze (machine-refuted route), NOT
  closable by any finite-algebraic identity in this file's toolbox. No missing-Mathlib-API
  blocker was hit; everything attempted was either proven or refuted.
- Consumer-side caveat discovered: any equivalence "`earDeletedExterior ≡
  RayCrossingAlternation`" quantified over ALL off-boundary `x` is FALSE as stated
  (`rayCrossingAlternation_not_universal`); the kernel form needs the genericity guard
  `∀ k, side ρ.r x (P.q k) ≠ 0` (or a perturbation wrapper). Worth checking how the
  residue map's item-3 equivalence is phrased before building on it.

## Verify (reproduced)

```
ssh uisai2 'cd ~/repos/proof_in_the_book && lake env lean ProofsInTheBook/ZinanCh36Theta.lean'
# → 0 errors, 0 warnings; 27 × "depends on axioms: [propext, Classical.choice, Quot.sound]"
```

27 audited names: lagrange2, cos_add_id2, sin_add_id2, mono_ncos2, mono_theta2,
branch_squeeze_theta2_ne_zero, det2_pos_of_theta2_mem, forward_strict_support2,
det2_posVec_lineMap, mono_thetaPos_edge, thetaPos_eq_zero_at_forward, side_translate,
crossTau_translate, crossingEdges'_translate, windCross_translate, crossU_mem_Ioo,
crossTau_injOn_crossingEdges, crossTau_ne_zero_of_offBoundary, not_onBoundary_at_cut,
exists_sorted_enum, alt_of_cut_dichotomy, rayCrossingAlternation_of_ray_dichotomy,
windCross_mem_of_ray_dichotomy, rayCrossingAlternation_not_universal,
posVec_turn_support_fails, lineCrossing_eSign_sum_zero, windCross_eq_neg_backwardSum.
