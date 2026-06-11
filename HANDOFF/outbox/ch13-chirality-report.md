# Ch13 Chirality Elimination — Report (ZinanFFCT56)

**File:** `ProofsInTheBook/ZinanFFCT56.lean` (NEW, single-writer). Imports only committed
upstream (`ZinanFFCT21`, `ZinanFFCT55`). Verified on uisai2: 0 errors, 0 warnings, clean-3
(`[propext, Classical.choice, Quot.sound]` for all 10 results — no `sorryAx`). No
`sorry`/`admit`/`axiom`/`native_decide`.

## What was eliminated

The design's resolution is **eliminate, not transport**. FFCT55 pinned that the WBS widening
family's `-θ` derivative reads the span coefficient `b ≤ 0` (opposite of legacy `WBSBetaSign`).
This module shows that the `b < 0` configuration (the **mid-fold**) is geometrically impossible at an
interior apex, so the WBS axis-edge support-stuck branch dies outright.

### Bricks landed (clean-3)

1. **`bcoef_ne_zero_of_short_edge`** (§A, C2). `b = 0 ⟹ p = ±mid`, both killed by `ShortArc p mid`.
2. **`midFold_coeffs_of_bneg`** (§A, C1). Strict open hemisphere + `b < 0 ⟹ a > 0` (inner product
   against `h`); rearranges `P i = a•P(i+1) + b•P j` to `P(i+1) = (1/a)•P i + ((-b)/a)•P j` with
   **both coefficients > 0** — the mid-fold with between-vertex `P(i+1)`.
3. **`midFold_interior_contradiction`** (§B, master, the §5 mechanism). With `M = P(i+1) = c•P0 + d•Q`
   (`c,d>0`), the **successor** edge `(M,R)=(P(i+1),P(i+2))` weak supports at `P0=P i` and `Q=P j`
   give `0 ≤ det3 M R P0 = d·det3 Q R P0` and `0 ≤ det3 M R Q = -c·det3 Q R P0`, opposite multiples
   ⟹ `det3 Q R P0 = 0` ⟹ `det3 P0 M R = d·det3 P0 Q R = 0` ⟹ flat adjacent joint at apex `P(i+1)`
   (joint index `i`) ⟹ killed by `PositiveJoints` + `jointAngle_lt_pi`. This is the exact **mirror**
   of FFCT21's `far_fold_no_predecessor` (predecessor-edge kill), with the apex and killing edge
   shifted by one.
4. **`midFold_bneg_false`** (§B′). Packages 2+3 with the weak-polygon `edge_support`/`edge_short`
   (universal, no `NonIncident` needed) into a single `b < 0 ⟹ False` on a weakly convex
   `PositiveJoints` arm.
5. **`wbs_axisEdge_supportStuck_false`** (§C, brick 5). At the WBS opened arm `openedWBS A B k`, the
   axis-edge pattern `i+1 = (openingAxis k).val` makes the apex interior (`openingAxis_interior`:
   `1 ≤ K.val < n` ⟹ `i+2 = K.val+1 ≤ n < n+1`), so §B′ fires. **The axis-edge WBS support-stuck
   branch is eliminated.**

### Dispatch + consequence (clean-3)

6. **`wbs_supportStuck_dispatch_chiral`** (§D, brick 6). At a WBS support-stuck `b < 0` binding:
   either axis-edge (`i+1 = K`, ⟹ `False` by §C) or the named `NonAxisMixedBindingResidue`. The
   all-fixed/all-rotated cases are already killed upstream by FFCT55 §R1/R2
   (`wbsConstantBinding_false_allFixed/allRotated`), so the genuine binding is mixed; this dispatch
   handles the mixed case's axis-position taxonomy (axis-in-edge vs not).
7. **`wbs_supportStuck_nonAxis_only`** (§E, brick 8). Since the axis-edge case is impossible, any WBS
   support-stuck `b < 0` binding reduces to a non-axis mixed binding.

## The honest survivor (brick 7)

**`NonAxisMixedBindingResidue A B k i j …`** (named, non-vacuous). The general non-axis mixed
binding — where the rotated vertex is **not** in the edge's slot-2 axis position — does not
slot-normalize to FFCT55's single-rotation `wbsAxisEdgeSupport`; its derivative reads an un-pivoted
`det3_cross_expansion` quantity, not the Gram `hβ` form, so the FFCT55 axis-edge `b ≤ 0` derivative
output does not apply. The residue is the precise per-pattern goal: a `b < 0` mid-fold datum at a
non-axis (`i+1 ≠ K`) binding on the opened arm.

**Honest status of brick 7:** the mid-fold *kill* (§B/§B′) is pattern-agnostic — it fires on ANY
`b < 0` span datum at an interior apex with the successor-edge supports. What remains genuinely open
is the **sign supply** for the non-axis patterns: the derivative there reads the un-pivoted
cross-expansion quantity whose sign is not yet shown `b ≤ 0`. So the surface is not "the local kill
fails" but "the non-axis derivative does not yet hand us a `b < 0`". Once any non-axis pattern's
derivative is shown to force `b < 0` (or `b > 0` with a symmetric mirror-fold kill), feeding it
straight into `midFold_bneg_false` closes it with zero new geometry. This is the exact reduction
brick 7 asked for; the residue is named with its precise satisfiable goal and three non-vacuity
guards (`midFold_coeffs_nonvacuous`, `midFold_support_collapse_identity`,
`nonAxisMixedBindingResidue_unfold`).

## Cut-chain implications (FFCT48–54)

- The legacy `StuckAtKData`/`WBSBetaSign` route assumed a single chirality. FFCT55 showed the WBS
  chirality is flipped; this module shows the flipped (mid-fold) chirality is **locally impossible**
  at the axis-edge, so it never needs a `MidFoldCutTransport`. The correct replacement is
  `MidFoldInteriorImpossible` (= `wbs_axisEdge_supportStuck_false`), not a transport.
- **For the CutReady line (FFCT48/49/53/54):** the CUT branch at a WBS support-stuck sup now fires
  **only at non-axis mixed bindings** (`wbs_supportStuck_nonAxis_only`). The axis-edge sub-case that
  the cut-normalization machinery (FFCT52/53) would have had to transport is gone — it contradicts
  weak convexity directly. The consumers' docstrings should record: "WBS support-stuck ⟹ non-axis
  mixed binding (axis-edge eliminated, FFCT56); the residual chirality is
  `NonAxisMixedBindingResidue`, the named per-pattern sign-normalization survivor."
- No FFCT48–55 statement is weakened or changed (single-writer; FFCT56 only *adds*). The boundary
  case `i+1 = n` (`MidFoldLastBoundaryCase`) is **not reached** at axis-edge bindings (the apex is
  interior by `openingAxis_interior`), so it is not needed here.

## Verification

```
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT56.lean'
```
→ 0 errors, 0 warnings, all 10 `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
(FFCT55 + FFCT21 oleans built first; both clean-3.)
