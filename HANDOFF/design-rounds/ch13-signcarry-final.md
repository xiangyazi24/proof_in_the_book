## 1. Precise diagnosis

The missing datum is **not** another determinant-zero step. That part is landed.

The missing datum is the **sign-carrying re-extraction**:

```lean
det3 U V (A (k+1)) = 0
```

only says `A (k+1)` lies in the real plane/span of the anchors `U,V`. To continue the sweep, the next state needs explicit coefficients with the correct cone sign, e.g.

```lean
(A (k+1) : E3) =
  c' • (U : E3) + d' • (V : E3)
```

with the coefficient needed by the next determinant step strictly positive. The probe-`1` case avoids this entirely: it normalizes immediately to the ordinary support zero on edge `(0,1)` with probe `n`, so no propagation/re-extraction is needed. This is exactly what `wrapPlanePropagation_probe_one` does in `ZinanFFCT78`. fileciteturn117file0

FFCT22’s `OnFoldRay` is the right **shape** of the invariant, but it does not already solve this. FFCT22 defines:

```lean
structure OnFoldRay (v w z : S2) : Prop where
  col : det3 (v : E3) (w : E3) (z : E3) = 0
  coeff : (z : E3) ∈ Submodule.span NNReal ({(v : E3), (w : E3)} : Set E3)
```

and proves `far_fold_tail_collinear_step`, the determinant-vanishing half. The file’s own honesty note says the full propagation must re-extract cone membership of the next vertex and that the determinant identities alone give no coefficient sign information inside the plane. fileciteturn120file0

So the fix is:

> Reuse/copy the `OnFoldRay` invariant, but add the missing **sector re-extraction theorem**. The induction state must carry the cone coefficients, and every time a new vertex enters the plane, a b-trichotomy on its real coefficients must either restore the cone state or exit through a landed kill/endpoint branch.

---

## 2. Why the apex side closed but the wrap side did not

`apexNBoundaryZeroPropagation` is not a propagation theorem. Its hypothesis is already an ordinary nonincident support zero:

```lean
sOrient (A i) (A (i+1)) (A n) = 0
```

with `i + 1 < n`, so it directly returns:

```lean
NormalizedInteriorSupportZero A
```

by choosing `(i,n)`. No coefficient signs are needed. fileciteturn117file0

The wrap case is different:

```lean
sOrient (A n) (A 0) (A j) = 0
```

Here the zero is on the **wrap edge** `(n,0)`, and the ordinary normalized edge `(0,1)` only appears after pushing the plane one step into the arm. Probe `1` is the one special case where that push is unnecessary; arbitrary probe `j` requires repeated sign-carrying propagation. The v10 report states this precisely: FFCT76/78 close probe `1` and the already-normalized apex case, but not the arbitrary interior wrap probe. fileciteturn119file0

---

## 3. Mirror/reversal will not avoid wrap propagation

The mirror/reversal suites are useful for routing opposite endpoint orientations, but they do not turn the wrap edge into an ordinary edge. Reversal sends the wrap edge to the wrap edge with reversed orientation. Cyclic determinant rotation can rewrite

```lean
det3 (A n) (A 0) (A j)
```

as

```lean
det3 (A j) (A n) (A 0)
```

but `(j,n)` is not generally an edge. So it does not match the apex theorem’s ordinary-edge shape:

```lean
det3 (A i) (A (i+1)) (A n) = 0.
```

Thus the route is not “mirror to apex”; it is “propagate the wrap plane until it becomes ordinary, or exit through a kill.”

---

## 4. Correct invariant

Define a wrap-specific cone state. Do not make the first implementation fully anchor-generic; concrete anchors make the incident-edge bookkeeping much lighter.

```lean
structure WrapPlaneState
    {n : ℕ} (A : Fin (n + 1) → S2) (j : Fin (n + 1))
    (k : ℕ) : Prop where
  hk : k < n + 1
  c d : ℝ
  rep :
    (A ⟨k, hk⟩ : E3) =
      c • (A (Fin.last n) : E3) + d • (A j : E3)
  hc_pos : 0 < c
  hd_pos : 0 < d
```

This is the sign-carrying version of `OnFoldRay`: it contains the plane membership and the cone sign needed for the next step.

A generic version can later be factored as:

```lean
structure OnFoldRayWithCoeffs (U V z : S2) : Prop where
  c d : ℝ
  rep : (z : E3) = c • (U : E3) + d • (V : E3)
  hc_pos : 0 < c
  hd_pos : 0 < d
```

but start with the wrap-specific one.

---

## 5. Landed algebra to reuse

`boundaryPlane_step_sameSign` is already the correct same-sign determinant step:

```lean
theorem boundaryPlane_step_sameSign
    ...
    (hrep :
      (A ⟨k, by omega⟩ : E3) =
        c • (U : E3) + d • (V : E3))
    (_hc : c ≠ 0) (_hd : d ≠ 0)
    (hsame : 0 < c * d)
    ...
    :
    sOrient U V (A ⟨k + 1, by omega⟩) = 0
```

It proves the determinant-zero propagation for one edge under same-sign coefficients. fileciteturn115file0

For the wrap state, instantiate:

```lean
U := A (Fin.last n)
V := A j
```

and use weak supports:

```lean
0 ≤ sOrient (A k) (A (k+1)) (A (Fin.last n))
0 ≤ sOrient (A k) (A (k+1)) (A j)
```

when the anchors are nonincident to the current edge.

---

## 6. The real missing brick: sector re-extraction

After the same-sign step:

```lean
hzeroNext :
  sOrient (A (Fin.last n)) (A j) (A ⟨k+1⟩) = 0
```

use FFCT25’s real-span extraction to get real coefficients:

```lean
(A ⟨k+1⟩ : E3) =
  c' • (A (Fin.last n) : E3) + d' • (A j : E3)
```

Then run a trichotomy on `c'` and `d'`.

Signature:

```lean
theorem wrap_next_state_or_progress
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (hA : WeakConvexSphArm A)
    (hpos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hside : SameSides A B)
    (hangle : JointLe A B)
    (hnr : NoNonadjacentRepeat A)
    (hhem :
      ∃ h : E3, ‖h‖ = 1 ∧
        ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    {j : Fin (n + 1)} {k : ℕ}
    (hj_ne_last : j ≠ Fin.last n)
    (hj_ne_zero : j ≠ 0)
    (S : WrapPlaneState A j k)
    (hk1 : k + 1 < n + 1)
    (hnoninc_last : (Fin.last n) ≠ ⟨k, by omega⟩ ∧
                    (Fin.last n) ≠ ⟨k + 1, by omega⟩)
    (hnoninc_j : j ≠ ⟨k, by omega⟩ ∧
                 j ≠ ⟨k + 1, by omega⟩) :
    BoundaryZeroProgress A B ∨
      WrapPlaneState A j (k + 1)
```

Proof cases after coefficient extraction:

```text
c' > 0, d' > 0  → return next WrapPlaneState.
c' = 0 or d' = 0 → repeat/antipodal/short/open-hemisphere kill.
c' < 0 and d' < 0 → impossible by strict hemisphere positivity.
c' and d' opposite signs → route to endpoint/collapse branch, not back to the tail residue.
```

The last line is the key anti-circularity requirement from the reports: opposite-sign branches must go to endpoint progress or a landed contradiction, not into `BPosANegTailCornerResidueV9`. The v10 report explicitly says feeding the apex normalized zero into the generic endpoint consumer re-enters the same tail corner; this brick must avoid that route. fileciteturn118file0

Estimate: **250–450 lines, master**.

---

## 7. Opposite-sign routing without circularity

Do not call:

```lean
endpoint_of_boundaryZeroProgress_at_level_nr
```

inside the proof of `BPosANegTailCornerResidueV9`; that is the circular path described in the reports. Instead, route opposite-sign states directly through already landed non-recursive kills:

1. **If the far anchor has a real successor:** use `bpos_aneg_false_of_successor` from FFCT70. It closes the `b > 0, a < 0` branch when the far vertex is not the last vertex. fileciteturn113file0

2. **If the local pattern is a mid-fold:** use FFCT56’s pattern-agnostic midFold kill. The design requirement is to normalize the coefficient equation so the apex’s successor edge is an ordinary arm edge.

3. **If the sign pattern is reversed:** use FFCT61/FFCT52 mirror/reversal transports, then apply the same successor or midFold kill on the transformed arm.

4. **If the far anchor is exactly the last vertex and no successor exists:** this is the signed tail corner. It must be consumed by the same wrap propagation theorem, but from the **wrap edge side**, not by calling the v9 tail residue. This is where `apexNBoundaryZeroPropagation` is insufficient by itself; the proof must continue with wrap propagation.

Add a concrete lemma:

```lean
theorem wrap_oppositeSign_progress_nonrecursive
    {n : ℕ} {A B : Fin (n + 1) → S2}
    ...
    {j : Fin (n + 1)} {k : ℕ}
    (hrep :
      (A ⟨k, by omega⟩ : E3) =
        c • (A (Fin.last n) : E3) + d • (A j : E3))
    (hopp : c * d < 0)
    (hnoninc : ... ) :
    BoundaryZeroProgress A B
```

This lemma is mostly routing, not determinant algebra. It should import/reuse FFCT56, FFCT61, FFCT70, FFCT75.

Estimate: **180–320 lines, master**.

---

## 8. Zero-coefficient routing

A zero coefficient in

```lean
A (k+1) = c' • A n + d' • A j
```

means the vertex is a scalar multiple of one anchor. Since all are unit sphere points and an open hemisphere is present, scalar-multiple collapses to equality, not antipodal. Equality is then killed by one of:

```lean
NoNonadjacentRepeat A
ShortArc edge_short
```

depending on whether the indices are nonadjacent or adjacent.

Write concrete lemmas rather than a too-generic one:

```lean
theorem wrap_coeff_zero_last_absurd
    {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A)
    (hnr : NoNonadjacentRepeat A)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    {j : Fin (n + 1)} {k : ℕ}
    (hindex : ... nonadjacent index data ...)
    {d : ℝ}
    (hrep : (A ⟨k, by omega⟩ : E3) = d • (A j : E3)) :
    False
```

and the mirror version with `A (Fin.last n)`.

Estimate: **120–200 lines, worker/master**.

---

## 9. Decreasing induction

The induction should decrease the distance from the current swept vertex to the probe `j` along the ordinary arm direction.

For wrap binding:

```lean
sOrient (A n) (A 0) (A j) = 0
```

the initial propagation state is at `k = 0` after the b-trichotomy produces:

```lean
A 0 = c • A n + d • A j
```

with `c,d > 0`.

Then each successful step advances:

```lean
k ↦ k + 1.
```

Stop conditions:

- `j.val = 1`: already handled by `wrapPlanePropagation_probe_one`.
- current edge `(k,k+1)` with probe `j` is ordinary nonincident: return `NormalizedInteriorSupportZero`.
- current propagation creates three consecutive interior vertices in the plane: use `flat_interior_joint_absurd_public`.
- `k+1 = j`: route through the adjacent/probe-hit case; either one more step gives a flat joint, or normalized zero is available from a neighboring ordinary edge.

Concrete theorem:

```lean
theorem wrapPlanePropagation_from_state
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (hA : WeakConvexSphArm A)
    (hpos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hside : SameSides A B)
    (hangle : JointLe A B)
    (hnr : NoNonadjacentRepeat A)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    {j : Fin (n + 1)}
    (hj_ne_last : j ≠ Fin.last n)
    (hj_ne_zero : j ≠ 0)
    {k : ℕ}
    (S : WrapPlaneState A j k)
    (hkj : k < j.val) :
    BoundaryZeroProgress A B
```

Proof by strong induction on `j.val - k`.

Estimate: **250–450 lines, master**.

---

## 10. Full wrap theorem

First turn the wrap zero into an initial coefficient state by extracting coefficients in the plane `(A n, A j)`.

```lean
theorem wrapPlanePropagation
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (hA : WeakConvexSphArm A)
    (hpos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hside : SameSides A B)
    (hangle : JointLe A B)
    (hnr : NoNonadjacentRepeat A)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    {j : Fin (n + 1)}
    (hj_ne_last : j ≠ Fin.last n)
    (hj_ne_zero : j ≠ 0)
    (hzero : sOrient (A (Fin.last n)) (A 0) (A j) = 0) :
    BoundaryZeroProgress A B
```

Implementation outline:

1. If `j.val = 1`, use `wrapPlanePropagation_probe_one`.
2. Otherwise use real-span extraction from `hzero`:
   ```lean
   A 0 = c • A n + d • A j
   ```
3. Trichotomize `c,d`.
4. Positive-positive gives `WrapPlaneState A j 0`; call `wrapPlanePropagation_from_state`.
5. Zero/negative/opposite branches route as above.

Estimate: **160–260 lines, master assembly** after the state induction.

---

## 11. Why `OnFoldRay` is still worth reusing

Use FFCT22’s definitions where they help:

```lean
OnFoldRay.coeffs
far_fold_tail_collinear_step
real_comb_of_mem_span_pair
coplanar_triple_det3_zero_of_onFoldRay
far_fold_tail_not_interior
```

But do not expect `far_fold_tail_collinear_step` to produce the next `OnFoldRay`. It only proves the determinant-zero half. FFCT22’s header explicitly states the cone re-extraction was scoped out. fileciteturn120file0

Best implementation pattern:

```lean
-- Use `WrapPlaneState` for the actual induction.
-- Provide bridge:
theorem WrapPlaneState.to_OnFoldRay :
  WrapPlaneState A j k →
    OnFoldRay (A (Fin.last n)) (A j) (A ⟨k, ...⟩)
```

This lets you reuse coplanarity/flat-joint bridges while retaining explicit coefficient signs in `WrapPlaneState`.

Estimate: **20–40 lines, worker**.

---

## 12. Wrappers to finish v10

Once `wrapPlanePropagation` is landed:

```lean
theorem weakWrapSeed_v9_of_wrapPropagation :
    WeakVanishingWrapSeedResidueV9
```

Use FFCT75’s wrap index facts:

```lean
weak_wrap_base_is_last
weak_wrap_successor_is_zero
weak_wrap_probe_interior
```

to rewrite a raw wrap support into:

```lean
sOrient (P (Fin.last n)) (P 0) (P b) = 0
```

then call `wrapPlanePropagation`. fileciteturn110file0

```lean
theorem supportStuckWBSWrapSeed_v9_of_wrapPropagation :
    SupportStuckWBSWrapSeedResidueV9
```

Same proof, but for the opened WBS arm.

```lean
theorem bpos_aneg_tail_v9_of_wrapPropagation :
    BPosANegTailCornerResidueV9
```

Use:

```lean
bpos_aneg_tail_span_forces_zero
```

then route the produced apex/wrap zero through the non-circular propagation theorem, **not** through `endpoint_of_boundaryZeroProgress_at_level_nr` in a way that re-enters the same residue. FFCT75 has the zero-support consequence. fileciteturn110file0

Finally:

```lean
theorem spherical_arm_mono_final_ch13_v10
    (hcross : CrossPieceNoCollisionAtSup) :
    SphericalArmMonotone
```

Use `spherical_arm_mono_final_ch13_v10_of_hcross_and_boundaryResidues` from the final report with the three wrappers. The final report states the current wrapper needs `hcross` plus exactly the three boundary residues. fileciteturn118file0

---

## 13. CrossPieceNoCollisionAtSup remains

Keep `CrossPieceNoCollisionAtSup` as the sole accepted final input. The boundary propagation theorem consumes determinant zeros involving the wrap edge or apex `n`. A cross-piece collision at the supremum is a different geometric phenomenon: it can occur without creating the support-zero pattern needed by `wrapPlanePropagation`.

The reports’ target is therefore exactly:

```lean
theorem spherical_arm_mono_final_ch13_v10
    (hcross : CrossPieceNoCollisionAtSup) :
    SphericalArmMonotone
```

not an unconditional theorem. fileciteturn118file0

---

## 14. Ordered brick list

| # | Brick | Purpose | Difficulty | Estimate |
|---:|---|---|---:|---:|
| 1 | `WrapPlaneState` | sign-carrying invariant | worker | 20–40 |
| 2 | `WrapPlaneState.to_OnFoldRay` | reuse FFCT22 coplanar machinery | worker | 20–40 |
| 3 | concrete real-span extraction for wrap anchors | get `c,d` from `det3 = 0` | worker | 50–90 |
| 4 | zero-coeff absurd lemmas | kill `c=0`/`d=0` | worker/master | 120–200 |
| 5 | negative-negative hemisphere absurd | kill both coefficients negative | worker | 30–60 |
| 6 | `wrap_oppositeSign_progress_nonrecursive` | route opposite signs to FFCT56/70/61 or direct endpoint progress | master | 180–320 |
| 7 | `wrap_next_state_or_progress` | one-step propagation with b-trichotomy | master | 250–450 |
| 8 | `wrapPlanePropagation_from_state` | decreasing induction on `j.val - k` | master | 250–450 |
| 9 | `wrapPlanePropagation` | full arbitrary-probe theorem | master | 160–260 |
| 10 | `weakWrapSeed_v9_of_wrapPropagation` | first residue wrapper | worker/master | 80–140 |
| 11 | `supportStuckWBSWrapSeed_v9_of_wrapPropagation` | WBS wrapper | master | 120–220 |
| 12 | `bpos_aneg_tail_v9_of_wrapPropagation` | signed tail wrapper, non-circular | master | 120–220 |
| 13 | `V10BoundaryResidues_of_wrapPropagation` | package three fields | worker | 30–60 |
| 14 | `spherical_arm_mono_final_ch13_v10` | hcross-only headline | worker | 20–40 |

---

## 15. Degenerate audit

`j.val = 1`: already closed by `wrapPlanePropagation_probe_one`; do not enter induction.

`j = 0` or `j = n`: excluded by nonincident wrap seed; FFCT75 gives the interior-probe lemma for raw wrap seeds. fileciteturn110file0

`n = 2` and `n = 3`: there is no long propagation. Dispatch to probe-one/adjacent/flat-joint/base cases. In Lean, put these before constructing `WrapPlaneState`.

Propagation reaches `k + 1 = j`: stop; either the current ordinary zero is already normalized, or the next neighboring step gives a flat joint. Do not attempt to divide by a coefficient of the anchor vertex itself.

Both anchors adjacent to the current edge: this is not a normalized cut seed. Route to `flat_interior_joint_absurd_public` or FFCT56 midFold.

Opposite-sign branch: must not call the v9 tail residue. This was the circularity recorded in the v10/final reports. It must be closed by landed local kills or by the same `wrapPlanePropagation` on a strictly smaller boundary-distance measure.
