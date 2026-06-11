## 1. Verdict

Design the final wave around one theorem:

```lean
wrapPlanePropagation
```

but formulate it as **boundary-zero progress**, not as a bare “all coefficients propagate” lemma. The coefficient propagation step is only valid in the same-sign cone branch. The zero-coefficient and opposite-sign branches must be routed to the already-landed corner kills, mirror/reversal transports, successor collapse, or endpoint payload.

This theorem should discharge:

```lean
WeakVanishingWrapSeedResidue
SupportStuckWBSWrapSeedResidue
BPosANegTailCornerResidue
```

and should **not** try to discharge:

```lean
CrossPieceNoCollisionAtSup
```

FFCT75 explicitly records that the requested `{hcross}`-only surface was not introduced because the wrap-base and signed tail corners still needed cyclic boundary propagation; after this wave, `hcross` is exactly the one final surface field to keep. fileciteturn110file0

---

## 2. Output API

Add a new file:

```lean
ProofsInTheBook/ZinanFFCT76.lean
```

Imports:

```lean
import ProofsInTheBook.ZinanFFCT75
import ProofsInTheBook.ZinanFFCT44
```

Use two shared output predicates.

```lean
/-- A normalized ordinary nonincident support zero, suitable for the landed cut/seed machinery. -/
def NormalizedInteriorSupportZero {n : ℕ} (A : Fin (n + 1) → S2) : Prop :=
  ∃ i j : ℕ,
    i + 1 < j ∧
    i + 1 < n + 1 ∧
    j < n + 1 ∧
    sOrient (A ⟨i, by omega⟩)
      (A ⟨i + 1, by omega⟩)
      (A ⟨j, by omega⟩) = 0

/-- The progress payload produced by a boundary zero. -/
def BoundaryZeroProgress {n : ℕ} (A B : Fin (n + 1) → S2) : Prop :=
  NormalizedInteriorSupportZero A ∨ endpt A ≤ endpt B
```

The flat-joint branches prove `False`, so they can close either side of `BoundaryZeroProgress`.

---

## 3. Wrap propagation theorem

This is the central theorem.

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
    (hhem :
      ∃ h : E3, ‖h‖ = 1 ∧
        ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    {j : Fin (n + 1)}
    (hj_ne_last : j ≠ Fin.last n)
    (hj_ne_zero : j ≠ 0)
    (hzero : sOrient (A (Fin.last n)) (A 0) (A j) = 0) :
    BoundaryZeroProgress A B
```

This theorem takes a wrap-edge support zero:

```lean
det3 (A n) (A 0) (A j) = 0
```

and pushes it into one of the three useful outcomes:

1. a normalized ordinary vanishing support,
2. an interior flat joint contradiction,
3. a direct endpoint conclusion.

FFCT75 already supplies the index-normalization facts for raw wrap seeds: a wrap base is `n`, its successor is `0`, and the probed vertex is strictly between `0` and `n`. fileciteturn110file0

---

## 4. Apex-`n` variant

The tail-corner residue is not literally wrap-edge shaped; it produces an apex-`n` support zero. Add the variant:

```lean
theorem apexNBoundaryZeroPropagation
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
    {i : ℕ}
    (hi : i < n + 1)
    (hi1 : i + 1 < n + 1)
    (hfar : i + 1 < n)
    (hzero :
      sOrient (A ⟨i, hi⟩)
        (A ⟨i + 1, hi1⟩)
        (A ⟨n, by omega⟩) = 0) :
    BoundaryZeroProgress A B
```

Proof idea: if this is already an ordinary normalized zero usable by the landed machinery, return the left disjunct. In the signed tail-corner branch, use the wrap edge `(n,0)` supports at `i` and `i+1` to force a wrap zero:

```lean
sOrient (A n) (A 0) (A (i+1)) = 0
```

then call `wrapPlanePropagation`.

FFCT75’s `bpos_aneg_tail_span_forces_zero` gives the easy support-zero consequence for the signed tail corner. fileciteturn110file0

---

## 5. Which b-trichotomy legs are killable

Use the normalization

```lean
A 0 = c • A n + d • A j
```

for the wrap binding. This is better than normalizing `A n = a • A 0 + b • A j`, because edge `(0,1)` is ordinary and lets propagation enter the arm.

The legs:

**`c = 0` or `d = 0`: kill.**  
A unit vector becomes a nonnegative/real scalar multiple of a vertex. With the open hemisphere and short-arc/no-repeat hypotheses, this collapses to equality or antipodality. Equality is killed by `NoNonadjacentRepeat` or the wrap edge’s `ShortArc`; antipodality is killed by the open hemisphere.

**`c < 0` and `d < 0`: impossible.**  
Take the strict hemisphere normal `h`; all inner products with vertices are positive, so the right side has negative inner product but `⟪h,A0⟫ > 0`.

**`c * d > 0`: propagation leg.**  
Since both cannot be negative, this is the positive-positive cone leg. Supports of edge `(0,1)` at `n` and `j` force:

```lean
sOrient (A n) (A j) (A 1) = 0
```

so `A 1` lies in the same plane. Then re-extract real coefficients for `A 1` in the plane and repeat/trichotomize.

**`c * d < 0`: route to landed corner machinery.**  
This is not a propagation leg. It is the signed endpoint/mid-fold pattern. Use FFCT56’s pattern-agnostic midFold kill when the apex has an interior successor configuration, FFCT70’s successor collapse when the far vertex has a real successor, and the apex-`n` propagation for the last tail corner. FFCT70 explicitly closes the successor-edge part of the `b > 0, a < 0` endpoint case and leaves only the final tail corner. fileciteturn113file0

---

## 6. Local same-sign step

This is the worker-grade algebraic brick.

```lean
theorem boundaryPlane_step_sameSign
    {n : ℕ} {A : Fin (n + 1) → S2}
    {U V : S2} {k : ℕ}
    (hk : k + 1 < n + 1)
    {c d : ℝ}
    (hrep :
      (A ⟨k, by omega⟩ : E3) =
        c • (U : E3) + d • (V : E3))
    (hc : c ≠ 0) (hd : d ≠ 0)
    (hsame : 0 < c * d)
    (hU :
      0 ≤ sOrient (A ⟨k, by omega⟩)
        (A ⟨k + 1, by omega⟩) U)
    (hV :
      0 ≤ sOrient (A ⟨k, by omega⟩)
        (A ⟨k + 1, by omega⟩) V) :
    sOrient U V (A ⟨k + 1, by omega⟩) = 0
```

Proof:

```lean
sOrient (cU+dV) W U = d * sOrient V W U
sOrient (cU+dV) W V = c * sOrient U W V
sOrient V W U =  sOrient U V W
sOrient U W V = -sOrient U V W
```

So the weak supports become:

```lean
0 ≤ d * D
0 ≤ -c * D
```

where `D = sOrient U V W`. If `c*d > 0`, then `D = 0`.

Estimate: **70–120 lines**, worker.

---

## 7. Plane state invariant

Use a concrete propagation state rather than a loose “in plane” hypothesis.

```lean
structure PlaneState {n : ℕ}
    (A : Fin (n + 1) → S2) (U V : S2) (k : ℕ) : Prop where
  hk : k < n + 1
  c : ℝ
  d : ℝ
  rep :
    (A ⟨k, hk⟩ : E3) =
      c • (U : E3) + d • (V : E3)
  sameSign : 0 < c * d
```

A `PlaneState` means `A k` is in the anchor plane and is in the same-sign branch, so the next step can use `boundaryPlane_step_sameSign`.

---

## 8. Re-extraction after a zero

Once same-sign propagation gives:

```lean
sOrient U V (A (k+1)) = 0
```

extract coefficients:

```lean
theorem planeState_of_det_zero
    {n : ℕ} {A : Fin (n + 1) → S2} {U V : S2}
    (hU_ne_V : (U : E3) ≠ (V : E3))
    (hU_not_anti : (U : E3) ≠ -(V : E3))
    {k : ℕ} (hk : k < n + 1)
    (hzero : sOrient U V (A ⟨k, hk⟩) = 0) :
    ∃ c d : ℝ,
      (A ⟨k, hk⟩ : E3) =
        c • (U : E3) + d • (V : E3)
```

Use FFCT25’s span extraction theorem `lin_indep_span_of_det3_zero`, built exactly for extracting real coefficients from a vanishing determinant over a non-antipodal independent pair. fileciteturn102file0

Then run the sign trichotomy on `c,d`.

Estimate: **30–70 lines**, worker.

---

## 9. Step theorem

The real one-step theorem is:

```lean
theorem PlaneState.next_or_progress
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
    {U V : S2} {k : ℕ}
    (S : PlaneState A U V k)
    (hk1 : k + 1 < n + 1)
    (hU_nonincident :
      -- U is nonincident to edge (k,k+1), so edge_support applies
      True) -- replace by concrete Fin index side condition
    (hV_nonincident :
      True) :
    BoundaryZeroProgress A B ∨ PlaneState A U V (k + 1)
```

Implementation note: do **not** keep `U,V` abstract in the final wrap proof if the nonincident bookkeeping becomes heavy. Use concrete anchor versions:

```lean
PlaneState A (A (Fin.last n)) (A j) k
```

Then edge-support hypotheses are simply:

```lean
hA.closed_convex.edge_support ⟨k,_⟩ (Fin.last n)
hA.closed_convex.edge_support ⟨k,_⟩ j
```

with the incident cases routed to normalized-zero or flat-joint payload.

Estimate: **200–350 lines**, master.

---

## 10. Termination theorem

Avoid proving a complicated “all vertices forever” theorem. Terminate by distance to either:

1. a normalized ordinary nonincident support zero,
2. three consecutive interior vertices in the same plane,
3. a landed endpoint/corner branch.

The theorem:

```lean
theorem PlaneState.progress_until_exit
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
    {U V : S2} {k : ℕ}
    (S : PlaneState A U V k)
    (fuel : ℕ)
    (hbound : k + fuel < n + 1) :
    BoundaryZeroProgress A B
```

Use strong induction on `fuel`. At each step:

- If the current edge/probe arrangement is ordinary and nonincident, produce `NormalizedInteriorSupportZero`.
- If propagation creates three consecutive interior vertices in the plane, use the flat-joint kill.
- Otherwise call `PlaneState.next_or_progress`.

If the propagation ever reaches all edges in the same plane, use FFCT44’s `commonLine_collapse_forces_flat_joint`. FFCT44 proves that a closed chain whose every edge plane contains a common axis and whose interior joints are open is impossible. fileciteturn112file0

Estimate: **250–450 lines**, master.

---

## 11. Public flat-joint kill

FFCT44 has the pattern internally; expose a public reusable version.

```lean
theorem flat_interior_joint_absurd_public
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A)
    (hpos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hangle : JointLe A B)
    {r : ℕ}
    (hr : r + 2 < n + 1)
    (hdet :
      det3 (A ⟨r, by omega⟩ : E3)
           (A ⟨r + 1, by omega⟩ : E3)
           (A ⟨r + 2, by omega⟩ : E3) = 0) :
    False
```

Proof: use the public bridge `sphAngle_eq_zero_or_pi_of_det3_zero`, the edge-short facts from weak convexity, `PositiveJoints` for the lower bound, and `jointAngle_lt_pi` from strict `B` plus `JointLe`.

Estimate: **80–130 lines**, worker.

---

## 12. Discharging `WeakVanishingWrapSeedResidue`

Wrapper:

```lean
theorem weakVanishingWrapSeed_of_boundaryPropagation :
    WeakVanishingWrapSeedResidue := by
  intro n A B hA hpos hB hside hangle hnr hhem a b hne hne1 hwrap hzero
  have hbase : a.val = n := weak_wrap_base_is_last hwrap
  have hsucc : a + 1 = (0 : Fin (n + 1)) :=
    weak_wrap_successor_is_zero hwrap
  have hinterior : 0 < b.val ∧ b.val < n :=
    weak_wrap_probe_interior hne hne1 hwrap

  -- rewrite hzero into:
  -- sOrient (A (Fin.last n)) (A 0) (A b) = 0
  have hprog :=
    wrapPlanePropagation
      (A := A) (B := B) ... (j := b) ... hzero'

  rcases hprog with hnorm | hend
  · -- feed `hnorm` into the landed normalized weak seed/cut machinery
    ...
  · exact hend
```

The exact final lines depend on `WeakVanishingWrapSeedResidue`’s conclusion, but all index normalization is already proven in FFCT75. fileciteturn110file0

Estimate: **80–140 lines**, worker/master.

---

## 13. Discharging `SupportStuckWBSWrapSeedResidue`

Same theorem, opened-arm context.

```lean
theorem supportStuckWBSWrapSeed_of_boundaryPropagation :
    SupportStuckWBSWrapSeedResidue := by
  -- unfold residue
  -- identify opened arm A'
  -- rewrite the support-stuck wrap index using `weak_wrap_*`
  -- apply `wrapPlanePropagation` to A'
  -- map the normalized support progress to the support-stuck payload
```

Extra obligations are the opened arm’s weak convexity, positive joints, no-repeat, hemisphere, and comparison hypotheses. These are already threaded by the WBS/NR framework in FFCT74.

Estimate: **120–220 lines**, master wiring.

---

## 14. Discharging `BPosANegTailCornerResidue`

Use the apex variant.

```lean
theorem bpos_aneg_tailCorner_of_boundaryPropagation :
    BPosANegTailCornerResidue := by
  intro n P B hP hpos hB hside hangle hnr hhem i hij hi hi1 hn a b hspan hb ha

  have hzero :
      sOrient (P ⟨i, hi⟩)
        (P ⟨i + 1, hi1⟩)
        (P ⟨n, hn⟩) = 0 :=
    bpos_aneg_tail_span_forces_zero hi hi1 hn hspan

  have hprog :=
    apexNBoundaryZeroPropagation
      (A := P) (B := B) ... hzero

  rcases hprog with hnorm | hend
  · -- normalized support zero goes through landed cut/seed machinery
    ...
  · exact hend
```

FFCT75 already proves `bpos_aneg_tail_span_forces_zero`, the immediate zero-support consequence of the signed tail-corner span. fileciteturn110file0

Estimate: **100–180 lines**, master wiring.

---

## 15. Exact final surface

After these three wrappers:

```lean
structure Ch13FinalSurface76 : Prop where
  hcross : CrossPieceNoCollisionAtSup
```

and the new headline:

```lean
theorem spherical_arm_mono_final_ch13_v9
    (res : Ch13FinalSurface76)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤
      sDist (B 0) (B (Fin.last n))
```

`CrossPieceNoCollisionAtSup` should remain. It is a collision-at-sup exclusion, not a boundary-support-zero propagation statement. The new theorem only consumes determinant zeros involving the wrap edge or endpoint apex; it does not rule out cross-piece collisions compatible with all support inequalities.

---

## 16. Ordered brick list

| # | Brick | Difficulty | Estimate |
|---:|---|---:|---:|
| 1 | `NormalizedInteriorSupportZero`, `BoundaryZeroProgress` | worker | 20–40 |
| 2 | `flat_interior_joint_absurd_public` | worker | 80–130 |
| 3 | `boundaryPlane_step_sameSign` | worker | 70–120 |
| 4 | concrete zero-coeff kill lemmas | worker/master | 120–200 |
| 5 | `boundaryPlane_step_oppositeSign` routing to FFCT56/70/61 | master | 180–300 |
| 6 | `PlaneState` + `planeState_of_det_zero` | worker/master | 100–170 |
| 7 | `PlaneState.next_or_progress` | master | 200–350 |
| 8 | `PlaneState.progress_until_exit` | master | 250–450 |
| 9 | `wrapPlanePropagation` | master | 150–250 |
| 10 | `apexNBoundaryZeroPropagation` | master | 120–220 |
| 11 | `weakVanishingWrapSeed_of_boundaryPropagation` | worker/master | 80–140 |
| 12 | `supportStuckWBSWrapSeed_of_boundaryPropagation` | master | 120–220 |
| 13 | `bpos_aneg_tailCorner_of_boundaryPropagation` | master | 100–180 |
| 14 | `Ch13FinalSurface76`, `spherical_arm_mono_final_ch13_v9` | worker | 40–80 |

---

## 17. Degenerate audit

`n = 2`: do not run propagation. Dispatch to the existing base / two-edge comparison.

`n = 3`: wrap probes are adjacent or near-adjacent. Use adjacent folded-flat / last-corner / midFold kills, not a long propagation.

`j = 1`: the wrap zero cyclically becomes the ordinary support of edge `(0,1)` at `n`, i.e. a normalized boundary case already routed by landed cut machinery.

`j = n - 1`: this is the tail boundary case. Use the tail-ray / betweenness-additivity route already reduced in FFCT63, or the `apexNBoundaryZeroPropagation` wrapper if it appears as endpoint `n`.

Propagation hitting `j`: stop. If the current edge/probe is nonincident, return `NormalizedInteriorSupportZero`; if incident, one more propagation step either creates a flat interior joint or enters a landed endpoint branch.

Both anchors adjacent: this is not a cut seed. Use FFCT56/midFold or flat-joint kill.

No theorem should assert a universal `TailFoldBoundary A` without the full weak-convex/positive-joint/no-repeat/open-hemisphere/comparison context; FFCT63 and FFCT75 explicitly fixed that vacuity trap.
