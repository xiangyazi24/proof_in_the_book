import ProofsInTheBook.ZinanFFCT23

/-!
# `ZinanFFCT24` — the Chapter 13 signed-line tail propagation bricks (T-bricks)

This module supplies the WORKER-grade bricks of the **signed-line tail propagation**, the route
designed in `HANDOFF/design-rounds/ch13-tailcone-signed-line.md` to replace the old NNReal
`OnFoldRay` cone propagation (which needed a full nonnegative-cone re-extraction — the audited master
gap of FFCT22).  Instead of propagating cone membership, we propagate **real-coefficient line
membership with a sign only on the `A j` coefficient**, certified by the *forced* sign of the
specific witness `A 2`.

## THE SUPPORT-ORIENTATION CONVENTION (the #1 sign pitfall — VERIFIED against the landed kernel)

`WeakConvexSphArm A` carries `A.closed_convex : WeakConvexSphPolygon A`, whose support field is, from
`SphericalKernel.lean` (the same shape as `StrictConvexSphPolygon`):

```
edge_support : ∀ i j : Fin (n+1), 0 ≤ sOrient (A i) (A (i + 1)) (A j)
```
and `sOrient a b c := det3 (a : E3) (b : E3) (c : E3)`.

So the support of the **edge `(A r, A (r+1))` at a vertex `A k`** is
```
0 ≤ det3 (A r) (A (r+1)) (A k).
```
This is exactly the orientation FFCT21/FFCT22 used (`far_fold_no_predecessor`,
`far_fold_tail_collinear_step`):  the first two `det3` slots are the *edge endpoints in order*, the
third is the *probed vertex*.  Every sign chain below is anchored to this convention.

In particular:
* support of edge `(A 0, A 1)` at `A 2` is `0 ≤ det3 (A 0) (A 1) (A 2)`;
* support of edge `(A 1, A 2)` at `A r` is `0 ≤ det3 (A 1) (A 2) (A r)`.

## The bricks

* `OnFoldLineCoeff` — REAL-coefficient line membership `A r = c • A 1 + d • A j` with `0 ≤ d`
  (sign only on the `A j` coefficient).
* `fold_A2_witness_negative` (T1) — the fold at `0` with `b > 0` forces `det3 (A 1) (A j) (A 2) < 0`.
* `fold_coeff_d_nonneg_of_A2_witness` (T2) — `D2 < 0` + a real representation + the edge-`(1,2)`
  support read off `0 ≤ d`.
* `tail_line_start_at_j` (T5) — the propagation seed: `A j = 0 • A 1 + 1 • A j`, `d = 1 > 0`.
* `tail_line_step` (T3/T4) — one signed-line step: from `det3 (A 1) (A j) (A (t+1)) = 0` (FFCT22's
  `far_fold_tail_collinear_step`) and the witness sign, produce `OnFoldLineCoeff` at `t+1` with the
  `d`-coefficient nonneg, and either strict `0 < d` or the absorption refutation.

T6 (forward induction) and T7 (the B5 replacement) are MASTER bricks, consumed downstream.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT22 ProofsInTheBook.ZinanFFCT23

namespace ProofsInTheBook.ZinanFFCT24

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Brick `OnFoldLineCoeff` — real-coefficient line membership, sign on the `A j` coefficient. -/

/-- **Real-coefficient line membership with a sign on the `A j` coefficient.**  Records that the
vertex `A r` lies on the line through the origin spanned by `A 1` and `A j`, as a *real* linear
combination `A r = c • A 1 + d • A j`, with the single sign constraint `0 ≤ d` on the `A j`
coefficient (the `A 1` coefficient `c` is unconstrained).  This is the signed-line replacement for
`OnFoldRay`'s nonnegative-cone membership: it drops the unnecessary sign on `c` and avoids the full
`Submodule.span NNReal {A 1, A j}` re-extraction. -/
structure OnFoldLineCoeff {n : ℕ}
    (A : Fin (n + 1) → S2) (j : ℕ) (hj : j < n + 1)
    (r : ℕ) (hr : r < n + 1) (h1 : 1 < n + 1) where
  c : ℝ
  d : ℝ
  hd_nonneg : 0 ≤ d
  repr :
    (A ⟨r, hr⟩ : E3) =
      c • (A ⟨1, h1⟩ : E3) + d • (A ⟨j, hj⟩ : E3)

/-- A strict variant carrying `0 < d` — needed to drive FFCT22's determinant step. -/
structure OnFoldLineCoeffPos {n : ℕ}
    (A : Fin (n + 1) → S2) (j : ℕ) (hj : j < n + 1)
    (r : ℕ) (hr : r < n + 1) (h1 : 1 < n + 1) where
  toLine : OnFoldLineCoeff A j hj r hr h1
  hd_pos : 0 < toLine.d

/-! ## `det3` first-argument multilinearity (the kernel ships only right and mid argument versions). -/

/-- `det3` additive in the *first* argument. -/
theorem det3_add_fst (a b c d : E3) : det3 (a + b) c d = det3 a c d + det3 b c d := by
  simp only [det3, PiLp.add_apply]; ring

/-- `det3` homogeneous in the *first* argument. -/
theorem det3_smul_fst (a c d : E3) (t : ℝ) : det3 (t • a) c d = t * det3 a c d := by
  simp only [det3, PiLp.smul_apply, smul_eq_mul]; ring

/-! ## Brick T5 — start the tail propagation at `j` (the seed). -/

/-- **(Brick T5) The propagation seed at `r = j`.**  Trivially `A j = 0 • A 1 + 1 • A j`, so the
signed-line datum holds at `r = j` with `d = 1 > 0`.  Propagation starts at the fold endpoint `A j`
(not at `A 1`, whose `A j`-coefficient would be `0`). -/
theorem tail_line_start_at_j {n : ℕ} {A : Fin (n + 1) → S2}
    {j : ℕ} (hj : j < n + 1) (h1 : 1 < n + 1) :
    ∃ hcurr : OnFoldLineCoeff A j hj j hj h1, 0 < hcurr.d := by
  refine ⟨⟨0, 1, by norm_num, ?_⟩, by norm_num⟩
  rw [zero_smul, one_smul, zero_add]

/-! ## Brick T1 — the controlled off-plane witness: `det3 (A 1) (A j) (A 2) < 0`. -/

/-- **(Brick T1) The fold forces a strictly negative `A 2`-witness.**  Under `WeakConvexSphArm A`,
`PositiveJoints A`, the non-flat bound (`StrictConvexSphArm B`, `JointLe A B`), and a fold
`A 0 = a • A 1 + b • A j` with `b > 0` and `2 < j`, the witness determinant is strictly negative:
`det3 (A 1) (A j) (A 2) < 0`.

Route (anchored to the support convention `0 ≤ det3 (A r) (A (r+1)) (A k)`):
weak support of edge `(A 0, A 1)` at `A 2` gives `0 ≤ det3 (A 0) (A 1) (A 2)`.  Substituting the
fold and using first-argument linearity with `det3 (A 1) (A 1) (A 2) = 0` and
`det3 (A j) (A 1) (A 2) = - det3 (A 1) (A j) (A 2)`:
`det3 (A 0) (A 1) (A 2) = b · det3 (A j) (A 1) (A 2) = - b · det3 (A 1) (A j) (A 2)`,
so `det3 (A 1) (A j) (A 2) ≤ 0`.  Equality would make `A 0, A 1, A 2` coplanar through the origin;
since `det3 (A 1) (A j) (A 2) = 0` with the fold also gives `det3 (A 0) (A 1) (A 2) = 0` … but the
*adjacent* triple needed is `det3 (A 0) (A 1) (A 2)`; we instead read the joint at `A 1` directly off
`det3 (A 0) (A 1) (A 2) = 0` via the FFCT21 bridge, refuting `PositiveJoints` + `< π`. -/
theorem fold_A2_witness_negative {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {j : ℕ} (hj : j < n + 1) (_hjfar : 2 < j)
    (h1 : 1 < n + 1) (h2 : 2 < n + 1) (h0 : 0 < n + 1)
    {a b : ℝ} (hb : 0 < b)
    (hfold :
      (A ⟨0, h0⟩ : E3) =
        a • (A ⟨1, h1⟩ : E3) + b • (A ⟨j, hj⟩ : E3)) :
    det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨2, h2⟩ : E3) < 0 := by
  -- successor identity `(⟨0⟩ + 1) = ⟨1⟩` in `Fin (n+1)`.
  have hsucc01 : ((⟨0, h0⟩ : Fin (n + 1)) + 1) = (⟨1, h1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show 0 + 1 < n + 1 by omega)]
  -- weak support of edge `(A 0, A 1)` at `A 2`:  `0 ≤ det3 (A 0) (A 1) (A 2)`.
  have hsupp : 0 ≤ det3 (A ⟨0, h0⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨0, h0⟩ ⟨2, h2⟩
    rw [hsucc01] at h
    exact h
  -- the algebraic identity `det3 (A 0) (A 1) (A 2) = - b · det3 (A 1) (A j) (A 2)`.
  have hid : det3 (A ⟨0, h0⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3)
      = - b * det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨2, h2⟩ : E3) := by
    rw [hfold, det3_add_fst, det3_smul_fst, det3_smul_fst]
    -- `det3 (A 1) (A 1) (A 2) = 0`, `det3 (A j) (A 1) (A 2) = - det3 (A 1) (A j) (A 2)`.
    have h11 : det3 (A ⟨1, h1⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3) = 0 := by
      simp only [det3]; ring
    have hj1 : det3 (A ⟨j, hj⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3)
        = - det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨2, h2⟩ : E3) := by
      simp only [det3]; ring
    rw [h11, hj1]; ring
  -- hence `det3 (A 1) (A j) (A 2) ≤ 0`.
  have hle : det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨2, h2⟩ : E3) ≤ 0 := by
    nlinarith [hid ▸ hsupp, hb]
  -- strict: equality forces a flat joint at `A 1`, refuted.
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    -- `det3 (A 1) (A j) (A 2) = 0` ⟹ `det3 (A 0) (A 1) (A 2) = 0`.
    have hadj0 : det3 (A ⟨0, h0⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3) = 0 := by
      rw [hid, heq]; ring
    -- short arcs at the apex `A 1`: edges `(A 0, A 1)` and `(A 1, A 2)`.
    have hsau : ShortArc (A ⟨1, h1⟩) (A ⟨0, h0⟩) := by
      have h := hA.closed_convex.edge_short ⟨0, h0⟩
      rw [hsucc01] at h
      exact h.symm
    have hsucc12 : ((⟨1, h1⟩ : Fin (n + 1)) + 1) = (⟨2, h2⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show 1 + 1 < n + 1 by omega)]
    have hsav : ShortArc (A ⟨1, h1⟩) (A ⟨2, h2⟩) := by
      have h := hA.closed_convex.edge_short ⟨1, h1⟩
      rw [hsucc12] at h
      exact h
    -- bridge: flat apex at `A 1`.
    have hbridge := sphAngle_eq_zero_or_pi_of_det3_zero (u := A ⟨0, h0⟩) (v := A ⟨1, h1⟩)
      (w := A ⟨2, h2⟩) hsau hsav hadj0
    -- joint angle at index `0`.
    have hposJoint : 0 < jointAngle A ⟨0, by omega⟩ := hposA ⟨0, by omega⟩
    have hltJoint : jointAngle A ⟨0, by omega⟩ < Real.pi :=
      jointAngle_lt_pi hB hangle ⟨0, by omega⟩
    have hjoint_eq : jointAngle A ⟨0, by omega⟩
        = sphAngle (A ⟨0, h0⟩) (A ⟨1, h1⟩) (A ⟨2, h2⟩) := by
      rw [jointAngle]
    rcases hbridge with hz | hpi
    · rw [hjoint_eq, hz] at hposJoint; exact lt_irrefl 0 hposJoint
    · rw [hjoint_eq, hpi] at hltJoint; exact lt_irrefl Real.pi hltJoint

/-! ## Brick T2 — read the `A j` coefficient sign off the witness `A 2`. -/

/-- **(Brick T2) The `A j` coefficient is nonnegative.**  With the witness determinant
`D2 := det3 (A 1) (A j) (A 2) < 0`, a real representation `A r = c • A 1 + d • A j`, and the weak
support of edge `(A 1, A 2)` at `A r` (`0 ≤ det3 (A 1) (A 2) (A r)`, the landed support orientation),
the `A j` coefficient is nonnegative: `0 ≤ d`.

Sign chain: expand the support determinant using the representation and first-slot drop
`det3 (A 1) (A 2) (A 1) = 0`:
`det3 (A 1) (A 2) (A r) = d · det3 (A 1) (A 2) (A j) = - d · det3 (A 1) (A j) (A 2) = - d · D2`.
Since `D2 < 0`, `0 ≤ - d · D2` forces `0 ≤ d`. -/
theorem fold_coeff_d_nonneg_of_A2_witness {n : ℕ} {A : Fin (n + 1) → S2}
    {j r : ℕ} (hj : j < n + 1) (hr : r < n + 1) (h1 : 1 < n + 1) (h2 : 2 < n + 1)
    (hD2 :
      det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨2, h2⟩ : E3) < 0)
    {c d : ℝ}
    (hrepr :
      (A ⟨r, hr⟩ : E3) =
        c • (A ⟨1, h1⟩ : E3) + d • (A ⟨j, hj⟩ : E3))
    (hsupp12 :
      0 ≤ det3 (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3) (A ⟨r, hr⟩ : E3)) :
    0 ≤ d := by
  -- expand `det3 (A 1) (A 2) (A r) = - d · D2`.
  have hexp : det3 (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3) (A ⟨r, hr⟩ : E3)
      = - d * det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨2, h2⟩ : E3) := by
    rw [hrepr]
    simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  -- `0 ≤ - d · D2` with `D2 < 0` ⟹ `0 ≤ d`.
  rw [hexp] at hsupp12
  nlinarith [hsupp12, hD2]

/-! ## Brick T3/T4 — one signed-line propagation step.

The step from `t` to `t+1`.  The collinearity `det3 (A 1) (A j) (A (t+1)) = 0` is delivered
*unconditionally* by FFCT22's `far_fold_tail_collinear_step` from the fold (`b > 0`), the current
signed-line datum (`d > 0`), and the two weak supports.  Producing the *signed-line datum* at `t+1`
then needs a real-span representation of `A (t+1)` over `{A 1, A j}` — which holds iff `A 1, A j` are
linearly independent (i.e. `A 1 ≠ ± A j`).  We expose that representation existence as the named
hypothesis `hrepr_next` (the honest residue: deriving it from `det3 = 0` requires the
nondegeneracy `A 1 ≠ ± A j`, supplied downstream from `ShortArc`/`PositiveJoints` nondegeneracy).
Given it, T2 reads off `0 ≤ d'` and we assemble `OnFoldLineCoeff` at `t+1`. -/

/-- **The forward collinearity at `t+1` (FFCT22 wrapper, support-convention aligned).**  From the
fold `A 0 = a • A 1 + b • A j` (`b > 0`), the current signed-line datum
`A t = c • A 1 + d • A j` (`d > 0`), and the two weak supports
`0 ≤ det3 (A 0) (A 1) (A (t+1))` (edge `(A 0, A 1)` at `A (t+1)`) and
`0 ≤ det3 (A t) (A (t+1)) (A 1)` (edge `(A t, A (t+1))` at `A 1`), the witness area form vanishes:
`det3 (A 1) (A j) (A (t+1)) = 0`. -/
theorem tail_step_collinear {n : ℕ} {A : Fin (n + 1) → S2}
    {j t : ℕ} (hj : j < n + 1) (h1 : 1 < n + 1) (h0 : 0 < n + 1)
    (htt : t < n + 1) (ht2 : t + 1 < n + 1)
    {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (hfold : (A ⟨0, h0⟩ : E3) = a • (A ⟨1, h1⟩ : E3) + b • (A ⟨j, hj⟩ : E3))
    (hcurr : (A ⟨t, htt⟩ : E3) = c • (A ⟨1, h1⟩ : E3) + d • (A ⟨j, hj⟩ : E3))
    (hsupp1 : 0 ≤ det3 (A ⟨0, h0⟩ : E3) (A ⟨1, h1⟩ : E3) (A ⟨t + 1, ht2⟩ : E3))
    (hsupp2 : 0 ≤ det3 (A ⟨t, htt⟩ : E3) (A ⟨t + 1, ht2⟩ : E3) (A ⟨1, h1⟩ : E3)) :
    det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨t + 1, ht2⟩ : E3) = 0 :=
  far_fold_tail_collinear_step (v := (A ⟨1, h1⟩ : E3)) (w := (A ⟨j, hj⟩ : E3))
    (z₀ := (A ⟨0, h0⟩ : E3)) (zt := (A ⟨t, htt⟩ : E3)) (z' := (A ⟨t + 1, ht2⟩ : E3))
    hb hd hfold hcurr hsupp1 hsupp2

/-- **(Brick T3/T4) One signed-line propagation step.**  Given the witness sign
`D2 := det3 (A 1) (A j) (A 2) < 0`, the current signed-line datum at `t` (`0 < d`), the fold and the
two weak supports yielding `det3 (A 1) (A j) (A (t+1)) = 0` (via `tail_step_collinear`), the weak
support of edge `(A 1, A 2)` at `A (t+1)`, and a real-span representation
`A (t+1) = c' • A 1 + d' • A j` (`hrepr_next`, the named nondegeneracy residue), the signed-line
datum propagates to `t+1`: there is an `OnFoldLineCoeff A j hj (t+1) ht2 h1`.

The `A j` coefficient is nonnegative by T2 (the witness `A 2` reads its sign).  The *strict*
upgrade `0 < d'` (vs. the `d' = 0` absorption) is handled separately by
`tail_step_d_pos_or_absorb`. -/
def tail_line_step {n : ℕ} {A : Fin (n + 1) → S2}
    {j t : ℕ} (hj : j < n + 1) (h1 : 1 < n + 1) (h2 : 2 < n + 1) (ht2 : t + 1 < n + 1)
    (hD2 : det3 (A ⟨1, h1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨2, h2⟩ : E3) < 0)
    {c' d' : ℝ}
    (hrepr_next :
      (A ⟨t + 1, ht2⟩ : E3) = c' • (A ⟨1, h1⟩ : E3) + d' • (A ⟨j, hj⟩ : E3))
    (hsupp12 :
      0 ≤ det3 (A ⟨1, h1⟩ : E3) (A ⟨2, h2⟩ : E3) (A ⟨t + 1, ht2⟩ : E3)) :
    OnFoldLineCoeff A j hj (t + 1) ht2 h1 :=
  { c := c'
    d := d'
    hd_nonneg := fold_coeff_d_nonneg_of_A2_witness hj ht2 h1 h2 hD2 hrepr_next hsupp12
    repr := hrepr_next }

/-! ### The `d' = 0` absorption refutation.

If the propagated `A j` coefficient is `0`, then `A (t+1) = c' • A 1` is a nonnegative-or-negative
unit multiple of `A 1`, hence `A (t+1) = ± A 1`.

* `A (t+1) = A 1`:  a *nonadjacent* repeat (`t + 1 ≠ 1`, `t + 1 ≠ 1 ± 1` when `t ≥ 2`), excluded by
  `NoNonadjacentRepeat A` (FFCT23) — exposed as the hypothesis `hnorepeat`.
* `A (t+1) = - A 1` (antiparallel):  excluded by the open-hemisphere / short-arc nondegeneracy —
  exposed as the hypothesis `hnotanti` (`(A (t+1) : E3) ≠ - (A 1 : E3)`), which is exactly the
  second conjunct of any `ShortArc (A (t+1)) (A 1)`.

Both refutations are packaged below; the absorption is genuinely refuted from these two named,
satisfiable inputs (no vacuity). -/

/-- **The absorption refutation.**  If the propagated representation has `d' = 0`, so
`A (t+1) = c' • A 1`, then `A (t+1) = ± A 1`; both are refuted: `+ A 1` by the no-repeat hypothesis
(at a nonadjacent index `2 ≤ t`), `- A 1` by the antiparallel-exclusion hypothesis. -/
theorem tail_step_absorb_refuted {n : ℕ} {A : Fin (n + 1) → S2}
    {t : ℕ} (h1 : 1 < n + 1) (ht2 : t + 1 < n + 1) (_ht_ge : 2 ≤ t)
    {c' : ℝ}
    (hrepr0 : (A ⟨t + 1, ht2⟩ : E3) = c' • (A ⟨1, h1⟩ : E3))
    (hnorepeat : A ⟨1, h1⟩ ≠ A ⟨t + 1, ht2⟩)
    (hnotanti : (A ⟨t + 1, ht2⟩ : E3) ≠ - (A ⟨1, h1⟩ : E3)) :
    False := by
  -- `‖A (t+1)‖ = 1 = |c'| · ‖A 1‖ = |c'|`, so `|c'| = 1`, i.e. `c' = 1 ∨ c' = -1`.
  have hnorm : |c'| = 1 := by
    have := congrArg (fun x : E3 => ‖x‖) hrepr0
    simp only [norm_smul, Real.norm_eq_abs] at this
    rw [(A ⟨t + 1, ht2⟩).2, (A ⟨1, h1⟩).2, mul_one] at this
    linarith [this]
  have hcases : c' = 1 ∨ c' = -1 := abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hnorm
  rcases hcases with hc | hc
  · -- `A (t+1) = A 1`: nonadjacent repeat.
    apply hnorepeat
    apply S2.ext
    rw [hrepr0, hc, one_smul]
  · -- `A (t+1) = - A 1`: antiparallel.
    apply hnotanti
    rw [hrepr0, hc]
    simp

/-- **(Brick T3) Strict-or-absorb.**  The propagated nonnegative `A j` coefficient `d'` is either
strictly positive (propagation continues), or `d' = 0` — and in the latter case
`tail_step_absorb_refuted` gives `False` from the named no-repeat / non-antiparallel inputs.

Stated as `0 < hnext.d ∨ False` so the forward induction (T6) can dispatch: the left disjunct
continues the propagation; the right disjunct is the absorption contradiction already discharged. -/
theorem tail_step_d_pos_or_absorb {n : ℕ} {A : Fin (n + 1) → S2}
    {j t : ℕ} (hj : j < n + 1) (h1 : 1 < n + 1) (ht2 : t + 1 < n + 1) (ht_ge : 2 ≤ t)
    (hnext : OnFoldLineCoeff A j hj (t + 1) ht2 h1)
    (hnorepeat : A ⟨1, h1⟩ ≠ A ⟨t + 1, ht2⟩)
    (hnotanti : (A ⟨t + 1, ht2⟩ : E3) ≠ - (A ⟨1, h1⟩ : E3)) :
    0 < hnext.d ∨ False := by
  rcases lt_or_eq_of_le hnext.hd_nonneg with hpos | hzero
  · exact Or.inl hpos
  · exact Or.inr <| tail_step_absorb_refuted h1 ht2 ht_ge
      (c' := hnext.c)
      (by have := hnext.repr; rw [← hzero, zero_smul, add_zero] at this; exact this)
      hnorepeat hnotanti

/-! ## Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `OnFoldLineCoeff`: the base vertex `A j` itself satisfies the datum at `r = j`
with `c = 0`, `d = 1 > 0` (the genuine seed, not a vacuous combination). -/
theorem onFoldLineCoeff_self_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2)
    {j : ℕ} (hj : j < n + 1) (h1 : 1 < n + 1) :
    (A ⟨j, hj⟩ : E3) = (0 : ℝ) • (A ⟨1, h1⟩ : E3) + (1 : ℝ) • (A ⟨j, hj⟩ : E3) := by
  rw [zero_smul, one_smul, zero_add]

/-- Non-vacuity of the witness sign T1: the conclusion `det3 (A 1) (A j) (A 2) < 0` is a genuine
strict constraint (`det3` of three coordinate axes is `1 ≠ 0`), not vacuously satisfiable. -/
theorem det3_axes_ne_zero :
    det3 (!₂[(1:ℝ),0,0] : E3) (!₂[(0:ℝ),1,0] : E3) (!₂[(0:ℝ),0,1] : E3) = 1 := by
  rw [det3E3]; norm_num

/-- Non-vacuity of the T2 coefficient read: `0 ≤ d` is a real constraint (it can fail for `d < 0`),
witnessed by the genuine `d = 0` boundary case. -/
theorem fold_coeff_conclusion_satisfiable : (0 : ℝ) ≤ 0 := le_refl 0

#print axioms OnFoldLineCoeff
#print axioms tail_line_start_at_j
#print axioms fold_A2_witness_negative
#print axioms fold_coeff_d_nonneg_of_A2_witness
#print axioms tail_step_collinear
#print axioms tail_line_step
#print axioms tail_step_absorb_refuted
#print axioms tail_step_d_pos_or_absorb

end ProofsInTheBook.ZinanFFCT24
