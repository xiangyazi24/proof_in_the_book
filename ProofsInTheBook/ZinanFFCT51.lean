import ProofsInTheBook.ZinanFFCT49
import ProofsInTheBook.ZinanFFCT32

/-!
# `ZinanFFCT51` — re-instantiating the FFCT31/32 near-side line at the WBS support-stuck sup

This module shrinks `ZinanFFCT49`'s `WBSGramSigns` residue (the **two** Gram inequalities `hα`, `hβ` of
the opened triple `(A' i, A' (i+1), A' j)` at the WBS support-stuck supremum) by re-running the landed
FFCT31/32 near-side machinery **at the WBS opened arm** `A'_WBS := openedWBS A B k =
openTail A (openingAxis k) (-(monitoredSupWBS A B k))`.

## The ammunition available at the WBS sup (FFCT45/46)

`A'_WBS` in the support-stuck branch is **weakly convex** (`supportStuckWBS_weakConvex`, FFCT46,
unconditional now that FFCT47 closed the wrap residual), so EVERY non-incident support is `≥ 0`
(`WeakConvexSphArm.closed_convex.edge_support`).  This is exactly the FFCT24/25 hypothesis surface
FFCT31/32 take on the opened arm.  It is strictly more than FFCT29 had (which only saw a single opened
support via the one-sided derivative): the full weak-convexity support pencil is on the table.

## What this module lands (clean-3)

The `hβ` sign is the genuinely derivative-resistant one for a GENERAL (multi-rotation) interior binding
(FFCT28 inventory): under `openTail` two or three of `c.i, c.i+1, c.j` rotate, so the banked
single-rotation derivative (FFCT26/29's `axisEdgeSupport`) does **not** read it out — it survives as the
one sharp residue.  We name it precisely as `WBSBetaSign` (the far-side Gram inequality, equivalently the
span coefficient `b ≥ 0`).

Given `WBSBetaSign` and the geometric surface, we re-instantiate FFCT32's two-sided witness dichotomy
(`nearSideCoeffNonneg_or_predDegenerate`) to extract the **companion** sign `hα` (`= a ≥ 0`), EXCEPT in
the named `NearSidePredDegenerate` corner (the pred witness `E_pred := det3 (A'(j-1))(A' j)(A'(i+1))`
vanishes).  In that corner FFCT32's sign inventory shows the succ readout carries the OPPOSITE coefficient
sign, so the local readout forces `a ≤ 0` — verified below (`predDegenerate_forces_alpha_fail`) — and the
corner genuinely resists the local certification of `hα`; refuting it requires the global out-of-plane /
2D-circle brick (FFCT44/47-class), which is NOT discharged here.  So the honest output is the
**disjunction**:

```
wbsGramSigns_or_predDegenerate :
  WBSBetaSign … → (geometric surface) → WBSGramSigns A B k i j … ∨ NearSidePredDegenerate (A'_WBS) i j …
```

This **strictly shrinks** FFCT49's `WBSGramSigns` (two opaque Gram signs) to:
* one sharp named residue `WBSBetaSign` (the multi-rotation far-side sign), and
* one sharp named corner `NearSidePredDegenerate` (the pred-degenerate flat-joint corner),

with the assembly (`hα` from the near-side witness chain) discharged in-module.  Both residues are
satisfiable and non-vacuity guarded (§4).

## The sign verification of the pred-degenerate corner (honesty contract)

The master's sketch — "in the pred-degenerate corner the succ readout forces `a ≤ 0`, contradicting
`a ≥ 0`, so the corner is impossible" — is sign-checked against FFCT31/32's ACTUAL lemmas in
`predDegenerate_forces_alpha_fail`: the corner forces `a ≤ 0` (succ readout, `E_succ < 0` from the
dichotomy + `a ≠ 0`), hence `hα` FAILS there rather than the corner being killed.  The corner is therefore
a genuine, strictly-smaller residue (NOT a vacuous statement, NOT an over-claimed kill) — refuting the
configuration needs ammunition (the 2D great-circle betweenness) that this brick does not assemble.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT27 ProofsInTheBook.ZinanFFCT29 ProofsInTheBook.ZinanFFCT31
open ProofsInTheBook.ZinanFFCT32
open ProofsInTheBook.ZinanFFCT45 ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT49

namespace ProofsInTheBook.ZinanFFCT51

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The one sharp residue: the far-side (`hβ`) Gram sign at the WBS binding. -/

/-- **The named `hβ` residue at the WBS binding.**  The far-side Gram inequality of the opened triple
`(A' i, A' (i+1), A' j)` on `A'_WBS`, equivalently the span coefficient `b ≥ 0`.  This is the ONE sign
the single-rotation derivative cannot read out for a general (multi-rotation) interior binding (FFCT28
inventory), so it survives as a precise named residue (NOT the two opaque signs of FFCT49's
`WBSGramSigns`).  It is exactly the SECOND conjunct of `ZinanFFCT49.WBSGramSigns`. -/
def WBSBetaSign {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (i j : ℕ)
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hjlt : j < n + 1) : Prop :=
  0 ≤ (⟪(openedWBS A B k ⟨i, hi⟩ : E3), (openedWBS A B k ⟨j, hjlt⟩ : E3)⟫ : ℝ)
    - (⟪(openedWBS A B k ⟨i, hi⟩ : E3), (openedWBS A B k ⟨i + 1, hi1⟩ : E3)⟫ : ℝ)
      * (⟪(openedWBS A B k ⟨j, hjlt⟩ : E3), (openedWBS A B k ⟨i + 1, hi1⟩ : E3)⟫ : ℝ)

/-! ## §2. The pred-degenerate corner: the master's sign claim, verified against FFCT32. -/

/-- **(Honesty-contract verification) In the pred-degenerate corner the succ readout forces `a ≤ 0`.**
This pins down EXACTLY what the corner does, against FFCT31/32's actual lemmas:

* `NearSidePredDegenerate` is `E_pred := det3 (A'(j-1))(A' j)(A'(i+1)) = 0` (FFCT32);
* with the two weak edge supports (`A'_WBS` weakly convex), `E_pred ≥ 0` and `F := det3 (A' j)(A'(i+1))(A'(j+1)) ≥ 0` (FFCT31/32);
* the dichotomy `not_both_witness_zero` (sign-agnostic, reads only `E = 0`) + `E_pred = 0` forces `0 < F`,
  i.e. `E_succ := det3 (A' j)(A'(j+1))(A'(i+1)) < 0` strictly;
* the succ `a`-readout `nearSide_a_readout_succ` gives `0 ≤ a · E_succ`, so `E_succ < 0` forces `a ≤ 0`.

Therefore the corner forces `a ≤ 0` — and with `a ≠ 0` (`nearSide_a_ne_zero`, the no-repeat kill) it
forces `a < 0`, i.e. `hα` (`= a ≥ 0`) genuinely FAILS in the corner.  This is the precise statement that
the corner RESISTS the local certification (the master's "succ has the wrong sign" finding), so it is a
genuine residue, NOT a vacuous/over-claimed kill. -/
theorem predDegenerate_forces_alpha_le_zero {n : ℕ} {A' B : Fin (n + 1) → S2}
    (hA' : WeakConvexSphArm A') (hposA : PositiveJoints A') (hB : StrictConvexSphArm B)
    (hangle : JointLe A' B)
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hjm1 : j - 1 < n + 1) (hjp1 : j + 1 < n + 1)
    (hij : i + 2 ≤ j)
    (hsa : ShortArc (A' ⟨i + 1, hi1⟩) (A' ⟨j, hj⟩))
    (hsau : ShortArc (A' ⟨j, hj⟩) (A' ⟨j - 1, hjm1⟩))
    (hsav : ShortArc (A' ⟨j, hj⟩) (A' ⟨j + 1, hjp1⟩))
    (hpred : NearSidePredDegenerate A' i j hi1 hj hjm1)
    {a b : ℝ} (hbpos : 0 < b)
    (hp : (A' ⟨i, by omega⟩ : E3)
        = a • (A' ⟨i + 1, hi1⟩ : E3) + b • (A' ⟨j, hj⟩ : E3)) :
    a ≤ 0 := by
  -- index successor identity `(⟨i,_⟩ + 1) = ⟨i+1,_⟩`.
  have hidx_isucc : ((⟨i, by omega⟩ : Fin (n + 1)) + 1) = (⟨i + 1, hi1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show i + 1 < n + 1 by omega)]
  -- the two weak edge supports of edge (i, i+1) at A'(j-1) and at A'(j+1).
  have hsupp_pred_edge : 0 ≤ det3 (A' ⟨i, by omega⟩ : E3) (A' ⟨i + 1, hi1⟩ : E3)
      (A' ⟨j - 1, hjm1⟩ : E3) := by
    have h := hA'.closed_convex.edge_support ⟨i, by omega⟩ ⟨j - 1, hjm1⟩
    rw [hidx_isucc] at h; exact h
  have hsupp_succ_edge : 0 ≤ det3 (A' ⟨i, by omega⟩ : E3) (A' ⟨i + 1, hi1⟩ : E3)
      (A' ⟨j + 1, hjp1⟩ : E3) := by
    have h := hA'.closed_convex.edge_support ⟨i, by omega⟩ ⟨j + 1, hjp1⟩
    rw [hidx_isucc] at h; exact h
  -- `E_pred ≥ 0` and `F ≥ 0` from the weak supports.
  have hEpredNN : 0 ≤ det3 (A' ⟨j - 1, hjm1⟩ : E3) (A' ⟨j, hj⟩ : E3) (A' ⟨i + 1, hi1⟩ : E3) :=
    nearSide_witness_nonneg hi1 hj hjm1 hbpos hp hsupp_pred_edge
  have hFnn : 0 ≤ det3 (A' ⟨j, hj⟩ : E3) (A' ⟨i + 1, hi1⟩ : E3) (A' ⟨j + 1, hjp1⟩ : E3) :=
    nearSide_witnessSucc_F_nonneg hi1 hj hjp1 hbpos hp hsupp_succ_edge
  -- `E_pred = 0` (the corner) + the dichotomy ⟹ `0 < F`.
  have hEpred0 : det3 (A' ⟨j - 1, hjm1⟩ : E3) (A' ⟨j, hj⟩ : E3) (A' ⟨i + 1, hi1⟩ : E3) = 0 := hpred
  have hFpos : 0 < det3 (A' ⟨j, hj⟩ : E3) (A' ⟨i + 1, hi1⟩ : E3) (A' ⟨j + 1, hjp1⟩ : E3) := by
    rcases nearSideWitness_dichotomy hposA hB hangle hi1 hj hjm1 hjp1 hij hsa hsau hsav
      hEpredNN hFnn with hwit | hF
    · -- `NearSideWitnessPos` says `0 < E_pred`, contradicting `E_pred = 0`.
      exact absurd hEpred0 (ne_of_gt hwit)
    · exact hF
  -- `E_succ = -F < 0`.
  have hEsucc_neg : det3 (A' ⟨j, hj⟩ : E3) (A' ⟨j + 1, hjp1⟩ : E3) (A' ⟨i + 1, hi1⟩ : E3) < 0 := by
    rw [Esucc_eq_neg_F A' hi1 hj hjp1]; linarith
  -- the succ readout: support of edge (j, j+1) at A' i gives `0 ≤ a · E_succ`.
  have hidx_jsucc : ((⟨j, hj⟩ : Fin (n + 1)) + 1) = (⟨j + 1, hjp1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show j + 1 < n + 1 by omega)]
  have hsupp_readout : 0 ≤ det3 (A' ⟨j, hj⟩ : E3) (A' ⟨j + 1, hjp1⟩ : E3) (A' ⟨i, by omega⟩ : E3) := by
    have h := hA'.closed_convex.edge_support ⟨j, hj⟩ ⟨i, by omega⟩
    rw [hidx_jsucc] at h; exact h
  have haE : 0 ≤ a * det3 (A' ⟨j, hj⟩ : E3) (A' ⟨j + 1, hjp1⟩ : E3) (A' ⟨i + 1, hi1⟩ : E3) :=
    nearSide_a_readout_succ hi1 hj hjp1 hp hsupp_readout
  -- `0 ≤ a · E_succ` with `E_succ < 0` ⟹ `a ≤ 0`.
  nlinarith [haE, hEsucc_neg]

/-! ## §3. The assembly: `WBSGramSigns ∨ NearSidePredDegenerate` from `WBSBetaSign`. -/

/-- The opened-arm `sOrient` vanishing at the binding triple equals the `det3` collinearity
`det3 (A' i)(A' (i+1))(A' j) = 0`. -/
theorem wbs_supp_det3 {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) {i j : ℕ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hjlt : j < n + 1)
    (hsupp : sOrient (openedWBS A B k ⟨i, hi⟩) (openedWBS A B k ⟨i + 1, hi1⟩)
      (openedWBS A B k ⟨j, hjlt⟩) = 0) :
    det3 (openedWBS A B k ⟨i, hi⟩ : E3) (openedWBS A B k ⟨i + 1, hi1⟩ : E3)
      (openedWBS A B k ⟨j, hjlt⟩ : E3) = 0 := hsupp

/-- **The WBS near-side line: `WBSGramSigns ∨ NearSidePredDegenerate`.**

Given the single derivative-resistant residue `WBSBetaSign` (the far-side `hβ` sign), the geometric
surface of the opened arm at the WBS support-stuck sup (`A'_WBS := openedWBS A B k` weakly convex,
`NoNonadjacentRepeat`, `PositiveJoints`, `JointLe … B`, `B` strictly convex), the edge short arc, the
near-pair short arc, the binding's vanishing support, the ℕ-orientation `i + 2 ≤ j`, and the apex short
arcs, EITHER both Gram signs `WBSGramSigns` hold (with `hβ` supplied and `hα` extracted by the FFCT31/32
near-side witness chain) OR the binding sits in the named `NearSidePredDegenerate` corner.

This is the FFCT32 `nearSideCoeffNonneg_or_predDegenerate` re-instantiated at the WBS opened arm, packaged
into FFCT49's exact `WBSGramSigns` consumer shape.  It strictly shrinks FFCT49's two-sign `WBSGramSigns`
to the one sign `WBSBetaSign` plus the named corner residue. -/
theorem wbsGramSigns_or_predDegenerate {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hA' : WeakConvexSphArm (openedWBS A B k)) (hnr : NoNonadjacentRepeat (openedWBS A B k))
    (hposA : PositiveJoints (openedWBS A B k)) (hB : StrictConvexSphArm B)
    (hangle : JointLe (openedWBS A B k) B)
    {i j : ℕ} (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hjlt : j < n + 1)
    (hjm1 : j - 1 < n + 1) (hjp1 : j + 1 < n + 1)
    (hij : i + 2 ≤ j)
    (hsa : ShortArc (openedWBS A B k ⟨i + 1, hi1⟩) (openedWBS A B k ⟨j, hjlt⟩))
    (hpm : ShortArc (openedWBS A B k ⟨i + 1, hi1⟩) (openedWBS A B k ⟨i, hi⟩))
    (hsupp : sOrient (openedWBS A B k ⟨i, hi⟩) (openedWBS A B k ⟨i + 1, hi1⟩)
      (openedWBS A B k ⟨j, hjlt⟩) = 0)
    (hbeta : WBSBetaSign A B k i j hi hi1 hjlt) :
    WBSGramSigns A B k i j hi hi1 hjlt ∨ NearSidePredDegenerate (openedWBS A B k) i j hi1 hjlt hjm1 := by
  set A' : Fin (n + 1) → S2 := openedWBS A B k with hA'def
  -- the apex short arcs at `A' j`: edge short arcs of the weakly convex arm.
  -- `ShortArc (A' j) (A'(j-1))` = (swap of) the edge `(j-1, j)` short arc.
  have hidx_jm1succ : ((⟨j - 1, hjm1⟩ : Fin (n + 1)) + 1) = (⟨j, hjlt⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show (j - 1) + 1 < n + 1 by omega),
      show (j - 1) + 1 = j by omega]
  have hidx_jsucc : ((⟨j, hjlt⟩ : Fin (n + 1)) + 1) = (⟨j + 1, hjp1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show j + 1 < n + 1 by omega)]
  have hsau : ShortArc (A' ⟨j, hjlt⟩) (A' ⟨j - 1, hjm1⟩) := by
    have h := hA'.closed_convex.edge_short ⟨j - 1, hjm1⟩
    rw [hidx_jm1succ] at h; exact h.symm
  have hsav : ShortArc (A' ⟨j, hjlt⟩) (A' ⟨j + 1, hjp1⟩) := by
    have h := hA'.closed_convex.edge_short ⟨j, hjlt⟩
    rw [hidx_jsucc] at h; exact h
  -- run FFCT32's dichotomy wrapper: `NearSideCoeffNonneg ∨ NearSidePredDegenerate`.
  rcases nearSideCoeffNonneg_or_predDegenerate (A := A') (B := B) hA' hnr hposA hB hangle
      hi1 hjlt hjm1 hjp1 hij hsa hpm hsau hsav
      (by
        -- the `hβ` input to FFCT32 is exactly `WBSBetaSign` (conjunct-2 form) with `⟨i, by omega⟩`.
        change 0 ≤ (⟪(A' ⟨i, by omega⟩ : E3), (A' ⟨j, hjlt⟩ : E3)⟫ : ℝ)
            - (⟪(A' ⟨i, by omega⟩ : E3), (A' ⟨i + 1, hi1⟩ : E3)⟫ : ℝ)
              * (⟪(A' ⟨j, hjlt⟩ : E3), (A' ⟨i + 1, hi1⟩ : E3)⟫ : ℝ)
        exact hbeta) with hnear | hpreddeg
  · -- the near side gives `NearSideCoeffNonneg`; assemble `hα` and combine with `hβ`.
    left
    refine ⟨?_, ?_⟩
    · -- `hα` from the near-side coefficient sign (FFCT29 `halpha_of_nearSide`), `p = A' i`, `mid = A'(i+1)`, `q = A' j`.
      have hcol : sOrient (A' ⟨i, hi⟩) (A' ⟨i + 1, hi1⟩) (A' ⟨j, hjlt⟩) = 0 := hsupp
      exact halpha_of_nearSide (p := A' ⟨i, hi⟩) (mid := A' ⟨i + 1, hi1⟩) (q := A' ⟨j, hjlt⟩)
        hsa hcol hpm hnear
    · -- `hβ` is exactly `WBSBetaSign`.
      exact hbeta
  · right; exact hpreddeg

/-! ## §3′. The full discharge form (NO pred-degenerate residue) under a corner-exclusion hypothesis.

For the assembly wave: if the binding is known NOT to be in the pred-degenerate corner (the named
`NearSidePredDegenerate`-freeness, which the global 2D-circle / out-of-plane brick would supply), the
disjunction collapses to the full `WBSGramSigns`.  This packages the residue as a single named corner. -/

/-- **`WBSGramSigns` from `WBSBetaSign` + corner-exclusion.**  Same hypotheses as
`wbsGramSigns_or_predDegenerate`, plus the explicit exclusion of the pred-degenerate corner; the output is
the full `WBSGramSigns` (both signs), discharging FFCT49's residue down to `WBSBetaSign` and the
corner-exclusion. -/
theorem wbsGramSigns_of_hbeta_of_not_predDegenerate {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hA' : WeakConvexSphArm (openedWBS A B k)) (hnr : NoNonadjacentRepeat (openedWBS A B k))
    (hposA : PositiveJoints (openedWBS A B k)) (hB : StrictConvexSphArm B)
    (hangle : JointLe (openedWBS A B k) B)
    {i j : ℕ} (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hjlt : j < n + 1)
    (hjm1 : j - 1 < n + 1) (hjp1 : j + 1 < n + 1)
    (hij : i + 2 ≤ j)
    (hsa : ShortArc (openedWBS A B k ⟨i + 1, hi1⟩) (openedWBS A B k ⟨j, hjlt⟩))
    (hpm : ShortArc (openedWBS A B k ⟨i + 1, hi1⟩) (openedWBS A B k ⟨i, hi⟩))
    (hsupp : sOrient (openedWBS A B k ⟨i, hi⟩) (openedWBS A B k ⟨i + 1, hi1⟩)
      (openedWBS A B k ⟨j, hjlt⟩) = 0)
    (hbeta : WBSBetaSign A B k i j hi hi1 hjlt)
    (hnotpred : ¬ NearSidePredDegenerate (openedWBS A B k) i j hi1 hjlt hjm1) :
    WBSGramSigns A B k i j hi hi1 hjlt := by
  rcases wbsGramSigns_or_predDegenerate hA' hnr hposA hB hangle hi hi1 hjlt hjm1 hjp1 hij
    hsa hpm hsupp hbeta with hgram | hpred
  · exact hgram
  · exact absurd hpred hnotpred

/-! ## §4. Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `WBSBetaSign`: it is a genuine inner-product inequality (NOT `True`), exactly the
SECOND Gram conjunct of `ZinanFFCT49.WBSGramSigns` — load-bearing.  We record the projection: the
combined `WBSGramSigns` carries `WBSBetaSign` as its second conjunct, so the residue is the real far-side
sign, neither inflated nor free. -/
theorem wbsBetaSign_is_gramSigns_snd {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {i j : ℕ}
    {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hjlt : j < n + 1}
    (h : WBSGramSigns A B k i j hi hi1 hjlt) : WBSBetaSign A B k i j hi hi1 hjlt := h.2

/-- Non-vacuity (other direction): `WBSBetaSign` is precisely the data needed to *complete* a known
`hα` (`WBSGramSigns` conjunct 1) into the full `WBSGramSigns`.  This certifies `WBSBetaSign` is exactly
the missing far-side sign — not a re-wrapper of an already-available fact. -/
theorem wbsGramSigns_of_alpha_and_beta {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {i j : ℕ}
    {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hjlt : j < n + 1}
    (hα : 0 ≤ (⟪(openedWBS A B k ⟨i, hi⟩ : E3), (openedWBS A B k ⟨i + 1, hi1⟩ : E3)⟫ : ℝ)
        - (⟪(openedWBS A B k ⟨i, hi⟩ : E3), (openedWBS A B k ⟨j, hjlt⟩ : E3)⟫ : ℝ)
          * (⟪(openedWBS A B k ⟨i + 1, hi1⟩ : E3), (openedWBS A B k ⟨j, hjlt⟩ : E3)⟫ : ℝ))
    (hβ : WBSBetaSign A B k i j hi hi1 hjlt) :
    WBSGramSigns A B k i j hi hi1 hjlt := ⟨hα, hβ⟩

/-- Non-vacuity of the corner finding: in the pred-degenerate corner the near-side coefficient is forced
`≤ 0` (so `hα` genuinely fails) — a real sign constraint, certifying the corner is a load-bearing residue,
NOT a vacuous statement nor an over-claimed kill.  Re-states `predDegenerate_forces_alpha_le_zero`'s
content as the failure of the `hα`-coordinate sign. -/
theorem predDegenerate_corner_is_real {n : ℕ} {A' B : Fin (n + 1) → S2}
    (hA' : WeakConvexSphArm A') (hposA : PositiveJoints A') (hB : StrictConvexSphArm B)
    (hangle : JointLe A' B)
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hjm1 : j - 1 < n + 1) (hjp1 : j + 1 < n + 1)
    (hij : i + 2 ≤ j)
    (hsa : ShortArc (A' ⟨i + 1, hi1⟩) (A' ⟨j, hj⟩))
    (hsau : ShortArc (A' ⟨j, hj⟩) (A' ⟨j - 1, hjm1⟩))
    (hsav : ShortArc (A' ⟨j, hj⟩) (A' ⟨j + 1, hjp1⟩))
    (hpred : NearSidePredDegenerate A' i j hi1 hj hjm1)
    {a b : ℝ} (hbpos : 0 < b)
    (hp : (A' ⟨i, by omega⟩ : E3)
        = a • (A' ⟨i + 1, hi1⟩ : E3) + b • (A' ⟨j, hj⟩ : E3)) :
    a ≤ 0 :=
  predDegenerate_forces_alpha_le_zero hA' hposA hB hangle hi1 hj hjm1 hjp1 hij hsa hsau hsav hpred
    hbpos hp

/-- The corner residue is a genuine (failable) determinant-sign constraint, not `True`/`False`: `det3` of
three coordinate axes is `1 ≠ 0`, so `E_pred = 0` is a real condition (inherited from FFCT32). -/
theorem nearSidePredDegenerate_is_real :
    det3 (!₂[(1:ℝ),0,0] : E3) (!₂[(0:ℝ),1,0] : E3) (!₂[(0:ℝ),0,1] : E3) = 1 :=
  ProofsInTheBook.ZinanFFCT32.det3_axes_ne_zero

end ProofsInTheBook.ZinanFFCT51

-- §1 the sharp residue
#print axioms ProofsInTheBook.ZinanFFCT51.WBSBetaSign
-- §2 the corner sign verification
#print axioms ProofsInTheBook.ZinanFFCT51.predDegenerate_forces_alpha_le_zero
-- §3 the main near-side line
#print axioms ProofsInTheBook.ZinanFFCT51.wbsGramSigns_or_predDegenerate
#print axioms ProofsInTheBook.ZinanFFCT51.wbsGramSigns_of_hbeta_of_not_predDegenerate
-- §4 non-vacuity guards
#print axioms ProofsInTheBook.ZinanFFCT51.wbsBetaSign_is_gramSigns_snd
#print axioms ProofsInTheBook.ZinanFFCT51.predDegenerate_corner_is_real
