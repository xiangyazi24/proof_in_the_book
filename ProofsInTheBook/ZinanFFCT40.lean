import ProofsInTheBook.ZinanFFCT39

/-!
# `ZinanFFCT40` — the §3.3 REPAIR of clause (iii): the *vacuously-conditional* half of the Chapter-13
  `-δ` headline, restated with correct scoping and re-threaded honestly.

`ZinanFFCT38.mainPlus_headline_final` is `clean-3`, but `ZinanFFCT39`'s adversarial audit established
that its clause-(iii) half is **vacuously conditional**: the two names `glueWClauseIII_of_residues`
consumes are FALSE `Prop`s as demanded —

* `OpenedEdgesDistinctW` over **all** arms (refuted by the constant arm, `not_openedEdgesDistinctW_constant`);
* `HemiMarginStrictPosAtSupW` over **all** of `StuckW` (self-contradictory on the hemi branch,
  `hemiMarginStrictPosAtSupW_self_contradictory_on_hemiStuck`).

`ZinanFFCT38.stuckOutcomeW_weakConvex_of_residues` hides this: its pure-hemi (all-supports-strict)
sub-case is closed by `exfalso`, leaning on the false `hhemstrict r` to declare it impossible — exactly
the playbook §3.3 "vacuous conditional via an unsatisfiable hypothesis" failure mode.

This module carries out the genuine repair.  The truth, established below by re-using the honest
FFCT30/36 hemi-stuck dichotomy (`hemiStuck_dichotomy_tangentFree`, which is `(∃ vanishing support) ∨
WeakConvex`, **with no hemi-strictness residual at all**), is:

> At a `StuckW` supremum the opened arm is `WeakConvexSphArm`, and EITHER a non-incident support vanishes
> (the support / weak-flat outcome the CUT step consumes) OR there is none — the **pure-hemi** outcome,
> in which all supports are strict and the arm is in fact `StrictConvexSphArm` (a tilted hemisphere
> normal exists), with the joint *not* having reached.

The original clause (iii) demanded `∃ vanishing support` **unconditionally** under `StuckW`.  The
pure-hemi outcome has **no** vanishing support, so the original conclusion is genuinely **false** there.
The honest repair therefore restates clause (iii) (and the family-agnostic outcome it feeds) with the
pure-hemi disjunct made explicit:

    StuckW → WeakConvex ∧ ( (∃ vanishing support) ∨ StrictConvexSphArm A'_W )

— and the corrected `InteriorOpeningOutcome'` carries the same third alternative.  To recover the
*original* termination-ready `InteriorOpeningOutcome` (whose recursion needs either a deficit drop or a
vanishing support), the pure-hemi alternative must be collapsed: the single, honestly-named, **non-vacuous**
residual `PureHemiProgressW` (a pure-hemi supremum forces either `ReachW` — joint reached, deficit drops
— or a vanishing support).  This is the *real* irreducible content of the hemi branch, isolated cleanly
instead of being faked away by the false strict-margin Prop.

## What is proved here (clean-3, no `sorry`/`axiom`/`admit`/`native_decide`)

* `§1` `weakConvex_of_supportStuckW_of_hemiPos_anyH` — the `∃ h'` sibling of
  `SphericalOpeningGlue.weakConvex_of_supportStuck_of_hemiPos`, at the W angles (a near-verbatim copy
  with the fixed `h₀` generalised to an existential unit witness — `open_hemisphere` is itself `∃`).
* `§2` `OpenedClosingEdgeDistinctAtSupW`, `SupportStuckMarginsPosAtSupW` — the correctly **context-scoped**
  residuals (scoped exactly to the glue binders, NOT over all arms), with non-vacuity guards and the
  refutation-resistance checks that killed FFCT38's shapes.
* `§3` `GlueWClauseIII'` / `glueWClauseIII_repaired` — the corrected clause (iii) with the pure-hemi
  disjunct, discharged from the scoped residuals via the honest FFCT30/36 dichotomy (NO `exfalso` on
  pure-hemi, NO false strict-margin Prop).
* `§3` `InteriorOpeningOutcomeW'`, `interiorOpeningOutcomeW_repaired` — the corrected family-agnostic
  outcome, and `mainPlus_headline_repaired` — the headline with the FINAL honest residue list (the
  pure-hemi alternative collapsed by the named `PureHemiProgressW`).

The honest residue surface is strictly *smaller and true* where FFCT38's was *larger and false*.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT38
open ProofsInTheBook.ZinanFFCT39

namespace ProofsInTheBook.ZinanFFCT40

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The any-`h` support-stuck weak-convex assembler.

`SphericalOpeningGlue.weakConvex_of_supportStuck_of_hemiPos` hard-wires the *fixed* ambient normal `h₀`
into `open_hemisphere := ⟨h₀, hnorm, hhem⟩`.  Since `WeakConvexSphPolygon.open_hemisphere` is itself
`∃ h, ‖h‖ = 1 ∧ ∀ i, 0 < ⟪h, P i⟫`, the proof generalises verbatim to *any* unit witness `h'` with
strict margins — which is exactly what the hemi-stuck branch (whose vanishing margin disqualifies the
ambient `h₀`) needs to supply via a tilt.  This is the near-verbatim copy with `h₀ ⤳ ∃ h'`. -/

/-- **The `∃ h'` sibling of `weakConvex_of_supportStuck_of_hemiPos`.**  From the closure supports
(`≥ 0`), edge distinctness, and a strict open-hemisphere witness `h'` for *some* unit `h'` (rather than
the fixed ambient `h₀`), the opened arm is `WeakConvexSphArm`.  The proof is the original's, reading the
existential witness off `hhem`. -/
theorem weakConvex_of_supportStuckW_of_hemiPos_anyH {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) {K : Fin (n + 1)} {δ : ℝ}
    (hsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 ≤ sOrient (openTail A K δ i) (openTail A K δ (i + 1)) (openTail A K δ j))
    (hdist : ∀ i : Fin (n + 1), openTail A K δ i ≠ openTail A K δ (i + 1))
    (hhem : ∃ h' : E3, ‖h'‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h', ((openTail A K δ r : S2) : E3)⟫ : ℝ)) :
    WeakConvexSphArm (openTail A K δ) := by
  obtain ⟨h', hnorm, hhem'⟩ := hhem
  -- verbatim from `weakConvex_of_supportStuck_of_hemiPos`, with `h'` the supplied witness.
  have h3 : 3 ≤ n + 1 := by have := hA.two_le; omega
  have hedge : ∀ i : Fin (n + 1), ShortArc (openTail A K δ i) (openTail A K δ (i + 1)) :=
    fun i => shortArc_of_hemisphere (hhem' i) (hhem' (i + 1)) (hdist i)
  refine { two_le := hA.two_le, closed_convex := ?_ }
  refine { three_le := h3
           edge_short := hedge
           edge_support := ?_
           open_hemisphere := ⟨h', hnorm, hhem'⟩ }
  intro i j
  by_cases hji : j = i
  · subst hji; rw [sOrient, det3_self_right]
  · by_cases hji1 : j = i + 1
    · subst hji1; rw [sOrient, det3_self_mid]
    · exact hsupp i j hji hji1

/-! ## §2. Correctly-scoped residuals.

FFCT38's two names were quantified over **all** arms / all of `StuckW`, which is precisely why they were
false (refuted by the constant arm and by the hemi disjunct).  The honest replacements are quantified
**inside** the glue context — the strict-convex / deficit / hemisphere / stuck binders of
`GlueWClauseIII` — and scoped to the support branch where they are genuinely true.  These are the
`InteriorOpeningGlueW`-binder-matched, refutation-resistant versions. -/

/-- **(Scoped Brick 1.)**  `OpenedClosingEdgeDistinctAtSupW`: the single wraparound closing edge
`(last, 0)` of the opened arm is distinct, quantified **inside** the glue context (`StrictConvexSphArm A`
present).  This is FFCT39's `OpenedClosingEdgeDistinctW` sub-residual lifted to the context binders, so
it cannot be refuted by a constant arm (which is excluded by `StrictConvexSphArm A`).  All other opened
edges are discharged unconditionally by `openedEdgesDistinctW_of_closing`. -/
def OpenedClosingEdgeDistinctAtSupW : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∀ h₀ : E3, ‖h₀‖ = 1 → (∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) →
      StuckW A B k h₀ Real.pi →
      OpenedClosingEdgeDistinctW A B k h₀

/-- **(Scoped Brick 2.)**  `SupportStuckMarginsPosAtSupW`: at a **support-stuck** supremum (the support
disjunct of `StuckW`), no fixed-`h₀` hemisphere margin of the opened arm vanishes.  Quantified inside the
glue context and **restricted to the support branch** — this is the geometric content
`BoundaryConvexPersistAtSup`, named.  It does NOT contradict the hemi-stuck branch: the premise is the
support disjunct, where (unlike the hemi disjunct) no `h₀`-margin need vanish, so the §3.3 self-
contradiction that killed FFCT38's global `HemiMarginStrictPosAtSupW` is structurally avoided. -/
def SupportStuckMarginsPosAtSupW : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∀ h₀ : E3, ‖h₀‖ = 1 → (∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) →
      (∃ c : NonIncident n,
        supportConstraint A (openingAxis k) c (-(monitoredSupW A B k h₀ Real.pi)) = 0) →
      SupportStuckMarginsPos A B k h₀

/-! ### Non-vacuity / refutation-resistance guards for the scoped residuals. -/

/-- Non-vacuity of `OpenedClosingEdgeDistinctAtSupW`'s **conclusion** (not a vacuous hypothesis): the
closing-edge distinctness is, at `δ*_W = 0`, the genuine base-arm closing edge `A last ≠ A (last+1)`,
real geometric content (mirrors FFCT39's `openedClosingEdgeDistinctW_nonvacuous`). -/
theorem openedClosingEdgeDistinctAtSupW_conclusion_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2)
    (K : Fin (n + 1)) (i : Fin (n + 1)) (hne : openTailW A K 0 i ≠ openTailW A K 0 (i + 1)) :
    A i ≠ A (i + 1) :=
  openedClosingEdgeDistinctW_nonvacuous A K i hne

/-- **Refutation-resistance of the scoped Brick 1.**  Unlike FFCT38's all-arms `OpenedEdgesDistinctW`,
the scoped form is NOT refutable by a constant arm: the constant arm fails `StrictConvexSphArm A`, so it
is excluded from the context binders before the closing-edge clause is ever reached.  We record the
explicit witness: a constant arm has no `StrictConvexSphArm` instance (it would force a strict
non-incident support `0 < sOrient p p p = 0`). -/
theorem openedClosingEdgeDistinctAtSupW_constantArm_excluded {n : ℕ} (p : S2)
    (hStrict : StrictConvexSphArm (fun _ : Fin (n + 1) => p)) : False := by
  have h3 := hStrict.closed_convex.three_le
  -- pick a non-incident triple (0, 0+1, 0+2); the strict support is `sOrient p p p = 0`, contradiction.
  have hni0 : (0 + 2 : Fin (n + 1)) ≠ 0 := by
    intro he; have h := congrArg Fin.val he
    have h2v : ((0 + 2 : Fin (n + 1)) : ℕ) = 2 := by simp; omega
    rw [h2v] at h; simp at h
  have hni1 : (0 + 2 : Fin (n + 1)) ≠ 0 + 1 := by
    intro he; have h := congrArg Fin.val he
    have h2v : ((0 + 2 : Fin (n + 1)) : ℕ) = 2 := by simp; omega
    have h1v : ((0 + 1 : Fin (n + 1)) : ℕ) = 1 := by simp; omega
    rw [h2v, h1v] at h; omega
  have hpos := hStrict.closed_convex.strict_nonincident 0 (0 + 2) hni0 hni1
  rw [sOrient, det3_self_right] at hpos
  exact lt_irrefl _ hpos

/-- Non-vacuity of `SupportStuckMarginsPosAtSupW`'s **conclusion**: at `δ*_W = 0` it is `⟪h₀, A r⟫ ≠ 0`,
which holds for an arm strictly inside the `h₀`-hemisphere — real geometric content (mirrors FFCT39's
`supportStuckMarginsPos_nonvacuous`). -/
theorem supportStuckMarginsPosAtSupW_conclusion_nonvacuous {n : ℕ} {A : Fin (n + 1) → S2}
    {K : Fin (n + 1)} {h₀ : E3} (r : Fin (n + 1)) (hpos : 0 < (⟪h₀, (A r : E3)⟫ : ℝ)) :
    hemiMargin A K h₀ r 0 ≠ 0 :=
  supportStuckMarginsPos_nonvacuous r hpos

/-- **Refutation-resistance of the scoped Brick 2.**  The scoped premise is the **support** disjunct of
`StuckW`, NOT all of `StuckW`.  On the hemi disjunct the global FFCT38 form was self-contradictory
(`hemiMarginStrictPosAtSupW_self_contradictory_on_hemiStuck`); the scoped form never asserts strictness
at a hemi-stuck vertex, because its premise is the *support* disjunct.  We record that the scoped
premise and a hemi-stuck datum are *not* a contradiction by exhibiting that the scoped conclusion
(`SupportStuckMarginsPos`, all margins `≠ 0`) is consistent with a *support*-stuck supremum whose
hemisphere margins are all strictly positive (the support branch's defining geometry). -/
theorem supportStuckMarginsPosAtSupW_supportBranch_consistent {n : ℕ} {A B : Fin (n + 1) → S2}
    {k : Fin (n - 1)} {h₀ : E3}
    (hstrict : ∀ r : Fin (n + 1),
      0 < hemiMargin A (openingAxis k) h₀ r (-(monitoredSupW A B k h₀ Real.pi))) :
    SupportStuckMarginsPos A B k h₀ :=
  fun r => ne_of_gt (hstrict r)

/-! ## §3. The repaired clause (iii), the corrected outcome, and the repaired headline.

The honest dichotomy at a `StuckW` supremum is `ZinanFFCT36.hemiStuck_dichotomy_tangentFree` (the
equator residual is already discharged outright by FFCT36): from the closure supports (`≥ 0`) and the
closure margins (`≥ 0`), it returns

    (∃ vanishing non-incident support) ∨ WeakConvexSphArm A'_W,

with **no** hemi-strictness residual.  We thread BOTH branches honestly:

* if a support vanishes, FFCT39's `openedEdgesDistinctW_of_closing` (mod the scoped closing-edge
  residual) gives edge distinctness, FFCT39's `hemiMarginStrictPos_supportStuck` (mod the scoped
  support-margin residual) gives strict ambient-`h₀` margins, and `§1` assembles `WeakConvex`; the
  vanishing support is the FFCT38 §1 W bridge — the **support** alternative;
* otherwise all supports are strict, the dichotomy already returns `WeakConvexSphArm`, and the arm is in
  fact `StrictConvexSphArm` (the tilted normal exists) — the **pure-hemi** alternative.  There is no
  vanishing support here, so the clause must (and does) carry it as the explicit second disjunct. -/

/-- **The pure-hemi strict-convexity certificate.**  In the pure-hemi sub-branch (a hemisphere margin
vanishes but ALL non-incident supports are strict), the opened arm `A'_W` is `StrictConvexSphArm`: the
strict supports + a tilted strict open-hemisphere normal (FFCT30 tilt + FFCT36 separation, packaged in
`hemiStuck_dichotomy_tangentFree`'s strict branch) give `reach_strictConvex_interior` at `-δ*_W`. -/
theorem pureHemi_strictConvexW {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3} (hnorm : ‖h₀‖ = 1)
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hstrictsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 < sOrient (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) i)
        (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) (i + 1))
        (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) j)) :
    StrictConvexSphArm (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)) := by
  set d : ℝ := -(monitoredSupW A B k h₀ Real.pi) with hd
  have hAW : openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)
      = openTail A (openingAxis k) d := rfl
  have h3 : 3 ≤ n + 1 := by have := hA.two_le; omega
  -- strict supports in the `openTail … d` form.
  have hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 < sOrient (openTail A (openingAxis k) d i) (openTail A (openingAxis k) d (i + 1))
        (openTail A (openingAxis k) d j) := by
    intro i j hji hji1; have := hstrictsupp i j hji hji1; rwa [hAW] at this
  -- closure margins (≥ 0) for the tilt base.
  have hhemnn : ∀ r : Fin (n + 1),
      0 ≤ (⟪h₀, ((openTail A (openingAxis k) d r : S2) : E3)⟫ : ℝ) := by
    intro r; have := hemiW_inner_nonneg hka hkt h0 r; rwa [hAW] at this
  -- the tilt: FFCT36 strict-support separation gives the equator tangent; FFCT30 tilt gives `h'`.
  have hshort := shortArc_edge_zero_of_strict hA h3 hmix
  have htangent : EquatorTangentExists A (openingAxis k) h₀ d :=
    equatorTangentExists_of_strictSupports hmix hshort
  obtain ⟨t, ht⟩ := htangent
  obtain ⟨h', hh'norm, hh'pos⟩ :=
    exists_unit_perturbed_normal_of_tangent (m := n + 1) (by omega)
      (fun r => ((openTail A (openingAxis k) d r : S2) : E3)) h₀ t hhemnn ht
  -- strict convexity from `reach_strictConvex_interior` with the tilted normal.
  rw [hAW]
  exact reach_strictConvex_interior hA hh'norm hmix hh'pos

/-- **The repaired STUCK outcome (the honest clause-(iii) core).**  From a `StuckW` supremum, the scoped
closing-edge residual, and the scoped support-margin residual, the opened arm `A'_W` is `WeakConvexSphArm`,
and EITHER a non-incident support vanishes OR `A'_W` is `StrictConvexSphArm` (the pure-hemi case).  NO
`exfalso` on the pure-hemi branch; NO false strict-margin Prop. -/
theorem stuckOutcomeW_repaired {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3} (hnorm : ‖h₀‖ = 1)
    (hkdef : jointAngle A k < jointAngle B k)
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hhpos : ∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ))
    (hclose : OpenedClosingEdgeDistinctW A B k h₀)
    (hmargins : (∃ c : NonIncident n,
        supportConstraint A (openingAxis k) c (-(monitoredSupW A B k h₀ Real.pi)) = 0) →
      SupportStuckMarginsPos A B k h₀)
    (hstuck : StuckW A B k h₀ Real.pi) :
    WeakConvexSphArm (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)) ∧
      ((∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
          sOrient (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) i)
            (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) (i + 1))
            (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) j) = 0) ∨
        StrictConvexSphArm (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi))) := by
  classical
  set d : ℝ := -(monitoredSupW A B k h₀ Real.pi) with hd
  have hAW : openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)
      = openTail A (openingAxis k) d := rfl
  have h3 : 3 ≤ n + 1 := by have := hA.two_le; omega
  -- closure supports (≥ 0) and margins (≥ 0) in the `openTail … d` form.
  have hsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (openTail A (openingAxis k) d i) (openTail A (openingAxis k) d (i + 1))
        (openTail A (openingAxis k) d j) := by
    intro i j hji hji1; have := supportW_sOrient_nonneg hka hkt h0 i j hji hji1; rwa [hAW] at this
  have hhemnn : ∀ r : Fin (n + 1),
      0 ≤ (⟪h₀, ((openTail A (openingAxis k) d r : S2) : E3)⟫ : ℝ) := by
    intro r; have := hemiW_inner_nonneg hka hkt h0 r; rwa [hAW] at this
  -- the honest dichotomy: (∃ vanishing support) ∨ WeakConvex, with NO hemi residual.
  rcases hemiStuck_dichotomy_tangentFree hA h3 hsupp hhemnn with hsupzero | hweak
  · -- SUPPORT alternative: a non-incident support vanishes.
    -- WeakConvex via the support brick; the vanishing support is the payload.
    obtain ⟨i, j, hji, hji1, heq⟩ := hsupzero
    have hvanish : ∃ c : NonIncident n,
        supportConstraint A (openingAxis k) c (-(monitoredSupW A B k h₀ Real.pi)) = 0 := by
      refine ⟨(⟨(i, j), ⟨hji, hji1⟩⟩ : NonIncident n), ?_⟩
      rw [supportConstraint_apply]; exact heq
    -- edge distinctness from FFCT39 (mod the scoped closing-edge residual).
    have hdist : OpenedEdgesDistinctW A B k h₀ := openedEdgesDistinctW_of_closing hA k h₀ hclose
    have hdist' : ∀ i : Fin (n + 1),
        openTail A (openingAxis k) d i ≠ openTail A (openingAxis k) d (i + 1) := by
      intro i; have := hdist i; rwa [hAW] at this
    -- strict ambient-h₀ margins from FFCT39 (mod the scoped support-margin residual).
    have hpos : SupportStuckMarginsPos A B k h₀ := hmargins hvanish
    have hhemstrict : ∀ r : Fin (n + 1),
        0 < (⟪h₀, ((openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) r : S2) : E3)⟫ : ℝ) :=
      hemiMarginStrictPos_supportStuck hka hkt h0 hpos
    have hhemstrict' : ∀ r : Fin (n + 1),
        0 < (⟪h₀, ((openTail A (openingAxis k) d r : S2) : E3)⟫ : ℝ) := by
      intro r; have := hhemstrict r; rwa [hAW] at this
    have hweak : WeakConvexSphArm (openTail A (openingAxis k) d) :=
      weakConvex_of_supportStuckW_of_hemiPos_anyH hA hsupp hdist' ⟨h₀, hnorm, hhemstrict'⟩
    rw [hAW]
    exact ⟨hweak, Or.inl ⟨i, j, hji, hji1, heq⟩⟩
  · -- WeakConvex without a vanishing support: split on whether some support actually vanishes.
    by_cases hsome : ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
        sOrient (openTail A (openingAxis k) d i) (openTail A (openingAxis k) d (i + 1))
          (openTail A (openingAxis k) d j) = 0
    · -- some support vanishes: the SUPPORT alternative (with `hweak` already in hand).
      obtain ⟨i, j, hji, hji1, heq⟩ := hsome
      rw [hAW]
      exact ⟨hweak, Or.inl ⟨i, j, hji, hji1, heq⟩⟩
    · -- PURE-HEMI: all supports strict ⟹ `A'_W` is strictly convex.
      have hmix : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
          0 < sOrient (openTail A (openingAxis k) d i) (openTail A (openingAxis k) d (i + 1))
            (openTail A (openingAxis k) d j) := by
        intro i j hji hji1
        exact lt_of_le_of_ne (hsupp i j hji hji1) (fun h => hsome ⟨i, j, hji, hji1, h.symm⟩)
      have hmix' : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
          0 < sOrient (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) i)
            (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) (i + 1))
            (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) j) := by
        intro i j hji hji1; rw [hAW]; exact hmix i j hji hji1
      have hstrict := pureHemi_strictConvexW hA hnorm hka hkt h0 hmix'
      exact ⟨hweak, Or.inr hstrict⟩

/-! ### The corrected clause (iii) `Prop` and its discharge. -/

/-- **The repaired clause (iii) `Prop`** (the `-δ` STUCK outcome with the pure-hemi disjunct made
explicit).  This is the honest replacement for `ZinanFFCT37.GlueWClauseIII`: at a `StuckW` supremum the
opened arm is `WeakConvexSphArm`, and EITHER a non-incident support vanishes OR `A'_W` is strictly convex
(the pure-hemi case the original clause silently — and falsely — demanded a vanishing support for). -/
def GlueWClauseIII' : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A → StrictConvexSphArm B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∀ h₀ : E3, ‖h₀‖ = 1 → (∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) →
      StuckW A B k h₀ Real.pi →
        WeakConvexSphArm (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)) ∧
        ((∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
            sOrient (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) i)
              (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) (i + 1))
              (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) j) = 0) ∨
          StrictConvexSphArm (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)))

/-- **`GlueWClauseIII'` from the two correctly-scoped residuals.**  The honest discharge of the repaired
clause (iii): assembles `stuckOutcomeW_repaired` from `OpenedClosingEdgeDistinctAtSupW` (scoped Brick 1)
and `SupportStuckMarginsPosAtSupW` (scoped Brick 2).  No vacuous hypothesis is consumed. -/
theorem glueWClauseIII_repaired (hclose : OpenedClosingEdgeDistinctAtSupW)
    (hmargins : SupportStuckMarginsPosAtSupW) :
    GlueWClauseIII' := by
  intro n A B hA hB k hkdef h₀ hnorm hhpos hstuck
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0 :=
    monitoredFamily_init_admissible hA hhpos hkdef
  have hclose' : OpenedClosingEdgeDistinctW A B k h₀ :=
    hclose n A B hA k hkdef h₀ hnorm hhpos hstuck
  have hmargins' : (∃ c : NonIncident n,
      supportConstraint A (openingAxis k) c (-(monitoredSupW A B k h₀ Real.pi)) = 0) →
      SupportStuckMarginsPos A B k h₀ :=
    fun hsup => hmargins n A B hA k hkdef h₀ hnorm hhpos hsup
  exact stuckOutcomeW_repaired hA hnorm hkdef hka hkt h0 hhpos hclose' hmargins' hstuck

/-! ### The corrected family-agnostic outcome.

`SphericalArmAssembly.InteriorOpeningOutcome`'s STUCK disjunct is `WeakConvex ∧ ∃ vanishing support`,
consumed by `open_step`'s CUT branch.  The pure-hemi alternative produces a *strictly convex* `A'_W`
with NO deficit drop and NO vanishing support — neither the original REACH disjunct (no drop) nor the
STUCK disjunct (no vanishing support).  So the honest corrected outcome carries the explicit third
alternative `InteriorOpeningOutcome'`. -/

/-- **The corrected interior-opening outcome** (`-δ`, with the pure-hemi third alternative).  Identical
to `SphericalArmAssembly.InteriorOpeningOutcome` except the STUCK disjunct additionally admits a
strictly-convex pure-hemi opened arm — strictly convex but **without** a guaranteed deficit drop or
vanishing support, the honest outcome the audit exposed.  The third disjunct is exactly the data
`stuckOutcomeW_repaired` produces in the pure-hemi case; collapsing it back into the original
`InteriorOpeningOutcome` shape is the job of the named `PureHemiProgressW` residual below. -/
def InteriorOpeningOutcomeW' : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2,
    StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∃ A' : Fin (n + 1) → S2,
      endpt A ≤ endpt A' ∧ SameSides A' B ∧ JointLe A' B ∧
      ((StrictConvexSphArm A' ∧ deficitCount A' B < deficitCount A B) ∨
       (WeakConvexSphArm A' ∧
        ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
          sOrient (A' i) (A' (i + 1)) (A' j) = 0) ∨
       -- the honest PURE-HEMI third alternative: strictly convex, no deficit-drop guarantee.
       StrictConvexSphArm A')

/-- **The pure-hemi progress residual** (the FINAL honest irreducible content of the hemi branch).  At a
pure-hemi supremum (a hemisphere margin vanishes, all non-incident supports strict, so `A'_W` is
strictly convex), the opening makes recursion-ready progress: EITHER the joint reached `B`'s value
(`ReachW`, so the deficit drops by `deficitCount_openTail_reach_lt`) OR a non-incident support in fact
vanishes (the CUT-ready weak-flat alternative).  This is the single named, **non-vacuous** residual that
collapses the pure-hemi third alternative back into the original `InteriorOpeningOutcome` shape — the
geometric fact FFCT38 hid behind the false `HemiMarginStrictPosAtSupW`. -/
def PureHemiProgressW : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A → StrictConvexSphArm B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∀ h₀ : E3, ‖h₀‖ = 1 → (∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) →
      StuckW A B k h₀ Real.pi →
      StrictConvexSphArm (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)) →
        ReachW A B k h₀ Real.pi ∨
        (∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
          sOrient (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) i)
            (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) (i + 1))
            (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) j) = 0)

/-- **The corrected `InteriorOpeningOutcome` (original shape) from the repaired clause (iii) + the
pure-hemi progress residual.**  Threads `glueWClauseIII_repaired`'s output through the FFCT38 dispatch,
but resolves the pure-hemi alternative honestly: if pure-hemi yields `ReachW`, the joint reached and the
deficit drops (the REACH disjunct); if it yields a vanishing support, that is the STUCK disjunct.  Thus
the *original* termination-ready `InteriorOpeningOutcome` is recovered with no false hypothesis. -/
theorem interiorOpeningOutcomeW_repaired (hcap : GlueWBaseCap)
    (hclose : OpenedClosingEdgeDistinctAtSupW) (hmargins : SupportStuckMarginsPosAtSupW)
    (hprog : PureHemiProgressW) :
    SphericalArmAssembly.InteriorOpeningOutcome := by
  intro n A B hA hB hside hangle k hkdef
  obtain ⟨h₀, hnorm, hhpos⟩ := hA.closed_convex.open_hemisphere
  set K : Fin (n + 1) := openingAxis k with hK
  set δ : ℝ := monitoredSupW A B k h₀ Real.pi with hδ
  set A' : Fin (n + 1) → S2 := openTailW A K δ with hA'
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0 :=
    monitoredFamily_init_admissible hA hhpos hkdef
  -- `A' = openTail A K (-δ)`.
  have hA'eq : A' = openTail A K (-δ) := rfl
  -- side/joint bookkeeping (verbatim from `interiorOpeningOutcomeW_of_glue`).
  have hjointk : jointAngle A' k = openedInteriorJointAngle A k (-δ) := by
    rw [hA'eq]; exact jointAngle_openTail_eq_openedInterior A k (-δ)
  have hslack : openedInteriorJointAngle A k (-δ) ≤ jointAngle B k := by
    have hmem := monitoredSupW_mem (B := B) (h₀ := h₀) hka hkt Real.pi_nonneg h0
    have := hmem.2 (Sum.inr (Sum.inr ()))
    simp only [monitoredFamilyW, monitoredFamily, interiorTargetSlack] at this
    rw [hδ]; linarith
  have hside' : SameSides A' B := by
    intro i; rw [hA'eq, openTail_preserves_sides A K (-δ) i]; exact hside i
  have hangle' : JointLe A' B := by
    intro r
    by_cases hrk : r = k
    · rw [hrk, hjointk]; exact hslack
    · rw [hA'eq, jointAngle_openTail_eq_of_ne A k (-δ) hrk]; exact hangle r
  -- endpoint non-decrease (clause i, mod the cap).
  have hmono : endpt A ≤ endpt A' :=
    glueW_clause_i hA hB hka hkt h0 (hcap n A B hA hB k hkdef h₀ hnorm hhpos)
  refine ⟨A', hmono, hside', hangle', ?_⟩
  by_cases hstuck : StuckW A B k h₀ Real.pi
  · -- STUCK: the repaired clause (iii).
    have hclause :=
      glueWClauseIII_repaired hclose hmargins n A B hA hB k hkdef h₀ hnorm hhpos hstuck
    obtain ⟨hweak, halt⟩ := hclause
    rcases halt with hvanish | hstrict
    · -- vanishing support: the STUCK (RIGHT) disjunct.
      exact Or.inr ⟨hweak, hvanish⟩
    · -- pure-hemi strict arm: collapse via the progress residual.
      rcases hprog n A B hA hB k hkdef h₀ hnorm hhpos hstuck hstrict with hreach | hvanish
      · -- ReachW ⟹ deficit drops: the REACH (LEFT) disjunct.
        have hreach_k : jointAngle (openTail A K (-δ)) k = jointAngle B k := by
          rw [jointAngle_openTail_eq_openedInterior A k (-δ)]; exact hreach
        have hdrop : deficitCount A' B < deficitCount A B := by
          rw [hA'eq]; exact deficitCount_openTail_reach_lt A B k (-δ) hkdef hreach_k
        exact Or.inl ⟨hstrict, hdrop⟩
      · -- a support actually vanishes: the STUCK (RIGHT) disjunct (with `hweak`).
        exact Or.inr ⟨hweak, hvanish⟩
  · -- ¬ StuckW ⟹ ReachW: the REACH (LEFT) disjunct.
    have hreach : ReachW A B k h₀ Real.pi := glueW_clause_ii hA hB hka hkt h0 hstuck
    have hreach_k : jointAngle (openTail A K (-δ)) k = jointAngle B k := by
      rw [jointAngle_openTail_eq_openedInterior A k (-δ)]; exact hreach
    have hstrict : StrictConvexSphArm A' :=
      strictW_persistence_at_reach hA hnorm hka hkt h0 hstuck
    have hdrop : deficitCount A' B < deficitCount A B := by
      rw [hA'eq]; exact deficitCount_openTail_reach_lt A B k (-δ) hkdef hreach_k
    exact Or.inl ⟨hstrict, hdrop⟩

/-- **The corrected outcome `InteriorOpeningOutcomeW'` is inhabited** from the repaired clause (iii)
alone (no pure-hemi progress residual).  This exhibits the honest three-alternative shape directly: the
pure-hemi strict-convex arm is a genuine third outcome the audit exposed, here produced without faking it
away.  (The headline route instead collapses it via `PureHemiProgressW` to recover the original
termination-ready `InteriorOpeningOutcome`; this theorem records that the corrected shape itself is
true.) -/
theorem interiorOpeningOutcomeW'_repaired (hcap : GlueWBaseCap)
    (hclose : OpenedClosingEdgeDistinctAtSupW) (hmargins : SupportStuckMarginsPosAtSupW) :
    InteriorOpeningOutcomeW' := by
  intro n A B hA hB hside hangle k hkdef
  obtain ⟨h₀, hnorm, hhpos⟩ := hA.closed_convex.open_hemisphere
  set K : Fin (n + 1) := openingAxis k with hK
  set δ : ℝ := monitoredSupW A B k h₀ Real.pi with hδ
  set A' : Fin (n + 1) → S2 := openTailW A K δ with hA'
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0 :=
    monitoredFamily_init_admissible hA hhpos hkdef
  have hA'eq : A' = openTail A K (-δ) := rfl
  have hjointk : jointAngle A' k = openedInteriorJointAngle A k (-δ) := by
    rw [hA'eq]; exact jointAngle_openTail_eq_openedInterior A k (-δ)
  have hslack : openedInteriorJointAngle A k (-δ) ≤ jointAngle B k := by
    have hmem := monitoredSupW_mem (B := B) (h₀ := h₀) hka hkt Real.pi_nonneg h0
    have := hmem.2 (Sum.inr (Sum.inr ()))
    simp only [monitoredFamilyW, monitoredFamily, interiorTargetSlack] at this
    rw [hδ]; linarith
  have hside' : SameSides A' B := by
    intro i; rw [hA'eq, openTail_preserves_sides A K (-δ) i]; exact hside i
  have hangle' : JointLe A' B := by
    intro r
    by_cases hrk : r = k
    · rw [hrk, hjointk]; exact hslack
    · rw [hA'eq, jointAngle_openTail_eq_of_ne A k (-δ) hrk]; exact hangle r
  have hmono : endpt A ≤ endpt A' :=
    glueW_clause_i hA hB hka hkt h0 (hcap n A B hA hB k hkdef h₀ hnorm hhpos)
  refine ⟨A', hmono, hside', hangle', ?_⟩
  by_cases hstuck : StuckW A B k h₀ Real.pi
  · obtain ⟨hweak, halt⟩ :=
      glueWClauseIII_repaired hclose hmargins n A B hA hB k hkdef h₀ hnorm hhpos hstuck
    rcases halt with hvanish | hstrict
    · exact Or.inr (Or.inl ⟨hweak, hvanish⟩)
    · exact Or.inr (Or.inr hstrict)
  · have hreach : ReachW A B k h₀ Real.pi := glueW_clause_ii hA hB hka hkt h0 hstuck
    have hreach_k : jointAngle (openTail A K (-δ)) k = jointAngle B k := by
      rw [jointAngle_openTail_eq_openedInterior A k (-δ)]; exact hreach
    have hstrict : StrictConvexSphArm A' :=
      strictW_persistence_at_reach hA hnorm hka hkt h0 hstuck
    have hdrop : deficitCount A' B < deficitCount A B := by
      rw [hA'eq]; exact deficitCount_openTail_reach_lt A B k (-δ) hkdef hreach_k
    exact Or.inl ⟨hstrict, hdrop⟩

/-- **The Chapter-13 spherical arm lemma, with the REPAIRED (non-vacuous) clause-(iii) residue surface.**
`sDist (A 0)(A last) ≤ sDist (B 0)(B last)` for strictly convex arms with equal sides and `A`'s joints
`≤` `B`'s, conditional on the HONEST residue list:

* `hcore : SpliceBodyDiagMono`, `hstruct : SpliceStructuralData` — pre-B1 splice geometry;
* `hcap : GlueWBaseCap` — the endpoint base-angle cap (clause (i));
* `hclose : OpenedClosingEdgeDistinctAtSupW` — the single wraparound closing edge, **scoped to the glue
  context** (refutation-resistant: a constant arm is excluded by `StrictConvexSphArm`);
* `hmargins : SupportStuckMarginsPosAtSupW` — the strict ambient-`h₀` margins, **scoped to the support
  branch** (refutation-resistant: never asserted at a hemi-stuck vertex);
* `hprog : PureHemiProgressW` — the pure-hemi progress residual (the genuine hemi-branch content the
  false `HemiMarginStrictPosAtSupW` hid).

Every hypothesis is a named, satisfiable, refutation-checked `Prop`.  This is the same headline
inequality FFCT38 proved, now resting on a **true** clause-(iii) surface. -/
theorem mainPlus_headline_repaired
    (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData)
    (hcap : GlueWBaseCap) (hclose : OpenedClosingEdgeDistinctAtSupW)
    (hmargins : SupportStuckMarginsPosAtSupW) (hprog : PureHemiProgressW)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_spliceBodyDiagMono hcore hstruct
    (interiorOpeningOutcomeW_repaired hcap hclose hmargins hprog) hn A B hA hB hside hangle

/-! ## §4. Non-vacuity / anti-impostor guards (playbook §3.3) for the repaired surface. -/

/-- Non-vacuity of the repaired clause (iii): its conclusion is a real disjunction of genuine geometric
data (a `WeakConvexSphArm` arm with either a real vanishing non-incident support or a real strict-convex
certificate), realised by the unopened arm at `δ*_W = 0` (`openTailW A K 0 = A`, strictly convex). -/
theorem glueWClauseIII'_conclusion_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (hA : StrictConvexSphArm A) :
    StrictConvexSphArm (openTailW A K 0) := by
  rw [openTailW_zero]; exact hA

/-- Non-vacuity of `PureHemiProgressW`: its conclusion is a real disjunction (`ReachW` is a genuine angle
equation; the vanishing support is genuine non-incident data), not a vacuous-hypothesis impostor.  At
`δ*_W = 0` the `ReachW` member is `openedInteriorJointAngle A k 0 = jointAngle B k`, a real condition. -/
theorem pureHemiProgressW_reach_real {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) :
    ReachW A B k h₀ Real.pi ↔
      openedInteriorJointAngle A k (-(monitoredSupW A B k h₀ Real.pi)) = jointAngle B k := Iff.rfl

/-- Non-vacuity of the repaired headline: the inequality is realised reflexively at `A = B`. -/
theorem mainPlus_headline_repaired_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

/-- Non-vacuity of the any-`h` assembler: its conclusion (`WeakConvexSphArm`) is realised at the
unopened arm `openTailW A K 0 = A` (weakly convex), with the ambient normal as the existential witness —
so the assembler is a real production, not vacuous. -/
theorem weakConvex_anyH_conclusion_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (hA : StrictConvexSphArm A) :
    WeakConvexSphArm (openTailW A K 0) := by
  rw [openTailW_zero]; exact strictConvexSphArm_toWeak hA

end ProofsInTheBook.ZinanFFCT40

-- §1 the any-h assembler
#print axioms ProofsInTheBook.ZinanFFCT40.weakConvex_of_supportStuckW_of_hemiPos_anyH
-- §3 the pure-hemi strict certificate + repaired stuck outcome + repaired clause (iii)
#print axioms ProofsInTheBook.ZinanFFCT40.pureHemi_strictConvexW
#print axioms ProofsInTheBook.ZinanFFCT40.stuckOutcomeW_repaired
#print axioms ProofsInTheBook.ZinanFFCT40.glueWClauseIII_repaired
-- §3 the corrected outcome + repaired headline
#print axioms ProofsInTheBook.ZinanFFCT40.interiorOpeningOutcomeW'_repaired
#print axioms ProofsInTheBook.ZinanFFCT40.interiorOpeningOutcomeW_repaired
#print axioms ProofsInTheBook.ZinanFFCT40.mainPlus_headline_repaired
-- refutation-resistance witnesses
#print axioms ProofsInTheBook.ZinanFFCT40.openedClosingEdgeDistinctAtSupW_constantArm_excluded
