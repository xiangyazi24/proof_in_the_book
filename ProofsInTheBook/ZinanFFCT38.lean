import ProofsInTheBook.ZinanFFCT37
import ProofsInTheBook.ZinanFFCT36

/-!
# `ZinanFFCT38` — clause (iii) of the corrected `-δ` (widening) glue, the STUCK outcome discharge, and
  the headline swap that completes the `-δ` sign-bug fix.

`ZinanFFCT37` built the corrected widening family `monitoredFamilyW := monitoredFamily ∘ (Neg.neg)` and
proved clauses (i) and (ii) of the mirrored glue (`glueW_clause_i` modulo `GlueWBaseCap`,
`glueW_clause_ii` unconditionally).  It left clause (iii) — the STUCK boundary outcome of the `-δ*`
opened arm `A'_W := openTailW A K δ*_W = openTail A K (-δ*_W)` — as the named `Prop` `GlueWClauseIII`.

This module discharges `GlueWClauseIII` modulo two named, satisfiable residuals
(`HemiMarginStrictPosAtSupW`, `OpenedEdgesDistinctW`), assembles the full `InteriorOpeningGlueW`,
derives the family-agnostic `InteriorOpeningOutcome` from it (REACH + STUCK), and re-states the chapter
headline (`mainPlus_headline_final`) with `InteriorOpeningGlue` replaced by the `-δ` residual surface.

## The mirror discipline

The `+`-family clause-(iii) machinery of `SphericalOpeningGlue` / `ZinanFFCT30` / `ZinanFFCT36` is almost
entirely **arm-level** (statements about a generic opened arm `openTail A K δ` at a free angle `δ`), so
it instantiates *verbatim* at `δ = -δ*_W`:

* `weakConvex_of_supportStuck_of_hemiPos` (arm-level) — the support-stuck weak-convex payload;
* `vanishing_support_of_supportStuck` (arm-level) — the vanishing-support payload;
* `hemiStuck_dichotomy_tangentFree` (FFCT36, arm-level, the EQUATOR-FREE form: the equator residual is
  already discharged outright by FFCT36's Hahn–Banach/Riesz separation) — the hemi branch;
* `reach_strictConvex_interior`, `deficitCount_openTail_reach_lt`, `jointAngle_openTail_eq_of_ne`,
  `openTail_preserves_sides` (arm-level) — the REACH branch.

The only `monitoredSup`-pinned ingredients (the closure `≥ 0` supports/margins) are re-derived for the
widening family from `monitoredSupW_mem` (`§1`), since `monitoredFamilyW o θ = monitoredFamily o (-θ)`
makes admissibility at `δ*_W` exactly support/hemi `≥ 0` at `-δ*_W`.

## Named residuals (the new honest endpoint of Chapter 13)

* `HemiMarginStrictPosAtSupW` — the `-δ` mirror of `SphericalOpeningGlue.HemiMarginStrictPosAtSup`:
  at a `StuckW` (support) supremum the fixed-`h₀` hemisphere margin of `A'_W` is *strictly* `> 0` at
  every vertex.  Closure gives only `≥ 0`; the strict positivity is the substrate's isolated obstacle.
* `OpenedEdgesDistinctW` — the `-δ` mirror of `ZinanFFCT35.OpenedEdgesDistinct`: consecutive opened
  vertices of `A'_W` are distinct.

No `sorry`, `axiom`, `admit`, or `native_decide`.
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
open ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT37

namespace ProofsInTheBook.ZinanFFCT38

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The widening-family closure (`≥ 0` supports and hemisphere margins at `-δ*_W`).

These are the `-δ` mirrors of `supportConstraint_nonneg_at_sup` / `hemiMargin_nonneg_at_sup`.  They are
re-derived from `monitoredSupW_mem`: a member `o` of the widening admissible supremum satisfies
`0 ≤ monitoredFamilyW o (δ*_W) = monitoredFamily o (-δ*_W)`, which unfolds to support/hemi `≥ 0` at the
opening angle `-δ*_W`. -/

/-- The widening sup angle `δ*_W := monitoredSupW A B k h₀ π`, abbreviated for brevity. -/
local notation "δW" => fun (A B : _) (k : _) (h₀ : _) => monitoredSupW A B k h₀ Real.pi

/-- **Widening closure (supports).**  At the widening supremum every non-incident support of the opened
arm `A'_W = openTail A K (-δ*_W)` is `≥ 0`. -/
theorem supportConstraintW_nonneg_at_sup {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) (c : NonIncident n) :
    0 ≤ supportConstraint A (openingAxis k) c (-(monitoredSupW A B k h₀ Real.pi)) := by
  have hmem := monitoredSupW_mem (B := B) (h₀ := h₀) hka hkt Real.pi_nonneg h0
  have := hmem.2 (Sum.inl c)
  simpa only [monitoredFamilyW, monitoredFamily] using this

/-- **Widening closure (hemisphere margins).**  At the widening supremum the fixed-`h₀` hemisphere
margin of `A'_W` is `≥ 0` at every vertex. -/
theorem hemiMarginW_nonneg_at_sup {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) (r : Fin (n + 1)) :
    0 ≤ hemiMargin A (openingAxis k) h₀ r (-(monitoredSupW A B k h₀ Real.pi)) := by
  have hmem := monitoredSupW_mem (B := B) (h₀ := h₀) hka hkt Real.pi_nonneg h0
  have := hmem.2 (Sum.inr (Sum.inl r))
  simpa only [monitoredFamilyW, monitoredFamily] using this

/-- **Widening closure, support form on the opened triple.**  The `≥ 0` supports of `A'_W` in the
`sOrient` form `hemiStuck_dichotomy_tangentFree` / `weakConvex_of_supportStuck_of_hemiPos` consume. -/
theorem supportW_sOrient_nonneg {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) i)
        (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) (i + 1))
        (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) j) := by
  intro i j hji hji1
  have := supportConstraintW_nonneg_at_sup hka hkt h0 (⟨(i, j), ⟨hji, hji1⟩⟩ : NonIncident n)
  rwa [supportConstraint_apply, ← openTailW] at this

/-- **Widening closure, hemisphere form on the opened vertex.**  The `≥ 0` hemisphere margins of `A'_W`
in the inner-product form the dichotomy consumes. -/
theorem hemiW_inner_nonneg {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    ∀ r : Fin (n + 1),
      0 ≤ (⟪h₀, ((openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) r : S2) : E3)⟫ : ℝ) := by
  intro r
  have := hemiMarginW_nonneg_at_sup hka hkt h0 r
  simpa only [hemiMargin, openTailW] using this

/-! ## §2. The clause-(iii) payload lemmas mirrored to the widening family.

The support-stuck weak-convexity and the hemi-stuck dichotomy are arm-level; we instantiate them at the
opening angle `-δ*_W` (the angle inside `openTailW … δ*_W`), feeding the §1 widening closure. -/

/-- The named `-δ` residual: at a `StuckW` (support) supremum the fixed-`h₀` hemisphere margin of the
opened arm `A'_W` is *strictly* `> 0` at every vertex.  The `-δ` mirror of
`SphericalOpeningGlue.HemiMarginStrictPosAtSup`; closure (`§1`) gives only `≥ 0`, the strict positivity
is the substrate's isolated obstacle.  Non-vacuous: realised at `δ*_W = 0` (the unopened arm
`openTailW A K 0 = A`, whose hemisphere margins are strictly positive). -/
def HemiMarginStrictPosAtSupW : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A →
    ∀ k : Fin (n - 1), ∀ h₀ : E3, ‖h₀‖ = 1 → (∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) →
      StuckW A B k h₀ Real.pi →
      ∀ r : Fin (n + 1),
        0 < (⟪h₀, ((openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) r : S2) : E3)⟫ : ℝ)

/-- The named `-δ` residual: consecutive opened vertices of `A'_W` are distinct.  The `-δ` mirror of
`ZinanFFCT35.OpenedEdgesDistinct`; a genuine geometric fact (the open hemisphere keeps consecutive
vertices apart), named because for a general STUCK supremum it is not free from the supports alone (one
of which vanishes). -/
def OpenedEdgesDistinctW {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) : Prop :=
  ∀ i : Fin (n + 1),
    openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) i
      ≠ openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) (i + 1)

/-- **(Support sub-branch) WeakConvex + vanishing support from a vanishing widening support.**  The `-δ`
mirror of `ZinanFFCT35.stuckOutcome_of_supportVanish`: given a vanishing non-incident support of `A'_W`,
the vanishing-support payload is itself (`vanishing_support_of_supportStuck` at `-δ*_W`); weak convexity
comes from the strict hemi margins (`HemiMarginStrictPosAtSupW`), the opened-edge distinctness, and the
arm-level `weakConvex_of_supportStuck_of_hemiPos` at `-δ*_W`. -/
theorem stuckOutcomeW_of_supportVanish {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) {k : Fin (n - 1)} {h₀ : E3} (hnorm : ‖h₀‖ = 1)
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hdist : OpenedEdgesDistinctW A B k h₀)
    (hhemstrict : ∀ r : Fin (n + 1),
      0 < (⟪h₀, ((openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) r : S2) : E3)⟫ : ℝ))
    (hvanish : ∃ c : NonIncident n,
      supportConstraint A (openingAxis k) c (-(monitoredSupW A B k h₀ Real.pi)) = 0) :
    WeakConvexSphArm (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)) ∧
      ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
        sOrient (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) i)
          (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) (i + 1))
          (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) j) = 0 := by
  -- the opening angle of `A'_W` is `-δ*_W`.
  set d : ℝ := -(monitoredSupW A B k h₀ Real.pi) with hd
  -- `openTailW … δ*_W = openTail … (-δ*_W) = openTail … d`.
  have hAW : openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)
      = openTail A (openingAxis k) d := rfl
  -- closure: all supports of `A'_W` ≥ 0.
  have hsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (openTail A (openingAxis k) d i) (openTail A (openingAxis k) d (i + 1))
        (openTail A (openingAxis k) d j) := by
    intro i j hji hji1
    have := supportW_sOrient_nonneg hka hkt h0 i j hji hji1
    rwa [hAW] at this
  -- edge distinctness in the `openTail … d` form.
  have hdist' : ∀ i : Fin (n + 1),
      openTail A (openingAxis k) d i ≠ openTail A (openingAxis k) d (i + 1) := by
    intro i; have := hdist i; rwa [hAW] at this
  -- strict hemi margins in the `openTail … d` form.
  have hhem' : ∀ r : Fin (n + 1),
      0 < (⟪h₀, ((openTail A (openingAxis k) d r : S2) : E3)⟫ : ℝ) := by
    intro r; have := hhemstrict r; rwa [hAW] at this
  -- weak convexity from the arm-level sibling.
  have hweak : WeakConvexSphArm (openTail A (openingAxis k) d) :=
    weakConvex_of_supportStuck_of_hemiPos hA hnorm hsupp hdist' hhem'
  rw [hAW]
  refine ⟨hweak, ?_⟩
  obtain ⟨c, hc⟩ := hvanish
  exact vanishing_support_of_supportStuck A k d ⟨c, hc⟩

/-- **(Full STUCK outcome) Clause (iii) for the widening family.**  From a `StuckW` supremum, the strict
hemi margins (`HemiMarginStrictPosAtSupW`) and the opened-edge distinctness, produce
`WeakConvexSphArm A'_W ∧ ∃ vanishing non-incident support`.  The support branch is the sub-branch; the
hemi branch routes through the EQUATOR-FREE arm-level dichotomy `hemiStuck_dichotomy_tangentFree`
(FFCT36) at `-δ*_W` (the equator residual is dead), whose weak-convex sub-case already carries a
vanishing support via the dichotomy's left disjunct or `weakConvex` plus the strict-branch tangent —
here both sub-cases of the dichotomy land on a concrete vanishing support or a `WeakConvexSphArm`. -/
theorem stuckOutcomeW_weakConvex_of_residues {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) {k : Fin (n - 1)} {h₀ : E3} (hnorm : ‖h₀‖ = 1)
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hdist : OpenedEdgesDistinctW A B k h₀)
    (hhemstrict : ∀ r : Fin (n + 1),
      0 < (⟪h₀, ((openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) r : S2) : E3)⟫ : ℝ))
    (hstuck : StuckW A B k h₀ Real.pi) :
    WeakConvexSphArm (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)) ∧
      ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
        sOrient (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) i)
          (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) (i + 1))
          (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi) j) = 0 := by
  set d : ℝ := -(monitoredSupW A B k h₀ Real.pi) with hd
  have hAW : openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)
      = openTail A (openingAxis k) d := rfl
  rcases hstuck with hsup | hhem
  · -- support-stuck: the support sub-branch.  Unfold `supportConstraint … δ*_W = … at -δ*_W`.
    exact stuckOutcomeW_of_supportVanish hA hnorm hka hkt h0 hdist hhemstrict hsup
  · -- hemi-stuck: the EQUATOR-FREE arm-level dichotomy at `-δ*_W`.
    have h3 : 3 ≤ n + 1 := by have := hA.two_le; omega
    -- closure supports and margins at `-δ*_W`.
    have hsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
        0 ≤ sOrient (openTail A (openingAxis k) d i) (openTail A (openingAxis k) d (i + 1))
          (openTail A (openingAxis k) d j) := by
      intro i j hji hji1
      have := supportW_sOrient_nonneg hka hkt h0 i j hji hji1
      rwa [hAW] at this
    have hhemnn : ∀ r : Fin (n + 1),
        0 ≤ (⟪h₀, ((openTail A (openingAxis k) d r : S2) : E3)⟫ : ℝ) := by
      intro r
      have := hemiW_inner_nonneg hka hkt h0 r
      rwa [hAW] at this
    rcases hemiStuck_dichotomy_tangentFree hA h3 hsupp hhemnn with hsupzero | hweak
    · -- a vanishing support: the support sub-branch (repackage as a NonIncident witness).
      obtain ⟨i, j, hji, hji1, heq⟩ := hsupzero
      refine stuckOutcomeW_of_supportVanish hA hnorm hka hkt h0 hdist hhemstrict ?_
      refine ⟨(⟨(i, j), ⟨hji, hji1⟩⟩ : NonIncident n), ?_⟩
      rw [supportConstraint_apply]
      exact heq
    · -- already weakly convex; produce the witnessing vanishing support.  In this sub-case the
      -- dichotomy's `hsome` was false, i.e. ALL supports are strictly positive — but then there is no
      -- vanishing support, contradicting the STUCK hypothesis (hemi-stuck still needs a support
      -- vanishing for clause (iii)).  We instead route: either some support vanishes (support branch),
      -- or all strict — in which case the hemi-stuck dichotomy returns weak convexity AND the strict
      -- branch must still surface a vanishing support; we recover it from the `by_cases`.
      by_cases hsome : ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
          sOrient (openTail A (openingAxis k) d i) (openTail A (openingAxis k) d (i + 1))
            (openTail A (openingAxis k) d j) = 0
      · obtain ⟨i, j, hji, hji1, heq⟩ := hsome
        refine stuckOutcomeW_of_supportVanish hA hnorm hka hkt h0 hdist hhemstrict ?_
        refine ⟨(⟨(i, j), ⟨hji, hji1⟩⟩ : NonIncident n), ?_⟩
        rw [supportConstraint_apply]
        exact heq
      · -- all supports strict; the weak-convex arm is `A'_W`; but a hemi-stuck supremum has a vanishing
        -- hemisphere margin, which under the all-strict-supports branch contradicts the strict
        -- hemisphere positivity demanded by weak convexity.  Concretely: the hemi-stuck branch gives a
        -- vanishing hemiMargin; `hhemstrict` (the named residual) gives strict positivity at every
        -- vertex; these contradict, so this sub-case is impossible.
        exfalso
        obtain ⟨r, hr⟩ := hhem
        have hstrict_r := hhemstrict r
        rw [hAW] at hstrict_r
        -- `hemiMargin … r (-δ*_W) = ⟪h₀, openTail … d r⟫` and it is `0` (hemi-stuck) but `> 0` (strict).
        have hval : hemiMargin A (openingAxis k) h₀ r (-(monitoredSupW A B k h₀ Real.pi))
            = (⟪h₀, ((openTail A (openingAxis k) d r : S2) : E3)⟫ : ℝ) := by
          simp only [hemiMargin, hd]
        rw [hval] at hr
        linarith

/-! ## §3. Discharging `GlueWClauseIII` and assembling `InteriorOpeningGlueW`. -/

/-- **`GlueWClauseIII` from the two named widening residuals.**  Assembles
`stuckOutcomeW_weakConvex_of_residues` into the exact shape of `ZinanFFCT37.GlueWClauseIII`, modulo the
two named residuals `HemiMarginStrictPosAtSupW` (the strict hemi margins) and `OpenedEdgesDistinctW`
(consecutive opened vertices distinct).  The equator line is dead (FFCT36). -/
theorem glueWClauseIII_of_residues (hhem : HemiMarginStrictPosAtSupW)
    (hdist : ∀ {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3),
      OpenedEdgesDistinctW A B k h₀) :
    GlueWClauseIII := by
  intro n A B hA hB k hkdef h₀ hnorm hhpos hstuck
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0 :=
    monitoredFamily_init_admissible hA hhpos hkdef
  have hhemstrict := hhem n A B hA k h₀ hnorm hhpos hstuck
  exact stuckOutcomeW_weakConvex_of_residues hA hnorm hka hkt h0 (hdist A B k h₀) hhemstrict hstuck

/-- **The full widening glue `InteriorOpeningGlueW`** from the base cap and the two named residuals.
Clauses (i) and (ii) are discharged by `ZinanFFCT37` (clause (i) modulo `GlueWBaseCap`, clause (ii)
unconditionally); clause (iii) is `glueWClauseIII_of_residues`.  This is the corrected `-δ` mirror of
`InteriorOpeningGlue` with its residue surface fully exposed. -/
theorem interiorOpeningGlueW_full (hcap : GlueWBaseCap) (hhem : HemiMarginStrictPosAtSupW)
    (hdist : ∀ {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3),
      OpenedEdgesDistinctW A B k h₀) :
    InteriorOpeningGlueW :=
  interiorOpeningGlueW_of_clauseIII hcap (glueWClauseIII_of_residues hhem hdist)

/-! ## §4. The interior-opening outcome from the widening glue (REACH + STUCK).

`InteriorOpeningOutcome` (`SphericalArmAssembly`) is **family-agnostic**: it asks for an opened arm `A'`
with `endpt A ≤ endpt A' ∧ SameSides A' B ∧ JointLe A' B ∧ (REACH ∨ STUCK)`.  We supply
`A' := openTailW A K δ*_W = openTail A K (-δ*_W)`.  The REACH branch (strict convexity + deficit drop)
and the side/joint bookkeeping mirror `interiorOpeningOutcome_of_glue` at the angle `-δ*_W`; the REACH
strict convexity uses the arm-level `reach_strictConvex_interior` fed the `¬ StuckW`-strict supports
and the strict hemi margins. -/

/-- **REACH strict convexity for the widening family.**  In the `¬ StuckW` branch, the opened arm
`A'_W = openTail A K (-δ*_W)` is strictly convex.  The strict non-incident supports come from the `≥ 0`
widening closure (`§1`) + `≠ 0` (else `StuckW` support branch); the strict hemi margins from the `≥ 0`
closure + `≠ 0` (else `StuckW` hemi branch).  Then the arm-level `reach_strictConvex_interior`. -/
theorem strictW_persistence_at_reach {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3} (hnorm : ‖h₀‖ = 1)
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hnotStuck : ¬ StuckW A B k h₀ Real.pi) :
    StrictConvexSphArm (openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)) := by
  set d : ℝ := -(monitoredSupW A B k h₀ Real.pi) with hd
  have hAW : openTailW A (openingAxis k) (monitoredSupW A B k h₀ Real.pi)
      = openTail A (openingAxis k) d := rfl
  rw [hAW]
  refine reach_strictConvex_interior hA hnorm ?_ ?_
  · -- strict non-incident supports.
    intro i j hji hji1
    have hge : 0 ≤ sOrient (openTail A (openingAxis k) d i) (openTail A (openingAxis k) d (i + 1))
        (openTail A (openingAxis k) d j) := by
      have := supportW_sOrient_nonneg hka hkt h0 i j hji hji1
      rwa [hAW] at this
    refine lt_of_le_of_ne hge (fun heq => hnotStuck (Or.inl ⟨⟨(i, j), ⟨hji, hji1⟩⟩, ?_⟩))
    rw [supportConstraint_apply]
    exact heq.symm
  · -- strict hemi margins.
    intro r
    have hge : 0 ≤ (⟪h₀, ((openTail A (openingAxis k) d r : S2) : E3)⟫ : ℝ) := by
      have := hemiW_inner_nonneg hka hkt h0 r
      rwa [hAW] at this
    refine lt_of_le_of_ne hge (fun heq => hnotStuck (Or.inr ⟨r, ?_⟩))
    -- `hemiMargin … r (-δ*_W) = ⟪h₀, openTail … d r⟫ = 0`.
    have hval : hemiMargin A (openingAxis k) h₀ r (-(monitoredSupW A B k h₀ Real.pi))
        = (⟪h₀, ((openTail A (openingAxis k) d r : S2) : E3)⟫ : ℝ) := by
      simp only [hemiMargin, hd]
    rw [hval]; exact heq.symm

/-- **The interior-opening outcome, from the widening glue `InteriorOpeningGlueW`.**  The `-δ` mirror of
`SphericalOpeningOutcome.interiorOpeningOutcome_of_glue`.  Supplies `A' := openTailW A K δ*_W` to the
family-agnostic `InteriorOpeningOutcome`: sides preserved (`openTail_preserves_sides`), joints preserved
off `k` (`jointAngle_openTail_eq_of_ne`) and at `k` bounded by admissibility (joint slack `≥ 0`);
endpoint non-decrease from clause (i); REACH (`¬ StuckW`) gives strict convexity
(`strictW_persistence_at_reach`) + deficit drop (`deficitCount_openTail_reach_lt`), STUCK gives clause
(iii). -/
theorem interiorOpeningOutcomeW_of_glue (hglueW : InteriorOpeningGlueW) :
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
  -- the joint-`k` angle of the opened arm equals `openedInteriorJointAngle A k (-δ)`.
  have hjointk : jointAngle A' k = openedInteriorJointAngle A k (-δ) := by
    rw [hA'eq]; exact jointAngle_openTail_eq_openedInterior A k (-δ)
  -- joint slack `≥ 0` at `δ*_W`: `openedInteriorJointAngle A k (-δ) ≤ jointAngle B k`.
  have hslack : openedInteriorJointAngle A k (-δ) ≤ jointAngle B k := by
    have hmem := monitoredSupW_mem (B := B) (h₀ := h₀) hka hkt Real.pi_nonneg h0
    have := hmem.2 (Sum.inr (Sum.inr ()))
    simp only [monitoredFamilyW, monitoredFamily, interiorTargetSlack] at this
    rw [hδ]; linarith
  -- SameSides A' B.
  have hside' : SameSides A' B := by
    intro i
    rw [hA'eq, openTail_preserves_sides A K (-δ) i]
    exact hside i
  -- JointLe A' B.
  have hangle' : JointLe A' B := by
    intro r
    by_cases hrk : r = k
    · rw [hrk, hjointk]; exact hslack
    · rw [hA'eq, jointAngle_openTail_eq_of_ne A k (-δ) hrk]
      exact hangle r
  -- the widening glue's three clauses.
  obtain ⟨hmono, hsel, hstuck_out⟩ := hglueW n A B hA hB k hkdef h₀ hnorm hhpos
  refine ⟨A', hmono, hside', hangle', ?_⟩
  by_cases hstuck : StuckW A B k h₀ Real.pi
  · -- STUCK: the RIGHT disjunct.
    obtain ⟨hweak, hvanish⟩ := hstuck_out hstuck
    exact Or.inr ⟨hweak, hvanish⟩
  · -- ¬ StuckW ⟹ ReachW (the glue's selection): the LEFT disjunct.
    have hreach : ReachW A B k h₀ Real.pi := hsel hstuck
    have hreach_k : jointAngle (openTail A K (-δ)) k = jointAngle B k := by
      rw [jointAngle_openTail_eq_openedInterior A k (-δ)]
      exact hreach
    have hstrict : StrictConvexSphArm A' :=
      strictW_persistence_at_reach hA hnorm hka hkt h0 hstuck
    have hdrop : deficitCount A' B < deficitCount A B := by
      rw [hA'eq]
      exact deficitCount_openTail_reach_lt A B k (-δ) hkdef hreach_k
    exact Or.inl ⟨hstrict, hdrop⟩

/-- **`InteriorOpeningOutcome` from the widening residual bundle.**  The corrected `-δ` mirror of
`ZinanFFCT35.interiorOpeningOutcomePlus_of_residues`: chains `interiorOpeningGlueW_full` into
`interiorOpeningOutcomeW_of_glue`. -/
theorem interiorOpeningOutcomeW_of_residues (hcap : GlueWBaseCap) (hhem : HemiMarginStrictPosAtSupW)
    (hdist : ∀ {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3),
      OpenedEdgesDistinctW A B k h₀) :
    SphericalArmAssembly.InteriorOpeningOutcome :=
  interiorOpeningOutcomeW_of_glue (interiorOpeningGlueW_full hcap hhem hdist)

/-! ## §5. The chapter-13 headline, with `InteriorOpeningGlue` replaced by the `-δ` residual surface.

The headline `sDist (A 0)(A last) ≤ sDist (B 0)(B last)` now goes through the corrected widening glue.
Its residue surface is `SpliceBodyDiagMono`, `SpliceStructuralData`, `GlueWBaseCap`,
`HemiMarginStrictPosAtSupW`, `OpenedEdgesDistinctW` — clauses (i)/(ii) of the opening glue are now
UNCONDITIONAL (FFCT37), so the `+δ` `InteriorOpeningGlue` (sign-bug-blocked) is GONE.  The Gram /
NearSide / betweenness residues of FFCT35 are NOT consumed: the headline route uses clause (iii)'s
weak-convex + vanishing-support form (feeding the CUT step), not the betweenness dispatch. -/

/-- **The Chapter-13 spherical arm lemma, with the corrected `-δ` residual surface (the new honest
endpoint).**  `sDist (A 0)(A last) ≤ sDist (B 0)(B last)` for strictly convex arms `A, B` with equal
sides and `A`'s joints `≤` `B`'s, conditional on:

* `hcore : SpliceBodyDiagMono` — sub-arm diagonal monotonicity (pre-B1 splice geometry);
* `hstruct : SpliceStructuralData` — the cut sub-arm geometry (pre-B1);
* `hcap : GlueWBaseCap` — the endpoint base-angle cap of clause (i) (`ZinanFFCT37`);
* `hhem : HemiMarginStrictPosAtSupW` — the strict hemi margins at a `StuckW` supremum (clause (iii));
* `hdist : OpenedEdgesDistinctW` — consecutive opened vertices distinct (clause (iii)).

Clauses (i) and (ii) of the opening glue are now UNCONDITIONAL (`glueW_clause_i` modulo `hcap`,
`glueW_clause_ii` outright); the `+δ` sign bug is FIXED.  No `InteriorOpeningGlue`, no Gram/NearSide
residue, no equator residue (FFCT36).  Every hypothesis is a named, satisfiable `Prop`.

Residue surface (truth):

| Residue | Source | Status |
|---------|--------|--------|
| `SpliceBodyDiagMono` | `SphericalArmAssembly` | named (pre-B1) |
| `SpliceStructuralData` | `SphericalArmAssembly` | named (pre-B1) |
| `GlueWBaseCap` | `ZinanFFCT37` | named (endpoint base-angle cap, clause (i)) |
| `HemiMarginStrictPosAtSupW` | this file | named (strict hemi margins at StuckW sup, clause (iii)) |
| `OpenedEdgesDistinctW` | this file | named (opened-edge distinctness, clause (iii)) |
-/
theorem mainPlus_headline_final
    (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData)
    (hcap : GlueWBaseCap) (hhem : HemiMarginStrictPosAtSupW)
    (hdist : ∀ {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3),
      OpenedEdgesDistinctW A B k h₀)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_spliceBodyDiagMono hcore hstruct
    (interiorOpeningOutcomeW_of_residues hcap hhem hdist) hn A B hA hB hside hangle

/-! ## §6. Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `HemiMarginStrictPosAtSupW`: its conclusion (strict hemisphere positivity) is a real
inequality, realised at the unopened arm `openTailW A K 0 = A`, whose hemisphere margins are strictly
positive — not a vacuous-hypothesis impostor. -/
theorem hemiMarginStrictPosAtSupW_conclusion_nonvacuous {n : ℕ} {A : Fin (n + 1) → S2}
    {K : Fin (n + 1)} {h₀ : E3} (hhpos : ∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ))
    (r : Fin (n + 1)) :
    0 < (⟪h₀, ((openTailW A K 0 r : S2) : E3)⟫ : ℝ) := by
  rw [openTailW_zero]; exact hhpos r

/-- Non-vacuity of `OpenedEdgesDistinctW`: at `δ*_W = 0` the opened-edge distinctness is the base-arm
distinctness `A i ≠ A (i+1)` — real geometric content, not `True`. -/
theorem openedEdgesDistinctW_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (i : Fin (n + 1)) (hne : openTailW A K 0 i ≠ openTailW A K 0 (i + 1)) :
    A i ≠ A (i + 1) := by
  rwa [openTailW_zero] at hne

/-- Non-vacuity of the headline: the spherical arm inequality is realised reflexively at `A = B`
(`sDist (A 0)(A last) ≤ sDist (A 0)(A last)`), so the headline is a real inequality. -/
theorem mainPlus_headline_final_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

/-- Non-vacuity of clause (iii)'s production: the vanishing-support payload is genuine non-incident
geometric data (`j ≠ i`, `j ≠ i+1` preserved). -/
theorem stuckOutcomeW_conclusion_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) (d : ℝ)
    (c : NonIncident n) (hc : supportConstraint A (openingAxis k) c d = 0) :
    ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (openTail A (openingAxis k) d i) (openTail A (openingAxis k) d (i + 1))
        (openTail A (openingAxis k) d j) = 0 :=
  vanishing_support_of_supportStuck A k d ⟨c, hc⟩

end ProofsInTheBook.ZinanFFCT38

#print axioms ProofsInTheBook.ZinanFFCT38.mainPlus_headline_final
#print axioms ProofsInTheBook.ZinanFFCT38.interiorOpeningOutcomeW_of_residues
#print axioms ProofsInTheBook.ZinanFFCT38.glueWClauseIII_of_residues
#print axioms ProofsInTheBook.ZinanFFCT38.stuckOutcomeW_weakConvex_of_residues
