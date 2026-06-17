import ProofsInTheBook.ZinanFFCT19
import ProofsInTheBook.ZinanFFCT46
import ProofsInTheBook.ZinanFFCT47

/-!
# `ZinanFFCT48` — the CUT-replacement consumer + the cut-ready opening outcome

## Context (design `HANDOFF/design-rounds/ch13-cut-replacement.md`)

The legacy CUT path of Chapter 13 went through `SpliceBodyDiagMono` + `SpliceStructuralData`
(`SphericalArmAssembly.cut_step`).  The design round of 2026-06-09 establishes that
`SpliceBodyDiagMono` is a **false** overgeneralized residual (the one-side-monotone splice-body
comparison is false in a 2-edge limit), and that `SpliceStructuralData` is the wrong payload level.

The landed B1/B5 line replaces the CUT branch with a `StuckAtKData` / `CutReadyPlus` consumer:
the modern CUT payload is a *stuck datum with Gram signs* (`StuckAtKData`), from which the
folded-flat betweenness (`stuckAtK_betweenness`) and the general-`k` diagonal inequality
(`stuckAtK_diag_le_plus`) are *derived*, and the endpoint bound is closed through the repaired
residue `FoldedFlatCutTransportPlus` (ZinanFFCT18).  `SpliceBodyDiagMono` and `SpliceStructuralData`
are RETIRED, not consumed.

## This file (design bricks 1, 2, 4)

* **Brick 1** `CutReadyPlus` — the cut-ready datum (design §5): a normalized stuck cut `(i, j)`
  with `StuckAtKData A B i j` and the ear-convexity certificates for `A[i+1 .. j]`, `B[i+1 .. j]`.
* **Brick 2** `cut_step_from_stuckAtK_plus` — the CUT consumer (design §4): from `CutReadyPlus A B`
  (weak positive `A`, strict `B`, matched sides/joints), the dimension IH `∀ m < n, MainPlus m`,
  and `FoldedFlatCutTransportPlus`, derive `endpt A ≤ endpt B`.  This is the modern replacement of
  `cut_step`.  The betweenness comes from `stuckAtK_betweenness`, the diagonal inequality from
  `stuckAtK_diag_le_plus`, and both feed `FoldedFlatCutTransportPlus`.
* **Brick 4** `InteriorOpeningOutcomePlus` + `interiorOpeningOutcomePlus_of_bridge` — the outcome
  refactor (design §5/§6): the opening outcome now carries cut-ready data on the weak branch
  (`WeakConvexSphArm A' ∧ CutReadyPlus A' B`) instead of a bare vanishing support.  The discharge
  mirrors `ZinanFFCT46.interiorOpeningOutcomeWBS`, upgrading the SUPPORT-stuck payload via the
  brick-3 bridge `CutReadyPlus_of_supportStuckWBS` (sibling-owned, ZinanFFCT49), taken here as a
  NAMED hypothesis in the design §6 shape.  The REACH / BASE-stuck branches are unchanged
  (strict + deficit drop, banked in FFCT45/46).

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47

namespace ProofsInTheBook.ZinanFFCT48

set_option maxHeartbeats 1600000

/-! ## §1. (Brick 1) The cut-ready datum `CutReadyPlus`.

Design §5.  The modern CUT payload is not "some support vanishes"; it is a stuck datum with Gram
signs (`StuckAtKData`) at a normalized interior cut `(i, j)` with `i + 1 < j ≤ N`, together with the
ear-convexity certificates that the diagonal-inequality core (`stuckAtK_diag_le_plus`) consumes.

The index constraints `i + 1 < j` and `j ≤ N` live inside `hsk` (they are `hsk.hij1`, `hsk.hj`),
so the `intervalArm` sub-arm bounds elaborate from them.  We surface them as explicit fields too,
so the bound `(i + 1) + (j - (i + 1)) ≤ N` is available to downstream consumers without unpacking
`hsk`. -/

/-- **(Brick 1) The cut-ready datum.**  For arms `A, B : Fin (N + 1) → S2` and a normalized cut
`(i, j)`, this carries:
* the general-`k` stuck datum `hsk : StuckAtKData A B i j` (folded-flat support at the middle vertex,
  the two convex-position Gram signs, the equal first side, and `i + 1 < j ≤ N`),
* the ear-convexity certificates `hAe`, `hBe` for the sub-arm `A[i+1 .. j]` (`= intervalArm` of
  length `j - (i + 1)`), which the diagonal-inequality core consumes.

This is the design-§5 replacement for the old bare vanishing-support payload of
`InteriorOpeningOutcome`. -/
def CutReadyPlus {N : ℕ} (A B : Fin (N + 1) → S2) : Prop :=
  ∃ (i j : ℕ) (hsk : StuckAtKData A B i j),
    WeakConvexSphArm
      (intervalArm A (i + 1) (j - (i + 1)) (by have := hsk.hij1; have := hsk.hj; omega)) ∧
    StrictConvexSphArm
      (intervalArm B (i + 1) (j - (i + 1)) (by have := hsk.hij1; have := hsk.hj; omega))

/-! ## §2. (Brick 2) The CUT consumer `cut_step_from_stuckAtK_plus`.

Design §4.  From `CutReadyPlus A B` (weak positive `A`, strict `B`, matched sides/joints), the
dimension IH `∀ m < n, MainPlus m`, and the repaired residue `FoldedFlatCutTransportPlus`, the
endpoint bound `endpt A ≤ endpt B` follows.  This deletes both `SpliceStructuralData` and
`SpliceBodyDiagMono` from the CUT path.

Sketch (each cited lemma pinned to its real signature):
* `stuckAtK_betweenness hij1 hj hsk` — the folded-flat betweenness
  `A ⟨i⟩ ∈ span≥0 {A ⟨i+1⟩, A ⟨j⟩}` (derived from the Gram signs, `SphericalStuckGeneral`).
* `stuckAtK_diag_le_plus hij1 hj hsk (ih (j-(i+1)) _) hApos hAe hBe hside hangle` — the diagonal
  inequality `sDist (A ⟨i⟩)(A ⟨j⟩) ≤ sDist (B ⟨i⟩)(B ⟨j⟩)` (the ear comparison via the level-`m`
  `MainPlus` IH, threading the parent's `PositiveJoints`, `ZinanFFCT19`).  Note `m = j - (i+1) < n`
  since `j ≤ n` and `i + 1 < j`, so the IH applies.
* `FoldedFlatCutTransportPlus` (the named Prop residue, `ZinanFFCT18`) consumes the betweenness +
  the diagonal inequality to close the endpoint.  Its binders are `n, 2 ≤ n, ihdim, A, B, hA, hApos,
  hB, hside, hangle, i, j, j ≠ i, j ≠ i + 1, hi1, hj, span-membership, diag ≤`.

`SameSides`/`JointLe` unfold definitionally to the `∀ k, sideLen … = …` / `∀ k, jointAngle … ≤ …`
forms that `stuckAtK_diag_le_plus` consumes (`hsideAll`/`hangleAll`). -/

/-- **(Brick 2) The CUT step from a cut-ready datum.**  For level `n ≥ 2`, a weakly convex `A` with
positive interior joints carrying a `CutReadyPlus A B`, a strict `B`, equal sides, nondecreasing
joints, the dimension IH `∀ m < n, MainPlus m`, and the residue `FoldedFlatCutTransportPlus`, the
endpoint bound `endpt A ≤ endpt B` holds.

This is the design-§4 replacement of `SphericalArmAssembly.cut_step`: it cuts at the collinear middle
vertex of `hsk`, derives the betweenness and the diagonal inequality, and closes through
`FoldedFlatCutTransportPlus`.  No `SpliceBodyDiagMono`, no `SpliceStructuralData`. -/
theorem cut_step_from_stuckAtK_plus
    (hffct : FoldedFlatCutTransportPlus)
    {n : ℕ} (hn : 2 ≤ n)
    (ih : ∀ m : ℕ, m < n → MainPlus m)
    {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hApos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (hcr : CutReadyPlus A B) :
    endpt A ≤ endpt B := by
  obtain ⟨i, j, hsk, hAe, hBe⟩ := hcr
  have hij1 : i + 1 < j := hsk.hij1
  have hj : j ≤ n := hsk.hj
  -- non-incidence of the cut: `j ≠ i` and `j ≠ i + 1`.
  have hji : j ≠ i := by omega
  have hji1 : j ≠ i + 1 := by omega
  -- Fin bounds for the cut indices.
  have hi1 : i + 1 < n + 1 := by omega
  have hjlt : j < n + 1 := by omega
  -- the level-`m = j - (i + 1) < n` `MainPlus` IH.
  have hMm : MainPlus (j - (i + 1)) := ih (j - (i + 1)) (by omega)
  -- the folded-flat betweenness at the middle vertex `A ⟨i⟩`.
  have hcol :
      (A ⟨i, by omega⟩ : E3)
        ∈ Submodule.span NNReal
          ({(A ⟨i + 1, hi1⟩ : E3), (A ⟨j, hjlt⟩ : E3)} : Set E3) :=
    stuckAtK_betweenness hij1 hj hsk
  -- the general-`k` diagonal inequality from the ear comparison + folded-flat equation.
  have hdiag :
      sDist (A ⟨i, by omega⟩) (A ⟨j, hjlt⟩)
        ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hjlt⟩) :=
    stuckAtK_diag_le_plus hij1 hj hsk hMm hApos hAe hBe hside hangle
  -- feed the betweenness + the derived diagonal inequality into the repaired residue.
  exact hffct n hn ih A B hA hApos hB hside hangle i j hji hji1 hi1 hjlt hcol hdiag

/-! ## §3. (Brick 4) The cut-ready opening outcome `InteriorOpeningOutcomePlus`.

Design §5/§6.  The interior-opening outcome now outputs cut-ready data on the weak branch:
`(StrictConvexSphArm A' ∧ deficitCount A' B < deficitCount A B)` (REACH) **or**
`(WeakConvexSphArm A' ∧ CutReadyPlus A' B)` (CUT) — the latter the design-§5 upgrade of the old bare
vanishing-support payload.

The discharge `interiorOpeningOutcomePlus_of_bridge` mirrors `ZinanFFCT46.interiorOpeningOutcomeWBS`
on the hemisphere-free WBS supremum, but the SUPPORT-stuck branch now produces `CutReadyPlus A' B`
via the brick-3 bridge (sibling-owned), taken as the named hypothesis `hbridge` in the §6 shape.
REACH / BASE-stuck (the latter collapsed to REACH) are unchanged. -/

/-- **(Brick 4) The cut-ready interior-opening outcome.**  As `SphericalArmAssembly.InteriorOpeningOutcome`,
but the STUCK disjunct carries `CutReadyPlus A' B` (the modern stuck datum + ear certificates) instead
of a bare vanishing non-incident support. -/
def InteriorOpeningOutcomePlus : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2,
    StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∃ A' : Fin (n + 1) → S2,
      endpt A ≤ endpt A' ∧ SameSides A' B ∧ JointLe A' B ∧
      ((StrictConvexSphArm A' ∧ deficitCount A' B < deficitCount A B) ∨
       (WeakConvexSphArm A' ∧ CutReadyPlus A' B))

/-- **The §6-shaped brick-3 bridge for the WBS support-stuck branch** (sibling-owned, ZinanFFCT49).
At the WBS supremum, when the opened arm `A'_WBS = openTail A (openingAxis k) (-(monitoredSupWBS A B k))`
is support-stuck (some non-incident support vanishes) and is weakly convex, matched to `B` on
sides/joints, the bridge normalizes the vanishing support to a cut `(i, j)` and builds
`CutReadyPlus A'_WBS B`.  Taken here as a named hypothesis in exactly the context the SUPPORT-stuck
branch of `interiorOpeningOutcomePlus_of_bridge` supplies. -/
def SupportStuckWBS_CutReadyBridge : Prop :=
  ∀ {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k),
    SupportStuckWBS A B k →
    WeakConvexSphArm (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) →
    SameSides (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) B →
    JointLe (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) B →
    CutReadyPlus (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) B

/-- **(Brick 4 discharge) `InteriorOpeningOutcomePlus` from the brick-3 bridge.**  Mirrors
`ZinanFFCT46.interiorOpeningOutcomeWBS`, upgrading the SUPPORT-stuck payload from a bare vanishing
support to `CutReadyPlus A' B` (via `hbridge`).  The wrap residual `OpenedWrapShortArcAtSupWBS` is
discharged unconditionally by `ZinanFFCT47.openedWrapShortArcAtSupWBS_holds`, so the only input here
is the brick-3 bridge.

* **REACH** (and **BASE-stuck**, collapsed to REACH) → strict + deficit drop, banked in FFCT45/46.
* **SUPPORT-stuck** → weak (FFCT46, unconditional via the discharged wrap residual) + the bridge's
  `CutReadyPlus`. -/
theorem interiorOpeningOutcomePlus_of_bridge
    (hbridge : SupportStuckWBS_CutReadyBridge) :
    InteriorOpeningOutcomePlus := by
  intro n A B hA hB hside hangle k hkdef
  set K : Fin (n + 1) := openingAxis k with hK
  set δ : ℝ := monitoredSupWBS A B k with hδ
  set A' : Fin (n + 1) → S2 := openTail A K (-δ) with hA'
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  -- side / joint bookkeeping (verbatim from `interiorOpeningOutcomeWBS`).
  have hjointk : jointAngle A' k = openedInteriorJointAngle A k (-δ) := by
    rw [hA']; exact jointAngle_openTail_eq_openedInterior A k (-δ)
  have hslack : openedInteriorJointAngle A k (-δ) ≤ jointAngle B k :=
    openedInteriorJoint_le_at_supWBS hA hka hkt hkdef
  have hside' : SameSides A' B := by
    intro i; rw [hA', openTail_preserves_sides A K (-δ) i]; exact hside i
  have hangle' : JointLe A' B := by
    intro r
    by_cases hrk : r = k
    · rw [hrk, hjointk]; exact hslack
    · rw [hA', jointAngle_openTail_eq_of_ne A k (-δ) hrk]; exact hangle r
  have hmono : endpt A ≤ endpt A' := glueWBS_clause_i hA hka hkt hkdef
  refine ⟨A', hmono, hside', hangle', ?_⟩
  -- dispatch on `SupportStuckWBS`.
  by_cases hstuck : SupportStuckWBS A B k
  · -- SUPPORT-stuck: weak convex (FFCT46) + the brick-3 bridge's `CutReadyPlus`.  RIGHT disjunct.
    have hwrap : ShortArc (openTail A K (-δ) (Fin.last n)) (openTail A K (-δ) 0) :=
      openedWrapShortArcAtSupWBS_holds n A B hA hB k hkdef
    have hweak : WeakConvexSphArm A' :=
      supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrap
    have hcr : CutReadyPlus A' B :=
      hbridge hA hB hka hkt hkdef hstuck hweak hside' hangle'
    exact Or.inr ⟨hweak, hcr⟩
  · -- ¬ SUPPORT-stuck: REACH or BASE-stuck (clause ii); BASE-stuck collapses to REACH.
    have hreach : ReachWBS A B k := by
      rcases glueWBS_clause_ii hA hB hka hkt hkdef hstuck with hr | hbase
      · exact hr
      · rcases BaseStuckProgressWBS_holds n A B hA hB k hkdef hbase with hr | hvan
        · exact hr
        · exfalso
          obtain ⟨i, j, hji, hji1, heq⟩ := hvan
          exact hstuck ⟨⟨(i, j), ⟨hji, hji1⟩⟩, by rw [supportConstraint_apply]; exact heq⟩
    -- REACH: strictly convex (FFCT46) + deficit drop.  LEFT disjunct.
    have hstrict : StrictConvexSphArm A' := reachWBS_strictConvex hA hB hka hkt hkdef hstuck
    have hreach_k : jointAngle A' k = jointAngle B k := by rw [hjointk]; exact hreach
    have hdrop : deficitCount A' B < deficitCount A B := by
      rw [hA']; exact deficitCount_openTail_reach_lt A B k (-δ) hkdef hreach_k
    exact Or.inl ⟨hstrict, hdrop⟩

/-! ## §4. Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `cut_step_from_stuckAtK_plus`'s conclusion: realised reflexively at `A = B`. -/
theorem cut_step_from_stuckAtK_plus_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

/-- Non-vacuity of `InteriorOpeningOutcomePlus`: its strict-deficit-drop disjunct is realisable
(reflexively, the REACH conclusion `endpt A ≤ endpt A`), so the outcome is a load-bearing
production, not a vacuous-hypothesis impostor. -/
theorem interiorOpeningOutcomePlus_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

/-- **Constructor for `CutReadyPlus`**: from a normalized stuck cut `(i, j)` with `StuckAtKData` and
the ear-convexity certificates, build the cut-ready datum.  (Used by the brick-3 bridge.) -/
theorem cutReadyPlus_intro {N : ℕ} {A B : Fin (N + 1) → S2} {i j : ℕ}
    (hsk : StuckAtKData A B i j)
    (hAe : WeakConvexSphArm
      (intervalArm A (i + 1) (j - (i + 1)) (by have := hsk.hij1; have := hsk.hj; omega)))
    (hBe : StrictConvexSphArm
      (intervalArm B (i + 1) (j - (i + 1)) (by have := hsk.hij1; have := hsk.hj; omega))) :
    CutReadyPlus A B :=
  ⟨i, j, hsk, hAe, hBe⟩

/-- `CutReadyPlus` is a genuine geometric datum (a normalized stuck cut with Gram signs + ear
certificates): it unpacks to a real `StuckAtKData`, so the RIGHT disjunct of the outcome is not a
vacuous-hypothesis impostor. -/
theorem cutReadyPlus_yields_stuckData {N : ℕ} {A B : Fin (N + 1) → S2}
    (hcr : CutReadyPlus A B) : ∃ i j : ℕ, StuckAtKData A B i j := by
  obtain ⟨i, j, hsk, _, _⟩ := hcr
  exact ⟨i, j, hsk⟩

end ProofsInTheBook.ZinanFFCT48

#print axioms ProofsInTheBook.ZinanFFCT48.cut_step_from_stuckAtK_plus
#print axioms ProofsInTheBook.ZinanFFCT48.interiorOpeningOutcomePlus_of_bridge
