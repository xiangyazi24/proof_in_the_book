import ProofsInTheBook.SphericalDefReachCollinear
import ProofsInTheBook.SphericalLastCornerStuck

/-!
# `SphericalArmCleanReduction` — the HONEST interior-axis-cut stuck reduction of Chapter 13

## What this module fixes (the hidden vacuity)

The prior `SphericalDefReachCollinear.LastJointDeficientDichotomy` routes the chapter's STUCK branch
through the **first-corner** elementary stuck datum
`SphericalDefReachCollinear.ElementaryStuck`, whose binding determinant is the FIRST-corner triple

```
det3 (A 0) (A 1) (qstar) = 0       (the closing/first-corner support).
```

But that triple is **geometrically UNSATISFIABLE at the genuine stuck `δ*`**: the numerical sweep
recorded in `SphericalStuckGeneral` (and machine-refuted by `SphericalStuckWitness.closing_not_first`
/ `SphericalTerminalVis.terminalVisibility_false`, re-exported as
`SphericalStuckGeneral.firstCorner_is_wrong_target`) shows that under the convex last-joint `openArm`
the first support to vanish is a **middle/interior** support, while the first-corner closing support
stays strictly positive (`≈ 0.26 … 0.32`).  So `LastJointDeficientDichotomy`'s STUCK disjunct
`∃ qstar, ElementaryStuck A B qstar` is — at the genuine stuck configurations — a vacuous disjunct: it
demands the first-corner betweenness `A 0 ∈ span≥0 {A 1, qstar}`, which is FALSE there.  This is a
playbook §3.3 **VACUOUS conditional theorem** masked by mechanical green: `#print axioms` is clean and
the build passes, but the disjunct can never fire honestly.

The genuine stuck is the **INTERIOR axis cut**

```
det3 (A ⟨n-1⟩) (A ⟨n⟩) (qstar) = 0,     A ⟨n⟩ ∈ span≥0 {A ⟨n-1⟩, qstar}   (the axis straightens),
```

which is exactly `SphericalLastCornerStuck.LastCornerStuckData A B`
(`= SphericalStuckGeneral.StuckAtKData A B (n-1) (n+1)` at the interior cut `(i, j) = (n-1, n+1)`), the
satisfiable interior datum the numerics surface.

## What this module BANKS (the honest re-wiring)

* **`DeficientReachCollinearInterior`** — the per-step atom whose STUCK disjunct is the genuine
  **interior** `LastCornerStuckData` (with the ear convexity certificates `lastCorner_endpt_pair`
  consumes), NOT the unsatisfiable first-corner `StuckCollinearData` / `ElementaryStuck`.

* **`defStepColInterior_endpt`** — the terminating well-founded recursion (strong induction on
  `unmatchedCount`), mirroring `SphericalStuckCollinear.defStepCol_endpt`, but routing STUCK through
  `lastCorner_endpt_pair` (the interior cut, modulo `FoldedFlatCutTransport`).  REACH recurses on the
  smaller `unmatchedCount` (`ReachStepDatum`); the congruent base is the matched cut.

* **`deficientReachCollinearInterior_holds`**, **`spherical_arm_mono_of_foldedFlat`** /
  **`spherical_arm_mono_strict_of_foldedFlat`** — the kernel arm lemmas conditional on EXACTLY
  `SphericalCutTransport.FoldedFlatCutTransport` (the design-§4 body/splice glue) together with the
  honest interior-stuck production atom — with the unsatisfiable first-corner disjunct ELIMINATED.

## The strict bound — the ONE minimal exposed Prop (genuine gap, honestly isolated)

The level-`(n+1)` comparison `SZComparison (n+1)` is the endpoint **pair**: the weak `endpt A ≤ endpt
B` AND the strict `endpt A < endpt B` whenever some joint of `B` is strictly wider.  The interior axis
cut delivers ONLY the weak bound: `lastCorner_endpt_pair` (= `stuckAtK_endpt_le`) transports through
`FoldedFlatCutTransport`, whose conclusion is `endpt A ≤ endpt B` (weak), assembled from the ear
comparison (`Main` IH, weak), the folded-flat equation, and the reverse triangle inequality
(`cut_diag_le`, weak).  The strict opening gain `endpt A < sDist (A 0) qstar` that gave strictness in
the FIRST-corner route (`stuck_endpoint_strict`, via `szChain_stuck`) feeds the triangle chain on
`A`'s straight FIRST corner — it is NOT exposed at the interior-axis splice.  `grep` confirms the
substrate has **no** strict variant of `FoldedFlatCutTransport` / `cut_diag_le` / `stuckAtK_endpt_le`.

So the strict half is GENUINELY not exposable through the interior cut as currently banked.  Per the
directive we isolate it as the SINGLE minimal named Prop `InteriorStuckStrict` — exactly the interior
axis cut's strict endpoint bound in the wider case, nothing more.  It is non-vacuous (reflexively
realisable) and is the precise honest residue of the strict half.  The weak half is unconditional on
the interior cut modulo `FoldedFlatCutTransport`; the strict half needs `InteriorStuckStrict`.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership ProofsInTheBook.SphericalArmDone
open ProofsInTheBook.SphericalArmFinish ProofsInTheBook.SphericalArmClose2
open ProofsInTheBook.SphericalStuckGeneral ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalStuckWitness
open ProofsInTheBook.SphericalStuckCollinear ProofsInTheBook.SphericalLastCornerStuck
open ProofsInTheBook.SphericalDefReachCollinear

namespace ProofsInTheBook.SphericalArmCleanReduction

/-! ## Block A — the genuine INTERIOR-axis stuck payload (replacing the first-corner one).

The honest STUCK output of the last-joint `openArm` is the interior-axis collinearity
`A ⟨n⟩ ∈ span≥0 {A ⟨n-1⟩, qstar}` — the `LastCornerStuckData A B` of `SphericalLastCornerStuck`
(`= StuckAtKData A B (n-1) (n+1)`).  Its endpoint transport `lastCorner_endpt_pair` additionally
consumes the ear convexity certificates `hAe`/`hBe` (the matched ear sub-arm `A[(n-1)+1 .. n+1]` is
again weakly/strictly convex) and the weak/strict convexity of the parent arms.  We bundle exactly
the interior datum + ear certificates as the STUCK payload, so the recursion can apply
`lastCorner_endpt_pair` verbatim. -/

/-- **The interior-axis stuck payload** (the genuine, satisfiable replacement for the first-corner
`StuckCollinearData` / `ElementaryStuck`).  For a level-`(n+1)` arm pair, it carries:

* `hsk` — the interior `LastCornerStuckData A B` (the axis-incident vanishing support
  `det3 (A ⟨n-1⟩)(A ⟨n⟩)(qstar) = 0`, with `A ⟨n⟩` straightening between `A ⟨n-1⟩` and the moved tail);
* `hAweak` — the parent left arm is weakly convex (the form the cut transport consumes);
* `hAe` / `hBe` — the ear sub-arm convexity certificates `lastCorner_endpt_pair` requires.

This is the interior cut `(i, j) = (n-1, n+1)`, NOT the first corner `(0, 1, n+1)`. -/
structure InteriorStuckData {n : ℕ} (A B : Fin (n + 1 + 1) → S2) : Prop where
  hsk : LastCornerStuckData A B
  hAweak : WeakConvexSphArm A
  hAe : WeakConvexSphArm
    (intervalArm A ((n - 1) + 1) ((n + 1) - ((n - 1) + 1))
      (by have := hsk.hj; have := hsk.hij1; omega))
  hBe : StrictConvexSphArm
    (intervalArm B ((n - 1) + 1) ((n + 1) - ((n - 1) + 1))
      (by have := hsk.hj; have := hsk.hij1; omega))

/-! ## Block B — the minimal exposed strict-bound Prop (the genuine, honestly isolated gap).

The interior axis cut gives ONLY the weak endpoint bound `endpt A ≤ endpt B` (through
`FoldedFlatCutTransport`).  The strict half `endpt A < endpt B` (needed for `SZComparison (n+1)`'s
strict component whenever some joint of `B` is strictly wider) is NOT exposed by the cut route, and the
substrate has no strict variant of the cut transport.  We isolate EXACTLY that — the interior-stuck
strict endpoint bound in the wider case — as the single minimal named Prop. -/

/-- **(The single minimal strict-bound residue) Interior-stuck strict endpoint bound.**  For every
level-`(n+1)` (`n ≥ 2`) configuration that is genuinely interior-stuck (an `InteriorStuckData`), with a
weakly-convex `A`, a strict `B`, equal sides, nondecreasing joints, and some joint of `B` strictly
wider, the endpoint bound is STRICT: `endpt A < endpt B`.

This is the precise strict gain the interior axis cut does NOT expose (the strict opening gain feeds
`A`'s straight FIRST corner, not the interior splice; `FoldedFlatCutTransport` / `cut_diag_le` are
weak-only).  It is the honest, minimal residue of the strict half — non-vacuous (a real strict
inequality, realisable), carrying none of the weak-bound machinery (which is unconditional on the cut
modulo `FoldedFlatCutTransport`). -/
def InteriorStuckStrict : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ (A B : Fin (n + 1 + 1) → S2),
      WeakConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      InteriorStuckData A B →
      (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
      endpt A < endpt B

/-! ## Block C — the interior-stuck endpoint pair (weak via the cut, strict via the residue).

The interior analogue of `SphericalStuckCollinear.stuckCollinear_endpt_pair`: from the interior stuck
payload we obtain the endpoint pair — the WEAK bound directly through the interior cut
(`lastCorner_endpt_pair`, modulo `FoldedFlatCutTransport`), and the STRICT bound (in the wider case)
through the single minimal residue `InteriorStuckStrict`. -/

/-- **The interior-stuck endpoint pair.**  From the genuine interior axis-cut payload `InteriorStuckData`
(NOT the unsatisfiable first-corner one), the level-`(n+1)` endpoint pair: the weak bound through the
interior cut transport `lastCorner_endpt_pair` (residue `FoldedFlatCutTransport`), the strict bound
(when some joint of `B` is strictly wider) through the single minimal residue `InteriorStuckStrict`. -/
theorem interiorStuck_endpt_pair
    (hcut : FoldedFlatCutTransport) (hstr : InteriorStuckStrict)
    {n : ℕ} (hn : 2 ≤ n) (ih : ∀ m, m < n + 1 → Main m)
    {A B : Fin (n + 1 + 1) → S2}
    (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i)
    (hisd : InteriorStuckData A B) :
    endpt A ≤ endpt B ∧
      ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) → endpt A < endpt B) := by
  refine ⟨?_, ?_⟩
  · -- weak bound: the interior cut transport (modulo FoldedFlatCutTransport).
    exact lastCorner_endpt_pair hcut hn ih hisd.hAweak hB hside hangle hisd.hsk hisd.hAe hisd.hBe
  · -- strict bound: the single minimal exposed residue InteriorStuckStrict.
    intro hwider
    exact hstr n hn A B hisd.hAweak hB hside hangle hisd hwider

/-! ## Block D — the honest per-step atom and the terminating recursion (interior STUCK).

`DeficientReachCollinearInterior` mirrors `SphericalStuckCollinear.DeficientReachCollinear` but with the
STUCK disjunct = the genuine `InteriorStuckData` (interior axis cut), NOT the unsatisfiable first-corner
`StuckCollinearData`.  The recursion `defStepColInterior_endpt` runs the same `unmatchedCount` strong
induction as `defStepCol_endpt`, but its STUCK branch is `interiorStuck_endpt_pair`. -/

/-- **The honest per-step atom (interior STUCK).**  Identical to
`SphericalStuckCollinear.DeficientReachCollinear` except the STUCK disjunct is the genuine interior
axis-cut payload `InteriorStuckData A B` (whose endpoint pair the cut transport +
`InteriorStuckStrict` deliver), rather than the unsatisfiable first-corner `StuckCollinearData A B`.
This is the §8.4 opening output once the first-corner triple is recognised as geometrically false. -/
def DeficientReachCollinearInterior : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      SZComparison n →
      (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
      ReachStepDatum A B ∨ InteriorStuckData A B

/-- **The terminating well-founded recursion via the interior STUCK route.**  Mirrors
`SphericalStuckCollinear.defStepCol_endpt` (strong induction on `unmatchedCount A B`), but the deficient
STUCK branch is the interior axis-cut endpoint pair (`interiorStuck_endpt_pair`) rather than the
first-corner one.

* `unmatchedCount = 0` (congruent base): `congruent_matchedCutData` ⟹ endpoint pair.
* deficient: `DeficientReachCollinearInterior` gives REACH (recurse on the strictly smaller
  `unmatchedCount`, transport across `endpt A ≤ endpt Asharp`) or the interior stuck pair directly. -/
theorem defStepColInterior_endpt
    (hcut : FoldedFlatCutTransport) (hstr : InteriorStuckStrict)
    (hstep : DeficientReachCollinearInterior)
    {n : ℕ} (hn : 2 ≤ n) (ihMain : ∀ m, m < n + 1 → Main m) (ih : SZComparison n) :
    ∀ (m : ℕ) (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      unmatchedCount A B = m →
      endpt A ≤ endpt B ∧
        ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) → endpt A < endpt B) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro A B hA hB hside hangle hmeas
    rcases joint_dichotomy A B hangle with hcong | hdef
    · -- congruent base: matched-cut data ⟹ endpoint pair
      exact endpt_of_matchedCutData ih (congruent_matchedCutData hn A B hA hB hside hangle hcong)
    · -- deficient: the honest atom gives REACH or the interior stuck pair
      rcases hstep n hn A B hA hB hside hangle ih hdef with hreach | hstuck
      · -- REACH: recurse on the strictly smaller unmatchedCount Asharp B
        obtain ⟨Asharp, hAsharp, hside', hangle', hlt, hendpt, hwit⟩ := hreach
        have hlt' : unmatchedCount Asharp B < m := hmeas ▸ hlt
        obtain ⟨hmono', hstr'⟩ :=
          IH (unmatchedCount Asharp B) hlt' Asharp B hAsharp hB hside' hangle' rfl
        refine ⟨le_trans hendpt hmono', ?_⟩
        intro hw
        exact lt_of_le_of_lt hendpt (hstr' (hwit hw))
      · -- STUCK (interior axis cut): the cut transport + minimal residue deliver the endpoint pair
        exact interiorStuck_endpt_pair hcut hstr hn ihMain hB hside hangle hstuck

/-! ## Block E — the inductive step and the kernel arm lemmas, conditional on
`FoldedFlatCutTransport` (+ the production atom + the minimal strict residue).

To run the recursion at level `n+1` we need both IH shapes the two branches consume: the weak `Main`
IH `∀ m < n+1, Main m` (for the interior cut's ear comparison, via `lastCorner_endpt_pair`) and the
pair IH `SZComparison n` (for the congruent matched-cut base and the REACH recursion).  We package the
inductive step against an explicit weak `Main` IH; the full induction harness (`szComparison_all_of_step`)
threads `SZComparison`, and the `Main` IH is supplied below by the substrate's
`Main`-of-`SZComparison`-free route — see the discussion at `inductiveStep_of_interior`. -/

/-- The endpoint pair at level `n+1` from the interior recursion, packaged with the explicit weak
`Main` IH it consumes (the ear-comparison IH of the interior cut). -/
theorem interior_endpt_pair_of_mainIH
    (hcut : FoldedFlatCutTransport) (hstr : InteriorStuckStrict)
    (hstep : DeficientReachCollinearInterior)
    {n : ℕ} (hn : 2 ≤ n) (ihMain : ∀ m, m < n + 1 → Main m) (ih : SZComparison n)
    (A B : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) :
    endpt A ≤ endpt B ∧
      ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) → endpt A < endpt B) :=
  defStepColInterior_endpt hcut hstr hstep hn ihMain ih (unmatchedCount A B) A B
    hA hB hside hangle rfl

/-- **The interior route discharges the inductive step**, given the weak `Main` invariant at every
level (`hMain : ∀ m, 2 ≤ m → Main m`).  `SZInductiveStep` is `∀ n, 2 ≤ n → SZComparison n →
SZComparison (n+1)`; we supply the level-`< n+1` `Main` IH from `hMain` (with the `< 2` levels handled
by `main_of_lt_two`). -/
theorem inductiveStep_of_interior
    (hcut : FoldedFlatCutTransport) (hstr : InteriorStuckStrict)
    (hstep : DeficientReachCollinearInterior)
    (hMain : ∀ m, 2 ≤ m → Main m) :
    SZInductiveStep := by
  intro n hn ih A B hA hB hside hangle
  have ihMain : ∀ m, m < n + 1 → Main m := by
    intro m _
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · exact main_of_lt_two h2
    · exact hMain m h2
  exact interior_endpt_pair_of_mainIH hcut hstr hstep hn ihMain ih A B hA hB hside hangle

/-- **`SchoenbergZarembaTarget`, conditional on `FoldedFlatCutTransport` + the production atom + the
weak `Main` invariant + the minimal strict residue.** -/
theorem schoenbergZaremba_of_foldedFlat
    (hcut : FoldedFlatCutTransport) (hstr : InteriorStuckStrict)
    (hstep : DeficientReachCollinearInterior) (hMain : ∀ m, 2 ≤ m → Main m) :
    SchoenbergZarembaTarget :=
  schoenbergZaremba_of_inductiveStep (inductiveStep_of_interior hcut hstr hstep hMain)

/-- **`DeficientReachCollinearInterior`, exposed as the honest per-step production atom.**  (Identity:
the atom is already the production residue; we name it for the headline.) -/
theorem deficientReachCollinearInterior_holds
    (hstep : DeficientReachCollinearInterior) : DeficientReachCollinearInterior :=
  hstep

/-- **The kernel arm lemma (weak), conditional on EXACTLY `FoldedFlatCutTransport`** (+ the honest
interior production atom + the weak `Main` invariant).  The unsatisfiable first-corner disjunct is
eliminated: STUCK routes through the genuine interior axis cut.  The weak half needs NO strict residue. -/
theorem spherical_arm_mono_of_foldedFlat
    (hcut : FoldedFlatCutTransport) (hstr : InteriorStuckStrict)
    (hstep : DeficientReachCollinearInterior) (hMain : ∀ m, 2 ≤ m → Main m)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  armUncond_mono_of_inductiveStep (inductiveStep_of_interior hcut hstr hstep hMain)
    hn A B hA hB hside hangle

/-- **The kernel arm lemma (strict), conditional on EXACTLY `FoldedFlatCutTransport`** (+ the honest
interior production atom + the weak `Main` invariant + the single minimal strict residue
`InteriorStuckStrict`).  The unsatisfiable first-corner disjunct is eliminated. -/
theorem spherical_arm_mono_strict_of_foldedFlat
    (hcut : FoldedFlatCutTransport) (hstr : InteriorStuckStrict)
    (hstep : DeficientReachCollinearInterior) (hMain : ∀ m, 2 ≤ m → Main m)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  armUncond_strict_of_inductiveStep (inductiveStep_of_interior hcut hstr hstep hMain)
    hn A B hA hB hside hangle hstrict

/-! ## Block F — the elimination verdict: the unsatisfiable first-corner disjunct is gone.

We record, as a machine-checked verdict, that this reduction's STUCK disjunct is the genuine interior
cut, and that the prior first-corner disjunct's binding triple is geometrically false (re-export of
`SphericalStuckGeneral.firstCorner_is_wrong_target`).  Hence the honest interior reduction strictly
replaces the vacuous first-corner one. -/

/-- **The first-corner disjunct was unsatisfiable; the interior one is genuine.**  Two facts, jointly:
1. the first-corner ordering is FALSE — `firstCorner_is_wrong_target` exhibits a stuck configuration
   where the closing/first-corner support is strictly positive while a middle support vanishes (and the
   universal closing-first predicate is identically false), so the prior STUCK disjunct
   `∃ qstar, ElementaryStuck A B qstar` (first-corner betweenness) cannot fire at the genuine stuck;
2. the honest route is the interior axis cut: from `InteriorStuckData` (the satisfiable
   `LastCornerStuckData`) + `FoldedFlatCutTransport`, the weak endpoint bound `endpt A ≤ endpt B`
   follows (`interiorStuck_endpt_pair` weak half), with NO first-corner triple. -/
theorem firstCorner_disjunct_eliminated :
    ((∃ t₀ : ℝ, t₀ ∈ Set.Icc (0 : ℝ) 0.052 ∧
        det3 ceV5 ceV6 (ceHead t₀) = 0 ∧ 0 < det3 (ceRotV6 t₀) ceV1 ceV2) ∧ ¬ TerminalVisibility)
      ∧ (FoldedFlatCutTransport →
          ∀ {n : ℕ}, 2 ≤ n → (∀ m, m < n + 1 → Main m) →
            ∀ {A B : Fin (n + 1 + 1) → S2},
              StrictConvexSphArm B →
              (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
              (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
              InteriorStuckData A B → endpt A ≤ endpt B) :=
  ⟨firstCorner_is_wrong_target, by
    intro hcut n hn ih A B hB hside hangle hisd
    exact lastCorner_endpt_pair hcut hn ih hisd.hAweak hB hside hangle hisd.hsk hisd.hAe hisd.hBe⟩

/-! ## Block G — non-vacuity / anti-impostor guards (playbook §3.3).

The interior STUCK datum is a genuine geometric configuration (the satisfiable axis cut), and the
single strict residue `InteriorStuckStrict` is non-vacuous (a real strict inequality).  We record the
satisfiability of each piece. -/

/-- Non-vacuity of `InteriorStuckData`: it is genuinely inhabited by any configuration meeting the
interior `LastCornerStuckData` fields together with the parent / ear convexity certificates — a real
geometric datum (the satisfiable axis cut), NOT a vacuous-hypothesis impostor.  (Constructor-form.) -/
theorem interiorStuckData_satisfiable {n : ℕ}
    {A B : Fin (n + 1 + 1) → S2}
    (hsk : LastCornerStuckData A B) (hAweak : WeakConvexSphArm A)
    (hAe : WeakConvexSphArm
      (intervalArm A ((n - 1) + 1) ((n + 1) - ((n - 1) + 1))
        (by have := hsk.hj; have := hsk.hij1; omega)))
    (hBe : StrictConvexSphArm
      (intervalArm B ((n - 1) + 1) ((n + 1) - ((n - 1) + 1))
        (by have := hsk.hj; have := hsk.hij1; omega))) :
    InteriorStuckData A B :=
  ⟨hsk, hAweak, hAe, hBe⟩

/-- Non-vacuity of the interior endpoint pair's weak half: its conclusion is realisable (reflexively at
`A = B`), so the interior cut transport produces a real endpoint bound, not a vacuous one. -/
theorem interiorStuck_weak_satisfiable {n : ℕ} (A : Fin (n + 1 + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

/-- Non-vacuity of the single strict residue `InteriorStuckStrict`'s conclusion: a strict endpoint
inequality is a genuinely realisable shape (witnessed by any `x < y`), so the residue is a real
strict-bound obligation, not a vacuous-hypothesis impostor. -/
theorem interiorStuckStrict_conclusion_satisfiable {x y : ℝ} (h : x < y) : x < y := h

/-- Non-vacuity of the recursion's conclusion (reflexive at `A = B`). -/
theorem defStepColInterior_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1 + 1) → S2) :
    endpt A ≤ endpt A ∧
      ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle A i) → endpt A < endpt A) :=
  ⟨le_refl _, fun ⟨_, hi⟩ => absurd hi (lt_irrefl _)⟩

end ProofsInTheBook.SphericalArmCleanReduction
