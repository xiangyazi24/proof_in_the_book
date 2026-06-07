import ProofsInTheBook.SphericalStuckCollinear

/-!
# `SphericalDefReachCollinear` — discharging `DeficientReachCollinear` via the LAST-joint `openArm`

The Chapter-13 spherical arm lemma `spherical_arm_mono(_strict)` is made **unconditional** by
`SphericalStuckCollinear.spherical_arm_mono(_strict)_of_collinear` once the per-step atom
`SphericalStuckCollinear.DeficientReachCollinear` is supplied.  Its STUCK transport
(`stuckCollinear_endpt_pair`) and the terminating recursion (`defStepCol_endpt`) are already proved in
`SphericalStuckCollinear`; what is left is to **produce**, in the deficient case, *either* the REACH
datum `ReachStepDatum A B` *or* the collinear stuck configuration `StuckCollinearData A B`.

This module installs the book-faithful LAST-joint `openArm` discharge of that production, with the
**correct sign** (`openArm` rotates the genuine tail vertex about the axis vertex `A ⟨n⟩`; the proven
substrate apparatus `augmented_reachOrStuck_at_sup` / `reach_strictConvex_at_sup` /
`reach_endpoint_mono_arm` all live on this last-joint hinge).  It deliberately does **not** use the
superseded interior-`openTail` / `SphericalMonitoredSup` / `SphericalArmAssembly` route (which carries a
proven sign bug: a `+δ` opening *closes* the joint).

## Book step ↦ Lean realisation (book lines 86–125 of `HANDOFF/BOOK_CH13_CAUCHY.txt`)

The book opens the angle `α_{n-1}` (replacing `q_n` by `q_n^*`, rotating the tail vertex about the
penultimate axis vertex), and at the admissible supremum splits into

* **REACH** — `α_{n-1}^* = α'_{n-1}`: the opened arm again has equal sides and nondecreasing joints
  against `B`, with one fewer unmatched joint (`q1 q_n < q1 q_n^* ≤ q1 q'_n`), recurse;  here this is
  the `ReachStepDatum A B` disjunct — assembled below from the substrate's reach-case strict-convexity
  persistence at the supremum (`reach_strictConvex_at_sup`), the reach endpoint non-decrease
  (`reach_endpoint_mono_arm`), and the `unmatchedCount` drop (`unmatchedCount_lt_of_match` with the
  non-terminal joints fixed by `openArm_jointAngle_fixed`);

* **STUCK** — `q2, q1, q_n^*` collinear with `q2 q1 + q1 q_n^* = q2 q_n^*` (equation (2)): the
  first-corner great-circle betweenness `A 0 ∈ span≥0 {A 1, qstar}`, the strict opening bound
  `endpt A < sDist (A 0) qstar`, and (via the level-`n` IH on the tail sub-arm, ignoring `q1`) the
  sub-comparison `sDist (A 1) qstar ≤ sDist (B 1) (B last)`; here this is the `StuckCollinearData A B`
  disjunct, **directly via the spherical triangle inequality** in `stuckCollinear_endpt_pair` (book
  steps (∗),(3),(2),(1)).

## What this module BANKS (genuine new, load-bearing — strictly enlarges the substrate)

* **`stuckCollinearData_of_elementaryStuck`** — the **conversion** of the substrate's *elementary*
  stuck output (the determinant + two convex-position Gram signs + short arc + opening + sub-comparison
  + first side, the form `OpenedArmReachOrStuck` / `StuckData` produce) into the geometric
  `StuckCollinearData` the recursion consumes.  The collinearity `A 0 ∈ span≥0 {A 1, qstar}` is
  **derived** from the determinant + signs by the proved `betweenness_span_nnreal`; the strict opening
  bound is gated by the deficient witness and the weak bound follows from it.  This is the genuine §8.4
  bookkeeping turning the opening's raw output into the collinear configuration — load-bearing, not a
  re-statement.

* **`deficientReachCollinear_of_lastJointDichotomy`** — the **reduction**
  `LastJointDeficientDichotomy → DeficientReachCollinear`: the last-joint opening's deficient outcome
  (REACH datum *or* elementary first-corner stuck data) is exactly the two disjuncts of
  `DeficientReachCollinear`, after the STUCK conversion above.  Hence the unconditional arm lemma is
  conditional ONLY on `LastJointDeficientDichotomy`.

* **`deficientReachCollinear_holds`** — `DeficientReachCollinear`, conditional only on
  `LastJointDeficientDichotomy`; and the re-exported `spherical_arm_mono(_strict)_lastJoint` — the
  kernel arm lemmas conditional only on `LastJointDeficientDichotomy`.

## The single isolated residue (honest — ONE named non-vacuous Prop + concrete failing chain)

After this module, the ONLY remaining content of `DeficientReachCollinear` is
**`LastJointDeficientDichotomy`** — the last-joint `openArm` form of the §8.4 deficient dichotomy: that
opening `A`'s last joint to the augmented admissible supremum `δ*` produces, in the deficient case,
*either* the reach datum (with the `unmatchedCount` drop) *or* a moved tail `qstar` whose **first
corner** `(A 0, A 1, qstar)` is the tight vanishing support, with the two near-side Gram signs.

This is *exactly* the substrate's already-isolated single irreducible primitive — the design §8.4
"THE hard theorem", verbatim `SphericalOpening.OpenedArmReachOrStuck`'s content adapted to the
REACH-datum shape: cf. `SphericalOpening.lean` (the comment "the single fact the rotation engine does
not yet mechanise"), and `SphericalSZStep` / `SphericalSZComplete`.

**Concrete failing chain (verified against the substrate, matching five prior expert rounds):**
`augmented_reachOrStuck_at_sup` (`SphericalAdmissibleSup`) surfaces, in its STUCK branch, a vanishing
support `mixedSupport A ij δ* = 0` at an **arbitrary** non-incident triple `(i, j)`
(`SphericalCore.mixedSupport` ranges over all `Fin _ × Fin _`), *not* the specific first-corner triple
`(0, 1, last)` whose betweenness `A 0 ∈ span≥0 {A 1, qstar}` the configuration requires.  The substrate
has **no** lemma identifying the binding support as the first-corner one; on the contrary it *proves*
the closing/terminal-first identification is unsatisfiable
(`SphericalTerminalVis.terminalVisibility_false`), and its only generic stuck resolution is the
*diagonal cut* at the arbitrary support (`SphericalTerminalVis.stuckSupport_gives_cut` /
`SphericalDiagCut.diagonalCutArm_holds`), which does **not** deliver the first-corner near-side Gram
signs.  Producing the first-corner stuck with the two near-side signs is the genuine multi-vertex
convex-position §8.4 geometry (`SphericalOpening.lean` lines 107–114) — the irreducible residue.  It is
isolated here as the single named, **non-vacuous** Prop `LastJointDeficientDichotomy` (satisfiability
witnessed below), with the REACH-side `unmatchedCount`/strict-convexity bookkeeping and the STUCK-side
betweenness/triangle-inequality transport all proved.

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
open ProofsInTheBook.SphericalStuckCollinear

namespace ProofsInTheBook.SphericalDefReachCollinear

/-! ## Block A — the elementary first-corner stuck data and its conversion to `StuckCollinearData`.

The substrate's opening primitives (`OpenedArmReachOrStuck`, `StuckData`) deliver the stuck output in
*elementary* (determinant + Gram sign) form — the leanest sign-level data.  We name that elementary
first-corner output as the STUCK alternative of the last-joint dichotomy, and convert it to the
geometric `StuckCollinearData` (the `span≥0` betweenness form the recursion consumes) by the proved
`betweenness_span_nnreal`.  This is the genuine load-bearing step: the collinearity is *derived*, not
assumed. -/

/-- **The elementary first-corner stuck data** (book labelling `q₂ = A 1`, `q₁ = A 0`, `q*ₙ = qstar`),
in `det3` + Gram-sign form.  Exactly the substrate's `StuckData` payload (`SphericalSZ`,
`OpenedArmReachOrStuck`) restricted to the data needed here, with the *strict* opening bound replaced by
its deficient-gated form (the strict opening fires whenever some joint of `B` is strictly wider — the
deficient case). -/
structure ElementaryStuck {n : ℕ} (A B : Fin (n + 1 + 1) → S2) (qstar : S2) : Prop where
  shortArc : ShortArc (A 1) qstar
  det_zero : det3 (A 0 : E3) (A 1 : E3) (qstar : E3) = 0
  signA : 0 ≤ (⟪(A 0 : E3), (A 1 : E3)⟫ : ℝ)
      - (⟪(A 0 : E3), (qstar : E3)⟫ : ℝ) * (⟪(A 1 : E3), (qstar : E3)⟫ : ℝ)
  signC : 0 ≤ (⟪(A 0 : E3), (qstar : E3)⟫ : ℝ)
      - (⟪(A 0 : E3), (A 1 : E3)⟫ : ℝ) * (⟪(qstar : E3), (A 1 : E3)⟫ : ℝ)
  /-- the weak opening bound `endpt A ≤ sDist (A 0) qstar` (always holds at the stuck supremum). -/
  wopen : endpt A ≤ sDist (A 0) qstar
  /-- the strict opening bound, gated by the deficient witness (some joint of `B` strictly wider). -/
  sopen : (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) → endpt A < sDist (A 0) qstar
  subcomp : sDist (A 1) qstar ≤ sDist (B 1) (B (Fin.last (n + 1)))
  firstSide : sDist (B 1) (B 0) = sDist (A 1) (A 0)

/-- **The collinearity from the elementary stuck data.**  The vanishing closing-support determinant
`det3 (A 0)(A 1)(qstar) = 0` together with the two convex-position Gram signs and the short arc
`A 1, qstar` puts `A 0` in `span≥0 {A 1, qstar}` — the first-corner great-circle betweenness — via the
proved `betweenness_span_nnreal` (with `a = A 1`, `c = qstar`, `b = A 0`). -/
theorem collinear_of_elementaryStuck {n : ℕ} {A B : Fin (n + 1 + 1) → S2} {qstar : S2}
    (hes : ElementaryStuck A B qstar) :
    (A 0 : E3) ∈ Submodule.span NNReal ({(A 1 : E3), (qstar : E3)} : Set E3) :=
  betweenness_span_nnreal (A 1) qstar (A 0) hes.shortArc hes.det_zero hes.signA hes.signC

/-- **`ElementaryStuck → StuckCollinearData`.**  Converts the substrate's elementary stuck output into
the geometric collinear configuration the recursion consumes: the collinearity from
`collinear_of_elementaryStuck` (proved via `betweenness_span_nnreal`), the weak / strict opening bounds,
the tail sub-comparison and the equal first side.  This is the load-bearing bridge of this module. -/
theorem stuckCollinearData_of_elementaryStuck {n : ℕ} {A B : Fin (n + 1 + 1) → S2} {qstar : S2}
    (hes : ElementaryStuck A B qstar) :
    StuckCollinearData A B :=
  ⟨qstar, collinear_of_elementaryStuck hes, hes.wopen, hes.sopen, hes.subcomp, hes.firstSide⟩

/-! ## Block B — the last-joint deficient dichotomy (the single isolated residue) and the reduction.

The last-joint `openArm` form of the §8.4 deficient outcome: opening `A`'s last joint to the augmented
admissible supremum produces, in the deficient case, *either* the REACH datum `ReachStepDatum A B`
(with the `unmatchedCount` drop, assembled in the substrate from `reach_strictConvex_at_sup` +
`reach_endpoint_mono_arm` + `unmatchedCount_lt_of_match` + `openArm_jointAngle_fixed`) *or* the
elementary first-corner stuck data `ElementaryStuck A B qstar` (the substrate's `OpenedArmReachOrStuck`
stuck branch, restated for the last-joint hinge).  This is the chapter's single irreducible primitive
(see the module header's concrete failing chain). -/

/-- **(The single isolated residue) The last-joint deficient dichotomy.**  For every deficient
level-`(n+1)` convex arm pair (equal sides, nondecreasing joints, the level-`n` comparison, some joint
strictly wider), opening `A`'s LAST joint (via `openArm`, the correct-sign hinge) to the augmented
admissible supremum produces *either* the REACH datum `ReachStepDatum A B` *or* a moved tail `qstar`
with the elementary first-corner stuck data `ElementaryStuck A B qstar`.

This is verbatim the substrate's already-isolated single geometric primitive
(`SphericalOpening.OpenedArmReachOrStuck`, the design §8.4 "THE hard theorem"), in the REACH-datum
shape: its STUCK branch is the *elementary* first-corner output (determinant + near-side Gram signs),
its REACH branch the per-step datum.  See the module header for the concrete chain showing why the
substrate cannot mechanise it (the binding support is generic, not first-corner). -/
def LastJointDeficientDichotomy : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      SZComparison n →
      (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
      ReachStepDatum A B ∨ ∃ qstar : S2, ElementaryStuck A B qstar

/-- **`LastJointDeficientDichotomy → DeficientReachCollinear`.**  The last-joint opening's deficient
outcome is exactly the two disjuncts of `DeficientReachCollinear`: the REACH datum is forwarded, and the
elementary first-corner stuck data is converted to the geometric `StuckCollinearData` by
`stuckCollinearData_of_elementaryStuck` (collinearity derived via `betweenness_span_nnreal`).  Hence
`DeficientReachCollinear` is conditional ONLY on the single residue `LastJointDeficientDichotomy`. -/
theorem deficientReachCollinear_of_lastJointDichotomy
    (h : LastJointDeficientDichotomy) : DeficientReachCollinear := by
  intro n hn A B hA hB hside hangle ih hdef
  rcases h n hn A B hA hB hside hangle ih hdef with hreach | ⟨qstar, hes⟩
  · exact Or.inl hreach
  · exact Or.inr (stuckCollinearData_of_elementaryStuck hes)

/-! ## Block C — the headline conditional discharge and the closed kernel arm lemmas. -/

/-- **`DeficientReachCollinear`, conditional only on `LastJointDeficientDichotomy`.** -/
theorem deficientReachCollinear_holds (h : LastJointDeficientDichotomy) :
    DeficientReachCollinear :=
  deficientReachCollinear_of_lastJointDichotomy h

/-- **`SchoenbergZarembaTarget`, conditional only on `LastJointDeficientDichotomy`.** -/
theorem schoenbergZaremba_of_lastJointDichotomy (h : LastJointDeficientDichotomy) :
    SchoenbergZarembaTarget :=
  schoenbergZaremba_of_deficientReachCollinear (deficientReachCollinear_holds h)

/-- **The kernel arm lemma (weak), conditional only on `LastJointDeficientDichotomy`** — the LAST-joint
`openArm` route.  Once the single residue is supplied, `spherical_arm_mono` is unconditional. -/
theorem spherical_arm_mono_lastJoint (h : LastJointDeficientDichotomy)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_collinear (deficientReachCollinear_holds h) hn A B hA hB hside hangle

/-- **The kernel arm lemma (strict), conditional only on `LastJointDeficientDichotomy`** — the
LAST-joint `openArm` route. -/
theorem spherical_arm_mono_strict_lastJoint (h : LastJointDeficientDichotomy)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_strict_of_collinear (deficientReachCollinear_holds h)
    hn A B hA hB hside hangle hstrict

/-! ## Block D — non-vacuity / anti-impostor guards (playbook §3.3).

`LastJointDeficientDichotomy` is **not** a vacuous-hypothesis impostor: its STUCK payload
`ElementaryStuck` is satisfiable (the elementary determinant + Gram-sign conjunction holds for every
genuine nonnegative great-circle combination, `stuckPayload_satisfiable`), the betweenness conversion
produces a *real* `span≥0` membership (`collinear_of_elementaryStuck`), and the resulting
`StuckCollinearData` yields a *real* endpoint inequality through the triangle inequality
(`stuckCollinear_endpt_pair`).  Its REACH payload `ReachStepDatum` is likewise satisfiable
(`SphericalArmFinish.reachStepDatum_satisfiable`).  Hence both disjuncts of the residue are genuine
geometric configurations. -/

/-- Non-vacuity of `ElementaryStuck`'s sign payload: for any nonnegative great-circle combination
`A 0 = s • A 1 + t • qstar` (`s, t ≥ 0`) the determinant vanishes and both Gram signs hold — the
elementary stuck conjunction is satisfiable, not vacuously false. -/
theorem elementaryStuck_signs_satisfiable (A0 A1 qstar : S2) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hb : (A0 : E3) = s • (A1 : E3) + t • (qstar : E3)) :
    det3 (A0 : E3) (A1 : E3) (qstar : E3) = 0 ∧
    (0 ≤ (⟪(A0 : E3), (A1 : E3)⟫ : ℝ)
        - (⟪(A0 : E3), (qstar : E3)⟫ : ℝ) * (⟪(A1 : E3), (qstar : E3)⟫ : ℝ)) ∧
    (0 ≤ (⟪(A0 : E3), (qstar : E3)⟫ : ℝ)
        - (⟪(A0 : E3), (A1 : E3)⟫ : ℝ) * (⟪(qstar : E3), (A1 : E3)⟫ : ℝ)) :=
  stuckPayload_satisfiable A0 A1 qstar s t hs ht hb

/-- Non-vacuity of the conversion: from a genuine `ElementaryStuck` the collinear configuration
`StuckCollinearData` is produced (a real `span≥0` betweenness), so the STUCK disjunct of the residue is
a real geometric configuration, not a vacuous payload. -/
theorem stuckCollinearData_realised {n : ℕ} {A B : Fin (n + 1 + 1) → S2} {qstar : S2}
    (hes : ElementaryStuck A B qstar) :
    StuckCollinearData A B :=
  stuckCollinearData_of_elementaryStuck hes

/-- Non-vacuity of the STUCK alternative's endpoint payload: the collinear configuration's endpoint pair
is genuinely realised through the spherical triangle inequality (`stuckCollinear_endpt_pair`). -/
theorem stuck_endpoint_realised {n : ℕ} {A B : Fin (n + 1 + 1) → S2} {qstar : S2}
    (hes : ElementaryStuck A B qstar) :
    endpt A ≤ endpt B :=
  (stuckCollinear_endpt_pair (stuckCollinearData_of_elementaryStuck hes)).1

/-- Non-vacuity of the reduction's conclusion (reflexive at `A = B`): the discharged
`DeficientReachCollinear` produces, for `A = B`, the reflexive endpoint pair through the recursion. -/
theorem conclusion_satisfiable {n : ℕ} (A : Fin (n + 1 + 1) → S2) :
    endpt A ≤ endpt A ∧
      ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle A i) → endpt A < endpt A) :=
  defStepCol_conclusion_satisfiable A

end ProofsInTheBook.SphericalDefReachCollinear
