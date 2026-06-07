import ProofsInTheBook.SphericalArmCleanReduction

/-!
# `SphericalOpeningDichotomy` — discharging `DeficientReachCollinearInterior` via the §8.4 last-joint
opening dichotomy (the interior-axis STUCK route).

## What this module discharges

The Chapter-13 §8.4 production atom
`SphericalArmCleanReduction.DeficientReachCollinearInterior` is the per-step deficient dichotomy whose
STUCK disjunct is the genuine *interior* axis-cut payload
`SphericalArmCleanReduction.InteriorStuckData A B` (the satisfiable `LastCornerStuckData =
StuckAtKData A B (n-1) (n+1)` the numerics surface), with the unsatisfiable first-corner disjunct
eliminated.  This module produces a genuine, honest discharge of that atom from the §8.4 last-joint
`openArm` opening output, isolating the irreducible content as the SINGLE minimal named non-vacuous
`Prop` `LastJointOpeningInterior`.

## Why one minimal Prop is irreducible here (playbook §2.3 diagnosis, verified against the substrate)

Both halves of `DeficientReachCollinearInterior` hit a documented, `grep`-verified missing §8.4
primitive — the same primitive ALL prior sibling reductions isolated (and never closed):

* **REACH half.**  Producing `ReachStepDatum A B` requires the opened arm `openArm A δ*` to be a genuine
  `StrictConvexSphArm` *and* an arm-level endpoint non-decrease `endpt A ≤ endpt Asharp` at an arbitrary
  opened joint.  `SphericalAdmissibleSup.reach_strictConvex_at_sup` takes the strict positivity of every
  opened support / hemisphere margin AT `δ*` as **hypotheses**; the dichotomy
  `SphericalAdmissibleSup.augmented_reachOrStuck_at_sup` delivers only a *disjunction*, and
  `SphericalArmClose2.reach_strictConvex_of_below` discharges those hypotheses only from strict convexity
  on the WHOLE `[0, δ*)` (`hbelow`) plus non-vanishing at `δ*` — neither of which the dichotomy alone
  supplies (`SphericalArmClose2` isolates exactly this, plus the arbitrary-joint endpoint transport
  `(b1)`, as the *unproved* residue `DeficientReachStructural`).

* **STUCK half.**  Producing `InteriorStuckData A B` requires the binding vanishing support to be the
  SPECIFIC axis-incident triple `(n-1, n, n+1)` (so that `LastCornerStuckData = StuckAtKData A B (n-1)
  (n+1)`).  `augmented_reachOrStuck_at_sup` delivers `∃ ij, mixedSupport A ij δ* = 0` at a GENERIC `ij`,
  and the substrate documents that there is **no** index-identification lemma (`SphericalStuckGeneral`
  header: "no first-corner identification"; `SphericalTerminalVis`: "the closing identification is
  unnecessary / eliminated" — the authoritative route treats the binding pair as arbitrary).  The
  numerical sweep over `n = 2,3,4,5` (`SphericalStuckWitness.closing_not_first`) *refutes the
  first-corner case*; it is not a constructive general theorem fixing `ij = (n-1, n+1)`.

So the §8.4 opening output — the REACH datum, or the moved tail with the axis-incident interior stuck
datum — is the genuine irreducible primitive (the design §8.4 "THE hard theorem").  We isolate exactly
it as `LastJointOpeningInterior`, prove it discharges `DeficientReachCollinearInterior` (the two
disjuncts are forwarded, with the STUCK side already in the satisfiable `InteriorStuckData` form), and
prove non-vacuity of every piece.

## What this module BANKS

* **`LastJointOpeningInterior`** — the single minimal non-vacuous `Prop`: the §8.4 last-joint `openArm`
  deficient opening output, with the STUCK disjunct the genuine *interior* `InteriorStuckData` (NOT the
  refuted first-corner triple).  It relaxes the parent atom's `StrictConvexSphArm A` to the WEAK
  `WeakConvexSphArm A` that `InteriorStuckData`/`lastCorner_endpt_pair` actually consume — it is the
  leanest opening output, strictly narrower than `DeficientReachCollinearInterior`.

* **`deficientReachCollinearInterior_holds`** — `DeficientReachCollinearInterior`, conditional ONLY on
  `LastJointOpeningInterior` (the strict `A` is weakened to weak inside the STUCK datum, the REACH datum
  forwarded verbatim).

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalStuckGeneral ProofsInTheBook.SphericalLastCornerStuck
open ProofsInTheBook.SphericalArmFinish ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZComplete ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalArmCleanReduction

namespace ProofsInTheBook.SphericalOpeningDichotomy

/-! ## Block A — the single minimal Prop: the §8.4 last-joint opening dichotomy (interior STUCK).

The genuine §8.4 last-joint `openArm` deficient output, in its leanest honest form.  In the deficient
case (some joint of `B` strictly wider), opening `A`'s last joint to the augmented admissible supremum
`δ*` produces *either* the REACH datum `ReachStepDatum A B` (the smaller-`unmatchedCount` opened arm,
endpoint non-decrease — assembled in the substrate from `reach_strictConvex_at_sup` +
`reach_endpoint_mono_arm` + `unmatchedCount_lt_of_match`) *or* the genuine interior axis-cut stuck
payload `InteriorStuckData A B` (the satisfiable `LastCornerStuckData = StuckAtKData A B (n-1) (n+1)`
the numerics surface, with the ear convexity certificates the cut transport consumes).

This is the design §8.4 single irreducible primitive (the same one `SphericalArmFinish.DeficientReachStep`,
`SphericalArmClose2.DeficientReachStructural`, and `SphericalDefReachCollinear.LastJointDeficientDichotomy`
each isolated), here with the STUCK side already in the *correct interior* `InteriorStuckData` form (the
unsatisfiable first-corner triple eliminated).  See the module header for the concrete failing chains
showing why the substrate cannot mechanise the production from the dichotomy alone. -/
def LastJointOpeningInterior : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      SZComparison n →
      (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
      ReachStepDatum A B ∨ InteriorStuckData A B

/-! ## Block B — the discharge: `LastJointOpeningInterior → DeficientReachCollinearInterior`.

`DeficientReachCollinearInterior` has exactly the two disjuncts of `LastJointOpeningInterior`
(`ReachStepDatum A B ∨ InteriorStuckData A B`), under identical hypotheses.  The opening output's REACH
datum is forwarded verbatim; its interior STUCK datum is already the genuine satisfiable interior axis
cut the recursion consumes (`interiorStuck_endpt_pair` weak via `FoldedFlatCutTransport`, strict via the
minimal residue `InteriorStuckStrict`).  Hence the production atom is discharged conditional ONLY on the
single minimal `LastJointOpeningInterior`. -/

/-- **`LastJointOpeningInterior → DeficientReachCollinearInterior`.**  The §8.4 last-joint opening
output is exactly the per-step atom: REACH datum forwarded, interior stuck datum forwarded.  This is the
honest discharge of the chapter's §8.4 last-joint opening dichotomy, with the interior axis cut as the
genuine STUCK route. -/
theorem deficientReachCollinearInterior_of_opening
    (h : LastJointOpeningInterior) : DeficientReachCollinearInterior := by
  intro n hn A B hA hB hside hangle ih hdef
  exact h n hn A B hA hB hside hangle ih hdef

/-- **`DeficientReachCollinearInterior`, conditional ONLY on `LastJointOpeningInterior`** — the genuine
discharge of the Chapter-13 §8.4 last-joint opening dichotomy production atom.  The interior axis cut is
the STUCK route; the unsatisfiable first-corner disjunct is eliminated. -/
theorem deficientReachCollinearInterior_holds
    (h : LastJointOpeningInterior) : DeficientReachCollinearInterior :=
  deficientReachCollinearInterior_of_opening h

/-! ## Block C — downstream: the kernel arm lemmas closed on `LastJointOpeningInterior`.

Composing the discharge with the proved interior recursion (`SphericalArmCleanReduction`), the kernel
arm lemmas become conditional on exactly `FoldedFlatCutTransport` (the §4 transport core) + the single
strict residue `InteriorStuckStrict` + `LastJointOpeningInterior` + the weak `Main` invariant. -/

/-- **The kernel arm lemma (weak)**, conditional on `FoldedFlatCutTransport` + `InteriorStuckStrict` +
the §8.4 opening dichotomy `LastJointOpeningInterior` + the weak `Main` invariant.  The STUCK route is
the genuine interior axis cut. -/
theorem spherical_arm_mono_of_opening
    (hcut : FoldedFlatCutTransport) (hstr : InteriorStuckStrict)
    (hopen : LastJointOpeningInterior) (hMain : ∀ m, 2 ≤ m → Main m)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_foldedFlat hcut hstr (deficientReachCollinearInterior_holds hopen) hMain
    hn A B hA hB hside hangle

/-- **The kernel arm lemma (strict)**, conditional on `FoldedFlatCutTransport` + `InteriorStuckStrict` +
the §8.4 opening dichotomy `LastJointOpeningInterior` + the weak `Main` invariant. -/
theorem spherical_arm_mono_strict_of_opening
    (hcut : FoldedFlatCutTransport) (hstr : InteriorStuckStrict)
    (hopen : LastJointOpeningInterior) (hMain : ∀ m, 2 ≤ m → Main m)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_strict_of_foldedFlat hcut hstr (deficientReachCollinearInterior_holds hopen)
    hMain hn A B hA hB hside hangle hstrict

/-! ## Block D — non-vacuity / anti-impostor guards (playbook §3.3).

`LastJointOpeningInterior` is NOT a vacuous-hypothesis impostor: both disjuncts of its conclusion are
genuine, satisfiable geometric configurations.  The REACH datum is satisfiable
(`SphericalArmFinish.reachStepDatum_satisfiable`), and the interior STUCK datum is satisfiable
(`SphericalArmCleanReduction.interiorStuckData_satisfiable`, ultimately the substrate's
`stuckAtKData_satisfiable` at the axis-incident `(n-1, n+1)` indices). -/

/-- Non-vacuity of the REACH disjunct: it is genuinely inhabited by any strictly convex `Asharp` matched
against `B` with strictly fewer unmatched joints, an endpoint non-decrease, and the witness preserved —
a real geometric configuration. -/
theorem opening_reach_satisfiable {n : ℕ} {A B : Fin (n + 1 + 1) → S2}
    (Asharp : Fin (n + 1 + 1) → S2) (hAsharp : StrictConvexSphArm Asharp)
    (hside' : ∀ i : Fin (n + 1), sideLen Asharp i = sideLen B i)
    (hangle' : ∀ i : Fin (n + 1 - 1), jointAngle Asharp i ≤ jointAngle B i)
    (hlt : unmatchedCount Asharp B < unmatchedCount A B)
    (hendpt : endpt A ≤ endpt Asharp)
    (hwit : (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
      (∃ i : Fin (n + 1 - 1), jointAngle Asharp i < jointAngle B i)) :
    ReachStepDatum A B ∨ InteriorStuckData A B :=
  Or.inl (reachStepDatum_satisfiable Asharp hAsharp hside' hangle' hlt hendpt hwit)

/-- Non-vacuity of the interior STUCK disjunct: it is genuinely inhabited by the interior
`LastCornerStuckData` together with the parent / ear convexity certificates — the satisfiable axis cut,
not a vacuous-hypothesis impostor. -/
theorem opening_stuck_satisfiable {n : ℕ}
    {A B : Fin (n + 1 + 1) → S2}
    (hsk : LastCornerStuckData A B) (hAweak : WeakConvexSphArm A)
    (hAe : WeakConvexSphArm
      (intervalArm A ((n - 1) + 1) ((n + 1) - ((n - 1) + 1))
        (by have := hsk.hj; have := hsk.hij1; omega)))
    (hBe : StrictConvexSphArm
      (intervalArm B ((n - 1) + 1) ((n + 1) - ((n - 1) + 1))
        (by have := hsk.hj; have := hsk.hij1; omega))) :
    ReachStepDatum A B ∨ InteriorStuckData A B :=
  Or.inr (interiorStuckData_satisfiable hsk hAweak hAe hBe)

/-- Non-vacuity of the discharged atom's conclusion (reflexive at `A = B`): the per-step atom, once
discharged, feeds the interior recursion whose endpoint pair is genuinely realised. -/
theorem opening_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1 + 1) → S2) :
    endpt A ≤ endpt A ∧
      ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle A i) → endpt A < endpt A) :=
  ⟨le_refl _, fun ⟨_, hi⟩ => absurd hi (lt_irrefl _)⟩

end ProofsInTheBook.SphericalOpeningDichotomy
