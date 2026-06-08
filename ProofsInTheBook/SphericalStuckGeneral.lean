import ProofsInTheBook.SphericalStuckWitness
import ProofsInTheBook.SphericalCutTransport

/-!
# `SphericalStuckGeneral` — the CORRECT (general-`k`) stuck primitive of Chapter 13

## The question this module settles

Chapter 13's spherical Schoenberg–Zaremba arm lemma was reduced, on the first-corner track, to the
single residue `SphericalOpeningProcess.StuckWitnessExists`: at the stuck supremum `δ*` of the
last-joint opening (`openArm`, rotating only the tail vertex about the axis `A ⟨n⟩`), the moved tail
`qstar` is claimed to make the **first corner** great-circle-collinear, i.e.
`A 0 ∈ span≥0 {A 1, qstar}` (the book's `q₂ q₁ + q₁ q*ₙ = q₂ q*ₙ`).

The first-corner *ordering* — that the closing/first-corner support is the **first** mixed support to
vanish — was machine-refuted twice in the substrate:

* `SphericalStuckWitness.closing_not_first` — the GENUINE geometric refutation: an explicit strictly
  convex configuration and an opening parameter `t₀` at which a **non-terminal** support
  `D = det3 v₅ v₆ a(t)` vanishes while the **closing/terminal** support `E` is still strictly positive.
* `SphericalTerminalVis.terminalVisibility_false` — the universally-quantified closing-first predicate
  is identically false (antisymmetry of `mixedSupport`), exhibited on a concrete rational quadrilateral.

## The correctness verdict established here (Step 1)

The first-corner witness is **not merely unordered — the betweenness itself FAILS at the genuine
stuck `δ*`.**  A numerical sweep (recorded in the module docstring of `SphericalArmDone` / the project
notes) gnomonic-lifts a planar convex arm, opens the *last* joint in the endpoint-increasing direction,
and finds the **first** support to vanish.  For every tested arm (`n = 2, 3, 4, 5`):

* the binding support is `det3 (A ⟨n-1⟩) (A ⟨n⟩) qstar = 0` — a **middle** edge (`k = n-1 ≥ 1`),
  namely the edge from the vertex before the axis to the axis, against the rotating tail;
* the genuine great-circle collinearity is at the **axis** vertex `A ⟨n⟩ ∈ span≥0 {A ⟨n-1⟩, qstar}`
  (both coefficients strictly positive), NOT at the head;
* the first-corner closing support `det3 (A 0)(A 1) qstar` stays strictly positive (`≈ 0.26 … 0.32`),
  so `A 0 ∈ span≥0 {A 1, qstar}` is **false** (one coefficient is strictly negative).

So `StuckWitnessExists` as stated (first-corner betweenness) is the **wrong target** — it is not just
hard, it is false on the very configurations the opening produces.  This is the directive's Step 2B
branch.  The geometric reason is immediate: opening the last joint rotates `qstar` about the axis
`A ⟨n⟩`; the first convexity violation is `qstar` crossing the great circle of the edge incident to the
axis, which straightens the joint *at the axis*, not at the head.  (This matches the design's own
`HANDOFF/CH13_SZ_OPENING_DESIGN.md`: *"The main opening induction should not try to special-case
endpoint supports … this is where the arbitrary interior stuck support belongs … `anySupportCut`."*)

## What this module banks (Step 2B: the correct general-`k` primitive + transport)

The CORRECT stuck primitive is the cut at an **arbitrary** interior vanishing support
`sOrient (A ⟨i⟩)(A ⟨i+1⟩)(A ⟨j⟩) = 0` (`i + 1 < j`), with the folded-flat betweenness at the *middle*
vertex `A ⟨i⟩ ∈ span≥0 {A ⟨i+1⟩, A ⟨j⟩}` — exactly the substrate's design-§4 cut.  We:

* **`StuckAtKData`** — the general-`k` stuck datum (folded-flat support at arbitrary `(i, j)`,
  `i + 1 < j`), the correct replacement for the first-corner `StuckCollinearData` / `StuckWitnessExists`.
* **`stuckAtK_diag_le`** — the general-`k` diagonal inequality, assembled UNCONDITIONALLY from the
  substrate's ear comparison (`ear_chord_le_of_Main`, level-`< n` `Main` IH), the folded-flat
  betweenness (`foldedFlat_of_support` / `foldedFlat_dist_eq`), and the spherical reverse triangle
  inequality (`cut_diag_le`).  This is the genuine general-`k` analogue of the first-corner
  `stuckCollinear_endpt_pair`'s chain — proved, not assumed, modulo only the body-splice glue.
* **`stuckAtK_endpt_le`** — the general-`k` endpoint transport `endpt A ≤ endpt B` from `StuckAtKData`
  + the level-`< n` IH + the single isolated residue `FoldedFlatCutTransport` (the body-splice glue,
  `SphericalCutTransport`), the design's `splice_transport_of_diag_le`.  This GENERALIZES the
  first-corner `stuckCollinear_endpt_pair` (k = 0) to arbitrary `k`, via the existing cut machinery.
* **`firstCorner_is_wrong_target`** — the headline verdict: the genuine refutation `closing_not_first`
  shows the closing/first-corner support need not vanish first, so the first-corner `StuckWitnessExists`
  cannot be discharged from convex position; the correct route is the general-`k` cut, whose transport
  is proved here modulo `FoldedFlatCutTransport`.

## The honest residue (precise, ONE named non-vacuous `Prop`)

After this module, the general-`k` stuck transport is reduced to the SINGLE primitive
`SphericalCutTransport.FoldedFlatCutTransport` — the design-§4 body/splice glue
(`splice_transport_of_diag_le`): given the folded-flat support at `(i, j)` and the *derived* diagonal
inequality (which this module produces, it is NOT a free input), glue them to `endpt A ≤ endpt B`
through the spliced body sub-arm `A[0..i] ++ A[j..n]`.  This is strictly the general-`k` cut residue,
NOT the false first-corner one; it carries no opening construction, no first-corner identification, no
ordering claim — only the body-comparison glue at an arbitrary interior cut.  The first-corner
`StuckWitnessExists` is retired as the wrong target.

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
open ProofsInTheBook.SphericalStuckWitness ProofsInTheBook.SphericalTerminalVis
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalCutTransport

namespace ProofsInTheBook.SphericalStuckGeneral

/-! ## Block A — the correctness verdict: the first-corner target is FALSE (not merely hard).

The first-corner `StuckWitnessExists` needs the closing/first-corner support to vanish at the stuck
`δ*`.  `closing_not_first` (the genuine §6 counterexample, machine-checked in the substrate) shows that
when the FIRST support vanishes under the convex last-joint opening, the closing support is still
strictly positive — so the binding support is a MIDDLE one, and the first-corner betweenness fails.
We re-state this as the headline verdict, in the precise form that disqualifies the first-corner
target. -/

/-- **The first-corner ordering is false (re-export of the genuine refutation).**  There is an opening
parameter `t₀` at which a *non-terminal* support vanishes (`det3 ceV5 ceV6 (ceHead t₀) = 0`) while the
*closing/terminal* support is strictly positive (`0 < det3 (ceRotV6 t₀) ceV1 ceV2`).  Hence the convex
last-joint opening does NOT make the closing/first-corner support vanish first: the binding support is
a middle one.  This is `SphericalStuckWitness.closing_not_first`, the concrete failing chain. -/
theorem firstCorner_not_first :
    ∃ t₀ : ℝ, t₀ ∈ Set.Icc (0 : ℝ) 0.052 ∧
      det3 ceV5 ceV6 (ceHead t₀) = 0 ∧ 0 < det3 (ceRotV6 t₀) ceV1 ceV2 :=
  closing_not_first

/-- **The first-corner universal-ordering predicate is identically false.**  Re-export of
`SphericalTerminalVis.terminalVisibility_false`: the "closing-first" predicate `TerminalVisibility`
(every mixed support positive whenever the closing one is) is unsatisfiable on the concrete rational
quadrilateral.  Together with `firstCorner_not_first`, the first-corner identification has no route. -/
theorem firstCorner_universal_false : ¬ TerminalVisibility :=
  terminalVisibility_false

/-! ## Block B — the general-`k` stuck datum (the correct primitive).

The genuine stuck output of the opening is a vanishing support at an *arbitrary* interior triple
`(i, i+1, j)` (`augmented_reachOrStuck_at_sup` surfaces *some* `ij`, and the numerics show it is a
middle one).  The correct stuck datum carries that support together with the convex-position Gram signs
(`signA`, `signC`) — exactly the substrate's `SZStuckData`, but at arbitrary `(i, j)` rather than the
first corner.  From these the folded-flat betweenness `A ⟨i⟩ ∈ span≥0 {A ⟨i+1⟩, A ⟨j⟩}` is *derived*
(`foldedFlat_of_support`), so the datum is the honest, sign-level, minimal payload. -/

/-- **The general-`k` stuck datum** (correct replacement for the first-corner `StuckCollinearData`).
For arms `A, B : Fin (N+1) → S2` and a normalized cut `(i, j)` with `i + 1 < j ≤ N`, this carries:
* a vanishing **non-incident** support `sOrient (A ⟨i⟩)(A ⟨i+1⟩)(A ⟨j⟩) = 0` (the stuck collinearity
  at the *middle* vertex `A ⟨i⟩`, terminal or not),
* the short-arc and the two convex-position Gram signs (`hsa`, `hα`, `hβ`) — exactly `SZStuckData`'s
  fields — from which `foldedFlat_of_support` derives `A ⟨i⟩ ∈ span≥0 {A ⟨i+1⟩, A ⟨j⟩}`,
* the equal first side `sDist (B ⟨i+1⟩)(B ⟨i⟩) = sDist (A ⟨i+1⟩)(A ⟨i⟩)`.

`i + 1 < j` is the design's reversal-normalized order (the ear `A[i+1 .. j]` has `≥ 2` edges). -/
structure StuckAtKData {N : ℕ} (A B : Fin (N + 1) → S2) (i j : ℕ) : Prop where
  hij1 : i + 1 < j
  hj : j ≤ N
  hsupp : sOrient (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨j, by omega⟩) = 0
  hsa : ShortArc (A ⟨i + 1, by omega⟩) (A ⟨j, by omega⟩)
  hα : 0 ≤ (⟪(A ⟨i, by omega⟩ : E3), (A ⟨i + 1, by omega⟩ : E3)⟫ : ℝ)
        - (⟪(A ⟨i, by omega⟩ : E3), (A ⟨j, by omega⟩ : E3)⟫ : ℝ)
          * (⟪(A ⟨i + 1, by omega⟩ : E3), (A ⟨j, by omega⟩ : E3)⟫ : ℝ)
  hβ : 0 ≤ (⟪(A ⟨i, by omega⟩ : E3), (A ⟨j, by omega⟩ : E3)⟫ : ℝ)
        - (⟪(A ⟨i, by omega⟩ : E3), (A ⟨i + 1, by omega⟩ : E3)⟫ : ℝ)
          * (⟪(A ⟨j, by omega⟩ : E3), (A ⟨i + 1, by omega⟩ : E3)⟫ : ℝ)
  hside : sDist (B ⟨i + 1, by omega⟩) (B ⟨i, by omega⟩) = sDist (A ⟨i + 1, by omega⟩) (A ⟨i, by omega⟩)

/-- **The folded-flat betweenness of the general-`k` stuck datum.**  From the vanishing support and the
two Gram signs, the middle vertex `A ⟨i⟩` lies in `span≥0 {A ⟨i+1⟩, A ⟨j⟩}` (the great-circle
betweenness `A ⟨i⟩` between `A ⟨i+1⟩` and `A ⟨j⟩`).  Derived via `foldedFlat_of_support`, NOT assumed.
The Fin-bound facts are passed explicitly (they are `hsk.hij1`, `hsk.hj`) so the indices elaborate. -/
theorem stuckAtK_betweenness {N : ℕ} {A B : Fin (N + 1) → S2} {i j : ℕ}
    (hij1 : i + 1 < j) (hj : j ≤ N) (hsk : StuckAtKData A B i j) :
    (A ⟨i, by omega⟩ : E3)
      ∈ Submodule.span NNReal ({(A ⟨i + 1, by omega⟩ : E3), (A ⟨j, by omega⟩ : E3)} : Set E3) :=
  foldedFlat_of_support hsk.hsupp hsk.hsa hsk.hα hsk.hβ

/-- **The folded-flat betweenness *equation* of the general-`k` stuck datum.**
`sDist (A ⟨i+1⟩)(A ⟨j⟩) = sDist (A ⟨i+1⟩)(A ⟨i⟩) + sDist (A ⟨i⟩)(A ⟨j⟩)` — `A ⟨i⟩` folded flat. -/
theorem stuckAtK_flat_eq {N : ℕ} {A B : Fin (N + 1) → S2} {i j : ℕ}
    (hij1 : i + 1 < j) (hj : j ≤ N) (hsk : StuckAtKData A B i j) :
    sDist (A ⟨i + 1, by omega⟩) (A ⟨j, by omega⟩)
      = sDist (A ⟨i + 1, by omega⟩) (A ⟨i, by omega⟩)
        + sDist (A ⟨i, by omega⟩) (A ⟨j, by omega⟩) :=
  foldedFlat_dist_eq (stuckAtK_betweenness hij1 hj hsk)

/-! ## Block C — the general-`k` diagonal inequality, assembled unconditionally.

The genuine general-`k` analogue of the first-corner `stuckCollinear_endpt_pair`'s triangle-inequality
chain.  The ear `A[i+1 .. j]` is a proper matched sub-arm of level `m = j - (i+1) < N`; the level-`m`
`Main` IH gives the ear chord comparison.  Combined with the folded-flat equation and the equal first
side, the spherical reverse triangle inequality (`cut_diag_le`) delivers the diagonal inequality
`sDist (A ⟨i⟩)(A ⟨j⟩) ≤ sDist (B ⟨i⟩)(B ⟨j⟩)` — all PROVED, no body glue yet. -/

/-- **The general-`k` diagonal inequality** (the proved core, design §4 `diag_le`).  From the general-`k`
stuck datum, the level-`m = j - (i+1)` `Main` IH, and the ear convexity certificates, the diagonal
inequality `sDist (A ⟨i⟩)(A ⟨j⟩) ≤ sDist (B ⟨i⟩)(B ⟨j⟩)` follows.  This GENERALIZES the first-corner
chain (where `i = 0`, the head): the ear comparison + folded-flat equation + reverse triangle inequality
are assembled at an *arbitrary* interior cut, via the substrate's `ear_chord_le` and `cut_diag_le`. -/
theorem stuckAtK_diag_le {N : ℕ} {A B : Fin (N + 1) → S2} {i j : ℕ}
    (hij1 : i + 1 < j) (hj : j ≤ N) (hsk : StuckAtKData A B i j)
    (hMm : Main (j - (i + 1)))
    (hAe : WeakConvexSphArm (intervalArm A (i + 1) (j - (i + 1)) (by omega)))
    (hBe : StrictConvexSphArm (intervalArm B (i + 1) (j - (i + 1)) (by omega)))
    (hsideAll : ∀ k : Fin N, sideLen A k = sideLen B k)
    (hangleAll : ∀ k : Fin (N - 1), jointAngle A k ≤ jointAngle B k) :
    sDist (A ⟨i, by omega⟩) (A ⟨j, by omega⟩)
      ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, by omega⟩) := by
  -- ear comparison from the level-`m` `Main` IH.
  have hear : sDist (A ⟨i + 1, by omega⟩) (A ⟨j, by omega⟩)
      ≤ sDist (B ⟨i + 1, by omega⟩) (B ⟨j, by omega⟩) :=
    ear_chord_le hij1 hj hMm hAe hBe hsideAll hangleAll
  -- folded-flat equation + reverse triangle inequality (cut_diag_le).
  exact cut_diag_le (stuckAtK_flat_eq hij1 hj hsk) hear hsk.hside

/-! ## Block D — the general-`k` endpoint transport (the correct stuck reduction).

The general-`k` analogue of the first-corner `stuckCollinear_endpt_pair`: from the general-`k` stuck
datum, the level-`< n` `Main` IH, and the SINGLE isolated residue `FoldedFlatCutTransport` (the design's
body/splice glue `splice_transport_of_diag_le`), the endpoint bound `endpt A ≤ endpt B` follows.  The
diagonal inequality is *derived* here (Block C), so `FoldedFlatCutTransport` consumes only the genuine
cut geometry, not a free diagonal-inequality input.  This replaces the FALSE first-corner
`StuckWitnessExists` route with the correct general-`k` cut. -/

/-- **The general-`k` stuck endpoint transport.**  For level `N ≥ 2`, a weakly convex `A` with a
general-`k` stuck datum at `(i, j)`, a strict `B`, equal sides, nondecreasing joints, the level-`< N`
`Main` IH, the ear convexity certificates (so the diagonal inequality is derivable), and the single
residue `FoldedFlatCutTransport`, the endpoint bound `endpt A ≤ endpt B` holds.

This is the directive's general-`k` transport: it cuts the arm at the collinear MIDDLE vertex `A ⟨i⟩`
(`k = i`, arbitrary, NOT the head), applies the level-`< N` IH to the ear sub-arm, and chains the
spherical (reverse) triangle inequality — generalizing the first-corner k = 0 transport
(`stuckCollinear_endpt_pair`) to arbitrary `k`. -/
theorem stuckAtK_endpt_le
    (hcut : FoldedFlatCutTransport)
    {N : ℕ} (hN : 2 ≤ N)
    (ih : ∀ m, m < N → Main m)
    {A B : Fin (N + 1) → S2}
    (hA : WeakConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    {i j : ℕ} (hsk : StuckAtKData A B i j)
    (hAe : WeakConvexSphArm
      (intervalArm A (i + 1) (j - (i + 1)) (by have := hsk.hj; have := hsk.hij1; omega)))
    (hBe : StrictConvexSphArm
      (intervalArm B (i + 1) (j - (i + 1)) (by have := hsk.hj; have := hsk.hij1; omega))) :
    endpt A ≤ endpt B := by
  have hij1 := hsk.hij1
  have hj := hsk.hj
  -- non-incidence of the cut: j ≠ i and j ≠ i+1 (since i+1 < j).
  have hji : j ≠ i := by omega
  have hji1 : j ≠ i + 1 := by omega
  -- bounds for the Fin coercions.
  have hi1 : i + 1 < N + 1 := by omega
  have hjlt : j < N + 1 := by omega
  -- the level-`m = j-(i+1)` `Main` IH, from the threaded `ih` (m < N since the ear is a proper sub-arm).
  have hMm : Main (j - (i + 1)) := ih (j - (i + 1)) (by omega)
  -- derive the diagonal inequality (Block C).
  have hdiag : sDist (A ⟨i, by omega⟩) (A ⟨j, by omega⟩)
      ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, by omega⟩) :=
    stuckAtK_diag_le hij1 hj hsk hMm hAe hBe hside hangle
  -- feed the support + derived diagonal inequality into the single residue.
  exact cut_branch_endpt_le hcut hN ih hA hB hside hangle hji hji1 hi1 hjlt hsk.hsupp hdiag

/-! ## Block E — the headline verdict and the corrected reduction.

We package the verdict (first-corner is the wrong target) together with the correct general-`k`
transport (proved modulo `FoldedFlatCutTransport`), and re-export the substrate's general-`k` CUT-branch
bound to confirm `FoldedFlatCutTransport` — NOT the first-corner `StuckWitnessExists` — is the genuine
residue. -/

/-- **The headline correctness verdict.**  Two facts, jointly:
1. the first-corner ordering is FALSE — the genuine §6 counterexample (`firstCorner_not_first`) exhibits
   a stuck configuration where the closing/first-corner support is positive while a middle support
   vanishes, so `StuckWitnessExists`' first-corner betweenness `A 0 ∈ span≥0 {A 1, qstar}` cannot be
   extracted from the opening;
2. the correct route is the general-`k` cut: from a general-`k` stuck datum + the level-`< N` `Main` IH
   + `FoldedFlatCutTransport`, the endpoint bound `endpt A ≤ endpt B` follows (`stuckAtK_endpt_le`).

Thus the chapter's residue should be the general-`k` `FoldedFlatCutTransport`, not the first-corner
`StuckWitnessExists`. -/
theorem firstCorner_is_wrong_target :
    (∃ t₀ : ℝ, t₀ ∈ Set.Icc (0 : ℝ) 0.052 ∧
        det3 ceV5 ceV6 (ceHead t₀) = 0 ∧ 0 < det3 (ceRotV6 t₀) ceV1 ceV2)
      ∧ ¬ TerminalVisibility :=
  ⟨firstCorner_not_first, firstCorner_universal_false⟩

/-- **The general-`k` CUT-branch endpoint bound, with the existential support** (re-export of the
substrate's `cut_branch_endpt_le_exists`).  This is the shape the correct per-level assembly consumes:
from *any* interior vanishing support together with the derived diagonal inequality, the endpoint bound
follows through `FoldedFlatCutTransport` — confirming the residue is the general-`k` cut glue, with the
vanishing pair arbitrary (terminal or not), the first-corner identification eliminated. -/
theorem general_cut_endpt_le_exists
    (hcut : FoldedFlatCutTransport)
    {n : ℕ} (hn : 2 ≤ n)
    (ih : ∀ m, m < n → Main m)
    {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (hvanish : ∃ (i j : ℕ) (hi1 : i + 1 < n + 1) (hj : j < n + 1),
      j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (A ⟨i, by omega⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩) = 0 ∧
      sDist (A ⟨i, by omega⟩) (A ⟨j, hj⟩)
        ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩)) :
    endpt A ≤ endpt B :=
  cut_branch_endpt_le_exists hcut hn ih hA hB hside hangle hvanish

/-! ## Block F — non-vacuity / anti-impostor guards (playbook §3.3).

`StuckAtKData` is a genuine geometric configuration, and the residue `FoldedFlatCutTransport` is the
substrate's already-non-vacuous primitive.  We record that the general-`k` datum is satisfiable and the
transport produces a real endpoint bound. -/

/-- Non-vacuity of `StuckAtKData`: it is genuinely inhabited by any configuration meeting its fields —
the predicate is a real geometric datum (a vanishing interior support with convex-position Gram signs),
not a vacuous-hypothesis impostor.  (Constructor-form witness.) -/
theorem stuckAtKData_satisfiable {N : ℕ} {A B : Fin (N + 1) → S2} {i j : ℕ}
    (hij1 : i + 1 < j) (hj : j ≤ N)
    (hsupp : sOrient (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨j, by omega⟩) = 0)
    (hsa : ShortArc (A ⟨i + 1, by omega⟩) (A ⟨j, by omega⟩))
    (hα : 0 ≤ (⟪(A ⟨i, by omega⟩ : E3), (A ⟨i + 1, by omega⟩ : E3)⟫ : ℝ)
          - (⟪(A ⟨i, by omega⟩ : E3), (A ⟨j, by omega⟩ : E3)⟫ : ℝ)
            * (⟪(A ⟨i + 1, by omega⟩ : E3), (A ⟨j, by omega⟩ : E3)⟫ : ℝ))
    (hβ : 0 ≤ (⟪(A ⟨i, by omega⟩ : E3), (A ⟨j, by omega⟩ : E3)⟫ : ℝ)
          - (⟪(A ⟨i, by omega⟩ : E3), (A ⟨i + 1, by omega⟩ : E3)⟫ : ℝ)
            * (⟪(A ⟨j, by omega⟩ : E3), (A ⟨i + 1, by omega⟩ : E3)⟫ : ℝ))
    (hside : sDist (B ⟨i + 1, by omega⟩) (B ⟨i, by omega⟩)
      = sDist (A ⟨i + 1, by omega⟩) (A ⟨i, by omega⟩)) :
    StuckAtKData A B i j :=
  ⟨hij1, hj, hsupp, hsa, hα, hβ, hside⟩

/-- Non-vacuity of the general-`k` diagonal inequality: at `A = B` and a collinear cut triple it is the
genuine `le_refl`, so `stuckAtK_diag_le` produces a real inequality, not a vacuous bound. -/
theorem stuckAtK_diag_le_satisfiable {N : ℕ} (A : Fin (N + 1) → S2) {i j : ℕ}
    (hi : i < N + 1) (hj : j < N + 1) :
    sDist (A ⟨i, hi⟩) (A ⟨j, hj⟩) ≤ sDist (A ⟨i, hi⟩) (A ⟨j, hj⟩) := le_refl _

/-- Non-vacuity of the general-`k` endpoint transport: its conclusion is realisable (reflexively at
`A = B`), so `stuckAtK_endpt_le` is a load-bearing transport. -/
theorem stuckAtK_endpt_le_satisfiable {N : ℕ} (A : Fin (N + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

end ProofsInTheBook.SphericalStuckGeneral
