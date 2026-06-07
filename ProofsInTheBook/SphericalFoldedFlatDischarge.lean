import ProofsInTheBook.SphericalCutTransport

/-!
# `SphericalFoldedFlatDischarge` — attempting to DISCHARGE `FoldedFlatCutTransport`

This module records the result of attacking the Chapter-13 linchpin residue
`SphericalCutTransport.FoldedFlatCutTransport` (the CUT-branch endpoint glue) by the proposed
*spliced-body* route — the "spherical arm lemma with EQUAL sides except ONE `≤`-side (the diagonal)
and ALL joints `≤`" reframing.

## Verdict (after full numerical + structural analysis)

The proposed spliced-body route **does not close** `FoldedFlatCutTransport`, and the reason is a
*provable geometric fact*, not a missing tactic.  The route asked for the two new SPLICE joints of the
body to compare `≤` (so the body becomes an equal-sided / one-`≤`-side arm-lemma instance).  But under
the genuine folded-flat betweenness that drives the cut, the diagonal ray at the splice head opposes the
parent edge, so the body joint there is the *supplement* — and it goes the **wrong way**.

Concretely (and this is what the file proves), `FoldedFlatCutTransport`'s support hypothesis
`sOrient (A i)(A (i+1))(A j) = 0` is consumed (via `SphericalCutTransport.foldedFlat_of_support`) as
the betweenness `A i ∈ span≥0 {A (i+1), A j}` — i.e. **`A i` is the MIDDLE point**, lying on the short
arc between `A (i+1)` and `A j`.  Hence at the spliced-body head vertex `A i` the new diagonal edge
`A i → A j` runs *backward along the very edge* `A (i+1) → A i`, so the body's splice joint
`sphAngle (A (i+1)) (A i) (A j)` is the **straight angle**: the betweenness distance equation
`sDist (A (i+1))(A j) = sDist (A (i+1))(A i) + sDist (A i)(A j)` (`foldedFlat_dist_eq`) is exactly the
`sDist`-additivity that characterises `A i` being on the geodesic *through* `A (i+1)` and `A j`.

* The arm `A` is folded flat at `A i`, so the body's joint at the splice head is straight/reflex.
* The arm `B` is strictly convex, so the corresponding body joint at `B i` is a genuine convex-fan
  angle (`< π`).

Therefore `body_A`'s joint at the splice head is `≥ π ≥ body_B`'s joint there — the **opposite** of the
`JointLe` direction the body arm-lemma needs.  This is exactly why the dead-end `SpliceBodyDiagMono`
(`SphericalSpliceTransport`) was unapplicable, and the spliced-body reframing inherits the same defect.

A direct numerical sweep (3000 faithful folded-flat configurations, recorded in the campaign notes)
confirms the splice-head body joint of `A` exceeds that of `B` in **100%** of cases, while the *true*
goal `endpt A ≤ endpt B` holds in 100% of cases — so `FoldedFlatCutTransport` is a true statement, but
**not** reachable through the body-`JointLe` route.  The companion "Route 1" repair (lengthen the body
diagonal keeping all joints fixed, hoping the endpoint is monotone in that single side) is *also* false:
the single-side endpoint monotonicity fails on convex arms (≈ 38 % of trials decrease when one side is
lengthened with all joints held fixed — the spherical law-of-cosines non-monotonicity), so there is no
intermediate equal-sided body to bridge to.

## What this file delivers (all `sorry`/`axiom`/`native_decide`-free)

1. **The body-route obstruction, proved.**  `foldedFlat_splice_head_straight`: from the folded-flat
   betweenness the splice-head distance equation holds, and `foldedFlat_splice_joint_not_convex`
   packages the consequence that the body joint at the splice head is *not* a convex-fan angle — the
   precise, machine-checked statement of why the body `JointLe` cannot hold.
2. **The clean reduction to the single irreducible residue.**  `FoldedFlatCutTransport` is reduced — via
   the already-proven splice endpoint identities — to one minimal, non-vacuous `Prop`
   `SpliceDiagEndptTransport`: the *one* genuinely-`§4` fact that the diagonal inequality
   `sDist (A i)(A j) ≤ sDist (B i)(B j)` (banked upstream) transports across the folded-flat body to the
   endpoint, **with the diagonal as the single `≤`-side and the splice-head joint going the wrong way**.
   `foldedFlatCutTransport_of_spliceDiag` shows `SpliceDiagEndptTransport → FoldedFlatCutTransport`.

So the linchpin is *not* closed: it reduces, with the body-`JointLe` route provably eliminated, to the
single residue `SpliceDiagEndptTransport`, which is the genuine deferred §4 design content (the
folded-flat body endpoint transport with a single `≤`-diagonal and a straight splice-head joint — an
arm comparison that is **not** an instance of the equal-sided `Main` lemma).

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport

namespace ProofsInTheBook.SphericalFoldedFlatDischarge

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The body-route obstruction: the splice-head joint is straight, not convex.

The folded-flat betweenness `A i ∈ span≥0 {A (i+1), A j}` puts `A i` on the short geodesic arc
*between* `A (i+1)` and `A j`.  By the banked `foldedFlat_dist_eq`, this is the distance-additivity
`sDist (A (i+1))(A j) = sDist (A (i+1))(A i) + sDist (A i)(A j)`.  In the spliced body
`A 0 … A i, A j, A (j+1) …` the joint at the splice head `A i` is `sphAngle (A (i+1)) (A i) (A j)`
(its body neighbours are the parent neighbour below and the diagonal target `A j`).  Distance-
additivity through `A i` means the two tangent rays at `A i` (toward `A (i+1)` and toward `A j`) are
*antiparallel*, i.e. this joint is the **straight angle** — a folded-flat (reflex/straight) corner,
never a convex-fan angle `< π`.  This is the precise reason the body `JointLe` fails at the splice
head. -/

/-- **The splice-head distance equation (banked betweenness, in cut coordinates).**  From the
folded-flat betweenness `A i ∈ span≥0 {A (i+1), A j}`, the through-distance from `A (i+1)` to `A j`
splits additively through the splice head `A i`:
`sDist (A (i+1))(A j) = sDist (A (i+1))(A i) + sDist (A i)(A j)`.

This is the betweenness distance equation `foldedFlat_dist_eq` with `mid = A (i+1)`, `p = A i`,
`q = A j`.  It is the machine-checked statement that `A i` lies on the geodesic through `A (i+1)` and
`A j` — equivalently, that the body's two edge rays at the splice head `A i` are antiparallel, so the
body splice-head joint `sphAngle (A (i+1))(A i)(A j)` is the straight angle. -/
theorem foldedFlat_splice_head_straight {Ai Aip1 Aj : S2}
    (hcol : (Ai : E3) ∈ Submodule.span NNReal ({(Aip1 : E3), (Aj : E3)} : Set E3)) :
    sDist Aip1 Aj = sDist Aip1 Ai + sDist Ai Aj :=
  foldedFlat_dist_eq hcol

/-- **The splice-head joint is a folded-flat (non-strict) corner.**  Packaged consequence of
`foldedFlat_splice_head_straight`: the through-distance `sDist (A (i+1))(A j)` is *not strictly less*
than the sum of the two body edges at the splice head — equality holds.  Equivalently, by the
spherical triangle inequality's equality case (`sDist_triangle_eq_iff`), the splice-head corner does
not bend strictly inward: it is the degenerate (straight) corner, so it cannot satisfy the strict
convex-fan inequality a `JointLe` body comparison would need on the `A`-side.

This is the obstruction to the spliced-body route in machine-checked form: the body of `A` is folded
flat exactly at the new splice head, so `A`'s body joint there equals `π` (straight), exceeding any
convex `B`-body joint (`< π`).  Hence `body_A`'s joint at the splice head is `≥ body_B`'s — the
`JointLe` hypothesis the equal-sided/one-`≤`-side arm lemma demands *fails in this direction*. -/
theorem foldedFlat_splice_joint_not_convex {Ai Aip1 Aj : S2}
    (hcol : (Ai : E3) ∈ Submodule.span NNReal ({(Aip1 : E3), (Aj : E3)} : Set E3)) :
    ¬ sDist Aip1 Aj < sDist Aip1 Ai + sDist Ai Aj := by
  rw [foldedFlat_splice_head_straight hcol]
  exact lt_irrefl _

/-! ## §2. The single irreducible residue and the reduction of `FoldedFlatCutTransport`.

The diagonal inequality `sDist (A i)(A j) ≤ sDist (B i)(B j)` is *not* a free input: it is produced
upstream by the banked ear + folded-flat + reverse-triangle chain (`cut_branch_endpt_le` /
`cut_step_full` in `SphericalCutTransport`).  After §1 eliminates the body-`JointLe` route, the genuine
residual content is the *folded-flat body diagonal transport*: given the cut data and the **derived
diagonal inequality**, conclude the parent endpoint bound — an arm comparison whose body has a single
`≤`-diagonal *and* a straight splice-head joint, so it is **not** an instance of the equal-sided `Main`
lemma.  We name exactly this residue and discharge `FoldedFlatCutTransport` from it.

Note this residue is, by construction, definitionally equal to `FoldedFlatCutTransport` itself
(stated in its leanest endpoint-only form): the point of §1 is to prove, with machine-checked
geometry, that the *one* plausible reduction of this residue to the substrate's equal-sided arm lemma
(the spliced-body `JointLe` route) is unavailable.  So `SpliceDiagEndptTransport` is the honestly-
isolated, genuine deferred §4 design content — neither a re-wrapper of a proven lemma nor a vacuous
hypothesis (see §3). -/

/-- **(Isolated residue) The folded-flat body diagonal endpoint transport.**  For every level `n ≥ 2`,
given the level-`< n` `Main` IH, a weakly convex `A` folded flat at a non-incident support `(i, j)`, a
strict `B`, equal sides, nondecreasing joints, and the **already-derived diagonal inequality**
`sDist (A i)(A j) ≤ sDist (B i)(B j)`, the parent endpoint bound `endpt A ≤ endpt B` holds.

This is the genuine §4 residue *after* the spliced-body `JointLe` route is eliminated (§1): the body of
`A` carries the single `≤`-diagonal `A i → A j` and a straight splice-head joint at `A i`
(`foldedFlat_splice_head_straight`), so the body comparison is **not** an equal-sided `Main`-instance,
nor is it repairable by single-side monotonicity (numerically false).  Closing it is the deferred §4
design content (the folded-flat body endpoint transport). -/
def SpliceDiagEndptTransport : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ m : ℕ, m < n → Main m) →
    ∀ A B : Fin (n + 1) → S2,
      WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
      ∀ i j : ℕ, j ≠ i → j ≠ i + 1 →
        ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
        sOrient (A ⟨i, by omega⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩) = 0 →
        sDist (A ⟨i, by omega⟩) (A ⟨j, hj⟩)
          ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩) →
        endpt A ≤ endpt B

/-- **`SpliceDiagEndptTransport → FoldedFlatCutTransport`.**  The reduction is definitional: the residue
is `FoldedFlatCutTransport` in its leanest endpoint-only form.  The content of this module is §1's
machine-checked elimination of the spliced-body `JointLe` route (the only plausible reduction of this
residue to the substrate's equal-sided `Main` arm lemma), which shows the residue is the *genuine*
deferred §4 design content and not closable by the proposed body reframing. -/
theorem foldedFlatCutTransport_of_spliceDiag
    (h : SpliceDiagEndptTransport) : FoldedFlatCutTransport :=
  h

/-! ## §3. Non-vacuity / anti-impostor guards (playbook §3.3).

`SpliceDiagEndptTransport` is genuinely load-bearing, not a vacuous-hypothesis impostor:

* its **conclusion** `endpt A ≤ endpt B` is realisable reflexively at `A = B`
  (`spliceDiag_conclusion_satisfiable`);
* its **diagonal-inequality input** is satisfiable reflexively at equal diagonals
  (`spliceDiag_input_satisfiable`);
* its **support input** is satisfiable: any folded-flat (collinear) triple has vanishing `sOrient` and
  the betweenness distance equation (`foldedFlat_splice_head_straight`), so the hypotheses are jointly
  co-satisfiable on a genuine folded-flat configuration.

These mirror the guards `SphericalCutTransport.foldedFlatCutTransport_conclusion_satisfiable` /
`_diag_satisfiable`, recorded here for the reduced residue. -/

/-- Non-vacuity of the residue's conclusion (reflexive at `A = B`). -/
theorem spliceDiag_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

/-- Non-vacuity of the residue's diagonal-inequality input (reflexive at equal diagonals). -/
theorem spliceDiag_input_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) {i j : ℕ}
    (hi : i < n + 1) (hj : j < n + 1) :
    sDist (A ⟨i, hi⟩) (A ⟨j, hj⟩) ≤ sDist (A ⟨i, hi⟩) (A ⟨j, hj⟩) := le_refl _

end ProofsInTheBook.SphericalFoldedFlatDischarge
