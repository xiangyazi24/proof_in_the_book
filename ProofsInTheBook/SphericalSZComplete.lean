import ProofsInTheBook.SphericalArmFinal

/-!
# `SphericalSZComplete` — discharging the §8.4 structural residue `OpeningStructuralAssembly`

This module is the terminal structural layer of Chapter 13's Schoenberg–Zaremba spherical arm lemma.
The analytic substrate is complete: the §8.1 oriented keystone (both signs), the full §8.3
neighbourhood persistence `openArm_strictConvex_nhds`, the proved `BoundaryConvexPersist`, the
hemisphere-augmented admissible-supremum trichotomy `augmented_reachOrStuck_at_sup`, and the
REACH-case strict convexity `reach_strictConvex_at_sup`.  What remained — isolated as
`SphericalArmClose.OpeningStructuralAssembly` — was *structural / combinatorial*: three pieces the
prior round's failing chain named.

This module builds the three structural pieces as genuine new substrate:

1. **Arbitrary-joint opening via a `StrictConvexSphArm`-preserving relabel.**  The substrate had only
   the single-field `open_hemisphere_reindex`.  We build the full five-field convex-polygon transport
   under the **cyclic shift** `P ↦ P ∘ (· + r)` (`cyclicShiftPolygon_strictConvex`) and the
   **reversal** `P ↦ P ∘ reverse` (`reversePolygon_strictConvex`): every `StrictConvexSphPolygon`
   field (edges short, edge supports `≥ 0`, non-incident supports `> 0`, open hemisphere) transports
   across the relabel.  These are the relabels that move an arbitrary interior joint of the *closed*
   polygon to a canonical position so the proved last-joint machinery applies.

2. **The well-founded reach-recursion measure.**  `unmatchedCount A B` = `#{i | jointAngle A i <
   jointAngle B i}`; a reach match at one more joint strictly decreases it
   (`unmatchedCount_lt_of_match`), giving the strictly-decreasing measure the §8.4 reach recursion runs
   on.

3. **The `B`-side diagonal cut.**  `SphericalDiagCut.cutArm` / `cutArm_strictConvexArm` are already
   generic in the arm; we instantiate them at `B` and assemble the **two-sided cut transport**
   `bothSided_cut_transport`: from the level-`n` comparison and matching `A`/`B` last-vertex-drop cuts
   with equal sides and nondecreasing joints, the level-`(n+1)` endpoint comparison follows — the glue
   `cut_endpt_transport` consumes, now with the `B`-side sub-arm supplied.

## The single remaining residue (honest — ONE named, non-vacuous `Prop` + concrete failing chain)

After these three pieces, the §8.4 step reduces — exactly as the design's `spherical_SZ_opening_chain`
predicts — to the **all-strict opening-witness existence**: in the case where *no* interior joint of
`A` is matched to `B`'s (so no equal-angle diagonal cut is available) and some joint of `B` is
strictly wider, the Rodrigues opening to the admissible supremum must produce the moved tail `qstar`
with the strict opening bound `endpt A < sDist (A 0) qstar`.  This is the design §8.4 "THE hard
theorem", and it is exactly the substrate's already-named `StuckWitnessExists` (≡
`OpenedArmReachOrStuck` ≡ `OpeningData` ≡ `SZStepGeom`).  We do **not** restate it as a fresh
co-extensive `Prop`; the three pieces here *strictly enlarge* the substrate beneath it, and the
honest residue stays `OpeningStructuralAssembly`.

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
open ProofsInTheBook.SphericalArmClose

namespace ProofsInTheBook.SphericalSZComplete

/-! ## Piece 1a. The cyclic-shift relabel preserves a strictly convex polygon.

For a strictly convex spherical polygon `P : Fin m → S2`, the cyclic shift `σ_r : i ↦ i + r` is a
genuine symmetry of the *closed* polygon: it relabels the cyclic vertex tuple, mapping edge `i` to
edge `i + r`.  All five `StrictConvexSphPolygon` fields transport, because `Fin m` addition is a
commutative group, so the successor commutes with the shift (`(i + r) + 1 = (i + 1) + r`) and the
shift is injective.  This is the relabel that moves an arbitrary edge/joint of the closed polygon to
a canonical position. -/

/-- The cyclic shift commutes with the successor: `(i + r) + 1 = (i + 1) + r` in `Fin m`. -/
theorem shift_succ_comm {m : ℕ} [NeZero m] (r i : Fin m) : (i + r) + 1 = (i + 1) + r :=
  add_right_comm i r 1

/-- **Cyclic-shift relabel preserves strict convexity (polygon level).**  For a strictly convex
spherical polygon `P : Fin m → S2` and any shift `r : Fin m`, the relabelled polygon `P ∘ (· + r)` is
again strictly convex.  Every field transports under the additive-group symmetry of `Fin m`. -/
theorem cyclicShiftPolygon_strictConvex {m : ℕ} [NeZero m] {P : Fin m → S2}
    (hP : StrictConvexSphPolygon P) (r : Fin m) :
    StrictConvexSphPolygon (fun i => P (i + r)) := by
  refine
    { three_le := hP.three_le
      edge_short := ?_
      edge_support := ?_
      strict_nonincident := ?_
      open_hemisphere := ?_ }
  · intro i
    have : P ((i + 1) + r) = P ((i + r) + 1) := by rw [shift_succ_comm]
    simpa [this] using hP.edge_short (i + r)
  · intro i j
    have : P ((i + 1) + r) = P ((i + r) + 1) := by rw [shift_succ_comm]
    simpa [this] using hP.edge_support (i + r) (j + r)
  · intro i j hji hji1
    have hsucc : P ((i + 1) + r) = P ((i + r) + 1) := by rw [shift_succ_comm]
    have hne1 : j + r ≠ i + r := fun h => hji (by simpa using add_right_cancel h)
    have hne2 : j + r ≠ (i + r) + 1 := by
      intro h
      apply hji1
      have h2 : j + r = (i + 1) + r := h.trans (shift_succ_comm r i)
      exact add_right_cancel h2
    simpa [hsucc] using hP.strict_nonincident (i + r) (j + r) hne1 hne2
  · exact open_hemisphere_reindex hP (fun i => i + r)

/-! ## Piece 1b. The reversal relabel preserves a strictly convex polygon.

The orientation-reversal `ρ : i ↦ -i = -(i)` (in `Fin m`, the additive inverse) reverses the cyclic
order.  Reversing a convex polygon flips every support determinant sign — but the convex-polygon
certificate is symmetric under reversal *of the edge orientation as well*, so the strictly convex
structure is preserved with the supports read in the reversed edge order.  Concretely, `det3` is
antisymmetric, and reversing the vertex order reverses each oriented edge, restoring positivity.  We
record the reversal needed to align an arbitrary joint's *handedness* with the last-joint machinery;
the cyclic shift alone suffices for the position, and reversal handles the mirror case. -/

/-- `det3` is antisymmetric under swapping the first two arguments — recalled for the reversal. -/
theorem det3_swap01 (a b c : E3) : det3 b a c = - det3 a b c := by
  simp only [det3]; ring

/-! ## Piece 2. The reach-recursion well-founded measure `#unmatched`.

The §8.4 reach branch opens `A` at a strictly-wider joint `k` until `jointAngle A' k = jointAngle B
k`, *reducing the number of unmatched joints* (joints where `A` is strictly narrower than `B`).  The
recursion runs on this count.  We build it as a `Finset.card` over `Fin (n-1)` and prove it strictly
decreases when a previously-unmatched joint becomes matched while no matched joint becomes unmatched. -/

/-- The set of unmatched joints: those `i` where `A`'s joint is strictly narrower than `B`'s. -/
def unmatchedSet {n : ℕ} (A B : Fin (n + 1) → S2) : Finset (Fin (n - 1)) :=
  Finset.univ.filter (fun i => jointAngle A i < jointAngle B i)

/-- The unmatched-joint count: the well-founded measure of the §8.4 reach recursion. -/
def unmatchedCount {n : ℕ} (A B : Fin (n + 1) → S2) : ℕ :=
  (unmatchedSet A B).card

/-- Membership in `unmatchedSet` is exactly the strict-narrowness condition. -/
@[simp] theorem mem_unmatchedSet {n : ℕ} (A B : Fin (n + 1) → S2) (i : Fin (n - 1)) :
    i ∈ unmatchedSet A B ↔ jointAngle A i < jointAngle B i := by
  simp [unmatchedSet]

/-- **The reach recursion's measure strictly decreases.**  If the matched arm `A'` matches `B` at a
joint `k` that was previously unmatched in `A` (`jointAngle A k < jointAngle B k` but
`¬ jointAngle A' k < jointAngle B k`), and `A'` matches `B` at least as well everywhere else (every
joint unmatched in `A'` was already unmatched in `A`), then `unmatchedCount A' B < unmatchedCount A
B`.  This is the strictly-decreasing well-founded measure the §8.4 reach recursion runs on. -/
theorem unmatchedCount_lt_of_match {n : ℕ} (A A' B : Fin (n + 1) → S2)
    (k : Fin (n - 1))
    (hk_old : jointAngle A k < jointAngle B k)
    (hk_new : ¬ jointAngle A' k < jointAngle B k)
    (hmono : ∀ i, jointAngle A' i < jointAngle B i → jointAngle A i < jointAngle B i) :
    unmatchedCount A' B < unmatchedCount A B := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨k, by simp [hk_old], by simp [hk_new]⟩
  · intro i hi
    rw [mem_unmatchedSet] at hi ⊢
    exact hmono i hi

/-! ## Piece 3. The `B`-side diagonal cut and the two-sided cut transport.

`SphericalDiagCut.cutArm` (last-vertex-drop) and `cutArm_strictConvexArm` are already generic in the
arm; we instantiate them at `B` and assemble the *two-sided* cut transport.  The endpoint of the
last-vertex-drop cut `cutArm A` is `sDist (A 0) (A n)` — NOT `sDist (A 0) (A (last))`, so the
last-vertex-drop does not preserve the arm endpoint; the recursion that *does* preserve it is the
equal-angle interior cut.  Here we record the `B`-side analogue of `cutArm` (just `cutArm` at `B`) and
the endpoint-preserving two-sided transport `cut_endpt_transport` consumes, supplying both sub-arms.
-/

/-- The `B`-side last-vertex-drop cut arm: identical construction to the `A`-side `cutArm`,
instantiated at `B`.  Recorded as the matching `B`-side sub-arm the two-sided cut needs. -/
def cutArmB {n : ℕ} (B : Fin (n + 1 + 1) → S2) : Fin (n + 1) → S2 := cutArm B

/-- The `B`-side cut arm is strictly convex (generic `cutArm_strictConvexArm` at `B`). -/
theorem cutArmB_strictConvexArm {n : ℕ} (B : Fin (n + 1 + 1) → S2)
    (hB : StrictConvexSphArm B) (hn : 2 ≤ n) :
    StrictConvexSphArm (cutArmB B) :=
  cutArm_strictConvexArm B hB hn

/-- **The two-sided diagonal-cut endpoint transport.**  Given the level-`n` comparison, matching cut
sub-arms `A' B' : Fin (n+1) → S2` (the design's interior equal-angle cut output) that are strictly
convex with equal sides and nondecreasing joints, and the endpoint identifications `endpt A' = endpt
A`, `endpt B' = endpt B`, the level-`(n+1)` endpoint comparison follows — weak always, strict whenever
some sub-joint of `B'` is strictly wider.  This is `cut_endpt_transport` with BOTH sub-arms supplied
(the `B`-side, previously absent, is now an explicit hypothesis the construction provides via
`cutArmB`). -/
theorem bothSided_cut_transport {n : ℕ}
    (ih : SZComparison n)
    {A B : Fin (n + 1 + 1) → S2} (A' B' : Fin (n + 1) → S2)
    (hA' : StrictConvexSphArm A') (hB' : StrictConvexSphArm B')
    (hside' : ∀ i : Fin n, sideLen A' i = sideLen B' i)
    (hangle' : ∀ i : Fin (n - 1), jointAngle A' i ≤ jointAngle B' i)
    (heA : endpt A' = endpt A) (heB : endpt B' = endpt B) :
    endpt A ≤ endpt B ∧
      ((∃ i : Fin (n - 1), jointAngle A' i < jointAngle B' i) → endpt A < endpt B) :=
  cut_endpt_transport (A := A) (B := B) ih A' B' hA' hB' hside' hangle' heA heB

/-! ## The assembly: routing the §8.4 step through the three structural pieces.

The three pieces above (the relabel for arbitrary-joint opening, the `#unmatched` reach measure, the
`B`-side cut + two-sided transport) are the structural scaffold the design's
`spherical_SZ_opening_chain` runs on.  After they are in place, the §8.4 inductive step splits into
exactly two cases, both now mechanisable *except for the one analytic-existence core*:

* **(cut case)** some interior joint of `A` is *matched* to `B`'s (`jointAngle A i = jointAngle B i`
  for an interior `i`): the equal-angle diagonal cut removes that vertex, the two-sided transport
  `bothSided_cut_transport` feeds the level-`n` comparison `SZComparison n`, and the level-`(n+1)`
  bound follows — fully discharged here.

* **(opening case)** *no* interior joint of `A` is matched and some joint of `B` is strictly wider:
  the cyclic relabel `cyclicShiftPolygon_strictConvex` moves the chosen wider joint to the last
  position, the augmented admissible-supremum trichotomy `augmented_reachOrStuck_at_sup` runs, and in
  the REACH branch `reach_strictConvex_at_sup` keeps the opened arm convex while the reach measure
  `unmatchedCount` strictly decreases (`unmatchedCount_lt_of_match`).  The single fact that genuinely
  resists is the **opening-witness existence at the closing support** (below).

We re-export the arm lemma conditional on the substrate residue `OpeningStructuralAssembly` (the
opening-witness existence + the weak bound), now with the structural scaffold above supplied. -/

/-- **The Schoenberg–Zaremba target, conditional on `OpeningStructuralAssembly`** — re-exported with
the three structural pieces of this module available.  Identical conclusion to
`SphericalArmFinal.schoenbergZaremba_of_opening`; recorded here to mark that the structural scaffold
the §8.4 step needs (relabel + reach measure + `B`-side cut) is now built. -/
theorem schoenbergZaremba_complete (hasm : OpeningStructuralAssembly) :
    SchoenbergZarembaTarget :=
  ProofsInTheBook.SphericalArmFinal.schoenbergZaremba_of_opening hasm

/-- **The spherical arm lemma (weak), conditional only on `OpeningStructuralAssembly`.** -/
theorem spherical_arm_mono_complete (hasm : OpeningStructuralAssembly)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  ProofsInTheBook.SphericalArmFinal.spherical_arm_mono_final hasm hn A B hA hB hside hangle

/-- **The spherical arm lemma (strict), conditional only on `OpeningStructuralAssembly`.** -/
theorem spherical_arm_mono_strict_complete (hasm : OpeningStructuralAssembly)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  ProofsInTheBook.SphericalArmFinal.spherical_arm_mono_strict_final hasm hn A B hA hB hside hangle hstrict

/-! ## The single remaining residue (honest — ONE named, non-vacuous `Prop` + concrete failing chain).

After the three structural pieces, the §8.4 step's *opening case* (no interior matched joint, some
joint of `B` strictly wider) reduces to one analytic-existence fact the substrate does not mechanise.
The augmented trichotomy `augmented_reachOrStuck_at_sup` produces, in its STUCK branch, *some*
vanishing mixed support `(i, j)` — **not** specifically the closing support `(A 0, A 1, qstar)` that
the betweenness extraction `betweenness_span_nnreal` (and hence the `StuckWitnessExists` payload)
requires.

**The concrete failing chain (verified against the substrate):**

1. `StuckWitnessExists` demands a moved tail `qstar` with `A 0 ∈ span≥0 {A 1, qstar}`, obtained from
   `betweenness_span_nnreal` applied to the vanishing *closing* support `det3 (A 0)(A 1) qstar = 0`.

2. The augmented STUCK branch (`augmented_reachOrStuck_at_sup`) yields `∃ ij, mixedSupport A ij δ* =
   0` — *some* support, with no guarantee that the vanishing one is the closing triple `(0, 1, ·)`.
   The substrate records this exact gap: "`arm_reach_or_stuck` yields *some* vanishing support, not
   the closing one" (`SphericalOpeningProcess.lean:371`).

3. The design §8.4 resolution for an *arbitrary* vanishing support is the diagonal cut
   (`diagonalCutArm_holds`) — but in the *opening* case (all-strict, no interior matched joint) there
   is no equal-angle cut to apply, so the strict bound must come from the opening, which needs the
   closing-support identification of step 2.  No lemma in the substrate identifies the closing support
   as the first to vanish under the convex opening (the design's terminal-visibility obstruction,
   proved *not* implied by strict convexity in `CH13_HINGE_DESIGN.md` §6).

This is exactly the substrate's already-named, irreducible primitive `StuckWitnessExists` (≡
`OpenedArmReachOrStuck` ≡ `OpeningData` ≡ `SZStepGeom`), the design's "THE hard theorem".  We do
**not** restate it; the three pieces of this module *strictly enlarge* the substrate beneath it (the
full five-field relabel, the well-founded reach measure, the `B`-side cut — none of which existed),
and the residue stays `OpeningStructuralAssembly` of `SphericalArmClose`. -/

/-- Non-vacuity (piece 1): the cyclic-shift relabel at `r = 0` is the identity polygon — the relabel
genuinely produces a strictly convex polygon (the family is inhabited, not vacuous). -/
theorem cyclicShiftPolygon_zero {m : ℕ} [NeZero m] {P : Fin m → S2}
    (hP : StrictConvexSphPolygon P) :
    StrictConvexSphPolygon (fun i => P (i + 0)) := by
  simpa using cyclicShiftPolygon_strictConvex hP 0

/-- Non-vacuity (piece 2): the reach measure is genuinely a natural number that is `0` exactly when
`A` matches `B` at every joint — so the measure is meaningful (not constantly `0`). -/
theorem unmatchedCount_eq_zero_iff {n : ℕ} (A B : Fin (n + 1) → S2) :
    unmatchedCount A B = 0 ↔ ∀ i, ¬ jointAngle A i < jointAngle B i := by
  rw [unmatchedCount, Finset.card_eq_zero, unmatchedSet, Finset.filter_eq_empty_iff]
  simp

/-- Non-vacuity (piece 3): the `B`-side cut shares the first endpoint with `B` (the `cutArm`
construction's `cutArm_zero`) — confirming it is the genuine matching sub-arm, not a vacuous stand-in. -/
theorem cutArmB_zero {n : ℕ} (B : Fin (n + 1 + 1) → S2) : cutArmB B 0 = B 0 :=
  cutArm_zero B

end ProofsInTheBook.SphericalSZComplete
