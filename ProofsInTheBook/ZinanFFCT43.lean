import ProofsInTheBook.ZinanFFCT42

/-!
# `ZinanFFCT43` — discharging `OpenedClosingEdgeDistinctAtSupWB` via **endpoint positivity**.

`ZinanFFCT42.mainPlus_headline_basestuck_free` still consumes
`ZinanFFCT41.OpenedClosingEdgeDistinctAtSupWB` as a named residual: at a `StuckWB` supremum the single
wraparound *closing* edge `(last, 0)` of the opened arm `A'_WB := openTail A K (-δ*_WB)` must be distinct,
i.e.

    openTail A K (-δ*_WB) (Fin.last n) ≠ openTail A K (-δ*_WB) (Fin.last n + 1).

## The route (the master's endpoint-positivity argument)

The closing edge is the **endpoint pair** of the opened polygon: `Fin.last n + 1 = 0` in `Fin (n + 1)`
(`ZinanFFCT42.lastAddOne_eq_zero`), so the closing edge is `(last, 0)`, and its spherical length is exactly
`endpt (openTail A K (-δ*_WB)) = sDist (A'_WB 0) (A'_WB last)`.  The whole point of the base-capped
widening family `WB` (and its discharged cap `GlueWBaseCap_at_supWB`) is that opening by `-δ*_WB` does **not
shrink the endpoint**:

* `ZinanFFCT41.glueWB_clause_i` (now unconditional, the cap discharged): `endpt A ≤ endpt A'_WB`.

And the *unopened* arm `A` is a strict convex closed polygon, so its own wraparound edge `(last, 0)` is a
genuine (short, hence non-degenerate) edge:

* `A last ≠ A (last + 1) = A 0` from `StrictConvexSphArm`'s `edge_short` at `i = last`
  (`ZinanFFCT39.base_consecutive_ne`), so `endpt A = sDist (A 0) (A last) > 0` (`sDist_pos_of_ne`).

Chaining: `0 < endpt A ≤ endpt A'_WB = sDist (A'_WB 0) (A'_WB last)`, so `sDist (A'_WB 0) (A'_WB last) ≠ 0`,
whence `A'_WB 0 ≠ A'_WB last` (`sDist_eq_zero_iff`), i.e. the closing edge is distinct.  No
convex-position machinery, no straightening — the endpoint never collapses because the cap keeps the
endpoint from shrinking and the base endpoint was already positive.

The `StuckWB` hypothesis of the residual is **not needed** (the closing edge is distinct at *any* `WB`
supremum, stuck or not); we carry it as an unused binder, faithful to the consumer's exact shape.

## What is proved here (clean-3, no `sorry`/`axiom`/`admit`/`native_decide`)

* `§1` `strict_arm_endpt_pos` — `0 < endpt A` for a `StrictConvexSphArm` (the base wraparound edge is
  short, so its endpoints differ).
* `§2` `closing_distinct_at_supWB` — `A'_WB 0 ≠ A'_WB last` at the `WB` supremum, by
  `endpt A ≤ endpt A'_WB` (clause (i)) and `0 < endpt A`.
* `§3` `OpenedClosingEdgeDistinctAtSupWB_holds` — the residual in its EXACT `ZinanFFCT41` shape, and
  `mainPlus_headline_closing_free` — the headline with `OpenedClosingEdgeDistinctAtSupWB` **also**
  discharged.  The residue surface drops the closing-edge clause; what remains is the four FFCT40/41
  splice/margin/pure-hemi residuals (`SpliceBodyDiagMono`, `SpliceStructuralData`,
  `SupportStuckMarginsPosAtSupWB`, `PureHemiProgressWB`).

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
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.ZinanFFCT39
open ProofsInTheBook.ZinanFFCT41
open ProofsInTheBook.ZinanFFCT42

namespace ProofsInTheBook.ZinanFFCT43

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. Endpoint positivity for a strict convex arm. -/

/-- **The endpoint of a strict convex arm is positive.**  `endpt A = sDist (A 0)(A last)`; the wraparound
edge `(last, last + 1)` of the closed polygon is short (`StrictConvexSphArm`'s `edge_short`), and
`last + 1 = 0` (`ZinanFFCT42.lastAddOne_eq_zero`), so `A last ≠ A 0`, whence `0 < sDist (A 0)(A last)`. -/
theorem strict_arm_endpt_pos {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A) :
    0 < endpt A := by
  -- the wraparound edge `(last, last + 1 = 0)` is short ⟹ `A last ≠ A 0`.
  have hwrap : A (Fin.last n) ≠ A (Fin.last n + 1) := base_consecutive_ne hA (Fin.last n)
  rw [lastAddOne_eq_zero] at hwrap
  have hne : A 0 ≠ A (Fin.last n) := fun h => hwrap h.symm
  -- `endpt A = sDist (A 0)(A last) > 0`.
  exact sDist_pos_of_ne hne

/-! ## §2. The closing edge `(A'_WB 0, A'_WB last)` is distinct at the `WB` supremum. -/

/-- **The closing endpoint pair of `A'_WB` is distinct.**  From `glueWB_clause_i`
(`endpt A ≤ endpt A'_WB`, unconditional now the cap is discharged) and `strict_arm_endpt_pos`
(`0 < endpt A`), the opened-arm endpoint `endpt A'_WB = sDist (A'_WB 0)(A'_WB last)` is positive, hence
`A'_WB 0 ≠ A'_WB last`. -/
theorem closing_distinct_at_supWB {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0) :
    openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) 0
      ≠ openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (Fin.last n) := by
  -- `0 < endpt A ≤ endpt A'_WB = sDist (A'_WB 0)(A'_WB last)`.
  have hpos : 0 < endpt A := strict_arm_endpt_pos hA
  have hmono : endpt A ≤ endpt (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀))) :=
    glueWB_clause_i hA hka hkt h0
  have hendpt : 0 < endpt (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀))) :=
    lt_of_lt_of_le hpos hmono
  -- `endpt A'_WB = sDist (A'_WB 0)(A'_WB last)`; positivity ⟹ the endpoints differ.
  have hsd : (0 : ℝ) < sDist (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) 0)
      (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (Fin.last n)) := hendpt
  intro heq
  rw [sDist_eq_zero_iff.2 heq] at hsd
  exact lt_irrefl 0 hsd

/-! ## §3. The residual discharged, and the closing-edge-free headline. -/

/-- **`OpenedClosingEdgeDistinctAtSupWB` holds** — in its EXACT `ZinanFFCT41` shape.  At a `StuckWB`
supremum the closing edge `(last, last + 1 = 0)` of `A'_WB` is distinct.  Unconditional in the `StuckWB`
premise (which is carried as an unused binder, faithful to the consumer's shape): the endpoint never
collapses because the discharged cap keeps `endpt A ≤ endpt A'_WB`, and the base endpoint `endpt A` is
positive.  The goal's `Fin.last n + 1` is `0` (`ZinanFFCT42.lastAddOne_eq_zero`), so the closing edge is
the endpoint pair `(A'_WB last, A'_WB 0)`. -/
theorem OpenedClosingEdgeDistinctAtSupWB_holds : ZinanFFCT41.OpenedClosingEdgeDistinctAtSupWB := by
  intro n A B hA k hkdef h₀ hnorm hhpos _hstuck
  -- the glue-context inputs of `glueWB_clause_i`, derived inside the scoped binders.
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0 :=
    monitoredFamily_init_admissible hA hhpos hkdef
  -- `A'_WB 0 ≠ A'_WB last`; the goal asks `A'_WB last ≠ A'_WB (last + 1) = A'_WB 0`.
  have hne := closing_distinct_at_supWB hA hka hkt h0
  rw [lastAddOne_eq_zero]
  exact fun h => hne h.symm

/-- **The closing-edge-free headline.**  `ZinanFFCT42.mainPlus_headline_basestuck_free` with
`OpenedClosingEdgeDistinctAtSupWB` **also discharged** (supplied by
`OpenedClosingEdgeDistinctAtSupWB_holds`).  The residue surface drops `hclose` entirely; what remains is
exactly the four FFCT40/41 residuals (`SpliceBodyDiagMono`, `SpliceStructuralData`,
`SupportStuckMarginsPosAtSupWB`, `PureHemiProgressWB`).  `GlueWBaseCap`, `BaseStuckProgressW`, and now
`OpenedClosingEdgeDistinctAtSupWB` are all GONE from the surface. -/
theorem mainPlus_headline_closing_free
    (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData)
    (hmargins : SupportStuckMarginsPosAtSupWB) (hprog : PureHemiProgressWB)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  ZinanFFCT42.mainPlus_headline_basestuck_free hcore hstruct
    OpenedClosingEdgeDistinctAtSupWB_holds hmargins hprog hn A B hA hB hside hangle

/-! ### Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `strict_arm_endpt_pos`: `endpt A` is the genuine spherical length `sDist (A 0)(A last)`,
unfolded here, so the positivity is a real geometric fact, not a degenerate constant. -/
theorem strict_arm_endpt_pos_unfolds {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A = sDist (A 0) (A (Fin.last n)) := rfl

/-- Non-vacuity of the discharged residual's conclusion: it is a genuine edge inequality between two
distinct opened vertices, realised at `δ = 0` (the unopened arm) where the closing edge is the base
endpoint pair `A last ≠ A 0` of a strict convex arm.  Not a vacuous-hypothesis impostor: the conclusion
is a real distinctness, and the (unused) `StuckWB` premise does not gate it. -/
theorem openedClosingEdgeDistinctAtSupWB_conclusion_real {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) :
    A (Fin.last n) ≠ A 0 := by
  have hwrap : A (Fin.last n) ≠ A (Fin.last n + 1) := base_consecutive_ne hA (Fin.last n)
  rwa [lastAddOne_eq_zero] at hwrap

end ProofsInTheBook.ZinanFFCT43

-- §1 endpoint positivity
#print axioms ProofsInTheBook.ZinanFFCT43.strict_arm_endpt_pos
-- §2 closing edge distinct at the WB supremum
#print axioms ProofsInTheBook.ZinanFFCT43.closing_distinct_at_supWB
-- §3 the residual DISCHARGED + the closing-edge-free headline
#print axioms ProofsInTheBook.ZinanFFCT43.OpenedClosingEdgeDistinctAtSupWB_holds
#print axioms ProofsInTheBook.ZinanFFCT43.mainPlus_headline_closing_free
-- non-vacuity guards
#print axioms ProofsInTheBook.ZinanFFCT43.openedClosingEdgeDistinctAtSupWB_conclusion_real
