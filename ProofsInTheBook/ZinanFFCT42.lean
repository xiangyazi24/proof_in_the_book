import ProofsInTheBook.ZinanFFCT41

/-!
# `ZinanFFCT42` — discharging `BaseStuckProgressW` via the **diagonal = wrap-edge cyclic identity**.

`ZinanFFCT41.mainPlus_headline_basecapped` consumes `ZinanFFCT41.BaseStuckProgressW` as its lone
genuinely-new residual: at a `BaseStuckWB` supremum (the base triangle `(A 0, A K, A last)` has
straightened to `γbase + δ*_WB = π`) the opening must still make recursion-ready progress —
`ReachWB ∨ ∃ vanishing non-incident support of A'_WB`.

## The shortcut (collapses the design's 250-450 line convex-position route)

The base monitor's value at the supremum is, **by definition**,
`baseCapSupportW A k δ*_WB = sOrient (A 0)(A K)(rotS2 (A K)(-δ*_WB)(A last))`.  Opening
`A'_WB := openTail A K (-δ*_WB)` fixes vertices `≤ K` and rotates vertices `> K`, so
`A'_WB 0 = A 0`, `A'_WB K = A K`, `A'_WB last = rotS2 (A K)(-δ*_WB)(A last)`.  Hence

    BaseStuckWB A B k h₀  ⟺  sOrient (A'_WB 0)(A'_WB K)(A'_WB last) = 0,

i.e. base-stuck's zero **is** the diagonal support of the *opened* arm at the triple `(0, K, last)`.

Now the closed polygon `A'_WB` (a `Fin (n+1)` cyclic tuple) has the **wraparound edge** `(last, 0)`,
because `Fin.last n + 1 = 0` in `Fin (n+1)`.  Its support at the interior vertex `K` is
`sOrient (A'_WB last)(A'_WB 0)(A'_WB K)`, which by the cyclic invariance of `det3`
(`det3 a b c = det3 c a b`) equals the diagonal `sOrient (A'_WB 0)(A'_WB K)(A'_WB last)`.

So the base diagonal zero is **literally** the wrap-edge non-incident support vanishing at
`(i, j) = (Fin.last n, K)`:
`i = last`, `i + 1 = last + 1 = 0` (Fin wrap), `j = K` interior gives `K ≠ last` and `K ≠ 0`, the
two `NonIncident` conditions in `BaseStuckProgressW`'s exact payload shape.  The whole residual
collapses to a `det3` cyclic-permutation identity plus the `openTail` index bookkeeping — **no
strict convex-position machinery, no straightening completion, no sub-arm IH**.

The consumer's payload (`ZinanFFCT41.BaseStuckProgressW` / the `NonIncident` family) uses **Fin
arithmetic** for `i + 1` (`NonIncident n := {c // c.2 ≠ c.1 ∧ c.2 ≠ c.1 + 1}`), so the wrap edge
genuinely qualifies — verified against `SphericalMonitoredSup.NonIncident` and
`ZinanFFCT41.interiorOpeningOutcomeWB_basecapped` (which feeds the payload into `StuckWB` via
`supportConstraint_apply` at exactly this `i+1`-Fin form).

## What is proved here (clean-3, no `sorry`/`axiom`/`admit`/`native_decide`)

* `§1` `det3_cyc_rot`, `lastAddOne_eq_zero` — the algebra/index micro-lemmas.
* `§2` `baseStuck_eq_openedDiagonal` — base-stuck's zero is the opened diagonal `(0,K,last)`.
* `§3` `baseDiagonal_zero_is_wrapEdgeSupport_zero` (Brick 1, ~one bridge) and
  `baseStuck_forces_vanishingSupport` (the vanishing-support payload at `(last, K)`).
* `§4` `BaseStuckProgressW_holds` — the residual in its **exact** `ZinanFFCT41` shape, and
  `mainPlus_headline_basestuck_free` — the headline with `BaseStuckProgressW` **discharged**.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT41

namespace ProofsInTheBook.ZinanFFCT42

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The micro-lemmas: `det3` cyclic rotation and the `Fin (n+1)` wrap index. -/

/-- `det3` cyclic rotation `det3 a b c = det3 c a b` (the even permutation, two transpositions).
Pure coordinate algebra. -/
theorem det3_cyc_rot (a b c : E3) : det3 a b c = det3 c a b := by
  simp only [det3]; ring

/-- The `sOrient` cyclic rotation `sOrient a b c = sOrient c a b` (the even permutation), inherited
from `det3_cyc_rot` through `sOrient = det3 ∘ coe`. -/
theorem sOrient_cyc_rot (a b c : S2) : sOrient a b c = sOrient c a b := by
  simp only [sOrient]; exact det3_cyc_rot _ _ _

/-- The wraparound index identity `Fin.last n + 1 = 0` in `Fin (n + 1)` (so the closed polygon's
last edge is `(last, 0)`). -/
theorem lastAddOne_eq_zero (n : ℕ) : (Fin.last n + 1 : Fin (n + 1)) = 0 := by
  apply Fin.ext
  simp only [Fin.val_add, Fin.val_last, Fin.val_zero, Fin.val_one']
  rcases n with _ | m
  · rfl
  · rw [Nat.mod_eq_of_lt (show 1 < m + 1 + 1 by omega)]
    simp [Nat.mod_self]

/-! ## §2. Base-stuck's zero is the opened diagonal support `(0, K, last)` of `A'_WB`. -/

/-- **Base-stuck = opened diagonal zero.**  `baseCapSupportW A k δ*_WB` is, by definition, the
oriented base support with the endpoint vertex opened by `-δ*_WB`; since `openTail A K (-δ*_WB)`
fixes `0` and `K` (both `≤ K`) and rotates `last` (`K.val < n`), it equals the diagonal support
`sOrient (A'_WB 0)(A'_WB K)(A'_WB last)` of the opened arm. -/
theorem baseStuck_eq_openedDiagonal {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) (δ : ℝ) :
    baseCapSupportW A k δ
      = sOrient (openTail A (openingAxis k) (-δ) 0)
          (openTail A (openingAxis k) (-δ) (openingAxis k))
          (openTail A (openingAxis k) (-δ) (Fin.last n)) := by
  obtain ⟨hK1, hKn⟩ := openingAxis_interior k
  -- `A'_WB 0 = A 0`, `A'_WB K = A K`, `A'_WB last = rotS2 (A K)(-δ)(A last)`.
  rw [openTail_zero, openTail_axis,
      openTail_rot A (openingAxis k) (-δ) (r := Fin.last n) (by rw [Fin.val_last]; exact hKn)]
  rfl

/-! ## §3. Brick 1 — the opened diagonal zero **is** the wrap-edge non-incident support zero. -/

/-- **(Brick 1, the cyclic-identity bridge.)**  In the opened closed polygon `A'_WB := openTail A K
(-δ)`, a zero diagonal support at the triple `(0, K, last)` is **literally** a zero non-incident
edge support at the wraparound pair `(i, j) = (Fin.last n, K)`:
`i = last`, `i + 1 = last + 1 = 0` (Fin wrap), and the support
`sOrient (A'_WB last)(A'_WB 0)(A'_WB K)` equals the diagonal by `det3` cyclic rotation.  The two
`NonIncident` side conditions `j ≠ i` (`K ≠ last`) and `j ≠ i + 1` (`K ≠ 0`) hold because `K` is an
interior axis (`1 ≤ K.val < n`). -/
theorem baseDiagonal_zero_is_wrapEdgeSupport_zero {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1))
    (δ : ℝ)
    (hdiag : sOrient (openTail A (openingAxis k) (-δ) 0)
        (openTail A (openingAxis k) (-δ) (openingAxis k))
        (openTail A (openingAxis k) (-δ) (Fin.last n)) = 0) :
    ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (openTail A (openingAxis k) (-δ) i)
        (openTail A (openingAxis k) (-δ) (i + 1))
        (openTail A (openingAxis k) (-δ) j) = 0 := by
  obtain ⟨hK1, hKn⟩ := openingAxis_interior k
  refine ⟨Fin.last n, openingAxis k, ?_, ?_, ?_⟩
  · -- `K ≠ last`: `K.val < n = (last).val`.
    intro h
    rw [h, Fin.val_last] at hKn
    exact lt_irrefl n hKn
  · -- `K ≠ last + 1 = 0`: `1 ≤ K.val`.
    rw [lastAddOne_eq_zero]
    intro h
    rw [h, Fin.val_zero] at hK1
    exact absurd hK1 (by norm_num)
  · -- the wrap-edge support `sOrient (A'_WB last)(A'_WB 0)(A'_WB K)` = the diagonal (cyclic).
    rw [lastAddOne_eq_zero]
    -- goal: `sOrient (A'_WB last)(A'_WB 0)(A'_WB K) = 0`; `hdiag` is the diagonal `(0,K,last)`.
    -- `sOrient (0)(K)(last) = sOrient (last)(0)(K)` (cyclic, a=0,b=K,c=last).
    rw [sOrient_cyc_rot] at hdiag
    exact hdiag

/-- **Base-stuck forces a vanishing non-incident support** of `A'_WB`, in the exact payload shape of
`ZinanFFCT41.BaseStuckProgressW`.  Compose `baseStuck_eq_openedDiagonal` (base-stuck = opened
diagonal zero) with `baseDiagonal_zero_is_wrapEdgeSupport_zero` (the cyclic identity). -/
theorem baseStuck_forces_vanishingSupport {n : ℕ} {A B : Fin (n + 1) → S2} (k : Fin (n - 1)) (h₀ : E3)
    (hbase : BaseStuckWB A B k h₀) :
    ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) i)
        (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (i + 1))
        (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) j) = 0 := by
  -- `BaseStuckWB` unfolds to `baseCapSupportW A k δ*_WB = 0`.
  have hdiag : sOrient (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) 0)
      (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (openingAxis k))
      (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) (Fin.last n)) = 0 := by
    rw [← baseStuck_eq_openedDiagonal]; exact hbase
  exact baseDiagonal_zero_is_wrapEdgeSupport_zero A k (monitoredSupWB A B k h₀) hdiag

/-! ## §4. `BaseStuckProgressW` discharged, and the base-stuck-free headline. -/

/-- **`BaseStuckProgressW` holds** — in its EXACT `ZinanFFCT41` shape.  A base-stuck supremum always
makes recursion-ready progress by taking the **vanishing-support** disjunct: the base diagonal zero
*is* the wraparound non-incident support zero of `A'_WB` (the cyclic identity, §3).  `ReachWB` is
never needed.  This is unconditional — no `OpenedClosingEdge*`, no `SupportStuckMargins`, no
straightening completion, no sub-arm IH. -/
theorem BaseStuckProgressW_holds : ZinanFFCT41.BaseStuckProgressW := by
  intro n A B _hA _hB k _hkdef h₀ _hnorm _hhpos hbase
  exact Or.inr (baseStuck_forces_vanishingSupport k h₀ hbase)

/-- **The base-stuck-free headline.**  `ZinanFFCT41.mainPlus_headline_basecapped` with
`BaseStuckProgressW` **discharged** (supplied by `BaseStuckProgressW_holds`).  The residue surface
drops `hbase : BaseStuckProgressW` entirely; what remains is exactly the four FFCT40/41 splice/edge
residuals (`SpliceBodyDiagMono`, `SpliceStructuralData`, `OpenedClosingEdgeDistinctAtSupWB`,
`SupportStuckMarginsPosAtSupWB`) plus the pure-hemi progress residual `PureHemiProgressWB`.
`GlueWBaseCap` (FFCT41) and now `BaseStuckProgressW` are both GONE from the surface. -/
theorem mainPlus_headline_basestuck_free
    (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData)
    (hclose : OpenedClosingEdgeDistinctAtSupWB) (hmargins : SupportStuckMarginsPosAtSupWB)
    (hprog : PureHemiProgressWB)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  ZinanFFCT41.mainPlus_headline_basecapped hcore hstruct hclose hmargins hprog
    BaseStuckProgressW_holds hn A B hA hB hside hangle

/-! ### Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `baseStuck_eq_openedDiagonal`: at `δ = 0` the opened diagonal is the *unopened*
strict convex base support `sOrient (A 0)(A K)(A last)`, a genuine continuous functional (strictly
positive for a strict arm at an interior axis), so the identity bridges a real geometric quantity,
not a degenerate constant. -/
theorem baseStuck_eq_openedDiagonal_at_zero {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    baseCapSupportW A k 0
      = sOrient (openTail A (openingAxis k) 0 0)
          (openTail A (openingAxis k) 0 (openingAxis k))
          (openTail A (openingAxis k) 0 (Fin.last n)) := by
  have h := baseStuck_eq_openedDiagonal A k 0
  rwa [neg_zero] at h

/-- Non-vacuity of the discharged `BaseStuckProgressW`: its conclusion is a genuine disjunction whose
chosen `Or.inr` member is real `NonIncident` data at the wraparound pair `(last, K)` — the side
conditions `K ≠ last` and `K ≠ 0` are nondegenerate (an interior axis has `1 ≤ K.val < n`), so this
is not a vacuous-hypothesis impostor.  Witnessed here by the genuine wrap-edge index pair. -/
theorem baseStuckProgressW_payload_indices_nondegenerate {n : ℕ} (k : Fin (n - 1)) :
    (openingAxis k : Fin (n + 1)) ≠ Fin.last n ∧
      (openingAxis k : Fin (n + 1)) ≠ Fin.last n + 1 := by
  obtain ⟨hK1, hKn⟩ := openingAxis_interior k
  refine ⟨?_, ?_⟩
  · intro h; rw [h, Fin.val_last] at hKn; exact lt_irrefl n hKn
  · rw [lastAddOne_eq_zero]; intro h; rw [h, Fin.val_zero] at hK1; exact absurd hK1 (by norm_num)

end ProofsInTheBook.ZinanFFCT42

-- §1 the algebra/index micro-lemmas
#print axioms ProofsInTheBook.ZinanFFCT42.det3_cyc_rot
#print axioms ProofsInTheBook.ZinanFFCT42.lastAddOne_eq_zero
-- §2 base-stuck = opened diagonal
#print axioms ProofsInTheBook.ZinanFFCT42.baseStuck_eq_openedDiagonal
-- §3 Brick 1 (the cyclic-identity bridge) + the vanishing-support payload
#print axioms ProofsInTheBook.ZinanFFCT42.baseDiagonal_zero_is_wrapEdgeSupport_zero
#print axioms ProofsInTheBook.ZinanFFCT42.baseStuck_forces_vanishingSupport
-- §4 the residual DISCHARGED + the base-stuck-free headline
#print axioms ProofsInTheBook.ZinanFFCT42.BaseStuckProgressW_holds
#print axioms ProofsInTheBook.ZinanFFCT42.mainPlus_headline_basestuck_free
-- non-vacuity guards
#print axioms ProofsInTheBook.ZinanFFCT42.baseStuckProgressW_payload_indices_nondegenerate
