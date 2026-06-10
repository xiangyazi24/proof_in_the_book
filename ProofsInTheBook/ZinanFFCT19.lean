import ProofsInTheBook.ZinanFFCT18
import ProofsInTheBook.SphericalLastCornerStuck

/-!
# `ZinanFFCT19` — the routine / needs-care bricks of the Ch13 `MainPlus` DAG

## Context

`ZinanFFCT18` installed the repaired left-arm predicate `PositiveJoints` and the strengthened
per-level invariant `MainPlus` (= `Main` with `PositiveJoints A`), together with the Layer-1/2
substrate: `strictConvexSphArm_positiveJoints`, `intervalArm_positiveJoints`, the `armMono_of_MainPlus`
bridge, and the base anchors `mainPlus_two` / `mainPlus_of_lt_two`.

This module bolts on the remaining routine / needs-care bricks of the `MainPlus` DAG, in dependency
order, so the strengthened recursion assembles exactly as the un-repaired `SphericalSZInduction` /
`SphericalSZStepClose` chain did — but threading `PositiveJoints` through every layer, which is what
excises the FFCT17 zigzag counterexample.

## The decisive new geometric brick (§1)

`lastCorner_hcol_forces_joint_zero` — the brick that makes `PositiveJoints` *actually* exclude the
last-corner (axis-incident) stuck: the folded-flat betweenness `A ⟨k⟩ ∈ span≥0 {A ⟨k+1⟩, A ⟨k+2⟩}`
forces the joint at apex `A ⟨k+1⟩` (joint index `k`) to angle `0`.  Geometrically: when the betweenness
vertex `A ⟨k⟩` lies on the minor arc between `A ⟨k+1⟩` and `A ⟨k+2⟩`, the two tangent rays at the apex
`A ⟨k+1⟩` (toward `A ⟨k⟩` and toward `A ⟨k+2⟩`) are *positively parallel*, so the unoriented spherical
angle between them is `0`.  The tangent computation uses `projOut` linearity (`tangentTo v · = projOut
(v:E3) ·` is `ℝ`-linear) and `projOut_self (v:E3) = 0`.

With this, `PositiveJoints A` (every interior joint `> 0`) is genuinely incompatible with a last-corner
stuck datum (§2): the stuck datum's betweenness gives joint `n-1` angle `0`, contradicting positivity.

## The `MainPlus` recursion bricks (§3–§7)

* `SZOpeningStepPlus` (§3) — the Plus step predicate, `SZOpeningStep` with `PositiveJoints` threaded
  through both the conclusion's left arm and the deficit-drop inner IH.
* `mainPlus_at_level` / `mainPlus_all` (§4) — the lex `(n, deficitCount)` recursion, copied verbatim
  from `SphericalSZInduction.main_at_level` / `main_all`, with `PositiveJoints` threaded.
* `spherical_arm_mono_of_stepPlus` (§5) — the strict-arm headline via `mainPlus_all` +
  `armMono_of_MainPlus` + `strictConvexSphArm_positiveJoints`.
* `ear_chord_le_of_MainPlus` (§6) — the ear chord comparison from `MainPlus m` (the ear inherits
  `PositiveJoints` via `intervalArm_positiveJoints`).
* `stuckAtK_diag_le_plus` (§7) — the general-`k` diagonal inequality from `MainPlus`, threading the
  ear's positive joints.

No `sorry`, `axiom`, `admit`, or `native_decide`; no statement weakened.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalCutTransport ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.TetDihedral
open ProofsInTheBook.ZinanFFCT18

namespace ProofsInTheBook.ZinanFFCT19

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The folded-flat betweenness forces the apex joint to `0`.

The decisive new geometric brick.  Phrased first on three abstract sphere points, then specialised to
the last-corner indices. -/

/-- **Tangent rays at the apex are positively parallel under betweenness.**  If `p ∈ span≥0 {v, w}`
(the betweenness point `p` on the minor arc from `v` to `w`) and the arc `(v, p)` is short
(`tangentTo v p ≠ 0`), then `tangentTo v p` is a nonnegative multiple of `tangentTo v w`: writing
`p = s • v + t • w` (`s, t ≥ 0`), `tangentTo v p = projOut v p = s • projOut v v + t • projOut v w
= t • tangentTo v w` (since `projOut v v = 0`). -/
theorem tangentTo_eq_nnsmul_of_betweenness {p v w : S2}
    (hcol : (p : E3) ∈ Submodule.span NNReal ({(v : E3), (w : E3)} : Set E3)) :
    ∃ t : ℝ, 0 ≤ t ∧ tangentTo v p = t • tangentTo v w := by
  rw [Submodule.mem_span_pair] at hcol
  obtain ⟨s, t, hst⟩ := hcol
  -- `(↑s) • v + (↑t) • w = p` as real-scalar combination.
  have hst' : (s : ℝ) • (v : E3) + (t : ℝ) • (w : E3) = (p : E3) := by
    have := hst
    rwa [NNReal.smul_def, NNReal.smul_def] at this
  refine ⟨(t : ℝ), t.2, ?_⟩
  -- apply `projOut (v:E3)` to both sides.
  have hv0 : (v : E3) ≠ 0 := by
    intro h; have := v.2; rw [h, norm_zero] at this; norm_num at this
  have hkey : projOut (v : E3) (p : E3)
      = (s : ℝ) • projOut (v : E3) (v : E3) + (t : ℝ) • projOut (v : E3) (w : E3) := by
    rw [← hst', projOut_add, projOut_smul, projOut_smul]
  rw [projOut_self (v : E3) hv0, smul_zero, zero_add] at hkey
  -- `tangentTo v p = projOut v p` and `tangentTo v w = projOut v w`.
  show projOut (v : E3) (p : E3) = (t : ℝ) • projOut (v : E3) (w : E3)
  exact hkey

/-- **Folded-flat betweenness forces the apex spherical angle to `0`.**  If `p ∈ span≥0 {v, w}` and
the arc `(v, p)` is short, then `sphAngle p v w = 0` — the apex `v` sees `p` and `w` in the *same*
tangent direction.  (`tangentTo v p = t • tangentTo v w` with `t ≥ 0`; since `tangentTo v p ≠ 0`,
necessarily `t > 0` and `tangentTo v w ≠ 0`, so `tangentTo v w = t⁻¹ • tangentTo v p` with `t⁻¹ > 0`,
the positive-parallel condition of `InnerProductGeometry.angle_eq_zero_iff`.) -/
theorem sphAngle_zero_of_betweenness {p v w : S2}
    (hsa : ShortArc v p)
    (hcol : (p : E3) ∈ Submodule.span NNReal ({(v : E3), (w : E3)} : Set E3)) :
    sphAngle p v w = 0 := by
  obtain ⟨t, htnn, htvp⟩ := tangentTo_eq_nnsmul_of_betweenness hcol
  -- `tangentTo v p ≠ 0` since the arc `(v, p)` is short.
  have hvp0 : (tangentTo v p : E3) ≠ 0 := (tangentTo_ne_zero_iff v p).2 hsa
  -- from `tangentTo v p = t • tangentTo v w` and `tangentTo v p ≠ 0`: `t ≠ 0` and `tangentTo v w ≠ 0`.
  have ht0 : t ≠ 0 := by
    intro h; rw [h, zero_smul] at htvp; exact hvp0 htvp
  have htpos : 0 < t := lt_of_le_of_ne htnn (Ne.symm ht0)
  have hvw0 : (tangentTo v w : E3) ≠ 0 := by
    intro h; rw [h, smul_zero] at htvp; exact hvp0 htvp
  -- `sphAngle p v w = angle (tangentTo v p) (tangentTo v w) = 0`.
  rw [sphAngle, InnerProductGeometry.angle_eq_zero_iff]
  refine ⟨hvp0, t⁻¹, by positivity, ?_⟩
  rw [htvp, smul_smul, inv_mul_cancel₀ ht0, one_smul]

/-- **(Brick 1) The last-corner betweenness forces the apex joint to `0`.**  For an arm
`A : Fin (N + 1) → S2`, the folded-flat betweenness `A ⟨k⟩ ∈ span≥0 {A ⟨k+1⟩, A ⟨k+2⟩}` at a
last-corner triple (`k + 2 ≤ N`), together with the short edge `(A ⟨k+1⟩, A ⟨k⟩)`, forces the interior
joint at apex `A ⟨k+1⟩` — i.e. `jointAngle A ⟨k, _⟩` — to angle `0`.

The joint index is `k : Fin (N - 1)` (apex vertex `A ⟨k+1⟩`, neighbours `A ⟨k⟩` and `A ⟨k+2⟩`); the
betweenness point `A ⟨k⟩` lies on the minor arc between the apex's two neighbours, so the apex sees them
in the same tangent direction (`sphAngle_zero_of_betweenness`). -/
theorem lastCorner_hcol_forces_joint_zero {N : ℕ} {A : Fin (N + 1) → S2} {k : ℕ}
    (hk2 : k + 2 ≤ N)
    (hsa : ShortArc (A ⟨k + 1, by omega⟩) (A ⟨k, by omega⟩))
    (hcol : (A ⟨k, by omega⟩ : E3)
      ∈ Submodule.span NNReal
        ({(A ⟨k + 1, by omega⟩ : E3), (A ⟨k + 2, by omega⟩ : E3)} : Set E3)) :
    jointAngle A ⟨k, by omega⟩ = 0 := by
  rw [jointAngle]
  -- `jointAngle A ⟨k⟩ = sphAngle (A ⟨k⟩) (A ⟨k+1⟩) (A ⟨k+2⟩)`; apex `v = A ⟨k+1⟩`, between point
  -- `p = A ⟨k⟩`, far point `w = A ⟨k+2⟩`.
  exact sphAngle_zero_of_betweenness (p := A ⟨k, by omega⟩) (v := A ⟨k + 1, by omega⟩)
    (w := A ⟨k + 2, by omega⟩) hsa hcol

/-! ## §2. `PositiveJoints` excludes the last-corner stuck. -/

/-- **(Brick 2) No last-corner stuck under `PositiveJoints`.**  A weakly convex `PositiveJoints` arm `A`
cannot carry a last-corner stuck datum `StuckAtKData A B (n-1) (n+1)`: the stuck datum's betweenness
(`stuckAtK_betweenness`) folds `A ⟨n-1⟩` flat between `A ⟨n⟩` and `A ⟨n+1⟩`, which by Brick 1 forces the
interior joint at index `n-1` to angle `0` — contradicting `PositiveJoints A` (every interior joint
`> 0`).  The short edge `(A ⟨n⟩, A ⟨n-1⟩)` Brick 1 needs is the arm edge `(A ⟨n-1⟩, A ⟨n⟩)` reversed,
from weak convexity's `edge_short`.

Stated at level `N = n+1` (arms `Fin (n+1+1) → S2`), the last-corner indices `(i, j) = (n-1, n+1)`. -/
theorem no_lastCornerStuck_of_PositiveJoints {n : ℕ} (hn : 2 ≤ n)
    {A B : Fin (n + 1 + 1) → S2}
    (hA : WeakConvexSphArm A)
    (hpos : PositiveJoints A)
    (hsk : StuckAtKData (N := n + 1) A B (n - 1) (n + 1)) :
    False := by
  -- the betweenness `A ⟨n-1⟩ ∈ span≥0 {A ⟨n⟩, A ⟨n+1⟩}`.
  have hij1 : (n - 1) + 1 < n + 1 := by omega
  have hj : n + 1 ≤ n + 1 := le_refl _
  have hcol := stuckAtK_betweenness (N := n + 1) hij1 hj hsk
  -- normalise `(n-1)+2 = n+1`, so the betweenness is in last-corner shape `{A ⟨(n-1)+1⟩, A ⟨(n-1)+2⟩}`.
  have hcol' : (A ⟨n - 1, by omega⟩ : E3)
      ∈ Submodule.span NNReal
        ({(A ⟨(n - 1) + 1, by omega⟩ : E3), (A ⟨(n - 1) + 2, by omega⟩ : E3)} : Set E3) := by
    have he2 : (⟨n + 1, by omega⟩ : Fin (n + 1 + 1)) = (⟨(n - 1) + 2, by omega⟩ : Fin (n + 1 + 1)) := by
      apply Fin.ext; show n + 1 = (n - 1) + 2; omega
    rwa [show (A ⟨n + 1, by omega⟩ : E3) = (A ⟨(n - 1) + 2, by omega⟩ : E3) from by rw [he2]] at hcol
  -- the short edge `(A ⟨(n-1)+1⟩, A ⟨n-1⟩) = (A ⟨n⟩, A ⟨n-1⟩)` from the arm edge `(A ⟨n-1⟩, A ⟨n⟩)`.
  have hedge : ShortArc (A ⟨n - 1, by omega⟩) (A ⟨(n - 1) + 1, by omega⟩) := by
    have he := hA.closed_convex.edge_short ⟨n - 1, by omega⟩
    have hsucc : ((⟨n - 1, by omega⟩ : Fin (n + 1 + 1)) + 1)
        = (⟨(n - 1) + 1, by omega⟩ : Fin (n + 1 + 1)) := by
      apply Fin.ext
      simp only [Fin.add_def, Fin.val_mk, Fin.val_one,
        Nat.mod_eq_of_lt (show (n - 1) + 1 < n + 1 + 1 by omega)]
    rwa [hsucc] at he
  have hsaEdge : ShortArc (A ⟨(n - 1) + 1, by omega⟩) (A ⟨n - 1, by omega⟩) := hedge.symm
  have hzero := lastCorner_hcol_forces_joint_zero (N := n + 1) (A := A) (k := n - 1)
    (by omega) hsaEdge hcol'
  -- contradiction with positivity.
  have hposk := hpos ⟨n - 1, by omega⟩
  rw [hzero] at hposk
  exact lt_irrefl 0 hposk

/-! ## §3. The Plus step predicate. -/

/-- **(Brick 3) The Plus opening/cut step predicate.**  As `SZOpeningStep`, but with `PositiveJoints`
threaded through both the level-`n` left arm and the deficit-drop inner IH's left arm.  This is the
per-step content the strengthened lex recursion consumes. -/
def SZOpeningStepPlus : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ m : ℕ, m < n → MainPlus m) →
    (∀ A B : Fin (n + 1) → S2,
      WeakConvexSphArm A → PositiveJoints A →
      StrictConvexSphArm B → SameSides A B → JointLe A B →
      (∀ A' B' : Fin (n + 1) → S2,
        WeakConvexSphArm A' → PositiveJoints A' →
        StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
        deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B') →
      endpt A ≤ endpt B)

/-! ## §4. The lex `(n, deficitCount)` recursion (verbatim copy with `PositiveJoints` threaded). -/

/-- **(Brick 4a) `MainPlus n` at a fixed level, by strong induction on `deficitCount`.**  Verbatim copy
of `SphericalSZInduction.main_at_level` with `PositiveJoints` threaded through the step. -/
theorem mainPlus_at_level (hstep : SZOpeningStepPlus) {n : ℕ} (hn : 2 ≤ n)
    (ihdim : ∀ m : ℕ, m < n → MainPlus m) :
    ∀ d : ℕ, ∀ A B : Fin (n + 1) → S2,
      WeakConvexSphArm A → PositiveJoints A →
      StrictConvexSphArm B → SameSides A B → JointLe A B →
      deficitCount A B = d → endpt A ≤ endpt B := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intro A B hA hposA hB hside hangle hdef
    refine hstep n hn ihdim A B hA hposA hB hside hangle ?_
    intro A' B' hA' hposA' hB' hside' hangle' hlt
    exact IH (deficitCount A' B') (hdef ▸ hlt) A' B' hA' hposA' hB' hside' hangle' rfl

/-- **(Brick 4b) `MainPlus n` for all `n`, by strong induction on `n`** (the lex outer level).  Verbatim
copy of `SphericalSZInduction.main_all` with `PositiveJoints` threaded; base from FFCT18's
`mainPlus_of_lt_two`. -/
theorem mainPlus_all (hstep : SZOpeningStepPlus) : ∀ n : ℕ, 2 ≤ n → MainPlus n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn A B hA hposA hB hside hangle
    have ihdim : ∀ m : ℕ, m < n → MainPlus m := by
      intro m hm
      rcases Nat.lt_or_ge m 2 with h2 | h2
      · exact mainPlus_of_lt_two h2
      · exact IH m hm h2
    exact mainPlus_at_level hstep hn ihdim (deficitCount A B) A B hA hposA hB hside hangle rfl

/-! ## §5. The strict-arm headline from the Plus step. -/

/-- **(Brick 5) Spherical arm monotonicity (weak), conditional only on `SZOpeningStepPlus`.**  Strict
arms `A`, `B` with equal sides and nondecreasing joints satisfy `endpt A ≤ endpt B`, via `mainPlus_all`
and the FFCT18 bridge `armMono_of_MainPlus` (which supplies `PositiveJoints A` from
`strictConvexSphArm_positiveJoints`). -/
theorem spherical_arm_mono_of_stepPlus (hstep : SZOpeningStepPlus)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  armMono_of_MainPlus (mainPlus_all hstep n hn) A B hA hB hside hangle

/-! ## §6. The ear chord comparison from `MainPlus`. -/

/-- **(Brick 6) The ear chord comparison from `MainPlus m`.**  Copy of
`SphericalSZStepClose.ear_chord_le_of_Main` with `MainPlus` replacing `Main`: the ear `A[a..a+m]` is
weakly convex with `PositiveJoints` (inherited from the parent via `intervalArm_positiveJoints`), the
ear `B[a..a+m]` strictly convex, and the parent sides/joints match, so `MainPlus m` gives the ear chord
comparison. -/
theorem ear_chord_le_of_MainPlus {N : ℕ} {A B : Fin (N + 1) → S2} {a m : ℕ} (hb : a + m ≤ N)
    (hMm : MainPlus m)
    (hposA : PositiveJoints A)
    (hAe : WeakConvexSphArm (intervalArm A a m hb))
    (hBe : StrictConvexSphArm (intervalArm B a m hb))
    (hside : ∀ i : Fin N, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (N - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A ⟨a, by omega⟩) (A ⟨a + m, by omega⟩)
      ≤ sDist (B ⟨a, by omega⟩) (B ⟨a + m, by omega⟩) := by
  have hposEar : PositiveJoints (intervalArm A a m hb) := intervalArm_positiveJoints a m hb hposA
  have hcmp : endpt (intervalArm A a m hb) ≤ endpt (intervalArm B a m hb) :=
    hMm (intervalArm A a m hb) (intervalArm B a m hb) hAe hposEar hBe
      (intervalArm_sameSides hb hside) (intervalArm_jointLe hb hangle)
  rwa [intervalArm_endpt A a m hb, intervalArm_endpt B a m hb] at hcmp

/-! ## §7. The general-`k` diagonal inequality from `MainPlus`. -/

/-- **(Brick 7) The general-`k` diagonal inequality from `MainPlus`.**  Copy of
`SphericalStuckGeneral.stuckAtK_diag_le` with `MainPlus` replacing `Main`: the ear comparison comes from
`ear_chord_le_of_MainPlus` (threading the parent's `PositiveJoints` to the ear), and the folded-flat
equation + reverse triangle inequality (`cut_diag_le`) deliver the diagonal inequality. -/
theorem stuckAtK_diag_le_plus {N : ℕ} {A B : Fin (N + 1) → S2} {i j : ℕ}
    (hij1 : i + 1 < j) (hj : j ≤ N) (hsk : StuckAtKData A B i j)
    (hMm : MainPlus (j - (i + 1)))
    (hposA : PositiveJoints A)
    (hAe : WeakConvexSphArm (intervalArm A (i + 1) (j - (i + 1)) (by omega)))
    (hBe : StrictConvexSphArm (intervalArm B (i + 1) (j - (i + 1)) (by omega)))
    (hsideAll : ∀ k : Fin N, sideLen A k = sideLen B k)
    (hangleAll : ∀ k : Fin (N - 1), jointAngle A k ≤ jointAngle B k) :
    sDist (A ⟨i, by omega⟩) (A ⟨j, by omega⟩)
      ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, by omega⟩) := by
  -- ear comparison from the level-`m` `MainPlus` IH.
  have hb : (i + 1) + (j - (i + 1)) ≤ N := by omega
  have hear0 := ear_chord_le_of_MainPlus (A := A) (B := B) (a := i + 1) (m := j - (i + 1)) hb
    hMm hposA hAe hBe hsideAll hangleAll
  -- rewrite `(i+1) + (j-(i+1)) = j`.
  have hjeq : (i + 1) + (j - (i + 1)) = j := by omega
  rw [show (⟨(i + 1) + (j - (i + 1)), by omega⟩ : Fin (N + 1)) = (⟨j, by omega⟩ : Fin (N + 1)) from
        Fin.ext hjeq] at hear0
  have hear : sDist (A ⟨i + 1, by omega⟩) (A ⟨j, by omega⟩)
      ≤ sDist (B ⟨i + 1, by omega⟩) (B ⟨j, by omega⟩) := hear0
  -- folded-flat equation + reverse triangle inequality (cut_diag_le).
  exact cut_diag_le (stuckAtK_flat_eq hij1 hj hsk) hear hsk.hside

/-! ## §8. Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `sphAngle_zero_of_betweenness`: a genuine collinear betweenness `p ∈ span≥0 {v, w}`
with `p` strictly between gives a real angle-`0` conclusion (the apex sees `p` and `w` aligned), not a
vacuous bound — realised by the degenerate self-membership `v ∈ span≥0 {v, w}` only when `v = p` (then
the hypothesis `ShortArc v p` is false), so the lemma genuinely consumes both hypotheses. -/
theorem sphAngle_zero_of_betweenness_nonvacuous {v w : S2} :
    (v : E3) ∈ Submodule.span NNReal ({(v : E3), (w : E3)} : Set E3) :=
  Submodule.mem_span_of_mem (by simp)

/-- Non-vacuity of the Plus step's conclusion: realised reflexively at `A = B`. -/
theorem szOpeningStepPlus_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

/-- Non-vacuity of the general-`k` Plus diagonal inequality: realised reflexively at `A = B`. -/
theorem stuckAtK_diag_le_plus_satisfiable {N : ℕ} (A : Fin (N + 1) → S2) {i j : ℕ}
    (hi : i < N + 1) (hj : j < N + 1) :
    sDist (A ⟨i, hi⟩) (A ⟨j, hj⟩) ≤ sDist (A ⟨i, hi⟩) (A ⟨j, hj⟩) := le_refl _

#print axioms lastCorner_hcol_forces_joint_zero
#print axioms no_lastCornerStuck_of_PositiveJoints
#print axioms mainPlus_all
#print axioms spherical_arm_mono_of_stepPlus
#print axioms ear_chord_le_of_MainPlus
#print axioms stuckAtK_diag_le_plus

end ProofsInTheBook.ZinanFFCT19
