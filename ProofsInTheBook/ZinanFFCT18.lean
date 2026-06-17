import ProofsInTheBook.ZinanFFCT17

/-!
# `ZinanFFCT18` — the repaired induction predicate `MainPlus` (positive joints) and its
# Layer-1/2 substrate

## Context

`ZinanFFCT17` kernel-anchored the route-level hole: `Main`, `SZOpeningStep` and
`FoldedFlatCutTransport` are all FALSE as stated, because `WeakConvexSphArm` is vacuous on
collinear zigzags (all supports `0`, all joints `0`).  The repair (design round 2026-06-09,
ChatGPT-Pro audited, numerically cross-validated): strengthen the LEFT-arm predicate by **positive
interior joints**.

* The SZ opening only *opens* joints starting from a strictly convex arm (whose joints are
  strictly positive — proven here), so every arm the recursion feeds has positive joints;
* the zigzag stratum has all joints `0` and is excised at the hypothesis level (anchored here);
* `jointAngle_lt_pi` (FFCT3) keeps the satisfiable class inside `(0, π)`: flat fans (`π`) and
  zigzags (`0`) are both excluded, exactly the closure-of-strict configurations remain.

## This file (Layer 1 + the routine half of Layer 2)

* `PositiveJoints`, `MainPlus`, `FoldedFlatCutTransportPlus` (the repaired residue, carrying the
  folded-flat betweenness `hcol` explicitly per the round-2 recommendation — the consumers derive
  it from the Gram signs via `stuckAtK_betweenness`, and FFCT17 showed the support alone is too
  weak a hypothesis).
* The `0`-side of the FFCT3 collinearity bridge: `det3_zero_of_sphAngle_zero`,
  `sphAngle_pos_of_det3_ne` (mirrors of the proven `π`-side).
* **`strict_jointAngle_pos`** / **`strictConvexSphArm_positiveJoints`** — strict arms have
  positive joints (the new lemma the `armMono` bridge needs).
* **`intervalArm_positiveJoints`** — ears inherit positive joints (via `intervalArm_jointAngle`).
* **`weakConvex_no_antipodal`** — no two vertices of a weakly convex arm are antipodal (open
  hemisphere), killing the antipodal branch of the endgame position table.
* **`endpoint_le_of_tail_fold`** — the `(i, j) = (0, n−1)` endgame arithmetic: a folded-flat tail
  plus the diagonal inequality plus the equal last side give the endpoint bound (pure
  `sDist_triangle` algebra).
* Sanity anchors: the FFCT17 zigzag FAILS `PositiveJoints` (so `MainPlus` is immune to the
  committed counterexample), and `MainPlus` is satisfiable at the base level.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT17

namespace ProofsInTheBook.ZinanFFCT18

set_option maxHeartbeats 1600000

/-! ## §1. Layer 1: the repaired predicates. -/

/-- **Positive interior joints** — the left-arm strengthening that excises the zigzag stratum. -/
def PositiveJoints {n : ℕ} (A : Fin (n + 1) → S2) : Prop :=
  ∀ k : Fin (n - 1), 0 < jointAngle A k

/-- **The repaired per-level induction statement.**  `Main` with the left arm additionally
required to have positive interior joints. -/
def MainPlus (n : ℕ) : Prop :=
  ∀ A B : Fin (n + 1) → S2,
    WeakConvexSphArm A → PositiveJoints A →
    StrictConvexSphArm B → SameSides A B → JointLe A B →
    endpt A ≤ endpt B

/-- **The repaired CUT-branch residue.**  As `FoldedFlatCutTransport`, but (a) the left arm has
positive joints, and (b) the folded-flat *betweenness* is carried explicitly (the support equation
alone is too weak — FFCT17; the stuck pipeline derives the betweenness from its Gram signs via
`stuckAtK_betweenness`, so this is the honest interface). -/
def FoldedFlatCutTransportPlus : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ m : ℕ, m < n → MainPlus m) →
    ∀ A B : Fin (n + 1) → S2,
      WeakConvexSphArm A → PositiveJoints A →
      StrictConvexSphArm B → SameSides A B → JointLe A B →
      ∀ i j : ℕ, j ≠ i → j ≠ i + 1 →
        ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
        (A ⟨i, by omega⟩ : E3) ∈
          Submodule.span NNReal ({(A ⟨i + 1, hi1⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3) →
        sDist (A ⟨i, by omega⟩) (A ⟨j, hj⟩) ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩) →
        endpt A ≤ endpt B

/-! ## §2. The `0`-side of the collinearity bridge (mirrors of the proven `π`-side). -/

/-- **A zero spherical angle forces collinearity** (`angle = 0` ⟹ positively parallel tangents ⟹
`det3 = 0`), via `InnerProductGeometry.angle_eq_zero_iff` and the proven
`det3_zero_of_antiparallel`. -/
theorem det3_zero_of_sphAngle_zero (u v w : S2) (h : sphAngle u v w = 0) :
    det3 (u : E3) (v : E3) (w : E3) = 0 := by
  rw [sphAngle, InnerProductGeometry.angle_eq_zero_iff] at h
  obtain ⟨_, r, _, heq⟩ := h
  exact det3_zero_of_antiparallel u v w r heq

/-- **Contrapositive: a non-degenerate triple bends strictly above `0`.** -/
theorem sphAngle_pos_of_det3_ne (u v w : S2) (h : det3 (u : E3) (v : E3) (w : E3) ≠ 0) :
    0 < sphAngle u v w := by
  rcases lt_or_eq_of_le (sphAngle_nonneg u v w) with hlt | heq
  · exact hlt
  · exact absurd (det3_zero_of_sphAngle_zero u v w heq.symm) h

/-! ## §3. Strict arms have positive joints (the `armMono` bridge lemma). -/

/-- **Strict polygon joints are `> 0`.**  Mirror of `strict_jointAngle_lt_pi`: the joint triple of
a strictly convex arm has `det3 > 0` (strict non-incidence at `j = k + 2`), so the angle is
positive by the §2 bridge. -/
theorem strict_jointAngle_pos {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (k : Fin (n - 1)) :
    0 < jointAngle B k := by
  have hki : k.val < n - 1 := k.isLt
  have h2 : 2 ≤ n := hB.two_le
  rw [jointAngle]
  refine sphAngle_pos_of_det3_ne _ _ _ ?_
  have hP := hB.closed_convex.strict_nonincident
  have hik : k.val < n + 1 := by omega
  have hi1 : k.val + 1 < n + 1 := by omega
  have hi2 : k.val + 2 < n + 1 := by omega
  have hne1 : (⟨k.val + 2, hi2⟩ : Fin (n + 1)) ≠ ⟨k.val, hik⟩ := by
    intro h; have := congrArg Fin.val h; simp at this
  have hne2 : (⟨k.val + 2, hi2⟩ : Fin (n + 1)) ≠ (⟨k.val, hik⟩ : Fin (n + 1)) + 1 := by
    intro h
    have hsucc : ((⟨k.val, hik⟩ : Fin (n + 1)) + 1) = (⟨k.val + 1, hi1⟩ : Fin (n + 1)) := by
      apply Fin.ext
      simp [Fin.add_def, Nat.mod_eq_of_lt hi1]
    rw [hsucc] at h
    have := congrArg Fin.val h; simp at this
  have key := hP ⟨k.val, hik⟩ ⟨k.val + 2, hi2⟩ hne1 hne2
  have hsucc : ((⟨k.val, hik⟩ : Fin (n + 1)) + 1) = (⟨k.val + 1, hi1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp [Fin.add_def, Nat.mod_eq_of_lt hi1]
  rw [hsucc] at key
  exact ne_of_gt key

/-- **Strict arms have positive joints** — the bridge `armMono_of_MainPlus` needs. -/
theorem strictConvexSphArm_positiveJoints {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) : PositiveJoints B :=
  fun k => strict_jointAngle_pos hB k

/-- **The final arm lemma from `MainPlus`** (the strict-left headline shape survives the repair). -/
theorem armMono_of_MainPlus {n : ℕ} (hM : MainPlus n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B) :
    endpt A ≤ endpt B :=
  hM A B (strictConvexSphArm_toWeak hA) (strictConvexSphArm_positiveJoints hA) hB hside hangle

/-! ## §4. Ears inherit positive joints (the routine Layer-2 preservation lemma). -/

/-- **Interval sub-arms inherit positive joints**: the ear's interior joints are exactly the
parent's joints `a + i` (`intervalArm_jointAngle`). -/
theorem intervalArm_positiveJoints {N : ℕ} {A : Fin (N + 1) → S2} (a m : ℕ) (hb : a + m ≤ N)
    (hpos : PositiveJoints A) :
    PositiveJoints (intervalArm A a m hb) := by
  intro i
  rw [intervalArm_jointAngle A a m hb i]
  exact hpos ⟨a + i.val, by have := i.isLt; omega⟩

/-! ## §5. No antipodal vertex pairs (kills the antipodal branch of the endgame table). -/

/-- **No two vertices of a weakly convex arm are antipodal** (both sit in one open hemisphere). -/
theorem weakConvex_no_antipodal {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (r s : Fin (n + 1)) :
    (A r : E3) ≠ -(A s : E3) := by
  obtain ⟨h, _, hpos⟩ := hA.closed_convex.open_hemisphere
  intro heq
  have hr := hpos r
  have hs := hpos s
  rw [heq, inner_neg_right] at hr
  linarith

/-! ## §6. The `(0, n−1)` endgame arithmetic. -/

/-- **Endpoint bound from a folded-flat tail.**  If the last vertex `An` is folded flat between
`An1` (the second-to-last) and `A0` (`hflatTail`), the diagonal inequality holds at `(0, n−1)`
(`hdiag`), and the last sides agree (`hsideLast`), then the endpoint bound follows from the
spherical triangle inequality on `B`'s corner.  Stated pointwise on the six sphere points, so it
can be instantiated by any index bookkeeping. -/
theorem endpoint_le_of_tail_fold {A0 An1 An B0 Bn1 Bn : S2}
    (hflatTail : sDist A0 An1 = sDist A0 An + sDist An An1)
    (hdiag : sDist A0 An1 ≤ sDist B0 Bn1)
    (hsideLast : sDist An An1 = sDist Bn Bn1) :
    sDist A0 An ≤ sDist B0 Bn := by
  have htri : sDist B0 Bn1 ≤ sDist B0 Bn + sDist Bn Bn1 := sDist_triangle B0 Bn Bn1
  have h1 : sDist A0 An = sDist A0 An1 - sDist An An1 := by linarith
  rw [h1, hsideLast]
  linarith

/-! ## §7. Sanity anchors (playbook §3.3 non-vacuity / immunity guards). -/

/-- **The FFCT17 zigzag fails `PositiveJoints`** — `MainPlus` is immune to the committed
counterexample (its joint at `0` is `0`, not positive). -/
theorem zigzag_not_positiveJoints : ¬ PositiveJoints ProofsInTheBook.ZinanFFCT17.aArm := by
  intro hpos
  have h0 := hpos ⟨0, by omega⟩
  have hzero : jointAngle ProofsInTheBook.ZinanFFCT17.aArm (⟨0, by omega⟩ : Fin (3 - 1)) = 0 := by
    rw [jointAngle]
    have e0 : (ProofsInTheBook.ZinanFFCT17.aArm ⟨0, by omega⟩) = ProofsInTheBook.ZinanFFCT17.pQ :=
      rfl
    have e1 : (ProofsInTheBook.ZinanFFCT17.aArm ⟨0 + 1, by omega⟩)
        = ProofsInTheBook.ZinanFFCT17.qQ := rfl
    have e2 : (ProofsInTheBook.ZinanFFCT17.aArm ⟨0 + 2, by omega⟩)
        = ProofsInTheBook.ZinanFFCT17.pQ := rfl
    rw [e0, e1, e2]
    exact ProofsInTheBook.ZinanFFCT17.sphAngle_self_zero ProofsInTheBook.ZinanFFCT17.shortArc_qp
  rw [hzero] at h0
  exact lt_irrefl 0 h0

/-- **`PositiveJoints` is satisfiable** — e.g. by any strictly convex arm (the FFCT17 companion). -/
theorem positiveJoints_satisfiable : PositiveJoints ProofsInTheBook.ZinanFFCT17.bArm :=
  strictConvexSphArm_positiveJoints ProofsInTheBook.ZinanFFCT17.bArm_strictConvex

/-- **`MainPlus` keeps the proven base** — at `n = 2` it follows from the proven `Main 2` (the
extra hypothesis is simply discarded). -/
theorem mainPlus_two : MainPlus 2 :=
  fun A B hA _ hB hside hangle => main_two A B hA hB hside hangle

/-- `MainPlus` below level two, from the proven `main_of_lt_two`. -/
theorem mainPlus_of_lt_two {m : ℕ} (hm : m < 2) : MainPlus m :=
  fun A B hA _ hB hside hangle => main_of_lt_two hm A B hA hB hside hangle

#print axioms ProofsInTheBook.ZinanFFCT18.strictConvexSphArm_positiveJoints
#print axioms ProofsInTheBook.ZinanFFCT18.intervalArm_positiveJoints
#print axioms ProofsInTheBook.ZinanFFCT18.weakConvex_no_antipodal
#print axioms ProofsInTheBook.ZinanFFCT18.endpoint_le_of_tail_fold
#print axioms ProofsInTheBook.ZinanFFCT18.zigzag_not_positiveJoints
#print axioms ProofsInTheBook.ZinanFFCT18.mainPlus_two

end ProofsInTheBook.ZinanFFCT18
