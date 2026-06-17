[intro]
I’ll check FFCT30/34/36 for the exact tilt/separation lemmas and the current hemi-stuck dichotomy before recommending whether to repair the statement or change the monitored family.

[answer]
1. **Inventory verdict**

`FFCT30` already has the finite tilt core:

```lean
exists_perturbed_normal_of_tangent
exists_unit_perturbed_normal_of_tangent
```

It needs a tangent direction `t` positive on the `h₀`-equator set. filecite has the any-normal weak-convex assembler:

```lean
weakConvex_of_supportStuckW_of_hemiPos_anyH
```

It consumes weak supports, opened edge distinctness, and **some** strict hemisphere witness `∃ h'`. fileciteturn144file0 the fixed-`h₀` residual

```lean
SupportStuckMarginsPosAtSupWB
```

is the wrong target. Simultaneous support + hemi binding makes fixed `h₀` strictness false.

---

2. **Support-stuck honest replacement**

Replace `SupportStuckMarginsPosAtSupWB` by:

```lean
def SupportStuckOpenHemisphereAtSupWB : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∀ h₀ : E3, ‖h₀‖ = 1 → (∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) →
      (∃ c : NonIncident n,
        supportConstraint A (openingAxis k) c (-(monitoredSupWB A B k h₀)) = 0) →
      ∃ h' : E3, ‖h'‖ = 1 ∧
        ∀ r : Fin (n + 1),
          0 < (⟪h', ((openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)) r : S2) : E3)⟫ : ℝ)
```

Sketch: closure gives all supports `≥ 0`. A support-stuck zero is allowed. Instead of requiring fixed `h₀` margins strict, prove existence of a tilted normal using a weak-support collapse argument. Feed the resulting `∃ h'` into `weakConvex_of_supportStuckW_of_hemiPos_anyH`.

Classification: **master**, 300–500 lines.

---

3. **Does FFCT36 collapse survive one vanishing support?**

The strict-support version does **not** apply literally, because one support may be zero. But the convex-collapse argument should survive if its conclusion is strengthened to use `PositiveJoints` / joint-in-`(0,π)` instead of strict supports.

The right theorem is not “strict supports give equator tangent”; it is:

```lean
theorem equatorTangentExists_of_weakSupports_jointOpen
    {n : ℕ} {P : Fin (n + 1) → S2} {h₀ : E3}
    (hside : ∀ i : Fin (n + 1), ShortArc (P i) (P (i + 1)))
    (hsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (P i) (P (i + 1)) (P j))
    (hjopen : ∀ r : Fin (n - 1), 0 < jointAngle P r ∧ jointAngle P r < Real.pi)
    (hmargin : ∀ r : Fin (n + 1), 0 ≤ (⟪h₀, (P r : E3)⟫ : ℝ)) :
    ∃ t : E3,
      ∀ r : Fin (n + 1),
        (⟪h₀, (P r : E3)⟫ : ℝ) = 0 →
          0 < (⟪t, (P r : E3)⟫ : ℝ)
```

Sketch: suppose no such `t`; by finite separation, `0 ∈ convexHull Z`, where `Z` is the equator set. For every edge support functional, the convex combination has value `0`, while each term is `≥ 0`, so every positive-weight equator vertex lies in every edge plane. If two non-antipodal positive-weight equator vertices occur, all edge planes coincide, forcing consecutive triples coplanar and a joint `0` or `π`.

Classification: **master**, 350–650 lines.

---

4. **Antipodal/collapse subcase**

The dangerous separation subcase is when `0 ∈ convexHull Z` is represented by an antipodal pair. Do not try to kill antipodality merely from fixed `h₀`; both points are on its equator.

Use the stronger “common edge-plane” collapse:

```lean
theorem commonLine_collapse_forces_flat_joint
    {n : ℕ} {P : Fin (n + 1) → S2} {z : S2}
    (hside : ∀ i : Fin (n + 1), ShortArc (P i) (P (i + 1)))
    (hallplanes : ∀ i : Fin (n + 1),
      det3 (P i : E3) (P (i + 1) : E3) (z : E3) = 0)
    (hjopen : ∀ r : Fin (n - 1), 0 < jointAngle P r ∧ jointAngle P r < Real.pi) :
    False
```

Sketch: every edge great circle contains the common axis line `ℝ z`. If a shared vertex is not a pole, two consecutive edge planes both contain `z` and that vertex, hence are the same plane; this propagates planarity and yields a flat joint. If every shared vertex were a pole, `ShortArc` kills adjacent antipodal/equal degeneracy.

Classification: **master**, 250–450 lines.

---

5. **Support-stuck assembler using the honest target**

```lean
theorem stuckOutcomeWB_supportVanish_anyH
    (hhemi : SupportStuckOpenHemisphereAtSupWB)
    (hclose : OpenedClosingEdgeDistinctAtSupWB)
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3}
    (hnorm : ‖h₀‖ = 1)
    (hhpos : ∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ))
    (hkdef : jointAngle A k < jointAngle B k)
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hvanish : ∃ c : NonIncident n,
      supportConstraint A (openingAxis k) c (-(monitoredSupWB A B k h₀)) = 0) :
    WeakConvexSphArm (openTail A (openingAxis k) (-(monitoredSupWB A B k h₀)))
```

Sketch: get closure supports from `supportWB_sOrient_nonneg`; get edge distinctness from `hclose`; get `∃ h'` from `hhemi`; apply `weakConvex_of_supportStuckW_of_hemiPos_anyH`.

Classification: **worker/needs-care**, 80–130 lines.

---

6. **PureHemiProgressWB verdict**

`PureHemiProgressWB` as currently shaped is very likely **false**. At a pure hemi-stuck WB supremum, the arm can be strictly convex after tilting, no W-support vanishes, and the target joint need not have reached. FFCT41 itself says this branch is a genuine residual and that it is not a NonIncident support payload. fileciteturn137 the honest diagnosis: do not try to prove `ReachWB ∨ support vanish` at the same `δ*_WB` from a pure hemi event. That would fake progress.

---

7. **Recommended fix for pure hemi: choose (c), drop hemi monitors**

The cleanest design is option **(c)**: remove hemisphere members from the monitored family. Keep only:

1. nonincident support constraints,
2. joint slack,
3. base cap support.

Then prove open-hemisphere existence from weak supports + positive/nonflat joints using the collapse theorem above. This removes the hemi-stuck branch entirely.

New family:

```lean
def monitoredFamilyWBS
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    (NonIncident n ⊕ Unit) ⊕ Unit → ℝ → ℝ
  | Sum.inl (Sum.inl c) => fun θ => supportConstraint A (openingAxis k) c (-θ)
  | Sum.inl (Sum.inr ()) => fun θ =>
      jointAngle B k - openedInteriorJointAngle A k (-θ)
  | Sum.inr () => baseCapSupportW A k
```

Here `WBS = Widening + Base + Supports`, no hemisphere.

Classification: **needs-care refactor**, 120–180 lines.

---

8. **WBS trichotomy**

```lean
def ReachWBS ... : Prop :=
  openedInteriorJointAngle A k (-(monitoredSupWBS A B k)) = jointAngle B k

def SupportStuckWBS ... : Prop :=
  ∃ c : NonIncident n,
    supportConstraint A (openingAxis k) c (-(monitoredSupWBS A B k)) = 0

def BaseStuckWBS ... : Prop :=
  baseCapSupportW A k (monitoredSupWBS A B k) = 0

theorem opening_boundary_trichotomyWBS :
  monitoredSupWBS A B k = Real.pi ∨
    ReachWBS A B k ∨ SupportStuckWBS A B k ∨ BaseStuckWBS A B k
```

Sketch: same `reach_or_stuck` engine as FFCT37/41. CAP is killed by the same deficit-bound argument; base cap is already monitored. No hemi branch exists.

Classification: **needs-care**, 120–200 lines.

---

9. **Open hemisphere from supports at the WBS supremum**

```lean
theorem openHemisphere_at_WBS_sup
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    {k : Fin (n - 1)}
    (hside : SameSides (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) B)
    (hangle : JointLe (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) B)
    (hpos : PositiveJoints (openTail A (openingAxis k) (-(monitoredSupWBS A B k))))
    :
    ∃ h' : E3, ‖h'‖ = 1 ∧
      ∀ r : Fin (n + 1),
        0 < (⟪h', ((openTail A (openingAxis k) (-(monitoredSupWBS A B k)) r : S2) : E3)⟫ : ℝ)
```

Sketch: use support closure `≥ 0`, side preservation for `ShortArc`, and `JointLe` with strict `B` to get all joints `<π`; combine with `PositiveJoints` for joints in `(0,π)`. Apply `equatorTangentExists_of_weakSupports_jointOpen` + FFCT30’s tilt lemma. This is the main theorem replacing all fixed-hemi residuals.

Classification: **master**, 400–750 lines.

---

10. **Weak/strict convexity at WBS sup**

Support branch:

```lean
theorem supportStuckWBS_weakConvex
    ... (hstuck : SupportStuckWBS A B k) :
    WeakConvexSphArm (openTail A (openingAxis k) (-(monitoredSupWBS A B k)))
```

Reach/no-stuck branch:

```lean
theorem reachWBS_strictConvex
    ... (hreach : ReachWBS A B k) (hnotSupport : ¬ SupportStuckWBS A B k) :
    StrictConvexSphArm (openTail A (openingAxis k) (-(monitoredSupWBS A B k)))
```

Sketch: support branch uses weak supports + open hemisphere. Reach/no-support branch upgrades `≥0` supports to `>0` via `¬ SupportStuckWBS`, then uses the same open hemisphere theorem.

Classification: **needs-care**, 150–250 lines each.

---

11. **Base-stuck remains as before**

Since `BaseStuckProgressW` is now a theorem after FFCT42, port it to WBS:

```lean
def BaseStuckProgressWBS : Prop :=
  ∀ n A B, StrictConvexSphArm A → StrictConvexSphArm B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
      BaseStuckWBS A B k →
        ReachWBS A B k ∨
        ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
          sOrient (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) i)
            (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (i + 1))
            (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) j) = 0
```

Sketch: copy the FFCT42 theorem proof, replacing `monitoredSupWB` with `monitoredSupWBS`; it should use only support/base/slack closure, not hemi monitors. If the existing proof mentions hemi closure, isolate those uses and replace by `openHemisphere_at_WBS_sup`.

Classification: **needs-care/master port**, 150–300 lines.

---

12. **Outcome theorem with no hemi residuals**

```lean
theorem interiorOpeningOutcomeWBS
    (hbase : BaseStuckProgressWBS) :
    SphericalArmAssembly.InteriorOpeningOutcome
```

Sketch: choose `A' = openTail A (openingAxis k) (-(monitoredSupWBS A B k))`. Sides and joints are as before. Trichotomy gives REACH / support / base; REACH gives deficit drop, support gives weak+vanishing support, base is collapsed by `hbase`.

Classification: **master wrapper**, 200–350 lines.

---

13. **If you keep WB instead of WBS**

Then replace `SupportStuckMarginsPosAtSupWB` with `SupportStuckOpenHemisphereAtSupWB`, but **do not** try to prove `PureHemiProgressWB`. Instead add a fourth branch to `InteriorOpeningOutcome`:

```lean
StrictConvexSphArm A' ∧ SameSides A' B ∧ JointLe A' B ∧
jointAngle A k < jointAngle A' k ∧ jointAngle A' k < jointAngle B k
```

Then the induction measure must be changed from deficit count alone to something that records continuous joint progress, which Lean cannot well-found directly without a quantitative discrete measure. This is much more invasive.

Classification: **not recommended**.

---

14. **Degenerate audit**

Simultaneous support + hemi binding: handled by `SupportStuckOpenHemisphereAtSupWB`; fixed `h₀` may fail, but `h'` exists.

Pure hemi with no support and no reach: this is exactly why `PureHemiProgressWB` is false-shaped; WBS removes it.

Antipodal equator pair in the collapse proof: cannot be killed by fixed `h₀`; must be killed by common-edge-plane collapse + `jointAngle ∈ (0,π)`.

Fully planar / zigzag stratum: killed by `PositiveJoints` and `jointAngle_lt_pi`, same as FFCT17/18 repair.

Constant arm: excluded by `StrictConvexSphArm A` at the opening input and by edge `ShortArc` preservation.

---

15. **Recommended ordered DAG**

1. `equatorTangentExists_of_weakSupports_jointOpen` — master, 350–650 lines.  
2. `openHemisphere_of_weakSupports_jointOpen` via FFCT30 tilt — master wrapper, 120–180 lines.  
3. `monitoredFamilyWBS`, `monitoredSupWBS`, trichotomy — needs-care, 150–250 lines.  
4. `openHemisphere_at_WBS_sup` — master, 250–450 lines.  
5. `supportStuckWBS_weakConvex` — needs-care, 150–220 lines.  
6. `reachWBS_strictConvex` — needs-care, 150–220 lines.  
7. `BaseStuckProgressWBS` port from FFCT42 — master/needs-care, 150–300 lines.  
8. `interiorOpeningOutcomeWBS` — master wrapper, 200–350 lines.  
9. Replace `mainPlus_headline_basestuck_free`’s hemisphere residual surface with `interiorOpeningOutcomeWBS`.

Bottom line: do not prove the fixed-margin residual, and do not prove pure-hemi progress at the same sup. Remove hemi monitoring and derive the open hemisphere from weak supports plus positive/nonflat joints.
