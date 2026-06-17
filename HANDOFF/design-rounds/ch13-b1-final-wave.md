[intro]
I’ll read the new FFCT25–27 plus the admissible-supremum/opening outcome files to avoid guessing the monitored-family and hemi-margin plumbing.

[answer]
1. **Current inventory**

FFCT26 has closed the derivative layer: `det3_cross_expansion`, `det3_axis_cross_eq_neg_gram(_S2)`, `hasDerivAt_rot`, `hasDerivAt_mixedSupport`, `deriv_nonpos_of_left_nonneg_zero`, and `shortArc_axis_opened_tail`. fileciteturn proved the old `halpha_of_hbeta_and_positive_axis_joint` hypothesis set unsatisfiable, landed the coefficient equivalences `hbeta_iff_bcoef_nonneg` / `halpha_iff_acoef_nonneg`, and closed `StuckAtKData_of_axis_edge_binding` conditional on an `hα` input. fileciteturn114file0L15-L36

2. **Answer to Q1: the `a ≥ 0` supplier**

For the axis-edge binding branch, do **not** use an out-of-plane witness. The stronger fact is that the whole branch contradicts `PositiveJoints` once `hβ` is known.

Use FFCT27’s theorem:

```lean
design_halpha_hyps_unsatisfiable
```

It says:

```lean
det3 p mid q = 0 →
ShortArc mid q →
ShortArc mid p →
hβ ≥ 0 →
0 < sphAngle p mid q →
False
```

fileciteturn116 axis-edge binding is impossible**

```lean
theorem axis_edge_binding_false_of_positiveJoints
    {n : ℕ} {A B : Fin (n + 1 + 1) → S2} {δ : ℝ}
    {i : ℕ} (hi_axis : i + 1 = n)
    (hpos : PositiveJoints (openArm A δ))
    (hsa : ShortArc (openArm A δ ⟨i + 1, by omega⟩)
                    (openArm A δ (Fin.last (n + 1))))
    (hpm : ShortArc (openArm A δ ⟨i + 1, by omega⟩)
                    (openArm A δ ⟨i, by omega⟩))
    (hsupp :
      sOrient (openArm A δ ⟨i, by omega⟩)
              (openArm A δ ⟨i + 1, by omega⟩)
              (openArm A δ (Fin.last (n + 1))) = 0)
    (hβ : 0 ≤
      (⟪(openArm A δ ⟨i, by omega⟩ : E3),
          (openArm A δ (Fin.last (n + 1)) : E3)⟫ : ℝ)
      - (⟪(openArm A δ ⟨i, by omega⟩ : E3),
          (openArm A δ ⟨i + 1, by omega⟩ : E3)⟫ : ℝ)
        * (⟪(openArm A δ (Fin.last (n + 1)) : E3),
            (openArm A δ ⟨i + 1, by omega⟩ : E3)⟫ : ℝ)) :
    False
```

Sketch: instantiate `design_halpha_hyps_unsatisfiable` with  
`p = openArm A δ ⟨i⟩`, `mid = openArm A δ ⟨i+1⟩`, `q = openArm A δ last`. The joint positivity is exactly `hpos ⟨i, by omega⟩`, after unfolding `jointAngle`. `hsupp` is the collinearity input.

Classification: **worker/needs-care**, 50–90 lines.

4. **Brick A′: if an `a ≥ 0` supplier is still required**

```lean
theorem acoef_nonneg_of_axis_edge_binding
    {n : ℕ} {A B : Fin (n + 1 + 1) → S2} {δ : ℝ}
    {i : ℕ} (hi_axis : i + 1 = n)
    (hfalse : False) :
    ∀ a b : ℝ,
      (openArm A δ ⟨i, by omega⟩ : E3)
        = a • (openArm A δ ⟨i + 1, by omega⟩ : E3)
          + b • (openArm A δ (Fin.last (n + 1)) : E3) →
      0 ≤ a
```

Sketch: `intro a b hp; exact False.elim hfalse`. This is honest because the axis-edge branch is inconsistent under `PositiveJoints + hβ`; using a witness readout here would hide the stronger contradiction.

Classification: **routine**, 5 lines.

5. **Why the out-of-plane witness route is not recommended**

The candidate edge `(axis, tail)` at `p` is useless because `p, axis, tail` are already coplanar, so `det3 axis tail p = 0`. A witness `z` would need a controlled sign for `D = det3 axis tail z`; but if `D = 0`, the readout collapses, and if `D ≠ 0`, the support that reads `a` depends on the chosen directed edge. The contradiction route avoids all of this and is strictly stronger.

6. **Answer to Q2: monitored pairs**

There are two monitored-family regimes.

In `SphericalAdmissibleSup`, the legacy last-joint family monitors **all pairs**:

```lean
def combinedSupport ... :
  Option (Fin (n+1+1) × Fin (n+1+1)) → ℝ → ℝ
  | none => targetSlack A T
  | some ij => mixedSupport A ij
```

and `augmentedSupport` adds `hemiMargin`. citeturnnon-incident edge–vertex pairs**:

```lean
def NonIncident (n : ℕ) : Type :=
  {c : Fin (n + 1) × Fin (n + 1) // c.2 ≠ c.1 ∧ c.2 ≠ c.1 + 1}

def supportConstraint ... (c : NonIncident n) : ℝ → ℝ :=
  interiorSupport A K (c.1.1, c.1.1 + 1, c.1.2)
```

citeturn normalization decision**

For the corrected `MainPlus` proof, use `SphericalMonitoredSup`, not the legacy all-pair `SphericalAdmissibleSup` family. Then “binding pair is a genuine edge-support triple” is already in the type: `c : NonIncident n` gives edge `(c.1.1, c.1.1+1)` and vertex `c.1.2`.

Remaining normalization is **not** “all bindings normalize to the axis edge.” That is false/unsupported. The correct split is:

```lean
theorem supportBinding_dispatch
    {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3}
    (c : NonIncident n)
    :
    c.1.1 + 1 = (openingAxis k).val
      ∨ c.1.1 + 1 ≠ (openingAxis k).val
```

Axis-edge branch: contradiction by Brick A.  
Non-axis branch: route through `FoldedFlatCutTransportPlus` / FFCT25 after obtaining the genuine fold data.

Classification: **routine split**, but non-axis fold-data extraction remains **master**.

8. **Answer to Q3: hemiMargin**

Legacy `SphericalAdmissibleSup`:

```lean
def hemiMargin (A : Fin (n+1+1) → S2) (h : E3) : ℝ → ℝ :=
  fun θ => ⟪h, rot (openAxis A) θ (A (Fin.last (n+1)))⟫
```

citeturn119lean
def hemiMargin (A : Fin (n+1) → S2) (K : Fin (n+1)) (h₀ : E3) (r : Fin (n+1)) : ℝ → ℝ :=
  fun θ => ⟪h₀, ((openTail A K θ r : S2) : E3)⟫
```

citeturn124file0L92 NonIncident n, supportConstraint ... c δ* = 0) ∨
(∃ r : Fin (n+1), hemiMargin ... r δ* = 0)
```

citeturn126file0L38 branch is **not already discharged**. `SphericalOpeningOutcome` says the STUCK boundary outcome still needs a boundary-glue fact: pure hemisphere-stuck must force a vanishing non-incident support, or otherwise produce the weak opened arm. citeturn123:

```lean
theorem hemiStuck_forces_supportStuck_or_weakConvex
    {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3} {Tcap : ℝ}
    (hA : StrictConvexSphArm A)
    (hpos : PositiveJoints (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap)))
    (hhem : ∃ r : Fin (n + 1),
      hemiMargin A (openingAxis k) h₀ r (monitoredSup A B k h₀ Tcap) = 0)
    (hsupports : ∀ c : NonIncident n,
      0 ≤ supportConstraint A (openingAxis k) c (monitoredSup A B k h₀ Tcap)) :
    (∃ c : NonIncident n,
      supportConstraint A (openingAxis k) c (monitoredSup A B k h₀ Tcap) = 0)
```

Sketch: if no support constraint vanishes, then all supports are positive by closure + nonzero; `reach_strictConvex_interior` can build strict convexity provided hemisphere margins are positive. But a hemi margin is zero, so strict convexity fails only through hemisphere; show this is incompatible with open hemisphere of the original strict arm plus rotation before any support vanishes, or identify the first support forced by boundary contact. This is the real hemi-stuck brick.

Classification: **master**, 200–350 lines.

10. **Answer to Q4: final wrapper chain**

Once a support-stuck `c : NonIncident n` is available:

```lean
supportConstraint A (openingAxis k) c δ* = 0
```

the opened arm is

```lean
Aδ := openTail A (openingAxis k) δ*
```

and the support is already

```lean
sOrient (Aδ c.1.1) (Aδ (c.1.1 + 1)) (Aδ c.1.2) = 0
```

by `supportConstraint_apply`. citeturn124file0Plus
    {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {h₀ : E3} {Tcap : ℝ}
    (hcut : FoldedFlatCutTransportPlus)
    (ih : ∀ m, m < n → MainPlus m)
    (hAδweak : WeakConvexSphArm Aδ)
    (hAδpos : PositiveJoints Aδ)
    (hB : StrictConvexSphArm B)
    (hsideδ : SameSides Aδ B)
    (hangleδ : JointLe Aδ B)
    (c : NonIncident n)
    (hzero : supportConstraint A (openingAxis k) c δ* = 0) :
    endpt Aδ ≤ endpt B
```

Axis-edge subcase: close by `axis_edge_binding_false_of_positiveJoints`.  
Non-axis subcase: build `StuckAtKData` or directly call `FoldedFlatCutTransportPlus` once `hcol` is extracted; then `stuckAtK_betweenness → far_fold_boundary_classification_final → endpoint endgame`.

11. **Which arm does FFCT25 use?**

FFCT25’s final classification applies to the **opened arm** `Aδ`, not the original arm. Its hypotheses are `WeakConvexSphArm A`, `PositiveJoints A`, `StrictConvexSphArm B`, `JointLe A B`, and the nondegenerate fold datum; in the stuck branch instantiate `A := Aδ`. citeturn111file0Arm Aδ
hAδpos  : PositiveJoints Aδ
hangleδ : JointLe Aδ B
```

These are exactly the opened-arm preservation outputs from the MainPlus DAG.

12. **Superseded conditionals**

Supersede old/legacy:

```lean
SphericalAdmissibleSup.reachOrStuck_at_sup
SphericalAdmissibleSup.augmented_reachOrStuck_at_sup
SphericalCutTransport.FoldedFlatCutTransport
SphericalStuckGeneral.stuckAtK_endpt_le
SphericalLastCornerStuck.lastCorner_endpt_pair
```

Use new/repaired:

```lean
ZinanFFCT18.FoldedFlatCutTransportPlus
SphericalMonitoredSup.opening_boundary_trichotomy
SphericalOpeningOutcome.interiorOpeningOutcome_holds
ZinanFFCT25.far_fold_boundary_classification_final
```

The legacy last-corner stuck route is not the right MainPlus spine; the corrected spine is interior monitored support/hemisphere trichotomy plus PositiveJoints.

13. **Degenerate audit**

`δ* = 0`: axis-edge binding at zero contradicts initial strict convexity if the support is nonincident; otherwise it is not in `NonIncident`. For legacy all-pair `mixedSupport`, this is another reason to avoid the all-pair family.

`q` antipodal to axis: killed by `ShortArc` of the opened last edge, already proved as `shortArc_axis_opened_tail`. cite axis`: impossible for an actual edge by `ShortArc`; in the opened arm, edge shortness must be part of `hAδweak`.

`A i = q`: killed by `NoNonadjacentRepeat` only for nonadjacent cases; for the adjacent axis-edge case, the stronger `axis_edge_binding_false_of_positiveJoints` closes it.

14. **Remaining ordered bricks**

1. `axis_edge_binding_false_of_positiveJoints` — worker/needs-care, 50–90 lines.  
2. `acoef_nonneg_of_axis_edge_binding` — routine if still needed, 5 lines by exfalso.  
3. `supportStuck_dispatch_MainPlus` — master wrapper, 150–250 lines.  
4. `hemiStuck_forces_supportStuck_or_weakConvex` — master, 200–350 lines.  
5. `interiorOpeningOutcomePlus_holds` — master wrapper replacing old branch plumbing, 150–250 lines.  
6. `SZOpeningStepPlus_of_InteriorOpeningOutcomePlus` — needs-care, 100–180 lines.  
7. `mainPlus_all` / headline swap — routine once the step is available.
