[intro]
I’ll check FFCT21/22 for the exact landed names around `TailConePropagates`, `OnFoldRay`, and the boundary-classification theorem, then I’ll give the remaining master-brick route.

I’ve got the FFCT21 predecessor-kill API. I’m checking FFCT22’s exact `OnFoldRay` and tail-propagation definitions now so the signatures below align with the committed names.

[answer]
1. **Verdict on the out-of-plane witness**

Yes: `PositiveJoints` extracts an off-plane witness, but not enough to discharge the old `TailConePropagates` as stated. After FFCT21 gives `i = 0`, write

```lean
A 0 = a • A 1 + b • A j, 0 < b.
```

Then weak support of edge `(A0,A1)` at `A2` gives

```lean
0 ≤ det3 (A0) (A1) (A2) = -b * det3 (A1) (Aj) (A2),
```

so `det3 (A1) (Aj) (A2) ≤ 0`. If equality held, the consecutive triple `(A0,A1,A2)` would be coplanar, so the joint at `A1` is `0` or `π`, contradicting `PositiveJoints` plus `jointAngle_lt_pi`; hence the witness is strict with **negative** orientation. FFCT21 already has the flat-joint bridge `sphAngle_eq_zero_or_pi_of_det3_zero`. fileciteturn not try to prove old `TailConePropagates`**

The old `TailConePropagates` asks for `OnFoldRay`, i.e. NNReal cone membership:

```lean
structure OnFoldRay (v w z : S2) : Prop where
  col : det3 (v : E3) (w : E3) (z : E3) = 0
  coeff : (z : E3) ∈ Submodule.span NNReal ({(v : E3), (w : E3)} : Set E3)
```

fileciteturn107file uses that three consecutive vertices lie in the same real 2-plane, via `coplanar_triple_det3_zero`; the nonnegative cone signs are not used in `far_fold_tail_not_interior`. fileciteturn108file0L7-L38

So the recommended repair is: **replace `TailConePropagates` by a weaker signed-line propagation predicate**, not a full NNReal cone propagation.

---

3. **New weak tail predicate**

```lean
structure OnFoldLineCoeff {n : ℕ}
    (A : Fin (n + 1) → S2) (j : ℕ) (hj : j < n + 1)
    (r : ℕ) (hr : r < n + 1) : Prop where
  c d : ℝ
  hd_nonneg : 0 ≤ d
  repr :
    (A ⟨r, hr⟩ : E3) =
      c • (A ⟨1, by omega⟩ : E3) + d • (A ⟨j, hj⟩ : E3)
```

Sketch: this records real span plus the sign of the `Aj` coefficient; it drops the unnecessary sign of the `A1` coefficient. The strict version is `0 < d`, needed only to run FFCT22’s determinant step. This avoids the hard and probably unnecessary task of proving full `Submodule.span NNReal {A1,Aj}` membership.

Classification: routine, 20–40 lines.

---

4. **Brick T1: controlled off-plane witness**

```lean
theorem fold_A2_witness_negative {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {j : ℕ} (hj : j < n + 1) (hjfar : 2 < j)
    {a b : ℝ} (hb : 0 < b)
    (hfold :
      (A ⟨0, by omega⟩ : E3) =
        a • (A ⟨1, by omega⟩ : E3) + b • (A ⟨j, hj⟩ : E3)) :
    det3 (A ⟨1, by omega⟩ : E3) (A ⟨j, hj⟩ : E3)
      (A ⟨2, by omega⟩ : E3) < 0
```

Sketch: weak support of edge `(0,1)` at vertex `2` gives `0 ≤ det3 A0 A1 A2`. Rewrite with `hfold` to get `0 ≤ -b * D₂`, hence `D₂ ≤ 0`. If `D₂ = 0`, then `A0,A1,A2` are coplanar and `far_fold_tail_not_interior`’s local bridge gives joint `0 ∨ π`, contradicted by `hposA` and `jointAngle_lt_pi`.

Classification: needs-care, 80–140 lines.  
Sign pitfall: the identity is `det3 A0 A1 A2 = -b * det3 A1 Aj A2`; reversing the base order flips the whole route.

---

5. **Brick T2: coefficient sign read by witness**

```lean
theorem fold_coeff_d_nonneg_of_A2_witness {n : ℕ} {A : Fin (n + 1) → S2}
    {j r : ℕ} (hj : j < n + 1) (hr : r < n + 1)
    (hD2 :
      det3 (A ⟨1, by omega⟩ : E3) (A ⟨j, hj⟩ : E3)
        (A ⟨2, by omega⟩ : E3) < 0)
    {c d : ℝ}
    (hrepr :
      (A ⟨r, hr⟩ : E3) =
        c • (A ⟨1, by omega⟩ : E3) + d • (A ⟨j, hj⟩ : E3))
    (hsupp12 :
      0 ≤ det3 (A ⟨1, by omega⟩ : E3) (A ⟨2, by omega⟩ : E3)
        (A ⟨r, hr⟩ : E3)) :
    0 ≤ d
```

Sketch: expand `hsupp12` using `hrepr`. The determinant is

```lean
det3 A1 A2 (c A1 + d Aj) = d * det3 A1 A2 Aj = -d * D2.
```

Since `D2 < 0`, nonnegativity implies `0 ≤ d`. This uses weak support of edge `(A1,A2)` at every vertex.

Classification: routine/needs-care, 40–70 lines.

---

6. **Brick T3: strict or absorption**

```lean
theorem fold_coeff_d_pos_or_absorb {n : ℕ} {A B : Fin (n + 1) → S2}
    (hposA : PositiveJoints A) (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {j r : ℕ} (hj : j < n + 1) (hr : r < n + 1)
    (hline_prev : ∃ p q : ℝ,
      p • (A ⟨1, by omega⟩ : E3) + q • (A ⟨j, hj⟩ : E3) =
        (A ⟨r - 1, by omega⟩ : E3))
    (hline_curr : ∃ p q : ℝ,
      p • (A ⟨1, by omega⟩ : E3) + q • (A ⟨j, hj⟩ : E3) =
        (A ⟨r, hr⟩ : E3))
    {c d : ℝ}
    (hd : 0 ≤ d)
    (hline_next :
      (A ⟨r + 1, by omega⟩ : E3) =
        c • (A ⟨1, by omega⟩ : E3) + d • (A ⟨j, hj⟩ : E3))
    (hsau : ShortArc (A ⟨r, hr⟩) (A ⟨r - 1, by omega⟩))
    (hsav : ShortArc (A ⟨r, hr⟩) (A ⟨r + 1, by omega⟩)) :
    0 < d ∨ False
```

Sketch: if `d > 0`, continue propagation. If `d = 0`, the three consecutive vertices `A(r-1), A r, A(r+1)` are all in the real span of `{A1,Aj}`, hence `det3 = 0`, and `far_fold_tail_not_interior` gives `False`. This is the zero-coefficient absorption missing from the old cone-propagation story.

Classification: needs-care, 80–120 lines.

---

7. **Brick T4: one signed-line propagation step**

```lean
theorem far_fold_tail_line_step_or_absorb {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {j t : ℕ} (hj : j < n + 1) (ht : t + 1 < n + 1)
    (hD2 :
      det3 (A ⟨1, by omega⟩ : E3) (A ⟨j, hj⟩ : E3)
        (A ⟨2, by omega⟩ : E3) < 0)
    (hfold0 : OnFoldLineCoeff A j hj 0 (by omega))
    (hcurr : OnFoldLineCoeff A j hj t (by omega))
    (hdcurr : 0 < hcurr.d)
    (hprev_line : ∃ p q : ℝ,
      p • (A ⟨1, by omega⟩ : E3) + q • (A ⟨j, hj⟩ : E3) =
        (A ⟨t - 1, by omega⟩ : E3)) :
    (∃ hnext : OnFoldLineCoeff A j hj (t + 1) (by omega), 0 < hnext.d) ∨ False
```

Sketch: FFCT22’s `far_fold_tail_collinear_step` gives `det3 A1 Aj A(t+1)=0`, hence real-span representation of `A(t+1)`. Brick T2 gives nonnegative `Aj` coefficient using the witness `A2`. Brick T3 upgrades `0≤d` to either `0<d` or immediate contradiction.

Classification: master/needs-care, 140–220 lines.

---

8. **Brick T5: start the tail propagation at `j`**

```lean
theorem tail_line_start_at_j {n : ℕ} {A : Fin (n + 1) → S2}
    {j : ℕ} (hj : j < n + 1) :
    ∃ hcurr : OnFoldLineCoeff A j hj j hj, 0 < hcurr.d
```

Sketch: take `c = 0`, `d = 1`, so `A j = 0•A1 + 1•Aj`. This starts propagation forward from the fold endpoint `Aj`, not from `A1`; that avoids the `d=0` problem at `A1`.

Classification: routine, 10–20 lines.

---

9. **Brick T6: forward propagation until contradiction**

```lean
theorem tail_line_propagation_refutes_interior_j {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {j : ℕ} (hj : j < n + 1) (hjtail : j ≤ n - 2)
    {a b : ℝ} (hb : 0 < b)
    (hfold :
      (A ⟨0, by omega⟩ : E3) =
        a • (A ⟨1, by omega⟩ : E3) + b • (A ⟨j, hj⟩ : E3)) :
    False
```

Sketch: get `D2 < 0` from T1 and initialize at `t=j` via T5. Iterate T4 while `t+1 < n+1`; because `j ≤ n-2`, at least one step exists. Either a zero-coefficient absorption gives `False`, or enough consecutive line vertices accumulate and FFCT22’s `far_fold_tail_not_interior` fires.

Classification: master, 180–300 lines.  
Sign pitfall: the propagation moves **forward from `j`**, not from `1`; starting at `1` has coefficient `d=0` and cannot drive FFCT22’s determinant step.

---

10. **Brick T7: replace `TailConePropagates` in B5**

```lean
theorem far_fold_boundary_classification_no_tail_hyp {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    (hnd : ∃ a b : ℝ≥0, 0 < (a : ℝ) ∧ 0 < (b : ℝ) ∧
      (a : ℝ) • (A ⟨i + 1, by omega⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3) =
        (A ⟨i, by omega⟩ : E3)) :
    i = 0 ∧ (j = n ∨ j = n - 1)
```

Sketch: first use FFCT21’s `far_fold_boundary_classification_of_nondeg` to get `i=0`. Rewrite the fold datum as `A0 = a•A1 + b•Aj` with `b>0`. If `j ≤ n-2`, call T6 for contradiction; hence `j = n` or `j = n-1`.

Classification: needs-care/master wrapper, 70–120 lines.  
This supersedes FFCT22’s conditional `far_fold_boundary_classification`, whose current tail hypothesis is explicit. file. **Audit against zigzag and fully planar arms**

The `[p,q,p,q]` zigzag fails immediately at `PositiveJoints`, already proved in FFCT18, so none of the signed-line machinery is invoked. Fully planar arms also fail once three consecutive vertices are in the fold plane: FFCT22’s `far_fold_tail_not_interior` converts coplanarity to joint `0 ∨ π`, then `PositiveJoints` and `jointAngle_lt_pi` refute it. fileciteturn108file0L7-L38

The sign-sensitive place is T1/T2: the witness orientation must be fixed as

```lean
D2 = det3 (A1) (Aj) (A2) < 0.
```

Using `det3 (A1) (A2) (Aj)` instead silently flips the coefficient inequality.

---

12. **Why this is better than arbitrary out-of-plane witness extraction**

A generic witness `v_k` has uncontrolled sign. The specific witness `A2` has a forced sign from weak support of the fold edge `(A0,A1)`, and it reads the `Aj` coefficient through weak support of edge `(A1,A2)`. This uses only `WeakConvexSphArm + PositiveJoints`, not strict support of `A`, and avoids the full NNReal cone re-extraction that FFCT22 scoped as the master gap.
