[intro]
I’ll inspect FFCT37/38 and the endpoint monotonicity lemma now, then I’ll choose between adding a base-cap monitor versus proving an intermediate straightening branch.

[answer]
1. **Banked endpoint monotonicity**

The exact endpoint companion is pointwise at the final angle, not whole-interval:

```lean
theorem endpt_openTail_interior_mono_neg
    {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1)) {δ : ℝ}
    (hδ0 : 0 ≤ δ)
    (hδπ : δ + sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) ≤ Real.pi) :
    endpt A ≤ endpt (openTail A (openingAxis k) (-δ))
```

It is re-exported in `corrected_endpt_mono`, and FFCT37’s `glueW_clause_i` applies it with `δ = monitoredSupW ... π`. citeturn131file0 ed straightening completion found**

I found endpoint monotonicity and hinge/triangle tools, but not a ready “base straightening completion” lemma of the form

```lean
sphAngle (A0) AK Alast = π →
endpt A = sDist A0 AK + sDist AK Alast →
endpt A ≤ endpt B
```

The repo comments around `SphericalOpeningGlue` say the endpoint sign is governed by the base-triangle support and that the banked monotonicity requires the cap. They do not package a separate straightening branch. citeturn133file0**

Choose **(a)**. It is the least invasive fix: make the admissible family stop before base branch overflow, so `GlueWBaseCap` becomes an admissibility consequence and no new intermediate-arm terminal branch is needed.

Option (b) is much more invasive: it requires a new “straightened intermediate arm completes the induction” branch, plus sub-arm IH comparisons for `d(A0,AK)` and `d(AK,Alast)` against `B`. That is not currently a consumer shape of `mainPlus_headline_final`, and it would need fresh deficit/drop bookkeeping for an intermediate `δ0`.

4. **Base monitor: correct sinusoid**

Let

```lean
K := openingAxis k
γbase := sphAngle (A 0) (A K) (A (Fin.last n))
qθ := rotS2 (A K) (-θ) (A (Fin.last n))
```

Use the support with edge order:

```lean
sOrient (A 0) (A K) qθ
```

The branch-free identity should be:

```lean
sOrient (A 0) (A K) (rotS2 (A K) (-θ) (A (Fin.last n)))
  =
‖tangentTo (A K) (A 0)‖
  * ‖tangentTo (A K) (A (Fin.last n))‖
  * Real.sin (γbase + θ)
```

This is the base analogue of FFCT37’s `support_openNeg_eq_sin`, whose statement for the joint-witness support is described as `sOrient p a (rotS2 a (-θ) q) = ‖u‖‖w‖ sin(γ+θ)`. citeturn128file0L20-L31θ`, not `sOrient (A K) (A 0) qθ`. `SphericalOpeningGlue` records the base orientation as `0 < sOrient (A 0)(A K)(A last)`, equivalently `sOrient (A K)(A 0)(A last) < 0`; the latter is the sign-bug diagnostic, not the monitor you want. citeturn133file0L35-L38

5. **New family definition**

Add a new base-capped widening family, extending FFCT37:

```lean
def baseCapSupportW
    {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) : ℝ → ℝ :=
  fun θ =>
    sOrient (A 0) (A (openingAxis k))
      (rotS2 (A (openingAxis k)) (-θ) (A (Fin.last n)))

def monitoredFamilyWB
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) :
    (NonIncident n ⊕ (Fin (n + 1) ⊕ Unit)) ⊕ Unit → ℝ → ℝ
  | Sum.inl o => monitoredFamilyW A B k h₀ o
  | Sum.inr () => baseCapSupportW A k
```

Worker, 30–50 lines. `continuous` follows from `continuous_monitoredFamilyW` and continuity of `rotS2`/det3, same style as `continuous_supportConstraint`.

6. **Base sinusoid lemma**

```lean
theorem baseSupport_openNeg_eq_sin
    {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1))
    (hbase0 : ShortArc (A (openingAxis k)) (A 0))
    (hbaseLast : ShortArc (A (openingAxis k)) (A (Fin.last n)))
    (θ : ℝ) :
    baseCapSupportW A k θ
      =
    ‖tangentTo (A (openingAxis k)) (A 0)‖
      * ‖tangentTo (A (openingAxis k)) (A (Fin.last n))‖
      * Real.sin (sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) + θ)
```

Needs-care/master, 100–180 lines. Proof mirrors FFCT37’s `support_openNeg_eq_sin`; the oriented datum comes from the base support sign recorded in `SphericalOpeningGlue`, not from `joint_axis_support_neg`.

7. **Base cap from admissibility**

```lean
theorem admissibleWB_baseCap
    {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3}
    (hbase0 : ShortArc (A (openingAxis k)) (A 0))
    (hbaseLast : ShortArc (A (openingAxis k)) (A (Fin.last n)))
    {θ : ℝ}
    (hadm : θ ∈ admissibleSet (monitoredFamilyWB A B k h₀) Real.pi) :
    θ + sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) ≤ Real.pi
```

Sketch: admissibility gives `0 ≤ baseCapSupportW A k θ`. Rewrite by `baseSupport_openNeg_eq_sin`; tangent norms are positive from `ShortArc`, so `0 ≤ sin(γbase+θ)`. With `θ ∈ [0,π]`, `γbase ∈ [0,π]`, and strict base nondegeneracy giving `γbase < π`, the same argument as `admissibleW_le_deficit` proves `γbase+θ ≤ π`. FFCT37 already has this exact sine-branch pattern for the joint witness. Needs-care, 100–150 lines.

8. **New supremum and `GlueWBaseCap`**

```lean
def monitoredSupWB
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) : ℝ :=
  sSup (admissibleSet (monitoredFamilyWB A B k h₀) Real.pi)

theorem GlueWBaseCap_of_monitoredSupWB
    {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hbase0 : ShortArc (A (openingAxis k)) (A 0))
    (hbaseLast : ShortArc (A (openingAxis k)) (A (Fin.last n)))
    (h0 : ∀ o, 0 ≤ monitoredFamilyWB A B k h₀ o 0) :
    monitoredSupWB A B k h₀
      + sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) ≤ Real.pi
```

Worker/needs-care, 60–100 lines. Use `sSup_mem_admissibleSet` for `monitoredFamilyWB` and then `admissibleWB_baseCap`.

9. **Trichotomy with new BaseStuck branch**

The new trichotomy has one extra branch:

```lean
def BaseStuckW
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) : Prop :=
  baseCapSupportW A k (monitoredSupWB A B k h₀) = 0

theorem opening_boundary_trichotomyWB :
  monitoredSupWB A B k h₀ = Real.pi ∨
    ReachWB A B k h₀ ∨ StuckWB A B k h₀ ∨ BaseStuckW A B k h₀
```

Needs-care, 80–120 lines. But for the existing spine, you do **not** need to consume `BaseStuckW` separately if clause (i) is the only missing residual: `BaseStuckW` is admissible and `GlueWBaseCap_of_monitoredSupWB` still gives the endpoint cap. It only matters for clause (ii) if `¬ StuckW → ReachW` was formulated without excluding base-stuck; update it to `¬ StuckWB ∧ ¬ BaseStuckW → ReachWB`, or absorb `BaseStuckW` into “not reach” and close by endpoint monotonicity + subsequent comparison if needed.

10. **Do not use straightening completion as primary route**

The tempting identity is:

```lean
sphAngle (A0) K Alast = Real.pi →
sDist A0 Alast = sDist A0 K + sDist K Alast
```

This is plausible via `sphAngle = π` → antiparallel tangents → equality in spherical triangle inequality. But the comparison

```lean
sDist A0 K + sDist K Alast ≥ endpt B
```

is not immediate. It requires two sub-arm IH bounds: one for `A[0..K]` vs `B[0..K]`, and one for `A[K..last]` vs `B[K..last]`, plus triangle inequality on `B`.

That is a new induction branch, not present in the current `InteriorOpeningGlueW` consumer. So route (b) is larger and riskier.

11. **If straightening branch is later needed**

Use this shape:

```lean
theorem baseStraight_endpoint_eq_sum
    {a k q : S2}
    (hπ : sphAngle a k q = Real.pi)
    (hka : ShortArc k a) (hkq : ShortArc k q) :
    sDist a q = sDist a k + sDist k q

theorem baseStraight_completion_by_IH
    (ih_left : sDist (A 0) (A K) ≤ sDist (B 0) (B K))
    (ih_right : sDist (A K) (A last) ≤ sDist (B K) (B last))
    (hπ : sphAngle (A 0) (A K) (A last) = Real.pi) :
    endpt A ≤ endpt B
```

Sketch: first theorem by spherical triangle equality. Second theorem uses `baseStraight_endpoint_eq_sum`, adds the two IH inequalities, then uses `sDist_triangle (B 0) (B K) (B last)`.

Master, 200–300 lines if sub-arm IH wrappers are absent.

12. **Degenerate audit**

`base + δ = π` at `δ=0`: for a strict arm, the base triple `(A0,K,last)` should be nondegenerate unless incident; if it is π, the whole endpoint is already straightened and the straightening branch can close. For the monitor route, this just means `baseCapSupportW A k 0 = 0`; then the supremum may be zero and `GlueWBaseCap` is immediate.

`K=0` or `K=last`: impossible because `openingAxis k = k+1` for `k : Fin (n-1)`, so it is interior.

Small `n`: if `n=2`, `k : Fin 1`; `K=1`, base triple `(A0,A1,A2)` is exactly the only joint. The base monitor duplicates the joint witness, which is harmless.

13. **Ordered brick list**

1. `baseCapSupportW` / `monitoredFamilyWB` / `monitoredSupWB` — worker, 50–80 lines.  
2. `continuous_baseCapSupportW` / `continuous_monitoredFamilyWB` — worker, 60–100 lines.  
3. `base_orientedDatum_eq` — needs-care, 70–120 lines; same sign discipline as FFCT37.  
4. `baseSupport_openNeg_eq_sin` — master/needs-care, 100–180 lines.  
5. `admissibleWB_baseCap` — needs-care, 100–150 lines.  
6. `GlueWBaseCap_of_monitoredSupWB` — worker/needs-care, 60–100 lines.  
7. `opening_boundary_trichotomyWB` — needs-care, 80–120 lines.  
8. Replace `glueW_clause_i` input by `GlueWBaseCap_of_monitoredSupWB` and update `mainPlus_headline_final` to use `monitoredSupWB` — needs-care wrapper, 80–160 lines.

14. **Final recommendation**

Implement (a). Add the base-cap support as a monitored member and derive `GlueWBaseCap` by admissibility. Do not open a new straightening-completion branch unless the base monitor breaks, because straightening completion needs fresh sub-arm IH plumbing not currently present in the W-glue spine.
