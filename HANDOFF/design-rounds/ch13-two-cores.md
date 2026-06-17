## 1. Executive choice

Use the **global convex-position route** for Core 1, specifically the already-landed `PlanarConvexDiag` / `cyclicTriplePos_unconditional` machinery. Do **not** use vertex-deletion induction.

For Core 2, do **not** depend on Core 1 as stated. The proposed Core1→Core2 chain has a hypothesis mismatch: Core 1 is about the **strict comparison arm `B`**, while TailRayMembership is about the **weak folded arm `A`**. Determinant signs do not transfer from `B` to `A` through `JointLe`. Instead, extract the needed ray coefficient sign directly on `A` using the witness vertex `A 2`, weak supports, and `PositiveJoints`.

So the two cores close as:

```text
Core 1: StrictDiagonalSupport
  ← cyclicTriplePos_unconditional / PlanarConvexDiag global theorem.

Core 2: TailRayMembership
  ← tail line collinearity
  + fold coefficients a,b > 0
  + positive witness determinant at A2
  + weak supports of edges (n−1,n) and (n,0).
```

This avoids the sign-indeterminate local GP route that FFCT63 explicitly ruled out. FFCT63 records that the strict-interior diagonal support needs a global convex-position argument, not a local `nlinarith` proof. fileciteturn104file0

---

## 2. Core 1 audit: why deletion induction is circular

The deletion idea would need:

```lean
deleteVertex_strict :
  StrictConvexSphPolygon B →
  StrictConvexSphPolygon (deleteVertex B k)
```

The old edges are inherited, and the open hemisphere is inherited. The problem is the **new edge** created by deletion:

```text
B (k−1) —— B (k+1)
```

To prove its strict supports against all remaining vertices, you need:

```lean
0 < sOrient (B (k−1)) (B (k+1)) (B m)
```

for vertices `m` on the relevant arc. That is exactly a `StrictDiagonalSupport` statement for the distance-2 diagonal `(k−1,k+1)` in the original polygon. The endpoint-adjacent cases are easy, but supports against vertices farther away are the same global theorem.

So the deletion proof becomes a mutual diagonal-support theorem over all arcs, not a true reduction. It can be made correct, but it is a more complicated way to reprove the global convex-position theorem already present in `PlanarConvexDiag`.

---

## 3. Core 1 winning theorem already in the repo

`PlanarConvexDiag.lean` proves the planar convex-position primitive using a shared-apex Grassmann–Plücker identity:

```lean
theorem det3_apex_plucker (A E P M Q : E3) :
  det3 A P Q * det3 A E M =
    det3 A M Q * det3 A E P +
    det3 A P M * det3 A E Q
```

Then it proves the global natural-number induction:

```lean
theorem det3_diag_pos_nat ...
```

and exports the spherical result:

```lean
theorem cyclicTriplePos_unconditional {n : ℕ} [NeZero n] {P : Fin n → S2}
    (h : StrictConvexSphPolygon P) : CyclicTriplePos P
```

This is exactly the missing global convex-position argument. fileciteturn107file0

---

## 4. Core 1 exact adapter: normalized wrap diagonal

FFCT63’s normalized statement is the wrap diagonal:

```text
(B n, B 1)
```

and an arc-interior vertex:

```text
B (1 + v),   1 ≤ v ≤ n−2.
```

Use `cyclicTriplePos_unconditional` on the increasing triple:

```text
1 < 1+v < n.
```

It gives:

```lean
0 < sOrient (B ⟨1⟩) (B ⟨1+v⟩) (B ⟨n⟩)
```

Cyclic rotation gives:

```lean
0 < sOrient (B ⟨n⟩) (B ⟨1⟩) (B ⟨1+v⟩)
```

Add:

```lean
theorem strictDiagonal_arcInterior_of_cyclicTriple
    {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B)
    {v : ℕ} (hv1 : 1 ≤ v) (hvn : v ≤ n - 2) :
    0 < sOrient
      (B ⟨n, by omega⟩)
      (B ⟨1, by omega⟩)
      (B ⟨1 + v, by omega⟩) := by
  have hcyc :=
    ProofsInTheBook.PlanarConvexDiag.cyclicTriplePos_unconditional
      hB.closed_convex
  have hpos :
      0 < sOrient
        (B ⟨1, by omega⟩)
        (B ⟨1 + v, by omega⟩)
        (B ⟨n, by omega⟩) := by
    exact hcyc
      ⟨1, by omega⟩
      ⟨1 + v, by omega⟩
      ⟨n, by omega⟩
      (by omega)
      (by omega)
  -- rotate `(1,1+v,n)` to `(n,1,1+v)`
  -- use existing `sOrient_cyc_rot` or unfold `sOrient` and use `det3_cyclic`.
  ...
```

If `CyclicTriplePos`’s argument order is slightly different, swap the one line that instantiates it; the cyclic-rotation target is the same.

---

## 5. Core 1 residual discharge statements

FFCT63 already defines the interior residue as:

```lean
def StrictDiagonalInteriorSupport {n : ℕ}
    (B : Fin (n + 1) → S2) (hn3 : 3 ≤ n) : Prop :=
  ∀ v : ℕ, (hv : v < n) → 2 ≤ v → v ≤ n - 3 →
    0 < sOrient
      (B ⟨n, by omega⟩)
      (B ⟨1, by omega⟩)
      (B ⟨1 + v, by have := hv; omega⟩)
```

fileciteturn105file0

Discharge it:

```lean
theorem StrictDiagonalInteriorSupport_holds
    {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hn3 : 3 ≤ n) :
    StrictDiagonalInteriorSupport B hn3 := by
  intro v hv hv2 hvn
  exact strictDiagonal_arcInterior_of_cyclicTriple
    (B := B) hB
    (by omega)
    (by omega)
```

Then either call FFCT63’s assembly theorem from interior support, or prove the full wrap statement directly:

```lean
theorem StrictDiagonalSupport_wrap_holds
    {n : ℕ} {B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hn3 : 3 ≤ n) :
    ∀ v : ℕ, 1 ≤ v → v ≤ n - 2 →
      0 < sOrient
        (B ⟨n, by omega⟩)
        (B ⟨1, by omega⟩)
        (B ⟨1 + v, by omega⟩) :=
  fun v hv1 hvn =>
    strictDiagonal_arcInterior_of_cyclicTriple hB hv1 hvn
```

This bypasses the FFCT63 base/top split entirely, though the base/top lemmas remain valid.

---

## 6. Core 1 general per-arc form

If a later consumer asks for an arbitrary normalized diagonal `(B i, B j)` with vertices strictly between them, use:

```lean
theorem strictDiagonalSupport_between_of_cyclicTriple
    {N : ℕ} [NeZero N] {B : Fin N → S2}
    (hB : StrictConvexSphPolygon B)
    {i m j : Fin N}
    (him : i.val < m.val) (hmj : m.val < j.val) :
    0 < sOrient (B j) (B i) (B m) := by
  have hcyc :=
    ProofsInTheBook.PlanarConvexDiag.cyclicTriplePos_unconditional hB
  have hpos : 0 < sOrient (B i) (B m) (B j) :=
    hcyc i m j him hmj
  -- rotate `(i,m,j)` to `(j,i,m)`
  ...
```

This is the clean per-arc theorem. The second arc has the opposite sign, as expected; do not state “all vertices lie on one side of a diagonal” for a closed polygon.

---

## 7. Core 1 estimates

| Brick | Statement | Difficulty | Estimate |
|---|---|---:|---:|
| C1.1 | `sOrient` cyclic rotation alias | worker | 10–20 lines |
| C1.2 | `strictDiagonal_arcInterior_of_cyclicTriple` | worker | 40–80 lines |
| C1.3 | `StrictDiagonalInteriorSupport_holds` | worker | 20–40 lines |
| C1.4 | `StrictDiagonalSupport_wrap_holds` / consumer adapter | worker | 30–70 lines |

No master geometry remains for Core 1 if `PlanarConvexDiag` is accepted.

---

## 8. Core 2: correct target

FFCT63 says the metric tail equality:

```lean
sDist (A 0) (A ⟨n−1⟩)
  = endpt A + sDist (A (Fin.last n)) (A ⟨n−1⟩)
```

is equivalent to the ray membership:

```lean
(A (Fin.last n) : E3) ∈
  Submodule.span NNReal
    ({(A 0 : E3), (A ⟨n - 1⟩ : E3)} : Set E3)
```

and that the metric-from-ray reduction is already discharged. So prove the ray membership and then call `tailFoldBoundary_of_rayMembership`. fileciteturn104file0

---

## 9. Core 2: the proposed Core1→Core2 chain is not type-correct

The suggested chain uses Core 1 to sign:

```lean
sOrient (A ⟨n-1⟩) (A ⟨1⟩) (A m)
```

But Core 1 applies to a **strictly convex closed spherical polygon**. In the tail-fold branch, `A` is only `WeakConvexSphArm` plus `PositiveJoints`; it has a far fold, so it is not strict. The strict comparison arm `B` does not give determinant signs for `A`.

So do not use `StrictDiagonalSupport` for Core 2 unless you have separately proved a weak+positive-joint diagonal support theorem for `A`. You do not need it.

---

## 10. Core 2: use the witness `A 2`

Assume the `(0,n−1)` far fold:

```lean
A0 = a • A1 + b • A(n−1),    0 < a, 0 < b
```

and the tail line result:

```lean
det3 A1 A(n−1) An = 0.
```

Let:

```lean
u := A 1
v := A (n - 1)
p := A 0
q := A n
m := A 2
```

Extract real line coefficients:

```lean
q = α • u + β • v.
```

Define:

```lean
D := sOrient v u m.
```

The critical fact is:

```lean
0 < D.
```

Proof:

```lean
sOrient p u m
  = sOrient (a u + b v) u m
  = b * sOrient v u m
  = b * D.
```

Weak support of edge `(0,1)` at `2` gives `0 ≤ sOrient p u m`. PositiveJoints gives the joint at `1` is not `0`; `jointAngle_lt_pi` gives it is not `π`; together with the collinearity bridges, this gives:

```lean
sOrient p u m ≠ 0.
```

Hence `0 < sOrient p u m`, and since `0 < b`, `0 < D`.

Now use two weak supports involving `q = An`:

1. Edge `(n−1,n)` at `2`:
   ```lean
   0 ≤ sOrient v q m
     = α * D
   ```
   so `0 ≤ α`.

2. Wrap edge `(n,0)` at `2`:
   ```lean
   0 ≤ sOrient q p m
     = (β * a - α * b) * D
   ```
   so:
   ```lean
   0 ≤ β * a - α * b.
   ```

Then:

```lean
q = (α / a) • p + ((β*a - α*b) / a) • v
```

with both coefficients nonnegative. That is exactly:

```lean
q ∈ span≥0 {p, v}.
```

---

## 11. Core 2 exact Lean bricks

### 11.1 Witness determinant positivity

```lean
theorem tail_witness_det_pos
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn4 : 4 ≤ n)
    (hA : WeakConvexSphArm A)
    (hpos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hangle : JointLe A B)
    {a b : NNReal}
    (ha : 0 < (a : ℝ)) (hb : 0 < (b : ℝ))
    (hfold :
      (a : ℝ) • (A ⟨1, by omega⟩ : E3) +
      (b : ℝ) • (A ⟨n - 1, by omega⟩ : E3) =
        (A ⟨0, by omega⟩ : E3)) :
    0 < sOrient
      (A ⟨n - 1, by omega⟩)
      (A ⟨1, by omega⟩)
      (A ⟨2, by omega⟩)
```

Proof sketch: expand `sOrient (A0)(A1)(A2)` using `hfold`. Weak support gives nonnegative; `PositiveJoints` and `jointAngle_lt_pi` give nonzero. Divide by `b > 0`.

Estimate: **100–160 lines**, master/worker.

---

### 11.2 Real line coefficients for `An`

Use FFCT25’s span extraction theorem. That file proves `lin_indep_span_of_det3_zero`: if two unit vectors are neither equal nor antipodal and `det3 v w z = 0`, then `z` is in their real span. fileciteturn102file0

```lean
theorem tail_line_coeffs_of_collinear
    {n : ℕ} {A : Fin (n + 1) → S2}
    (hn4 : 4 ≤ n)
    (hA : WeakConvexSphArm A)
    (hline :
      det3 (A ⟨1, by omega⟩ : E3)
           (A ⟨n - 1, by omega⟩ : E3)
           (A ⟨n, by omega⟩ : E3) = 0)
    (hne :
      (A ⟨1, by omega⟩ : E3) ≠
        (A ⟨n - 1, by omega⟩ : E3))
    (hanti :
      (A ⟨1, by omega⟩ : E3) ≠
        - (A ⟨n - 1, by omega⟩ : E3)) :
    ∃ α β : ℝ,
      (A ⟨n, by omega⟩ : E3) =
        α • (A ⟨1, by omega⟩ : E3) +
        β • (A ⟨n - 1, by omega⟩ : E3)
```

Estimate: **30–60 lines**, worker.

Use existing no-repeat / no-antipodal lemmas to supply `hne` and `hanti`.

---

### 11.3 Coefficient signs

```lean
theorem tail_coeff_signs
    {n : ℕ} {A : Fin (n + 1) → S2}
    (hn4 : 4 ≤ n)
    (hA : WeakConvexSphArm A)
    {a b : NNReal} {α β : ℝ}
    (ha : 0 < (a : ℝ)) (hb : 0 < (b : ℝ))
    (hfold :
      (a : ℝ) • (A ⟨1, by omega⟩ : E3) +
      (b : ℝ) • (A ⟨n - 1, by omega⟩ : E3) =
        (A ⟨0, by omega⟩ : E3))
    (hq :
      (A ⟨n, by omega⟩ : E3) =
        α • (A ⟨1, by omega⟩ : E3) +
        β • (A ⟨n - 1, by omega⟩ : E3))
    (hD :
      0 < sOrient
        (A ⟨n - 1, by omega⟩)
        (A ⟨1, by omega⟩)
        (A ⟨2, by omega⟩)) :
    0 ≤ α ∧ 0 ≤ β * (a : ℝ) - α * (b : ℝ)
```

Proof sketch: weak support of edge `(n−1,n)` at `2` gives `0 ≤ α * D`; weak support of wrap edge `(n,0)` at `2` gives `0 ≤ (β*a − α*b) * D`.

Estimate: **80–140 lines**, worker.

---

### 11.4 Cone conversion

```lean
theorem tail_rayMembership_of_coeff_signs
    {u v p q : E3} {a b α β : ℝ}
    (ha : 0 < a)
    (hfold : p = a • u + b • v)
    (hq : q = α • u + β • v)
    (hα : 0 ≤ α)
    (hμ : 0 ≤ β * a - α * b) :
    q ∈ Submodule.span NNReal ({p, v} : Set E3)
```

Proof sketch:

```lean
q = (α / a) • p + ((β*a - α*b) / a) • v
```

and both coefficients are nonnegative. Use `Submodule.mem_span_pair` as in FFCT19/FFCT18 style.

Estimate: **60–100 lines**, worker.

---

### 11.5 TailRayMembership final

```lean
theorem TailRayMembership_holds
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn4 : 4 ≤ n)
    (hA : WeakConvexSphArm A)
    (hpos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hangle : JointLe A B)
    {a b : NNReal}
    (ha : 0 < (a : ℝ)) (hb : 0 < (b : ℝ))
    (hfold :
      (a : ℝ) • (A ⟨1, by omega⟩ : E3) +
      (b : ℝ) • (A ⟨n - 1, by omega⟩ : E3) =
        (A ⟨0, by omega⟩ : E3))
    (hline :
      det3 (A ⟨1, by omega⟩ : E3)
           (A ⟨n - 1, by omega⟩ : E3)
           (A ⟨n, by omega⟩ : E3) = 0) :
    (A ⟨n, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨0, by omega⟩ : E3),
          (A ⟨n - 1, by omega⟩ : E3)} : Set E3)
```

Proof: get `D > 0`, get `α β`, prove coefficient signs, convert to NNReal cone.

Estimate: **80–140 lines**, master assembly.

---

## 12. Core 2 small cases

For `n = 3`, there is no out-of-plane witness `A 2` distinct from `A(n−1)`. This tail case should be impossible or already adjacent.

Add:

```lean
theorem tail_case_n3_impossible
    {A : Fin (3 + 1) → S2}
    (hA : WeakConvexSphArm A)
    (hpos : PositiveJoints A)
    (hcol :
      (A ⟨0, by omega⟩ : E3) ∈
        Submodule.span NNReal
          ({(A ⟨1, by omega⟩ : E3),
            (A ⟨2, by omega⟩ : E3)} : Set E3)) :
    False
```

Proof: apply the landed last-corner/betweenness-to-zero-joint lemma from FFCT19: folded-flat betweenness at an adjacent triple forces the apex joint to `0`, contradicting `PositiveJoints`.

Estimate: **30–60 lines**, worker.

For `n = 4`, the witness `A 2` is valid and distinct from `A(n−1)=A3`, so the general `hn4` proof works.

---

## 13. Metric tail boundary wiring

Once `TailRayMembership_holds` is proved, do not reprove spherical distance additivity. FFCT63 says the ray-membership-to-metric reduction has already been discharged as the honest supplier:

```lean
tailFoldBoundary_of_rayMembership
```

So wire:

```lean
theorem TailFoldBoundary_holds
    ... :
    TailFoldBoundary A (by omega) := by
  have hray := TailRayMembership_holds ...
  exact tailFoldBoundary_of_rayMembership ... hray
```

Estimate: **20–40 lines**, worker.

---

## 14. Ordered implementation plan

### Core 1

1. **Import global convex-position theorem**
   ```lean
   import ProofsInTheBook.PlanarConvexDiag
   ```
   Worker, **5 lines**.

2. **Orientation cyclic alias**
   ```lean
   theorem sOrient_cyclic ...
   ```
   Worker, **10–20 lines**.

3. **Wrap diagonal support**
   ```lean
   strictDiagonal_arcInterior_of_cyclicTriple
   ```
   Worker, **40–80 lines**.

4. **FFCT63 residue discharge**
   ```lean
   StrictDiagonalInteriorSupport_holds
   StrictDiagonalSupport_wrap_holds
   ```
   Worker, **50–100 lines**.

5. **Consumer replacement**
   Replace the `StrictDiagonalSupport` hypothesis by `StrictDiagonalSupport_wrap_holds`.
   Worker, **20–60 lines**.

### Core 2

6. **Small-case kill**
   ```lean
   tail_case_n3_impossible
   ```
   Worker, **30–60 lines**.

7. **Witness determinant positivity**
   ```lean
   tail_witness_det_pos
   ```
   Master/worker, **100–160 lines**.

8. **Line coefficient extraction**
   ```lean
   tail_line_coeffs_of_collinear
   ```
   Worker, **30–60 lines**.

9. **Coefficient signs**
   ```lean
   tail_coeff_signs
   ```
   Worker, **80–140 lines**.

10. **Cone conversion**
    ```lean
    tail_rayMembership_of_coeff_signs
    ```
    Worker, **60–100 lines**.

11. **TailRayMembership**
    ```lean
    TailRayMembership_holds
    ```
    Master assembly, **80–140 lines**.

12. **Metric boundary**
    ```lean
    TailFoldBoundary_holds
    ```
    Worker, **20–40 lines**.

13. **Final FFCT assembly replacement**
    Supply both:
    ```lean
    StrictDiagonalSupport_wrap_holds
    TailFoldBoundary_holds
    ```
    to the FFCT54/63/64 assembly.
    Worker/master, **40–100 lines**.

---

## 15. Degenerate / refutation audit

The Core 1 proof does not assert the false “all vertices are on one side of a diagonal.” It is per-arc: one arc has one sign, the other arc has the opposite sign. That is why the cyclic-triple theorem is used with a normalized increasing triple.

The deletion route is not used, so no hidden “vertex deletion preserves strict convexity” theorem is smuggled in.

Core 2 uses only `A`-side weak supports plus `PositiveJoints`; it does not transfer determinant signs from `B` to `A`. This avoids the invalid Core1→Core2 dependency through the comparison arm.

The `n = 3` tail-ray case is separated and killed by the adjacent folded-flat joint-zero lemma. For `n ≥ 4`, the witness `A 2` exists and is the needed out-of-plane point.

The wrap edge `(A n, A 0)` is valid because `WeakConvexSphArm` is defined via the closed polygon on `Fin (n+1)`, so edge support includes the cyclic last edge.
