## 1. Current status: what is already enough

The assembly should now be organized around the **ray-indexed guard-free package**:

```lean
def RayWindValuesWithSign (P : StrictSimplePolygon n) (ρ : RayDirection P) (s : ℤ) : Prop :=
  (s = 1 ∨ s = -1) ∧
    ∀ x : Pt, ¬ OnBoundary P x → windCross P ρ x = 0 ∨ windCross P ρ x = s
```

and the data carrier:

```lean
structure RayOrientedWindData (P : StrictSimplePolygon n) (ρ : RayDirection P) : Type where
  s : ℤ
  hs : s = 1 ∨ s = -1
  values : RayWindValuesWithSign P ρ s
```

These are exactly the right master-induction payloads: no vertex guard, fixed ray direction, projected sign as data. `ZinanCh36SignSync` also already has `WindValuesWithSign.of_raywise`, the signed singleton jump, and the arithmetic sign core. fileciteturn91file0

---

## 2. Adapter A: triangle guardful → ray-indexed guard-free

Yes, the intended adapter is a **30–60 line perturb/local-constancy wrapper**, but do **not** try to specialize the three-polygon selector `exists_near_point_off_all_generic`. That selector needs a diagonal split and child polygons. For the triangle base, add a single-polygon variant.

The reusable pieces are already in `ZinanCh36Perturb`: the file proves the perturb direction algebra, `exists_badt_polygon`, and `exists_eps_segment_in_nhds`; the three-polygon selector is built from those. fileciteturn93file0

Add:

```lean
theorem exists_near_point_off_generic
    {m : ℕ} (Q : StrictSimplePolygon m) (ρ : RayDirection Q)
    {x : Pt} (hQoff : ¬ OnBoundary Q x) {U : Set Pt} (hU : U ∈ nhds x) :
    ∃ y ∈ U,
      ¬ OnBoundary Q y ∧
      ∀ k : Fin m, side ρ.r y (Q.q k) ≠ 0
```

Proof: copy the one-polygon part of `exists_near_point_off_all_generic`: choose `λ` so `w = sweepDir ρ.r λ` is transverse to every edge of `Q`, get the bad `t` set from `exists_badt_polygon`, choose `t ∈ (0, ε)` outside that finite set and inside the preimage of `U`.

Then the adapter:

```lean
theorem triangle_rayWindValuesWithSign
    (Q : StrictSimplePolygon 3) (ρ : RayDirection Q) :
    RayWindValuesWithSign Q ρ (triSign Q) := by
  refine ⟨triSign_unit Q, ?_⟩
  intro x hoff
  have hev := windCross_locally_constant_off_boundary Q ρ hoff
  obtain ⟨U, hUnhds, hUeq⟩ := eventually_iff_exists_mem.mp hev
  obtain ⟨y, hyU, hyoff, hyvert⟩ :=
    exists_near_point_off_generic Q ρ hoff hUnhds
  have hyval :=
    (triangle_windValuesWithSign Q).values ρ y hyoff hyvert
  have hxy : windCross Q ρ y = windCross Q ρ x := hUeq y hyU
  simpa [hxy] using hyval
```

The base theorem landed in `ZinanCh36TriBase` as guard-ful `WindValuesWithSign Q (triSign Q)`, and `triSign` is the orientation sign of the triangle. fileciteturn92file0

Estimate: single-polygon selector **60–100 lines** if copied cleanly; adapter **20–35 lines**.

---

## 3. Adapter B: non-circular split supply

Do **not** use an `EarCutData` supplier as the premise of the value induction. The consumer-facing `PolygonEarExistence.isConvexVertex'_holds` still takes:

```lean
Esup : ∀ {m : ℕ} (P : StrictSimplePolygon m) (σ : RayDirection P),
  4 ≤ m → EarCutData P σ (ear P)
```

and the file’s own documentation identifies `EarCutData`’s genuine field as `earDeletedExterior`, the very field the value route is trying to produce. fileciteturn81file0

Use a separate non-circular structure:

```lean
structure EarValueSplitData
    {n : ℕ} (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (i : Fin n) : Prop where
  hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i)
  lax : LeftStrictAxioms P (cyclicPrev i) (cyclicNext i)
  rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i)
  σL : RayDirection (buildLeftPoly hdiag lax)
  σR : RayDirection (buildRightPoly hdiag rax)
  hLr : σL.r = ρ.r
  hRr : σR.r = ρ.r
```

The non-circular induction premise is:

```lean
Esplit : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
  4 ≤ m → EarValueSplitData P ρ (ear P)
```

If a full `EarCutData` is already available elsewhere, you may write:

```lean
def EarValueSplitData.of_EarCutData ... : EarValueSplitData P ρ i := ...
```

but only as a projection adapter, not as a premise for proving `earDeletedExterior`.

On the question “which landed theorem produces the ear diagonal for arbitrary strict simple `P`?”: the current consumer path does **not** expose an unconditional producer independent of the ear residue. The ear-delete file says the construction of the `(n-1)` ear-deleted polygon is via `buildRightPoly` for an ear-base diagonal, and `buildRightPoly` needs `IsDiagonal'` plus `RightStrictAxioms`; it does not manufacture the diagonal itself. fileciteturn83file0

---

## 4. RayDirection supply

`RayDirection` is polygon-indexed and contains a vector plus the no-edge-parallel proof:

```lean
structure RayDirection {n : ℕ} (P : StrictSimplePolygon n) where
  r : Pt
  r_ne_zero : r ≠ 0
  no_edge_parallel :
    ∀ i : Fin n, det2 r (P.q (cyclicNext i) - P.q i) ≠ 0
```

So `.r` is not globally free: the same vector may fail `no_edge_parallel` for a child polygon. You cannot fix one global `r0` for all polygons without proving it is nonparallel to every edge of every subpolygon. fileciteturn80file0

The split data must therefore carry:

```lean
σL : RayDirection (buildLeftPoly hdiag lax)
σR : RayDirection (buildRightPoly hdiag rax)
hLr : σL.r = ρ.r
hRr : σR.r = ρ.r
```

Exactly as `EarValueSplitData` above. The common-ray proofs are what allow `windCross_split_common`.

---

## 5. BuildRightPoly strictness and size

For the ear base `(prev i, next i)`, `PolygonEarDelete` proves:

```lean
leftLength (cyclicPrev i) (cyclicNext i) = 3
rightLength (cyclicPrev i) (cyclicNext i) = n - 1
```

and the file documentation states that the ear-deleted `(n-1)`-gon is `buildRightPoly` for the ear base, with tuple `subpolygonRightTuple`, preserving strict simplicity under `RightStrictAxioms`. fileciteturn83file0

So the strong induction descent is by vertex count:

```lean
m ↦ m - 1
```

and the IH applies to:

```lean
buildRightPoly D.hdiag D.rax :
  StrictSimplePolygon (rightLength (cyclicPrev i) (cyclicNext i))
```

then rewrite `rightLength_earBase hm i` to identify the size as `m - 1`.

---

## 6. Brick 12: exact induction statement

Use strong induction on `m`:

```lean
theorem rayOrientedWindData_all_of_earValueSplits
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esplit : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      4 ≤ m → EarValueSplitData P ρ (ear P))
    (Htube : ∀ {m : ℕ} {P : StrictSimplePolygon m} {ρ : RayDirection P}
      {i j : Fin m}
      (h : IsDiagonal' P ρ i j)
      (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
      (σL : RayDirection (buildLeftPoly h lax))
      (σR : RayDirection (buildRightPoly h rax)),
      DiagTubeStraddle h lax rax σL σR) :
    ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RayOrientedWindData P ρ
```

Proof shape:

```lean
intro m
induction' m using Nat.strong_induction_on with m IH
intro P ρ
have hm3le : 3 ≤ m := P.hthree

by_cases h4 : 4 ≤ m
· -- split step
  let i := ear P
  let D := Esplit P ρ h4
  let L := buildLeftPoly D.hdiag D.lax
  let R := buildRightPoly D.hdiag D.rax

  have DL : RayOrientedWindData L D.σL := triangle_rayWindValuesWithSign L D.σL
  -- because leftLength_earBase makes L a 3-gon; if Lean does not see it definitional,
  -- transport across the equality.

  have hRlen : rightLength (cyclicPrev i) (cyclicNext i) = m - 1 :=
    PolygonEarDelete.rightLength_earBase h4 i

  have DR : RayOrientedWindData R D.σR := by
    -- apply IH (m - 1)
    have hlt : m - 1 < m := by omega
    exact IH (m - 1) hlt R D.σR
    -- use hRlen casts if needed

  have hsync : DL.s = DR.s :=
    split_child_signs_eq D.hdiag D.lax D.rax D.σL D.σR D.hLr D.hRr
      (Htube D.hdiag D.lax D.rax D.σL D.σR)
      DL.values DR.values

  exact rayOrientedWindData_of_split D DL DR hsync

· -- base must be m = 3
  have hm : m = 3 := le_antisymm (by omega) hm3le
  subst hm
  exact triangle_rayWindValuesWithSign P ρ
```

The step theorem should be:

```lean
theorem rayOrientedWindData_of_split
    {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i : Fin n} (hn : 4 ≤ n)
    (D : EarValueSplitData P ρ i)
    (DL : RayOrientedWindData (buildLeftPoly D.hdiag D.lax) D.σL)
    (DR : RayOrientedWindData (buildRightPoly D.hdiag D.rax) D.σR)
    (hsync : DL.s = DR.s) :
    RayOrientedWindData P ρ
```

Inside, rewrite `DR.values` along `hsync`, then call `rayWindValues_split`.

Estimate: induction theorem **120–180 lines**; split step wrapper **40–70 lines**. Mostly master because of size casts.

---

## 7. Adapter for left child being a triangle

The left child type is:

```lean
buildLeftPoly D.hdiag D.lax :
  StrictSimplePolygon (leftLength (cyclicPrev i) (cyclicNext i))
```

but `triangle_rayWindValuesWithSign` wants `StrictSimplePolygon 3`. Use the landed equality:

```lean
leftLength_earBase (hn : 4 ≤ n) i :
  leftLength (cyclicPrev i) (cyclicNext i) = 3
```

Add:

```lean
theorem leftEar_rayOrientedWindData
    {P : StrictSimplePolygon n} {ρ : RayDirection P} {i : Fin n}
    (hn : 4 ≤ n) (D : EarValueSplitData P ρ i) :
    RayOrientedWindData (buildLeftPoly D.hdiag D.lax) D.σL
```

Proof: rewrite the length equality, then use `triangle_rayWindValuesWithSign`.

Estimate: **30–60 lines**.

---

## 8. Brick 13: value-to-exterior wiring

First produce interior values for an ear point.

```lean
theorem earInterior_values_of_data
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esplit : ...)
    (Htube : ...)
    {n : ℕ} (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (hn : 4 ≤ n)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2)
    (hsum : w0 + w1 + w2 = 1)
    (hx : x =
      w0 • P.q (cyclicPrev (ear P)) +
      w1 • P.q (ear P) +
      w2 • P.q (cyclicNext (ear P)))
    (hPoff : ¬ OnBoundary P x)
    (hLoff : ¬ OnBoundary (buildLeftPoly D.hdiag D.lax) x)
    (hRoff : ¬ OnBoundary (buildRightPoly D.hdiag D.rax) x) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      windCross P ρ x = s ∧
      windCross (buildLeftPoly D.hdiag D.lax) D.σL x = s ∧
      windCross (buildRightPoly D.hdiag D.rax) D.σR x = 0
```

But the committed `earInterior_values_of_rightValues` consumes guardful packages. Prefer to write a **ray-indexed** variant to avoid going back through vertex guards:

```lean
theorem earInterior_values_ray
    {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i : Fin n} (hn : 4 ≤ n) (D : EarValueSplitData P ρ i)
    (DL : RayOrientedWindData (buildLeftPoly D.hdiag D.lax) D.σL)
    (DR : RayOrientedWindData (buildRightPoly D.hdiag D.rax) D.σR)
    (hsync : DL.s = DR.s)
    {x : Pt}
    (hTriOdd : Odd (CrossingNumber' (buildLeftPoly D.hdiag D.lax) D.σL x))
    (hLoff : ¬ OnBoundary (buildLeftPoly D.hdiag D.lax) x)
    (hRoff : ¬ OnBoundary (buildRightPoly D.hdiag D.rax) x)
    (hPoff : ¬ OnBoundary P x) :
    windCross P ρ x = DL.s ∧
    windCross (buildLeftPoly D.hdiag D.lax) D.σL x = DL.s ∧
    windCross (buildRightPoly D.hdiag D.rax) D.σR x = 0
```

`hTriOdd` can be supplied by `leftCN_earBase_eq_one` for generic points, or by the triangle value package plus nonzero/odd bridge depending on what is easiest. `PolygonEarDelete` already has `leftCN_earBase_eq_one` for strict interior ear points with side guards. fileciteturn83file0

Estimate: **80–140 lines**.

Then exterior:

```lean
theorem earDeletedExterior_of_values
    ... :
    ¬ ClosedRegion' (buildRightPoly D.hdiag D.rax) D.σR x :=
  earDeletedExterior_winding_route_sign D.hdiag D.lax D.rax D.σL D.σR
    D.hLr D.hRr hRoff hLin hPin
```

`earDeletedExterior_winding_route_sign` is already committed in `ZinanCh36InteriorValue`, generalizing the harvest’s `1` to arbitrary `s`. fileciteturn89file0

Estimate: **20–40 lines**.

---

## 9. Producing `EarCutData`

Make a builder that takes non-circular split data and the new exterior theorem.

```lean
def EarCutData_of_interiorValues
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esplit : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      4 ≤ m → EarValueSplitData P ρ (ear P))
    (Htube : ...)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P)
    (hm : 4 ≤ m) :
    EarCutData P ρ (ear P) :=
{ hdiag := (Esplit P ρ hm).hdiag
  lax := (Esplit P ρ hm).lax
  rax := (Esplit P ρ hm).rax
  σL := (Esplit P ρ hm).σL
  σR := (Esplit P ρ hm).σR
  hLr := (Esplit P ρ hm).hLr
  hRr := (Esplit P ρ hm).hRr
  earDeletedExterior := by
    -- call earDeletedExterior_of_values
}
```

I cannot quote the exact field names of `EarCutData` from the truncated connector output, so use `#check EarCutData` locally before writing the constructor. The design assumption from `PolygonEarDelete` is clear: the fields include the diagonal split data and the single exterior field; its file explicitly says `earDeletedExterior` is the genuine field the residue carries. fileciteturn83file0

Estimate: **80–140 lines**, mostly field-name alignment.

---

## 10. PolygonGeomResidue and headline wiring

Once you have:

```lean
Esup_from_values :
  ∀ {m : ℕ} (P : StrictSimplePolygon m) (σ : RayDirection P),
    4 ≤ m → EarCutData P σ (ear P)
```

plug it into the landed bridge:

```lean
PolygonEarExistence.isConvexVertex'_holds
  ear
  Esup_from_values
  rest
```

That returns `PolygonGeomResidue`. Then use the existing art-gallery bridge in `PolygonEarExistence`, which was specifically set up to consume `EarCutData` plus remaining cut data plus `M`. fileciteturn81file0

Wrapper chain:

```lean
def polygonGeomResidue_of_interiorValues
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esplit : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      4 ≤ m → EarValueSplitData P ρ (ear P))
    (Htube : ...)
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RemainingResidualData P ρ (ear P)) :
    PolygonGeomResidue :=
  PolygonEarExistence.isConvexVertex'_holds ear
    (fun P σ hm => EarCutData_of_interiorValues ear Esplit Htube P σ hm)
    rest
```

Final theorem:

```lean
theorem artGallery_strict_mod_M
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esplit : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      4 ≤ m → EarValueSplitData P ρ (ear P))
    (Htube : ...)
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RemainingResidualData P ρ (ear P))
    (M : DiagonalAttachInput (...))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  PolygonGeomInput.artGallery_strict_of_residue
    (polygonGeomResidue_of_interiorValues ear Esplit Htube rest) M P ρ
```

Estimate: **60–100 lines** if imports are aligned.

---

## 11. Ordered remaining bricks

1. **Adapter A selector**
   ```lean
   exists_near_point_off_generic
   triangle_rayWindValuesWithSign
   ```
   Worker, **80–130 lines**.

2. **Non-circular split-data structure**
   ```lean
   structure EarValueSplitData ...
   ```
   Worker, **20–35 lines**.

3. **Left triangle adapter**
   ```lean
   leftEar_rayOrientedWindData
   ```
   Worker, **30–60 lines**.

4. **Split assembly theorem**
   ```lean
   rayOrientedWindData_of_split
   ```
   Worker/master, **50–90 lines**.

5. **Strong induction**
   ```lean
   rayOrientedWindData_all_of_earValueSplits
   ```
   Master, **120–180 lines**.

6. **Ray-indexed ear interior values**
   ```lean
   earInterior_values_ray
   ```
   Worker/master, **80–140 lines**.

7. **Ear exterior from values**
   ```lean
   earDeletedExterior_of_values
   ```
   Worker, **20–40 lines**.

8. **EarCutData builder**
   ```lean
   EarCutData_of_interiorValues
   ```
   Worker/master, **80–140 lines**.

9. **Residue/headline wrappers**
   ```lean
   polygonGeomResidue_of_interiorValues
   artGallery_strict_mod_M
   ```
   Worker, **60–100 lines**.

---

## 12. Audit

The induction does **not** assume ear deletion preserves strictness without evidence: the child is literally `buildRightPoly hdiag rax`, whose type is a `StrictSimplePolygon` at the right arc length; `rightLength_earBase` supplies the `(m - 1)` arithmetic in the ear-base case. fileciteturn83file0

It does **not** use half-plane or reflex-sensitive arguments. All reflex-sensitive geometry is quarantined in `DiagTubeStraddle`, which is the explicit transversal single-edge flip primitive documented in `ZinanCh36DiagTube`. fileciteturn90file0

It does **not** require a global ray direction. Every split carries child `RayDirection`s and common-ray equalities; this is necessary because `RayDirection` is polygon-indexed by a no-edge-parallel field. fileciteturn80file0

It does **not** hard-code orientation sign `1`. The base uses `triSign`; sibling synchronization identifies child signs; final `earDeletedExterior` only needs the right winding to be `0`, so the conclusion is orientation-invariant.
