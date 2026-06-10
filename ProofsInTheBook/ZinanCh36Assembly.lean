import ProofsInTheBook.ZinanCh36Straddle
import ProofsInTheBook.ZinanCh36InteriorValue
import ProofsInTheBook.ZinanCh36TriBase
import ProofsInTheBook.PolygonEarDelete
import ProofsInTheBook.PolygonEarCornerEscape
import ProofsInTheBook.PolygonEarExistence

/-!
# `ZinanCh36Assembly` — the final assembly of the Ch36 interior-value campaign

This file implements the 9 ordered bricks of the archived assembly design
(`HANDOFF/design-rounds/ch36-assembly-final.md`).  The design's `Htube` input is **no longer
needed**: `ZinanCh36Straddle.split_child_signs_eq_final` discharges the sibling sign sync
UNCONDITIONALLY, so the master induction needs no diagonal-tube hypothesis.

## Brick inventory

1. `exists_near_point_off_generic` (single-polygon selector) + `triangle_rayWindValuesWithSign`
   (Adapter A: triangle guard-ful → ray-indexed guard-free).
2. `EarValueSplitData` — the non-circular split-data structure (Type-valued: carries `σL/σR`).
3. `leftEar_rayOrientedWindData` — the left child IS a 3-gon (`leftLength_earBase`), transported.
4. `rayOrientedWindData_of_split` — the split assembly step (sync via `split_child_signs_eq_final`).
5. `rayOrientedWindData_all_of_earValueSplits` — the strong induction (no `Htube`).
6. `earInterior_values_ray` — the ray-indexed ear-interior value distribution.
7. `earDeletedExterior_of_values` — the committed signed exterior route.
8. `EarCutData_of_interiorValues` — the `EarCutData` builder.
9. `polygonGeomResidue_of_interiorValues` + `artGallery_strict_mod_M` — residue/headline wiring.

## Remaining genuine inputs (honesty contract)

* `Esplit` — the ear-diagonal supply (`EarValueSplitData`): a GENUINE architectural input, exactly
  as the design §3 confirms (no unconditional producer of the ear diagonal is landed).
* `rest` — the standard combinatorial cut data (`RemainingResidualData`).
* `M` — the peel oracle (`DiagonalAttachInput`).

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36Assembly

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonWinding (windCross)
open ProofsInTheBook.PolygonEarDelete
open ProofsInTheBook.PolygonDiagonal (leftLength rightLength)
open ProofsInTheBook.ZinanCh36SignSync (RayWindValuesWithSign RayOrientedWindData)
open ProofsInTheBook.ZinanCh36InteriorValue (WindValuesWithSign)
open ProofsInTheBook.ZinanCh36NonInterleave (sweepDir det2_r_sweepDir_pos)
open ProofsInTheBook.ZinanCh36Perturb
  (exists_lambda_transverse_edges exists_badt_polygon exists_eps_segment_in_nhds)

noncomputable section

variable {n : ℕ}

/-! ## Brick 1 — Adapter A: triangle guard-ful → ray-indexed guard-free

### Single-polygon off-boundary + vertex-generic selector

The one-polygon part of `exists_near_point_off_all_generic`: from a point `x` off `Q`'s boundary and
any neighbourhood `U`, produce a nearby `y ∈ U` off `Q`'s boundary AND `ρ`-vertex-generic.  We pick
`w = sweepDir ρ.r λ` transverse to every edge of `Q` (and to the ray), then `t ∈ (0, ε)` outside the
single per-polygon bad-`t` set and inside the preimage of `U`. -/
theorem exists_near_point_off_generic
    {m : ℕ} (Q : StrictSimplePolygon m) (ρ : RayDirection Q)
    {x : Pt} (_hQoff : ¬ OnBoundary Q x) {U : Set Pt} (hU : U ∈ nhds x) :
    ∃ y ∈ U, ¬ OnBoundary Q y ∧ ∀ k : Fin m, side ρ.r y (Q.q k) ≠ 0 := by
  classical
  -- Edge-transversality bad-λ set for `Q` (its edges are non-parallel to `ρ.r`).
  obtain ⟨badL, hbadL⟩ :=
    exists_lambda_transverse_edges ρ.r Q ρ.no_edge_parallel
  -- Pick `λ` outside it.
  obtain ⟨lam, hlam⟩ := badL.exists_notMem
  set w : Pt := sweepDir ρ.r lam with hwdef
  have hedge : ∀ k : Fin m, det2 (Q.q (cyclicNext k) - Q.q k) w ≠ 0 := hbadL lam hlam
  have hrw : det2 ρ.r w ≠ 0 :=
    ne_of_gt (det2_r_sweepDir_pos ρ.r_ne_zero lam)
  -- Per-polygon bad-`t` set.
  obtain ⟨badt, hbadt⟩ := exists_badt_polygon ρ.r Q x w hedge hrw
  -- Neighbourhood capture: `t ∈ (0, ε) ⟹ x + t•w ∈ U`.
  obtain ⟨ε, hε, hUseg⟩ := exists_eps_segment_in_nhds x w hU
  -- Pick `t ∈ (0, ε)` avoiding `badt`.
  obtain ⟨t, htio, htbad⟩ :
      ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) ε ∧ t ∉ badt := by
    have hinf : (Set.Ioo (0 : ℝ) ε).Infinite := Set.Ioo_infinite hε
    have hns : ¬ (Set.Ioo (0 : ℝ) ε ⊆ ((badt : Finset ℝ) : Set ℝ)) :=
      fun hsub => hinf (badt.finite_toSet.subset hsub)
    rw [Set.not_subset] at hns
    obtain ⟨t, hio, hnb⟩ := hns; exact ⟨t, hio, hnb⟩
  refine ⟨x + t • w, hUseg t htio, ?_⟩
  obtain ⟨hoff, hvert⟩ := hbadt t htbad
  exact ⟨hoff, hvert⟩

/-- **Adapter A.**  The triangle's guard-ful signed value package
(`triangle_windValuesWithSign`) upgrades to the ray-indexed GUARD-FREE package
`RayWindValuesWithSign Q ρ (triSign Q)`: at any off-boundary point (even a vertex-ray point), local
constancy lets us read off the value at a nearby vertex-generic point, where the guard-ful package
applies. -/
theorem triangle_rayWindValuesWithSign
    (Q : StrictSimplePolygon 3) (ρ : RayDirection Q) :
    RayWindValuesWithSign Q ρ (ZinanCh36TriBase.triSign Q) := by
  refine ⟨ZinanCh36TriBase.triSign_unit Q, ?_⟩
  intro x hoff
  -- parent local constancy on a neighbourhood `U` of `x`.
  have hev :
      ∀ᶠ y in nhds x, windCross Q ρ y = windCross Q ρ x :=
    PolygonWindingExterior.windCross_locally_constant_off_boundary Q ρ hoff
  rw [Filter.eventually_iff] at hev
  obtain ⟨y, hyU, hyoff, hyvert⟩ :=
    exists_near_point_off_generic Q ρ hoff hev
  -- guard-ful value at the nearby generic point.
  have hyval :=
    (ZinanCh36TriBase.triangle_windValuesWithSign Q).2 ρ y hyoff hyvert
  -- transfer back along local constancy.
  have hxy : windCross Q ρ y = windCross Q ρ x := hyU
  rwa [hxy] at hyval

#print axioms ProofsInTheBook.ZinanCh36Assembly.exists_near_point_off_generic
#print axioms ProofsInTheBook.ZinanCh36Assembly.triangle_rayWindValuesWithSign

/-! ## Brick 2 — the non-circular split-data structure

`EarValueSplitData P ρ i` carries the ear-diagonal split at vertex `i`: the diagonal between
`cyclicPrev i` and `cyclicNext i`, the two strict-axiom bundles, the two child ray directions along
the common parent direction.  This is `Type`-valued because it carries the child `RayDirection`s
`σL/σR` as data (the design's `: Prop` cannot hold the ray data).  It is NOT circular: it never
mentions `earDeletedExterior`, so it can serve as the induction premise that ultimately PRODUCES
that exterior field. -/
structure EarValueSplitData
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n) : Type where
  /-- the ear base is a diagonal of `P` along `ρ`. -/
  hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i)
  /-- left strict axioms at the ear base. -/
  lax : LeftStrictAxioms P (cyclicPrev i) (cyclicNext i)
  /-- right strict axioms at the ear base. -/
  rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i)
  /-- the left child ray direction. -/
  σL : RayDirection (buildLeftPoly hdiag lax)
  /-- the right child ray direction. -/
  σR : RayDirection (buildRightPoly hdiag rax)
  /-- the left child ray reuses the parent direction. -/
  hLr : σL.r = ρ.r
  /-- the right child ray reuses the parent direction. -/
  hRr : σR.r = ρ.r

/-! ## Brick 3 — the left child IS a triangle

The left child of the ear base is a `3`-gon (`leftLength_earBase`).  We transport
`triangle_rayWindValuesWithSign` across the size equality to package the left child as
`RayOrientedWindData`.  The sign carried is `triSign (cast L)`. -/

/-- **Transport of Adapter A across a `= 3` size equality.**  Any strict simple `m`-gon with
`m = 3` gets the triangle ray package by transporting along the equality.  This is the generic cast
lemma that the left-child triangle identification needs. -/
def rayOrientedWindData_of_eq_three
    {m : ℕ} (he : m = 3) (Q : StrictSimplePolygon m) (σ : RayDirection Q) :
    RayOrientedWindData Q σ := by
  subst he
  exact ⟨ZinanCh36TriBase.triSign Q,
    ZinanCh36TriBase.triSign_unit Q,
    triangle_rayWindValuesWithSign Q σ⟩

/-- **The left ear child as oriented ray-wind data.**  Because `leftLength (cyclicPrev i)
(cyclicNext i) = 3`, the left child `buildLeftPoly D.hdiag D.lax` is a triangle, so Adapter A
applies after transporting along the size equality. -/
def leftEar_rayOrientedWindData
    {P : StrictSimplePolygon n} {ρ : RayDirection P} {i : Fin n}
    (hn : 4 ≤ n) (D : EarValueSplitData P ρ i) :
    RayOrientedWindData (buildLeftPoly D.hdiag D.lax) D.σL :=
  rayOrientedWindData_of_eq_three (leftLength_earBase hn i)
    (buildLeftPoly D.hdiag D.lax) D.σL

#print axioms ProofsInTheBook.ZinanCh36Assembly.leftEar_rayOrientedWindData

/-! ## Brick 4 — the split assembly step

Given the split data `D` and oriented ray packages for both children, the parent inherits an
oriented ray package.  The two child signs coincide by the UNCONDITIONAL sibling sync
`split_child_signs_eq_final` (no `Htube` input); rewriting the right child's package to the left
sign, the perturb wrapper `rayWindValues_split` produces the parent package at the common sign. -/
def rayOrientedWindData_of_split
    {P : StrictSimplePolygon n} {ρ : RayDirection P} {i : Fin n}
    (D : EarValueSplitData P ρ i)
    (DL : RayOrientedWindData (buildLeftPoly D.hdiag D.lax) D.σL)
    (DR : RayOrientedWindData (buildRightPoly D.hdiag D.rax) D.σR) :
    RayOrientedWindData P ρ := by
  -- the two child signs coincide (UNCONDITIONAL sibling sync).
  have hsync : DL.s = DR.s :=
    ZinanCh36Straddle.split_child_signs_eq_final D.hdiag D.lax D.rax D.hLr D.hRr
      DL.values DR.values
  -- rewrite the right package to the left sign.
  have HVR' : RayWindValuesWithSign (buildRightPoly D.hdiag D.rax) D.σR DL.s := by
    rw [hsync]; exact DR.values
  -- the perturb wrapper at the common sign `DL.s`.
  exact ⟨DL.s, DL.hs,
    ZinanCh36Perturb.rayWindValues_split D.hdiag D.lax D.rax D.σL D.σR D.hLr D.hRr
      DL.values HVR'⟩

#print axioms ProofsInTheBook.ZinanCh36Assembly.rayOrientedWindData_of_split

/-! ## Brick 5 — the strong induction over vertex count

The master theorem: from the ear-diagonal supply `Esplit` alone (NO `Htube`), every strict simple
polygon with a ray carries an oriented ray-wind package.  Strong induction on `m`:

* base `m = 3`: the triangle leaf (Adapter A);
* step `4 ≤ m`: the ear base splits `P` into the left triangle (brick 3) and the right `(m-1)`-gon;
  the IH at `m - 1` (via `rightLength_earBase`) packages the right child; brick 4 assembles. -/
def rayOrientedWindData_all_of_earValueSplits
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esplit : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      4 ≤ m → EarValueSplitData P ρ (ear P)) :
    ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RayOrientedWindData P ρ := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m IH =>
    intro P ρ
    have hm3le : 3 ≤ m := P.hthree
    by_cases h4 : 4 ≤ m
    · -- split step.
      let i := ear P
      let D := Esplit P ρ h4
      -- left child is a triangle.
      have DL : RayOrientedWindData (buildLeftPoly D.hdiag D.lax) D.σL :=
        leftEar_rayOrientedWindData h4 D
      -- right child has `m - 1 < m` vertices; apply the IH after transporting the size.
      have hRlen : rightLength (cyclicPrev i) (cyclicNext i) = m - 1 :=
        rightLength_earBase h4 i
      have hlt : rightLength (cyclicPrev i) (cyclicNext i) < m := by
        rw [hRlen]; omega
      have DR : RayOrientedWindData (buildRightPoly D.hdiag D.rax) D.σR :=
        IH (rightLength (cyclicPrev i) (cyclicNext i)) hlt
          (buildRightPoly D.hdiag D.rax) D.σR
      exact rayOrientedWindData_of_split D DL DR
    · -- base: `m = 3`.
      have hm : m = 3 := le_antisymm (by omega) hm3le
      exact rayOrientedWindData_of_eq_three hm P ρ

#print axioms ProofsInTheBook.ZinanCh36Assembly.rayOrientedWindData_all_of_earValueSplits

/-! ## Brick 6 — the ray-indexed ear-interior value distribution

At an ear-interior point `x` (a strict convex combination of the three ear vertices, off all three
boundaries) with the left crossing odd, the ray packages distribute:

* `windCross_L = DL.s` (left package + odd crossing),
* `windCross_P = DL.s` (parent package + the split, the exterior parent value `0` excluded),
* `windCross_R = 0`.

The parent package `HVP` is supplied externally (from the master induction at `P`).  The both-sides
analysis is by `omega` on `windCross_L + windCross_R = windCross_P` with `L = s`, `P ∈ {0,s}`,
`R ∈ {0,s}`, `s = ±1`. -/
theorem earInterior_values_ray
    {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hLr : σL.r = ρ.r) (hRr : σR.r = ρ.r) {s : ℤ}
    (HVL : RayWindValuesWithSign (buildLeftPoly h lax) σL s)
    (HVR : RayWindValuesWithSign (buildRightPoly h rax) σR s)
    (HVP : RayWindValuesWithSign P ρ s)
    {x : Pt}
    (hLodd : Odd (CrossingNumber' (buildLeftPoly h lax) σL x))
    (hLoff : ¬ OnBoundary (buildLeftPoly h lax) x)
    (hRoff : ¬ OnBoundary (buildRightPoly h rax) x)
    (hPoff : ¬ OnBoundary P x) :
    windCross (buildLeftPoly h lax) σL x = s ∧
      windCross P ρ x = s ∧
      windCross (buildRightPoly h rax) σR x = 0 := by
  -- left winding = s (odd crossing forces nonzero, package pins it to s).
  have hLne : windCross (buildLeftPoly h lax) σL x ≠ 0 :=
    PolygonWinding.windCross_ne_zero_of_odd_crossing _ _ hLodd
  have hLs : windCross (buildLeftPoly h lax) σL x = s := by
    rcases HVL.values x hLoff with h0 | hs
    · exact absurd h0 hLne
    · exact hs
  -- the split identity and the three package memberships.
  have hsplit := PolygonWinding.windCross_split_common h lax rax σL σR hLr hRr x
  have hPval := HVP.values x hPoff
  have hRval := HVR.values x hRoff
  have hsu : s = 1 ∨ s = -1 := HVL.sign_unit
  -- `omega` resolves: with `L = s`, `P ∈ {0,s}`, `R ∈ {0,s}`, `s = ±1`, force `P = s`, `R = 0`.
  refine ⟨hLs, ?_, ?_⟩ <;>
    rcases hPval with hP0 | hPs <;> rcases hRval with hR0 | hRs <;>
      rcases hsu with hs1 | hsm1 <;> omega

#print axioms ProofsInTheBook.ZinanCh36Assembly.earInterior_values_ray

/-! ## Brick 7 — the ear-deleted exterior from the ray packages

Wiring brick 6 into the committed signed exterior route `earDeletedExterior_winding_route_sign`: the
ear-interior point lies outside the ear-deleted polygon `R`. -/
theorem earDeletedExterior_of_values
    {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hLr : σL.r = ρ.r) (hRr : σR.r = ρ.r) {s : ℤ}
    (HVL : RayWindValuesWithSign (buildLeftPoly h lax) σL s)
    (HVR : RayWindValuesWithSign (buildRightPoly h rax) σR s)
    (HVP : RayWindValuesWithSign P ρ s)
    {x : Pt}
    (hLodd : Odd (CrossingNumber' (buildLeftPoly h lax) σL x))
    (hLoff : ¬ OnBoundary (buildLeftPoly h lax) x)
    (hRoff : ¬ OnBoundary (buildRightPoly h rax) x)
    (hPoff : ¬ OnBoundary P x) :
    ¬ ClosedRegion' (buildRightPoly h rax) σR x := by
  obtain ⟨hLs, hPs, _hR0⟩ :=
    earInterior_values_ray h lax rax σL σR hLr hRr HVL HVR HVP
      hLodd hLoff hRoff hPoff
  exact ZinanCh36InteriorValue.earDeletedExterior_winding_route_sign
    h lax rax σL σR hLr hRr hRoff hLs hPs

#print axioms ProofsInTheBook.ZinanCh36Assembly.earDeletedExterior_of_values

/-! ## Brick 8 helper — the left-child interior is odd (GUARD-FREE)

For an ear-interior point (strict convex combination of the three ear vertices) the LEFT child is a
triangle whose vertices are exactly those three ear points (`subpolygonLeftTuple_earBase`).  The
guard-free triangle interior lemma `interior_mem_region` then gives `ClosedRegion' L σL x`, and since
`x` is off the left boundary the crossing number is odd.  No vertex-ray side guards are needed —
`interior_mem_region` picks its own vertex-avoiding ray internally and transports. -/
/-- **Transport of the guard-free triangle interior-odd across a `= 3` size equality.**  Any strict
simple `m`-gon `Q` with `m = 3` whose three vertices realize a strict convex combination has odd
crossing number at that off-boundary point — `interior_mem_region` applied after `subst`. -/
theorem tri_interior_odd_of_eq_three
    {m : ℕ} (he : m = 3) (Q : StrictSimplePolygon m) (σ : RayDirection Q)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • Q.q ⟨0, by omega⟩ + w1 • Q.q ⟨1, by omega⟩ + w2 • Q.q ⟨2, by omega⟩)
    (hoff : ¬ OnBoundary Q x) :
    Odd (CrossingNumber' Q σ x) := by
  subst he
  have hreg : ClosedRegion' Q σ x :=
    PolygonTriangleConvex.interior_mem_region Q σ hw0 hw1 hw2 hsum hx
  rcases hreg with hb | hodd
  · exact absurd hb hoff
  · exact hodd

theorem leftEar_interior_odd
    {P : StrictSimplePolygon n} {ρ : RayDirection P} {i : Fin n}
    (hn : 4 ≤ n) (D : EarValueSplitData P ρ i)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i))
    (hLoff : ¬ OnBoundary (buildLeftPoly D.hdiag D.lax) x) :
    Odd (CrossingNumber' (buildLeftPoly D.hdiag D.lax) D.σL x) := by
  have he : leftLength (cyclicPrev i) (cyclicNext i) = 3 := leftLength_earBase hn i
  -- the three left-child vertex identities (ear base ⟹ `prev i, i, next i`).
  have hq0 : (buildLeftPoly D.hdiag D.lax).q ⟨0, by rw [he]; omega⟩ = P.q (cyclicPrev i) := by
    rw [buildLeftPoly_q, subpolygonLeftTuple_earBase hn P i ⟨0, by rw [he]; omega⟩]; rfl
  have hq1 : (buildLeftPoly D.hdiag D.lax).q ⟨1, by rw [he]; omega⟩ = P.q i := by
    rw [buildLeftPoly_q, subpolygonLeftTuple_earBase hn P i ⟨1, by rw [he]; omega⟩]; rfl
  have hq2 : (buildLeftPoly D.hdiag D.lax).q ⟨2, by rw [he]; omega⟩ = P.q (cyclicNext i) := by
    rw [buildLeftPoly_q, subpolygonLeftTuple_earBase hn P i ⟨2, by rw [he]; omega⟩]; rfl
  -- `x` is the convex combination of the left child's three vertices.
  have hxL : x = w0 • (buildLeftPoly D.hdiag D.lax).q ⟨0, by rw [he]; omega⟩
      + w1 • (buildLeftPoly D.hdiag D.lax).q ⟨1, by rw [he]; omega⟩
      + w2 • (buildLeftPoly D.hdiag D.lax).q ⟨2, by rw [he]; omega⟩ := by
    rw [hq0, hq1, hq2]; exact hx
  exact tri_interior_odd_of_eq_three he (buildLeftPoly D.hdiag D.lax) D.σL
    hw0 hw1 hw2 hsum hxL hLoff

#print axioms ProofsInTheBook.ZinanCh36Assembly.leftEar_interior_odd

/-- **The ear orientation is nondegenerate**, derived from the left strict axioms.  The left
child's middle-vertex noncollinearity (`lax.noncollinear ⟨1⟩`) is exactly `orient (P.q (cyclicPrev
i)) (P.q i) (P.q (cyclicNext i)) ≠ 0` after identifying the left tuple at indices `0,1,2`. -/
theorem earOrient_of_lax
    {P : StrictSimplePolygon n} {ρ : RayDirection P} {i : Fin n}
    (hn : 4 ≤ n) (D : EarValueSplitData P ρ i) :
    orient (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) ≠ 0 := by
  have he : leftLength (cyclicPrev i) (cyclicNext i) = 3 := leftLength_earBase hn i
  set k : Fin (leftLength (cyclicPrev i) (cyclicNext i)) := ⟨1, by rw [he]; omega⟩ with hkdef
  have hnc := D.lax.noncollinear k
  -- index identities for the left tuple at `cyclicPrev k`, `k`, `cyclicNext k`.
  have hkprev : (cyclicPrev k).val = 0 := by
    rw [PolygonConvexVertex.cyclicPrev_val, hkdef]; simp
  have hknext : (cyclicNext k).val = 2 := by
    rw [leftBase_cyclicNext hn i k, hkdef]; norm_num
  have hkval : k.val = 1 := rfl
  rw [subpolygonLeftTuple_earBase hn P i (cyclicPrev k),
      subpolygonLeftTuple_earBase hn P i k,
      subpolygonLeftTuple_earBase hn P i (cyclicNext k)] at hnc
  rw [hkprev, hkval, hknext] at hnc
  simpa using hnc

#print axioms ProofsInTheBook.ZinanCh36Assembly.earOrient_of_lax

/-- **Transport of the triangle off-boundary across a `= 3` size equality.** -/
theorem offBoundary_left_of_interior
    {m : ℕ} (he : m = 3) (Q : StrictSimplePolygon m)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • Q.q ⟨0, by omega⟩ + w1 • Q.q ⟨1, by omega⟩ + w2 • Q.q ⟨2, by omega⟩) :
    ¬ OnBoundary Q x := by
  subst he
  exact PolygonTriangleConvex.not_onBoundary_of_interior Q hw0 hw1 hw2 hsum hx

/-! ## Brick 8 — the `EarCutData` builder

Assembles `EarCutData P ρ (ear P)` from the non-circular split supply `Esplit`.  All structural
fields project from `EarValueSplitData`; the single genuine `earDeletedExterior` field is produced
by the value route (brick 7) using the master induction packages for the left child, the given
right child ray, and the parent.  The left-child oddness is guard-free (brick-8 helper). -/
def EarCutData_of_interiorValues
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esplit : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      4 ≤ m → EarValueSplitData P ρ (ear P))
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (hm : 4 ≤ m) :
    EarCutData P ρ (ear P) :=
  let D := Esplit P ρ hm
  { hdiag := D.hdiag
    lax := D.lax
    rax := D.rax
    leftRayEq := ⟨D.σL, D.hLr⟩
    rightRayEq := ⟨D.σR, D.hRr⟩
    earOrient := earOrient_of_lax hm D
    earDeletedExterior := by
      intro x w0 w1 w2 hPoff hw0 hw1 hw2 hsum hx σR hσRr
      -- the master induction packages for the left child, the GIVEN right child ray, the parent.
      have hL :
          RayOrientedWindData (buildLeftPoly D.hdiag D.lax) D.σL :=
        leftEar_rayOrientedWindData hm D
      have hRx :
          RayOrientedWindData (buildRightPoly D.hdiag D.rax) σR :=
        rayOrientedWindData_all_of_earValueSplits ear Esplit
          (buildRightPoly D.hdiag D.rax) σR
      have hP : RayOrientedWindData P ρ :=
        rayOrientedWindData_all_of_earValueSplits ear Esplit P ρ
      -- sibling sign sync: the left and the given right child signs coincide.
      have hsyncLR : hL.s = hRx.s :=
        ZinanCh36Straddle.split_child_signs_eq_final D.hdiag D.lax D.rax D.hLr hσRr
          hL.values hRx.values
      -- the parent package: assemble from the left + given right via the perturb wrapper at `hL.s`.
      have HVRx' : RayWindValuesWithSign (buildRightPoly D.hdiag D.rax) σR hL.s := by
        rw [hsyncLR]; exact hRx.values
      have HVP : RayWindValuesWithSign P ρ hL.s :=
        ZinanCh36Perturb.rayWindValues_split D.hdiag D.lax D.rax D.σL σR D.hLr hσRr
          hL.values HVRx'
      -- off the left boundary: an ear-interior point is off the (left) triangle boundary.
      have hLoff : ¬ OnBoundary (buildLeftPoly D.hdiag D.lax) x := by
        -- the left child is a triangle whose interior point `x` is off its boundary.
        have he : leftLength (cyclicPrev (ear P)) (cyclicNext (ear P)) = 3 :=
          leftLength_earBase hm (ear P)
        have hq0 : (buildLeftPoly D.hdiag D.lax).q ⟨0, by rw [he]; omega⟩
            = P.q (cyclicPrev (ear P)) := by
          rw [buildLeftPoly_q, subpolygonLeftTuple_earBase hm P (ear P) ⟨0, by rw [he]; omega⟩]; rfl
        have hq1 : (buildLeftPoly D.hdiag D.lax).q ⟨1, by rw [he]; omega⟩ = P.q (ear P) := by
          rw [buildLeftPoly_q, subpolygonLeftTuple_earBase hm P (ear P) ⟨1, by rw [he]; omega⟩]; rfl
        have hq2 : (buildLeftPoly D.hdiag D.lax).q ⟨2, by rw [he]; omega⟩
            = P.q (cyclicNext (ear P)) := by
          rw [buildLeftPoly_q, subpolygonLeftTuple_earBase hm P (ear P) ⟨2, by rw [he]; omega⟩]; rfl
        have hxL : x = w0 • (buildLeftPoly D.hdiag D.lax).q ⟨0, by rw [he]; omega⟩
            + w1 • (buildLeftPoly D.hdiag D.lax).q ⟨1, by rw [he]; omega⟩
            + w2 • (buildLeftPoly D.hdiag D.lax).q ⟨2, by rw [he]; omega⟩ := by
          rw [hq0, hq1, hq2]; exact hx
        exact offBoundary_left_of_interior he (buildLeftPoly D.hdiag D.lax)
          hw0 hw1 hw2 hsum hxL
      have hLodd : Odd (CrossingNumber' (buildLeftPoly D.hdiag D.lax) D.σL x) :=
        leftEar_interior_odd hm D hw0 hw1 hw2 hsum hx hLoff
      -- The right boundary off-ness: an ear-interior parent point is off the ear-deleted boundary
      -- (UNCONDITIONAL: `interiorEar_offBoundary_earDeleted`).
      have hRoff : ¬ OnBoundary (buildRightPoly D.hdiag D.rax) x :=
        PolygonEarCornerEscape.interiorEar_offBoundary_earDeleted P ρ (ear P)
          D.hdiag D.rax (earOrient_of_lax hm D) hPoff hw1 hsum hx
      exact earDeletedExterior_of_values D.hdiag D.lax D.rax D.σL σR D.hLr hσRr
        hL.values HVRx' HVP hLodd hLoff hRoff hPoff }

#print axioms ProofsInTheBook.ZinanCh36Assembly.EarCutData_of_interiorValues

/-! ## Brick 9 — residue and headline wiring

The `EarCutData` builder (brick 8) supplies the `Esup` premise of the landed
`PolygonEarExistence.isConvexVertex'_holds` / `artGallery_strict`.  The `rest` (combinatorial cut
data) and `M` (peel oracle) remain genuine inputs, exactly as in the landed bridge. -/

/-- **The `PolygonGeomResidue` discharged from interior values.**  Wires the `EarCutData` builder
into the landed `isConvexVertex'_holds`: the convex-vertex containment is now PROVED via the
interior-value route (ear induction down to the `n = 3` triangle leaf).  Remaining input: `rest`. -/
def polygonGeomResidue_of_interiorValues
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esplit : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      4 ≤ m → EarValueSplitData P ρ (ear P))
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      PolygonJordan.RemainingResidualData P ρ (ear P)) :
    PolygonGeomInput.PolygonGeomResidue :=
  PolygonEarExistence.isConvexVertex'_holds ear
    (fun P σ hm => EarCutData_of_interiorValues ear Esplit P σ hm)
    rest

#print axioms ProofsInTheBook.ZinanCh36Assembly.polygonGeomResidue_of_interiorValues

/-- **Chapter-36 art-gallery `⌊n/3⌋` headline from interior values.**  Every strict simple polygon
with a ray admits `≤ ⌊n/3⌋` vertex guards seeing its whole closed region, with the convex-vertex
containment now PROVED from the interior-value ear induction.  The remaining inputs are the
ear-diagonal supply `Esplit` (architectural, no unconditional producer landed — design §3), the
combinatorial cut data `rest`, and the peel oracle `M`. -/
theorem artGallery_strict_mod_M {n : ℕ}
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esplit : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      4 ≤ m → EarValueSplitData P ρ (ear P))
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      PolygonJordan.RemainingResidualData P ρ (ear P))
    (M : PolygonLast.DiagonalAttachInput
      (PolygonOracleClose.baseTriangleFacts_of_leaf
        (PolygonLeaf.baseTriangleLeaf_of_atoms
          PolygonTriangleConvex.triangleConvexLeaf_holds
          PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, PolygonRayIndep.Sees P ρ (P.q v) x :=
  PolygonGeomInput.artGallery_strict_of_residue
    (polygonGeomResidue_of_interiorValues ear Esplit rest) M P ρ

#print axioms ProofsInTheBook.ZinanCh36Assembly.artGallery_strict_mod_M

end

end ProofsInTheBook.ZinanCh36Assembly
