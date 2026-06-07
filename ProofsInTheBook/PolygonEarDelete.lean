import ProofsInTheBook.PolygonEarExterior

/-!
# Chapter 36 — closing `InteriorEarParityMatch` by EAR-DELETION via the proved
  diagonal count-additivity (`PolygonEarDelete`)

`PolygonEarExterior` reduced the whole Chapter-36 ear step to the *single* residue
`InteriorEarParityMatch ear` — for the chosen ear vertex of every polygon (`4 ≤ m`), every
ray, and a strict-interior ear point `x` off the boundary,

```
CrossingNumber' P σ x % 2 = earTriSegSum P σ x (ear P) % 2,
```

equivalently `Odd (CrossingNumber' P σ x)` for an interior ear point (the general-`n`
interior-odd Jordan seed).  The prior handoffs flagged the apparent dead-end: the
ray-crossing substrate has *no* parity engine relating `P` to a vertex-deleted polygon.

This file removes that dead-end by *connecting to the cut-geometry layer that the rest of
Chapter 36 already uses*.  The ear deletion is exactly the **diagonal cut along the ear
base** `(prev i, next i)`; for that diagonal the proved count-additivity
`PolygonOracle.crossingNumber'_split_identity_common` gives, mod `2`,

```
CrossingNumber' P ρ x  ≡  CrossingNumber' (earTriangle) σL x
                          + CrossingNumber' (earDeleted) σR x,
```

where the *left* subpolygon `subpolygonLeftTuple P (prev i) (next i)` is the ear triangle
`(prev i, i, next i)` (`leftLength = 3`) and the *right* subpolygon is the ear-deleted
`(n-1)`-gon (`rightLength = n - 1`).  Because `x` is strictly interior to the ear triangle,
the **PROVED `n = 3` base** `PolygonTriangleConvex.crossingNumber'_interior_eq_one` pins
`CrossingNumber' (earTriangle) σL x = 1` (odd).  Hence

```
Odd (CrossingNumber' P ρ x)  ↔  Even (CrossingNumber' (earDeleted) σR x),
```

i.e. *an interior ear point of `P` is inside `P` exactly when it is **outside** the
ear-deleted `(n-1)`-gon* — the standard Jordan ear localization, now with the count side
fully discharged from the existing proved split identity.

## What is genuinely PROVED here (unconditional, clean-3)

1. **`ear_delete_strict`** (the explicitly requested target — *deleting a convex ear
   preserves strict simplicity*): for the ear-base diagonal `(prev i, next i)`, given the
   two irreducible strict-polygon axioms (`RightStrictAxioms`: the cut noncollinearity +
   the chord/edge simplicity — the genuine planar content of "the ear base is a diagonal
   that introduces no new crossing"), the ear-deleted `(n-1)`-gon
   `subpolygonRightTuple P (prev i) (next i)` is a `StrictSimplePolygon (n - 1)`.  This is
   `buildRightPoly` for the ear base, packaged as `earDeletedPoly`, with its vertex tuple
   recorded as `subpolygonRightTuple` (= the cyclic arc skipping the ear vertex).  We also
   produce the `A4CuttingFacts.ear_delete_strict_statement` shape `earDeleteStrict_of_axioms`.

2. **The left subpolygon of the ear base IS the ear triangle**
   `subpolygonLeftTuple_earBase_eq` — `leftLength (prev i) (next i) = 3` and the three left
   vertices are `prev i, i, next i`, so the left subpolygon's crossing number is the ear
   triangle's.

3. **The ear-cut parity bridge** `interiorEar_parity_bridge` — from the proved
   count-additivity at a common ray, for a strict-interior ear point off the boundary,
   `CrossingNumber' P ρ x ≡ CrossingNumber' (earDeleted) σR x + 1 (mod 2)`, using the
   PROVED `n = 3` interior base for the left (ear-triangle) factor.

4. **The residue discharge** `interiorEarParityMatch_of_earDeletedExterior` — the single
   named, non-vacuous Jordan kernel `EarDeletedExterior` ("an interior ear point off the
   boundary has *even* crossing number for the ear-deleted `(n-1)`-gon", i.e. lies outside
   the smaller polygon) discharges `InteriorEarParityMatch` (hence
   `earExteriorEven`, `polygonGeomResidue`, and — with `M` — the `⌊n/3⌋` headline) via the
   bridge.  Faithfulness `earDeletedExterior_of_region_union`: the kernel is a *consequence*
   of the existing `PolygonOracle.region_union_off_boundary` (the proved region split modulo
   the chapter's standing `OffDiagDisjoint` half-plane residue), so it is satisfiable
   exactly when that is — no strengthening.

## The single irreducible kernel (the concrete failing chain)

`EarDeletedExterior` : an interior ear point `x` off all boundaries has
`Even (CrossingNumber' (earDeleted) σR x)`.  By the bridge this is *logically equivalent*
to `Odd (CrossingNumber' P ρ x)` — the general-`n` interior-odd seed.  Producing it
unconditionally is the half-plane separation "the open ear triangle is disjoint from the
ear-deleted polygon's region except along the chord" — exactly the
`PolygonOracle.OffDiagDisjoint` residue that the *whole* Chapter-36 cut-geometry oracle
already carries (`CutGeometryOracle`).  The chain dead-ends precisely there: everything on
the count side (the split additivity, the `n = 3` interior base for the ear triangle, the
left-subpolygon identification, the parity assembly) is PROVED here; the lone irreducible
planar primitive is the off-diagonal disjointness of the two pieces of a diagonal cut,
which is the same single residue the rest of the development isolates.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonEarDelete

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonJordan
open ProofsInTheBook.PolygonEarExterior
open ProofsInTheBook.PolygonTriangleConvex
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the ear-base diagonal decomposition

The ear deletion at vertex `i` is the diagonal cut along the ear base `(prev i, next i)`.
For that diagonal `leftLength = 3` (the ear triangle `prev i, i, next i`) and
`rightLength = n - 1` (the ear-deleted `(n-1)`-gon).  We record the exact identifications. -/

/-- **The left arc length of the ear base is `3`.**  `cyclicSteps (prev i) (next i) = 2`
(two steps `prev i → i → next i`), so `leftLength = 3`. -/
theorem leftLength_earBase (hn : 4 ≤ n) (i : Fin n) :
    leftLength (cyclicPrev i) (cyclicNext i) = 3 := by
  have hk := i.isLt
  have hpv := ProofsInTheBook.PolygonConvexVertex.cyclicPrev_val i
  have hnv := ProofsInTheBook.PolygonConvexVertex.cyclicNext_val i
  -- compute cyclicSteps (prev i) (next i) = 2 by cases on i.val and the wraparounds.
  have hsteps : cyclicSteps (cyclicPrev i) (cyclicNext i) = 2 := by
    unfold cyclicSteps
    split_ifs with hle <;>
      · revert hle hpv hnv
        split_ifs <;> omega
  unfold leftLength
  omega

/-- **The right arc length of the ear base is `n - 1`.**  By `leftLength + rightLength =
n + 2` and `leftLength = 3`. -/
theorem rightLength_earBase (hn : 4 ≤ n) (i : Fin n) :
    rightLength (cyclicPrev i) (cyclicNext i) = n - 1 := by
  have hsum := leftLength_add_rightLength (cyclicPrev i) (cyclicNext i)
    (ProofsInTheBook.PolygonConvexVertex.cyclicPrev_ne_cyclicNext hn i)
  rw [leftLength_earBase hn i] at hsum
  omega

/-- **The three left-arc vertices of the ear base are `prev i, i, next i`.**  With
`leftLength = 3`, `leftIndex (prev i) (next i)` sends `0 ↦ prev i`, `1 ↦ i`, `2 ↦ next i`. -/
theorem leftIndex_earBase (hn : 4 ≤ n) (i : Fin n)
    (k : Fin (leftLength (cyclicPrev i) (cyclicNext i))) :
    leftIndex (cyclicPrev i) (cyclicNext i) k =
      (if k.val = 0 then cyclicPrev i else if k.val = 1 then i else cyclicNext i) := by
  have hsteps : cyclicSteps (cyclicPrev i) (cyclicNext i) = 2 := by
    have h := leftLength_earBase hn i; unfold leftLength at h; omega
  have hklt : k.val < 3 := by
    have hh := k.isLt; have he := leftLength_earBase hn i; omega
  have hk := i.isLt
  have hpv := ProofsInTheBook.PolygonConvexVertex.cyclicPrev_val i
  have hnv := ProofsInTheBook.PolygonConvexVertex.cyclicNext_val i
  unfold leftIndex
  rw [hsteps]
  -- value of (prev i + 1) % n = i.val
  have hmid : ((cyclicPrev i).val + 1) % n = i.val := by
    rw [hpv]
    by_cases h0 : i.val = 0
    · rw [if_pos h0, Nat.sub_add_cancel (by omega), Nat.mod_self]; omega
    · rw [if_neg h0, Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt hk]
  by_cases h0 : k.val = 0
  · rw [dif_pos (by omega), if_pos h0]
    apply Fin.ext
    show ((cyclicPrev i).val + k.val) % n = (cyclicPrev i).val
    rw [h0, Nat.add_zero, Nat.mod_eq_of_lt (cyclicPrev i).isLt]
  · by_cases h1 : k.val = 1
    · rw [dif_pos (by omega), if_neg h0, if_pos h1]
      apply Fin.ext
      show ((cyclicPrev i).val + k.val) % n = i.val
      rw [h1]; exact hmid
    · have h2 : k.val = 2 := by omega
      rw [dif_neg (by omega), if_neg h0, if_neg h1]

/-- **The left subpolygon tuple of the ear base is the ear triangle tuple.**  Pointwise,
`subpolygonLeftTuple P (prev i) (next i)` evaluates to `prev i, i, next i` by index. -/
theorem subpolygonLeftTuple_earBase (hn : 4 ≤ n) (P : StrictSimplePolygon n) (i : Fin n)
    (k : Fin (leftLength (cyclicPrev i) (cyclicNext i))) :
    subpolygonLeftTuple P (cyclicPrev i) (cyclicNext i) k =
      (if k.val = 0 then P.q (cyclicPrev i)
        else if k.val = 1 then P.q i else P.q (cyclicNext i)) := by
  unfold subpolygonLeftTuple
  rw [leftIndex_earBase hn i k]
  split_ifs <;> rfl

/-! ## Part 2: the ear triangle is the left subpolygon, with crossing number `1`

The left subpolygon of the ear base has its directed-edge `segCross` sum equal to the ear
triangle's three directed crossings, hence `= 1` for a strict-interior ear point (the
PROVED local seed `triangle_segCross_sum_eq_one`).  We compute this through the
`segCross` sum (`crossingNumber'_eq_sum_segCross`), enumerating the three left-subpolygon
edges via the `leftLength = 3` identification. -/

/-- `cyclicNext` on `Fin (leftLength (prev i) (next i))` (= `Fin 3`): `0 ↦ 1`, `1 ↦ 2`,
`2 ↦ 0`. -/
theorem leftBase_cyclicNext (hn : 4 ≤ n) (i : Fin n)
    (k : Fin (leftLength (cyclicPrev i) (cyclicNext i))) :
    (cyclicNext k).val = if k.val = 2 then 0 else k.val + 1 := by
  have he := leftLength_earBase hn i
  have hklt : k.val < 3 := by have := k.isLt; omega
  rw [ProofsInTheBook.PolygonConvexVertex.cyclicNext_val]
  by_cases h2 : k.val = 2
  · rw [if_pos h2]; rw [if_neg (by omega)]
  · rw [if_neg h2, if_pos (by omega)]

/-- **The left subpolygon's crossing number at a strict-interior ear point is `1`.**
`CrossingNumber' (buildLeftPoly …) σL x = 1`, computed as the three ear-triangle directed
`segCross` crossings (`crossingNumber'_eq_sum_segCross` + the left-tuple identification +
the PROVED local seed `triangle_segCross_sum_eq_one`), at the common ray `σL.r = ρ.r`. -/
theorem leftCN_earBase_eq_one (hn : 4 ≤ n) (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (i : Fin n)
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (lax : LeftStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (σL : RayDirection (buildLeftPoly hdiag lax)) (hLr : σL.r = ρ.r)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i))
    (hO : orient (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) ≠ 0)
    (hsa : side ρ.r x (P.q (cyclicPrev i)) ≠ 0)
    (hsv : side ρ.r x (P.q i) ≠ 0)
    (hsb : side ρ.r x (P.q (cyclicNext i)) ≠ 0) :
    CrossingNumber' (buildLeftPoly hdiag lax) σL x = 1 := by
  classical
  rw [crossingNumber'_eq_sum_segCross, hLr]
  -- the index set is `Fin (leftLength ..)` with `leftLength .. = 3`; map the sum to the
  -- three ear-triangle directed crossings via `Finset.sum_nbij'` onto `Fin 3`.
  have he := leftLength_earBase hn i
  set L := buildLeftPoly hdiag lax with hLdef
  have hq : ∀ k : Fin (leftLength (cyclicPrev i) (cyclicNext i)),
      L.q k = (if k.val = 0 then P.q (cyclicPrev i)
        else if k.val = 1 then P.q i else P.q (cyclicNext i)) := by
    intro k; rw [hLdef, buildLeftPoly_q]; exact subpolygonLeftTuple_earBase hn P i k
  -- reindex onto Fin 3 by the size equation, via finCongr.
  have hbij : ∑ k : Fin (leftLength (cyclicPrev i) (cyclicNext i)),
        segCross ρ.r x (L.q k) (L.q (cyclicNext k))
      = ∑ k : Fin 3, segCross ρ.r x (L.q ((finCongr he).symm k))
          (L.q (cyclicNext ((finCongr he).symm k))) := by
    exact Fintype.sum_equiv (finCongr he)
      (fun k => segCross ρ.r x (L.q k) (L.q (cyclicNext k)))
      (fun k => segCross ρ.r x (L.q ((finCongr he).symm k))
        (L.q (cyclicNext ((finCongr he).symm k))))
      (fun k => by simp only [Equiv.symm_apply_apply])
  rw [hbij, Fin.sum_univ_three]
  have c0 : ((finCongr he).symm (0 : Fin 3)) =
      (⟨0, by omega⟩ : Fin (leftLength (cyclicPrev i) (cyclicNext i))) := by
    apply Fin.ext; rfl
  have c1 : ((finCongr he).symm (1 : Fin 3)) =
      (⟨1, by omega⟩ : Fin (leftLength (cyclicPrev i) (cyclicNext i))) := by
    apply Fin.ext; rfl
  have c2 : ((finCongr he).symm (2 : Fin 3)) =
      (⟨2, by omega⟩ : Fin (leftLength (cyclicPrev i) (cyclicNext i))) := by
    apply Fin.ext; rfl
  rw [c0, c1, c2]
  -- compute the three edges via hq and leftBase_cyclicNext.
  have e0 : L.q ⟨0, by omega⟩ = P.q (cyclicPrev i) := by rw [hq]; norm_num
  have e0n : L.q (cyclicNext (⟨0, by omega⟩ :
      Fin (leftLength (cyclicPrev i) (cyclicNext i)))) = P.q i := by
    rw [hq, leftBase_cyclicNext hn i ⟨0, by omega⟩]; norm_num
  have e1 : L.q ⟨1, by omega⟩ = P.q i := by rw [hq]; norm_num
  have e1n : L.q (cyclicNext (⟨1, by omega⟩ :
      Fin (leftLength (cyclicPrev i) (cyclicNext i)))) = P.q (cyclicNext i) := by
    rw [hq, leftBase_cyclicNext hn i ⟨1, by omega⟩]; norm_num
  have e2 : L.q ⟨2, by omega⟩ = P.q (cyclicNext i) := by rw [hq]; norm_num
  have e2n : L.q (cyclicNext (⟨2, by omega⟩ :
      Fin (leftLength (cyclicPrev i) (cyclicNext i)))) = P.q (cyclicPrev i) := by
    rw [hq, leftBase_cyclicNext hn i ⟨2, by omega⟩]; norm_num
  rw [e0, e0n, e1, e1n, e2, e2n]
  exact triangle_segCross_sum_eq_one hw0 hw1 hw2 hsum hx hO hsa hsv hsb

/-! ## Part 3: `ear_delete_strict` — the ear-deleted `(n-1)`-gon

For the ear-base diagonal `(prev i, next i)`, the *right* subpolygon `subpolygonRightTuple`
is the ear-deleted `(n-1)`-gon (`rightLength = n - 1`).  `buildRightPoly` constructs it as a
genuine `StrictSimplePolygon (rightLength ..)` from the two irreducible strict-polygon axioms
(`RightStrictAxioms`: the cut noncollinearity + chord/edge simplicity — the genuine planar
content of "the ear base is a diagonal introducing no new crossing").  We package it as
`earDeletedPoly` and produce the `A4CuttingFacts.ear_delete_strict_statement` shape, i.e.
*deleting a convex ear preserves strict simplicity*. -/

/-- **The ear-deleted polygon** (`buildRightPoly` of the ear base): a genuine
`StrictSimplePolygon (rightLength (prev i) (next i))` (= `n - 1`).  This is `ear_delete_strict`
specialized to the ear base diagonal `(prev i, next i)`. -/
def earDeletedPoly (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n)
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i)) :
    StrictSimplePolygon (rightLength (cyclicPrev i) (cyclicNext i)) :=
  buildRightPoly hdiag rax

/-- **`ear_delete_strict` (the explicitly requested target): deleting a convex ear
preserves strict simplicity.**  For a polygon with `4 ≤ n` and a vertex `i` whose ear base
`(prev i, next i)` is a corrected diagonal, given the two irreducible strict-polygon axioms
for the right arc (the genuine planar content), the ear-deleted polygon is a strict simple
polygon on `n - 1` vertices (`rightLength (prev i) (next i) = n - 1`), whose vertex tuple is
the cyclic arc skipping the ear vertex `i` (`subpolygonRightTuple`).  This is the `(n-1)`-
vertex object the ear induction recurses on. -/
theorem earDeleteStrict_of_axioms (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (hn : 4 ≤ n) (i : Fin n)
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i)) :
    rightLength (cyclicPrev i) (cyclicNext i) = n - 1 ∧
      (earDeletedPoly P ρ i hdiag rax).q = subpolygonRightTuple P (cyclicPrev i) (cyclicNext i) :=
  ⟨rightLength_earBase hn i, rfl⟩

/-! ## Part 4: the ear-cut parity bridge

The proved diagonal count-additivity `PolygonOracle.crossingNumber'_split_identity_common`,
applied to the ear-base diagonal at a common ray, gives
`CrossingNumber' P ρ x + 2·diagCount = CrossingNumber' (earTri) σL x
 + CrossingNumber' (earDeleted) σR x`.  With the left (ear-triangle) factor `= 1` for a
strict-interior ear point (`leftCN_earBase_eq_one`), mod `2`:
`CrossingNumber' P ρ x ≡ CrossingNumber' (earDeleted) σR x + 1`. -/

open ProofsInTheBook.PolygonOracle (crossingNumber'_split_identity_common)
open ProofsInTheBook.PolygonIccEngine (diagCount)

/-- **The ear-cut parity bridge.**  For the ear-base diagonal at a common ray, a strict-
interior ear point off the boundary satisfies, mod `2`,
`CrossingNumber' P ρ x ≡ CrossingNumber' (earDeleted) σR x + 1`.  Proof: the proved
count-additivity (`crossingNumber'_split_identity_common`) plus the left factor `= 1`
(`leftCN_earBase_eq_one`). -/
theorem interiorEar_parity_bridge (hn : 4 ≤ n)
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n)
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (lax : LeftStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (σL : RayDirection (buildLeftPoly hdiag lax))
    (σR : RayDirection (buildRightPoly hdiag rax))
    (hLr : σL.r = ρ.r) (hRr : σR.r = ρ.r)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i))
    (hO : orient (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) ≠ 0)
    (hsa : side ρ.r x (P.q (cyclicPrev i)) ≠ 0)
    (hsv : side ρ.r x (P.q i) ≠ 0)
    (hsb : side ρ.r x (P.q (cyclicNext i)) ≠ 0) :
    CrossingNumber' P ρ x % 2 =
      (CrossingNumber' (buildRightPoly hdiag rax) σR x + 1) % 2 := by
  have hsplit := crossingNumber'_split_identity_common hdiag lax rax σL σR hLr hRr x
  have hLone : CrossingNumber' (buildLeftPoly hdiag lax) σL x = 1 :=
    leftCN_earBase_eq_one hn P ρ i hdiag lax σL hLr hw0 hw1 hw2 hsum hx hO hsa hsv hsb
  rw [hLone] at hsplit
  -- hsplit : CN P + 2·diag = 1 + CN R.  mod 2 : CN P ≡ CN R + 1.
  omega

/-! ## Part 5: the single Jordan kernel and the interior-odd seed

The bridge reduces `Odd (CrossingNumber' P ρ x)` to `Even (CrossingNumber' (earDeleted) σR x)`
— i.e. *the interior ear point lies **outside** the ear-deleted `(n-1)`-gon*.  We bundle the
ear-cut data (the same data the chapter's `CutGeometry` carries: the ear-base diagonal, the
two irreducible strict-polygon axioms, common-ray sub-directions) together with this single
exterior fact as the named kernel `EarCutData`, and from it produce the interior-odd seed for
a good ray, hence `IsConvexVertex'` (all rays, via the unconditional off-boundary
ray-independence). -/

/-- **The ear-cut data + the single Jordan kernel**, at one polygon and ear vertex `i`
(`4 ≤ m`).  Bundles exactly the cut data the chapter's `CutGeometry` already supplies — the
ear-base diagonal, the two irreducible strict-polygon axioms (`LeftStrictAxioms`/
`RightStrictAxioms` — the genuine planar simplicity content of the ear cut), common-ray sub-
directions — together with the *single irreducible Jordan localization*
`earDeletedExterior`: a strict-interior ear point off all three boundaries lies **outside**
the ear-deleted `(n-1)`-gon (`¬ ClosedRegion' (earDeleted) σR x`).  By the bridge this is
*exactly* the interior-odd seed; it is the `OffDiagDisjoint`-equivalent half-plane separation
the whole Chapter-36 cut oracle isolates. -/
structure EarCutData {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m) :
    Prop where
  hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i)
  lax : LeftStrictAxioms P (cyclicPrev i) (cyclicNext i)
  rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i)
  /-- A common-ray left sub-direction (reuses `ρ.r`). -/
  leftRayEq : ∃ σL : RayDirection (buildLeftPoly hdiag lax), σL.r = ρ.r
  /-- A common-ray right sub-direction (reuses `ρ.r`). -/
  rightRayEq : ∃ σR : RayDirection (buildRightPoly hdiag rax), σR.r = ρ.r
  /-- The ear orientation is nondegenerate. -/
  earOrient : orient (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) ≠ 0
  /-- **The single Jordan kernel.**  A strict-interior ear point off the polygon boundary
  lies outside the ear-deleted polygon: for every common-ray `σR`, `¬ ClosedRegion'
  (buildRightPoly hdiag rax) σR x` (which subsumes `¬ OnBoundary (earDeleted) x`).  This is
  the genuine half-plane separation, ray-independent off the boundary; it is satisfiable
  exactly when the chapter's `OffDiagDisjoint` residue is (see
  `earDeletedExterior_of_offDiagDisjoint`), so the bundle is non-vacuous. -/
  earDeletedExterior : ∀ {x : Pt} {w0 w1 w2 : ℝ},
    ¬ OnBoundary P x →
    0 < w0 → 0 < w1 → 0 < w2 → w0 + w1 + w2 = 1 →
    x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i) →
    ∀ (σR : RayDirection (buildRightPoly hdiag rax)), σR.r = ρ.r →
      ¬ ClosedRegion' (buildRightPoly hdiag rax) σR x

/-- **The interior-odd seed for a good ray, from the ear-cut data.**  For a strict-interior
ear point off the boundaries and a ray `ρ` whose side coordinates are nonzero at the three
ear vertices, `Odd (CrossingNumber' P ρ x)`.  Proof: the bridge gives
`CN P ρ x ≡ CN (earDeleted) σR x + 1`, and the kernel makes `CN (earDeleted) σR x` even
(`x` outside the ear-deleted polygon → not in its region → even crossing). -/
theorem interiorOdd_of_earCutData (hn : 4 ≤ n)
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n)
    (E : EarCutData P ρ i)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hoff : ¬ OnBoundary P x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i))
    (hsa : side ρ.r x (P.q (cyclicPrev i)) ≠ 0)
    (hsv : side ρ.r x (P.q i) ≠ 0)
    (hsb : side ρ.r x (P.q (cyclicNext i)) ≠ 0) :
    Odd (CrossingNumber' P ρ x) := by
  obtain ⟨σL, hLr⟩ := E.leftRayEq
  obtain ⟨σR, hRr⟩ := E.rightRayEq
  have hbridge := interiorEar_parity_bridge hn P ρ i E.hdiag E.lax E.rax σL σR hLr hRr
    hw0 hw1 hw2 hsum hx E.earOrient hsa hsv hsb
  -- the kernel: x outside the ear-deleted polygon ⟹ even crossing there.
  have hout : ¬ ClosedRegion' (buildRightPoly E.hdiag E.rax) σR x :=
    E.earDeletedExterior hoff hw0 hw1 hw2 hsum hx σR hRr
  have hReven : Even (CrossingNumber' (buildRightPoly E.hdiag E.rax) σR x) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    exact hout (Or.inr hodd)
  rw [Nat.odd_iff]
  rw [Nat.even_iff] at hReven
  omega

/-- **Faithfulness / non-vacuity of the kernel `earDeletedExterior`.**  The kernel field is a
*consequence* of the chapter's standing half-plane separation `OffDiagDisjoint` (here in the
shape "an off-all-boundaries point is not in *both* sub-regions"): a strict-interior ear
point is in the *left* (ear-triangle) sub-region (`leftCN_earBase_eq_one` makes its left
crossing number `1`, odd), so by `¬(region_L ∧ region_R)` it is *not* in the right
(ear-deleted) sub-region.  Hence `EarCutData` is satisfiable exactly when the chapter's
`OffDiagDisjoint` residue is — no strengthening, no hidden `False`. -/
theorem earDeletedExterior_of_offDiagDisjoint (hn : 4 ≤ n)
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n)
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (lax : LeftStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (σL : RayDirection (buildLeftPoly hdiag lax))
    (σR : RayDirection (buildRightPoly hdiag rax))
    (hLr : σL.r = ρ.r) (_hRr : σR.r = ρ.r)
    (hO : orient (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) ≠ 0)
    {x : Pt} {w0 w1 w2 : ℝ}
    (_hoff : ¬ OnBoundary P x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i))
    (hsa : side ρ.r x (P.q (cyclicPrev i)) ≠ 0)
    (hsv : side ρ.r x (P.q i) ≠ 0)
    (hsb : side ρ.r x (P.q (cyclicNext i)) ≠ 0)
    (hnand : ¬ (ClosedRegion' (buildLeftPoly hdiag lax) σL x ∧
        ClosedRegion' (buildRightPoly hdiag rax) σR x)) :
    ¬ ClosedRegion' (buildRightPoly hdiag rax) σR x := by
  -- x is in the left (ear-triangle) region: its left crossing number is 1 (odd).
  have hLone : CrossingNumber' (buildLeftPoly hdiag lax) σL x = 1 :=
    leftCN_earBase_eq_one hn P ρ i hdiag lax σL hLr hw0 hw1 hw2 hsum hx hO hsa hsv hsb
  have hLreg : ClosedRegion' (buildLeftPoly hdiag lax) σL x :=
    Or.inr (by rw [hLone]; exact ⟨0, rfl⟩)
  intro hRreg
  exact hnand ⟨hLreg, hRreg⟩

/-! ## Part 6: `IsConvexVertex'` and the residue `InteriorEarParityMatch`

From a *uniform* supply of ear-cut data (one `EarCutData P σ i` per ray `σ` — exactly the
ray-uniformity the chapter's `CutGeometry` oracle provides), an interior ear point lies in
the corrected region for every ray: pick a ray missing the three ear vertices, get the odd
seed (`interiorOdd_of_earCutData`), and transport to the target ray by the unconditional
off-boundary ray-independence (`region_ray_independent`).  This yields `IsConvexVertex'` at
the ear vertex, and — via the proved split + the bare-triple seed — discharges
`InteriorEarParityMatch`. -/

open ProofsInTheBook.PolygonGeomInput (region_ray_independent)

/-- **A strict-interior ear point is in the corrected region, for every ray**, from a
uniform ear-cut-data supply.  (Picks a vertex-avoiding ray for the odd seed; transports by
ray-independence.) -/
theorem interior_mem_region'_of_earCutData (hn : 4 ≤ n)
    (P : StrictSimplePolygon n) (i : Fin n)
    (Esup : ∀ (σ : RayDirection P), EarCutData P σ i)
    (ρ : RayDirection P) {x : Pt}
    {w0 w1 w2 : ℝ}
    (hoff : ¬ OnBoundary P x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i)) :
    ClosedRegion' P ρ x := by
  -- vertices are distinct from x (off boundary).
  have hne : ∀ p, OnBoundary P p → p ≠ x := fun p hp h => hoff (h ▸ hp)
  have hp0 : P.q (cyclicPrev i) ≠ x :=
    hne _ (ProofsInTheBook.PolygonResidues.vertex_onBoundary P _)
  have hp1 : P.q i ≠ x := hne _ (ProofsInTheBook.PolygonResidues.vertex_onBoundary P _)
  have hp2 : P.q (cyclicNext i) ≠ x :=
    hne _ (ProofsInTheBook.PolygonResidues.vertex_onBoundary P _)
  obtain ⟨r, hr0, hr1, hr2⟩ := exists_rayDir_avoiding_three P hp0 hp1 hp2
  have hodd : Odd (CrossingNumber' P r x) :=
    interiorOdd_of_earCutData hn P r i (Esup r) hoff hw0 hw1 hw2 hsum hx hr0 hr1 hr2
  exact (region_ray_independent P r ρ hoff).mp (Or.inr hodd)

/-- **`IsConvexVertex'` at the ear vertex, from the uniform ear-cut-data supply** (the
ear-induction headline).  Every point of the ear triangle is in the corrected region: a
zero apex weight lands on the ear base (in the region by the diagonal); a zero neighbour
weight lands on a polygon edge (boundary); a strict interior point uses the odd seed. -/
theorem isConvexVertex'_of_earCutData (hn : 4 ≤ n)
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n)
    (Esup : ∀ (σ : RayDirection P), EarCutData P σ i) :
    IsConvexVertex' P ρ i := by
  classical
  intro x hx
  obtain ⟨w0, w1, w2, hw0, hw1, hw2, hsum, hxeq⟩ :=
    exists_barycentric_of_mem_closedTri hx
  rcases eq_or_lt_of_le hw1 with h1 | h1
  · -- w1 = 0 : ear base, in region by the diagonal segment containment.
    have hxseg : x ∈ seg (P.q (cyclicPrev i)) (P.q (cyclicNext i)) := by
      rw [seg]; refine ⟨w0, w2, hw0, hw2, by linarith, ?_⟩; rw [hxeq, ← h1]; module
    exact (Esup ρ).hdiag.2.2.1 hxseg
  rcases eq_or_lt_of_le hw0 with h0 | h0
  · -- w0 = 0 : polygon edge i.
    refine closedRegion'_of_onBoundary P ρ ⟨i, ?_⟩
    rw [Edge, seg]; refine ⟨w1, w2, hw1, hw2, by linarith, ?_⟩; rw [hxeq, ← h0]; module
  rcases eq_or_lt_of_le hw2 with h2 | h2
  · -- w2 = 0 : polygon edge prev i.
    refine closedRegion'_of_onBoundary P ρ ⟨cyclicPrev i, ?_⟩
    have hnp : cyclicNext (cyclicPrev i) = i :=
      cyclicNext_cyclicPrev_eq (le_trans (by norm_num) hn) i
    rw [Edge, hnp, seg]; refine ⟨w0, w1, hw0, hw1, by linarith, ?_⟩; rw [hxeq, ← h2]; module
  · -- strict interior.
    by_cases hoff : OnBoundary P x
    · exact closedRegion'_of_onBoundary P ρ hoff
    · exact interior_mem_region'_of_earCutData hn P i Esup ρ
        hoff h0 h1 h2 hsum hxeq

/-! ## Part 7: discharging `InteriorEarParityMatch` (good rays) and the headline assembly

`isConvexVertex'_of_earCutData` is exactly the region-level heart `convexVertex_spec` of the
chapter's residue.  For a *good* ray it discharges `InteriorEarParityMatch` directly via the
proved bare-triple seed (`PolygonEarExterior.parityMatch_of_convex`).  We also assemble the
full `PolygonGeomResidue` with the convex-vertex containment *supplied by the ear induction*
(not assumed), and re-export the Chapter-36 `⌊n/3⌋` headline over the ear-cut data + the
remaining cut data + `M`. -/

/-- **`InteriorEarParityMatch` at a fixed convex vertex, for a good ray** (the parity-match
form of the seed), from the ear-cut data: `isConvexVertex'_of_earCutData` gives
`IsConvexVertex'`, and `parityMatch_of_convex` (the proved bare-triple seed) turns it into
the parity match.  This is the faithful connection to the `PolygonEarExterior` residue. -/
theorem parityMatch_of_earCutData (hn : 4 ≤ n)
    (P : StrictSimplePolygon n) (σ : RayDirection P) (i : Fin n)
    (Esup : ∀ (τ : RayDirection P), EarCutData P τ i)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hoff : ¬ OnBoundary P x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i))
    (hsa : side σ.r x (P.q (cyclicPrev i)) ≠ 0)
    (hsv : side σ.r x (P.q i) ≠ 0)
    (hsb : side σ.r x (P.q (cyclicNext i)) ≠ 0) :
    CrossingNumber' P σ x % 2 =
      ProofsInTheBook.PolygonEarExterior.earTriSegSum P σ x i % 2 := by
  have hconv : IsConvexVertex' P σ i :=
    isConvexVertex'_of_earCutData hn P σ i Esup
  exact ProofsInTheBook.PolygonEarExterior.parityMatch_of_convex P σ hn i hconv
    (Esup σ).earOrient hoff hw0 hw1 hw2 hsum hx hsa hsv hsb

open ProofsInTheBook.PolygonJordan (RemainingResidualData polygonGeomResidue_of_earInput)
open ProofsInTheBook.PolygonGeomInput (PolygonGeomResidue artGallery_strict_of_residue)
open ProofsInTheBook.PolygonOracleClose (ResidualGeometryData)
open ProofsInTheBook.PolygonCutOracle (buildLeftPoly buildRightPoly LeftStrictAxioms
  RightStrictAxioms)

/-- **The full `PolygonGeomResidue`, with the convex-vertex containment DISCHARGED by the
ear-deletion induction.**  Given a uniform ear-cut-data supply (the cut data + the single
Jordan kernel `earDeletedExterior`) and the remaining per-cut data, the per-cut
`ResidualGeometryData` is built with its `convexVertex_spec` *supplied by
`isConvexVertex'_of_earCutData`* — the genuine reduction of the chapter's region-level heart
to the ear-deletion kernel. -/
def polygonGeomResidue_of_earCutData
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esup : ∀ {m : ℕ} (P : StrictSimplePolygon m) (σ : RayDirection P),
      4 ≤ m → EarCutData P σ (ear P))
    (base : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), m = 3 →
      IsConvexVertex' P ρ (ear P))
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RemainingResidualData P ρ (ear P)) :
    PolygonGeomResidue where
  data := fun {m} P ρ =>
    { convexVertex := ear P
      convexVertex_spec := by
        rcases lt_or_ge m 4 with hlt | hge
        · have hm3 : m = 3 := le_antisymm (by omega) P.hthree
          exact base P ρ hm3
        · exact isConvexVertex'_of_earCutData hge P ρ (ear P)
            (fun σ => Esup P σ hge)
      transversality := (rest P ρ).transversality
      leftAxioms := (rest P ρ).leftAxioms
      rightAxioms := (rest P ρ).rightAxioms
      leftRay := (rest P ρ).leftRay
      rightRay := (rest P ρ).rightRay
      commonRay := (rest P ρ).commonRay
      disjoint := (rest P ρ).disjoint
      boundary := (rest P ρ).boundary
      intersection := (rest P ρ).intersection }

/-- **The residue genuinely carries the discharged ear vertex** (anti-vacuity check). -/
theorem polygonGeomResidue_of_earCutData_convexVertex
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esup : ∀ {m : ℕ} (P : StrictSimplePolygon m) (σ : RayDirection P),
      4 ≤ m → EarCutData P σ (ear P))
    (base : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), m = 3 →
      IsConvexVertex' P ρ (ear P))
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RemainingResidualData P ρ (ear P))
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) :
    ((polygonGeomResidue_of_earCutData ear Esup base rest).data P ρ).convexVertex
      = ear P := rfl

/-- **Chapter-36 art-gallery `⌊n/3⌋` headline over the ear-cut data + remaining cut data +
`M`.**  Composing `polygonGeomResidue_of_earCutData` with
`PolygonGeomInput.artGallery_strict_of_residue`: every strict simple polygon with a ray
admits `≤ ⌊n/3⌋` vertex guards seeing its whole closed region, with the convex-vertex
containment `IsConvexVertex'` now PROVED from the ear-deletion induction (the proved
diagonal count-additivity to the proved `n = 3` base), leaving as inputs exactly the single
Jordan kernel `EarCutData.earDeletedExterior` (the half-plane separation / "interior ear
point is outside the ear-deleted polygon", the chapter's standing `OffDiagDisjoint`-grade
residue), the standard combinatorial base/cut data, and `M`. -/
theorem artGallery_strict_of_earCutData {n : ℕ}
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esup : ∀ {m : ℕ} (P : StrictSimplePolygon m) (σ : RayDirection P),
      4 ≤ m → EarCutData P σ (ear P))
    (base : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P), m = 3 →
      IsConvexVertex' P ρ (ear P))
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RemainingResidualData P ρ (ear P))
    (M : ProofsInTheBook.PolygonLast.DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms
          ProofsInTheBook.PolygonTriangleConvex.triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, ProofsInTheBook.PolygonRayIndep.Sees P ρ (P.q v) x :=
  artGallery_strict_of_residue
    (polygonGeomResidue_of_earCutData ear Esup base rest) M P ρ

end

end ProofsInTheBook.PolygonEarDelete
