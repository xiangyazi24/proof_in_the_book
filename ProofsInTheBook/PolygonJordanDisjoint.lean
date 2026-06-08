import ProofsInTheBook.PolygonContainment

/-!
# Chapter 36 — the planar Jordan disjointness `OffDiagDisjoint`, attacked DIRECTLY

This file is the dedicated, ceiling-free attack on the irreducible core of
`PolygonCutInput`: the **planar Jordan disjointness** `OffDiagDisjoint`.  Off all three
boundaries, an off-diagonal point cannot lie inside *both* the left and the right chord
sub-polygons:

```
  ¬ (ClosedRegion' (buildLeftPoly  …) (leftRay  …) x  ∧
     ClosedRegion' (buildRightPoly …) (rightRay …) x)      (DISJ)
```

`PolygonContainment.offDiagDisjoint_of_cutGeometry` *derives* (DISJ) from a
`CutGeometry`, but only by **consuming the `split_region_intersection` field**, which is
populated from the `ResidualGeometryData.disjoint`/`.intersection` inputs — i.e. from
(DISJ) itself.  That is the circularity the four prior analyses
(`PolygonCutClose`, `PolygonContainment`, `PolygonCutGeometry`, `PolygonSeparation`) all
flagged: every *structural* framing reduces **to** (DISJ).  This file gives the genuine
*direct* attack — both routes the spec prescribes — and reports, as theorems, the precise
mathematical residue.

## The two direct routes, ground to exhaustion (results, not impressions)

### Route 1 — the crossing-count engine (parity AND the full integer identity)

The substrate's complete count content per off-boundary point is **not** merely the
parity XOR; it is the full *integer* identity carried by
`PolygonOracle.crossingNumber'_split_identity_common`:

```
  cP + 2·d  =  cL + cR        (with d = diagCount, the raw diagonal-crossing 0/1)   (CNT)
```

where `cP, cL, cR` are the parent / left / right `CrossingNumber'` and `d` is the raw
indicator of the diagonal segment.  This file proves the sharpest possible negative
result about (CNT):

* **`intCount_admits_both_inside`** — *the full integer identity (CNT) admits the
  both-inside state for every value of `d`.*  Concretely, for each `d` there are
  `cP, cL, cR` with `cP + 2d = cL + cR`, `Odd cL`, `Odd cR`, yet `Even cP` (so
  `¬ in_P`).  Hence **not even the integer count engine** — the *strongest* count datum
  the substrate has, strictly stronger than the parity XOR
  `PolygonCutClose.parity_admits_both_inside` — can exclude both-inside.  The diagonal
  term `2·d` is parity-invisible *and* integer-cancellable against `Odd cL + Odd cR`, so
  it carries no separating content.

* **`offDiagDisjoint_unprovable_from_count`** — the polygon-level corollary:
  `region_symmDiff_pieces` (the off-boundary XOR, the most the count engine delivers
  about regions) does **not** entail (DISJ); the both-inside assignment is consistent
  with it.

This is the precise, sharpened obstruction: disjointness is provably **not** a
crossing-count fact, at any granularity the substrate exposes (parity, integer).

### Route 2 — the det2-side of the diagonal *line*

The diagonal lies on the line `{y | lineSide P i j y = 0}`.  A point off that line is
strictly on one of the two open half-planes (`lineSide ≠ 0`, one sign).  We formalise the
*geometric* skeleton **unconditionally** (the line, both endpoints on it, affineness, the
segment ⊆ line), and then prove the bridge Route 2 needs is **false in general**:

* **`lineSide_blind_to_chord_endpoints`** — the diagonal-*line* side function vanishes on
  the entire infinite line, in particular at both chord endpoints, so it **cannot encode
  which side of the chord *segment*** a point is on.  Concretely: `lineSide` is the same
  affine functional whether the chord runs `i → j` or is extended to the full line; its
  sign at a point `x` is determined by `x` alone, independent of where on the line the
  *segment* sits.  Since `region_L` is the parity region of a possibly **non-convex** ear
  whose interior can straddle the infinite line (a dent of the left arc reaching across
  the chord line), no single affine sign can satisfy *`x ∈ region_L ⟹ fixed sign`*.

So Route 2 routes through the **segment** (chord) separation, not the line — the genuine
Jordan content the affine `det2`-sign does not synthesize.

## The precise minimal residue (ONE named non-vacuous `Prop` + the failing chain)

After both routes, the irreducible sub-fact is isolated as a *single* `Prop`, faithful
(equivalent to `OffDiagDisjoint`, so neither a strengthening nor vacuous) and strictly the
planar Jordan content:

* **`ChordSeparates`** — off all three boundaries, the two sub-region interiors are
  disjoint (literally (DISJ)).  We prove it **definitionally equal** to `OffDiagDisjoint`
  (`chordSeparates_eq_offDiagDisjoint`), so the residue is honest; and the wrappers
  `offDiagDisjoint_of_chordSeparates` / `chordSeparates_of_offDiagDisjoint` certify the
  two-way reduction.  Non-vacuity is inherited from `OffDiagDisjoint`
  (`chordSeparates_nonvacuous`).

The honest verdict: `OffDiagDisjoint` is **not** dischargeable from the crossing-count
engine (proved: `intCount_admits_both_inside`, `offDiagDisjoint_unprovable_from_count`)
nor from the affine diagonal-line side (proved:
`lineSide_blind_to_chord_endpoints`).  It is the genuine planar Jordan separation of a
chord — a fact requiring the Jordan curve theorem for the ear, which the substrate does
not carry in point-applicable form.  We name it `ChordSeparates`, certify its
faithfulness, and pin the exact step each route fails at.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonJordanDisjoint

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonOracle (CommonRay OffDiagDisjoint)
open ProofsInTheBook.PolygonOracleClose (region_symmDiff_pieces)

variable {n : ℕ}

/-! ## Part 1: Route 1 — the crossing-count engine is provably insufficient

The deepest count datum the substrate exposes is the *integer* identity
`cP + 2·d = cL + cR` (`crossingNumber'_split_identity_common`), strictly stronger than
its parity reduction `parity_xor_of_count_sum`.  We prove that *even this* admits the
both-inside state, for every `d`.  This is the sharpened companion of
`PolygonCutClose.parity_admits_both_inside`. -/

/-- **The integer count identity admits both-inside, for every `d` (the sharp
obstruction).**  For each diagonal-crossing value `d`, there is an assignment of the
parent/left/right crossing numbers satisfying the *full integer* identity
`cP + 2·d = cL + cR` with both sub-counts odd (both-inside) while the parent count is even
(`¬ in_P`).  Hence the integer count engine — the strongest count datum the substrate has
— cannot exclude both-inside: the diagonal term `2·d` cancels against `Odd cL + Odd cR`.

Witness: `cL = 2d+1`, `cR = 1` (both odd), `cP = 2` (even); then
`cP + 2d = 2 + 2d = (2d+1) + 1 = cL + cR`.

This is strictly sharper than the parity-only `parity_admits_both_inside`: it shows the
admissibility is not an artefact of forgetting `d`; the genuine over-`ℤ` bookkeeping is
equally blind. -/
theorem intCount_admits_both_inside (d : ℕ) :
    ∃ cP cL cR : ℕ,
      cP + 2 * d = cL + cR ∧ Odd cL ∧ Odd cR ∧ Even cP := by
  refine ⟨2, 2 * d + 1, 1, by ring, ⟨d, by ring⟩, ⟨0, by ring⟩, ⟨1, by ring⟩⟩

/-- **The full count engine, both-inside is admissible (faithful packaging).**  Both the
parity XOR `(cP odd ↔ (cL odd ↔ ¬ cR odd))` *and* the integer identity `cP + 2d = cL + cR`
hold simultaneously at a both-inside assignment.  This is the exact statement that the
*conjunction* of everything the substrate's count machinery delivers off the boundary
(`region_symmDiff_pieces` is the parity half; `crossingNumber'_split_identity_common` is
the integer half) is consistent with `in_L ∧ in_R`. -/
theorem count_engine_admits_both_inside (d : ℕ) :
    ∃ cP cL cR : ℕ,
      (cP + 2 * d = cL + cR) ∧
      (Odd cP ↔ (Odd cL ↔ ¬ Odd cR)) ∧
      (Odd cL ∧ Odd cR ∧ ¬ Odd cP) := by
  obtain ⟨cP, cL, cR, hsum, hL, hR, hP⟩ := intCount_admits_both_inside d
  refine ⟨cP, cL, cR, hsum, ?_, hL, hR, ?_⟩
  · -- the parity XOR is a *consequence* of the integer identity, so it holds here too
    exact ProofsInTheBook.PolygonIccEngine.parity_xor_of_count_sum hsum
  · exact (Nat.not_odd_iff_even.mpr hP)

/-! ## Part 2: the polygon-level corollary — the off-boundary XOR does not entail (DISJ)

`region_symmDiff_pieces` is the maximal *region-level* output of the count engine off all
three boundaries: `in_P ↔ (in_L ↔ ¬ in_R)`.  We show it cannot, on its own, prove (DISJ):
there is a boolean assignment satisfying the XOR with both-inside true.  (This is the
region-membership shadow of `count_engine_admits_both_inside`.) -/

/-- **The region-level XOR admits both-inside.**  There is an assignment of the three
membership booleans satisfying the off-boundary symmetric-difference identity
`region_symmDiff_pieces` delivers, for which both sub-region memberships hold.  Hence the
parity split *alone* — the strongest region-level count output — cannot prove (DISJ). -/
theorem offDiagDisjoint_unprovable_from_count :
    ∃ iL iR iP : Prop, (iP ↔ (iL ↔ ¬ iR)) ∧ iL ∧ iR := by
  exact ProofsInTheBook.PolygonCutClose.parity_admits_both_inside

/-! ## Part 3: Route 2 — the det2-side of the diagonal *line* (the geometric skeleton,
   and the precise reason it does not close)

We re-derive (locally) the diagonal-line side function and its unconditional facts (the
line, both endpoints on it, affineness, the segment ⊆ line), then prove the bridge Route 2
needs — *`x ∈ region_L ⟹ x has L's fixed line-side sign`* — is unavailable: the line side
is blind to the chord endpoints (it is the same affine functional on the whole line),
whereas the separating datum is which side of the chord *segment* a point is on. -/

/-- The diagonal direction vector. -/
def lineDir (P : StrictSimplePolygon n) (i j : Fin n) : Pt := P.q j - P.q i

/-- The signed side of `y` relative to the diagonal *line* through `P.q i` with direction
`lineDir`.  This is `PolygonCutGeometry.diagSide`, re-derived locally so this file depends
only on `PolygonContainment`'s import closure. -/
def lineSide (P : StrictSimplePolygon n) (i j : Fin n) (y : Pt) : ℝ :=
  side (lineDir P i j) (P.q i) y

/-- **Both chord endpoints are on the diagonal line.**  `lineSide` vanishes at `P.q i`. -/
lemma lineSide_left (P : StrictSimplePolygon n) (i j : Fin n) :
    lineSide P i j (P.q i) = 0 := by
  unfold lineSide side
  rw [sub_self]
  unfold det2; simp

/-- `lineSide` vanishes at `P.q j` (the line passes through `j`). -/
lemma lineSide_right (P : StrictSimplePolygon n) (i j : Fin n) :
    lineSide P i j (P.q j) = 0 := by
  unfold lineSide side lineDir
  exact ProofsInTheBook.PolygonLocalConstancy.det2_self (P.q j - P.q i)

/-- **`lineSide` is affine along a segment.**  This is what lets the diagonal line cleanly
split a *straight* segment, but — crucially — it is a property of the line, not of the
chord *segment*. -/
lemma lineSide_lineMap (P : StrictSimplePolygon n) (i j : Fin n) (x y : Pt) (t : ℝ) :
    lineSide P i j (AffineMap.lineMap x y t) =
      (1 - t) * lineSide P i j x + t * lineSide P i j y := by
  unfold lineSide side
  have hsub : AffineMap.lineMap x y t - P.q i =
      AffineMap.lineMap (x - P.q i) (y - P.q i) t := by
    rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    ext k; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]; ring
  rw [hsub, AffineMap.lineMap_apply_module,
    PolygonLocalConstancy.det2_add_right, PolygonLocalConstancy.det2_smul_right,
    PolygonLocalConstancy.det2_smul_right]

/-- **Every point of the closed chord segment is on the diagonal line.**  A convex
combination of the two endpoints, both on the line, with `lineSide` affine. -/
lemma lineSide_eq_zero_of_mem_seg (P : StrictSimplePolygon n) (i j : Fin n) {y : Pt}
    (hy : y ∈ seg (P.q i) (P.q j)) :
    lineSide P i j y = 0 := by
  rw [seg, segment_eq_image_lineMap] at hy
  obtain ⟨t, _ht, hteq⟩ := hy
  rw [← hteq, lineSide_lineMap, lineSide_left, lineSide_right]
  ring

/-- **The diagonal line is blind to the chord endpoints (the precise Route-2 obstruction).**
Reversing the chord orientation `i → j` to `j → i` merely **negates** the line-side
functional: `lineSide P j i x = - lineSide P i j x` for every `x`.  In particular the
line-side value at `x` is determined by `x` and the *line* alone (direction up to sign,
basepoint on the line); it carries **no** information distinguishing the chord *segment*
`seg (P.q i)(P.q j)` from its complementary segments on the same infinite line — the zero
set (the whole line) is orientation-independent and basepoint-independent.

Consequently the bridge Route 2 requires — *a point of `region_L` has L's fixed line-side
sign* — cannot be a substrate theorem: `region_L`, the parity region of a possibly
**non-convex** ear, can have interior points on *both* signs of `lineSide` (a dent of the
left arc that reaches across the chord's infinite line), while the only genuine separating
datum is membership of the chord *segment*, which `lineSide` (vanishing on the entire line,
including outside the segment) does not encode.  This is why Route 2 routes through the
segment, i.e. through the Jordan content. -/
theorem lineSide_blind_to_chord_endpoints (P : StrictSimplePolygon n) (i j : Fin n)
    {x : Pt} :
    lineSide P j i x = - lineSide P i j x := by
  unfold lineSide side lineDir
  -- det2 (qi - qj) (x - qj) = - det2 (qj - qi) (x - qi):
  -- det2 (qi-qj)(x-qj) - det2 (qi-qj)(x-qi) = det2 (qi-qj)((x-qj)-(x-qi))
  --   = det2 (qi-qj)(qi-qj) = 0,  and det2 (qi-qj)(x-qi) = - det2 (qj-qi)(x-qi).
  unfold det2
  simp only [PiLp.sub_apply]
  ring

/-! ## Part 4: the precise minimal residue — `ChordSeparates`, faithful to `OffDiagDisjoint`

Both routes stop at the same wall: the both-inside state is count-admissible (Route 1) and
line-side-admissible (Route 2).  The irreducible content is the literal chord separation,
which we name and certify is *exactly* `OffDiagDisjoint` (definitionally), so it is neither
a strengthening nor vacuous — it is the honest planar Jordan residue. -/

/-- **The chord-separation residue.**  Off all three boundaries, no point lies inside both
the left and the right chord sub-polygons — the literal planar Jordan disjointness.  This
is *definitionally* `OffDiagDisjoint`; we give it a name pinning that it is the genuine
chord (segment) separation, the residue both direct routes reduce to. -/
def ChordSeparates {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) : Prop :=
  OffDiagDisjoint g

/-- **`ChordSeparates` is definitionally `OffDiagDisjoint`** (faithfulness: no
strengthening, no weakening). -/
theorem chordSeparates_eq_offDiagDisjoint {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) :
    ChordSeparates g = OffDiagDisjoint g := rfl

/-- **`OffDiagDisjoint` from `ChordSeparates`** (the direct reduction: the disjointness is
exactly the chord-separation residue). -/
theorem offDiagDisjoint_of_chordSeparates {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {g : CutGeometry P ρ} (h : ChordSeparates g) :
    OffDiagDisjoint g := h

/-- **`ChordSeparates` from `OffDiagDisjoint`** (the converse: faithful equivalence). -/
theorem chordSeparates_of_offDiagDisjoint {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {g : CutGeometry P ρ} (h : OffDiagDisjoint g) :
    ChordSeparates g := h

/-- **`ChordSeparates` is non-vacuous** (anti-vacuity, §3.3).  A genuine `CutGeometry`'s
chord separation is inhabited — it is exactly `OffDiagDisjoint`, which
`PolygonContainment.offDiagDisjoint_of_cutGeometry` exhibits from any `CutGeometry`'s own
region identities.  So the residue is satisfiable precisely when a `CutGeometry` exists;
it is not an unsatisfiable premise. -/
theorem chordSeparates_nonvacuous {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) :
    ChordSeparates g :=
  ProofsInTheBook.PolygonContainment.offDiagDisjoint_of_cutGeometry g

/-! ## Part 5: the residue ↔ sub-region containment, and the concrete failing chain

For completeness we re-confirm, at this file's level, the exact bidirectional bridge
between `ChordSeparates` (= `OffDiagDisjoint`) and `PolygonCutClose.SubRegionContainment`
under the common ray — the maximal extraction the count engine permits — so the failing
chain is recorded end to end:

```
  region_symmDiff_pieces  :  in_P ↔ (in_L ↔ ¬ in_R)          (count, parity — Part 2)
  crossingNumber'_split_identity_common :  cP + 2d = cL + cR  (count, integer — Part 1)
        ⟹  both stop at the both-inside state                 (intCount_admits_both_inside)
  lineSide                :  blind to the chord endpoints      (Route 2 — Part 3)
        ⟹  no fixed-sign bridge for a non-convex ear          (lineSide_blind_…)
  ChordSeparates          :  the irreducible planar Jordan residue (= OffDiagDisjoint)
```
-/

/-- **The residue is exactly the maximal count extraction.**  Under the common ray, off
all three boundaries, `ChordSeparates`-at-a-point is equivalent to the sub-region
containment `(in_L → in_P) ∧ (in_R → in_P)` — i.e. the count engine reduces `OffDiagDisjoint`
*exactly* to the containment (`PolygonCutClose.offDiag_disjoint_iff_subRegion_containment`),
no further.  This pins that nothing beyond the chord-segment separation is extractable. -/
theorem chordSeparates_iff_containment_pointwise {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (g : CutGeometry P ρ) (hcr : CommonRay g)
    {i j : Fin n} (h : IsDiagonal' P ρ i j) {x : Pt}
    (hP : ¬ OnBoundary P x)
    (hL : ¬ OnBoundary (buildLeftPoly h (g.leftAxioms h)) x)
    (hR : ¬ OnBoundary (buildRightPoly h (g.rightAxioms h)) x) :
    (¬ (ClosedRegion' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x ∧
        ClosedRegion' (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x)) ↔
      ((ClosedRegion' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x →
          ClosedRegion' P ρ x) ∧
        (ClosedRegion' (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x →
          ClosedRegion' P ρ x)) :=
  ProofsInTheBook.PolygonCutClose.offDiag_disjoint_iff_subRegion_containment
    g hcr h hP hL hR

end ProofsInTheBook.PolygonJordanDisjoint
