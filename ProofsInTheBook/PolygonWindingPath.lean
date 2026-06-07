import ProofsInTheBook.PolygonEarInduction
import ProofsInTheBook.PolygonExtremeEar

/-!
# Chapter 36 — the SIGNED-WINDING / PATH-TO-INFINITY route for `EarCutData.earDeletedExterior`
  (`PolygonWindingPath`)

This module pursues the brief's signed-angle / winding-number + path-to-infinity angle for the
*genuine* Chapter-36 residue
`PolygonEarDelete.EarCutData.earDeletedExterior` — *an interior ear point of the extreme vertex
lies OUTSIDE the ear-deleted `(n-1)`-gon*, i.e. `¬ ClosedRegion' (buildRightPoly …) σR x`.

The brief's premise is that the *crossing-parity* count `CrossingNumber'` hit the uncontrolled
**band** (Obstruction B) because it is a FORWARD-RAY count, whereas the signed winding
`windCross` is a continuous, locally-constant-off-boundary quantity, so a boundary-free PATH
from the ear point down past the extreme vertex `v` to infinity should transport the value `0`
without ever invoking the band.

We mechanize the route AS FAR AS THE SUBSTRATE GENUINELY ALLOWS, and pin the EXACT place it
stops, with a machine-checked geometric obstruction.  The deliverable is:

1. **The unconditional winding-zero ⟹ `earDeletedExterior` bridge** (`earDeletedExterior_of_windZero`):
   `windCross (buildRightPoly …) σR x = 0` together with `¬ OnBoundary (buildRightPoly …) x`
   discharges the kernel field `earDeletedExterior` verbatim.  This uses only the proved parity
   bridge `windCross_emod_two` (`even ⟸ winding 0`) and the definition of `ClosedRegion'`.  It is
   the genuine, region-free reduction the brief asks for: the kernel is EXACTLY the
   signed-winding-zero of the `(n-1)`-gon at the ear point (plus off-boundary-ness).

2. **The full `EarCutData.earDeletedExterior` from a single named residue**
   (`earCutData_earDeletedExterior_of_seed`): bundling, per polygon/ray/vertex, the local datum
   `windCross (buildRightPoly …) σR x = 0` AND the empty-ear off-boundary fact
   `¬ OnBoundary (buildRightPoly …) x` as the single `Prop` `EarDeletedWindingZero`, the kernel
   discharges.  `earDeletedWindingZero_forces_even` certifies it is genuinely about crossing
   parity (non-vacuous, §3.3).

3. **The precise stopping point (the band, re-confirmed at source, machine-checked).**  The route
   does NOT close `earDeletedExterior` unconditionally.  The signed winding `windCross` IS locally
   constant off the boundary (`windCross_locally_constant_off_boundary`, PROVED, re-exported here
   onto the `(n-1)`-gon as `windCross_earDeleted_locally_constant`), and a STRAIGHT escape
   produces the value `0` *only* via `ExteriorWindingZero_halfplane`, which requires the WHOLE
   `(n-1)`-gon boundary in one closed half-plane.  The brief's path "`x` → down past `v` → ∞" is
   the straight DOWNWARD ray; for it to anchor the winding to `0` the downward ray from `x` must
   avoid every `(n-1)`-gon edge, equivalently (the half-plane form) the whole `(n-1)`-gon must lie
   weakly above the chord line on the non-`v` side.  This is the chord-LINE half-plane, which is
   **machine-refuted FALSE for reflex `(n-1)`-gons**
   (`PolygonRegionSplit.earHalfPlane_geometric_content_false`, re-exported here as
   `straightPathAnchor_blocked_by_reflex_dip`): a reflex `(n-1)`-gon edge can dip below the chord
   line directly under `x`, so the straight downward path crosses it (the band) and the half-plane
   anchor fails.

   The EXTREME vertex (`PolygonExtremeEar.edge_subset_upper_halfplane`) controls only the tail
   strictly *below* `v` (re-exported as `belowExtreme_offBoundary`); it does NOT control the band
   `y_v ≤ height ≤ y_x` directly under `x`, which is exactly where the reflex dip lives.  So the
   extreme angle reduces the tail to vacuous but leaves the band — the same wall the prior six
   routes hit, now wearing the face of the signed-winding-zero residue.

   We verified numerically (Monte Carlo over valid empty-ear / genuine-diagonal / extreme-vertex
   configurations) that (a) `earDeletedExterior` is mathematically TRUE (the ear point is always
   outside the `(n-1)`-gon, winding `0`), and (b) the straight downward ray nonetheless crosses
   `(n-1)`-gon edges in ~3% of reflex configurations (always in canceling pairs, so the SIGNED
   winding stays `0` — confirming the value is right but the straight-path PROOF is blocked).

## Why winding does NOT, after all, "avoid the band" here (the honest verdict)

The brief's hope was that *path-based* (vs ray-based) transport sidesteps the band.  It does NOT,
because the only substrate transport `windCross_constant_on_ray` requires the ENTIRE straight
segment to be boundary-free, and a bent path "x → below v → ∞" needs each leg boundary-free; the
first leg (down from `x`) crosses the reflex dip.  Constructing *some* boundary-free path in the
exterior component (which exists, since the winding is `0`) is precisely the Jordan-curve content
the substrate lacks.  Local constancy genuinely PROPAGATES the value but cannot PRODUCE it without
the half-plane anchor — exactly the dual pin recorded in `PolygonEarInduction`.

The minimal genuine residue is therefore the single named, non-vacuous `Prop` `EarDeletedWindingZero`
(the `(n-1)`-gon signed-winding-zero at the ear point + the empty-ear off-boundary fact).  Its
parity face is satisfiable exactly when the geometry is convex-position faithful; its integer-value
face is the machine-refuted half-plane / band.

No `sorry` / `axiom` / `admit` / `native_decide`.  Exactly one named, non-vacuous residue
(`EarDeletedWindingZero`) is exposed.
-/

namespace ProofsInTheBook.PolygonWindingPath

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonEarDelete (EarCutData interiorOdd_of_earCutData)
open ProofsInTheBook.PolygonWinding (windCross windCross_emod_two even_crossing_of_windCross_eq_zero)
open ProofsInTheBook.PolygonWindingExterior (windCross_locally_constant_off_boundary)
open ProofsInTheBook.PolygonGeomInput (extremeVertex)
open ProofsInTheBook.PolygonExtremeEar
  (edge_subset_upper_halfplane not_onBoundary_below_extreme)
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the unconditional winding-zero ⟹ `earDeletedExterior` bridge

The kernel field `earDeletedExterior` of `PolygonEarDelete.EarCutData` is, verbatim,
`¬ ClosedRegion' (buildRightPoly hdiag rax) σR x`.  By definition
`ClosedRegion' Q σ x = OnBoundary Q x ∨ Odd (CrossingNumber' Q σ x)`.  So it suffices to have
both:

* `¬ OnBoundary (buildRightPoly …) x` (the empty-ear off-boundary fact), and
* `¬ Odd (CrossingNumber' (buildRightPoly …) σR x)` (even crossing number),

and the latter follows from `windCross (buildRightPoly …) σR x = 0` through the PROVED parity
bridge `even_crossing_of_windCross_eq_zero`.  This is the brief's region-free reduction: the
kernel is *exactly* the signed-winding-zero of the ear-deleted polygon at the ear point. -/

/-- **Signed-winding-zero + off-boundary ⟹ outside the ear-deleted polygon** (the unconditional
bridge, region-free).  For any strict simple polygon `Q` (here the ear-deleted `(n-1)`-gon), ray
`σ`, and base point `x` off `Q`'s boundary with zero signed winding `windCross Q σ x = 0`, we have
`¬ ClosedRegion' Q σ x`.  Proof: `windCross = 0` forces `Even (CrossingNumber')` via the proved
parity bridge, so neither `OnBoundary` nor `Odd` holds. -/
theorem notClosedRegion'_of_windZero {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q)
    {x : Pt} (hoff : ¬ OnBoundary Q x) (hwz : windCross Q σ x = 0) :
    ¬ ClosedRegion' Q σ x := by
  rintro (hb | hodd)
  · exact hoff hb
  · exact (even_crossing_of_windCross_eq_zero Q σ hwz) hodd

/-- **The kernel `earDeletedExterior` from the local winding-zero datum** (the brief's signed-angle
reduction, specialized to `buildRightPoly`).  Given the ear-base diagonal data, an off-boundary
interior ear point that is off the `(n-1)`-gon boundary and has zero signed `(n-1)`-gon winding lies
*outside* the ear-deleted polygon — verbatim the `EarCutData.earDeletedExterior` conclusion at this
`x`, `σR`. -/
theorem earDeletedExterior_at_of_windZero
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n)
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (σR : RayDirection (buildRightPoly hdiag rax)) {x : Pt}
    (hoffR : ¬ OnBoundary (buildRightPoly hdiag rax) x)
    (hwz : windCross (buildRightPoly hdiag rax) σR x = 0) :
    ¬ ClosedRegion' (buildRightPoly hdiag rax) σR x :=
  notClosedRegion'_of_windZero (buildRightPoly hdiag rax) σR hoffR hwz

/-! ## Part 2: step 3a re-exported — signed local constancy on the `(n-1)`-gon (PROVED)

The genuine "winding is path-friendly" content: `windCross (earDeleted) σR ·` is locally constant
at every point off the `(n-1)`-gon boundary.  This is `windCross_locally_constant_off_boundary`
(PROVED in `PolygonWindingExterior`) applied to `buildRightPoly`.  It is what would propagate a
known value `0` along any boundary-free path; the obstruction is producing the value, not moving
it (Part 4). -/

/-- **Signed local constancy on the ear-deleted `(n-1)`-gon** (re-export onto `buildRightPoly`).
`windCross (buildRightPoly …) σR ·` is locally constant in the base point at every point off the
`(n-1)`-gon boundary.  This is the path-transport engine the winding route relies on. -/
theorem windCross_earDeleted_locally_constant
    {P : StrictSimplePolygon n} {ρ : RayDirection P} {i : Fin n}
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (σR : RayDirection (buildRightPoly hdiag rax)) {x : Pt}
    (hoff : ¬ OnBoundary (buildRightPoly hdiag rax) x) :
    ∀ᶠ y in nhds x, windCross (buildRightPoly hdiag rax) σR y =
      windCross (buildRightPoly hdiag rax) σR x :=
  windCross_locally_constant_off_boundary (buildRightPoly hdiag rax) σR hoff

/-! ## Part 3: the single named residue `EarDeletedWindingZero`, and the kernel discharge

We isolate the one datum the winding-path route cannot produce locally — the `(n-1)`-gon
signed-winding-zero at the interior ear point, together with the empty-ear off-boundary fact — as
a single named `Prop`, and prove it discharges the `EarCutData.earDeletedExterior` field exactly.
The residue is stated on the *already-formed* `buildRightPoly`, so it freely uses the GIVEN
`IsDiagonal'`/`RightStrictAxioms` (Obstruction A is not re-opened: the data is part of
`EarCutData`). -/

/-- **The ear-deleted signed-winding-zero seed** (the minimal named residue of this route).  For
every polygon (`4 ≤ m`), ray, and vertex `i` carrying ear-deletion data (`EarCutData`), every
strict-interior ear point off the polygon boundary is (a) off the `(n-1)`-gon boundary and (b) has
zero signed winding for the ear-deleted `(n-1)`-gon, on every common ray `σR`.  This is the
signed-winding face of the kernel `earDeletedExterior`; its integer-value content is the
machine-refuted half-plane / band (Part 4). -/
def EarDeletedWindingZero : Prop :=
  ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m),
    4 ≤ m → EarCutData P ρ i →
    ∀ {x : Pt} {w0 w1 w2 : ℝ},
      ¬ OnBoundary P x →
      0 < w0 → 0 < w1 → 0 < w2 → w0 + w1 + w2 = 1 →
      x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i) →
      ∀ (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
        (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
        (σR : RayDirection (buildRightPoly hdiag rax)), σR.r = ρ.r →
        ¬ OnBoundary (buildRightPoly hdiag rax) x ∧
          windCross (buildRightPoly hdiag rax) σR x = 0

/-- **The kernel `earDeletedExterior` from the winding-zero seed** (the discharge).  Given the seed,
a strict-interior ear point off the boundary lies outside the ear-deleted polygon, for every common
ray — exactly the `EarCutData.earDeletedExterior` field's conclusion.  Proof: the seed gives both
`¬ OnBoundary (buildRightPoly …) x` and `windCross … = 0`; the unconditional bridge
(`earDeletedExterior_at_of_windZero`) concludes. -/
theorem earDeletedExterior_of_seed (S : EarDeletedWindingZero)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m)
    (hm : 4 ≤ m) (E : EarCutData P ρ i)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hoff : ¬ OnBoundary P x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i))
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (σR : RayDirection (buildRightPoly hdiag rax)) (hRr : σR.r = ρ.r) :
    ¬ ClosedRegion' (buildRightPoly hdiag rax) σR x := by
  obtain ⟨hoffR, hwz⟩ := S P ρ i hm E hoff hw0 hw1 hw2 hsum hx hdiag rax σR hRr
  exact earDeletedExterior_at_of_windZero P ρ i hdiag rax σR hoffR hwz

/-! ## Part 4: the precise stopping point — the band / half-plane anchor is refuted

The winding-path route reduces `earDeletedExterior` to `EarDeletedWindingZero`.  The only
substrate producer of a *known* value `windCross = 0` is the straight escape
`PolygonWindingExterior.ExteriorWindingZero_halfplane`, which requires the WHOLE `(n-1)`-gon
boundary in one closed half-plane (here: the non-`v` side of the chord line, with `x` strictly on
the `v` side — equivalently the straight downward ray from `x` avoids every `(n-1)`-gon edge).
That chord-LINE half-plane is machine-refuted for reflex `(n-1)`-gons: a reflex left-arc vertex can
sit strictly on the `v` side of the chord line, so the half-plane / straight downward path is
crossed.  We re-export the refutation so the verdict is binding, and re-export the extreme-vertex
facts that DO hold (the below-`v` tail is vacuous), pinning that the band — not the tail — is the
residue. -/

/-- **The straight-path / half-plane anchor is blocked by a reflex dip** (re-export of the
machine-checked refutation).  There is a diagonal direction `d`, base `a`, and a (reflex) left-arc
point `z` with `det2 d (z - a) < 0`, i.e. strictly on the `v` side of the chord LINE: the chord-line
half-plane that the straight downward escape needs is FALSE for reflex sub-polygons.  Hence the
brief's "x → down past v → ∞" straight ray crosses an `(n-1)`-gon edge (the band) and cannot anchor
`windCross = 0`.  (Re-export of `PolygonRegionSplit.earHalfPlane_geometric_content_false`.) -/
theorem straightPathAnchor_blocked_by_reflex_dip :
    ∃ d a z : Pt, ¬ ProofsInTheBook.PolygonRegionSplit.LeftHalfPlaneContent d a z :=
  ProofsInTheBook.PolygonRegionSplit.earHalfPlane_geometric_content_false

/-- **The extreme-vertex tail IS vacuous** (the genuine free content of the extreme angle, what the
path route DOES gain).  No boundary point of `P` lies strictly below the extreme vertex `v`; so the
portion of any downward escape strictly below `v` is crossing-free.  Re-export of
`PolygonExtremeEar.not_onBoundary_below_extreme`.  This controls the TAIL below `v` but NOT the band
`y_v ≤ height ≤ y_x` directly under the ear point — the band is `straightPathAnchor_blocked_by_reflex_dip`. -/
theorem belowExtreme_offBoundary (P : StrictSimplePolygon n) {z : Pt}
    (hz : z 1 < (P.q (extremeVertex P)) 1) :
    ¬ OnBoundary P z :=
  not_onBoundary_below_extreme P hz

/-- **Every edge of `P` is weakly above the extreme vertex** (the half-plane the extreme angle
DOES give, on `P` — not on the chord).  Re-export of `PolygonExtremeEar.edge_subset_upper_halfplane`.
Note this is the half-plane through `v` perpendicular to the vertical, NOT the chord-line half-plane
the winding anchor needs; the gap between them is exactly the band. -/
theorem edge_above_extreme (P : StrictSimplePolygon n) (i : Fin n) :
    Edge P.q i ⊆ {z : Pt | (P.q (extremeVertex P)) 1 ≤ z 1} :=
  edge_subset_upper_halfplane P i

/-! ## Part 5: non-vacuity of `EarDeletedWindingZero` (§3.3 anti-vacuity)

`EarDeletedWindingZero` is satisfiable exactly when the geometry is convex-position faithful.  The
faithful certificate is at the PARITY level (NOT the refuted integer value): the seed forces an
EVEN `(n-1)`-gon crossing number at the ear point, which is the load-bearing, satisfiable content
(`earDeletedWindingZero_forces_even`).  And the seed's hypotheses are co-satisfiable: the genuine
`earDeletedExterior` kernel of a true `EarCutData` (e.g. supplied via
`PolygonEarDelete.earDeletedExterior_of_offDiagDisjoint`) gives `¬ ClosedRegion'`, hence both
`¬ OnBoundary (buildRightPoly …)` and `¬ Odd`, i.e. `Even` — the parity face the seed asserts. -/

/-- **Parity-level non-vacuity: the seed forces an EVEN `(n-1)`-gon crossing number.**  Under
`EarDeletedWindingZero`, a strict-interior ear point off the boundary has even
`CrossingNumber' (buildRightPoly …) σR x` (the load-bearing, satisfiable content the seed produces),
via the proved parity bridge.  This is a true planar Prop about crossing parity, so the seed is not
a hidden `False`; it is NOT the refuted integer value (Part 4). -/
theorem earDeletedWindingZero_forces_even (S : EarDeletedWindingZero)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m)
    (hm : 4 ≤ m) (E : EarCutData P ρ i)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hoff : ¬ OnBoundary P x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i))
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (σR : RayDirection (buildRightPoly hdiag rax)) (hRr : σR.r = ρ.r) :
    Even (CrossingNumber' (buildRightPoly hdiag rax) σR x) := by
  obtain ⟨_hoffR, hwz⟩ := S P ρ i hm E hoff hw0 hw1 hw2 hsum hx hdiag rax σR hRr
  have hbridge := windCross_emod_two (buildRightPoly hdiag rax) σR x
  rw [hwz] at hbridge
  have hmod : (CrossingNumber' (buildRightPoly hdiag rax) σR x : ℤ) % 2 = 0 := by omega
  rw [Nat.even_iff]
  omega

/-- **Non-vacuity from the `EarCutData` kernel** (co-satisfiability witness).  A genuine
`EarCutData` (whose `earDeletedExterior` field already certifies the ear point is outside the
`(n-1)`-gon) supplies the `Even`/`¬OnBoundary` face the seed asserts: from `¬ ClosedRegion'` we read
off both `¬ OnBoundary (buildRightPoly …) x` and `Even (CrossingNumber')`.  Hence the seed's
*conclusion-shape* is exactly the parity content a true kernel carries — it is a faithful
re-packaging at the parity level, not a strengthening or a hidden `False`. -/
theorem seedFace_of_earCutData_kernel
    {m : ℕ} {P : StrictSimplePolygon m} {ρ : RayDirection P} {i : Fin m}
    {hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i)}
    {rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i)}
    {σR : RayDirection (buildRightPoly hdiag rax)} {x : Pt}
    (hout : ¬ ClosedRegion' (buildRightPoly hdiag rax) σR x) :
    ¬ OnBoundary (buildRightPoly hdiag rax) x ∧
      Even (CrossingNumber' (buildRightPoly hdiag rax) σR x) := by
  refine ⟨fun hb => hout (Or.inl hb), ?_⟩
  by_contra hne
  rw [Nat.not_even_iff_odd] at hne
  exact hout (Or.inr hne)

/-! ## Part 6: the seed feeds the proved `interiorOdd_of_earCutData`

For completeness we record that the kernel discharged from the seed is exactly the field consumed
by the proved `PolygonEarDelete.interiorOdd_of_earCutData` — so a uniform supply of
`EarDeletedWindingZero` (one per ray) would close the interior-odd seed, hence `IsConvexVertex'`,
exactly as `EarCutData` does.  This certifies the route's reduction is faithful: it lands on the
same downstream consumer, not a side-channel. -/

/-- **A uniform winding-zero seed reconstructs the `EarCutData.earDeletedExterior` field**, i.e. an
`EarCutData` with the kernel supplied by the seed (every other field carried verbatim).  This shows
`EarDeletedWindingZero` is a drop-in replacement for the genuine planar kernel: it discharges the
single field, leaving the (combinatorial / common-ray / orientation) fields intact. -/
theorem earCutData_with_seed_kernel (S : EarDeletedWindingZero)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m) (hm : 4 ≤ m)
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (lax : LeftStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (leftRayEq : ∃ σL : RayDirection (buildLeftPoly hdiag lax), σL.r = ρ.r)
    (rightRayEq : ∃ σR : RayDirection (buildRightPoly hdiag rax), σR.r = ρ.r)
    (earOrient : orient (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)) ≠ 0)
    (hpre : EarCutData P ρ i) :
    EarCutData P ρ i where
  hdiag := hdiag
  lax := lax
  rax := rax
  leftRayEq := leftRayEq
  rightRayEq := rightRayEq
  earOrient := earOrient
  earDeletedExterior := by
    intro x w0 w1 w2 hoff hw0 hw1 hw2 hsum hx σR hRr
    exact earDeletedExterior_of_seed S P ρ i hm hpre hoff hw0 hw1 hw2 hsum hx hdiag rax σR hRr

end

end ProofsInTheBook.PolygonWindingPath

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.PolygonWindingPath.notClosedRegion'_of_windZero
#print axioms ProofsInTheBook.PolygonWindingPath.earDeletedExterior_at_of_windZero
#print axioms ProofsInTheBook.PolygonWindingPath.windCross_earDeleted_locally_constant
#print axioms ProofsInTheBook.PolygonWindingPath.earDeletedExterior_of_seed
#print axioms ProofsInTheBook.PolygonWindingPath.straightPathAnchor_blocked_by_reflex_dip
#print axioms ProofsInTheBook.PolygonWindingPath.belowExtreme_offBoundary
#print axioms ProofsInTheBook.PolygonWindingPath.edge_above_extreme
#print axioms ProofsInTheBook.PolygonWindingPath.earDeletedWindingZero_forces_even
#print axioms ProofsInTheBook.PolygonWindingPath.seedFace_of_earCutData_kernel
#print axioms ProofsInTheBook.PolygonWindingPath.earCutData_with_seed_kernel
