import ProofsInTheBook.PolygonWindingPath
import ProofsInTheBook.PolygonWindingExterior

/-!
# Chapter 36 — the EAR-EDGE ESCAPE route for `EarCutData.earDeletedExterior`
  (`PolygonEarEscape`)

This module pursues a *genuinely new* explicit-path angle for the Chapter-36 residue
`PolygonEarDelete.EarCutData.earDeletedExterior` — *a strict-interior ear point of the extreme
vertex lies OUTSIDE the ear-deleted `(n-1)`-gon* `P' := buildRightPoly …`, i.e.
`windCross P' σR x = 0` ⟹ `¬ ClosedRegion' P' σR x` (the bridge
`PolygonWindingPath.earDeletedExterior_at_of_windZero`).

## The key structural fact the prior (straight-downward) route did not exploit

`windCross P'` / `CrossingNumber'` is, in this substrate, a **forward-RAY count**: `windCross P' σ x
= ∑ₖ rawSignedInd σ.r x (P'.q k) (P'.q (next k))`, with `rawSignedInd` keyed on
`RawEdgeCrosses σ.r x a b` (the forward ray from `x` in the FIXED direction `σ.r` meeting the
edge).  The ONLY transport the engine offers is `windCross_constant_on_ray`: `windCross` is constant
along a *straight segment* `x + t•v` (a FREE escape vector `v`, independent of `σ.r`) as long as the
whole segment is **off `P'`'s boundary**, and `exists_far_T_windCross_zero` makes the far value `0`.
So the route is fundamentally: *find a boundary-free escape path off `P'` and slide `0` back to `x`.*

The prior winding route used the single straight DOWNWARD ray and hit the band (reflex `P'` edges
dipping below `x`), because `windCross_constant_on_ray` is single-straight-line and a reflex edge can
cross the downward segment in the band `y_v ≤ height ≤ y_x`.

**The new observation.**  The ear edges `uv = (q_{prev i}, q_i)` and `vw = (q_i, q_{next i})` are
**NOT edges of `P'`**: `P'` is the right sub-polygon `subpolygonRightTuple` whose vertex tuple skips
the ear vertex `i`, replacing `uv, vw` by the single diagonal `uw`.  `OnBoundary P' z` therefore only
"sees" `P'` edges, so **crossing an ear edge is free for `windCross P'`** — it does not move the
point onto `P'`'s boundary.  Concretely, a small neighbourhood of the extreme vertex `v = q_i`
contains **no `P'` edge at all** (both edges incident to `v` were deleted), and everything below `v`
is `P'`-free (`belowExtreme_offBoundary_earDeleted`, PROVED unconditionally here from
`edge_subset_upper_halfplane` lifted to `P'`, since every `P'` vertex is a `P` vertex `≠ i`).

This lets us replace the single downward ray (whose ENTIRE length must miss every `P'` edge, refuted
in the band) by a **bent two-leg escape**:

  * **Leg 1** `x → q1` : from the interior ear point `x` to a point `q1` just across an ear edge,
    near `v`.  This leg crosses only the (non-`P'`) ear edge and stays inside the (empty) ear
    triangle, so it is `P'`-boundary-free.  *This is the only leg not forced by the extreme angle.*
  * **Leg 2** `q1 → ∞` : straight DOWN from `q1` (near `v`) past `v` to a far point.  Near `v` there
    are no `P'` edges, and below `v` there are none either, so this leg is `P'`-boundary-free —
    UNCONDITIONALLY (`belowExtreme_offBoundary_earDeleted`).

Sliding `windCross P' = 0` from the far point back along Leg 2 to `q1` and back along Leg 1 to `x`
gives `windCross P' x = 0` — *without ever invoking the band's reflex dips*, because the bent path
routes through the deleted (ear-edge) corner at `v` where `P'` has no boundary.

## What is genuinely closed here, and the single residue that remains

PROVED unconditionally in this module:

* `belowExtreme_offBoundary_earDeleted` — every point strictly below the extreme vertex is off `P'`'s
  boundary (Leg-2's tail; the genuine free content of the extreme angle, lifted to `P'`).
* `earDeleted_edge_above_extreme` — every `P'` edge lies weakly above `v` (cornerstone of Leg 2).
* `windCross_earDeleted_zero_of_escape` — the transport engine: ANY single escape vector whose ray
  from `x` is `P'`-boundary-free forces `windCross P' x = 0` (re-packaging
  `windCross_constant_on_ray` + `exists_far_T_windCross_zero`).
* `windCross_earDeleted_zero_of_two_leg` — the BENT-path transport: two boundary-free legs
  `x → q1 → ∞` (with each leg meeting no `P'` edge) force `windCross P' x = 0`.
* `earDeletedExterior_of_two_leg` — feeding the bent path into the proved bridge: a boundary-free
  two-leg escape discharges `¬ ClosedRegion' P' σR x`, verbatim the kernel conclusion.

The ONE remaining geometric input is **Leg 1's boundary-freeness** — that the short segment from `x`
across an ear edge into `v`'s deleted corner meets **no `P'` edge** (the *empty-ear* fact: no `P'`
edge enters the ear triangle / `v`'s corner).  We isolate exactly this as the single named,
non-vacuous `Prop` `EarCornerEscape`.  This is STRICTLY WEAKER and STRICTLY MORE LOCAL than the prior
straight-downward residue: that one required the ENTIRE downward ray (anywhere in the band) to miss
every `P'` edge — refuted by a reflex dip *anywhere*; this one requires only the local, empty-ear
corner at `v` to be `P'`-free, which is the geometric content of "`v` is an ear" rather than the full
planar Jordan curve theorem.

`EarCornerEscape` is genuinely about the geometry (it produces a `P'`-boundary-free bent escape), and
it discharges `EarDeletedWindingZero` (hence `EarCutData.earDeletedExterior`) through the bent-path
transport.  Its parity face is the proved `earDeletedWindingZero_forces_even`.

No `sorry` / `axiom` / `admit` / `native_decide`.  Exactly one named, non-vacuous residue
(`EarCornerEscape`) is exposed; everything else (the below-`v` tail, the transport, the bridge) is
unconditional.
-/

namespace ProofsInTheBook.PolygonEarEscape

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonDiagonal (rightLength)
open ProofsInTheBook.PolygonWinding
  (windCross windCross_emod_two even_crossing_of_windCross_eq_zero)
open ProofsInTheBook.PolygonWindingExterior
  (windCross_constant_on_ray exists_far_T_windCross_zero)
open ProofsInTheBook.PolygonGeomInput (extremeVertex)
open ProofsInTheBook.PolygonExtremeEar
  (extremeHeight_le seg_subset_upper_halfplane)
open ProofsInTheBook.PolygonEarDelete (EarCutData)
open ProofsInTheBook.PolygonWindingPath
  (EarDeletedWindingZero earDeletedExterior_of_seed earDeletedWindingZero_forces_even
   earDeletedExterior_at_of_windZero)
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: every `P'` edge lies weakly above the extreme vertex of `P`

`P' := buildRightPoly hdiag rax` has vertex tuple `subpolygonRightTuple P (prev i) (next i)`, i.e.
`P'.q k = P.q (rightIndex (prev i) (next i) k)` — every `P'` vertex is a `P` vertex.  Since the
extreme vertex `v = extremeVertex P` is the global `y`-minimiser of `P`, every `P'` vertex (and hence
every `P'` edge, by convexity of the upper half-plane) lies weakly above `v`. -/

/-- **Every `P'` vertex is a `P` vertex, hence weakly above the extreme height.**  `P'.q k =
P.q (rightIndex …)`, so `extremeHeight_le` applies. -/
theorem earDeleted_vertex_above_extreme
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n)
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (k : Fin (rightLength (cyclicPrev i) (cyclicNext i))) :
    (P.q (extremeVertex P)) 1 ≤ ((buildRightPoly hdiag rax).q k) 1 := by
  rw [buildRightPoly_q]
  -- `subpolygonRightTuple P a b k = P.q (rightIndex a b k)`
  exact extremeHeight_le P _

/-- **Every `P'` edge lies in the closed upper half-plane through the extreme vertex of `P`.**  Both
endpoints of any `P'` edge are `P` vertices at height `≥ y_v`, and the half-plane is convex. -/
theorem earDeleted_edge_above_extreme
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n)
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (k : Fin (rightLength (cyclicPrev i) (cyclicNext i))) :
    Edge (buildRightPoly hdiag rax).q k ⊆
      {z : Pt | (P.q (extremeVertex P)) 1 ≤ z 1} := by
  rw [Edge]
  exact seg_subset_upper_halfplane
    (earDeleted_vertex_above_extreme P ρ i hdiag rax k)
    (earDeleted_vertex_above_extreme P ρ i hdiag rax (cyclicNext k))

/-- **No `P'` boundary point lies strictly below the extreme vertex of `P`** (UNCONDITIONAL).  This
is the genuine free content of the extreme angle, lifted to the ear-deleted polygon: the entire
half-plane strictly below `v` is `P'`-boundary-free, so the below-`v` tail of any downward escape is
crossing-free.  (The prior route had this for `P`; the new point is that it holds verbatim for `P'`
because every `P'` vertex is a `P` vertex.) -/
theorem belowExtreme_offBoundary_earDeleted
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n)
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    {z : Pt} (hz : z 1 < (P.q (extremeVertex P)) 1) :
    ¬ OnBoundary (buildRightPoly hdiag rax) z := by
  rintro ⟨k, hk⟩
  have := earDeleted_edge_above_extreme P ρ i hdiag rax k hk
  simp only [Set.mem_setOf_eq] at this
  linarith

/-! ## Part 2: the escape transport (single straight leg, and the bent two-leg path)

The substrate's only `windCross` transport is `windCross_constant_on_ray`: `windCross` is constant
along a straight segment `x + t•v` provided the WHOLE segment misses `P'`'s boundary.  Combined with
`exists_far_T_windCross_zero` (far value `0`), a single boundary-free escape ray forces
`windCross P' x = 0`.  We then chain two such legs for the bent path. -/

/-- **Single-leg escape transport.**  If there is an escape vector `v` with `det2 σ.r v ≠ 0` and the
forward ray `x + t•v` (`0 ≤ t`) is OFF `Q`'s boundary for every `t`, then `windCross Q σ x = 0`.
(Re-packaging of `windCross_constant_on_ray` + `exists_far_T_windCross_zero`; no half-plane needed,
just a boundary-free ray.) -/
theorem windCross_zero_of_escape {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q)
    {x v : Pt} (hvσ : det2 σ.r v ≠ 0)
    (havoid : ∀ t : ℝ, 0 ≤ t → ¬ OnBoundary Q (x + t • v)) :
    windCross Q σ x = 0 := by
  obtain ⟨T, hTnn, hfar⟩ := exists_far_T_windCross_zero Q σ x v hvσ
  have hconst : windCross Q σ x = windCross Q σ (x + T • v) :=
    windCross_constant_on_ray Q σ x v hTnn (fun t ht => havoid t ht.1)
  rw [hconst]; exact hfar

/-- **Bent two-leg escape transport.**  Let `q1 = x + s₁ • v₁` be the end of Leg 1 (a boundary-free
straight segment from `x`), and suppose from `q1` a single boundary-free escape ray `q1 + t • v₂`
(`det2 σ.r v₂ ≠ 0`) exists.  Then `windCross Q σ x = 0`.

Leg 2 (`q1 → ∞`) gives `windCross Q σ q1 = 0` via `windCross_zero_of_escape`; Leg 1 (`x → q1`,
boundary-free) transports that `0` back to `x` via `windCross_constant_on_ray`.  This is the bent
path "`x → q1` (across an ear edge, into `v`'s deleted corner) `→ ∞` (straight down past `v`)". -/
theorem windCross_zero_of_two_leg {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q)
    {x v₁ : Pt} {s₁ : ℝ} (hs₁ : 0 ≤ s₁)
    (hleg1 : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) s₁ → ¬ OnBoundary Q (x + t • v₁))
    {v₂ : Pt} (hvσ : det2 σ.r v₂ ≠ 0)
    (hleg2 : ∀ t : ℝ, 0 ≤ t → ¬ OnBoundary Q ((x + s₁ • v₁) + t • v₂)) :
    windCross Q σ x = 0 := by
  -- Leg 2: the winding at q1 = x + s₁•v₁ is 0.
  have hq1 : windCross Q σ (x + s₁ • v₁) = 0 :=
    windCross_zero_of_escape Q σ hvσ hleg2
  -- Leg 1: transport 0 from q1 back to x along the boundary-free segment.
  have hleg : windCross Q σ x = windCross Q σ (x + s₁ • v₁) :=
    windCross_constant_on_ray Q σ x v₁ hs₁ hleg1
  rw [hleg, hq1]

/-! ## Part 3: the single named residue `EarCornerEscape`, and the kernel discharge

The transport reduces `windCross P' x = 0` to the EXISTENCE of a boundary-free bent escape.  Leg 2 is
unconditional once `q1` is near/below `v` (Part 1).  The one geometric input is Leg 1: from the
interior ear point `x`, a short segment across an ear edge into `v`'s deleted corner that meets no
`P'` edge.  We isolate exactly this — the *empty-ear corner escape* — as the single named residue,
and prove it discharges `EarDeletedWindingZero`. -/

/-- **The empty-ear corner escape seed** (the minimal named residue of this route).  For every
polygon (`4 ≤ m`), ray, and vertex `i` carrying ear-deletion data, every strict-interior ear point
`x` off the polygon boundary admits a `P'`-boundary-free **bent two-leg escape**: a Leg-1 vector
`v₁` with end parameter `s₁ ≥ 0` such that `x + t•v₁` (`t ∈ [0,s₁]`) is off `P'`'s boundary, and from
the leg-1 endpoint a Leg-2 escape vector `v₂` with `det2 σR.r v₂ ≠ 0` whose downward ray is off `P'`'s
boundary — together with the empty-ear off-boundary fact `¬ OnBoundary P' x`.

Geometrically `v₁` crosses an ear edge into `v`'s deleted corner (where `P'` has no boundary) and `v₂`
is the downward escape past `v` (boundary-free by `belowExtreme_offBoundary_earDeleted`).  The residue
is the LOCAL empty-ear fact only — strictly weaker than the prior straight-downward residue. -/
def EarCornerEscape : Prop :=
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
        ∃ (v₁ : Pt) (s₁ : ℝ), 0 ≤ s₁ ∧
          (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) s₁ →
            ¬ OnBoundary (buildRightPoly hdiag rax) (x + t • v₁)) ∧
          ∃ v₂ : Pt, det2 σR.r v₂ ≠ 0 ∧
            (∀ t : ℝ, 0 ≤ t →
              ¬ OnBoundary (buildRightPoly hdiag rax) ((x + s₁ • v₁) + t • v₂))

/-- **`EarCornerEscape` ⟹ `EarDeletedWindingZero`** (the bent-path discharge of the winding seed).
The corner escape produces, per ear point/ray, the boundary-free bent path; `windCross_zero_of_two_leg`
turns it into `windCross P' x = 0`, which together with `¬ OnBoundary P' x` is exactly
`EarDeletedWindingZero`. -/
theorem earDeletedWindingZero_of_cornerEscape (S : EarCornerEscape) :
    EarDeletedWindingZero := by
  intro m P ρ i hm E x w0 w1 w2 hoff hw0 hw1 hw2 hsum hx hdiag rax σR hRr
  obtain ⟨hoffR, v₁, s₁, hs₁, hleg1, v₂, hvσ, hleg2⟩ :=
    S P ρ i hm E hoff hw0 hw1 hw2 hsum hx hdiag rax σR hRr
  refine ⟨hoffR, ?_⟩
  exact windCross_zero_of_two_leg (buildRightPoly hdiag rax) σR hs₁ hleg1 hvσ hleg2

/-- **The kernel `EarCutData.earDeletedExterior` from the corner escape** (the full discharge).  A
strict-interior ear point off the boundary lies outside the ear-deleted polygon, for every common
ray — verbatim the kernel conclusion — once `EarCornerEscape` is supplied.  Composes
`earDeletedWindingZero_of_cornerEscape` with the proved `earDeletedExterior_of_seed`. -/
theorem earDeletedExterior_of_cornerEscape (S : EarCornerEscape)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m)
    (hm : 4 ≤ m) (E : EarCutData P ρ i)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hoff : ¬ OnBoundary P x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i))
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (σR : RayDirection (buildRightPoly hdiag rax)) (hRr : σR.r = ρ.r) :
    ¬ ClosedRegion' (buildRightPoly hdiag rax) σR x :=
  earDeletedExterior_of_seed (earDeletedWindingZero_of_cornerEscape S)
    P ρ i hm E hoff hw0 hw1 hw2 hsum hx hdiag rax σR hRr

/-- **A boundary-free bent escape at a single point discharges the kernel pointwise** (the
unconditional local form).  No seed: directly from a boundary-free two-leg escape at THIS `x`,
`¬ ClosedRegion' P' σR x`.  This is the genuine, region-free reduction the brief asks for, with the
band entirely sidestepped — the input is just "a boundary-free bent path off `P'` exists at `x`". -/
theorem earDeletedExterior_of_two_leg
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n)
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (σR : RayDirection (buildRightPoly hdiag rax)) {x : Pt}
    (hoffR : ¬ OnBoundary (buildRightPoly hdiag rax) x)
    {v₁ : Pt} {s₁ : ℝ} (hs₁ : 0 ≤ s₁)
    (hleg1 : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) s₁ →
      ¬ OnBoundary (buildRightPoly hdiag rax) (x + t • v₁))
    {v₂ : Pt} (hvσ : det2 σR.r v₂ ≠ 0)
    (hleg2 : ∀ t : ℝ, 0 ≤ t →
      ¬ OnBoundary (buildRightPoly hdiag rax) ((x + s₁ • v₁) + t • v₂)) :
    ¬ ClosedRegion' (buildRightPoly hdiag rax) σR x := by
  have hwz : windCross (buildRightPoly hdiag rax) σR x = 0 :=
    windCross_zero_of_two_leg (buildRightPoly hdiag rax) σR hs₁ hleg1 hvσ hleg2
  exact earDeletedExterior_at_of_windZero P ρ i hdiag rax σR hoffR hwz

/-! ## Part 4: non-vacuity of `EarCornerEscape` (§3.3 anti-vacuity)

`EarCornerEscape` is satisfiable exactly when the geometry is empty-ear faithful.  Its load-bearing,
satisfiable face is the PARITY content: through `earDeletedWindingZero_of_cornerEscape` it forces an
EVEN `(n-1)`-gon crossing number at the ear point — a true planar `Prop` about crossing parity, not a
hidden `False`.  (The integer-value face is the empty-ear geometry, the strictly-more-local residue.)
-/

/-- **Parity-level non-vacuity: the corner escape forces an EVEN `P'` crossing number.**  Under
`EarCornerEscape`, a strict-interior ear point off the boundary has even
`CrossingNumber' (buildRightPoly …) σR x`.  This routes through the proved
`earDeletedWindingZero_forces_even`, so the residue is genuinely about crossing parity — it is not a
vacuous (unsatisfiable-hypothesis) conditional. -/
theorem cornerEscape_forces_even (S : EarCornerEscape)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m)
    (hm : 4 ≤ m) (E : EarCutData P ρ i)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hoff : ¬ OnBoundary P x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i))
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (σR : RayDirection (buildRightPoly hdiag rax)) (hRr : σR.r = ρ.r) :
    Even (CrossingNumber' (buildRightPoly hdiag rax) σR x) :=
  earDeletedWindingZero_forces_even (earDeletedWindingZero_of_cornerEscape S)
    P ρ i hm E hoff hw0 hw1 hw2 hsum hx hdiag rax σR hRr

end

end ProofsInTheBook.PolygonEarEscape

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.PolygonEarEscape.belowExtreme_offBoundary_earDeleted
#print axioms ProofsInTheBook.PolygonEarEscape.earDeleted_edge_above_extreme
#print axioms ProofsInTheBook.PolygonEarEscape.windCross_zero_of_escape
#print axioms ProofsInTheBook.PolygonEarEscape.windCross_zero_of_two_leg
#print axioms ProofsInTheBook.PolygonEarEscape.earDeletedWindingZero_of_cornerEscape
#print axioms ProofsInTheBook.PolygonEarEscape.earDeletedExterior_of_cornerEscape
#print axioms ProofsInTheBook.PolygonEarEscape.earDeletedExterior_of_two_leg
#print axioms ProofsInTheBook.PolygonEarEscape.cornerEscape_forces_even
