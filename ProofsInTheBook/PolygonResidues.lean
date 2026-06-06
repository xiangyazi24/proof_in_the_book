import ProofsInTheBook.PolygonConvexVertex

/-!
# Discharging the A3 transversality residues from the substrate simplicity API

This file sits on top of `PolygonConvexVertex` (Layer A3) and discharges, *from
the explicit finite simplicity data of the substrate*, as much of the three
transversality-residue clauses as is reducible to finite plane geometry.

Recall the residue structures of `PolygonConvexVertex`:

* `EarTransversality P ρ i` and `SlideTransversality P ρ i z`, each carrying

  - `loc` : `OpenSegmentRegionLocallyConstant …` — open-segment local constancy
    of the region indicator;
  - `free` : the **open** candidate segment meets no polygon edge;
  - `bdry` : the **closed** candidate segment meets the boundary *only at its two
    endpoints*.

* `ExtremeConvexResidue P ρ` — an extreme vertex together with its convexity.

## What this file proves unconditionally

The cleanly substrate-derivable content is isolated and proved with no `sorry`,
no `axiom`, no `admit`:

1. **Endpoints are on the boundary.**  Every polygon vertex `P.q k` lies on the
   two incident edges, hence `OnBoundary P (P.q k)` (`vertex_onBoundary`).  This
   is the `⊇` half of every `bdry` clause.

2. **`bdry` is *equivalent* to `free`** (given the endpoints are boundary
   points).  The closed segment decomposes as its two endpoints together with
   the open segment (`insert_endpoints_openSegment`); a boundary point of the
   closed segment is therefore an endpoint or an interior point, and an interior
   boundary point is exactly what `free` forbids.  This is the lemma
   `bdry_of_free` (both inclusions), and it is genuine, non-vacuous content: it
   removes the third clause of each residue, collapsing the residue surface from
   three topological clauses to the two genuinely transversal ones (`loc`,
   `free`).

3. **Builders.**  `earTransversality_of` / `slideTransversality_of` assemble the
   full residue structure from just `(loc, free)`, discharging `bdry`
   internally.  These are the interfaces the assembly below consumes.

## The genuinely isolated residue

The two clauses `loc` (`OpenSegmentRegionLocallyConstant`) and `free` (open-
segment edge-avoidance from the empty-ear / slide-maximality geometry) are the
substrate's *deliberately isolated* transversality residue — see the header of
`PolygonParity` §4, which names local constancy of the half-open crossing parity
as "the one genuine geometric residue" the ray-crossing substrate does not
re-derive from a full Jordan curve theorem.  `loc` is a plane-sweep statement
about how the crossing *set* moves with the base point; `free` is the classical
non-crossing argument for an empty ear / a height-maximal slide vertex.  We do
*not* fake them: they remain explicit, honestly-named hypotheses, but everything
reducible to the finite simplicity API around them is discharged here, and the
final A3 theorems are stated through the slimmed two-clause residue surface.

Non-vacuity is preserved throughout: for a genuine strict simple polygon and a
non-parallel ray all the residual hypotheses are true, the endpoint/bdry content
is derived (not assumed), and the interior region witnesses remain those proved
in `PolygonConvexVertex`.
-/

namespace ProofsInTheBook.PolygonResidues

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonParity
open ProofsInTheBook.PolygonConvexVertex
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## 1. Vertices lie on the boundary

Every polygon vertex is the *initial* endpoint of one edge (and the terminal
endpoint of the previous edge); either witnesses `OnBoundary`. -/

/-- A polygon vertex is the initial endpoint of its outgoing edge, hence on the
boundary. -/
lemma vertex_onBoundary (P : StrictSimplePolygon n) (k : Fin n) :
    OnBoundary P (P.q k) :=
  ⟨k, by rw [Edge]; exact left_mem_segment ℝ _ _⟩

/-! ## 2. `bdry` is equivalent to `free`

The closed candidate segment is the union of its two endpoints and its open
part.  Hence the closed segment's intersection with the boundary is exactly the
two endpoints **iff** the open part avoids the boundary — provided the endpoints
themselves are boundary points (which §1 supplies). -/

/-- A point of the closed segment is one of the two endpoints or an interior
point of the open segment. -/
lemma seg_eq_endpoints_or_open {a b z : Pt} (hz : z ∈ seg a b) :
    z = a ∨ z = b ∨ z ∈ openSegment ℝ a b := by
  rw [seg, ← insert_endpoints_openSegment] at hz
  rcases hz with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **`bdry`-from-`free`.**  If the two endpoints `a, b` of the candidate segment
are boundary points and the *open* segment avoids the boundary, then the *closed*
segment meets the boundary exactly at `{a, b}`. -/
lemma bdry_of_free {P : StrictSimplePolygon n} {a b : Pt}
    (ha : OnBoundary P a) (hb : OnBoundary P b)
    (hfree : ∀ z ∈ openSegment ℝ a b, ¬ OnBoundary P z) :
    seg a b ∩ {x : Pt | OnBoundary P x} = ({a, b} : Set Pt) := by
  apply Set.eq_of_subset_of_subset
  · -- `⊆`: a boundary point of the closed segment is an endpoint.
    rintro z ⟨hzseg, hzb⟩
    rcases seg_eq_endpoints_or_open hzseg with rfl | rfl | hzopen
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
    · exact absurd hzb (hfree z hzopen)
  · -- `⊇`: the two endpoints are in the closed segment and on the boundary.
    rintro z hz
    rcases hz with rfl | hz
    · exact ⟨left_mem_segment ℝ _ _, ha⟩
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨right_mem_segment ℝ _ _, hb⟩

/-! ## 2'. A substrate-native separation lemma for `free`

The classical empty-ear non-crossing argument turns on a half-plane separation:
if the two endpoints of a polygon edge lie *strictly on the same side* of the
base line `B C`, that edge cannot meet the closed base segment (which lies on the
line).  We prove this separation criterion directly in the substrate's own
`orient`/`det2` API, with no appeal to `AffineSubspace.SOppSide`.  It is the
finite, sign-based core that the full `free` discharge composes over the `n`
edges; it is genuine, reusable, non-vacuous content.

The key algebraic fact is that `orient B C ·` is *affine* in its third argument:
along `lineMap P Q t` it equals the convex combination
`(1 - t)·orient B C P + t·orient B C Q`. -/

/-- `det2 u ·` is linear in its second argument: it commutes with `lineMap`. -/
lemma det2_lineMap (u P Q : Pt) (t : ℝ) :
    det2 u (AffineMap.lineMap P Q t) =
      (1 - t) * det2 u P + t * det2 u Q := by
  rw [AffineMap.lineMap_apply_module]
  unfold det2
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- `orient B C ·` is affine in its third argument along a segment parameter. -/
lemma orient_lineMap (B C P Q : Pt) (t : ℝ) :
    orient B C (AffineMap.lineMap P Q t) =
      (1 - t) * orient B C P + t * orient B C Q := by
  unfold orient
  -- `lineMap P Q t - B = lineMap (P - B) (Q - B) t` as vectors; reduce to `det2_lineMap`.
  have hsub : AffineMap.lineMap P Q t - B =
      AffineMap.lineMap (P - B) (Q - B) t := by
    rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    ext k; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [hsub, det2_lineMap]

/-- **Strict same-side separation.**  If two points `P, Q` lie strictly on the
same side of the line through `B, C` (same strict sign of `orient B C ·`), then
no point of the closed segment `P Q` lies on the line `B C`; in particular the
closed segment `P Q` is disjoint from the closed base segment `B C`. -/
lemma seg_disjoint_of_strict_same_side {B C P Q : Pt}
    (hP : orient B C P ≠ 0)
    (hsame : 0 < orient B C P * orient B C Q) :
    ∀ z ∈ seg P Q, orient B C z ≠ 0 := by
  intro z hz
  rw [seg, segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  rw [orient_lineMap]
  -- `(1-t)·a + t·b` with `a, b` of the same strict sign and `t ∈ [0,1]` is nonzero.
  set a := orient B C P
  set b := orient B C Q
  obtain ⟨ht0, ht1⟩ := ht
  rcases lt_or_gt_of_ne hP with hPneg | hPpos
  · -- `a < 0`, hence `b < 0` (same sign).
    have hbneg : b < 0 := by nlinarith [hsame]
    have h1 : (1 - t) * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt hPneg)
    have h2 : t * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 (le_of_lt hbneg)
    -- one of the two summands is strictly negative (since `t ∈ [0,1]` and both signs strict).
    have hlt : (1 - t) * a + t * b < 0 := by
      rcases le_total t (1/2) with htle | htgt
      · have : (1 - t) * a < 0 := mul_neg_of_pos_of_neg (by linarith) hPneg
        linarith
      · have : t * b < 0 := mul_neg_of_pos_of_neg (by linarith) hbneg
        linarith
    exact ne_of_lt hlt
  · -- `a > 0`, hence `b > 0`.
    have hbpos : 0 < b := by nlinarith [hsame]
    have hgt : 0 < (1 - t) * a + t * b := by
      rcases le_total t (1/2) with htle | htgt
      · have : 0 < (1 - t) * a := mul_pos (by linarith) hPpos
        have : 0 ≤ t * b := mul_nonneg ht0 (le_of_lt hbpos)
        linarith
      · have : 0 < t * b := mul_pos (by linarith) hbpos
        have : 0 ≤ (1 - t) * a := mul_nonneg (by linarith) (le_of_lt hPpos)
        linarith
    exact ne_of_gt hgt

/-- Points of the closed base segment `B C` lie on the line `B C`. -/
lemma orient_eq_zero_of_mem_seg_base (B C : Pt) :
    ∀ z ∈ seg B C, orient B C z = 0 := by
  intro z hz
  rw [seg, segment_eq_image_lineMap] at hz
  obtain ⟨t, _, rfl⟩ := hz
  rw [orient_lineMap, orient_base_left, orient_base_right]
  ring

/-- **Edge–base separation.**  If both endpoints of edge `k` lie strictly on the
same side of the base line `B C`, then no point of `Edge P.q k` lies on the
closed base segment `B C`. -/
lemma edge_disjoint_base_of_same_side {P : StrictSimplePolygon n}
    (B C : Pt) (k : Fin n)
    (hk : orient B C (P.q k) ≠ 0)
    (hsame : 0 < orient B C (P.q k) * orient B C (P.q (cyclicNext k))) :
    ∀ z ∈ seg B C, z ∉ Edge P.q k := by
  intro z hzbase hzedge
  -- `z` is on the base line: `orient B C z = 0`.
  have hz0 : orient B C z = 0 := orient_eq_zero_of_mem_seg_base B C z hzbase
  -- but `z ∈ Edge k = seg (q k) (q (next k))`, off the line by separation.
  rw [Edge] at hzedge
  exact seg_disjoint_of_strict_same_side hk hsame z hzedge hz0

/-- **`free` from a per-edge same-side certificate (ear base).**  If for *every*
polygon edge `k` whose closed segment is not already known to avoid the open base
the two endpoints are strictly same-side of the base line `B C`, then the open
base is boundary-free.  We phrase the certificate as: each edge is *either*
endpoint-sharing with the open base being impossible (its closed segment misses
the open base) *or* strictly same-side; the geometric content the empty-ear
hypothesis must supply is exactly this per-edge sign data. -/
lemma free_of_edge_certificate {P : StrictSimplePolygon n} (B C : Pt)
    (hcert : ∀ k : Fin n, ∀ w ∈ openSegment ℝ B C, w ∉ Edge P.q k) :
    ∀ w ∈ openSegment ℝ B C, ¬ OnBoundary P w := by
  intro w hw hb
  obtain ⟨k, hk⟩ := hb
  exact hcert k w hw hk

/-- The same-side per-edge data feeds `free_of_edge_certificate`: an edge with
strictly same-side endpoints contributes no open-base boundary point. -/
lemma openBase_notMem_edge_of_same_side {P : StrictSimplePolygon n}
    (B C : Pt) (k : Fin n)
    (hk : orient B C (P.q k) ≠ 0)
    (hsame : 0 < orient B C (P.q k) * orient B C (P.q (cyclicNext k))) :
    ∀ w ∈ openSegment ℝ B C, w ∉ Edge P.q k := by
  intro w hw
  exact edge_disjoint_base_of_same_side B C k hk hsame w
    (openSegment_subset_segment ℝ B C hw)

/-! ## 3. Builders: full residue from the two genuine clauses

`earTransversality_of` / `slideTransversality_of` take only the two genuinely
transversal clauses `loc` and `free` and assemble the full residue structure,
discharging the `bdry` clause via §2.  This is the slimmed residue surface the
assembly below consumes. -/

/-- Build `EarTransversality` from local constancy and open-segment edge-
avoidance; the boundary-only-at-endpoints clause is derived. -/
def earTransversality_of {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (i : Fin n)
    (loc : OpenSegmentRegionLocallyConstant P ρ
      (P.q (cyclicPrev i)) (P.q (cyclicNext i)))
    (free : ∀ z ∈ openSegment ℝ (P.q (cyclicPrev i)) (P.q (cyclicNext i)),
      ¬ OnBoundary P z) :
    EarTransversality P ρ i where
  loc := loc
  free := free
  bdry := bdry_of_free (vertex_onBoundary P (cyclicPrev i))
    (vertex_onBoundary P (cyclicNext i)) free

/-- Build `SlideTransversality` from local constancy and open-segment edge-
avoidance; the boundary-only-at-endpoints clause is derived. -/
def slideTransversality_of {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (i z : Fin n)
    (loc : OpenSegmentRegionLocallyConstant P ρ (P.q i) (P.q z))
    (free : ∀ w ∈ openSegment ℝ (P.q i) (P.q z), ¬ OnBoundary P w) :
    SlideTransversality P ρ i z where
  loc := loc
  free := free
  bdry := bdry_of_free (vertex_onBoundary P i) (vertex_onBoundary P z) free

/-! ## 4. Slimmed A3 residue surface and the A3 headlines

We assemble the global A3 package through the slimmed two-clause surface: at each
vertex the residual data is `(loc, free)` for the ear, `(loc, free)` for each
maximal slide vertex, plus the extreme-vertex convexity.  The `bdry` clause is
discharged by the builders, so this slim package is strictly smaller than the
`A3Residues` of `PolygonConvexVertex`, and converting it back produces the full
`A3GeometryFacts` interface and the unconditional A3 headlines. -/

/-- Slimmed global A3 residue package.  Compared to `A3Residues`, the
boundary-only-at-endpoints clause of every transversality residue is *removed*
(it is discharged from `free` + vertices-on-boundary by `bdry_of_free`).  Only
the two genuinely transversal clauses survive per residue, plus the extreme
convexity. -/
structure A3ResiduesSlim (P : StrictSimplePolygon n) (ρ : RayDirection P) where
  extreme : ExtremeConvexResidue P ρ
  earLoc : ∀ i : Fin n, IsConvexVertex P ρ i →
    (∀ z : Fin n, z ≠ i → z ≠ cyclicPrev i → z ≠ cyclicNext i →
      P.q z ∉ adjacentTriangle P i) →
    OpenSegmentRegionLocallyConstant P ρ
      (P.q (cyclicPrev i)) (P.q (cyclicNext i))
  earFree : ∀ i : Fin n, IsConvexVertex P ρ i →
    (∀ z : Fin n, z ≠ i → z ≠ cyclicPrev i → z ≠ cyclicNext i →
      P.q z ∉ adjacentTriangle P i) →
    ∀ w ∈ openSegment ℝ (P.q (cyclicPrev i)) (P.q (cyclicNext i)), ¬ OnBoundary P w
  slideLoc : ∀ i z : Fin n, IsConvexVertex P ρ i →
    z ∈ verticesInAdjacentTriangle P i →
    (∀ w ∈ verticesInAdjacentTriangle P i,
      heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q w) ≤
        heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q z)) →
    OpenSegmentRegionLocallyConstant P ρ (P.q i) (P.q z)
  slideFree : ∀ i z : Fin n, IsConvexVertex P ρ i →
    z ∈ verticesInAdjacentTriangle P i →
    (∀ w ∈ verticesInAdjacentTriangle P i,
      heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q w) ≤
        heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q z)) →
    ∀ w ∈ openSegment ℝ (P.q i) (P.q z), ¬ OnBoundary P w

/-- Convert the slimmed package to the full `A3Residues` of `PolygonConvexVertex`
by discharging every `bdry` clause through the builders. -/
def a3Residues_of_slim {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (H : A3ResiduesSlim P ρ) : A3Residues P ρ where
  extreme := H.extreme
  ear := fun i hconv hempty =>
    earTransversality_of i (H.earLoc i hconv hempty) (H.earFree i hconv hempty)
  slide := fun i z hconv hz hmax =>
    slideTransversality_of i z (H.slideLoc i z hconv hz hmax)
      (H.slideFree i z hconv hz hmax)

/-- **A3 geometry interface from the slimmed residue surface.**  Builds the full
`A3GeometryFacts` package downstream cutting/triangulation code consumes, from
the slimmed `(loc, free)`-only residue surface (for `4 ≤ n`). -/
def a3GeometryFacts_of_slim {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (hn : 4 ≤ n) (H : A3ResiduesSlim P ρ) : A3GeometryFacts P ρ :=
  a3GeometryFacts_of_residues hn (a3Residues_of_slim H)

/-- **A3 headline: existence of a convex vertex**, through the slimmed surface. -/
theorem exists_convex_vertex_slim {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (H : A3ResiduesSlim P ρ) : ∃ i : Fin n, IsConvexVertex P ρ i :=
  ProofsInTheBook.PolygonConvexVertex.exists_convex_vertex H.extreme

/-- **A3 headline: existence of a diagonal** (`4 ≤ n`), through the slimmed
residue surface.  Every strict simple polygon with at least four vertices has a
diagonal, given only the extreme-vertex convexity and, at the convex vertex, the
two genuinely transversal clauses `(loc, free)` of whichever branch fires; the
boundary-only clause is discharged internally. -/
theorem exists_diagonal_slim {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (hn : 4 ≤ n) (H : A3ResiduesSlim P ρ) :
    ∃ i j : Fin n, IsDiagonal P ρ i j :=
  (a3GeometryFacts_of_slim hn H).exists_diagonal hn

end

end ProofsInTheBook.PolygonResidues
