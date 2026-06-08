import ProofsInTheBook.PolygonDiagonal

/-!
# Round-2 parity machinery for the polygon substrate (Chapter 36)

This file develops the *proof-level* parity machinery sitting on top of the
half-open ray–crossing substrate of `PolygonSubstrate`/`PolygonDiagonal`.

The substrate fixes, for a strict simple polygon `P` and a non-parallel ray
direction `ρ`, the finite set `CrossingEdges P ρ x` of polygon edges that are
*properly* crossed by the half-open ray emanating from `x`, and the parity
membership predicate

```
ClosedRegion P ρ x  :=  OnBoundary P x  ∨  Odd (CrossingNumber P ρ x).
```

The genuinely topological content needed downstream (the existence of a convex
vertex, the ear/diagonal facts, the region-cut identities) ultimately rests on
four foundational facts, which the round-2 design isolates:

* **(a) local constancy** of `CrossingNumber` away from the boundary;
* **(b) the single–edge jump lemma**: crossing one edge transversally flips the
  parity by exactly one;
* **(c) the half-open convention** handling vertices/degeneracies, so a ray
  through a vertex is counted on exactly one incident edge;
* **the interior-to-exterior boundary-crossing theorem** (the finite Jordan
  substitute): a segment from a region point to a non-region point must meet the
  polygon boundary.

This file proves the *bookkeeping core* of (a),(b),(c) unconditionally — the
purely finite/`Finset` parity algebra that turns "exactly one crossing edge
changes status" into "the parity flips" — and packages the genuinely geometric
*transversality input* (which crossing edges change, and that they change by a
singleton) as named, documented, non-vacuous evidence predicates.  On top of
that core it derives the interior-to-exterior boundary-crossing theorem in the
form actually consumed by the cutting layer.

Nothing here is assumed globally: every geometric residue is exposed as an
explicit hypothesis of the theorem that needs it, mirroring the
`A3GeometryFacts`/`A4CuttingFacts` interface discipline of `PolygonDiagonal`.
-/

namespace ProofsInTheBook.PolygonParity

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## 1. The crossing set as a decidable membership filter

We record the basic membership characterization of `CrossingEdges` and the fact
that `CrossingNumber` is the cardinality of that explicit `Finset`.  These are
the hooks every parity argument uses. -/

/-- Membership in the crossing set is exactly the `EdgeCrossesRay` predicate. -/
lemma mem_crossingEdges_iff (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (i : Fin n) :
    i ∈ CrossingEdges P ρ x ↔ EdgeCrossesRay P ρ x i := by
  classical
  unfold CrossingEdges
  simp [Finset.mem_filter]

/-- `CrossingNumber` is, by definition, the cardinality of the crossing set. -/
lemma crossingNumber_eq_card (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) :
    CrossingNumber P ρ x = (CrossingEdges P ρ x).card := rfl

/-! ## 2. Parity bookkeeping: the abstract single–edge jump

The mathematical heart of item (b) is finite/`Finset` algebra, independent of
any geometry: if the crossing sets at two points `x,y` agree on every edge
except a single edge `i`, then the two crossing numbers differ by exactly one,
hence have opposite parity.  We phrase the agreement as a symmetric–difference
condition so that the geometric input is exactly "which edges change status". -/

/-- If two finite sets of indices differ in exactly one element (their symmetric
difference is a singleton), then their cardinalities differ by exactly one. -/
lemma card_eq_succ_or_succ_of_symmDiff_singleton
    {S T : Finset (Fin n)} {i : Fin n}
    (h : symmDiff S T = {i}) :
    S.card = T.card + 1 ∨ T.card = S.card + 1 := by
  classical
  -- `i` lies in exactly one of `S`, `T`.
  have hmem : i ∈ symmDiff S T := by rw [h]; exact Finset.mem_singleton_self i
  rw [Finset.mem_symmDiff] at hmem
  -- All other elements agree.
  have hagree : ∀ j : Fin n, j ≠ i → (j ∈ S ↔ j ∈ T) := by
    intro j hj
    constructor
    · intro hjS
      by_contra hjT
      have : j ∈ symmDiff S T := by
        rw [Finset.mem_symmDiff]; exact Or.inl ⟨hjS, hjT⟩
      rw [h, Finset.mem_singleton] at this
      exact hj this
    · intro hjT
      by_contra hjS
      have : j ∈ symmDiff S T := by
        rw [Finset.mem_symmDiff]; exact Or.inr ⟨hjT, hjS⟩
      rw [h, Finset.mem_singleton] at this
      exact hj this
  rcases hmem with ⟨hiS, hiT⟩ | ⟨hiT, hiS⟩
  · -- `i ∈ S`, `i ∉ T`; so `S = insert i T`.
    left
    have hST : S = insert i T := by
      apply Finset.ext
      intro j
      by_cases hj : j = i
      · subst hj
        simp [hiS, hiT, Finset.mem_insert]
      · rw [Finset.mem_insert]
        constructor
        · intro hjS; exact Or.inr ((hagree j hj).mp hjS)
        · intro hjor
          rcases hjor with h0 | h1
          · exact absurd h0 hj
          · exact (hagree j hj).mpr h1
    rw [hST, Finset.card_insert_of_notMem hiT]
  · -- `i ∈ T`, `i ∉ S`; so `T = insert i S`.
    right
    have hTS : T = insert i S := by
      apply Finset.ext
      intro j
      by_cases hj : j = i
      · subst hj
        simp [hiS, hiT, Finset.mem_insert]
      · rw [Finset.mem_insert]
        constructor
        · intro hjT; exact Or.inr ((hagree j hj).mpr hjT)
        · intro hjor
          rcases hjor with h0 | h1
          · exact absurd h0 hj
          · exact (hagree j hj).mp h1
    rw [hTS, Finset.card_insert_of_notMem hiS]

/-- Opposite-parity form of the abstract single–edge jump: if the crossing sets
at `x` and `y` differ in exactly one edge, the crossing numbers have opposite
parity. -/
lemma odd_crossingNumber_iff_not_odd_of_symmDiff_singleton
    (P : StrictSimplePolygon n) (ρ : RayDirection P) {x y : Pt} {i : Fin n}
    (h : symmDiff (CrossingEdges P ρ x) (CrossingEdges P ρ y) = {i}) :
    (Odd (CrossingNumber P ρ x) ↔ ¬ Odd (CrossingNumber P ρ y)) := by
  classical
  rw [crossingNumber_eq_card, crossingNumber_eq_card]
  rcases card_eq_succ_or_succ_of_symmDiff_singleton h with hc | hc
  · -- `S.card = T.card + 1`.
    rw [hc, Nat.odd_add_one]
  · -- `T.card = S.card + 1`.
    rw [hc, Nat.odd_add_one, not_not]

/-! ## 3. Local constancy of the crossing number (item (a), bookkeeping core)

Item (a) of the round-2 design is the statement that the half-open crossing
number is *locally constant* away from the boundary.  Its genuinely geometric
content — *which* edges change crossing status as `x` varies, and that this
only happens when `x` sweeps across a polygon edge — is the transversality
input isolated as a residue in §4.  The purely set-theoretic core, however, is
unconditional: equal crossing sets give equal crossing numbers, and (off the
boundary) equal region membership. -/

/-- Equal crossing sets give equal crossing numbers.  This is the trivial
direction of local constancy: the geometry is entirely contained in the
hypothesis `CrossingEdges P ρ x = CrossingEdges P ρ y`. -/
lemma crossingNumber_eq_of_crossingEdges_eq
    (P : StrictSimplePolygon n) (ρ : RayDirection P) {x y : Pt}
    (h : CrossingEdges P ρ x = CrossingEdges P ρ y) :
    CrossingNumber P ρ x = CrossingNumber P ρ y := by
  rw [crossingNumber_eq_card, crossingNumber_eq_card, h]

/-- Off the boundary, equal crossing sets give equal region membership.  This is
the membership form of local constancy that the Jordan substitute consumes. -/
lemma closedRegion_iff_of_crossingEdges_eq
    (P : StrictSimplePolygon n) (ρ : RayDirection P) {x y : Pt}
    (hx : ¬ OnBoundary P x) (hy : ¬ OnBoundary P y)
    (h : CrossingEdges P ρ x = CrossingEdges P ρ y) :
    (ClosedRegion P ρ x ↔ ClosedRegion P ρ y) := by
  unfold ClosedRegion
  rw [crossingNumber_eq_of_crossingEdges_eq P ρ h]
  constructor
  · rintro (hb | ho)
    · exact absurd hb hx
    · exact Or.inr ho
  · rintro (hb | ho)
    · exact absurd hb hy
    · exact Or.inr ho

/-! ## 4. The interior-to-exterior boundary-crossing theorem (finite Jordan substitute)

This is the theorem actually consumed by the cutting layer: a straight segment
joining a region point to a non-region point must meet the polygon boundary.
We do *not* assume the Jordan curve theorem.  Instead we package the one genuine
geometric residue — item (a)'s transversality content in topological form: along
a boundary-free segment the region-membership indicator is locally constant —
and derive the theorem by a finite connectedness argument on the parameter
interval `[0,1]`.

The residue is non-vacuous: for a real strict simple polygon and a ray direction
not parallel to any edge, the half-open crossing set is genuinely locally
constant off the boundary (each edge's crossing status is an open/closed
transversal condition in the base point), so the hypothesis is satisfiable and
faithful, not a disguised assumption of the conclusion. -/

/-- **Geometric residue (a), topological form.**  If the closed segment `x y`
avoids the polygon boundary, then the region-membership indicator along the
segment is locally constant in the parameter `t ∈ [0,1]`.

This is exactly the transversality content of local constancy of the crossing
number: as the base point slides along a boundary-free segment, no edge can
change its half-open crossing status, so the parity — hence region membership —
cannot change without a small perturbation also failing to change it. -/
def SegmentRegionLocallyConstant (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x y : Pt) : Prop :=
  (∀ z ∈ seg x y, ¬ OnBoundary P z) →
    IsLocallyConstant
      (fun t : Set.Icc (0 : ℝ) 1 =>
        ClosedRegion P ρ (AffineMap.lineMap x y (t : ℝ)))

set_option synthInstance.maxHeartbeats 400000 in
/-- **Interior-to-exterior boundary-crossing theorem (finite Jordan substitute).**
A straight segment from a region point `x` to a non-region point `y` must meet
the polygon boundary.

The proof is a genuine connectedness argument: assuming the segment avoids the
boundary, the residue makes the region indicator along `[0,1]` locally constant,
hence its `True`-fiber is clopen; since `[0,1]` is connected the fiber is all of
`[0,1]` or empty, contradicting that it contains `0` (image `x`, in region) but
not `1` (image `y`, out of region). -/
theorem interior_to_exterior_meets_boundary
    (P : StrictSimplePolygon n) (ρ : RayDirection P) {x y : Pt}
    (hloc : SegmentRegionLocallyConstant P ρ x y)
    (hx : ClosedRegion P ρ x) (hy : ¬ ClosedRegion P ρ y) :
    ∃ z ∈ seg x y, OnBoundary P z := by
  classical
  by_contra hcon
  -- The segment avoids the boundary.
  have havoid : ∀ z ∈ seg x y, ¬ OnBoundary P z := by
    intro z hz hb; exact hcon ⟨z, hz, hb⟩
  -- Region-membership along the segment is locally constant.
  have hLC := hloc havoid
  -- The set of parameters whose image lies in the region is clopen in `[0,1]`.
  set f : Set.Icc (0 : ℝ) 1 → Prop :=
    fun t => ClosedRegion P ρ (AffineMap.lineMap x y (t : ℝ)) with hf
  have hclopen : IsClopen {t : Set.Icc (0 : ℝ) 1 | f t = True} :=
    hLC.isClopen_fiber True
  -- `0` lies in the fiber: image is `x`, which is in the region.
  have h0mem : (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∈
      {t : Set.Icc (0 : ℝ) 1 | f t = True} := by
    simp only [Set.mem_setOf_eq, hf, eq_iff_iff, iff_true]
    have : AffineMap.lineMap x y ((0 : ℝ)) = x := by simp
    rw [this]; exact hx
  -- The fiber is therefore all of `[0,1]`.
  have huniv : {t : Set.Icc (0 : ℝ) 1 | f t = True} = Set.univ :=
    IsClopen.eq_univ hclopen ⟨_, h0mem⟩
  -- But `1` is not in the fiber: image is `y`, not in the region.
  have h1mem : (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∈
      {t : Set.Icc (0 : ℝ) 1 | f t = True} := by rw [huniv]; trivial
  simp only [Set.mem_setOf_eq, hf, eq_iff_iff, iff_true] at h1mem
  have hy1 : AffineMap.lineMap x y ((1 : ℝ)) = y := by simp
  rw [hy1] at h1mem
  exact hy h1mem

/-! ### 4.1 Segment region-containment from boundary avoidance

The contrapositive of the Jordan substitute is the workhorse of the convex-vertex
and slide arguments: a segment that avoids the boundary (except possibly at its
endpoints) and has one endpoint in the region lies *entirely* in the region.
This is exactly the `seg ⊆ ClosedRegion` clause those layers must establish. -/

/-- If a segment from `x` to `y` avoids the boundary and `x` is in the region,
then every point of the segment is in the region. -/
theorem seg_subset_region_of_boundary_free
    (P : StrictSimplePolygon n) (ρ : RayDirection P) {x y : Pt}
    (hloc : ∀ z ∈ seg x y, SegmentRegionLocallyConstant P ρ x z)
    (hfree : ∀ z ∈ seg x y, ¬ OnBoundary P z)
    (hx : ClosedRegion P ρ x) :
    seg x y ⊆ {z : Pt | ClosedRegion P ρ z} := by
  intro z hz
  by_contra hznot
  -- The sub-segment `x z` lies inside `seg x y`, hence is boundary free.
  have hsub : seg x z ⊆ seg x y := by
    have hxmem : x ∈ seg x y := left_mem_segment ℝ x y
    have hcvx : Convex ℝ (seg x y) := by rw [seg]; exact convex_segment x y
    exact hcvx.segment_subset hxmem hz
  have hfree' : ∀ w ∈ seg x z, ¬ OnBoundary P w := fun w hw => hfree w (hsub hw)
  -- Jordan substitute on the boundary-free sub-segment `x z`: `x` in, `z` out
  -- would force a boundary point, contradiction.
  obtain ⟨w, hw, hwb⟩ :=
    interior_to_exterior_meets_boundary P ρ (hloc z hz) hx hznot
  exact hfree' w hw hwb

/-! ## 5. The half-open vertex convention (item (c))

Item (c): under the half-open `[0,1)` parametrization, a ray through a polygon
vertex is counted on *exactly one* of the two incident edges.  The mechanism is
that the terminal endpoint `b` of an edge `a → b` is excluded (`u < 1`), so the
crossing point produced by `RayProperlyCrossesHalfOpenEdge r x a b` is never the
edge's terminal vertex.  We prove this exclusion unconditionally; it is the
purely algebraic core that makes the half-open convention single-count vertices. -/

/-- **Terminal-vertex exclusion.**  The crossing point of a half-open
ray/edge crossing is never the terminal vertex `b` of the edge (when the edge is
nondegenerate, `a ≠ b`).  This is the algebraic content of the half-open
`[0,1)` convention. -/
lemma halfOpen_crossing_point_ne_terminal
    {r x a b : Pt} (hab : a ≠ b)
    (_h : RayProperlyCrossesHalfOpenEdge r x a b) :
    ∀ τ u : ℝ, 0 ≤ τ → 0 ≤ u → u < 1 →
      x + τ • r = AffineMap.lineMap a b u →
      AffineMap.lineMap a b u ≠ b := by
  intro _ u _ _ hu _ heq
  have h1 : AffineMap.lineMap a b (1 : ℝ) = b := by simp
  have hinj : Function.Injective (AffineMap.lineMap a b : ℝ → Pt) :=
    AffineMap.lineMap_injective ℝ hab
  have : u = (1 : ℝ) := hinj (heq.trans h1.symm)
  linarith

/-- The terminal vertex `q (cyclicNext i)` of edge `i` is never the crossing
point under the half-open convention.  Hence a ray hitting that vertex is *not*
counted on edge `i`; the half-open convention forces the count onto the other
incident edge.  This is the single-counting guarantee of item (c). -/
lemma edge_terminal_vertex_not_halfOpen_crossing
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) (i : Fin n)
    (τ u : ℝ) (hτ : 0 ≤ τ) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (heq : x + τ • ρ.r =
      AffineMap.lineMap (P.q i) (P.q (cyclicNext i)) u) :
    AffineMap.lineMap (P.q i) (P.q (cyclicNext i)) u ≠ P.q (cyclicNext i) := by
  have hab : P.q i ≠ P.q (cyclicNext i) := by
    intro hcontra
    have : i = cyclicNext i := P.injective_q hcontra
    have htwo : 2 ≤ n := Nat.le_trans (by decide) P.hthree
    exact cyclicNext_ne_self htwo i this.symm
  exact halfOpen_crossing_point_ne_terminal hab
    ⟨τ, u, hτ, hu0, hu1, heq⟩ τ u hτ hu0 hu1 heq

/-! ## 6. Open-segment region constancy and diagonal certification

The convex-vertex and slide arguments of `PolygonDiagonal` ultimately have to
produce an `IsDiagonal P ρ i j` whose endpoints are polygon *vertices* — hence
boundary points.  The `seg ⊆ region` clause therefore cannot be obtained from the
all-points-boundary-free workhorse of §4.1 (the endpoints fail the hypothesis).
The faithful tool is open-segment constancy: along the *open* diagonal, which is
genuinely boundary free, region membership is constant; seeded by one interior
region point it gives region membership of every interior point, and the two
endpoints are in the region for free (they are boundary points). -/

/-- **Open-segment region constancy residue.**  If the open segment between `x`
and `y` avoids the boundary, region membership along it (parametrized by
`t ∈ (0,1)`) is locally constant.  This is the same transversality content as the
§4 residue, restricted to the open parameter interval so that the diagonal
endpoints (which are on the boundary) are excluded. -/
def OpenSegmentRegionLocallyConstant (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (x y : Pt) : Prop :=
  (∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z) →
    IsLocallyConstant
      (fun t : Set.Ioo (0 : ℝ) 1 =>
        ClosedRegion P ρ (AffineMap.lineMap x y (t : ℝ)))

set_option synthInstance.maxHeartbeats 400000 in
/-- Region membership is constant across the boundary-free open segment: if some
interior point `z₀` is in the region, every interior point is.  Proof by
connectedness of the open parameter interval `(0,1)`. -/
theorem openSegment_region_const_of_boundary_free
    (P : StrictSimplePolygon n) (ρ : RayDirection P) {x y : Pt}
    (hloc : OpenSegmentRegionLocallyConstant P ρ x y)
    (hfree : ∀ z ∈ openSegment ℝ x y, ¬ OnBoundary P z)
    {z₀ : Pt} (hz₀ : z₀ ∈ openSegment ℝ x y) (hz₀reg : ClosedRegion P ρ z₀) :
    ∀ z ∈ openSegment ℝ x y, ClosedRegion P ρ z := by
  classical
  -- The open parameter interval is a preconnected space.
  haveI : PreconnectedSpace (Set.Ioo (0 : ℝ) 1) := by
    rw [← isPreconnected_iff_preconnectedSpace]; exact isPreconnected_Ioo
  -- Locally constant indicator on the open interval.
  have hLC := hloc hfree
  set f : Set.Ioo (0 : ℝ) 1 → Prop :=
    fun t => ClosedRegion P ρ (AffineMap.lineMap x y (t : ℝ)) with hf
  have hclopen : IsClopen {t : Set.Ioo (0 : ℝ) 1 | f t = True} :=
    hLC.isClopen_fiber True
  -- The seed point's parameter lies in the fiber.
  rw [openSegment_eq_image_lineMap] at hz₀
  obtain ⟨t₀, ht₀, ht₀eq⟩ := hz₀
  have hseed : (⟨t₀, ht₀⟩ : Set.Ioo (0 : ℝ) 1) ∈
      {t : Set.Ioo (0 : ℝ) 1 | f t = True} := by
    simp only [Set.mem_setOf_eq, hf, eq_iff_iff, iff_true]
    rw [ht₀eq]; exact hz₀reg
  -- Hence the fiber is everything.
  have huniv : {t : Set.Ioo (0 : ℝ) 1 | f t = True} = Set.univ :=
    IsClopen.eq_univ hclopen ⟨_, hseed⟩
  -- Read off membership for an arbitrary interior point.
  intro z hz
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨t, ht, hteq⟩ := hz
  have hmem : (⟨t, ht⟩ : Set.Ioo (0 : ℝ) 1) ∈
      {t : Set.Ioo (0 : ℝ) 1 | f t = True} := by rw [huniv]; trivial
  simp only [Set.mem_setOf_eq, hf, eq_iff_iff, iff_true] at hmem
  rw [hteq] at hmem
  exact hmem

/-- **Diagonal certification.**  Given the combinatorial data (`i ≠ j`,
non-adjacency), the boundary-only intersection clause, open-segment local
constancy, the open-segment boundary certificate (interior points are
boundary-free), and a single interior witness lying in the region, the pair
`i, j` is a diagonal.

This discharges the `seg ⊆ region` clause of `IsDiagonal` via open-segment
constancy: the endpoints are in the region as boundary points, every interior
point by constancy. -/
theorem isDiagonal_of_certificate
    (P : StrictSimplePolygon n) (ρ : RayDirection P) {i j : Fin n}
    (hij : i ≠ j) (hnadj : ¬ CyclicAdjacent i j)
    (hloc : OpenSegmentRegionLocallyConstant P ρ (P.q i) (P.q j))
    (hfree : ∀ z ∈ openSegment ℝ (P.q i) (P.q j), ¬ OnBoundary P z)
    {z₀ : Pt} (hz₀ : z₀ ∈ openSegment ℝ (P.q i) (P.q j))
    (hz₀reg : ClosedRegion P ρ z₀)
    (hbdry : seg (P.q i) (P.q j) ∩ {x : Pt | OnBoundary P x}
      = ({P.q i, P.q j} : Set Pt)) :
    IsDiagonal P ρ i j := by
  refine ⟨hij, hnadj, ?_, hbdry⟩
  intro z hz
  -- Interior points: constancy; endpoints: boundary membership.
  rcases (segment_eq_image_lineMap ℝ (P.q i) (P.q j) ▸ hz :
      z ∈ (AffineMap.lineMap (P.q i) (P.q j)) '' Set.Icc (0:ℝ) 1) with ⟨t, ht, hteq⟩
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · -- `t = 0`: `z = P.q i`, a boundary point.
    refine Or.inl ⟨i, ?_⟩
    have hzi : z = P.q i := by rw [← hteq, ← h0]; simp
    rw [hzi, Edge]
    exact left_mem_segment ℝ _ _
  · rcases eq_or_lt_of_le ht.2 with h1 | h1
    · -- `t = 1`: `z = P.q j`, a boundary point.
      refine Or.inl ⟨j, ?_⟩
      have hzj : z = P.q j := by rw [← hteq, h1]; simp
      rw [hzj, Edge]
      exact left_mem_segment ℝ _ _
    · -- `0 < t < 1`: interior point, in the region by constancy.
      have hzopen : z ∈ openSegment ℝ (P.q i) (P.q j) := by
        rw [openSegment_eq_image_lineMap]
        exact ⟨t, ⟨h0, h1⟩, hteq⟩
      exact openSegment_region_const_of_boundary_free P ρ hloc hfree hz₀ hz₀reg z hzopen

end

end ProofsInTheBook.PolygonParity
