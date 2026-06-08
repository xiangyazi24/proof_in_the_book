/-
# Chapter 36 — the cut-geometry oracle via the COMMON-RAY reduction.

This file corrects the missed connection in the Chapter-36 endgame: the previous
analysis claimed the crossing-count identity "does not close because the three
crossing numbers use different rays".  The machinery to fix that is already
present:

* `PolygonIccEngine.region_transfer_common_ray` /
  `closedRegion'_ray_indep_segment` — region transfer to a common ray;
* `PolygonCutOracle.edgeCrossesRay'_congr` — the crossing status of an edge depends
  *only* on `(ray, base point, endpoint pair)`, so the **same** edge in parent and
  child has the **same** status at a common ray `r*`;
* `PolygonIccEngine.split_region_symmDiff_of_countSum` — the symmetric-difference
  split from a `CountSummationDatum`.

The genuinely new content here is the **edge-index correspondence + count identity
at a common ray**:

```
count_L(r*, x) + count_R(r*, x) = count_P(r*, x) + 2 · diagCount(r*, x)
```

The left/right sub-edges map to parent edges (the cyclic arc) plus the diagonal
(once in each side, opposite orientations — the *same* geometric crossing event by
`RawEdgeCrosses` orientation-symmetry).  This is the modular-arithmetic /
finite-summation content the `CountSummationDatum` previously *assumed*; we *prove*
it (for a common ray) and feed it into the symmDiff split.

## Honest scope

The count identity is proved at a *common ray* `r*` valid for the parent and both
sub-polygons.  Producing such a single `r*` for all three polygons — and the
region transfer onto it — is the genuine, *named*, honest residual
(`CommonRayDatum`): its existence is the `validDir_avoiding`-over-the-union-of-edges
genericity (a direction valid for the union of all three edge collections) combined
with the conditional `SegmentChain` connectivity that `PolygonIccEngine` isolates.
We do **not** fake the half-plane disjointness (`union` vs `symmDiff`) nor the
diagonal-segment intersection — those stay the irreducible Jordan residue inside
`CutGeometryOracle`, exactly as `PolygonCutOracle` flagged.

No `sorry`, `axiom`, `admit`, or `native_decide`.

Build dependency: `ProofsInTheBook.PolygonLast` (and transitively the Chapter-36
stack).  Verified on uisai1 via `lake env lean`.
-/
import ProofsInTheBook.PolygonLast

namespace ProofsInTheBook.PolygonOracle

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonTriangulation
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonFinish
open ProofsInTheBook.PolygonIccEngine
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonLast
open ProofsInTheBook.PolygonRayIndep
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: orientation symmetry of the raw edge crossing

The raw crossing `RawEdgeCrosses r x a b` is symmetric in the endpoint pair `a, b`:
the half-open span `Span (side r x a) (side r x b)` is visibly symmetric, and the
forward ray parameter `det2 (a - x) (b - a) / det2 r (b - a)` is *equal* under the
swap (the two determinant numerators differ by `det2 (a - b) (b - a) = 0`).  This is
exactly the fact the diagonal edge needs: it is the *same* geometric crossing event
whether read `i → j` (right sub-polygon) or `j → i` (left sub-polygon).

We work with the *definitional* body of `RawEdgeCrosses` (`rawSide := side`,
`rawTau := det2 (a-x)(b-a) / det2 r (b-a)` are private to `PolygonCutOracle`, but the
def is non-irreducible, so a `show` with the explicit body is definitionally valid). -/

/-- The algebraic kernel: `det2 (a - x) (b - a) = det2 (b - x) (b - a)`.
(The two `rawTau` numerators under an endpoint swap.) -/
lemma det2_sub_base_eq (x a b : Pt) :
    det2 (a - x) (b - a) = det2 (b - x) (b - a) := by
  have h : a - x = (b - x) - (b - a) := by abel
  rw [h, det2_sub_left, PolygonLocalConstancy.det2_self, sub_zero]

/-- The `rawTau` symmetry as an explicit ratio equality (stated on the definitional
body, no private name used). -/
lemma rawTau_swap_eq (r x a b : Pt) :
    det2 (a - x) (b - a) / det2 r (b - a) = det2 (b - x) (a - b) / det2 r (a - b) := by
  have hden : det2 r (a - b) = - det2 r (b - a) := by
    have h : a - b = -(b - a) := by abel
    rw [h]; rw [show (-(b - a)) = (-1 : ℝ) • (b - a) by module, det2_smul_right]; ring
  have hnum : det2 (b - x) (a - b) = - det2 (b - x) (b - a) := by
    have h : a - b = -(b - a) := by abel
    rw [h]; rw [show (-(b - a)) = (-1 : ℝ) • (b - a) by module, det2_smul_right]; ring
  rw [hden, hnum, neg_div_neg_eq, det2_sub_base_eq x a b]

/-- **`RawEdgeCrosses` is orientation-symmetric.**  `RawEdgeCrosses r x a b ↔
RawEdgeCrosses r x b a`.  `Span` is symmetric; the ray parameters agree by
`rawTau_swap_eq`. -/
lemma rawEdgeCrosses_symm (r x a b : Pt) :
    RawEdgeCrosses r x a b ↔ RawEdgeCrosses r x b a := by
  show (Span (side r x a) (side r x b) ∧ 0 ≤ det2 (a - x) (b - a) / det2 r (b - a)) ↔
       (Span (side r x b) (side r x a) ∧ 0 ≤ det2 (b - x) (a - b) / det2 r (a - b))
  rw [← rawTau_swap_eq r x a b]
  have hspan_symm : ∀ p q : ℝ, Span p q → Span q p := by
    intro p q h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
  constructor
  · rintro ⟨hspan, htau⟩
    exact ⟨hspan_symm _ _ hspan, htau⟩
  · rintro ⟨hspan, htau⟩
    exact ⟨hspan_symm _ _ hspan, htau⟩

/-! ## Part 2: the edge-index correspondence (left/right sub-edges ↦ parent edges ∪ diagonal)

The left subpolygon's vertex `k : Fin (leftLength i j)` is `leftIndex i j k`; its edge
`k` joins `P.q (leftIndex i j k)` to `P.q (leftIndex i j (cyclicNext k))`.  For
`k.val < cyclicSteps i j` (the `cyclicSteps i j` *arc* edges), these endpoints are the
two consecutive parent vertices `(i + k) % n` and `(i + k + 1) % n` — exactly parent
edge `(i + k) % n`.  For `k.val = cyclicSteps i j` (the single *diagonal* edge), the
endpoints are `j` and `i` — the diagonal read `j → i`.  This Part proves those endpoint
identities; Part 3 turns them into the crossing-count identity. -/

/-- The cyclic position `(i + d) % n` as an element of `Fin n`. -/
def arcPt (i : Fin n) (d : ℕ) : Fin n :=
  ⟨(i.val + d) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

@[simp] lemma arcPt_val (i : Fin n) (d : ℕ) : (arcPt i d).val = (i.val + d) % n := rfl

/-- `leftIndex i j k = arcPt i k.val` when `k.val < cyclicSteps i j`. -/
lemma leftIndex_arc {i j : Fin n} {k : Fin (leftLength i j)}
    (hk : k.val < cyclicSteps i j) : leftIndex i j k = arcPt i k.val := by
  unfold leftIndex arcPt
  simp only [hk, dif_pos]

/-- `leftIndex i j k = j` at the final index `k.val = cyclicSteps i j`. -/
lemma leftIndex_last {i j : Fin n} {k : Fin (leftLength i j)}
    (hk : k.val = cyclicSteps i j) : leftIndex i j k = j := by
  unfold leftIndex
  have : ¬ k.val < cyclicSteps i j := by omega
  simp only [this, dif_neg, not_false_iff]

/-- The cyclic successor on `Fin n` of an arc position is the next arc position
(modular).  `cyclicNext (arcPt i d) = arcPt i (d + 1)`. -/
lemma cyclicNext_arcPt (i : Fin n) (d : ℕ) (hn : 0 < n) :
    cyclicNext (arcPt i d) = arcPt i (d + 1) := by
  apply Fin.ext
  unfold cyclicNext arcPt
  have hkey : (i.val + (d + 1)) % n = ((i.val + d) % n + 1) % n := by
    have hdm := Nat.div_add_mod (i.val + d) n
    conv_lhs => rw [show i.val + (d + 1) = ((i.val + d) % n + 1) + n * ((i.val + d) / n) by omega]
    rw [Nat.add_mul_mod_self_left]
  by_cases h : (i.val + d) % n + 1 < n
  · simp only [h, dif_pos]
    rw [hkey, Nat.mod_eq_of_lt h]
  · simp only [h, dif_neg, not_false_iff]
    have hmlt : (i.val + d) % n < n := Nat.mod_lt _ hn
    have heq : (i.val + d) % n + 1 = n := by omega
    rw [hkey, heq, Nat.mod_self]

/-! ### 2b. Raw crossing counts (decoupled from ray validity)

The crossing-count identity is a statement about the *raw* edge crossing
`RawEdgeCrosses r x` for an *arbitrary* direction vector `r` — validity of `r` (the
`RayDirection` axiom) is irrelevant to the combinatorial identity; it only enters the
parity/region transfer (Part 4).  We define a raw crossing count for any vertex tuple
and prove the parent crossing number equals it. -/

/-- The raw crossing count of a vertex tuple `q : Fin m → Pt` along direction `r`
from base `x`: the number of edges `k → cyclicNext k` raw-crossed by the ray. -/
def rawCount {m : ℕ} (q : Fin m → Pt) (r x : Pt) : ℕ := by
  classical
  exact (Finset.univ.filter fun k : Fin m => RawEdgeCrosses r x (q k) (q (cyclicNext k))).card

/-- **The parent crossing number is the raw count of its vertex tuple.** -/
lemma crossingNumber'_eq_rawCount (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) : CrossingNumber' P ρ x = rawCount P.q ρ.r x := by
  classical
  rw [crossingNumber'_eq_card]
  unfold CrossingEdges' rawCount
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [edgeCrossesRay'_eq_raw P ρ x i]

/-- **The left subpolygon crossing number is the raw count of its tuple.** -/
lemma crossingNumber'_left_eq_rawCount {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (hdiag : IsDiagonal' P ρ i j) (lax : LeftStrictAxioms P i j)
    (σ : RayDirection (buildLeftPoly hdiag lax)) (x : Pt) :
    CrossingNumber' (buildLeftPoly hdiag lax) σ x =
      rawCount (subpolygonLeftTuple P i j) σ.r x := by
  classical
  rw [crossingNumber'_eq_card]
  unfold CrossingEdges' rawCount
  congr 1
  apply Finset.filter_congr
  intro k _
  rw [edgeCrossesRay'_eq_raw (buildLeftPoly hdiag lax) σ x k]
  rw [buildLeftPoly_q hdiag lax]

/-- **The right subpolygon crossing number is the raw count of its tuple.** -/
lemma crossingNumber'_right_eq_rawCount {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (hdiag : IsDiagonal' P ρ i j) (rax : RightStrictAxioms P i j)
    (σ : RayDirection (buildRightPoly hdiag rax)) (x : Pt) :
    CrossingNumber' (buildRightPoly hdiag rax) σ x =
      rawCount (subpolygonRightTuple P i j) σ.r x := by
  classical
  rw [crossingNumber'_eq_card]
  unfold CrossingEdges' rawCount
  congr 1
  apply Finset.filter_congr
  intro k _
  rw [edgeCrossesRay'_eq_raw (buildRightPoly hdiag rax) σ x k]
  rw [buildRightPoly_q hdiag rax]

/-! ## Part 3: the crossing-count identity at a common direction

The genuinely new content: for *any* direction vector `r`, base point `x`, and diagonal
endpoints `i ≠ j`,

```
rawCount (subpolygonLeftTuple P i j) r x + rawCount (subpolygonRightTuple P i j) r x
  = rawCount P.q r x + 2 · [RawEdgeCrosses r x (P.q i) (P.q j)].
```

The proof: each sub-edge maps to a parent edge (arc edges) or the diagonal (one per side,
the *same* geometric crossing by `rawEdgeCrosses_symm`); the two arcs partition the
parent edges via the rotation bijection `d ↦ arcPt i d` on `Fin n`. -/

/-- The `0/1` crossing indicator of the edge with endpoints `a → b`. -/
def rawInd (r x a b : Pt) : ℕ := by
  classical
  exact if RawEdgeCrosses r x a b then 1 else 0

/-- `rawCount` as a `Finset.univ`-sum of indicators over the index type. -/
lemma rawCount_eq_sum {m : ℕ} (q : Fin m → Pt) (r x : Pt) :
    rawCount q r x = ∑ k : Fin m, rawInd r x (q k) (q (cyclicNext k)) := by
  classical
  unfold rawCount rawInd
  rw [Finset.card_filter]

/-- **Endpoints of a left arc edge.**  For `k.val < cyclicSteps i j`, the left sub-edge
`k` joins the parent vertices `arcPt i k.val` and `arcPt i (k.val + 1)`. -/
lemma left_arc_edge_endpoints {i j : Fin n} (hij : i ≠ j) {k : Fin (leftLength i j)}
    (hk : k.val < cyclicSteps i j) :
    leftIndex i j k = arcPt i k.val ∧
      leftIndex i j (cyclicNext k) = arcPt i (k.val + 1) := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hcyc : cyclicSteps i j < n := by
    have := cyclicSteps_add_reverse i j hij
    have := cyclicSteps_pos_of_ne j i hij.symm
    omega
  refine ⟨leftIndex_arc hk, ?_⟩
  -- cyclicNext k = ⟨k.val + 1, _⟩ since k.val + 1 < leftLength
  have hnext : (cyclicNext k).val = k.val + 1 := by
    unfold cyclicNext
    have hlt : k.val + 1 < leftLength i j := by unfold leftLength; omega
    simp only [hlt, dif_pos]
  by_cases hk1 : k.val + 1 < cyclicSteps i j
  · rw [leftIndex_arc (k := cyclicNext k) (by rw [hnext]; exact hk1), hnext]
  · -- k.val + 1 = cyclicSteps i j ⇒ leftIndex (cyclicNext k) = j = arcPt i (k.val+1)
    have heq : (cyclicNext k).val = cyclicSteps i j := by rw [hnext]; omega
    rw [leftIndex_last (k := cyclicNext k) heq]
    -- j = arcPt i (k.val + 1) with k.val + 1 = cyclicSteps i j
    apply Fin.ext
    show j.val = (i.val + (k.val + 1)) % n
    rw [show k.val + 1 = cyclicSteps i j by omega]
    exact PolygonLast.j_val_eq_arcPos hij

/-- **Endpoints of the left diagonal edge.**  At the final index `k.val = cyclicSteps i j`,
the left sub-edge joins `j` and `i` — the diagonal read `j → i`. -/
lemma left_diag_edge_endpoints {i j : Fin n} (hij : i ≠ j) {k : Fin (leftLength i j)}
    (hk : k.val = cyclicSteps i j) :
    leftIndex i j k = j ∧ leftIndex i j (cyclicNext k) = i := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hcpos : 0 < cyclicSteps i j := cyclicSteps_pos_of_ne i j hij
  refine ⟨leftIndex_last hk, ?_⟩
  -- cyclicNext k = ⟨0⟩ since k.val + 1 = leftLength
  have hnext : (cyclicNext k).val = 0 := by
    unfold cyclicNext
    have hge : ¬ k.val + 1 < leftLength i j := by unfold leftLength; omega
    simp only [hge, dif_neg, not_false_iff]
  rw [leftIndex_arc (k := cyclicNext k) (by rw [hnext]; exact hcpos)]
  apply Fin.ext
  rw [hnext]
  show (i.val + 0) % n = i.val
  rw [Nat.add_zero, Nat.mod_eq_of_lt i.isLt]

/-- **The left arc-edge indicator equals the parent edge indicator.**  For
`k.val < cyclicSteps i j`, the left sub-edge `k` has the *same* crossing indicator as
parent edge `arcPt i k.val`. -/
lemma rawInd_left_arc {P : StrictSimplePolygon n} {i j : Fin n} (hij : i ≠ j)
    (r x : Pt) {k : Fin (leftLength i j)} (hk : k.val < cyclicSteps i j) :
    rawInd r x (subpolygonLeftTuple P i j k)
        (subpolygonLeftTuple P i j (cyclicNext k)) =
      rawInd r x (P.q (arcPt i k.val)) (P.q (cyclicNext (arcPt i k.val))) := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  obtain ⟨h1, h2⟩ := left_arc_edge_endpoints hij hk
  unfold subpolygonLeftTuple
  rw [h1, h2, cyclicNext_arcPt i k.val hn]

/-- **The left diagonal-edge indicator equals the diagonal indicator** (orientation
`j → i`, identified with `i → j` by `rawEdgeCrosses_symm`). -/
lemma rawInd_left_diag {P : StrictSimplePolygon n} {i j : Fin n} (hij : i ≠ j)
    (r x : Pt) {k : Fin (leftLength i j)} (hk : k.val = cyclicSteps i j) :
    rawInd r x (subpolygonLeftTuple P i j k)
        (subpolygonLeftTuple P i j (cyclicNext k)) =
      rawInd r x (P.q i) (P.q j) := by
  obtain ⟨h1, h2⟩ := left_diag_edge_endpoints hij hk
  unfold subpolygonLeftTuple rawInd
  rw [h1, h2]
  rw [rawEdgeCrosses_symm r x (P.q j) (P.q i)]

/-! ### 3b. The arc-sum splits

Summing the indicators over `Fin (leftLength i j) = Fin (cyclicSteps i j + 1)`, the last
index is the diagonal edge and the first `cyclicSteps i j` are the arc edges.  The arc
edges' indicators equal the parent indicators at `arcPt i d`. -/

/-- **Left arc-sum split.**  The left raw count splits as the sum of parent indicators
over the left arc (`d < cyclicSteps i j`) plus the diagonal indicator. -/
lemma rawCount_left_split {P : StrictSimplePolygon n} {i j : Fin n} (hij : i ≠ j)
    (r x : Pt) :
    rawCount (subpolygonLeftTuple P i j) r x =
      (∑ d : Fin (cyclicSteps i j),
        rawInd r x (P.q (arcPt i d.val)) (P.q (cyclicNext (arcPt i d.val)))) +
      rawInd r x (P.q i) (P.q j) := by
  rw [rawCount_eq_sum]
  -- leftLength i j = cyclicSteps i j + 1 definitionally, so sum is over Fin (cs + 1)
  rw [show (∑ k : Fin (leftLength i j),
      rawInd r x (subpolygonLeftTuple P i j k) (subpolygonLeftTuple P i j (cyclicNext k))) =
      ∑ k : Fin (cyclicSteps i j + 1),
      rawInd r x (subpolygonLeftTuple P i j k) (subpolygonLeftTuple P i j (cyclicNext k)) from rfl]
  rw [Fin.sum_univ_castSucc]
  congr 1
  · -- arc part
    apply Finset.sum_congr rfl
    intro d _
    rw [rawInd_left_arc hij r x (k := Fin.castSucc d) (by
      simp only [Fin.val_castSucc]; exact d.isLt)]
    simp only [Fin.val_castSucc]
  · -- diagonal part: the last index
    rw [rawInd_left_diag hij r x (k := Fin.last (cyclicSteps i j)) (by
      simp only [Fin.val_last])]

/-- `subpolygonRightTuple P i j = subpolygonLeftTuple P j i` (definitional: the right
arc from `i` is the left arc from `j`). -/
lemma subpolygonRightTuple_eq (P : StrictSimplePolygon n) (i j : Fin n) :
    subpolygonRightTuple P i j = subpolygonLeftTuple P j i := rfl

/-- **Right arc-sum split.**  Apply the left split to the swapped pair `(j, i)` (the
right tuple of `(i,j)` is the left tuple of `(j,i)`).  The diagonal indicator
`rawInd r x (P.q j) (P.q i)` is identified with `rawInd r x (P.q i) (P.q j)` via the
orientation symmetry. -/
lemma rawCount_right_split {P : StrictSimplePolygon n} {i j : Fin n} (hij : i ≠ j)
    (r x : Pt) :
    rawCount (subpolygonRightTuple P i j) r x =
      (∑ d : Fin (cyclicSteps j i),
        rawInd r x (P.q (arcPt j d.val)) (P.q (cyclicNext (arcPt j d.val)))) +
      rawInd r x (P.q i) (P.q j) := by
  have heq : rawCount (subpolygonRightTuple P i j) r x
      = rawCount (subpolygonLeftTuple P j i) r x := rfl
  rw [heq, rawCount_left_split (P := P) (i := j) (j := i) hij.symm r x]
  congr 1
  -- rawInd r x (P.q j) (P.q i) = rawInd r x (P.q i) (P.q j)
  unfold rawInd
  rw [rawEdgeCrosses_symm r x (P.q j) (P.q i)]

/-! ### 3c. The parent rotation sum

The combined arc edges `{arcPt i d : d < cyclicSteps i j} ∪ {arcPt j d : d < cyclicSteps j i}`
are exactly the parent edges `Fin n`, via the rotation bijection `d ↦ arcPt i d` on
`Fin n` (using `arcPt j d = arcPt i (cyclicSteps i j + d)` and
`cyclicSteps i j + cyclicSteps j i = n`).  Hence the two arc sums add up to the parent
raw count. -/

/-- `arcPt j d = arcPt i (cyclicSteps i j + d)` (the right arc continues the left arc). -/
lemma arcPt_j_eq {i j : Fin n} (hij : i ≠ j) (d : ℕ) :
    arcPt j d = arcPt i (cyclicSteps i j + d) := by
  apply Fin.ext
  show (j.val + d) % n = (i.val + (cyclicSteps i j + d)) % n
  have hjv : j.val = (i.val + cyclicSteps i j) % n := PolygonLast.j_val_eq_arcPos hij
  conv_lhs => rw [hjv]
  -- ((i+cs)%n + d) % n = (i + cs + d) % n = (i + (cs + d)) % n
  rw [Nat.mod_add_mod, show i.val + cyclicSteps i j + d = i.val + (cyclicSteps i j + d) by ring]

/-- **The parent raw count equals the sum of the two arc sums.**  The map
`e : Fin n → Fin n`, `d ↦ arcPt i d`, is a bijection (rotation); splitting `Fin n` at
`cyclicSteps i j` gives the left arc (`d < cs_ij`) and the right arc
(`arcPt i (cs_ij + d') = arcPt j d'`, `d' < cs_ji`). -/
lemma rawCount_parent_eq_arcs {P : StrictSimplePolygon n} {i j : Fin n} (hij : i ≠ j)
    (r x : Pt) :
    rawCount P.q r x =
      (∑ d : Fin (cyclicSteps i j),
        rawInd r x (P.q (arcPt i d.val)) (P.q (cyclicNext (arcPt i d.val)))) +
      (∑ d : Fin (cyclicSteps j i),
        rawInd r x (P.q (arcPt j d.val)) (P.q (cyclicNext (arcPt j d.val)))) := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hsum : cyclicSteps i j + cyclicSteps j i = n := cyclicSteps_add_reverse i j hij
  -- the rotation map d ↦ arcPt i d on Fin n
  let g : Fin n → ℕ := fun p => rawInd r x (P.q p) (P.q (cyclicNext p))
  -- abbreviation for the indexed summand
  let e : Fin n → Fin n := fun d => arcPt i d.val
  have he_bij : Function.Bijective e := by
    apply (Finite.injective_iff_bijective).mp
    intro a b hab
    have hval : (i.val + a.val) % n = (i.val + b.val) % n := congrArg Fin.val hab
    have hmod : a.val % n = b.val % n :=
      Nat.ModEq.add_left_cancel' i.val (show (i.val + a.val) ≡ (i.val + b.val) [MOD n] from hval)
    rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hmod
    exact Fin.ext hmod
  -- Step 1: rawCount P.q = ∑_{d : Fin n} g (arcPt i d.val)  (reindex via rotation)
  have hstep1 : rawCount P.q r x = ∑ d : Fin n, g (arcPt i d.val) := by
    rw [rawCount_eq_sum]
    exact (Equiv.sum_comp (Equiv.ofBijective e he_bij) g).symm
  rw [hstep1]
  -- Step 2: split Fin n = Fin (cs_ij + cs_ji)
  have hcast : (∑ d : Fin n, g (arcPt i d.val)) =
      ∑ d : Fin (cyclicSteps i j + cyclicSteps j i), g (arcPt i d.val) := by
    apply Fintype.sum_equiv (finCongr hsum.symm)
    intro d
    simp only [finCongr_apply, Fin.val_cast]
  rw [hcast, Fin.sum_univ_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · -- left arc: castAdd indices have val = d.val
    apply Finset.sum_congr rfl
    intro d _
    show g (arcPt i (Fin.castAdd (cyclicSteps j i) d).val) = _
    simp only [Fin.val_castAdd]; rfl
  · -- right arc: natAdd indices have val = cs_ij + d.val; arcPt i (cs_ij+d) = arcPt j d
    apply Finset.sum_congr rfl
    intro d _
    show g (arcPt i (Fin.natAdd (cyclicSteps i j) d).val) = _
    rw [Fin.val_natAdd, ← arcPt_j_eq hij d.val]

/-! ### 3d. The raw count identity and its `CrossingNumber'` bridge -/

/-- **The raw crossing-count identity (common direction).**  For *any* direction `r`,
base `x`, and `i ≠ j`:
`rawCount_L + rawCount_R = rawCount_P + 2 · [diagonal crossed]`.  The two arc sums add to
the parent (rotation bijection); each side contributes the diagonal once. -/
theorem rawCount_split_identity {P : StrictSimplePolygon n} {i j : Fin n} (hij : i ≠ j)
    (r x : Pt) :
    rawCount (subpolygonLeftTuple P i j) r x +
        rawCount (subpolygonRightTuple P i j) r x =
      rawCount P.q r x + 2 * rawInd r x (P.q i) (P.q j) := by
  rw [rawCount_left_split hij r x, rawCount_right_split hij r x,
    rawCount_parent_eq_arcs hij r x]
  ring

/-- **The crossing-number split identity at a common ray `r*`.**  When the parent ray
`ρ`, the left sub-polygon ray `σL`, and the right sub-polygon ray `σR` all share the same
direction vector `r*` (`ρ.r = σL.r = σR.r`), the three crossing numbers satisfy the
bookkeeping identity

`count_P(r*) + 2 · diagCount(r*) = count_L(r*) + count_R(r*)`

— exactly the `CountSummationDatum` shape.  This is the identity the previous analysis
claimed "does not close because the three crossing numbers use different rays": once the
rays are made *common* (which the `validDir_avoiding`-over-the-union genericity provides),
it closes by `rawCount_split_identity`.  `diagCount` here is `PolygonIccEngine.diagCount`,
the `0/1` raw indicator of the diagonal segment. -/
theorem crossingNumber'_split_identity_common
    {P : StrictSimplePolygon n} {ρ : RayDirection P} {i j : Fin n}
    (hdiag : IsDiagonal' P ρ i j) (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly hdiag lax))
    (σR : RayDirection (buildRightPoly hdiag rax))
    (hL : σL.r = ρ.r) (hR : σR.r = ρ.r) (x : Pt) :
    CrossingNumber' P ρ x + 2 * diagCount P ρ x i j =
      CrossingNumber' (buildLeftPoly hdiag lax) σL x +
        CrossingNumber' (buildRightPoly hdiag rax) σR x := by
  have hij : i ≠ j := hdiag.1
  rw [crossingNumber'_eq_rawCount P ρ x,
    crossingNumber'_left_eq_rawCount hdiag lax σL x,
    crossingNumber'_right_eq_rawCount hdiag rax σR x, hL, hR]
  -- diagCount P ρ x i j = rawInd ρ.r x (P.q i) (P.q j)
  have hdiagcount : diagCount P ρ x i j = rawInd ρ.r x (P.q i) (P.q j) := by
    unfold diagCount rawInd; rfl
  rw [hdiagcount, rawCount_split_identity hij ρ.r x]

/-! ## Part 4: discharging `CountSummationDatum` from a common-ray `CutGeometry`

The previous `CountSummationDatum` was an *assumed* numerical identity.  We now *prove*
it for any `CutGeometry g` whose chosen sub-polygon rays share the parent direction
vector (`g.leftRay h |>.r = ρ.r` and likewise on the right) — the common-ray condition.
This condition is exactly what `validDir_avoiding` over the union of the parent and both
sub-polygons' edge slopes produces: a single direction valid for all three.  We name that
existence residual (`CommonRayDatum`) honestly, and prove the count identity (hence the
symmetric-difference split) outright under it. -/

/-- **The common-ray condition on a `CutGeometry`.**  For every diagonal, the supplied
left and right sub-polygon ray directions reuse the parent's direction vector `ρ.r`.
This is satisfiable: a direction avoiding the (finite) union of all three polygons' edge
slopes works for all three (`validDir_avoiding`); the obstruction the design flagged —
`ρ.r` possibly parallel to the diagonal — is sidestepped because `r*` is chosen fresh for
the *union*, then the parent is *transferred* onto it by ray-independence. -/
def CommonRay {P : StrictSimplePolygon n} {ρ : RayDirection P} (g : CutGeometry P ρ) :
    Prop :=
  ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j),
    (g.leftRay h).r = ρ.r ∧ (g.rightRay h).r = ρ.r

/-- **`CountSummationDatum` from a common-ray `CutGeometry`.**  Under the common-ray
condition the previously-assumed count identity is *proved* by
`crossingNumber'_split_identity_common`. -/
def countSummationDatum_of_commonRay {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) (hcr : CommonRay g) : CountSummationDatum g where
  count_sum := by
    intro i j h x
    have hL := (hcr h).1
    have hR := (hcr h).2
    exact crossingNumber'_split_identity_common h (g.leftAxioms h) (g.rightAxioms h)
      (g.leftRay h) (g.rightRay h) hL hR x

/-- **The symmetric-difference split, fully discharged under the common-ray condition.**
Off the boundaries of all three polygons the parent region is the symmetric difference of
the two sub-regions — *proved*, not assumed: the count identity
(`crossingNumber'_split_identity_common`) discharges the `CountSummationDatum` hypothesis
of `split_region_symmDiff_of_countSum`. -/
theorem split_region_symmDiff_commonRay {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) (hcr : CommonRay g) {i j : Fin n} (h : IsDiagonal' P ρ i j)
    {x : Pt} (hP : ¬ OnBoundary P x)
    (hL : ¬ OnBoundary (buildLeftPoly h (g.leftAxioms h)) x)
    (hR : ¬ OnBoundary (buildRightPoly h (g.rightAxioms h)) x) :
    ClosedRegion' P ρ x ↔
      (ClosedRegion' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x ↔
        ¬ ClosedRegion' (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x) :=
  split_region_symmDiff_of_countSum g (countSummationDatum_of_commonRay g hcr) h hP hL hR

/-! ## Part 5: union from symmDiff + the (named) disjointness residual

The `split_region_union` field demands the *set* union `region_P = region_L ∪ region_R`.
The common-ray count identity gives the **symmetric difference** off all boundaries; the
gap is precisely the *both-odd* case, i.e. a point inside *both* sub-polygons.  By the
count identity, such a point has `count_P` even, so it is **not** in `region_P`; hence the
union over-counts unless the two sub-regions are disjoint off the diagonal — the
**half-plane disjointness**, which is irreducibly geometric (a point off the diagonal
cannot lie strictly inside both sub-polygons).  We name that residual and prove the union
*reduces* to it (plus a boundary-handling datum).  This is the honest decomposition: the
parity/count half is discharged here; only the planar disjointness + boundary bookkeeping
remain in `CutGeometryOracle`. -/

/-- **The half-plane disjointness residual.**  Off all three boundaries, no point lies in
*both* sub-regions (they meet only along the diagonal, which is on both boundaries).  This
is the irreducibly-geometric half-plane separation. -/
def OffDiagDisjoint {P : StrictSimplePolygon n} {ρ : RayDirection P} (g : CutGeometry P ρ) :
    Prop :=
  ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j) {x : Pt},
    ¬ OnBoundary P x →
    ¬ OnBoundary (buildLeftPoly h (g.leftAxioms h)) x →
    ¬ OnBoundary (buildRightPoly h (g.rightAxioms h)) x →
    ¬ (ClosedRegion' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x ∧
        ClosedRegion' (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x)

/-- **Pointwise union off all boundaries.**  Combining the proved symmetric-difference
split with the disjointness residual, at an off-all-boundaries point the parent region
membership is the *disjunction* (union) of the two sub-region memberships. -/
theorem region_union_off_boundary {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) (hcr : CommonRay g) (hdisj : OffDiagDisjoint g)
    {i j : Fin n} (h : IsDiagonal' P ρ i j) {x : Pt} (hP : ¬ OnBoundary P x)
    (hL : ¬ OnBoundary (buildLeftPoly h (g.leftAxioms h)) x)
    (hR : ¬ OnBoundary (buildRightPoly h (g.rightAxioms h)) x) :
    ClosedRegion' P ρ x ↔
      (ClosedRegion' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x ∨
        ClosedRegion' (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x) := by
  have hxor := split_region_symmDiff_commonRay g hcr h hP hL hR
  have hnand := hdisj h hP hL hR
  -- with ¬(L ∧ R), the XOR (L ↔ ¬R) is equivalent to the OR (L ∨ R)
  constructor
  · intro hPx
    rw [hxor] at hPx
    by_cases hLx : ClosedRegion' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x
    · exact Or.inl hLx
    · -- ¬L and (L ↔ ¬R) ⟹ ¬¬R ⟹ R
      right
      by_contra hRx
      exact hLx (hPx.mpr hRx)
  · intro hOr
    rw [hxor]
    rcases hOr with hLx | hRx
    · constructor
      · intro _; exact fun hRx => hnand ⟨hLx, hRx⟩
      · intro _; exact hLx
    · constructor
      · intro hLx; exact absurd ⟨hLx, hRx⟩ hnand
      · intro hnRx; exact absurd hRx hnRx

/-! ## Part 6: the assembled Chapter-36 headline

The Chapter-36 art-gallery `⌊n/3⌋` headline is `PolygonLast.artGallery_strict_attach`,
conditional on the residual `CutGeometryOracle`, `BaseTriangleFacts`, and the
`DiagonalAttachInput` peel-ordering witness.  This file's contribution is to **discharge
the count/parity content of the oracle's split fields**: the previously-*assumed*
`CountSummationDatum` is now *proved* (under the common-ray condition) by the edge-index
correspondence + the raw count identity.  Concretely, the residual surface of the union
field is reduced from "the full Jordan region split" to exactly the half-plane
disjointness (`OffDiagDisjoint`) plus boundary bookkeeping — the count/parity half is
mechanically closed.

We re-export the headline so this module names the single Chapter-36 conclusion, and we
record the discharged-content theorem as the file's headline contribution. -/

/-- **Chapter-36 art-gallery headline (re-exported).**  Every strict simple polygon with
a ray direction admits `≤ ⌊n/3⌋` vertex guards seeing its whole closed region, given the
residual `CutGeometryOracle`, the base-triangle facts, and the diagonal-attach peel
witness.  (Identical to `PolygonLast.artGallery_strict_attach`; named here so the
common-ray reduction module exposes the final conclusion.) -/
theorem artGallery_strict_headline (g : CutGeometryOracle) (B : BaseTriangleFacts)
    (M : DiagonalAttachInput B) (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  PolygonLast.artGallery_strict_attach g B M P ρ

/-- **The headline contribution of this module (summary theorem).**  The conjunction the
common-ray reduction discharges: for every `CutGeometry` with the common-ray condition,
(i) the count identity `count_P + 2·diagCount = count_L + count_R` holds at the common
ray for every diagonal and off-boundary point, and (ii) hence the parent region is the
symmetric difference of the two sub-regions off all boundaries; and (iii) adjoining the
half-plane disjointness residual upgrades the symmetric difference to the *union* — the
exact shape the oracle's `split_region_union` field consumes (off boundaries).  None of
this is assumed: it is all derived from the edge-index correspondence. -/
theorem commonRay_reduction_summary {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) (hcr : CommonRay g) :
    -- (i) the count identity at the common ray
    (∀ {i j : Fin n} (h : IsDiagonal' P ρ i j) (x : Pt),
        CrossingNumber' P ρ x + 2 * diagCount P ρ x i j =
          CrossingNumber' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x +
            CrossingNumber' (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x) ∧
    -- (ii) the symmetric-difference split off all boundaries
    (∀ {i j : Fin n} (h : IsDiagonal' P ρ i j) {x : Pt}, ¬ OnBoundary P x →
        ¬ OnBoundary (buildLeftPoly h (g.leftAxioms h)) x →
        ¬ OnBoundary (buildRightPoly h (g.rightAxioms h)) x →
        (ClosedRegion' P ρ x ↔
          (ClosedRegion' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x ↔
            ¬ ClosedRegion' (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x))) ∧
    -- (iii) union from the disjointness residual
    (OffDiagDisjoint g → ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j) {x : Pt},
        ¬ OnBoundary P x →
        ¬ OnBoundary (buildLeftPoly h (g.leftAxioms h)) x →
        ¬ OnBoundary (buildRightPoly h (g.rightAxioms h)) x →
        (ClosedRegion' P ρ x ↔
          (ClosedRegion' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x ∨
            ClosedRegion' (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j h x
    exact (countSummationDatum_of_commonRay g hcr).count_sum h x
  · intro i j h x hP hL hR
    exact split_region_symmDiff_commonRay g hcr h hP hL hR
  · intro hdisj i j h x hP hL hR
    exact region_union_off_boundary g hcr hdisj h hP hL hR

end

end ProofsInTheBook.PolygonOracle
