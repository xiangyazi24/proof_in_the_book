import ProofsInTheBook.ZinanCh36DiagTube
import ProofsInTheBook.ZinanCh36Perturb

/-!
# `ZinanCh36Straddle` — discharging the diagonal-tube straddle primitive (`DiagTubeStraddle`)

This file closes the ONE remaining named geometric residue of the Chapter-36 diagonal-tube chain:
the `DiagTubeStraddle` primitive of `ZinanCh36DiagTube`.  We produce, in any neighbourhood `U` of
the diagonal midpoint, two points `zp, zm` off all three boundaries whose LEFT-child crossing sets
differ by EXACTLY the diagonal edge of the left child, and whose RIGHT-child crossing sets differ by
EXACTLY the diagonal edge of the right child — the transversal single-edge flip of the shared
diagonal.

## The geometry

Anchor a point `c` on the OPEN diagonal segment, near `diagMid`, that is *ray-generic* for both
children and the parent (no vertex of any of the three polygons lies on the ray line through `c`).
Such anchors are cofinite on the open diagonal: each vertex-on-ray-line condition is a non-constant
affine condition along the diagonal (the ray vector is non-parallel to the diagonal edge), so it
fails at only one diagonal point; finitely many vertices cut out finitely many bad anchors, avoided
by `Set.Ioo`-infinitude (mirroring `ZinanCh36Perturb`'s brick-10 selection).

Then set `zp := c + t • w`, `zm := c - t • w` for the transverse direction `w = sweepDir ρ.r λ`
(`λ` outside the finitely many edge-parallel values, so `w` is non-parallel to every child edge and
`det2 ρ.r w > 0`), with `t > 0` small.

* **Non-diagonal child edges are stable.**  For a non-diagonal child edge `k`, the two endpoint
  side coordinates are nonzero at `c` (ray-genericity), so their signs are preserved at `zp`/`zm`
  for small `t`, hence `SpanCrossesSide` agrees at `zp`/`zm`.  If the span is FALSE the edge is not
  crossed at either point.  If the span is TRUE, then `c` is interior to the diagonal and OFF every
  non-diagonal child edge (the diagonal is the child's closing edge; two distinct child edges meet
  only at a shared vertex, and `c` is not a vertex), so `crossTau ≠ 0` at `c` and its sign is
  preserved at `zp`/`zm` — the forward guard agrees too.  Either way the crossing status agrees.

* **The diagonal child edge flips.**  Along the whole diagonal line, `crossTau` of the diagonal edge
  is identically `0` (the ray from a diagonal point hits the diagonal line at parameter `0`), and its
  slope along `w` is nonzero (`w` transverse to the diagonal edge); so `crossTau` is `> 0` at one of
  `zp`/`zm` and `< 0` at the other.  The span of the diagonal edge is TRUE at `c` (its two endpoints
  straddle the ray line: `σ.r` is non-parallel to the diagonal) and stable, so the diagonal edge is
  crossed at exactly one of `zp`/`zm`.

The symmetric difference is therefore the singleton `{diagonal edge}` on each child.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36Straddle

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonContainment
open ProofsInTheBook.PolygonLocalConstancy
  (crossTau crossDen crossU crossDen_ne_zero det2_sub_left det2_smul_left
   det2_smul_right det2_sub_right det2_self crossTau_eq_zero_imp_onEdge)
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonWinding
open ProofsInTheBook.PolygonWindingZero (perpVec det2_perpVec_pos perpVec_zero perpVec_one)
open ProofsInTheBook.ZinanCh36NonInterleave
  (sweepDir det2_r_sweepDir_pos det2_sweepDir_left)
open ProofsInTheBook.ZinanCh36DiagTube (diagMid diagMid_mem_openSegment diagMid_off_parent_boundary)
open ProofsInTheBook.ZinanCh36Perturb
  (side_perturb_affine exists_lambda_transverse_edges exists_badt_polygon)

noncomputable section

variable {n : ℕ}

/-! ## §1. Affine-in-`s` algebra of the normal segment `s ↦ c + s • w` -/

/-- `side r (c + s•w) v` is affine in `s`: constant term `side r c v`, slope `- det2 r w`.
Restatement of `ZinanCh36Perturb.side_perturb_affine` with the local name. -/
lemma side_step (r c w v : Pt) (s : ℝ) :
    side r (c + s • w) v = side r c v - s * det2 r w :=
  side_perturb_affine r c w v s

/-- `crossTau Q ρ (c + s•w) k` is affine in `s`: constant term `crossTau Q ρ c k`,
slope `- det2 w (edgeVec) / crossDen`. -/
lemma crossTau_step {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q)
    (c w : Pt) (k : Fin m) (s : ℝ) :
    crossTau Q σ (c + s • w) k =
      crossTau Q σ c k - s * (det2 w (Q.q (cyclicNext k) - Q.q k) / crossDen Q σ k) := by
  unfold crossTau crossDen
  have hkey : det2 (Q.q k - (c + s • w)) (Q.q (cyclicNext k) - Q.q k) =
      det2 (Q.q k - c) (Q.q (cyclicNext k) - Q.q k)
        - s * det2 w (Q.q (cyclicNext k) - Q.q k) := by
    have hsub : Q.q k - (c + s • w) = (Q.q k - c) - s • w := by
      ext l; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hsub, det2_sub_left, det2_smul_left]
  rw [hkey, sub_div]
  ring

/-- **`sweepDir ρ.r λ` is non-parallel to a fixed nonzero vector for cofinitely many `λ`.**
`det2 (sweepDir r λ) v = det2 (perpVec r) v + λ·det2 r v` is affine in `λ`.  If `det2 r v ≠ 0` it
vanishes once; if `det2 r v = 0` (so `v ∥ r`) it is the nonzero constant `det2 (perpVec r) v`.  We
collect the bad `λ` over a finite family of nonzero vectors. -/
lemma exists_lambda_transverse_family {ι : Type*} (s : Finset ι) (r : Pt) (hr : r ≠ 0)
    (vec : ι → Pt) (hvec : ∀ a ∈ s, vec a ≠ 0) :
    ∃ bad : Finset ℝ, ∀ lam : ℝ, lam ∉ bad → ∀ a ∈ s, det2 (sweepDir r lam) (vec a) ≠ 0 := by
  classical
  -- For each `a`, the affine function `λ ↦ det2 (perpVec r)(vec a) + λ·det2 r (vec a)` is not
  -- identically zero: at λ = 0 it is `det2 (perpVec r)(vec a)`, and when `det2 r (vec a) = 0` this
  -- value is nonzero.  Bad λ values form a finite set.
  set bad : Finset ℝ := s.filter (fun a => det2 r (vec a) ≠ 0) |>.image
    (fun a => - det2 (perpVec r) (vec a) / det2 r (vec a)) with hbad
  refine ⟨bad, fun lam hlam a ha hz => ?_⟩
  rw [det2_sweepDir_left] at hz
  by_cases hrv : det2 r (vec a) = 0
  · -- `v ∥ r`: the constant term `det2 (perpVec r)(vec a)` must be nonzero.
    rw [hrv, mul_zero, add_zero] at hz
    -- `det2 (perpVec r) v = - det2 v (perpVec r)`; and `det2 v (perpVec r) ≠ 0` for `v ∥ r`, `v ≠ 0`.
    -- From `det2 r v = 0`, `v` is a scalar multiple of `r`; `det2 (perpVec r) v` is then a nonzero
    -- multiple of `det2 (perpVec r) r = - det2 r (perpVec r) < 0`.
    have hva : vec a ≠ 0 := hvec a ha
    -- Use the explicit coordinate computation.
    have hpr : det2 (perpVec r) (vec a) = - ((r 0) * (vec a 0) + (r 1) * (vec a 1)) := by
      unfold det2
      rw [perpVec_zero, perpVec_one]; ring
    have hrvexp : det2 r (vec a) = (r 0) * (vec a 1) - (r 1) * (vec a 0) := by
      unfold det2; ring
    -- `det2 r (vec a) = 0` and `(r0,r1)≠0`, `(va0,va1)≠0` ⟹ `r0·va0+r1·va1 ≠ 0`.
    have hr2 : (r 0) ^ 2 + (r 1) ^ 2 ≠ 0 := by
      intro h0
      apply hr
      have h00 : r 0 = 0 := by nlinarith [sq_nonneg (r 0), sq_nonneg (r 1)]
      have h11 : r 1 = 0 := by nlinarith [sq_nonneg (r 0), sq_nonneg (r 1)]
      exact pt_ext_zero_one h00 h11
    have hva2 : (vec a 0) ^ 2 + (vec a 1) ^ 2 ≠ 0 := by
      intro h0
      apply hva
      have h00 : vec a 0 = 0 := by nlinarith [sq_nonneg (vec a 0), sq_nonneg (vec a 1)]
      have h11 : vec a 1 = 0 := by nlinarith [sq_nonneg (vec a 0), sq_nonneg (vec a 1)]
      exact pt_ext_zero_one h00 h11
    rw [hpr] at hz
    rw [hrvexp] at hrv
    -- (r0 va1 = r1 va0) and (r0 va0 + r1 va1 = 0) ⟹ (r0²+r1²)(va0²+va1²)=0, contradiction.
    have hprod : ((r 0) ^ 2 + (r 1) ^ 2) * ((vec a 0) ^ 2 + (vec a 1) ^ 2) = 0 := by
      nlinarith [hz, hrv]
    exact (mul_ne_zero hr2 hva2) hprod
  · -- `det2 r (vec a) ≠ 0`: `λ` equals the root, so `λ ∈ bad`.
    apply hlam
    refine Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hrv⟩, ?_⟩
    field_simp
    linarith [hz]

/-! ## §2. The diagonal as the closing edge of each child

The diagonal `(P.q i, P.q j)` is the closing edge of both children: index `leftLastIndex i j` in the
left child (`PolygonContainment.diag_eq_left_closing_edge`), and the analogous last index in the right
child, which we set up here. -/

/-- The closing-edge index of the right sub-polygon. -/
def rightLastIndex (i j : Fin n) : Fin (rightLength i j) :=
  ⟨cyclicSteps j i, by unfold rightLength; omega⟩

/-- The last right-arc vertex is the diagonal endpoint `i`. -/
lemma rightIndex_rightLastIndex (i j : Fin n) :
    rightIndex i j (rightLastIndex i j) = i := by
  unfold rightIndex rightLastIndex
  have hlt : ¬ ((⟨cyclicSteps j i, by unfold rightLength; omega⟩ : Fin (rightLength i j)).val
      < cyclicSteps j i) := by simp
  simp only [hlt, dif_neg, not_false_iff]

/-- The cyclic successor of the right closing-edge index is `0`. -/
lemma cyclicNext_rightLastIndex {i j : Fin n} (hij : i ≠ j) :
    cyclicNext (rightLastIndex i j) = (⟨0, by unfold rightLength; omega⟩ : Fin (rightLength i j)) := by
  unfold cyclicNext rightLastIndex
  have hpos : 0 < cyclicSteps j i := cyclicSteps_pos_of_ne j i hij.symm
  have hge : ¬ (cyclicSteps j i + 1 < rightLength i j) := by unfold rightLength; omega
  simp only [hge, dif_neg, not_false_iff]

/-- The `0`-th right-arc vertex is the diagonal endpoint `j`. -/
lemma rightIndex_zero {i j : Fin n} (hij : i ≠ j) :
    rightIndex i j (⟨0, by unfold rightLength; omega⟩ : Fin (rightLength i j)) = j := by
  unfold rightIndex
  have hpos : 0 < cyclicSteps j i := cyclicSteps_pos_of_ne j i hij.symm
  simp only [hpos, dif_pos]
  apply Fin.ext
  simp [Nat.mod_eq_of_lt j.isLt]

/-- **The diagonal segment is the closing edge of the right sub-polygon.** -/
lemma diag_eq_right_closing_edge {P : StrictSimplePolygon n} {i j : Fin n} (hij : i ≠ j) :
    Edge (subpolygonRightTuple P i j) (rightLastIndex i j) = seg (P.q i) (P.q j) := by
  unfold Edge subpolygonRightTuple
  rw [rightIndex_rightLastIndex, cyclicNext_rightLastIndex hij, rightIndex_zero hij]

/-! ## §3. A point on the open diagonal is off every non-diagonal child edge

An interior point `c` of the open diagonal is not a parent vertex (the diagonal meets the parent
boundary only at its endpoints, and `c` is neither endpoint), hence not a child vertex; and it lies
on the child's diagonal closing edge.  By the child's edge-intersection axiom, the only child edge
through `c` is the diagonal edge itself. -/

/-- An interior point of the open diagonal is not a parent vertex. -/
lemma openDiag_ne_parent_vertex {P : StrictSimplePolygon n} {ρ : RayDirection P} {i j : Fin n}
    (h : IsDiagonal' P ρ i j) {c : Pt} (hc : c ∈ openSegment ℝ (P.q i) (P.q j)) (m : Fin n) :
    c ≠ P.q m := by
  intro hcm
  -- `P.q m` is on the boundary, and `c ∈ seg ∩ boundary = {P.q i, P.q j}`.
  have hbd : OnBoundary P (P.q m) := by
    refine ⟨m, ?_⟩
    rw [Edge]; exact left_mem_segment ℝ _ _
  have hmem : c ∈ (seg (P.q i) (P.q j) ∩ {x : Pt | OnBoundary P x}) :=
    ⟨openSegment_subset_segment ℝ _ _ hc, by rw [hcm]; exact hbd⟩
  rw [h.2.2.2] at hmem
  -- so `c` is an endpoint, but `c ∈ openSegment` excludes both endpoints.
  have hqij : P.q i ≠ P.q j := fun he => h.1 (P.injective_q he)
  rcases (Set.mem_insert_iff.mp hmem) with he | he
  · rw [he] at hc; exact hqij ((left_mem_openSegment_iff).mp hc)
  · rw [Set.mem_singleton_iff] at he
    rw [he] at hc; exact hqij ((right_mem_openSegment_iff).mp hc)

/-- **A point on the open diagonal lies on no non-diagonal child edge.**  Generic over the child:
given a child polygon `Q` whose vertices are parent vertices (`hvert`), whose closing edge `d` is the
diagonal segment (`hdiag_edge`), an interior diagonal point `c` lies on `Edge Q.q d` but on no other
child edge `k ≠ d` (two distinct child edges meet only at a shared vertex, and `c` is not a vertex). -/
lemma openDiag_off_nondiag_child_edge {P : StrictSimplePolygon n} {ρ : RayDirection P} {i j : Fin n}
    (h : IsDiagonal' P ρ i j) {m : ℕ} (Q : StrictSimplePolygon m) (d : Fin m)
    (hvert : ∀ a : Fin m, ∃ b : Fin n, Q.q a = P.q b)
    (hdiag_edge : Edge Q.q d = seg (P.q i) (P.q j))
    {c : Pt} (hc : c ∈ openSegment ℝ (P.q i) (P.q j)) {k : Fin m} (hk : k ≠ d) :
    c ∉ Edge Q.q k := by
  intro hck
  -- `c` is on both `Edge Q.q d` (diagonal) and `Edge Q.q k`.
  have hcd : c ∈ Edge Q.q d := by rw [hdiag_edge]; exact openSegment_subset_segment ℝ _ _ hc
  -- `c` is not a child vertex (it is not a parent vertex).
  have hcnotvert : ∀ a : Fin m, c ≠ Q.q a := by
    intro a
    obtain ⟨b, hb⟩ := hvert a
    rw [hb]; exact openDiag_ne_parent_vertex h hc b
  -- Use the edge-intersection axiom on `k`, `d`.
  have hei := Q.edge_intersection k d
  unfold EdgeIntersectionCondition at hei
  rw [dif_neg hk] at hei
  by_cases hnext : cyclicNext k = d
  · rw [dif_pos hnext] at hei
    -- intersection = {Q.q d}; `c` is in it, so `c = Q.q d`, a vertex — contradiction.
    have : c ∈ ({Q.q d} : Set Pt) := by rw [← hei]; exact ⟨hck, hcd⟩
    exact hcnotvert d (Set.mem_singleton_iff.mp this)
  · rw [dif_neg hnext] at hei
    by_cases hprev : cyclicNext d = k
    · rw [dif_pos hprev] at hei
      have : c ∈ ({Q.q k} : Set Pt) := by rw [← hei]; exact ⟨hck, hcd⟩
      exact hcnotvert k (Set.mem_singleton_iff.mp this)
    · rw [dif_neg hprev] at hei
      -- disjoint edges, but `c` is in both.
      exact (Set.disjoint_left.mp hei) hck hcd

/-! ## §4. Sign-preservation of the affine perturbation

If the perturbation amplitude `t·(slope)` is strictly dominated by the value at the anchor `c`, both
perturbed values `c ± t•w` keep that value's (nonzero) sign. -/

/-- The product of `a - p` and `a + p` is positive when `|p| < |a|`. -/
lemma mul_pos_of_abs_lt {a p : ℝ} (h : |p| < |a|) : 0 < (a - p) * (a + p) := by
  have hp2 : p ^ 2 < a ^ 2 := by
    have h1 : |p| ^ 2 < |a| ^ 2 := by nlinarith [abs_nonneg p, abs_nonneg a]
    rwa [sq_abs, sq_abs] at h1
  nlinarith [hp2]

/-- **Threshold dominance.**  For `α ≠ 0`, if `0 < t` and `t < |α| / (|β| + 1)`, then
`|t · β| < |α|`.  The `+1` makes the threshold positive even when `β = 0`. -/
lemma abs_mul_lt_of_lt_threshold {α β t : ℝ} (hα : α ≠ 0) (ht : 0 < t)
    (hlt : t < |α| / (|β| + 1)) : |t * β| < |α| := by
  have hβpos : (0 : ℝ) < |β| + 1 := by positivity
  have hαpos : 0 < |α| := abs_pos.mpr hα
  rw [lt_div_iff₀ hβpos] at hlt
  calc |t * β| = t * |β| := by rw [abs_mul, abs_of_pos ht]
    _ ≤ t * (|β| + 1) := by nlinarith [abs_nonneg β]
    _ < |α| := by linarith [hlt]

/-- If `|p| < |a|`, then `a - p` keeps the sign of `a`, so `(a-p)*a > 0`. -/
lemma mul_pos_of_abs_lt_anchor {a p : ℝ} (h : |p| < |a|) : 0 < (a - p) * a := by
  have ha : a ≠ 0 := by rintro rfl; simp at h; exact absurd h (not_lt.mpr (abs_nonneg p))
  have hpa : |p| < |a| := h
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have : a - p < 0 := by
      have := abs_lt.mp hpa; rw [abs_of_neg hneg] at this; linarith [this.1]
    nlinarith
  · have : 0 < a - p := by
      have := abs_lt.mp hpa; rw [abs_of_pos hpos] at this; linarith [this.2]
    nlinarith

/-- **Side value keeps its sign at both perturbed points.**  If `|t·det2 r w| < |side r c v|`, then
`side r (c+t•w) v` and `side r (c-t•w) v` have the same (nonzero) sign as `side r c v`. -/
lemma side_sign_stable (r c w v : Pt) {t : ℝ}
    (hb : |t * det2 r w| < |side r c v|) :
    0 < side r (c + t • w) v * side r (c + (-t) • w) v := by
  have e1 : side r (c + t • w) v = side r c v - t * det2 r w := side_step r c w v t
  have e2 : side r (c + (-t) • w) v = side r c v + t * det2 r w := by
    rw [side_step r c w v (-t)]; ring
  rw [e1, e2]
  exact mul_pos_of_abs_lt hb

/-- `side r (c+t•w) v` keeps the sign of `side r c v` (anchor product positive). -/
lemma side_sign_stable_anchor (r c w v : Pt) {t : ℝ}
    (hb : |t * det2 r w| < |side r c v|) :
    0 < side r (c + t • w) v * side r c v := by
  rw [side_step r c w v t]
  exact mul_pos_of_abs_lt_anchor hb

/-- **`crossTau` keeps its sign at both perturbed points.**  Slope `det2 w (edge)/crossDen`. -/
lemma crossTau_sign_stable {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q)
    (c w : Pt) (k : Fin m) {t : ℝ}
    (hb : |t * (det2 w (Q.q (cyclicNext k) - Q.q k) / crossDen Q σ k)| < |crossTau Q σ c k|) :
    0 < crossTau Q σ (c + t • w) k * crossTau Q σ (c + (-t) • w) k := by
  have e1 := crossTau_step Q σ c w k t
  have e2 : crossTau Q σ (c + (-t) • w) k =
      crossTau Q σ c k + t * (det2 w (Q.q (cyclicNext k) - Q.q k) / crossDen Q σ k) := by
    rw [crossTau_step Q σ c w k (-t)]; ring
  rw [e1, e2]
  exact mul_pos_of_abs_lt hb

/-! ## §5. Span equality and crossing-status equality for a non-diagonal edge

With both endpoint side coordinates sign-stable, the span predicate agrees at `zp` and `zm`.  If the
span is true, the anchor `c` is off the edge (interior diagonal), so `crossTau c k ≠ 0` and, being
sign-stable, the forward guard agrees too.  Hence the full crossing status agrees. -/

/-- The span agrees at the two sign-stable perturbed points. -/
lemma span_eq_of_sign_stable {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q)
    (zp zm : Pt) (k : Fin m)
    (ha : 0 < side σ.r zp (Q.q k) * side σ.r zm (Q.q k))
    (hb : 0 < side σ.r zp (Q.q (cyclicNext k)) * side σ.r zm (Q.q (cyclicNext k))) :
    (SpanCrossesSide Q σ zp k ↔ SpanCrossesSide Q σ zm k) := by
  have hap : side σ.r zp (Q.q k) ≠ 0 := by rintro h; rw [h, zero_mul] at ha; exact lt_irrefl 0 ha
  have ham : side σ.r zm (Q.q k) ≠ 0 := by rintro h; rw [h, mul_zero] at ha; exact lt_irrefl 0 ha
  have hbp : side σ.r zp (Q.q (cyclicNext k)) ≠ 0 := by
    rintro h; rw [h, zero_mul] at hb; exact lt_irrefl 0 hb
  have hbm : side σ.r zm (Q.q (cyclicNext k)) ≠ 0 := by
    rintro h; rw [h, mul_zero] at hb; exact lt_irrefl 0 hb
  unfold SpanCrossesSide
  rw [span_iff_opp_sign hap hbp, span_iff_opp_sign ham hbm]
  -- both products have the same sign as the product at `c`, so the `< 0` conditions agree.
  constructor
  · intro hp; nlinarith [ha, hb, hp]
  · intro hm; nlinarith [ha, hb, hm]

/-- **Crossing status agrees across `zp`, `zm` for a non-diagonal edge.**  The span agrees (both
endpoints sign-stable); if it is false the edge is not crossed at either point; if it is true the
anchor is off the edge (interior diagonal) so `crossTau c k ≠ 0`, hence the forward guard, being
sign-stable, agrees too. -/
lemma edgeCrosses_eq_nondiag {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q)
    (c zp zm : Pt) (k : Fin m)
    (hak : 0 < side σ.r zp (Q.q k) * side σ.r zm (Q.q k))
    (hbk : 0 < side σ.r zp (Q.q (cyclicNext k)) * side σ.r zm (Q.q (cyclicNext k)))
    (hac : 0 < side σ.r zp (Q.q k) * side σ.r c (Q.q k))
    (hbc : 0 < side σ.r zp (Q.q (cyclicNext k)) * side σ.r c (Q.q (cyclicNext k)))
    (hcoff : c ∉ Edge Q.q k)
    (hτstab : crossTau Q σ c k ≠ 0 → 0 < crossTau Q σ zp k * crossTau Q σ zm k) :
    (EdgeCrossesRay' Q σ zp k ↔ EdgeCrossesRay' Q σ zm k) := by
  have hspan := span_eq_of_sign_stable Q σ zp zm k hak hbk
  unfold EdgeCrossesRay'
  by_cases hspanp : SpanCrossesSide Q σ zp k
  · -- span true at zp, hence at zm and at c.
    have hspanm : SpanCrossesSide Q σ zm k := hspan.mp hspanp
    -- span at c agrees with span at zp (same-sign side values).
    have hspanc : SpanCrossesSide Q σ c k := by
      have hapc : side σ.r zp (Q.q k) ≠ 0 := by
        rintro h; rw [h, zero_mul] at hac; exact lt_irrefl 0 hac
      have hbpc : side σ.r zp (Q.q (cyclicNext k)) ≠ 0 := by
        rintro h; rw [h, zero_mul] at hbc; exact lt_irrefl 0 hbc
      have hacc : side σ.r c (Q.q k) ≠ 0 := by
        rintro h; rw [h, mul_zero] at hac; exact lt_irrefl 0 hac
      have hbcc : side σ.r c (Q.q (cyclicNext k)) ≠ 0 := by
        rintro h; rw [h, mul_zero] at hbc; exact lt_irrefl 0 hbc
      have := (span_eq_of_sign_stable Q σ zp c k hac hbc).mp hspanp
      exact this
    -- crossTau c k ≠ 0 (else c ∈ Edge k).
    have hτc : crossTau Q σ c k ≠ 0 := by
      intro hτ0
      exact hcoff (crossTau_eq_zero_span_imp_onEdge Q σ c k hτ0 hspanc)
    have hτpos := hτstab hτc
    -- forward guard agrees.
    have hfwd : (0 ≤ crossTau Q σ zp k ↔ 0 ≤ crossTau Q σ zm k) := by
      constructor
      · intro h; nlinarith [hτpos]
      · intro h; nlinarith [hτpos]
    constructor
    · rintro ⟨_, hτ⟩; exact ⟨hspanm, hfwd.mp hτ⟩
    · rintro ⟨_, hτ⟩; exact ⟨hspanp, hfwd.mpr hτ⟩
  · -- span false at zp, hence at zm: edge not crossed at either point.
    have hspanm : ¬ SpanCrossesSide Q σ zm k := fun hm => hspanp (hspan.mpr hm)
    constructor
    · rintro ⟨h, _⟩; exact absurd h hspanp
    · rintro ⟨h, _⟩; exact absurd h hspanm

/-! ## §6. The diagonal-edge flip

For the diagonal edge `d`: the span is true and stable (its two endpoints, the diagonal endpoints,
straddle the ray line since `σ.r` is non-parallel to the diagonal), while `crossTau c d = 0` and
`crossTau` has nonzero slope along `w`, so `crossTau zp d` and `crossTau zm d` have OPPOSITE nonzero
signs.  Hence the diagonal edge is crossed at exactly one of `zp`, `zm`. -/
lemma edgeCrosses_flip_diag {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q)
    (c w : Pt) (d : Fin m) {t : ℝ} (ht : 0 < t)
    (hspanp : SpanCrossesSide Q σ (c + t • w) d)
    (hspanm : SpanCrossesSide Q σ (c + (-t) • w) d)
    (hτ0 : crossTau Q σ c d = 0)
    (hslope : det2 w (Q.q (cyclicNext d) - Q.q d) ≠ 0) :
    (EdgeCrossesRay' Q σ (c + t • w) d ↔ ¬ EdgeCrossesRay' Q σ (c + (-t) • w) d) := by
  set γ : ℝ := det2 w (Q.q (cyclicNext d) - Q.q d) / crossDen Q σ d with hγ
  have hγne : γ ≠ 0 := div_ne_zero hslope (crossDen_ne_zero Q σ d)
  have eτp : crossTau Q σ (c + t • w) d = - (t * γ) := by
    rw [crossTau_step Q σ c w d t, hτ0]; ring
  have eτm : crossTau Q σ (c + (-t) • w) d = t * γ := by
    rw [crossTau_step Q σ c w d (-t), hτ0]; ring
  have htγ : t * γ ≠ 0 := mul_ne_zero (ne_of_gt ht) hγne
  unfold EdgeCrossesRay'
  rcases lt_or_gt_of_ne htγ with hneg | hpos
  · -- t*γ < 0: τ at zp = -(t*γ) > 0 (crossed); τ at zm = t*γ < 0 (not crossed).
    have hzp : 0 ≤ crossTau Q σ (c + t • w) d := by rw [eτp]; linarith
    have hzm : ¬ 0 ≤ crossTau Q σ (c + (-t) • w) d := by rw [eτm]; linarith
    constructor
    · intro _; rintro ⟨_, hτ⟩; exact hzm hτ
    · intro _; exact ⟨hspanp, hzp⟩
  · -- t*γ > 0: τ at zp = -(t*γ) < 0 (not crossed); τ at zm = t*γ > 0 (crossed).
    have hzp : ¬ 0 ≤ crossTau Q σ (c + t • w) d := by rw [eτp]; linarith
    have hzm : 0 ≤ crossTau Q σ (c + (-t) • w) d := by rw [eτm]; linarith
    constructor
    · rintro ⟨_, hτ⟩; exact absurd hτ hzp
    · intro hcon; exact absurd ⟨hspanm, hzm⟩ hcon

/-! ## §7. Assembling the singleton symmetric difference

With per-edge agreement off the diagonal and the diagonal flip, the symmetric difference of the two
crossing sets is exactly `{d}`. -/

lemma symmDiff_crossingEdges_eq_singleton {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q)
    (zp zm : Pt) (d : Fin m)
    (hnondiag : ∀ k : Fin m, k ≠ d →
      (EdgeCrossesRay' Q σ zp k ↔ EdgeCrossesRay' Q σ zm k))
    (hflip : EdgeCrossesRay' Q σ zp d ↔ ¬ EdgeCrossesRay' Q σ zm d) :
    symmDiff (CrossingEdges' Q σ zp) (CrossingEdges' Q σ zm) = {d} := by
  classical
  ext k
  rw [Finset.mem_symmDiff, Finset.mem_singleton,
    mem_crossingEdges'_iff, mem_crossingEdges'_iff]
  constructor
  · rintro (⟨hp, hm⟩ | ⟨hm, hp⟩)
    · by_contra hkd
      exact hm ((hnondiag k hkd).mp hp)
    · by_contra hkd
      exact hp ((hnondiag k hkd).mpr hm)
  · intro hkd
    subst hkd
    by_cases hp : EdgeCrossesRay' Q σ zp k
    · exact Or.inl ⟨hp, hflip.mp hp⟩
    · refine Or.inr ⟨?_, hp⟩
      by_contra hm
      exact hp (hflip.mpr hm)

/-! ## §8. The diagonal-edge facts at an interior diagonal anchor

We anchor at `c = lineMap (P.q i) (P.q j) u` with `u ∈ (0,1)`.  For a child whose diagonal edge `d`
has endpoint pair `(a, b) = (Q.q d, Q.q (cyclicNext d))` equal to a permutation of the diagonal
endpoints, the side coordinates of `a` and `b` at `c` are explicit multiples of `det2 σ.r (B-A)`
(the diagonal Cramer datum), and `crossTau c d = 0`. -/

/-- For `c` on the segment `seg a b`, the diagonal-edge crossing parameter vanishes:
`det2 (a - c) (b - a) = 0`. -/
lemma det2_sub_diag_zero (a b : Pt) {u : ℝ}
    (c : Pt) (hc : c = AffineMap.lineMap a b u) :
    det2 (a - c) (b - a) = 0 := by
  subst hc
  have hac : a - AffineMap.lineMap a b u = (-u) • (b - a) := by
    rw [AffineMap.lineMap_apply_module]
    ext l; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [hac, det2_smul_left, det2_self, mul_zero]

/-- `side r c v = det2 r (v - c)` for `c` on `seg A B`, written with the lineMap parameter. -/
lemma side_lineMap_endpoint (r A B : Pt) {u : ℝ} :
    side r (AffineMap.lineMap A B u) A = (-u) * det2 r (B - A) ∧
    side r (AffineMap.lineMap A B u) B = (1 - u) * det2 r (B - A) := by
  constructor
  · unfold side
    have : A - AffineMap.lineMap A B u = (-u) • (B - A) := by
      rw [AffineMap.lineMap_apply_module]
      ext l; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [this, det2_smul_right]
  · unfold side
    have : B - AffineMap.lineMap A B u = (1 - u) • (B - A) := by
      rw [AffineMap.lineMap_apply_module]
      ext l; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [this, det2_smul_right]

/-- **The diagonal-edge data at an interior anchor.**  For a child whose diagonal edge `d` has
endpoints `Q.q d = E1`, `Q.q (cyclicNext d) = E2`, and an anchor `c = lineMap E1 E2 v` with
`v ∈ (0,1)` (interior of the diagonal), with `σ.r` non-parallel to `E2 - E1`: the diagonal `crossTau`
vanishes and the span is true. -/
lemma diag_edge_data {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q) (d : Fin m)
    {E1 E2 : Pt} (hd : Q.q d = E1) (hnd : Q.q (cyclicNext d) = E2)
    (hpar : det2 σ.r (E2 - E1) ≠ 0) {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) 1)
    {c : Pt} (hc : c = AffineMap.lineMap E1 E2 v) :
    crossTau Q σ c d = 0 ∧ SpanCrossesSide Q σ c d := by
  constructor
  · -- crossTau = det2 (Q.q d - c)(Q.q (next d) - Q.q d)/crossDen, numerator zero on the segment.
    unfold crossTau
    rw [hd, hnd]
    have hzero : det2 (E1 - c) (E2 - E1) = 0 := det2_sub_diag_zero E1 E2 c hc
    rw [hzero, zero_div]
  · -- span: side at E1 = (1-v)·det2 σ.r (E2-E1), side at E2 = -v·... wait, use side_lineMap_endpoint.
    unfold SpanCrossesSide
    rw [hd, hnd, hc]
    obtain ⟨hs1, hs2⟩ := side_lineMap_endpoint σ.r E1 E2 (u := v)
    rw [hs1, hs2]
    -- side at E1 is `(-v)·det2 σ.r (E2-E1)`, at E2 is `(1-v)·det2 σ.r (E2-E1)`; opposite signs.
    have hv0 := hv.1
    have hv1 := hv.2
    rw [span_iff_opp_sign]
    · -- product `(-v)(1-v)·D² < 0`.
      have hD2 : 0 < det2 σ.r (E2 - E1) ^ 2 := by positivity
      have : -v * det2 σ.r (E2 - E1) * ((1 - v) * det2 σ.r (E2 - E1))
          = - (v * (1 - v)) * det2 σ.r (E2 - E1) ^ 2 := by ring
      rw [this]
      have hvv : 0 < v * (1 - v) := mul_pos hv0 (by linarith)
      nlinarith [hD2, hvv]
    · -- `(-v)·D ≠ 0`.
      have : (0:ℝ) < v := hv0
      exact mul_ne_zero (by linarith) hpar
    · -- `(1-v)·D ≠ 0`.
      exact mul_ne_zero (by linarith [hv1]) hpar

/-! ## §8.5. Per-child threshold: a single `δ_Q > 0` dominating all amplitudes

Collecting the per-vertex side thresholds and the per-nondiagonal-edge `crossTau` thresholds (only
those with nonzero anchor value) into one finite set, its minimum `δ_Q > 0` dominates every required
amplitude bound: for `0 < t < δ_Q`, both `hsguard` and `hτbound` hold. -/
lemma exists_child_threshold {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q)
    (c w : Pt) (d : Fin m) (hgen : ∀ k : Fin m, side σ.r c (Q.q k) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (∀ k : Fin m, |t * det2 σ.r w| < |side σ.r c (Q.q k)|) ∧
      (∀ k : Fin m, k ≠ d → crossTau Q σ c k ≠ 0 →
        |t * (det2 w (Q.q (cyclicNext k) - Q.q k) / crossDen Q σ k)| < |crossTau Q σ c k|) := by
  classical
  -- Side thresholds (all positive, since every side value is nonzero).
  let sthr : Fin m → ℝ := fun k => |side σ.r c (Q.q k)| / (|det2 σ.r w| + 1)
  -- crossTau thresholds, only for edges with nonzero anchor value.
  let tthr : Fin m → ℝ := fun k =>
    |crossTau Q σ c k| / (|det2 w (Q.q (cyclicNext k) - Q.q k) / crossDen Q σ k| + 1)
  let S : Finset ℝ :=
    (Finset.univ.image sthr) ∪
      ((Finset.univ.filter fun k => crossTau Q σ c k ≠ 0).image tthr)
  have hmpos : 0 < m := by have := Q.hthree; omega
  have hsthr_mem : ∀ k : Fin m, sthr k ∈ S := fun k =>
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
  have htthr_mem : ∀ k : Fin m, crossTau Q σ c k ≠ 0 → tthr k ∈ S := fun k hk =>
    Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩, rfl⟩)
  have hSne : S.Nonempty := ⟨sthr ⟨0, hmpos⟩, hsthr_mem ⟨0, hmpos⟩⟩
  -- every element of S is positive.
  have hSpos : ∀ x ∈ S, 0 < x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      have h1 : 0 < |side σ.r c (Q.q k)| := abs_pos.mpr (hgen k)
      show 0 < |side σ.r c (Q.q k)| / (|det2 σ.r w| + 1)
      positivity
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_filter] at hk
      have h1 : 0 < |crossTau Q σ c k| := abs_pos.mpr hk.2
      show 0 < |crossTau Q σ c k| / (|det2 w (Q.q (cyclicNext k) - Q.q k) / crossDen Q σ k| + 1)
      positivity
  refine ⟨S.min' hSne, hSpos _ (S.min'_mem hSne), fun t ht htlt => ⟨?_, ?_⟩⟩
  · intro k
    have hθ : S.min' hSne ≤ sthr k := Finset.min'_le S _ (hsthr_mem k)
    exact abs_mul_lt_of_lt_threshold (hgen k) ht (lt_of_lt_of_le htlt hθ)
  · intro k hkd hτc
    have hθ : S.min' hSne ≤ tthr k := Finset.min'_le S _ (htthr_mem k hτc)
    exact abs_mul_lt_of_lt_threshold hτc ht (lt_of_lt_of_le htlt hθ)

/-! ## §8.7. Ray-generic anchors are cofinite on the diagonal

`side σ.r (lineMap A B u) v` is affine in `u` with slope `- det2 σ.r (B - A)`.  When `σ.r` is
non-parallel to `B - A` (the diagonal edge vector), this slope is nonzero, so the vertex-on-ray-line
condition holds at only one `u`.  Over finitely many child vertices, only finitely many `u` are
bad. -/

/-- `side σ.r (lineMap A B u) v` as an affine function of `u`. -/
lemma side_lineMap_affine (r A B v : Pt) (u : ℝ) :
    side r (AffineMap.lineMap A B u) v = det2 r (v - A) - u * det2 r (B - A) := by
  unfold side
  have hsub : v - AffineMap.lineMap A B u = (v - A) - u • (B - A) := by
    rw [AffineMap.lineMap_apply_module]
    ext l; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [hsub, det2_sub_right, det2_smul_right]

/-- The finite bad-`u` set of anchors where some child vertex is on the ray line; off it, every child
vertex is off the ray line through `lineMap A B u`. -/
lemma exists_anchor_bad {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q)
    (A B : Pt) (hslope : det2 σ.r (B - A) ≠ 0) :
    ∃ bad : Finset ℝ, ∀ u : ℝ, u ∉ bad →
      ∀ k : Fin m, side σ.r (AffineMap.lineMap A B u) (Q.q k) ≠ 0 := by
  classical
  refine ⟨Finset.univ.image (fun k => det2 σ.r (Q.q k - A) / det2 σ.r (B - A)),
    fun u hub k hz => hub ?_⟩
  rw [side_lineMap_affine] at hz
  refine Finset.mem_image.mpr ⟨k, Finset.mem_univ k, ?_⟩
  field_simp
  linarith [hz]

/-! ## §8.8. Neighbourhood box capture around the midpoint

`Φ (u, s) = lineMap A B u + s • w` is continuous and sends `(1/2, 0)` to `diagMid`, so for any nhds
`U` of `diagMid` there is `η > 0` such that `|u - 1/2| < η` and `|s| < η` keep `Φ (u, s)` in `U`. -/
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
lemma exists_box_in_nhds (A B w : Pt) {U : Set Pt}
    (hU : U ∈ nhds (AffineMap.lineMap A B (1 / 2 : ℝ))) :
    ∃ η : ℝ, 0 < η ∧ ∀ u s : ℝ, |u - 1 / 2| < η → |s| < η →
      AffineMap.lineMap A B u + s • w ∈ U := by
  have hg : Continuous (fun s : ℝ => s • w) := continuous_id.smul continuous_const
  have hf : Continuous (fun u : ℝ => AffineMap.lineMap A B u) := AffineMap.lineMap_continuous
  have hcont : Continuous (fun p : ℝ × ℝ => AffineMap.lineMap A B p.1 + p.2 • w) :=
    (hf.comp continuous_fst).add (hg.comp continuous_snd)
  have hpre : (fun p : ℝ × ℝ => AffineMap.lineMap A B p.1 + p.2 • w) ⁻¹' U ∈ nhds ((1 / 2, 0) : ℝ × ℝ) := by
    apply hcont.continuousAt.preimage_mem_nhds
    show U ∈ nhds (AffineMap.lineMap A B (1 / 2 : ℝ) + (0 : ℝ) • w)
    rw [zero_smul, add_zero]; exact hU
  rw [Metric.mem_nhds_iff] at hpre
  obtain ⟨η, hη, hball⟩ := hpre
  refine ⟨η / 2, by linarith, fun u s hu hs => ?_⟩
  have hmem : ((u, s) : ℝ × ℝ) ∈ Metric.ball (1 / 2, 0) η := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [sub_zero]
    rw [max_lt_iff]; constructor <;> linarith
  have := hball hmem
  simpa using this

/-! ## §9. The per-child singleton symmetric difference at a good anchor

Given a generic interior diagonal anchor `c`, a transverse direction `w`, and a small `t` whose
amplitude is dominated by every vertex side-coordinate (`hsguard`) and by every non-diagonal
`crossTau` (`hτbound`), with the diagonal datum `crossTau c d = 0`, span true, and nonzero slope, the
two crossing sets at `zp = c+t•w`, `zm = c-t•w` differ by exactly `{d}`. -/
lemma per_child_symmDiff {P : StrictSimplePolygon n} {ρ : RayDirection P} {i j : Fin n}
    (h : IsDiagonal' P ρ i j) {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q)
    (d : Fin m) (c w : Pt) {t : ℝ} (ht : 0 < t)
    (hvert : ∀ a : Fin m, ∃ b : Fin n, Q.q a = P.q b)
    (hdiag_edge : Edge Q.q d = seg (P.q i) (P.q j))
    (hc_open : c ∈ openSegment ℝ (P.q i) (P.q j))
    (hsguard : ∀ k : Fin m, |t * det2 σ.r w| < |side σ.r c (Q.q k)|)
    (hτbound : ∀ k : Fin m, k ≠ d → crossTau Q σ c k ≠ 0 →
      |t * (det2 w (Q.q (cyclicNext k) - Q.q k) / crossDen Q σ k)| < |crossTau Q σ c k|)
    (hτdiag0 : crossTau Q σ c d = 0)
    (hslope_d : det2 w (Q.q (cyclicNext d) - Q.q d) ≠ 0)
    (hspanc_d : SpanCrossesSide Q σ c d) :
    symmDiff (CrossingEdges' Q σ (c + t • w)) (CrossingEdges' Q σ (c + (-t) • w)) = {d} := by
  set zp := c + t • w with hzp
  set zm := c + (-t) • w with hzm
  -- Diagonal-edge span is true at zp and zm (the two diagonal endpoints are sign-stable vertices).
  have hspanp_d : SpanCrossesSide Q σ zp d :=
    (span_eq_of_sign_stable Q σ zp c d
      (side_sign_stable_anchor σ.r c w (Q.q d) (hsguard d))
      (side_sign_stable_anchor σ.r c w (Q.q (cyclicNext d)) (hsguard (cyclicNext d)))).mpr hspanc_d
  have habs : |(-t) * det2 σ.r w| = |t * det2 σ.r w| := by
    rw [neg_mul, abs_neg]
  have hspanm_d : SpanCrossesSide Q σ zm d := by
    have key := span_eq_of_sign_stable Q σ zm c d
      (side_sign_stable_anchor σ.r c w (Q.q d) (t := -t) (by rw [habs]; exact hsguard d))
      (side_sign_stable_anchor σ.r c w (Q.q (cyclicNext d)) (t := -t)
        (by rw [habs]; exact hsguard (cyclicNext d)))
    exact key.mpr hspanc_d
  -- The diagonal flip.
  have hflip := edgeCrosses_flip_diag Q σ c w d ht hspanp_d hspanm_d hτdiag0 hslope_d
  -- Non-diagonal stability.
  have hnondiag : ∀ k : Fin m, k ≠ d →
      (EdgeCrossesRay' Q σ zp k ↔ EdgeCrossesRay' Q σ zm k) := by
    intro k hkd
    have hak : 0 < side σ.r zp (Q.q k) * side σ.r zm (Q.q k) :=
      side_sign_stable σ.r c w (Q.q k) (hsguard k)
    have hbk : 0 < side σ.r zp (Q.q (cyclicNext k)) * side σ.r zm (Q.q (cyclicNext k)) :=
      side_sign_stable σ.r c w (Q.q (cyclicNext k)) (hsguard (cyclicNext k))
    have hac : 0 < side σ.r zp (Q.q k) * side σ.r c (Q.q k) :=
      side_sign_stable_anchor σ.r c w (Q.q k) (hsguard k)
    have hbc : 0 < side σ.r zp (Q.q (cyclicNext k)) * side σ.r c (Q.q (cyclicNext k)) :=
      side_sign_stable_anchor σ.r c w (Q.q (cyclicNext k)) (hsguard (cyclicNext k))
    have hcoff : c ∉ Edge Q.q k :=
      openDiag_off_nondiag_child_edge h Q d hvert hdiag_edge hc_open hkd
    have hτstab : crossTau Q σ c k ≠ 0 → 0 < crossTau Q σ zp k * crossTau Q σ zm k := by
      intro hτc
      exact crossTau_sign_stable Q σ c w k (hτbound k hkd hτc)
    exact edgeCrosses_eq_nondiag Q σ c zp zm k hak hbk hac hbc hcoff hτstab
  exact symmDiff_crossingEdges_eq_singleton Q σ zp zm d hnondiag hflip

/-! ## §10. The straddle datum

We assemble the selection: a transverse direction `w = sweepDir ρ.r λ` (non-parallel to every edge of
`P`, `L`, `R`), a ray-generic interior diagonal anchor `c = lineMap (P.q i) (P.q j) u` near `diagMid`,
and a small `t > 0` below the per-child amplitude thresholds and avoiding the off-boundary bad-`t`
sets.  `per_child_symmDiff` then lands the singleton symmetric difference on each child, and
`exists_badt_polygon` lands the off-boundary facts. -/

/-- **`DiagTubeStraddle` (the named missing primitive), DISCHARGED.** -/
theorem diagTubeStraddle {P : StrictSimplePolygon n} {ρ : RayDirection P} {i j : Fin n}
    (h : IsDiagonal' P ρ i j) (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax)) :
    ZinanCh36DiagTube.DiagTubeStraddle h lax rax σL σR := by
  classical
  intro U hU
  set dL : Fin (PolygonDiagonal.leftLength i j) := leftLastIndex i j with hdL
  set dR : Fin (PolygonDiagonal.rightLength i j) := rightLastIndex i j with hdR
  have hij : i ≠ j := h.1
  -- Child vertices are parent vertices.
  have hvertL : ∀ a : Fin (PolygonDiagonal.leftLength i j),
      ∃ b : Fin n, (buildLeftPoly h lax).q a = P.q b :=
    fun a => ⟨leftIndex i j a, by rw [buildLeftPoly_q]; rfl⟩
  have hvertR : ∀ a : Fin (PolygonDiagonal.rightLength i j),
      ∃ b : Fin n, (buildRightPoly h rax).q a = P.q b :=
    fun a => ⟨rightIndex i j a, by rw [buildRightPoly_q]; rfl⟩
  -- Diagonal closing-edge facts.
  have hLedge : Edge (buildLeftPoly h lax).q dL = seg (P.q i) (P.q j) := by
    rw [buildLeftPoly_q, hdL]; exact diag_eq_left_closing_edge hij
  have hRedge : Edge (buildRightPoly h rax).q dR = seg (P.q i) (P.q j) := by
    rw [buildRightPoly_q, hdR]; exact diag_eq_right_closing_edge hij
  -- Diagonal-edge endpoint identifications.
  have hLqd : (buildLeftPoly h lax).q dL = P.q j := by
    rw [buildLeftPoly_q, hdL]
    show subpolygonLeftTuple P i j (leftLastIndex i j) = P.q j
    unfold subpolygonLeftTuple
    rw [leftIndex_leftLastIndex]
  have hLqnd : (buildLeftPoly h lax).q (cyclicNext dL) = P.q i := by
    rw [buildLeftPoly_q, hdL]
    show subpolygonLeftTuple P i j (cyclicNext (leftLastIndex i j)) = P.q i
    unfold subpolygonLeftTuple
    rw [cyclicNext_leftLastIndex hij, leftIndex_zero hij]
  have hRqd : (buildRightPoly h rax).q dR = P.q i := by
    rw [buildRightPoly_q, hdR]
    show subpolygonRightTuple P i j (rightLastIndex i j) = P.q i
    unfold subpolygonRightTuple
    rw [rightIndex_rightLastIndex]
  have hRqnd : (buildRightPoly h rax).q (cyclicNext dR) = P.q j := by
    rw [buildRightPoly_q, hdR]
    show subpolygonRightTuple P i j (cyclicNext (rightLastIndex i j)) = P.q j
    unfold subpolygonRightTuple
    rw [cyclicNext_rightLastIndex hij, rightIndex_zero hij]
  -- `σ.r` non-parallel to the diagonal edge of each child.
  have hLpar : det2 σL.r (P.q i - P.q j) ≠ 0 := by
    have := σL.no_edge_parallel dL; rw [hLqd, hLqnd] at this; exact this
  have hRpar : det2 σR.r (P.q j - P.q i) ≠ 0 := by
    have := σR.no_edge_parallel dR; rw [hRqd, hRqnd] at this; exact this
  -- §1. Transverse direction `w = sweepDir ρ.r λ`, non-parallel to every edge of P, L, R.
  obtain ⟨badP, hbadP⟩ := exists_lambda_transverse_family (Finset.univ) ρ.r ρ.r_ne_zero
    (fun k => P.q (cyclicNext k) - P.q k) (fun k _ => edgeVec_ne_zero P k)
  obtain ⟨badL, hbadL⟩ := exists_lambda_transverse_family (Finset.univ) ρ.r ρ.r_ne_zero
    (fun k => (buildLeftPoly h lax).q (cyclicNext k) - (buildLeftPoly h lax).q k)
    (fun k _ => edgeVec_ne_zero (buildLeftPoly h lax) k)
  obtain ⟨badR, hbadR⟩ := exists_lambda_transverse_family (Finset.univ) ρ.r ρ.r_ne_zero
    (fun k => (buildRightPoly h rax).q (cyclicNext k) - (buildRightPoly h rax).q k)
    (fun k _ => edgeVec_ne_zero (buildRightPoly h rax) k)
  obtain ⟨lam, hlam⟩ := (badP ∪ badL ∪ badR).exists_notMem
  rw [Finset.mem_union, Finset.mem_union, not_or, not_or] at hlam
  obtain ⟨⟨hlamP, hlamL⟩, hlamR⟩ := hlam
  set w : Pt := sweepDir ρ.r lam with hwdef
  have hwP : ∀ k : Fin n, det2 (P.q (cyclicNext k) - P.q k) w ≠ 0 := fun k => by
    have := hbadP lam hlamP k (Finset.mem_univ k)
    rw [det2_antisymm]; simpa using neg_ne_zero.mpr this
  have hwL : ∀ k, det2 ((buildLeftPoly h lax).q (cyclicNext k) - (buildLeftPoly h lax).q k) w ≠ 0 :=
    fun k => by
      have := hbadL lam hlamL k (Finset.mem_univ k)
      rw [det2_antisymm]; simpa using neg_ne_zero.mpr this
  have hwR : ∀ k,
      det2 ((buildRightPoly h rax).q (cyclicNext k) - (buildRightPoly h rax).q k) w ≠ 0 :=
    fun k => by
      have := hbadR lam hlamR k (Finset.mem_univ k)
      rw [det2_antisymm]; simpa using neg_ne_zero.mpr this
  have hrw : det2 ρ.r w ≠ 0 := ne_of_gt (det2_r_sweepDir_pos ρ.r_ne_zero lam)
  -- Diagonal-edge slopes for `w`.
  have hslopeL :
      det2 w ((buildLeftPoly h lax).q (cyclicNext dL) - (buildLeftPoly h lax).q dL) ≠ 0 := by
    rw [det2_antisymm]; simpa using neg_ne_zero.mpr (hwL dL)
  have hslopeR :
      det2 w ((buildRightPoly h rax).q (cyclicNext dR) - (buildRightPoly h rax).q dR) ≠ 0 := by
    rw [det2_antisymm]; simpa using neg_ne_zero.mpr (hwR dR)
  -- §2. nhds box around `diagMid = lineMap (P.q i)(P.q j)(1/2)`.
  have hUmid : U ∈ nhds (AffineMap.lineMap (P.q i) (P.q j) (1 / 2 : ℝ)) := hU
  obtain ⟨η, hη, hbox⟩ := exists_box_in_nhds (P.q i) (P.q j) w hUmid
  -- §3. Ray-generic anchor `u ∈ (1/2 - η, 1/2 + η) ∩ (0,1)`.
  have hsubneg : ∀ a b : Pt, b - a = (-1 : ℝ) • (a - b) := by
    intro a b; ext l; simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hLparB : det2 σL.r (P.q j - P.q i) ≠ 0 := by
    rw [hsubneg (P.q i) (P.q j), det2_smul_right]
    simpa using hLpar
  have hRparB : det2 σR.r (P.q i - P.q j) ≠ 0 := by
    rw [hsubneg (P.q j) (P.q i), det2_smul_right]
    simpa using hRpar
  obtain ⟨badUL, hbadUL⟩ := exists_anchor_bad (buildLeftPoly h lax) σL (P.q i) (P.q j) hLparB
  obtain ⟨badUR, hbadUR⟩ := exists_anchor_bad (buildRightPoly h rax) σR (P.q i) (P.q j) hRpar
  -- the open interval to pick `u` from.
  set lo : ℝ := max (1 / 2 - η) 0 with hlo
  set hi : ℝ := min (1 / 2 + η) 1 with hhi
  have hlohi : lo < hi := by
    rw [hlo, hhi]; rw [max_lt_iff]; refine ⟨lt_min (by linarith) (by linarith),
      lt_min (by linarith) (by norm_num)⟩
  have hinfU : (Set.Ioo lo hi).Infinite := Set.Ioo_infinite hlohi
  obtain ⟨u, huio, hubad⟩ : ∃ u ∈ Set.Ioo lo hi, u ∉ (badUL ∪ badUR) := by
    have hns : ¬ (Set.Ioo lo hi ⊆ ((badUL ∪ badUR : Finset ℝ) : Set ℝ)) :=
      fun hsub => hinfU ((badUL ∪ badUR).finite_toSet.subset hsub)
    rw [Set.not_subset] at hns; obtain ⟨u, hu1, hu2⟩ := hns; exact ⟨u, hu1, hu2⟩
  rw [Finset.mem_union, not_or] at hubad
  set c : Pt := AffineMap.lineMap (P.q i) (P.q j) u with hcdef
  -- `u ∈ (0,1)` and `|u - 1/2| < η`.
  have hu01 : u ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · have := huio.1; rw [hlo] at this; exact lt_of_le_of_lt (le_max_right _ _) this
    · have := huio.2; rw [hhi] at this; exact lt_of_lt_of_le this (min_le_right _ _)
  have huη : |u - 1 / 2| < η := by
    rw [abs_lt]; constructor
    · have := huio.1; rw [hlo] at this; have := lt_of_le_of_lt (le_max_left _ _) this; linarith
    · have := huio.2; rw [hhi] at this; have := lt_of_lt_of_le this (min_le_left _ _); linarith
  -- `c` is on the open diagonal segment.
  have hc_open : c ∈ openSegment ℝ (P.q i) (P.q j) := by
    rw [hcdef, openSegment_eq_image_lineMap]; exact ⟨u, hu01, rfl⟩
  -- Ray-genericity at `c`.
  have hgenL : ∀ k, side σL.r c ((buildLeftPoly h lax).q k) ≠ 0 := hbadUL u hubad.1
  have hgenR : ∀ k, side σR.r c ((buildRightPoly h rax).q k) ≠ 0 := hbadUR u hubad.2
  -- Diagonal-edge data at `c` for each child.
  -- For L: E1 = P.q j, E2 = P.q i; `det2 σL.r (E2 - E1) = det2 σL.r (P.q i - P.q j) = hLpar`.
  obtain ⟨hτ0L, hspancL⟩ := diag_edge_data (buildLeftPoly h lax) σL dL hLqd hLqnd hLpar
    (v := 1 - u) ⟨by linarith [hu01.2], by linarith [hu01.1]⟩
    (by show c = AffineMap.lineMap (P.q j) (P.q i) (1 - u)
        rw [hcdef]
        rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
        ext l; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring)
  -- For R: E1 = P.q i, E2 = P.q j; `det2 σR.r (E2 - E1) = det2 σR.r (P.q j - P.q i) = hRpar`.
  obtain ⟨hτ0R, hspancR⟩ := diag_edge_data (buildRightPoly h rax) σR dR hRqd hRqnd hRpar
    (v := u) hu01 (by show c = AffineMap.lineMap (P.q i) (P.q j) u; rw [hcdef])
  -- §4. per-child thresholds.
  obtain ⟨δL, hδLpos, hδL⟩ := exists_child_threshold (buildLeftPoly h lax) σL c w dL hgenL
  obtain ⟨δR, hδRpos, hδR⟩ := exists_child_threshold (buildRightPoly h rax) σR c w dR hgenR
  -- §5. off-boundary bad-t sets at `c` (for P, L, R), valid for both signs.
  obtain ⟨btP, hbtP⟩ := exists_badt_polygon ρ.r P c w hwP hrw
  obtain ⟨btL, hbtL⟩ := exists_badt_polygon ρ.r (buildLeftPoly h lax) c w hwL hrw
  obtain ⟨btR, hbtR⟩ := exists_badt_polygon ρ.r (buildRightPoly h rax) c w hwR hrw
  set Bneg : Finset ℝ := (btP ∪ btL ∪ btR).image (fun t => -t) with hBneg
  set B : Finset ℝ := btP ∪ btL ∪ btR ∪ Bneg with hB
  -- §6. pick `t ∈ (0, min η δL δR)` avoiding `B`.
  set ub : ℝ := min η (min δL δR) with hub
  have hubpos : 0 < ub := by rw [hub]; exact lt_min hη (lt_min hδLpos hδRpos)
  have hinfT : (Set.Ioo (0 : ℝ) ub).Infinite := Set.Ioo_infinite hubpos
  obtain ⟨t, htio, htB⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) ub, t ∉ B := by
    have hns : ¬ (Set.Ioo (0 : ℝ) ub ⊆ (B : Set ℝ)) :=
      fun hsub => hinfT (B.finite_toSet.subset hsub)
    rw [Set.not_subset] at hns; obtain ⟨t, ht1, ht2⟩ := hns; exact ⟨t, ht1, ht2⟩
  have ht0 : 0 < t := htio.1
  have htub : t < ub := htio.2
  -- `t` and `-t` avoid the per-polygon off-boundary bad sets.
  have htnotB : t ∉ (btP ∪ btL ∪ btR) := fun hmem => htB (by rw [hB, Finset.mem_union]; exact Or.inl hmem)
  have htnegnotB : -t ∉ (btP ∪ btL ∪ btR) := by
    intro hmem
    -- if `-t ∈ btP∪btL∪btR` then `t ∈ Bneg` (image of negation), contradicting `t ∉ B`.
    apply htB; rw [hB, Finset.mem_union]; right
    rw [hBneg, Finset.mem_image]; exact ⟨-t, hmem, by ring⟩
  rw [Finset.mem_union, Finset.mem_union, not_or, not_or] at htnotB htnegnotB
  obtain ⟨⟨htP, htL⟩, htR⟩ := htnotB
  obtain ⟨⟨htnP, htnL⟩, htnR⟩ := htnegnotB
  -- thresholds at this `t`.
  have httη : t < η := lt_of_lt_of_le htub (by rw [hub]; exact min_le_left _ _)
  have httL : t < δL := lt_of_lt_of_le htub (by rw [hub]; exact le_trans (min_le_right _ _) (min_le_left _ _))
  have httR : t < δR := lt_of_lt_of_le htub (by rw [hub]; exact le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hsguardL, hτboundL⟩ := hδL t ht0 httL
  obtain ⟨hsguardR, hτboundR⟩ := hδR t ht0 httR
  -- The two points.
  refine ⟨c + t • w, c + (-t) • w, dL, dR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- zp ∈ U
    rw [hcdef]; exact hbox u t huη (by rw [abs_of_pos ht0]; exact httη)
  · -- zm ∈ U
    rw [hcdef]; exact hbox u (-t) huη (by rw [abs_neg, abs_of_pos ht0]; exact httη)
  · exact (hbtP t htP).1
  · exact (hbtP (-t) htnP).1
  · exact (hbtL t htL).1
  · exact (hbtL (-t) htnL).1
  · exact (hbtR t htR).1
  · exact (hbtR (-t) htnR).1
  · -- left symmDiff
    exact per_child_symmDiff h (buildLeftPoly h lax) σL dL c w ht0 hvertL hLedge hc_open
      hsguardL hτboundL hτ0L hslopeL hspancL
  · -- right symmDiff
    exact per_child_symmDiff h (buildRightPoly h rax) σR dR c w ht0 hvertR hRedge hc_open
      hsguardR hτboundR hτ0R hslopeR hspancR

/-! ## §11. Payoff: the unconditional sibling theorems

With `diagTubeStraddle` discharging the last named primitive, the conditional master bricks of
`ZinanCh36DiagTube` become UNCONDITIONAL.  We instantiate them. -/

/-- **Two-sided diagonal tube points (unconditional).**  Sibling of
`ZinanCh36DiagTube.exists_two_sided_diag_points` with the straddle hypothesis discharged. -/
theorem exists_two_sided_diag_points_final {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j) (lax : LeftStrictAxioms P i j)
    (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax)) :
    ∃ zp zm : Pt,
      ¬ OnBoundary P zp ∧ ¬ OnBoundary P zm ∧
      ¬ OnBoundary (buildLeftPoly h lax) zp ∧ ¬ OnBoundary (buildLeftPoly h lax) zm ∧
      ¬ OnBoundary (buildRightPoly h rax) zp ∧ ¬ OnBoundary (buildRightPoly h rax) zm ∧
      PolygonWinding.windCross P ρ zp = PolygonWinding.windCross P ρ (diagMid P i j) ∧
      PolygonWinding.windCross P ρ zm = PolygonWinding.windCross P ρ (diagMid P i j) ∧
      PolygonWinding.windCross (buildLeftPoly h lax) σL zp
          ≠ PolygonWinding.windCross (buildLeftPoly h lax) σL zm ∧
      PolygonWinding.windCross (buildRightPoly h rax) σR zp
          ≠ PolygonWinding.windCross (buildRightPoly h rax) σR zm :=
  ZinanCh36DiagTube.exists_two_sided_diag_points h lax rax σL σR
    (diagTubeStraddle h lax rax σL σR)

/-- **Sibling sign synchronization (brick 7), UNCONDITIONAL.**  At an `IsDiagonal'` split with child
ray packages along the common parent direction, the two child signs coincide — with the
diagonal-tube straddle primitive discharged by `diagTubeStraddle`. -/
theorem split_child_signs_eq_final {P : StrictSimplePolygon n} {ρ : RayDirection P} {i j : Fin n}
    (h : IsDiagonal' P ρ i j) (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    {σL : RayDirection (buildLeftPoly h lax)} {σR : RayDirection (buildRightPoly h rax)}
    (hLr : σL.r = ρ.r) (hRr : σR.r = ρ.r) {sL sR : ℤ}
    (HVL : ZinanCh36SignSync.RayWindValuesWithSign (buildLeftPoly h lax) σL sL)
    (HVR : ZinanCh36SignSync.RayWindValuesWithSign (buildRightPoly h rax) σR sR) :
    sL = sR :=
  ZinanCh36DiagTube.split_child_signs_eq h lax rax hLr hRr HVL HVR
    (diagTubeStraddle h lax rax σL σR)

end

end ProofsInTheBook.ZinanCh36Straddle

/-! ## Axiom audit (clean-3 expected: `propext`, `Classical.choice`, `Quot.sound`) -/

#print axioms ProofsInTheBook.ZinanCh36Straddle.diagTubeStraddle
#print axioms ProofsInTheBook.ZinanCh36Straddle.exists_two_sided_diag_points_final
#print axioms ProofsInTheBook.ZinanCh36Straddle.split_child_signs_eq_final
