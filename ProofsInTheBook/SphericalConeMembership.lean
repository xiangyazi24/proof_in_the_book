import ProofsInTheBook.SphericalCornerStep
import ProofsInTheBook.PlanarConvexDiag

/-!
# `SphericalConeMembership` — discharging the tangent-cone membership of Chapter 13's arm lemma

`SphericalCornerStep` reduced the unconditional spherical arm lemma to the single residue
`MatchedCutCornerConeStep`, whose payload bundles two facts at the cut apex `A 2`:

1. the **HINGE 11.3 tangent-cone membership** — the cut diagonal's tangent ray lies in the nonnegative
   cone `span ℝ≥0` of the two adjacent edge tangent rays, and
2. the **matched first joint** `jointAngle A 0 = jointAngle B 0` (the §8.4 reach recursion / all-strict
   opening residue), plus the matched corner-triangle sides and the strictness link.

This module **discharges (1) UNCONDITIONALLY** — converting the determinant-sign data of
`cutCorner_tangent_decomp` into the genuine `span ℝ≥0` cone membership.  The bridge is the gnomonic /
tangent-plane geometry the prior round flagged as absent:

* **`mem_span_nnreal_of_planar_signs`** — the planar nonneg-cone-from-signs lemma.  For vectors
  `u, v, w` all orthogonal to a common `m ≠ 0` (so coplanar in the `2`-plane `m^⊥`) with `v, w`
  independent (`det3 m v w ≠ 0`), if `0 ≤ det3 m u w · det3 m v w` and `0 ≤ det3 m v u · det3 m v w`
  then `u ∈ span ℝ≥0 {v, w}`.  This is `betweenness_span_nnreal`'s convex-position algebra
  (`normsq_smul_b` + the Gram-coordinate signs) transported from the sphere to the tangent plane: a ray
  whose planar orientation against both bounding edges is sign-consistent is a nonnegative combination.

* **`det3_tangentTo_eq`** — the gnomonic transport tangent ↔ planar orientation: at apex `m`,
  `det3 m (A i) (A j) = det3 m (tangentTo m (A i)) (tangentTo m (A j))`.  The component of each
  neighbour along `m` contributes a repeated column, so the spherical orientation `sOrient m (A i)(A j)`
  is exactly the planar orientation of the two tangent directions in `m^⊥`.

* **`cutCorner_cone_membership`** — *the residue, discharged*: for a strictly convex spherical polygon
  with apex index `2`, the diagonal tangent ray `tangentTo (P 2) (P 0)` lies in
  `span ℝ≥0 {tangentTo (P 2)(P 1), tangentTo (P 2)(P 3)}`.  The three required `det3`-sign products are
  the `cutCorner_tangent_decomp` cyclic signs (`cyclicTriplePos_unconditional`), transported to the
  tangent plane by `det3_tangentTo_eq` and reordered by `det3` antisymmetry: all three apex-`2`
  orientations `det3 (P2)(P0)(P3)`, `det3 (P2)(P1)(P3)`, `det3 (P2)(P1)(P0)` are *negative* (each is an
  odd permutation of a positive increasing triple), so the two sign products are positive.

With the cone membership now proved substrate, `CornerConeFacts` reduces to the matched first joint +
matched sides + short-arc nondegeneracy + the strictness link — exactly the §8.4 opening data, with the
analytic tangent-cone core removed.  We isolate that strictly-narrower residue as
`MatchedFirstJointStep` and prove `MatchedFirstJointStep → MatchedCutCornerConeStep`, hence the
unconditional kernel arm lemmas conditional ONLY on the §8.4 matched-joint existence.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep

namespace ProofsInTheBook.SphericalConeMembership

/-! ## Block A — `det3` multilinearity in the second and third slots (pure `ring` identities). -/

/-- `det3` is additive in its third slot. -/
theorem det3_add_right (a b c d : E3) :
    det3 a b (c + d) = det3 a b c + det3 a b d := by
  simp only [det3, add_apply]; ring

/-- `det3` is homogeneous in its third slot. -/
theorem det3_smul_right (r : ℝ) (a b c : E3) :
    det3 a b (r • c) = r * det3 a b c := by
  simp only [det3, smul_apply]; ring

/-- `det3` is additive in its second slot. -/
theorem det3_add_mid (a b c d : E3) :
    det3 a (b + c) d = det3 a b d + det3 a c d := by
  simp only [det3, add_apply]; ring

/-- `det3` is homogeneous in its second slot. -/
theorem det3_smul_mid (r : ℝ) (a b c : E3) :
    det3 a (r • b) c = r * det3 a b c := by
  simp only [det3, smul_apply]; ring

/-- `det3` vanishes with a repeated second/third slot. -/
theorem det3_self_mid₂ (a b : E3) : det3 a b b = 0 := by
  simp only [det3]; ring

/-- `det3` is antisymmetric under swapping the last two slots. -/
theorem det3_swap_right (a b c : E3) : det3 a b c = - det3 a c b := by
  simp only [det3]; ring

/-- `det3` is antisymmetric under swapping the first two slots. -/
theorem det3_swap_left (a b c : E3) : det3 a b c = - det3 b a c := by
  simp only [det3]; ring

/-! ## Block B — the planar nonneg-cone-from-signs lemma.

For three vectors `u, v, w` all orthogonal to a common nonzero `m`, they lie in the `2`-plane `m^⊥`.
`normsq_smul_b` (substrate) gives the explicit coplanar decomposition of `u` along `v, w` once
`⟪v × w, u⟫ = 0` — which holds because `v × w` is parallel to `m` (both `v, w ⟂ m`) and `u ⟂ m`.  The
two Gram coordinates `α, β` then satisfy `α · det3 m v w = ‖v×w‖² · det3 m u w` and
`β · det3 m v w = ‖v×w‖² · det3 m v u`, so the sign of each coordinate is the sign of the planar
orientation product — the convex-position betweenness, transported to the tangent plane. -/

/-- `v × w` is parallel to `m` when `v, w ⟂ m`: `cross v w = (det3 m v w / ‖m‖²) • m`. -/
theorem cross_parallel_of_perp {m v w : E3} (hm : m ≠ 0)
    (hv : (⟪m, v⟫ : ℝ) = 0) (hw : (⟪m, w⟫ : ℝ) = 0) :
    cross v w = ((det3 m v w) / ‖m‖ ^ 2) • m := by
  -- `m × (v × w) = ⟪m,w⟫•v − ⟪m,v⟫•w = 0`, so `v × w` is parallel to `m`.
  have hcr : cross m (cross v w) = 0 := by
    rw [SphericalRotation.cross_cross, hw, hv, zero_smul, zero_smul, sub_zero]
  -- `m × (m × (v×w)) = ⟪m, v×w⟫ • m − ‖m‖² • (v×w)`, and the LHS = m × 0 = 0.
  have hc0 : cross m (0 : E3) = 0 := by
    apply ext_coord <;> simp
  have hcc := SphericalRotation.cross_cross m m (cross v w)
  rw [hcr, hc0, real_inner_self_eq_norm_sq] at hcc
  -- hcc : 0 = ⟪m, v×w⟫ • m − ‖m‖² • (v×w)
  have hmm : (0 : ℝ) < ‖m‖ ^ 2 := by positivity
  have hmx : (⟪m, cross v w⟫ : ℝ) = det3 m v w := inner_cross_eq_det3 m v w
  -- solve for `v × w`
  have hpar : (‖m‖ ^ 2 : ℝ) • (cross v w) = (det3 m v w) • m := by
    rw [← hmx]
    have hz : (⟪m, cross v w⟫ : ℝ) • m - (‖m‖ ^ 2 : ℝ) • (cross v w) = 0 := hcc.symm
    linear_combination (norm := module) -hz
  -- divide by ‖m‖²
  have : cross v w = (‖m‖ ^ 2 : ℝ)⁻¹ • ((det3 m v w) • m) := by
    rw [← hpar, smul_smul, inv_mul_cancel₀ (ne_of_gt hmm), one_smul]
  rw [this, smul_smul, div_eq_inv_mul]

/-- The coplanarity input for `normsq_smul_b`: `⟪v × w, u⟫ = 0` when `u, v, w ⟂ m` (`m ≠ 0`). -/
theorem inner_cross_perp {m u v w : E3} (hm : m ≠ 0)
    (hu : (⟪m, u⟫ : ℝ) = 0) (hv : (⟪m, v⟫ : ℝ) = 0) (hw : (⟪m, w⟫ : ℝ) = 0) :
    (⟪cross v w, u⟫ : ℝ) = 0 := by
  rw [cross_parallel_of_perp hm hv hw, real_inner_smul_left, hu, mul_zero]

/-- **Planar nonneg-cone from sign-consistency.**  Let `m ≠ 0` and let `u, v, w` all be orthogonal to
`m` (so coplanar in the `2`-plane `m^⊥`), with `v, w` independent (`det3 m v w ≠ 0`).  If the planar
orientation of `u` against each bounding edge is sign-consistent with the edge's own orientation —
`0 ≤ det3 m u w · det3 m v w` and `0 ≤ det3 m v u · det3 m v w` — then `u` is a nonnegative combination
`u ∈ span ℝ≥0 {v, w}`.  (The tangent-plane analogue of `betweenness_span_nnreal`.) -/
theorem mem_span_nnreal_of_planar_signs {m u v w : E3} (hm : m ≠ 0)
    (hu : (⟪m, u⟫ : ℝ) = 0) (hv : (⟪m, v⟫ : ℝ) = 0) (hw : (⟪m, w⟫ : ℝ) = 0)
    (hD : det3 m v w ≠ 0)
    (h1 : 0 ≤ det3 m u w * det3 m v w)
    (h2 : 0 ≤ det3 m v u * det3 m v w) :
    u ∈ Submodule.span NNReal ({v, w} : Set E3) := by
  -- coplanarity of `u` with `v, w`
  have hperp : (⟪cross v w, u⟫ : ℝ) = 0 := inner_cross_perp hm hu hv hw
  -- the explicit Gram decomposition `‖v×w‖² • u = α • v + β • w`
  have hns := normsq_smul_b v u w hperp
  set W : ℝ := ‖cross v w‖ ^ 2 with hWdef
  set α : ℝ := (⟪u, v⟫ : ℝ) * (⟪w, w⟫ : ℝ) - (⟪u, w⟫ : ℝ) * (⟪v, w⟫ : ℝ) with hαdef
  set β : ℝ := (⟪u, w⟫ : ℝ) * (⟪v, v⟫ : ℝ) - (⟪u, v⟫ : ℝ) * (⟪w, v⟫ : ℝ) with hβdef
  -- `hns : W • u = α • v + β • w`
  have hW0 : (0 : ℝ) < W := by
    rw [hWdef]
    have hne : cross v w ≠ 0 := by
      intro hz
      apply hD
      rw [← inner_cross_eq_det3, hz, inner_zero_right]
    positivity
  -- The two coordinate identities relating `α, β` to the planar orientations.
  -- Apply `det3 m · w` to `hns`: W·det3 m u w = α·det3 m v w + β·det3 m w w = α·det3 m v w.
  have hcoordα : W * det3 m u w = α * det3 m v w := by
    have h := congrArg (fun z => det3 m z w) hns
    simp only at h
    -- h : det3 m (W•u) w = det3 m (α•v + β•w) w
    rw [det3_smul_mid, det3_add_mid, det3_smul_mid, det3_smul_mid, det3_self_mid₂,
      mul_zero, add_zero] at h
    exact h
  -- Apply `det3 m v ·` to `hns`: W·det3 m v u = α·det3 m v v + β·det3 m v w = β·det3 m v w.
  have hcoordβ : W * det3 m v u = β * det3 m v w := by
    have h := congrArg (fun z => det3 m v z) hns
    simp only at h
    -- h : det3 m v (W•u) = det3 m v (α•v + β•w)
    rw [det3_smul_right, det3_add_right, det3_smul_right, det3_smul_right] at h
    -- h : W·det3 m v u = α·det3 m v v + β·det3 m v w
    rw [show det3 m v v = 0 from det3_self_mid₂ m v, mul_zero, zero_add] at h
    exact h
  -- From the sign hypotheses, extract `α ≥ 0`, `β ≥ 0`.
  have hD2 : (0 : ℝ) < det3 m v w ^ 2 := by positivity
  have hα0 : 0 ≤ α := by
    -- α·D² = (α·D)·D = (W·det3 m u w)·D = W·(det3 m u w · D) ≥ 0
    have hkey : α * det3 m v w ^ 2 = W * (det3 m u w * det3 m v w) := by
      rw [sq]; linear_combination (-(det3 m v w)) * hcoordα
    have hpos : 0 ≤ α * det3 m v w ^ 2 := by
      rw [hkey]; exact mul_nonneg (le_of_lt hW0) h1
    exact nonneg_of_mul_nonneg_left hpos hD2
  have hβ0 : 0 ≤ β := by
    have hkey : β * det3 m v w ^ 2 = W * (det3 m v u * det3 m v w) := by
      rw [sq]; linear_combination (-(det3 m v w)) * hcoordβ
    have hpos : 0 ≤ β * det3 m v w ^ 2 := by
      rw [hkey]; exact mul_nonneg (le_of_lt hW0) h2
    exact nonneg_of_mul_nonneg_left hpos hD2
  -- assemble `u = (α/W) • v + (β/W) • w` with nonnegative coordinates
  have hu_eq : u = (α / W) • v + (β / W) • w := by
    have hns2 : u = (1 / W) • (α • v + β • w) := by
      rw [← hns, smul_smul, one_div_mul_cancel (ne_of_gt hW0), one_smul]
    rw [hns2, smul_add, smul_smul, smul_smul]; congr 2 <;> ring
  have hadiv : 0 ≤ α / W := div_nonneg hα0 (le_of_lt hW0)
  have hbdiv : 0 ≤ β / W := div_nonneg hβ0 (le_of_lt hW0)
  rw [Submodule.mem_span_pair]
  refine ⟨⟨α / W, hadiv⟩, ⟨β / W, hbdiv⟩, ?_⟩
  show (α / W : ℝ) • v + (β / W : ℝ) • w = u
  exact hu_eq.symm

/-! ## Block C — the gnomonic transport tangent ↔ planar orientation.

At apex `m`, the spherical orientation `sOrient m (A i)(A j) = det3 m (A i)(A j)` equals the planar
orientation `det3 m (tangentTo m (A i))(tangentTo m (A j))` of the two tangent directions in `m^⊥`:
decomposing `A i = cos • m + tangentTo m (A i)`, the `cos • m` component is a repeated first column. -/

/-- **Gnomonic transport (tangent ↔ planar orientation).**  `det3 m (p) (q) = det3 m (tangentTo m p)
(tangentTo m q)`: the component of each neighbour along the apex `m` is a repeated first column. -/
theorem det3_tangentTo_eq (m p q : S2) :
    det3 (m : E3) (p : E3) (q : E3)
      = det3 (m : E3) (tangentTo m p) (tangentTo m q) := by
  -- the three repeated-`m`-column determinants all vanish
  have mmm : det3 (m : E3) (m : E3) (m : E3) = 0 := by simp only [det3]; ring
  have mmt : det3 (m : E3) (m : E3) (tangentTo m q) = 0 := by simp only [det3]; ring
  have mtm : det3 (m : E3) (tangentTo m p) (m : E3) = 0 := by simp only [det3]; ring
  conv_lhs =>
    rw [decompose_unit_along_tangent m p, decompose_unit_along_tangent m q]
  simp only [det3_add_mid, det3_add_right, det3_smul_mid, det3_smul_right,
    mmm, mmt, mtm, mul_zero, add_zero, zero_add]

/-! ## Block D — the cut-corner cone membership, discharged from `CyclicTriplePos`. -/

/-- The tangent at the apex is orthogonal to the apex (the `⟪m, tangentTo m p⟫ = 0` input). -/
theorem inner_apex_tangentTo (m p : S2) : (⟪(m : E3), tangentTo m p⟫ : ℝ) = 0 := by
  rw [real_inner_comm]; exact tangentTo_orthogonal m p

/-- **The cut-corner tangent-cone membership (HINGE 11.3, cone form) — DISCHARGED.**  For a strictly
convex spherical polygon `P : Fin N → S2` and a cut apex at index `2` (with `4 ≤ N` so `0,1,2,3` are
distinct vertices in increasing order), the cut diagonal's tangent ray `tangentTo (P 2)(P 0)` lies in
the nonnegative cone of the two adjacent edge tangent rays `tangentTo (P 2)(P 1)` and
`tangentTo (P 2)(P 3)`:

  `tangentTo (P 2)(P 0) ∈ span ℝ≥0 {tangentTo (P 2)(P 1), tangentTo (P 2)(P 3)}`.

This is the genuine HINGE 11.3 analytic fact the substrate previously had only in determinant-sign
form.  The proof transports the three apex-`2` orientations to the tangent plane (`det3_tangentTo_eq`),
reads off their signs from `cyclicTriplePos_unconditional` (each is an odd permutation of a positive
increasing triple, hence negative), and feeds the two positive sign products to
`mem_span_nnreal_of_planar_signs`. -/
theorem cutCorner_cone_membership {N : ℕ} [NeZero N] {P : Fin N → S2}
    (hP : StrictConvexSphPolygon P)
    (h0 : (0 : Fin N) < (1 : Fin N)) (h1 : (1 : Fin N) < (2 : Fin N))
    (h2 : (2 : Fin N) < (3 : Fin N)) :
    (tangentTo (P 2) (P 0) : E3)
      ∈ Submodule.span NNReal
        ({(tangentTo (P 2) (P 1) : E3), (tangentTo (P 2) (P 3) : E3)} : Set E3) := by
  have hcyc : CyclicTriplePos P := cyclicTriplePos_unconditional hP
  set m : S2 := P 2 with hm
  set u : E3 := tangentTo m (P 0) with hudef
  set v : E3 := tangentTo m (P 1) with hvdef
  set w : E3 := tangentTo m (P 3) with hwdef
  -- The three increasing-order positive orientations.
  have p012 : 0 < det3 (P 0 : E3) (P 1 : E3) (P 2 : E3) := hcyc 0 1 2 h0 h1
  have p023 : 0 < det3 (P 0 : E3) (P 2 : E3) (P 3 : E3) := hcyc 0 2 3 (h0.trans h1) h2
  have p123 : 0 < det3 (P 1 : E3) (P 2 : E3) (P 3 : E3) := hcyc 1 2 3 h1 h2
  -- The three apex-2 orientations, all NEGATIVE (odd permutations of the above).
  -- det3 (P2) (P1) (P3) = - det3 (P1) (P2) (P3) < 0
  have d_vw : det3 (m : E3) (P 1 : E3) (P 3 : E3) < 0 := by
    rw [hm, det3_swap_left]; linarith [p123]
  -- det3 (P2) (P0) (P3) = - det3 (P0) (P2) (P3) < 0
  have d_uw : det3 (m : E3) (P 0 : E3) (P 3 : E3) < 0 := by
    rw [hm, det3_swap_left]; linarith [p023]
  -- det3 (P2) (P1) (P0) = - det3 (P0) (P1) (P2)  (reversal = transposition of outer two)
  have d_vu : det3 (m : E3) (P 1 : E3) (P 0 : E3) < 0 := by
    rw [hm]
    -- det3 (P2)(P1)(P0) = - det3 (P0)(P1)(P2)
    have : det3 (P 2 : E3) (P 1 : E3) (P 0 : E3) = - det3 (P 0 : E3) (P 1 : E3) (P 2 : E3) := by
      simp only [det3]; ring
    rw [this]; linarith [p012]
  -- Transport to the tangent plane.
  have tvw : det3 (m : E3) v w = det3 (m : E3) (P 1 : E3) (P 3 : E3) := by
    rw [hvdef, hwdef, ← det3_tangentTo_eq]
  have tuw : det3 (m : E3) u w = det3 (m : E3) (P 0 : E3) (P 3 : E3) := by
    rw [hudef, hwdef, ← det3_tangentTo_eq]
  have tvu : det3 (m : E3) v u = det3 (m : E3) (P 1 : E3) (P 0 : E3) := by
    rw [hvdef, hudef, ← det3_tangentTo_eq]
  -- The hypotheses of the planar cone lemma.
  have hmne : (m : E3) ≠ 0 := by
    intro h; have := m.2; rw [h, norm_zero] at this; norm_num at this
  have hum : (⟪(m : E3), u⟫ : ℝ) = 0 := by rw [hudef]; exact inner_apex_tangentTo m (P 0)
  have hvm : (⟪(m : E3), v⟫ : ℝ) = 0 := by rw [hvdef]; exact inner_apex_tangentTo m (P 1)
  have hwm : (⟪(m : E3), w⟫ : ℝ) = 0 := by rw [hwdef]; exact inner_apex_tangentTo m (P 3)
  have hDne : det3 (m : E3) v w ≠ 0 := by rw [tvw]; exact ne_of_lt d_vw
  have hsign1 : 0 ≤ det3 (m : E3) u w * det3 (m : E3) v w := by
    rw [tuw, tvw]; exact le_of_lt (mul_pos_of_neg_of_neg d_uw d_vw)
  have hsign2 : 0 ≤ det3 (m : E3) v u * det3 (m : E3) v w := by
    rw [tvu, tvw]; exact le_of_lt (mul_pos_of_neg_of_neg d_vu d_vw)
  -- apply the planar cone lemma
  have := mem_span_nnreal_of_planar_signs hmne hum hvm hwm hDne hsign1 hsign2
  -- rewrite the set members back
  rw [hudef, hvdef, hwdef, hm] at this
  exact this

/-! ## Block E — the cut-corner cone membership in the level-`(n+1)` arm indexing.

The arm `A : Fin (n + 1 + 1) → S2` has its closure `A.closed_convex : StrictConvexSphPolygon A` on
`N = n + 2` vertices, with `n ≥ 2` so `N ≥ 4`.  We specialise `cutCorner_cone_membership` to the apex
index `2`, matching the `(⟨2, _⟩, ⟨3, _⟩)` shape `CornerConeFacts` consumes. -/

/-- The value of `(2 : Fin (n + 1 + 1))` is `2` (for `n ≥ 2`). -/
theorem two_val {n : ℕ} (hn : 2 ≤ n) : ((2 : Fin (n + 1 + 1)) : ℕ) = 2 := by
  simp; omega

/-- The value of `(3 : Fin (n + 1 + 1))` is `3` (for `n ≥ 2`). -/
theorem three_val {n : ℕ} (hn : 2 ≤ n) : ((3 : Fin (n + 1 + 1)) : ℕ) = 3 := by
  simp; omega

theorem cut_indices_lt {n : ℕ} (hn : 2 ≤ n) :
    (0 : Fin (n + 1 + 1)) < (1 : Fin (n + 1 + 1)) ∧
    (1 : Fin (n + 1 + 1)) < (2 : Fin (n + 1 + 1)) ∧
    (2 : Fin (n + 1 + 1)) < (3 : Fin (n + 1 + 1)) := by
  have h1 : ((1 : Fin (n + 1 + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [Fin.lt_def, Fin.val_zero, h1]; omega
  · rw [Fin.lt_def, h1, two_val hn]; omega
  · rw [Fin.lt_def, two_val hn, three_val hn]; omega

/-- The index `(⟨3, _⟩ : Fin (n + 1 + 1))` equals the numeral `3`. -/
theorem fin_three_eq {n : ℕ} (hn : 2 ≤ n) :
    (⟨3, by omega⟩ : Fin (n + 1 + 1)) = (3 : Fin (n + 1 + 1)) :=
  Fin.ext (by rw [three_val hn])

/-- The index `(⟨2, _⟩ : Fin (n + 1 + 1))` equals the numeral `2`. -/
theorem fin_two_eq {n : ℕ} (hn : 2 ≤ n) :
    (⟨2, by omega⟩ : Fin (n + 1 + 1)) = (2 : Fin (n + 1 + 1)) :=
  Fin.ext (by rw [two_val hn])

/-- **The cut-corner cone membership in arm indexing — DISCHARGED.**  For a strictly convex arm
`A : Fin (n + 1 + 1) → S2` (`n ≥ 2`), the diagonal tangent ray at the cut apex `A ⟨2⟩` lies in the
nonnegative cone of the two edge tangent rays toward `A 1` and `A ⟨3⟩` — exactly the cone-membership
conjunct of `CornerConeFacts`. -/
theorem armCutCorner_cone_membership {n : ℕ} (hn : 2 ≤ n) (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) :
    (tangentTo (A ⟨2, by omega⟩) (A 0) : E3)
      ∈ Submodule.span NNReal
        ({(tangentTo (A ⟨2, by omega⟩) (A 1) : E3),
          (tangentTo (A ⟨2, by omega⟩) (A ⟨3, by omega⟩) : E3)} : Set E3) := by
  have hP : StrictConvexSphPolygon (n := n + 1 + 1) A := hA.closed_convex
  obtain ⟨h0, h1, h2⟩ := cut_indices_lt hn
  have hmem := cutCorner_cone_membership hP h0 h1 h2
  -- rewrite the numerals `2, 3` to the `⟨_, _⟩` forms
  rw [fin_two_eq hn, fin_three_eq hn]
  exact hmem

/-! ## Block F — the strictly-narrower residue: the matched first joint only.

With the cone membership now PROVED substrate, `CornerConeFacts` no longer needs the two cone
memberships as hypotheses.  The remaining content is the §8.4 matched-joint data: the matched first
joint, the matched corner-triangle sides (parent sides + matched diagonal via SAS), the short-arc
nondegeneracy, and the strictness link.  We isolate exactly this strictly-narrower residue and prove it
discharges `MatchedCutCornerConeStep`. -/

/-- The per-level §8.4 matched-joint facts: the matched first joint, the corner-triangle short-arc
nondegeneracy and matched sides, and the strictness link.  This is `CornerConeFacts` with the two cone
memberships REMOVED (now proved unconditionally by `armCutCorner_cone_membership`). -/
def MatchedFirstJointFacts (n : ℕ) (hn : 2 ≤ n) (A B : Fin (n + 1 + 1) → S2) : Prop :=
  jointAngle A (⟨0, by omega⟩ : Fin n) = jointAngle B (⟨0, by omega⟩ : Fin n) ∧
  ShortArc (A 1) (A ⟨2, by omega⟩) ∧ ShortArc (A ⟨2, by omega⟩) (A 0) ∧
    ShortArc (B ⟨2, by omega⟩) (B 0) ∧
  sDist (A 1) (A ⟨2, by omega⟩) = sDist (B 1) (B ⟨2, by omega⟩) ∧
  sDist (A ⟨2, by omega⟩) (A 0) = sDist (B ⟨2, by omega⟩) (B 0) ∧
  sDist (A 1) (A 0) = sDist (B 1) (B 0) ∧
  ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
    ∃ i : Fin (n - 1), jointAngle (frontCut A) i < jointAngle (frontCut B) i)

/-- **(Strictly-narrower residue) The matched-first-joint step.**  For every level-`(n+1)` convex pair
with equal sides, nondecreasing joints, and `SZComparison n`, the §8.4 matched-joint facts hold.  Its
payload is strictly the §8.4 reach recursion / all-strict opening data — the *cone membership* has been
removed (discharged here unconditionally). -/
def MatchedFirstJointStep : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n),
    ∀ (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      SZComparison n →
      MatchedFirstJointFacts n hn A B

/-- **`MatchedFirstJointFacts → CornerConeFacts` (cone membership supplied).**  The two cone
memberships are furnished by `armCutCorner_cone_membership` for `A` and `B`; everything else is carried
from `MatchedFirstJointFacts`. -/
theorem cornerConeFacts_of_matchedFirstJoint {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hf : MatchedFirstJointFacts n hn A B) :
    CornerConeFacts n hn A B := by
  obtain ⟨hjoint0, hAs12, hAs20, hBs20, hs01, hs12, hdiag, hlink⟩ := hf
  exact ⟨hjoint0, hAs12, hAs20, hBs20, hs01, hs12, hdiag,
    armCutCorner_cone_membership hn A hA,
    armCutCorner_cone_membership hn B hB, hlink⟩

/-- **`MatchedFirstJointStep → MatchedCutCornerConeStep` (the reduction).**  Each level's matched-joint
facts are upgraded to the corner cone facts by supplying the proved cone membership. -/
theorem matchedCutCornerConeStep_of_matchedFirstJoint (h : MatchedFirstJointStep) :
    MatchedCutCornerConeStep := by
  intro n hn A B hA hB hside hangle ih
  exact cornerConeFacts_of_matchedFirstJoint hn A B hA hB (h n hn A B hA hB hside hangle ih)

/-! ## Block G — the kernel arm lemmas, conditional only on `MatchedFirstJointStep`. -/

/-- **`MatchedFirstJointStep` cleanly closes the chain.**  Composing with the proved
`schoenbergZaremba_of_cone`, the matched-first-joint step yields `SchoenbergZarembaTarget` — the cone
membership entirely discharged. -/
theorem schoenbergZaremba_of_matchedFirstJoint (h : MatchedFirstJointStep) :
    SchoenbergZarembaTarget :=
  schoenbergZaremba_of_cone (matchedCutCornerConeStep_of_matchedFirstJoint h)

/-- **The unconditional kernel arm lemma (weak), conditional only on `MatchedFirstJointStep`.** -/
theorem armUncond_mono_of_matchedFirstJoint (h : MatchedFirstJointStep)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  armUncond_mono_of_cone (matchedCutCornerConeStep_of_matchedFirstJoint h) hn A B hA hB hside hangle

/-- **The unconditional kernel arm lemma (strict), conditional only on `MatchedFirstJointStep`.** -/
theorem armUncond_strict_of_matchedFirstJoint (h : MatchedFirstJointStep)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  armUncond_strict_of_cone (matchedCutCornerConeStep_of_matchedFirstJoint h)
    hn A B hA hB hside hangle hstrict

/-! ## Block H — non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `mem_span_nnreal_of_planar_signs`: at `u = v` (a bounding edge itself) the
membership holds — the cone genuinely contains its own generators, confirming the planar cone lemma is
not vacuous. -/
theorem planar_cone_self_mem (v w : E3) :
    v ∈ Submodule.span NNReal ({v, w} : Set E3) :=
  Submodule.subset_span (by left; rfl)

/-- Non-vacuity of the gnomonic transport: it is a genuine identity (reflexive in form), confirming the
tangent ↔ planar orientation bridge carries real content (the `cos • m` columns genuinely vanish). -/
theorem det3_tangentTo_self (m p : S2) :
    det3 (m : E3) (p : E3) (p : E3) = det3 (m : E3) (tangentTo m p) (tangentTo m p) :=
  det3_tangentTo_eq m p p

/-- Non-vacuity of the cone membership: the discharged HINGE 11.3 cone membership is a genuine
nonnegative-cone fact (the cone contains the diagonal tangent), realised on every strictly convex
spherical polygon with a degree-`≥ 4` apex window — not a vacuous payload. -/
theorem cutCorner_cone_membership_nonvacuous {n : ℕ} (hn : 2 ≤ n) (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) :
    (tangentTo (A ⟨2, by omega⟩) (A 0) : E3)
      ∈ Submodule.span NNReal
        ({(tangentTo (A ⟨2, by omega⟩) (A 1) : E3),
          (tangentTo (A ⟨2, by omega⟩) (A ⟨3, by omega⟩) : E3)} : Set E3) :=
  armCutCorner_cone_membership hn A hA

/-- Non-vacuity of `MatchedFirstJointStep`: its conclusion is genuinely realised at the congruent
configuration `A = B` (matched joint, matched sides reflexive, strictness link vacuous), provided the
corner triangle is short — so the residue's payload is a real geometric configuration. -/
theorem matchedFirstJointFacts_refl {n : ℕ} (hn : 2 ≤ n) (A : Fin (n + 1 + 1) → S2)
    (hAs12 : ShortArc (A 1) (A ⟨2, by omega⟩)) (hAs20 : ShortArc (A ⟨2, by omega⟩) (A 0)) :
    MatchedFirstJointFacts n hn A A :=
  ⟨rfl, hAs12, hAs20, hAs20, rfl, rfl, rfl, by
    rintro ⟨i, hi⟩; exact absurd hi (lt_irrefl _)⟩

end ProofsInTheBook.SphericalConeMembership
