import ProofsInTheBook.SphericalKernel

/-!
# Chapter 13 — the local extrinsic vertex model (`VertexStar`) and its link map

This module builds the **local ℝ³ data of a single convex-polytope vertex** and the bridge from that
extrinsic data to the abstract spherical arm machinery of `SphericalKernel`.

A `VertexStar` records:
* an apex `o : E3`;
* a cyclically ordered family of neighbours `p : Fin (n+1) → E3` (`n+1` edges, `n ≥ 2`);
* purely **ℝ³-derivable convexity predicates** on the *raw* edge vectors `v i := p i - o`:
  each neighbour is distinct from the apex; the raw directions lie in one open hemisphere; and the
  oriented great-circle edges of the direction polygon turn strictly the same way
  (`det3`-positivity of consecutive raw directions against every other direction).

From this we build:
* `edgeDir : Fin (n+1) → S2`, the normalised edge directions (the vertex link as a point set on `S²`);
* `vertexLink := edgeDir`, presented as a `Fin (n+1) → S2` family;
* **`vertexLink_strictArm`** — the link is a `StrictConvexSphArm`.  Each of the five
  `StrictConvexSphPolygon` fields is *derived* from the ℝ³ convexity fields (the §3.3 trap of
  positing a `StrictConvexSphArm` as a structure field is avoided);
* **`sideLen_vertexLink`** (Bridge A) — the spherical side length of the link equals the Euclidean
  `EuclideanGeometry.angle (p i) o (p (i+1))` at the apex; a *theorem*, not a posited field.

A concrete `cubeCornerStar : VertexStar` (apex at the origin, three neighbours along `+x,+y,+z`)
witnesses non-vacuity (§3.3): every convexity field is discharged by an explicit computation, so the
`VertexStar` predicate is inhabited.

No `sorry`, `axiom`, or `admit`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13VertexStar

/-! ## The local extrinsic vertex model -/

/-- The **local ℝ³ data of one convex-polytope vertex**.

`n + 1` neighbours `p 0, …, p n` are arranged cyclically around the apex `o`.  The convexity data is
phrased entirely on the **raw** edge vectors `p i - o` (no posited spherical structure):

* `apex_ne` — every neighbour differs from the apex (so the edge direction is well defined);
* `open_hemi` — the raw edge vectors all lie strictly on the positive side of a common unit
  functional `h` (one open hemisphere);
* `turn_support` — each oriented raw edge `(p i - o, p (i+1) - o)` keeps **every** other raw
  direction on the nonnegative side of the plane it spans through the apex;
* `turn_strict` — the same, strictly, for the non-incident directions.

These are exactly the predicates `vertexLink_strictArm` consumes, and they are satisfiable
(see `cubeCornerStar`). -/
structure VertexStar where
  /-- Arm parameter: there are `n + 1` neighbours / edges, with `n ≥ 2`. -/
  n : ℕ
  /-- At least three edges (`n + 1 ≥ 3`): a convex-polytope vertex has `≥ 3` incident edges. -/
  hn : 2 ≤ n
  /-- The apex of the star. -/
  o : E3
  /-- The cyclically ordered neighbours. -/
  p : Fin (n + 1) → E3
  /-- Each neighbour differs from the apex. -/
  apex_ne : ∀ i : Fin (n + 1), p i ≠ o
  /-- The raw edge vectors lie in one open hemisphere. -/
  open_hemi : ∃ h : E3, ‖h‖ = 1 ∧ ∀ i : Fin (n + 1), 0 < ⟪h, p i - o⟫
  /-- Each oriented raw edge supports every raw direction on the nonnegative side. -/
  turn_support : ∀ i j : Fin (n + 1), 0 ≤ det3 (p i - o) (p (i + 1) - o) (p j - o)
  /-- Non-incident raw directions are strictly on the positive side. -/
  turn_strict : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 < det3 (p i - o) (p (i + 1) - o) (p j - o)

namespace VertexStar

variable (S : VertexStar)

/-- The raw edge vector `p i - o`. -/
def rawDir (i : Fin (S.n + 1)) : E3 := S.p i - S.o

theorem rawDir_ne_zero (i : Fin (S.n + 1)) : S.rawDir i ≠ 0 := by
  simp only [rawDir, sub_ne_zero]
  exact S.apex_ne i

theorem norm_rawDir_pos (i : Fin (S.n + 1)) : 0 < ‖S.rawDir i‖ :=
  norm_pos_iff.mpr (S.rawDir_ne_zero i)

/-- The unit edge direction at the apex toward `p i`, a point of `S²`. -/
def edgeDir (i : Fin (S.n + 1)) : S2 :=
  ⟨‖S.rawDir i‖⁻¹ • S.rawDir i, by
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (ne_of_gt (S.norm_rawDir_pos i))⟩

/-- `edgeDir i` is the positive multiple `‖rawDir i‖⁻¹` of the raw direction. -/
theorem edgeDir_coe (i : Fin (S.n + 1)) :
    (S.edgeDir i : E3) = ‖S.rawDir i‖⁻¹ • S.rawDir i := rfl

theorem inv_norm_pos (i : Fin (S.n + 1)) : 0 < ‖S.rawDir i‖⁻¹ :=
  inv_pos.mpr (S.norm_rawDir_pos i)

/-- The **vertex link**: the cyclic edge-direction family, presented as a `Fin (n+1) → S²` tuple in
the `StrictConvexSphArm` convention. -/
def vertexLink : Fin (S.n + 1) → S2 := S.edgeDir

@[simp] theorem vertexLink_apply (i : Fin (S.n + 1)) : S.vertexLink i = S.edgeDir i := rfl

/-! ### `sOrient` of the link in terms of raw `det3`

`sOrient (edgeDir a) (edgeDir b) (edgeDir c)` is the raw `det3` scaled by the three positive inverse
norms, because `det3` is multilinear and `edgeDir` is a positive rescaling of `rawDir`. -/

/-- `det3` is multilinear: scaling each argument multiplies the determinant by the product. -/
theorem det3_smul (ca cb cc : ℝ) (a b c : E3) :
    det3 (ca • a) (cb • b) (cc • c) = (ca * cb * cc) * det3 a b c := by
  simp only [det3, PiLp.smul_apply, smul_eq_mul]; ring

/-- The signed volume of three link directions is a positive multiple of the raw `det3`. -/
theorem sOrient_edgeDir (a b c : Fin (S.n + 1)) :
    sOrient (S.edgeDir a) (S.edgeDir b) (S.edgeDir c)
      = (‖S.rawDir a‖⁻¹ * ‖S.rawDir b‖⁻¹ * ‖S.rawDir c‖⁻¹)
        * det3 (S.rawDir a) (S.rawDir b) (S.rawDir c) := by
  rw [sOrient, edgeDir_coe, edgeDir_coe, edgeDir_coe, det3_smul]

/-- The product of the three inverse norms is positive. -/
theorem inv_norm_prod_pos (a b c : Fin (S.n + 1)) :
    0 < ‖S.rawDir a‖⁻¹ * ‖S.rawDir b‖⁻¹ * ‖S.rawDir c‖⁻¹ :=
  mul_pos (mul_pos (S.inv_norm_pos a) (S.inv_norm_pos b)) (S.inv_norm_pos c)

/-- Sign transfer (nonnegative): the raw support hypothesis gives nonnegative link orientation. -/
theorem sOrient_edgeDir_nonneg (a b c : Fin (S.n + 1))
    (h : 0 ≤ det3 (S.rawDir a) (S.rawDir b) (S.rawDir c)) :
    0 ≤ sOrient (S.edgeDir a) (S.edgeDir b) (S.edgeDir c) := by
  rw [sOrient_edgeDir]
  exact mul_nonneg (le_of_lt (S.inv_norm_prod_pos a b c)) h

/-- Sign transfer (strict). -/
theorem sOrient_edgeDir_pos (a b c : Fin (S.n + 1))
    (h : 0 < det3 (S.rawDir a) (S.rawDir b) (S.rawDir c)) :
    0 < sOrient (S.edgeDir a) (S.edgeDir b) (S.edgeDir c) := by
  rw [sOrient_edgeDir]
  exact mul_pos (S.inv_norm_prod_pos a b c) h

/-! ### Short-arc of consecutive link directions (derived, not posited)

If `edgeDir i = ± edgeDir (i+1)` then the raw directions `rawDir i, rawDir (i+1)` are parallel, so
`det3 (rawDir i) (rawDir (i+1)) (rawDir j) = 0` for **every** `j`.  But `turn_strict` gives a `j`
(existing because `n ≥ 2`) with that determinant strictly positive.  Hence the consecutive link
directions are neither equal nor antipodal: the link edge is a short arc. -/

/-- Since `n ≥ 2`, every edge index `i` admits a non-incident index `j` (`j ≠ i`, `j ≠ i+1`). -/
theorem exists_noninc (i : Fin (S.n + 1)) : ∃ j : Fin (S.n + 1), j ≠ i ∧ j ≠ i + 1 := by
  -- The set `{i, i+1}` has at most 2 elements; with `≥ 3` total there is a third.
  by_contra hcon
  push_neg at hcon
  -- every j is i or i+1
  have hsub : (Finset.univ : Finset (Fin (S.n + 1))) ⊆ {i, i + 1} := by
    intro j _
    rcases eq_or_ne j i with hji | hji
    · simp [hji]
    · have := hcon j hji
      simp [this]
  have hle := Finset.card_le_card hsub
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  have hle2 : ({i, i + 1} : Finset (Fin (S.n + 1))).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  have := S.hn
  omega

/-- If `det3 a b c > 0` for some `c`, then `b` is not a scalar multiple of `a`. -/
theorem not_smul_of_det3_pos {a b : E3} (c : E3) (h : 0 < det3 a b c)
    (t : ℝ) : b ≠ t • a := by
  intro hb
  rw [hb] at h
  have : det3 a (t • a) c = 0 := by
    simp only [det3, PiLp.smul_apply, smul_eq_mul]; ring
  rw [this] at h; exact lt_irrefl _ h

/-- Consecutive link directions are not equal. -/
theorem edgeDir_ne (i : Fin (S.n + 1)) : S.edgeDir i ≠ S.edgeDir (i + 1) := by
  obtain ⟨j, hji, hjip⟩ := S.exists_noninc i
  intro heq
  -- edgeDir i = edgeDir (i+1) ⟹ rawDir (i+1) = (‖raw(i+1)‖/‖raw i‖) • rawDir i
  have hcoe : (S.edgeDir i : E3) = (S.edgeDir (i + 1) : E3) := by rw [heq]
  rw [edgeDir_coe, edgeDir_coe] at hcoe
  -- rawDir (i+1) = (‖raw(i+1)‖ * ‖raw i‖⁻¹) • rawDir i
  have hraw : S.rawDir (i + 1) = (‖S.rawDir (i + 1)‖ * ‖S.rawDir i‖⁻¹) • S.rawDir i := by
    have h1 : ‖S.rawDir (i + 1)‖ • (‖S.rawDir i‖⁻¹ • S.rawDir i)
        = ‖S.rawDir (i + 1)‖ • (‖S.rawDir (i + 1)‖⁻¹ • S.rawDir (i + 1)) := by
      rw [hcoe]
    rw [smul_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt (S.norm_rawDir_pos (i + 1))),
      one_smul] at h1
    exact h1.symm
  have hpos := S.turn_strict i j hji hjip
  exact (not_smul_of_det3_pos (S.rawDir j) hpos (‖S.rawDir (i + 1)‖ * ‖S.rawDir i‖⁻¹)) hraw

/-- Consecutive link directions are not antipodal. -/
theorem edgeDir_not_antipodal (i : Fin (S.n + 1)) :
    (S.edgeDir i : E3) ≠ -(S.edgeDir (i + 1) : E3) := by
  obtain ⟨j, hji, hjip⟩ := S.exists_noninc i
  intro heq
  rw [edgeDir_coe, edgeDir_coe] at heq
  -- ‖raw i‖⁻¹ • raw i = -(‖raw(i+1)‖⁻¹ • raw(i+1)) ⟹ raw(i+1) = (-(‖raw(i+1)‖ * ‖raw i‖⁻¹)) • raw i
  have hraw : S.rawDir (i + 1) = (-(‖S.rawDir (i + 1)‖ * ‖S.rawDir i‖⁻¹)) • S.rawDir i := by
    have h1 := congrArg (fun z : E3 => ‖S.rawDir (i + 1)‖ • z) heq
    simp only [smul_neg, smul_smul] at h1
    rw [mul_inv_cancel₀ (ne_of_gt (S.norm_rawDir_pos (i + 1))), one_smul] at h1
    -- h1 : (‖r(i+1)‖ * ‖r i‖⁻¹) • r i = -r(i+1)
    rw [neg_smul, h1, neg_neg]
  have hpos := S.turn_strict i j hji hjip
  exact (not_smul_of_det3_pos (S.rawDir j) hpos (-(‖S.rawDir (i + 1)‖ * ‖S.rawDir i‖⁻¹))) hraw

/-- The consecutive link edge is a short arc. -/
theorem edgeDir_shortArc (i : Fin (S.n + 1)) : ShortArc (S.edgeDir i) (S.edgeDir (i + 1)) :=
  ⟨S.edgeDir_ne i, S.edgeDir_not_antipodal i⟩

/-! ### Open-hemisphere transfer

`edgeDir i` is a positive multiple of `rawDir i = p i - o`, so the hemisphere functional `h` of the
raw data is positive on the link directions too. -/

theorem inner_h_edgeDir_pos {h : E3} (i : Fin (S.n + 1))
    (hraw : 0 < ⟪h, S.rawDir i⟫) : 0 < ⟪h, (S.edgeDir i : E3)⟫ := by
  rw [edgeDir_coe, real_inner_smul_right]
  exact mul_pos (S.inv_norm_pos i) hraw

/-! ## The link is a strictly convex spherical arm -/

/-- **The vertex link is a strictly convex spherical arm.**

Each of the five `StrictConvexSphPolygon` fields is derived from the ℝ³ convexity fields of `S`:
`edge_short` from `turn_strict` (via `edgeDir_shortArc`); `edge_support`/`strict_nonincident` from
`turn_support`/`turn_strict` (via the `det3` sign-transfer lemmas); `open_hemisphere` from
`open_hemi`; `three_le` from `hn`. -/
theorem vertexLink_strictArm : StrictConvexSphArm S.vertexLink where
  two_le := S.hn
  closed_convex :=
    { three_le := by have := S.hn; omega
      edge_short := fun i => by
        simpa only [vertexLink_apply] using S.edgeDir_shortArc i
      edge_support := fun i j => by
        simp only [vertexLink_apply]
        exact S.sOrient_edgeDir_nonneg i (i + 1) j (S.turn_support i j)
      strict_nonincident := fun i j hji hjip => by
        simp only [vertexLink_apply]
        exact S.sOrient_edgeDir_pos i (i + 1) j (S.turn_strict i j hji hjip)
      open_hemisphere := by
        obtain ⟨h, hh, hpos⟩ := S.open_hemi
        exact ⟨h, hh, fun i => by
          simpa only [vertexLink_apply] using S.inner_h_edgeDir_pos i (hpos i)⟩ }

/-! ## Bridge A — link side length = Euclidean apex angle (a theorem)

`sideLen vertexLink i = sDist (edgeDir i) (edgeDir (i+1)) = arccos ⟪edgeDir i, edgeDir (i+1)⟫`.
Both directions point from the apex `o`, so this is the unoriented Euclidean angle
`∠ (p i) o (p (i+1))` (scale-invariance of `InnerProductGeometry.angle` under the positive inverse
norms). -/

/-- The spherical side length of the link equals `arccos` of the inner product of the two link unit
directions. -/
theorem sideLen_vertexLink_eq_iAngle (i : Fin S.n) :
    sideLen S.vertexLink i
      = InnerProductGeometry.angle (S.edgeDir i.castSucc : E3) (S.edgeDir i.succ : E3) := by
  -- sideLen = sDist (edgeDir castSucc) (edgeDir succ) = arccos (sInner …)
  unfold sideLen
  rw [vertexLink_apply, vertexLink_apply]
  rw [sDist, InnerProductGeometry.angle]
  congr 1
  -- sInner = ⟪·,·⟫ ; and ‖edgeDir‖ = 1 so the denominator is 1
  rw [sInner]
  rw [S2.norm_coe, S2.norm_coe, mul_one, div_one]

/-- **Bridge A.**  The link side length is the Euclidean angle at the apex between the two incident
neighbours.  Here `i.castSucc` and `i.succ = i.castSucc + 1` are consecutive neighbour indices. -/
theorem sideLen_vertexLink (i : Fin S.n) :
    sideLen S.vertexLink i
      = EuclideanGeometry.angle (S.p i.castSucc) S.o (S.p i.succ) := by
  rw [sideLen_vertexLink_eq_iAngle]
  -- edgeDir = (positive scalar) • rawDir, and rawDir k = p k - o = p k -ᵥ o
  rw [edgeDir_coe, edgeDir_coe]
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (S.inv_norm_pos _),
      InnerProductGeometry.angle_smul_right_of_pos _ _ (S.inv_norm_pos _)]
  -- rawDir k = p k - o = p k -ᵥ o
  show InnerProductGeometry.angle (S.rawDir i.castSucc) (S.rawDir i.succ) = _
  rw [EuclideanGeometry.angle]
  rfl

end VertexStar

/-! ## §3.3 non-vacuity: the cube-corner vertex star

Apex at the origin, three neighbours along `+x`, `+y`, `+z` (`n = 2`, so `n + 1 = 3` edges).  Every
convexity field is discharged by an explicit coordinate computation, proving `VertexStar` is
inhabited (the predicate is satisfiable, not a §3.3 trap). -/

/-- The three cube-corner neighbours `e_x, e_y, e_z`, defined by cases so every index reduces. -/
def cubeNbr : Fin 3 → E3
  | 0 => !₂[(1:ℝ), 0, 0]
  | 1 => !₂[(0:ℝ), 1, 0]
  | 2 => !₂[(0:ℝ), 0, 1]

@[simp] theorem cubeNbr_zero : cubeNbr 0 = !₂[(1:ℝ), 0, 0] := rfl
@[simp] theorem cubeNbr_one : cubeNbr 1 = !₂[(0:ℝ), 1, 0] := rfl
@[simp] theorem cubeNbr_two : cubeNbr 2 = !₂[(0:ℝ), 0, 1] := rfl
@[simp] theorem cubeNbr_zero_succ : cubeNbr (0 + 1) = !₂[(0:ℝ), 1, 0] := rfl
@[simp] theorem cubeNbr_one_succ : cubeNbr (1 + 1) = !₂[(0:ℝ), 0, 1] := rfl
@[simp] theorem cubeNbr_two_succ : cubeNbr (2 + 1) = !₂[(1:ℝ), 0, 0] := rfl

/-- Each coordinate of each `!₂` neighbour, packaged for `simp`/`norm_num`. -/
theorem ex_apply : (!₂[(1:ℝ), 0, 0] : E3) 0 = 1 ∧ (!₂[(1:ℝ), 0, 0] : E3) 1 = 0 ∧
    (!₂[(1:ℝ), 0, 0] : E3) 2 = 0 := ⟨rfl, rfl, rfl⟩
theorem ey_apply : (!₂[(0:ℝ), 1, 0] : E3) 0 = 0 ∧ (!₂[(0:ℝ), 1, 0] : E3) 1 = 1 ∧
    (!₂[(0:ℝ), 1, 0] : E3) 2 = 0 := ⟨rfl, rfl, rfl⟩
theorem ez_apply : (!₂[(0:ℝ), 0, 1] : E3) 0 = 0 ∧ (!₂[(0:ℝ), 0, 1] : E3) 1 = 0 ∧
    (!₂[(0:ℝ), 0, 1] : E3) 2 = 1 := ⟨rfl, rfl, rfl⟩
theorem ones_apply : (!₂[(1:ℝ), 1, 1] : E3) 0 = 1 ∧ (!₂[(1:ℝ), 1, 1] : E3) 1 = 1 ∧
    (!₂[(1:ℝ), 1, 1] : E3) 2 = 1 := ⟨rfl, rfl, rfl⟩

/-- Uniform evaluation: `cubeNbr k` is the `k`-th standard basis vector, so its `c`-th coordinate is
the Kronecker delta `δ_{kc}`.  This avoids reducing `Fin` `match` discriminants like `i + 1`. -/
theorem cubeNbr_apply (k c : Fin 3) : (cubeNbr k) c = (if k = c then (1:ℝ) else 0) := by
  fin_cases k <;> fin_cases c <;> rfl

/-- The cube-corner vertex star: apex `0`, neighbours `e_x, e_y, e_z`. -/
def cubeCornerStar : VertexStar where
  n := 2
  hn := le_refl 2
  o := 0
  p := cubeNbr
  apex_ne := by
    intro i hcon
    -- each neighbour is a unit vector, so it cannot equal the apex `0`.
    have hnorm : ‖cubeNbr i‖ = ‖(0 : E3)‖ := by rw [hcon]
    rw [norm_zero] at hnorm
    revert hnorm
    fin_cases i <;>
      · rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
        norm_num [cubeNbr, ex_apply.1, ex_apply.2.1, ex_apply.2.2, ey_apply.1, ey_apply.2.1,
          ey_apply.2.2, ez_apply.1, ez_apply.2.1, ez_apply.2.2]
  open_hemi := by
    -- functional h = (e_x + e_y + e_z)/√3; ⟪h, e_k⟫ = 1/√3 > 0
    refine ⟨(Real.sqrt 3)⁻¹ • !₂[(1:ℝ), 1, 1], ?_, ?_⟩
    · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 3)]
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
      rw [ones_apply.1, ones_apply.2.1, ones_apply.2.2]
      rw [inv_mul_eq_one₀ (by positivity)]
      norm_num
    · intro i
      rw [sub_zero, real_inner_smul_left]
      have hpos : (0 : ℝ) < (Real.sqrt 3)⁻¹ := by positivity
      apply mul_pos hpos
      rw [PiLp.inner_apply, Fin.sum_univ_three]
      fin_cases i <;>
        · simp only [cubeNbr, RCLike.inner_apply, conj_trivial]
          norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons]
  turn_support := by
    intro i j
    simp only [sub_zero]
    show (0 : ℝ) ≤ det3 _ _ _
    rw [det3]
    simp only [cubeNbr_apply]
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff, Fin.add_def]
  turn_strict := by
    intro i j hji hjip
    simp only [sub_zero]
    show (0 : ℝ) < det3 _ _ _
    rw [det3]
    simp only [cubeNbr_apply]
    fin_cases i <;> fin_cases j <;>
      first
      | (exfalso; revert hji hjip; decide)
      | norm_num [Fin.ext_iff, Fin.add_def]

/-- `VertexStar` is inhabited: the cube-corner star satisfies all convexity fields. -/
theorem vertexStar_inhabited : Nonempty VertexStar := ⟨cubeCornerStar⟩

/-- The cube-corner link is a strictly convex spherical arm (instantiating `vertexLink_strictArm`). -/
theorem cubeCornerStar_link_strictArm :
    StrictConvexSphArm cubeCornerStar.vertexLink :=
  cubeCornerStar.vertexLink_strictArm

end ProofsInTheBook.Ch13VertexStar

#print axioms ProofsInTheBook.Ch13VertexStar.VertexStar.vertexLink_strictArm
#print axioms ProofsInTheBook.Ch13VertexStar.VertexStar.sideLen_vertexLink
