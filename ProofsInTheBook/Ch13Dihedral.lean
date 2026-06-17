import ProofsInTheBook.Ch13VertexStar

/-!
# Chapter 13 — the extrinsic dihedral angle of a vertex star (Bridge B)

This module supplies the §3.3 **load-bearing bridge** between the abstract spherical joint angle of
the vertex link (`jointAngle` of `SphericalKernel`, computed on the link `vertexLink := edgeDir`) and
the **extrinsic dihedral angle** of the underlying ℝ³ vertex star, defined directly from the two
ℝ³ face half-planes meeting along an edge.

* `VertexStar.dihedral S i` — for an internal joint index `i : Fin (S.n - 1)`, the dihedral angle of
  the star along the *middle* edge `o → p (i+1)` of the consecutive triple `i, i+1, i+2`.  It is
  defined INDEPENDENTLY of the spherical link, as the unoriented angle between the projections of the
  two *outer* raw edge vectors `p i - o` and `p (i+2) - o` onto the plane orthogonal to the middle
  raw edge direction `p (i+1) - o`.  This mirrors `TetDihedral.dihedralAngle` exactly (the same
  `projOut`/`angle` recipe), so it is the standard interior dihedral angle, NOT a re-wrapping of
  `jointAngle`.

* **`jointAngle_vertexLink_eq_dihedral`** (Bridge B) — a *theorem*: the spherical joint angle of the
  link equals the extrinsic dihedral.  The proof identifies `tangentTo (edgeDir b) x = projOut
  (edgeDir b) x` with `projOut (rawDir b) x` (projection onto a line is invariant under positive
  rescaling of the axis), then kills the positive inverse-norm scalings of the two outer directions
  via `InnerProductGeometry.angle_smul_left/right_of_pos`.

The §3.3 non-vacuity witness is `cubeCornerStar`: its single internal joint has dihedral `π/2`, and
Bridge B applies on it.

No `sorry`, `axiom`, or `admit`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.Ch13VertexStar

namespace VertexStar

variable (S : VertexStar)

/-! ## `projOut` is invariant under positive rescaling of the projection axis

`projOut d x = x - (⟪x,d⟫/⟪d,d⟫) • d` projects `x` onto the *line* through `d`'s complement.  Scaling
`d` by `c ≠ 0` leaves the line — hence the projection — unchanged. -/

/-- Scaling the projection axis by a nonzero scalar does not change `projOut`. -/
theorem projOut_smul_left {c : ℝ} (hc : c ≠ 0) (d x : E3) :
    projOut (c • d) x = projOut d x := by
  simp only [projOut, real_inner_smul_right, real_inner_smul_left, smul_smul]
  congr 2
  field_simp

/-! ## The extrinsic dihedral angle of a vertex star

For an internal joint `i : Fin (S.n - 1)`, the three consecutive neighbour indices in `Fin (S.n+1)`
are `⟨i,_⟩`, `⟨i+1,_⟩`, `⟨i+2,_⟩` — exactly the triple `jointAngle` consumes.  The middle edge
direction is `rawDir ⟨i+1⟩ = p ⟨i+1⟩ - o`. -/

/-- The lower index `⟨i.val, _⟩ : Fin (S.n + 1)` of the consecutive triple at internal joint `i`. -/
def jIdx0 (i : Fin (S.n - 1)) : Fin (S.n + 1) := ⟨i.val, by have := i.isLt; omega⟩
/-- The middle index `⟨i.val + 1, _⟩ : Fin (S.n + 1)` (the dihedral edge). -/
def jIdx1 (i : Fin (S.n - 1)) : Fin (S.n + 1) := ⟨i.val + 1, by have := i.isLt; omega⟩
/-- The upper index `⟨i.val + 2, _⟩ : Fin (S.n + 1)`. -/
def jIdx2 (i : Fin (S.n - 1)) : Fin (S.n + 1) := ⟨i.val + 2, by have := i.isLt; omega⟩

/-- **The extrinsic dihedral angle** of the star `S` along the middle edge `o → p ⟨i+1⟩` of the
consecutive triple `⟨i⟩, ⟨i+1⟩, ⟨i+2⟩`.  Defined directly from the ℝ³ data, mirroring
`TetDihedral.dihedralAngle`: project the two outer raw edge vectors `p ⟨i⟩ - o` and `p ⟨i+2⟩ - o`
onto the plane perpendicular to the middle raw edge direction `p ⟨i+1⟩ - o`, and take the angle.

This is *independent* of the spherical link `vertexLink`; Bridge B (`jointAngle_vertexLink_eq_dihedral`)
identifies it with the link's `jointAngle`. -/
def dihedral (i : Fin (S.n - 1)) : ℝ :=
  InnerProductGeometry.angle
    (projOut (S.rawDir (S.jIdx1 i)) (S.rawDir (S.jIdx0 i)))
    (projOut (S.rawDir (S.jIdx1 i)) (S.rawDir (S.jIdx2 i)))

/-! ## Bridge B — `jointAngle vertexLink = dihedral`

`jointAngle S.vertexLink i = sphAngle (edgeDir ⟨i⟩) (edgeDir ⟨i+1⟩) (edgeDir ⟨i+2⟩)`
`= angle (tangentTo (edgeDir ⟨i+1⟩) (edgeDir ⟨i⟩)) (tangentTo (edgeDir ⟨i+1⟩) (edgeDir ⟨i+2⟩))`
`= angle (projOut (edgeDir ⟨i+1⟩) (edgeDir ⟨i⟩)) (projOut (edgeDir ⟨i+1⟩) (edgeDir ⟨i+2⟩))`.

Now `edgeDir x = ‖rawDir x‖⁻¹ • rawDir x` with `‖rawDir x‖⁻¹ > 0`.  Scaling the axis (`projOut_smul_left`)
and the projected vector (`projOut_smul`) gives
`projOut (edgeDir ⟨i+1⟩) (edgeDir ⟨i⟩) = ‖rawDir ⟨i⟩‖⁻¹ • projOut (rawDir ⟨i+1⟩) (rawDir ⟨i⟩)`,
and likewise for the upper direction.  The two positive scalars are killed by the angle lemmas. -/

/-- `tangentTo (edgeDir b) (edgeDir a)`, as a `projOut` of the *raw* directions, scaled by the
positive inverse norm `‖rawDir a‖⁻¹`. -/
theorem tangentTo_edgeDir_eq (a b : Fin (S.n + 1)) :
    tangentTo (S.edgeDir b) (S.edgeDir a)
      = ‖S.rawDir a‖⁻¹ • projOut (S.rawDir b) (S.rawDir a) := by
  rw [tangentTo, edgeDir_coe, edgeDir_coe,
    projOut_smul_left (ne_of_gt (S.inv_norm_pos b)) (S.rawDir b) _,
    projOut_smul (S.rawDir b) (‖S.rawDir a‖⁻¹) (S.rawDir a)]

/-- **Bridge B.**  The spherical joint angle of the vertex link equals the extrinsic ℝ³ dihedral
angle of the star along the corresponding middle edge.  A *theorem*: the dihedral is defined
independently of the link in `dihedral`, so this is not vacuous. -/
theorem jointAngle_vertexLink_eq_dihedral (i : Fin (S.n - 1)) :
    jointAngle S.vertexLink i = S.dihedral i := by
  -- Unfold `jointAngle ∘ vertexLink` to `sphAngle` of the three `edgeDir`s, then to `angle` of the
  -- two tangents.  The three indices coincide with `jIdx0/1/2`.
  rw [jointAngle]
  simp only [vertexLink_apply]
  rw [sphAngle]
  -- rewrite both tangents as scaled raw `projOut`s
  show InnerProductGeometry.angle
      (tangentTo (S.edgeDir (S.jIdx1 i)) (S.edgeDir (S.jIdx0 i)))
      (tangentTo (S.edgeDir (S.jIdx1 i)) (S.edgeDir (S.jIdx2 i))) = _
  rw [tangentTo_edgeDir_eq, tangentTo_edgeDir_eq]
  -- kill the two positive inverse-norm scalings
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ (S.inv_norm_pos (S.jIdx0 i)),
      InnerProductGeometry.angle_smul_right_of_pos _ _ (S.inv_norm_pos (S.jIdx2 i))]
  rfl

end VertexStar

/-! ## §3.3 non-vacuity: the cube-corner dihedral

`cubeCornerStar` has `n = 2`, so `Fin (S.n - 1) = Fin 1`: a single internal joint `0`.  Bridge B
applies, identifying the link's joint angle with the extrinsic dihedral of the cube corner. -/

/-- The cube corner's single internal joint angle equals its extrinsic dihedral (Bridge B on the
§3.3 witness).  Witnesses that `jointAngle_vertexLink_eq_dihedral` is non-vacuously instantiable. -/
example (i : Fin (cubeCornerStar.n - 1)) :
    jointAngle cubeCornerStar.vertexLink i = cubeCornerStar.dihedral i :=
  cubeCornerStar.jointAngle_vertexLink_eq_dihedral i

end ProofsInTheBook.Ch13VertexStar

#print axioms ProofsInTheBook.Ch13VertexStar.VertexStar.jointAngle_vertexLink_eq_dihedral
