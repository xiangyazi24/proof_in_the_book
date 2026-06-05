import ProofsInTheBook.TetPearls
import ProofsInTheBook.Chapter09

/-!
# Dihedral angles of tetrahedra (Chapter 9, geometry layer)

This module implements the dihedral-angle layer for the simplices-only Pearl/Bricard route to
Hilbert's third problem, on top of the substrate in `TetPearls.lean`
(`Tet`, `Tet.carrier`, affine independence) and reusing the concrete regular-tetrahedron coordinate
model from `Chapter09.lean`.

## The definition (projection form)

For a tetrahedron `T` and a directed edge `i j` (`i ≠ j`), let `d := T.v j - T.v i` be the edge
direction and let `k, l` be the two remaining vertex indices.  Projecting the opposite vertices
orthogonally to the edge line and measuring the angle between the projections gives the *interior
dihedral angle* of `T` along the edge `{i,j}`:

* `projOut d x := x - (⟪x,d⟫/⟪d,d⟫) • d`     (orthogonal complement of `x` away from `d`);
* `dihedralAngle T i j := InnerProductGeometry.angle (projOut d u) (projOut d w)`,
  where `u := T.v k - T.v i`, `w := T.v l - T.v i`.

This avoids the cross-section machinery and only needs Mathlib's unoriented `angle` (valued in
`[0,π]`).

## Contents

* `dihedralAngle` — the definition above.
* `projOut_ne_zero` — the two projections are nonzero (else the four vertices are affinely
  dependent).
* `dihedralAngle_mem_Ioo` — `0 < dihedralAngle T i j < π` (the projections are not parallel, of
  either sign; a parallel relation is an affine dependence among the four vertices).
* `dihedralAngle_comm` — symmetry/well-definedness `dihedralAngle T i j = dihedralAngle T j i`.
* `dihedralAngle_mapIso` — invariance under Euclidean isometries (reflections allowed), via the
  Mazur–Ulam linear isometry of `f : Pt3 ≃ᵢ Pt3`.
* `regularTet`, `regularTet_dihedralAngle` — every edge of the regular tetrahedron has dihedral
  angle `arccos (1/3)`.
* `cornerTet`, `cornerTet_dihedralAngle_right` — the three edges at the corner vertex of the
  orthogonal corner tetrahedron `{0, e₀, e₁, e₂}` have dihedral angle `π/2`.

No `sorry`, `axiom`, or `admit`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls

namespace ProofsInTheBook.TetDihedral

/-! ## The orthogonal-projection operator `projOut` -/

/-- `projOut d x` is the component of `x` orthogonal to `d`: `x - (⟪x,d⟫/⟪d,d⟫) • d`.  When `d ≠ 0`
this is the orthogonal projection of `x` onto the hyperplane `dᗮ`. -/
def projOut (d x : Pt3) : Pt3 := x - ((⟪x, d⟫ / ⟪d, d⟫) : ℝ) • d

/-- `projOut d x` is orthogonal to `d` whenever `d ≠ 0`. -/
theorem inner_projOut_right (d x : Pt3) (hd : d ≠ 0) : ⟪projOut d x, d⟫ = 0 := by
  have hdd : (⟪d, d⟫ : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ⟪d, d⟫ := real_inner_self_pos.mpr hd
    exact ne_of_gt this
  simp only [projOut, inner_sub_left, real_inner_smul_left]
  field_simp
  ring

/-- `projOut` is additive in its second argument. -/
theorem projOut_add (d x y : Pt3) : projOut d (x + y) = projOut d x + projOut d y := by
  simp only [projOut, inner_add_left, add_div, add_smul]
  abel

/-- `projOut` is homogeneous in its second argument. -/
theorem projOut_smul (d : Pt3) (r : ℝ) (x : Pt3) : projOut d (r • x) = r • projOut d x := by
  simp only [projOut, real_inner_smul_left, smul_sub, smul_smul]
  congr 2
  rw [mul_div_assoc]

theorem projOut_sub (d x y : Pt3) : projOut d (x - y) = projOut d x - projOut d y := by
  rw [sub_eq_add_neg, projOut_add, show -y = (-1 : ℝ) • y from by simp, projOut_smul]
  simp [sub_eq_add_neg]

/-- The inner product of two `projOut`-projections, as a closed form in the original inner products.
`⟪projOut d x, projOut d y⟫ = ⟪x,y⟫ - ⟪x,d⟫⟪y,d⟫/⟪d,d⟫`. -/
theorem inner_projOut_projOut (d x y : Pt3) (hd : d ≠ 0) :
    (⟪projOut d x, projOut d y⟫ : ℝ)
      = ⟪x, y⟫ - ⟪x, d⟫ * ⟪y, d⟫ / ⟪d, d⟫ := by
  have hdd : (⟪d, d⟫ : ℝ) ≠ 0 := ne_of_gt (real_inner_self_pos.mpr hd)
  simp only [projOut, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm d x, real_inner_comm d y, real_inner_comm d d]
  field_simp
  ring

/-! ## The complementary index pair of an edge -/

/-- The two vertex indices other than `i` and `j` (in some order).  Defined by an explicit,
fully reducible table over `Fin 4 × Fin 4` so that `decide`/`fin_cases` evaluate it. -/
def otherTwo (i j : Fin 4) : Fin 4 × Fin 4 :=
  let cand : List (Fin 4) := [0, 1, 2, 3]
  let s := cand.filter (fun m => m ≠ i ∧ m ≠ j)
  (s.getD 0 0, s.getD 1 0)

theorem otherTwo_spec {i j : Fin 4} (hij : i ≠ j) :
    let p := otherTwo i j
    p.1 ≠ i ∧ p.1 ≠ j ∧ p.2 ≠ i ∧ p.2 ≠ j ∧ p.1 ≠ p.2 := by
  fin_cases i <;> fin_cases j <;> first | (exact absurd rfl hij) | decide

/-! ## The dihedral angle -/

/-- The interior dihedral angle of `T` along the (unoriented) edge `{i,j}`, defined as the angle
between the orthogonal-to-edge projections of the two opposite vertices.  See the module header. -/
def dihedralAngle (T : Tet) (i j : Fin 4) : ℝ :=
  let d := T.v j - T.v i
  let k := (otherTwo i j).1
  let l := (otherTwo i j).2
  InnerProductGeometry.angle (projOut d (T.v k - T.v i)) (projOut d (T.v l - T.v i))

/-! ## Nonvanishing and the affine-dependence lemma

The crux: if a projection `projOut d (T.v k - T.v i)` is parallel to (any scalar multiple of) the
other, the four vertices are affinely dependent — contradicting `T.affIndep`.  We package the
general "parallel ⇒ affine dependence" computation once. -/

/-- **Affine-dependence obstruction.**  If, for the four *distinct* indices `i,j,k,l`, the projected
opposite vertices satisfy `projOut d u = r • projOut d w` for *some* real `r` (where
`d = T.v j - T.v i`, `u = T.v k - T.v i`, `w = T.v l - T.v i`), then the four vertices are affinely
dependent.  Since they are affinely independent, no such `r` exists. -/
theorem not_projOut_parallel (T : Tet) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (r : ℝ) :
    projOut (T.v j - T.v i) (T.v k - T.v i)
      ≠ r • projOut (T.v j - T.v i) (T.v l - T.v i) := by
  intro hpar
  -- Set d, u, w and the scalar coefficients.
  set d := T.v j - T.v i with hd
  set u := T.v k - T.v i with hu
  set w := T.v l - T.v i with hw
  -- From `projOut d u = r • projOut d w`, isolate `u - r • w` as a multiple of `d`.
  -- projOut d u = u - cu • d, projOut d w = w - cw • d
  set cu : ℝ := ⟪u, d⟫ / ⟪d, d⟫ with hcu
  set cw : ℝ := ⟪w, d⟫ / ⟪d, d⟫ with hcw
  have hpar' : u - cu • d = r • (w - cw • d) := by
    simpa [projOut, hcu, hcw] using hpar
  -- Hence u - r • w = (cu - r * cw) • d.
  set s : ℝ := cu - r * cw with hs
  have hcombo : u - r • w = s • d := by
    have : u - cu • d = r • w - (r * cw) • d := by
      rw [hpar']; module
    have h2 : u - r • w = cu • d - (r * cw) • d := by
      rw [sub_eq_iff_eq_add] at this ⊢
      rw [this]; module
    rw [h2, hs, sub_smul]
  -- Substitute the vertex differences: this is an affine dependence among v i, v j, v k, v l.
  -- Coefficients: on v k: 1, v l: -r, v j: -s, v i: (-1 + r + s); they sum to 0.
  rw [hu, hw, hd] at hcombo
  -- Build the weight function on Fin 4.
  set wfun : Fin 4 → ℝ := fun m =>
    if m = k then 1 else if m = l then -r else if m = j then -s else (-1 + r + s) with hwfun
  -- The four weight evaluations.
  have hwk : wfun k = 1 := by simp only [hwfun]; simp
  have hwl : wfun l = -r := by
    simp only [hwfun]; rw [if_neg (Ne.symm hkl)]; simp
  have hwj : wfun j = -s := by
    simp only [hwfun]; rw [if_neg hjk, if_neg hjl]; simp
  have hwi : wfun i = -1 + r + s := by
    simp only [hwfun]; rw [if_neg hik, if_neg hil, if_neg hij]
  -- The index set {i,j,k,l} is all of `Fin 4` (four distinct elements).
  have hset : (Finset.univ : Finset (Fin 4)) = {i, j, k, l} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin]
    rw [Finset.card_insert_of_notMem (by simp [hij, hik, hil]),
      Finset.card_insert_of_notMem (by simp [hjk, hjl]),
      Finset.card_insert_of_notMem (by simp [hkl]), Finset.card_singleton]
  have hsum : ∑ m, wfun m = 0 := by
    rw [hset, Finset.sum_insert (by simp [hij, hik, hil]),
      Finset.sum_insert (by simp [hjk, hjl]), Finset.sum_insert (by simp [hkl]),
      Finset.sum_singleton, hwi, hwj, hwk, hwl]
    ring
  have hvsub : ∑ m, wfun m • T.v m = 0 := by
    rw [hset, Finset.sum_insert (by simp [hij, hik, hil]),
      Finset.sum_insert (by simp [hjk, hjl]), Finset.sum_insert (by simp [hkl]),
      Finset.sum_singleton, hwi, hwj, hwk, hwl]
    -- (-1+r+s)•v i + (-s)•v j + 1•v k + (-r)•v l = 0, i.e. hcombo rearranged.
    have hcombo' : (T.v k - T.v i) - r • (T.v l - T.v i) - s • (T.v j - T.v i) = 0 := by
      rw [hcombo]; abel
    rw [← hcombo']; module
  -- Affine independence forces the weight of v k to be 0, but it is 1.
  have hzero := T.affIndep.eq_zero_of_sum_eq_zero (s := Finset.univ) (w := wfun) hsum hvsub k
    (Finset.mem_univ k)
  rw [hwk] at hzero
  exact one_ne_zero hzero

/-- The first projected opposite vertex is nonzero (taking `r = 0` in `not_projOut_parallel`
forces it; we package the direct argument). -/
theorem projOut_fst_ne_zero (T : Tet) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    projOut (T.v j - T.v i) (T.v k - T.v i) ≠ 0 := by
  intro h
  exact not_projOut_parallel T hij hik hil hjk hjl hkl 0 (by rw [h]; simp)

/-- The second projected opposite vertex is nonzero. -/
theorem projOut_snd_ne_zero (T : Tet) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    projOut (T.v j - T.v i) (T.v l - T.v i) ≠ 0 := by
  -- by symmetry k ↔ l
  intro h
  exact projOut_fst_ne_zero T hij hil hik hjl hjk hkl.symm h

/-! ## Strict bounds `0 < dihedralAngle < π` -/

/-- **Strict bounds.**  The dihedral angle lies strictly between `0` and `π`. -/
theorem dihedralAngle_mem_Ioo (T : Tet) {i j : Fin 4} (hij : i ≠ j) :
    dihedralAngle T i j ∈ Set.Ioo 0 Real.pi := by
  obtain ⟨hk_i, hk_j, hl_i, hl_j, hkl⟩ := otherTwo_spec hij
  set k := (otherTwo i j).1
  set l := (otherTwo i j).2
  -- distinctness in the canonical i,j,k,l order
  have hik : i ≠ k := (Ne.symm hk_i)
  have hil : i ≠ l := (Ne.symm hl_i)
  have hjk : j ≠ k := (Ne.symm hk_j)
  have hjl : j ≠ l := (Ne.symm hl_j)
  set d := T.v j - T.v i with hd
  set U := projOut d (T.v k - T.v i) with hU
  set W := projOut d (T.v l - T.v i) with hW
  have hUne : U ≠ 0 := projOut_fst_ne_zero T hij hik hil hjk hjl hkl
  refine ⟨?_, ?_⟩
  · -- angle ≠ 0 and angle ≥ 0
    rcases lt_or_eq_of_le (InnerProductGeometry.angle_nonneg U W) with h | h
    · exact h
    · exfalso
      -- angle = 0 ⇒ W = r • U with r > 0 ⇒ contradiction with not_projOut_parallel
      have h' : InnerProductGeometry.angle U W = 0 := h.symm
      rw [InnerProductGeometry.angle_eq_zero_iff] at h'
      obtain ⟨_, r, hr, hWrU⟩ := h'
      have hrne : r ≠ 0 := ne_of_gt hr
      -- W = r • U  ⇒  U = r⁻¹ • W
      have : U = r⁻¹ • W := by rw [hWrU, smul_smul, inv_mul_cancel₀ hrne, one_smul]
      exact not_projOut_parallel T hij hik hil hjk hjl hkl r⁻¹ this
  · -- angle ≤ π and angle ≠ π
    rcases lt_or_eq_of_le (InnerProductGeometry.angle_le_pi U W) with h | h
    · exact h
    · exfalso
      rw [InnerProductGeometry.angle_eq_pi_iff] at h
      obtain ⟨_, r, hr, hWrU⟩ := h
      have hrne : r ≠ 0 := ne_of_lt hr
      have : U = r⁻¹ • W := by rw [hWrU, smul_smul, inv_mul_cancel₀ hrne, one_smul]
      exact not_projOut_parallel T hij hik hil hjk hjl hkl r⁻¹ this

theorem dihedralAngle_pos (T : Tet) {i j : Fin 4} (hij : i ≠ j) :
    0 < dihedralAngle T i j := (dihedralAngle_mem_Ioo T hij).1

theorem dihedralAngle_lt_pi (T : Tet) {i j : Fin 4} (hij : i ≠ j) :
    dihedralAngle T i j < Real.pi := (dihedralAngle_mem_Ioo T hij).2

/-! ## Symmetry: `dihedralAngle T i j = dihedralAngle T j i`

The angle is the unoriented angle between the projections of the two opposite vertices onto the
plane orthogonal to the edge.  Reversing the edge replaces `d` by `-d`; but `projOut` is invariant
under `d ↦ -d` (the projection is onto the *line* through `d`), and the complementary pair `{k,l}`
is unchanged, so the two projected vectors are literally the same. -/

theorem projOut_neg_left (d x : Pt3) : projOut (-d) x = projOut d x := by
  simp only [projOut, inner_neg_right, inner_neg_left, neg_neg, smul_neg,
    neg_div, neg_smul]

theorem otherTwo_symm (i j : Fin 4) : otherTwo j i = otherTwo i j := by
  fin_cases i <;> fin_cases j <;> rfl

/-- `projOut d d = 0`: the component of `d` orthogonal to itself vanishes (for `d ≠ 0`). -/
theorem projOut_self (d : Pt3) (hd : d ≠ 0) : projOut d d = 0 := by
  have hdd : (⟪d, d⟫ : ℝ) ≠ 0 := ne_of_gt (real_inner_self_pos.mpr hd)
  simp only [projOut]
  rw [div_self hdd, one_smul, sub_self]

/-- Changing the base point on the edge line does not change the projected opposite vertex:
`projOut d (x - c • d) = projOut d x`. -/
theorem projOut_sub_smul_self (d x : Pt3) (c : ℝ) (hd : d ≠ 0) :
    projOut d (x - c • d) = projOut d x := by
  rw [projOut_sub, projOut_smul, projOut_self d hd, smul_zero, sub_zero]

/-- **Well-definedness / symmetry.**  The dihedral angle does not depend on the orientation of the
edge.  We argue for `i ≠ j` (the only geometrically meaningful case; equal indices give a degenerate
direction `0` on both sides). -/
theorem dihedralAngle_comm (T : Tet) {i j : Fin 4} (hij : i ≠ j) :
    dihedralAngle T i j = dihedralAngle T j i := by
  have hd : T.v j - T.v i ≠ 0 := sub_ne_zero.mpr (fun h => hij (T.v_injective h.symm))
  simp only [dihedralAngle, otherTwo_symm]
  -- on the `j i` side, direction is `T.v i - T.v j = -(T.v j - T.v i)` and base point is `T.v j`.
  rw [show T.v i - T.v j = -(T.v j - T.v i) by abel, projOut_neg_left, projOut_neg_left]
  -- rewrite the base point from `T.v j` back to `T.v i` using `T.v · - T.v j = (T.v · - T.v i) - d`.
  have hbase : ∀ m : Fin 4, T.v m - T.v j = (T.v m - T.v i) - (1 : ℝ) • (T.v j - T.v i) := by
    intro m; rw [one_smul]; abel
  rw [hbase (otherTwo i j).1, hbase (otherTwo i j).2,
    projOut_sub_smul_self _ _ _ hd, projOut_sub_smul_self _ _ _ hd]

/-! ## Isometry invariance

A Euclidean isometry `f : Pt3 ≃ᵢ Pt3` (reflections allowed) has, by Mazur–Ulam, an associated real
linear isometry equivalence `g := f.toRealLinearIsometryEquiv` with `g x = f x - f 0`.  Mapping a
tetrahedron's vertices by `f` produces another tetrahedron whose edge difference vectors are exactly
the `g`-images of the original ones (`g (a - b) = f a - f b`).  Because `g` preserves inner products
and `projOut`/`angle` are built from inner products, the dihedral angles agree. -/

/-- The image of a tetrahedron under a Euclidean isometry `f : Pt3 ≃ᵢ Pt3`. -/
def Tet.mapIso (f : Pt3 ≃ᵢ Pt3) (T : Tet) : Tet where
  v := f ∘ T.v
  affIndep := by
    have : AffineIndependent ℝ ((f.toRealAffineIsometryEquiv.toAffineEquiv) ∘ T.v) :=
      (AffineEquiv.affineIndependent_iff _).mpr T.affIndep
    -- the underlying function of the affine equiv is `f`
    have hcoe : ⇑(f.toRealAffineIsometryEquiv.toAffineEquiv) = (f : Pt3 → Pt3) := by
      ext x
      rfl
    simpa [Function.comp, hcoe] using this

/-- `projOut` commutes with a linear isometry equivalence. -/
theorem projOut_linearIsometryEquiv (g : Pt3 ≃ₗᵢ[ℝ] Pt3) (d x : Pt3) :
    projOut (g d) (g x) = g (projOut d x) := by
  simp only [projOut, map_sub, map_smul, g.inner_map_map]

/-- **Isometry invariance** (reflections allowed).  Mapping a tetrahedron by any Euclidean isometry
of `Pt3` preserves every dihedral angle. -/
theorem dihedralAngle_mapIso (f : Pt3 ≃ᵢ Pt3) (T : Tet) (i j : Fin 4) :
    dihedralAngle (Tet.mapIso f T) i j = dihedralAngle T i j := by
  set g : Pt3 ≃ₗᵢ[ℝ] Pt3 := f.toRealLinearIsometryEquiv with hg
  -- (mapIso f T).v m = f (T.v m); and g (a - b) = f a - f b.
  have hv : ∀ m, (Tet.mapIso f T).v m = f (T.v m) := fun m => rfl
  have hgsub : ∀ a b : Pt3, g (a - b) = f a - f b := by
    intro a b
    rw [map_sub]
    simp only [hg, IsometryEquiv.toRealLinearIsometryEquiv_apply]
    abel
  simp only [dihedralAngle]
  -- the complementary pair is the same on both sides; rewrite each projected vector via g.
  set k := (otherTwo i j).1
  set l := (otherTwo i j).2
  rw [hv i, hv j, hv k, hv l]
  rw [show f (T.v j) - f (T.v i) = g (T.v j - T.v i) from (hgsub _ _).symm,
      show f (T.v k) - f (T.v i) = g (T.v k - T.v i) from (hgsub _ _).symm,
      show f (T.v l) - f (T.v i) = g (T.v l - T.v i) from (hgsub _ _).symm]
  rw [projOut_linearIsometryEquiv g, projOut_linearIsometryEquiv g]
  exact g.toLinearIsometry.angle_map _ _

/-! ## Concrete value: the regular tetrahedron

We reuse the coordinate regular tetrahedron from `Chapter09`, whose vertices are the four sign
vectors with an even number of minus signs.  Its squared edge lengths and pairwise dot products are
already computed there; we recompute the projection cosine directly and identify it with `1/3`. -/

open ProofsInTheBook.Chapter09 in
/-- The regular tetrahedron of `Chapter09`, packaged as a `Tet`. -/
def regularTet : Tet where
  v := regularTetrahedronVertex
  affIndep := regularTetrahedronVertex_affineIndependent

open ProofsInTheBook.Chapter09 in
/-- Real inner product of two regular-tetrahedron vertices equals the coordinate `dot3`. -/
theorem inner_regularTetVertex (i j : Fin 4) :
    (⟪regularTetrahedronVertex i, regularTetrahedronVertex j⟫ : ℝ)
      = dot3 (regularTetrahedronVertex i) (regularTetrahedronVertex j) := by
  rw [PiLp.inner_apply, Fin.sum_univ_three, dot3]
  simp only [RCLike.inner_apply, conj_trivial]
  fin_cases i <;> fin_cases j <;> simp [regularTetrahedronVertex]

open ProofsInTheBook.Chapter09 in
/-- The real inner product of two vertex *difference* vectors of the regular tetrahedron, expanded
via bilinearity and the known pairwise dot products. -/
theorem inner_regularTet_diff (a b c e : Fin 4) :
    (⟪regularTetrahedronVertex a - regularTetrahedronVertex b,
        regularTetrahedronVertex c - regularTetrahedronVertex e⟫ : ℝ)
      = dot3 (regularTetrahedronVertex a) (regularTetrahedronVertex c)
        - dot3 (regularTetrahedronVertex a) (regularTetrahedronVertex e)
        - dot3 (regularTetrahedronVertex b) (regularTetrahedronVertex c)
        + dot3 (regularTetrahedronVertex b) (regularTetrahedronVertex e) := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
      inner_regularTetVertex, inner_regularTetVertex, inner_regularTetVertex,
      inner_regularTetVertex]
  ring

open ProofsInTheBook.Chapter09 in
/-- **Regular tetrahedron dihedral angle.**  Every edge of the regular tetrahedron has dihedral
angle `arccos (1/3)`. -/
theorem regularTet_dihedralAngle {i j : Fin 4} (hij : i ≠ j) :
    dihedralAngle regularTet i j = Real.arccos (1 / 3) := by
  obtain ⟨hk_i, hk_j, hl_i, hl_j, hkl⟩ := otherTwo_spec hij
  -- abbreviations matching `dihedralAngle regularTet i j`
  set k := (otherTwo i j).1
  set l := (otherTwo i j).2
  have hik : i ≠ k := Ne.symm hk_i
  have hil : i ≠ l := Ne.symm hl_i
  have hjk : j ≠ k := Ne.symm hk_j
  have hjl : j ≠ l := Ne.symm hl_j
  -- the angle is arccos of the inner-product cosine; compute the cosine = 1/3.
  show InnerProductGeometry.angle
      (projOut (regularTet.v j - regularTet.v i) (regularTet.v k - regularTet.v i))
      (projOut (regularTet.v j - regularTet.v i) (regularTet.v l - regularTet.v i))
      = Real.arccos (1 / 3)
  -- It suffices to show the cosine equals 1/3 *and* the angle is in [0,π] (arccos is the inverse).
  -- We use: angle x y = arccos (⟪x,y⟫/(‖x‖‖y‖)), so it remains to show that ratio = 1/3.
  rw [InnerProductGeometry.angle]
  congr 1
  -- reduce to a rational identity in the dot products.
  set d := regularTet.v j - regularTet.v i with hd
  set U := projOut d (regularTet.v k - regularTet.v i) with hU
  set W := projOut d (regularTet.v l - regularTet.v i) with hW
  -- All the dot products of (vertex) and (vertex) are 3 (equal) or -1 (distinct).
  have hdd_self : ∀ a : Fin 4, dot3 (regularTetrahedronVertex a) (regularTetrahedronVertex a) = 3 :=
    regularTetrahedronVertex_dot_self
  have hdd_ne : ∀ {a b : Fin 4}, a ≠ b →
      dot3 (regularTetrahedronVertex a) (regularTetrahedronVertex b) = -1 :=
    fun h => regularTetrahedronVertex_dot_of_ne h
  -- All the individual dot products among {i,j,k,l}, both orderings, as a rewrite set.
  have dij := hdd_ne hij; have dji := hdd_ne hij.symm
  have dik := hdd_ne hik; have dki := hdd_ne hik.symm
  have dil := hdd_ne hil; have dli := hdd_ne hil.symm
  have djk := hdd_ne hjk; have dkj := hdd_ne hjk.symm
  have djl := hdd_ne hjl; have dlj := hdd_ne hjl.symm
  have dkl := hdd_ne hkl; have dlk := hdd_ne hkl.symm
  have dii := hdd_self i; have djj := hdd_self j
  have dkk := hdd_self k; have dll := hdd_self l
  -- compute ⟪d,d⟫ = 8, ⟪u,d⟫ = 4, ⟪w,d⟫ = 4, ⟪u,w⟫ = 4, ⟪u,u⟫ = 8, ⟪w,w⟫ = 8.
  have hidd : (⟪d, d⟫ : ℝ) = 8 := by
    rw [hd]; show (⟪regularTet.v j - regularTet.v i, regularTet.v j - regularTet.v i⟫ : ℝ) = 8
    rw [show regularTet.v = regularTetrahedronVertex from rfl, inner_regularTet_diff]
    simp only [dij, dji, dii, djj]; norm_num
  have hud : (⟪regularTet.v k - regularTet.v i, d⟫ : ℝ) = 4 := by
    rw [hd]; show (⟪regularTet.v k - regularTet.v i, regularTet.v j - regularTet.v i⟫ : ℝ) = 4
    rw [show regularTet.v = regularTetrahedronVertex from rfl, inner_regularTet_diff]
    simp only [dkj, dki, dij, dii]; norm_num
  have hwd : (⟪regularTet.v l - regularTet.v i, d⟫ : ℝ) = 4 := by
    rw [hd]; show (⟪regularTet.v l - regularTet.v i, regularTet.v j - regularTet.v i⟫ : ℝ) = 4
    rw [show regularTet.v = regularTetrahedronVertex from rfl, inner_regularTet_diff]
    simp only [dlj, dli, dij, dii]; norm_num
  have huw : (⟪regularTet.v k - regularTet.v i, regularTet.v l - regularTet.v i⟫ : ℝ) = 4 := by
    rw [show regularTet.v = regularTetrahedronVertex from rfl, inner_regularTet_diff]
    simp only [dkl, dki, dil, dii]; norm_num
  have huu : (⟪regularTet.v k - regularTet.v i, regularTet.v k - regularTet.v i⟫ : ℝ) = 8 := by
    rw [show regularTet.v = regularTetrahedronVertex from rfl, inner_regularTet_diff]
    simp only [dkk, dki, dik, dii]; norm_num
  have hww : (⟪regularTet.v l - regularTet.v i, regularTet.v l - regularTet.v i⟫ : ℝ) = 8 := by
    rw [show regularTet.v = regularTetrahedronVertex from rfl, inner_regularTet_diff]
    simp only [dll, dli, dil, dii]; norm_num
  -- now ⟪U,W⟫ = ⟪u,w⟫ - ⟪u,d⟫⟪w,d⟫/⟪d,d⟫ = 4 - (-4)(-4)/8 = 2, ‖U‖²=‖W‖²=⟪u,u⟫-⟪u,d⟫²/⟪d,d⟫=8-2=6.
  -- cos = ⟪U,W⟫/(‖U‖‖W‖) = 2/6 = 1/3.
  have hdne : d ≠ 0 := by
    rw [hd]; exact sub_ne_zero.mpr (fun h => hij (regularTet.v_injective h.symm))
  set u := regularTet.v k - regularTet.v i with hu
  set w := regularTet.v l - regularTet.v i with hw'
  have hUW : (⟪U, W⟫ : ℝ) = 2 := by
    rw [hU, hW, inner_projOut_projOut d u w hdne, hidd, huw, hud, hwd]; norm_num
  have hUU : (⟪U, U⟫ : ℝ) = 6 := by
    rw [hU, inner_projOut_projOut d u u hdne, hidd, huu, hud]; norm_num
  have hWW : (⟪W, W⟫ : ℝ) = 6 := by
    rw [hW, inner_projOut_projOut d w w hdne, hidd, hww, hwd]; norm_num
  -- ‖U‖ = ‖W‖ = √6
  have hnU : ‖U‖ = Real.sqrt 6 := by
    rw [← Real.sqrt_sq (norm_nonneg U), ← real_inner_self_eq_norm_sq, hUU]
  have hnW : ‖W‖ = Real.sqrt 6 := by
    rw [← Real.sqrt_sq (norm_nonneg W), ← real_inner_self_eq_norm_sq, hWW]
  rw [hUW, hnU, hnW, ← Real.sqrt_mul (by norm_num) 6]
  rw [show (6 : ℝ) * 6 = 36 by norm_num, show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-! ## Concrete value: the orthogonal corner tetrahedron

The corner tetrahedron has vertices `0, e₀, e₁, e₂` (the origin and the three standard basis points).
The three edges meeting at the corner vertex `0` are mutually orthogonal, so each has dihedral angle
`π/2`.  We prove the three corner edges; the cube decomposes into such tetrahedra. -/

/-- The standard basis point `eₘ` in `Pt3` (the `m`-th coordinate is `1`, others `0`). -/
def basisPt (m : Fin 3) : Pt3 := EuclideanSpace.single m (1 : ℝ)

/-- Vertices of the orthogonal corner tetrahedron: `v 0 = 0`, `v (m+1) = e_m`. -/
def cornerVertex : Fin 4 → Pt3 :=
  fun i => if h : i = 0 then 0 else basisPt (i.pred h)

theorem cornerVertex_zero : cornerVertex 0 = 0 := by simp [cornerVertex]

theorem cornerVertex_succ (m : Fin 3) : cornerVertex m.succ = basisPt m := by
  simp [cornerVertex, Fin.succ_ne_zero, Fin.pred_succ]

theorem inner_basisPt (m n : Fin 3) :
    (⟪basisPt m, basisPt n⟫ : ℝ) = if m = n then 1 else 0 := by
  simp only [basisPt]
  rw [EuclideanSpace.inner_single_left]
  simp only [PiLp.single_apply, map_one, one_mul]

theorem cornerVertex_affineIndependent : AffineIndependent ℝ cornerVertex := by
  rw [affineIndependent_iff_of_fintype]
  intro w hsum hvec i
  -- ∑ w m • v m = 0 with ∑ w m = 0. Pair against basisPt n.
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hsum] at hvec
  -- take inner products with each basis point to recover w (m+1) = 0, then w 0 = 0 from the sum.
  have key : ∀ n : Fin 3, w n.succ = 0 := by
    intro n
    have := congrArg (fun x : Pt3 => (⟪x, basisPt n⟫ : ℝ)) hvec
    simp only [inner_zero_left] at this
    rw [Fin.sum_univ_four] at this
    simp only [inner_add_left, real_inner_smul_left, cornerVertex_zero, inner_zero_left,
      mul_zero] at this
    rw [show (1 : Fin 4) = (0 : Fin 3).succ from rfl,
        show (2 : Fin 4) = (1 : Fin 3).succ from rfl,
        show (3 : Fin 4) = (2 : Fin 3).succ from rfl,
        cornerVertex_succ, cornerVertex_succ, cornerVertex_succ] at this
    rw [inner_basisPt, inner_basisPt, inner_basisPt] at this
    fin_cases n <;> simp_all
  -- now from ∑ w = 0 and the three succ-weights vanishing, w 0 = 0.
  have h0 : w 0 = 0 := by
    rw [Fin.sum_univ_four] at hsum
    rw [show (1 : Fin 4) = (0 : Fin 3).succ from rfl,
        show (2 : Fin 4) = (1 : Fin 3).succ from rfl,
        show (3 : Fin 4) = (2 : Fin 3).succ from rfl] at hsum
    rw [key 0, key 1, key 2] at hsum
    simpa using hsum
  fin_cases i
  · exact h0
  · exact key 0
  · exact key 1
  · exact key 2

/-- The orthogonal corner tetrahedron `{0, e₀, e₁, e₂}` as a `Tet`. -/
def cornerTet : Tet where
  v := cornerVertex
  affIndep := cornerVertex_affineIndependent

/-- The three edges meeting at the corner vertex `0` are mutually orthogonal, so their projected
opposite vertices have inner product `0`: the two faces meet at a right angle.  We prove the
dihedral angle along each corner edge is `π/2`. -/
theorem cornerTet_dihedralAngle_right {j : Fin 4} (hj : j ≠ 0) :
    dihedralAngle cornerTet 0 j = Real.pi / 2 := by
  obtain ⟨hk_i, hk_j, hl_i, hl_j, hkl⟩ := otherTwo_spec (Ne.symm hj)
  set k := (otherTwo 0 j).1
  set l := (otherTwo 0 j).2
  -- the four indices 0, j, k, l are all distinct and nonzero except for 0.
  have hik : (0 : Fin 4) ≠ k := Ne.symm hk_i
  have hil : (0 : Fin 4) ≠ l := Ne.symm hl_i
  have hjk : j ≠ k := Ne.symm hk_j
  have hjl : j ≠ l := Ne.symm hl_j
  show InnerProductGeometry.angle
      (projOut (cornerTet.v j - cornerTet.v 0) (cornerTet.v k - cornerTet.v 0))
      (projOut (cornerTet.v j - cornerTet.v 0) (cornerTet.v l - cornerTet.v 0))
      = Real.pi / 2
  rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  -- cornerTet.v 0 = 0, so the difference vectors are just the basis points.
  have hv0 : cornerTet.v 0 = 0 := cornerVertex_zero
  -- make k, l opaque so we can substitute their successor forms.
  clear_value k l
  -- write j, k, l as successors of basis indices.
  obtain ⟨jm, rfl⟩ : ∃ m : Fin 3, m.succ = j := ⟨j.pred hj, Fin.succ_pred j hj⟩
  obtain ⟨km, rfl⟩ : ∃ m : Fin 3, m.succ = k := ⟨k.pred (Ne.symm hik), Fin.succ_pred k (Ne.symm hik)⟩
  obtain ⟨lm, rfl⟩ : ∃ m : Fin 3, m.succ = l := ⟨l.pred (Ne.symm hil), Fin.succ_pred l (Ne.symm hil)⟩
  show (⟪projOut (cornerTet.v jm.succ - cornerTet.v 0) (cornerTet.v km.succ - cornerTet.v 0),
        projOut (cornerTet.v jm.succ - cornerTet.v 0) (cornerTet.v lm.succ - cornerTet.v 0)⟫ : ℝ)
      = 0
  rw [hv0]
  simp only [sub_zero]
  show (⟪projOut (cornerTet.v jm.succ) (cornerTet.v km.succ),
        projOut (cornerTet.v jm.succ) (cornerTet.v lm.succ)⟫ : ℝ) = 0
  rw [show cornerTet.v = cornerVertex from rfl, cornerVertex_succ, cornerVertex_succ,
      cornerVertex_succ]
  -- basis indices are distinct: jm ≠ km, jm ≠ lm, km ≠ lm.
  have hjm_km : jm ≠ km := fun h => hjk (by rw [h])
  have hjm_lm : jm ≠ lm := fun h => hjl (by rw [h])
  have hkm_lm : km ≠ lm := fun h => hkl (by rw [h])
  -- inner products of distinct basis points are 0, of equal ones are 1.
  have hkm_jm : km ≠ jm := fun h => hjm_km h.symm
  have hlm_jm : lm ≠ jm := fun h => hjm_lm h.symm
  simp only [projOut, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    inner_basisPt, if_neg hkm_lm, if_neg hjm_lm, if_neg hkm_jm, if_neg hlm_jm]
  norm_num

end ProofsInTheBook.TetDihedral
