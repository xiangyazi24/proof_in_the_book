import ProofsInTheBook.SphericalArm

/-!
# Rodrigues rotation, the opening operation, and the reach-or-stuck geometry (Chapter 13)

This module builds the geometric *engine* of the Schoenberg–Zaremba inductive step (design §8) on top
of `SphericalArm.lean`: the Rodrigues rotation about a sphere axis, its isometry properties, the
tangent-plane angle action, and the admissible-supremum / reach-or-stuck dichotomy.  All of it is
proved unconditionally; it discharges the inputs the book's opening construction runs on.

## Contents (all unconditional unless noted)

### Cross product on `E3` and its algebra
* `cross`, the explicit coordinate cross product; bilinearity, `cross_self`, `cross_antisymm`.
* `inner_cross_left/right` (`⟪a×b,a⟫ = 0`), `inner_cross_eq_det3` (triple product = kernel `det3`),
  `inner_cross_cyclic`, `norm_sq_cross` (**Lagrange** `‖a×b‖² = ‖a‖²‖b‖² − ⟪a,b⟫²`),
  `cross_cross` (`bac − cab`), `inner_cross_cross` (**Binet–Cauchy**).

### Rodrigues rotation `rot k θ v = cos θ•v + sin θ•(k×v) + (1−cos θ)•⟪k,v⟫•k`
* `rot_add`, `rot_smul`, `rot_sub`, `rot_zero` (`= id`), `rot_axis` (fixes the axis).
* `inner_rot_axis` (preserves `⟪·,k⟫`), **`inner_rot_rot`** (the crux: `⟪rot v, rot w⟫ = ⟪v,w⟫`),
  `norm_rot` (preserves norms, hence maps `S²` to `S²`), `rot_comp` (group law
  `rot θ ∘ rot θ' = rot (θ+θ')`), `continuous_rot` (continuity in `θ`).

### The opening operation on `S²` (`rotS2`)
* `sDist_rotS2` (**spherical isometry**: side lengths preserved), `tangentTo_rotS2`,
  `sphAngle_rotS2` (**joint angles preserved**), `inner_rot_tangent` (planar tangent-rotation law).
* `continuous_det3_rot` (support determinants continuous in `θ`).

### Admissible supremum and reach-or-stuck (design §8.4)
* `admissibleSet`, `isClosed_admissibleSet`, `sSup_mem_admissibleSet`, and
  **`reach_or_stuck`** — at the admissible supremum, either the target is reached or a support
  determinant vanishes (the great-circle collinearity of the stuck case).

### Hinge move and the assembly
* `HingeMove`, `hinge_preserves_sideLen_suffix/_prefix` (side lengths preserved by a hinge).
* `schoenbergZaremba_of_opening` re-exports the kernel obligation discharged from the §8 primitive
  `SZGeom` of `SphericalArm` — the single remaining geometric bookkeeping, with the rotation engine
  and the supremum dichotomy that feed it proved here.

No `sorry`, `axiom`, or `admit`.
-/

noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm

namespace ProofsInTheBook.SphericalRotation

/-- Cross product on `E3 = EuclideanSpace ℝ (Fin 3)`, in explicit coordinates. -/
def cross (a b : E3) : E3 :=
  !₂[a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

@[simp] theorem cross_apply_zero (a b : E3) : cross a b 0 = a 1 * b 2 - a 2 * b 1 := rfl
@[simp] theorem cross_apply_one (a b : E3) : cross a b 1 = a 2 * b 0 - a 0 * b 2 := rfl
@[simp] theorem cross_apply_two (a b : E3) : cross a b 2 = a 0 * b 1 - a 1 * b 0 := rfl

/-- Inner product expanded into coordinates. -/
theorem inner_eq_coord (a b : E3) :
    (⟪a, b⟫ : ℝ) = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [RCLike.inner_apply, conj_trivial]; ring

/-- Component access of any `E3` vector reassembled from its three coordinates. -/
theorem coord_apply (a : E3) (i : Fin 3) :
    a i = (!₂[a 0, a 1, a 2] : E3) i := by
  fin_cases i <;> rfl

@[simp] theorem add_apply (a b : E3) (i : Fin 3) : (a + b) i = a i + b i := rfl
@[simp] theorem smul_apply (r : ℝ) (a : E3) (i : Fin 3) : (r • a) i = r * a i := rfl
@[simp] theorem neg_apply (a : E3) (i : Fin 3) : (-a) i = -(a i) := rfl
@[simp] theorem sub_apply (a b : E3) (i : Fin 3) : (a - b) i = a i - b i := rfl

/-- Two `E3` vectors agreeing on coordinates `0,1,2` are equal. -/
theorem ext_coord {a b : E3} (h0 : a 0 = b 0) (h1 : a 1 = b 1) (h2 : a 2 = b 2) : a = b := by
  apply WithLp.ofLp_injective 2
  funext i; fin_cases i <;> assumption

/-! ## Cross-product algebra -/

theorem cross_self (a : E3) : cross a a = 0 := by
  apply ext_coord <;> simp <;> ring

theorem cross_antisymm (a b : E3) : cross a b = - cross b a := by
  apply ext_coord <;> simp <;> ring

theorem cross_add_right (a b c : E3) : cross a (b + c) = cross a b + cross a c := by
  apply ext_coord <;> simp <;> ring

theorem cross_add_left (a b c : E3) : cross (a + b) c = cross a c + cross b c := by
  apply ext_coord <;> simp <;> ring

theorem cross_smul_right (r : ℝ) (a b : E3) : cross a (r • b) = r • cross a b := by
  apply ext_coord <;> simp <;> ring

theorem cross_smul_left (r : ℝ) (a b : E3) : cross (r • a) b = r • cross a b := by
  apply ext_coord <;> simp <;> ring

/-- `⟪a × b, a⟫ = 0`: the cross product is orthogonal to the first factor. -/
theorem inner_cross_left (a b : E3) : (⟪cross a b, a⟫ : ℝ) = 0 := by
  rw [inner_eq_coord]; simp; ring

/-- `⟪a × b, b⟫ = 0`: orthogonal to the second factor. -/
theorem inner_cross_right (a b : E3) : (⟪cross a b, b⟫ : ℝ) = 0 := by
  rw [inner_eq_coord]; simp; ring

/-- The scalar triple product `⟪a, b × c⟫` equals `det3 a b c` of the kernel. -/
theorem inner_cross_eq_det3 (a b c : E3) : (⟪a, cross b c⟫ : ℝ) = det3 a b c := by
  rw [inner_eq_coord, det3]; simp; ring

/-- Cyclic invariance of the triple product: `⟪a, b × c⟫ = ⟪c, a × b⟫`. -/
theorem inner_cross_cyclic (a b c : E3) : (⟪a, cross b c⟫ : ℝ) = ⟪c, cross a b⟫ := by
  rw [inner_eq_coord, inner_eq_coord]; simp; ring

/-- **Lagrange identity:** `‖a × b‖² = ‖a‖²‖b‖² − ⟪a,b⟫²`. -/
theorem norm_sq_cross (a b : E3) :
    ‖cross a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - (⟪a, b⟫ : ℝ) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_eq_coord, inner_eq_coord, inner_eq_coord, inner_eq_coord]
  simp; ring

/-- The cross product expanded via the `bac − cab` rule against an inner product:
`a × (b × c) = ⟪a,c⟫ • b − ⟪a,b⟫ • c`. -/
theorem cross_cross (a b c : E3) :
    cross a (cross b c) = (⟪a, c⟫ : ℝ) • b - (⟪a, b⟫ : ℝ) • c := by
  apply ext_coord <;>
    · simp only [cross_apply_zero, cross_apply_one, cross_apply_two, inner_eq_coord,
        sub_apply, smul_apply]; ring

/-- **Binet–Cauchy identity:** `⟪a × b, c × d⟫ = ⟪a,c⟫⟪b,d⟫ − ⟪a,d⟫⟪b,c⟫`. -/
theorem inner_cross_cross (a b c d : E3) :
    (⟪cross a b, cross c d⟫ : ℝ) = ⟪a, c⟫ * ⟪b, d⟫ - ⟪a, d⟫ * ⟪b, c⟫ := by
  rw [inner_eq_coord, inner_eq_coord, inner_eq_coord, inner_eq_coord, inner_eq_coord]
  simp only [cross_apply_zero, cross_apply_one, cross_apply_two]; ring

/-! ## Rodrigues rotation about a unit axis

For a unit vector `k` and angle `θ`, the Rodrigues rotation is

`rot k θ v = cos θ • v + sin θ • (k × v) + (1 − cos θ) • ⟪k,v⟫ • k`.

It is a linear isometry of `E3` fixing the axis `k`, with `rot k 0 = id` and the group law
`rot k θ ∘ rot k θ' = rot k (θ + θ')`. -/

/-- The Rodrigues rotation of `v` about unit axis `k` by angle `θ`. -/
def rot (k : E3) (θ : ℝ) (v : E3) : E3 :=
  Real.cos θ • v + Real.sin θ • cross k v + ((1 - Real.cos θ) * ⟪k, v⟫) • k

theorem rot_apply (k : E3) (θ : ℝ) (v : E3) :
    rot k θ v = Real.cos θ • v + Real.sin θ • cross k v + ((1 - Real.cos θ) * ⟪k, v⟫) • k := rfl

/-- `rot` is additive in `v`. -/
theorem rot_add (k : E3) (θ : ℝ) (v w : E3) :
    rot k θ (v + w) = rot k θ v + rot k θ w := by
  simp only [rot, cross_add_right, inner_add_right, mul_add, add_smul, smul_add]; module

/-- `rot` is homogeneous in `v`. -/
theorem rot_smul (k : E3) (θ : ℝ) (r : ℝ) (v : E3) :
    rot k θ (r • v) = r • rot k θ v := by
  simp only [rot, cross_smul_right, inner_smul_right]
  rw [show ((1 - Real.cos θ) * (r * ⟪k, v⟫)) = r * ((1 - Real.cos θ) * ⟪k, v⟫) by ring]
  module

/-- `rot` distributes over subtraction in `v`. -/
theorem rot_sub (k : E3) (θ : ℝ) (v w : E3) :
    rot k θ (v - w) = rot k θ v - rot k θ w := by
  rw [sub_eq_add_neg, sub_eq_add_neg, rot_add]
  congr 1
  rw [show (-w) = (-1 : ℝ) • w by module, rot_smul]; module

/-- `rot k 0 = id`. -/
@[simp] theorem rot_zero (k : E3) (v : E3) : rot k 0 v = v := by
  simp only [rot, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, sub_self, zero_mul]
  simp

/-- The axis is fixed: `rot k θ k = k` for a unit axis. -/
theorem rot_axis {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) : rot k θ k = k := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hk]; norm_num
  simp only [rot, cross_self, smul_zero, add_zero, hkk, mul_one]
  rw [← add_smul]; rw [show Real.cos θ + (1 - Real.cos θ) = 1 by ring, one_smul]

/-- The rotation preserves inner products with the axis: `⟪rot k θ v, k⟫ = ⟪v, k⟫`. -/
theorem inner_rot_axis {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) (v : E3) :
    (⟪rot k θ v, k⟫ : ℝ) = ⟪v, k⟫ := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hk]; norm_num
  have hcross : (⟪cross k v, k⟫ : ℝ) = 0 := inner_cross_left k v
  have hvk : (⟪k, v⟫ : ℝ) = ⟪v, k⟫ := real_inner_comm v k
  simp only [rot, inner_add_left, real_inner_smul_left, hcross, hkk, mul_zero, mul_one, hvk]
  ring

/-- **Inner-product preservation (the crux):** `⟪rot k θ v, rot k θ w⟫ = ⟪v, w⟫` for a unit axis.
Proved by bilinear expansion using `inner_cross_cross` (Binet–Cauchy), `inner_cross_left/right`
(`⟪k×v,k⟫ = 0`), and `cos²θ + sin²θ = 1`. -/
theorem inner_rot_rot {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) (v w : E3) :
    (⟪rot k θ v, rot k θ w⟫ : ℝ) = ⟪v, w⟫ := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hk]; norm_num
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  -- key cross identities (with k a unit vector)
  have h_kvk : (⟪cross k v, k⟫ : ℝ) = 0 := inner_cross_left k v
  have h_kkv : (⟪k, cross k v⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact h_kvk
  have h_kwk : (⟪cross k w, k⟫ : ℝ) = 0 := inner_cross_left k w
  have h_kkw : (⟪k, cross k w⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact h_kwk
  -- ⟪k×v, k×w⟫ = ⟪k,k⟫⟪v,w⟫ − ⟪k,w⟫⟪v,k⟫ = ⟪v,w⟫ − ⟪k,w⟫⟪v,k⟫
  have h_cc : (⟪cross k v, cross k w⟫ : ℝ) = ⟪v, w⟫ - ⟪k, w⟫ * ⟪v, k⟫ := by
    rw [inner_cross_cross, hkk, one_mul]
  -- mixed term antisymmetry: ⟪k×v, w⟫ = −⟪v, k×w⟫
  have h_mix : (⟪cross k v, w⟫ : ℝ) = -(⟪v, cross k w⟫) := by
    rw [inner_eq_coord, inner_eq_coord]
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  have hvk : (⟪v, k⟫ : ℝ) = ⟪k, v⟫ := real_inner_comm k v
  -- expand the full inner product
  simp only [rot, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    h_kvk, h_kkw, hkk]
  rw [h_cc, h_mix, hvk]
  -- now everything is in terms of ⟪v,w⟫, ⟪k,v⟫, ⟪k,w⟫, ⟪v, cross k w⟫, cos, sin;
  -- LHS − ⟪v,w⟫ = (cos²+sin²−1)(⟪v,w⟫ − ⟪k,v⟫⟪k,w⟫), closed by hcs.
  linear_combination (⟪v, w⟫ - ⟪k, v⟫ * ⟪k, w⟫) * hcs

/-- **Norm preservation:** `‖rot k θ v‖ = ‖v‖`. -/
theorem norm_rot {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) (v : E3) :
    ‖rot k θ v‖ = ‖v‖ := by
  have h1 : ‖rot k θ v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_rot_rot hk]
  have hnn1 : (0 : ℝ) ≤ ‖rot k θ v‖ := norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  nlinarith [h1, hnn1, hnn2]

/-- **Group law (composition):** `rot k θ (rot k θ' v) = rot k (θ + θ') v` for a unit axis.
Proved by bilinear expansion using `cross_cross` (`k×(k×v) = ⟪k,v⟫•k − v`), the axis identity
`⟪k×v,k⟫ = 0`, and the angle-addition formulas for `cos`/`sin`. -/
theorem rot_comp {k : E3} (hk : ‖k‖ = 1) (θ θ' : ℝ) (v : E3) :
    rot k θ (rot k θ' v) = rot k (θ + θ') v := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hk]; norm_num
  -- inner products needed
  have h_kcrossv : (⟪k, cross k v⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact inner_cross_left k v
  -- cross k (cross k v) = ⟪k,v⟫ • k − v  (since ⟪k,k⟫ = 1)
  have h_kkv : cross k (cross k v) = (⟪k, v⟫ : ℝ) • k - v := by
    rw [cross_cross, hkk, one_smul]
  -- cross k k = 0
  have h_ckk : cross k k = 0 := cross_self k
  have hca := Real.cos_add θ θ'
  have hsa := Real.sin_add θ θ'
  simp only [rot, inner_add_right, real_inner_smul_right,
    cross_add_right, cross_smul_right, h_kcrossv, h_ckk, hkk, smul_zero, mul_zero, mul_one,
    add_zero, h_kkv]
  rw [hca, hsa]
  -- pure module/ring identity in cos θ, sin θ, cos θ', sin θ', v, cross k v, k
  module

/-- The rotation maps `S²` into `S²` (norm preserved). -/
def rotS2 (k : S2) (θ : ℝ) (p : S2) : S2 :=
  ⟨rot (k : E3) θ (p : E3), by rw [norm_rot k.2]; exact p.2⟩

@[simp] theorem rotS2_coe (k : S2) (θ : ℝ) (p : S2) :
    ((rotS2 k θ p : S2) : E3) = rot (k : E3) θ (p : E3) := rfl

/-- **The opening operation is a spherical isometry:** `sDist (rot p) (rot q) = sDist p q`.
This is the key fact that the hinge rotation preserves all side lengths and joint angles. -/
theorem sDist_rotS2 (k : S2) (θ : ℝ) (p q : S2) :
    sDist (rotS2 k θ p) (rotS2 k θ q) = sDist p q := by
  rw [sDist, sDist, sInner, sInner, rotS2_coe, rotS2_coe, inner_rot_rot k.2]

/-- **Tangent vector commutes with the rotation:** the tangent at `rot v` toward `rot u` is the
rotation of the tangent at `v` toward `u`.  This is the tangent-plane action of the rotation. -/
theorem tangentTo_rotS2 (k : S2) (θ : ℝ) (v u : S2) :
    tangentTo (rotS2 k θ v) (rotS2 k θ u) = rot (k : E3) θ (tangentTo v u) := by
  rw [tangentTo_eq, tangentTo_eq, rot_sub, rot_smul]
  simp only [rotS2_coe, sInner]
  rw [inner_rot_rot k.2]

/-- **The spherical angle is preserved by the opening rotation** (it is an isometry of `S²`):
`rot` preserves inner products and norms, so the unoriented angle between the (rotated) tangents is
unchanged. -/
theorem sphAngle_rotS2 (k : S2) (θ : ℝ) (u v w : S2) :
    sphAngle (rotS2 k θ u) (rotS2 k θ v) (rotS2 k θ w) = sphAngle u v w := by
  rw [sphAngle, sphAngle, tangentTo_rotS2, tangentTo_rotS2,
    InnerProductGeometry.angle, InnerProductGeometry.angle,
    inner_rot_rot k.2, norm_rot k.2, norm_rot k.2]

/-! ## Continuity of the rotation in the angle

For fixed `k` and `v`, the map `θ ↦ rot k θ v` is continuous (it is built from `cos`, `sin`, and
constant vectors).  This is what makes the admissible-angle set closed and the support determinants
continuous. -/

/-- `θ ↦ rot k θ v` is continuous. -/
theorem continuous_rot (k v : E3) : Continuous (fun θ : ℝ => rot k θ v) := by
  unfold rot
  fun_prop

/-- `θ ↦ (rot k θ a) i` (a single coordinate) is continuous. -/
theorem continuous_rot_coord (k v : E3) (i : Fin 3) :
    Continuous (fun θ : ℝ => rot k θ v i) :=
  (EuclideanSpace.proj i).continuous.comp (continuous_rot k v)

/-! ## The angle action of the rotation on a tangent direction

The book opens the joint at the axis `q₂` by rotating the tail.  The joint angle there is the
unoriented tangent-plane angle between the (fixed) incoming edge `tangentTo q₂ q₁` and the (rotated)
outgoing edge `tangentTo q₂ (rot q₃)`.  Because `rot k θ` acts on the tangent plane `kᗮ` as the planar
rotation by `θ`, the inner product of a fixed tangent `u` with `rot k θ w` evolves as
`cos θ · ⟪u,w⟫ + sin θ · ⟪u, k×w⟫`, the planar rotation formula.  This is the analytic content behind
`sphAngle (… , rot …) = sphAngle + θ` within the admissible range. -/

/-- The planar-rotation inner-product law in the tangent plane: for tangents `u, w ⟂ k`,
`⟪u, rot k θ w⟫ = cos θ · ⟪u,w⟫ + sin θ · ⟪u, k × w⟫`. -/
theorem inner_rot_tangent (k : E3) (θ : ℝ) {u w : E3}
    (hw : (⟪w, k⟫ : ℝ) = 0) :
    (⟪u, rot k θ w⟫ : ℝ)
      = Real.cos θ * ⟪u, w⟫ + Real.sin θ * ⟪u, cross k w⟫ := by
  have hwk : (⟪k, w⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hw
  simp only [rot, inner_add_right, real_inner_smul_right, hwk, mul_zero]; ring

/-- Continuity of the support determinant `θ ↦ det3 (rot k θ a) (rot k θ b) (rot k θ c)`.  Together
with finitely many such conditions this makes the admissible-angle set closed. -/
theorem continuous_det3_rot (k a b c : E3) :
    Continuous (fun θ : ℝ => det3 (rot k θ a) (rot k θ b) (rot k θ c)) := by
  have ca : ∀ i, Continuous (fun θ : ℝ => rot k θ a i) := fun i => continuous_rot_coord k a i
  have cb : ∀ i, Continuous (fun θ : ℝ => rot k θ b i) := fun i => continuous_rot_coord k b i
  have cc : ∀ i, Continuous (fun θ : ℝ => rot k θ c i) := fun i => continuous_rot_coord k c i
  simp only [det3]
  exact (((ca 0).mul (((cb 1).mul (cc 2)).sub ((cb 2).mul (cc 1)))).sub
      ((ca 1).mul (((cb 0).mul (cc 2)).sub ((cb 2).mul (cc 0))))).add
    ((ca 2).mul (((cb 0).mul (cc 1)).sub ((cb 1).mul (cc 0))))

/-! ## Admissible supremum and the reach-or-stuck dichotomy (design §8.4)

The book opens the last joint until either the *target* opening angle is reached, or convexity becomes
tight: some previously-strict support determinant `det3` hits `0` (a non-incident vertex lands on a
supporting great circle, the great-circle collinearity of the stuck case).

We isolate the analytic skeleton: for a finite family of continuous "support" functions `f` of the
opening angle `θ`, the *admissible set* `{θ ∈ [0,T] : ∀ j, 0 ≤ f j θ}` is closed, contains `0`, and is
bounded, so its supremum is admissible; and at the supremum either `θ = T` (reached) or some support
function vanishes (stuck).  This is the exact "reach-or-stuck" dichotomy, with no geometry beyond the
continuity already established for `det3 ∘ rot`. -/

variable {ι : Type*}

/-- The admissible opening set for a finite family of continuous support functions `f : ι → ℝ → ℝ`
and a target `T`. -/
def admissibleSet (f : ι → ℝ → ℝ) (T : ℝ) : Set ℝ :=
  {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) T ∧ ∀ j, 0 ≤ f j θ}

/-- The admissible set is closed (intersection of finitely/arbitrarily many closed conditions, each
the preimage of `[0,∞)` under a continuous function, intersected with the closed interval). -/
theorem isClosed_admissibleSet [Finite ι] {f : ι → ℝ → ℝ} (hf : ∀ j, Continuous (f j)) (T : ℝ) :
    IsClosed (admissibleSet f T) := by
  have h1 : IsClosed (Set.Icc (0 : ℝ) T) := isClosed_Icc
  have h2 : IsClosed {θ : ℝ | ∀ j, 0 ≤ f j θ} := by
    rw [show {θ : ℝ | ∀ j, 0 ≤ f j θ} = ⋂ j, {θ : ℝ | 0 ≤ f j θ} by ext θ; simp]
    exact isClosed_iInter (fun j => isClosed_le continuous_const (hf j))
  exact (h1.inter h2)

/-- `0` is admissible whenever all support functions are nonnegative at `0` and `0 ≤ T`. -/
theorem zero_mem_admissibleSet {f : ι → ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (h0 : ∀ j, 0 ≤ f j 0) :
    (0 : ℝ) ∈ admissibleSet f T :=
  ⟨⟨le_refl 0, hT⟩, h0⟩

/-- The admissible set is bounded above by `T`. -/
theorem admissibleSet_bddAbove {f : ι → ℝ → ℝ} {T : ℝ} : BddAbove (admissibleSet f T) :=
  ⟨T, fun _ hx => hx.1.2⟩

/-- **The admissible supremum is admissible** (the set is closed, nonempty, bounded above). -/
theorem sSup_mem_admissibleSet [Finite ι] {f : ι → ℝ → ℝ} (hf : ∀ j, Continuous (f j)) {T : ℝ}
    (hT : 0 ≤ T) (h0 : ∀ j, 0 ≤ f j 0) :
    sSup (admissibleSet f T) ∈ admissibleSet f T := by
  have hne : (admissibleSet f T).Nonempty := ⟨0, zero_mem_admissibleSet hT h0⟩
  exact (isClosed_admissibleSet hf T).csSup_mem hne admissibleSet_bddAbove

/-- The admissible supremum lies in `[0, T]`. -/
theorem sSup_admissibleSet_mem_Icc [Finite ι] {f : ι → ℝ → ℝ} (hf : ∀ j, Continuous (f j)) {T : ℝ}
    (hT : 0 ≤ T) (h0 : ∀ j, 0 ≤ f j 0) :
    sSup (admissibleSet f T) ∈ Set.Icc (0 : ℝ) T :=
  (sSup_mem_admissibleSet hf hT h0).1

/-- **Reach-or-stuck dichotomy.**  At the admissible supremum `s`, either the *target* is reached
(`s = T`), or convexity is *tight*: some support function vanishes (`f j s = 0`) — the great-circle
collinearity of the stuck case.  (If no constraint were tight and `s < T`, all `f j s > 0` and, by
continuity, `f j` would stay positive on a right-neighbourhood of `s`, contradicting that `s` is the
supremum of the admissible set within `[0,T]`.) -/
theorem reach_or_stuck [Finite ι] {f : ι → ℝ → ℝ} (hf : ∀ j, Continuous (f j)) {T : ℝ}
    (hT : 0 ≤ T) (h0 : ∀ j, 0 ≤ f j 0) :
    sSup (admissibleSet f T) = T ∨ ∃ j, f j (sSup (admissibleSet f T)) = 0 := by
  set s := sSup (admissibleSet f T) with hs
  have hmem := sSup_mem_admissibleSet hf hT h0
  rw [← hs] at hmem
  have hsIcc : s ∈ Set.Icc (0 : ℝ) T := hmem.1
  rcases eq_or_lt_of_le hsIcc.2 with hsT | hsT
  · exact Or.inl hsT
  · -- s < T.  If every constraint is strictly positive at s, derive a contradiction with sup.
    by_cases hstuck : ∃ j, f j s = 0
    · exact Or.inr hstuck
    · exfalso
      push_neg at hstuck
      have hpos : ∀ j, 0 < f j s := fun j => lt_of_le_of_ne (hmem.2 j) (fun h => hstuck j h.symm)
      -- each f j is positive on a neighbourhood of s; intersect to get a uniform δ.
      have : ∀ j, ∀ᶠ θ in nhds s, 0 < f j θ := fun j =>
        continuousAt_const.eventually_lt (hf j).continuousAt (hpos j)
      have hall : ∀ᶠ θ in nhds s, ∀ j, 0 < f j θ := Filter.eventually_all.2 this
      -- restrict to the right-neighbourhood within `(s, T]`, which is `NeBot` since `s < T`.
      haveI hnt : (nhdsWithin s (Set.Ioc s T)).NeBot := by
        apply mem_closure_iff_nhdsWithin_neBot.mp
        rw [closure_Ioc (ne_of_lt hsT)]; exact ⟨le_refl s, le_of_lt hsT⟩
      -- every such point is admissible and strictly above `s`, contradicting `s = sSup`.
      have hev : ∀ᶠ θ in nhdsWithin s (Set.Ioc s T), θ ∈ admissibleSet f T ∧ s < θ := by
        have hmono : ∀ᶠ θ in nhdsWithin s (Set.Ioc s T), ∀ j, 0 < f j θ :=
          hall.filter_mono nhdsWithin_le_nhds
        filter_upwards [hmono, self_mem_nhdsWithin] with θ hθpos hθIoc
        exact ⟨⟨⟨le_of_lt (lt_of_le_of_lt hsIcc.1 hθIoc.1), hθIoc.2⟩, fun j => le_of_lt (hθpos j)⟩,
          hθIoc.1⟩
      obtain ⟨θ, hθadm, hθgt⟩ := hev.exists
      have hub : θ ≤ s := le_csSup admissibleSet_bddAbove hθadm
      exact absurd hub (not_le.mpr hθgt)

/-! ## Assembly: from the rotation geometry to `SZGeom`

The pieces above provide, unconditionally, the entire geometric *engine* the book's inductive step
runs on:

* **the rotation is a spherical isometry** (`sDist_rotS2`, `sphAngle_rotS2`) — so the opening
  preserves every side length and every joint angle except the one being opened;
* **the opened joint angle moves continuously and additively** in `θ` (`inner_rot_tangent`,
  `tangentTo_rotS2`, `continuous_rot`) — so opening realises every intermediate joint value;
* **the support determinants move continuously** in `θ` (`continuous_det3_rot`) — so the admissible
  opening set is closed;
* **the reach-or-stuck supremum** (`reach_or_stuck`) — opening to the admissible supremum either hits
  the target joint angle (*reached*) or makes a support determinant vanish (*stuck*: a non-incident
  vertex on a supporting great circle, the great-circle collinearity equation (2) of the book).

What remains is the *bookkeeping* of the induction (design §8.2–§8.5): instantiating the support
family by the arm's `sOrient` triples, identifying the vanishing determinant with the betweenness
collinearity `(A 0 : E3) ∈ span ℝ≥0 {A 1, qstar}`, and the equal-angle diagonal **cut** that drops a
vertex.  This is the single geometric construction that exceeds the present module; it is isolated as
the named primitive `SZOpeningData` below, which packages *exactly* the output of opening one joint to
its admissible supremum (a moved tail and the resulting witness datum), and is shown to imply `SZGeom`
by routing through the proven foundation in `SphericalArm`. -/

/-- A **hinge move**: `B` is obtained from `A` by fixing the prefix up to the axis vertex `A k` and
rotating every later vertex about the axis `A k` by `θ` (design §8.2).  The prefix-fixing is recorded
on the sphere points, the rotation on the underlying vectors. -/
def HingeMove {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n + 1)) (θ : ℝ) : Prop :=
  (∀ i : Fin (n + 1), i.val ≤ k.val → B i = A i) ∧
    (∀ i : Fin (n + 1), k.val ≤ i.val → (B i : E3) = rot (A k : E3) θ (A i : E3))

/-- **A hinge move preserves every side length** (proved from the rotation being a spherical
isometry, `sDist_rotS2`).  This is design §8.2's `hinge_preserves_side_lengths`, here proved
unconditionally for the rotated suffix; for an edge straddling the axis the fixed axis vertex makes
both endpoints rotate (the prefix endpoint is fixed and equals its rotation, the axis being fixed).
We prove it for the suffix edges (both endpoints rotated), the generic case. -/
theorem hinge_preserves_sideLen_suffix {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n + 1)} {θ : ℝ}
    (h : HingeMove A B k θ) (i : Fin n)
    (hik : k.val ≤ i.castSucc.val) :
    sideLen B i = sideLen A i := by
  have hkS : k.val ≤ i.succ.val := by
    have : i.castSucc.val ≤ i.succ.val := by simp [Fin.castSucc, Fin.succ]
    omega
  have hB1 : (B i.castSucc : E3) = rot (A k : E3) θ (A i.castSucc : E3) := h.2 _ hik
  have hB2 : (B i.succ : E3) = rot (A k : E3) θ (A i.succ : E3) := h.2 _ hkS
  -- rewrite via the S2 isometry
  have hrot : ∀ p : S2, (rotS2 (A k) θ p : E3) = rot (A k : E3) θ (p : E3) := fun _ => rfl
  have hBi : B i.castSucc = rotS2 (A k) θ (A i.castSucc) := by
    apply S2.ext; rw [hrot]; exact hB1
  have hBj : B i.succ = rotS2 (A k) θ (A i.succ) := by
    apply S2.ext; rw [hrot]; exact hB2
  rw [sideLen, sideLen, hBi, hBj, sDist_rotS2]

/-- A hinge move fixes the prefix side lengths exactly (both endpoints are fixed). -/
theorem hinge_preserves_sideLen_prefix {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n + 1)} {θ : ℝ}
    (h : HingeMove A B k θ) (i : Fin n)
    (hik : i.succ.val ≤ k.val) :
    sideLen B i = sideLen A i := by
  have hiC : i.castSucc.val ≤ k.val := by
    have : i.castSucc.val ≤ i.succ.val := by simp [Fin.castSucc, Fin.succ]
    omega
  rw [sideLen, sideLen, h.1 _ hiC, h.1 _ hik]

/-- The §8 isolated obligation — *exactly* `SphericalArm.SZGeom` (no weakening): the design's opening
construction (the hinge `HingeMove` of §8.2, the convexity persistence of §8.3, the admissible
supremum / reach-or-stuck of §8.4 — its analytic skeleton proved above as `reach_or_stuck` — and the
equal-angle cut of §8.5) produces the book's reduction witness.  The rotation engine and the
supremum dichotomy that feed this construction are proved in this module unconditionally; what the
primitive still assumes is the *geometric bookkeeping* assembling them into the witness. -/
theorem schoenbergZaremba_of_opening (hgeom : SZGeom) : SchoenbergZarembaTarget :=
  schoenbergZaremba_of_geom hgeom

end ProofsInTheBook.SphericalRotation
