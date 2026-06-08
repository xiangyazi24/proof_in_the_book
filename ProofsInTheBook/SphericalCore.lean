import ProofsInTheBook.SphericalSZ

/-!
# Constructing the opening core `SZOpeningCore` (Chapter 13, arm-side closing piece)

This module is the last arm-side piece of the Schoenberg–Zaremba spherical arm lemma.  Its goal is to
*discharge* the named primitive `ProofsInTheBook.SphericalSZ.SZOpeningCore` — the elementary raw output
of the design §8 opening construction — by instantiating the abstract rotation engine of
`SphericalRotation.lean` on the arm's concrete `sOrient` support triples, with convexity persistence,
so that the conditional `schoenbergZaremba_of_core` becomes the **unconditional** spherical arm lemma.

## The structure of the opening step

`SZOpeningCore` is, after unfolding, exactly the geometric inductive step at level `(n+1)`:

* always the weak endpoint bound `endpt A ≤ endpt B`, and
* whenever some joint of `B` is strictly wider, *either* a stuck vertex `qstar` carrying the
  elementary `StuckData` (the closing support `det3 (A 0)(A 1) qstar = 0`, the two convex-position
  Gram signs, the opening / sub-comparison / equal-side bounds) *or* the direct strict bound.

The engine of `SphericalRotation.lean` supplies, **unconditionally**:

* the Rodrigues rotation `rotS2 (A n) θ` is a spherical isometry (`sDist_rotS2`, `sphAngle_rotS2`),
  so opening the last joint about the axis `A n` preserves every side length and every other joint;
* the tangent-plane action `inner_rot_tangent` and `continuous_rot`, so the opened joint moves
  continuously in `θ`;
* the support determinants `θ ↦ det3 (rot a)(rot b)(rot c)` are continuous (`continuous_det3_rot`);
* the admissible-supremum / `reach_or_stuck` dichotomy over an *abstract* finite support family.

## What this module adds

It performs the **concrete instantiation** of that abstract family by the arm's constraint
functions and the convex-position bookkeeping the book's stuck data demands.  The genuinely new,
unconditional content proved here:

* **Rotation-invariance of the determinant under a jointly-rotated triple**
  (`det3_rot_rot_rot`): `det3 (rot a)(rot b)(rot c) = det3 a b c`.  Hence the **tail-internal** and
  **head-internal** `sOrient` triples are `θ`-INVARIANT and stay nonnegative from the initial arm —
  only the **mixed** (fixed head vs rotated tail) triples and the target-angle bound are genuine
  `θ`-dependent constraints.
* the **opened-joint realization** law `cos_jointAngle_open`: when the axis is the base vertex, the
  cosine of the opened joint angle evolves as the planar-rotation formula
  `cos θ · ⟪u,w⟫ + sin θ · ⟪u, k × w⟫` of the two fixed tangents, the analytic content behind
  "opening realises every intermediate joint value".

The remainder — assembling these into the full §8 inductive step with the precise convex-position
sign bookkeeping — is developed below; the irreducible residue (if any) is named honestly.

No `sorry`, `axiom`, or `admit`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ

namespace ProofsInTheBook.SphericalCore

/-! ## Determinant invariance under a jointly-rotated triple

The scalar triple product is invariant under a common rotation: `det3 (rot a)(rot b)(rot c) =
det3 a b c`.  This is the algebraic fact that makes the **tail-internal** and **head-internal**
`sOrient` support triples `θ`-INVARIANT: when all three vertices of a support triple lie in the
rotated tail (or all three in the fixed head), the rotation acts jointly and the determinant — hence
the support sign — is unchanged from the initial arm, where it is nonnegative by convexity.

We prove it from the inner-product preservation `inner_rot_rot` together with the cross-product
identity `rot k θ (a × b) = (rot k θ a) × (rot k θ b)`, via the triple-product/cross identity
`det3 a b c = ⟪a, b × c⟫`. -/

/-- The Rodrigues rotation commutes with the cross product: `rot k θ (a × b) = (rot k θ a) × (rot k θ
b)` for a unit axis `k`.  Proved by expanding both sides through the engine's cross-product algebra
(`cross_cross`, the `bac − cab` rule, with `k` a unit axis so `k × (k × v) = ⟪k,v⟫•k − v`) into a
common basis and closing with `module` after substituting `cos²θ + sin²θ = 1`. -/
theorem rot_cross {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) (a b : E3) :
    rot k θ (cross a b) = cross (rot k θ a) (rot k θ b) := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hk]; norm_num
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hkk1 : (k 0) ^ 2 + (k 1) ^ 2 + (k 2) ^ 2 = 1 := by
    rw [inner_eq_coord] at hkk; linear_combination hkk
  apply ext_coord
  · simp only [rot, cross_apply_zero, cross_apply_one, cross_apply_two, add_apply, smul_apply,
      inner_eq_coord]
    linear_combination (Real.cos θ*Real.sin θ*(a 0)*(b 1)*(k 1) + Real.cos θ*Real.sin θ*(a 0)*(b 2)*(k 2) - Real.cos θ*Real.sin θ*(a 1)*(b 0)*(k 1) - Real.cos θ*Real.sin θ*(a 2)*(b 0)*(k 2) - Real.cos θ*(a 1)*(b 2) + Real.cos θ*(a 2)*(b 1) - Real.sin θ^2*(a 1)*(b 2) + Real.sin θ^2*(a 2)*(b 1) - Real.sin θ*(a 0)*(b 1)*(k 1) - Real.sin θ*(a 0)*(b 2)*(k 2) + Real.sin θ*(a 1)*(b 0)*(k 1) + Real.sin θ*(a 2)*(b 0)*(k 2) + (a 1)*(b 2) - (a 2)*(b 1)) * hkk1 + (-(a 0)*(b 1)*(k 0)*(k 2) + (a 0)*(b 2)*(k 0)*(k 1) + (a 1)*(b 0)*(k 0)*(k 2) + (a 1)*(b 2)*(k 1)^2 + (a 1)*(b 2)*(k 2)^2 - (a 1)*(b 2) - (a 2)*(b 0)*(k 0)*(k 1) - (a 2)*(b 1)*(k 1)^2 - (a 2)*(b 1)*(k 2)^2 + (a 2)*(b 1)) * hcs
  · simp only [rot, cross_apply_zero, cross_apply_one, cross_apply_two, add_apply, smul_apply,
      inner_eq_coord]
    linear_combination (-Real.cos θ^2*(a 0)*(b 2) + Real.cos θ^2*(a 2)*(b 0) - Real.cos θ*Real.sin θ*(a 0)*(b 1)*(k 0) + Real.cos θ*Real.sin θ*(a 1)*(b 0)*(k 0) + Real.cos θ*Real.sin θ*(a 1)*(b 2)*(k 2) - Real.cos θ*Real.sin θ*(a 2)*(b 1)*(k 2) + Real.cos θ*(a 0)*(b 2) - Real.cos θ*(a 2)*(b 0) + Real.sin θ*(a 0)*(b 1)*(k 0) - Real.sin θ*(a 1)*(b 0)*(k 0) - Real.sin θ*(a 1)*(b 2)*(k 2) + Real.sin θ*(a 2)*(b 1)*(k 2)) * hkk1 + (-(a 0)*(b 1)*(k 1)*(k 2) + (a 0)*(b 2)*(k 1)^2 + (a 1)*(b 0)*(k 1)*(k 2) - (a 1)*(b 2)*(k 0)*(k 1) - (a 2)*(b 0)*(k 1)^2 + (a 2)*(b 1)*(k 0)*(k 1)) * hcs
  · simp only [rot, cross_apply_zero, cross_apply_one, cross_apply_two, add_apply, smul_apply,
      inner_eq_coord]
    linear_combination (Real.cos θ^2*(a 0)*(b 1) - Real.cos θ^2*(a 1)*(b 0) - Real.cos θ*Real.sin θ*(a 0)*(b 2)*(k 0) - Real.cos θ*Real.sin θ*(a 1)*(b 2)*(k 1) + Real.cos θ*Real.sin θ*(a 2)*(b 0)*(k 0) + Real.cos θ*Real.sin θ*(a 2)*(b 1)*(k 1) - Real.cos θ*(a 0)*(b 1) + Real.cos θ*(a 1)*(b 0) + Real.sin θ*(a 0)*(b 2)*(k 0) + Real.sin θ*(a 1)*(b 2)*(k 1) - Real.sin θ*(a 2)*(b 0)*(k 0) - Real.sin θ*(a 2)*(b 1)*(k 1)) * hkk1 + (-(a 0)*(b 1)*(k 2)^2 + (a 0)*(b 2)*(k 1)*(k 2) + (a 1)*(b 0)*(k 2)^2 - (a 1)*(b 2)*(k 0)*(k 2) - (a 2)*(b 0)*(k 1)*(k 2) + (a 2)*(b 1)*(k 0)*(k 2)) * hcs

/-- **Determinant invariance under a jointly-rotated triple.**  `det3 (rot k θ a)(rot k θ b)(rot k θ
c) = det3 a b c` for a unit axis `k`.  Via the triple-product bridge `det3 x y z = ⟪x, y × z⟫`,
the cross commutation `rot_cross`, and the inner-product preservation `inner_rot_rot`. -/
theorem det3_rot_rot_rot {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) (a b c : E3) :
    det3 (rot k θ a) (rot k θ b) (rot k θ c) = det3 a b c := by
  rw [← inner_cross_eq_det3, ← inner_cross_eq_det3, ← rot_cross hk, inner_rot_rot hk]

/-- The same invariance for the kernel's `sOrient` (the `S²` signed volume) under the spherical
rotation `rotS2`.  Hence a support triple all of whose vertices are jointly rotated keeps its sign. -/
theorem sOrient_rotS2 (k : S2) (θ : ℝ) (a b c : S2) :
    sOrient (rotS2 k θ a) (rotS2 k θ b) (rotS2 k θ c) = sOrient a b c := by
  simp only [sOrient, rotS2_coe]
  exact det3_rot_rot_rot k.2 θ (a : E3) (b : E3) (c : E3)

/-! ## The opened-joint realization law (axis = base vertex)

The book opens the last joint at vertex `A n` by rotating the tail vertex about the axis `A n`.  The
incoming edge `tangentTo (A n) (A (n-1))` is *fixed*; the outgoing edge is the tangent toward the
*rotated* tail vertex.  Because the rotation axis IS the base vertex, the tangent at the (fixed) base
toward the rotated target is exactly the rotation of the original tangent — so the opened joint angle
evolves by the planar-rotation law in the tangent plane.  This is the analytic content behind
"opening realises every intermediate joint value" and is the precise variant of `tangentTo_rotS2`
needed when only the *target* (not the base) is rotated. -/

/-- **Tangent at the axis-vertex toward a rotated target = rotation of the tangent.**  When the base
point `k` is exactly the rotation axis, `tangentTo k (rotS2 k θ q) = rot (k:E3) θ (tangentTo k q)`
(the axis is fixed by `rot`, and `rot` preserves inner products). -/
theorem tangentTo_rotS2_axis (k : S2) (θ : ℝ) (q : S2) :
    tangentTo k (rotS2 k θ q) = rot (k : E3) θ (tangentTo k q) := by
  rw [tangentTo_eq, tangentTo_eq, rot_sub, rot_smul, rot_axis k.2]
  have hin : sInner (rotS2 k θ q) k = sInner q k := by
    simp only [sInner, rotS2_coe]; rw [inner_rot_axis k.2]
  rw [hin]
  rfl

/-- **The opened-joint angle moves by the planar-rotation law.**  The cosine-numerator of the opened
joint angle at axis `k` between the fixed incoming tangent `tangentTo k p` and the outgoing tangent
toward the rotated target `rotS2 k θ q` is
`cos θ · ⟪tangentTo k p, tangentTo k q⟫ + sin θ · ⟪tangentTo k p, k × tangentTo k q⟫` — the planar
rotation of a fixed tangent.  (The tangent `tangentTo k q ⟂ k`, so `inner_rot_tangent` applies.) -/
theorem inner_tangent_opened (k : S2) (θ : ℝ) (p q : S2) :
    (⟪tangentTo k p, tangentTo k (rotS2 k θ q)⟫ : ℝ)
      = Real.cos θ * ⟪tangentTo k p, tangentTo k q⟫
        + Real.sin θ * ⟪tangentTo k p, cross (k : E3) (tangentTo k q)⟫ := by
  rw [tangentTo_rotS2_axis]
  exact inner_rot_tangent (k : E3) θ (tangentTo_orthogonal k q)

/-! ## The concrete opening operation on an arm

The book opens the *last* joint of the arm `A : Fin (n+2) → S2` — the joint at the penultimate vertex
`A (Fin.last n).castSucc` (index `n`), between the fixed neighbour at index `n-1` and the tail vertex
at index `n+1`.  We rotate *only the tail vertex* (index `n+1`) about the axis `A ⟨n,_⟩`; every other
vertex is fixed.  This is the single hinge whose admissible supremum drives the inductive step.

`openArm A θ` is that moved arm.  Because the rotation axis is the fixed vertex `A ⟨n,_⟩`, the moved
arm shares with `A`:
* every side length (the prefix sides are untouched; the last side has the axis as one endpoint, fixed
  by `rot`, and the tail endpoint rotated — preserved because `rot` preserves inner products with the
  axis);
* every support triple all of whose vertices avoid the tail (jointly fixed) and, by `det3_rot_rot_rot`,
  every triple all of whose vertices lie in the rotated part (there is only one rotated vertex, so the
  latter is vacuous here, but the invariance is what makes the *general* tail-internal triples
  invariant in the book's multi-vertex tail). -/

/-- The arm obtained by opening the last joint of `A` by angle `θ`: rotate the tail vertex (index
`n+1`) about the axis vertex `A ⟨n,_⟩`, fixing every other vertex. -/
def openArm {n : ℕ} (A : Fin (n + 1 + 1) → S2) (θ : ℝ) : Fin (n + 1 + 1) → S2 :=
  fun i => if i.val ≤ n then A i else rotS2 (A ⟨n, by omega⟩) θ (A i)

/-- The axis vertex (index `n`) of the opening. -/
def openAxis {n : ℕ} (A : Fin (n + 1 + 1) → S2) : S2 := A ⟨n, by omega⟩

@[simp] theorem openArm_zero {n : ℕ} (A : Fin (n + 1 + 1) → S2) (θ : ℝ) :
    openArm A θ 0 = A 0 := by
  simp only [openArm]
  rw [if_pos (show (0 : Fin (n + 1 + 1)).val ≤ n by simp)]

/-- The opened arm fixes every vertex up to and including the axis (index `≤ n`). -/
theorem openArm_fixed {n : ℕ} (A : Fin (n + 1 + 1) → S2) (θ : ℝ) {i : Fin (n + 1 + 1)}
    (hi : i.val ≤ n) : openArm A θ i = A i := by
  simp only [openArm]; rw [if_pos hi]

/-- The opened arm rotates the tail vertex (index `n+1`, i.e. `Fin.last`). -/
theorem openArm_last {n : ℕ} (A : Fin (n + 1 + 1) → S2) (θ : ℝ) :
    openArm A θ (Fin.last (n + 1)) = rotS2 (openAxis A) θ (A (Fin.last (n + 1))) := by
  simp only [openArm, openAxis, Fin.last]
  rw [if_neg (by omega)]

/-- The opening preserves the distance from the axis vertex to the (rotated) tail vertex: the axis is
fixed by `rot`, which preserves inner products with the axis. -/
theorem sDist_axis_openLast {n : ℕ} (A : Fin (n + 1 + 1) → S2) (θ : ℝ) :
    sDist (openAxis A) (openArm A θ (Fin.last (n + 1)))
      = sDist (openAxis A) (A (Fin.last (n + 1))) := by
  rw [openArm_last, sDist, sDist, sInner, sInner, rotS2_coe]
  congr 1
  have h := inner_rot_axis (openAxis A).2 θ (A (Fin.last (n + 1)) : E3)
  rw [real_inner_comm (rot (openAxis A : E3) θ (A (Fin.last (n + 1)) : E3)) (openAxis A : E3), h,
      real_inner_comm (A (Fin.last (n + 1)) : E3) (openAxis A : E3)]

/-- **The opening preserves every side length.**  The prefix sides (both endpoints `≤ n`) are fixed;
the final side has the axis vertex (index `n`, fixed) and the tail vertex (index `n+1`, rotated about
the axis), preserved by `sDist_axis_openLast`. -/
theorem openArm_sideLen {n : ℕ} (A : Fin (n + 1 + 1) → S2) (θ : ℝ) (i : Fin (n + 1)) :
    sideLen (openArm A θ) i = sideLen A i := by
  rcases Nat.lt_or_ge i.val n with hlt | hge
  · -- both endpoints fixed: i.val < n means succ.val = i+1 ≤ n.
    have h1 : openArm A θ i.castSucc = A i.castSucc :=
      openArm_fixed A θ (by simp [Fin.castSucc]; omega)
    have h2 : openArm A θ i.succ = A i.succ :=
      openArm_fixed A θ (by simp [Fin.succ]; omega)
    rw [sideLen, sideLen, h1, h2]
  · -- i.val ≥ n; but i : Fin (n+1) so i.val ≤ n, hence i.val = n: the final side.
    have hin : i.val = n := by have := i.isLt; omega
    have hcast : i.castSucc = (⟨n, by omega⟩ : Fin (n + 1 + 1)) := by
      apply Fin.ext; simp [Fin.castSucc, hin]
    have hsucc : i.succ = Fin.last (n + 1) := by
      apply Fin.ext; simp [Fin.succ, Fin.last, hin]
    rw [sideLen, sideLen, hcast, hsucc]
    rw [openArm_fixed A θ (le_refl n)]
    have hax : A (⟨n, by omega⟩ : Fin (n + 1 + 1)) = openAxis A := rfl
    rw [hax]
    exact sDist_axis_openLast A θ

/-! ## Convexity persistence of the invariant support triples

For the opened arm, every support triple whose three vertices are *jointly fixed* (all indices `≤ n`)
keeps its `sOrient` value verbatim, and — by `sOrient_rotS2` (the invariance proved above) — every
triple whose three vertices are *jointly rotated* keeps its value too.  Only the **mixed** triples
(some fixed, some rotated) carry genuine `θ`-dependence.  Since the present hinge rotates a single
tail vertex (index `n+1`), the jointly-fixed triples are exactly those avoiding `Fin.last`; we record
their persistence, the convexity content the engine does not otherwise supply. -/

/-- A support triple of jointly-fixed vertices (all indices `≤ n`) keeps its orientation under the
opening: `sOrient (openArm A θ i)(openArm A θ j)(openArm A θ l) = sOrient (A i)(A j)(A l)`. -/
theorem sOrient_openArm_fixed {n : ℕ} (A : Fin (n + 1 + 1) → S2) (θ : ℝ)
    {i j l : Fin (n + 1 + 1)} (hi : i.val ≤ n) (hj : j.val ≤ n) (hl : l.val ≤ n) :
    sOrient (openArm A θ i) (openArm A θ j) (openArm A θ l) = sOrient (A i) (A j) (A l) := by
  rw [openArm_fixed A θ hi, openArm_fixed A θ hj, openArm_fixed A θ hl]

/-- A support triple of jointly-rotated vertices keeps its orientation under the opening (here all
three indices `> n`, i.e. all equal to `Fin.last`, hence degenerate; the lemma is stated in the
general `rotS2`-jointly-rotated form via `sOrient_rotS2`, the invariance that makes the book's
multi-vertex tail-internal triples `θ`-invariant). -/
theorem sOrient_jointlyRotated {n : ℕ} (A : Fin (n + 1 + 1) → S2) (θ : ℝ) (i j l : Fin (n + 1 + 1)) :
    sOrient (rotS2 (openAxis A) θ (A i)) (rotS2 (openAxis A) θ (A j))
        (rotS2 (openAxis A) θ (A l))
      = sOrient (A i) (A j) (A l) :=
  sOrient_rotS2 (openAxis A) θ (A i) (A j) (A l)

/-! ## The reach-or-stuck dichotomy on the arm's concrete support family

We now instantiate the engine's abstract `reach_or_stuck` on the arm's *concrete* support functions.
The constraints that govern the admissible opening of the last joint are the support determinants of
the moved arm.  By the invariance results above, the jointly-fixed and jointly-rotated determinants
are `θ`-constant; the genuinely `θ`-dependent constraints are the **mixed** triples (the fixed head
vertices against the rotated tail vertex) together with the target-angle bound.  We package a finite
family of such continuous constraints and read off the dichotomy. -/

/-- A finite family of mixed support functions for the opening of `A`'s last joint, each the support
determinant `θ ↦ det3 (A i)(A j)(rot (axis) θ (A (Fin.last (n+1))))` against the rotated tail vertex
(`i, j` ranging over the fixed head indices).  These are exactly the book's `θ`-dependent
constraints; each is continuous in `θ` (`continuous_mixedSupport`, built from `continuous_rot_coord`). -/
def mixedSupport {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (ij : Fin (n + 1 + 1) × Fin (n + 1 + 1)) : ℝ → ℝ :=
  fun θ => det3 (A ij.1 : E3) (A ij.2 : E3)
    (rot (openAxis A : E3) θ (A (Fin.last (n + 1)) : E3))

/-- Each mixed support function is continuous in `θ`. -/
theorem continuous_mixedSupport {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (ij : Fin (n + 1 + 1) × Fin (n + 1 + 1)) : Continuous (mixedSupport A ij) := by
  have hc : ∀ i : Fin 3,
      Continuous (fun θ : ℝ => rot (openAxis A : E3) θ (A (Fin.last (n + 1)) : E3) i) :=
    fun i => continuous_rot_coord (openAxis A : E3) (A (Fin.last (n + 1)) : E3) i
  show Continuous (fun θ : ℝ => det3 (A ij.1 : E3) (A ij.2 : E3)
    (rot (openAxis A : E3) θ (A (Fin.last (n + 1)) : E3)))
  simp only [det3]
  exact
    (((continuous_const.mul (((continuous_const).mul (hc 2)).sub ((continuous_const).mul (hc 1)))).sub
      ((continuous_const).mul (((continuous_const).mul (hc 2)).sub ((continuous_const).mul (hc 0))))).add
      ((continuous_const).mul (((continuous_const).mul (hc 1)).sub ((continuous_const).mul (hc 0)))))

/-- **The reach-or-stuck dichotomy on the arm's mixed support family.**  For the finite mixed-support
family with target `T ≥ 0`, all nonnegative at `θ = 0` (the initial convex arm), the admissible
supremum either reaches `T` (the target opening) or makes some mixed support determinant vanish (the
stuck great-circle collinearity).  This is the engine's `reach_or_stuck` instantiated on the concrete
arm constraints — the analytic skeleton of the book's §8.4, now carried on the genuine arm data. -/
theorem arm_reach_or_stuck {n : ℕ} (A : Fin (n + 1 + 1) → S2) {T : ℝ} (hT : 0 ≤ T)
    (h0 : ∀ ij : Fin (n + 1 + 1) × Fin (n + 1 + 1), 0 ≤ mixedSupport A ij 0) :
    sSup (admissibleSet (mixedSupport A) T) = T ∨
      ∃ ij : Fin (n + 1 + 1) × Fin (n + 1 + 1),
        mixedSupport A ij (sSup (admissibleSet (mixedSupport A) T)) = 0 :=
  reach_or_stuck (continuous_mixedSupport A) hT h0

/-! ## Status of the opening core, and the explicit chain to the arm lemma

The genuinely new, unconditional content delivered by this module:

* `rot_cross`, `det3_rot_rot_rot`, `sOrient_rotS2` — **rotation-invariance of the support
  determinant** under a jointly-rotated triple.  This is the convexity-persistence fact the engine did
  not supply: tail-internal and head-internal `sOrient` triples are `θ`-invariant.
* `tangentTo_rotS2_axis`, `inner_tangent_opened` — the **opened-joint realisation law** (the opened
  angle moves by the planar-rotation formula of the two fixed tangents).
* `openArm`, `openArm_sideLen`, `sDist_axis_openLast` — the **concrete opening operation** with full
  side-length preservation (every prefix side fixed, the last side preserved because the axis is the
  fixed vertex).
* `sOrient_openArm_fixed`, `sOrient_jointlyRotated` — **convexity persistence of the invariant
  triples** for the concrete opening.
* `mixedSupport`, `continuous_mixedSupport`, `arm_reach_or_stuck` — the **concrete instantiation** of
  the engine's `reach_or_stuck` on the arm's genuine `θ`-dependent mixed support family.

These strictly enlarge the proved substrate beneath `SZOpeningCore`: side-length preservation,
orientation-invariance of the non-mixed triples, the opened-angle realisation, and the reach-or-stuck
dichotomy on the concrete arm constraints are now all unconditional.  What remains *open* — and is
**not** wrapped, renamed, or faked here — is `ProofsInTheBook.SphericalSZ.SZOpeningCore` itself: the
final §8.2–§8.5 bookkeeping that converts the `arm_reach_or_stuck` output into the elementary
`StuckData` (the precise convex-position sign derivation at the tight mixed constraint, the IVT
matching of the target last joint in the reached case, and the equal-angle diagonal cut), under the
inductive hypothesis `SZComparison n`.  That residual is the genuine geometric heart of the
Schoenberg–Zaremba step; it is left as the honest open obligation, now resting on the substrate above.

The chain from it to the chapter's kernel obligation is fully proved and re-exported here, so that
discharging `SZOpeningCore` (with the help of the lemmas in this file) immediately yields the
**unconditional** spherical arm lemma. -/

/-- **The explicit chain `SZOpeningCore → SchoenbergZarembaTarget`**, re-exported through the proven
bridge `ProofsInTheBook.SphericalSZ.schoenbergZaremba_of_core`.  Once `SZOpeningCore` is discharged
(using the substrate proved in this module), the named kernel obligation `SchoenbergZarembaTarget`
holds unconditionally, hence so do `spherical_arm_mono` / `spherical_arm_mono_strict`. -/
theorem schoenbergZaremba_of_openingCore (hcore : SZOpeningCore) : SchoenbergZarembaTarget :=
  ProofsInTheBook.SphericalSZ.schoenbergZaremba_of_core hcore

end ProofsInTheBook.SphericalCore
