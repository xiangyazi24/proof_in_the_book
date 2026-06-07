import ProofsInTheBook.SphericalRotation
import ProofsInTheBook.SphericalCyclicTriple

/-!
# Spherical SSS congruence — the equal-sides / equal-joints endpoint rigidity (Chapter 13, §8.4)

This file proves the **R-cong** piece of the Schoenberg–Zaremba arm lemma: two spherical arms with
the same side lengths and the same interior joint angles have the same endpoint distance
(`endpt A = endpt B`, i.e. `sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n))`).

The route is *Gram congruence by strong induction*: rather than build an `SO(3)` element by hand we
propagate the full Gram congruence `⟪A i, A j⟫ = ⟪B i, B j⟫` for every pair of vertices, by strong
induction on `max i j`.  The decisive ingredients are:

* a **frame-coordinate determination lemma** (`eq_of_inner_frame_eq`): a vector of `E3` is determined
  by its three inner products against a frame `(p, q, p × q)` with `p × q ≠ 0` (proved by the bac–cab
  and Lagrange identities, no basis machinery);
* the **scalar-triple invariant** `det3`, whose square equals the Gram determinant of the three
  vectors (`det3_sq_eq_gram`), so equal Gram entries force equal `|det3|`, and whose sign is pinned by
  the convex cyclic orientation `CyclicTriplePos` (positive for both arms ⇒ the signs agree);
* the substrate's spherical cosine rule, which makes every consecutive-triple inner product local in
  the side lengths and the joint angle.

`CyclicTriplePos A` / `CyclicTriplePos B` are the only convex-orientation inputs.  They are *not*
vacuous: `SphericalCyclicTriple.cyclicTriplePos_triangle` proves them for every strictly convex
triangle.  They are exactly the residue the substrate already isolates (HINGE Lemma 2.3) and are
strictly weaker than `StrictConvexSphArm` would need to supply for a full discharge.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalCyclicTriple

namespace ProofsInTheBook.SphericalCongruence

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The frame-coordinate determination lemma. -/

/-- **Frame-coordinate determination.**  Two vectors with equal inner products against a frame
`(p, q, p × q)` (with `p × q ≠ 0`) are equal.  Proved directly from the bac–cab identity
(`cross_cross`) and the Lagrange identity (`norm_sq_cross`), avoiding all basis machinery. -/
theorem eq_of_inner_frame_eq {p q x y : E3} (h : cross p q ≠ 0)
    (hp : (⟪p, x⟫ : ℝ) = ⟪p, y⟫) (hq : (⟪q, x⟫ : ℝ) = ⟪q, y⟫)
    (hc : (⟪cross p q, x⟫ : ℝ) = ⟪cross p q, y⟫) : x = y := by
  rw [← sub_eq_zero]
  -- w := x - y is orthogonal to p, q, cross p q; show w = 0.
  set w := x - y with hw
  have hwp : (⟪w, p⟫ : ℝ) = 0 := by
    have : (⟪w, p⟫ : ℝ) = ⟪p, x⟫ - ⟪p, y⟫ := by
      rw [hw, inner_sub_left, real_inner_comm x p, real_inner_comm y p]
    rw [this, hp, sub_self]
  have hwq : (⟪w, q⟫ : ℝ) = 0 := by
    have : (⟪w, q⟫ : ℝ) = ⟪q, x⟫ - ⟪q, y⟫ := by
      rw [hw, inner_sub_left, real_inner_comm x q, real_inner_comm y q]
    rw [this, hq, sub_self]
  have hwc : (⟪w, cross p q⟫ : ℝ) = 0 := by
    have : (⟪w, cross p q⟫ : ℝ) = ⟪cross p q, x⟫ - ⟪cross p q, y⟫ := by
      rw [hw, inner_sub_left, real_inner_comm x (cross p q), real_inner_comm y (cross p q)]
    rw [this, hc, sub_self]
  -- bac–cab: cross w (cross p q) = ⟪w,q⟫ • p − ⟪w,p⟫ • q = 0.
  have hcwm : cross w (cross p q) = 0 := by
    rw [SphericalRotation.cross_cross, hwp, hwq, zero_smul, zero_smul, sub_zero]
  -- Lagrange: ‖cross w (p×q)‖² = ‖w‖²‖p×q‖² − ⟪w,p×q⟫².  LHS = 0, ⟪w,p×q⟫ = 0.
  have hlag := norm_sq_cross w (cross p q)
  rw [hcwm, norm_zero, hwc] at hlag
  have hmpos : (0 : ℝ) < ‖cross p q‖ ^ 2 := by
    have hne : ‖cross p q‖ ≠ 0 := by simpa [norm_eq_zero] using h
    positivity
  have hw2 : ‖w‖ ^ 2 = 0 := by nlinarith [hlag, hmpos, sq_nonneg (‖w‖)]
  have hwz : ‖w‖ = 0 := by nlinarith [hw2, norm_nonneg w]
  exact norm_eq_zero.mp hwz

/-! ## §2. The Gram-determinant identity for `det3`.

`det3 x y z ^ 2` equals the determinant of the `3×3` Gram matrix of `x, y, z`, a polynomial in the
six inner products.  Hence equal Gram entries force equal `det3` magnitude. -/

/-- **Gram-determinant identity.**  `det3 x y z ^ 2` is a polynomial in the six pairwise inner
products of `x, y, z` (the determinant of their Gram matrix). -/
theorem det3_sq_eq_gram (x y z : E3) :
    det3 x y z ^ 2 =
      (⟪x, x⟫ : ℝ) * (⟪y, y⟫ * ⟪z, z⟫ - ⟪y, z⟫ * ⟪z, y⟫)
        - ⟪x, y⟫ * (⟪y, x⟫ * ⟪z, z⟫ - ⟪y, z⟫ * ⟪z, x⟫)
        + ⟪x, z⟫ * (⟪y, x⟫ * ⟪z, y⟫ - ⟪y, y⟫ * ⟪z, x⟫) := by
  rw [det3]
  simp only [inner_eq_coord]
  ring

/-- If two triples have the same Gram matrix entries, their `det3`s have equal squares. -/
theorem det3_sq_congr {x y z x' y' z' : E3}
    (hxx : (⟪x, x⟫ : ℝ) = ⟪x', x'⟫) (hxy : (⟪x, y⟫ : ℝ) = ⟪x', y'⟫)
    (hxz : (⟪x, z⟫ : ℝ) = ⟪x', z'⟫) (hyx : (⟪y, x⟫ : ℝ) = ⟪y', x'⟫)
    (hyy : (⟪y, y⟫ : ℝ) = ⟪y', y'⟫) (hyz : (⟪y, z⟫ : ℝ) = ⟪y', z'⟫)
    (hzx : (⟪z, x⟫ : ℝ) = ⟪z', x'⟫) (hzy : (⟪z, y⟫ : ℝ) = ⟪z', y'⟫)
    (hzz : (⟪z, z⟫ : ℝ) = ⟪z', z'⟫) :
    det3 x y z ^ 2 = det3 x' y' z' ^ 2 := by
  rw [det3_sq_eq_gram, det3_sq_eq_gram, hxx, hxy, hxz, hyx, hyy, hyz, hzx, hzy, hzz]

/-- **Sign-pinned `det3` congruence.**  Two triples with equal Gram entries and both strictly
positively oriented (positive `det3`) have *equal* `det3`. -/
theorem det3_congr_of_pos {x y z x' y' z' : E3}
    (hxx : (⟪x, x⟫ : ℝ) = ⟪x', x'⟫) (hxy : (⟪x, y⟫ : ℝ) = ⟪x', y'⟫)
    (hxz : (⟪x, z⟫ : ℝ) = ⟪x', z'⟫) (hyx : (⟪y, x⟫ : ℝ) = ⟪y', x'⟫)
    (hyy : (⟪y, y⟫ : ℝ) = ⟪y', y'⟫) (hyz : (⟪y, z⟫ : ℝ) = ⟪y', z'⟫)
    (hzx : (⟪z, x⟫ : ℝ) = ⟪z', x'⟫) (hzy : (⟪z, y⟫ : ℝ) = ⟪z', y'⟫)
    (hzz : (⟪z, z⟫ : ℝ) = ⟪z', z'⟫)
    (hpos : 0 < det3 x y z) (hpos' : 0 < det3 x' y' z') :
    det3 x y z = det3 x' y' z' := by
  have hsq := det3_sq_congr hxx hxy hxz hyx hyy hyz hzx hzy hzz
  nlinarith [hsq, hpos, hpos', sq_nonneg (det3 x y z - det3 x' y' z'),
    sq_nonneg (det3 x y z + det3 x' y' z')]

/-! ## §3. Frame representation and the Gram transfer lemma.

Against the frame `(p, q, m := p × q)` with `m ≠ 0`, any vector `v` admits the explicit Cramer
representation `‖m‖² • v = (…) • p + (…) • q + ⟪m,v⟫ • m`.  Pairing with another vector `u` yields
the *Gram transfer* identity: `‖m‖² · ⟪u,v⟫` is a polynomial in the inner products of `u`, `v`
against the frame and in the frame's own Gram entries.  This is the engine that lets a matching frame
Gram + matching frame coordinates force matching `⟪u,v⟫`. -/

/-- The Cramer representation of `v` against the frame `(p, q, p × q)`. -/
theorem frame_repr {p q : E3} (h : cross p q ≠ 0) (v : E3) :
    (⟪cross p q, cross p q⟫ : ℝ) • v
      = ((⟪p, v⟫ : ℝ) * ⟪q, q⟫ - ⟪p, q⟫ * ⟪q, v⟫) • p
        + ((⟪p, p⟫ : ℝ) * ⟪q, v⟫ - ⟪p, q⟫ * ⟪p, v⟫) • q
        + (⟪cross p q, v⟫ : ℝ) • cross p q := by
  set m := cross p q with hm
  -- `d = ⟪m,m⟫ = ‖p‖²‖q‖² − ⟪p,q⟫²` (Lagrange).
  have hpm : (⟪p, m⟫ : ℝ) = 0 := by rw [hm]; rw [real_inner_comm]; exact inner_cross_left p q
  have hqm : (⟪q, m⟫ : ℝ) = 0 := by rw [hm]; rw [real_inner_comm]; exact inner_cross_right p q
  have hmp : (⟪m, p⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hpm
  have hmq : (⟪m, q⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hqm
  have hlag : (⟪m, m⟫ : ℝ) = ⟪p, p⟫ * ⟪q, q⟫ - ⟪p, q⟫ ^ 2 := by
    have hL := norm_sq_cross p q
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq] at hL
    rw [hm]; exact hL
  have hcrossp : (⟪cross p q, p⟫ : ℝ) = 0 := inner_cross_left p q
  have hcrossq : (⟪cross p q, q⟫ : ℝ) = 0 := inner_cross_right p q
  have hqp : (⟪q, p⟫ : ℝ) = ⟪p, q⟫ := (real_inner_comm q p).symm
  apply eq_of_inner_frame_eq h
  · -- ⟪p, d•v⟫ = ⟪p, RHS⟫
    simp only [inner_add_right, real_inner_smul_right, hpm, mul_zero, add_zero]
    -- ⟪m,m⟫·⟪p,v⟫ = (⟪p,v⟫⟪q,q⟫−⟪p,q⟫⟪q,v⟫)⟪p,p⟫ + (⟪p,p⟫⟪q,v⟫−⟪p,q⟫⟪p,v⟫)⟪p,q⟫
    rw [hlag]; ring
  · -- ⟪q, d•v⟫ = ⟪q, RHS⟫
    simp only [inner_add_right, real_inner_smul_right, hqm, mul_zero, add_zero]
    rw [hlag, hqp]; ring
  · -- ⟪m, d•v⟫ = ⟪m, RHS⟫
    simp only [inner_add_right, real_inner_smul_right, hcrossp, hcrossq, mul_zero, zero_add,
      add_zero]
    ring

/-- **Frame pairing identity.**  Pairing `frame_repr` with a vector `u` expresses
`‖p×q‖² · ⟪u,v⟫` as a polynomial in the inner products of `u, v` against the frame `(p,q,p×q)` and
the frame's own Gram entries. -/
theorem frame_pairing {p q : E3} (h : cross p q ≠ 0) (u v : E3) :
    (⟪cross p q, cross p q⟫ : ℝ) * ⟪u, v⟫
      = ((⟪p, v⟫ : ℝ) * ⟪q, q⟫ - ⟪p, q⟫ * ⟪q, v⟫) * ⟪u, p⟫
        + ((⟪p, p⟫ : ℝ) * ⟪q, v⟫ - ⟪p, q⟫ * ⟪p, v⟫) * ⟪u, q⟫
        + (⟪cross p q, v⟫ : ℝ) * ⟪u, cross p q⟫ := by
  have hr := frame_repr h v
  have := congrArg (fun w => (⟪u, w⟫ : ℝ)) hr
  simp only [inner_smul_right, inner_add_right] at this
  -- this : ⟪m,m⟫ * ⟪u,v⟫ = coef_a * ⟪u,p⟫ + coef_b * ⟪u,q⟫ + ⟪m,v⟫ * ⟪u,m⟫
  linarith [this]

/-- **The Gram transfer lemma (induction engine).**  Two frames `(p,q,p×q)`, `(p',q',p'×q')`
(both nondegenerate) whose `p,q`-Gram blocks agree, paired with vectors `u,v` and `u',v'` whose
coordinates against the two frames agree, have equal pairings `⟪u,v⟫ = ⟪u',v'⟫`.

`hmm` (the `p×q` self-inner product agreement) follows from the `p,q`-block agreement via Lagrange,
but is taken as an explicit hypothesis to keep the interface symmetric; it is discharged at the call
site. -/
theorem gram_transfer {p q u v p' q' u' v' : E3}
    (h : cross p q ≠ 0) (h' : cross p' q' ≠ 0)
    (hpp : (⟪p, p⟫ : ℝ) = ⟪p', p'⟫) (hpq : (⟪p, q⟫ : ℝ) = ⟪p', q'⟫)
    (hqq : (⟪q, q⟫ : ℝ) = ⟪q', q'⟫)
    (hmm : (⟪cross p q, cross p q⟫ : ℝ) = ⟪cross p' q', cross p' q'⟫)
    (hup : (⟪u, p⟫ : ℝ) = ⟪u', p'⟫) (huq : (⟪u, q⟫ : ℝ) = ⟪u', q'⟫)
    (hum : (⟪u, cross p q⟫ : ℝ) = ⟪u', cross p' q'⟫)
    (hpv : (⟪p, v⟫ : ℝ) = ⟪p', v'⟫) (hqv : (⟪q, v⟫ : ℝ) = ⟪q', v'⟫)
    (hmv : (⟪cross p q, v⟫ : ℝ) = ⟪cross p' q', v'⟫) :
    (⟪u, v⟫ : ℝ) = ⟪u', v'⟫ := by
  have hA := frame_pairing h u v
  have hB := frame_pairing h' u' v'
  -- The two pairing RHSs are equal by the matching hypotheses.
  rw [← hpp, ← hpq, ← hqq, ← hup, ← huq, ← hum, ← hpv, ← hqv, ← hmv, ← hmm] at hB
  -- Now hA, hB say ⟪m,m⟫·⟪u,v⟫ = R and ⟪m,m⟫·⟪u',v'⟫ = R with the same R.
  have hmpos : (0 : ℝ) < ⟪cross p q, cross p q⟫ := by
    have hne : ‖cross p q‖ ≠ 0 := by simpa [norm_eq_zero] using h
    have hpos2 : (0 : ℝ) < ‖cross p q‖ ^ 2 := by positivity
    rwa [← real_inner_self_eq_norm_sq] at hpos2
  have heq : (⟪cross p q, cross p q⟫ : ℝ) * ⟪u, v⟫
      = ⟪cross p q, cross p q⟫ * ⟪u', v'⟫ := by rw [hA, hB]
  exact mul_left_cancel₀ (ne_of_gt hmpos) heq

/-- For two distinct, non-antipodal unit vectors the cross product is nonzero. -/
theorem cross_ne_zero_of_shortArc {p q : S2} (h : ShortArc p q) :
    cross (p : E3) (q : E3) ≠ 0 := by
  -- ‖p×q‖² = 1 − ⟪p,q⟫²; and |⟪p,q⟫| < 1 since p ≠ ±q.
  intro hc
  have hnorm : ‖cross (p : E3) (q : E3)‖ ^ 2 = 1 - (sInner p q) ^ 2 := by
    rw [norm_sq_cross, p.2, q.2]; simp [sInner]
  rw [hc, norm_zero] at hnorm
  -- 0 = 1 − ⟪p,q⟫² ⟹ ⟪p,q⟫² = 1 ⟹ ⟪p,q⟫ = ±1 ⟹ p = ±q, contradicting ShortArc.
  have hsq : sInner p q * sInner p q = 1 := by nlinarith [hnorm]
  have habs : sInner p q = 1 ∨ sInner p q = -1 := mul_self_eq_one_iff.mp hsq
  rcases habs with h1 | h1
  · -- ⟪p,q⟫ = 1 ⟹ p = q
    exact h.1 (sDist_eq_zero_iff.mp (by rw [sDist, h1, Real.arccos_one]))
  · -- ⟪p,q⟫ = −1 ⟹ p = −q
    apply h.2
    have : sDist p q < Real.pi → False := by
      intro hlt; rw [sDist, h1, Real.arccos_neg_one] at hlt; exact lt_irrefl _ hlt
    by_contra hne
    exact this (sDist_lt_pi_of_not_antipodal hne)

/-! ## §4. Local geometry: consecutive sides and triples are local in sides + joints.

Equal side lengths give equal consecutive inner products; the spherical cosine rule makes every
consecutive-triple "diagonal" inner product `⟪A k, A (k+2)⟫` local in the two sides and the joint.
These are the only inner-product equalities the induction needs that are *not* furnished by the
inductive hypothesis. -/

/-- `⟪A i, A j⟫` (in `E3`) is `sInner (A i) (A j)`, the spherical inner product. -/
theorem inner_eq_sInner {n : ℕ} (A : Fin (n + 1) → S2) (i j : Fin (n + 1)) :
    (⟪(A i : E3), (A j : E3)⟫ : ℝ) = sInner (A i) (A j) := rfl

/-- Equal spherical distance gives equal spherical inner product (`cos` of `arccos`). -/
theorem sInner_eq_of_sDist_eq {p q p' q' : S2} (h : sDist p q = sDist p' q') :
    sInner p q = sInner p' q' := by
  have := congrArg Real.cos h
  rwa [cos_sDist, cos_sDist] at this

/-- **Consecutive-side congruence.**  Equal side lengths ⟹ equal consecutive inner products. -/
theorem inner_consecutive_eq {n : ℕ} {A B : Fin (n + 1) → S2}
    (hs : ∀ e : Fin n, sideLen A e = sideLen B e) (e : Fin n) :
    (⟪(A e.castSucc : E3), (A e.succ : E3)⟫ : ℝ) = ⟪(B e.castSucc : E3), (B e.succ : E3)⟫ := by
  have h := hs e
  rw [sideLen, sideLen] at h
  rw [inner_eq_sInner, inner_eq_sInner]
  exact sInner_eq_of_sDist_eq h

/-- **Consecutive-triple diagonal congruence (cosine rule).**  For a joint index `i : Fin (n-1)`,
the diagonal inner product `⟪A ⟨i⟩, A ⟨i+2⟩⟫` depends only on the two adjacent side lengths and the
joint angle, hence is equal between two arms with equal sides and equal joints. -/
theorem inner_diag_eq {n : ℕ} {A B : Fin (n + 1) → S2}
    (hs : ∀ e : Fin n, sideLen A e = sideLen B e)
    (hj : ∀ r : Fin (n - 1), jointAngle A r = jointAngle B r) (i : Fin (n - 1)) :
    (⟪(A ⟨i.val, by have := i.isLt; omega⟩ : E3),
        (A ⟨i.val + 2, by have := i.isLt; omega⟩ : E3)⟫ : ℝ)
      = ⟪(B ⟨i.val, by have := i.isLt; omega⟩ : E3),
        (B ⟨i.val + 2, by have := i.isLt; omega⟩ : E3)⟫ := by
  -- abbreviations for the three vertices of each arm
  set a₀ : S2 := A ⟨i.val, by have := i.isLt; omega⟩
  set a₁ : S2 := A ⟨i.val + 1, by have := i.isLt; omega⟩
  set a₂ : S2 := A ⟨i.val + 2, by have := i.isLt; omega⟩
  set b₀ : S2 := B ⟨i.val, by have := i.isLt; omega⟩
  set b₁ : S2 := B ⟨i.val + 1, by have := i.isLt; omega⟩
  set b₂ : S2 := B ⟨i.val + 2, by have := i.isLt; omega⟩
  -- the diagonal inner product is cos of the diagonal distance; apply the cosine rule
  rw [inner_eq_sInner, inner_eq_sInner]
  rw [show sInner a₀ a₂ = Real.cos (sDist a₀ a₂) from (cos_sDist a₀ a₂).symm,
    show sInner b₀ b₂ = Real.cos (sDist b₀ b₂) from (cos_sDist b₀ b₂).symm]
  rw [spherical_cosine_rule a₀ a₁ a₂, spherical_cosine_rule b₀ b₁ b₂]
  -- match the three local quantities: sDist a₀ a₁ = side i, sDist a₁ a₂ = side (i+1), joint i.
  have hi1 : i.val < n := by have := i.isLt; omega
  have hi2 : i.val + 1 < n := by have := i.isLt; omega
  -- side lengths
  have hside0 : sDist a₀ a₁ = sDist b₀ b₁ := by
    have := hs ⟨i.val, hi1⟩
    simp only [sideLen, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] at this
    simpa [a₀, a₁, b₀, b₁] using this
  have hside1 : sDist a₁ a₂ = sDist b₁ b₂ := by
    have := hs ⟨i.val + 1, hi2⟩
    simp only [sideLen, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] at this
    simpa [a₁, a₂, b₁, b₂] using this
  -- joint angle
  have hjoint : sphAngle a₀ a₁ a₂ = sphAngle b₀ b₁ b₂ := by
    have := hj i
    simp only [jointAngle] at this
    simpa [a₀, a₁, a₂, b₀, b₁, b₂] using this
  rw [hside0, hside1, hjoint]

/-! ## §5. The det3 cyclic identity and the sOrient evaluation of the frame coordinates. -/

/-- Cyclic invariance of `det3`: `det3 a b c = det3 c a b`. -/
theorem det3_cyclic (a b c : E3) : det3 a b c = det3 c a b := by
  rw [det3, det3]; ring

/-- `⟪a×b, a×b⟫ = ⟪a,a⟫⟪b,b⟫ − ⟪a,b⟫⟪b,a⟫` (Binet–Cauchy), so the frame normal's self inner product
is a polynomial in the `(a,b)`-Gram block. -/
theorem inner_cross_self_eq (a b : E3) :
    (⟪cross a b, cross a b⟫ : ℝ) = ⟪a, a⟫ * ⟪b, b⟫ - ⟪a, b⟫ * ⟪b, a⟫ := by
  rw [inner_cross_cross]

/-- `⟪cross a b, c⟫ = det3 a b c` (the cross product on the left). -/
theorem inner_cross_left_eq_det3 (a b c : E3) :
    (⟪cross a b, c⟫ : ℝ) = det3 a b c := by
  rw [real_inner_comm, inner_cross_eq_det3, det3, det3]; ring

/-- `⟪a, cross b c⟫ = det3 b c a` (the cross product on the right, cyclically rotated). -/
theorem inner_cross_right_eq_det3 (a b c : E3) :
    (⟪a, cross b c⟫ : ℝ) = det3 b c a := by
  rw [inner_cross_eq_det3, det3, det3]; ring

/-! ## §6. The Gram congruence: full pairwise inner-product equality, by strong induction.

The hypotheses are the convex cyclic-triple orientation of both arms (`CyclicTriplePos`), equal sides,
and equal joints.  The conclusion is the full Gram congruence `⟪A i, A j⟫ = ⟪B i, B j⟫` for all
vertices.  The induction is on `max i.val j.val`; the step uses the `gram_transfer` engine on the edge
frame `(A⟨r⟩, A⟨r+1⟩)` with `r = (max) − 2`. -/

/-- **Ordered Gram congruence** (the `i.val ≤ j.val` half).  By strong induction on `j.val`. -/
theorem gram_eq_ordered {n : ℕ} {A B : Fin (n + 1) → S2}
    (hcA : CyclicTriplePos A) (hcB : CyclicTriplePos B)
    (heA : ∀ i : Fin (n + 1), ShortArc (A i) (A (i + 1)))
    (heB : ∀ i : Fin (n + 1), ShortArc (B i) (B (i + 1)))
    (hs : ∀ e : Fin n, sideLen A e = sideLen B e)
    (hj : ∀ r : Fin (n - 1), jointAngle A r = jointAngle B r) :
    ∀ N : ℕ, ∀ i j : Fin (n + 1), i.val ≤ j.val → j.val ≤ N →
      (⟪(A i : E3), (A j : E3)⟫ : ℝ) = ⟪(B i : E3), (B j : E3)⟫ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro i j hij hjN
    -- self inner products are 1.
    by_cases hself : i.val = j.val
    · have : i = j := Fin.ext hself
      subst this
      rw [inner_eq_sInner, inner_eq_sInner, sInner_self, sInner_self]
    -- now i.val < j.val.
    have hlt : i.val < j.val := lt_of_le_of_ne hij hself
    -- consecutive side case: j = i + 1.
    by_cases hcons : j.val = i.val + 1
    · -- ⟪A i, A j⟫ is the side at e = ⟨i.val, _⟩.
      have hin : i.val < n := by omega
      have he := inner_consecutive_eq hs ⟨i.val, hin⟩
      -- identify castSucc/succ with i, j.
      have hcs : (⟨i.val, hin⟩ : Fin n).castSucc = i := by
        apply Fin.ext; simp [Fin.castSucc, Fin.castAdd, Fin.castLE]
      have hsc : (⟨i.val, hin⟩ : Fin n).succ = j := by
        apply Fin.ext; simp [Fin.succ]; omega
      rw [hcs, hsc] at he
      exact he
    -- general case: j.val ≥ i.val + 2 ≥ 2.
    have hj2 : i.val + 2 ≤ j.val := by omega
    -- the predecessor index of j and the frame base.
    have hjval2 : 2 ≤ j.val := by omega
    set r := j.val - 2 with hr
    have hrn : r + 2 = j.val := by omega
    have hr_lt : r < n := by have := j.isLt; omega
    have hr1_lt : r + 1 < n + 1 := by have := j.isLt; omega
    have hr_lt1 : r < n + 1 := by omega
    -- frame vertices
    set p : Fin (n + 1) := ⟨r, hr_lt1⟩ with hp
    set q : Fin (n + 1) := ⟨r + 1, hr1_lt⟩ with hq
    have hpval : p.val = r := rfl
    have hqval : q.val = r + 1 := rfl
    have hjval : j.val = r + 2 := by omega
    have hjeq : j = ⟨r + 2, by have := j.isLt; omega⟩ := by apply Fin.ext; simp [hjval]
    -- p + 1 = q (as Fin (n+1)), so heA at p gives ShortArc (A p) (A q).
    have hpq_succ : (p + 1 : Fin (n + 1)) = q := by
      have hplast : p ≠ Fin.last n := by
        intro hc; rw [hc, Fin.val_last] at hpval; omega
      apply Fin.ext
      rw [Fin.val_add_one, if_neg hplast, hpval, hqval]
    have hshortA : ShortArc (A p) (A q) := by have := heA p; rwa [hpq_succ] at this
    have hshortB : ShortArc (B p) (B q) := by have := heB p; rwa [hpq_succ] at this
    have hcrA : cross (A p : E3) (A q : E3) ≠ 0 := cross_ne_zero_of_shortArc hshortA
    have hcrB : cross (B p : E3) (B q : E3) ≠ 0 := cross_ne_zero_of_shortArc hshortB
    -- index ordering facts
    have hip : i.val ≤ r + 1 := by omega
    -- ===== frame Gram block matches =====
    have gpp : (⟪(A p : E3), (A p : E3)⟫ : ℝ) = ⟪(B p : E3), (B p : E3)⟫ := by
      rw [inner_eq_sInner, inner_eq_sInner, sInner_self, sInner_self]
    have gqq : (⟪(A q : E3), (A q : E3)⟫ : ℝ) = ⟪(B q : E3), (B q : E3)⟫ := by
      rw [inner_eq_sInner, inner_eq_sInner, sInner_self, sInner_self]
    have gpq : (⟪(A p : E3), (A q : E3)⟫ : ℝ) = ⟪(B p : E3), (B q : E3)⟫ := by
      have he := inner_consecutive_eq hs ⟨r, hr_lt⟩
      have hcs : (⟨r, hr_lt⟩ : Fin n).castSucc = p := by
        apply Fin.ext; simp [Fin.castSucc, Fin.castAdd, Fin.castLE, hp]
      have hsc : (⟨r, hr_lt⟩ : Fin n).succ = q := by
        apply Fin.ext; simp [Fin.succ, hq]
      rw [hcs, hsc] at he; exact he
    -- cross self inner products match via Lagrange (1·1 − ⟪p,q⟫²).
    have gmm : (⟪cross (A p : E3) (A q : E3), cross (A p : E3) (A q : E3)⟫ : ℝ)
        = ⟪cross (B p : E3) (B q : E3), cross (B p : E3) (B q : E3)⟫ := by
      rw [inner_cross_self_eq, inner_cross_self_eq]
      have hcA' : (⟪(A q : E3), (A p : E3)⟫ : ℝ) = ⟪(A p : E3), (A q : E3)⟫ :=
        real_inner_comm (A p : E3) (A q : E3)
      have hcB' : (⟪(B q : E3), (B p : E3)⟫ : ℝ) = ⟪(B p : E3), (B q : E3)⟫ :=
        real_inner_comm (B p : E3) (B q : E3)
      rw [hcA', hcB', gpp, gqq, gpq]
    -- ===== v = A j coordinates against the frame match =====
    -- ⟪p, v⟫ : the consecutive-triple diagonal at joint r.
    have hjoint_idx : r < n - 1 := by have := j.isLt; omega
    have vp : (⟪(A p : E3), (A j : E3)⟫ : ℝ) = ⟪(B p : E3), (B j : E3)⟫ := by
      have hd := inner_diag_eq hs hj ⟨r, hjoint_idx⟩
      -- identify the diag vertices with p and j.
      have e0 : (⟨(⟨r, hjoint_idx⟩ : Fin (n-1)).val,
          by have := (⟨r, hjoint_idx⟩ : Fin (n-1)).isLt; omega⟩ : Fin (n+1)) = p := by
        apply Fin.ext; simp [hp]
      have e2 : (⟨(⟨r, hjoint_idx⟩ : Fin (n-1)).val + 2,
          by have := (⟨r, hjoint_idx⟩ : Fin (n-1)).isLt; omega⟩ : Fin (n+1)) = j := by
        apply Fin.ext; simp [hjeq]
      rw [e0, e2] at hd; exact hd
    -- ⟪q, v⟫ : the side at e = ⟨r+1, _⟩.
    have vq : (⟪(A q : E3), (A j : E3)⟫ : ℝ) = ⟪(B q : E3), (B j : E3)⟫ := by
      have hin : r + 1 < n := by have := j.isLt; omega
      have he := inner_consecutive_eq hs ⟨r + 1, hin⟩
      have hcs : (⟨r + 1, hin⟩ : Fin n).castSucc = q := by
        apply Fin.ext; simp [Fin.castSucc, Fin.castAdd, Fin.castLE, hq]
      have hsc : (⟨r + 1, hin⟩ : Fin n).succ = j := by
        apply Fin.ext; simp [Fin.succ, hjeq]
      rw [hcs, hsc] at he; exact he
    -- ⟪cross p q, v⟫ = det3 (A p)(A q)(A j) = sOrient, positive for both, square matches.
    have vm : (⟪cross (A p : E3) (A q : E3), (A j : E3)⟫ : ℝ)
        = ⟪cross (B p : E3) (B q : E3), (B j : E3)⟫ := by
      rw [inner_cross_left_eq_det3, inner_cross_left_eq_det3]
      -- positivity from CyclicTriplePos at p < q < j.
      have hpltq : p < q := by rw [Fin.lt_def, hpval, hqval]; omega
      have hqltj : q < j := by rw [Fin.lt_def, hqval, hjval]; omega
      have hposA : 0 < det3 (A p : E3) (A q : E3) (A j : E3) := hcA p q j hpltq hqltj
      have hposB : 0 < det3 (B p : E3) (B q : E3) (B j : E3) := hcB p q j hpltq hqltj
      -- gram entries of triple (p,q,j): use gpp,gpq,vp (=⟪p,j⟫), gqq, vq (=⟪q,j⟫), self.
      have gjj : (⟪(A j : E3), (A j : E3)⟫ : ℝ) = ⟪(B j : E3), (B j : E3)⟫ := by
        rw [inner_eq_sInner, inner_eq_sInner, sInner_self, sInner_self]
      exact det3_congr_of_pos gpp gpq vp
        (by rw [real_inner_comm (A p : E3) (A q : E3), real_inner_comm (B p : E3) (B q : E3)]; exact gpq)
        gqq vq
        (by rw [real_inner_comm (A p : E3) (A j : E3), real_inner_comm (B p : E3) (B j : E3)]; exact vp)
        (by rw [real_inner_comm (A q : E3) (A j : E3), real_inner_comm (B q : E3) (B j : E3)]; exact vq)
        gjj hposA hposB
    -- ===== u = A i coordinates against the frame match (from IH) =====
    -- max(i, p) ≤ r+1 < j.val ≤ N, so IH applies (strictly smaller bound).
    have up : (⟪(A i : E3), (A p : E3)⟫ : ℝ) = ⟪(B i : E3), (B p : E3)⟫ := by
      rcases le_total i.val p.val with hle | hle
      · exact IH (r + 1) (by omega) i p hle (by omega)
      · rw [real_inner_comm (A p : E3) (A i : E3), real_inner_comm (B p : E3) (B i : E3)]
        exact IH (r + 1) (by omega) p i hle (by omega)
    have uq : (⟪(A i : E3), (A q : E3)⟫ : ℝ) = ⟪(B i : E3), (B q : E3)⟫ := by
      rcases le_total i.val q.val with hle | hle
      · exact IH (r + 1) (by omega) i q hle (by omega)
      · rw [real_inner_comm (A q : E3) (A i : E3), real_inner_comm (B q : E3) (B i : E3)]
        exact IH (r + 1) (by omega) q i hle (by omega)
    -- ⟪u, cross p q⟫ = det3 (A i)(A p)(A q).  Sign: i<p<q → positive (CyclicTriplePos); else 0.
    have um : (⟪(A i : E3), cross (A p : E3) (A q : E3)⟫ : ℝ)
        = ⟪(B i : E3), cross (B p : E3) (B q : E3)⟫ := by
      rw [inner_cross_right_eq_det3, inner_cross_right_eq_det3]
      -- det3 (A p)(A q)(A i) = sOrient (A p)(A q)(A i) ; we have i ≤ r+1 = q.val.
      rcases lt_or_eq_of_le hip with hilt | hieq
      · -- i.val < r+1 ⟹ i.val ≤ r ; further split i.val < r vs = r.
        rcases lt_or_eq_of_le (show i.val ≤ r by omega) with hir | hir
        · -- i < p < q : positive triple (cyclic order p,q,i  ↔  i,p,q via det3_cyclic).
          have hipp : i < p := by rw [Fin.lt_def, hpval]; omega
          have hpltq : p < q := by rw [Fin.lt_def, hpval, hqval]; omega
          have hposA : 0 < det3 (A i : E3) (A p : E3) (A q : E3) := hcA i p q hipp hpltq
          have hposB : 0 < det3 (B i : E3) (B p : E3) (B q : E3) := hcB i p q hipp hpltq
          -- det3 (A p)(A q)(A i) = det3 (A i)(A p)(A q) by cyclic.
          rw [det3_cyclic (A p : E3) (A q : E3) (A i : E3),
            det3_cyclic (B p : E3) (B q : E3) (B i : E3)]
          -- gram of (i,p,q): ⟪i,i⟫,⟪i,p⟫(=up),⟪i,q⟫(=uq),⟪p,p⟫,⟪p,q⟫,⟪q,q⟫ all match.
          have gii : (⟪(A i : E3), (A i : E3)⟫ : ℝ) = ⟪(B i : E3), (B i : E3)⟫ := by
            rw [inner_eq_sInner, inner_eq_sInner, sInner_self, sInner_self]
          exact det3_congr_of_pos gii up uq
            (by rw [real_inner_comm (A i : E3) (A p : E3), real_inner_comm (B i : E3) (B p : E3)]; exact up)
            gpp gpq
            (by rw [real_inner_comm (A i : E3) (A q : E3), real_inner_comm (B i : E3) (B q : E3)]; exact uq)
            (by rw [real_inner_comm (A p : E3) (A q : E3), real_inner_comm (B p : E3) (B q : E3)]; exact gpq)
            gqq hposA hposB
        · -- i.val = r = p.val ⟹ A i = A p, det3 (A p)(A q)(A p) = 0.
          have hieqp : i = p := Fin.ext (by rw [hpval]; exact hir)
          rw [hieqp]
          rw [show det3 (A p : E3) (A q : E3) (A p : E3) = 0 by rw [det3]; ring,
            show det3 (B p : E3) (B q : E3) (B p : E3) = 0 by rw [det3]; ring]
      · -- i.val = r+1 = q.val ⟹ A i = A q, det3 (A p)(A q)(A q) = 0.
        have hieqq : i = q := Fin.ext (by rw [hqval]; exact hieq)
        rw [hieqq]
        rw [show det3 (A p : E3) (A q : E3) (A q : E3) = 0 by rw [det3]; ring,
          show det3 (B p : E3) (B q : E3) (B q : E3) = 0 by rw [det3]; ring]
    -- ===== assemble via gram_transfer =====
    exact gram_transfer hcrA hcrB gpp gpq gqq gmm up uq um vp vq vm

/-- **Full Gram congruence.**  Symmetric closure of `gram_eq_ordered`: every pairwise vertex inner
product agrees between the two arms. -/
theorem gram_eq {n : ℕ} {A B : Fin (n + 1) → S2}
    (hcA : CyclicTriplePos A) (hcB : CyclicTriplePos B)
    (heA : ∀ i : Fin (n + 1), ShortArc (A i) (A (i + 1)))
    (heB : ∀ i : Fin (n + 1), ShortArc (B i) (B (i + 1)))
    (hs : ∀ e : Fin n, sideLen A e = sideLen B e)
    (hj : ∀ r : Fin (n - 1), jointAngle A r = jointAngle B r) (i j : Fin (n + 1)) :
    (⟪(A i : E3), (A j : E3)⟫ : ℝ) = ⟪(B i : E3), (B j : E3)⟫ := by
  rcases le_total i.val j.val with hle | hle
  · exact gram_eq_ordered hcA hcB heA heB hs hj (max i.val j.val) i j hle (le_max_right _ _)
  · rw [real_inner_comm (A j : E3) (A i : E3), real_inner_comm (B j : E3) (B i : E3)]
    exact gram_eq_ordered hcA hcB heA heB hs hj (max i.val j.val) j i hle (le_max_left _ _)

/-! ## §7. The endpoint congruence (R-cong).

Since endpoint distance is `arccos` of the endpoint inner product, full Gram congruence gives equal
endpoint distance.  The convex cyclic-triple orientation `CyclicTriplePos` of both arms is carried as
a named, non-vacuous hypothesis (`cyclicTriplePos_triangle` realises it for triangles; it is exactly
the substrate's HINGE Lemma 2.3 residue). -/

/-- **R-cong: spherical SSS/angle endpoint congruence (Gram-congruence form).**  Two spherical arms
with equal side lengths and equal interior joint angles, both satisfying the convex cyclic-triple
orientation property, have equal endpoint distance. -/
theorem congruent_endpoint_eq {n : ℕ} {A B : Fin (n + 1) → S2}
    (hcA : CyclicTriplePos A) (hcB : CyclicTriplePos B)
    (heA : ∀ i : Fin (n + 1), ShortArc (A i) (A (i + 1)))
    (heB : ∀ i : Fin (n + 1), ShortArc (B i) (B (i + 1)))
    (hs : ∀ e : Fin n, sideLen A e = sideLen B e)
    (hj : ∀ r : Fin (n - 1), jointAngle A r = jointAngle B r) :
    sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)) := by
  rw [sDist, sDist, sInner, sInner]
  rw [gram_eq hcA hcB heA heB hs hj 0 (Fin.last n)]

/-- **R-cong from `StrictConvexSphArm`, conditional on the cyclic-triple residue.**  The `ShortArc`
edge hypotheses are discharged from `StrictConvexSphArm` (its `edge_short` field); the convex
cyclic-triple orientation `CyclicTriplePos` of both arms remains as the named hypothesis (it is the
substrate's HINGE Lemma 2.3, not banked from `StrictConvexSphArm` alone). -/
theorem congruent_endpoint_eq_arm {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hcA : CyclicTriplePos A) (hcB : CyclicTriplePos B)
    (hs : ∀ e : Fin n, sideLen A e = sideLen B e)
    (hj : ∀ r : Fin (n - 1), jointAngle A r = jointAngle B r) :
    sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)) :=
  congruent_endpoint_eq hcA hcB hA.closed_convex.edge_short hB.closed_convex.edge_short hs hj

/-- **Endpoint congruence in `endpt` form**, ready to discharge the `(P2)` equal-joints branch of the
Schoenberg–Zaremba step (`SphericalSZFinal` §R-cong). -/
theorem endpt_eq_of_congruent {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hcA : CyclicTriplePos A) (hcB : CyclicTriplePos B)
    (hs : ∀ e : Fin n, sideLen A e = sideLen B e)
    (hj : ∀ r : Fin (n - 1), jointAngle A r = jointAngle B r) :
    ProofsInTheBook.SphericalArm.endpt A = ProofsInTheBook.SphericalArm.endpt B := by
  unfold ProofsInTheBook.SphericalArm.endpt
  exact congruent_endpoint_eq_arm hA hB hcA hcB hs hj

/-- **Non-vacuity witness.**  `CyclicTriplePos` is genuinely satisfiable — every strictly convex
spherical triangle satisfies it (`cyclicTriplePos_triangle`).  Hence `congruent_endpoint_eq_arm` is
not a vacuous conditional theorem: its cyclic-triple hypotheses are inhabited. -/
theorem cyclicTriplePos_nonvacuous (P : Fin 3 → S2) (h : StrictConvexSphPolygon P) :
    CyclicTriplePos P :=
  cyclicTriplePos_triangle P h

end ProofsInTheBook.SphericalCongruence
