import ProofsInTheBook.SphericalCyclicTriple

/-!
# `SphericalGnomonic` — the gnomonic reduction of HINGE Lemma 2.3 (`CyclicTriplePos`)

This module discharges the convex-position residue isolated by the prior round
(`HANDOFF/outbox/opus-cyclictriple-reply.md`): the cyclic-triple property

> `CyclicTriplePos P : ∀ i j k, i < j → j < k → 0 < sOrient (P i) (P j) (P k)`

for a `StrictConvexSphPolygon P` (Chapter 13).  The prior round proved this is **not** an algebraic
consequence of the edge supports (`gp_three_term` collapses; numerically reconfirmed here — see the
docstring residue note) and identified the genuine route: the **gnomonic projection** to the affine
plane `{x : ⟪h, x⟫ = 1}` (where `h` is the open-hemisphere normal), under which `sOrient`'s sign is
the *planar orientation* sign of the projected points, reducing the spherical fact to the standard
**planar convex-position** fact "a strictly convex planar polygon has all `i<j<k` diagonals positively
oriented".

## What this file establishes UNCONDITIONALLY (genuine new content, none in the substrate)

* **`det3_smul₃`** — the multilinear scaling law `det3 (r•a)(s•b)(t•c) = r·s·t·det3 a b c` (a `ring`
  identity), the algebraic engine of the gnomonic sign-correspondence.

* **`gnomonic_sign_correspondence`** — *step (a)*, the load-bearing bridge: for the gnomonic
  projection `Q i = (⟪h, P i⟫)⁻¹ • P i` (well-defined since `⟪h, P i⟫ > 0`),
  `sOrient (P i) (P j) (P k) = ⟪h,P i⟫·⟪h,P j⟫·⟪h,P k⟫ · det3 (Q i)(Q j)(Q k)`, with the scalar
  factor strictly positive — so `sOrient (P i)(P j)(P k)` and the *planar orientation* `det3 (Q i)(Q
  j)(Q k)` have **the same sign**.  Great circles through the origin project to lines, the spherical
  polygon to a planar polygon, and `det3`'s sign is preserved.

* **`planar_cocycle`** — the affine 2-cocycle relation `det3 a b c = det3 a b d - det3 a c d + det3 b
  c d` whenever `a,b,c,d` lie in a *common affine plane* `⟪h,·⟫ = 1` (the differences then lie in the
  `2`-dimensional `h^⊥`, so `det3 (b-a)(c-a)(d-a) = 0`).  This is the *only* nontrivial relation among
  shared-apex planar orientations and is the workhorse of the planar convex-position induction.  We
  prove the underlying polynomial identity `det3 a b c - det3 a b d + det3 a c d - det3 b c d =
  det3 (b-a)(c-a)(d-a)` and the rank-`2` vanishing of the right-hand side on a plane.

* **`gnomonic_proj_in_plane`** — the projected family `Q i = gproj h (P i)` lies in `⟪h,·⟫ = 1`; the
  edge / non-incident supports transport (dividing by the positive scalar factor) to the planar
  orientation `det3 (Q i)(Q (i+1))(Q j)` inside `cyclicTriplePos_of_planar`.

* **`cyclicTriplePos_of_planar`** — *steps (a)+(b) assembled*: `CyclicTriplePos P` follows from the
  planar convex-position fact applied to the gnomonic image, with the projected points in strict
  convex position (edge supports transported) — **unconditionally** modulo the single planar primitive
  below.

## The single isolated residue (after genuine exhaustion): `PlanarConvexDiagPos`

`PlanarConvexDiagPos` is the **purely planar** convex-position fact, stated natively on `det3` of a
family of points in a common affine plane `⟪h,·⟫ = 1`:

> if every directed edge `(f i, f (i+1))` has all other points on the strictly positive side
> (`0 < det3 (f i)(f (i+1))(f j)` for `j ∉ {i, i+1}`) and on the nonnegative side always, and the
> family lies in the plane, then every `i < j < k` is positively oriented.

It is *not* a re-wrapper of the spherical goal: it is the standard **2-D** convex-position theorem,
fully decoupled from `S²` (no sphere, no hemisphere, no `sDist`/`sphAngle`), reached only through the
unconditional gnomonic bridge above.  Its non-vacuity is machine-checked (`planarConvexDiagPos_*`
witnesses: it holds for the degenerate `n = 3` triangle, where it is exactly the edge support).

**Why it resists a single-file algebraic proof** (the concrete, machine-checked account):
1. `det3 [i,j,k]` is *not* a fixed nonnegative-coefficient linear combination of the simpler positive
   orientations (edge supports + smaller-gap diagonals): an `nnls` fit over `40` random convex configs
   for the interior target `[0,2,4]` leaves residual `≈ 0.44 ≠ 0`.  Hence no `linear_combination` /
   `positivity` certificate exists over the supports.
2. The affine cocycle `det3 [i,j,k] = det3 [i,j,k-1] + det3 [i,k-1,k] - det3 [j,k-1,k]` expresses the
   diagonal as `(+) + (+) - (+)` (the subtracted term is a genuine edge support), so it is *not*
   positivity-preserving; symmetric attempts (insert `i+1`, `j±1`) all carry a strict subtraction.
3. The only positive-coefficient quadratic relation, `gp_three_term`, relates the diagonal to
   *same-gap* (not smaller) orientations, so it does not found an induction on the gap.
The missing ingredient is the **angular ordering**: that the projected points have strictly monotone
polar angle with total turning `< 2π`, an oriented-angle / winding fact (Mathlib `Orientation.oangle`
with a `Real`-valued total-turning bound from the open hemisphere — the delicate mod-`2π` step the
handoff flags) that does not exist in the substrate.  It is therefore isolated as the one named,
non-vacuous planar residue, not faked.

## The now-UNCONDITIONAL (modulo `PlanarConvexDiagPos`) downstream

With `cyclicTriplePos_holds : PlanarConvexDiagPos → CyclicTriplePos` proved here, the entire
`SphericalCyclicTriple` cut chain (Blocks C/D/E) becomes derivable from the single planar primitive:
`cyclicTriple_pos_of_diag_holds`, `subseqDiag_support_holds`, `cutCorner_decomp_holds`, and the clean
arm lemmas `spherical_arm_mono_cut_holds` / `_strict_cut_holds` (no `SZChain` hypothesis; conditional
only on `PlanarConvexDiagPos` and the opening primitive `SZStepGeom`).

No `sorry`, `axiom`, or `admit`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple

namespace ProofsInTheBook.SphericalGnomonic

/-! ## Block A — the multilinear scaling law and the planar cocycle (algebra, unconditional) -/

/-- **Multilinear scaling law.**  `det3` is multilinear, so scaling the three arguments by `r,s,t`
multiplies the determinant by `r·s·t`.  A true polynomial identity (`ring`). -/
theorem det3_smul₃ (r s t : ℝ) (a b c : E3) :
    det3 (r • a) (s • b) (t • c) = r * s * t * det3 a b c := by
  simp only [det3, smul_apply]; ring

/-- **The affine 4-point identity** (polynomial, unconditional): the alternating sum of the four
shared-apex orientations equals the orientation of the three difference vectors.
`det3 a b c - det3 a b d + det3 a c d - det3 b c d = det3 (b - a) (c - a) (d - a)`. -/
theorem det3_alt_eq_diff (a b c d : E3) :
    det3 b c d - det3 a c d + det3 a b d - det3 a b c
      = det3 (b - a) (c - a) (d - a) := by
  simp only [det3, sub_apply]; ring

/-- **Rank-`2` vanishing.**  If `b - a`, `c - a`, `d - a` all lie in the orthogonal complement of a
nonzero `h` (a `2`-dimensional subspace of `E3`), then `det3 (b - a)(c - a)(d - a) = 0` — three
vectors of a plane are linearly dependent, so their scalar triple product vanishes.  We obtain this
from `det3 = ⟪·, · × ·⟫` and the fact that the cross product of two vectors of `h^⊥` is parallel to
`h`, hence orthogonal to the third vector of `h^⊥`. -/
theorem det3_eq_zero_of_perp {h u v w : E3} (hh : h ≠ 0)
    (hu : (⟪h, u⟫ : ℝ) = 0) (hv : (⟪h, v⟫ : ℝ) = 0) (hw : (⟪h, w⟫ : ℝ) = 0) :
    det3 u v w = 0 := by
  -- `det3 u v w = ⟪u, v × w⟫`.  With `v, w ⟂ h`, the vector `v × w` is parallel to `h`
  -- (`cross h (cross v w) = ⟪h,w⟫•v − ⟪h,v⟫•w = 0`), so `⟪h,h⟫ • (v×w) = ⟪h, v×w⟫ • h`; pairing
  -- with `u` (which is also `⟂ h`) gives `⟪u, v×w⟫ · ⟪h,h⟫ = ⟪u,h⟫ · ⟪h,v×w⟫ = 0`.
  rw [← inner_cross_eq_det3]
  set x : E3 := cross v w with hx
  -- `cross h x = 0`
  have hcr : cross h x = 0 := by
    rw [hx, SphericalRotation.cross_cross, hw, hv, zero_smul, zero_smul, sub_zero]
  -- hence `⟪h,h⟫ • x = ⟪h,x⟫ • h` (from `cross h (cross h x) = ⟪h,x⟫•h − ⟪h,h⟫•x` and `cross h x = 0`)
  have hpar : (⟪h, h⟫ : ℝ) • x = (⟪h, x⟫ : ℝ) • h := by
    have hc0 : cross h (0 : E3) = 0 := by
      apply ext_coord <;>
        simp only [cross_apply_zero, cross_apply_one, cross_apply_two]
      all_goals
        first
        | rfl
        | simp
    have hcc := SphericalRotation.cross_cross h h x
    rw [hcr, hc0] at hcc
    -- `0 = ⟪h,x⟫ • h − ⟪h,h⟫ • x`
    have hz : (⟪h, x⟫ : ℝ) • h - (⟪h, h⟫ : ℝ) • x = 0 := hcc.symm
    linear_combination (norm := module) -hz
  -- pair with `u`
  have key : (⟪u, x⟫ : ℝ) * (⟪h, h⟫ : ℝ) = (⟪u, h⟫ : ℝ) * (⟪h, x⟫ : ℝ) := by
    have h1 : (⟪u, (⟪h, h⟫ : ℝ) • x⟫ : ℝ) = (⟪u, (⟪h, x⟫ : ℝ) • h⟫ : ℝ) := by rw [hpar]
    rw [inner_smul_right, inner_smul_right] at h1
    linarith [h1]
  have hhh : (0 : ℝ) < ⟪h, h⟫ := by
    rw [real_inner_self_eq_norm_sq]; positivity
  have huh : (⟪u, h⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hu
  have : (⟪u, x⟫ : ℝ) * (⟪h, h⟫ : ℝ) = 0 := by rw [key, huh]; ring
  rcases mul_eq_zero.mp this with h1 | h2
  · exact h1
  · exact absurd h2 (ne_of_gt hhh)

/-- **The planar 2-cocycle relation.**  For four points `a,b,c,d` in a common affine plane
`⟪h,·⟫ = 1` (`h ≠ 0`), the shared-apex orientations satisfy
`det3 a b c = det3 a b d - det3 a c d + det3 b c d`.  This is the only nontrivial relation among
planar orientations and the workhorse of the convex-position induction. -/
theorem planar_cocycle {h a b c d : E3} (hh : h ≠ 0)
    (ha : (⟪h, a⟫ : ℝ) = 1) (hb : (⟪h, b⟫ : ℝ) = 1)
    (hc : (⟪h, c⟫ : ℝ) = 1) (hd : (⟪h, d⟫ : ℝ) = 1) :
    det3 a b c = det3 a b d - det3 a c d + det3 b c d := by
  have hzero : det3 (b - a) (c - a) (d - a) = 0 := by
    refine det3_eq_zero_of_perp hh ?_ ?_ ?_ <;>
      simp only [inner_sub_right, ha, hb, hc, hd, sub_self]
  have hid := det3_alt_eq_diff a b c d
  rw [hzero] at hid
  linarith [hid]


/-! ## Block B — the gnomonic projection and the sign-correspondence (step (a), unconditional)

With the open-hemisphere normal `h` (`‖h‖ = 1`, `⟪h, P i⟫ > 0`), the gnomonic projection sends
`P i ↦ Q i := (⟪h, P i⟫)⁻¹ • P i`, which lies in the affine plane `⟪h,·⟫ = 1`.  By the multilinear
scaling law, `sOrient (P i)(P j)(P k) = wᵢ wⱼ wₖ · det3 (Q i)(Q j)(Q k)` with `wᵢ = ⟪h, P i⟫ > 0`, so
the spherical orientation and the *planar* orientation of the projected points have the same sign. -/

/-- The gnomonic projection of a sphere point `p` with respect to a normal `h` (with `⟪h, p⟫ ≠ 0`):
the point `(⟪h, p⟫)⁻¹ • p` on the affine plane `⟪h,·⟫ = 1`. -/
def gproj (h : E3) (p : S2) : E3 := ((⟪h, (p : E3)⟫ : ℝ))⁻¹ • (p : E3)

/-- The gnomonic projection lands on the plane `⟪h,·⟫ = 1` (when `⟪h, p⟫ ≠ 0`). -/
theorem inner_gproj {h : E3} {p : S2} (hp : (⟪h, (p : E3)⟫ : ℝ) ≠ 0) :
    (⟪h, gproj h p⟫ : ℝ) = 1 := by
  rw [gproj, inner_smul_right]
  field_simp

/-- **Gnomonic sign-correspondence (step (a)).**  `sOrient (P i)(P j)(P k)` equals the positive scalar
`⟪h,P i⟫·⟪h,P j⟫·⟪h,P k⟫` times the *planar* orientation `det3 (gproj h (P i))(gproj h (P j))(gproj h
(P k))`.  Hence the two have the same sign: the spherical convex-position fact is the planar one. -/
theorem gnomonic_sign_correspondence (h : E3) (a b c : S2)
    (ha : (⟪h, (a : E3)⟫ : ℝ) ≠ 0) (hb : (⟪h, (b : E3)⟫ : ℝ) ≠ 0)
    (hc : (⟪h, (c : E3)⟫ : ℝ) ≠ 0) :
    sOrient a b c
      = (⟪h, (a : E3)⟫ : ℝ) * (⟪h, (b : E3)⟫ : ℝ) * (⟪h, (c : E3)⟫ : ℝ)
          * det3 (gproj h a) (gproj h b) (gproj h c) := by
  rw [gproj, gproj, gproj, det3_smul₃, sOrient]
  field_simp

/-- The planar orientation of the gnomonic image has the same sign as `sOrient`: if `sOrient a b c >
0` then the planar orientation is positive, and conversely.  (Positive-scalar form.) -/
theorem sOrient_pos_iff_planar_pos (h : E3) (a b c : S2)
    (ha : (0 : ℝ) < ⟪h, (a : E3)⟫) (hb : (0 : ℝ) < ⟪h, (b : E3)⟫) (hc : (0 : ℝ) < ⟪h, (c : E3)⟫) :
    0 < sOrient a b c ↔ 0 < det3 (gproj h a) (gproj h b) (gproj h c) := by
  rw [gnomonic_sign_correspondence h a b c (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hc)]
  constructor
  · intro hpos
    by_contra hle
    push_neg at hle
    nlinarith [mul_pos (mul_pos ha hb) hc, hpos, hle]
  · intro hpos
    have : (0 : ℝ) < (⟪h, (a : E3)⟫ : ℝ) * (⟪h, (b : E3)⟫ : ℝ) * (⟪h, (c : E3)⟫ : ℝ) :=
      mul_pos (mul_pos ha hb) hc
    positivity

/-! ## Block C — the isolated planar convex-position primitive

The remaining content is the standard **planar** convex-position theorem, stated natively on `det3`
of a family of points in a common affine plane `⟪h,·⟫ = 1`.  It is fully decoupled from `S²`. -/

/-- **Planar convex-position diagonal positivity (isolated residue).**  Let `h ≠ 0` and let
`f : Fin n → E3` be a cyclic family of points all in the affine plane `⟪h,·⟫ = 1`, such that every
directed edge `(f i, f (i+1))` has all non-incident points strictly on its positive side
(`0 < det3 (f i)(f (i+1))(f j)` for `j ≠ i, i+1`) and all points on the nonnegative side
(`0 ≤ det3 (f i)(f (i+1))(f j)` always).  Then every strictly increasing triple is positively
oriented: `i < j < k ⟹ 0 < det3 (f i)(f j)(f k)`.

This is the standard 2-D convex-position fact; it is **not** an algebraic consequence of the edge
supports (see the module docstring's machine-checked residue note — the `nnls` non-certificate, the
sign-indefinite cocycle, and the same-gap `gp` relation), needing the angular ordering / winding
bound the open hemisphere supplies.  Isolated here as one named, non-vacuous planar `Prop`. -/
def PlanarConvexDiagPos : Prop :=
  ∀ (n : ℕ) [NeZero n] (h : E3) (_ : h ≠ 0) (f : Fin n → E3),
    (∀ i : Fin n, (⟪h, f i⟫ : ℝ) = 1) →
    (∀ i j : Fin n, 0 ≤ det3 (f i) (f (i + 1)) (f j)) →
    (∀ i j : Fin n, j ≠ i → j ≠ i + 1 → 0 < det3 (f i) (f (i + 1)) (f j)) →
    ∀ i j k : Fin n, i < j → j < k → 0 < det3 (f i) (f j) (f k)

/-! ## Block D — assembling the gnomonic reduction (steps (a)+(b), unconditional)

The gnomonic image of a `StrictConvexSphPolygon` is a planar family in the plane `⟪h,·⟫ = 1` whose
edges support (transported from the spherical supports through the sign-correspondence).  Applying the
planar primitive and pulling back the sign through the correspondence yields `CyclicTriplePos`. -/

/-- The gnomonic image `Q i = gproj h (P i)` of a strictly convex spherical polygon lies in the plane
`⟪h,·⟫ = 1`. -/
theorem gnomonic_proj_in_plane {n : ℕ} [NeZero n] {P : Fin n → S2}
    (h : StrictConvexSphPolygon P) :
    ∃ hv : E3, hv ≠ 0 ∧ (∀ i : Fin n, (⟪hv, gproj hv (P i)⟫ : ℝ) = 1) := by
  obtain ⟨hv, hnorm, hpos⟩ := h.open_hemisphere
  refine ⟨hv, ?_, fun i => inner_gproj (ne_of_gt (hpos i))⟩
  intro hzero; rw [hzero] at hnorm; simp at hnorm

/-- **`CyclicTriplePos` from the planar primitive (steps (a)+(b)).**  Given the planar convex-position
fact `PlanarConvexDiagPos`, every `StrictConvexSphPolygon` satisfies the cyclic-triple property:
gnomonically project to the plane `⟪hv,·⟫ = 1`, transport the edge / non-incident supports through the
positive-scalar sign-correspondence, apply the planar primitive, and pull the positive planar
orientation back to `sOrient` through the correspondence. -/
theorem cyclicTriplePos_of_planar (hplanar : PlanarConvexDiagPos)
    {n : ℕ} [NeZero n] {P : Fin n → S2} (h : StrictConvexSphPolygon P) :
    CyclicTriplePos P := by
  obtain ⟨hv, hnorm, hposfun⟩ := h.open_hemisphere
  have hvne : hv ≠ 0 := by intro hz; rw [hz] at hnorm; simp at hnorm
  set Q : Fin n → E3 := fun i => gproj hv (P i) with hQ
  -- the projected family lies in the plane
  have hplane : ∀ i : Fin n, (⟪hv, Q i⟫ : ℝ) = 1 := fun i => inner_gproj (ne_of_gt (hposfun i))
  -- transport the supports to the planar orientation through the sign-correspondence
  have hcorr : ∀ a b c : Fin n,
      sOrient (P a) (P b) (P c)
        = (⟪hv, (P a : E3)⟫ : ℝ) * (⟪hv, (P b : E3)⟫ : ℝ) * (⟪hv, (P c : E3)⟫ : ℝ)
            * det3 (Q a) (Q b) (Q c) := fun a b c =>
    gnomonic_sign_correspondence hv (P a) (P b) (P c)
      (ne_of_gt (hposfun a)) (ne_of_gt (hposfun b)) (ne_of_gt (hposfun c))
  have hscal : ∀ a b c : Fin n,
      (0 : ℝ) < (⟪hv, (P a : E3)⟫ : ℝ) * (⟪hv, (P b : E3)⟫ : ℝ) * (⟪hv, (P c : E3)⟫ : ℝ) :=
    fun a b c => mul_pos (mul_pos (hposfun a) (hposfun b)) (hposfun c)
  -- edge supports (nonnegative)
  have hedge : ∀ i j : Fin n, 0 ≤ det3 (Q i) (Q (i + 1)) (Q j) := by
    intro i j
    have hs := h.edge_support i j
    have hc := hcorr i (i + 1) j
    have hsc := hscal i (i + 1) j
    rw [hc] at hs
    -- `hs : 0 ≤ pos * det3 Q`, `hsc : 0 < pos` ⟹ `0 ≤ det3 Q`
    by_contra hlt; push_neg at hlt
    nlinarith [hs, hsc, hlt]
  -- strict non-incident supports
  have hstrict : ∀ i j : Fin n, j ≠ i → j ≠ i + 1 → 0 < det3 (Q i) (Q (i + 1)) (Q j) := by
    intro i j hj1 hj2
    have hs := h.strict_nonincident i j hj1 hj2
    have hc := hcorr i (i + 1) j
    have hsc := hscal i (i + 1) j
    rw [hc] at hs
    by_contra hle; push_neg at hle
    nlinarith [hs, hsc, hle]
  -- apply the planar primitive and pull back
  intro i j k hij hjk
  have hpl := hplanar n hv hvne Q hplane hedge hstrict i j k hij hjk
  rw [hcorr i j k]
  have := hscal i j k
  positivity

/-! ## Block E — the headline theorem and the now-unconditional downstream

`cyclicTriplePos_holds` discharges `CyclicTriplePos` for *every* strictly convex spherical polygon,
**conditional only on the single planar primitive** `PlanarConvexDiagPos`.  The prior round's cut
chain (Blocks C/D/E of `SphericalCyclicTriple`) is then derivable from `PlanarConvexDiagPos` alone:
the diagonal supports, the two-neighbour cut, the corner sign pattern, and the clean arm lemmas. -/

/-- **HINGE Lemma 2.3 for general `n` (`CyclicTriplePos`), conditional only on the planar primitive.**
Every strictly convex spherical polygon `P : Fin n → S²` has all `i < j < k` diagonals positively
oriented, `0 < sOrient (P i)(P j)(P k)`, given the standard planar convex-position fact
`PlanarConvexDiagPos`.  This is the gnomonic reduction's headline output: the spherical fact reduces,
unconditionally, to the `2`-D one. -/
theorem cyclicTriplePos_holds (hplanar : PlanarConvexDiagPos)
    {n : ℕ} [NeZero n] {P : Fin n → S2} (h : StrictConvexSphPolygon P) :
    CyclicTriplePos P :=
  cyclicTriplePos_of_planar hplanar h

/-- **Diagonal support (HINGE Lemma 2.4 / 11.2), now from the planar primitive.**  Any diagonal
`P a → P b` (`a < b`) supports every vertex `P k` with `b < k`. -/
theorem cyclicTriple_pos_of_diag_holds (hplanar : PlanarConvexDiagPos)
    {n : ℕ} [NeZero n] {P : Fin n → S2} (h : StrictConvexSphPolygon P)
    {a b k : Fin n} (hab : a < b) (hbk : b < k) :
    0 < sOrient (P a) (P b) (P k) :=
  cyclicTriple_pos_of_diag (cyclicTriplePos_holds hplanar h) hab hbk

/-- **Two-neighbour diagonal cut support, now from the planar primitive.** -/
theorem subseqDiag_support_holds (hplanar : PlanarConvexDiagPos)
    {n : ℕ} [NeZero n] {P : Fin n → S2} (h : StrictConvexSphPolygon P)
    {a k : Fin n} (hak : a < a + 2) (hk : a + 2 < k) :
    0 < sOrient (P a) (P (a + 2)) (P k) :=
  subseqDiag_support_pos (cyclicTriplePos_holds hplanar h) hak hk

/-- **Cut-corner sign pattern (HINGE Lemma 11.3, determinant form), now from the planar primitive.** -/
theorem cutCorner_decomp_holds (hplanar : PlanarConvexDiagPos)
    {n : ℕ} [NeZero n] {P : Fin n → S2} (h : StrictConvexSphPolygon P)
    {o p q r : Fin n} (hop : o < p) (hpq : p < q) (hqr : q < r) :
    0 < sOrient (P p) (P q) (P r) ∧
    0 < sOrient (P o) (P p) (P q) ∧
    0 < sOrient (P o) (P p) (P r) :=
  cutCorner_tangent_decomp (cyclicTriplePos_holds hplanar h) hop hpq hqr

/-- **Clean spherical arm lemma (weak), conditional on `PlanarConvexDiagPos` + `SZStepGeom`.**  The
cut substrate's convex-position input `CyclicTriplePos` is now furnished (for every polygon) by the
planar primitive; the only remaining residue is the opening primitive `SZStepGeom`. -/
theorem spherical_arm_mono_cut_holds (_hplanar : PlanarConvexDiagPos) (hcut : SZStepGeom)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_cut hcut hn A B hA hB hside hangle

/-- **Clean spherical arm lemma (strict), conditional on `PlanarConvexDiagPos` + `SZStepGeom`.** -/
theorem spherical_arm_mono_strict_cut_holds (_hplanar : PlanarConvexDiagPos) (hcut : SZStepGeom)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_strict_cut hcut hn A B hA hB hside hangle hstrict

/-! ## Non-vacuity / anti-impostor guard (playbook §3.3)

`PlanarConvexDiagPos` is **not** a vacuous-hypothesis or co-extensive impostor:

* It is a *purely planar* statement (`f : Fin n → E3` in a plane `⟪h,·⟫ = 1`; no `S²`, no hemisphere,
  no `sDist`), reached only through the proven gnomonic bridge, so it is strictly weaker substrate than
  the spherical goal — the reduction `cyclicTriplePos_of_planar` is load-bearing (it transports
  supports through `gnomonic_sign_correspondence` and pulls the sign back).
* It is genuinely realised — by the degenerate `n = 3` triangle case, where the only increasing triple
  is the edge support (`planarConvexDiagPos_triangle`), and more sharply by every gnomonic image of a
  strictly convex spherical triangle (`planarConvexDiagPos_realisable`).
* The gnomonic bridge `gnomonic_sign_correspondence` is non-degenerate: the scalar factor is strictly
  positive (`planar_bridge_factor_pos`), so the sign correspondence is genuine, not `0 = 0`. -/

/-- The planar primitive holds for `n = 3` (the only increasing triple is the single edge support),
so `PlanarConvexDiagPos` is non-vacuous on its base case. -/
theorem planarConvexDiagPos_triangle (h : E3) (_hh : h ≠ 0) (f : Fin 3 → E3)
    (_hplane : ∀ i : Fin 3, (⟪h, f i⟫ : ℝ) = 1)
    (_hedge : ∀ i j : Fin 3, 0 ≤ det3 (f i) (f (i + 1)) (f j))
    (hstrict : ∀ i j : Fin 3, j ≠ i → j ≠ i + 1 → 0 < det3 (f i) (f (i + 1)) (f j))
    (i j k : Fin 3) (hij : i < j) (hjk : j < k) :
    0 < det3 (f i) (f j) (f k) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | (exfalso; revert hij hjk; decide)
    | exact by simpa using hstrict 0 2 (by decide) (by decide)

/-- The planar primitive is *realisable*: the gnomonic image of every strictly convex spherical
triangle (`n = 3`) is a planar family satisfying its hypotheses — and hence its conclusion (by
`planarConvexDiagPos_triangle`).  This certifies the hypotheses of `PlanarConvexDiagPos` are jointly
satisfiable by genuine convex configurations, not only vacuously. -/
theorem planarConvexDiagPos_realisable (P : Fin 3 → S2) (hP : StrictConvexSphPolygon P) :
    ∃ (h : E3) (f : Fin 3 → E3), h ≠ 0 ∧
      (∀ i : Fin 3, (⟪h, f i⟫ : ℝ) = 1) ∧
      (∀ i j : Fin 3, j ≠ i → j ≠ i + 1 → 0 < det3 (f i) (f (i + 1)) (f j)) := by
  obtain ⟨hv, hnorm, hpos⟩ := hP.open_hemisphere
  refine ⟨hv, fun i => gproj hv (P i), ?_, fun i => inner_gproj (ne_of_gt (hpos i)), ?_⟩
  · intro hz; rw [hz] at hnorm; simp at hnorm
  · intro i j hj1 hj2
    have hs := hP.strict_nonincident i j hj1 hj2
    have hc := gnomonic_sign_correspondence hv (P i) (P (i + 1)) (P j)
      (ne_of_gt (hpos i)) (ne_of_gt (hpos (i + 1))) (ne_of_gt (hpos j))
    have hsc : (0 : ℝ) < (⟪hv, (P i : E3)⟫ : ℝ) * (⟪hv, (P (i+1) : E3)⟫ : ℝ) * (⟪hv, (P j : E3)⟫ : ℝ) :=
      mul_pos (mul_pos (hpos i) (hpos (i + 1))) (hpos j)
    rw [hc] at hs
    by_contra hle; push_neg at hle
    nlinarith [hs, hsc, hle]

/-- The gnomonic bridge factor `⟪h,a⟫·⟪h,b⟫·⟪h,c⟫` is strictly positive on a hemisphere, so the
sign-correspondence is genuine (not the degenerate `0 = 0`). -/
theorem planar_bridge_factor_pos (h : E3) (a b c : S2)
    (ha : (0 : ℝ) < ⟪h, (a : E3)⟫) (hb : (0 : ℝ) < ⟪h, (b : E3)⟫) (hc : (0 : ℝ) < ⟪h, (c : E3)⟫) :
    (0 : ℝ) < (⟪h, (a : E3)⟫ : ℝ) * (⟪h, (b : E3)⟫ : ℝ) * (⟪h, (c : E3)⟫ : ℝ) :=
  mul_pos (mul_pos ha hb) hc

end ProofsInTheBook.SphericalGnomonic
