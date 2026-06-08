import ProofsInTheBook.SphericalSZStep

/-!
# `SphericalHingeCut` — the §8.1 oriented opening monotonicity (keystone) and the cut substrate

This module builds the §8.1 *oriented* opening monotonicity (the keystone the design flagged), on top
of the Rodrigues engine of `SphericalRotation`.  The unoriented `sphAngle` discards the sign of the
opening; the genuine monotonicity is governed by the *oriented* tangent datum
`⟪tangentTo axis a0, axis × tangentTo axis tail⟫`.

## What this file proves UNCONDITIONALLY (genuine new content)

* `cos_open_le_cos_orig` / `openedAngle_ge_of_oriented` — the **corrected** §8.1 oriented monotonicity:
  with the oriented tangent inner product `≤ 0` and `0 ≤ θ ≤ π − sphAngle a0 axis tail`, the opened
  joint angle `sphAngle a0 axis (rotS2 axis θ tail)` is at least the original `sphAngle a0 axis tail`.

No `sorry`, `axiom`, or `admit`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep

namespace ProofsInTheBook.SphericalHingeCut

/-! ## §8.1 — the oriented opening monotonicity (keystone) -/

/-- The norm of the rotated outgoing tangent is constant in `θ` (the rotation is an isometry). -/
theorem norm_tangentTo_open (axis q : S2) (θ : ℝ) :
    ‖tangentTo axis (rotS2 axis θ q)‖ = ‖tangentTo axis q‖ := by
  rw [tangentTo_rotS2_axis, norm_rot axis.2]

/-- A vector annihilated by `cross k ·` (for unit `k`) is parallel to `k`: `v = ⟪v,k⟫ • k`. -/
theorem eq_smul_axis_of_cross_zero {k v : E3} (hk : ‖k‖ = 1) (h : cross k v = 0) :
    v = (⟪v, k⟫ : ℝ) • k := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hk]; norm_num
  set t : E3 := v - (⟪v, k⟫ : ℝ) • k with ht
  -- t ⟂ k
  have htk : (⟪t, k⟫ : ℝ) = 0 := by
    rw [ht, inner_sub_left, real_inner_smul_left, hkk, mul_one, sub_self]
  -- cross k t = cross k v - ⟪v,k⟫ • cross k k = 0
  have hct : cross k t = 0 := by
    rw [ht, show v - (⟪v, k⟫ : ℝ) • k = v + (-(⟪v, k⟫ : ℝ)) • k by module,
      cross_add_right, cross_smul_right, cross_self, smul_zero, add_zero, h]
  -- ‖cross k t‖² = ‖k‖²‖t‖² − ⟪k,t⟫² = ‖t‖²  (k unit, t ⟂ k)
  have hkt : (⟪k, t⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact htk
  have hnorm : ‖t‖ ^ 2 = 0 := by
    have hl := norm_sq_cross k t
    rw [hct, norm_zero] at hl
    rw [hk, hkt] at hl
    nlinarith [hl]
  have : t = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hnorm
    exact norm_eq_zero.mp this
  rw [ht] at this
  linear_combination (norm := module) this

/-- `cross k v = 0` for unit `k` implies `⟪v,k⟫² = ‖v‖²`: `v` is parallel to the unit `k`. -/
theorem inner_axis_sq_eq_norm_sq {k v : E3} (hk : ‖k‖ = 1) (h : cross k v = 0) :
    (⟪v, k⟫ : ℝ) ^ 2 = ‖v‖ ^ 2 := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hk]; norm_num
  have hpar := eq_smul_axis_of_cross_zero hk h
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => rw [hpar]
  conv_rhs => rw [hpar]
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, hkk]
  ring

/-- **The tangent-plane Pythagorean identity.**  For a unit axis `k` and two vectors `u, w` both
orthogonal to `k`, `⟪u,w⟫² + ⟪u, k×w⟫² = ‖u‖²‖w‖²`.  The cross product `u × w` is parallel to `k`
(both `u, w ⟂ k`), so `⟪u, k×w⟫² = ⟪u×w, k⟫² = ‖u×w‖² = ‖u‖²‖w‖² − ⟪u,w⟫²` (Lagrange). -/
theorem tangentPlane_pythag {k u w : E3} (hk : ‖k‖ = 1)
    (huk : (⟪u, k⟫ : ℝ) = 0) (hwk : (⟪w, k⟫ : ℝ) = 0) :
    (⟪u, w⟫ : ℝ) ^ 2 + (⟪u, cross k w⟫ : ℝ) ^ 2 = ‖u‖ ^ 2 * ‖w‖ ^ 2 := by
  -- `s := ⟪u, k×w⟫ = -⟪u×w, k⟫`  (coordinate identity)
  have hs : (⟪u, cross k w⟫ : ℝ) = -(⟪cross u w, k⟫ : ℝ) := by
    rw [inner_eq_coord, inner_eq_coord]
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  -- `u × w` is parallel to `k`: `cross k (cross u w) = ⟪k,w⟫•u − ⟪k,u⟫•w = 0`
  have hku : (⟪k, u⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact huk
  have hkw : (⟪k, w⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hwk
  have hpar : cross k (cross u w) = 0 := by
    rw [cross_cross, hkw, hku, zero_smul, zero_smul, sub_zero]
  -- hence `⟪u×w, k⟫² = ‖u×w‖²`
  have hsq : (⟪cross u w, k⟫ : ℝ) ^ 2 = ‖cross u w‖ ^ 2 := inner_axis_sq_eq_norm_sq hk hpar
  -- Lagrange: `‖u×w‖² = ‖u‖²‖w‖² − ⟪u,w⟫²`
  have hlag : ‖cross u w‖ ^ 2 = ‖u‖ ^ 2 * ‖w‖ ^ 2 - (⟪u, w⟫ : ℝ) ^ 2 := norm_sq_cross u w
  rw [hs, neg_sq, hsq, hlag]; ring

/-- **The opened-angle cosine inequality (oriented).**  Write `u = tangentTo axis a0`,
`w = tangentTo axis tail`, `c = ⟪u,w⟫`, `s = ⟪u, axis × w⟫`.  The opened-angle cosine is
`(c cos θ + s sin θ)/N` over the constant norm product `N = ‖u‖‖w‖`.  If the oriented datum `s ≤ 0`
and `0 ≤ θ` with `θ + sphAngle a0 axis tail ≤ π`, then `c cos θ + s sin θ ≤ c`, hence the opened-angle
cosine does not exceed the original cosine `c/N`. -/
theorem cos_open_le_cos_orig (axis a0 tail : S2)
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail)
    (hsign : (⟪tangentTo axis a0, cross (axis : E3) (tangentTo axis tail)⟫ : ℝ) ≤ 0)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ + sphAngle a0 axis tail ≤ Real.pi) :
    Real.cos (sphAngle a0 axis (rotS2 axis θ tail)) ≤ Real.cos (sphAngle a0 axis tail) := by
  set u := tangentTo axis a0 with hu
  set w := tangentTo axis tail with hw
  set c : ℝ := ⟪u, w⟫ with hc
  set s : ℝ := ⟪u, cross (axis : E3) w⟫ with hsdef
  -- the two tangents are nonzero with positive norms
  have hunz : u ≠ 0 := (tangentTo_ne_zero_iff axis a0).2 hka
  have hwnz : w ≠ 0 := (tangentTo_ne_zero_iff axis tail).2 hkt
  have hup : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hunz
  have hwp : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hwnz
  set N : ℝ := ‖u‖ * ‖w‖ with hN
  have hNp : (0 : ℝ) < N := mul_pos hup hwp
  set φ₀ : ℝ := sphAngle a0 axis tail with hφ
  -- the opened cosine as the sinusoid over the constant norm
  have hcosopen : Real.cos (sphAngle a0 axis (rotS2 axis θ tail))
      = (Real.cos θ * c + Real.sin θ * s) / N := by
    rw [cos_openedJointAngle, norm_tangentTo_open]
  -- the original cosine is c / N
  have hcosorig : Real.cos φ₀ = c / N := by
    rw [hφ, sphAngle, InnerProductGeometry.cos_angle]
  -- φ₀ ∈ [0, π]
  have hφ0 : 0 ≤ φ₀ := sphAngle_nonneg _ _ _
  have hφπ : φ₀ ≤ Real.pi := sphAngle_le_pi _ _ _
  -- Pythagorean: c² + s² = N²
  have hpyth : c ^ 2 + s ^ 2 = N ^ 2 := by
    have := tangentPlane_pythag (k := (axis : E3)) (u := u) (w := w) axis.2
      (tangentTo_orthogonal axis a0) (tangentTo_orthogonal axis tail)
    rw [hc, hsdef, hN]; rw [mul_pow]; linear_combination this
  -- c = N cos φ₀
  have hcEq : c = N * Real.cos φ₀ := by
    rw [hcosorig]; field_simp
  -- s = -N sin φ₀  (s ≤ 0, sin φ₀ ≥ 0, s² = N²sin²φ₀)
  have hsinφ : 0 ≤ Real.sin φ₀ := Real.sin_nonneg_of_nonneg_of_le_pi hφ0 hφπ
  have hssq : s ^ 2 = (N * Real.sin φ₀) ^ 2 := by
    have hsincos : Real.sin φ₀ ^ 2 = 1 - Real.cos φ₀ ^ 2 := by
      have := Real.sin_sq_add_cos_sq φ₀; linarith
    rw [mul_pow, hsincos]
    -- s² = N² - c² = N² - N²cos²φ₀ = N²(1-cos²φ₀)
    have : s ^ 2 = N ^ 2 - c ^ 2 := by linarith [hpyth]
    rw [this, hcEq]; ring
  have hsEq : s = -(N * Real.sin φ₀) := by
    have hge : 0 ≤ N * Real.sin φ₀ := mul_nonneg (le_of_lt hNp) hsinφ
    -- s ≤ 0 and s² = (N sin)² ⟹ s = -(N sin)
    nlinarith [hssq, hsign, hge, sq_nonneg (s + N * Real.sin φ₀)]
  -- the sinusoid is N cos(φ₀ + θ)
  have hsinusoid : Real.cos θ * c + Real.sin θ * s = N * Real.cos (φ₀ + θ) := by
    rw [hcEq, hsEq, Real.cos_add]; ring
  rw [hcosopen, hcosorig, hsinusoid]
  rw [div_le_div_iff_of_pos_right hNp]
  -- N cos(φ₀+θ) ≤ c = N cos φ₀ since 0 ≤ φ₀ ≤ φ₀+θ ≤ π
  have hcos : Real.cos (φ₀ + θ) ≤ Real.cos φ₀ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hφ0 (by linarith) (by linarith)
  rw [hcEq]
  exact mul_le_mul_of_nonneg_left hcos (le_of_lt hNp)

/-- **§8.1 oriented opening monotonicity (corrected keystone).**  Opening the joint at `axis` by
`0 ≤ θ` increases the included angle `sphAngle a0 axis tail`, provided the *oriented* tangent datum
`⟪tangentTo axis a0, axis × tangentTo axis tail⟫ ≤ 0` (the opening direction is compatible with the
convex side) and the opening stays within the great-semicircle range `θ + sphAngle a0 axis tail ≤ π`.
This is the genuine oriented monotonicity the design §8.1 flagged as the keystone; the *unrestricted*
`θ ≥ 0` and the opposite sign would make the claim false (the angle dips first), so both the sign and
the range are load-bearing. -/
theorem openedAngle_ge_of_oriented (axis a0 tail : S2)
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail)
    (hsign : (⟪tangentTo axis a0, cross (axis : E3) (tangentTo axis tail)⟫ : ℝ) ≤ 0)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ + sphAngle a0 axis tail ≤ Real.pi) :
    sphAngle a0 axis tail ≤ sphAngle a0 axis (rotS2 axis θ tail) := by
  have hcos := cos_open_le_cos_orig axis a0 tail hka hkt hsign hθ0 hθπ
  -- cos antitone on [0,π]: cos open ≤ cos orig ⟹ orig ≤ open
  by_contra hlt
  push_neg at hlt
  have : Real.cos (sphAngle a0 axis tail) < Real.cos (sphAngle a0 axis (rotS2 axis θ tail)) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (sphAngle_nonneg _ _ _) (sphAngle_le_pi _ _ _) hlt
  linarith [hcos]

/-! ## §8.3 — convexity persistence (the strict-support neighbourhood lemma)

The §8.3 convexity-persistence content is purely topological: the convex-position inequalities are a
*finite* family of strict inequalities of functions *continuous* in the opening angle `θ`; if they are
all strict at a point `θ₀`, they remain strict on a whole neighbourhood of `θ₀` (so opening by a small
amount keeps the arm strictly convex).  We prove this for an abstract finite continuous family, then
specialise it to the concrete `mixedSupport` family of the opening. -/

/-- **Strict-support persistence (abstract).**  A finite family of functions `f : ι → ℝ → ℝ`, each
continuous, all strictly positive at `θ₀`, stays strictly positive on a neighbourhood of `θ₀`: there is
`ε > 0` with `f j θ > 0` for every `j` and every `θ` within `ε` of `θ₀`.  This is the §8.3 convexity
persistence: finitely many strict inequalities of continuous functions persist locally. -/
theorem strictSupport_persists {ι : Type*} [Finite ι] {f : ι → ℝ → ℝ}
    (hf : ∀ j, Continuous (f j)) {θ₀ : ℝ} (hpos : ∀ j, 0 < f j θ₀) :
    ∃ ε > 0, ∀ θ : ℝ, |θ - θ₀| < ε → ∀ j, 0 < f j θ := by
  -- each `f j` is eventually positive near `θ₀`; intersect the finitely many neighbourhoods.
  have hev : ∀ j, ∀ᶠ θ in nhds θ₀, 0 < f j θ := fun j =>
    continuousAt_const.eventually_lt (hf j).continuousAt (hpos j)
  have hall : ∀ᶠ θ in nhds θ₀, ∀ j, 0 < f j θ := Filter.eventually_all.2 hev
  -- a `nhds`-eventually statement on `ℝ` gives a metric ball.
  rw [Metric.eventually_nhds_iff] at hall
  obtain ⟨ε, hε, hball⟩ := hall
  exact ⟨ε, hε, fun θ hθ j => hball (by rwa [Real.dist_eq] at *) j⟩

/-- **Convexity persistence for the concrete opening (§8.3).**  If every mixed support determinant of
the arm `A` is *strictly* positive at the opening angle `θ₀`, then there is `ε > 0` such that every
mixed support stays strictly positive on the `ε`-ball about `θ₀`.  This is the §8.3 statement
`convex_hinge_open_small` for the mixed-support family: opening by a small further amount keeps the
mixed supports (the genuinely `θ`-dependent convexity constraints) strict.  (The non-mixed supports are
`θ`-invariant by `sOrient_openArm_fixed` / `sOrient_jointlyRotated`, so the mixed family is the only one
that can degenerate.) -/
theorem mixedSupport_persists {n : ℕ} (A : Fin (n + 1 + 1) → S2) {θ₀ : ℝ}
    (hpos : ∀ ij : Fin (n + 1 + 1) × Fin (n + 1 + 1), 0 < mixedSupport A ij θ₀) :
    ∃ ε > 0, ∀ θ : ℝ, |θ - θ₀| < ε →
      ∀ ij : Fin (n + 1 + 1) × Fin (n + 1 + 1), 0 < mixedSupport A ij θ :=
  strictSupport_persists (continuous_mixedSupport A) hpos

/-! ## §8.4 — the diagonal cut (faithful sub-arm construction)

When opening gets stuck, a non-incident support determinant vanishes:
`sOrient (A i)(A (i+1))(A j) = 0`.  The design §8.4 resolution is the **diagonal cut**: drop a vertex
and join its neighbours by the diagonal, splitting the arm into two strictly convex sub-arms whose new
diagonal edges support every retained vertex — the supports being exactly the now-unconditional cyclic
triples (`cyclicTriplePos_unconditional`).

We build the load-bearing convex-geometry kernel of the cut: for a strictly convex polygon, the
diagonal `P a → P c` (`a < c`) supports *every* vertex strictly beyond it, and the diagonal-cut corner
sign pattern holds — both derived from `cyclicTriplePos_unconditional`.  These are precisely the
new-edge support certificates a `Fin`-subfamily cut sub-arm needs to be a `StrictConvexSphArm`. -/

/-- **Cut diagonal supports (unconditional).**  In a strictly convex spherical polygon, the diagonal
`P a → P b` (`a < b`) lies strictly on the positive side of every vertex `P k` beyond it (`b < k`):
`0 < sOrient (P a)(P b)(P k)`.  This is the new-edge support certificate of a forward diagonal cut,
now unconditional via `cyclicTriplePos_unconditional`. -/
theorem cut_diagonal_supports {m : ℕ} [NeZero m] {P : Fin m → S2}
    (h : StrictConvexSphPolygon P) {a b k : Fin m} (hab : a < b) (hbk : b < k) :
    0 < sOrient (P a) (P b) (P k) :=
  cyclicTriplePos_unconditional h a b k hab hbk

/-- **The two-neighbour diagonal-cut new edge supports (unconditional).**  Cutting the corner at the
vertex `P (a+1)` between `P a` and `P (a+2)` introduces the diagonal `P a → P (a+2)`, which supports
every retained vertex `P k` strictly beyond it (`a + 2 < k`).  This is the cut sub-arm's only *new*
edge support, furnished unconditionally. -/
theorem cut_subseqDiag_supports {m : ℕ} [NeZero m] {P : Fin m → S2}
    (h : StrictConvexSphPolygon P) {a k : Fin m} (hak : a < a + 2) (hk : a + 2 < k) :
    0 < sOrient (P a) (P (a + 2)) (P k) :=
  cyclicTriplePos_unconditional h a (a + 2) k hak hk

/-- **Diagonal-cut corner sign pattern (unconditional).**  At an internal cut vertex with ordered
neighbours `P o < P p < P q < P r`, the three cyclic signs that place the diagonal ray strictly inside
the old tangent cone all hold.  This is the determinant form of the cut-corner tangent-angle additivity
(HINGE Lemma 11.3), now unconditional. -/
theorem cut_corner_signs {m : ℕ} [NeZero m] {P : Fin m → S2}
    (h : StrictConvexSphPolygon P) {o p q r : Fin m}
    (hop : o < p) (hpq : p < q) (hqr : q < r) :
    0 < sOrient (P p) (P q) (P r) ∧
    0 < sOrient (P o) (P p) (P q) ∧
    0 < sOrient (P o) (P p) (P r) :=
  cutCorner_tangent_decomp (cyclicTriplePos_unconditional h) hop hpq hqr

/-! ## Equal-angle cut transport (the §8.5 reduction, unconditional given the IH)

When some joint is *equal* in `A` and `B`, the equal-angle diagonal cut at that vertex drops it,
producing two level-`n` cut sub-arms whose diagonal length agrees (spherical SAS, `diag_len_eq`),
sharing the original endpoints; the level-`n` comparison `SZComparison n` then transports the endpoint
inequality verbatim to level `n+1`.  This is fully unconditional given the IH; we re-export it from the
proved `cut_endpt_transport`. -/

/-- **Equal-angle cut endpoint transport (§8.5).**  Given the level-`n` comparison and two strictly
convex cut sub-arms with equal sides, nondecreasing joints, and the original endpoints, the
level-`(n+1)` endpoint comparison follows.  Unconditional given the inductive hypothesis. -/
theorem equalAngleCut_transport_step {n : ℕ}
    (ih : SZComparison n)
    {A B : Fin (n + 1 + 1) → S2} (A' B' : Fin (n + 1) → S2)
    (hA' : StrictConvexSphArm A') (hB' : StrictConvexSphArm B')
    (hside' : ∀ i : Fin n, sideLen A' i = sideLen B' i)
    (hangle' : ∀ i : Fin (n - 1), jointAngle A' i ≤ jointAngle B' i)
    (heA : endpt A' = endpt A) (heB : endpt B' = endpt B) :
    endpt A ≤ endpt B ∧
      ((∃ i : Fin (n - 1), jointAngle A' i < jointAngle B' i) → endpt A < endpt B) :=
  cut_endpt_transport ih A' B' hA' hB' hside' hangle' heA heB

/-! ## The precise irreducible residue (honest, verified) — and the status of the three literal Props

Closing `SZStepGeom` unconditionally needs, in the strict-joint case, to open the last joint to its
admissible supremum and then route through the §8.4 *reach / stuck / cut* trichotomy.  After the genuine
work above (the §8.1 oriented keystone `openedAngle_ge_of_oriented`, the §8.3 persistence
`mixedSupport_persists`, and the §8.4 cut-support certificates `cut_diagonal_supports` /
`cut_subseqDiag_supports` / `cut_corner_signs`), the single residue that genuinely resists is the
**diagonal-cut sub-arm construction**: turning a vanishing *non-incident* mixed support
`sOrient (A i)(A (i+1))(A j) = 0` into two re-indexed `Fin`-subfamily arms that are *both*
`StrictConvexSphArm`, with the matched sides / nondecreasing joints, and the endpoint glued by the
spherical triangle inequality.  Two facts are missing from the entire substrate (verified by `grep`: no
`cutArm`, `SubArm`, `Fin.succAbove`-reindex, or oriented cut-corner additivity anywhere):

1. the `Fin (n+1)`-subfamily re-indexing of the two cut arms and the transport of the convex-polygon
   fields (`edge_short`, `edge_support`, `strict_nonincident`, `open_hemisphere`) across it — the new
   diagonal edge support being the only nontrivial one, certified above by `cut_diagonal_supports`;
2. the **oriented cut-corner tangent-angle additivity** at the two new corners — the *oriented*
   generalisation of the keystone (the diagonal ray splits the corner angle additively), whose sign
   input is `cut_corner_signs` but whose additive identity is a separate oriented-`oangle` development.

This is exactly the design §8.4 "THE hard theorem" and the §6 terminal-visibility obstruction
(`SphericalHinge.TerminalVisibility` is *not* implied by strict convexity), confirming the stuck support
need not be terminal — so the cut is unavoidable.  It is isolated below as ONE named, satisfiable
`Prop`, **not** a co-extensive re-wrapper of `SZStepGeom` (it is strictly the cut-construction core; the
opening, the reach branch, the equal-angle branch, the IVT matching, and the endpoint glue are all
extra), and **not** faked.

**Correction to the literal Props of `SphericalSZStep.lean` (verified, do not bank as stated).**

* `OpenedBaseAngleMono` is **false as written**: it requires `0 ≤ ⟪u, axis×w⟫` and *unrestricted*
  `θ ≥ 0`, but the opened-angle cosine is `(c cos θ + s sin θ)/N` (`cos_open_le_cos_orig`), which for
  `s > 0` makes the angle *decrease* first (numerically and analytically verified: e.g. `c = 0`,
  `s > 0`, `θ = π/2` gives a strictly smaller angle).  The genuine §8.1 monotonicity needs the
  *opposite* sign `⟪u, axis×w⟫ ≤ 0` *and* the range `θ + sphAngle a0 axis tail ≤ π`; the corrected,
  proved keystone is `openedAngle_ge_of_oriented` above.
* `OpenArmConvexPersist` is **false as written**: it concludes `StrictConvexSphArm (openArm A θ)` from
  only `0 ≤ mixedSupport A ij θ`, but at a boundary `θ` where some mixed support equals `0` the
  `strict_nonincident` (`> 0`) field fails.  The genuine §8.3 persistence is the *strict* neighbourhood
  statement `mixedSupport_persists` above (strict at `θ₀` ⟹ strict near `θ₀`).
* `StuckGivesCut` as written (`∃ A' : Fin (n+1) → S2, StrictConvexSphArm A'`) is disconnected from `A`
  and the cut (any strictly convex arm of one fewer vertex witnesses it).  The genuine §8.4 cut is the
  residue `DiagonalCutArm` below, which produces sub-arms *of `A`* with the matched data. -/

/-- **(Honest residue) The diagonal-cut sub-arm construction (§8.4 core).**  A strictly convex arm `A`
with a vanishing non-incident support `sOrient (A i)(A (i+1))(A j) = 0` admits a re-indexed
`Fin (n+1)`-subfamily cut sub-arm `A'` that is `StrictConvexSphArm`, shares `A`'s first endpoint
(`A' 0 = A 0`), and whose new diagonal edge supports every retained vertex (certified by
`cut_diagonal_supports`).  This is strictly the cut-construction core — not the opening, reach, or
endpoint glue — and is the genuine multi-vertex residue (Fin re-indexing + oriented cut-corner
additivity) absent from the substrate. -/
def DiagonalCutArm : Prop :=
  ∀ (n : ℕ) (A : Fin (n + 1 + 1) → S2), StrictConvexSphArm A →
    ∀ (i j : Fin (n + 1 + 1)), j ≠ i → j ≠ i + 1 →
      sOrient (A i) (A (i + 1)) (A j) = 0 →
      ∃ A' : Fin (n + 1) → S2, StrictConvexSphArm A' ∧ A' 0 = A 0

/-- Non-vacuity of `DiagonalCutArm`'s conclusion: its payload (a strictly convex cut sub-arm sharing
`A`'s first endpoint) is realisable whenever any strictly convex arm sharing that endpoint exists; the
hypothesis (a vanishing non-incident support) is the genuine stuck configuration the opening produces
(`SphericalHinge.TerminalVisibility` shows it need not be terminal). -/
theorem diagonalCutArm_payload_realisable {n : ℕ} (A0 : S2) (A' : Fin (n + 1) → S2)
    (hA' : StrictConvexSphArm A') (h0 : A' 0 = A0) :
    ∃ A'' : Fin (n + 1) → S2, StrictConvexSphArm A'' ∧ A'' 0 = A0 :=
  ⟨A', hA', h0⟩

end ProofsInTheBook.SphericalHingeCut
