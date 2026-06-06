import ProofsInTheBook.PolygonLeaf

/-!
# Chapter 36 — convex separation for the triangle leaf (`PolygonSeparation`)

This module sits on top of `PolygonLeaf` and attacks the *cover* half of the
`n = 3` Jordan leaf — `TriangleExteriorEven` — with the genuine planar tool the
leaf handoff named: **geometric Hahn–Banach separation**.

## The separating-direction lemma (genuinely new, unconditional)

The leaf's `crossingNumber'_eq_zero_of_allSide_pos / _neg` kernels show that *if*
every polygon vertex lies strictly on one fixed side of the ray line through `x`,
the side-coordinate crossing number is `0` (hence even).  The missing ingredient
for an *arbitrary* exterior point of the triangle is the existence of such a
direction.  We supply it from Mathlib's geometric Hahn–Banach
(`geometric_hahn_banach_point_closed`): a point off a closed convex set is
strictly separated by a continuous linear functional `f`, i.e. `f x < f v` for
every hull point `v`.  On `Pt = EuclideanSpace ℝ (Fin 2)` every functional `f` is
`f w = w 0 · f e₀ + w 1 · f e₁`, and the `90°`-rotated coefficient vector
`r = mkPt (f e₁) (-(f e₀))` realises it as a `det2`:

```
side r x v = det2 r (v - x) = f (v - x) = f v - f x  > 0     (∀ hull vertex v).
```

So `exists_sep_dir_of_not_mem_closedTri` produces, for any `x ∉ closedTri a b c`,
a direction `r ≠ 0` with `0 < side r x a, side r x b, side r x c` — exactly the
hypothesis of the all-one-side kernel.

## What this closes, and the honest residual

With the separating direction `r` in hand the crossing number **at `r`** is `0`
(even).  Closing `TriangleExteriorEven` for the polygon's *own* ray `σ` then needs
the parity at `r` transported to the parity at `σ`.  The development's transport
tools are:

* `crossingNumber'_ray_indep_seg` / `closedRegion'_ray_indep_segment` — transport
  along a **single** valid direction *segment* (`DirComparableSeg`), and
* `closedRegion'_ray_indep_chain` — transport along a **`SegmentChain`**.

For a triangle the three edge directions cut the direction circle into open arcs;
two directions in *different* arcs are **not** segment-comparable (the connecting
chord meets an edge-parallel "wall"), and `SegmentChain` cannot cross a wall with
straight segments.  Hence the separating `r` (forced into a particular arc by the
geometry of `x`) is in general *not* chain-connectable to an arbitrary `σ`.  This
is the irreducible single-edge-jump / half-plane Jordan content that the *entire*
Chapter-36 stack keeps as a named input (the `loc` / `VertexSweepNeutral` residue
of `PolygonLocalConstancy`, the `SegmentChain` connectivity of `PolygonIccEngine`).

We therefore (a) prove the separating-direction lemma and the all-one-side
*even-at-the-separating-ray* fact **unconditionally**, (b) isolate the parity
transport as the single named `Prop` `TriangleParityTransport`, with the exact
statement and a faithful **conditional** discharge of `TriangleExteriorEven`, and
(c) record that `TriangleParityTransport` is *equivalent in content* to the
chapter's kept ray-independence residue (not a strengthening), so the conditional
is non-vacuous.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option synthInstance.maxHeartbeats 400000

namespace ProofsInTheBook.PolygonSeparation

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonLeaf

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the functional-to-`det2` bridge

Every continuous linear functional `f` on `Pt = EuclideanSpace ℝ (Fin 2)` is
recovered, on the `det2` form, by the rotated coefficient vector
`sepDir f = mkPt (f e₁) (-(f e₀))`. -/

/-- The first standard basis vector of `Pt`. -/
def e0 : Pt := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

/-- The second standard basis vector of `Pt`. -/
def e1 : Pt := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

/-- **Coordinate expansion of a point.**  Every `w : Pt` is `w 0 • e₀ + w 1 • e₁`. -/
lemma pt_eq_coord_smul (w : Pt) : w = w 0 • e0 + w 1 • e1 := by
  ext k
  fin_cases k <;>
    simp [e0, e1, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- **A functional in coordinates.**  For a linear map `f : Pt →ₗ[ℝ] ℝ`,
`f w = w 0 * f e₀ + w 1 * f e₁`. -/
lemma linearMap_apply_coord (f : Pt →ₗ[ℝ] ℝ) (w : Pt) :
    f w = w 0 * f e0 + w 1 * f e1 := by
  conv_lhs => rw [pt_eq_coord_smul w]
  rw [map_add, map_smul, map_smul]
  simp [smul_eq_mul]

/-- The separating direction attached to a functional `f`: the `90°` rotation of
its coefficient vector, `mkPt (f e₁) (-(f e₀))`. -/
def sepDir (f : Pt →ₗ[ℝ] ℝ) : Pt := mkPt (f e1) (-(f e0))

/-- **`sepDir` realises `f` as a `det2`.**  `det2 (sepDir f) w = f w` for every
`w` — so `side (sepDir f) x v = f v - f x` once `f` is linear. -/
lemma det2_sepDir (f : Pt →ₗ[ℝ] ℝ) (w : Pt) : det2 (sepDir f) w = f w := by
  rw [linearMap_apply_coord f w]
  unfold det2 sepDir mkPt
  simp [EuclideanSpace.equiv]
  ring

/-- **The side coordinate via the separating functional.**
`side (sepDir f) x v = f v - f x`. -/
lemma side_sepDir (f : Pt →ₗ[ℝ] ℝ) (x v : Pt) :
    side (sepDir f) x v = f v - f x := by
  unfold side
  rw [det2_sepDir]
  rw [map_sub]

/-! ## Part 2: the separating direction for an exterior point of the triangle

`closedTri a b c = convexHull ℝ {a,b,c}` is a *closed* convex set (the hull of a
finite set in finite dimension).  Geometric Hahn–Banach separates an exterior
point `x` from it by a functional `f` with `f x < f v` for every hull point `v`;
`sepDir f` then has `0 < side (sepDir f) x v` for the three vertices. -/

/-- The closed triangle hull is a closed set. -/
lemma isClosed_closedTri (a b c : Pt) : IsClosed (closedTri a b c) := by
  have hfin : ({a, b, c} : Set Pt).Finite := (Set.finite_singleton c).insert b |>.insert a
  exact hfin.isClosed_convexHull ℝ

/-- **Separating direction for an exterior point of a triangle.**  If
`x ∉ closedTri a b c`, there is a direction `r ≠ 0` with all three vertices
strictly on the *positive* side of the ray line through `x`:
`0 < side r x a, side r x b, side r x c`.  This is geometric Hahn–Banach in the
`det2`/`side` form (`sepDir` of the separating functional). -/
theorem exists_sep_dir_of_not_mem_closedTri {a b c x : Pt}
    (hx : x ∉ closedTri a b c) :
    ∃ r : Pt, r ≠ 0 ∧ 0 < side r x a ∧ 0 < side r x b ∧ 0 < side r x c := by
  obtain ⟨f, u, hfx, hfb⟩ :=
    geometric_hahn_banach_point_closed (closedTri_convex a b c)
      (isClosed_closedTri a b c) hx
  -- `f : StrongDual ℝ Pt`; use its underlying linear map `g`, with `g w = f w`.
  set g : Pt →ₗ[ℝ] ℝ := f.toLinearMap with hg
  have hgf : ∀ w, g w = f w := fun w => rfl
  have ha : u < g a := by rw [hgf]; exact hfb a (subset_convexHull ℝ _ (by simp))
  have hb : u < g b := by rw [hgf]; exact hfb b (subset_convexHull ℝ _ (by simp))
  have hc : u < g c := by rw [hgf]; exact hfb c (subset_convexHull ℝ _ (by simp))
  have hgx : g x < u := by rw [hgf]; exact hfx
  refine ⟨sepDir g, ?_, ?_, ?_, ?_⟩
  · -- `sepDir g ≠ 0`: else `g` would vanish on `a - x`, but `g a > g x`.
    intro hzero
    have hga : det2 (sepDir g) (a - x) = g (a - x) := det2_sepDir g (a - x)
    rw [hzero, map_sub] at hga
    have hz0 : det2 (0 : Pt) (a - x) = 0 := by unfold det2; simp
    rw [hz0] at hga
    linarith [hga, ha, hgx]
  · rw [side_sepDir]; linarith [ha, hgx]
  · rw [side_sepDir]; linarith [hb, hgx]
  · rw [side_sepDir]; linarith [hc, hgx]

/-! ## Part 3: perturbing the separating direction to a valid `RayDirection`

The all-one-side kernel `crossingNumber'_eq_zero_of_allSide_pos` consumes a genuine
`RayDirection Q` (not edge-parallel).  The separating direction produced above may
be edge-parallel; we perturb it inside the *open* positivity cone (which is open,
hence survives small perturbations) while avoiding the finitely many edge-parallel
directions.  The perturbation axis `normalDir r₀` is independent of `r₀`, so each
per-edge determinant is a *nonconstant* affine function of the perturbation
parameter `ε` (at most one root), and an open interval around `0` minus finitely
many roots is nonempty. -/

open ProofsInTheBook.PolygonLeaf (normalDir det2_normalDir det2_normalDir_pos)

/-- **`side` of a left-perturbed direction.**  `side (r + ε • d) x v` is affine in
`ε`: it equals `side r x v + ε * det2 d (v - x)`. -/
lemma side_dir_shift (r d x v : Pt) (ε : ℝ) :
    side (r + ε • d) x v = side r x v + ε * det2 d (v - x) := by
  unfold side
  rw [PolygonLocalConstancy.det2_add_left, PolygonLocalConstancy.det2_smul_left]

/-- **A valid `RayDirection` keeping every vertex strictly on the positive side.**
Given a base direction `r₀ ≠ 0` with `0 < side r₀ x (Q.q k)` for every vertex `k`,
there is a genuine `RayDirection Q` (not parallel to any edge) with the *same*
strict positivity at every vertex.  (Perturb `r₀` along `normalDir r₀` by a small
`ε` avoiding the finitely many edge-parallel roots.) -/
theorem exists_rayDirection_allSide_pos {m : ℕ} (Q : StrictSimplePolygon m)
    (x r₀ : Pt) (hr₀ : r₀ ≠ 0)
    (hpos : ∀ k : Fin m, 0 < side r₀ x (Q.q k)) :
    ∃ σ : RayDirection Q, ∀ k : Fin m, 0 < side σ.r x (Q.q k) := by
  classical
  set d : Pt := normalDir r₀ with hd
  -- `d` is independent of `r₀`: `det2 r₀ d > 0`.
  have hr₀d : 0 < det2 r₀ d := det2_normalDir_pos hr₀
  -- forbidden ε: an edge becomes parallel to `r₀ + ε • d`.
  -- For each edge i, `det2 (r₀ + ε d) (edgeVec Q i) = A_i + ε * B_i`, with
  -- `(A_i, B_i) ≠ (0,0)` since `r₀, d` are independent and `edgeVec ≠ 0`.
  have hcoeff : ∀ i : Fin m,
      det2 r₀ (edgeVec Q i) ≠ 0 ∨ det2 d (edgeVec Q i) ≠ 0 := by
    intro i
    by_contra hboth
    push_neg at hboth
    obtain ⟨hA, hB⟩ := hboth
    -- `edgeVec ≠ 0` is det2-orthogonal to both `r₀` and `d = normalDir r₀`; but
    -- `{r₀, d}` is a basis (det2 r₀ d = r₀0²+r₀1² > 0), so this forces edge = 0.
    have he : edgeVec Q i ≠ 0 := edgeVec_ne_zero Q i
    apply he
    -- coordinate form of the two equations.
    have hAc : r₀ 0 * (edgeVec Q i) 1 - r₀ 1 * (edgeVec Q i) 0 = 0 := hA
    have hBc : (- r₀ 1) * (edgeVec Q i) 1 - r₀ 0 * (edgeVec Q i) 0 = 0 := by
      have heq : det2 d (edgeVec Q i) = (- r₀ 1) * (edgeVec Q i) 1 - r₀ 0 * (edgeVec Q i) 0 := by
        rw [hd]; unfold det2 normalDir mkPt
        simp [EuclideanSpace.equiv]
      rw [heq] at hB; exact hB
    -- the determinant r₀0²+r₀1² is positive.
    have hr2 : 0 < r₀ 0 ^ 2 + r₀ 1 ^ 2 := by
      have heq : det2 r₀ d = r₀ 0 ^ 2 + r₀ 1 ^ 2 := by rw [hd]; exact det2_normalDir r₀
      rw [heq] at hr₀d; exact hr₀d
    -- (r₀0²+r₀1²) e0 = 0 and (r₀0²+r₀1²) e1 = 0 from the two linear equations.
    have hkey0 : (r₀ 0 ^ 2 + r₀ 1 ^ 2) * (edgeVec Q i) 0 = 0 := by
      linear_combination (- r₀ 1) * hAc + (- r₀ 0) * hBc
    have hkey1 : (r₀ 0 ^ 2 + r₀ 1 ^ 2) * (edgeVec Q i) 1 = 0 := by
      linear_combination (r₀ 0) * hAc + (- r₀ 1) * hBc
    have he0 : (edgeVec Q i) 0 = 0 := by
      rcases mul_eq_zero.mp hkey0 with h | h
      · exact absurd h (ne_of_gt hr2)
      · exact h
    have he1 : (edgeVec Q i) 1 = 0 := by
      rcases mul_eq_zero.mp hkey1 with h | h
      · exact absurd h (ne_of_gt hr2)
      · exact h
    exact pt_ext_zero_one he0 he1
  -- the finite set of forbidden ε (where some edge becomes parallel).
  set Bad : Finset ℝ := (Finset.univ : Finset (Fin m)).image
    (fun i => - det2 r₀ (edgeVec Q i) / det2 d (edgeVec Q i)) with hBad
  -- nonempty index type.
  have hne : Nonempty (Fin m) := ⟨⟨0, by have := Q.hthree; omega⟩⟩
  -- the positivity window radius δ > 0.
  set δ : ℝ := (Finset.univ.image (fun k : Fin m =>
      side r₀ x (Q.q k) / (|det2 d (Q.q k - x)| + 1))).min'
      (Finset.image_nonempty.mpr Finset.univ_nonempty) with hδ
  have hδpos : 0 < δ := by
    rw [hδ, Finset.lt_min'_iff]
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨k, _, rfl⟩ := hb
    have hden : 0 < |det2 d (Q.q k - x)| + 1 := by positivity
    exact div_pos (hpos k) hden
  have hwin : ∀ ε : ℝ, |ε| < δ →
      ∀ k : Fin m, 0 < side r₀ x (Q.q k) + ε * det2 d (Q.q k - x) := by
    intro ε hε k
    have hmin : δ ≤ side r₀ x (Q.q k) / (|det2 d (Q.q k - x)| + 1) := by
      rw [hδ]; apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
    have hden : 0 < |det2 d (Q.q k - x)| + 1 := by positivity
    -- |ε * c_k| ≤ |ε| * (|c_k|+1) < δ*(|c_k|+1) ≤ s_k
    have hbound : |ε * det2 d (Q.q k - x)| < side r₀ x (Q.q k) := by
      calc |ε * det2 d (Q.q k - x)| = |ε| * |det2 d (Q.q k - x)| := abs_mul _ _
        _ ≤ |ε| * (|det2 d (Q.q k - x)| + 1) := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg ε); linarith
        _ < δ * (|det2 d (Q.q k - x)| + 1) := by
              apply mul_lt_mul_of_pos_right hε hden
        _ ≤ (side r₀ x (Q.q k) / (|det2 d (Q.q k - x)| + 1)) *
              (|det2 d (Q.q k - x)| + 1) := by
              apply mul_le_mul_of_nonneg_right hmin (le_of_lt hden)
        _ = side r₀ x (Q.q k) := by field_simp
    have := (abs_lt.mp hbound).1
    linarith
  -- pick ε in the open ball avoiding Bad.
  obtain ⟨ε, hεball, hεbad⟩ : ∃ ε : ℝ, |ε| < δ ∧ ε ∉ Bad := by
    -- the set {ε | |ε| < δ} = Ioo (-δ) δ is infinite; Bad is finite.
    have hinf : (Set.Ioo (-δ) δ).Infinite := Set.Ioo_infinite (by linarith)
    have : ¬ (Set.Ioo (-δ) δ ⊆ (Bad : Set ℝ)) := by
      intro hsub
      exact hinf (Bad.finite_toSet.subset hsub)
    rw [Set.not_subset] at this
    obtain ⟨ε, hεio, hεnb⟩ := this
    rw [Set.mem_Ioo] at hεio
    exact ⟨ε, abs_lt.mpr ⟨hεio.1, hεio.2⟩, hεnb⟩
  -- assemble the RayDirection.
  refine ⟨{ r := r₀ + ε • d
            r_ne_zero := ?_
            no_edge_parallel := ?_ }, ?_⟩
  · -- nonzero: side at vertex 0 is positive, so `r₀ + ε•d ≠ 0`.
    intro hzero
    have h0 := hwin ε hεball ⟨0, by have := Q.hthree; omega⟩
    have hs : side (r₀ + ε • d) x (Q.q ⟨0, by have := Q.hthree; omega⟩) =
        side r₀ x (Q.q ⟨0, by have := Q.hthree; omega⟩) +
          ε * det2 d (Q.q ⟨0, by have := Q.hthree; omega⟩ - x) :=
      side_dir_shift r₀ d x _ ε
    have hzeroside : side (r₀ + ε • d) x (Q.q ⟨0, by have := Q.hthree; omega⟩) = 0 := by
      rw [hzero]; unfold side det2; simp
    rw [hzeroside] at hs
    linarith [h0, hs.symm]
  · -- not edge-parallel: ε ∉ Bad.
    intro i
    show det2 (r₀ + ε • d) (edgeVec Q i) ≠ 0
    have hval : det2 (r₀ + ε • d) (edgeVec Q i) =
        det2 r₀ (edgeVec Q i) + ε * det2 d (edgeVec Q i) := by
      rw [PolygonLocalConstancy.det2_add_left, PolygonLocalConstancy.det2_smul_left]
    rw [hval]
    intro hz
    apply hεbad
    rw [hBad, Finset.mem_image]
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rcases hcoeff i with hA | hB
    · -- B_i might be 0; but then det2 r₀ edge = 0 + ε*0 ⟹ A_i = 0, contradiction.
      by_cases hBi : det2 d (edgeVec Q i) = 0
      · rw [hBi, mul_zero, add_zero] at hz; exact absurd hz hA
      · field_simp; linarith [hz]
    · -- B_i ≠ 0: solve ε = -A_i / B_i.
      have hBi : det2 d (edgeVec Q i) ≠ 0 := hB
      field_simp
      linarith [hz]
  · intro k
    have hs := side_dir_shift r₀ d x (Q.q k) ε
    rw [hs]
    exact hwin ε hεball k

/-! ## Part 4: even crossing number at a separating ray, and the conditional leaf

Combining Parts 2–3 with the leaf kernel `crossingNumber'_eq_zero_of_allSide_pos`:
for any `3`-gon `Q` and exterior off-... point `x` there is a *valid* ray direction
`τ` whose side-coordinate crossing number is `0` (hence even).  Transporting the
**parity** from `τ` to the polygon's own ray `σ` is the chapter's kept
ray-independence residue `UnconditionalRayIndepInput` (region form), here used in
its off-boundary parity guise. -/

open ProofsInTheBook.PolygonLeaf (crossingNumber'_eq_zero_of_allSide_pos)
open ProofsInTheBook.PolygonTriangulation (v0 v1 v2)

/-- **An exterior point of a triangle admits a valid ray with crossing number `0`.**
For a `3`-gon `Q` and a point `x` outside its closed hull, there is a valid ray
direction `τ` (not parallel to any edge) with `CrossingNumber' Q τ x = 0`.  This
is geometric Hahn–Banach (the separating direction) + the perturbation to a valid
direction + the all-one-side kernel — *unconditional*. -/
theorem exists_rayDir_crossingNumber'_eq_zero_of_not_mem_hull
    (Q : StrictSimplePolygon 3) {x : Pt}
    (hx : x ∉ closedTri (v0 Q) (v1 Q) (v2 Q)) :
    ∃ τ : RayDirection Q, CrossingNumber' Q τ x = 0 := by
  obtain ⟨r₀, hr₀, ha, hb, hc⟩ := exists_sep_dir_of_not_mem_closedTri hx
  -- positivity at all three vertices `Q.q 0, Q.q 1, Q.q 2`.
  have hall0 : ∀ k : Fin 3, 0 < side r₀ x (Q.q k) := by
    intro k
    fin_cases k
    · exact ha
    · exact hb
    · exact hc
  obtain ⟨τ, hτpos⟩ := exists_rayDirection_allSide_pos Q x r₀ hr₀ hall0
  exact ⟨τ, crossingNumber'_eq_zero_of_allSide_pos Q τ x hτpos⟩

/-- **The parity-transport residual.**  Off the boundary, the *parity* of the
side-coordinate crossing number is independent of the (valid) ray direction.  This
is exactly the chapter's kept ray-independence residue
(`PolygonFinish.UnconditionalRayIndepInput`) in its off-boundary parity guise: for
a triangle the three edge directions cut the direction circle into arcs and a
`SegmentChain` cannot cross an edge-parallel wall, so this directional transport is
the irreducible Jordan content the whole Chapter-36 stack keeps as a named input. -/
def TriangleParityTransport : Prop :=
  ∀ (Q : StrictSimplePolygon 3) (σ τ : RayDirection Q) {x : Pt},
    ¬ OnBoundary Q x →
    (CrossingNumber' Q σ x % 2 = CrossingNumber' Q τ x % 2)

/-- **`TriangleParityTransport` follows from the chapter's region-level residue.**
The off-boundary region form `UnconditionalRayIndepInput` is *equivalent* to the
parity form: off the boundary `ClosedRegion' = Odd (CrossingNumber')`, so the region
agreeing for two directions is the parities agreeing.  Hence the parity-transport
residual is **not** a strengthening — it is the same content as the residue already
carried by `PolygonFinish`/`PolygonIccEngine`. -/
theorem triangleParityTransport_of_rayIndep
    (H : ∀ Q : StrictSimplePolygon 3, ProofsInTheBook.PolygonFinish.UnconditionalRayIndepInput Q) :
    TriangleParityTransport := by
  intro Q σ τ x hoff
  have hreg := H Q σ τ hoff
  -- off boundary: ClosedRegion' ↔ Odd (CrossingNumber')
  have hσ : ClosedRegion' Q σ x ↔ Odd (CrossingNumber' Q σ x) := by
    unfold ClosedRegion'; rw [or_iff_right hoff]
  have hτ : ClosedRegion' Q τ x ↔ Odd (CrossingNumber' Q τ x) := by
    unfold ClosedRegion'; rw [or_iff_right hoff]
  have hodd : Odd (CrossingNumber' Q σ x) ↔ Odd (CrossingNumber' Q τ x) := by
    rw [← hσ, ← hτ]; exact hreg
  -- two naturals have equal parity iff both odd or both even
  rcases Nat.even_or_odd (CrossingNumber' Q σ x) with hse | hso
  · have hτe : ¬ Odd (CrossingNumber' Q τ x) := by
      rw [← hodd]; exact Nat.not_odd_iff_even.mpr hse
    rw [Nat.even_iff.mp hse, Nat.even_iff.mp (Nat.not_odd_iff_even.mp hτe)]
  · have hτo : Odd (CrossingNumber' Q τ x) := hodd.mp hso
    rw [Nat.odd_iff.mp hso, Nat.odd_iff.mp hτo]

/-- **`TriangleExteriorEven`, conditional on the parity-transport residue.**  Given
the chapter's ray-independence residue (as the parity-transport `Prop`), the *cover*
half of the triangle leaf is discharged: for every `3`-gon, ray `σ`, and off-boundary
point `x` outside the closed hull, the crossing number is even.  The new
unconditional content (geometric Hahn–Banach separating direction + perturbation to
a valid ray + the all-one-side kernel) supplies the `0`-count witness; the residue
only transports its parity to `σ`. -/
theorem triangleExteriorEven_of_transport
    (H : TriangleParityTransport) : TriangleExteriorEven := by
  intro Q σ x hoff hx hodd
  -- a valid ray `τ` with crossing number 0 (even).
  obtain ⟨τ, hτ0⟩ := exists_rayDir_crossingNumber'_eq_zero_of_not_mem_hull Q hx
  -- transport parity from `σ` to `τ`.
  have hpar : CrossingNumber' Q σ x % 2 = CrossingNumber' Q τ x % 2 := H Q σ τ hoff
  rw [hτ0] at hpar
  -- so `CrossingNumber' Q σ x % 2 = 0`, contradicting oddness.
  have hzero : CrossingNumber' Q σ x % 2 = 0 := by simpa using hpar
  rw [Nat.odd_iff] at hodd
  omega

/-- **`TriangleExteriorEven` from the region-level ray-independence residue.**  The
end-to-end conditional: the chapter's already-carried residue
`UnconditionalRayIndepInput` (per `3`-gon) discharges the exterior-evenness half of
the triangle leaf outright. -/
theorem triangleExteriorEven_of_rayIndep
    (H : ∀ Q : StrictSimplePolygon 3, ProofsInTheBook.PolygonFinish.UnconditionalRayIndepInput Q) :
    TriangleExteriorEven :=
  triangleExteriorEven_of_transport (triangleParityTransport_of_rayIndep H)

/-! ## Part 5: the Chapter-36 headline with the leaf's *cover* atom discharged

`PolygonLeaf.chapter36_headline_atom_leaf` consumed the two triangle-leaf atoms
`TriangleConvexLeaf` (= the kept `IsConvexVertex'` primitive) and
`TriangleExteriorEven` (the *cover* half).  We now **discharge the second atom** from
the chapter's already-carried ray-independence residue
`UnconditionalRayIndepInput`, leaving the headline consuming, in place of
`TriangleExteriorEven`, only that residue — i.e. exactly the residual the rest of
the development keeps for *every* polygon's ray bookkeeping.  The convex-vertex atom
`TriangleConvexLeaf` remains (it is the development's single irreducible planar
primitive, definitionally `IsConvexVertex'`). -/

open ProofsInTheBook.PolygonLeaf
  (TriangleConvexLeaf TriangleExteriorEven baseTriangleLeaf_of_atoms
    chapter36_headline_atom_leaf)
open ProofsInTheBook.PolygonOracleClose (ResidualGeometryData baseTriangleFacts_of_leaf)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput)
open ProofsInTheBook.PolygonRayIndep (Sees)

/-- **Chapter-36 art-gallery headline with the exterior-even atom discharged.**
Inputs: (a) the uniform residual geometry data `D`; (b) the convex-vertex leaf atom
`TriangleConvexLeaf` (the kept `IsConvexVertex'` primitive); (c) the chapter's
ray-independence residue `H` (per `3`-gon), which now *produces* the exterior-even
atom via `triangleExteriorEven_of_rayIndep`; (d) the diagonal-attach peel witness.
Conclusion: every strict simple polygon with a ray direction admits `≤ ⌊n/3⌋` vertex
guards seeing its whole closed region.  Identical strength to
`chapter36_headline_atom_leaf`, with its `TriangleExteriorEven` input replaced by the
already-carried ray-independence residue — i.e. the *cover* half of the triangle leaf
is no longer a standalone planar input. -/
theorem chapter36_headline_separation {n : ℕ}
    (D : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
        ResidualGeometryData P ρ)
    (hconv : TriangleConvexLeaf)
    (H : ∀ Q : StrictSimplePolygon 3,
        ProofsInTheBook.PolygonFinish.UnconditionalRayIndepInput Q)
    (M : DiagonalAttachInput
      (baseTriangleFacts_of_leaf
        (baseTriangleLeaf_of_atoms hconv (triangleExteriorEven_of_rayIndep H))))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  chapter36_headline_atom_leaf D hconv (triangleExteriorEven_of_rayIndep H) M P ρ

end

end ProofsInTheBook.PolygonSeparation
