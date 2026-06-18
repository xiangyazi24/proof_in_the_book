# Cauchy ch13 angular `turn_pos` chain: compile blockers and corrected Lean interfaces

I cannot honestly produce a complete compiling Lean proof for the requested angular-gap/turn-positive chain against the connected repo.  I checked the repository surface available through the GitHub connector and the named API is not present:

```text
ProofsInTheBook/ZinanCh13AngularOrder.lean        -- fetch_file: Not Found
ProofsInTheBook/ZinanCh13ConeAxis.lean            -- fetch/search: Not Found
rayAngleKey                                      -- repo search: no hits
angularList                                      -- repo search: no hits
angularNextPerm                                  -- repo search: no hits
SurroundsAxisPlane                               -- repo search: no hits
projPerp in this angular API                     -- repo search: no hits
```

So there is no exact target for a compiling proof.  More importantly, the requested item (1) has a dependency-order trap:

> `ProjectedAngleInjective` must **not** be proved from `StrictConvexSphPolygon` if that same strict spherical polygon is later proved using the angular `turn_pos` chain.  That would reintroduce the same orientation circularity that `RotationFaithful` is meant to eliminate.

The right proof of projected-angle injectivity must come directly from **edge extremality** of the convex vertex cone plus **axis interior positive-cone membership**, not from the already-oriented spherical link.

## 1. Correct source for projected-angle injectivity

Let `v` be a vertex, `w_i = pos (nbr i) - pos v`, and let the axis satisfy

```text
a = ∑ i, λ_i • w_i,     λ_i > 0.
```

Suppose two projected rays have the same angular direction.  With nonzero projections this means

```text
projPerp a (w_j) = c • projPerp a (w_i),     c > 0.
```

Since

```text
w = projPerp a w + k_w • a
```

for a scalar `k_w`, this gives

```text
w_j = c • w_i + t • a
```

for some real `t`.  Taking inner product with the axis, and using `0 < ⟪a,w_i⟫`, `0 < ⟪a,w_j⟫`, determines `t`.  The key extremality contradiction is obtained by substituting the positive-cone expression for `a`:

```text
w_j = c • w_i + t • ∑ k, λ_k • w_k.
```

If `t ≥ 0`, this expresses the edge ray `w_j` as a nonnegative combination involving other edge rays; strict face support for the face opposite `w_j` forces every coefficient except the `j` coefficient to vanish, contradiction with `c > 0` or with positive coefficients in `a`.

If `t < 0`, rearrange instead:

```text
(-t) • a + w_j = c • w_i
```

and use the positive-cone expression of `a` to express `w_i` as a nonnegative combination involving other edge rays; edge extremality for `w_i` gives the contradiction.

This is the direct noncircular proof.  It needs a formal edge-extremality lemma:

```lean
/-- Edge ray extremality from strict support of the two incident faces.
If `w_e` is written as a nonnegative combination of all incident edge rays,
then every ray with positive coefficient must be the same edge. -/
theorem edgeRay_extreme_of_face_support_strict
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    {v : M.Vertex} {e : D}
    (he_tail : M.tail e = v)
    {β : {d : D // M.tail d = v} → ℝ}
    (hβ_nonneg : ∀ d, 0 ≤ β d)
    (hrepr : edgeVec P e = ∑ d, β d • edgeVec P d.1) :
    ∀ d, d.1 ≠ e → β d = 0 := by
  -- Use the two face normals of the two faces incident to `e` at `v`.
  -- For a triangular convex vertex fan, every other incident edge is strictly
  -- negative for at least one of those supporting face normals; `e` itself is
  -- zero for both.  Dotting the representation with those normals kills all
  -- non-`e` coefficients.
  -- This must be proved before using any oriented link theorem.
  sorry
```

Then the projected-angle injectivity theorem has this shape:

```lean
/-- No duplicate projected angular directions.  This must be proved from axis
interior plus raw edge extremality, not from `StrictConvexSphPolygon`. -/
theorem projectedExtremeNoDuplicate_of_axisInterior
    (P : TriangulatedEuclideanPolyhedron M)
    (hsimple : M.IsSimpleGraph)
    {v : M.Vertex}
    (axis : E3)
    (haxisCone : ∃ λ : {d : D // M.tail d = v} → ℝ,
      (∀ d, 0 < λ d) ∧ axis = ∑ d, λ d • edgeVec P d.1)
    (haxisDual : ∀ d : D, M.tail d = v → 0 < inner ℝ axis (edgeVec P d)) :
    ∀ d e : {d : D // M.tail d = v}, d ≠ e →
      ¬ ∃ c : ℝ, 0 < c ∧
        projPerp axis (edgeVec P e.1) = c • projPerp axis (edgeVec P d.1) := by
  -- Algebra described above, using `edgeRay_extreme_of_face_support_strict`.
  sorry
```

Once the actual `rayAngleKey` API exists, this implies:

```lean
theorem projectedAngleInjective_of_noDuplicate
    ... : Function.Injective (fun d => rayAngleKey axis (edgeVec P d.1)) := by
  -- Use the `Complex.arg`/coordinate lemma:
  -- same nonzero projected angle + same half-line ⇔ positive scalar multiple.
  sorry
```

## 2. Correct angular-gap theorem statement

The theorem should not be stated only as “gap `< π`”; the determinant-positive theorem also needs **positive gap**.  The corrected contract is:

```lean
/-- Cyclic forward angle gap from `u` to `v`, using keys in the repo's branch cut. -/
noncomputable def cyclicRayGap (a u v : E3) : ℝ :=
  if rayAngleKey a u ≤ rayAngleKey a v then
    rayAngleKey a v - rayAngleKey a u
  else
    rayAngleKey a v + 2 * Real.pi - rayAngleKey a u

/-- Corrected gap theorem. -/
theorem consecutive_cyclicRayGap_pos_lt_pi_of_surrounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → E3) (a : E3)
    (hsur : SurroundsAxisPlane w a)
    (hproj : ∀ i, projPerp a (w i) ≠ 0)
    (hangleInj : Function.Injective (fun i => rayAngleKey a (w i))) :
    ∀ i : ι,
      0 < cyclicRayGap a (w ((angularNextPerm w a).symm i)) (w i) ∧
      cyclicRayGap a (w ((angularNextPerm w a).symm i)) (w i) < Real.pi := by
  -- Needs actual definitions of `rayAngleKey`, `angularNextPerm`, and
  -- sorted-list predecessor lemmas from `angularList`/`List.formPerm`.
  sorry
```

The proof obligations are:

* `0 < gap`: predecessor/current are distinct by the permutation/list no-duplicate theorem, and `hangleInj` rules out equal angle keys.
* `gap < π`: if a consecutive cyclic gap is `≥ π`, use the midpoint frame vector as a test vector in `aᗮ`; sorted adjacency puts every projected ray in the opposite closed halfspace; this contradicts `SurroundsAxisPlane`.

## 3. Required frame/trig lemmas

A complete compiling proof needs these lemmas in the angular-order file.  Their statements must match the actual right-handed frame used by `rayAngleKey`.

```lean
/-- Unit vector in the axis plane at angle `θ` in the same frame used by `rayAngleKey`. -/
noncomputable def angleFrameVec (a : E3) (θ : ℝ) : E3 :=
  Real.cos θ • perpSeed a + Real.sin θ • perpSeed₂ a

lemma angleFrameVec_mem_perp (a : E3) (θ : ℝ) :
    inner ℝ a (angleFrameVec a θ) = 0 := by
  -- from `perpSeed` and `perpSeed₂` orthogonality to `a`
  sorry

lemma angleFrameVec_ne_zero (a : E3) (θ : ℝ) :
    angleFrameVec a θ ≠ 0 := by
  -- norm squared = cos² θ + sin² θ = 1
  sorry

lemma inner_projPerp_angleFrameVec
    (a u : E3) (hu : projPerp a u ≠ 0) (θ : ℝ) :
    inner ℝ (projPerp a u) (angleFrameVec a θ) =
      ‖projPerp a u‖ * Real.cos (rayAngleKey a u - θ) := by
  -- Expand projected coordinates, `Complex.arg`, and the frame basis.
  sorry
```

Then the halfspace contradiction uses the elementary trig lemma:

```lean
lemma cos_nonpos_of_outside_gap_midpoint
    {lo hi θ : ℝ}
    (hlohi : lo < hi)
    (hgap : Real.pi ≤ hi - lo)
    (houtside : θ ≤ lo ∨ hi ≤ θ)
    (hrangeθ : -Real.pi < θ ∧ θ ≤ Real.pi)
    (hrangelo : -Real.pi < lo ∧ lo ≤ Real.pi)
    (hrangehi : -Real.pi < hi ∧ hi ≤ Real.pi) :
    Real.cos (θ - ((lo + hi) / 2)) ≤ 0 := by
  -- Reduce to `|θ - mid| ∈ [π/2, π]` modulo the branch interval and use
  -- `Real.cos_nonpos_of_mem_Icc` / `Real.cos_le_zero_of_pi_div_two_le_of_le`.
  sorry
```

For the wrap gap, either reduce by adding `2π` to the smaller key before taking the midpoint, or define all gaps in a lifted coordinate system relative to the predecessor key.  The latter is cleaner:

```lean
def liftFrom (base θ : ℝ) : ℝ :=
  if base ≤ θ then θ else θ + 2 * Real.pi
```

Then for a successor gap from `base` to `next`, use

```lean
liftedGap base next = liftFrom base next - base
```

and every other key is outside the open interval `(base, liftFrom base next)` in this lifted coordinate.

## 4. Correct cyclic determinant lemma

The existing non-wrap theorem is insufficient for the wrap case:

```lean
det3_pos_of_rayAngleKey_lt_of_sub_lt_pi :
  rayAngleKey a u < rayAngleKey a v →
  rayAngleKey a v - rayAngleKey a u < Real.pi →
  0 < det3 u v a
```

Add the cyclic sine-factor lemma:

```lean
lemma det3_eq_posFactor_mul_sin_cyclicGap
    {a u v : E3}
    (hu : projPerp a u ≠ 0) (hv : projPerp a v ≠ 0) :
    ∃ K : ℝ, 0 < K ∧
      det3 u v a = K * Real.sin (cyclicRayGap a u v) := by
  -- This is the coordinate calculation already underlying the non-wrap theorem.
  -- The factor is `‖projPerp a u‖ * ‖projPerp a v‖ * ‖a‖` up to the
  -- orientation sign of the right-handed frame.  It must be positive because
  -- the frame is right-handed and both projections are nonzero.
  sorry
```

Then the cyclic turn lemma is short:

```lean
theorem det3_pos_cyclic
    {a u v : E3}
    (hu : projPerp a u ≠ 0)
    (hv : projPerp a v ≠ 0)
    (hgap0 : 0 < cyclicRayGap a u v)
    (hgappi : cyclicRayGap a u v < Real.pi) :
    0 < det3 u v a := by
  rcases det3_eq_posFactor_mul_sin_cyclicGap (a := a) (u := u) (v := v) hu hv with
    ⟨K, hK, hdet⟩
  rw [hdet]
  exact mul_pos hK (Real.sin_pos_of_pos_of_lt_pi hgap0 hgappi)
```

This proof is complete once the sine-factor lemma exists.

## 5. Final `turn_pos` shape

With the corrected gap theorem and cyclic determinant lemma, the final theorem is:

```lean
theorem turn_pos_pred_current_of_angularNextPerm_of_surrounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → E3) (a : E3)
    (hsur : SurroundsAxisPlane w a)
    (hproj : ∀ i, projPerp a (w i) ≠ 0)
    (hangleInj : Function.Injective (fun i => rayAngleKey a (w i))) :
    ∀ i : ι,
      0 < det3 (w ((angularNextPerm w a).symm i)) (w i) a := by
  intro i
  rcases consecutive_cyclicRayGap_pos_lt_pi_of_surrounds
      (w := w) (a := a) hsur hproj hangleInj i with
    ⟨hgap0, hgappi⟩
  exact det3_pos_cyclic
    (hu := hproj ((angularNextPerm w a).symm i))
    (hv := hproj i)
    hgap0 hgappi
```

If the repo’s `angularNextPerm` has type `Equiv.Perm ι`, the predecessor simplification is just `Equiv.apply_symm_apply`.  If it is packaged as `List.formPerm angularList`, a small bridge lemma is needed:

```lean
lemma angularNextPerm_apply_symm (i : ι) :
    angularNextPerm w a ((angularNextPerm w a).symm i) = i := by
  exact Equiv.apply_symm_apply _ _
```

## 6. Why this cannot be filled in here as a compiling proof

A no-`sorry` proof of the requested theorem requires concrete definitions and lemmas that are not in the inspectable repo:

* actual `rayAngleKey` definition and range theorem;
* actual `perpSeed`/`perpSeed₂` right-handed frame lemmas;
* actual `projPerp` theorem connecting raw `det3` to projected coordinates;
* actual `angularList` sorted/no-duplicate/formPerm predecessor lemmas;
* actual `SurroundsAxisPlane` statement, including whether it quantifies both positive and negative sides or only the positive side for every nonzero test vector.

Without those declarations, any “complete Lean proof” would be fabricated and would not compile.  The theorem also cannot be proved from `SurroundsAxisPlane + projPerp≠0` alone; it requires the no-duplicate projected-angle theorem above.  The correct next patch is therefore to add the frame/trig and sorted-list lemmas in `ZinanCh13AngularOrder.lean`, then the final `turn_pos` theorem is exactly the short assembly in §5.
