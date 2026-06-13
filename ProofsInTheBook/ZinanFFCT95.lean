import ProofsInTheBook.ZinanFFCT94

/-!
# `ZinanFFCT95` -- the gnomonic single-wind certificate (design bricks C + D-strict)

This file delivers the spherical transport layer of the single-wind no-repeat
route (design `HANDOFF/design-rounds/ch13-singlewind-route.md`):

## Brick C : `GnomonicSingleWind`
A `Type`-valued certificate for a spherical arm `P : Fin (n+1) → S2`.  It records
an open-hemisphere normal `h` (`hpos : 0 < ⟪h, P i⟫` for every vertex) together
with a full `FFCT94.PlanarLiftedTurnSpan` for the gnomonic image
`Q i = gproj h (P i)` in the affine plane `⟨h, ·⟩ = 1`.  Carrying the lifted
turn certificate (`θ`, `ρ`, `edge_eq`, `turn_pos`, `turn_lt_pi`, `one_wind`) is
exactly the data the no-repeat theorem `FFCT94`-style consumes.

## Brick D-strict : `strictConvexSphArm_gnomonicSingleWind`
`StrictConvexSphArm A → GnomonicSingleWind A`.

The construction has two genuinely different layers:

* **the geometric / hemisphere layer** (proved here, axiom-clean): the
  open-hemisphere normal `h` exists with `‖h‖ = 1` and `0 < ⟪h, A i⟫`; from it we
  build an *explicit orthonormal frame* `(u, v) ⊥ h` (`frameU`, `frameV` via a
  Gram-Schmidt step against a fixed axis and a cross product), and the gnomonic
  images all lie in the plane `⟨h, ·⟩ = 1`;

* **the analytic single-wind layer** (the *real content*, isolated): producing
  the lifted real turn function `θ : ℕ → ℝ` with `turn_pos`, `turn_lt_pi` and the
  decisive `one_wind : θ N - θ 0 < 2π`.  This is the open strictly-convex planar
  chain's total-turning bound.  Per the honesty contract it is isolated as one
  named, *non-vacuous* planar `Prop`
  `StrictPlanarChainLiftedTurnSpanExists`, exactly the way `ZinanFFCT92`
  isolates `PlanarClosedWeakStrictNoRepeat`.  `FFCT94.witChain_certificate`
  witnesses that the lifted-turn certificate it asks for is genuinely
  inhabitable, so the residual is not vacuous.

What is proved *unconditionally* in this file:

* `frame_orthonormal` : the explicit `(u, v) ⊥ h` frame is orthonormal, for any
  unit `h` — the load-bearing constructive geometric lemma;
* `gnomonic_image_in_plane` : the gnomonic images lie in `⟨h, ·⟩ = 1`;
* `gnomonic_image_edge_ne` : strict arms have nondegenerate gnomonic edges;
* `strictConvexSphArm_gnomonicSingleWind` : the certificate, modulo the one
  isolated planar lifted-turn residue.
-/

noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT94

namespace ProofsInTheBook.ZinanFFCT95

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## Brick C : the gnomonic single-wind certificate. -/

/-- **Gnomonic single-wind certificate** (design brick C).  A `Type`-valued
certificate for a spherical arm `P`: an open-hemisphere normal `h` with every
vertex strictly inside (`hpos`), an orthonormal-in-`h^⊥` frame `(u, v)`, and a
full `FFCT94.PlanarLiftedTurnSpan` for the gnomonic image `gproj h ∘ P` in the
affine plane `⟨h, ·⟩ = 1`. -/
structure GnomonicSingleWind {n : ℕ} (P : Fin (n + 1) → S2) where
  h : E3
  hnorm : ‖h‖ = 1
  hpos : ∀ i : Fin (n + 1), (0 : ℝ) < ⟪h, (P i : E3)⟫
  u : E3
  v : E3
  lifted : PlanarLiftedTurnSpan (fun i : Fin (n + 1) => gproj h (P i)) h u v

/-! ## The explicit orthonormal frame in `h^⊥`.

Given a unit `h`, we build an orthonormal pair `(u, v) ⊥ h`.  Uniform
construction valid for **every** unit `h`: pick a coordinate axis `k` with
`cross h k ≠ 0` (one of the three coordinate axes always works, since the three
squared norms `‖cross h k_j‖² = 1 - (h_j)²` sum to `2 > 0`), set
`u := ‖cross h k‖⁻¹ • cross h k` and `v := cross h u`.  Then `(u, v)` is
orthonormal and perpendicular to `h`, with the orientation `cross h u = v`.
-/

/-- From a nonzero seed `s ⊥ h` of unit-normalizable length, the pair
`(u, v) = (‖s‖⁻¹ • s, cross h u)` is orthonormal and perpendicular to `h`.  This
is the algebraic core of the frame construction. -/
theorem orthoFrame_of_seed {h s : E3} (hh : ‖h‖ = 1)
    (hperp : (⟪h, s⟫ : ℝ) = 0) (hs : s ≠ 0) :
    ∃ u v : E3, (⟪h, u⟫ : ℝ) = 0 ∧ (⟪h, v⟫ : ℝ) = 0 ∧
      (⟪u, u⟫ : ℝ) = 1 ∧ (⟪v, v⟫ : ℝ) = 1 ∧ (⟪u, v⟫ : ℝ) = 0 := by
  set u : E3 := ‖s‖⁻¹ • s with hu
  have hsn : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  have hsn2 : (‖s‖ : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ hsn
  -- ⟪h, u⟫ = 0
  have hhu : (⟪h, u⟫ : ℝ) = 0 := by
    rw [hu, real_inner_smul_right, hperp, mul_zero]
  -- ⟪u, u⟫ = 1
  have huu : (⟪u, u⟫ : ℝ) = 1 := by
    rw [hu, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  set v : E3 := cross h u with hv
  -- ⟪h, v⟫ = 0
  have hhv : (⟪h, v⟫ : ℝ) = 0 := by
    rw [hv, real_inner_comm]; exact inner_cross_left h u
  -- ⟪u, v⟫ = 0
  have huv : (⟪u, v⟫ : ℝ) = 0 := by
    rw [hv, real_inner_comm]; exact inner_cross_right h u
  -- ⟪v, v⟫ = ‖v‖² = ‖h‖²‖u‖² − ⟪h,u⟫² = 1·1 − 0 = 1
  have hvv : (⟪v, v⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hv, norm_sq_cross, hh, hhu,
      ← real_inner_self_eq_norm_sq, huu]
    ring
  exact ⟨u, v, hhu, hhv, huu, hvv, huv⟩

/-- For any unit vector `h : E3` there is an orthonormal pair `(u, v)` with both
perpendicular to `h`. -/
theorem exists_orthoFrame {h : E3} (hh : ‖h‖ = 1) :
    ∃ u v : E3, (⟪h, u⟫ : ℝ) = 0 ∧ (⟪h, v⟫ : ℝ) = 0 ∧
      (⟪u, u⟫ : ℝ) = 1 ∧ (⟪v, v⟫ : ℝ) = 1 ∧ (⟪u, v⟫ : ℝ) = 0 := by
  -- The three coordinate axes.
  set k0 : E3 := !₂[(1 : ℝ), 0, 0] with hk0
  set k1 : E3 := !₂[(0 : ℝ), 1, 0] with hk1
  set k2 : E3 := !₂[(0 : ℝ), 0, 1] with hk2
  -- Each cross product is perpendicular to `h`.
  have hperp : ∀ k : E3, (⟪h, cross h k⟫ : ℝ) = 0 := by
    intro k; rw [real_inner_comm]; exact inner_cross_left h k
  -- At least one of `cross h k0/k1/k2` is nonzero: else all coordinates of `h`
  -- vanish, contradicting `‖h‖ = 1`.
  have hsome : cross h k0 ≠ 0 ∨ cross h k1 ≠ 0 ∨ cross h k2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h0, h1, h2⟩ := hcon
    -- From `cross h k0 = 0` etc. extract that every coordinate of `h` is `0`.
    -- `cross h k0 = (0, h2, -h1)`, `cross h k1 = (-h2, 0, h0)`.
    have hh2 : h 2 = 0 := by
      have c0 := congrArg (fun w : E3 => w 1) h0
      simp only [hk0, cross_apply_one] at c0
      simpa using c0
    have hh1 : h 1 = 0 := by
      have c0 := congrArg (fun w : E3 => w 2) h0
      simp only [hk0, cross_apply_two] at c0
      have : -(h 1) = 0 := by simpa using c0
      linarith
    have hh0 : h 0 = 0 := by
      have c1 := congrArg (fun w : E3 => w 2) h1
      simp only [hk1, cross_apply_two] at c1
      simpa using c1
    have : ‖h‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_eq_coord, hh0, hh1, hh2]; ring
    rw [hh] at this; norm_num at this
  -- Build the frame from whichever seed is nonzero.
  rcases hsome with hk | hk | hk
  · exact orthoFrame_of_seed hh (hperp k0) hk
  · exact orthoFrame_of_seed hh (hperp k1) hk
  · exact orthoFrame_of_seed hh (hperp k2) hk

/-! ## Gnomonic image facts for a strict arm. -/

/-- The gnomonic images of a strict arm lie in the affine plane `⟨h, ·⟩ = 1`,
where `h` is the open-hemisphere normal. -/
theorem gnomonic_image_in_plane {n : ℕ} {A : Fin (n + 1) → S2}
    {h : E3} (hhem : ∀ i : Fin (n + 1), (0 : ℝ) < ⟪h, (A i : E3)⟫)
    (i : Fin (n + 1)) :
    (⟪h, gproj h (A i)⟫ : ℝ) = 1 :=
  inner_gproj (ne_of_gt (hhem i))

/-- A strict arm has nondegenerate gnomonic edges: `gproj h (A i) ≠ gproj h (A (i+1))`. -/
theorem gnomonic_image_edge_ne {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A)
    {h : E3} (hhem : ∀ i : Fin (n + 1), (0 : ℝ) < ⟪h, (A i : E3)⟫)
    (i : Fin (n + 1)) :
    gproj h (A i) ≠ gproj h (A (i + 1)) :=
  ProofsInTheBook.ZinanFFCT92.gproj_ne_of_short (hhem i) (hhem (i + 1))
    (hA.closed_convex.edge_short i)

/-! ## The isolated single-wind residue (the *real content*).

The hemisphere/frame layer is fully discharged above.  What remains is the
purely-planar analytic statement: a strictly convex *open* polygonal chain in a
common affine plane (every directed edge weakly supports all vertices, every
non-incident vertex strictly so, every edge nondegenerate), equipped with an
orthonormal frame `(u, v) ⊥ h`, carries a *lifted* edge-direction certificate —
a real turn function `θ` with strictly positive turns below `π` and total
turning *below `2π`* (single wind).

This is precisely `FFCT94.PlanarLiftedTurnSpan`.  The decisive piece is
`one_wind : θ N - θ 0 < 2π`: the total turning of an open strictly-convex planar
chain in convex position is strictly below one full turn.  We isolate it here as
one named planar `Prop`, in the style of `ZinanFFCT92.PlanarClosedWeakStrictNoRepeat`.

Non-vacuity: `FFCT94.witChain_certificate` exhibits an explicit strictly convex
planar chain that *does* carry such a lifted certificate (with total turning
`π/4 < 2π`), so this residue is satisfiable — it is not a vacuous hypothesis. -/

/-- The isolated planar single-wind residue.  For every strictly convex open
planar chain `Q : Fin (n+1) → E3` in the plane `⟨h, ·⟩ = 1` with an orthonormal
frame `(u, v) ⊥ h`, all directed edges weakly supporting all vertices, all
non-incident vertices strictly supported, and all edges nondegenerate, there is a
`PlanarLiftedTurnSpan Q h u v`. -/
def StrictPlanarChainLiftedTurnSpanExists : Prop :=
  ∀ {n : ℕ} (Q : Fin (n + 1) → E3) (h u v : E3),
    (⟪h, u⟫ : ℝ) = 0 → (⟪h, v⟫ : ℝ) = 0 →
    (⟪u, u⟫ : ℝ) = 1 → (⟪v, v⟫ : ℝ) = 1 → (⟪u, v⟫ : ℝ) = 0 →
    (∀ i : Fin (n + 1), (⟪h, Q i⟫ : ℝ) = 1) →
    (∀ i j : Fin (n + 1), 0 ≤ det3 (Q i) (Q (i + 1)) (Q j)) →
    (∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 → 0 < det3 (Q i) (Q (i + 1)) (Q j)) →
    (∀ i : Fin (n + 1), Q i ≠ Q (i + 1)) →
    Nonempty (PlanarLiftedTurnSpan Q h u v)

/-! ## Brick D-strict : the gnomonic single-wind certificate from a strict arm. -/

/-- **Brick D-strict.**  Modulo the isolated planar single-wind residue
`StrictPlanarChainLiftedTurnSpanExists`, every strictly convex spherical arm
admits a `GnomonicSingleWind` certificate.

Construction.  Take the open-hemisphere normal `h` (`‖h‖ = 1`, `0 < ⟪h, A i⟫`);
build an orthonormal frame `(u, v) ⊥ h` (`exists_orthoFrame`); the gnomonic
images `Q = gproj h ∘ A` lie in `⟨h, ·⟩ = 1` (`gnomonic_image_in_plane`), have
nondegenerate edges (`gnomonic_image_edge_ne`), and inherit the strict / weak
edge supports from the spherical strict supports through the gnomonic sign
correspondence (`sOrient_pos_iff_planar_pos` and its weak analogue).  Feeding
these planar facts to the residue produces the `PlanarLiftedTurnSpan`. -/
theorem strictConvexSphArm_gnomonicSingleWind
    (hres : StrictPlanarChainLiftedTurnSpanExists)
    {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A) :
    Nonempty (GnomonicSingleWind A) := by
  -- The open-hemisphere normal.
  obtain ⟨h, hnorm, hhem⟩ := hA.closed_convex.open_hemisphere
  -- The orthonormal frame in `h^⊥`.
  obtain ⟨u, v, hhu, hhv, huu, hvv, huv⟩ := exists_orthoFrame hnorm
  -- The gnomonic image.
  set Q : Fin (n + 1) → E3 := fun i => gproj h (A i) with hQ
  -- in-plane
  have hplane : ∀ i : Fin (n + 1), (⟪h, Q i⟫ : ℝ) = 1 :=
    fun i => gnomonic_image_in_plane hhem i
  -- weak edge supports (nonnegative)
  have hsupp : ∀ i j : Fin (n + 1), 0 ≤ det3 (Q i) (Q (i + 1)) (Q j) := by
    intro i j
    have hs : 0 ≤ sOrient (A i) (A (i + 1)) (A j) := hA.closed_convex.edge_support i j
    -- transport: sOrient = (pos scalar) * det3 (gproj …)
    have hc := gnomonic_sign_correspondence h (A i) (A (i + 1)) (A j)
      (ne_of_gt (hhem i)) (ne_of_gt (hhem (i + 1))) (ne_of_gt (hhem j))
    have hsc : (0 : ℝ) <
        (⟪h, (A i : E3)⟫ : ℝ) * (⟪h, (A (i + 1) : E3)⟫ : ℝ) * (⟪h, (A j : E3)⟫ : ℝ) :=
      mul_pos (mul_pos (hhem i) (hhem (i + 1))) (hhem j)
    rw [hc] at hs
    change 0 ≤ det3 (gproj h (A i)) (gproj h (A (i + 1))) (gproj h (A j))
    by_contra hlt; push Not at hlt
    nlinarith [hs, hsc, hlt]
  -- strict non-incident supports
  have hstrict : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 < det3 (Q i) (Q (i + 1)) (Q j) := by
    intro i j hj1 hj2
    have hs := hA.closed_convex.strict_nonincident i j hj1 hj2
    change 0 < det3 (gproj h (A i)) (gproj h (A (i + 1))) (gproj h (A j))
    exact (sOrient_pos_iff_planar_pos h (A i) (A (i + 1)) (A j)
      (hhem i) (hhem (i + 1)) (hhem j)).mp hs
  -- nondegenerate edges
  have hedge : ∀ i : Fin (n + 1), Q i ≠ Q (i + 1) :=
    fun i => gnomonic_image_edge_ne hA hhem i
  -- Apply the residue.
  obtain ⟨lifted⟩ := hres Q h u v hhu hhv huu hvv huv hplane hsupp hstrict hedge
  exact ⟨{ h := h, hnorm := hnorm, hpos := hhem, u := u, v := v, lifted := lifted }⟩

/-! ## Guards. -/

#check @GnomonicSingleWind
#check @orthoFrame_of_seed
#check @exists_orthoFrame
#check @gnomonic_image_in_plane
#check @gnomonic_image_edge_ne
#check @StrictPlanarChainLiftedTurnSpanExists
#check @strictConvexSphArm_gnomonicSingleWind

#print axioms exists_orthoFrame
#print axioms gnomonic_image_in_plane
#print axioms gnomonic_image_edge_ne
#print axioms strictConvexSphArm_gnomonicSingleWind

end ProofsInTheBook.ZinanFFCT95
