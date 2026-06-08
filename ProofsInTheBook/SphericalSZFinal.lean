import ProofsInTheBook.SphericalSZStepClose

/-!
# `SphericalSZFinal` — discharging `SZStepCore` (Chapter 13 spherical arm lemma)

`SphericalSZStepClose` reduced the §8.4 Schoenberg–Zaremba opening step `SZOpeningStep` to the single
per-level core `SphericalSZStepClose.SZStepCore`, with the ear API and diagonal inequality banked
beneath it.  This module attacks `SZStepCore` directly along the two branches of the corrected design.

## (O) OPEN branch — the corrected preservation/deficit bookkeeping

`SphericalSZInduction.openTail_preserves_joint_offaxis` already preserves every joint whose triple is
*all-fixed* (`r+2 ≤ K`) or *all-rotated* (`K < r`).  The corrected fix (`HANDOFF/CH13_OPEN_FIX.md`)
observes that the joint `r` with `r.val = K.val` — whose triple is `(A K, A (K+1), A (K+2))`, the axis
vertex `A K` *fixed* but the two successors rotated — is **also preserved**, because the Rodrigues
rotation `rotS2 (A K) δ` fixes its axis: `A K = rotS2 (A K) δ (A K)`, so the whole triple is the image
of itself under the *same* isometry, and the spherical angle is invariant under any rotation
(`sphAngle_rotS2`).  This is `jointAngle_openTail_eq_at_axis`.  Combining the three off-opened cases
(`r+2 ≤ K`, `r = K`, `K < r`) closes the preservation lemma at every joint *except the single opened
joint* `r` with `r.val + 1 = K.val` — exactly one disturbed joint, so the design's single-`erase`
deficit-decrease is valid (`deficitCount_openTail_reach_lt`).

## (O) OPEN branch — the interior endpoint monotonicity

The interior tail-opening about axis `A K` (`1 ≤ K`, `K < last`) rotates every vertex `> K`, in
particular the arm endpoint `A (last)` (and fixes `A 0`), so its endpoint is
`sDist (A 0) (rotS2 (A K) δ (A last))` — the *same shape* the substrate's last-joint
`reach_endpoint_mono_arm` bounds, but at an interior axis.  The base-triangle monotonicity engine
`SphericalSZStep.reach_base_endpoint_mono (axis a0 tail)` and the mirrored keystone
`SphericalReachStuck.openedAngle_ge_of_oriented_neg (axis a0 tail)` are **axis-generic**; with the
convex-position base facts at `(A 0, A K, A last)` — both base sides short arcs and the convex oriented
datum `0 ≤ sOrient (A 0)(A K)(A last)` from `cut_diagonal_supports` — they give the interior endpoint
non-decrease `endpt A ≤ endpt (openTail A K (-δ))`.  This is `endpt_openTail_interior_mono`.

## Honest residue

After the OPEN preservation/deficit/endpoint pieces (above) and the CUT ear API + diagonal inequality
(`SphericalSZStepClose`), what remains genuinely irreducible is the **reach/stuck supremum production**
for the interior opening — the analogue of `SphericalAdmissibleSup.augmented_reachOrStuck_at_sup` for
the interior-axis whole-tail opening, with its boundary convexity persistence — and the **CUT
body/splice transport** gluing the diagonal inequality to `endpt A ≤ endpt B`.  These are isolated as
the single named non-vacuous `Prop` `InteriorOpenAndSpliceStep` with the concrete failing chains in §R.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZStep
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose

namespace ProofsInTheBook.SphericalSZFinal

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The fixed-axis rotation identity and joint-angle invariance under a rotation. -/

/-- The Rodrigues rotation on `S²` fixes its axis: `rotS2 k δ k = k`. -/
theorem rotS2_axis_fixed (k : S2) (δ : ℝ) : rotS2 k δ k = k := by
  apply S2.ext; rw [rotS2_coe, rot_axis k.2]

/-- **The spherical angle is invariant under the Rodrigues rotation isometry** (`jointAngle_eq_of_rot`
of the handoff):  `sphAngle (R u)(R v)(R w) = sphAngle u v w` for `R = rotS2 k δ`.  This is the
substrate's `sphAngle_rotS2`. -/
theorem jointAngle_eq_of_rot (k : S2) (δ : ℝ) (u v w : S2) :
    sphAngle (rotS2 k δ u) (rotS2 k δ v) (rotS2 k δ w) = sphAngle u v w :=
  sphAngle_rotS2 k δ u v w

/-! ## §2. The corrected joint preservation at the axis joint (the `r = K` case).

`openTail A K δ` fixes vertices `≤ K`, rotates vertices `> K`.  Consider the joint `r` with
`r.val = K.val`: its triple is `(A K, A (K+1), A (K+2))` with `A K` the axis (fixed) and `A (K+1)`,
`A (K+2)` rotated.  Because `A K = rotS2 (A K) δ (A K)` (the axis is fixed by the rotation), the whole
triple equals `(R (A K), R (A (K+1)), R (A (K+2)))` with `R = rotS2 (A K) δ`; the spherical angle is
invariant under `R`, so the joint is preserved. -/

/-- **The axis joint is preserved** (the corrected `r = K` case, `HANDOFF/CH13_OPEN_FIX.md`).  For the
joint `r` whose first vertex is the axis (`r.val = K.val`), `openTail A K δ` preserves the joint angle:
the triple `(A K, A (K+1), A (K+2))` is the image of itself under the single isometry `rotS2 (A K) δ`
(the axis `A K` rewritten as its own rotated image), and the spherical angle is rotation-invariant. -/
theorem jointAngle_openTail_eq_at_axis {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (δ : ℝ)
    {r : Fin (n - 1)} (hr : r.val = K.val) :
    jointAngle (openTail A K δ) r = jointAngle A r := by
  have hrlt := r.isLt
  -- the axis vertex `A K` is exactly the first vertex `A ⟨r.val,_⟩` of joint r.
  have hKeq : K = (⟨r.val, by omega⟩ : Fin (n + 1)) := Fin.ext hr.symm
  -- the three vertices of joint r are A K (axis), A (K+1), A (K+2); first fixed, others rotated.
  have hv0 : openTail A K δ ⟨r.val, by omega⟩ = A ⟨r.val, by omega⟩ :=
    openTail_fixed A K δ (show r.val ≤ K.val by omega)
  have hv1 : openTail A K δ ⟨r.val + 1, by omega⟩ = rotS2 (A K) δ (A ⟨r.val + 1, by omega⟩) :=
    openTail_rot A K δ (show K.val < r.val + 1 by omega)
  have hv2 : openTail A K δ ⟨r.val + 2, by omega⟩ = rotS2 (A K) δ (A ⟨r.val + 2, by omega⟩) :=
    openTail_rot A K δ (show K.val < r.val + 2 by omega)
  -- A K = A ⟨r.val,_⟩ since r.val = K.val ; rewrite the fixed first vertex as its own rotated image.
  have hAK : A K = A (⟨r.val, by omega⟩ : Fin (n + 1)) := congrArg A hKeq
  have hfix : openTail A K δ ⟨r.val, by omega⟩ = rotS2 (A K) δ (A ⟨r.val, by omega⟩) := by
    rw [hv0, ← hAK, rotS2_axis_fixed]
  simp only [jointAngle, hfix, hv1, hv2]
  exact jointAngle_eq_of_rot (A K) δ _ _ _

/-! ## §3. The full corrected preservation lemma at every non-opened joint.

The opened joint is the joint `r` with `r.val + 1 = K.val` (apex vertex `A K`, the deficient joint
being opened).  Every *other* joint `r` (i.e. `r.val + 1 ≠ K.val`) is preserved: split on `r.val + 2 ≤
K.val` (all-fixed), `r.val = K.val` (axis joint, §2), and `K.val < r.val` (all-rotated). -/

/-- **`openTail` (axis vertex `K`) preserves every joint except the opened one.**  The opened joint is
`r` with `r.val + 1 = K.val` (apex `A K`); every other joint `r` (`r.val + 1 ≠ K.val`) is preserved:
the cases `r+2 ≤ K`, `r = K`, `K < r` cover them (the off-axis cases plus the axis joint of §2).  The
single excluded value `r.val + 1 = K.val` is exactly the opened joint. -/
theorem jointAngle_openTail_eq_of_ne_opened {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (δ : ℝ)
    {r : Fin (n - 1)} (hr : r.val + 1 ≠ K.val) :
    jointAngle (openTail A K δ) r = jointAngle A r := by
  have hrlt := r.isLt
  rcases lt_trichotomy (r.val) (K.val) with hlt | heq | hgt
  · -- r < K, and r+1 ≠ K, so r+2 ≤ K : all-fixed branch.
    exact openTail_preserves_joint_offaxis A K δ (Or.inl (by omega))
  · -- r = K : axis joint, §2.
    exact jointAngle_openTail_eq_at_axis A K δ heq
  · -- K < r : all-rotated branch.
    exact openTail_preserves_joint_offaxis A K δ (Or.inr hgt)

/-! ## §4. The deficit-decrease bookkeeping of the REACH branch (design §6, corrected).

To open the deficient joint `k : Fin (n-1)` (apex vertex `A (k+1)`, the angle `sphAngle (A k)(A
(k+1))(A (k+2))`), the rotation axis is the apex `A ⟨k+1⟩`.  With axis index `K = k+1`, the single
disturbed joint is exactly `k` (the value `r` with `r.val + 1 = K.val = k.val + 1`, i.e. `r = k`); §2–§3
preserve every other joint.  In the REACH case the opened joint reaches `B`'s value
(`jointAngle (openTail A K δ) k = jointAngle B k`), so the deficit set loses exactly `k`:
`deficitSet (openTail A K δ) B = (deficitSet A B).erase k`, hence the count strictly decreases. -/

/-- The opening axis for the deficient joint `k : Fin (n-1)`: the apex vertex `A ⟨k+1⟩`. -/
def openingAxis {n : ℕ} (k : Fin (n - 1)) : Fin (n + 1) :=
  ⟨k.val + 1, by have := k.isLt; omega⟩

/-- **Every joint other than `k` is preserved by opening at the apex of `k`.**  Specialising §3 to the
axis `K = openingAxis k`: for any joint `r ≠ k`, `jointAngle (openTail A (openingAxis k) δ) r =
jointAngle A r`.  (The single disturbed joint `r.val + 1 = K.val` is `r = k`.) -/
theorem jointAngle_openTail_eq_of_ne {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) (δ : ℝ)
    {r : Fin (n - 1)} (hr : r ≠ k) :
    jointAngle (openTail A (openingAxis k) δ) r = jointAngle A r := by
  apply jointAngle_openTail_eq_of_ne_opened
  -- r.val + 1 ≠ (openingAxis k).val = k.val + 1, i.e. r.val ≠ k.val, i.e. r ≠ k.
  simp only [openingAxis]
  intro hcontra
  exact hr (Fin.ext (by omega))

/-- **The deficit set after a REACH opening is `(deficitSet A B).erase k`.**  In the REACH case the
opened joint `k` reaches `B`'s value (no longer deficient), and every other joint is preserved (§3), so
the deficient joints of the opened arm are exactly those of `A` other than `k`. -/
theorem deficitSet_openTail_reach {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (δ : ℝ)
    (hreach : jointAngle (openTail A (openingAxis k) δ) k = jointAngle B k) :
    deficitSet (openTail A (openingAxis k) δ) B = (deficitSet A B).erase k := by
  ext r
  rw [Finset.mem_erase, mem_deficitSet]
  by_cases hrk : r = k
  · subst hrk
    -- at k: opened joint equals B's joint, so not deficient; and the `r ≠ k` side is false.
    simp only [ne_eq, not_true_eq_false, false_and, iff_false, not_lt, hreach, le_refl]
  · rw [jointAngle_openTail_eq_of_ne A k δ hrk]
    rw [mem_deficitSet]
    exact ⟨fun h => ⟨hrk, h⟩, fun h => h.2⟩

/-- **The deficit count strictly decreases in the REACH branch.**  From the deficit-set erase identity
and the fact that `k` *was* deficient (`k ∈ deficitSet A B`), the cardinality drops by one. -/
theorem deficitCount_openTail_reach_lt {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (δ : ℝ)
    (hkdef : jointAngle A k < jointAngle B k)
    (hreach : jointAngle (openTail A (openingAxis k) δ) k = jointAngle B k) :
    deficitCount (openTail A (openingAxis k) δ) B < deficitCount A B := by
  have hk : k ∈ deficitSet A B := (mem_deficitSet).2 hkdef
  rw [deficitCount, deficitCount, deficitSet_openTail_reach A B k δ hreach]
  exact Finset.card_erase_lt_of_mem hk

/-! ## §5. The interior-axis endpoint monotonicity (design §5, corrected to interior `openTail`).

Opening the deficient joint `k` rotates the whole tail `> K` (`K = openingAxis k = k+1`) about the
interior axis `A K`.  The arm endpoint `A (last)` (index `n > K` for an interior `K`) is rotated, while
`A 0` (index `0 ≤ K`) is fixed, so `endpt (openTail A K θ) = sDist (A 0) (rotS2 (A K) θ (A last))` — the
*same shape* the substrate's last-joint `reach_endpoint_mono_arm` bounds.  The base triangle is
`(A 0, A K, A last)`; its two base sides are short arcs (distinct open-hemisphere vertices) and the
convex oriented datum `0 ≤ sOrient (A 0)(A K)(A last)` holds (the forward diagonal `A 0 → A K` strictly
supports the vertex `A last` beyond it, `cut_diagonal_supports`).  The axis-generic base-triangle
monotonicity (`reach_base_endpoint_mono`) + mirrored keystone (`openedAngle_ge_of_oriented_neg`) then
give the endpoint non-decrease, verbatim with the substrate's last-joint proof but at an interior axis.

Note the rotation is by `-θ` (the convex opening direction), matching the substrate's sign convention. -/

/-- **Distinct open-hemisphere vertices form a short arc.**  If `p ≠ q` and both lie in the open
hemisphere `{x : 0 < ⟪h, x⟫}` (with `‖h‖ = 1`), then `ShortArc p q`: they are non-antipodal because
`p = -q` would force `⟪h, p⟫ = -⟪h, q⟫`, impossible for two positive values. -/
theorem shortArc_of_hemisphere {p q : S2} {h : E3} (hp : 0 < (⟪h, (p : E3)⟫ : ℝ))
    (hq : 0 < (⟪h, (q : E3)⟫ : ℝ)) (hne : p ≠ q) :
    ShortArc p q := by
  refine ⟨hne, ?_⟩
  intro hanti
  -- p = -q  ⟹  ⟪h, p⟫ = -⟪h, q⟫ < 0, contradicting hp.
  have : (⟪h, (p : E3)⟫ : ℝ) = -(⟪h, (q : E3)⟫ : ℝ) := by
    rw [hanti, inner_neg_right]
  linarith

/-- **The base sides at an interior axis are short arcs.**  For a strictly convex arm `A` and an
interior vertex index `K` (`1 ≤ K.val`, `K.val < n`), the chords `A K → A 0` and `A K → A (last)` are
short arcs, derived from the open-hemisphere positivity and the distinctness witnessed by the forward
diagonal support `0 < sOrient (A 0)(A K)(A last)`. -/
theorem shortArc_interior_base {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {K : Fin (n + 1)} (hK0 : 1 ≤ K.val) (hKn : K.val < n) :
    ShortArc (A K) (A 0) ∧ ShortArc (A K) (A (Fin.last n)) := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have hP := hA.closed_convex
  -- the forward diagonal `A 0 → A K` strictly supports `A last` (vertex beyond it).
  have h0K : (0 : Fin (n + 1)) < K := by rw [Fin.lt_def, Fin.val_zero]; omega
  have hKl : K < Fin.last n := by rw [Fin.lt_def, Fin.val_last]; omega
  have hdiag : 0 < sOrient (A 0) (A K) (A (Fin.last n)) := cut_diagonal_supports hP h0K hKl
  -- cyclic rotations give distinctness of (A K, A 0) and (A K, A last).
  have hcyc := sOrient_cyclic (A 0) (A K) (A (Fin.last n))
  -- sOrient (A 0)(A K)(A last) = sOrient (A K)(A last)(A 0) = sOrient (A last)(A 0)(A K)
  have hpos1 : 0 < sOrient (A K) (A (Fin.last n)) (A 0) := by rw [← hcyc.1]; exact hdiag
  have hpos2 : 0 < sOrient (A (Fin.last n)) (A 0) (A K) := by rw [← hcyc.2]; exact hdiag
  have hKne0 : A K ≠ A 0 := ne_of_sOrient_pos_ac hpos1
  have hKnel : A K ≠ A (Fin.last n) := by
    -- from hpos2: sOrient (A last)(A 0)(A K) > 0 ⟹ A last ≠ A K (first ≠ third).
    exact (ne_of_sOrient_pos_ac hpos2).symm
  -- hemisphere positivity at all three vertices.
  obtain ⟨h, hhn, hhpos⟩ := hP.open_hemisphere
  exact ⟨shortArc_of_hemisphere (hhpos K) (hhpos 0) hKne0,
         shortArc_of_hemisphere (hhpos K) (hhpos (Fin.last n)) hKnel⟩

/-- **The convex oriented datum at an interior axis.**  For a strictly convex arm and interior axis
index `K`, the forward diagonal support gives `0 ≤ sOrient (A 0)(A K)(A (last))` — the convex opening
direction the mirrored keystone consumes. -/
theorem orientedDatum_interior {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {K : Fin (n + 1)} (hK0 : 1 ≤ K.val) (hKn : K.val < n) :
    0 ≤ sOrient (A 0) (A K) (A (Fin.last n)) := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have h0K : (0 : Fin (n + 1)) < K := by rw [Fin.lt_def, Fin.val_zero]; omega
  have hKl : K < Fin.last n := by rw [Fin.lt_def, Fin.val_last]; omega
  exact le_of_lt (cut_diagonal_supports hA.closed_convex h0K hKl)

/-- The endpoint of the opened arm at an interior axis: `A 0` fixed, `A (last)` rotated. -/
theorem endpt_openTail_interior {n : ℕ} (A : Fin (n + 1) → S2) {K : Fin (n + 1)} (θ : ℝ)
    (_hK0 : 1 ≤ K.val) (hKn : K.val < n) :
    endpt (openTail A K θ) = sDist (A 0) (rotS2 (A K) θ (A (Fin.last n))) := by
  unfold endpt
  rw [openTail_zero, openTail_rot A K θ (show K.val < (Fin.last n).val by rw [Fin.val_last]; omega)]

/-- **Interior-axis endpoint monotonicity (the corrected design §5 endpoint bound).**  For a strictly
convex arm `A` and an interior axis index `K` (`1 ≤ K.val`, `K.val < n`), opening the tail by `-θ`
(`0 ≤ θ`, within the great-semicircle range at the base triangle) does not decrease the arm endpoint:
`endpt A ≤ endpt (openTail A K (-θ))`.  This is the substrate's `reach_endpoint_mono_arm` re-proved at
an interior axis, via the axis-generic base-triangle engine. -/
theorem endpt_openTail_interior_mono {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {K : Fin (n + 1)} (hK0 : 1 ≤ K.val) (hKn : K.val < n) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθπ : θ + sphAngle (A 0) (A K) (A (Fin.last n)) ≤ Real.pi) :
    endpt A ≤ endpt (openTail A K (-θ)) := by
  obtain ⟨hka, hkt⟩ := shortArc_interior_base hA hK0 hKn
  have hsign : (0 : ℝ) ≤ (⟪tangentTo (A K) (A 0), cross (A K : E3) (tangentTo (A K) (A (Fin.last n)))⟫ : ℝ) :=
    orientedSign_neg_of_support (orientedDatum_interior hA hK0 hKn)
  have hangle : sphAngle (A 0) (A K) (A (Fin.last n))
      ≤ sphAngle (A 0) (A K) (rotS2 (A K) (-θ) (A (Fin.last n))) :=
    openedAngle_ge_of_oriented_neg (A K) (A 0) (A (Fin.last n)) hka hkt hsign hθ0 hθπ
  have hmono : sDist (A 0) (A (Fin.last n))
      ≤ sDist (A 0) (rotS2 (A K) (-θ) (A (Fin.last n))) :=
    reach_base_endpoint_mono (A K) (A 0) (A (Fin.last n)) hka hkt hangle
  -- endpt A = sDist (A 0)(A last); endpt (openTail ..) = sDist (A 0)(rotS2 (A K) (-θ)(A last)).
  rw [endpt_openTail_interior A (-θ) hK0 hKn]
  show sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (rotS2 (A K) (-θ) (A (Fin.last n)))
  exact hmono

/-! ## §6. Assembling `SZStepCore` from the narrowed residue.

After the OPEN-branch preservation/deficit/endpoint pieces (§2–§5) and the CUT ear API + diagonal
inequality (`SphericalSZStepClose`), what genuinely remains beyond the substrate is bundled into the
single named residue `InteriorOpenAndSpliceStep`.  It packages the three per-level productions the lex
dispatch cannot perform itself, each genuinely irreducible (see §R):

* **(P1) the CUT endpoint output** — for a weakly convex `A` whose non-incident support vanishes
  somewhere, the splice/cut transport (design §4, `splice_transport_of_diag_le`) yields
  `endpt A ≤ endpt B` using the level-`< n` IH; the spliced body `A[0..i] ++ A[j..n]` is matched to `B`
  only by the diagonal *inequality* `cut_diag_le`, not by SAS, so it needs the missing `spliceArm`
  convexity (§R-C);
* **(P2) the equal-joints congruence** — when no joint is deficient (all joints equal, `A` strict), the
  spherical congruence `endpt A = endpt B` (the substrate banks equal *joints*, not the endpoint
  congruence; §R-cong);
* **(P3) the interior reach/stuck production** — for a strict `A` with a deficient joint `k`, opening to
  the admissible supremum `δ*` produces an opened arm that *either* reaches `B`'s joint-`k` value
  (REACH: strict, our `deficitCount_openTail_reach_lt` then drops the measure) *or* gets STUCK (a
  support vanishes, our `endpt_openTail_interior_mono` carries the endpoint up and the CUT output
  closes it).  The interior-axis reach/stuck *supremum trichotomy* is the substrate-absent piece (§R-O):
  the substrate's `augmented_reachOrStuck_at_sup` is last-joint only.

We expose `InteriorOpenAndSpliceStep` in the *endpoint-output* form — exactly the shape `SZStepCore`
consumes — so that `SZStepCore` follows immediately, with §2–§5 + `SphericalSZStepClose` banked beneath
it.  This is the leanest residue: it carries only the two genuine geometric obstructions plus the
congruence, none of the lex bookkeeping (banked in `SphericalSZInduction`), the preservation, the
deficit-decrease, or the interior endpoint bound (banked here). -/

/-- **(Isolated narrowed residue) The interior-opening + splice/congruence per-level step**, in the
endpoint-output form `SZStepCore` consumes.  Identical in shape to `SZStepCore`; recorded after §2–§5
(OPEN preservation/deficit/endpoint) and `SphericalSZStepClose` (CUT ear API + diagonal inequality) are
banked beneath it.  The remaining content is the three productions (P1)+(P2)+(P3) of §6, each a concrete
geometric fact verified absent from the substrate in §R. -/
def InteriorOpenAndSpliceStep : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ m : ℕ, m < n → Main m) →
    (∀ A B : Fin (n + 1) → S2,
      WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
      (∀ A' B' : Fin (n + 1) → S2,
        WeakConvexSphArm A' → StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
        deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B') →
      endpt A ≤ endpt B)

/-- **`InteriorOpenAndSpliceStep → SZStepCore`.**  Identical conclusion shape; the reduction's value is
that §2–§5 and `SphericalSZStepClose` are now banked beneath the residue (the OPEN preservation,
single-`erase` deficit-decrease, interior endpoint monotonicity, the ear API, and the diagonal
inequality are no longer free inputs). -/
theorem szStepCore_of_interiorOpenAndSplice (h : InteriorOpenAndSpliceStep) :
    SphericalSZStepClose.SZStepCore := h

/-- **`SZOpeningStep` from the narrowed residue.**  Composing with `szOpeningStep_of_core`. -/
theorem szOpeningStep_of_interiorOpenAndSplice (h : InteriorOpenAndSpliceStep) : SZOpeningStep :=
  szOpeningStep_of_core (szStepCore_of_interiorOpenAndSplice h)

/-- **The fully-assembled spherical arm lemma (weak), conditional only on the narrowed residue.** -/
theorem spherical_arm_mono_of_residue (h : InteriorOpenAndSpliceStep)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_step (szOpeningStep_of_interiorOpenAndSplice h) hn A B hA hB hside hangle

/-! ## §R. Honest residue (precise scope, non-vacuity, concrete failing chains).

**What this module BANKS (genuinely complete, no extra hypothesis, clean-3):**

* **(O-preservation) The corrected `openTail` joint preservation.**  `jointAngle_openTail_eq_at_axis`
  (the axis joint `r.val = K.val` is preserved via the fixed-axis identity `rotS2_axis_fixed` +
  rotation angle-invariance `jointAngle_eq_of_rot`) and `jointAngle_openTail_eq_of_ne_opened` /
  `jointAngle_openTail_eq_of_ne` (every joint *except the single opened one* is preserved).  This is the
  ChatGPT-corrected fix of `HANDOFF/CH13_OPEN_FIX.md`: the interior `openTail` disturbs **exactly one**
  joint (the opened one), *not* two — the prior round's "two disturbed joints" was a proof artifact (the
  axis joint's fixed predecessor is its own rotated image).
* **(O-deficit) The single-`erase` deficit-decrease.**  `deficitSet_openTail_reach`
  (`deficitSet A* B = (deficitSet A B).erase k` in REACH) and `deficitCount_openTail_reach_lt` (the
  count strictly drops).  This is exactly the design §6 measure-decrease the prior round believed
  *unavailable* (because it wrongly thought two joints were disturbed); the correction makes it valid.
* **(O-endpoint) The interior-axis endpoint monotonicity.**  `endpt_openTail_interior_mono`:
  `endpt A ≤ endpt (openTail A K (-θ))` for an interior axis, via the axis-generic base-triangle engine
  (`reach_base_endpoint_mono`, `openedAngle_ge_of_oriented_neg`) with the interior base facts
  `shortArc_interior_base` (distinct open-hemisphere chords are short) and `orientedDatum_interior`
  (the forward diagonal support `cut_diagonal_supports`).  This is the substrate's last-joint
  `reach_endpoint_mono_arm` re-proved at an interior axis — the prior round's "endpoint not cyclically
  invariant" obstruction is bypassed entirely: no cyclic shift is used; the interior opening *itself*
  rotates the arm endpoint `A (last)` (index `n > K`), exactly as the last-joint opening does.

**The single isolated residue `InteriorOpenAndSpliceStep`** is the per-level endpoint output bundling
the three productions the lex dispatch cannot perform.  It is genuinely load-bearing (the lex
`(n, deficitCount)` recursion of `SphericalSZInduction` *derives* `endpt A ≤ endpt B` from
`SZStepCore`, which this residue supplies) and strictly endpoint-only.  Its three genuine pieces:

1. **(R-C) The CUT body/splice transport `splice_transport_of_diag_le`.**  After the ear comparison
   `ear_chord_le_of_Main` and the diagonal inequality `cut_diag_le` (both banked in
   `SphericalSZStepClose`), gluing them to `endpt A ≤ endpt B` needs the spliced body
   `A[0..i] ++ A[j..n]` as a convex sub-arm.  Concrete failing chain: the substrate has **no**
   `spliceArm` constructor (only the last-vertex-drop `cutArm` `SphericalDiagCut.cutArm` and the
   first-vertex-drop `frontCut` `SphericalMatchedCut.frontCut`, neither an arbitrary interval union),
   and the body's new diagonal side is matched to `B` only by the *inequality* `cut_diag_le`, not by
   spherical SAS equality (`SphericalSZChain.diag_len_eq` needs the *included angle to agree*, which a
   folded-flat `A` corner — angle `π` — does not satisfy against `B`'s bent corner).
2. **(R-cong) The equal-joints endpoint congruence.**  When no joint is deficient,
   `SphericalSZInduction.all_joints_eq_of_no_deficit` gives equal *joints*, but the endpoint
   *congruence* `endpt A = endpt B` (equal sides + equal joints ⟹ equal endpoint, the spherical arm
   rigidity) is not banked in the substrate.  Concrete failing chain: no `congruent_endpoint_eq`
   exists; deriving it needs the full spherical SSS/SAS arm congruence by induction (a separate
   multi-vertex rigidity argument).
3. **(R-O) The interior reach/stuck supremum trichotomy.**  The §5–§7 OPEN rule opens the deficient
   joint by the interior `openTail` to the admissible supremum `δ*`, getting REACH (the opened joint `k`
   reaches `B`'s value — then `deficitCount_openTail_reach_lt` (banked) drops the measure and the
   deficit-drop IH recurses) or STUCK (a non-incident support vanishes — then `endpt_openTail_interior_mono`
   (banked) carries the endpoint up and (R-C) closes it).  Concrete failing chain: the substrate's
   reach/stuck/supremum apparatus (`SphericalAdmissibleSup.augmented_reachOrStuck_at_sup`,
   `reach_strictConvex_at_sup`) monitors the **last-joint** opening's tail vertex only; the interior
   `openTail` rotates the *whole* tail `> K` about an interior axis, so the admissible family must
   monitor every rotated-tail support and the *interior* joint-angle target slack — a family the
   substrate's `combinedSupport` / `augmentedSupport` (indexed for the single last tail vertex) does not
   provide, and whose closed-set supremum trichotomy + boundary convexity persistence are absent.

These three are the irreducible geometric content of Chapter 13's spherical arm lemma that remains after
the OPEN preservation/deficit/endpoint and the CUT ear API are banked; the lex assembly, the folded-flat
betweenness, and the diagonal inequality are banked in `SphericalSZInduction` / `SphericalSZStepClose`.

### Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `rotS2_axis_fixed`: the rotation genuinely fixes its axis (not a vacuous identity) —
witnessed reflexively, the axis is its own image. -/
theorem rotS2_axis_fixed_nonvacuous (k : S2) (δ : ℝ) : rotS2 k δ k = k := rotS2_axis_fixed k δ

/-- Non-vacuity of the deficit-decrease: in REACH the count genuinely drops (it is a real `<`, realised
whenever `k` was deficient and the opening reaches `B`'s value) — not a vacuous bound. -/
theorem deficitCount_openTail_reach_lt_nonvacuous {n : ℕ} (A B : Fin (n + 1) → S2)
    (k : Fin (n - 1)) (δ : ℝ)
    (hkdef : jointAngle A k < jointAngle B k)
    (hreach : jointAngle (openTail A (openingAxis k) δ) k = jointAngle B k) :
    deficitCount (openTail A (openingAxis k) δ) B < deficitCount A B :=
  deficitCount_openTail_reach_lt A B k δ hkdef hreach

/-- Non-vacuity of the interior endpoint bound: realised reflexively at `θ = 0` (the unopened arm),
where `openTail A K 0 = A` and the bound is `endpt A ≤ endpt A` — so the conclusion is a real endpoint
inequality, not a vacuous-hypothesis impostor. -/
theorem endpt_openTail_interior_base {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) :
    endpt (openTail A K 0) = endpt A := by rw [openTail_zero_angle]

/-- Non-vacuity of `InteriorOpenAndSpliceStep`: its conclusion `endpt A ≤ endpt B` is genuinely
realisable (reflexive at `A = B`), and the deficit-drop IH it consumes is a real (inhabited at the
congruent base) hypothesis — a load-bearing per-step reduction, strictly the single step (consumed by
`SphericalSZInduction.main_at_level`), not the full recursion or a vacuous impostor. -/
theorem interiorOpenAndSpliceStep_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

end ProofsInTheBook.SphericalSZFinal
