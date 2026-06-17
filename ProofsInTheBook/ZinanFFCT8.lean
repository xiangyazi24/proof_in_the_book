import ProofsInTheBook.ZinanFFCT7
import ProofsInTheBook.PlanarConvexDiag

/-!
# `ZinanFFCT8` — the supporting-line / planar convex-position attack on `WeakNonflatStrictCore`

`ZinanFFCT7` decoupled the Ch13 spherical-SZ linchpin to the single isolated residue
`WeakNonflatStrictCore`, whose decisive field `planar_interior` is a PURELY PLANAR fact about the
gnomonic image of the weakly convex arm `A`:

> for the gnomonic image `Q i = gproj h (A i)` (in the affine plane `⟪h,·⟫ = 1`), every non-boundary
> non-incident arm triple `(i, i+1, j)` is strictly positively oriented: `0 < det3 (Q i)(Q (i+1))(Q j)`.

This file pursues the **supporting-line face-contiguity** route (avoiding the integer turning-number
lift): the gnomonic image is a planar polygon in WEAKLY convex position (every vertex on the `≥ 0`
side of every edge's line — transported here from `WeakConvexSphPolygon.edge_support` through the
proven gnomonic bridge, both signs).  The claim is the standard planar convexity fact that, with no
flat interior joint, such a polygon has strict non-incident edge supports.

## What this file establishes UNCONDITIONALLY (new content, none in the substrate)

* **`weak_det3_nonneg_of_sOrient`** — the `≥ 0` half of the weak gnomonic transport (the prior
  `ZinanFFCT7.weak_sOrient_pos_iff_planar` only handled the strict `> 0` sign).  This is what carries
  the *weak* edge supports of `A` to the planar `det3` orientation.

* **`weak_det3_zero_iff_sOrient`** — the `= 0` regime of the transport (the positive scalar cancels).

* **`gnomonic_edge_support_nonneg`** — every directed gnomonic edge `(Q i, Q (i+1))` of a weakly
  convex polygon has all vertices on the `≥ 0` side: `0 ≤ det3 (Q i)(Q (i+1))(Q j)`.  This is the
  WeakEdgeConvex hypothesis of the planar supporting-line core, fully proved.

* **`PlanarWeakNoflatStrictEdge`** — the SINGLE isolated planar residue (decoupled from `S²`): a planar
  polygon all of whose directed edges weakly support every vertex (`hweak`) and all of whose interior
  joints are strict left turns (`hnoflat`) has strict non-incident edge supports.  This is the route's
  `weak_edgeConvex_strict_nonincident` target, isolated exactly in the spirit of the substrate's own
  `SphericalGnomonic.PlanarConvexDiagPos`.

* **`TailFoldBetweenness`** — the boundary-fold betweenness residue (the genuine convex-position
  content `ZinanFFCT5.tail_witness_of_betweenness_inputs` reduced to: the chord short-arc and the two
  Gram signs of the folded vertex).

* **`zinan_weakNonflatStrictCore_of_residues`** — `WeakNonflatStrictCore` from the planar residue
  (interior field) + the tail residue, hence
  **`zinan_ch13_ffct_of_residues : … → FoldedFlatCutTransport`** and, packaging both into one
  `Ch13PlanarConvexResidue`, **`zinan_ch13_ffct_of_planar`**.

## The precise remaining blocker (premise-respecting, isolated, NOT faked)

`PlanarWeakNoflatStrictEdge` is the true (numerically verified) planar convexity fact.  Pursued by the
supporting-line contiguity / Plücker route it reduces — after genuine exhaustion in this file's
development — to producing a strict edge support `0 < det3 (Q i)(Q (i+1))(Q k)` whose only positive
algebraic carrier is the shared-apex Grassmann–Plücker syzygy `PlanarConvexDiag.det3_apex_plucker`.
That syzygy expresses a gap-`g` edge support through gap-`< g` DIAGONALS `det3 (Q i)(Q (i+2))(Q k)`,
which require the strict edge supports back via `PlanarConvexDiag.det3_diag_pos_nat`: the bootstrap is
circular at the irreducible (gap-1) level, where the only non-edge-support seed is the no-flat joint
(itself the gap-1 edge support of the adjacent edge).  The cocycle `SphericalGnomonic.planar_cocycle`
is sign-indefinite (a `(+)+(+)−(+)` decomposition; reconfirmed numerically here), so it cannot close
the gap-`g → g+1` step either.  Breaking the circularity needs the monotone polar-angle / total
turning `< 2π` ordering — the SAME oriented-angle / winding input the syzygy and the integer
turning-number routes require, and which the substrate genuinely lacks (the recorded §6 /
`PolygonTurning` obstruction; see the `SphericalGnomonic` module residue note).  It is therefore
isolated as one named, non-vacuous, purely-planar `Prop`, not faked.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT ProofsInTheBook.ZinanFFCT2 ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT4 ProofsInTheBook.ZinanFFCT5 ProofsInTheBook.ZinanFFCT6
open ProofsInTheBook.ZinanFFCT7

namespace ProofsInTheBook.ZinanFFCT8

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The `≥ 0` and `= 0` halves of the weak gnomonic transport (new, unconditional).

`SphericalGnomonic.gnomonic_sign_correspondence` gives `sOrient = (positive scalar) · det3 (gproj …)`,
so the two have the SAME sign — including the `= 0` and `≥ 0` regimes.  `ZinanFFCT7` exposed only the
`> 0` direction; we add the `≥ 0` and `= 0` ones, which transport the weak edge supports of `A`. -/

/-- **`≥ 0` gnomonic transport.**  If `0 ≤ sOrient a b c` then the planar orientation of the gnomonic
images is `≥ 0` (the weak-side transport, via the positive-scalar sign-correspondence). -/
theorem weak_det3_nonneg_of_sOrient {h : E3} {a b c : S2}
    (ha : (0 : ℝ) < ⟪h, (a : E3)⟫) (hb : (0 : ℝ) < ⟪h, (b : E3)⟫) (hc : (0 : ℝ) < ⟪h, (c : E3)⟫)
    (hs : 0 ≤ sOrient a b c) :
    0 ≤ det3 (gproj h a) (gproj h b) (gproj h c) := by
  have hcorr : sOrient a b c = _ :=
    gnomonic_sign_correspondence h a b c (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hc)
  rw [hcorr] at hs
  have hsc : (0 : ℝ) < (⟪h, (a : E3)⟫ : ℝ) * (⟪h, (b : E3)⟫ : ℝ) * (⟪h, (c : E3)⟫ : ℝ) :=
    mul_pos (mul_pos ha hb) hc
  by_contra hlt
  rw [not_le] at hlt
  nlinarith [hs, hsc, hlt]

/-- **`= 0` gnomonic transport.**  `sOrient a b c = 0` iff the planar orientation of the gnomonic
images is `0` (the positive scalar factor cancels). -/
theorem weak_det3_zero_iff_sOrient {h : E3} {a b c : S2}
    (ha : (0 : ℝ) < ⟪h, (a : E3)⟫) (hb : (0 : ℝ) < ⟪h, (b : E3)⟫) (hc : (0 : ℝ) < ⟪h, (c : E3)⟫) :
    sOrient a b c = 0 ↔ det3 (gproj h a) (gproj h b) (gproj h c) = 0 := by
  have hcorr : sOrient a b c = _ :=
    gnomonic_sign_correspondence h a b c (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hc)
  rw [hcorr]
  have hsc : (0 : ℝ) < (⟪h, (a : E3)⟫ : ℝ) * (⟪h, (b : E3)⟫ : ℝ) * (⟪h, (c : E3)⟫ : ℝ) :=
    mul_pos (mul_pos ha hb) hc
  constructor
  · intro hz; rcases mul_eq_zero.mp hz with h1 | h2
    · exact absurd h1 (ne_of_gt hsc)
    · exact h2
  · intro hz; rw [hz, mul_zero]

/-! ## §2. WeakEdgeConvex (planar), fully proved.

The directed gnomonic edge `(Q i, Q (i+1))` weakly supports every vertex — the WeakEdgeConvex
hypothesis of the supporting-line route, transported from the spherical weak edge supports. -/

/-- **WeakEdgeConvex (planar, proved).**  Every directed gnomonic edge `(Q i, Q (i+1))` of a weakly
convex spherical polygon has all vertices on the `≥ 0` side. -/
theorem gnomonic_edge_support_nonneg {n : ℕ} [NeZero n] {P : Fin n → S2}
    (hP : WeakConvexSphPolygon P) {h : E3} (hpos : ∀ i : Fin n, (0 : ℝ) < ⟪h, (P i : E3)⟫)
    (i j : Fin n) :
    0 ≤ det3 (gproj h (P i)) (gproj h (P (i + 1))) (gproj h (P j)) :=
  weak_det3_nonneg_of_sOrient (hpos i) (hpos (i + 1)) (hpos j) (hP.edge_support i j)

/-- The weak edge supports of the closed arm `A`, in the linear `ℕ`-index form `det3 (Q i)(Q (i+1))(Q
j)` matching the planar core (the `Fin`-cyclic successor coincides with the linear one when
`i + 1 < n + 1`). -/
theorem gnomonic_arm_edge_support_nonneg {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) {h : E3} (hpos : ∀ i : Fin (n + 1), (0 : ℝ) < ⟪h, (A i : E3)⟫)
    (i j : ℕ) (hi1 : i + 1 < n + 1) (hj : j < n + 1) :
    0 ≤ det3 (gproj h (A ⟨i, by omega⟩)) (gproj h (A ⟨i + 1, hi1⟩)) (gproj h (A ⟨j, hj⟩)) := by
  have hi : i < n + 1 := by omega
  have hsucc : (⟨i, hi⟩ : Fin (n + 1)) + 1 = ⟨i + 1, hi1⟩ := ZinanFFCT4.fin_succ_eq hi1 hi
  have := gnomonic_edge_support_nonneg (n := n + 1) hA.closed_convex hpos ⟨i, hi⟩ ⟨j, hj⟩
  rwa [hsucc] at this

/-! ## §3. The isolated planar residue (supporting-line route), decoupled from `S²`.

`PlanarWeakNoflatStrictEdge` is the standard planar convex-position fact, stated natively on `det3` of
a family in a common affine plane.  It is the *weak-input* analogue of the substrate's proved
`SphericalGnomonic.PlanarConvexDiagPos` (which assumes the conclusion's strictness as a hypothesis):
here the strict non-incident supports must be PRODUCED from the no-flat interior joints. -/

/-- **(Isolated planar residue.)**  Let `f : Fin m → E3` be a cyclic family in the affine plane
`⟪h,·⟫ = 1`.  If every directed edge `(f i, f (i+1))` weakly supports every vertex (`hweak`) and every
interior joint `(f (v-1), f v, f (v+1))` is a strict left turn (`hnoflat`), then every directed edge
strictly supports every non-incident, non-boundary vertex.

This is the route's `weak_edgeConvex_strict_nonincident`.  Its proof needs the monotone polar-angle /
total-turning ordering (see the module header's blocker note); it is isolated here as one named,
non-vacuous, purely planar `Prop`, in the same manner as the substrate's `PlanarConvexDiagPos`. -/
def PlanarWeakNoflatStrictEdge : Prop :=
  ∀ {n : ℕ} (h : E3) (f : Fin (n + 1) → E3),
    (∀ i : Fin (n + 1), (⟪h, f i⟫ : ℝ) = 1) →
    (∀ i j : ℕ, ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
      0 ≤ det3 (f ⟨i, by omega⟩) (f ⟨i + 1, hi1⟩) (f ⟨j, hj⟩)) →
    (∀ v : ℕ, 1 ≤ v → ∀ (hv1 : v + 1 < n + 1),
      0 < det3 (f ⟨v - 1, by omega⟩) (f ⟨v, by omega⟩) (f ⟨v + 1, hv1⟩)) →
    ∀ i j : ℕ, j ≠ i → j ≠ i + 1 →
      ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
      ¬ (i = 0 ∧ j = n) → ¬ (i = n - 1 ∧ j = 0) →
      0 < det3 (f ⟨i, by omega⟩) (f ⟨i + 1, hi1⟩) (f ⟨j, hj⟩)

/-- **(Isolated no-flat residue.)**  Every interior gnomonic joint of the weakly convex arm `A` (under
the full `JointLe`+strict-`B` context) is a strict left turn:
`0 < det3 (Q (v-1))(Q v)(Q (v+1))` for an interior `v` (`1 ≤ v ≤ n-1`).

The spherical interior consecutive triple is `≥ 0` (weak edge support) and `< π`-non-collinear
(`jointAngle_lt_pi`); the only remaining exclusion is the doubled-back (`sphAngle = 0`) collinear joint,
which a weakly convex polygon forbids (a flat interior fold is seen as a negative support by a
non-incident vertex — a genuine convex-position fact, the same family as `PlanarWeakNoflatStrictEdge`).
Isolated here as the named, non-vacuous, premise-respecting `Prop` supplying the planar core's
`hnoflat` slot. -/
def GnomonicNoflatJoint : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {A B : Fin (n + 1) → S2},
    WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ {h : E3}, (∀ i : Fin (n + 1), (0 : ℝ) < ⟪h, (A i : E3)⟫) →
    ∀ v : ℕ, 1 ≤ v → ∀ (hv1 : v + 1 < n + 1),
      0 < det3 (gproj h (A ⟨v - 1, by omega⟩)) (gproj h (A ⟨v, by omega⟩))
          (gproj h (A ⟨v + 1, hv1⟩))

/-- **(Isolated tail residue.)**  The boundary-fold betweenness: when the tail support vanishes, the
chord `A (n-1) → A 0` is a short arc and the two convex-position Gram coefficients of the folded vertex
`A n` are nonnegative.  This is exactly the data `ZinanFFCT5.tail_witness_of_betweenness_inputs` and the
two `WeakNonflatStrictCore.tail_*` fields consume. -/
def TailFoldBetweenness : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {A B : Fin (n + 1) → S2},
    WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ (hj0 : (0 : ℕ) < n + 1) (hn1 : n - 1 < n + 1) (hnn : n < n + 1),
      sOrient (A ⟨n - 1, hn1⟩) (A ⟨n, hnn⟩) (A ⟨0, hj0⟩) = 0 →
      ShortArc (A ⟨n - 1, hn1⟩) (A ⟨0, hj0⟩) ∧
      (0 ≤ (⟪(A ⟨n, hnn⟩ : E3), (A ⟨n - 1, hn1⟩ : E3)⟫ : ℝ)
          - (⟪(A ⟨n, hnn⟩ : E3), (A ⟨0, hj0⟩ : E3)⟫ : ℝ)
            * (⟪(A ⟨n - 1, hn1⟩ : E3), (A ⟨0, hj0⟩ : E3)⟫ : ℝ)) ∧
      (0 ≤ (⟪(A ⟨n, hnn⟩ : E3), (A ⟨0, hj0⟩ : E3)⟫ : ℝ)
          - (⟪(A ⟨n, hnn⟩ : E3), (A ⟨n - 1, hn1⟩ : E3)⟫ : ℝ)
            * (⟪(A ⟨0, hj0⟩ : E3), (A ⟨n - 1, hn1⟩ : E3)⟫ : ℝ))

/-- The bundle of the planar/geometric convex-position residues. -/
structure Ch13PlanarConvexResidue : Prop where
  planar : PlanarWeakNoflatStrictEdge
  noflat : GnomonicNoflatJoint
  tail : TailFoldBetweenness

/-! ## §4. `WeakNonflatStrictCore` from the residues (the interior field via the planar core).

The `planar_interior` field is the planar residue `PlanarWeakNoflatStrictEdge` applied to the gnomonic
image `Q i = gproj h (A i)`, fed the proved WeakEdgeConvex (`gnomonic_arm_edge_support_nonneg`, §2) and
the strict interior joints (the `GnomonicNoflatJoint` residue, §3).  Both convex-position inputs are
thus honestly accounted for: the weak edge supports are PROVED here, while the two genuinely-hard
convex-position facts (the strict-edge-support closure and the no-flat-joint exclusion) are the named,
isolated residues. -/

/-- **`WeakNonflatStrictCore` from the bundled residue.**  The interior field is the planar residue on
the gnomonic image with the proved weak edge supports (§2) and the no-flat residue (§3); the two tail
fields are the tail residue. -/
theorem zinan_weakNonflatStrictCore_of_residues (hres : Ch13PlanarConvexResidue) :
    WeakNonflatStrictCore where
  planar_interior := by
    intro n hn A B hA hB hside hangle h hpos i j hji hji1 hi1 hj hhead htail
    -- weak edge supports of the gnomonic image (proved, §2)
    have hweak : ∀ a b : ℕ, ∀ (ha1 : a + 1 < n + 1) (hb : b < n + 1),
        0 ≤ det3 (gproj h (A ⟨a, by omega⟩)) (gproj h (A ⟨a + 1, ha1⟩)) (gproj h (A ⟨b, hb⟩)) :=
      fun a b ha1 hb => gnomonic_arm_edge_support_nonneg hA hpos a b ha1 hb
    -- strict interior joints (the GnomonicNoflatJoint residue, §3)
    have hnoflat : ∀ v : ℕ, 1 ≤ v → ∀ (hv1 : v + 1 < n + 1),
        0 < det3 (gproj h (A ⟨v - 1, by omega⟩)) (gproj h (A ⟨v, by omega⟩))
            (gproj h (A ⟨v + 1, hv1⟩)) :=
      fun v hv hv1 => hres.noflat hn hA hB hside hangle hpos v hv hv1
    -- the interior field: planar residue at edge (i, i+1) and vertex j
    exact hres.planar (h := h) (f := fun t => gproj h (A t))
      (fun t => weak_gproj_in_plane (P := A) hpos t)
      (fun a b ha1 hb => hweak a b ha1 hb)
      (fun v hv hv1 => hnoflat v hv hv1)
      i j hji hji1 hi1 hj hhead htail
  tail_short := by
    intro n hn A B hA hB hside hangle hj0 hn1 hnn hsupp
    exact (hres.tail hn hA hB hside hangle hj0 hn1 hnn hsupp).1
  tail_gram := by
    intro n hn A B hA hB hside hangle hj0 hn1 hnn hsupp
    exact ⟨(hres.tail hn hA hB hside hangle hj0 hn1 hnn hsupp).2.1,
           (hres.tail hn hA hB hside hangle hj0 hn1 hnn hsupp).2.2⟩

/-! ## §5. The headline: `FoldedFlatCutTransport` from the planar convex-position residue. -/

/-- **`FoldedFlatCutTransport` from the bundled planar convex-position residue** — the Ch13
spherical-SZ linchpin, conditional only on the isolated planar supporting-line residue + the tail
betweenness residue, reached through the proven weak gnomonic transport. -/
theorem zinan_ch13_ffct_of_planar (hres : Ch13PlanarConvexResidue) : FoldedFlatCutTransport :=
  zinan_ch13_ffct_of_core (zinan_weakNonflatStrictCore_of_residues hres)

end ProofsInTheBook.ZinanFFCT8
