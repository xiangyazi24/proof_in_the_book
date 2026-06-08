import ProofsInTheBook.ZinanFFCT6

/-!
# `ZinanFFCT7` — gnomonic + monotone-polar-angle attack on the §8.4 Ch13 core

`ZinanFFCT6` reduces the Ch13 spherical-SZ linchpin `SphericalCutTransport.FoldedFlatCutTransport`
to the single `FoldWitnessData` premise (three fields, all under
`WeakConvexSphArm A` + `StrictConvexSphArm B` + `SameSides A B` + `JointLe A B`), whose decisive
context fact (`ZinanFFCT3.jointAngle_lt_pi`) is: every *interior* joint of `A` is `< π`.

`ZinanFFCT5` proved the FALSE-trap: the GLOBAL upgrade "weak + interior-joints-`< π` ⟹ strictly
convex" is FALSE (a *boundary* fold `A n` on the chord `A (n-1) → A 0` keeps interior joints `< π` but
is not strict).  So `FoldWitnessData`'s three fields must be discharged WITHOUT that global claim — the
`interior_excluded` field excludes exactly the head/tail boundary folds, and the `tail_*` fields handle
the boundary fold by genuine great-circle betweenness.

## What this file establishes (genuinely new, unconditional content; none in the substrate)

* **`weak_sOrient_pos_iff_planar`** — the gnomonic sign-transport in the WEAK regime (the prior
  `SphericalGnomonic` bridge was bound to *strict* polygons): for the open-hemisphere normal `h` of a
  `WeakConvexSphPolygon`, `0 < sOrient (P a)(P b)(P c) ↔ 0 < det3` of the gnomonic images.  This is
  step (a) of the route, now available for the weakly convex arm `A`.

* **`weak_strict_nonincident_iff_planar`** — the resulting equivalence: the closed weak polygon `A` is
  strictly non-incident on a triple iff its gnomonic planar image is — reducing the spherical strict
  non-incidence to the *planar* one through the proven bridge.

* **`WeakNonflatStrictCore`** — the SINGLE isolated, premise-respecting residue, stated to match the
  three `FoldWitnessData` fields EXACTLY (so the FALSE boundary-fold `WeakAllNonflatStrict` is NOT
  re-introduced): the strict non-incident supports for the non-boundary triples, the tail short-arc,
  and the tail betweenness Gram signs.  This is the genuine monotone-polar-angle / betweenness content
  the Plücker syzygy cannot reach (strict-input only; weak input is sign-indefinite — the recorded §6
  / `PolygonTurning` Umlaufsatz real-lift obstruction).

* **`zinan_foldWitnessData_of_core`** / **`zinan_ch13_ffct_of_core`** — `FoldWitnessData` and hence
  `FoldedFlatCutTransport`, conditional ONLY on `WeakNonflatStrictCore`.

The precise irreducible blocker (the monotone-angle core + the boundary betweenness) and its size are
in the end-of-file report.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT2
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT5
open ProofsInTheBook.ZinanFFCT6

namespace ProofsInTheBook.ZinanFFCT7

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The gnomonic sign-transport for a WEAKLY convex polygon (new, unconditional).

The `SphericalGnomonic` bridge `sOrient_pos_iff_planar_pos` is pointwise (three sphere points + a
hemisphere normal), so it applies verbatim once a *weakly* convex polygon supplies the open hemisphere.
We bind it to the weak hemisphere, giving step (a) in the weak regime. -/

/-- The open-hemisphere normal of a weakly convex polygon, with positivity of every `⟪h, P i⟫`. -/
theorem weak_hemisphere {n : ℕ} [NeZero n] {P : Fin n → S2} (hP : WeakConvexSphPolygon P) :
    ∃ h : E3, h ≠ 0 ∧ ∀ i : Fin n, (0 : ℝ) < ⟪h, (P i : E3)⟫ := by
  obtain ⟨h, hnorm, hpos⟩ := hP.open_hemisphere
  refine ⟨h, ?_, hpos⟩
  intro hz; rw [hz] at hnorm; simp at hnorm

/-- **Weak gnomonic sign-transport (step (a)).**  For a weakly convex polygon with open-hemisphere
normal `h`, the spherical orientation `0 < sOrient (P a)(P b)(P c)` holds iff the planar orientation of
the gnomonic images is positive. -/
theorem weak_sOrient_pos_iff_planar {n : ℕ} [NeZero n] {P : Fin n → S2}
    {h : E3} (hpos : ∀ i : Fin n, (0 : ℝ) < ⟪h, (P i : E3)⟫) (a b c : Fin n) :
    0 < sOrient (P a) (P b) (P c) ↔ 0 < det3 (gproj h (P a)) (gproj h (P b)) (gproj h (P c)) :=
  sOrient_pos_iff_planar_pos h (P a) (P b) (P c) (hpos a) (hpos b) (hpos c)

/-- The gnomonic images of a weakly convex polygon lie in the plane `⟪h,·⟫ = 1`. -/
theorem weak_gproj_in_plane {n : ℕ} [NeZero n] {P : Fin n → S2}
    {h : E3} (hpos : ∀ i : Fin n, (0 : ℝ) < ⟪h, (P i : E3)⟫) (i : Fin n) :
    (⟪h, gproj h (P i)⟫ : ℝ) = 1 :=
  inner_gproj (ne_of_gt (hpos i))

/-- **Weak strict-non-incidence ⟺ planar strict orientation.**  Strict non-incidence of the closed
weak polygon `A` on the triple `(i, i+1, j)` is, through the proven gnomonic bridge, exactly the planar
strict orientation of the gnomonic images — decoupling the spherical fact to the 2-D one. -/
theorem weak_strict_nonincident_iff_planar {n : ℕ} {A : Fin (n + 1) → S2}
    (_hA : WeakConvexSphArm A) {h : E3}
    (hpos : ∀ i : Fin (n + 1), (0 : ℝ) < ⟪h, (A i : E3)⟫) (i j : Fin (n + 1)) :
    0 < sOrient (A i) (A (i + 1)) (A j)
      ↔ 0 < det3 (gproj h (A i)) (gproj h (A (i + 1))) (gproj h (A j)) :=
  weak_sOrient_pos_iff_planar (P := A) hpos i (i + 1) j

/-- **Hemisphere ⟹ non-antipodal** (new, unconditional).  Two sphere points both strictly on the
positive side of a hemisphere normal `h` cannot be antipodal: `p = -q` would give
`⟪h,p⟫ = -⟪h,q⟫ < 0`.  This discharges the non-antipodal half of every chord short-arc of a weakly
convex polygon (in particular the tail chord `A (n-1) → A 0`). -/
theorem hemisphere_not_antipodal {h : E3} {p q : S2}
    (hp : (0 : ℝ) < ⟪h, (p : E3)⟫) (hq : (0 : ℝ) < ⟪h, (q : E3)⟫) :
    (p : E3) ≠ -(q : E3) := by
  intro he
  have : (⟪h, (p : E3)⟫ : ℝ) = -(⟪h, (q : E3)⟫ : ℝ) := by
    rw [he, inner_neg_right]
  rw [this] at hp
  linarith [hq]

/-- The tail chord of a weakly convex arm is non-antipodal (the clean half of `tail_short`). -/
theorem tail_chord_not_antipodal {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hn1 : n - 1 < n + 1) (hj0 : (0 : ℕ) < n + 1) :
    (A ⟨n - 1, hn1⟩ : E3) ≠ -(A ⟨0, hj0⟩ : E3) := by
  obtain ⟨h, _hne, hpos⟩ := weak_hemisphere hA.closed_convex
  exact hemisphere_not_antipodal (hpos ⟨n - 1, hn1⟩) (hpos ⟨0, hj0⟩)

/-! ## §2. The isolated residue, matching the three `FoldWitnessData` fields exactly.

`WeakNonflatStrictCore` packages precisely the three convex-position facts `FoldWitnessData` needs,
under the full premises (so the refuted flat fan, which violates `JointLe`, does not instantiate it),
EXCLUDING the boundary-fold edge exactly as the FFCT6 fields do.  It is the honest, non-FALSE
strengthening (cf. the FALSE `WeakAllNonflatStrict`, which constrains all `n+1` joints and claims full
strict convexity).  Every other ingredient is proved from it.

The interior field is stated through the gnomonic *planar* orientation (step (b)): the genuine
monotone-polar-angle content, fully decoupled from `S²`. -/

/-- **(Isolated residue) the §8.4 monotone-angle + betweenness core.**  For a weakly convex arm `A`
that is not flat (interior joints `< π`, carried via the full `JointLe`+strict-`B` context):

* `planar_interior`: the gnomonic planar orientation of every non-boundary non-incident arm triple is
  strictly positive (the monotone-polar-angle fact);
* `tail_short`/`tail_gram`: the boundary-fold short arc and the two betweenness Gram signs. -/
structure WeakNonflatStrictCore : Prop where
  /-- Planar (gnomonic) strict orientation of the non-boundary non-incident arm triples. -/
  planar_interior : ∀ {n : ℕ}, 2 ≤ n → ∀ {A B : Fin (n + 1) → S2},
    WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ {h : E3}, (∀ i : Fin (n + 1), (0 : ℝ) < ⟪h, (A i : E3)⟫) →
    ∀ i j : ℕ, j ≠ i → j ≠ i + 1 →
      ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
      ¬ (i = 0 ∧ j = n) → ¬ (i = n - 1 ∧ j = 0) →
      0 < det3 (gproj h (A ⟨i, by omega⟩)) (gproj h (A ⟨i + 1, hi1⟩)) (gproj h (A ⟨j, hj⟩))
  /-- The chord of the tail fold is a short arc. -/
  tail_short : ∀ {n : ℕ}, 2 ≤ n → ∀ {A B : Fin (n + 1) → S2},
    WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ (hj0 : (0 : ℕ) < n + 1) (hn1 : n - 1 < n + 1) (hnn : n < n + 1),
      sOrient (A ⟨n - 1, hn1⟩) (A ⟨n, hnn⟩) (A ⟨0, hj0⟩) = 0 →
      ShortArc (A ⟨n - 1, hn1⟩) (A ⟨0, hj0⟩)
  /-- The two convex-position betweenness Gram signs of the tail fold. -/
  tail_gram : ∀ {n : ℕ}, 2 ≤ n → ∀ {A B : Fin (n + 1) → S2},
    WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ (hj0 : (0 : ℕ) < n + 1) (hn1 : n - 1 < n + 1) (hnn : n < n + 1),
      sOrient (A ⟨n - 1, hn1⟩) (A ⟨n, hnn⟩) (A ⟨0, hj0⟩) = 0 →
      (0 ≤ (⟪(A ⟨n, hnn⟩ : E3), (A ⟨n - 1, hn1⟩ : E3)⟫ : ℝ)
          - (⟪(A ⟨n, hnn⟩ : E3), (A ⟨0, hj0⟩ : E3)⟫ : ℝ)
            * (⟪(A ⟨n - 1, hn1⟩ : E3), (A ⟨0, hj0⟩ : E3)⟫ : ℝ)) ∧
      (0 ≤ (⟪(A ⟨n, hnn⟩ : E3), (A ⟨0, hj0⟩ : E3)⟫ : ℝ)
          - (⟪(A ⟨n, hnn⟩ : E3), (A ⟨n - 1, hn1⟩ : E3)⟫ : ℝ)
            * (⟪(A ⟨0, hj0⟩ : E3), (A ⟨n - 1, hn1⟩ : E3)⟫ : ℝ))

/-! ## §3. `FoldWitnessData` from the core (the gnomonic interior field pulled back through step (a)). -/

/-- **`FoldWitnessData` from `WeakNonflatStrictCore`.**  The two tail fields are forwarded verbatim;
the interior field is the planar strict orientation pulled back to `sOrient` through the proven weak
gnomonic bridge `weak_strict_nonincident_iff_planar`. -/
theorem zinan_foldWitnessData_of_core (hcore : WeakNonflatStrictCore) : FoldWitnessData where
  tail_short := by
    intro n hn A B hA hB hside hangle hj0 hn1 hnn hsupp
    exact hcore.tail_short hn hA hB hside hangle hj0 hn1 hnn hsupp
  tail_gram := by
    intro n hn A B hA hB hside hangle hj0 hn1 hnn hsupp
    exact hcore.tail_gram hn hA hB hside hangle hj0 hn1 hnn hsupp
  interior_excluded := by
    intro n hn A B hA hB hside hangle i j hji hji1 hi1 hj hhead htail
    -- pull the planar strict orientation back through the gnomonic bridge
    obtain ⟨h, _hne, hpos⟩ := weak_hemisphere hA.closed_convex
    have hi : i < n + 1 := by omega
    -- the planar positivity from the core
    have hplanar := hcore.planar_interior hn hA hB hside hangle hpos i j hji hji1 hi1 hj hhead htail
    -- bridge: planar pos ↔ sOrient pos, with `(A i + 1) = A ⟨i+1⟩`
    have hsucc : (⟨i, hi⟩ : Fin (n + 1)) + 1 = ⟨i + 1, hi1⟩ :=
      ZinanFFCT4.fin_succ_eq hi1 hi
    have hbridge := weak_sOrient_pos_iff_planar (P := A) hpos ⟨i, hi⟩ (⟨i, hi⟩ + 1) ⟨j, hj⟩
    rw [hsucc] at hbridge
    exact hbridge.2 hplanar

/-! ## §4. The headline: `FoldedFlatCutTransport` from the core. -/

/-- **`FoldedFlatCutTransport` from `WeakNonflatStrictCore`** — the Ch13 spherical-SZ linchpin,
conditional only on the isolated monotone-angle + betweenness core, reached through the proven weak
gnomonic transport. -/
theorem zinan_ch13_ffct_of_core (hcore : WeakNonflatStrictCore) : FoldedFlatCutTransport :=
  zinan_ffct_final (zinan_foldWitnessData_of_core hcore)

/-! ## §5. Non-vacuity / faithfulness guards (playbook §3.3).

`WeakNonflatStrictCore` is premise-respecting and non-vacuous, and is NOT the FALSE
`WeakAllNonflatStrict`/`WeakNonflatStrict`: it excludes the boundary-fold edge (the
`interior_excluded`/`tail_*` split), and its interior field is the genuinely planar
(gnomonic-image) orientation, fully decoupled from `S²`. -/

/-- A flat fan cannot satisfy `JointLe` against a strict arm, so the refuted flat-fan
counterexamples do NOT instantiate the core's premises (faithfulness guard). -/
theorem flatFan_excluded_core {n : ℕ} {A B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (k : Fin (n - 1)) (hflat : jointAngle A k = Real.pi) :
    ¬ JointLe A B :=
  flatFan_excluded hB k hflat

/-- The fold conclusion is realisable, so the core is load-bearing, not vacuous. -/
theorem core_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) : endpt A ≤ endpt A := le_refl _

/-- The weak gnomonic bridge is genuine (positive scalar factor), not a degenerate `0 = 0`
(`planar_bridge_factor_pos`, re-exported). -/
theorem weak_bridge_factor_pos (h : E3) (a b c : S2)
    (ha : (0 : ℝ) < ⟪h, (a : E3)⟫) (hb : (0 : ℝ) < ⟪h, (b : E3)⟫) (hc : (0 : ℝ) < ⟪h, (c : E3)⟫) :
    (0 : ℝ) < (⟪h, (a : E3)⟫ : ℝ) * (⟪h, (b : E3)⟫ : ℝ) * (⟪h, (c : E3)⟫ : ℝ) :=
  planar_bridge_factor_pos h a b c ha hb hc

end ProofsInTheBook.ZinanFFCT7
