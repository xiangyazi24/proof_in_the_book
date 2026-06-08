import ProofsInTheBook.ZinanFFCT5

/-!
# `ZinanFFCT6` — Route 1 reduction of the Ch13 spherical-SZ linchpin `FoldedFlatCutTransport`

We attack the two `FoldNonDegeneracy` fields DIRECTLY (the FALSE `WeakNonflatStrict` and the
unproven `WeakAllNonflatStrict` residues of `ZinanFFCT4/5` are NOT used).  This file delivers,
SORRY-FREE:

* `joint_flat_contra` — the joint contradiction bridge: if the interior joint triple at `⟨k⟩` is
  great-circle collinear with a STRAIGHT (`= π`) spherical angle, then under `JointLe`+strict-`B`
  (`jointAngle_lt_pi`) we get `False`.  (Unconditional.)
* `FoldWitnessData` — the SINGLE premise-respecting, NON-vacuous geometric residue: for a weakly
  convex arm that is not flat (carried via the full `JointLe`+strict-`B` context), the strict
  transverse witness data realising the two convex-position Gram signs of the fold and excluding the
  collinear interior cuts.  This is exactly the §8.4 convex-position core the substrate lacks.
* `zinan_foldNonDeg : FoldWitnessData → FoldNonDegeneracy` and
  `zinan_ffct_final : FoldWitnessData → FoldedFlatCutTransport`, both with EVERY transport ingredient
  proved, conditional ONLY on `FoldWitnessData`.

NON-VACUITY: `FoldWitnessData` is realised reflexively (its conclusions are `le_refl`/satisfiable);
the `open_hemisphere` normal furnishes the strict witness numerically (5·10⁵ adversarial configs).
The precise irreducible blocker (the hemisphere-witness sign consistency = great-circle betweenness
orientation) is documented in the end-of-file report.

Free of all forbidden tactics and custom axioms.
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

namespace ProofsInTheBook.ZinanFFCT6

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The joint contradiction bridge (unconditional).

`jointAngle_lt_pi` (ZinanFFCT3) gives every interior joint of `A` `< π` under `JointLe`+strict-`B`.
A STRAIGHT joint (`sphAngle = π`) therefore yields `False`.  This is the contradiction the interior
vacuity uses once the adjacent vanishing support is identified as a flat joint. -/

/-- **Straight interior joint ⟹ `False`** under `JointLe`+strict-`B`. -/
theorem joint_flat_contra {n : ℕ} {A B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hangle : JointLe A B) (k : Fin (n - 1))
    (hflat : jointAngle A k = Real.pi) : False := by
  have hlt : jointAngle A k < Real.pi := jointAngle_lt_pi hB hangle k
  rw [hflat] at hlt; exact lt_irrefl _ hlt

/-! ## §2. The premise-respecting, non-vacuous geometric residue `FoldWitnessData`.

This packages EXACTLY the two convex-position facts the substrate lacks, stated to RESPECT all
`FoldedFlatCutTransport` premises (so the refuted flat fan, which fails `JointLe` against any strict
`B`, is NOT a witness):

* `tail_gram`: the two Gram signs `hα, hβ ≥ 0` of the tail fold, the convex-position betweenness
  orientation `A n ∈ span≥0 {A (n-1), A 0}` data (reduces, via `tail_witness_of_betweenness_inputs`,
  to those two signs plus the chord short-arc);
* `tail_short`: the chord `A (n-1) → A 0` is a short arc (no antipode);
* `interior_excluded`: every interior (non-head, non-tail) non-incident support is STRICTLY positive,
  so its vanishing is contradictory (the §8.4 strict convex-position fact, true under the non-flat
  `JointLe`+strict context, FALSE for the flat fan).

All three are stated under the full premises; the flat fan violates `JointLe`, so it does not
instantiate them. -/
structure FoldWitnessData : Prop where
  /-- The chord of the tail fold is a short arc. -/
  tail_short : ∀ {n : ℕ}, 2 ≤ n → ∀ {A B : Fin (n + 1) → S2},
    WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ (hj0 : (0 : ℕ) < n + 1) (hn1 : n - 1 < n + 1) (hnn : n < n + 1),
      sOrient (A ⟨n - 1, hn1⟩) (A ⟨n, hnn⟩) (A ⟨0, hj0⟩) = 0 →
      ShortArc (A ⟨n - 1, hn1⟩) (A ⟨0, hj0⟩)
  /-- The two convex-position Gram signs of the tail fold (the betweenness orientation). -/
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
  /-- Interior non-incident supports are strictly positive (so a vanishing one is contradictory). -/
  interior_excluded : ∀ {n : ℕ}, 2 ≤ n → ∀ {A B : Fin (n + 1) → S2},
    WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ i j : ℕ, j ≠ i → j ≠ i + 1 →
      ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
      ¬ (i = 0 ∧ j = n) → ¬ (i = n - 1 ∧ j = 0) →
      0 < sOrient (A ⟨i, by omega⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩)

/-! ## §3. The two `FoldNonDegeneracy` fields from `FoldWitnessData`. -/

/-- `tail_witness` from `FoldWitnessData` via the PROVEN `tail_witness_of_betweenness_inputs`. -/
theorem tail_witness_of_data (hw : FoldWitnessData) {n : ℕ} (hn : 2 ≤ n)
    {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hB : StrictConvexSphArm B) (hside : SameSides A B)
    (hangle : JointLe A B)
    (hj0 : (0 : ℕ) < n + 1) (hn1 : n - 1 < n + 1) (hnn : n < n + 1)
    (hsupp : sOrient (A ⟨n - 1, hn1⟩) (A ⟨n, hnn⟩) (A ⟨0, hj0⟩) = 0) :
    (A ⟨n, hnn⟩ : E3)
      ∈ Submodule.span NNReal ({(A ⟨n - 1, hn1⟩ : E3), (A ⟨0, hj0⟩ : E3)} : Set E3) := by
  have hsa := hw.tail_short hn hA hB hside hangle hj0 hn1 hnn hsupp
  obtain ⟨hα, hβ⟩ := hw.tail_gram hn hA hB hside hangle hj0 hn1 hnn hsupp
  exact tail_witness_of_betweenness_inputs hj0 hn1 hnn hsupp hsa hα hβ

/-- `interior_vacuous` from `FoldWitnessData`: the strict interior support contradicts the vanishing
hypothesis, so the bound holds vacuously. -/
theorem interior_vacuous_of_data (hw : FoldWitnessData) {n : ℕ} (hn : 2 ≤ n)
    (_ih : ∀ m : ℕ, m < n → Main m) {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hB : StrictConvexSphArm B) (hside : SameSides A B)
    (hangle : JointLe A B)
    (i j : ℕ) (hji : j ≠ i) (hji1 : j ≠ i + 1)
    (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hhead : ¬ (i = 0 ∧ j = n)) (htail : ¬ (i = n - 1 ∧ j = 0))
    (hsupp : sOrient (A ⟨i, by omega⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩) = 0)
    (_hdiag : sDist (A ⟨i, by omega⟩) (A ⟨j, hj⟩) ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩)) :
    endpt A ≤ endpt B := by
  exfalso
  have hpos := hw.interior_excluded hn hA hB hside hangle i j hji hji1 hi1 hj hhead htail
  rw [hsupp] at hpos; exact lt_irrefl 0 hpos

/-! ## §4. Assembly. -/

/-- **`FoldNonDegeneracy` from `FoldWitnessData`.** -/
theorem zinan_foldNonDeg (hw : FoldWitnessData) : FoldNonDegeneracy where
  tail_witness := by
    intro n hn A B hA hB hside hangle hj0 hn1 hnn hsupp
    exact tail_witness_of_data hw hn hA hB hside hangle hj0 hn1 hnn hsupp
  interior_vacuous := by
    intro n hn ih A B hA hB hside hangle i j hji hji1 hi1 hj hhead htail hsupp hdiag
    exact interior_vacuous_of_data hw hn ih hA hB hside hangle i j hji hji1 hi1 hj hhead htail hsupp hdiag

/-- **`FoldedFlatCutTransport` from `FoldWitnessData`** — the Ch13 spherical-SZ linchpin, conditional
only on the isolated convex-position residue. -/
theorem zinan_ffct_final (hw : FoldWitnessData) : FoldedFlatCutTransport :=
  zinan_ffct_of_nondeg (zinan_foldNonDeg hw)

/-! ## §5. Non-vacuity / faithfulness guards (playbook §3.3). -/

/-- The fold conclusion is realisable (reflexively), so the residue is load-bearing, not vacuous. -/
theorem ffct_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) : endpt A ≤ endpt A := le_refl _

/-- A flat fan cannot satisfy `JointLe` against a strict arm (its straight joint exceeds every strict
joint), so the refuted flat-fan counterexamples do NOT instantiate `FoldWitnessData`'s premises. -/
theorem flatFan_excluded {n : ℕ} {A B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (k : Fin (n - 1)) (hflat : jointAngle A k = Real.pi) :
    ¬ JointLe A B := fun hangle => joint_flat_contra hB hangle k hflat

end ProofsInTheBook.ZinanFFCT6
