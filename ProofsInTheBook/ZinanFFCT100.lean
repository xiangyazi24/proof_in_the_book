import ProofsInTheBook.ZinanFFCT86

/-!
# Ch13 corrected reduction: the endpoint residue splits into proper-no-collision + the trivial full-closure

The earlier single-wind reduction (FFCT97/98) targeted `CrossPieceNoCollisionAtSup` — that a
cross-piece collision `openedWBS r = openedWBS s` (`r ≤ K < s`, `r + 2 ≤ s`) *never* occurs.
That is FALSE in the abstract planar form (FFCT99: an equilateral chain that closes,
`Q₀ = Q₃`, is a valid `PlanarLiftedTurnSpan`).  The genuine obstruction: a collision forces the
sub-arc `[r,s]` edge directions to sum to zero, which needs span `> π`, and a span-`(π,2π)`
self-closure is excluded by the global support ONLY when there is a vertex *outside* `[r,s]`
(properness).  The all-of-the-arm closure `r = 0 ∧ s = n` has no external vertex and is NOT
excludable — but it is harmless: there `endpt (openedWBS) = sDist (Q₀) (Qₙ) = sDist (Qᵣ) (Qₛ)
= 0 ≤ endpt B` since `Q₀ = Qₙ`.

So `CrossPieceCollisionEndpointAtSup` (FFCT86, the predicate the headline
`spherical_arm_mono_final_ch13_v11` actually consumes) reduces to the TRUE residue
`ProperCrossPieceNoCollisionAtSup`: proper cross-piece collisions (`0 < r ∨ s < n`) do not occur.
The full-closure branch is discharged here, unconditionally.
-/

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT86

namespace ProofsInTheBook.ZinanFFCT100

/-- **The proper cross-piece no-collision residue (TRUE).**  A cross-piece collision with a
vertex outside the colliding sub-arc (`0 < r ∨ s < n`, i.e. not the full-arm closure) does not
occur.  Unlike the unrestricted `CrossPieceNoCollisionAtSup`, this excludes the harmless
all-of-the-arm closure `r = 0 ∧ s = n`, so it is not refuted by the equilateral (FFCT99). -/
def ProperCrossPieceNoCollisionAtSup : Prop :=
  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
    StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    SupportStuckWBS A B k →
      ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1),
        r + 2 ≤ s → r ≤ (openingAxis k).val → (openingAxis k).val < s →
        (0 < r ∨ s < n) →
          openedWBS A B k ⟨r, hr⟩ ≠ openedWBS A B k ⟨s, hs⟩

/-- **The endpoint residue from the proper-no-collision residue.**  Splitting on whether the
collision is the full-arm closure `r = 0 ∧ s = n`: the proper case is excluded by the residue,
and the full-closure case gives `endpt (openedWBS) = 0 ≤ endpt B`. -/
theorem collisionEndpoint_of_properNoCollision
    (hproper : ProperCrossPieceNoCollisionAtSup) :
    CrossPieceCollisionEndpointAtSup := by
  intro n A B hA hB hside hangle k hkdef hstuck r s hr hs hrs hrK hKs hcoll
  by_cases hfull : r = 0 ∧ s = n
  · -- Full-arm closure: endpt (openedWBS) = sDist (Qᵣ) (Qₛ) = 0.
    obtain ⟨hr0, hsn⟩ := hfull
    have e0 : (0 : Fin (n + 1)) = ⟨r, hr⟩ := by
      apply Fin.ext; simp [hr0]
    have en : (Fin.last n) = ⟨s, hs⟩ := by
      apply Fin.ext; simp [hsn]
    have hzero : endpt (openedWBS A B k) = 0 := by
      unfold endpt
      rw [e0, en, hcoll]
      unfold sDist
      rw [S2.inner_self]
      exact Real.arccos_one
    rw [hzero]
    unfold endpt
    exact sDist_nonneg _ _
  · -- Proper collision: excluded by the residue.
    exfalso
    have hprop : 0 < r ∨ s < n := by
      rcases Nat.eq_zero_or_pos r with hr0 | hrpos
      · refine Or.inr ?_
        rcases Nat.lt_or_ge s n with hlt | hge
        · exact hlt
        · exact absurd ⟨hr0, le_antisymm (by omega) hge⟩ hfull
      · exact Or.inl hrpos
    exact (hproper A B hA hB hside hangle k hkdef hstuck r s hr hs hrs hrK hKs hprop) hcoll

/-- **Ch13 strict-arm monotonicity from the proper-no-collision residue.**  Composing with
FFCT86's `spherical_arm_mono_final_ch13_v11`, Chapter 13 closes once
`ProperCrossPieceNoCollisionAtSup` is discharged — the TRUE residue (the equilateral closure is
the harmless `endpt = 0` branch, not a counterexample). -/
theorem spherical_arm_mono_ch13_of_properNoCollision
    (hproper : ProperCrossPieceNoCollisionAtSup) :
    SphericalArmMonotone :=
  spherical_arm_mono_final_ch13_v11 (collisionEndpoint_of_properNoCollision hproper)

end ProofsInTheBook.ZinanFFCT100

#print axioms ProofsInTheBook.ZinanFFCT100.collisionEndpoint_of_properNoCollision
#print axioms ProofsInTheBook.ZinanFFCT100.spherical_arm_mono_ch13_of_properNoCollision
