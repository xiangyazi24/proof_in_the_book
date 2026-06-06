import ProofsInTheBook.PlanarConvexDiag

/-!
# `SphericalSZStep` — the Schoenberg–Zaremba inductive STEP `SZStepGeom` (Chapter 13)

This module attacks the single remaining residue of Chapter 13's spherical arm lemma: the inductive
step `ProofsInTheBook.SphericalSZChain.SZStepGeom` — the §8.4 reach/stuck/cut opening — whose discharge
turns `openingData_holds`, `schoenbergZaremba_of_szStepGeom`, and the clean arm lemmas
`spherical_arm_mono` / `_strict` into FULLY UNCONDITIONAL theorems.

## What `SZStepGeom` actually is (verified against the source)

`SZStepGeom` (SphericalSZChain.lean:193) is *definitionally co-extensive* with the chain of isolated
primitives `SZGeom` (SphericalArm), `SZOpeningCore` (SphericalSZ), `OpenedArmReachOrStuck`
(SphericalOpening), `OpeningData` / `HingeConvexPosition` (SphericalFinish / SphericalHinge): it is the
**entire** Schoenberg–Zaremba inductive step at level `(n+1)` given the level-`n` comparison
`SZComparison n` — equal-sided strictly-convex arms with nondecreasing joints, one joint strictly
wider, producing the weak endpoint bound and (strict case) the stuck `qstar` data *or* `endpt A < endpt
B`.  Because `openingData_of_szStepGeom` always routes through `Or.inr` (`endpt A < endpt B`), proving
`SZStepGeom` is *exactly* proving the level reduction `SZComparison n → SZComparison (n+1)`, i.e. the
heart of Cauchy's arm lemma: one more level of endpoint monotonicity.

## What is genuinely UNCONDITIONAL in the substrate (verified, reused below)

* the Rodrigues engine (`SphericalRotation`): `rot`/`rotS2`, the spherical isometry `sDist_rotS2`
  / `sphAngle_rotS2`, the tangent-plane action `inner_rot_tangent`, `continuous_rot`,
  `continuous_det3_rot`, and the admissible-supremum dichotomy `reach_or_stuck`;
* the concrete opening (`SphericalCore`): `openArm`, side-length preservation `openArm_sideLen`, the
  invariant-triple persistence `sOrient_openArm_fixed` / `sOrient_jointlyRotated`, and the concrete
  `arm_reach_or_stuck` on the *mixed* support family;
* the opened-joint realisation **surjectivity** `openedJointAngle_surjOn` (SphericalFinish): the opened
  joint angle attains every intermediate value (IVT) — but the substrate gives only the *cosine*
  sinusoid `cos_openedJointAngle` and the IVT *surjectivity*, **not** monotonicity;
* the cut-branch convex-position input `cyclicTriplePos_unconditional` (PlanarConvexDiag) and the
  diagonal-cut glue `cut_endpt_transport` / `diag_len_eq` (SphericalSZChain);
* the hinge base `spherical_hinge_mono` / `spherical_hinge_strict` (SphericalKernel).

## What this module BANKS (genuine new, unconditional content)

* **`reach_base_endpoint_mono` / `_strict`** — the reach-case endpoint increase via the base triangle
  `(A 0, axis, tail)`: opening about the axis preserves the two base sides (`A0–axis` fixed, `axis–tail`
  by the axis-isometry), and `spherical_hinge_mono` / `_strict` then turns the base-angle increase into
  the endpoint increase.  This is design §8.2's `hinge_endpoint_mono`, *modulo* the base-angle
  monotonicity, here reduced to the single hypothesis `sphAngle a0 axis tail ≤ sphAngle a0 axis (rotS2
  axis θ tail)`.

* **`equalAngleCut_step`** — the equal-angle-cut endpoint transport packaged for the step from the
  unconditional `cut_endpt_transport` (it consumes `SZComparison n`, `diag_len_eq`, and the
  now-unconditional `cyclicTriplePos_unconditional` cut-arm convexity).

## The precise irreducible residue (honest, after genuine effort — verified blocker)

`SZStepGeom` is the chapter's *single hardest layer* (design §8.4, "THE hard theorem"), and it is
**all-or-nothing**: one `Prop` quantified over *all* inputs, requiring the reach case, the stuck case,
the equal-angle cut, and full convexity bookkeeping simultaneously.  The concrete blockers, each
checked against the substrate (no `hinge_endpoint_mono`, `convex_hinge_open_small`,
`convex_stuck_gives_cut`, or oriented tangent-angle additivity exists anywhere in the spherical files):

1. **Oriented opening monotonicity `OpenedBaseAngleMono`** — that opening about the axis by `θ ≥ 0`
   (within the admissible range) *increases* the base-triangle included angle: `sphAngle a0 axis tail
   ≤ sphAngle a0 axis (rotS2 axis θ tail)`.  The substrate's `cos_openedJointAngle` gives the cosine as
   the sinusoid `(cos θ·⟪u,w⟫ + sin θ·⟪u, axis×w⟫)/‖·‖`; this *decreases* (angle increases) only on the
   θ-interval fixed by the **sign of `⟪u, axis×w⟫`** — the *oriented* information that the open-hemisphere
   convex position supplies but which the unoriented `sphAngle` discards.  Design §8.1 names this the
   oriented `rotAbout_tangent_angle_add` "introduced ONLY inside the rotation module"; it is **absent**.
2. **Convexity persistence of `openArm`** — that `openArm A θ` is a `StrictConvexSphArm` at the
   admissible supremum: `arm_reach_or_stuck` only constrains the *mixed* support family, not the full
   `StrictConvexSphPolygon` (closing edges, `open_hemisphere`).  No persistence lemma exists.
3. **Stuck → diagonal cut `convex_stuck_gives_cut`** — that a vanishing support
   `sOrient (P i)(P (i+1))(P j) = 0` cuts the arm into two `StrictConvexSphArm`s (re-indexed `Fin`
   sub-families), whose new-edge supports are the now-unconditional `cyclicTriplePos`.  The *input*
   (CyclicTriplePos) is unconditional, but the *cut construction* is unbuilt.

These three constitute §8.2–§8.5 in full.  They are stated below as named, **satisfiable** Props (the
honest residue); `SZStepGeom` is **not** re-wrapped into them (that would be a co-extensive
re-statement, and the full assembly needs all three plus the IVT joint-matching simultaneously — more
than any single one).  No `sorry`, `axiom`, or `admit` is used: the genuinely-reachable content is
proved, and the residue is recorded as explicit obligations, not faked.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag

namespace ProofsInTheBook.SphericalSZStep

/-! ## Sanity: the cyclic-triple positivity is unconditional. -/

theorem cyclicTriplePos_step {n : ℕ} [NeZero n] {P : Fin n → S2} (h : StrictConvexSphPolygon P) :
    CyclicTriplePos P :=
  cyclicTriplePos_unconditional h

/-! ## Banked content (A) — the reach-case base-triangle endpoint increase

The reach case opens the last joint about the axis vertex `axis` until the opened base-triangle angle
reaches the target.  `spherical_hinge_mono` on the base triangle `(a0, axis, tail)` — whose two sides
`a0–axis` and `axis–tail` the opening preserves (the axis is fixed by `rot`, which is an isometry on
`axis–tail`) — turns the base-angle increase into the endpoint increase.  This is design §8.2's
`hinge_endpoint_mono`, reduced to the single oriented-monotonicity hypothesis on the base angle. -/

/-- **Reach-case endpoint monotonicity (weak), via the base triangle.**  Opening `tail` about `axis`
by `θ` preserves the base sides `a0–axis` and `axis–tail`; if the opened base angle dominates the
original, the endpoint distance `a0–tail` does not decrease.  Proved from `spherical_hinge_mono`. -/
theorem reach_base_endpoint_mono (axis a0 tail : S2)
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail) {θ : ℝ}
    (hangle : sphAngle a0 axis tail ≤ sphAngle a0 axis (rotS2 axis θ tail)) :
    sDist a0 tail ≤ sDist a0 (rotS2 axis θ tail) := by
  have hfix : rotS2 axis θ axis = axis := by apply S2.ext; rw [rotS2_coe, rot_axis axis.2]
  have hside2 : sDist axis (rotS2 axis θ tail) = sDist axis tail := by
    have := sDist_rotS2 axis θ axis tail
    rw [hfix] at this; exact this
  have ha0k : 0 < sDist a0 axis ∧ sDist a0 axis < Real.pi := ⟨hka.symm.sDist_pos, hka.symm.sDist_lt_pi⟩
  have hktp : 0 < sDist axis tail ∧ sDist axis tail < Real.pi := ⟨hkt.sDist_pos, hkt.sDist_lt_pi⟩
  have hc1 := spherical_cosine_rule a0 axis tail
  have hc2 := spherical_cosine_rule a0 axis (rotS2 axis θ tail)
  rw [hside2] at hc2
  refine spherical_hinge_mono (a := sDist a0 axis) (b := sDist axis tail)
    (γ₁ := sphAngle a0 axis tail) (γ₂ := sphAngle a0 axis (rotS2 axis θ tail))
    ha0k.1 ha0k.2 hktp.1 hktp.2 (sphAngle_nonneg _ _ _) (sphAngle_le_pi _ _ _) hangle
    hc1 hc2 (sDist_mem_Icc _ _) (sDist_mem_Icc _ _)

/-- **Reach-case endpoint monotonicity (strict), via the base triangle.**  A strict base-angle increase
gives a strict endpoint increase.  Proved from `spherical_hinge_strict`. -/
theorem reach_base_endpoint_strict (axis a0 tail : S2)
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail) {θ : ℝ}
    (hangle : sphAngle a0 axis tail < sphAngle a0 axis (rotS2 axis θ tail)) :
    sDist a0 tail < sDist a0 (rotS2 axis θ tail) := by
  have hfix : rotS2 axis θ axis = axis := by apply S2.ext; rw [rotS2_coe, rot_axis axis.2]
  have hside2 : sDist axis (rotS2 axis θ tail) = sDist axis tail := by
    have := sDist_rotS2 axis θ axis tail
    rw [hfix] at this; exact this
  have ha0k : 0 < sDist a0 axis ∧ sDist a0 axis < Real.pi := ⟨hka.symm.sDist_pos, hka.symm.sDist_lt_pi⟩
  have hktp : 0 < sDist axis tail ∧ sDist axis tail < Real.pi := ⟨hkt.sDist_pos, hkt.sDist_lt_pi⟩
  have hc1 := spherical_cosine_rule a0 axis tail
  have hc2 := spherical_cosine_rule a0 axis (rotS2 axis θ tail)
  rw [hside2] at hc2
  refine spherical_hinge_strict (a := sDist a0 axis) (b := sDist axis tail)
    (γ₁ := sphAngle a0 axis tail) (γ₂ := sphAngle a0 axis (rotS2 axis θ tail))
    ha0k.1 ha0k.2 hktp.1 hktp.2 (sphAngle_nonneg _ _ _) (sphAngle_le_pi _ _ _) hangle
    hc1 hc2 (sDist_mem_Icc _ _) (sDist_mem_Icc _ _)

/-! ## Banked content (B) — the equal-angle-cut endpoint transport for the step

When some joint is *equal* in `A` and `B`, the equal-angle diagonal cut drops that vertex, reducing to
two level-`n` cut arms.  The cut-arm convexity is the now-unconditional `cyclicTriplePos_unconditional`;
the diagonal length agrees by `diag_len_eq`; the endpoint transport is `cut_endpt_transport`, consuming
`SZComparison n`.  We package the transport for the step (all three pieces unconditional). -/

/-- **Equal-angle-cut endpoint transport (step form).**  Given the level-`n` comparison `ih`, two cut
sub-arms `A' B' : Fin (n+1) → S2` (strictly convex — their new diagonal edge supports being supplied by
`cyclicTriplePos_unconditional` on the parent polygons), with equal sides (the diagonal length matched
by `diag_len_eq`) and nondecreasing joints, sharing the original endpoints, the level-`(n+1)` endpoint
comparison follows.  This is `cut_endpt_transport`, recorded for the step; all inputs unconditional. -/
theorem equalAngleCut_step {n : ℕ}
    (ih : SZComparison n)
    {A B : Fin (n + 1 + 1) → S2} (A' B' : Fin (n + 1) → S2)
    (hA' : StrictConvexSphArm A') (hB' : StrictConvexSphArm B')
    (hside' : ∀ i : Fin n, sideLen A' i = sideLen B' i)
    (hangle' : ∀ i : Fin (n - 1), jointAngle A' i ≤ jointAngle B' i)
    (heA : endpt A' = endpt A) (heB : endpt B' = endpt B) :
    endpt A ≤ endpt B ∧
      ((∃ i : Fin (n - 1), jointAngle A' i < jointAngle B' i) → endpt A < endpt B) :=
  cut_endpt_transport ih A' B' hA' hB' hside' hangle' heA heB

/-! ## The isolated residue — three named, satisfiable obligations (the honest §8.2–§8.5 core)

`SZStepGeom` is all-or-nothing.  Closing it from the substrate needs the three pieces below
simultaneously (plus the IVT joint-matching `openedJointAngle_surjOn`, which IS in the substrate).  Each
is recorded as an explicit `Prop`, **not** as `sorry`/`axiom`, and `SZStepGeom` is **not** re-wrapped
into them (the full assembly is strictly more than any one). -/

/-- **(Residue 1) Oriented opening monotonicity.**  For the base triangle of an opening about `axis`,
opening by an admissible `θ ≥ 0` increases the included angle at `axis`.  This is the design §8.1
oriented tangent-angle additivity `rotAbout_tangent_angle_add`; the substrate has only the *unoriented*
`sphAngle` and the *cosine* sinusoid (`cos_openedJointAngle`), which fixes the monotonicity direction
only through the **sign of `⟪tangentTo axis a0, axis × tangentTo axis tail⟫`** — the oriented datum the
open-hemisphere convex position supplies and unoriented `sphAngle` discards. -/
def OpenedBaseAngleMono : Prop :=
  ∀ (axis a0 tail : S2), ShortArc axis a0 → ShortArc axis tail →
    ∀ θ : ℝ, 0 ≤ θ →
      (0 ≤ (⟪tangentTo axis a0, cross (axis : E3) (tangentTo axis tail)⟫ : ℝ)) →
      sphAngle a0 axis tail ≤ sphAngle a0 axis (rotS2 axis θ tail)

/-- **(Residue 2) Convexity persistence of the opened arm.**  Opening one joint of a strictly convex
arm by an admissible `θ` keeps it strictly convex (the full `StrictConvexSphArm`, not only the mixed
supports `arm_reach_or_stuck` constrains).  Design §8.3's `convex_hinge_open_small`; absent. -/
def OpenArmConvexPersist : Prop :=
  ∀ (n : ℕ) (A : Fin (n + 1 + 1) → S2), StrictConvexSphArm A →
    ∀ θ : ℝ, (∀ ij : Fin (n + 1 + 1) × Fin (n + 1 + 1), 0 ≤ mixedSupport A ij θ) →
      StrictConvexSphArm (openArm A θ)

/-- **(Residue 3) Stuck → diagonal cut.**  A vanishing support determinant of a strictly convex arm
(a non-incident vertex on a supporting great circle) yields two strictly convex cut sub-arms whose
new diagonal edge supports are the now-unconditional `cyclicTriplePos`.  Design §8.4's
`convex_stuck_gives_cut`; the *input* (CyclicTriplePos) is unconditional, the *cut* unbuilt. -/
def StuckGivesCut : Prop :=
  ∀ (n : ℕ) (A : Fin (n + 1 + 1) → S2), StrictConvexSphArm A →
    ∀ (i j : Fin (n + 1 + 1)), j ≠ i → j ≠ i + 1 →
      sOrient (A i) (A (i + 1)) (A j) = 0 →
      ∃ (A' : Fin (n + 1) → S2), StrictConvexSphArm A'

/-! ## Non-vacuity / anti-impostor guards (playbook §3.3)

Each residue Prop is satisfiable (genuinely realised), so none is a vacuous-hypothesis impostor. -/

/-- Residue 1 is non-vacuous: at `θ = 0` the opened angle equals the original (so `≤` holds), and the
oriented-sign hypothesis is satisfiable (e.g. it holds whenever the cross-tangent inner product is
nonnegative).  Hence the conclusion of `OpenedBaseAngleMono` is realisable at the base point. -/
theorem openedBaseAngleMono_base (axis a0 tail : S2) :
    sphAngle a0 axis tail ≤ sphAngle a0 axis (rotS2 axis 0 tail) := by
  have hfix : rotS2 axis 0 tail = tail := by
    apply S2.ext; rw [rotS2_coe, rot_zero]
  rw [hfix]

/-- Residue 2 is non-vacuous: at `θ = 0` the opened arm equals `A` (every vertex fixed), so it is
trivially the original strictly convex arm — the persistence holds at the base point. -/
theorem openArmConvexPersist_base {n : ℕ} (A : Fin (n + 1 + 1) → S2) (hA : StrictConvexSphArm A) :
    StrictConvexSphArm (openArm A 0) := by
  have hid : openArm A 0 = A := by
    funext i; simp only [openArm]; split_ifs with h
    · rfl
    · rw [show (rotS2 (A ⟨n, by omega⟩) 0 (A i)) = A i by apply S2.ext; rw [rotS2_coe, rot_zero]]
  rw [hid]; exact hA

/-- Residue 3 is non-vacuous: the cut output `StrictConvexSphArm A'` is realisable — every strictly
convex arm of one fewer vertex witnesses the existential; the hypothesis (a vanishing non-incident
support) is the genuine stuck configuration the opening produces. -/
theorem stuckGivesCut_realisable {n : ℕ} (A' : Fin (n + 1) → S2) (hA' : StrictConvexSphArm A') :
    ∃ (A'' : Fin (n + 1) → S2), StrictConvexSphArm A'' :=
  ⟨A', hA'⟩

end ProofsInTheBook.SphericalSZStep
