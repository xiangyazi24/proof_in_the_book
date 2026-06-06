# opus-hingecut-reply — Chapter 13 §8.1–§8.4 hinge/cut machinery

Status: **TARGET (`szStepGeom_holds : SZStepGeom` unconditional) NOT CLOSED.**  The §8.1 keystone
(oriented opening monotonicity) is **proved** in corrected form; the §8.3 persistence and §8.4 cut
substrate are **proved**.  The irreducible residue is precisely isolated as ONE named, satisfiable
`Prop` (`DiagonalCutArm`).  File: `ProofsInTheBook/SphericalHingeCut.lean` — compiles, RC=0, no
sorry/axiom/admit/native_decide.

## CRITICAL CORRECTION (verified, not impression): the three literal Props are flawed

I read `SphericalSZStep.lean` line by line.  All three literal residue Props are mathematically wrong
or disconnected **as written** — which is exactly why they could not drive the assembly:

1. **`OpenedBaseAngleMono` is FALSE as written.**  It requires `0 ≤ ⟪u, axis×w⟫` and *unrestricted*
   `θ ≥ 0`.  The opened-angle cosine is `(c cos θ + s sin θ)/N` with `c=⟪u,w⟫`, `s=⟪u,axis×w⟫`,
   `N=‖u‖‖w‖` (this much is `cos_openedJointAngle` + norm-constancy).  For `s>0` the angle *decreases*
   first: e.g. `c=0, s>0, θ=π/2` gives a strictly smaller angle.  Numerically + analytically verified.
   The genuine §8.1 monotonicity needs the **opposite sign** `⟪u,axis×w⟫ ≤ 0` **and** the range
   `θ + sphAngle a0 axis tail ≤ π` (the opened angle is `arccos((N/?)cos(φ₀+θ))`, monotone only while
   `φ₀+θ ≤ π`).
2. **`OpenArmConvexPersist` is FALSE as written.**  It concludes `StrictConvexSphArm (openArm A θ)`
   from only `0 ≤ mixedSupport A ij θ`, but at a boundary `θ` where a mixed support equals `0` the
   `strict_nonincident` (`>0`) field fails.  The genuine §8.3 fact is the **strict-neighbourhood**
   statement.
3. **`StuckGivesCut` as written** (`∃ A' : Fin (n+1)→S2, StrictConvexSphArm A'`) is disconnected from
   `A` and the cut — any one-vertex-fewer convex arm witnesses it (cf. its own non-vacuity
   `stuckGivesCut_realisable`).  The genuine §8.4 cut must produce sub-arms *of `A`* with matched data.

I therefore did **not** bank the literal Props (proving a false statement is impossible; proving the
trivial one is a no-op).  I proved the **corrected, genuinely-true** versions instead.

## What is PROVED (genuine new content, all clean-3)

* `tangentPlane_pythag` — the tangent-plane Pythagorean identity `⟪u,w⟫²+⟪u,k×w⟫²=‖u‖²‖w‖²` for
  `u,w ⟂` unit `k` (via `u×w ∥ k`, `eq_smul_axis_of_cross_zero`, `inner_axis_sq_eq_norm_sq`, Lagrange
  `norm_sq_cross`).  This is what writes the opening sinusoid as a single shifted cosine.
* **§8.1 KEYSTONE — `cos_open_le_cos_orig` / `openedAngle_ge_of_oriented`** (the corrected oriented
  monotonicity the design flagged as the keystone): with `⟪tangentTo axis a0, axis×tangentTo axis tail⟫
  ≤ 0`, `0 ≤ θ`, and `θ + sphAngle a0 axis tail ≤ π`, the opened joint angle dominates the original.
  Proof: sinusoid `= N cos(φ₀+θ)` (from `c=N cosφ₀`, `s=-N sinφ₀` via `tangentPlane_pythag` + sign),
  then `cos` antitone on `[0,π]`.
* **§8.3 — `strictSupport_persists` / `mixedSupport_persists`** (the corrected convexity persistence):
  a finite family of continuous supports, strict at `θ₀`, stays strict on an `ε`-ball — the genuine
  `convex_hinge_open_small` for the concrete `mixedSupport` family.
* **§8.4 cut substrate — `cut_diagonal_supports`, `cut_subseqDiag_supports`, `cut_corner_signs`**: the
  new diagonal edge of a cut sub-arm supports every retained vertex, and the cut-corner sign pattern
  (HINGE 11.3 determinant form), all UNCONDITIONAL via `cyclicTriplePos_unconditional`.
* **§8.5 — `equalAngleCut_transport_step`**: the equal-angle cut endpoint transport given the IH
  (`cut_endpt_transport`).

## The precise irreducible residue (honest, after genuine exhaustion)

Closing `SZStepGeom` needs, in the strict-joint case, opening to the admissible supremum then the §8.4
reach/stuck/cut trichotomy.  With the keystone + persistence + cut-supports proved, the single residue
that genuinely resists is the **diagonal-cut sub-arm construction** — isolated as the named, satisfiable
`Prop` **`DiagonalCutArm`** (with witness `diagonalCutArm_payload_realisable`).  Two facts are absent
from the entire substrate (verified by `grep`: no `cutArm`/`SubArm`/`Fin.succAbove`-reindex/oriented
cut-corner additivity anywhere):

1. the `Fin (n+1)`-subfamily re-indexing of the two cut arms and transport of all four
   `StrictConvexSphPolygon` fields across it (the new diagonal edge support being the only nontrivial
   one — certified by `cut_diagonal_supports`);
2. the **oriented cut-corner tangent-angle additivity** at the two new corners (the *oriented*
   generalisation of the keystone: the diagonal ray splits the corner angle additively), whose sign
   input is `cut_corner_signs` but whose additive identity is a separate oriented-`oangle` development.

This is exactly the design §8.4 "THE hard theorem", and `SphericalHinge.TerminalVisibility` (proved NOT
implied by strict convexity, §6 counterexample) confirms the stuck support need not be terminal — so the
cut is unavoidable and is genuine multi-vertex convex-position geometry (gnomonic / planar-convex-
position with total turning `< π`), a multi-hundred-line build absent from the substrate.  `DiagonalCutArm`
is **not** a co-extensive re-wrapper of `SZStepGeom` (it is strictly the cut core; the opening, the reach
branch, the equal-angle branch, the IVT matching `openedJointAngle_surjOn`, and the endpoint glue are all
strictly extra), and **not** faked.  This matches the verdict of the two prior expert rounds
(`opus-szstep-reply`, `opus-szchain-reply`).

## Verification

* `lake env lean ProofsInTheBook/SphericalHingeCut.lean` → RC=0.
* `lake build ProofsInTheBook.SphericalHingeCut` → Build completed successfully (8435 jobs).
* `grep -nE '\bsorry\b|\badmit\b|^axiom |native_decide'` → 1 hit, inside the doc comment prose; 0 in
  code.
* `#print axioms` (rebuilt oleans) — clean-3 `[propext, Classical.choice, Quot.sound]` on every proved
  theorem: `openedAngle_ge_of_oriented`, `cos_open_le_cos_orig`, `tangentPlane_pythag`,
  `mixedSupport_persists`, `strictSupport_persists`, `cut_diagonal_supports`, `cut_corner_signs`,
  `equalAngleCut_transport_step`.

## Net effect on the chapter

The §8.1 keystone the design flagged as the linchpin is now proved (in corrected form), together with
the §8.3 persistence and the §8.4 cut-support certificates.  The arm lemma remains conditional on the
single named primitive `DiagonalCutArm` (the cut-construction core) — strictly narrower than the prior
`SZStepGeom`/`OpenedArmReachOrStuck`, since the opening, reach, equal-angle and glue layers are now all
discharged or reduced to it.  The unconditional `spherical_arm_mono(_strict)` is therefore **not** yet
delivered; the honest residue is `DiagonalCutArm` (the Fin-subfamily cut + oriented cut-corner additivity).
