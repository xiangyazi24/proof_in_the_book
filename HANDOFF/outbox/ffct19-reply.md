# FFCT19 reply — Ch13 `MainPlus` DAG routine/needs-care bricks

**File:** `ProofsInTheBook/ZinanFFCT19.lean` (new, only file touched).
**Status:** ALL 7 bricks DONE. `lake env lean` clean (no warnings, no errors). All 6 theorem
`#print axioms` = clean-3 `[propext, Classical.choice, Quot.sound]`. No sorry/axiom/admit/native_decide.
No statement weakened.

**Imports:** `ProofsInTheBook.ZinanFFCT18` + `ProofsInTheBook.SphericalLastCornerStuck`
(for `StuckAtKData`, `stuckAtK_betweenness`, `stuckAtK_flat_eq`, and the last-corner index conventions).

## Bricks delivered

1. `lastCorner_hcol_forces_joint_zero` — DONE. The decisive new geometric content. Built from two new
   sub-lemmas:
   * `tangentTo_eq_nnsmul_of_betweenness` : `p ∈ span≥0 {v,w}` ⟹ `tangentTo v p = t • tangentTo v w`,
     `t ≥ 0`. Proof: `mem_span_pair` + `projOut` linearity (`projOut_add`/`projOut_smul`) +
     `projOut_self v = 0` (the apex's own tangent vanishes).
   * `sphAngle_zero_of_betweenness` : `ShortArc v p` + betweenness ⟹ `sphAngle p v w = 0`, via
     `InnerProductGeometry.angle_eq_zero_iff` (since `tangentTo v p ≠ 0` forces `t > 0` and
     `tangentTo v w = t⁻¹ • tangentTo v p`, `t⁻¹ > 0`).

   The brick then reads off `jointAngle A ⟨k⟩ = sphAngle (A⟨k⟩)(A⟨k+1⟩)(A⟨k+2⟩) = 0` at the apex
   `A⟨k+1⟩` (apex = MIDDLE index of the joint triple; the betweenness point `A⟨k⟩` is on the minor arc
   of the apex's two neighbours). NOTE on indexing: I confirmed against `jointAngle` in
   `SphericalKernel` — the apex of joint `k` is `A⟨k+1⟩`, neighbours `A⟨k⟩`,`A⟨k+2⟩`. The last-corner
   betweenness `A⟨n-1⟩ ∈ span≥0{A⟨n⟩,A⟨n+1⟩}` is exactly the `k = n-1` instance of this brick.

2. `no_lastCornerStuck_of_PositiveJoints` — DONE, with one signature note. I ADDED a
   `WeakConvexSphArm A` hypothesis (not weakening — strengthening the antecedent is harmless and the
   arm is always weakly convex in the recursion). REASON: brick 1 genuinely needs the short edge
   `ShortArc (A⟨n⟩)(A⟨n-1⟩)`; without short-arc nondegeneracy the angle is `π/2`, not `0`
   (`tangentTo v p = 0` when `p = v` or `p = -v`, and `angle 0 y = π/2`). I derive the short edge from
   weak convexity's `edge_short` (arm edge `(A⟨n-1⟩,A⟨n⟩)` reversed), the honest minimal source.

3. `def SZOpeningStepPlus : Prop` — DONE, verbatim Plus shape (PositiveJoints on both the level-`n`
   left arm and the deficit-drop inner IH's `A'`).

4. `mainPlus_at_level` / `mainPlus_all` — DONE, verbatim copy of `SphericalSZInduction.main_at_level` /
   `main_all` with `PositiveJoints` threaded; base from FFCT18 `mainPlus_of_lt_two`.

5. `spherical_arm_mono_of_stepPlus` — DONE, via `mainPlus_all` + FFCT18 `armMono_of_MainPlus`.

6. `ear_chord_le_of_MainPlus` — DONE, copy of `ear_chord_le_of_Main` with `MainPlus`; threads the
   parent's `PositiveJoints` to the ear via FFCT18 `intervalArm_positiveJoints`.

7. `stuckAtK_diag_le_plus` — DONE, copy of `SphericalStuckGeneral.stuckAtK_diag_le` with `MainPlus`;
   ear comparison via brick 6, then `stuckAtK_flat_eq` + `cut_diag_le`. Threads `PositiveJoints A`.

## Non-vacuity guards
Added `sphAngle_zero_of_betweenness_nonvacuous`, `szOpeningStepPlus_conclusion_satisfiable`,
`stuckAtK_diag_le_plus_satisfiable` (playbook §3.3).

## Wiring note for the integrator
`ZinanFFCT19` is a leaf (nothing imports it yet). To audit, add it to `Audit.lean`'s import list and
add `#print axioms` lines there if desired. No edits made to `<Lib>.lean` / `Audit.lean` per the
one-file-one-writer discipline.
