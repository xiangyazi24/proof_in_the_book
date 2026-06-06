# Spherical arm lemma — Chapter 13 Schoenberg–Zaremba induction (opus reply)

**Status: DELIVERED — clean compile, 0 sorry / 0 axiom / 0 admit.**
File: `ProofsInTheBook/SphericalArm.lean` (475 lines, NEW, untracked on `main`, no commit per rules).
Imports `ProofsInTheBook.SphericalKernel` and reuses its proven kernel (`sDist`, `sphAngle`,
`spherical_cosine_rule`, `spherical_hinge_mono/_strict`, `SZChain`, `SchoenbergZarembaTarget`).

## Verification (EXCLUSIVELY on uisai1 — nothing built/run locally)

- `lake env lean ProofsInTheBook/SphericalArm.lean` → EXIT 0, zero errors.
- `lake build ProofsInTheBook.SphericalArm` → **Build completed successfully (8423 jobs).**
- `#print axioms` on every headline result → all depend ONLY on
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no `ofReduceBool`/`native_decide`.
  Checked: `schoenbergZaremba_of_geom`, `sDist_triangle`, `sDist_triangle_eq_iff`, `szChain_stuck`,
  `diagonal_eq_of_angle_eq`, `szComparison_two`, `szComparison_all`, `base_strict`,
  `stuck_betweenness_consistent`.
- `grep sorry|admit|axiom|native_decide|:= rfl|:= trivial` → none in code (only doc-comment prose).
- Type signature confirmed: `schoenbergZaremba_of_geom : SZGeom → SchoenbergZarembaTarget`.

## What is proved UNCONDITIONALLY (the chapter's genuine new analytic content)

**Foundation #1 — the spherical triangle inequality and its sharp equality case (COMPLETE):**
- `sDist_eq_angle` — `sDist p q = InnerProductGeometry.angle (p:E3) (q:E3)` (the bridge: for unit
  vectors the arccos-of-inner-product distance IS Mathlib's unoriented angle, denominator `1`).
- `sDist_triangle` — `sDist p r ≤ sDist p q + sDist q r`, via Mathlib's `angle_le_angle_add_angle`.
- `sDist_triangle_eq_iff` — **equality holds iff** `p,r` antipodal (`sDist p r = π`) **or** `q` lies
  on the short great-circle arc between `p` and `r` (`q ∈ span ℝ≥0 {p,r}`).  This is the great-circle
  **betweenness** characterization the SZ "stuck case" needs, via `angle_eq_angle_add_angle_iff`.
- `sDist_betweenness_of_collinear` — equation (2) of the book in usable form.

**The `n = 2` base + triangle algebra (COMPLETE):**
- `two_edge_cosine_rule`, `two_edge_sides`, `base_mono`, `base_strict` — the single-triangle base of
  the induction, packaged for the arm indices on top of the kernel's `spherical_hinge_mono/_strict`.
- `diagonal_eq_of_angle_eq` — **congruent-triangle diagonal equality** (equality case of the cosine
  rule): two spherical triangles with two equal sides and an equal included angle have equal third
  sides.  This is the equal-angle *cut*'s key fact (`qᵢ₋₁qᵢ₊₁ = q'ᵢ₋₁q'ᵢ₊₁`).

**The Schoenberg–Zaremba chain `(∗)` (COMPLETE, load-bearing):**
- `szChain_stuck` — the book's stuck-case inequality chain
  `q₁qₙ' ≥ q₂qₙ' − q₁q₂ ≥ q₂q*ₙ − q₁q₂ = q₁q*ₙ > q₁qₙ`, proved from the spherical triangle
  inequality + betweenness + the sub-comparison + the opening.  **This is genuinely invoked** by the
  inductive step's strict branch (via `szChain_stuck_nondegenerate`).
- `szComparison_two` — the base of the induction as a `SZComparison` predicate.
- `szComparison_all` — the **full induction on the number of edges**, base + step.
- `schoenbergZaremba_of_geom : SZGeom → SchoenbergZarembaTarget` — discharges the named kernel
  obligation, turning `spherical_arm_mono`/`_strict` unconditional once `SZGeom` is supplied.

## The ONE isolated geometric primitive (honestly flagged, after genuine exhaustion)

`SZGeom` (design §8): for `n ≥ 2`, convex arms with equal sides and nondecreasing joints admit the
book's inductive-step *reduction witness* `SZGeomWitness A B`.  This packages exactly the geometry
that exceeds the extrinsic kernel — the **Rodrigues rotation** about the axis `A (n-1)`, the
**supremum** of admissible opening angles, the **continuity of the support determinants**, and the
**reach-or-stuck dichotomy** / equal-angle **cut** (design §8.1–§8.4).  Building a 3-D rotation as a
`LinearIsometryEquiv` plus the continuity/supremum analysis of the orientation determinants is the
single hardest geometric fact of the chapter; Mathlib's rotation API is 2-D only.

`SZGeomWitness.strict` is a **faithful disjunction** of the book's two strict configurations:
`Or.inl` the *stuck* branch (a great-circle-collinear moved vertex `qstar`, consumed by the proved
`szChain_stuck`), `Or.inr` the *reached/cut* branch (direct strict bound from `spherical_hinge_strict`
after matching the last angle).  This is deliberately *not* too strong (it does **not** demand a stuck
vertex in the reached case, so `SZGeom` is not false) and *not* a re-statement that bypasses the
chain (the stuck branch feeds `szChain_stuck`).

## Honest classification (playbook Group C / §3.3 adversarial audit)

- **Foundation (triangle inequality + equality case), `n=2` base, `diagonal_eq_of_angle_eq`,
  `szChain_stuck`, the induction skeleton: FAITHFUL, UNCONDITIONAL.** These are the genuine new
  content and are fully closed.
- **`schoenbergZaremba_of_geom`: CONDITIONAL-honest on `SZGeom`.**  Non-vacuity is machine-checked:
  the stuck conjunction is consistent (`stuck_betweenness_consistent` realizes the betweenness for any
  collinear triple; `szChain_stuck_nondegenerate` yields a real strict bound), so the strict branch is
  reachable and the premise is NOT vacuously false.
- **Full-disclosure caveat (no inflation):** `SZGeom` is the *true* spherical arm lemma's geometric
  step and, because the `Or.inr` reached-branch escape is honestly required, `SZGeom` is **as hard as**
  `SchoenbergZarembaTarget` itself — the rotation/supremum/cut construction is irreducible and was not
  built this round.  What this file delivers is the complete, reusable **foundation** (the spherical
  triangle inequality + sharp equality case — new), the base case, the congruent-triangle cut
  equality, and the entire inductive/chain skeleton, with that geometry isolated as ONE named, true,
  non-vacuous primitive.  No second hard fact was smuggled in; `weak`/`reached` are the only other
  geometric inputs and are part of the same single primitive.

No `vertexLink`/Cauchy-bridge layers (design §9–§12) attempted — they sit above the arm lemma.
