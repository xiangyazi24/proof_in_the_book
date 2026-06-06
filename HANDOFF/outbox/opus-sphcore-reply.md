# SphericalCore — opening substrate for `SZOpeningCore` (opus reply)

**Status: DELIVERED, clean compile, 0 sorry / 0 axiom / 0 admit / 0 native_decide.**
File: `ProofsInTheBook/SphericalCore.lean` (325 lines, NEW, untracked on `main`, no commit per rules).
Imports `ProofsInTheBook.SphericalSZ`; reuses the proven rotation engine + SZ foundation.

**Honest headline:** the named primitive `ProofsInTheBook.SphericalSZ.SZOpeningCore` is **NOT yet
discharged**. What I did deliver is a strictly larger, fully-verified substrate beneath it — the
rotation-invariance of the support determinant, the concrete opening operation with full
side-length preservation, the opened-joint realisation law, and the engine's `reach_or_stuck`
instantiated on the arm's concrete support family — together with the explicit chain to the chapter's
kernel obligation. I did **not** fake, wrap, or rename the gap (an initial `SZOpeningStep := hcore`
re-wrapper was written and then **removed** as banking per playbook §2.6/§3.3).

## Verification (EXCLUSIVELY on uisai1 — nothing built/run locally; Mac kernel-panic rule honoured)

- `lake env lean ProofsInTheBook/SphericalCore.lean` → EXIT 0, zero errors.
- `lake build ProofsInTheBook.SphericalCore` → **Build completed successfully (8426 jobs).**
- `#print axioms` (from rebuilt oleans) on all 12 headline results → every one depends ONLY on
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no `ofReduceBool`/`native_decide`.
  Checked: `rot_cross`, `det3_rot_rot_rot`, `sOrient_rotS2`, `tangentTo_rotS2_axis`,
  `inner_tangent_opened`, `openArm_sideLen`, `sDist_axis_openLast`, `sOrient_openArm_fixed`,
  `sOrient_jointlyRotated`, `continuous_mixedSupport`, `arm_reach_or_stuck`,
  `schoenbergZaremba_of_openingCore`.
- `grep sorry|admit|axiom|native_decide` in code → none.
- Local and remote `SphericalCore.lean` md5-identical (`cdcc3c11…`). Root `ProofsInTheBook.lean`
  untouched (not my file).
- Dependency oleans verified md5-identical local/remote before building; numerical + symbolic
  (sympy, reduced mod the unit-axis + Pythagorean ideal) pre-checks done for `rot_cross` /
  det-invariance before formalising (playbook simulation-first).

## What is proved UNCONDITIONALLY (genuine new content above the engine)

1. **Rotation-invariance of the support determinant** — the convexity-persistence fact the engine
   lacked (it had *no* det-algebra).
   - `rot_cross` : `rot k θ (a × b) = (rot k θ a) × (rot k θ b)` for a unit axis. Proven coordinate-
     wise by `ext_coord` + per-coordinate `linear_combination` against `‖k‖²=1` and `cos²+sin²=1`
     (the exact multipliers obtained from a sympy ideal reduction, verified numerically first).
   - `det3_rot_rot_rot` : `det3 (rot a)(rot b)(rot c) = det3 a b c`, via the triple-product bridge
     `det3 x y z = ⟪x, y×z⟫` + `rot_cross` + `inner_rot_rot`.
   - `sOrient_rotS2` : the same for the kernel's `sOrient`. **Hence tail-internal and head-internal
     `sOrient` support triples are `θ`-INVARIANT** — they stay nonneg from the initial arm, so only
     the mixed triples + the target bound are genuine `θ`-dependent constraints (the design's split).

2. **The opened-joint realisation law** (axis = base vertex).
   - `tangentTo_rotS2_axis` : `tangentTo k (rotS2 k θ q) = rot k θ (tangentTo k q)` (axis fixed by
     `rot`, inner products preserved) — the variant of `tangentTo_rotS2` for a *rotated target,
     fixed base*, which is the opening's actual geometry.
   - `inner_tangent_opened` : the cosine-numerator of the opened joint moves by the planar-rotation
     formula `cos θ · ⟪u,w⟫ + sin θ · ⟪u, k×w⟫` of the two fixed tangents (the analytic content of
     "opening realises every intermediate joint value").

3. **The concrete opening operation** `openArm A θ` (rotate only the tail vertex `n+1` about the axis
   vertex `n`, fix the rest), with:
   - `openArm_sideLen` : **every side length preserved** — prefix sides untouched; the final side has
     the axis as one endpoint (fixed by `rot`), preserved via `inner_rot_axis` (`sDist_axis_openLast`).
   - `openArm_fixed`/`openArm_last`/`openArm_zero` : the vertex bookkeeping.

4. **Convexity persistence of the invariant triples** for the concrete opening:
   `sOrient_openArm_fixed` (jointly-fixed triples verbatim) and `sOrient_jointlyRotated` (jointly-
   rotated triples via the invariance of (1)).

5. **The reach-or-stuck dichotomy on the arm's concrete support family:**
   `mixedSupport` (the finite family of `θ ↦ det3 (A i)(A j)(rot axis θ (A last))` mixed determinants),
   `continuous_mixedSupport` (each continuous, built explicitly from `continuous_rot_coord`), and
   `arm_reach_or_stuck` — the engine's `reach_or_stuck` instantiated on this concrete family: at the
   admissible supremum either the target is reached or some mixed support determinant vanishes (the
   stuck great-circle collinearity). This is the design §8.4 skeleton now carried on genuine arm data.

6. **Explicit chain:** `schoenbergZaremba_of_openingCore : SZOpeningCore → SchoenbergZarembaTarget`
   (re-export of the proven `SphericalSZ.schoenbergZaremba_of_core`).

## The single resistant residue (honest, after genuine effort) — `SZOpeningCore` itself

`SZOpeningCore` packages the §8 opening *output* in elementary form (the `StuckData`: the closing
support `det3 (A 0)(A 1) qstar = 0`, the two convex-position Gram signs, and the opening /
sub-comparison / equal-side bounds, under the inductive hypothesis `SZComparison n`). Discharging it
requires three things the present substrate does **not** yet mechanise, and which together are the
genuine geometric heart of the Schoenberg–Zaremba inductive step (design §8.2–§8.5):

- **(IVT realisation)** that the opened last joint, moving by `inner_tangent_opened` (a sinusoid in
  θ with constant norm), continuously *surjects* onto `[jointAngle A, π)` so the target `jointAngle B`
  is realised at some admissible θ (the *reached* case, then closed by `spherical_hinge_strict` + IH);
- **(the resistant sign case)** the precise convex-position sign derivation at the *tight* mixed
  constraint: at the admissible supremum where one mixed determinant vanishes, deriving `StuckData`'s
  two Gram signs `signA`, `signC` from the *still-valid* other mixed constraints (≥ 0 throughout the
  admissible interval). This is the one truly resistant bookkeeping step — the signs of the
  neighbouring Gram quantities at tightness — and is named here, not faked;
- **(the cut)** the equal-angle diagonal cut routing the equal-joint case to level `n`.

I did not bank or fake this: the `weak` half of `SZOpeningCore` is itself the monotone arm lemma (not
separately cheap), and there is **no honest strictly-smaller primitive** to reduce it to — `StuckData`
(det3 + signs) is already the most elementary form, so any "reduction" to a renamed predicate would be
a trivial re-wrapper (which I removed). `SZOpeningCore` remains the open obligation, now resting on the
enlarged substrate above; the four §8 sub-facts (realisation surjectivity, the convex-position sign
derivation at tightness, the cut, and threading the IH) are what close it.

## Non-vacuity / anti-impostor (playbook §3.3)

- `SZOpeningCore`'s stuck condition `det3 (A 0)(A 1) qstar = 0` is satisfiable — every great-circle
  betweenness realises it (`SphericalSZ.det_zero_of_betweenness`, already in the dep file). So the
  obligation is not a vacuous (unsatisfiable-hypothesis) impostor.
- No `def : Prop` impostor for any unproved goal; the only `def : Prop` referenced (`SZOpeningCore`)
  lives in the dependency, is an honest named obligation, and is NOT claimed proved.
- `schoenbergZaremba_of_openingCore` is a genuine implication (real content in the deps), not a
  re-statement of its hypothesis.

## Honest classification

- `rot_cross`, `det3_rot_rot_rot`, `sOrient_rotS2`, `tangentTo_rotS2_axis`, `inner_tangent_opened`,
  `openArm_sideLen`, `sDist_axis_openLast`, `sOrient_openArm_fixed`, `sOrient_jointlyRotated`,
  `continuous_mixedSupport`, `arm_reach_or_stuck` : **FAITHFUL, UNCONDITIONAL** new content.
- `schoenbergZaremba_of_openingCore` : **FAITHFUL** implication (CONDITIONAL-honest chain link).
- `SZOpeningCore` : **OPEN** — honestly not discharged this round.

## Chapter 13's remaining frontier

1. **`SZOpeningCore`** — the §8.2–§8.5 finish: IVT realisation surjectivity of the opened joint, the
   convex-position sign derivation at the tight mixed constraint (the named resistant sign case), the
   equal-angle cut, and threading `SZComparison n`. Discharging it (with this module's substrate)
   makes `SZGeom` → `SchoenbergZarembaTarget` → `spherical_arm_mono`/`_strict` **unconditional**.
2. **The vertex-link correspondence** (design §9–§12): the Cauchy bridge identifying each convex-
   polyhedron vertex link with a `StrictConvexSphArm`, so the spherical arm lemma drives Cauchy's
   rigidity theorem — the chapter's top-level goal.
