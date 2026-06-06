# SZGeom engine — Rodrigues rotation / opening / reach-or-stuck (opus reply)

**Status: DELIVERED — clean compile, 0 sorry / 0 axiom / 0 admit / 0 native_decide.**
File: `ProofsInTheBook/SphericalRotation.lean` (489 lines, NEW, untracked on `main`, no commit per
rules).  Imports `ProofsInTheBook.SphericalArm`; reuses its kernel + the proven SZ foundation.

## Verification (EXCLUSIVELY on uisai1 — nothing built/run locally)

- `lake env lean ProofsInTheBook/SphericalRotation.lean` → EXIT 0, zero errors.
- `lake build ProofsInTheBook.SphericalRotation` → **Build completed successfully (8424 jobs).**
- `#print axioms` (from rebuilt oleans) on every headline result → all depend ONLY on
  `[propext, Classical.choice, Quot.sound]`.  No `sorryAx`, no `ofReduceBool`/`native_decide`.
  Checked: `inner_rot_rot`, `rot_comp`, `norm_rot`, `sDist_rotS2`, `sphAngle_rotS2`,
  `tangentTo_rotS2`, `norm_sq_cross`, `inner_cross_eq_det3`, `reach_or_stuck`,
  `sSup_mem_admissibleSet`, `continuous_det3_rot`, `hinge_preserves_sideLen_suffix`,
  `schoenbergZaremba_of_opening`.
- `grep sorry|admit|axiom|native_decide` → none in code.  (`:= rfl` lines are all genuine
  definitional unfoldings of `cross`/`rot`/coordinate access — not trivially-true impostor theorems.)

## What is proved UNCONDITIONALLY (the chapter's geometric engine — genuine new content)

**Cross-product algebra (the kernel had `det3`; this builds the vector cross product):**
- `cross` over `EuclideanSpace ℝ (Fin 3)` in explicit coordinates; bilinearity, `cross_self`,
  `cross_antisymm`, `cross_smul_left/right`.
- `inner_cross_left/right` (`⟪a×b,a⟫ = ⟪a×b,b⟫ = 0`), **`inner_cross_eq_det3`** (the triple product
  `⟪a, b×c⟫ = det3 a b c` — the bridge to the kernel's orientation), `inner_cross_cyclic`,
  **`norm_sq_cross`** (Lagrange: `‖a×b‖² = ‖a‖²‖b‖² − ⟪a,b⟫²`), `cross_cross` (bac−cab),
  **`inner_cross_cross`** (Binet–Cauchy).

**Rodrigues rotation `rot k θ v = cos θ•v + sin θ•(k×v) + (1−cos θ)•⟪k,v⟫•k` (unit axis):**
- `rot_add`, `rot_smul`, `rot_sub`, `rot_zero` (`rot k 0 = id`), `rot_axis` (`rot k θ k = k`).
- `inner_rot_axis` (`⟪rot v, k⟫ = ⟪v,k⟫`).
- **`inner_rot_rot` (THE CRUX): `⟪rot k θ v, rot k θ w⟫ = ⟪v,w⟫`.**  Proved by full bilinear
  expansion using Binet–Cauchy + `⟪k×v,k⟫=0` + mixed-term antisymmetry, closed with one
  `linear_combination (⟪v,w⟫ − ⟪k,v⟫⟪k,w⟫) * (cos²+sin²=1)`.  This is the load-bearing identity.
- `norm_rot` (`‖rot v‖ = ‖v‖`, hence maps `S²`→`S²`), **`rot_comp`** (group law
  `rot θ ∘ rot θ' = rot (θ+θ')`, via `cross_cross` + angle-addition + `module`), `continuous_rot`.

**The opening operation on `S²` (`rotS2`) — the hinge isometry:**
- **`sDist_rotS2`**: `sDist (rot p) (rot q) = sDist p q` — the opening preserves every side length.
- `tangentTo_rotS2`: tangents commute with `rot`; **`sphAngle_rotS2`**: the opening preserves every
  spherical angle (so all joint angles except the opened one are fixed).
- `inner_rot_tangent`: the planar tangent-rotation law `⟪u, rot k θ w⟫ = cos θ⟪u,w⟫ + sin θ⟪u,k×w⟫`
  for tangents `w ⟂ k` — the analytic content of the linear angle action.
- **`continuous_det3_rot`**: `θ ↦ det3 (rot a)(rot b)(rot c)` continuous (support determinants).

**Admissible supremum + reach-or-stuck (design §8.4 — the analytic skeleton, COMPLETE):**
- `admissibleSet f T = {θ ∈ [0,T] : ∀ j, 0 ≤ f j θ}`; `isClosed_admissibleSet` (closed: finite
  intersection of `f_j ≥ 0` preimages ∩ `Icc`), `zero_mem_admissibleSet`, `admissibleSet_bddAbove`,
  `sSup_mem_admissibleSet` (the supremum is admissible: closed + nonempty + bounded ⇒ `csSup_mem`).
- **`reach_or_stuck`**: at the admissible supremum `s`, either `s = T` (**reached**) or some
  `f j s = 0` (**stuck**).  Proved: if `s < T` and all `f j s > 0`, each `f_j` stays positive on a
  right-neighbourhood `(s,T]` (continuity + `NeBot` of `𝓝[Ioc s T] s`), giving an admissible point
  `> s`, contradicting `s = sSup`.  This is the exact "great-circle collinearity emerges" dichotomy.

**Hinge move (design §8.2):**
- `HingeMove A B k θ` (prefix fixed, suffix `= rot (A k) θ`); `hinge_preserves_sideLen_suffix` and
  `hinge_preserves_sideLen_prefix` (every side length preserved), proved from `sDist_rotS2`.

## The ONE isolated primitive (honest, after genuine effort)

**`SZGeom` (of `SphericalArm`) is the single remaining geometric input.**  `schoenbergZaremba_of_opening
: SZGeom → SchoenbergZarembaTarget` re-exports the kernel obligation, now standing on the full
rotation/isometry/supremum engine proved here.

What `SZGeom` still assumes is the *geometric bookkeeping* of assembling the engine into the witness:
instantiating the support family by the arm's `sOrient` triples, identifying a vanishing support
determinant with the betweenness collinearity `(A 0 : E3) ∈ span ℝ≥0 {A 1, qstar}`, and the
equal-angle diagonal **cut** of §8.5.  This is the irreducible core the design flags as the chapter's
hardest fact (Mathlib's rotation API is 2-D only; the full 3-D induction with the cut exceeds one
round).  **No fake reduction was banked**: I explicitly removed a `SZOpeningData ↔ SZGeom := Iff.rfl`
re-wrapper as a vacuous re-statement; the only bridge to the kernel is the honest re-export, and every
other result is genuine unconditional content.

## Honest classification (playbook §3.3)

- **Cross-product algebra, Rodrigues rotation, `inner_rot_rot`, `rot_comp`, `norm_rot`, the `rotS2`
  isometry (`sDist_rotS2`/`sphAngle_rotS2`), continuity, the admissible-sup `reach_or_stuck`, the
  hinge side-length preservation: FAITHFUL, UNCONDITIONAL.**  This is the genuine geometric engine
  the book's opening construction runs on, fully closed.
- **`schoenbergZaremba_of_opening`: CONDITIONAL-honest on `SZGeom`** (re-export of the already-proven
  `schoenbergZaremba_of_geom`; non-vacuity of the strict branch is machine-checked in `SphericalArm`).
- **Full-disclosure caveat:** `SZGeom` itself (witness *existence* with the cut) is NOT proved this
  round; it remains the one isolated primitive, now supported by the proven engine rather than left
  bare.

## Chapter 13's remaining frontier (the last layer above the arm lemma)

1. **`SZGeom`** — assemble engine → witness: hinge-open one joint to the admissible supremum,
   instantiate `reach_or_stuck` on the `sOrient` triples, extract the great-circle collinearity from
   the vanishing `det3`, and the equal-angle diagonal cut (design §8.2–§8.5).  This discharges
   `SchoenbergZarembaTarget`, making `spherical_arm_mono`/`_strict` unconditional.
2. **The vertex-link correspondence** (design §9–§12): the Cauchy bridge identifying each convex
   polyhedron vertex link with a `StrictConvexSphArm`, so the (now unconditional) spherical arm lemma
   drives Cauchy's rigidity theorem — the chapter's top-level goal.
