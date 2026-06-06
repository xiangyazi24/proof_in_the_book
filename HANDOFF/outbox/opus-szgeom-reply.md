# SZGeom assembly — collinearity extraction + opening core (opus reply)

**Status: DELIVERED — clean compile, 0 sorry / 0 axiom / 0 admit / 0 native_decide.**
File: `ProofsInTheBook/SphericalSZ.lean` (248 lines, NEW, untracked on `main`, no commit per rules).
Imports `ProofsInTheBook.SphericalRotation`; reuses the proven rotation engine + the SZ foundation in
`SphericalArm`.

## Verification (EXCLUSIVELY on uisai1 — nothing built/run locally; Mac kernel-panic rule honoured)

- `lake env lean ProofsInTheBook/SphericalSZ.lean` → EXIT 0, zero errors.
- `lake build ProofsInTheBook.SphericalSZ` → **Build completed successfully (8425 jobs).**
- `#print axioms` (from rebuilt oleans) on every headline result → all depend ONLY on
  `[propext, Classical.choice, Quot.sound]`.  No `sorryAx`, no `ofReduceBool`/`native_decide`.
  Checked: `betweenness_span_nnreal`, `normsq_smul_b`, `cross_ne_zero_of_shortArc`, `szGeom_of_core`,
  `schoenbergZaremba_of_core`, `det_zero_of_betweenness`.
- `grep sorry|admit|axiom|native_decide` in code → none (only the docstring phrase "No sorry…").
  The single `:= rfl` (`⟪a,c⟫ = sInner a c`) is a genuine definitional unfolding, not an impostor.
- Local and remote `SphericalSZ.lean` md5-identical. Root `ProofsInTheBook.lean` untouched (not my file).

## What is proved UNCONDITIONALLY (genuine new content above the engine)

**The great-circle collinearity extraction — the geometric heart of the book's stuck case.**
The rotation engine left the bookkeeping "a vanishing support determinant ⟹ the betweenness
`(A 0 : E3) ∈ span ℝ≥0 {A 1, qstar}`" as the frontier. That is now proved from scratch:

- `crossw_eq` : `(a×c)×b = ⟪b,a⟫•c − ⟪b,c⟫•a` (specialised double-cross identity).
- `cross_lin` : bilinearity packaged for the chain.
- **`normsq_smul_b`** : the explicit coplanar decomposition — if `⟪a×c, b⟫ = 0` then
  `‖a×c‖²•b = (⟪b,a⟫⟪c,c⟫ − ⟪b,c⟫⟪a,c⟫)•a + (⟪b,c⟫⟪a,a⟫ − ⟪b,a⟫⟪c,a⟫)•c`.  Proved by the
  double-cross expansion `(a×c)×((a×c)×b) = ⟪a×c,b⟫•(a×c) − ‖a×c‖²•b` rewritten through `crossw_eq`,
  closed by `linear_combination ... module`.  This makes the Gram coefficients of a coplanar middle
  vertex fully explicit.
- `cross_ne_zero_of_shortArc` : a short arc has independent endpoints (`a×c ≠ 0`), via Lagrange
  (`norm_sq_cross`) + the short-arc nondegeneracy `⟪a,c⟫ ≠ ±1` (reusing the kernel's equal/antipodal
  characterisations).
- **`betweenness_span_nnreal`** : from `det3 b a c = 0`, `ShortArc a c`, and the two convex-position
  Gram signs, the coplanar middle `b ∈ span ℝ≥0 {a, c}` — exactly equation (2)'s betweenness.
  Dividing `normsq_smul_b` by `‖a×c‖² > 0` exhibits `b` as the nonnegative combination
  `b = (α/‖a×c‖²)•a + (β/‖a×c‖²)•c`.  (The NNReal membership is built directly via
  `Submodule.mem_span_pair`, no reliance on Mathlib's private angle-span helper.)

## The single isolated geometric primitive (honest, after genuine effort)

`SZOpeningCore` (`def : Prop`) packages **exactly** the raw output of the design §8 opening
construction — rotate the tail about the pivot to the admissible supremum, `reach_or_stuck` on the
`sOrient` triples — in the most **elementary** form:

- always the weak bound `endpt A ≤ endpt B`;
- whenever some joint of `B` is strictly wider, **either** a stuck vertex `qstar` with `StuckData`
  (short arc `A 1, qstar`; the bare determinant equation `det3 (A 0)(A 1) qstar = 0`; the two convex-
  position Gram signs; the opening / sub-comparison / equal-side bounds) **or** the direct strict
  endpoint bound (reached / equal-angle-cut case).

It deliberately states the stuck case through the bare `det3 = 0` + signs, **not** the `span ℝ≥0`
betweenness — that is *derived* by `betweenness_span_nnreal`.  So the primitive is strictly smaller
and more elementary than the old `SZGeom`, and the bridge is genuinely load-bearing.

- **`szGeom_of_core : SZOpeningCore → SZGeom`** — proved.  Forwards the weak bound; converts the
  stuck `StuckData` (det3 = 0 + signs) into the witness's `span ℝ≥0` betweenness via
  `betweenness_span_nnreal`; forwards the opening / sub-comparison / equal-side bounds into
  `SZGeomWitness.strict`'s `Or.inl`; forwards the reached/cut case as `Or.inr`.
- **`schoenbergZaremba_of_core : SZOpeningCore → SchoenbergZarembaTarget`** — composes the bridge
  with the proven `schoenbergZaremba_of_geom`.

## Non-vacuity guard (anti-impostor, playbook §3.3)

`det_zero_of_betweenness` proves the **converse** of the determinant extraction: every genuine
great-circle betweenness `A 0 = s•A 1 + t•qstar` satisfies `det3 (A 0)(A 1) qstar = 0`.  Hence the
central condition of `StuckData` is satisfiable — `SZOpeningCore` is not a vacuous
(unsatisfiable-hypothesis) impostor.  (`#print axioms` cannot detect an unsatisfiable premise; this
is the explicit satisfiability check the playbook requires for conditional theorems.)

## Honest classification (playbook §3.3)

- **`crossw_eq`, `cross_lin`, `normsq_smul_b`, `cross_ne_zero_of_shortArc`,
  `betweenness_span_nnreal`, `det_zero_of_betweenness`: FAITHFUL, UNCONDITIONAL.**  This is the genuine
  geometric bookkeeping flagged as the rotation engine's "remaining frontier (1)": vanishing support
  determinant ⟹ great-circle betweenness.  It is new content, not a re-wrapper (the two sign
  conditions are the convex-position signs, not the goal in disguise; `det3 = 0` alone gives only the
  *real*-span coplanarity, the signs upgrade ℝ→ℝ≥0).
- **`szGeom_of_core` / `schoenbergZaremba_of_core`: CONDITIONAL-honest on `SZOpeningCore`.**  The
  primitive is now the elementary opening output (a moved vertex + det3/sign data), strictly smaller
  than the old `SZGeom`; every consequence (the betweenness extraction, the chain, the cut routing) is
  proved.
- **Full-disclosure caveat — the ONE resistant case, named after genuine exhaustion:** constructing
  `SZOpeningCore` itself — the Rodrigues opening with **convexity persistence** (the rotated tail stays
  a `StrictConvexSphArm`) and the supremum dichotomy **instantiated on the arm's `sOrient` triples** to
  yield the stuck/reached split with the correct convex-position signs — is NOT proved this round.  The
  engine's `reach_or_stuck` is the analytic skeleton over an *abstract* support family; wiring it to the
  concrete arm needs convexity-persistence infrastructure the engine does not yet mechanise.  I did not
  fake or bank this: the `weak` half is itself the monotone arm lemma (not separately cheap), so the
  core cannot be discharged trivially.  It remains the single, now-elementary, isolated primitive.

## Chapter 13's remaining frontier

1. **`SZOpeningCore`** — the Rodrigues opening with convexity persistence + `reach_or_stuck`
   instantiated on the `sOrient` triples (produce `qstar`, the det3/sign stuck data, and the
   reached/cut split).  Discharging this makes `SZGeom`, hence `SchoenbergZarembaTarget`, hence
   `spherical_arm_mono`/`_strict`, **unconditional**.  The betweenness extraction it feeds is now done.
2. **The vertex-link correspondence** (design §9–§12): the Cauchy bridge identifying each convex-
   polyhedron vertex link with a `StrictConvexSphArm`, so the spherical arm lemma drives Cauchy's
   rigidity theorem — the chapter's top-level goal.
