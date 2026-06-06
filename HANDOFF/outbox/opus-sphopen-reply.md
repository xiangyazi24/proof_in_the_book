# SphericalOpening — the multi-vertex opening construction for `OpeningData` (opus reply)

**Status: DELIVERED, clean compile, 0 sorry / 0 axiom / 0 admit / 0 native_decide.**
File: `ProofsInTheBook/SphericalOpening.lean` (233 lines, NEW, untracked on `main`, no commit per rules).
Imports `ProofsInTheBook.SphericalFinish`; reuses the proven rotation engine + SZ + Core + Finish substrate.

## Honest headline

`OpeningData` is **NOT discharged unconditionally** this round, and faithfully so: after unfolding it
is the *entire* Schoenberg–Zaremba opening induction (the design explicitly names §8.4 "the hard
theorem to isolate"; every prior round flagged it as "a substantial development, not a single lemma,
and not faithfully completable in one round"). What is delivered:

1. **Genuine unconditional new content** above the substrate — the non-terminal joint-angle and
   endpoint persistence of the concrete `openArm`.
2. **A load-bearing reduction** of `OpeningData` to a **single** named, **satisfiable** geometric
   primitive `OpenedArmReachOrStuck` (the §8.3–§8.4 multi-vertex convex-position outcome), stated in
   *elementary* determinant + sign form so the reduction genuinely **derives** the `span ℝ≥0`
   betweenness (via the proven `betweenness_span_nnreal`) rather than re-stating it.
3. **The full chain composed**: `OpenedArmReachOrStuck → OpeningData → SchoenbergZarembaTarget`, so
   discharging the one isolated residue makes the **unconditional spherical arm lemma**
   (`spherical_arm_mono` / `spherical_arm_mono_strict`) drop out.

The one irreducible residue is isolated honestly as `OpenedArmReachOrStuck`, NOT faked, wrapped into a
vacuous hypothesis, or made trivially true — and its stuck payload is proved **satisfiable**.

## Verification (EXCLUSIVELY on uisai1 — nothing built/run locally; Mac kernel-panic rule honoured)

- `lake env lean ProofsInTheBook/SphericalOpening.lean` → EXIT 0, zero errors, zero warnings.
- `lake build ProofsInTheBook.SphericalOpening` → **Build completed successfully (8428 jobs).**
- `#print axioms` (from rebuilt oleans) on all 7 headline results → every one depends ONLY on
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no `ofReduceBool`/native.
  Checked: `openArm_jointAngle_fixed`, `sphAngle_openArm_fixed`, `openArm_endpt`,
  `openingData_of_reachOrStuck`, `openingData_holds`, `schoenbergZaremba_of_reachOrStuck`,
  `stuckPayload_satisfiable`.
- `grep -E 'sorry|admit|native_decide|^axiom '` → only the doc-comment line "No `sorry`…"; no code hit.
- Local and remote `SphericalOpening.lean` md5-identical (`e180f79a…`). Temp audit file removed from
  server. Root `ProofsInTheBook.lean` untouched (not my file — see wiring note).

## What is proved UNCONDITIONALLY (genuine new content above the substrate)

- `openArm_endpt` — the opened endpoint distance is `sDist (A 0) (openArm A θ (Fin.last (n+1)))`
  (the fixed first vertex to the moved tail — the quantity the opening grows). Via `openArm_zero`.
- `sphAngle_openArm_fixed` — opening preserves a spherical angle all of whose three vertices are
  jointly fixed (indices `≤ n`).
- `openArm_jointAngle_fixed` — **opening preserves every non-terminal joint angle** (`i.val + 2 ≤ n`,
  so the joint's highest vertex `i+2` avoids the rotated tail `n+1`; the single terminal joint
  `i.val = n-1`, vertices `n-1, n, n+1`, is exactly the opened one). This is design §8.2's
  `hinge_preserves_other_angles` for the concrete `openArm`.

## The reduction (load-bearing, §3.3-clean)

- `OpenedArmReachOrStuck : Prop` — the isolated §8.3–§8.4 convex-position primitive in **elementary
  form**: for strictly-wider convex arms, opening to the admissible supremum yields *either* a moved
  tail `qstar` with {`ShortArc (A 1) qstar`, **`det3 (A 0)(A 1) qstar = 0`**, the two convex-position
  **Gram signs**, the strict opening bound, the level-`n` sub-comparison bound} *or* the direct strict
  endpoint bound; plus the always-true weak bound `endpt A ≤ endpt B`.
- `openingData_of_reachOrStuck : OpenedArmReachOrStuck → OpeningData` — the **real work**: converts the
  elementary determinant + sign output into `OpeningData`'s `span ℝ≥0` betweenness membership via the
  proven `betweenness_span_nnreal`, forwarding the short arc / opening / sub-comparison bounds and the
  reached/cut branch. Strictly more primitive input (det + signs) than `OpeningData`'s output
  (membership) ⟹ genuinely load-bearing, not a re-wrap.
- `openingData_holds : OpenedArmReachOrStuck → OpeningData` — named entry point (alias of the above).
- `schoenbergZaremba_of_reachOrStuck : OpenedArmReachOrStuck → SchoenbergZarembaTarget` — composes the
  reduction with the proven `schoenbergZaremba_of_openingData`. Discharging the one residue makes the
  spherical arm lemma unconditional.

## The single isolated residue (honest, after genuine exhaustion) — `OpenedArmReachOrStuck`

This packages exactly the geometry the rotation engine does not mechanise: the design §8.3 hinge
**convex-persistence** (the opened arm stays a `StrictConvexSphArm` at admissible θ — the multi-vertex
mixed-triple `edge_support` / `strict_nonincident` + `open_hemisphere`, the orientation-convention
content that puts the coplanar `A 0` on the *near* side of the arc) together with the §8.4 admissible-
supremum **reach/stuck** outcome on the genuine arm and the §8.5 stuck-cut sub-arm + IH application.
Its analytic skeleton is proved in the substrate (this module's persistence lemmas; `arm_reach_or_stuck`,
side/orientation persistence, the IVT realisation `openedJointAngle_surjOn`, the Gram-sign ⟺
betweenness equivalence). The body is several missing convexity-persistence theorems — a substantial
multi-vertex development, not a single lemma.

**Why it cannot be reduced further this round:** producing the structured stuck/reached output from the
raw `arm_reach_or_stuck` dichotomy requires (a) the opened arm to be convex at the supremum, (b)
identifying the vanishing mixed support as the *closing* one with the convex-position signs supplied by
the *other* still-valid constraints, and (c) the dropped-first-vertex sub-arm to be a convex
`StrictConvexSphArm` so `SZComparison n` applies. (a)–(c) are exactly the §8.3 persistence theorems
the substrate does not contain; they are inseparable from the multi-vertex convex bookkeeping.

## Non-vacuity / anti-impostor (playbook §3.3)

- `OpenedArmReachOrStuck` is the genuine SZ opening step — mathematically **true** (the content of the
  book's proof), hence the conditional chain is NOT vacuous.
- `stuckPayload_satisfiable` — the elementary stuck payload (det = 0 ∧ both Gram signs) is realised by
  *every* nonnegative great-circle combination `A 0 = s • A 1 + t • qstar` (`det_zero_of_betweenness`
  + `stuckSigns_of_between`), the exact converse the reduction relies on. So the stuck branch is
  satisfiable, not a vacuous-hypothesis impostor.
- The reduction `openingData_of_reachOrStuck` **produces** the `span ℝ≥0` membership (real work via
  `betweenness_span_nnreal`), not a re-statement of its hypothesis.
- No `def : Prop` impostor for any *proved* goal; `OpenedArmReachOrStuck` is an honest named open
  obligation and is NOT claimed proved. `OpeningData` itself is NOT proved (only reduced).

## Honest classification

- `openArm_endpt`, `sphAngle_openArm_fixed`, `openArm_jointAngle_fixed`, `stuckPayload_satisfiable`:
  **FAITHFUL, UNCONDITIONAL** new content.
- `openingData_of_reachOrStuck`, `openingData_holds`, `schoenbergZaremba_of_reachOrStuck`: **FAITHFUL**
  reductions (CONDITIONAL-honest chain links on the strictly-isolated `OpenedArmReachOrStuck`).
- `OpeningData` : **OPEN** (reduced to `OpenedArmReachOrStuck`, not discharged).

## Wiring note (root file is not mine)

`SphericalOpening.lean` is NOT yet imported in `ProofsInTheBook.lean` (I own only my new file). To
wire: add `import ProofsInTheBook.SphericalOpening` after the `SphericalFinish` import. The module
builds standalone (8428 jobs) and `#print axioms` is clean from rebuilt oleans.

## Chapter 13's remaining frontier (vertex-link only)

1. **`OpenedArmReachOrStuck`** — the design §8.3 hinge convex-persistence + the §8.4 admissible-
   supremum reach/stuck on the genuine arm + the §8.5 stuck-cut sub-arm (the multi-vertex bookkeeping),
   which with this module's substrate discharges `OpeningData` ⟹ `SchoenbergZarembaTarget` ⟹ the
   **unconditional spherical arm lemma**.
2. **The vertex-link correspondence** (design §9–§12): the Cauchy bridge identifying each convex-
   polyhedron vertex link with a `StrictConvexSphArm`, driving Cauchy's rigidity theorem.
