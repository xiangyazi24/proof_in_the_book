# Ch13 — `StrictDiagonalSupport` (Brick 1) + `TailFoldBoundary` (Brick 2): clean discharges, isolated cores, and the `htfb` vacuity fix (ZinanFFCT63)

**File:** `ProofsInTheBook/ZinanFFCT63.lean` (NEW; imports only `ZinanFFCT54`, which re-exports the
kernel + FFCT18/19/21/23/25/52/53).  Does NOT import or touch `ZinanFFCT62` (codex-owned).
**Status:** compiles 0 errors / 0 warnings; all **6** `#print axioms` report clean-3
(`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no custom axiom, no `native_decide`).
No `sorry`/`admit`/`axiom`/`native_decide` (real-proof-term grep clean; only docstring mentions).
**Verify:** `scp … uisai2 && ssh uisai2 'lake env lean ProofsInTheBook/ZinanFFCT63.lean'` (LEANEXIT=0).
Did **not** git commit.

---

## Headline (honest)

Both FFCTPlus leftovers reduce to genuine **spherical convex-position cores** that the substrate does
not cheaply support, and — verified numerically BEFORE writing any Lean — the *local* determinant
routes sketched in the brick spec are **provably sign-indeterminate / non-contradictory**.  I therefore
discharged everything that IS clean (and it is substantial + load-bearing), isolated the true
irreducible cores as **satisfiable, non-vacuous** residues, and — most importantly — **fixed a §3.3
vacuity bug** in FFCT53's assembly that `#print axioms` could never have caught.

---

## Brick 1 — `StrictDiagonalSupport`: two of the cases KILLED unconditionally

The honesty-contract trap was avoided: FFCT54's `StrictDiagonalSupport` is correctly the **per-arc**
claim (only the `[1..n]` arc's interior vertices vs the wrap diagonal `(B n, B 1)`), NOT the false
"all other vertices on one side" (which fails for a closed polygon — a square's diagonal splits the
two arcs onto OPPOSITE sides).

**Discharged unconditionally (clean-3, load-bearing):**
- `strictDiagonal_base` (`v = 1`, vertex `B 2`): `0 < sOrient (B n)(B 1)(B 2)` — **direct** from
  `strict_nonincident` of the parent edge `(1,2)` at the non-incident vertex `n`, via cyclic `det3`
  rotation (`det3 (B n)(B 1)(B 2) = det3 (B 1)(B 2)(B n)`).
- `strictDiagonal_top` (`v = n − 2`, vertex `B ⟨n−1⟩`): `0 < sOrient (B n)(B 1)(B ⟨n−1⟩)` — **direct**
  from `strict_nonincident` of edge `(n−1, n)` at the non-incident vertex `1`, via two cyclic
  rotations.
- `strictDiagonalSupport_of_interior`: **assembles FFCT54's exact `StrictDiagonalSupport`** from the
  named interior residue + the two discharged boundary cases.  Splits `v ∈ {1, …, n−2}` into base /
  strict-interior / top.

**Net residue shrinkage (verified for all `n ≥ 3`):**
- `n = 3, 4`: the strict-interior range `2 ≤ v ≤ n − 3` is **EMPTY** → `StrictDiagonalSupport` is
  **FULLY discharged unconditionally** on those dimensions.
- `n ≥ 5`: residue = `StrictDiagonalInteriorSupport` (only `2 ≤ v ≤ n − 3`); base/top killed.

**Why the interior `2 ≤ v ≤ n − 3` is the genuine irreducible core (numerically established):**
- The up-induction via the Grassmann–Plücker / cofactor identity inner-producted with the hemisphere
  normal gives `D_m·⟨h,B(m−1)⟩ = E_n·⟨h,B 1⟩ − E_1·⟨h,B n⟩ + D_{m−1}·⟨h,B m⟩` with `D_{m−1} > 0` (IH)
  and `E_1, E_n > 0` (strict edge supports).  But `E_n⟨h,B1⟩ − E_1⟨h,Bn⟩` is **not sign-definite**
  (min ≈ −0.59 over 20000 random strict polygons), so the step is **not** closable by a local
  `nlinarith`/sign argument.
- The "no vertex on the plane" sub-claim's two-neighbour-edge route gives `αβ < 0` from BOTH neighbour
  edges (no contradiction); projecting an interior vertex onto the diagonal plane violates a
  *globally-dependent* support, not a single canonical one.
- A faithful interior proof needs a 2D-projection convex-polygon (ordered winding) framework or a
  global hemisphere argument — substantial new infrastructure, not a one-file grind.

Exposed as `StrictDiagonalInteriorSupport` with non-vacuity guards
(`strictDiagonalInteriorSupport_conclusion_satisfiable` — genuine strict `0 < sOrient`;
`strictDiagonalInteriorSupport_range_nonempty` — the `n ≥ 5` regime where it actually bites).

---

## Brick 2 — `TailFoldBoundary`: the metric⟸ray reduction DISCHARGED + the vacuity bug FIXED

**The metric collinearity reduces, unconditionally, to a ray membership.**
`tailFoldBoundary_of_rayMembership`: FFCT53's `TailFoldBoundary A`
(`sDist (A 0)(A ⟨n−1⟩) = endpt A + sDist (A last)(A ⟨n−1⟩)`) follows from
`TailRayMembership A` (`A (last) ∈ span≥0 {A 0, A ⟨n−1⟩}`) via `sDist_betweenness_of_collinear`.
(The metric⟺ray equivalence was numerically confirmed.)  That ray membership is **exactly the FFCT22
audited master gap**: `far_fold_tail_collinear_step` delivers only the determinant-vanishing half
(`det3 = 0`, the LINE), while the sign of the new cone coefficient (the RAY) needs the out-of-plane
re-extraction FFCT22 packages as `TailConePropagates` and flags out-of-scope.  Exposed as
`TailRayMembership` (non-vacuity guard `tailRayMembership_shape_inhabited`).

**THE VACUITY BUG (playbook §3.3) — found and fixed.**
FFCT53's `foldedFlatCutTransportPlusNR_holds` consumes
`htfb : ∀ {n} (hn : 2 ≤ n) (A), TailFoldBoundary A` — a **free universal with NO geometric
hypotheses**, which is **unsatisfiable / false**: a generic convex arm does NOT have its last vertex
folded onto the `(0,n−1)` ray (confirmed concretely: lhs 0.4688 ≠ rhs 0.8891 on a random convex
4-vertex arm).  `#print axioms` is blind to this (it verifies proof legality, not premise
satisfiability).  Any instance fed this `htfb` would be operationally vacuous.

The honest, **satisfiable** replacement: `BoundaryTailRay` — the ray membership in the genuine
`(0,n−1)` boundary-fold context (`WeakConvexSphArm` + `PositiveJoints` + `NoNonadjacentRepeat` + the
fold betweenness `A 0 ∈ span≥0 {A 1, A ⟨n−1⟩}`).  Suppliers `tailFoldBoundary_of_boundaryTailRay` and
`tailFoldBoundary_supply_in_context` thread it through the actual `(0,n−1)` consumer context (where
`i = 0`, `j = n−1`, `hcol`, `hA`, `hposA`, `hnr` are all in scope), producing `TailFoldBoundary` from a
**real geometric premise**, not a vacuous one.  Premise satisfiability witnessed by
`boundaryTailRay_premises_satisfiable`.

---

## §3.3 self-adversarial audit (done before reporting)

- **No vacuous statements.**  Every new `Prop` (`StrictDiagonalInteriorSupport`, `TailRayMembership`,
  `BoundaryTailRay`) concludes a genuine strict inequality / cone membership; each carries an
  inhabitation/refutation guard.  The Brick-2 fix EXISTS precisely because I caught FFCT53's `htfb` as
  the vacuous impostor.
- **No fragment impostor / no faked discharge.**  The interior convex-position core and the cone
  re-extraction are NOT faked — I numerically PROVED their local routes are sign-indeterminate and
  exposed them as named residues, rather than banking a hand-wave.
- **Residue genuinely shrinks** (not a re-wrapper): Brick 1 kills the two arc-boundary cases (and ALL
  of `n ∈ {3,4}`); Brick 2 reduces the metric equation to the cone residue AND repairs an
  unsatisfiable premise into a satisfiable one.

---

## FINAL surviving surface (after this wave)

1. **`StrictDiagonalInteriorSupport`** (Brick 1 core) — strict-interior arc vertices `2 ≤ v ≤ n − 3`
   only; the genuine spherical convex-position core (2D-projection / global-hemisphere argument).
   Base/top cases and all of `n ∈ {3,4}` discharged unconditionally.
2. **`TailRayMembership` / `BoundaryTailRay`** (Brick 2 core) — the FFCT22 cone re-extraction
   (`A last ∈ span≥0 {A 0, A ⟨n−1⟩}`), now in a **satisfiable, context-carrying** shape; the metric
   reduction to it is discharged unconditionally.
3. (unchanged) `BackwardFoldCase` (operationally dead at the real consumer), `hsupply` (NR supply),
   the A-side `hivl` already discharged in FFCT54.

## Wiring note (for the orchestrator)

`foldedFlatCutTransportPlusNR_holds`'s `htfb` parameter should be re-typed to consume `BoundaryTailRay`
(threaded in the `(0,n−1)` branch via `tailFoldBoundary_supply_in_context hbtr hn3 hA hposA hnr hcol`)
instead of the free `∀ {n} (hn) (A), TailFoldBoundary A`.  That edit lives in FFCT53 and is left to the
single owner of that file (not touched here, per the one-file rule).
