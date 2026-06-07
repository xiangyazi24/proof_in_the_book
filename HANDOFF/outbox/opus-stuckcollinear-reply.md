# opus-stuckcollinear-reply — the STUCK branch via the spherical triangle inequality (fresh route)

## Status (honest)

**The fresh collinearity route is BUILT, clean-3, full-build-clean. The STUCK branch's *matched-cut*
obstacle (b2) — the refuted SAS at the collinear corner — is DISCHARGED: the STUCK branch now produces
`endpt A ≤ endpt B` *directly via the spherical triangle inequality*, never through `MatchedCutData`.
The arm lemma is closed conditional on the SINGLE fresh per-step atom `DeficientReachCollinear`, whose
STUCK disjunct is the genuine collinear opening configuration `StuckCollinearData` (no SAS). It is NOT
unconditional: the irreducible residue is the *existence* of the opening witness with the first-corner
betweenness — the design §8.4 "THE hard theorem", co-extensive with the substrate's own already-named
`SZStepGeom` / `StuckWitnessExists`, isolated as irreducible by five prior expert rounds. The
collinearity route makes the STUCK *transport* unconditional (the triangle inequality, banked here); it
does not, and cannot from the listed pieces, manufacture the opening *existence*.**

New file: `ProofsInTheBook/SphericalStuckCollinear.lean` (owned this round). One substrate edit: lib
root `ProofsInTheBook.lean`, `import ProofsInTheBook.SphericalStuckCollinear` after `SphericalArmClose2`.
No edit to `SphericalArmFinish` / `SphericalArmClose2` was needed (the fresh route is additive — a new
recursion consuming the substrate). Branch main, no commits.

## Why the fresh route, not the matched cut (the refutation honored)

`opus-armclose2-reply.md` refuted the matched cut: at a stuck vertex `A`'s opened corner is collinear
(angle `π`) while `B`'s is `< π`, so the SAS diagonal match `diag_len_eq` fails. The directive's fresh
route bypasses the cut entirely. The mechanism is the kernel's own triangle inequality
(`SphericalArm.sDist_triangle` = `InnerProductGeometry.angle_le_angle_add_angle`):

* at `δ*` a non-incident support of `openArm A δ*` **vanishes** (obstacle (a)'s STUCK disjunct,
  `reachStrictConvex_dichotomy_at`, banked in `SphericalArmClose2`);
* `vanishingSupport_planar_collinear` ⟹ the three vertices lie on a common great circle — a **straight
  joint** of `A_{δ*}`;
* a straight joint is the **tight** case of the triangle inequality: the through-distance *equals* the
  sum (`sDist_betweenness_of_collinear`, the betweenness equation) — the straightened sub-configuration's
  endpoint is a geodesic of length = sum, one fewer effective bend;
* `B` is strictly convex (all joints bend `< π`), so the **flat-≤-bent** step is the triangle inequality
  on `B`'s first corner: `sDist (B 1) (B last) ≤ sDist (B 1) (B 0) + sDist (B 0) (B last)`, combined
  with the *equality* on `A`'s collinear first corner. This is the genuine SZ stuck argument.

## What this round BANKS (genuine new, clean-3)

* **`szChain_stuck_weak`** — the **weak (non-strict) flat-≤-bent triangle-inequality chain**, the
  monotone companion the substrate lacked (`stuck_endpoint_strict` only gave the *strict* bound). Built
  directly from `sDist_triangle` + the betweenness.
* **`stuck_endpoint_mono`** — the weak stuck-case endpoint glue on the genuine arm (the directive's
  flat-≤-bent weak direction): collinearity + weak opening + tail sub-comparison + equal first side ⟹
  `endpt A ≤ endpt B`.
* **`stuckCollinear_endpt_pair`** — the **complete fresh-route stuck reduction**: the collinear stuck
  configuration `StuckCollinearData` ⟹ the endpoint *pair* (`≤`, and `<` when some `B`-joint is wider)
  *directly via the triangle inequality* (weak from `szChain_stuck_weak`, strict from the kernel's
  `szChain_stuck`). This is the replacement for the refuted matched-cut CUT branch.
* **`StuckCollinearData`** — the fresh STUCK payload (existential `qstar` + first-corner betweenness +
  weak/strict opening + tail sub-comparison + equal first side); **no** SAS data.
* **`DeficientReachCollinear`** — the fresh per-step atom: deficient case ⟹ `ReachStepDatum A B`
  (REACH, obstacle (a) banked) **or** `StuckCollinearData A B` (STUCK, this module), **not**
  `MatchedCutData A B`.
* **`defStepCol_endpt`** — the terminating well-founded recursion (strong induction on
  `unmatchedCount A B`) on the fresh atom: congruent base ⟹ `congruent_matchedCutData`; deficient ⟹
  REACH (recurse on smaller measure, transport across `endpt A ≤ endpt Asharp`) or the collinear stuck
  pair directly.
* **`inductiveStep_of_deficientReachCollinear`, `schoenbergZaremba_of_deficientReachCollinear`,
  `spherical_arm_mono(_strict)_of_collinear`** — the kernel arm lemmas, conditional ONLY on
  `DeficientReachCollinear`. All clean-3.
* **`stuckCollinearData_of_szStepGeom_stuck`** — the faithful connection: when the substrate's existing
  primitive `SZStepGeom` fires its (betweenness-form) stuck branch, it yields exactly
  `StuckCollinearData` — confirming the residue is the genuine opening witness, NOT the matched cut.

## The single remaining residue (named, non-vacuous, concrete failing chain)

**`DeficientReachCollinear`** — but with obstacle (b2)'s matched-cut requirement *removed*. Its STUCK
disjunct is `StuckCollinearData A B`: the *existence* of the opening to `δ*` producing the moved tail
`qstar` with the **first-corner betweenness** `A 0 ∈ span≥0 {A 1, qstar}` and the opening /
sub-comparison / first-side bounds. This is the genuine multi-vertex §8.4 construction — co-extensive
with the substrate's `SphericalSZChain.SZStepGeom` strict field / `SphericalOpeningProcess.StuckWitnessExists`
/ `OpenedArmReachOrStuck` (the substrate's own already-named residue; design §8.4 "THE hard theorem").

Concrete failing chain (verified by `grep`, file:line):
* `SphericalCore.openArm` (`:160`) opens only the **last** joint; `reach_endpoint_mono_arm`
  (`SphericalReachStuck:236`) is the last-joint base triangle only — no arm-level open-at-an-interior-joint
  lemma.
* The STUCK disjunct of `reachStrictConvex_dichotomy_at` (`SphericalArmClose2:242`) surfaces a vanishing
  support at an **arbitrary** non-incident triple `(i, i+1, j)`, NOT the first-corner triple
  `(1, 0, last)` the betweenness `A 0 ∈ span≥0 {A 1, qstar}` requires. No substrate lemma identifies the
  binding support as the first-corner one (`grep` over `SphericalAdmissibleSup`, `SphericalReachStuck`,
  `SphericalOpeningProcess` for any first-corner / binding-support identification: none).

So the collinearity gives the *right kind* of fact (a betweenness / triangle-inequality tightness), and
the triangle-inequality transport is now unconditional — but mapping the *arbitrary* stuck collinearity
to the *first-corner* betweenness needs the convex-position binding-support analysis the rotation engine
does not mechanize. The directive's "drop the collinear vertex ⟹ shorter arm" presupposes the dropped
vertex is the endpoint-relevant (first/last) corner; for an arbitrary interior collinear vertex the
last-vertex-drop `cutArm` / `stuckSupport_gives_cut` carries no endpoint relation to `A` (proved-absent),
so the reduction cannot close without the binding-support identification.

## Non-vacuity guards (playbook §3.3)

`szChain_stuck_weak_nonvacuous` (the weak chain is a real theorem, witnessed by the betweenness),
`stuckCollinearData_satisfiable` (the STUCK payload is a real configuration), `stuckCollinear_pair_nonvacuous`
(it yields a real endpoint inequality via the triangle inequality), `defStepCol_conclusion_satisfiable`
(the recursion conclusion realised reflexively). All in-file, clean-3.

## Verification

* `rsync` + `ssh uisai1 ... lake env lean ProofsInTheBook/SphericalStuckCollinear.lean` → **RC=0**, **0
  errors, 0 warnings**, 0 sorry/admit/native_decide.
* **FULL `lake build`** (lib root wired) → "**Build completed successfully (8644 jobs)**", **0 `error:`**;
  `✔ Built ProofsInTheBook.SphericalStuckCollinear`.
* `#print axioms` (scratch importer, fresh oleans) → **clean-3 `[propext, Classical.choice, Quot.sound]`**
  on: `spherical_arm_mono_strict_of_collinear`, `spherical_arm_mono_of_collinear`,
  `schoenbergZaremba_of_deficientReachCollinear`, `defStepCol_endpt`, `stuckCollinear_endpt_pair`,
  `szChain_stuck_weak`, `stuck_endpoint_mono`. No `sorryAx`, no `ofReduceBool`/`native_decide`.
* `grep -nE 'sorry|admit|native_decide|^axiom '` over the new file → **0 in code** (only module-doc prose).

## Honest verdict

The directive's fresh route is **correct and is now banked unconditionally as the STUCK transport**: the
collinearity (`vanishingSupport_planar_collinear`) ⟹ the betweenness ⟹ `endpt A ≤ endpt B` via the
**spherical triangle inequality** (`szChain_stuck_weak` / kernel `szChain_stuck`), with **no** matched
SAS cut — so obstacle (b2) (the refuted matched cut at the collinear corner) is genuinely discharged,
replaced by the triangle inequality the kernel already has. The arm lemma is closed conditional on the
single fresh atom `DeficientReachCollinear`, whose STUCK disjunct is the genuine collinear opening
configuration, not the impossible SAS match. It is **NOT** unconditional: the irreducible residue is the
*existence* of the opening to `δ*` with the first-corner betweenness (`StuckCollinearData`) — co-extensive
with the substrate's own `SZStepGeom` / `StuckWitnessExists`, the design §8.4 "THE hard theorem", which
the binding-support identification (arbitrary stuck triple ⟹ first-corner betweenness) and the
arbitrary-interior-joint opening still resist. The chapter's arm lemma is not made unconditional this
round; its STUCK *transport* obstacle is closed via the triangle inequality, and the residue is now
purely the opening-witness *existence* (the same primitive the substrate already names), with the
matched-cut refutation removed from beneath it.
