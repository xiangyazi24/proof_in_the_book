# Ch13 §8.4 SZ spherical arm lemma — `SphericalSZClose` round (discharge `InteriorOpenAndSpliceStep`)

## Status: PARTIAL — the interior reach/stuck **production** and the `spliceArm` body **API** are now
## BANKED clean-3, strictly narrowing the residue. The headline "fully UNCONDITIONAL
## `spherical_arm_mono/_strict`" is NOT reached: of the three residual pieces, two (R-C transport,
## R-cong congruence) need substrate-absent sub-theories, and the third (R-O) bottoms out in the
## substrate's OWN isolated-open obstacle `BoundaryConvexPersistAtSup` (interior + hemisphere form).
## `InteriorOpenAndSpliceStep` therefore remains the single residue, now carrying only three precisely
## isolated irreducible analytic cores.

Branch `main`, **no commits** (as instructed). New file
`ProofsInTheBook/SphericalSZClose.lean` (432 lines) + 1 import in `ProofsInTheBook.lean`.
Verified on `uisai1`.

## Verification

* **RC**: `lake env lean ProofsInTheBook/SphericalSZClose.lean` → RC=0, **0 errors, 0 warnings**.
* **Full build**: `lake build` → **Build completed successfully (8650 jobs)**, 0 errors
  (was 8649; the new module is the +1 job; wired after `SphericalSZFinal`).
* **`#print axioms` — clean-3 ([propext, Classical.choice, Quot.sound], NO sorryAx/native_decide):**
  - `interior_reachOrStuck_at_sup`            — clean-3 ✓ (the interior trichotomy production)
  - `continuous_interiorSupport`              — clean-3 ✓
  - `continuous_openedInteriorJointAngle`     — clean-3 ✓
  - `sSup_interiorCombined_mem`               — clean-3 ✓
  - `spliceArm_endpt` / `_sideLen_splice` / `_sideLen_head` / `_sideLen_tail` — clean-3 ✓
  - `spherical_arm_mono_of_residue'`          — clean-3 ✓ (weak arm lemma, conditional on the residue)
* No `sorry` / `axiom` / `admit` / `native_decide` (grep clean — only the docstring mention at line 42).

## What was BANKED this round (genuinely new, unconditional, clean-3 — strictly enlarges the substrate)

### (R-O production) The INTERIOR reach/stuck supremum trichotomy

The substrate's reach/stuck/sup apparatus (`SphericalAdmissibleSup.reachOrStuck_at_sup` /
`augmented_reachOrStuck_at_sup`) is built on the **last-joint** `openArm` (a single rotated tail vertex,
`mixedSupport` indexed against `Fin.last`).  The decisive observation: the generic engine
`SphericalRotation.reach_or_stuck` is **agnostic** — it runs on *any* finite family of continuous
`f : ι → ℝ → ℝ`.  So the interior `openTail` (whole-tail rotation about an interior axis `A K`) needs
only its own continuous family, then the SAME engine.  Banked:

* `openedInteriorJointAngle` + `openedInteriorJointAngle_zero` + `continuous_openedInteriorJointAngle`
  — the interior opened joint-`k` angle `θ ↦ sphAngle (A k')(A K)(rotS2 (A K) θ (A ⟨k+2⟩))`, continuous
  via the substrate's *generic* `SphericalFinish.continuous_openedJointAngle` (the joint apex `K =
  openingAxis k`, far neighbour `A ⟨k+2⟩` rotates, prev `A k'` and axis fixed).
* `interiorSupport` + `interiorSupport_zero` + `continuous_interiorSupport` — the interior support of an
  arbitrary triple `θ ↦ sOrient (openTail A K θ i)(openTail A K θ j)(openTail A K θ l)`, continuous
  (`det3` of three `openTail`-coordinate-continuous vertices; proved by the explicit
  `Continuous.add/.sub/.mul` composition, mirroring `continuous_mixedSupport` — `fun_prop` blows the
  100k-step budget on `det3`).
* `interiorCombined` + `continuous_interiorCombined` + `sSup_interiorCombined_mem` — the interior
  combined admissible family (interior target slack + all interior supports), continuous and finite,
  with its admissible supremum `δ*` admissible (`sSup_mem_admissibleSet`).
* **`interior_reachOrStuck_at_sup`** — the interior trichotomy at `δ*`: `δ* = Tcap` ∨ REACH
  (`openedInteriorJointAngle A k δ* = T`) ∨ STUCK (`∃ ijl, interiorSupport A (openingAxis k) ijl δ* = 0`).
  This is the genuine interior analogue of `reachOrStuck_at_sup`, monitoring the *whole rotated tail*'s
  supports and the *interior* joint-angle target — the piece the prior round listed as
  substrate-absent (R-O).

### (R-C structure) The splice-body sub-arm `spliceArm` and its API (the body analogue of the BUILT ear)

* `spliceArm A i j` — the body `A[0..i] ++ A[j..N]` (`m = i + (N-j) + 1` edges; head vertex `v ≤ i`
  ↦ `A v`, tail vertex `v > i` ↦ `A (v-i-1+j)`).  (NB: the prior round's docstrings *claimed*
  `spliceArm` existed in `SphericalSZInduction`; it did not — only `intervalArm` (the ear) was built.
  This round builds it.)
* `spliceArm_zero/_last/_endpt` — the body keeps both arm endpoints, so `endpt (spliceArm …) = endpt A`
  (this is *why* the design recurses on the body for the endpoint comparison).
* `spliceArm_head/_tail` (vertex reindexing), `spliceArm_sideLen_head/_tail` (the non-splice sides are
  the parent's), `spliceArm_sideLen_splice` (the splice side at index `i` is exactly the diagonal
  `A i → A j`).

## The residue: `SphericalSZFinal.InteriorOpenAndSpliceStep` — now carrying only THREE irreducible cores

`spherical_arm_mono_of_residue'` re-exports the weak arm lemma conditional on the residue.  After this
round's banking, the residue's content is precisely the three cores below.  Each is a genuine
substrate-absent sub-theory (and the design `CH13_SZ_OPENING_DESIGN.md` itself only *states*
`splice_transport_of_diag_le` and `congruent_endpoint_eq` — it does not prove them):

1. **(R-O core) Boundary convexity of `openTail A K δ*`.**  `interior_reachOrStuck_at_sup` *produces* the
   trichotomy, but consuming REACH/STUCK needs `openTail A K δ*` weakly convex.  Admissibility at `δ*`
   gives every monitored support `≥ 0` — but `WeakConvexSphPolygon.open_hemisphere` demands the
   hemisphere functional **strictly `> 0`** at every (rotated-tail) vertex, which the sup gives only
   `≥ 0`.  This is **exactly** the substrate's own isolated-open obstacle
   `SphericalAdmissibleSup.BoundaryConvexPersistAtSup` (here in the interior + hemisphere-margin form).
   Failing chain: no boundary/closed-side convexity-persistence lemma exists anywhere in the substrate
   (`grep`); `mixedSupport_persists` is strict-open-neighbourhood only; `reach_strictConvex_at_sup`
   *takes* the strict mix/hemisphere positivity as hypotheses (it does not prove them), and
   `reach_or_stuck` cannot exclude a support being co-tight with the target at `δ*`.  **This is the
   genuine "one piece resists" — it is the same obstacle the entire prior last-joint campaign left open.**

2. **(R-C core) The splice-body side-and-angle-monotone transport `splice_transport_of_diag_le`.**  After
   `cut_diag_le` (banked) gives `sDist (A i)(A j) ≤ sDist (B i)(B j)`, gluing `spliceArm A i j` to
   `endpt A ≤ endpt B` is **not** a `Main`-instance: the splice side `A i → A j` matches `B`'s only by
   the *inequality* (not `SameSides`), and the new splice joint at `A i` is unmatched.  `Main`/`SZComparison`
   require equal sides; the body needs a strictly stronger arm comparison monotone in *both* one side
   (`≤`) and the angles.  Failing chain: no side-monotone arm lemma in the substrate; the splice joint
   is not among the matched joints.

3. **(R-cong core) The equal-joints endpoint congruence `congruent_endpoint_eq`.**  Equal sides + equal
   joints ⟹ `endpt A = endpt B` (spherical SSS arm rigidity).  The substrate banks the per-vertex SAS
   step `SphericalSZChain.diag_len_eq`, but assembling it along the arm needs spherical **angle
   additivity at a vertex** (the joint `sphAngle (A(i-1))(A i)(A(i+1))` splits as back-angle +
   forward approach angle in convex position) to carry the matched approach angle through each diagonal
   cut.  Failing chain: no spherical angle-addition/subtraction lemma exists in the substrate (`grep`
   for `sphAngle … + sphAngle …` / `oangle` in the tangent plane finds none); `diag_len_eq` alone
   matches one triangle but cannot propagate the prefix congruence forward.

## Honest scoping verdict

The directive's target ("discharge the 3 pieces → `InteriorOpenAndSpliceStep` → fully UNCONDITIONAL
`spherical_arm_mono/_strict`") is **not** reached.  What is genuinely achieved: the two *substrate-absent
structural* pieces the prior round flagged — the interior reach/stuck **production** (R-O's trichotomy,
via the generic engine on the interior `openTail` family) and the `spliceArm` body **API** (R-C's body
constructor) — are now built and banked clean-3, strictly narrowing the residue.  But the three
remaining cores are each a separate hard sub-theory that the design itself only *asserts*:

* **R-O core = the substrate's OWN isolated-open `BoundaryConvexPersistAtSup`** (interior + hemisphere
  form).  Closing it solves what the whole prior last-joint campaign explicitly left open — not
  closable here without a genuinely new boundary-persistence theory.  This is the honest "one resists".
* **R-C core** needs a side-monotone arm lemma (not in substrate; `Main` is equal-side only).
* **R-cong core** needs spherical tangent-plane angle additivity (not in substrate).

Per the doctrine (grind fully; if a piece genuinely resists, discharge what is mechanizable + isolate
the rest precisely with concrete failing chains), I banked every mechanizable structural production and
isolated the three irreducible cores exactly, with file:line-level failing chains in §R of the module.
I did **not** fabricate a re-wrapper, a vacuous conditional, or an axiom: `InteriorOpenAndSpliceStep`
is the unchanged load-bearing residue (the lex recursion of `SphericalSZInduction` genuinely derives the
arm lemma from it), and `spherical_arm_mono_of_residue'` is a faithful re-export, not a trivialisation.

Net advance vs. the prior `SZFinal` round: the residue no longer carries the interior reach/stuck
*production* (`interior_reachOrStuck_at_sup` banked) nor the body sub-arm *constructor* (`spliceArm` API
banked).  What remains is strictly the three analytic cores: the boundary convexity (= the substrate's
open `BoundaryConvexPersistAtSup`), the splice side-monotone transport, and the SSS angle-additivity
congruence.

Files touched: `ProofsInTheBook/SphericalSZClose.lean` (new, 432 lines), `ProofsInTheBook.lean` (+1 import).
