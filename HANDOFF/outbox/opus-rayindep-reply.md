# opus-rayindep — Ray-direction independence + the Fisk art-gallery bridge (Chapter 36 endgame)

**STATUS: ray-direction independence PROVED (unconditional analytic core, comparable
form); Fisk visibility + bridge headline PROVED (conditional on the named abstract
bridge); `CutGeometryOracle` discharge PARTIAL and honestly delimited.**

New file `ProofsInTheBook/PolygonRayIndep.lean` (903 lines) compiles clean on
uisai1: **0 sorry / 0 axiom / 0 admit / 0 native_decide**.  All 7 audited headline
constants are **clean-3** (`{propext, Classical.choice, Quot.sound}`).

Branch `main` (no switches, no commits).  Only the one NEW file touched (imports
`ProofsInTheBook.PolygonCutOracle` + `ProofsInTheBook.Chapter36`); not wired into
any root, so no other build disturbed.  Verified EXCLUSIVELY via rsync→uisai1
`lake env lean` per the kernel-panic rule; never ran lake locally.

## The mathematical idea (why it works)

The corrected base-point local-constancy proof of `PolygonSideCrossing` moves the
BASE point along a segment.  Ray-independence moves the **DIRECTION** instead.  The
key algebraic fact: `side r x v = det2 r (v - x)` is **LINEAR in `r`** (det2
left-bilinearity), so along `r(t) = lineMap r₁ r₂ t` each side coordinate is affine
in `t` — the *same* affine shape as `side_lineMap`, in the direction variable.  And
`crossTau = det2 (a-x) (b-a) / det2 r (b-a)` has a **constant numerator**
(independent of `r`) over the affine-in-`t` denominator — continuous wherever the
denominator stays nonzero.  At a direction event `side r(t₀) x v = 0` (direction
points along `v - x`), the two edges incident at `v` share the *same* side function,
so the parity-neutral handover `span_mod_two_through_vertex` applies **verbatim** —
the SAME algebraic lemma the convention's vertex-sweep uses, now in the direction.

## What was PROVED (unconditional core — genuine new content)

### Direction-variable substrate (Layers D1–D4)
- `dirSide` (affine in `t`, `det2` left-bilinear), `dirDen`/`dirTau` (constant
  numerator over affine denominator), continuity of all three; `ValidDirPath`
  (every intermediate direction is a genuine `RayDirection`), `rayAt`.
- `dstatusOf_iff`, `dfcount`, `crossingNumber'_rayAt_eq_sum`.

### The analytic engine (Layers D5–D8)
- `dstatusOf_eventually_eq_of_noEvent` — no-event per-edge direction-local
  constancy (forward-guard zero ⇒ x on boundary, ruled out).
- `dpair_count_eventually_const` — **the vertex-event pairing in the direction
  variable**: at a shared-vertex event the two incident edges' combined parity is
  neutral (`span_mod_two_through_vertex`), backward and forward regimes both handled
  via the common crossing parameter `τ_v ≠ 0`.
- `crossingNumber'_dir_parity_eventually_const` — assembly: R-events / N-events /
  Rest partition, mirroring `crossingNumber'_parity_eventually_const`.
- `crossingNumber'_dir_parity_const` — global constancy via `IsLocallyConstant` on
  the connected `ℝ`.

### Ray-independence headlines (Layers D8–D9)
- **`crossingNumber'_ray_indep_path`** — crossing parities agree at the two endpoint
  directions of a valid path.
- **`closedRegion'_ray_indep_path` / `closedRegion'_ray_indep`** — region-indicator
  ray-independence (off-boundary): the corrected closed region is the SAME for two
  comparable directions (`DirComparable`).
- `crossingNumber'_congr_r` — `CrossingNumber'` depends on the direction only
  through `.r` (via `edgeCrossesRay'_eq_raw`).
- **`validDirPath_const`** — the path hypothesis is **satisfiable** (constant path at
  any `RayDirection`), so the ray-independence theorems are NON-vacuous.

### The Fisk bridge (Layers F1–F4)
- **`vertex_sees_point_in_incident_triangle`, `triangle_vertex_sees_triangle`** —
  visibility lemma: a guard in a triangulation triangle sees every point of it
  (segment ⊆ convex triangle ⊆ region via `subset_region`).  `Sees` defined.
- **`AbstractBridge`** — the faithful, satisfiable correspondence linking each
  geometric triangle to an abstract `AbsTriangle n` realising its corners under
  `P.q`, plus the proven combinatorial `TriangulatedPolygon`.
- **`artGallery_strict_of_bridge` / `artGallery_strict`** — Chapter 36's endpoint:
  every strict simple polygon admits `≤ ⌊n/3⌋` vertex guards seeing the whole closed
  region, wiring the proven `Chapter36.chapter36` 3-colouring through coverage +
  visibility.
- **`abstractBridge_base`** — the bridge is NON-vacuous: the base `3`-gon
  triangulation `[(v0,v1,v2)]` is realised by abstract `⟨0,1,2⟩` (`.single`).

## Honest status of the three task items

1. **Ray-direction independence — PROVED** (unconditional analytic core, comparable
   form).  Hypothesis = a *valid direction path* (`ValidDirPath`/`DirComparable`):
   the straight direction segment stays a ray direction.  Satisfiable
   (`validDirPath_const`), faithful (= exactly the genericity the design names).
   The vertex-event neutrality, forward-guard continuity, and connectedness are
   fully proved.  **Remaining named input for the FULLY unconditional form** (any
   `r₁, r₂` with no validity assumption): a finite-avoidance lemma to chain through a
   third direction `r₃` with both segments valid + antipodal handling — pure
   genericity on the direction circle (bad set = finitely many edge angles + the
   angles making a segment hit `0` or an edge angle).  The analytic engine is done;
   only this finite-avoidance routing remains.

2. **`CutGeometryOracle` discharge — PARTIAL, honestly delimited** (Layer G).
   Ray-independence discharges the *fresh-ray parity-matching* obstruction the design
   flagged as THE analytic core (`closedRegion'_ray_indep`): a subpolygon's fresh
   ray gives the same region parity as the parent's where comparable.  It does NOT
   supply the split-set geometry itself (`split_region_union` /
   `split_region_intersection` — which half-plane of the diagonal a point lies in,
   and the diagonal's own `+2` crossing contribution); that is the residual planar
   Jordan content and is NOT claimed free.  `strictSimplePolygon_geomTriangulation'`
   stays conditional on the residual `CutGeometryOracle` (unchanged from
   PolygonCutOracle).

3. **The Fisk bridge — PROVED conditional on the abstract bridge.**  Visibility,
   `AbstractBridge` (faithful + base-case satisfiable), and the `⌊n/3⌋` headline are
   proved.  The one remaining named input is `AbstractBridge` for the general
   (non-base) triangulation — the index/glue structure of the conceptual
   `GeomTriangulation'.toAbstract`, which `GeomTriangulation'` does not currently
   carry (it stores points, not vertex indices).  The combinatorial 3-colourability
   it feeds is the already-proven `Chapter36.chapter36`.

## Faithfulness verdicts (playbook §3.1 Group C)
- **FAITHFUL (unconditional):** the entire direction-variable engine D1–D8,
  `crossingNumber'_ray_indep_path`, `closedRegion'_ray_indep_path`,
  `crossingNumber'_congr_r`, `validDirPath_const`, the visibility lemmas,
  `abstractBridge_base`.
- **CONDITIONAL-honest** on the explicit, satisfiable, faithful hypotheses
  `DirComparable` (ray-indep two-direction form) and `AbstractBridge` (Fisk
  headline).  Both are real *data* whose satisfiability is witnessed in-file
  (`validDirPath_const`, `abstractBridge_base`) — not trivially-true Props, not
  vacuous premises.  The split-set geometry of `CutGeometryOracle` is explicitly
  NOT discharged and NOT claimed.

## Adversarial self-audit notes
- **Vacuity check (the §3.3 trap):** both conditional hypotheses are witnessed
  inhabited in-file, so no headline is a vacuous conditional.  `#print axioms` alone
  can't see this; the witnesses do.
- **Statement-scope check:** `artGallery_strict`'s conclusion is `∃ guards, card ≤
  n/3 ∧ ∀ region point, ∃ guard, Sees guard point` — the faithful art-gallery
  statement (guards SEE the region, not merely "hit triangles"), with `Sees` =
  segment-in-region.  Not weakened to the bare combinatorial `chapter36`.

## Verification
```
rsync -az .../PolygonRayIndep.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH \
  && lake env lean ProofsInTheBook/PolygonRayIndep.lean'        # exit 0, no warnings
```
`#print axioms` on all 7 headlines → `[propext, Classical.choice, Quot.sound]`.
`grep sorry|admit|axiom|native_decide` → none.
