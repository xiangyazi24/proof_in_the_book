# opus-polyfinish — Chapter 36 final residues: direction-genericity chain + AbstractBridge enrichment

**STATUS: AbstractBridge realisation ENRICHMENT fully PROVED unconditionally
(the genuinely new content); direction-genericity OBSTRUCTION proved precisely +
existence backbone proved; ONE truly-resistant joint isolated and named honestly
(the whole-line `ValidDirPath` cannot chain arbitrary directions — a real
formalization-design limit, not wiring).**

New file `ProofsInTheBook/PolygonFinish.lean` (551 lines), imports
`ProofsInTheBook.PolygonRayIndep`.  Compiles clean on uisai1:
**0 sorry / 0 axiom / 0 admit / 0 native_decide**.  All 11 audited headlines are
**clean-3** `{propext, Classical.choice, Quot.sound}` (verified from rebuilt
oleans).  Branch `main`, no switches, no commits.  Only the one NEW file touched;
not wired into any root, so no other build disturbed.  Verified EXCLUSIVELY via
rsync→uisai1 `lake env lean` / `lake build` per the kernel-panic rule; never ran
lake locally.

---

## Task item 1 — the direction-genericity chain

### What was PROVED (genuine new content)

- **`dirComparable_forces_det2_eq`** — *the obstruction, proved*: a valid
  whole-line `ValidDirPath P r₁ r₂` forces `det2 r₁ e = det2 r₂ e` for **every**
  edge `e`.  Reason (now a Lean proof): `dirDen` (the per-edge determinant) is
  **affine in `t`** (`dirDen_affine`), and a valid path requires it nonzero on
  **all** of `ℝ`; an affine function nonzero on all of `ℝ` is a nonzero constant
  (evaluate at the root `t₀ = -a/(b-a)` if `a ≠ b`).  Hence the present whole-line
  engine connects **only** directions with identical per-edge determinants.
- **`validDir_avoiding` / `slopeRay` / `exists_validDir_avoiding`** — the
  finite-bad-direction genericity backbone: for *any* finite forbidden slope set
  `B`, there is a slope `t ∉ B ∪ edgeSlopes P`, giving a genuine `RayDirection`
  `mkPt 1 t` (the `rayDirection_exists` construction packaged as avoidance).  This
  is the constructive "a valid intermediate direction always exists outside
  finitely-many bad ones" the design named.

### The single isolated joint (honest)

The **fully unconditional** ray-independence (arbitrary `ρ σ : RayDirection P`) is
**NOT** reachable by "chaining valid paths through a third direction" over the
*existing* engine.  `PolygonRayIndep.ValidDirPath` quantifies `∀ t : ℝ` (the whole
line), and `dirComparable_forces_det2_eq` proves that pins the per-edge
determinants equal — so no whole-line path bridges two generic directions, nor
chains through a third.  The unconditional statement needs a **segment** (`Set.Icc`)
direction-path engine (re-deriving the D5–D8 local-constancy on `Icc 0 1`
connectedness instead of `ℝ`).  Since this file owns only `PolygonFinish.lean` and
cannot edit `PolygonRayIndep.lean`, that re-derivation is out of scope and is
isolated as the single named residual `UnconditionalRayIndepInput` (with
`closedRegion'_ray_indep_uncond` re-exporting it, and
`closedRegion'_ray_indep_comparable` discharging the comparable case with no extra
input).  This is a genuine mathematical/design obstruction, **not** fakeable.

---

## Task item 2 — the AbstractBridge enrichment (fully PROVED, the headline win)

`GeomTriangulation'` stores point-triples, not indices.  We **enriched the
`EarTriangulation'` recursion to emit indexed triangles** and proved the
realisation correspondence unconditionally:

- **`indexedTris`** — emits, in lockstep with `EarTriangulation'.triangles`, a list
  of *parent* `Fin n` index-triples: base `(0,1,2)`; each diagonal split remaps the
  left/right sub-triangles' indices through `leftIndex`/`rightIndex` (`mapLeftIdx`/
  `mapRightIdx`).
- **`realise_indexedTris`** — *point-faithfulness, list form*:
  `(indexedTris t).map (realiseTriple P) = t.triangles`, by induction over the
  cutting object.  The key step: a subpolygon vertex point
  `(G.leftPoly hdiag).q k = subpolygonLeftTuple P i j k = P.q (leftIndex i j k)`
  equals the remapped parent index's point (`leftPoly_q_eq` / `rightPoly_q_eq`), so
  realisation transports through the remap verbatim.
- **`indexedTris_realise`** / **`exists_absTriangle_realise`** — every geometric
  triangle is realised (`PolygonRayIndep.RealisedBy`) by an emitted index triple,
  and (via nondegeneracy + `injective_q`, lemmas `nondeg_corners_distinct`,
  `toAbsTriangle`) by a genuine `AbsTriangle n` with **distinct** indices.
- **`abstractBridge_of_glue`** — assembles `PolygonRayIndep.AbstractBridge` from a
  `CombinatorialGlue` (abstract triangle set + `TriangulatedPolygon` glue +
  realisation membership).
- **`realise_of_realiserClosed` / `combinatorialGlue_of_triang`** — pin the
  residual: for **any** realiser-closed set `S` the realisation field is automatic,
  so the *only* missing datum is a `TriangulatedPolygon n S` glue over a
  realiser-closed `S`.  The geometric/realisation content is fully discharged.
- **`artGallery_strict_finish`** — the `⌊n/3⌋` art-gallery headline (`Sees` =
  segment-in-region, the faithful statement), with the bridge realisation
  discharged and only the combinatorial glue as named input.
- **`combinatorialGlue_base`** — the residual is **non-vacuous**: the base `3`-gon's
  `CombinatorialGlue` is witnessed (single abstract `⟨0,1,2⟩`,
  `TriangulatedPolygon.single`, realising the base geometric triangle).

### Residual after item 2 (honest, narrowest)

The one remaining input for the general triangulation is the **abstract
combinatorial glue**: a `TriangulatedPolygon n S` over a set `S` containing a
realiser of every emitted geometric triangle.  This is exactly the inductive
diagonal-glue (`TriangulatedPolygon.glue` chain) that `GeomTriangulation'` does not
carry — the merge-two-sub-triangulations-along-the-diagonal-edge combinatorics.
The realisation half is now proved; only this abstract glue remains, and it is
satisfiable (base case witnessed).

---

## Task item 3 — final Chapter-36 headline with narrowest remaining input

`artGallery_strict_finish` is the narrowed headline.  Its inputs are exactly:
`BaseTriangleFacts` (the leaf region-equals-hull facts), an `EarTriangulation'` (which
upstream is produced from the `CutGeometryOracle` in `PolygonTriangulation`), and the
`CombinatorialGlue` (the abstract combinatorial triangulation — the only genuinely
new residual this file isolates).  The bridge **realisation** is DISCHARGED.

What is **NOT** claimed free (unchanged from PolygonRayIndep/PolygonCutOracle and not
touched here): the split-set planar Jordan geometry inside `CutGeometryOracle`
(`split_region_union` / `split_region_intersection`).  Ray-independence removed the
fresh-ray parity-matching obstruction; the split-set geometry is the residual planar
content and remains a named oracle field.  So the **unconditional** `artGallery` is
NOT achieved; the remaining inputs are precisely (a) the `CutGeometryOracle` split-set
geometry, (b) the abstract combinatorial glue.  Both are documented and satisfiable
in their base cases.

---

## Faithfulness verdicts (playbook §3.1 Group C, §3.3 adversarial)

- **FAITHFUL (unconditional):** `dirComparable_forces_det2_eq`, `dirDen_affine`,
  `validDir_avoiding`, `slopeRay`, `exists_validDir_avoiding`, the entire item-2
  enrichment (`indexedTris`, `realise_indexedTris`, `indexedTris_realise`,
  `exists_absTriangle_realise`, `toAbsTriangle`, `nondeg_corners_distinct`).
- **CONDITIONAL-honest:** `artGallery_strict_finish` on the satisfiable
  `CombinatorialGlue` (witnessed by `combinatorialGlue_base`); the comparable
  ray-independence on the satisfiable `DirComparable` (proven upstream).
- **NAMED RESIDUAL (not a result):** `UnconditionalRayIndepInput` /
  `closedRegion'_ray_indep_uncond` — explicitly the isolated segment-path-engine
  input, labeled as residual; `closedRegion'_self_consistent` is an explicitly
  labeled `Iff.rfl` sanity wrapper, not a headline.
- **Vacuity check (§3.3 trap):** the conditional `CombinatorialGlue` is witnessed
  inhabited (`combinatorialGlue_base`), so the headline is not a vacuous conditional;
  `dirComparable_forces_det2_eq`'s hypothesis is satisfiable (`validDirPath_const`
  upstream), so the obstruction theorem is not vacuous.
- **Statement-scope check:** `artGallery_strict_finish`'s conclusion is the faithful
  art-gallery statement (`∃ guards, card ≤ n/3 ∧ ∀ region point, ∃ guard, Sees`),
  with `Sees` = segment-in-region — not weakened to the bare combinatorial `chapter36`.

---

## Verification
```
rsync -az .../PolygonFinish.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH \
  && lake env lean ProofsInTheBook/PolygonFinish.lean'        # exit 0
# olean rebuilt; #print axioms on all 11 headlines → [propext, Classical.choice, Quot.sound]
# grep sorry|admit|axiom|native_decide → none
```
