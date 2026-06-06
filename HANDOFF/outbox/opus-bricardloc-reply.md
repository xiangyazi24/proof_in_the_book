# opus-bricardloc reply — the two LocationData certificates (Chapter 9)

**Status: DONE (regular-tet side fully discharged + cube side reduced to one honest isolate against
the *correct* normalization). Build clean, axioms clean, 0 sorry/axiom/admit.**

File owned & written: `ProofsInTheBook/BricardLocation.lean` (514 lines). Wired into the lib root
`ProofsInTheBook.lean` (one import line after `BricardCube`). On branch `main`, no commits.

## Verification

- `rsync` + `lake env lean ProofsInTheBook/BricardLocation.lean` on uisai1 → **EXIT 0**, no warnings.
- `lake build ProofsInTheBook.BricardLocation` → **Build completed successfully (8435 jobs)**; olean
  produced.
- `#print axioms` on every headline term (`regularTetLocationData`,
  `regularTet_pearlExtAngle_arccos`, `pearlAngleSum_oneTetRegular`,
  `angleClassQ_cube_externalPart_eq_zero_unconditional`, `spaceDiagonal_not_mem_cubeExtEdges`,
  `regularTet_cube_no_equidecomp_corrected`) → only `{propext, Classical.choice, Quot.sound}`.
  No `sorryAx`, no `ofReduceBool`/`native_decide`.
- `grep` for `sorry|admit|axiom` → only the two doc-string mentions; 0 real occurrences.

## What was built (the cheapest faithful route)

The cert chain is: `PearlClassificationCert` requires a `PearlSectorModel` whose load-bearing field is
`angle_bridge : PearlAngleSum = sectorAngleSum`. Using the design-sanctioned `fullSector_model`
(a single sector already covers the wedge), the whole geometric content collapses to **computing the
pearl angle sum** and matching it to the target. So I computed angle sums directly and bypassed the
abstract planar model.

### Regular-tetrahedron side — FULLY DISCHARGED, unconditional

- `pearlAngleSum_oneTetRegular`: every canonical pearl of the one-tet solid has **exactly one**
  incident edge occurrence (its source edge), because `EdgesNonOverlapping (oneTetSolid regularTet)`
  forces any incident occurrence to share the source edge as its segment, and the segment determines
  the ordered index pair (so the incident set is a singleton). Its dihedral angle is `arccos(1/3)`
  (`TetDihedral.regularTet_dihedralAngle`). ⟹ `PearlAngleSum = arccos(1/3)`.
- `regularTetLocationData : LocationData regularTetSolid (Pearls …)` — the **proven** `Ldata`. Each
  pearl gets the `externalEdge p.sourceEdge` location (with `relInterior_subset_sourceEdge_relInterior`
  giving the open-segment containment) and the one-sector model at `arccos(1/3)`.
- `regularTet_pearlExtAngle_arccos` — the **proven** `hP_arccos`.

This is exactly the headline's `Ldata`/`hP_arccos` regular-tet inputs, no hypotheses.

### Cube side — the honest obstruction + the correct, satisfiable normalization

**Critical finding (faithfulness, playbook §3.3).** The literal headline hypothesis
`hQ_pi2 : ∀ p ∈ Pearls(cube), pearlExtAngle (Rdata.cert p hp) = π/2` is **mathematically FALSE** for
the Kuhn cube, hence its premise set is unsatisfiable for the wrong reason (not Bricard). The Kuhn
solid's raw edges include the **main diagonal** `(0,0,0)–(1,1,1)` — edge `(0,3)` of every one of the
six orthoschemes — which carries pearls whose source edge is the diagonal. A diagonal pearl can only
be classified `solidInterior` (`PearlAngleSum = 2π`), giving `pearlExtAngle = 0 ≠ π/2`; the face
diagonals likewise give facet pearls with `pearlExtAngle = 0` (angle sum `π`). `externalEdge` is
geometrically unavailable for them because the diagonal is **not** a cube edge:
- `spaceDiagonal_not_mem_cubeExtEdges` (proven) — the space diagonal is not among the twelve
  `cubeExtEdges` (its endpoints differ in all three coordinates; cube edges are axis-parallel).

So `hQ_pi2` over the *full* canonical pearl set cannot be honestly discharged. This is an **over-strong
upstream hypothesis**, not a missing proof: the book only needs `angleClassQ(externalPart) = 0`, with
the interior/facet pearls folding into the `k·π` term that vanishes mod `ℚπ`.

**The correct, satisfiable normalization — proven unconditionally:**
- `angleClassQ_cube_externalPart_eq_zero_unconditional`: for **any** `LocationData cubeSolid P`,
  `angleClassQ(externalPart) = 0`. Reason: the cube's external angle is the *constant* `π/2`, a
  rational multiple of `π`, so each `pearlExtAngle ∈ {π/2, 0}` is in `ℚ·π`
  (`cube_pearlExtAngle_rat_mul_pi`), and the sum's class vanishes. This replaces `hQ_pi2`.

### The one honest cube isolate + the corrected headlines

- `CubePearlAngleData := LocationData cubeSolid (Pearls …)` — the named isolate: a classification
  certificate at every cube pearl (external `π/2`, facet `π`, interior `2π`), the cube analogue of
  `regularTetLocationData`. Its construction is the genuine residue: the six-orthoscheme Kuhn
  dihedral-angle / incidence computation. Satisfiable but heavy; named, not faked.
- `regularTet_cube_no_equidecomp_sharp_corrected` — Bricard via `bricard_condition_angleClassQ`:
  cube side `0` (proven unconditional), regular side `(card)·arccos(1/3) ≢ 0 mod ℚπ`.
- `regularTet_cube_no_equidecomp_corrected` — **fully discharged**: pins `Ldata :=
  regularTetLocationData`, discharges the regular normalization outright; the only remaining inputs
  are `Rdata : CubePearlAngleData` (the cube isolate) and `hmatch : Σ₁ = Σ₂` (the piece-matching
  residue carried by `BricardDoubleCount.sigma_match`, identical to the upstream `decomp`-derived
  match). No `hQ_pi2`.

## Honest classification

- **FAITHFUL / unconditional**: `regularTetLocationData`, `regularTet_pearlExtAngle_arccos`,
  `pearlAngleSum_oneTetRegular`, `angleClassQ_cube_externalPart_eq_zero_unconditional`,
  `spaceDiagonal_not_mem_cubeExtEdges`.
- **CONDITIONAL-honest on the named cube isolate** (`CubePearlAngleData`) **+ the Σ-match residue**:
  `regularTet_cube_no_equidecomp_corrected`. The premise set is *correctly* unsatisfiable (Bricard);
  the honest content is the reduction to {cube classification isolate, Σ₁=Σ₂}.

## Why I did NOT discharge the literal `BricardCube.regularTet_cube_no_equidecomp_concrete`

Doing so requires `Rdata`+`hQ_pi2` over the full Kuhn pearl set, which is unsatisfiable (diagonal
pearls). Constructing inhabitants of an unsatisfiable premise would be exactly the VACUOUS-conditional
trap the playbook warns against. The defect is upstream (the parent over-states `hQ_pi2` as ∀-pearls
rather than ∀-external-pearls / `angleClassQ(externalPart)=0`); I cannot fix the parent (I own only
`BricardLocation.lean`). My corrected headlines are the sharpest *faithful* statements, with the
regular side fully discharged and the cube side reduced to the single honest 3D isolate.

**Recommendation for the upstream owner:** weaken `hQ_pi2` in `BricardCube`/`BricardAggregate`/
`Bricard` to the satisfiable `angleClassQ(externalPart Rdata) = 0` (now available unconditionally as
`BricardLocation.angleClassQ_cube_externalPart_eq_zero_unconditional`), then the literal headline
becomes dischargeable with `Ldata := regularTetLocationData` and `Rdata := CubePearlAngleData`.
