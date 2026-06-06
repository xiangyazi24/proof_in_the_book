# Chapter 9 cube side closed — `ProofsInTheBook/BricardCube.lean`

**Status: DONE. The cube side is discharged concretely and unconditionally.
0 sorry / 0 axiom / 0 admit / 0 native_decide. Verifies clean on uisai1; olean built (8434 jobs);
axioms = core three only.** 790 lines.

I own only the NEW file `ProofsInTheBook/BricardCube.lean` (`import ProofsInTheBook.BricardConcrete`).
Stayed on `main`; **no commits**; touched nothing else; no codex/OpenAI tooling; never built locally
(kernel-panic rule respected). Verified exclusively on **uisai1** (`lake env lean` + `lake build` +
`#print axioms`).

## Verification (uisai1)

- `lake env lean ProofsInTheBook/BricardCube.lean` → **exit 0, zero errors** (only cosmetic
  `unusedSimpArgs` / deprecated-`push_neg` warnings).
- `nohup lake build ProofsInTheBook.BricardCube` → **`Build completed successfully (8434 jobs)`**.
- `#print axioms` on `regularTet_cube_no_equidecomp_concrete`, `edgeSourceFaithful_cubeSolid`,
  `edgesNonOverlapping_kuhnSolid`, `no_three_cubeVerts_collinear`, `cubeSolid`, `kuhnSolid`,
  `disjoint_interior_of_separating` → each **`[propext, Classical.choice, Quot.sound]`** (no `sorryAx`,
  no `ofReduceBool`/`trustCompiler`).
- `grep` → the only `sorry`/`axiom`/`admit` token is the doc-comment prose "No `sorry`…".

## The central claim, verified numerically first (then proved in Lean)

The brief asked me to verify the Kuhn 6-tet decomposition has **no partial collinear overlaps**.
Confirmed coordinate-by-coordinate (Python, exact `Fraction`) **before** writing Lean:
- 6 Kuhn tets (one per permutation of `Fin 3`), **19 distinct edge values**, 36 occurrences.
- **0** pairs of distinct edge values share two points (no collinear overlap).
- All 19 oriented as `(smaller-coord-sum, larger-coord-sum)` — **no carrier appears with both
  orientations** (so `Segment3` *values* dedupe cleanly; the swapped-orientation hazard does not occur).
- **No edge's line contains a third cube vertex; no 3 of the 8 cube vertices are collinear at all.**

This last fact is the clean lever: `EdgesNonOverlapping` for the *whole* Kuhn solid reduces to "no three
distinct cube vertices are collinear", exactly mirroring `tet_edges_nonoverlap` of
`BricardConcrete.lean` (affine-independence → non-collinearity) but for the cube-vertex set.

## Item 1 — the Kuhn decomposition (six order-simplices)

- **Six explicit tets** `kt012 … kt210` (vertex maps `![0, e_{σ0}, e_{σ0}+e_{σ1}, (1,1,1)]`).
- **Affine independence** `kvXXX_ai` for each, by the triangular coordinate extraction
  (`affineIndependent_iff_of_fintype` + `Finset.weightedVSub_eq_linear_combination`, read off the 3
  coordinate equations, grind).
- **Pairwise disjoint interiors** (`disj_XYZ_UVW`, all 15 unordered pairs): each carrier lies in an
  order halfspace `{coordDiff p q ≤ 0}` (`carrier_subset_coordDiff_le` via `convexHull_min`); the
  *interiors* land in the *open* halfspaces (`interior_coordDiff_le_subset_lt`: pushing along the
  witness direction `e_p−e_q` would exit the closed halfspace), which are disjoint
  (`disjoint_interior_of_separating`).  The separating coordinate pair per tet-pair was precomputed.
- **`kuhnSolid : TetSolid`** — the 6 pieces with `interior_disjoint` discharged by a 6×6 case bash
  (`first | absurd rfl hAB | disj_… | disj_….symm`).  Distinctness `ktX_ne_ktY` (15) proved by a
  discriminating coordinate.

## Item 2 — `EdgesNonOverlapping kuhnSolid`, PROVEN outright

- `kuhn_vertex_isCubeVertex` — every Kuhn-piece vertex is a cube vertex (`IsCubeVertex`).
- `no_three_cubeVerts_collinear` — three distinct cube vertices are never collinear (write
  `v,w = u + s•d`; the ratio `r = sw/sv` at the differing coordinate must be `0/1/−1`; `0`→`w=u`,
  `1`→`w=v`, `−1`→ coordinate value `2` or `−1`, impossible for `{0,1}`-coordinates).  **Clean closed
  argument — no 512-case bash.**
- `kuhn_edge_coordSum_lt` / `kuhn_edges_no_reverse` — Kuhn-edge orientation is canonical (coordinate
  sum strictly increasing along the index), so no edge is the orientation-reverse of another (this is
  the one subtlety the brief flagged: `Segment3` carries orientation, but the swapped-orientation
  duplicate never arises).
- `edgesNonOverlapping_kuhnSolid` — two distinct raw edges sharing two distinct points put all four
  (cube-vertex) endpoints on `line[x,y]`; the case split (`g.a ∈ {f.a,f.b}?`, `g.b ∈ {f.a,f.b}?`)
  either exhibits **three distinct collinear cube vertices** (contradiction via
  `no_three_cubeVerts_collinear`) or the **reverse-edge** case (contradiction via
  `kuhn_edges_no_reverse`), or forces `f = g`.

So **`edgeSourceFaithful_cubeSolid : EdgeSourceFaithful cubeSolid.toTetSolid`** is unconditional —
discharged by `edgeSourceFaithful_of_nonOverlapping edgesNonOverlapping_kuhnSolid`.  This closes the
*single truly-resistant concrete fact* that `BricardConcrete.lean` left open on the cube side.

## Item 3 — `cubeSolid : SolidWithAngles` (12 external edges at π/2)

- `cubeExtEdges` — the **twelve** unit-cube edges as `Segment3` (nondegeneracy by the differing
  coordinate, `euclid3_ne_of_coord`).
- `cubeSolid` — `toTetSolid := kuhnSolid`, `extEdges := cubeExtEdges`, `angleOfExtEdge := fun _ => π/2`;
  the `LocalDihedralModel` validation is `0 < π/2 < π` (`pi_div_two_mem_Ioo`).
- Note on the design (per the brief's honest warning): `LocalDihedralModel` only requires `0<θ<π`, and
  the headline's `hQ_pi2` quantifies over the *`LocationData` certificates*, not over the solid alone —
  it asks that each cube-side pearl be **classified onto an external (cube) edge of angle π/2**.  The
  external edges are exactly the 12 cube edges (true dihedral π/2 — `TetDihedral.cornerTet`-style right
  angles), so this is a **genuine, satisfiable** π/2 normalization — *not* a vacuous premise.

## Item 4 — the fully concrete headline

`regularTet_cube_no_equidecomp_concrete` specializes `regularTet_cube_no_equidecomp_concreteP`
(regular-tet side already concrete) to `SQ := cubeSolid`, **discharging the cube-side faithfulness
bridge `hFQ`** by the proven `edgeSourceFaithful_cubeSolid` — no longer a hypothesis.

**Exactly what remains (the minimal honest input set — now BOTH solids concrete):**
1. `Ldata`, `Rdata` — the two `LocationData`/`PearlSectorModel` cross-section certificates (the
   design-sanctioned isolated 3D residue of `PearlClassification.lean`);
2. `decomp` — the putative equidecomposition (the object refuted);
3. `hP_arccos`, `hQ_pi2` — the two external-angle normalizations (properties of the certificates).

**No geometric input remains undischarged on either side** — both `SolidWithAngles`
(`regularTetSolid`, `cubeSolid`), both `EdgeSourceFaithful` bridges, and both nonemptiness facts are
proven module results, not hypotheses.

## §3.3 faithfulness / non-vacuity self-audit

- **Not VACUOUS.** `hQ_pi2` is satisfiable: `cubeSolid.angleOfExtEdge e = π/2` (by `rfl`) over a
  *non-empty* 12-edge external set whose dihedral angles are genuinely π/2 — a `LocationData`
  classifying every cube-side pearl onto a cube edge satisfies it.  I deliberately built the **real
  Kuhn cube** (6 honest π/2-edged pieces) rather than a fake single-tet "cube" (which would make
  `hQ_pi2` unsatisfiable, the VACUOUS trap `BricardConcrete.lean` flagged).
- **`edgesNonOverlapping_kuhnSolid` is real geometry**, not a re-wrapper: it rests on genuine new
  lemmas (`no_three_cubeVerts_collinear`, canonical-orientation `kuhn_edges_no_reverse`), and the
  numeric pre-check confirmed the no-overlap claim is *true* of the Kuhn decomposition (not assumed).
- **Disjoint interiors are real**: separating open-halfspace confinement, not a definitional dodge.
- **No hidden weakening**: `regularTet_cube_no_equidecomp_concrete` is the parent
  `…_concreteP` minus the discharged `hFQ` — strictly sharper, no new premise, so no narrowed
  satisfiability.
- **Verdict: FAITHFUL/unconditional** for the entire cube geometry (Kuhn solid, disjoint interiors,
  `EdgesNonOverlapping`, `EdgeSourceFaithful`, `cubeSolid` `SolidWithAngles`), axioms = core three.
  **CONDITIONAL-honest** for the headline `…_concrete`: remaining inputs are the two
  `LocationData`/`PearlSectorModel` certificates (isolated 3D residue) and the two angle
  normalizations — nothing geometric.

## Wiring note (for whoever updates the import graph / Audit.lean — I did not touch them)

`BricardCube.lean` imports `ProofsInTheBook.BricardConcrete`.  To surface it, add it to the library
root and add `#print axioms` lines for `regularTet_cube_no_equidecomp_concrete`,
`edgeSourceFaithful_cubeSolid`, `edgesNonOverlapping_kuhnSolid`, `cubeSolid`, `kuhnSolid` to
`Audit.lean` (keeping Audit's own import list updated).  Verified output is the core three axioms.

Cosmetic: a handful of `unusedSimpArgs` warnings remain in the six affine-independence proofs (a
`simp only` whose lemmas are subsumed by the following `norm_num`); they are warnings only, not errors,
and I left the proofs as-is rather than destabilize six green proofs for cosmetics.
