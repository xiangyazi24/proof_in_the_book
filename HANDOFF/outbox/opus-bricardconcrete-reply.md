# Chapter 9 concrete inputs closed — `ProofsInTheBook/BricardConcrete.lean`

**Status: DONE for the achievable concrete content. 0 sorry / 0 axiom / 0 admit / 0 native_decide.
Verifies clean on uisai1; olean built (8433 jobs); axioms = core three only.** 372 lines.

I own only the NEW file `ProofsInTheBook/BricardConcrete.lean`
(`import ProofsInTheBook.BricardAggregate`). Stayed on `main`; **no commits**; touched nothing else;
no codex/OpenAI tooling; never built locally (kernel-panic rule respected). Verified exclusively on
**uisai1** (`lake env lean` + `lake build` + `#print axioms`).

## Verification (uisai1)

- `lake env lean ProofsInTheBook/BricardConcrete.lean` → **exit 0, zero output**.
- `nohup lake build ProofsInTheBook.BricardConcrete` → **`✔ Built … (8433 jobs)`**.
- `#print axioms` on the six headline/bridge results → each `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`, no `ofReduceBool`/`trustCompiler`): `edgeSourceFaithful_oneTetSolid`,
  `edgeSourceFaithful_of_nonOverlapping`, `tet_edges_nonoverlap`,
  `tet_three_vertices_not_collinear`, `edgeSourceFaithful_regularTetSolid`,
  `regularTet_cube_no_equidecomp_concreteP`.
- `grep` → the only `sorry`/`admit`/`axiom` token is in doc-comment prose; no real ones.

## Item 1 — `EdgeSourceFaithful`, PROVEN (the main deliverable, unconditional for non-overlap solids)

I re-read the **exact** statement in `BricardAggregate.lean`:
`EdgeSourceFaithful S` ⇔ for every `E ∈ allEdgeOccs S`, the canonical pearls *incident* to `E`
(`p.relInterior ⊆ E.carrier`) equal the pearls *sourced on* `E.seg` (`p.sourceEdge = E.seg`).

Source ⊆ incidence is the unconditional `pearlsOnSource_subset_incident` (already in
`BricardAggregate`). I proved the **converse** and isolated its exact geometric content:

- A canonical pearl has a **nondegenerate** relative interior (`p.lo < p.hi`, `point` injective ⟹
  `aPt ≠ bPt`; `pearl_aPt_ne_bPt`). Its closure (`= p.carrier`) lands in any closed superset of the
  relative interior, so both endpoints `aPt, bPt` lie in `E.seg.carrier` **and** in
  `p.sourceEdge.carrier` (`pearl_endpoints_mem_of_relInterior_subset`, via
  `segment_subset_closure_openSegment` + `IsClosed.closure_subset_iff`).
- Hence `p.sourceEdge` and `E.seg` share two **distinct** points. The only way the converse can fail
  is two *distinct collinear* raw edges overlapping. I named exactly this:
  `EdgesNonOverlapping S` := distinct segments of `PieceEdges S` never share two distinct points.
- `edgeSourceFaithful_of_nonOverlapping : EdgesNonOverlapping S → EdgeSourceFaithful S` — the converse,
  **unconditional modulo the named non-overlap predicate**.

**`EdgesNonOverlapping` proved outright for a single tetrahedron.** Two distinct edges of an
affinely-independent tet never share two distinct points (`tet_edges_nonoverlap`): both endpoint
pairs lie on `line[x,y]` (`segment_carrier_collinear` + `Collinear.mem_affineSpan_of_mem_of_ne`);
since the edges differ there are **three distinct vertices** among the four endpoints, all on that
line — collinear — contradicting `tet_three_vertices_not_collinear` (restrict `T.v` along the
embedding `![i,j,k] : Fin 3 ↪ Fin 4`, then `affineIndependent_iff_not_collinear`). The index
bookkeeping ("≥ 3 distinct among `i<j`, `k<l`, `(i,j)≠(k,l)`") is handled by a 3-way case split.

So **`edgeSourceFaithful_oneTetSolid (T : Tet) : EdgeSourceFaithful (oneTetSolid T)` is
unconditional** — no remaining hypothesis. This is the affine-independence case the brief identified
as the provable core.

## Item 2 — the concrete solids

- `oneTetSolid T` — the single-tet solid (singleton pieces; interior-disjointness trivial);
  `pieceEdges_oneTetSolid : PieceEdges (oneTetSolid T) = T.edges`.
- `regularTetSolid : SolidWithAngles` — `TetDihedral.regularTet` as a one-piece solid, all six edges
  declared external with external angle `arccos(1/3)`; the `LocalDihedralModel` validation is
  `0 < arccos(1/3) < π` (`arccos_third_mem_Ioo`, since `1/3 ∈ (-1,1)`).

**On the cube (honest assessment).** I did *not* fabricate a cube `SolidWithAngles`. Building a
genuine Kuhn/6-tet cube requires the full coordinate disjoint-interiors proof, **and** — critically —
its `EdgeSourceFaithful` is the genuine collinear residue: a simplicial subdivision of a cube has
collinear-overlapping raw edges (adjacent tets share edges; a swapped-orientation duplicate or a
collinear sub-edge would violate `EdgesNonOverlapping`), so the single-tet converse route does **not**
discharge it — exactly the joint flagged in `BricardAggregate.lean`. Manufacturing a fake single-tet
"cube" would make the headline's `hQ_pi2` an **unsatisfiable** premise (a cornerTet has only 3 of 6
edges at `π/2`), i.e. a VACUOUS conditional (playbook §3.3) — so I deliberately left the cube side
abstract rather than bank a vacuous instance.

## Item 3 — the `LocationData`/`PearlSectorModel` certificates

These are the **design-sanctioned isolated 3D residue** of `PearlClassification.lean` (the
`PearlSectorModel` cross-section certificate: orthogonal-slice apex/radius, sector list, planar
local-model witness, and the `PearlAngleSum = sectorAngleSum` bridge). They are not constructed here;
they remain the honest `Ldata`/`Rdata` inputs (as in the parent headline). The regular-tet angle
normalization `hP_arccos` is a property of `Ldata`'s certificates (each pearl classified onto an
external edge of angle `arccos(1/3)`), satisfiable and consistent with `regularTetSolid`.

## Item 4 — the sharpest assembled headline

`regularTet_cube_no_equidecomp_concreteP` specializes
`regularTet_cube_no_equidecomp_aggregated` to `SP = regularTetSolid`, **discharging two of its
hypotheses by proven facts**: the regular-tet faithfulness bridge `hFP`
(`edgeSourceFaithful_regularTetSolid`) and nonemptiness `hSP` (`regularTetSolid_pieces_nonempty`).

**Exactly what remains (the minimal honest hypothesis set), strictly sharper than the parent:**
1. `Ldata` — the regular-tet `LocationData` (the `PearlSectorModel` residue);
2. `SQ`, `Rdata`, `hFQ` — the **cube side**: a `SolidWithAngles`, its `LocationData`, and its
   `EdgeSourceFaithful` bridge (the genuine collinear-edge non-degeneracy, undischarged);
3. `decomp` — the putative equidecomposition (the object refuted);
4. `hP_arccos`, `hQ_pi2` — the two external-angle normalizations.

The regular-tet side's faithfulness and nonemptiness are **no longer hypotheses** — they are this
module's proven `EdgeSourceFaithful (oneTetSolid …)`.

## §3.3 faithfulness / non-vacuity self-audit

- **Not VACUOUS.** `edgeSourceFaithful_oneTetSolid` produces `EdgeSourceFaithful` *unconditionally*
  for any tet; `regularTetSolid` is a genuine inhabitant. The headline `…_concreteP` is the parent
  minus two discharged hypotheses — strictly sharper, no new premise, so no narrower satisfiability.
- **`hP_arccos` satisfiable** (a LocationData classifying every regular-tet pearl onto an external
  edge of angle `arccos(1/3)` satisfies it) — not an unsatisfiable premise. **I refused to bank a
  fake cube** precisely because it would have made `hQ_pi2` unsatisfiable (VACUOUS).
- **`tet_edges_nonoverlap` / `tet_three_vertices_not_collinear`** are genuine new geometry (affine
  independence ⟹ non-collinearity ⟹ no two-point edge overlap), not re-wrappers.
- **No hidden weakening.** The converse direction discharges exactly the *incidence ⊆ source* gap; the
  easy half (source ⊆ incidence) is the upstream proven lemma.
- **Verdict:** **FAITHFUL/unconditional** for the entire `EdgeSourceFaithful` theory and the concrete
  `regularTetSolid` (faithfulness + nonemptiness proven, axioms = core three). **CONDITIONAL-honest**
  for the headline `…_concreteP`: remaining inputs are the two `LocationData`/`PearlSectorModel`
  certificates (isolated 3D residue), the two angle normalizations, and the **cube-side**
  `SolidWithAngles`/`EdgeSourceFaithful` (the genuine collinear-edge non-degeneracy — the single
  truly-resistant concrete fact, isolated and named, not faked).

## Wiring note (for whoever updates the import graph / Audit.lean — I did not touch them)

`BricardConcrete.lean` imports `ProofsInTheBook.BricardAggregate`. To surface it, add it to the
library root and add `#print axioms` lines for the six results above to `Audit.lean` (keeping Audit's
own import list updated). Verified output is the core three axioms.
