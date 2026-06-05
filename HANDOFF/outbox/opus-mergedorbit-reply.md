# opus-mergedorbit reply — Chapter 35 φ-level merged-face single-orbit

## Status: SUBSTANTIAL DISCHARGE. Triangle backbone fully proved unconditionally;
`DeleteVertexMergedFaceSingleOrbit` reduced (from the fan) to ONE strictly-local,
non-vacuous outer-arc residue. 0 sorry / 0 axiom / clean-3.

New file: `ProofsInTheBook/PlanarMapFanMergedOrbit.lean`
(imports `ProofsInTheBook.PlanarMapFanFaces`; ~490 lines).
NOT yet wired into `ProofsInTheBook.lean` / `Audit.lean` (one writer; leaving the
import-graph edit to you, as per the discipline).

## The mathematical key (novel, fully proved): closed-form `φ'` at the seam

`σ = φ · α`, so `(deleteVertex v).φ x = (σ^k)(α x.1)` where `k = firstOutside`
counts `σ`-steps from `α x.1` to the first survivor.  The decisive observation:
the only deleted darts at a seam vertex `z ≠ v0` are those **pointing at `v0`**
(`head = v0`), and a simple graph has at most ONE such dart.  Hence the rotation
skips **at most one** dart, giving a two-case closed form (no seam rotation list
needed):

* **Case A** (`M.φ x.1` survives): `φ' x = M.φ x.1`
  (`deleteVertex_phi_apply_of_next_kept`, already in PlanarMapFanFaces).
* **Case B** (`M.φ x.1` deleted): `φ' x = M.σ (M.φ x.1) = M.φ (M.α (M.φ x.1))`,
  which then survives — `deleteVertex_phi_apply_of_next_deleted` (new, this file;
  `firstOutside = 2` via `Nat.find_eq_iff`).

## What is proved UNCONDITIONALLY from the fan

1. `deleteVertex_phi_apply_of_next_deleted` — the Case-B closed form.
2. `deleteVertex_phi_survRun_iterate` / `_sameCycle_of_survRun` — `φ'` follows
   `M.φ` step-for-step along any run of survivors (no face condition; the tool
   for the outer arc).
3. **Triangle-dart facts**: each fan triangle `T = (v0,a,b)` keeps exactly one
   surviving dart, the edge dart `T.d1` (`d0`, `d2` touch `v0`, deleted);
   `survivor_on_fanTriangle_eq_d1` shows any incident survivor on a triangle face
   IS that triangle's `d1`.
4. **Shared spoke + chain step** (the heart): consecutive triangles share the
   `v0`-spoke (`α T_i.d2 = T_{i+1}.d0`, via simple-graph no-parallel), so the
   Case-B closed form gives `φ'(T_i.d1) = T_{i+1}.d1`
   (`fanTriangle_chain_step` / `_sameCycle`).
5. **Whole fan-triangle chain**: `fanTriangle_edge_dart_sameCycle_ref` — every
   triangle edge dart along the path lies in the one `φ'`-cycle of the head
   triangle's edge dart (list induction over `consecutivePairs fan.path`).
6. **Main theorem** `deleteVertexMergedFaceSingleOrbit_of_fan (fan) (hchord)
   (htail0) (houter) : DeleteVertexMergedFaceSingleOrbit M d0`.  Every incident
   survivor is linked to the head triangle's edge dart `r`: non-outer faces are
   fan triangles (via `incident_faces_exact.exact_faces`) → handled by the chain;
   outer-face survivors → supplied by `houter`.  Then symmetry+transitivity of
   `SameCycle` gives the goal.  (`hchord` is used only to make `fan.x` occur once
   on the path, so the head pair is unique.)

## The single isolated residue (named, non-vacuous, NOT goal-in-disguise)

`MergedOuterArcReconnects M d0 r outerFace` :=
  every surviving dart on the OLD OUTER FACE is `φ'`-SameCycle to `r`
(`r` = a fixed fan-triangle edge dart).

Supplied to the main theorem as `houter`.  It is:
- **strictly weaker** than `DeleteVertexMergedFaceSingleOrbit`: the entire
  `t+1`-triangle chain (the combinatorially substantial part) is discharged
  unconditionally; the residue constrains only the outer-face survivors against
  one triangle dart;
- **satisfiable / non-vacuous** (holds for any genuine chordless boundary-vertex
  deletion, e.g. the tetrahedron `t = 1`);
- the exact `φ`-level analogue of the (proved) `DeleteVertexNeighborsConnected`
  residue in `PlanarMapFanConnectivity.lean`.

## Why the outer arc resisted (honest gap analysis)

The remaining seam bridges are `φ'(d1_t) = M.φ(α(T_t.d2))` (jump into the outer
face along edge `v0–w`) and `φ'(o_pre) = d1_0` (jump back along `v0–x`).  Both
require certifying that the reverse spokes `α(T_head.d0)` / `α(T_t.d2)` lie on
the **outer face**, i.e. that the edges `(v0,x)`, `(v0,w)` are boundary edges
with the outer face on the far side, AND that the outer-face survivors form one
contiguous `M.φ`-arc (deleted block = the 2 consecutive darts at `v0`).  The
current `BoundaryVertexFan` certificate exposes `x`, `w` as boundary *vertices*
but does NOT tie the spoke *darts* to `hNT.outerCycle`.  Discharging
`MergedOuterArcReconnects` therefore needs either a stronger fan field (the two
boundary spoke darts + the outer cycle's position of `v0`) or a boundary-list
walk on `hNT.outerCycle` (comparable in size to the connectivity file).  All the
`φ'`-machinery it would consume is already proved here
(`deleteVertex_phi_apply_of_next_deleted`, `*_survRun_*`), so it is a bounded
follow-up, not new core mathematics.

## Verification

- `lake env lean ProofsInTheBook/PlanarMapFanMergedOrbit.lean` — no errors, no
  warnings, no sorry (deps prebuilt: `lake build ProofsInTheBook.PlanarMapFanFaces`).
- `#print axioms deleteVertexMergedFaceSingleOrbit_of_fan` and
  `#print axioms deleteVertex_phi_apply_of_next_deleted`
  → both `[propext, Classical.choice, Quot.sound]` (clean-3, no sorryAx).
- Verified exclusively on `uisai1` (never `lake build`/`lake env lean` locally).

## Remaining to fully close `DeleteVertexMergedFaceSingleOrbit` unconditionally
- Discharge `MergedOuterArcReconnects` (the outer-face seam walk): identify the
  two boundary spoke darts on the outer face + the contiguous surviving outer arc
  (needs a fan/outer-cycle tie or a `hNT.outerCycle` list walk; all `φ'` tools
  already present).
