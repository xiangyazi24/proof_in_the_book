# opus-cubepearls reply — `CubePearlAngleData` constructed, Chapter 9 cube side CLOSED

**Status: DONE. `CubePearlAngleData` fully constructed (not a hypothesis); the corrected Chapter 9
headline is unconditional modulo only the `Σ₁ = Σ₂` piece-matching double count. Build clean, axioms
clean, 0 sorry/axiom/admit.**

File owned & written: `ProofsInTheBook/BricardCubePearls.lean` (1454 lines, 115 declarations).
Imports `ProofsInTheBook.BricardLocation`. On branch `main`, no commits, lib root untouched.

## Verification (uisai1)

- `lake env lean ProofsInTheBook/BricardCubePearls.lean` → **0 errors** (97 harmless
  `unused simp argument: Tet.v` linter warnings only).
- `lake build ProofsInTheBook.BricardCubePearls` → **Build completed successfully (8436 jobs)**, olean
  produced.
- `#print axioms` on `regularTet_cube_no_equidecomp_final`, `cubePearlAngleData`,
  `cubePearlCert_nonempty`, `pearlAngleSum_kuhn_terms`, `closedCube_subset_kuhnSolid_carrier`,
  `interior_kuhn_eq_openCube` → all exactly `{propext, Classical.choice, Quot.sound}`. No `sorryAx`,
  no `ofReduceBool`/`native_decide`.
- `grep sorry|admit|axiom|native_decide` → only the doc-string mention; 0 real occurrences.

## What was built (the genuine per-pearl Kuhn classification)

### 1. Edge inventory + dihedral angles (the math heart)

- All six Kuhn orthoschemes are congruent path-graphs `0→1→2→3`; the dihedral angle along each edge
  pair is **uniform**: `(0,1),(2,3)→π/4`, `(0,2),(1,2),(1,3)→π/2`, `(0,3)→π/3`. Proved as the 36
  lemmas `dih_σ_ij` via `dihedralAngle_eq_arccos` (`projOut` inner-product closed form + `norm_num`
  on explicit coordinates) and the `arccos` value lemmas (`arccos 0 = π/2`, `arccos(1/2) = π/3`,
  `arccos(1/√2) = π/4`).
- `pearlAngleSum_kuhn_terms`: for a non-overlapping solid the incident occurrences of a pearl are
  exactly those with `E.seg = sourceEdge` (`mem_IncidentTetEdges_iff_seg_eq`), so the angle sum is a
  36-term coordinate expression `∑ (if ktσ.v i = a ∧ ktσ.v j = b then dih_σij else 0)`. Plugging a
  concrete source edge collapses it.
- **Per-class angle sums (COMPUTED, not guessed):** cube edge `‖b−a‖²=1` → **π/2** (one orthoscheme
  at π/2, or two at π/4+π/4); face diagonal `‖b−a‖²=2` → **π** (two orthoschemes, each π/2); space
  diagonal `‖b−a‖²=3` → **2π** (all six orthoschemes, each π/3). The 19 distinct raw edges (12 cube,
  6 face, 1 space) are enumerated; each carries its class value.

### 2. The Kuhn carrier is the unit cube (the one resistant residue — discharged)

The face/space-diagonal pearls need the boundary/interior of the carrier. Proved
`kuhnSolid.carrier = [0,1]³`: `⊆` by convexity (vertices are cube vertices); `⊇` (the covering) by
exhibiting, for each of the 6 coordinate orderings, the explicit barycentric combination
`x = (1−x_{σ0})v0 + (x_{σ0}−x_{σ1})v1 + (x_{σ1}−x_{σ2})v2 + x_{σ2}v3` in the sorting simplex. Then
`interior_kuhn_eq_openCube : interior kuhnSolid.carrier = (0,1)³` (open cube is open + inside; interior
⊆ openCube via the coordinate-boundary perturbation argument).

### 3. Per-class containments + certificates

- cube edge → `externalEdge` (source ∈ `cubeExtEdges`, `relInterior ⊆ sourceEdge.relInterior`);
- face diagonal → `boundaryFacetInterior` (`relInterior ⊆ frontier`: in the carrier, not in openCube
  since a coordinate is constantly 0 or 1);
- space diagonal → `solidInterior` (`relInterior ⊆ interior = openCube`: `(t,t,t)` has all coords in
  `(0,1)`).
- `certOfLocation` builds the one-sector `fullSector` model; the load-bearing `angle_bridge` is
  exactly the computed `PearlAngleSum = loc.targetAngle`. The 19 `cert_<edge>` defs are genuine, valid
  certificates (no vacuity).

### 4. Assembly

- `cubePearlCert_nonempty`: dispatcher casing the source edge over the 6 pieces × 6 pairs (36
  branches) to the matching per-edge certificate.
- `cubePearlAngleData : CubePearlAngleData` — the **constructed** isolate (`LocationData cubeSolid
  (Pearls …)`), the cube analogue of `regularTetLocationData`.
- `regularTet_cube_no_equidecomp_final (hmatch : Σ₁ = Σ₂) : False` — **unconditional except for
  `hmatch`**: passes `Rdata := cubePearlAngleData`, discharges pearl-nonemptiness via
  `pearls_nonempty_of_pieces_nonempty regularTetSolid_pieces_nonempty`.

## Chapter 9 status

Both solids concrete; both faithfulness bridges, both `LocationData`s, both angle normalizations, the
cube classification isolate, and the regular-tet pearl nonemptiness are **all proven/constructed**.
The single remaining honest input is the book's piece-matching double count `Σ₁ = Σ₂` (the geometric
content of `BricardDoubleCount.sigma_match` / the upstream `decomp`-derived match). Per the corrected
route, the literal `hQ_pi2` is *not used* — it is false on the Kuhn cube (diagonal pearls); the
satisfiable `angleClassQ(externalPart) = 0` replaces it, proven unconditionally upstream.

## Honest classification

- **FAITHFUL / unconditional:** all dihedral/angle-sum lemmas, `pearlAngleSum_kuhn_terms`,
  `closedCube_subset_kuhnSolid_carrier`, `interior_kuhn_eq_openCube`, the three containments, the 19
  `cert_<edge>`, `cubePearlCert_nonempty`, `cubePearlAngleData`.
- **CONDITIONAL-honest on `Σ₁ = Σ₂`:** `regularTet_cube_no_equidecomp_final`. The premise is the
  genuine double-count residue; everything else is discharged. Not vacuous (`cubePearlAngleData` is a
  real inhabitant; the cube external part vanishing is proven *for it*).
