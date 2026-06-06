# opus-residualdata reply — the `D` oracle (`ResidualGeometryData` supplier), isolated

**Status: HONEST PARTIAL (playbook §3.3 outcome). The `D` supplier is NOT
unconditionally constructible from the Chapter-36 substrate; I isolated the
irreducible content as a SINGLE named honest input, built the genuine reductions
around it (NOT a co-extensive re-wrapper), and certified non-vacuity. Clean-3,
0 sorry/axiom/admit/native_decide.**

**File:** `ProofsInTheBook/PolygonResidualData.lean` (NEW, the only file I own, ~270 lines).
**Branch:** `main` (no switch, no commit). **Server:** `uisai1`. **No codex / OpenAI tooling.**
**Build dep:** `ProofsInTheBook.PolygonTriangleConvex` → *Build completed (8443 jobs)*.
**Verification (uisai1):** `lake env lean ProofsInTheBook/PolygonResidualData.lean` → **RC=0**.
NEVER ran lake/lean on the Mac. Leaf file; import graph / `Audit.lean` untouched.

## The verdict (source-level exhaustion, triply confirmed)

A fully unconditional `residualGeometryData_of_polygon` is **not reachable from this
substrate**. Every substantive field of `ResidualGeometryData` is a per-polygon
planar Jordan / convex-position / half-plane primitive the substrate is *architected
to isolate*, with **no producer** from a bare `StrictSimplePolygon` + `RayDirection`.
I verified each against the actual source (not impression):

- **`convexVertex_spec : IsConvexVertex'` (general `n`)** — the substrate's only route
  `PolygonConvexVertex.exists_convex_vertex` is *stated relative to* the bundle
  `ExtremeConvexResidue`, which **carries the convexity as a hypothesis**
  (`PolygonConvexVertex.lean:215-243`). The unconditional triangle template
  `triangleConvexLeaf_holds` works *only* at `n = 3` (adjacent triangle = whole hull
  = the 3 polygon edges, so `crossingNumber'_interior_eq_one`, a sum over **all**
  edges, applies). For general `n` the adjacent triangle's third side is a **chord**,
  not a polygon edge, so the interior-odd / forward-count argument does not transfer.
  This is the precise reason the triconvex engine does not lift.
- **`transversality : DiagonalTransversality'`** — packs boundary-freeness of the
  ear/slide open segments (`PolygonSideCrossing.lean:1204-1283`); `exists_diagonal'`
  *consumes* it, never produces it.
- **`leftAxioms`/`rightAxioms`** — carry `noncollinear` (cut-corner triples could be
  collinear) + `edge_inter` (diagonal meets arc edges properly): the source itself
  flags these as "the genuine planar content at a cut … the two `StrictSimplePolygon`
  axioms that are *not* combinatorial" (`PolygonCutOracle.lean:250-255`). No producer.
- **`leftRay`/`rightRay`/`commonRay`** — `CommonRay` *is* satisfiable
  (`commonRayDir_valid_for₃`), but the `commonRay` field demands `(leftRay h).r = ρ.r`
  for the **prescribed** `ρ`; a given `ρ.r` may be parallel to a sub-edge, so the rays
  cannot be derived freely for an arbitrary `ρ` — part of the irreducible per-cut datum.
- **`disjoint : OffDiagDisjoint`** — declared at its def site
  (`PolygonOracle.lean:547-557`) to be *"the irreducibly-geometric half-plane
  separation"*. I confirmed there is **no `det2` shortcut**: `ClosedRegion'` is defined
  by the **parity** of the crossing number (`OnBoundary ∨ Odd (CrossingNumber')`,
  `PolygonSideCrossing.lean:276`), *not* by a half-plane sign. The link between
  crossing-parity and the half-plane geometry IS the Jordan content the substrate lacks
  — so the "build it via the separating line / det2 sign" route the spec suggested does
  not connect to the parity definition of the region.
- **`boundary`/`intersection`** — the remaining Jordan-region split data.

So `D` is, by architecture, the bundle of irreducible planar inputs; discharging it
unconditionally is a *separate* Jordan-curve / convex-position campaign (hundreds of
lines), not a residue closable here. This matches both prior independent analyses
(`opus-geomdata-reply.md`, `opus-triconvex-reply.md`).

## What was built (faithful, non-vacuous, NOT a re-wrapper) — all clean-3

1. **`PolygonCutInput`** — the ONE isolated uniform planar input: for every polygon /
   ray, a genuine `CutGeometry` + the common-ray condition `CommonRay` + the half-plane
   disjointness `OffDiagDisjoint`. **Strictly smaller** than a uniform
   `ResidualGeometryData`: it does NOT carry a separate boundary-union datum (that half
   is derived). This is the faithful decomposition basis, isolating exactly the
   irreducible fields enumerated above.
2. **`residualGeometryData_of_polygon (H : PolygonCutInput) P ρ : ResidualGeometryData P ρ`**
   — the `D` supplier, conditional on the single isolated input. It is **not** a
   co-extensive re-wrapper: it builds each datum via `residualGeometryData_of_cutGeometry`,
   whose `boundary` (union) field is *derived* from the real `split_region_union` set
   equality (the count/parity half — discharged in `PolygonOracle`), with only
   `disjoint`/`intersection` carried verbatim. `commonRay` is met by the cut geometry's
   own rays under the supplied `CommonRay`.
3. **`residualSupply_of_input`** — the uniform supplier in the exact shape
   `cutGeometryOracle_of_data` / `artGallery_strict` consume.
4. **`artGallery_strict_one_input (H) (M) P ρ`** — the Chapter-36 `⌊n/3⌋` art-gallery
   headline, conditional on exactly the **single** isolated planar input
   `PolygonCutInput` and the peel oracle `M`. Collapses the seven planar fields of the
   `D` oracle into one named bundle (union/parity half discharged); convex-vertex leaf
   supplied unconditionally by `triangleConvexLeaf_holds`. Conclusion is the genuine
   `⌊n/3⌋` guard bound (`∃ guards, guards.card ≤ n/3 ∧ ∀ x ∈ region, ∃ v ∈ guards, Sees`).
5. **`polygonCutInput_of_uniform` + `polygonCutInput_geom_eq` + `..._convexVertex`** —
   the §3.3 anti-vacuity / faithfulness certificate: `PolygonCutInput` is inhabited
   *exactly when* a uniform `CutGeometry` with common rays + half-plane disjointness is
   (constructor = the decomposition basis), the bundle genuinely *uses* its input
   (`geom = geom` by `rfl`, ruling out a discard-input constant), and the supplier does
   not weaken the convex-vertex spec (`.convexVertex = (H.geom P ρ).convexVertex`).

## Verification (playbook §3 acceptance)

- **A (mechanical):** 0 sorry/admit/axiom/native_decide (grep: only the docstring
  mentions). `lake env lean ProofsInTheBook/PolygonResidualData.lean` → **RC=0**.
- **`#print axioms` (clean-3):** `residualGeometryData_of_polygon`,
  `artGallery_strict_one_input`, `polygonCutInput_of_uniform`, `residualSupply_of_input`
  → all `[propext, Classical.choice, Quot.sound]`.
- **B/C (signature/semantic):** the headline's printed conclusion is the genuine
  `⌊n/3⌋` art-gallery bound; the only geometric inputs are the single named bundle
  `PolygonCutInput` and `M`. **Verdict: CONDITIONAL-honest** on one satisfiable,
  faithful planar input (`PolygonCutInput`, non-vacuity certified) + `M`. Not a vacuous
  conditional (`polygonCutInput_of_uniform` exhibits the inhabiting basis); not a
  co-extensive re-wrapper (union/parity half derived, bundle strictly smaller than `D`).

## The isolated residue (per the task's "isolate ONE honest Prop" instruction)

`PolygonCutInput` is that one named honest input. Its `geom.convexVertex_spec`
(general-`n` `IsConvexVertex'`), `transversality`, `leftAxioms`/`rightAxioms`,
`split_region_intersection`, and the `disj` field (`OffDiagDisjoint`) are the
irreducible Jordan / convex-position / half-plane content. The concrete failing chains
are documented per field in the file header and above. To make `D` unconditional, the
missing front is a planar layer the substrate does not synthesize: an unconditional
producer of (a) a general-`n` convex vertex with adjacent-triangle region containment
(the chord-edge obstruction to lifting `crossingNumber'_interior_eq_one`), (b) the
ear/slide boundary-freeness, (c) the cut-corner strict axioms, and (d) the half-plane
crossing-parity separation `OffDiagDisjoint` — a separate large planar-topology
campaign, not a residual identity.

`M` (`DiagonalAttachInput`) was left untouched (the peel-reordering combinatorial
residual); the headline remains conditional on it as well.

## Discipline

No codex/OpenAI tooling (resource rule respected). Stayed on `main`, no commits, no
branch switch. Only created the NEW file `PolygonResidualData.lean`. Verified
exclusively via rsync + `lake env lean` on `uisai1` (no local build on the Mac).
