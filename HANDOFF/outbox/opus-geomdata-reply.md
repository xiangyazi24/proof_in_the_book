# opus-geomdata reply — the last three Ch36 residuals (`PolygonGeometryData.lean`)

**Status: HONEST PARTIAL — faithfulness/non-vacuity layer + conditional headline assembled
(clean-3, 0 sorry/axiom/admit/native_decide). The three residuals are NOT discharged
unconditionally; they are the substrate's deliberately-isolated Jordan / convex-position /
peel-order content. Precise blocking analysis below.**

**File:** `ProofsInTheBook/PolygonGeometryData.lean` (NEW, the only file I own, ~282 lines).
**Branch:** `main` (no switch, no commit). **Server:** `uisai1`.
**Build dep:** `ProofsInTheBook.PolygonDegenerateWall` → *Build completed successfully (8441 jobs)*.
**Verification (uisai1):** `lake env lean ProofsInTheBook/PolygonGeometryData.lean` → RC=0.

## Headline finding (the load-bearing conclusion)

The Chapter-36 stack is **architected without a Jordan curve theorem**. It supplies a *finite-
Jordan substitute* — boundary-free local constancy of the ray-crossing region indicator
(`openSegment_region'_const_of_boundary_free`, already unconditional) — but **no machinery that
produces an interior region seed, a convex-vertex region containment, or a half-plane
separation from first principles.** The three target residuals (`hconv`, `D`, `M`) are *exactly*
the points where such content is required, and the design isolates them as inputs by
construction. I verified this against the actual source (not impression):

- `IsConvexVertex' P ρ i` (= the field `hconv` and `D.convexVertex_spec`) is **definitionally**
  `closedTri(prev,i,next) ⊆ {x | ClosedRegion' P ρ x}` (`PolygonSideCrossing.lean:1187`). Its
  general-polygon form `PolygonConvexVertex.exists_convex_vertex` is **stated relative to**
  `ExtremeConvexResidue`, a bundle that *carries the convexity as a hypothesis* — nothing in the
  substrate derives it.
- `OffDiagDisjoint` (= `D.disjoint`) is declared at its def site (`PolygonOracle.lean:547-557`)
  to be *"the irreducibly-geometric half-plane separation"*.
- `DiagonalAttachInput` (= `M`) is declared (`PolygonLast.lean:472-475`) *"a strong hypothesis
  (universal …)"*; the file discharges only its index-freshness (via the proved
  `leftRight_image_inter`) and certifies non-vacuity.
- `PolygonSeparation.lean:42-49` states outright that the directional parity transport is *"the
  irreducible single-edge-jump / half-plane Jordan content that the entire Chapter-36 stack
  keeps as a named input."*

So a *fully unconditional* `artGallery_strict` is **not reachable from this substrate** without
building a new Jordan / convex-position layer (a genuinely separate ~hundreds-of-lines campaign,
not a "one resistant field" residue).

## What is PROVED (unconditional, clean-3: {propext, Classical.choice, Quot.sound})

`#print axioms` confirmed clean-3 on all of:
`artGallery_strict`, `triangleConvexLeaf_faithful`, `residualGeometryData_nonvacuous`,
`diagonalAttachInput_attach_nonvacuous`.

- **`hull_vertices_mem_region`** — the three hull vertices of any 3-gon are in the closed region
  (the `OnBoundary` branch). Confirms `IsConvexVertex'` is not demanding membership of an
  impossible point.
- **`triangleConvexLeaf_faithful`** — `hconv`'s `IsConvexVertex' Q σ ⟨1⟩` is *equivalent* to the
  genuine `closedTri(v0,v1,v2) ⊆ region` containment (via `base_subset_iff_convexVertex_one`),
  i.e. the honest finite-Jordan obligation, not a vacuous/over-strong premise.
- **`residualGeometryData_nonvacuous`** — `ResidualGeometryData P ρ` is inhabited *exactly when*
  a genuine `CutGeometry` with common rays (`CommonRay`) + half-plane disjointness
  (`OffDiagDisjoint`) is (re-exports `residualGeometryData_of_cutGeometry`). So `D` is a faithful
  decomposition (union field's count/parity half DERIVED, boundary/disjoint/intersection
  carried), not a strengthening.
- **`residualGeometryData_commonRay_satisfiable`** — the `commonRay` field's equation is
  genuinely solvable (re-exports `commonRayDir_valid_for₃`): one `mkPt 1 t*` valid for parent +
  both sub-polygons.
- **`diagonalAttachInput_attach_nonvacuous`** — the `AttachesTo` predicate under `M` is inhabited
  (re-exports `attachesTo_nonvacuous`). `M` is not a trivially-unsatisfiable premise.
- **`artGallery_strict`** — the assembled `⌊n/3⌋` art-gallery headline for any
  `StrictSimplePolygon n` with ray `ρ`, **conditional on exactly the three residuals** and
  threading the unconditional parity core (`unconditionalRayIndepInput_triangle`,
  `triangleExteriorEven_unconditional`). Strength identical to
  `PolygonDegenerateWall.artGallery_strict_unconditional`; not a co-extensive re-wrapper of
  `ResidualGeometryData` (it re-exports the existing assembly and adds the per-residual
  faithfulness certificates above).

## Precise residue (the concrete failing chain), per `hconv` (the one bounded candidate)

`hconv`'s remaining content reduces to ONE missing fact: **an interior point of the triangle has
ODD `CrossingNumber'` for some valid ray** (then ray-independence transports the parity to `σ`,
and `openSegment_region'_const_of_boundary_free` propagates region-membership across the hull).

The natural seed is the centroid `g`, where `side σ.r g q0 + side σ.r g q1 + side σ.r g q2 = 0`
(linearity of `det2` on `(q0-g)+(q1-g)+(q2-g)=0`). For a vertex-line-avoiding valid ray this
forces **exactly two edges to `Span`** (the two incident to the lone-sign vertex). The residue is
then the **forward-guard count**: showing **exactly one** of those two spanning edges has
`0 ≤ crossTau` (the line through `g` meets the boundary once forward, once backward). This needs
the sign of `crossTau` from the geometry — equivalently `closedTri ∩ line(g, τ.r) = chord` with
`g` strictly interior so its line-parameter `0` lies strictly between the two boundary
intersection parameters `τ_0, τ_2` (hence `τ_0·τ_2 < 0`, exactly one forward). The substrate has
**no lemma** computing `crossTau`'s sign nor the chord characterization; building it (Mathlib:
convex ∩ affine subspace, bounded convex subset of a line = segment, relative-interior strict-
betweenness) is ~300-400 new lines for `hconv` alone, and even then `D`/`M` (the genuinely
irreducible half-plane + peel content) remain. Documented in full in the file's Part 5
(`residue analysis`).

## Notes / discipline

- No codex / OpenAI tooling used (resource rule respected). Stayed on `main`, no commits, no
  branch switch. Only touched the NEW file `PolygonGeometryData.lean`.
- Verified EXCLUSIVELY via rsync + `lake env lean` on `uisai1` (no local `lake build`/`lake env
  lean` on the Mac).
- This is the playbook §3.3 honest outcome: rather than fake a vacuous/over-strong discharge of
  Jordan content the substrate cannot supply, I certified the three residuals' faithfulness/non-
  vacuity, assembled the conditional headline, and named the precise blocking math for the one
  bounded candidate (`hconv`). The headline `artGallery_strict` is `CONDITIONAL-honest` on three
  satisfiable, faithful planar/combinatorial inputs; the entire parity/count core below is
  unconditional.
