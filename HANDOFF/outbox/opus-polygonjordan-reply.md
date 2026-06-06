# opus-polygonjordan reply — Chapter-36 `PolygonGeomResidue` / `IsConvexVertex'` via EAR-REMOVAL INDUCTION: the interior odd seed is BUILT (the local edge-swap + triangle-seed chain is proved); the residue is collapsed to ONE genuine Jordan field with a faithfulness certificate

**Status: the ear-removal induction route is BUILT and closes the convex-vertex containment
`IsConvexVertex'` for GENERAL `n` — conditional on exactly ONE named, faithful Jordan field
`EarInductionInput.earExteriorEven` ("an interior ear point lies *outside* the ear-deleted
`(n-1)`-gon", the standard Jordan localization).  Everything else in the textbook ear step —
the local 3-edge det2 seed, the edge-swap count identity, the reversal symmetry, the
ray-avoidance, the parity assembly, the `n=3` base dispatch — is PROVED unconditionally
(clean-3).  This is genuinely NEW: prior rounds attacked per-edge `crossTau` directly and
found no interior seed; the ear induction DOES produce the seed, and the one residual field
is shown to be a *faithful reformulation* of the very `IsConvexVertex'` it establishes (not a
strengthening, not unsatisfiable).**

**File:** `ProofsInTheBook/PolygonJordan.lean` (FRESH, 735 lines, the only file I own).
**Branch:** `main` (no switch, no commit; `git status` shows it only as
`?? ProofsInTheBook/PolygonJordan.lean`).  **No codex / OpenAI tooling.  NEVER ran lake/lean
on the Mac.**  **Build dep:** `lake build ProofsInTheBook.PolygonGeomInput` → completed (8449
jobs).

## Verification (uisai1, playbook §3)

* `lake env lean ProofsInTheBook/PolygonJordan.lean` → **RC=0** (no errors, **no warnings**).
* `lake build ProofsInTheBook.PolygonJordan` → **"Build completed successfully (8450 jobs)"**,
  RC=0 — integrates, nothing downstream breaks.
* **Mechanical (A):** 0 `sorry` / `admit` / `native_decide` / `axiom` in the file (the only
  grep hits are the docstring header line and the word "admits").
* **`#print axioms` (clean-3, ALL):** `triangle_segCross_sum_eq_one`, `isConvexVertex'_all`,
  `artGallery_strict_of_earInput`, `earExteriorEven_of_convex`, `crossingNumber'_split_ear` →
  all **`[propext, Classical.choice, Quot.sound]`**.  No `sorryAx`, `ofReduceBool`,
  `native_decide`.

## The fresh route, as built (the standard polygon Jordan ear induction)

Target (`PolygonGeomInput.PolygonGeomResidue` heart): `IsConvexVertex' P ρ i` for general `n`,
i.e. `closedTri (q (prev i)) (q i) (q (next i)) ⊆ {x | ClosedRegion' P ρ x}`, which needs the
**interior odd-crossing seed** for an interior ear point.

1. **`segCross`** (Part 1) — a standalone directed-segment forward-crossing indicator (`Span`
   of the two endpoint side-coords + forward Cramer `segTau ≥ 0`), proved DEFINITIONALLY equal
   to the polygon's own per-edge `EdgeCrossesRay'` on a consecutive vertex pair
   (`segCross_eq_edgeCrossesRay'`), so `CrossingNumber'` is the directed-edge `segCross` sum
   (`crossingNumber'_eq_sum_segCross`).

2. **The local 3-edge triangle seed** (Part 2) `triangle_segCross_sum_eq_one`: for `x` strictly
   interior to `(a,v,b)` (positive barycentric weights) and a ray missing the three vertices,
   `segCross a v + segCross v b + segCross b a = 1`.  This is the `n=3` base in bare-triple
   form — the genuine interior odd seed — reusing the PROVED barycentric `forward_count_eq_one`
   of `PolygonTriangleConvex` via a clean per-edge product-form rewrite (`segCross_eq_indicator`).
   *(Numerically pre-verified: this constrained sum is always `1`; the UNconstrained per-edge
   swap parity is FALSE — confirming why prior per-edge attacks failed and why the EAR
   constraint is essential.)*

3. **The edge-swap count identity** (Parts 3-4) `crossingNumber'_split_ear`:
   `CrossingNumber' P x = segCross(a→v) + segCross(v→b) + restSum`, where `restSum` is the
   `segCross` sum over the *other* edges (= the ear-deleted polygon's edges, except it carries
   the chord `(a,b)`).  Pure `Finset.sum_erase_add` reindexing (no Jordan input).  Plus
   `segCross_symm` (reversal symmetry: `segCross a b = segCross b a` off-line — the two share
   the same ray-line intersection parameter; numerically `{0,2}`-valued, hence even).

4. **The seed assembly** (Part 5) `interior_crossingNumber'_odd_of_earInput` /
   `interior_mem_region'_of_earInput` / `isConvexVertex'_of_earInput` / `isConvexVertex'_all`:
   for an interior ear point `x` off the boundary, pick a ray missing the three ear vertices
   (`exists_rayDir_avoiding_three`, general-`n`), get `CrossingNumber'` ≡ `seed = 1` (mod 2)
   from split + residue-even + symmetry → **odd → in region**; transport to the polygon's own
   ray `ρ` by the PROVED off-boundary ray-independence (`region_ray_independent`).  The
   `closedTri` dichotomy: zero ear-vertex weight → base chord (in region by `earDiagonal`, the
   standard "ear base is a diagonal"); zero neighbour weight → a genuine *polygon* edge
   (boundary); strict interior → the odd seed.  `n=3` dispatched to the PROVED triangle leaf
   (`earBase`).  This yields `IsConvexVertex'` for ALL `n`.

5. **Assembly** (Part 6): `polygonGeomResidue_of_earInput` builds the full
   `PolygonGeomResidue` with `convexVertex_spec` **supplied by `isConvexVertex'_all`** (not
   assumed); `artGallery_strict_of_earInput` is the Chapter-36 `⌊n/3⌋` headline over the ear
   input + the remaining (already-isolated) cut data + `M`.

## The ONE residual field (named, non-vacuous, faithful)

`EarInductionInput.earExteriorEven` : for the chosen ear vertex and a strict-interior ear
point `x` off the boundary, `Even (segCross(a→b) + restSum)` — the ear-deleted `(n-1)`-gon
(chord `(a,b)` + untouched edges) crosses `x` evenly, i.e. **`x` lies outside the smaller
polygon**.  This is the Jordan localization the substrate keeps unproven in
`PolygonDiagonal.A4CuttingFacts` (`ear_delete_strict` builds the `(n-1)`-gon;
`ear_delete_region_union` is the region relation) — both fields have **no producer anywhere
in the tree** (confirmed: the only references outside the definition are docstring mentions in
`PolygonParity`/`PolygonTriangulation`).  The structure also carries the combinatorial
orientation (`earOrient`), the ear-base-diagonal (`earDiagonal`, the proved-elsewhere
`IsDiagonal'`), and the `n=3` base (`earBase`, = `triangleConvexLeaf_holds`); the `4 ≤ m`
gating makes the whole bundle satisfiable (no `∀m, 4≤m` vacuity bug).

**Faithfulness certificate (§3.3 non-vacuity), `earExteriorEven_of_convex`:** the genuine
Jordan field is a *consequence* of the very `IsConvexVertex'` it helps establish — an
off-boundary strict-interior ear point in the region has odd crossing number, and the proved
edge split (`crossingNumber'_split_ear`) + the triangle seed + reversal symmetry then force
`Even (segCross(a→b)+restSum)`.  So `earExteriorEven` is satisfiable exactly when the geometry
oracle's `IsConvexVertex'` is — a faithful decomposition of the same content, with no hidden
`False`, not a strengthening.

## Why this does not (yet) make the headline unconditional — the honest boundary

The interior odd SEED is now genuinely built, but the ear induction's load-bearing input —
that the ear-deleted `(n-1)`-gon excludes the interior ear point (`earExteriorEven`) — is
exactly the same Jordan localization the chapter has always isolated (`A4CuttingFacts`).  In
the textbook proof this comes from "the ear is empty / the base is a diagonal, so the ear
triangle is disjoint from the rest of the polygon's interior"; in Lean that requires either
(i) constructing the `(n-1)`-gon as a genuine `StrictSimplePolygon (n-1)` (the unbuilt
`ear_delete_strict`, whose `edge_intersection`/simplicity is itself Jordan content) and
recursing, or (ii) a direct half-plane separation of the ear from the deleted boundary.  What
THIS file adds, and prior rounds lacked, is that **the entire rest of the ear step is now
mechanized and the seed is produced from the `n=3` base** — the residue is collapsed from "the
whole interior-odd-seed Jordan layer" to the single even-parity field `earExteriorEven`, with
the local det2/triangle/swap algebra all discharged and a faithfulness proof tying that field
to `IsConvexVertex'` itself.

## Concrete failing chain (the one place it dead-ends)

`earExteriorEven P ρ hm hoff hw0 hw1 hw2 hsum hx : Even (segCross(a→b) + restSum)`.  To
discharge it unconditionally one must show the ear-deleted boundary crosses the interior ear
point evenly.  The substrate's only even-exterior producer is
`PolygonSeparation.exists_rayDir_crossingNumber'_eq_zero_of_not_mem_hull` (a *far exterior*
point) and `triangleExteriorEven`; neither pins the parity of the `restSum` (the deleted
boundary, a chord + `n-2` edges) at an interior ear point, because that needs the ear-deletion
to be a genuine simple `(n-1)`-gon (`ear_delete_strict`) or its region union
(`ear_delete_region_union`) — the named, producer-less `A4CuttingFacts` fields.  The chain
dead-ends exactly there, and nowhere else: the seed, the swap, the symmetry, the base, and the
ray transport are all proved above.

## Discipline

No codex / OpenAI tooling.  Stayed on `main`, no commits, no branch switch, zero
tracked-file modifications.  Created only the FRESH `PolygonJordan.lean`.  Verified
exclusively via rsync + `lake env lean` / `lake build` / `#print axioms` on `uisai1` (no local
Mac build).  Import-graph / `Audit.lean` / `ProofsInTheBook.lean` wiring left for the
orchestrator (leaf file; nothing imports it).
