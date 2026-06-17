# Ch13 (Cauchy rigidity) — doctrine (2026-06-17, after §3.3 audit)

## Finding (AUDIT-ch13-2026-06-17.md, codex verdict COMBINATORIAL-CORE-ONLY)
`chapter13` / `chapter13_rigidity` are VACUOUS as stated: `CauchyRigidityCertificate.isEmpty` proves
the cert premise is EMPTY for any edgeSigns, so the implications say nothing about real convex
polyhedra. The combinatorial sign-counting + arm-obstruction core IS proven (46 thms clean-3); what's
missing is the flex→certificate GEOMETRY bridge (line-454 TODO). `Ch13Realization.lean` has a
CONDITIONAL `ConvexPolytopeRealization` interface + `realization_rigid` (534-543), but "not a full ℝ³
polytope model, conditional on a realization datum" (header 16-18, 34-39).

## Goal (one sentence)
Make Chapter 13's rigidity headline NON-VACUOUS (not conditional on an uninhabitable cert) — ideally
as unconditional as feasible, like ch35 was driven to.

## Avenues
(a) [PRIMARY, tractable] Route the headline through the SATISFIABLE realization interface: a theorem
    `chapter13_realization (R : ConvexPolytopeRealization …) : Rigid …` via `realization_rigid`, where
    `ConvexPolytopeRealization` is VERIFIED satisfiable (inhabitable for an actual polytope — unlike the
    empty cert). This removes the empty-cert vacuity; residual = the realization datum (analogous to
    ch35's recursion residuals — a satisfiable interface, not a False). FIRST verify ConvexPolytopeRealization
    is not ALSO empty/vacuous (§3.3 check).
(b) [big] Build the full ℝ³ convex-polytope model + flex→certificate bridge: convex polytope type, two
    isometric embeddings, dihedral-angle signs, vertex-link↔combinatorial-cyclic-order bridge,
    incidence-derived face/vertex sign counts. Major geometry formalization (separate campaign).
(c) [honest middle] If (a)'s interface is itself only conditionally satisfiable, document chapter13 as
    the combinatorial core + the realization interface as the named residual, with the precise ℝ³ gap
    enumerated (the audit's §5 list). No vacuity hidden.

## Terminal conditions
- SUCCESS: a non-vacuous Cauchy rigidity headline — `chapter13_realization` conditional on a VERIFIED-
  satisfiable realization interface (clean-3), with any residual a genuine satisfiable interface (not
  an empty cert). Full ℝ³ (b) is the stretch goal.
- §3.3: verify EVERY interface (ConvexPolytopeRealization) is satisfiable before banking — the empty-cert
  trap already bit here once.

## Note
Start AFTER ch35 closes (user's order). cx2 scopes the realization interface in parallel.

## Avenue (b) SCOPED (2026-06-17, ChatGPT survey AUDIT-ch13-r3-2026-06-17.md)
VERDICT: full ℝ³ is NOT a bounded grind — a from-scratch ℝ³/polyhedral-geometry layer. Mathlib has
Convex/convexHull/IsExposed/Euclidean/Isometry/InnerProductGeometry.angle but NO polytope-face/incidence/
boundary-complex API, NO spherical-trig, NO dihedral-angle abstraction. 7 bridge pieces; hardest = piece1
(boundary complex from convexHull) OR piece6 (vertex-link↔combinatorial-order + spherical-arm bridge).
The genuinely-nontrivial flex CANNOT be instantiated (Cauchy: no convex flex) — the theorem is the
contradiction direction (congruent-faced ⟹ congruent), needing the full bridge + the repo's arm lemma.
Smaller faithful target: TriangulatedEuclideanPolyhedron (coords + face planes/normals + supporting-
halfspace convexity + vertex-link order) + CongruentTriangulatedRealizations(P,Q, equal edge lengths).

### Bounded first sub-goals (b1 → b…), ranked:
(b1) [START] Define TriangulatedEuclideanPolyhedron M (geometric realization: pos:Vertex→EuclideanSpace ℝ (Fin 3),
     face planes/outward normals, supporting-halfspace convexity, nondegeneracy) + construct the TETRAHEDRON
     instance (concrete ℝ³ coords, verify certificates). Real-ℝ³ witness (stronger than abstract tetraCubeCorner).
(b2) dihedralAngle on edges (from oriented face normals / perpendicular-plane 2D angle).
(b3) vertex-link bridge: geometric cyclic order around v = combinatorial link order (piece 6, the hard gate).
(b4) edgeSign from real dihedral-angle difference; count bridge from one incidence structure.
(b5) wire into chapter13_realization's R: ConvexPolytopeRealization ← TriangulatedEuclideanPolyhedron (+CongruentRealizations)
     so the headline is about REAL ℝ³ polyhedra, not the abstract certificate.
SCALE: a major multi-session campaign. (b1) is bounded + valuable groundwork; pieces (b3)/(b4) are the hard core.
STRATEGIC: surfaced to Xiang — full (b) is a from-scratch ℝ³ geometry build; his call whether to push past (b1).
