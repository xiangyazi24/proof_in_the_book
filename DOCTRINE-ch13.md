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

## Avenue (b) ROUND PLAN to convergence (2026-06-17, after b1+b2 done; ConvexPolytopeRealization spec read)
TARGET (干干净净): construct `ConvexPolytopeRealization M` from a pair of congruent ℝ³
`TriangulatedEuclideanPolyhedron` (P,Q) → `chapter13_realization` becomes a theorem about GENUINE ℝ³
convex polyhedra (Cauchy: congruent-faced convex triangulated polyhedra are congruent), inhabited by the
real tetrahedron. The abstract Cauchy core (46 thms, Ch13*.lean) + realization_rigid are ALREADY clean-3;
the bridge is the only gap. Fields to produce (from Ch13Realization.ConvexPolytopeRealization):
  starP/starQ (VertexStar from ℝ³ link), hnn, edgeSign+edgeSign_inv, sides_eq, close_eq, dartRep,
  interiorActive, twoArc, linkOrder (load-bearing), isSphere/triangle/isSimple.

ROUND R1 (b3a — VertexStar from ℝ³): for a TriangulatedEuclideanPolyhedron P and vertex v, build the
  spherical link = unit vectors (neighbor − pos v)/‖·‖ ∈ S2 in link order → `VertexStar`. Geometric
  sideLen/jointAngle/sDist from real coords. Gives starP/starQ. Verify on tetrahedron.
ROUND R2 (b3b — linkOrder, THE HARD GATE): σ.toList(dartRep v).map edgeSign = link-ordered real-sign list.
  geometric rotational order around v in ℝ³ = combinatorial σ order. The §3.3-load-bearing field.
ROUND R3 (b4 — edgeSign + congruence fields): edgeSign d := sign(dihedralAngleAtDart Q − …P) (b2's
  dihedralSignAtDart), edgeSign_inv; sides_eq/close_eq from CongruentFaces P Q (equal edge lengths);
  interiorActive; twoArc (TwoArcSplitData when signChangesFull=2).
ROUND R4 (b5 — assemble + wire): convexPolytopeRealization_of_euclideanPair (P Q) (hcong) :
  ConvexPolytopeRealization M; chapter13_euclidean via realization_rigid; inhabit w/ tetrahedron pair.
DISPATCH: codex max, single coherent line (hard proof, no parallel splintering). R2 is the gate — if it
  needs spherical-trig Mathlib gaps, dispatch ChatGPT (life/life2) in parallel for the lemma, codex grinds.

## R2/R3 decomposition (2026-06-17, after reading realization_rigid + linkDiff + b2 edgeSign)
KEY INSIGHT: edgeSign is ALREADY b2's `dihedralSignAtDart P Q d = realSignToEdgeSign(dihedralAngleAtDart Q d − dihedralAngleAtDart P d)`.
The linkOrder field `(M.σ.toList dartRep).map edgeSign = (List.ofFn (linkDiff starP-link Q-link)).map realSignToEdgeSign`
decomposes into:
  R2a (HARD geometry → codex-max): `dihedralAngleAtDart P d = (vertexStarOfEuclidean P (tail d)).linkAngle (link-index of d)`
       — the standard fact "dihedral angle at edge e = interior angle of the spherical vertex-figure at the
       link-vertex corresponding to e". Given R2a, linkDiff_i = dihedral_Q − dihedral_P = the exact quantity
       edgeSign uses ⇒ the VALUE match is automatic.
  R2b (order bridge): M.σ.toList(dartRep Q) order = the vertexStarOfEuclidean link order (List.ofFn index) —
       this is the R1d orientation/chirality convention, extended to the full σ-cycle = link cycle.
R3 (mostly mechanical given b2): edgeSign := dihedralSignAtDart; edgeSign_inv (dihedral is α/edge-invariant:
   dihedralAngleAtDart d depends only on the edge of d — prove dihedralAngleAtDart (α d) = dihedralAngleAtDart d);
   sides_eq/close_eq from CongruentFaces P Q (equal edge lengths ⇒ equal spherical link side lengths sDist/sideLen);
   interiorActive (nonzero edgeSign ⇒ some interior jointAngle differs — from R2a + the arm structure);
   twoArc (TwoArcSplitData when signChangesFull=2 — from the abstract Ch13ArmVertex machinery).
R4: assemble ConvexPolytopeRealization (P Q : TriangulatedEuclideanPolyhedron) (hcong : CongruentFaces) →
   realization_rigid gives dihedral_P = dihedral_Q at every vertex ⇒ chapter13_euclidean; inhabit w/ tetra pair.
ROUTING: R2a → codex-max (hard geometry). R2b/R3 → Mac codex or codex-max. R1 must land first.
