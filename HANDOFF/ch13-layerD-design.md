# Ch13 layer D — the remaining frontier for UNCONDITIONAL Cauchy rigidity

## State after the 2026-06-14 overnight run
- **Spherical arm lemma: FULLY PROVEN, unconditional, clean-3.** Both halves:
  - `≤`: `ZinanFFCT111.spherical_arm_mono_final_ch13 : SphericalArmMonotone` (2026-06-13).
  - strict: `ZinanFFCT112.spherical_arm_mono_strict_uncond` (2026-06-14), via the discharged residue
    `ZinanFFCT113.stuckWitnessExists_holds : StuckWitnessExists` (tiny-opening bootstrap off the ≤ lemma).
- **The arm lemma is now WIRED INTO `chapter13`**: `Chapter13.CauchyArmOpeningObstruction` /
  `CauchyArmClosingObstruction` carry genuine spherical arms and their `.contradiction` is DERIVED from
  `ZinanFFCT112.cauchy_arm_fixed_chord_contradiction_uncond`. The former posited `arm_conclusion` field
  is GONE. `chapter13` is clean-3 and transitively depends on the real arm lemma.
- **`chapter13` is still conditional on `CauchyRigidityCertificate`**, which is never constructed from
  geometry (`CauchyRigidityCertificate` is mentioned only in Chapter13.lean). THIS is layer D.

## What layer D must build (no Mathlib base; repo only has tetra-specific `TetDihedral` for Ch9)

The goal: a constructor `cauchyRigidityCertificate_of_polytopes : (two combinatorially-equivalent
convex polytopes in ℝ³ with congruent corresponding faces but not congruent overall) →
CauchyRigidityCertificate edgeSigns`, making `chapter13` yield unconditional rigidity. Concrete pieces:

1. **Convex polytope model in ℝ³.** A structure with vertices, edges, faces (the combinatorial face
   lattice + the metric embedding), convexity, and the sphere/Euler structure. Mathlib has
   `Polytope`-adjacent convex-geometry but no face-lattice polytope; likely build a bespoke
   `ConvexPolytope3` (vertices : Finset (EuclideanSpace ℝ (Fin 3)), faces, edge incidence, convex hull
   = body, each face planar+convex).

2. **Vertex link as a strictly convex spherical arm.**
   `vertexLink : ConvexPolytope3 → (v : vertex) → StrictConvexSphArm`
   The link of `v` is the intersection of a small sphere at `v` with the polytope — a convex spherical
   polygon whose vertices are the directions of the edges at `v` and whose side lengths are the face
   angles at `v`. Prove it is `StrictConvexSphArm` (strict convexity from polytope convexity).

3. **Congruent faces ⟹ equal link side lengths.** Corresponding faces congruent ⟹ the face angles at
   corresponding vertices agree ⟹ `sideLen (vertexLink P v) = sideLen (vertexLink Q v')` (the
   `equal_sides` field of the obstruction).

4. **Dihedral angle per edge ⟹ link joint angle.** The link joint angle at an edge = the dihedral
   angle of the polytope along that edge. So `jointAngle (vertexLink P v) = dihedral P (edge)`. The
   per-edge SIGN `sign(dihedral P e − dihedral Q e)` is the Cauchy edge sign (`EdgeSign`).

5. **The `CauchyArmVertex` from a vertex.** At each vertex, the two links (from P and Q) have equal
   sides (piece 3) and joints differing by the edge signs (piece 4). The number of strict sign changes
   around the vertex = `signChanges`. When `signChanges ∈ {0,2}`, split the cyclic link into a
   monotone-opening (or closing) arc with a FIXED chord (the shared edge to the next region) — this is
   exactly a `CauchyArmOpeningObstruction` / `ClosingObstruction`, now refuted by the proven arm lemma.
   The `≥ 4` bound (`CauchyArmVertex.four_le_signChanges`) then holds geometrically, not by posited fields.

6. **Assemble the certificate.** `vertexArmData := fun v => cauchyArmVertex_of_link …`; `faceSigns` from
   the per-face sign structure; `total_vertex_eq_total_face` from the global double-count (the sign
   changes counted by vertices = counted by faces); `nontrivial` from non-congruence. Feed to
   `chapter13` for `False` = rigidity.

## Difficulty / route notes
- Pieces 1–2 are the heavy lift (no Mathlib polytope/link substrate). Piece 5's "split the cyclic link
  at a fixed chord" is the geometric heart of Cauchy's sign lemma (Lemma II) — but the arm lemma it
  needs is now PROVEN, so piece 5 reduces to the combinatorial cyclic-sign-change splitting + applying
  `cauchy_arm_fixed_chord_contradiction_uncond`.
- This is a multi-session campaign. The deep analytic obstacle (the arm lemma) is already removed; layer
  D is laborious convex-polytope bookkeeping, not new deep mathematics.
- Suggested order: 1 → 2 → 3 → 4 → 5 → 6, each its own file, `#print axioms` clean-3 per piece, no sorry
  banking. Dispatch the heavy pieces (1,2) to focused agents.

---

## SHARP ARCHITECTURE (Plan agent, 2026-06-14) — HYBRID, §3.3-driven

**Decision: HYBRID** — extrinsic LOCAL geometry (per-vertex, derived) + intrinsic GLOBAL combinatorics
(reuse `CombMap`). The seam sits exactly on the §3.3 fault line.

**The §3.3 fault line (load-bearing):** two bridges MUST be THEOREMS, never structure fields/hypotheses:
- **Bridge A** `sideLen (vertexLink S) i = EuclideanGeometry.angle (S.p i) S.o (S.p (i+1))` (link side = face angle).
- **Bridge B** `jointAngle (vertexLink S) i = dihedral angle along edge i` (spherical angle = dihedral).
Positing either (or carrying `harm : StrictConvexSphArm (vertexLink S)` as a field) reintroduces the
exact trap just removed from `arm_conclusion`. REJECT any such design in review.

**Steps (one file each, clean-3 per file, no sorry banking):**
1. `Ch13VertexStar.lean` — `structure VertexStar` (apex o, neighbors p : Fin n → ℝ³, ℝ³-DERIVABLE strict
   local convexity predicate matching `StrictConvexSphPolygon`'s fields). `edgeDir`, `vertexLink`,
   and **`vertexLink_strictArm : StrictConvexSphArm (vertexLink S)`** (HARD sub-lemma #1: ℝ³ apex cone
   convexity ⟹ the 5 `StrictConvexSphPolygon` fields via `sOrient`/`det3`; `open_hemisphere` = inward normal).
2. `Ch13LinkBridges.lean` — Bridge A (easy: `cos_angle` + normalization) and **Bridge B** (HARD sub-lemma
   #2: spherical-angle = dihedral; reuse `TetDihedral.projOut`/`inner_projOut_projOut`). §3.3-critical.
3. `Ch13Congruence.lean` — `faceCongruent` (Mathlib `Congruent`) ⟹ equal link sides (Bridge A both sides).
4. `Ch13EdgeSign.lean` — `edgeSign` per edge; `cauchyArmVertex_of_stars` (signChanges = cyclic flip count;
   `signChanges_even` = cyclic parity; 0/2 → obstruction via the cyclic-split, HARD sub-lemma #3 — feeds
   the PROVEN `cauchy_arm_fixed_chord_contradiction_uncond`).
5. `Ch13Certificate.lean` — `CauchyPolytopePair` (CombMap + per-vertex VertexStars for P,Q + faceCongruent
   + not_congruent); Euler/`3F=2E` from `PlanarMap`; `total_vertex_eq_total_face` double-count;
   `cauchyRigidityCertificate_of_pair`.
6. `Ch13Rigidity.lean` — `cauchy_rigidity := chapter13 (cauchyRigidityCertificate_of_pair …)` clean-3.
   **MANDATORY non-vacuity guard**: concrete octahedron `CauchyPolytopePair` inhabiting every field except
   `not_congruent` (else the headline is vacuous).

**Hard sub-lemmas (dispatch):** #1 vertexLink_strictArm (focused agent), #2 Bridge B spherical=dihedral
(Opus, §3.3 load-bearing — must be a theorem), #3 cyclic sign-change split (focused agent, arm lemma done).
**Parallelizable independent:** `signChanges_even`, `total_vertex_eq_total_face` (pure CombMap/Fin-cyclic).

**Honest minimal residual:** the `not_congruent ⟹ nontrivial` global-rigidity step is the subtlest
non-arm piece; if it blocks, ship `cauchy_rigidity` conditional on that ONE tagged hypothesis (everything
else unconditional) — still a major advance over the current fully-unconstructed certificate.

---

## REFINED ASSEMBLY PLAN + design insights (2026-06-14, after Steps 1-3 done)

DONE+verified clean-3: Step 1 `Ch13VertexStar` (VertexStar, vertexLink_strictArm, Bridge A), Step 2
`Ch13Dihedral` (Bridge B jointAngle=dihedral, independent def), Step 3 `Ch13LinkSides` (equal face
angles ⟹ equal link sides). Step 4 `Ch13LemmaII` dispatched.

**Insight 1 — closed-polygon chord = closing side.** A vertex link is a CLOSED convex spherical polygon
(`StrictConvexSphArm`, n+1 vertices). Its `endpt = sDist (A 0)(A (Fin.last n))` is the CLOSING edge =
a side length. So for the signChanges=0 case (all joints of B ≥ A, some strict, equal sides), the arm
lemma gives endpt A < endpt B, but endpt = closing side is EQUAL by hsides ⟹ contradiction. This is the
`cauchy_all_open_fixed_closing` half of Lemma II — uses the proven arm lemma directly, no cut needed.

**Insight 2 — signChanges=2 via two-arc shared chord.** Two split vertices cut the cycle into a "A≤B"
arc and a "B≤A" arc sharing two endpoints. Arm lemma on each ⟹ chord_A ≤ chord_B AND chord_B ≤ chord_A
(same chord) ⟹ equal ⟹ strict arm lemma contradiction. Needs sub-arm construction (repo cut-arm machinery).

**Insight 3 — the ACTIVE-SUBGRAPH subtlety (critical for Step 5).** A vertex where P,Q have all dihedrals
equal has signChanges=0 and is NOT a `CauchyArmVertex` (can't produce the obstruction — no strict joint).
So Cauchy's argument restricts to the ACTIVE subgraph: the edges where `edgeSign ≠ 0`. `chapter13`'s
certificate `V/E/F` and the `≥4`-per-vertex + Euler bound are for the ACTIVE subgraph (a subgraph of the
sphere map). Step 5 must build the active subgraph (not the full polytope graph) and apply Euler there.
Vertices not incident to any active edge are excluded. Each active vertex has ≥4 sign changes among its
ACTIVE incident edges (Lemma II restricted to active edges).

**Step 5 (`Ch13Certificate`) plan:** `CauchyPolytopePair` = a `CombMap` sphere map + per-vertex
VertexStars for P and Q (consistent with incidence) + `faceCongruent` + `not_congruent`. Build the
active subgraph from `edgeSign`; `vertexArmData v` = `cauchyArmVertex_of_links` (Step 4) on v's two links
restricted to active edges; `faceSigns` from per-face active signs; `total_vertex_eq_total_face` =
CombMap orbit double-count; `nontrivial` from `not_congruent` (the subtle step — global non-congruence ⟹
some dihedral differs ⟹ some active edge; if it blocks, ship conditional on this ONE hypothesis).

**Step 6 (`Ch13Rigidity`):** `cauchy_rigidity := chapter13 (cauchyRigidityCertificate_of_pair …)`.
MANDATORY non-vacuity: a concrete octahedron `CauchyPolytopePair` inhabiting every field but `not_congruent`.
