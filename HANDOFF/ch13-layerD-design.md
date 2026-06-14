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
