# CODEX BRIEF (uisai2-local): Ch36 Esplit — Meisters two-ears / the ear-diagonal supply

Repo ~/repos/proof_in_the_book (zinan-overnight). CREATE ONLY ProofsInTheBook/ZinanCh36Ears.lean.
Verify locally: export PATH=$HOME/.elan/bin:$PATH && lake env lean ProofsInTheBook/ZinanCh36Ears.lean.
Rules: no sorry/admit/axiom/native_decide; clean-3.

## Context: AUDIT_CAMPAIGN.md Ch36 row + HANDOFF/outbox/ch36-assembly-report.md: the campaign's
artGallery_strict_mod_M needs Esplit : ∀ P rho, 4 <= m -> EarValueSplitData P rho (ear P) (the
ear-diagonal supply WITHOUT the exterior field — ZinanCh36Assembly defines EarValueSplitData).
No unconditional producer is landed. THE JOB: produce it (Meisters' ear theorem for strict
simple polygons).
## Route (classical, design honestly against the landed substrate):
1. INVENTORY: PolygonEarExistence/PolygonEarDelete/PolygonCutOracle — what diagonal-existence
   machinery exists (IsDiagonal' production? the convex-vertex selection? grep `isConvexVertex`,
   `leftmost`, `extreme`); the Ch36 campaign's own tools (the generic-point selectors, the
   separation machinery in ZinanCh36Perturb/FFCT-class files, windCross characterizations).
2. The classical proof: pick an extreme vertex v (e.g. lexicographic-min — exists, landed?);
   v is convex; the candidate diagonal (v-1, v+1): if no other vertex inside the triangle
   (v-1, v, v+1), it IS a diagonal (the IsDiagonal' fields: interior-disjointness from the
   boundary — the landed windCross/crossing machinery characterizes diagonals?); else the
   farthest-inside vertex u gives the diagonal (v, u)... produce EarValueSplitData at SOME index
   (the `ear P` choice function: define it via classical choice from the existence). The hard
   formalization points: "no vertex inside the triangle" -> the diagonal's interior-disjointness
   (the landed EdgeIntersectionCondition / the Straddle-file tools!); the farthest-blocker
   argument's maximality. USE the campaign's 2D toolkit (det2/side functions, the convex-weight
   collapse patterns) — this is plane geometry the repo is now rich in.
3. Honest scoping: EarValueSplitData also wants LeftStrictAxioms/RightStrictAxioms + the
   RayDirections with common r — read what those need (the strictness of the two sub-polygons:
   the landed subpolygon tuple machinery + the diagonal's strict-side facts). Land the existence
   chain; name sharply what resists.
4. Target: `esplit_holds : ∀ {m} (P) (rho), 4 <= m -> EarValueSplitData P rho (earChoice P)` =>
   artGallery's Esplit input dissolves => report the new Ch36 surface ({rest, M} only).
## Deliverable: ZinanCh36Ears.lean (0 errors, clean-3) + HANDOFF/outbox/ch36-ears-report.md.
No git commit. Grind to terminal.
