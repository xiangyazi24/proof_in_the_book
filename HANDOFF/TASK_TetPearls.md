# TASK: TetPearls.lean — tetrahedral solids + pearls partition (Ch09 layer 2-3)

Create ProofsInTheBook/TetPearls.lean (you own ONLY this file). Per HANDOFF/CH09_GEOMETRY_DESIGN.md
sections 1-3: implement Tet (4 affinely independent points, carrier = convexHull, interior),
TetSolid (Finset Tet, pairwise disjoint interiors, carrier), TetEquidecomp (piece bijection +
isometries, reflections allowed), Segment3 (carrier/relInterior/coord), PieceEdges (the 6 edges of
each tetrahedron), segmentIntersectionPoints (finite: two closed segments in ℝ³ intersect in at most
a point unless collinear-overlapping — handle the overlap case by returning the 4 endpoint-projections
or design around it; document), BreakpointsOnEdge, Pearls, and the four partition lemmas:
pearls_finite, raw_edge_covered_by_pearls, pearl_interiors_disjoint_on_same_edge,
incidence_constant_on_pearl. Also Tet.relativeInterior_eq_interior and volume_tet
(volume = |det|/6 — Mathlib likely has simplex volume; search MeasureTheory for parallelepiped /
simplex volume lemmas). NO sorry/axiom; if one lemma genuinely resists after real attempts, isolate
it as ONE named statement and report exactly. lake env lean. Append HANDOFF/outbox/tetpearls-reply.md.
