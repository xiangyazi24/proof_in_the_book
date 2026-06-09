# Ch36 residue map (Opus worker D, 2026-06-09; orchestrator-condensed — full version in worker transcript)

1. Two endpoints: combinatorial chapter36_artgallery_combinatorial (Chapter36.lean:297, Fisk
   3-coloring) PROVEN; geometric artGallery_strict_attach (PolygonLast.lean:557) honest-conditional
   on (i) CutGeometryOracle / PolygonGeomResidue, (ii) DiagonalAttachInput M.
2. M effectively discharged: core LastToFirstAll PROVEN (PolygonReroot.lean:177); residual =
   structural induction threading canonicalMergedGlue (bookkeeping, no Jordan content). NOTE
   PolygonMClose.lean:503: the UNIVERSAL M is false — route through canonicalMergedGlue only.
3. The bundle reduces (OffDiagDisjoint via segment identity PROVEN; ray-independence PROVEN;
   triangle_isConvexVertex' PROVEN) to ONE irreducible kernel:
   **EarCutData.earDeletedExterior (PolygonEarDelete.lean:379)** ≡ RayCrossingAlternation
   (PolygonWindingBound.lean:211) ≡ EarDeletedWindingZero (PolygonWindingPath.lean:177)
   ≡ LocalJumpSeed (PolygonLocalJump.lean:172).
4. Integer-lift obstruction DISSOLVED on the turning side: PolygonUmlaufsatz.coe_realTurning is
   unconditional; the standalone residue there is pure-ℝ ExtAngleRealSumPm2Pi (realTurning = ±2π,
   moderate, ear-clip induction; not on the guard headline's critical path).
5. EarHalfPlaneContainment is machine-REFUTED (reflex band; earHalfPlane_geometric_content_false;
   straightPathAnchor_blocked_by_reflex_dip) — every "produce a known winding value" route dies
   there. InteriorOddSeed ≡ allConvex (false at reflex) — do not target as stated.
6. RECOMMENDED ROUTE (lighter than the (B) complex-analytic campaign, which would need greenfield
   winding/degree API absent from Mathlib): port ZinanFFCT9.mono_theta's monotone branch-cut angle
   onto the POSITION vector (∂P − x), ordered by crossTau; alternation of eSign falls out of the
   monotone squeeze (the ray-direction genericity axioms already kill the antipodal care-point);
   feed through the PROVEN bridges windCross_mem_of_alternation → earDeletedExterior_of_seed.
   First bricks: thetaPos def + mono lemma; alternation; wiring. No Polygon file cites mono_theta yet.
