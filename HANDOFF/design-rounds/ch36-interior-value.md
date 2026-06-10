(pbook2 wave-6, 2026-06-10, via tab paste) ROUTE C WINS — the split-induction VALUE PACKAGE:
WindValuesWithSign P s := (s = ±1) ∧ ∀ ρ x off-boundary, windCross ∈ {0, s}. Ear split closes
algebraically: L + R = P with L,R ∈ {0,s} and P ∈ {0,±1} excludes s+s=2s ⟹ L=s forces R=0, P=s.
SIGN DISCIPLINE: parametrize by s throughout (orientation-dependent; reversing vertex order flips);
=1 consumers become wrappers. Bricks: route_sign generalization (worker 40-70); package+odd
consequence (worker 30-50); TRIANGLE SIGNED BASE triSign + triangle_windValuesWithSign (master/worker
250-450, from PolygonTriangleConvex's interior crossing + signed eSign); windValues_split_offAll
(worker 80-120); split PERTURB wrapper for on-diagonal points (master 200-350, local constancy only,
no interior connectivity); SIGN SYNCHRONIZATION through the ear peel tree (THE master brick 300-600 —
the left triangle's sign declared = tree sign, right subtree same sign; avoids global shoelace);
orientedWindData_all induction (master 200-350); earInterior_values (worker 100-160);
earDeletedExterior_unconditional (worker 80-120); EarCutData/PolygonGeomResidue wiring (worker
120-220) → artGallery_strict_mod_M. Audits: no half-plane use (reflex safe); strict simple ⟹
nondegenerate ears; use windCross_mem_final not the generic-guarded kernel at value points.
ROUTE A rejected (transport = interior connectivity); B rejected (uncontrolled reflex crossings).
