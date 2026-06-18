# Ch35 general closure — DOCTRINE (2026-06-17, route A, ChatGPT-designed)

GOAL: general Five Color Theorem — combinatorial-planar SimpleGraph (= PlaneSimpleGraph / CombMap sphere) → Colorable 5, NON-vacuous (triangle witness). From the proven fiveColor_planar_canonical (near-triangulation).

ROUTE A (chosen, AUDIT-ch35gap-routeA-design): triangulate the combinatorial sphere map.
KEY REUSE: ch35's freshMap/freshAlpha/freshSigma map-surgery (ChordSplit used it) — diagonal insertion = same primitives; Euler accounting same shape as ChordSplit Euler layer.

PHASES:
P1 [medium, START] sphere/simple bridge + triangle witness:
  - PlaneSimpleGraph.toCombMap_connected / toCombMap_V_eq/E/F/eulerChar / toCombMap_isSphereMap (count bridges; CombMap.two_mul_E_eq_card).
  - PlaneSimpleGraph.toCombMap_isSimpleGraph (dart_edge no-loop + edge_darts no-parallel).
  - trianglePlaneSimpleGraph (V=3,E=3,F=2,χ=2) + IsSphereMap by enumeration (NO native_decide).
P2 [hard core] face diagonal insertion (one step):
  - FaceDiagonalChoice (f, two nonadjacent face darts, no existing edge) + addFaceDiagonal via freshMap.
  - FaceDiagonalInsertion cert: sphere'/simple' preserved, V'=V, E'=E+1, F'=F+1 (FACE-SPLIT lemma = the heart: selected face orbit splits into 2, others unchanged), faceExcess decreases by 1.
P3 [hardest, Jordan-type] exists_face_diagonal_choice: nontriangular face has a valid noncrossing diagonal (nonadjacent boundary pair, no existing edge). Name as FaceTriangulationOracle; derive from a PlaneSimpleGraph 2-cell-embedding contract.
P4 triangulateByFaceExcess: well-founded recursion on faceExcess = Σ(faceLen f − 3); excess=0 ↔ all triangles; build NearTriangulation supermap (pick triangular outer face + boundaryCycleOfFace).
P5 wire: PlaneTriangulationExtension cert + colorable_of_triangulationExtension (pullback C along ιV) → fiveColor_planeSimpleGraph (P)(hsphere)(hTriangulable) : P.G.Colorable 5 + triangle non-vacuity.

TERMINAL: non-vacuous fiveColor_planeSimpleGraph, clean-3, triangle-witnessed. §3.3: verify the triangulation extension is genuinely constructible (not a vacuous oracle); the FaceTriangulationOracle must be inhabited (provable for real 2-cell sphere embeddings), else it's the ch13-style carried residual — decide derive-vs-carry per Xiang when P3 is reached.
PLAYBOOK: ChatGPT design + codex grind + decomposition + §3.3 non-vacuity verify (same as ch13-ℝ³).
