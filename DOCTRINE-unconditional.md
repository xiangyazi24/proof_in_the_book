# Unconditional push — discharge all 3 carried residuals (2026-06-17, user: 只要无条件的)

GOAL: make chapter13_cauchy_rigidity AND fiveColor_planeSimpleGraph FULLY UNCONDITIONAL by PROVING the 3 carried residuals (currently hypotheses). 统筹 parallel: 2 codex + ChatGPT design, rolling-harvest.

R#1 [DEEP] ch13 vertex-figure convexity + σ-orientation coherence:
  Derive vertexLinkGeometryOfEuclidean : TriangulatedEuclideanPolyhedron → ∀ v, VertexLinkGeometry (link
  convexity det>0 in σ-order) from face-halfspace convexity. BLOCKER (R4): det>0 needs σ-order ↔ outward-normal
  handedness coherence, NOT in b1. Path: either strengthen b1 with "σ = geometric rotation order" faithfulness
  field (then derive convexity from polytope convexity), OR prove global orientation coherence. ChatGPT life designs.
  → removes link-convexity residual from ConvexEuclideanPolyhedron.

R#2 [MEDIUM, most tractable] ch13 twoArcCut derivation:
  Prove twoArcCut_of_signChangesFull_eq_two : signChangesFull A B = 2 → TwoArcCut (linkDiff A B). Skeleton in
  AUDIT-ch13-R4-twoarc-cut (cyclicFlips_two_blocks decomposition + nondegeneracy + monotonicity transfer).
  Caveat: cyclicFlips=2 alone may not give nondegeneracy (2≤s-t,2≤wrapLen) — may need link n bound. codex1.
  → removes htwoArcCut residual from chapter13_cauchy_rigidity.

R#3 [DEEP] ch35 maximal-planar triangulability:
  Prove faceDiagonalSupplier_of_simple_sphere : FaceDiagonalSupplier (∀ simple sphere map, face len>3 → ∃
  valid FaceDiagonalChoice). = "maximal planar ⟺ triangulated". Jordan-type, Mathlib-unsupported. ChatGPT life2 designs.
  → removes FaceDiagonalSupplier residual from fiveColor_planeSimpleGraph.

TERMINAL: both headlines unconditional (residuals proven, clean-3, non-vacuity preserved). §3.3: after each
residual is proven, re-verify the headline drops the hypothesis AND the witnesses (tetra/triangle) still apply.
PLAYBOOK: ChatGPT design + codex grind + decomposition + §3.3 verify (ch13-ℝ³/ch35-gap proven loop).
ROUTING: codex1→R#2 (ready); ChatGPT life→R#1, life2→R#3 designs; codex2→R#1/R#3 when design lands.
