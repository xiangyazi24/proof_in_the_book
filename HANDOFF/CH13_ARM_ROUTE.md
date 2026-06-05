# CH13 ARM-LEMMA ROUTE — design note (book verbatim: HANDOFF/BOOK_CH13_CAUCHY.txt)

Book structure (Schoenberg–Zaremba proof of Cauchy's arm lemma + sign-counting):
  - PROVEN already in repo: the combinatorial core (2-colored plane graph sign-change counting
    + Euler part (C) contradiction).
  - Arm lemma (the named gap): convex n-gons Q, Q' with equal corresponding side lengths
    q_i q_{i+1} = q'_i q'_{i+1} (1 ≤ i ≤ n−1) and α_i ≤ α'_i (2 ≤ i ≤ n−1) ⟹ q_1 q_n ≤ q'_1 q'_n,
    equality iff all angles equal. Induction on n:
      n=3: cosine rule monotonicity — c² = a² + b² − 2ab·cos γ, γ ↦ c strictly increasing
           (PLANAR); spherical: cos c = cos a cos b + sin a sin b cos γ.
      n≥4: if some α_i = α'_i cut the vertex by the diagonal (congruent triangles q_{i−1} q_i q_{i+1});
           else open α_{n−1} to the max convexity-preserving α*; either reach α'_{n−1} (n=3 case +
           induction) or get stuck with q_2, q_1, q_n* collinear: chain
           q'_1 q'_n ≥ q'_2 q'_n − q'_1 q'_2 ≥ q_2 q_n* − q_1 q_2 = q_1 q_n* > q_1 q_n.
  - CRITICAL FAITHFULNESS POINT: the rigidity proof applies the arm lemma to SPHERICAL polygons
    (vertex links cut by small spheres). The planar arm lemma alone is NOT sufficient for the
    headline theorem. Two options:
      (i) full spherical arm lemma — needs spherical convex polygon substrate (absent in Mathlib;
          big build: arcs, spherical angles, spherical cosine rule (Mathlib has
          `EuclideanGeometry.cos_angle...`? check `InnerProductGeometry`), convexity on S²);
      (ii) reformulate the vertex-link comparison via the EUCLIDEAN geometry of the polytope
          directly (chords of the ε-sphere = ε-scaled angles; the spherical polygon's side lengths
          are face angles at p, its angles are dihedral angles). Any honest version still lives on S².
  - Substrate gap #2: vertex links of a convex polytope ARE convex spherical polygons, with
    correspondence facet-angle ↔ arc length, dihedral angle ↔ spherical angle.

VERDICT for sequencing: heaviest after Ch09. The PLANAR arm lemma (induction + cosine rule)
is a self-contained Euclidean brick formalizable today in Mathlib's EuclideanSpace — worth
banking as AUX while the spherical substrate is designed with ChatGPT. The convexity-preserving
"largest opening angle α*" step needs care (sup over a closed condition; the get-stuck
configuration is the boundary case where convexity degenerates to collinearity of q_2 q_1 q_n*).

Queue order: after Ch33 closes and Ch35 design iterates — pbook design question for the
spherical substrate (the weakest spherical-geometry kernel that supports the arm lemma + link
correspondence; possibly everything via 3D vectors and `Real.angle`, no intrinsic S² needed).
