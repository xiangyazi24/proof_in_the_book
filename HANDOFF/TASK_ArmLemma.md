# TASK: ArmLemma.lean — planar Cauchy arm lemma (Ch13 brick, AUX until substrate lands)

Create ProofsInTheBook/ArmLemma.lean (you own ONLY this file). Book statement (verbatim text in
HANDOFF/BOOK_CH13_CAUCHY.txt, proof = Schoenberg-Zaremba): Q and Q' convex planar n-gons with
vertices q_1..q_n resp q'_1..q'_n; equal corresponding side lengths dist (q i) (q (i+1)) =
dist (q' i) (q' (i+1)) for 1 <= i <= n-1; interior angles alpha_i <= alpha'_i at vertices
2 <= i <= n-1. Conclusion: dist (q 1) (q n) <= dist (q' 1) (q' n), equality iff all angles equal.

YOU choose the formalization of "convex n-gon" — recommended: q : Fin n -> EuclideanSpace ℝ (Fin 2)
in strictly convex position (e.g. every vertex is extreme / all turning cross-products share a
strict sign), with angles via EuclideanGeometry.angle (Mathlib has law of cosines:
EuclideanGeometry.law_cos / dist_sq_eq...). State BOTH the inequality and the equality
characterization. Choose the variant of convex-position that makes the Schoenberg induction go
through; document the choice at the top of the file.

Proof skeleton (the book's, n>=4): if some alpha_i = alpha'_i, cut the vertex with the diagonal
(congruent triangle q_{i-1} q_i q_{i+1}) and induct on n. Else all strict: open angle alpha_{n-1}
toward alpha'_{n-1} keeping all else fixed; either reach it (n=3 monotonicity + induction) or get
stuck where q_2, q_1, q_n* are collinear (q_2 q_1 + q_1 q_n* = q_2 q_n*); then the chain
q'_1 q'_n >= q'_2 q'_n - q'_1 q'_2 >= q_2 q_n* - q_1 q_2 = q_1 q_n* > q_1 q_n closes (triangle
inequality + induction on the (n-1)-gon ignoring q_1 + the n=3 case). The "open until stuck" step:
parametrize the moved vertex q_n(t) by the angle t in a closed interval; the stuck set is closed;
take the sup; continuity of t -> dist (q 1) (q_n(t)) — formalize with care (IsCompact.exists_sSup
or csSup on the interval; convexity of the intermediate polygons must be maintained — this is the
delicate invariant, document exactly what you keep).
Base case n=3: cosine-rule monotonicity, strict for strict angle increase.

This is hard. Grind it to the end — no sorry/axiom, no effort cap. If a sub-goal genuinely resists
after real attempts, prove everything else, isolate it as ONE named statement with the exact goal,
and report. lake env lean ProofsInTheBook/ArmLemma.lean. Append HANDOFF/outbox/armlemma-reply.md.
