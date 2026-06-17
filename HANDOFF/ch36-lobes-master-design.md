# Master brick design: sameSide_lobes_noninterleave (Ch36, the one topological brick)

Target (pbook2 round, statement pinned): two upper-halfplane boundary lobes (a,b), (c,d) of a
StrictSimplePolygon w.r.t. a generic line cannot interleave: ¬(τa < τc < τb < τd).

## Route: vertical-ray parity sweep (NO pocket polygon construction)

Setup: lobe 1 = boundary arc A1, feet p (τa), q (τb), strictly in {side > 0} except feet;
lobe 2 = arc A2, feet r (τc), s (τd). Interleaving assumed: τa < τc < τb < τd.
Coordinates: u-axis = along the line (param by crossTau-like affine coordinate), v-axis = side value.
"Vertical line at u0" = {side-coordinate axis above u = u0}; A-arc crossings of a vertical line are
1-D IVT events of the u-coordinate along the arc's edge walk.

Counting function: for a base point z in the closed upper halfplane, off A1, let
  N(z) = #(A1 ∩ upward vertical ray from z)  (mod 2).
Key sub-lemmas:
1. (1-D parity, NOT Jordan) A polyline arc with endpoints at u-coords u_start, u_end crosses a
   generic vertical line {u = u0} an ODD number of times iff u0 strictly separates u_start, u_end;
   EVEN otherwise. Proof: per-edge sign changes of (u − u0) telescope along the walk — exactly the
   1-D analogue of the proven lineCrossing_eSign_sum_zero telescope. Genericity: u0 avoids the
   finitely many vertex u-coords (the hvert guard transported).
2. N at A2's start foot r: vertical line u = τc ∈ (τa, τb) separates A1's feet ⟹ odd; all A1-points
   on that vertical line have v ≥ h0 > 0 (A1 compact, touches the line only at feet whose u ≠ τc)
   ⟹ the upward ray from r (v = 0) catches ALL of them ⟹ N(r) odd.
3. N at A2's end foot s: u = τd > τb does not separate A1's feet ⟹ even ⟹ N(s) even.
4. (local constancy) N is constant along any sub-segment of A2 that avoids A1: the upward-ray
   crossing count changes only when the base point crosses A1 itself. Carrier: mirror the proven
   windCross_locally_constant_off_boundary proof pattern (it is the same edge-local case analysis),
   specialized to the arc A1 (a sub-walk, i.e. a Finset of edges) instead of the full boundary.
   NOTE: A2 stays in the closed upper halfplane and only its feet touch the line; A1-crossings of
   the ray are at v > 0; tangency/vertex degeneracies are excluded by hvert + edge-genericity
   (finitely many bad u, and A2's feet u-coords differ from A1's vertex u-coords).
5. Conclusion: N flips parity along A2 ⟹ ∃ point on A2 ∩ A1, interior to edges of both (no shared
   vertices: simple polygon + disjoint sub-walks + no vertex on the line) ⟹ contradicts
   EdgeIntersectionCondition.

Lower-halfplane version: mirror (negate side).

## Lean shape
- Define lobes as: indices into the sorted full-line crossing list with consecutive-on-the-WALK
  structure? NO — define directly: `BoundaryLobe a b` = the sub-walk from crossing edge a to
  crossing edge b (walk order) with all interior path points side > 0. The noninterleave statement
  only needs: the arc's edge set, its two feet, side-positivity. Represent the arc as a function
  (Fin m → edge index) + adjacency, or reuse the repo's boundary-walk machinery (grep for walk/arc
  infrastructure in Polygon* before inventing).
- The 1-D telescope (sub-lemma 1) is a Finset.sum sign-flip telescope over the arc edges — mirror
  lineCrossing_eSign_sum_zero's proof.
- h0 > 0 compactness: finite min over the arc's finitely many edge-segments' intersections with the
  vertical line — finite case analysis, no topology library needed.
- Estimated total ~500-700 lines. Master writes sub-lemmas 1+4 first (the load-bearing ones).

## Why not the pocket route
Constructing Γ = A1 + chord as a StrictSimplePolygon costs: synthetic vertex lists, simplicity
proof, and windCross reuse on a DIFFERENT polygon — heavier and reintroduces the interleaving at
the meta level. The sweep needs no new polygon.
