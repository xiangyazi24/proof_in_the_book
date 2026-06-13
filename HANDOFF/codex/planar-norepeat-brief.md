# CODEX BRIEF (uisai2-local): the planar convex-position no-repeat (FFCT93) -> UNCONDITIONAL Ch13

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-92 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT93.lean. ON the build machine:
`export PATH=$HOME/.elan/bin:$PATH && lake build ProofsInTheBook.ZinanFFCT92 && lake env lean ProofsInTheBook/ZinanFFCT93.lean`.
Rules: no sorry/admit/axiom/native_decide; clean-3. NO effort cap. This is a SELF-CONTAINED classical
planar fact -- PROVABLE, grind to terminal.

## GOAL: prove FFCT92's PlanarClosedWeakStrictNoRepeat (read its exact def in ZinanFFCT92.lean):
points f : Fin(n+1) -> E3 all on the plane <h, x> = 1 (gnomonic image), with
- WEAK CONVEX POSITION: det3 (f i)(f (i+1))(f j) >= 0 for all i, j (every vertex on the >=0 side of
  every edge-line);
- nondegenerate edges f i != f (i+1);
- STRICT TURNS: det3 (f r)(f r+1)(f r+2) > 0 for consecutive triples;
conclusion: r+2 <= s => f r != f s (no nonadjacent repeat).
Then FFCT92's wrappers give the UNCONDITIONAL spherical_arm_mono_ch13 : SphericalArmMonotone.

## PROOF:
### Base s = r+2 (TRIVIAL, do first): f r = f (r+2) => det3 (f r)(f r+1)(f (r+2)) =
det3 (f r)(f r+1)(f r) = 0 (repeated argument), contradicting the strict turn > 0. One line.
### General s >= r+3: angular-monotonicity / convex-position contradiction.
Since all f lie on the 2-plane P = {<h,x>=1}, det3 (a)(b)(c) = <h, (b-a) x (c-a)> is the planar
signed area (orientation) in P; strict turns det3 (f i)(f i+1)(f i+2) > 0 mean every consecutive
turn is a strict LEFT turn. Weak convex position det3(f i)(f i+1)(f j) >= 0 means all vertices are
on the left of every edge.
KEY LEMMA (the content): under weak convex position + strict left turns, the directed edges
e_i := f(i+1) - f(i) have STRICTLY INCREASING planar angle (each consecutive edge turns left by an
exterior angle in (0, pi)), AND the total turning over the whole chain is < 2*pi (convex position
bounds it: all vertices on one side of each edge => the chain is part of a single convex polygon
boundary, total turn <= 2*pi; strict => < 2*pi for an open chain). A repeat f r = f s (r+2 <= s)
closes a sub-loop f r, ..., f s = f r whose directed edges have strictly increasing angles summing
to a MULTIPLE of 2*pi (closed polygon, total turning = 2*pi*winding) with each exterior angle in
(0, pi) and >= 3 edges, so the sub-loop is a closed convex polygon with winding 1 and >= 3 distinct
vertices -- but then f r is BOTH a vertex of this convex sub-polygon AND the chain continues past
index s with strictly increasing edge angle, forcing the edge (s, s+1) to point into the sub-loop's
interior, violating weak convex position (some vertex ends up on the wrong side). Formalize via the
cleanest available route:
  (a) the EDGE-ANGLE monotonicity: define the angle/argument of e_i (use Complex.arg of the planar
      coordinates, or a det2/inner monotonicity); strict turns => strictly monotone on the range
      where total turn < pi, and convex position caps the total. A repeat needs the angles to wrap,
      contradicting the cap.
  (b) OR Mathlib convexity: the vertices are in strictly convex position (grep Mathlib
      `StrictConvex`, `Convex.extremePoints`, `Sbtw`, planar `orientation`); strict convex position
      => the index->point map is injective on any window with total turn < 2*pi; a nonadjacent
      repeat violates strict extremality (a point cannot be a strict extreme point and equal another
      vertex). 
  (c) OR a direct telescoping: f s - f r = sum_{i=r}^{s-1} e_i; pair with the normal g of edge
      (r,r+1): <g, f s - f r> = sum <g, e_i>; convex position gives <g, f j - f r> >= 0 with equality
      only at the edge; strict turns make the partial sums strictly positive in the interior, so
      <g, f s - f r> > 0, contradicting f s = f r (which gives = 0). THIS telescoping (c) may be the
      shortest -- work it out: <g, f_{r+2} - f_r> = <g, e_r> + <g, e_{r+1}>; <g, e_r> = 0 (e_r along
      the edge), <g, e_{r+1}> = det-related > 0 (strict turn lifts off the edge line); inductively
      <g, f_m - f_r> strictly increases for m in (r+1, ...], staying > 0 until convex position would
      force it back -- but a repeat needs it to return to 0, impossible if it's strictly increasing.
      The subtlety: it's strictly increasing only while the chain turns away; convex position +
      bounded total turn ensure it does not return within the window before wrapping. NAIL the exact
      monotone quantity (try <g, f_m - f_r> or the signed area swept) and prove it is > 0 for all
      m in [r+2, s], contradicting the = 0 at m = s.
Pick the route that closes; (c) telescoping is likely cleanest and most Mathlib-light.

## Deliverable: ZinanFFCT93.lean (0 errors, clean-3) with PlanarClosedWeakStrictNoRepeat PROVED
(as a theorem) + the UNCONDITIONAL spherical_arm_mono_ch13 + HANDOFF/outbox/ch13-planar-report.md.
No git commit. Grind to terminal -- this is the last brick; the chapter closes here.
