# TASK Ch20 boundary organization — oddAtomicRG_card_odd

Prove (in a new file ProofsInTheBook/Chapter20E2Boundary.lean, importing the engine +
Chapter20E2Frontier + Chapter20):

  theorem oddAtomicRG_card_odd (D : SquareDissection) :
    Odd (Finset.univ.filter fun e : Sym2 D.vtx =>
      edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1 ∧ Odd (atomicMult D e)).card

This is the boundary half of Monsky's Lemma 2. NO effort cap.

ARGUMENT:
1. By E2 (atomicMult_even_of_interior, atomicMult_eq_one_of_boundary) and the fact that a
   non-atomic edge has atomicMult = 0 (even): for every e, `Odd (atomicMult D e)` ↔
   `IsAtomicEdge D e ∧ OnSquareBoundary D e`. So the filtered set equals
   {e | RG ∧ IsAtomicEdge ∧ OnSquareBoundary}.
2. The unit square corners (0,0),(1,0),(1,1),(0,1) are vertices of D: each is an extreme
   point of `Set.Icc (0,0) (1,1) = ⋃ triHull`, hence (extreme point of a finite union of
   convex hulls of finite sets) an extreme point of some triHull i, hence equals one of its
   three corners coords (extremePoints_convexHull_subset). Package as: ∃ vertices c00 c10 c11 c01
   with coord c00=(0,0), etc.
3. An atomic boundary edge s(p,q) (segment ⊆ frontier square) lies on exactly one of the four
   closed sides of the square (frontier_unitSquare gives the side classification: bottom y=0,
   right x=1, top y=1, left x=0). Group the atomic boundary RG edges by side.
4. Per side, the D-vertices on it, ordered by position, form a chain; its atomic edges are the
   consecutive pairs (this is sideAtomicEdges of the corner-to-corner side, OR reconstruct the
   chain). Colours along each side (realTwoAdicColor of the coords):
     - bottom (y=0): red or green only (realTwoAdicColor_bottom_list_redGreen-style: vy = v 0 = 0,
       colorOfValues vx 0 ∈ {red,green}); endpoints (0,0)=red, (1,0)=green ⇒ odd RG count
       (listRGTransitionCount_odd_of_red_to_green / squareBoundaryRGCount_odd_of_side_color_lists).
     - right (x=1): green/blue (no red) ⇒ 0 RG edges.
     - top (y=1): green/blue ⇒ 0 RG edges.
     - left (x=0): red/blue (no green) ⇒ 0 RG edges.
   Existing Chapter20 lemmas: realTwoAdicColor_origin/_one_zero/_zero_one/_one_one,
   colorOfValues_zero_right_red_or_green, listRGTransitionCount_eq_zero_of_greenBlue/_redBlue,
   squareBoundaryRGCount_odd_of_side_color_lists.
5. Total RG atomic boundary count = bottom count + 0 + 0 + 0 = odd. Hence the card is odd.

You own Chapter20E2Boundary.lean. Do NOT edit other files. Self-verify lake env lean; no lake
build. No sorry/axiom. Append to HANDOFF/outbox/ch20-boundary-reply.md. Only stop: math wrong or
a sub-lemma genuinely unprovable.
