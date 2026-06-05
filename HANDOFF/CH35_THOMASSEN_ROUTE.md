# CH35 THOMASSEN ROUTE — design draft v1 (to be iterated with ChatGPT/codex before dispatch)

DISCOVERY (same pattern as Ch33): the book's ch34 proof is Thomassen's 5-LIST-coloring.
Quote: "It does not use Euler's formula at all!" — no Kempe chains, no min-degree-5 vertex,
no general deletion. Verbatim text: HANDOFF/BOOK_CH34_FIVECOLOR.txt.

The two operations of Thomassen's induction act on NEAR-TRIANGULATIONS (all bounded faces
triangles, outer boundary a chordless-or-chorded simple cycle):
  Case 1 (chord uv): split along the chord into G1 (containing precolored x,y) and G2; induct twice.
  Case 2 (no chord): delete boundary vertex v0 (neighbor of x on B); neighbors x,v1..vt,w;
    remove two colors {gamma,delta} subset C(v0)\{alpha} from the lists of v1..vt; induct;
    color v0 by gamma or delta != color(w).
Crucially: near-triangulations have NO degree-1 vertices and NO bridges — exactly the two
counterexample classes that killed the general dart-model closed-star deletion (PlanarMapDelete).
So a RESTRICTED deletion theorem for near-triangulations is plausibly provable in the dart model.

## Faithful endpoint (no fragment)
chapter35_unconditional : every CombMap M with IsSphereMap M and simple underlying graph has
a proper 5-coloring of its vertices (orbit-quotient graph). Stronger book-faithful version:
5-list-colorable. Decide: plain 5 vs list-5 (the book proves list; list subsumes plain).

## Decomposition
(P1) NearTriangulation structure over CombMap: IsSphereMap + distinguished outer face +
     every other face has size 3 + outer boundary darts traverse a simple cycle (pairwise
     distinct vertices) + simple graph (no loops, no parallel edges).
(P2) Chord-split: given a chord (graph edge between non-adjacent-on-B boundary vertices),
     extract the two sub-maps. Dart-model spec: dart subsets D1, D2 with D1 ∩ D2 = chord's
     orbit-pair {e, α e} duplicated?? — OPEN DESIGN QUESTION: duplicate the chord edge's darts
     (each side keeps a copy) vs. shared-edge submap extraction. The σ at the two chord endpoints
     must be re-stitched. Each side must be proven NearTriangulation again.
(P3) Boundary-vertex deletion for near-triangulations: v0 on B, B chordless. Delete star(v0);
     new outer boundary (B\v0) ∪ {v1..vt}. Prove: still NearTriangulation (uses chordlessness:
     internal neighbors vi ∉ B). This is the restricted deletion theorem — the degree-1/bridge
     pathologies are excluded by the triangle faces + simple cycle boundary.
(P4) Thomassen induction on |V| with the strengthened hypothesis (x,y precolored on B, lists
     ≥3 on B, ≥5 inside) — pure combinatorics over (P2)+(P3).
(P5) Triangulation-completion bridge: every sphere map with simple graph and |V| ≥ 3 is a
     spanning subgraph of some NearTriangulation. Additive/local in the dart model: insert a
     diagonal into a face of size ≥ 4 (two new darts; F+1, E+1, eulerChar preserved). DEGENERACY
     WALL: faces whose boundary repeats vertices (bridges, cut vertices) — a diagonal there can
     create loops/parallels. Probably needs: first make 2-connected by adding edges (or handle
     blocks separately: coloring glues over cut vertices — graph-level argument, no maps needed).
     OPEN DESIGN QUESTION: cleanest formal path through degeneracies. Options:
       (i) block decomposition at the GRAPH level (5-list-color each block, glue at cut vertices;
           gluing for LIST version needs care — lists differ; plain 5-coloring glues by color
           permutation, lists do NOT glue naively. May force plain-5 endpoint, or strengthen).
       (ii) edge-addition induction making the map 2-connected first, all within dart model.
       (iii) restrict headline to 2-connected sphere maps?? NO — that is a fragment. Reject.
(P6) Endpoint assembly.

## Existing inventory
- PlanarMap.lean: CombMap (α involution no-fixed-point, σ), V/E/F as orbit counts, eulerChar,
  IsSphereMap := Connected ∧ eulerChar = 2.
- PlanarMapEuler.lean: Euler consequences (3F ≤ 2E, E ≤ 3V−6, min-degree-≤5).
- PlanarMapDelete.lean: Perm.deleteSet splice (PROVEN) + the deletion COUNTEREXAMPLES
  (twoEdgePathMap: closed-star deletion erases deg-1 neighbors; bridge face-merge breaks counts).
- Chapter35.lean: FiveColorReducible certificate machinery + Kempe-swap extension lemmas
  (coloring_extend_after_kempe_swap etc.) — reusable for a plain-5 endpoint via Kempe if the
  Thomassen list route stalls; chapter35 currently = certified version (fragment).
- Chapter36 (museum) needs polygon triangulation — NOTE the (P5) face-diagonal machinery is
  the same tool family; design for reuse.

## Open design questions for the ChatGPT round (send AFTER current pbook task completes)
1. (P2) chord-split dart bookkeeping: shared edge vs duplicated darts — which gives the cleaner
   NearTriangulation re-proof?
2. (P5) degeneracy path: block gluing for LIST coloring (does Thomassen's statement glue over
   cut vertices? the precolored-edge form does NOT obviously) vs 2-connectivization by edges.
3. Outer-boundary representation: distinguished face + cycle structure — as a φ-orbit with
   injective vertex map, or as an explicit dart list? Which makes (P3)'s "new boundary" proof
   shortest?
4. Termination/measure: |V| for case 2, but case 1 splits into parts each smaller in (V + chords)?
   G1, G2 both have fewer... G1 ∪ G2 = G with B1, B2 smaller cycles; each strictly fewer vertices?
   NO — G1 and G2 share u,v and can each have fewer vertices than G ONLY if both sides nonempty;
   measure = |V| with strict decrease needs B1, B2 proper. Verify.
5. Is there an existing Coq/Isabelle Thomassen formalization to port? (four-color in Coq uses
   hypermaps — their face/walkup machinery is the closest prior art for (P3).)
