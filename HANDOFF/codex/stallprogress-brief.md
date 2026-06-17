# CODEX BRIEF: stall-is-progress (FFCT84) — close brick C without new semantics

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-83 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT84.lean. Verify via scp + ssh uisai2 (export PATH=$HOME/.elan/bin:$PATH;
build FFCT83 olean first). Rules: no sorry/admit/axiom/native_decide; clean-3.

## The block (HANDOFF/outbox/ch13-CLOSED-final.md): brick C needed ¬OnFoldRay Y C P / ¬OnFoldRay
Y C Q and NR can't supply them. THE MASTER'S REFINEMENT — the stall IS progress:
OnFoldRay Y C P's det3 component is det3 Y C P = 0 where (Y, C) = the sweep's current edge
(r-1, r) [ordinary, interior] and P = A i [nonincident: r >= i+3 during the sweep] — i.e. a
VANISHING NONINCIDENT SUPPORT at an INTERIOR triple (i < n, and the edge interior): this is
EXACTLY a NormalizedStrictInteriorSupportZero-class witness (the far probe is i with i+1 < n+1 ✓
since i+1 < n by the corner's hypothesis; check the consumer's exact orientation/shape — the
witness may need (r-1, r; i) ordered/normalized via FFCT52's tools — all landed).
So restate brick C as a DICHOTOMY:
  openCone_or_interiorZero : (the brick-C hypotheses MINUS the two ¬OnFoldRay) ->
    OpenCone P Q Y ∨ (a NormalizedStrictInteriorSupportZero-class witness)
Proof: by_cases on det3 Y C P = 0 and det3 Y C Q = 0: a zero (+ its companion cone half if the
consumer needs OnFoldRay's full strength — NO: the consumer needs only the SUPPORT ZERO — check
FFCT81/82's no-tail consumer input: NormalizedStrictInteriorSupportZero is presumably just the
sOrient = 0 + index bounds — VERIFY) gives the right disjunct DIRECTLY; if both nonzero, the q24
circle-order argument runs withOUT the fold-ray subtlety?? CHECK the q24 brick-C geometry: the
short arc Y->C crossing P or Q needs P/Q ON the arc = det3 = 0 + between; with det3 Y C P ≠ 0
the crossing is excluded outright (P not even coplanar with the edge) — so the circle-order
argument simplifies: Y in-plane(P,Q), C in OpenCone, ShortArc Y C, and P, Q NOT coplanar with
(Y,C): then Y must be in the cone (the arc from C to Y stays in the open半plane... implement the
2D order argument: all four on the great circle span{P,Q}?? NO — Y, C in span{P,Q} ✓ all four
on ONE circle ✓ — then det3 Y C P = 0 AUTOMATICALLY (all coplanar)!!! CONTRADICTION with the
by_cases?! RESOLVE: if Y, C, P, Q are all in span{P,Q}, every det3 among them is 0 — so the
"both nonzero" branch is VACUOUS and the dichotomy ALWAYS exits through the interior zero?!
That would mean the sweep NEVER continues... wait — C in OpenCone(P,Q) means C in span{P,Q} ✓;
Y: brick B gave sOrient P Q Y = 0 ⟹ Y in span ✓ ⟹ det3 Y C P = det3 of three coplanar = 0
ALWAYS ⟹ the support of edge (Y,C) at P is IDENTICALLY ZERO at every sweep step ⟹ EVERY STEP
yields the interior-zero witness IMMEDIATELY — the FIRST step (r = n-1: edge (n-1, n)... wait
the edge (Y,C) = (A(r-1), A r) with A r in-plane and A(r-1) NOT YET — the zero det3 Y C P needs
Y in-plane too; at the step Y = A(r-1) is the NEW vertex (not yet known in-plane!) — re-examine:
det3 (A(r-1)) (A r) (A i): A r ∈ plane, A i = P ∈ plane: the det3 = 0 iff A(r-1) ∈ plane OR the
plane... det3 with TWO in-plane arguments: det3 x y z with y, z ∈ span{P,Q}: = 0 iff x ∈ span
OR... NO: det3 is zero iff the three are linearly dependent; y,z ∈ a 2-plane: if y,z independent
they span it; then det3 x y z = 0 iff x ∈ span{y,z} = the plane. So det3 (A(r-1))(A r)(A i) = 0
⟺ A(r-1) ∈ plane (when A r, A i independent ✓ generically). SO: the support of edge (r-1, r) at
P is zero IFF the sweep would continue anyway (A(r-1) in-plane)! The TWO branches COINCIDE:
support-zero-at-P ⟺ next-vertex-in-plane. Then where's the cone/sign issue? The weak support
0 ≤ sOrient (A r-1)(A r)(P): if A(r-1) ∉ plane it's ≠ 0 hence > 0 strictly — fine, no info
needed. The sweep continues ONLY when the support IS zero — and THEN we have the interior zero
witness (r-1, r; i) — EXIT WITH PROGRESS. If the support is strictly positive: A(r-1) ∉ plane —
the sweep STOPS — but then... the INVARIANT only reached r; the contradiction needs reaching
i+2. Hmm — if the sweep stops at r > i+2 with A(r-1) off-plane: no contradiction, no witness...
BUT WAIT: re-examine brick B: it derived sOrient P Q Y = 0 from the OpenCone of C + the supports
of edge (Y, C) at P AND Q — the OPPOSITE-multiples trick FORCES Y in-plane REGARDLESS (using
both supports ≥ 0 and c,d > 0)!! So Y = A(r-1) IS forced in-plane at every step (brick B,
landed) — the sweep NEVER stalls on the plane part; the issue was only the CONE part (brick C).
And NOW: with Y in-plane forced, det3 Y C P = 0 automatically (three coplanar with C,P... Y,C
in-plane, P in-plane ⟹ det3 = 0 ✓ identically) ⟹ the support of edge (r-1, r) at P is
IDENTICALLY ZERO once both endpoints are in-plane ⟹ (r-1, r; i) IS a vanishing nonincident
interior support at EVERY step of the sweep!!! ⟹ THE VERY FIRST STEP (edge (n-1, n), probe i)
gives the witness: det3 (A(n-1))(A n)(A i): A n in-plane (the cone), A i = P in-plane; A(n-1)
forced in-plane by brick B at the first step ⟹ the support (n-1, n; i) = 0 with n-1, n, i...
the EDGE (n-1, n) is interior-ish (n-1 ≥ 1) and the PROBE i has i+1 < n+1 ✓✓ — THE WITNESS
EXISTS IMMEDIATELY. NO SWEEP NEEDED AT ALL: brick B's first application + the coplanarity
identity = the interior zero witness. IMPLEMENT THIS: from the corner's hypotheses, ONE brick-B
step at the edge (n-1, n) gives A(n-1) in-plane; then sOrient (A(n-1))(A n)(A i) = 0 (coplanar
triple det3 — FFCT22's coplanar_triple_det3_zero or direct); normalize the triple's orientation
(the consumer wants (edge; probe) shape with the edge's index order — FFCT52 tools) ⟹ feed the
no-tail consumer ⟹ endpoint ⟹ bpos_aneg_tail discharged ⟹ the v9 residues close ⟹
spherical_arm_mono_final_ch13_v10 (hcross) ASSEMBLES.
CAVEAT: check the nonincidence of probe i to edge (n-1, n): i ≠ n-1, n needs i + 1 < n ⟹ i ≤
n-2 ⟹ i ≠ n-1? i = n-2 gives i ≠ n-1 ✓ ≠ n ✓. And the (n-1, n) edge with probe i: the
consumer's strict-interiority on the EDGE index? Read the exact consumer shape; if it demands
the EDGE interior too (edge index + 1 < n?), the (n-1, n) edge may need one more sweep step —
then iterate brick B (each step's coplanarity gives the witness at the NEXT edge down — pick
the first edge meeting the consumer's index constraints; all bounded, no cone needed).
## Deliverable: ZinanFFCT84.lean (0 errors, clean-3): the witness production + the corner
discharge + `spherical_arm_mono_final_ch13_v10 (hcross) : SphericalArmMonotone` VERBATIM +
HANDOFF/outbox/ch13-V10-DONE.md. No commit. Grind to terminal.
