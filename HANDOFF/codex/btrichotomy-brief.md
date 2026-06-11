# CODEX BRIEF: the b-TRICHOTOMY dispatch (kill SupportStuckWBSEndpointDispatch without derivatives)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-62 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT64.lean (FFCT63 is owned by a parallel worker — do NOT touch/import it).
Verify via scp + ssh uisai2 lake env lean (build FFCT62 olean first). Rules: no sorry/admit/
axiom/native_decide; clean-3; refutation-check anything new (5 impostors killed so far).

## The insight (master's): NO SIGN SUPPLY NEEDED — dispatch by trichotomy on b
At ANY WBS support-stuck binding (after FFCT52's orientation normalization to i+1 < j and FFCT55's
constant-pattern kills), the opened triple satisfies A' i = a*A'(i+1) + b*A' j (real span from the
vanishing support + independence). Case on b:
- b < 0: FFCT56's midFold machinery (midFold_coeffs_of_bneg needs hemisphere -> a > 0; then
  midFold_interior_contradiction — PATTERN-AGNOSTIC) kills it when the apex i+1 is interior
  (i+2 < n+1); the apex-at-tail case (i+1 = n) was FFCT60/61's route (j >= 2 killed; j in {0,1}
  -> FFCT62's mirror endpoint transports, mod their retained gap inputs — READ ch13-bundle-report
  for what those gaps are and whether they close with FFCT63's TailFoldBoundary work in flight;
  thread honestly).
- b = 0: a = 1, A' i = A'(i+1)?? wait b=0 gives A' i = a*A'(i+1), units => a = ±1 => equal
  (consecutive repeat — edge_short kill, FFCT52's distinctness) or antipodal (hemisphere kill).
- b > 0: and a's sign: a > 0 => the NNReal fold datum (both positive) => FFCT25
  far_fold_boundary_classification_final (needs NoNonadjacentRepeat — thread it; it is on the
  accepted surface) => i = 0 AND j in {n-1, n} => FFCT53's discharged boundary closes
  (foldedFlat_boundary_j_eq_n; the (0, n-1) case via its tail-fold route — mod TailFoldBoundary
  which the parallel FFCT63 worker is discharging; thread as named input if its olean isn't
  committed yet) => endpt A' <= endpt B — the ENDPOINT DISPATCH conclusion. a = 0: A' i = b*A' j
  unit => b = 1, repeat at distance |j - i| >= 2 => NoNonadjacentRepeat kill. a < 0 (with b > 0):
  rearrange A' j = (1/b) A' i - (a/b) A'(i+1) — both coefficients positive => A' j is the
  between-vertex => A' j in span>=0{A' i, A'(i+1)} — the vertex j between the ADJACENT pair
  (i, i+1): then sDist additivity says sDist(A' i, A'(i+1)) = sDist(A' i, A' j) + sDist(A' j,
  A'(i+1)) — the vertex j sits ON the edge arc (i, i+1)... kill via: the edge (i,i+1) is ShortArc
  and j != i, i+1 — a nonadjacent vertex on the open edge arc: consider the supports of edges
  (j-1, j) and (j, j+1) at i and i+1 + the coplanarity — OR simpler: this forces det3-coplanarity
  of (i, i+1, j) [have] AND the betweenness of j; then the support of edge (j, j+1) at i and at
  i+1: substitute A' j = c A' i + d A'(i+1) (c,d > 0): det3 (A' j)(A' j+1)(A' i) = d * det3
  (A'(i+1))(A' j+1)(A' i) and det3 (A' j)(A' j+1)(A' i+1) = c * det3 (A' i)(A' j+1)(A' i+1) =
  -c * det3 (A'(i+1))(A' j+1)(A' i)... wait det3(A' i)(A' j+1)(A' i+1) vs det3(A' i+1)(A' j+1)
  (A' i): swap slots 1,3 = one transposition = sign flip => the two supports are OPPOSITE
  multiples of one D => D = 0 => det3 (A' j)(A' j+1)(A' i) = 0 too => the triple (j, j+1, i)
  coplanar... iterate or directly: D = det3 (A'(i+1))(A' j+1)(A' i) = 0 means A' (j+1) in the
  span{A' i, A' i+1} = THE SAME PLANE => the plane accumulates j+1; with (i, i+1, j, j+1) all
  coplanar incl. the CONSECUTIVE pair (j, j+1): sphAngle at the joint j (between j-1... need
  three consecutive: have (j, j+1) in-plane; is j-1 in-plane? Not yet — run the same argument
  with edge (j-1, j) at i and i+1: same structure => j-1 in-plane => (j-1, j, j+1) coplanar =>
  FLAT JOINT at j => PositiveJoints kill (j interior: j < n needed... if j = n use the wrap/
  mirror routes — handle the corner honestly). This a<0 analysis is EXACTLY FFCT56's
  midFold-kill mechanism with the roles re-cast — check whether midFold_interior_contradiction
  can be INVOKED directly with the triple relabeled (the between-vertex is A' j with neighbors
  j-1, j+1 — its hmid shape is A' j = c A' i + d A'(i+1) but the lemma wants the apex's
  representation in terms of ITS OWN neighbor + far vertex... if shapes mismatch, prove the
  variant; the mechanism is identical).
## Assembly
`supportStuckWBS_endpoint_dispatch_final`: at any WBS support-stuck sup, endpt (openedWBS) <=
endpt B ∨ False-killed — i.e. the EndpointDispatch Prop of FFCT62 — modulo ONLY: NoNonadjacentRepeat
(accepted surface), TailFoldBoundary-class inputs (cite FFCT63's results if its file exists in
the tree by the time you finish — check; else named), and the j in {0,1} mirror-transport gaps
(read FFCT62's exact retained inputs and thread/discharge what you can). Then plug into FFCT62's
spherical_arm_mono_vNext for the sharpest headline. Report the EXACT final surface.

## Deliverables
ZinanFFCT64.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-btrichotomy-report.md. No git commit.
Grind to terminal.
