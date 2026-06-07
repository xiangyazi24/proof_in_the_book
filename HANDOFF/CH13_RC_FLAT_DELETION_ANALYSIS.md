# Ch13 R-C — independent flat-deletion analysis (await ChatGPT b25a1dd9)

## The R-C residue (after R-O closed, R-cong pending)
`SpliceBodyDiagMono` (SphericalSpliceTransport.lean): the folded-flat splice-body
endpoint comparison. The R-C agent reduced splice_transport_of_diag_le to it and
argued JointLe fails at the splice joint.

## My own computation — the simplest cut (j = i+2, single flat vertex)
A convex, vertex A(i+1) FLAT (angle π): A i, A(i+1), A(i+2) on one geodesic,
A(i+1) between. So sDist(A i, A(i+2)) = sideLen A i + sideLen A(i+1) (geodesic sum).
Delete A(i+1) -> body A♭ with new edge A i -> A(i+2).

KEY: deleting a FLAT vertex leaves the two ADJACENT joints UNCHANGED:
- joint at i in A♭ (between A(i-1)->A i and A i->A(i+2)): since A(i+1) is on the
  geodesic A i->A(i+2), direction A i->A(i+2) = direction A i->A(i+1), so this joint
  = angle(A(i-1)->A i, A i->A(i+1)) = ORIGINAL jointAngle A i. UNCHANGED.
- joint at i+2 in A♭: similarly = ORIGINAL jointAngle A(i+2). UNCHANGED.
This CONTRADICTS the R-C agent's claim that A-body splice joint = π - jointAngle A(i-1).
The agent may have formulated spliceArm for general j (ear), where the flat-fold
geometry differs, OR mis-identified the joint. WORTH CHECKING against b25a1dd9.

## The genuine asymmetry (the real obstruction)
B strictly convex, SAME sides. B♭ = delete B(i+1) (NOT flat) + chord B i->B(i+2):
- B♭ new edge = chord(B i,B(i+2)) < b_i + b_{i+1} = a_i + a_{i+1} = A♭ new edge.
  So A♭'s new edge is LONGER than B♭'s.
- B♭'s adjacent joints DO change (B(i+1) deletion bends them), unlike A♭'s.
So A♭ vs B♭ is NOT a clean Main-instance: A♭ has a longer splice edge AND
different joint structure than B♭. Comparing them directly is the wrong move.

## Hypothesis for the correct route (to confirm with b25a1dd9)
Do NOT compare A♭ to B♭. The flat vertex of A means A locally saturates the
triangle inequality where B does not. The classical Cauchy arm-lemma STUCK/cut
likely keeps the recursion EQUAL-SIDE by recursing on a piece that shares the
ACTUAL diagonal, using cut_diag_le as a direct endpoint transport (cut_endpt_transport),
not a body endpoint comparison. Candidate: prove a "flat-vertex deletion endpoint
identity" endpt A = endpt A♭ (trivial — endpoints 0,N untouched) and then bound
endpt A♭ by recursing the FULL arm at n-1 against a B-arm that ALSO has its (i,j)
diagonal as a genuine side (i.e. compare A♭ to spliceArm B but feed the EAR
recursion's equal-side structure, with the diagonal handled by cut_diag_le through
a transport, not a side comparison). Await ChatGPT's exact decomposition.
