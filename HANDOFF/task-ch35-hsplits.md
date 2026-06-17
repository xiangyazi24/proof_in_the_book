# TASK Ch35-hsplits: the actual-split count bound (the count route's single topological residue)

Repo: /Users/huangx/repos/proof_in_the_book (branch zinan-overnight). Create ONLY the new file
ProofsInTheBook/ZinanCh35Split.lean. Do not edit anything else. No git commit.

GOAL: prove the hsplits bound consumed by
`ZinanCh35CountRoute.numCycles_phiLift_faceCorr2_lower_of_splitsEnough` (READ
ProofsInTheBook/ZinanCh35CountRoute.lean fully first — 11 proven results; the bound is the ONLY gap):

  FaceCorrWord.concatLen Ls + 2 ≤ 2 * (actualSplitFinset C Ls).card + 2 * C.len

for C : SimplePrimalCycle M with H : C.FaceCorrCycleLists Ls (under the hypotheses that file's
consumers actually need — read `numCycles_phiLift_faceCorr2_lower_of_splitsEnough_all` /
`..._sphereShape_...` to pick the right ambient assumptions; if a genus-0/sphere-shape hypothesis is
genuinely needed, take it — kernel anchors in ZinanCh35TorusAnchor.lean suggest the count is
genus-free, but a sphere-shape-conditional proof is still a full success).

SUBSTRATE (read these first):
- HANDOFF/outbox/cutcapphi2-substrate.md — the verified pointwise φ'₂ case table
  (PlanarMapCutCap2Counts.lean:189-254): ordinary `inl d` enters a cap iff φ d ∈ {p_j, q_j}
  (bank-starts), else clean `inl d ↦ inl (φ d)`; caps are NOT cyclic shifts.
- CRITICAL ARITHMETIC CORRECTION (orchestrator-verified): the needed split count is
  s ≥ (concatLen + 2 − 2·len)/2 which can EXCEED len (K₄-sphere: concatLen 12, len 3 → s ≥ 4 > 3),
  so splits MUST also be sourced from the ordinary-dart runs of each faceCorr₂ cycle, not only the
  len cut indices. Attack design: run-decomposition of each faceCorr₂ orbit into maximal clean runs
  separated by cap-entries; each separation event is an actualSplit witness; count via
  sum_stepDelta_eq_neg_m_add_two_actualSplits (already proven in ZinanCh35CountRoute.lean:57).
- Kernel-checked anchors: ZinanCh35TorusAnchor.lean (F'−F = 2 on triangle-sphere, K₄-sphere, K₄-torus).

VERIFY (your ONLY loop; Mac has no local lake):
scp -q ProofsInTheBook/ZinanCh35Split.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ && ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && timeout 1800 lake env lean ProofsInTheBook/ZinanCh35Split.lean 2>&1 | head -50'

STRICT: no sorry/axiom/admit/native_decide. End with #print axioms for every claimed theorem (⊆
{propext, Classical.choice, Quot.sound}). Grind; only legitimate stops: mathematics wrong (give the
explicit small counterexample map) or genuinely missing Mathlib API (exact lemma + goal state). Bank
every compiling sub-lemma. When done or blocked write HANDOFF/outbox/ch35-hsplits-reply.md: status,
proven list with axioms output, exact blockers.
