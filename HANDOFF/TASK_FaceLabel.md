# TASK: the concrete orbit-label certificate (layers 4-9) — closes NumCyclesCutPhi2

Design: HANDOFF/CH35_GENUSFREE_DESIGN.md (complete, dependency-ordered, layers 1-9).
Layer 3 (abstract OrbitLabelCert engine) DONE: ProofsInTheBook/OrbitLabelCert.lean
(structure OrbitLabelCert q beta; orbitEquiv; numCycles_eq_card).

Remaining = layers 4-9 in a NEW file ProofsInTheBook/CutFaceLabel.lean
(import ProofsInTheBook.OrbitLabelCert + ProofsInTheBook.PlanarMapCutCap2FWalk):
- OldFace := Quotient (SameCycle.setoid M.phi-as-Perm — match the repo: phi is sigma*alpha;
  the F-count numCycles phiLift = F + 2k is proven in CutCap2FWalk; relate OldFace card to F
  via the existing bridges), CapSide, CutFaceLabel := OldFace ⊕ CapSide.
- cutFaceLabel : C.CutDart → CutFaceLabel via the SAME case classifier as the proven phi'2
  closed forms (PlanarMapCutCap2Counts/2F: per-class actions; the seam darts that the closed
  forms send into cap orbits get Sum.inr labels; everything else Sum.inl (faceOf <dart>)).
  CRITICAL: the label table must make cutFaceLabel_phi'2 (label invariance) TRUE — derive the
  table FROM the closed forms; kernel-check on the triangle (the 4 fibers must match the
  #eval orbit partition recorded in PlanarMapCutCap2F/Eval).
- anchors + the three basic label lemmas (layer 4), label invariance (layer 5), old-face
  connectivity via oldFaceLift_phi_step + quotient induction (layer 6), cap connectivity
  (layer 7), certificate assembly (layer 8), final: numCycles phi'2 = numCycles phi + 2,
  numCyclesCutPhi2_holds, UNCONDITIONAL cutCapMap2_F, downstream restatements (layer 9).
The design文本 has full skeletons for every lemma. The closed forms are all proven. The
kernel anchors are in the repo. NO sorry/axiom/admit.
