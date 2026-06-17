# TASK Ch35-gates: close the connectivity side (the LAST Ch35 residue)

Repo: /Users/huangx/repos/proof_in_the_book (branch zinan-overnight). Create ONLY the new file
ProofsInTheBook/ZinanCh35Gates.lean. Do not edit anything else. No git commit.

CONTEXT: ZinanCh35Split.lean (committed, clean-3) closed the whole F-side: hsplits is an exact
equality, NumCyclesCutPhi2 is a theorem, and `jordan_simple_cycle2_of_gates` /
`sphereChordSeparation_of_gates` / `separates_of_gates` reduce the chapter's Jordan headline to
ONLY the connectivity-side gate data. READ FIRST: ZinanCh35Split.lean (esp. the gate consumers at
the end), HANDOFF/ch35-countroute-spec.md, HANDOFF/outbox/ch35-hsplits-reply.md, and the defs of
the remaining gates: `gateCompat'` / `EndpointCapLink` / `InteriorTriangleGates` (rg them).

GOAL: supply the gate data — prove `EndpointCapLink` (the connectivity side of gateCompat') and
the `InteriorTriangleGates` suppliers, wiring them into `jordan_simple_cycle2_of_gates` so the
Ch35 chord-separation headline becomes unconditional (or conditional ONLY on hypotheses the
chapter's own NearTriangulation context already provides). If a gate is FALSE as stated, prove the
falsification kernel-anchored (rational/finite counterexample) and name the corrected gate — do
not fake, do not weaken silently.

VERIFY (your ONLY loop; Mac has no local lake):
scp -q ProofsInTheBook/ZinanCh35Gates.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ && ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && timeout 1800 lake env lean ProofsInTheBook/ZinanCh35Gates.lean 2>&1 | head -50'
(If an upstream olean is missing, `lake build ProofsInTheBook.<Module>` it on uisai2 first.)

STRICT: no sorry/axiom/admit/native_decide. #print axioms for every claimed theorem (⊆ {propext,
Classical.choice, Quot.sound}). Grind; legitimate stops only: math wrong (counterexample) or
genuinely missing Mathlib API (exact lemma + goal state). Bank every compiling sub-lemma. Write
HANDOFF/outbox/ch35-gates-reply.md when done or blocked: status, proven list + axioms, blockers.
