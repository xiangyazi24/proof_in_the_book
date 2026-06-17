# CODEX BRIEF: finish ZinanFFCT58.lean (Ch13 endpoint audit + repair)

You are finishing a mid-flight file in ~/repos/proof_in_the_book (branch zinan-overnight).
ONLY edit ProofsInTheBook/ZinanFFCT58.lean. NEVER touch any other file.
Verify loop: scp the file to uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ then
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT58.lean'
(if it imports ZinanFFCT57, first: ssh uisai2 '... lake build ProofsInTheBook.ZinanFFCT57' — FFCT57
is uncommitted but present in the working tree on both machines.)
ABSOLUTE RULES: no sorry, no admit, no new axiom, no native_decide. Every main theorem must end
with #print axioms showing only [propext, Classical.choice, Quot.sound]. Do not weaken statements
to vacuity: every conditional hypothesis must be satisfiable (the campaign has killed three
impostors already — your file IS the audit instrument).

## The mission (context: HANDOFF/outbox/ch13-final-endpoint-report.md + ch13-endpoint-audit-report.md if present, HANDOFF/design-rounds/ch13-cut-replacement.md)
1. AUDIT VERDICT: is SpliceBodyDiagMono (legacy splice residual, see SphericalSpliceTransport)
   FALSE under its stated hypotheses? The design round records "the general one-side-monotone
   statement is false in a 2-edge limit" (spherical law of cosines monotonicity flips for sides
   near pi). Either construct the kernel-anchored counterexample (explicit S2 points, the
   FFCT10/17 falsification idioms) proving ¬SpliceBodyDiagMono, OR prove the constrained version
   is not refutable that way and document precisely. The verdict decides part 2.
2. REPAIR (if FALSE or undetermined): the uncommitted ZinanFFCT57.lean's (b)-form headline
   spherical_arm_mono_final_honest carries Ch13Residues including SpliceBodyDiagMono — if that
   Prop is false the headline is vacuous. Rebuild the (b)-form WITHOUT the legacy splice Props:
   the modern chain is committed (ZinanFFCT48 cut_step_from_stuckAtK_plus, FFCT53
   FoldedFlatCutTransportPlusNR discharge, FFCT54 wiring, FFCT56 chirality elimination).
   Re-derive the double induction (mirror ZinanFFCT19's mainPlus_at_level/mainPlus_all recursion
   with the modern step) => spherical_arm_mono_final_v2 mod the honest bundle ONLY:
   the FFCT49/51/56 residues (NonAxisMixedBindingResidue etc.), StrictDiagonalSupport,
   TailFoldBoundary, NoNonadjacentRepeat. Keep FFCT57's (a)-form intact (it was sound).
3. The current file has ~2 errors — diagnose (may be import/olean staleness vs real proof gaps)
   and fix. The previous worker died mid-flight at 85 tool calls; its partial content may be
   80% done — read it fully first and salvage everything sound.
4. Report: write HANDOFF/outbox/ch13-endpoint-audit-report.md with the verdict, what you changed,
   the final honest surface list. Do NOT git commit.

Work until the file compiles 0-error clean-3 with the verdict theorems in place. The mathematics
is fully designed; this is disciplined Lean grinding. If a specific lemma resists, decompose and
attack each piece — do not stop at naming a difficulty.
