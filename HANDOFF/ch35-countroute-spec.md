# Ch35 count-route bricks — `ZinanCh35CountRoute.lean`

**Target file: `ProofsInTheBook/ZinanCh35CountRoute.lean` (NEW FILE — create it; touch NOTHING else).**
Imports: `ProofsInTheBook.FaceCorrWord`, `ProofsInTheBook.ChordSeparationClose` (both built — verify
with `lake env lean ProofsInTheBook/ZinanCh35CountRoute.lean` only; do NOT run `lake build`).
STRICT: NO `sorry` / `axiom` / `admit` / `native_decide`. If a brick blocks, skip it, keep the
others compiling, and report exactly what blocks in `HANDOFF/outbox/ch35count-reply.md`.

All new declarations go in THIS file (even those extending `ForcedSplits`/`FaceCorrWord`
functionality — open the right namespaces/sections; do not edit those files).

Context: read `FaceCorrWord.lean` (FaceCorrSplitCert, concatWord/concatLen/cycleListProd,
prefixPerm_concatWord, jordan_simple_cycle2_lower_of_splitCert), `ForcedSplits.lean`
(Swap, prefixPerm, stepDelta, stepDelta_ge_neg_one, stepDelta_eq_one_of_forced_split,
numCycles_prefix_telescopes, numCycles_mul_swap_dichotomy or its analogue, cutCapMap2_F_le_of_connected,
jordan_simple_cycle2_lower), `ChordSeparationClose.lean` (ChordJordanInput', connectivity_of_input',
sphereChordSeparation_of_input', NearTriangulation). Mirror their proofs/idioms.

## Bricks (dependency order; each pure algebra / wiring — none needs new topology)

1. `exists_cycleListProd_nodup (q : Equiv.Perm X) : ∃ Ls : List (List X), (∀ L ∈ Ls, 2 ≤ L.length ∧ L.Nodup) ∧ FaceCorrWord.cycleListProd Ls = q`
   — grind from the existing cycle-decomposition lemma in FaceCorrWord (grep `exists_cycleListProd`)
   plus `Equiv.Perm.toList`/cycle-support nodup facts. If the existing decomposition already gives
   nodup/length ≥ 2, just re-export with the conjunction.

2. `concatWord_ne_of_nodup {Ls} (hpos : ∀ L ∈ Ls, 2 ≤ L.length) (hnodup : ∀ L ∈ Ls, L.Nodup) (j) : (FaceCorrWord.concatWord Ls j).x ≠ (FaceCorrWord.concatWord Ls j).y`
   — consecutive entries of a nodup list are distinct; follow concatWord's indexing scheme
   (read its definition first; reuse any existing concatWord index lemmas).

3. `stepDelta_eq_neg_one_of_not_sameCycle (p) {m} (W) (j) (hne : (W j).x ≠ (W j).y) (hnot : ¬ (prefixPerm p W j.val).SameCycle (W j).x (W j).y) : ForcedSplits.stepDelta p W j = -1`
   — the merge half of the swap dichotomy (the split half `stepDelta_eq_one_of_forced_split`
   exists; mirror its proof through the numCycles-mul-swap dichotomy lemma).

4. `def actualSplitFinset (p) {m} (W) : Finset (Fin m) := Finset.univ.filter fun j => (prefixPerm p W j.val).SameCycle (W j).x (W j).y` (noncomputable/classical ok)

5. `sum_stepDelta_eq (p) {m} (W) (hne : ∀ j, (W j).x ≠ (W j).y) : (∑ j, stepDelta p W j) = -(m : ℤ) + 2 * ((actualSplitFinset p W).card : ℤ)`
   — split the sum over the filter; each split contributes +1 (existing), each non-split −1 (Brick 3);
   `Finset.sum_filter_add_sum_filter_not` + card arithmetic.

6. Finset enumeration: `Finset.orderIsoOfFin` (Mathlib) already enumerates a finset of a linear
   order as `Fin S.card ≃o S` — USE IT (no new def needed): from `S : Finset (Fin m)` get
   `splitIdx : Fin S.card → Fin m := fun i => (S.orderIsoOfFin rfl i : Fin m)` with injectivity
   from the order-iso. Check the exact Mathlib name/signature (`Finset.orderIsoOfFin S h : Fin k ≃o S`).

7. `faceCorrSplitCert_of_cycleWord_lower (C : SimplePrimalCycle M) (Ls) (hpos) (hnodup) (hfactor : cycleListProd Ls = C.faceCorr2) (hlower : (numCycles (C.phiLift * C.faceCorr2) : ℤ) ≥ (M.F : ℤ) + 2) : C.FaceCorrSplitCert`
   — assemble: W := concatWord Ls, m := concatLen Ls, S := actualSplitFinset, s := S.card,
   splitIdx via Brick 6, split_ne via Brick 2, forced_split from membership in the filter.
   hbound (`m + 2 ≤ 2*s + 2*C.len`): telescope `numCycles_prefix_telescopes` +
   `prefixPerm_concatWord`+`hfactor` (final perm = C.phiLift * C.faceCorr2) + Brick 5 sum formula +
   the existing fact `numCycles C.phiLift = M.F + 2*C.len` (grep ForcedSplits/PlanarMapCutCap* for
   the exact name — it exists; if the form differs, adapt) + `hlower`, then `omega`/`linarith` on ℤ.

8. Wiring consumers (copy shapes from ChordSeparationClose, replacing the faceCore field):
   ```lean
   structure ChordJordanInputLower' (C : SimplePrimalCycle M) : Prop where
     faceSplit : C.FaceCorrSplitCert
     gateCompat' : ∀ i : Fin C.len,
       DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
         ∃ P : C.OrdinaryDualPath2, C.EndpointCapLink i P ∧ C.InteriorTriangleGates P
   ```
   (match the EXACT field shape of `ChordJordanInput'.gateCompat'` — read it first; if it differs
   from the above, mirror the real one),
   `connectivity_of_inputLower'` (mirror `connectivity_of_input'`),
   `NearTriangulation.sphereChordSeparation_of_inputLower'` (mirror `sphereChordSeparation_of_input'`,
   final step through `jordan_simple_cycle2_lower_of_splitCert hin.faceSplit hNT.sphere.2 ...`),
   `NearTriangulation.separates_of_inputLower'` (mirror `separates_of_input'` if it exists).

NOTE (genus sanity): all bricks here are genus-free permutation algebra — they must NOT use or
require `eulerChar = 2`. The single remaining topological theorem
(`numCycles (C.phiLift * C.faceCorr2) ≥ M.F + 2` from Connected + χ=2) is NOT in scope for this
task — do not attempt it, do not state it, do not axiom it.

End the file with `#print axioms` for bricks 1, 3, 5, 7 and the wiring theorems (must be exactly
`[propext, Classical.choice, Quot.sound]`).

Report to `HANDOFF/outbox/ch35count-reply.md`: per-brick status, exact names of repo lemmas used,
anything skipped + why. Kill any background processes you started before exiting.

## VERIFICATION RECIPE (this machine is a Mac WITHOUT local lake — builds live on uisai2)

To typecheck your file after each edit (this is your ONLY verification loop):

    scp -q ProofsInTheBook/<YourFile>.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ && \
    ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && timeout 900 lake env lean ProofsInTheBook/<YourFile>.lean'

- NEVER run `lake build` anywhere. NEVER run local `lake env lean` on the Mac (no oleans here).
- All imports you need are already built on uisai2.
- To read existing repo files, read them locally on the Mac (the checkout matches uisai2).
