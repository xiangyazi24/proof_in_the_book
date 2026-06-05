# Cut-and-cap σ' rotation (Chapter 35 Jordan lemma, σ-half) — reply

**File:** `ProofsInTheBook/PlanarMapCutCapSigma.lean` (NEW, sole writer; no other
file touched). Imports `ProofsInTheBook.PlanarMapCutCap`.
**Status:** compiles clean on uisai1 (`lake env lean` + full `lake build
ProofsInTheBook.PlanarMapCutCapSigma`, 8430 jobs OK). 0 sorry / 0 axiom / 0 admit /
0 native_decide. 534 lines.
**Axiom audit:** every headline declaration depends on exactly
`{propext, Classical.choice, Quot.sound}` (`cutSigmaPerm`, `cutCapMap`,
`cutSigma_leftInv`/`rightInv`, `CutSigmaCounts.toSurgery`,
`jordan_simple_cycle_of_counts`).

## Verification

```
rsync -az .../PlanarMapCutCapSigma.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 '... lake env lean ProofsInTheBook/PlanarMapCutCapSigma.lean'  # no output = OK
ssh uisai1 '... lake build ProofsInTheBook.PlanarMapCutCapSigma'          # Build completed (8430 jobs)
# #print axioms on all headline decls -> {propext, Classical.choice, Quot.sound}
```
(Deps `PlanarMapCutCap` oleans built first.)

## What is PROVED unconditionally (the hard dart-engineering, now done)

The previous file (`PlanarMapCutCap.lean`) left `σ'` and the three σ-dependent
fields as an *abstract* `CutCapSurgery` bundle. This file replaces the abstract
`N`/`σ'` with an **explicit, fully verified construction**:

1. **Bank-start darts and distinctness.** `qDart i = dart i`,
   `pDart i = α (dart (prevIdx i))`; proved `qDart_inj`, `pDart_inj`,
   `pDart_ne_qDart` (the `3 ≤ len` digon exclusion lifts to the `2k` darts being
   pairwise distinct).

2. **Two classifiers** with full characterization lemmas:
   * `divertKind d` — classifies a dart by its `σ`-successor: `σ d = p_i`
     (`+`-bank end `ℓ_i^+`), `σ d = q_i` (`−`-bank end `ℓ_i^-`), or neither.
   * `startKind d` — classifies by whether `d` is a bank-start (`q_i`, `p_i`, or
     neither), used by the inverse.

3. **The concrete vertex rotation `σ'` = `cutSigmaPerm`** (design §3.1,
   *enumeration-free* form — needs no contiguous-interval data, only `σ⁻¹` of the
   bank-start darts):
   ```
   σ' (ℓ_i^+) = c_i^+    σ' (c_i^+) = q_i     -- + bank closes through its cap
   σ' (ℓ_i^-) = c_i^-    σ' (c_i^-) = p_i     -- − bank closes through its cap
   σ' (inl d) = inl (σ d)  otherwise
   ```
   Built as `Equiv.mk` with the explicit inverse `cutSigmaInv`; **both
   `left_inv` and `right_inv` proved by full case bash** (5 cases each). This is
   the hardest piece and it is complete.

4. **The concrete cut map `cutCapMap : CombMap C.CutDart`** = `⟨cutAlphaPerm,
   cutSigmaPerm⟩`, with `α_invol`/`α_no_fixed` discharged from the
   already-proved `cutAlpha` involution facts.

5. **Seam closed-forms** `cutSigma_capPlus_eq`, `cutSigma_capMinus_eq`,
   `cutSigma_plusEnd`, `cutSigma_minusEnd`, `cutSigma_clean` — the exact rerouting
   behaviour, the inputs for the orbit-count proofs.

6. **`CutSigmaCounts.toSurgery`** assembles a `CutCapSurgery M C` whose `N` is the
   **concrete** `cutCapMap` and whose `alpha_eq` is **`rfl`** (discharged by
   construction). And **`jordan_simple_cycle_of_counts`**: the end-to-end Jordan
   conclusion conditional only on `CutSigmaCounts` + the sanctioned `chi_le` for
   the concrete map — the abstract bundle no longer appears.

## What remains ISOLATED (narrowed, satisfiable, NOT vacuous)

The three orbit-count / connectivity facts are packaged as the **Prop bundle
`CutSigmaCounts M C`**, stated about the *concrete* `cutCapMap`:
`vertex_count : V' = V + k`, `face_count : F' = F + 2`,
`connected_of_dual_path`. This is **strictly tighter isolation** than the prior
abstract `CutCapSurgery`: the map, its `α`, and its `σ` are all now explicit; the
only open content is three orbit-count statements about one concrete permutation.
They are satisfiable (true of the genuine surgery `cutCapMap`), so the bundle is
not vacuous — and being pinned to `cutCapMap` it cannot cheat.

## Honest finding on the design's "two pure cap faces"

A concrete k=3 trace (in the source comments / scratch) shows the design's prose
"the two cap-dart cycles are two new faces" is **loose**: with the fixed `cutAlpha`
(`c_i^+ ↦ q_i` same vertex, `c_i^- ↦ α d_i = p_{i+1}` next vertex) the cap φ'-orbits
are **not** pure cap cycles unless every bank is a singleton (degree-2 cycle).
`F' = F + 2` is nonetheless **true** as a *count* (the standard cut-and-cap Euler
identity); the rigorous proof is the transposition-cycle-count argument, not a
pure-cap-orbit claim. I deliberately did **not** state a false "pure cap face"
lemma.

## Path to full unconditionality (enabler now present)

The two generic crux lemmas needed to discharge `CutSigmaCounts` have **landed and
verified clean** in parallel:
`ProofsInTheBook/PermTranspositionCycleCount.lean`
(`numCycles_mul_swap_dichotomy`, `numCycles_mul_swap_of_not_sameCycle`) and
`ProofsInTheBook/RelationComponentCount.lean`
(`numComp_addEdge_of_eqvGen`, `numComp_addEdge_of_not_eqvGen`).

Discharging `vertex_count`/`face_count` then reduces to: express `cutSigmaPerm`
(resp. `φ' = σ'∘α'`) as `(lifted σ) * (∏ 2k swaps)` and apply the dichotomy 2k
times (each a split, `+1`, with the 2k caps starting as fixed points contributing
`2k`); `connected_of_dual_path` reduces to the component-count / reachability lift
(design §4, reusing the `PlanarMapFanConnectivity` walk-rerouting style). This is a
large follow-on (the case-defined `σ'` must be reconciled with a swap-product
form), left isolated here rather than risk a long unverifiable grind under the
no-local-build constraint. The hard *construction* it depends on — `σ'` itself —
is now done and verified.
