# Ch35-hsplits reply (worker, 2026-06-09)

## Status: FULL SUCCESS — and stronger than asked

The hsplits bound is proven **unconditionally** (no sphere-shape, no connectivity, no
Euler hypothesis — genus-free, exactly as the torus anchors suggested), and with
**slack 0**: it is an exact equality. As a byproduct the previously named open core
`NumCyclesCutPhi2` (`numCycles φ'₂ = F + 2`) is now a **theorem** for every simple
primal cycle, closing the F-side of the corrected Ch35 surgery outright.

File: `ProofsInTheBook/ZinanCh35Split.lean` (648 lines, new file only, nothing else
touched, not committed). Verified on uisai2 via
`lake env lean ProofsInTheBook/ZinanCh35Split.lean`: **0 errors, 0 sorry**, all 16
`#print axioms` exactly `[propext, Classical.choice, Quot.sound]`.
(Note: I had to `lake build ProofsInTheBook.ZinanCh35CountRoute` on uisai2 first —
its olean wasn't built; build completed clean, 8460 jobs.)

## The mathematical content: the seam conjugacy

The substrate's "the F-side has NO semiconjugacy" (2FWalk.lean:48-53) is true for the
*stalling projection* tried there, but the right move is a **conjugacy**, not a
projection. Reading the corrected surgery pointwise:

1. `φ'₂(inl (dart i)) = inl (dart (next i))` and
   `φ'₂(inl (α dart i)) = inl (α (dart (prev i)))` hold **unconditionally**
   (already proven: `cutCapPhi2_dart` / `cutCapPhi2_alpha_dart`). The 2k seam darts
   form exactly two new k-cycles — the two new faces.
2. Define the **seam swap** `e`: `inl(dart i) ↦ c_i⁺`, `inl(α dart i) ↦ c_i⁻`,
   `c_i⁺ ↦ inl(α dart i)`, `c_i⁻ ↦ inl(dart i)` (sign-crossing!), identity on
   ordinary darts. The single transport identity
   `e(σ'₂(inl d)) = inl(σ d)` holds for **all** `d : D` — both cap diverts of the
   pointwise φ'₂ case table land, after `e`, exactly on the bank-start dart the cap
   stands in for (`σ d = p_j`: `c_{prev j}⁺ ↦ inl(α(dart(prev j))) = inl(p_j)`;
   `σ d = q_j`: `c_j⁻ ↦ inl(dart j) = inl(q_j)`).
3. Hence `e · φ'₂ · e⁻¹ = φ ⊕ (nextIdx ⊕ prevIdx)` (`seamSwap_phi2_conj`), so
   `numCycles φ'₂ = numCycles φ + 1 + 1 = F + 2` by conjugation invariance +
   sumCongr additivity. No topology, pure permutation algebra.
4. The proven telescope (`numCycles_prefix_telescopes` +
   `sum_stepDelta_eq_neg_m_add_two_actualSplits`), read **backwards** with the two
   exact counts `F+2` and `F+2k`, gives `concatLen Ls + 2 = 2·s + 2·len` exactly.

Sanity vs kernel anchors: triangle `4 = 2+2`, K₄-sphere `6 = 4+2`, K₄-torus `4 = 2+2`;
the exact identity matches the orchestrator's corrected arithmetic (K₄-sphere alt cut:
m = 12, len = 3 → s = 4 > len, kernel-checked positions {3,6,7,8}).

## Proven list (all clean-3 axioms)

Generic (`CutCapCount`):
- `numCycles_sumCongr` — `numCycles (f ⊕ g) = numCycles f + numCycles g`
- `numCycles_eq_one_of_forall_sameCycle`

`SimplePrimalCycle` (all unconditional, ∀ C over any `CombMap`, any genus):
- `seamSwap_phi2_conj` — `e · φ'₂ · e⁻¹ = φ ⊕ (nextIdx ⊕ prevIdx)`
- `numCycles_seamModel`, `numCycles_cutCapPhi2` — `numCycles φ'₂ = F + 2`
- `numCyclesCutPhi2_holds : C.NumCyclesCutPhi2` — **the named open core, closed**
- `cutCapMap2_F_unconditional` — `(cutCapMap2).F = M.F + 2`
- `numCycles_phiLift_mul_faceCorr2` — `numCycles (phiLift · faceCorr₂) = F + 2`
- `concatLen_add_two_eq_splits` — **exact**: `concatLen Ls + 2 = 2·s + 2·len`
- `splitsEnough` / `splitsEnough_all` — **the task target** (the hsplits bound,
  verbatim form consumed by `numCycles_phiLift_faceCorr2_lower_of_splitsEnough[_all]`)
- `numCycles_phiLift_faceCorr2_lower_unconditional`
- `faceCorrSplitCertUnconditional : C.FaceCorrSplitCert` — every cycle has a split cert
- `jordan_simple_cycle2_of_gates` — Jordan now needs only `hchi` + connectivity gates

`NearTriangulation`:
- `sphereChordSeparation_of_gates`, `separates_of_gates` — chord separation from the
  gate data alone (face side discharged).

## Axioms output

All 16 `#print axioms` lines: `[propext, Classical.choice, Quot.sound]`. No sorryAx,
no ofReduceBool/trustCompiler.

## Downstream implications for the orchestrator

- The Ch35 count-route residue is **gone**. What remains of the Ch35 chain is only the
  connectivity side (`gateCompat'` / `EndpointCapLink` + `InteriorTriangleGates`
  suppliers) — the F-side, split certificates, and `NumCyclesCutPhi2` are closed.
- `FaceCorrWord.lean`'s header claim "the split count is not genus-free / the split
  positions are the irreducible topological residue" is now obsolete (the *count* is
  genus-free and proven; only individual split *positions* remain cut-dependent, but
  nothing needs them anymore). Consider a doc sweep in a later commit (not done here —
  single-file discipline).
- `PlanarMapSeamInst/SeamSpec/SeamChain`'s two-cap-chain route is superseded.

## Blockers

None.
