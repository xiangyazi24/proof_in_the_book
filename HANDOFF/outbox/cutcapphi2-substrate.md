# cutCapPhi2 substrate report (Opus worker C, 2026-06-09; condensed by orchestrator)

Key verified facts for the Ch35 master theorem design (full citations in the worker transcript):

1. `CutDart = D ⊕ (Fin k ⊕ Fin k)`; `phiLift = M.φ ⊕ 1` (caps fixed; numCycles = F + 2k,
   PlanarMapCutCapF.lean:82/102); `faceCorr2 = phiLift⁻¹ * (cutCapMap2).φ` (2FWalk.lean:92);
   `cutCapPhi2_eq_phiLift_mul` is a pure group identity (2FWalk.lean:97).
2. Pointwise φ'₂ table (PlanarMapCutCap2Counts.lean:189-254): caps do NOT shift cyclically —
   `φ'₂(c_i^+) = σ'₂(inl(bank))`, generically ORDINARY. Ordinary `inl d` enters a cap iff
   `φ d ∈ {p_j, q_j}` (bank-starts); else `inl d ↦ inl (φ d)` (clean). So φ'₂-orbits mix
   cap/ordinary even at genus 0 (K₄-sphere γvγvγv chain); genus-1 novelty = the two SIGNS mix.
3. V-side blueprint (V' = V + k, unconditional, PlanarMapCutCapV.lean:948): conjugation
   (capShift) + explicit mergeProd·splitProd word (2k merges then k splits), powered by the
   projection semiconjugacy proj_merged (:643) reducing CutDart-SameCycle to σ-SameCycle.
   **The F-side has NO semiconjugacy** (2FWalk.lean:48-53) and capShift does not commute with α',
   so neither the conjugation nor the projection ports. F must go through ForcedSplits stepDelta.
4. Live target: the hsplits bound of ZinanCh35CountRoute.lean —
   `concatLen Ls + 2 ≤ 2·card(actualSplitFinset) + 2·len`.
   ORCHESTRATOR CORRECTION to the worker's "s = len suffices": the needed split count is
   `s ≥ (concatLen + 2 − 2·len)/2`, which EXCEEDS len when supp(faceCorr2) is large —
   K₄-sphere: concatLen = 18 − 6 = 12, len = 3 → s ≥ 4 > 3. The certificate must source splits
   from the ordinary-dart runs too, not only the k cut indices. Design accordingly.
5. Everything above and below the hsplits bound is proven (telescope, cert builders, Jordan
   consumer). The attack: seam-local SameCycle certificates along the canonical cycle-list word,
   using the pointwise case table; counts kernel-anchored cross-genus in ZinanCh35TorusAnchor.lean.
