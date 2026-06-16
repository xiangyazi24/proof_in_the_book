# Ch35 unconditional-close — residual worklist (post arcSplit core refactor, @ since 9a04d7d)

`arcSplit` is now DERIVED from `VertexNodup` (core refactor done). To make
`ZinanCh35Final.fiveColor_planar_of_recursionResiduals` UNCONDITIONAL we must inhabit
`Ch35RecursionResiduals` = `chordInputs : ChordRecursionInputSupplier` + `chordlessResidual : ChordlessOracleResidual`.
No remaining residual needs deep new geometry; the hardest is one localized chordlessness lemma.

## Genuine residuals (scout map, file:line in the scout audit)

### Chord branch — `ChordRecursionInputSupplier.supply`
- **R1** `p,q ∈ sideRegion₁` (precolored placement; chord choice). INDEPENDENT.
- **R2** side-2 anchors `Σ' a₀ a₁ ≠, tail=u/v` over keptDel₂. INDEPENDENT.
- **R3c-i/ii/iii** `sideMap₁.IsSimpleGraph`; `outer_simple` (Nodup); `InnerRepsAvoidBoundary`. INDEPENDENT (genus-0).
- **R3c-iv** `Side₁ChordIncidenceNonDegenerate` (`sideSigma₁ a₀ ≠ sideAlpha₁ a₁`). EASY decidable dart ineq.
- **R3a/b** side-1 precolored data + pullback `ThomassenLists`. BLOCKED on R3c.
- **R4a** `Side₂AnchorsShareFace` — ✅ **DONE** `ZinanCh35Side2Anchors.side₂AnchorsShareFace_canonical` (clean-3, mechanical port of side-1).
- **R4d-i…v** side-2 `IsSphereMap`/`IsSimpleGraph`/`outer_simple`/`inner_tri`/nondegeneracy. INDEPENDENT (genus-0).
- **R4b/c** side-2 precolored data + pullback lists. BLOCKED on R4a,R4d.

### Chordless branch — `ChordlessOracleResidual.supply`
- **R5a/c/d/e** `v0` selection; reserved colours γ,δ ∈ L v0; placements x=p; cp≠γ,δ. SMALL.
- **R5b** `BaseCount` (Euler degree-2⟺V=3). INDEPENDENT.
- **R6** `DeletedSeamData`: **R6a** `MergedOuterArcData` (the hard seam) → reduced to one lemma
  **`outer_v0_darts_consecutive`** (`M.φ bin = bout`, the unique in/out darts at v0 on the outer
  cycle are φ-adjacent; from `BoundaryChordless` + `outer_simple` + fan `v0_boundary`) + a cyclic-list
  arc walk (pure combinatorics; reuse `PlanarMapBoundaryArcSplit.arcSplit_of_nodup` tech). The other 3
  `MergedOuterArcData` fields (`exit`/`exit_face`/`exit_next_deleted`/`exit_jump`) close with existing
  fan machinery (`PlanarMapFanMergedOrbit` Case-B calculus + spoke-id `fanTriangle_shared_spoke`).
  **R6b-f** merged outerFace/outerCycle/outer_simple/outer_len/CleanFaceClass. BLOCKED on R6a.
- **R7** `deleted_lists` (Thomassen-list certificate on the deleted map). BLOCKED on R5b,R6.

## Keystone lemmas to land next (unlock the bulk)
1. **side `outer_simple`** (R3c-ii, mirrors to R4d-iii, R6d): ChatGPT-Pro route = direct `φ.toList`
   injectivity (`Equiv.Perm.nodup_toList` + `List.nodup_map_iff_inj_on`), push `S.tail x = S.tail y`
   through `freshSigma_sameCycle_iff` + `(filteredRotation M.σ keptDel₁).SameCycle ↔ M.σ.SameCycle`,
   then `hNT.outer_simple`. Irreducible sub-fact = the side outer φ-orbit trace (fresh dart + contiguous
   boundary-arc run).
2. **`outer_v0_darts_consecutive`** (R6a keystone): one localized chordlessness/planarity lemma.

## Provenance
Design converged via ChatGPT pbook-Pro + pbook2-xhigh (R2 on outer_simple) + 2 scout subagents
(R4a port — landed; R6a seam — reduced). Codex out of credits till Jun 18.
