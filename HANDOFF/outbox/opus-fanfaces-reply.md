# opus-fanfaces reply — Chapter 35 face-merge & vertex-quotient surgery

## Status: COMPLETE (2 of the 3 remaining FanSurgeryReconstruction fields fully discharged from the fan; 3rd field family = the genuinely-large BoundaryCycle, isolated as input; ONE residual φ-seam fact isolated as a named Prop)

New file: `ProofsInTheBook/PlanarMapFanFaces.lean` (731 lines, 0 sorry/axiom/admit, clean-3 axioms).
Root wiring: added `import ProofsInTheBook.PlanarMapFanFaces` to `ProofsInTheBook.lean` (after PlanarMapFanConnectivity).

## What is proved unconditionally from the fan

1. **`vertexQuotient` field — FULLY DISCHARGED, no extra hypothesis.**
   `deleteVertex_vertexQuotientEquiv (fan) (htail0 : M.tail d0 = v0)` :
   `Quotient((deleteVertex d0).σ) ≃ {Q : Quotient(M.σ) // Q ≠ ⟦d0⟧}`.
   - Forward map `x ↦ ⟦x.1⟧_σ` is well-defined + **injective for free** via the
     already-proved `deleteVertex_sigma_sameCycle_iff` (deleted-σ-step = M-σ-step on survivors).
   - The only fan content is **surjectivity**: every old vertex `≠ v0` retains a survivor.
     Non-neighbours keep all darts; neighbours of `v0` get a surviving edge dart from the fan
     (`fan_path_vertex_has_survivor`, re-derived locally — the connectivity file's analogues are `private`).
     This is exactly the two-edge-path obstruction's positive side.

2. **`facesMerge` field — DISCHARGED modulo ONE isolated φ-seam Prop.**
   `deleteVertex_facesMerge_of_fan (fan) (htail0) (hmerge) : M.DeleteVertexFacesMerge d0`.
   - New `φ`-calculus lemmas: `(deleteVertex).φ x` = first surviving σ-iterate of `α x.1`
     (`deleteVertex_phi_apply_coe`); agrees with `M.φ` when the next dart survives
     (`deleteVertex_phi_apply_of_next_kept`).
   - **Clean faces (∉ vertexFaces v0) survive unchanged**, proved unconditionally:
     such a face has no dart touching `v0` (head-`v0` darts would force the face into vertexFaces),
     so all its darts survive and every `φ`-step is preserved → its φ'-orbit traces its φ-orbit
     (`deleteVertex_phi_sameCycle_of_clean`, via `deleteVertex_phi_clean_iterate`).
   - **The classification (incident-with-`v0` vs clean) is φ'-invariant** via a finite-permutation
     argument (`cleanSurvSet_phi_invariant`): clean darts are closed under φ', so on the finite
     survivor type φ' bijects clean→clean, hence incident→incident. **No seam geometry needed for
     well-definedness.**
   - The forward face-map `faceMergeFun` (clean → its `inl` M-face, incident → `inr ()`) is then
     well-defined and **bijective** given `hmerge`; surjectivity onto `inr ()` uses a fan-triangle
     edge dart (`exists_incident_survivor`), so the fan is genuinely required.

3. **`connected` field** — reused from `PlanarMapFanConnectivity.deleteVertex_connected_of_fan`.

## The single isolated residual (named Prop, non-vacuous, NOT goal-in-disguise)

`DeleteVertexMergedFaceSingleOrbit M d0 : Prop` :=
  all surviving darts whose `M`-face is incident with `v0` lie in ONE `φ'`-cycle.

This is the residual `φ`-fan-rotation walk along the merge seam — the exact `φ`-level analogue of
the (proved) `DeleteVertexNeighborsConnected`. It is:
- **satisfiable** (holds for any genuine chordless boundary-vertex deletion, e.g. the tetrahedron);
- **strictly weaker** than `facesMerge` (only the merged darts' single-cycle; the clean-face
  bijection is proved unconditionally);
- consumed only as the injectivity-on-the-merged-class input to `faceMergeFun_bijective`.

## Assembly

`fanSurgeryReconstruction (fan) (htail0) (hmerge) (bdry) : FanSurgeryReconstruction hNT d0`,
where `bdry : DeletedOuterBoundary hNT d0` packages the new outer BoundaryCycle + simplicity +
length≥3 + inner-triangularity. The `BoundaryCycle` normalization is genuinely large (normalized
cyclic dart enumeration with all its certificates) and is supplied as input, as authorized by the
spec. All three dart-rotation surgery fields are discharged inside the constructor.

## Verification

- `lake env lean ProofsInTheBook/PlanarMapFanFaces.lean` — no errors, no sorry (only the repo-wide
  benign `push_neg` deprecation warnings).
- `lake build ProofsInTheBook.PlanarMapFanFaces` — Build completed successfully (8430 jobs).
- `#print axioms` on `deleteVertex_vertexQuotientEquiv`, `deleteVertex_facesMerge_of_fan`,
  `fanSurgeryReconstruction` → all `[propext, Classical.choice, Quot.sound]` (clean-3, no sorryAx).

## Remaining for a fully unconditional FanSurgeryReconstruction
- Discharge `DeleteVertexMergedFaceSingleOrbit` (the φ-seam single-cycle walk — bounded, fan-geometric).
- Construct `DeletedOuterBoundary` (the new outer BoundaryCycle normalization — large but standard).
