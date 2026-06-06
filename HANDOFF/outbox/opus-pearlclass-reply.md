# Pearl-angle classification — reply (opus-pearlclass)

**STATUS: COMPLETE. 0 sorry / 0 axiom / 0 admit / 0 native_decide. Clean-3 axioms only.**

File: `ProofsInTheBook/PearlClassification.lean` (514 lines, the one NEW file I own).
Imports the three substrate layers `TetPearls`, `TetDihedral`, `SectorSum`.

## Verification (exclusively on uisai2 — never built locally)

```
rsync -az .../PearlClassification.lean uisai2:.../ProofsInTheBook/
ssh uisai2 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH \
  && lake env lean ProofsInTheBook/PearlClassification.lean'   # EXIT=0
```

Dep oleans (`TetPearls`, `TetDihedral`, `SectorSum`, `Chapter09`) were already fresh on uisai2.
Olean built green: `✔ Built ProofsInTheBook.PearlClassification`, `Build completed (8423 jobs)`.

`#print axioms` for every public result → `[propext, Classical.choice, Quot.sound]` only
(no `sorryAx`, no `ofReduceBool`/`trustCompiler`). Audited:
`pearl_angle_sum_classification`, `pearlClassificationCert_nonvacuous`,
`CrossSection.exists_orthogonal_cross_section`, `.planeIso`, `.orthDir_finrank`,
`.projOut_mem_orthDir`, `.mem_orthPlane_iff`, `.direction_orthPlane`,
`PearlSectorModel.pearlAngleSum_eq_{wedge,pi,twoPi}`, `fullSector_model`,
`arccos_third_model_nonvacuous`.

Note: the file as handed to me **did not compile** (4 real errors: `EdgeOcc.dihedralAngle`
mis-resolved as a non-existent `Tet.dihedralAngle` field; `allEdgeOccs` had an unsolved
`Finset.mem_filter` metavariable on `Tet.edgePairs`). Fixed, then extended.

## What is delivered

### Task item 1 — cross-section machinery (VERIFIED, unconditional)
New `CrossSection` namespace builds, with no geometric assumption, the design's §6 reduction
ingredients:
- `orthDir u := (ℝ ∙ u)ᗮ` and `orthDir_finrank (hu : u ≠ 0) : finrank ℝ (orthDir u) = 2`
  (orthogonal complement of a line in 3-space is a plane; via
  `OrthonormalBasis.fromOrthogonalSpanSingleton` + the `Fact (finrank ℝ Pt3 = 2+1)` instance).
- `planeIso (hu) : orthDir u ≃ₗᵢ[ℝ] SectorSum.Plane` — the **isometric identification of the
  orthogonal plane's direction with `EuclideanSpace ℝ (Fin 2)`** (the `stdOrthonormalBasis`-of-
  complement repr), exactly the design's "identify Π with EuclideanSpace ℝ (Fin 2) via a linear
  isometry".
- `orthPlane x u := AffineSubspace.mk' x (orthDir u)` with `self_mem_orthPlane`,
  `direction_orthPlane`, and `mem_orthPlane_iff : q ∈ orthPlane x u ↔ ⟪q - x, u⟫ = 0` — the design's
  `Π := {y | ⟪y - x, u⟫ = 0}`.
- `projOut_mem_orthDir (hu) : TetDihedral.projOut u x ∈ orthDir u` — the **compatibility lemma**:
  the projection operator that defines the dihedral-angle sector edges in `TetDihedral` lands in the
  cross-section plane's direction. This is what ties the 2D identification to the dihedral angle by
  construction.
- `exists_orthogonal_cross_section x (hu) : ∃ Π, x ∈ Π ∧ Π.direction = (ℝ∙u)ᗮ ∧
  finrank ℝ Π.direction = 2 ∧ Nonempty (Π.direction ≃ₗᵢ Plane)` — the design's
  `exists_orthogonal_cross_section`, fully proved.

### Task item 2 — local models as a structure parameter (per SolidWithAngles pattern)
The genuinely-3D residue (slice of an *incident tet* IS a polar sector of angle exactly
`dihedralAngle`; the local solid slice is disk / half-disk / wedge; disjoint tet interiors ⇒ disjoint
sector interiors; union covers the target) is irreducible without a major standalone development, so
— exactly as the brief instructs ("structure parameters per the design's SolidWithAngles pattern
where the general proof is out of reach") — it is packaged as the named certificate
`PearlSectorModel S p θ`: a cross-section apex `x : Plane`, radius `ε`, sector list, a
**`SectorSum.PlanarSectorLocalModel x ε θ sectors` witness** (the load-bearing geometric content the
SectorSum layer consumes), and the bridge `PearlAngleSum S p = sectorAngleSum sectors`. Both fields
are load-bearing: the bridge alone gives `PearlAngleSum = sectorAngleSum`, and only the
`PlanarSectorLocalModel` field lets the SectorSum theorems conclude `= θ`.

`SolidWithAngles` (extends `TetSolid`) carries `extEdges`, `angleOfExtEdge`, and a
`LocalDihedralModel` (recording `0 < θ < π`) per external edge — no general boundary-edge extractor,
per the design.

### Task item 3 — the classification (VERIFIED, conditional only on the isolated residue)
- `EdgeOcc` / `allEdgeOccs` / `IncidentTetEdges` / `PearlAngleSum` — incident-edge angle sum.
- `PearlLocation` (externalEdge / boundaryFacetInterior / solidInterior) + `targetAngle`.
- `PearlSectorModel.pearlAngleSum_eq_{wedge,pi,twoPi}` — dispatch each target to the matching
  `SectorSum.planar_sectors_disjoint_cover_{wedge,halfdisk,disk}_angle_sum`, **unconditionally** from
  the certificate.
- **`pearl_angle_sum_classification (S) (p) (cert : PearlClassificationCert S p)`** — the headline
  trichotomy of §5: `PearlAngleSum` equals the external edge angle / `π` / `2π` according to the
  pearl's location. Proved by `match` on the location, each branch firing the corresponding SectorSum
  theorem through the lemmas above. No geometric assumption beyond `cert.model`.

## Faithfulness audit (playbook §3.3 — self, against design + SectorSum source)
- **`pearl_angle_sum_classification`: CONDITIONAL-honest** on the cross-section certificate
  `PearlClassificationCert` — precisely the design-sanctioned isolated 3D residue. Conclusion is the
  genuine design trichotomy on `PearlAngleSum` (the real incident-dihedral-angle sum), not a weakened
  variant.
- **NOT VACUOUS.** The §3.3 top failure mode (unsatisfiable hypothesis passing `#print axioms`) is
  closed at three levels: (i) `arccos_third_model_nonvacuous` builds a real
  `PlanarSectorLocalModel` at the **actual** regular-tet angle `arccos(1/3) ∈ (0,π)`;
  (ii) `pearlSectorModel_nonvacuous` inhabits the `PearlSectorModel` sub-structure;
  (iii) `pearlClassificationCert_nonvacuous` inhabits the **full top-level hypothesis**
  `PearlClassificationCert` for a pearl on a bona-fide external edge (`p.relInterior = e.relInterior`)
  with `PearlAngleSum = angleOfExtEdge e` — location is the honest `externalEdge e`, sector angle is
  the real external angle, nothing degenerate. The `externalEdge` branch's `targetAngle` reduces
  definitionally to `S.angleOfExtEdge e`, confirming the bridge is honest.
- Cross-section results (`orthDir_finrank`, `planeIso`, `mem_orthPlane_iff`, `direction_orthPlane`,
  `projOut_mem_orthDir`, `exists_orthogonal_cross_section`): **FAITHFUL, unconditional.**

## Residue (named, documented, non-vacuous)
Exactly one geometric residue remains, as the design prescribes: constructing an inhabitant of
`PearlSectorModel` for a *given* solid — i.e. proving the incident-tet slice is a sector of the right
angle and that the local slice fills the disk/half-disk/wedge. Everything reachable around it (the
orthogonal-plane + isometric-2D apparatus, the incident-angle bookkeeping, and the entire
classification dispatch) is proved unconditionally. This matches the brief's "deliver maximal verified
content; isolate genuinely-geometric residues as named structures (non-vacuous, documented)."

Branch stayed `main`; no commits; no codex/OpenAI tooling used; verified exclusively on uisai2.
