# Ch35 certificate assembly report

**Files created:** `ProofsInTheBook/ZinanCh35Cert.lean`, `HANDOFF/outbox/ch35-cert-report.md`.
No existing Lean file was edited. No git commit.

**Verification:** `export PATH=$HOME/.elan/bin:$PATH && lake env lean ProofsInTheBook/ZinanCh35Cert.lean`
passes. The audited declarations depend only on `[propext, Classical.choice, Quot.sound]`.
No `sorry`/`admit`/`axiom`/`native_decide`.

## What landed

`ProofsInTheBook.ZinanCh35Cert.Side₁CertificateInputs` names the exact input list consumed by the
campaign endpoint `ZinanCh35FinalClose.chordSideResidue₁_final`:

1. `ci : ContiguousInterval data hsep a₀ a₁ hne`
2. `hshare : Side₁AnchorsShareFace data hsep a₀ a₁`
3. `hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1)`
4. `ha₀ : M.tail a₀.1 = u`, `ha₁ : M.tail a₁.1 = v`
5. `pₛ qₛ cpₛ cqₛ`
6. `hLₛ : ThomassenLists (chordSideNearTriangulation_of_share ...) pₛ qₛ ... cpₛ cqₛ`
7. `confinement : ZinanCh35FinalClose.Side₁SchoenfliesConfinementInput data hsep`

`side₁Residue_of_certificateInputs` feeds these into `chordSideResidue₁_final`, producing
`ChordSideResidue`. `side₁Reconstruction_of_certificateInputs` then threads that residue into
`ChordSplitFinal.chordSideReconstruction_of_chord`, yielding the `ChordSideReconstruction` shape
consumed by the recursive chord induction.

## Five-color theorem surface

`PlanarInputs α` is the named remaining induction-level bundle:

```lean
recursiveDichotomy : ChordRecursiveDichotomy α
```

`fiveColor_of_planarInputs` proves `M.toSimpleGraph.Colorable 5` for a near-triangulation from
`PlanarInputs (ULift (Fin 5))`. The `ULift` is necessary because the Thomassen chain ties the color
universe to the dart universe; the produced coloring is projected back down to ordinary `Fin 5`.

`fiveColor_of_jordanInput` records the older `JordanInput` surface. `fiveColor_of_bookCertificate`
records the separate `Chapter35.chapter35` surface:

```lean
BookCertificate G := Chapter35.FiveColorReducible G
```

The repo still does not produce `FiveColorReducible G` from the Ch35 chord-side campaign endpoint.

## Side-2 mirror verdict

No landed side-2 analogue of `chordSideResidue₁_final` exists in this checkout. Side 2 has lower
level support (`sideMap₂`, `Side₂IsDisk`, `Side₂AnchorsShareFace`, `sideMap₂_isSphereMap`), but not
the final residue constructor/list/decrease/correspondence package parallel to side 1. Therefore the
top-level theorem must still take a uniform `ChordRecursiveDichotomy`, whose chord branch supplies
both side reconstructions.

## Chordless verdict

The chordless branch is partially closed but still not a uniform oracle producer:

* `ChordlessClose` pins `FanSurgeryReconstruction` to `DeleteVertexMergedFaceSingleOrbit` plus
  `DeletedOuterBoundary`, with the structural fan fields proved.
* `ChordlessFinal` can build the reconstruction from a merged outer-boundary cycle and
  `CleanFaceClass`, discharging `inner_tri` by the face-size route.

To fill `ChordlessOracle` uniformly, the remaining inputs are still: the chordless/dichotomy choice,
`FanIncidenceData`, deletion site/orientation data, `DeleteVertexMergedFaceSingleOrbit`, merged
outer-boundary normalization, clean-face classification, reserved-color facts, and the
`deleted_lists` Thomassen-list relabeling.

## Exact remaining top-level input

The sharp current certificate theorem is conditional on exactly:

```lean
PlanarInputs (ULift (Fin 5))
```

Equivalently, for every recursive near-triangulation with Thomassen lists, the planar layer must
supply either:

* `Σ u v, ChordRecursionData hNT u v p q L cp cq`, where side 1 can now be built from
  `Side₁CertificateInputs`, but side 2 still needs its mirror reconstruction family; or
* `ChordlessOracle hNT p q L cp cq`, with the chordless data listed above.
