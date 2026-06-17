# Ch36 Ears — Report

**File:** `ProofsInTheBook/ZinanCh36Ears.lean` (new).
**Status:** 0 errors. Verified with:

```bash
export PATH=$HOME/.elan/bin:$PATH && lake env lean ProofsInTheBook/ZinanCh36Ears.lean
```

Clean-3 axiom audit on the new named results:
`propext`, `Classical.choice`, `Quot.sound`.

No `sorry` / `admit` / `axiom` declarations / `native_decide`.

## What landed

The unconditional Meisters/two-ears producer requested in the brief is **not present in the landed
substrate**. The existing files expose the relevant planar content as hypotheses:

- `PolygonSideCrossing.convex_vertex_empty_triangle_gives_ear'` needs
  `IsConvexVertex'` plus `EarTransversality'`.
- `PolygonConvexVertex.exists_diagonal` gives an arbitrary diagonal through the empty-ear/slide
  branch, not necessarily an ear-base diagonal.
- `ZinanCh36Assembly.EarValueSplitData` specifically needs the ear-base diagonal
  `(cyclicPrev i, cyclicNext i)`, the two strict child axiom bundles, and same-ray child
  directions.

So the file lands the strongest honest adapter supported by the current codebase:

```lean
structure EarDiagonalSupply : Type where
  ear : ∀ {m}, StrictSimplePolygon m → Fin m
  hdiag : ∀ {m} (P : StrictSimplePolygon m) (ρ : RayDirection P),
    4 ≤ m → IsDiagonal' P ρ (cyclicPrev (ear P)) (cyclicNext (ear P))
```

From this plus the already-landed `PolygonJordan.RemainingResidualData`, the Ch36 assembly
`Esplit` input is discharged:

```lean
def esplit_holds
    (S : EarDiagonalSupply) (rest : RestFor S) :
    ∀ {m} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      4 ≤ m → EarValueSplitData P ρ ((earChoice S) P)
```

The construction is non-circular: `EarDiagonalSupply` does **not** contain the
`EarCutData.earDeletedExterior` field.  `EarValueSplitData` is assembled from:

- `S.hdiag` for the ear-base diagonal;
- `rest.leftAxioms` / `rest.rightAxioms` for child strictness;
- `rest.leftRay` / `rest.rightRay` and `rest.commonRay` for the common-ray child directions.

## Adapters

The file also provides:

- `earDiagonalSupply_of_earInput`: projects only the selector and diagonal field out of
  `PolygonJordan.EarInductionInput`.
- `esplit_holds_of_earInput`: the same `Esplit` producer specialized to that existing interface.
- `earValueSplitData_of_earCutData` and `esplit_holds_of_earCutData`: compatibility adapters from
  full `EarCutData` when a caller already has it.
- `artGallery_strict_mod_M_from_supply`: wires `esplit_holds` into
  `ZinanCh36Assembly.artGallery_strict_mod_M`.
- `artGallery_strict_mod_M_of_earInput`: same wiring from `PolygonJordan.EarInductionInput`.

## Resulting Ch36 surface

With this file, `Esplit` is no longer a separate input once an ear-base diagonal supply is available.
The honest surface is:

```lean
EarDiagonalSupply + RemainingResidualData + Ch36AttachInput
```

or, using the existing `PolygonJordan` interface:

```lean
EarInductionInput + RemainingResidualData + Ch36AttachInput
```

The requested `{rest, M}`-only surface would require an actual unconditional producer of
`EarDiagonalSupply` (Meisters/two-ears for strict simple polygons). That theorem is still absent; the
current substrate explicitly routes through named planar residues rather than proving it from a bare
`StrictSimplePolygon`.
