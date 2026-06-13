# Ch13 Face-Run Report (FFCT90)

## Files

- Added `ProofsInTheBook/ZinanFFCT90.lean`.
- Added this report.
- No existing Lean files were edited.

## Verification

Ran:

```bash
export PATH=$HOME/.elan/bin:$PATH && lake build ProofsInTheBook.ZinanFFCT89
export PATH=$HOME/.elan/bin:$PATH && lake env lean ProofsInTheBook/ZinanFFCT90.lean
export PATH=$HOME/.elan/bin:$PATH && lake build ProofsInTheBook.ZinanFFCT90
```

Both commands completed successfully.

`ZinanFFCT90.lean` contains no proof placeholders or unsafe declarations.

## What landed

`repeat_support_zero_next`:
from a repeat `P r = P s` and a non-wrapping successor edge `(s,s+1)`, weak supports of `(r,r+1)` and `(s,s+1)` force

```lean
det3 (P r) (P (r+1)) (P (s+1)) = 0
```

`repeat_support_zero_wrap`:
the same first-step determinant seed for the wrap case `s = n`, using the closing edge `(n,0)`:

```lean
det3 (P r) (P (r+1)) (P 0) = 0
```

`BoundedFaceRunPropagation`:
the exact remaining non-circular surface:
any repeat with `r + 3 ≤ s` must produce some consecutive flat triple.

`weakConvex_boundedJoints_noNonadjacentRepeat_of_faceRunPropagation`:
given `BoundedFaceRunPropagation`, the requested bounded no-repeat theorem follows by:

- gap `2`: FFCT88 `weakConvex_positiveJoints_noNonadjacentRepeat_gap_two`;
- gap `≥ 3`: `BoundedFaceRunPropagation` plus FFCT89 `weakConvex_boundedJoints_no_consecutive_det3_zero`.

`boundedWeakPositiveSimplicity_of_faceRunPropagation`, `crossPieceCollisionEndpointAtSup_of_faceRunPropagation`, and `spherical_arm_mono_ch13_of_faceRunPropagation`:
the FFCT89 wrappers close from the single face-run propagation surface.

## What did not land

The unconditional theorem named in the brief was not proved. The blocking step is exactly the face-run propagation from the first support-zero seed to a consecutive flat triple.

This is not an import/name issue. The current library repeatedly records the same obstruction:

- FFCT22 proves only the determinant-vanishing half of tail propagation and explicitly leaves cone/sign re-extraction out of scope.
- FFCT23 identifies `NoNonadjacentRepeat` as the audited master gap for weak positive arms.
- FFCT8 isolates the planar weak face-contiguity / strict-support upgrade as a real planar convexity residue.

So the final unconditional close still needs the convex face-contiguity theorem, or an equivalent signed-line propagation that does not require an existing no-repeat hypothesis.
