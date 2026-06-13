# ch13 face-contiguity report

## Added

Created `ProofsInTheBook/ZinanFFCT91.lean`.

The file proves the algebraic end of the face-contiguity route:

- `face_run_consecutive_flat_at`: if all vertices in a run lie on the support great circle of edge `(r,r+1)`, then any consecutive triple inside that run has determinant zero.
- `face_run_consecutive_flat`: packages the first interior flat triple `(r+1,r+2,r+3)`.
- `gap_three_flat_of_faceContiguity`: the `s = r+3` case follows from the face-contiguity statement.
- `boundedFaceRunPropagation_of_faceContiguity`: the face-contiguity statement supplies FFCT90's exact `BoundedFaceRunPropagation`.
- `boundedWeakPositiveSimplicity_of_faceContiguity`, `weakConvex_boundedJoints_noNonadjacentRepeat_of_faceContiguity`, `crossPieceCollisionEndpointAtSup_of_faceContiguity`, and `spherical_arm_mono_ch13_of_faceContiguity`: downstream FFCT90 composition from the sharper geometric surface.

## Remaining surface

The unconditional face-contiguity theorem itself is still isolated as:

```lean
def FaceContiguityPropagation : Prop := ...
```

This is narrower than FFCT90's old surface: it states exactly that the repeated run `[r+1,s]` lies on the support great circle of `(r,r+1)`. Once supplied, the rest of the route is now checked.

## Verification

Ran:

```bash
export PATH=$HOME/.elan/bin:$PATH && lake build ProofsInTheBook.ZinanFFCT90 && lake env lean ProofsInTheBook/ZinanFFCT91.lean
rg -n "sorry|admit|axiom|native_decide" ProofsInTheBook/ZinanFFCT91.lean
```

Result: build/check succeeded. The forbidden-token scan on `ZinanFFCT91.lean` returned no matches.
