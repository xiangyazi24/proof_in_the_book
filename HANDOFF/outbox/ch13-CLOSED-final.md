# CH13 closing attempt (`ZinanFFCT83`)

## Status

Created `ProofsInTheBook/ZinanFFCT83.lean`.

The exact requested hcross-only theorem

```lean
theorem spherical_arm_mono_final_ch13_v10
    (hcross : CrossPieceNoCollisionAtSup) :
    SphericalArmMonotone
```

is **not** landed.  The file is kernel-checked and records the landed algebraic
tail bricks, but the backward sweep still needs the semantic cone re-extraction
brick.  No `sorry`, `admit`, `axiom`, or `native_decide` was introduced.

Remote verification used the brief's required path:

```bash
scp ProofsInTheBook/ZinanFFCT83.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT83.lean
ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && lake build ProofsInTheBook.ZinanFFCT82 && lake env lean ProofsInTheBook/ZinanFFCT83.lean'
```

Result: 0 errors.  The new declarations are clean-3:

```text
OpenCone.sOrient_zero
openCone_tail_of_aneg_bpos
edgeAnchor_prev_plane_of_next_openCone
openCone_consecutive_absurd
bpos_aneg_tail_adjacent_forbidden
bpos_aneg_tailCornerResidueV9_of_forbiddenCore
spherical_arm_mono_final_ch13_v10_of_hcross_wrapNoTail_ffct83
```

Each depends only on:

```text
[propext, Classical.choice, Quot.sound]
```

## Landed Content

`OpenCone p q z` is the strict positive real cone:

```lean
def OpenCone (p q z : S2) : Prop :=
  ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
    (z : E3) = c • (p : E3) + d • (q : E3)
```

The signed tail span rearranges into the positive tail cone:

```lean
theorem openCone_tail_of_aneg_bpos :
    ... → 0 < b → a < 0 →
    OpenCone (P i) (P (i+1)) (P n)
```

The determinant anchor step is checked:

```lean
theorem edgeAnchor_prev_plane_of_next_openCone :
    OpenCone P Q C →
    0 ≤ sOrient Y C P →
    0 ≤ sOrient Y C Q →
    sOrient P Q Y = 0
```

The adjacent tail case closes:

```lean
theorem bpos_aneg_tail_adjacent_forbidden :
    i + 2 = n → ... → False
```

The file also exposes the precise missing core:

```lean
def BPosANegTailForbiddenCore : Prop := ...

theorem bpos_aneg_tailCornerResidueV9_of_forbiddenCore
    (hcore : BPosANegTailForbiddenCore) :
    BPosANegTailCornerResidueV9
```

and re-exports the checked FFCT81 conditional wrapper:

```lean
theorem spherical_arm_mono_final_ch13_v10_of_hcross_wrapNoTail_ffct83
    (hcross : CrossPieceNoCollisionAtSup)
    (hwrap : WrapPlanePropagationNoTail) :
    SphericalArmMonotone
```

## Blocking Point

The closing brief's Brick C is not present in the checked library:

```lean
openCone_of_plane_short_not_on_edge
```

The needed content is a sector re-extraction theorem: from

```text
Y in plane(P,Q),
ShortArc Y C,
C in OpenCone P Q,
not OnFoldRay Y C P,
not OnFoldRay Y C Q
```

derive `OpenCone P Q Y`.

This is the same sign-recovery gap already documented in `ZinanFFCT22.lean`:
`far_fold_tail_collinear_step` proves only the determinant-zero/plane half, not
the nonnegative-cone membership needed to continue an induction.  `OnFoldRay`
itself is available, but the theorem that excludes the wrong sector is not.

The statement in the design note that "`NR` excludes it" is not supported by the
current APIs.  `NoNonadjacentRepeat` excludes equality of nonadjacent vertices;
it does not exclude a nonincident vertex lying on the same fold ray or support
great circle.  The support-stuck pipeline explicitly treats nonincident support
zeros as real data, so this cannot be replaced by a repeat argument.

Therefore the final hcross-only theorem still requires one of:

```lean
BPosANegTailForbiddenCore
```

or the stronger propagation theorem already isolated by FFCT81:

```lean
WrapPlanePropagationNoTail
```

Once either is supplied, the checked wrappers in FFCT81/83 assemble the remaining
v10 endpoint surface without re-entering the signed-tail consumer.
