# CH13 v10 stratification report (`ZinanFFCT81`)

## Status

Created `ProofsInTheBook/ZinanFFCT81.lean`.

The stratified no-tail consumer is landed and kernel-checked.  The exact
hcross-only theorem

```lean
theorem spherical_arm_mono_final_ch13_v10
    (hcross : CrossPieceNoCollisionAtSup) :
    SphericalArmMonotone
```

is **not** landed, because the current `BoundaryZeroProgress` payload does not
carry the no-tail side condition needed to avoid the `BPosANegTailCornerResidueV9`
branch.  No proof placeholders or unsafe declarations were introduced.

Remote verification:

```bash
scp ProofsInTheBook/ZinanFFCT81.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT81.lean
ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && lake build ProofsInTheBook.ZinanFFCT80 && lake env lean ProofsInTheBook/ZinanFFCT81.lean'
```

Result: 0 errors.  The new declarations are clean-3:

```text
boundaryZeroProgress_of_noTail
endpoint_of_span_at_level_nr_noTail
endpoint_of_normalized_vanishing_support_at_level_nr_noTail
endpoint_of_normalizedInteriorZero_noTail
endpoint_of_boundaryZeroProgress_noTail_at_level_nr
wrapPlanePropagationGeneral_of_noTail
bpos_aneg_tailCornerResidueV9_of_wrapPlanePropagationNoTail
spherical_arm_mono_final_ch13_v10_of_hcross_wrapNoTail
```

Each depends only on:

```text
[propext, Classical.choice, Quot.sound]
```

## Landed content

`ZinanFFCT81` introduces the stronger progress shape:

```lean
def NormalizedStrictInteriorSupportZero {n : ℕ} (A : Fin (n + 1) → S2) : Prop
def BoundaryZeroProgressNoTail {n : ℕ} (A B : Fin (n + 1) → S2) : Prop
```

The extra datum is `j + 1 < n + 1` for the normalized far probe.  With that
side condition, the coefficient dispatch closes the `b > 0, a < 0` branch by
`bpos_aneg_false_of_successor`, so the consumer has no
`BPosANegTailCornerResidueV9` argument:

```lean
theorem endpoint_of_normalizedInteriorZero_noTail
```

The file also proves that a strengthened wrap propagation theorem would close
the signed tail residue without re-entry:

```lean
def WrapPlanePropagationNoTail : Prop

theorem bpos_aneg_tailCornerResidueV9_of_wrapPlanePropagationNoTail
    (hwrap : WrapPlanePropagationNoTail) :
    BPosANegTailCornerResidueV9
```

and assembles the corresponding conditional final wrapper:

```lean
theorem spherical_arm_mono_final_ch13_v10_of_hcross_wrapNoTail
    (hcross : CrossPieceNoCollisionAtSup)
    (hwrap : WrapPlanePropagationNoTail) :
    SphericalArmMonotone
```

## Why the exact brief target is still blocked

The existing `BoundaryZeroProgress` definition is:

```lean
def BoundaryZeroProgress {n : ℕ} (A B : Fin (n + 1) → S2) : Prop :=
  NormalizedInteriorSupportZero A ∨ endpt A ≤ endpt B
```

and `NormalizedInteriorSupportZero` only records:

```lean
i + 1 < j
j < n + 1
```

It does **not** record `j + 1 < n + 1`.  In fact, existing checked wrappers
use endpoint probes: `wrapPlanePropagation_probe_one` returns the normalized
zero `(i,j) = (0,n)`.  Therefore the old payload cannot feed a no-tail consumer
definitionally or by `omega`.

So the remaining honest missing theorem is not just:

```lean
WrapPlanePropagationGeneral
```

but a stronger propagation theorem that returns either an endpoint payload or a
normalized zero with the successor side condition:

```lean
WrapPlanePropagationNoTail
```

Once that is supplied, `ZinanFFCT81` closes the tail residue and assembles the
v10 final wrapper.
