# Ch13 corners audit (FFCT75)

## Outcome

The requested `{hcross}`-only final surface was **not** proved.

Created `ProofsInTheBook/ZinanFFCT75.lean` as a kernel-checked audit layer over
`ZinanFFCT74`.  It records the pieces that are derivable without adding new
geometric hypotheses, but it does not introduce
`spherical_arm_mono_final_ch13_v9 mod {hcross}` because the remaining boundary
propagation is not present in the current substrate.

## What is checked in `ZinanFFCT75`

* `bpos_aneg_tail_span_forces_zero`: the `BPosANegTailCornerResidue` signed span
  always gives the wrap/tail zero
  `sOrient (P i) (P (i+1)) (P n) = 0`.
* `weak_wrap_base_is_last`: a raw wrap seed really has base index `n`.
* `weak_wrap_successor_is_zero`: the successor of that base is the head vertex.
* `weak_wrap_probe_interior`: the probed vertex in a genuine wrap seed is
  strictly interior: `0 < b.val ∧ b.val < n`.
* `spherical_arm_mono_final_ch13_v8_reexport`: FFCT74 remains the strongest
  checked final theorem in this branch.

## Why the three residues did not close

### `WeakVanishingWrapSeedResidue`

For a wrap raw support, the data reduce to
`sOrient (P n) (P 0) (P b) = 0` with `0 < b.val < n`.
`orientationNormalized` only handles non-wrap bases (`a.val + 1 < n + 1`), and
`mirrorArm` preserves the wrap edge as a wrap edge.  No landed theorem converts
this cyclic boundary zero into a normalized zero support on `P` or `mirrorArm P`
for middle vertices `2 ≤ b ≤ n-2`.

### `SupportStuckWBSWrapSeedResidue`

This is the same obstruction after opening: the raw WBS witness is on the
opened arm's wrap edge.  FFCT42/45 convert monitored base-stuck data into an
ordinary support in their own pinned setting, but there is no general theorem
taking an arbitrary wrap-base vanishing support and returning the normalized
seed required by `mirrorSeed_of_wrapSeedResidue`.

### `BPosANegTailCornerResidue`

The signed span
`P i = a • P(i+1) + b • P n`, with `a < 0 < b`, immediately gives the zero
support at `(i, i+1, n)`.  For `i > 0` this looks like an interior non-head
support, but the available planar core (`planarWeakNoflatStrictEdgeCore_holds`)
requires boundary-exclusion hypotheses (`hfirst`, `hlast`) that are not supplied
by the arm context.  For `i = 0`, this is exactly the head/wrap boundary case.

The FFCT70 successor collapse handles `j + 1 < n + 1`; at `j = n` the successor
is the wrap edge.  Existing files contain the required algebraic readouts in
pieces, but no theorem propagates the resulting wrap boundary collinearity to a
flat controlled interior joint.

## Verification

Remote single-file check on `uisai2`:

```text
lake env lean ProofsInTheBook/ZinanFFCT75.lean
```

Result: passed.  The audit output contains only the expected Lean / Mathlib
foundations (`propext`, `Classical.choice`, `Quot.sound`) and no placeholder
proof marker.
