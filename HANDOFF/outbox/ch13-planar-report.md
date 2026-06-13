# Ch13 planar no-repeat report

## Outcome

Added `ProofsInTheBook/ZinanFFCT93.lean`.

The requested `PlanarClosedWeakStrictNoRepeat` proof cannot be supplied because
the statement in `ZinanFFCT92` is false as written.  `ZinanFFCT93` gives a
machine-checked counterexample:

```lean
theorem not_planarClosedWeakStrictNoRepeat :
    ¬ PlanarClosedWeakStrictNoRepeat
```

## Counterexample

Use the affine plane `z = 1` with normal `triH = (0,0,1)` and traverse the
triangle

```text
A = (0,0,1), B = (1,0,1), C = (0,1,1)
```

twice:

```text
A, B, C, A, B, C
```

The file proves:

- every vertex satisfies `⟪triH, x⟫ = 1`;
- every cyclic directed edge weakly supports every vertex;
- every cyclic edge is nonzero;
- every non-wrapping consecutive turn is strict;
- nevertheless `triTwice 0 = triTwice 3`, contradicting the requested
  no-repeat conclusion at gap `3`.

This is the standard multiple-traversal obstruction: the hypotheses allow a
convex polygonal cycle to be run more than once.

## Verification

Ran:

```bash
export PATH=$HOME/.elan/bin:$PATH
lake build ProofsInTheBook.ZinanFFCT92
lake env lean ProofsInTheBook/ZinanFFCT93.lean
```

Result: both completed successfully.  A clean-token scan on
`ProofsInTheBook/ZinanFFCT93.lean` returned no matches.

## Consequence

The downstream unconditional `spherical_arm_mono_ch13` wrapper cannot be derived
from the FFCT92 planar core without strengthening that planar core.  A likely
repair is to exclude multiple traversal, for example by adding a winding/total
turn bound, a primitivity condition, or a strict nonincident support hypothesis
strong enough to rule out repeated cycles.
