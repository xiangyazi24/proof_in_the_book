2026-06-05 08:40 CDT

Implemented `ProofsInTheBook/PolygonSubstrate.lean` for Layers A0-A2.

Lean check:

```text
/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/PolygonSubstrate.lean
```

passed with no `sorry`, `axiom`, or `admit`.

Contents:

- A0: `Pt`, `seg`, `closedTri`, `relIntTri`, `det2`, `orient`, `Collinear3`; determinant/orientation antisymmetry; collinearity iff; closed-triangle convexity; segment-in-triangle; finite segment-intersection parameters.
- A1: `StrictSimplePolygon` with cyclic tuple, injectivity, nonconsecutive collinearity exclusion, and explicit `EdgeIntersectionCondition`; `OnBoundary`; `RayDirection`; constructive `rayDirection_exists` by finite slope avoidance; half-open ray crossing; parity `ClosedRegion`; boundary/edge inclusion lemmas.
- A2: `IsDiagonal`; projection lemmas for region containment and boundary-only endpoint intersection; cyclic index-step split data and `diagonal_splits_boundary_indices`.

Notes:

- This Mathlib checkout does not expose a `relativeInterior` API under that name, so `relIntTri` is currently `interior (closedTri a b c)`. A0-A2 do not consume it.
- `diagonal_splits_boundary_indices` proves the index-level split as two positive cyclic edge counts adding to `n`, with each side smaller than the original cycle. It does not yet construct the actual subpolygon vertex tuples.
