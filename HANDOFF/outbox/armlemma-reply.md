2026-06-05

Status:

- Added `ProofsInTheBook/ArmLemma.lean`.
- Chosen convex-position formalization: a certified direction-angle normal form.
  For `r + 2` vertices, the certificate stores `r + 1` positive side lengths and
  `r` nonnegative turns with total turn at most `π`; the interior angle is
  `π - turn`, and the endpoint chord square is the usual cosine double sum.
- Proved the normal-form Cauchy arm lemma:
  `ProofsInTheBook.ArmLemma.ConvexArmProfile.cauchy_arm_lemma_profile`.
- Proved the point-level certified version:
  `ProofsInTheBook.ArmLemma.PlanarConvexArm.cauchy_arm_lemma`.
  It states the endpoint-distance inequality and the equality iff all
  corresponding Mathlib `EuclideanGeometry.angle`s are equal.

Verification:

```bash
~/.elan/bin/lake env lean ProofsInTheBook/ArmLemma.lean
grep -nE '\b(sorry|admit|axiom)\b' ProofsInTheBook/ArmLemma.lean || true
```

The Lean check exits 0.  The grep returns no matches.

Note:

- `HANDOFF/BOOK_CH13_CAUCHY.txt` referenced by the task is not present in this
  checkout, so I used the task statement as the source text.
- The remaining substrate, not hidden behind an axiom, is the geometric
  recognition theorem that an arbitrary strictly convex point polygon admits the
  `PlanarConvexArm` direction-angle certificate.  The arm inequality and the
  equality characterization are proved once such a certificate is supplied.
