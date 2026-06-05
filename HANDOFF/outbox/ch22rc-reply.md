Done.

- Proved `roots_im_nonpos_of_tendsto` in `ProofsInTheBook/Chapter22Stable.lean`.
- Followed the requested root-vector plan: root enumeration by `toList`, Cauchy-bound tail, Bolzano-Weierstrass subsequence, Vieta coefficient identification, and product-root recovery.
- No proof placeholders or unsafe declarations introduced.
- Verified with:
  `lake env lean ProofsInTheBook/Chapter22Stable.lean`

Lean reports only pre-existing warnings in the file (`push_neg` deprecation, one unused simp argument, and one unnecessary `simpa` suggestion).
