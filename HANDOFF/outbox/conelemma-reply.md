Cone lemma completed.

- Created `ProofsInTheBook/ConeLemma.lean`.
- Proved `ProofsInTheBook.cone_lemma` with no `sorry`/`axiom`.
- Route used: flat base change for kernels (`LinearMap.tensorKerEquiv`) to express the real kernel from the rational kernel basis; rational approximation of the real basis coordinates inside the positive orthant; denominator clearing via `IsLocalization.exist_integer_multiples_of_finite`.
- Verified with:
  `PATH=$HOME/.elan/bin:$PATH lake env lean ProofsInTheBook/ConeLemma.lean`
