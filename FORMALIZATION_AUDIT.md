# Formalization Audit

This file records semantic completion status for the full-book objective.

`bash scripts/goal check all` is a syntactic gate: it checks for `sorry`,
`: True`, and known black-box placeholders.  It is not enough to certify that
the book has been formalized.  A chapter remains semantically open if its main
statement has been weakened, if it only contains a local core component, or if
the proof bypasses the book argument.

## Current Evidence

- `bash scripts/goal check all` reports syntactic completion.
- `lake build` succeeds.
- The repository still contains chapters whose current `chapterNN` theorem is
  only a component of the book proof, not the book theorem.

## Work Order

Proceed in the order below.  The next default focus is the earliest unchecked
chapter in `Semantic TODO`; currently that is Chapter03.  Skipping ahead is
allowed only when the current chapter has a concrete blocker recorded in this
file or when a later chapter has a small dependency-free strengthening that is
explicitly logged in `Changelog.md`.

## Semantic TODO

- [ ] Chapter03: restore the general Sylvester theorem statement
  `∀ n k, 2 * k ≤ n → 0 < k → ∃ p, k < p ∧ p.Prime ∧ p ∣ n.choose k`
  and the almost-never-perfect-powers theorem.  The current file proves the
  central binomial case, a reusable factorial-divisibility lemma for binomial
  coefficients, the corresponding interval-prime binomial divisor lemma, and
  a `descFactorial` bridge reducing the general binomial divisor conclusion
  to proving that `n(n-1)...(n-k+1)` is not `(k+1)`-smooth.
- [ ] Chapter04: replace the remaining comment-level gap for the
  sum-of-two-squares sufficiency/involution argument with an actual Lean proof
  path, or narrow the theorem statements and record the gap explicitly.
- [ ] Chapter09: build the Dehn-invariant geometry layer.  The current file
  now defines the tensor-product target for an abstract angle quotient and the
  finite edge-sum algebra, but it still lacks actual polyhedral geometry,
  angle quotients by `πℚ`, and dissection invariance.
- [ ] Chapter10: prove an incidence/geometric Sylvester-Gallai statement from
  the extremal-distance argument.  The current file now has ordinary-line
  bookkeeping and the finite off-line pair minimization step, but it still
  lacks the actual plane geometry and closer-pair contradiction.
- [ ] Chapter11: prove Ungar's slope lower bound.  The current file now
  distinguishes finite slopes from the vertical direction and proves the
  nonvertical slope set embeds into the full direction set, but it still lacks
  Ungar's rotating-calipers construction.
- [ ] Chapter13: formalize Cauchy's rigidity proof beyond local edge-sign
  bookkeeping.
- [ ] Chapter16: formalize a real Borsuk/Kahn-Kalai component.  The current
  theorem only checks a supplied finite coloring certificate.
- [ ] Chapter19: restore the fundamental theorem of algebra statement and
  replace the black-box root existence with the minimum-modulus proof path.
  The current theorem is only the linear root calculation.
- [ ] Chapter20: formalize Monsky's parity/Sperner argument and 2-adic color
  construction.  The current theorem only defines the color model.
- [ ] Chapter24: extend cotangent symmetries to the full Herglotz functional
  equation / partial-fraction argument.  The current file proves the cotangent
  symmetries and the corresponding rational identity for the two singular
  terms.
- [ ] Chapter25: extend the finite polygonal linearity step to the actual
  Buffon needle probability statement.
- [ ] Chapter29: connect riffle labels to the Gilbert-Shannon-Reeds shuffle
  distribution.  The current file counts label assignments and proves the
  induced pile sizes sum to the deck size.
- [ ] Chapter30: formalize a real Lindstrom-Gessel-Viennot determinant/path
  statement.  The current file exposes the determinant's signed-permutation
  expansion and the diagonal determinant case, but not yet the path-family
  involution/cancellation proof.
- [ ] Chapter31: construct the actual Prüfer encode/decode bijection.  The
  current file now defines labeled trees as `SimpleGraph.IsTree` objects on
  `Fin n` and proves Cayley's count from a supplied Prüfer equivalence.
- [ ] Chapter34: prove the list-coloring/Galvin step for Dinitz arrays.  The
  current theorem now defines the list-respecting Dinitz solution target and
  checks that a supplied row/column-injective list-respecting coloring is a
  solution.
- [ ] Chapter35: formalize the five-color induction/Kempe-chain step.  The
  current file proves the average-degree lemma and the easy low-degree
  extension for vertices with at most four neighbor colors; the degree-five
  Kempe-chain case remains open.
- [ ] Chapter36: add the geometric prerequisites for the art-gallery theorem:
  triangulation existence for simple polygons and Fisk's 3-coloring of the
  triangulation graph.  The current file now proves the finite guard-selection
  step once a 3-colored triangulation is supplied.
- [ ] Chapter39: formalize Kneser graph coloring and prove Lovasz/Barany
  lower-bound components.  The current file now defines Kneser vertices,
  the Kneser graph adjacency relation, the coloring separation property for
  disjoint subsets, and the vertex count.
