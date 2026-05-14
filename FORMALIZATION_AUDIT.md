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

## Semantic TODO

- [ ] Chapter03: restore the general Sylvester theorem statement
  `∀ n k, 2 * k ≤ n → 0 < k → ∃ p, k < p ∧ p.Prime ∧ p ∣ n.choose k`
  and the almost-never-perfect-powers theorem.  The current file proves the
  central binomial case and a prime-divisor component only.
- [ ] Chapter04: replace the remaining comment-level gap for the
  sum-of-two-squares sufficiency/involution argument with an actual Lean proof
  path, or narrow the theorem statements and record the gap explicitly.
- [ ] Chapter09: build the Dehn-invariant geometry layer; the current theorem
  is only the abstract invariant obstruction.
- [ ] Chapter10: prove an incidence/geometric Sylvester-Gallai statement from
  the extremal-distance argument.  The current theorem only certifies a line
  already known to contain exactly two points.
- [ ] Chapter11: prove Ungar's slope lower bound.  The current theorem only
  turns an injected witness family into a slope-counting lower bound.
- [ ] Chapter13: formalize Cauchy's rigidity proof beyond local edge-sign
  bookkeeping.
- [ ] Chapter16: formalize a real Borsuk/Kahn-Kalai component.  The current
  theorem only checks a supplied finite coloring certificate.
- [ ] Chapter19: restore the fundamental theorem of algebra statement and
  replace the black-box root existence with the minimum-modulus proof path.
  The current theorem is only the linear root calculation.
- [ ] Chapter20: formalize Monsky's parity/Sperner argument and 2-adic color
  construction.  The current theorem only defines the color model.
- [ ] Chapter24: extend cotangent symmetries to the Herglotz functional
  equation / partial-fraction argument.  The current theorem is only a symmetry
  component.
- [ ] Chapter25: extend the finite polygonal linearity step to the actual
  Buffon needle probability statement.
- [ ] Chapter29: connect riffle labels to the Gilbert-Shannon-Reeds shuffle
  distribution.  The current file counts label assignments and proves the
  induced pile sizes sum to the deck size.
- [ ] Chapter30: formalize a real Lindstrom-Gessel-Viennot determinant/path
  statement rather than only the diagonal determinant case.
- [ ] Chapter31: connect the Prüfer code space to labeled trees and prove the
  bijective Cayley formula, not only the code-space cardinality.
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
  the Kneser graph adjacency relation, and the vertex count.
