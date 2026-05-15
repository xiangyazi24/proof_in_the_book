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

Current blocker: Chapter03's remaining Sylvester non-smoothness core is not yet
split into a Lean-feasible proof path.  Three `ssem` bridge attempts on
2026-05-14 (`9eabd2c5`, `8471a107`, `49c190b1`) timed out, including a
statement-only prompt.  Until this is decomposed further, later independent
semantic TODO items may be advanced in logged, build-checked increments.

## Semantic TODO

- [ ] Chapter03: restore the general Sylvester theorem statement
  `∀ n k, 2 * k ≤ n → 0 < k → ∃ p, k < p ∧ p.Prime ∧ p ∣ n.choose k`
  and the almost-never-perfect-powers theorem.  The current file proves the
  central binomial case, a reusable factorial-divisibility lemma for binomial
  coefficients, the corresponding interval-prime binomial divisor lemma, and
  a `descFactorial` bridge reducing the general binomial divisor conclusion
  to proving that `n(n-1)...(n-k+1)` is not `(k+1)`-smooth.  It also now
  proves that each factor `n - i` of the descending product inherits
  `(k+1)`-smoothness from the whole product, and therefore every prime
  divisor of such a factor is at most `k`; conversely, a large prime factor
  in any descending factor immediately witnesses non-smoothness of the whole
  descending product.
- [ ] Chapter04: replace the remaining comment-level gap for the
  sum-of-two-squares sufficiency/involution argument with an actual Lean proof
  path, or narrow the theorem statements and record the gap explicitly.  The
  current file now includes the modulo-four necessity, Brahmagupta
  multiplication, Mathlib-backed characterization, a finite `ZagierTriple`
  type, and the simple swap involution with fixed points characterized by
  `y = z`; it also proves that a swap fixed point gives a sum-of-two-squares
  representation.  It now also has the finite odd-cardinality involution
  lemma, applies it to the swap involution, and constructs the canonical
  triple `(1, 1, k)` for numbers of the form `4k + 1` with `0 < k`.  The
  three local branches of Zagier's piecewise involution are now constructed,
  along with a total map for primes `p ≠ 2` after ruling out the two boundary
  equalities.  The branch-one inverse case of this map is proved.  The other
  inverse cases, the full involution theorem, the unique fixed-point theorem,
  and the odd-cardinality conclusion remain open.
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
  bookkeeping.  The current file now separates zero edges from strict `+/-`
  signs and proves the strict triangular sign-change count is even, but it
  still lacks the arm lemma, Euler counting, and convex polyhedron geometry.
- [ ] Chapter16: formalize a real Borsuk/Kahn-Kalai component.  The current
  file now proves basic finite color-class partition facts for a supplied
  Borsuk-style coloring certificate, but it still lacks the Kahn-Kalai
  combinatorial construction or any Euclidean counterexample.
- [ ] Chapter19: restore the fundamental theorem of algebra statement and
  replace the black-box root existence with the minimum-modulus proof path.
  The current file now has the linear root calculation and the polynomial
  translation layer `w ↦ p(w+z₀)`, plus extraction of the first nonzero
  positive coefficient after subtracting the constant term.  It still lacks
  the minimum-modulus existence argument and local norm-decrease step.
- [ ] Chapter20: formalize Monsky's parity/Sperner argument and 2-adic color
  construction.  The current file now defines the color model and the local
  red-green edge parity atom for trichromatic triangles, but it still lacks
  the global Sperner parity count and 2-adic coloring construction.
- [ ] Chapter24: extend cotangent symmetries to the full Herglotz functional
  equation / partial-fraction argument.  The current file proves the cotangent
  symmetries, abstracts the period-one-plus-odd cancellation step, and proves
  the corresponding rational identity for the two singular terms.
- [ ] Chapter25: extend the finite polygonal linearity step to the actual
  Buffon needle probability statement.  The current file now also proves the
  single-segment expectation is nonnegative and bounded by `1` in the usual
  `0 < d`, `length ≤ d` needle regime, but it still lacks the measure-theoretic
  probability model and symmetry argument.
- [ ] Chapter29: connect riffle labels to the Gilbert-Shannon-Reeds shuffle
  distribution.  The current file counts label assignments and proves the
  label piles form a disjoint cover of the deck, with the induced pile-size
  vector summing to the deck size.
- [ ] Chapter30: formalize a real Lindstrom-Gessel-Viennot determinant/path
  statement.  The current file exposes the determinant's signed-permutation
  expansion, the diagonal determinant case, and an abstract finite
  sign-reversing cancellation layer with a good/bad split and packaged
  cancellation certificate, but not yet the path-family involution
  construction itself.
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
