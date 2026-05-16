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
- [x] Chapter04: replace the remaining comment-level gap for the
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
  equalities.  The three inverse cases and the full involution theorem for
  this map are proved.  A fixed point of the Zagier map is now shown to have
  `x = 1` and `y = 1`, fixed points are unique, the canonical triple is
  proved to be the unique fixed point for primes of the form `4k + 1` with
  `0 < k`, the triple set is proved odd, and the `swapYZ` fixed-point
  argument now yields a sum-of-two-squares representation for primes
  congruent to `1 mod 4`.  The public `chapter04_sufficiency` theorem now
  calls this Zagier proof path, with the prime `2` handled separately.
- [ ] Chapter09: build the Dehn-invariant geometry layer.  The current file
  defines the tensor-product target, concrete `ℝ/πℤ` quotient, edge-sum
  algebra, partition additivity, scissors certificate, obstruction lemma,
  and now states Hilbert's third problem via `hilbert_third_problem` and
  `arccos_one_third_irrational_over_pi`.  It still lacks actual polyhedral
  geometry and the full `πℚ` quotient.
- [ ] Chapter10: prove an incidence/geometric Sylvester-Gallai statement from
  the extremal-distance argument.  The current file now has ordinary-line
  bookkeeping, the finite off-line pair minimization step, the closer-pair
  contradiction structure (Gallai's argument that ≥3 points on a line yields
  a nearer off-line pair), and an abstract Sylvester-Gallai theorem statement.
  It still lacks the actual Euclidean geometry linking the abstract and
  concrete arguments.
- [ ] Chapter11: prove Ungar's slope lower bound.  The current file now
  distinguishes finite slopes from the vertical direction, proves the
  nonvertical slope set embeds into the full direction set, and states the
  target `n - 1 ≤ |directions|` lower bound.  It still lacks Ungar's
  rotating-calipers construction.
- [ ] Chapter13: formalize Cauchy's rigidity proof beyond local edge-sign
  bookkeeping.  The current file now separates zero edges from strict `+/-`
  signs, proves the strict triangular sign-change count is even, and states
  the abstract arm lemma and Euler sign-change parity interfaces.  It still
  lacks the concrete arm-lemma proof and convex polyhedron geometry.
- [ ] Chapter16: formalize a real Borsuk/Kahn-Kalai component.  The current
  file now proves basic finite color-class partition facts for a supplied
  Borsuk-style coloring certificate, but it still lacks the Kahn-Kalai
  combinatorial construction or any Euclidean counterexample.
- [ ] Chapter19: restore the fundamental theorem of algebra statement and
  replace the black-box root existence with the minimum-modulus proof path.
  The current file now has the polynomial translation layer, first-nonzero
  coefficient extraction, the local norm-decrease lemma statement
  (`complex_poly_local_norm_decrease`), the shifted-polynomial specialization
  (`shiftedPolynomial_local_norm_decrease`), and the minimum-modulus
  contradiction theorem (`fta_minimum_modulus_contradiction`).  The core
  analytic norm-decrease proof and the nonconstancy-implies-nonzero-shift
  remain as sorry.
- [ ] Chapter20: formalize Monsky's parity/Sperner argument and 2-adic color
  construction.  The current file proves the local parity atom, the
  `sum_nat_mod_two_eq_sum_mod_two` helper, the full `sperner_parity_abstract`
  theorem, and the `exists_trichromatic_of_odd_boundary` corollary — all
  sorry-free.  It still lacks the 2-adic coloring construction and the
  double-counting link between interior and boundary red-green edges.
- [ ] Chapter24: extend cotangent symmetries to the full Herglotz functional
  equation / partial-fraction argument.  The current file now proves the
  cotangent symmetries, abstracts the `HerglotzClass` structure with
  `eval_half` and `cancel` lemmas, proves the duplication formula for
  periodic functions, and defines the finite rational partial-sum function.
  It still lacks the limit argument connecting the partial sums to
  `π·cot(πx)`.
- [ ] Chapter25: extend the finite polygonal linearity step to the actual
  Buffon needle probability statement.  The current file now proves the
  single-segment crossing value is in `[0, 1]`, states Buffon's needle
  formula `P = 2ℓ/(πd)`, and proves the noodle generalization for curves.
  It still lacks the measure-theoretic probability foundation.
- [ ] Chapter29: connect riffle labels to the Gilbert-Shannon-Reeds shuffle
  distribution.  The current file counts label assignments, proves the
  label piles form a disjoint cover of the deck, defines the stable riffle
  order with irreflexivity, transitivity, and trichotomy, and states the
  pile-size counting interface.
- [ ] Chapter30: formalize a real Lindstrom-Gessel-Viennot determinant/path
  statement.  The current file exposes the determinant's signed-permutation
  expansion, the diagonal determinant case, abstract sign-reversing
  cancellation with good/bad split, a `BadInvolutionCertificate` package,
  the path-swap sign-change lemma (`path_swap_changes_sign`), and the
  LGV identity-case framework.  It still lacks the concrete path-family
  intersection involution construction.
- [ ] Chapter31: construct the actual Prüfer encode/decode bijection.  The
  current file defines labeled trees, proves Cayley's count from a supplied
  equivalence, defines Prüfer leaves (vertices not in the code), and proves
  the leaf set is nonempty for `n ≥ 2` by a counting argument.  It still
  lacks the actual encode/decode algorithms.
- [ ] Chapter34: prove the list-coloring/Galvin step for Dinitz arrays.  The
  current file defines Dinitz solutions, row/column injectivity, a
  kernel-perfect orientation structure, and Galvin's greedy extension step
  (unused colors exist when the list is larger than the neighbor set).  It
  still lacks the actual kernel-perfect orientation construction for
  bipartite graphs.
- [x] Chapter35: formalize the five-color induction/Kempe-chain step.  The
  file now proves the average-degree lemma, the low-degree extension,
  `swapColor` with injectivity, `kempeSwap_proper_abstract` (fully proved,
  no sorry), and the `kempe_frees_color` anchor swap.  The Kempe swap
  properness proof uses explicit case analysis with `if_pos`/`if_neg` for
  cross-boundary cases.  Only the planarity argument (step 4 of the
  five-color theorem) remains unstated.
- [ ] Chapter36: add the geometric prerequisites for the art-gallery theorem:
  triangulation existence for simple polygons and Fisk's 3-coloring of the
  triangulation graph.  The current file now proves the finite guard-selection
  step once a 3-colored triangulation is supplied.
- [ ] Chapter39: formalize Kneser graph coloring and prove Lovász/Bárány
  lower-bound components.  The current file now defines Kneser vertices,
  the Kneser graph adjacency relation, the coloring separation property,
  the vertex count, and states both the chromatic upper bound
  (`n - 2k + 2`-colorability) and the lower bound (not `(n - 2k + 1)`-colorable).
  Both bounds remain as sorry; the lower bound requires Borsuk-Ulam.
