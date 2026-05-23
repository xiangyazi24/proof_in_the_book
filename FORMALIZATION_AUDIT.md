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

  **Tier 2 progress (2026-05-23):** `chapter03_erdos` now has its first of
  three hypotheses fully discharged.  `prod_lPowerFreeParts_dvd_factorial_l2`
  (~300 LOC, Erdős l=2 divisibility step) is proved via 5 helpers:
  `lPowerFreePart_factorization_eq_mod` (squarefree-based),
  `card_filter_dvd_le_aux` (interval count of multiples),
  `factorization_factorial_ge_div` / `_ge_div_succ` / `_eq_div_of_sq_lt`
  (Legendre lemmas via `padicValNat_factorial`).  Plus
  `lPowerFreePart_two_ne_four` and `lPowerFreePart_ne_of_not_squarefree`
  (the squarefreeness obstruction for the `h_l2_contra` step),
  `lPowerFreePart_eq_self_iff_squarefree` + `lPowerFreePart_idem`
  (fixed-point characterization), plus basic dvd_self/le_self/pos/one
  lemmas.  The remaining gaps are `lPowerFreePart_injective_l2` (Step 3a
  distinctness, requires strengthening Step 1 from `n > k²` toward
  `n ≥ (2k-1)²`-ish) and the l ≥ 3 case (`h_ge3`).
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
  `arccos_one_third_irrational_over_pi`.

  **Tier 2 progress (2026-05-23):** The `πℚ` quotient is now built:
  `piQSubmodule := ℚ • π`, `AngleModPiQ := ℝ ⧸ πℚ`, `angleClassQ` projection.
  Algebra (`angleClassQ_pi`, `angleClassQ_rat_mul_pi`, `angleClassQ_pi_div_two`,
  `angleClassQ_pi_div n`, `angleClassQ_int_mul_pi`, additivity, `_eq_zero_iff`,
  `_sub_rat_mul_pi`).  Crucially `angleClassQ_arccos_one_third_ne_zero`
  uses `arccos_one_third_irrational_over_pi` to certify the tetrahedron's
  nontrivial Dehn-edge contribution in the new `πℚ` quotient.  The
  polyhedral-geometry side (defining cube + regular tetrahedron with
  dihedral angles in `EuclideanGeometry`) remains.
- [ ] Chapter10: prove an incidence/geometric Sylvester-Gallai statement from
  the extremal-distance argument.  The current file now has ordinary-line
  bookkeeping, the finite off-line pair minimization step, the closer-pair
  contradiction structure (Gallai's argument that ≥3 points on a line yields
  a nearer off-line pair), and an abstract Sylvester-Gallai theorem statement.

  **Tier 2 progress (2026-05-23):** `OrdinaryLine ↔ pointsOnLine.card = 2`
  biconditional, `pointsOnLine_subset/card_le/eq_empty_iff`,
  `offLinePairs_nonempty_iff/eq_empty_iff` (degenerate trivially-collinear
  characterization), `two_le_card_pointsOnLine_of_ordinaryLine`, and
  `sylvester_gallai_abstract_card_le` (combined ≤ 2 packaging).  Concrete
  Euclidean instantiation of `dist`, `footLine`, `closerPoint` remains TODO.
- [ ] Chapter11: prove Ungar's slope lower bound.  The current file now
  distinguishes finite slopes from the vertical direction, proves the
  nonvertical slope set embeds into the full direction set, and states the
  target `n - 1 ≤ |directions|` lower bound.  It still lacks Ungar's
  rotating-calipers construction.
- [ ] Chapter13: formalize Cauchy's rigidity proof beyond local edge-sign
  bookkeeping.  The current file now separates zero edges from strict `+/-`
  signs, proves the strict triangular sign-change count is even, and states
  the abstract arm lemma and Euler sign-change parity interfaces.

  **Tier 2 progress (2026-05-23):** `arm_lemma_abstract` strengthened from
  `True := trivial` placeholder to actual `chord < newChord` conclusion via
  hypothesis disjunction.  `euler_sign_change_parity` strengthened from
  `True := trivial` to actual `Even (∑ signChangesPerFace)` via
  `Finset.even_sum`.  Plus `signChangesAroundTriangle_eq_zero_iff` (= 0 iff
  all equal), `signChangesAroundTriangle_cycle` /
  `strictSignChangesAroundTriangle_cycle` (cyclic invariance for both
  edge-sign types), `strictSignChangesAroundTriangle_eq_zero_iff`.  The
  concrete arm-lemma geometric proof and convex polyhedron infrastructure
  remain TODO.
- [ ] Chapter16: formalize a real Borsuk/Kahn-Kalai component.  The current
  file now proves basic finite color-class partition facts for a supplied
  Borsuk-style coloring certificate.

  **Tier 2 progress (2026-05-23):** `borsukConjecture_iff_no_certificate`
  (Iff packaging), `KahnKalaiCertificate.nonempty` (any cert has nonempty
  underlying set, from pos_diam), `borsuk_no_certificate_of_conjecture`
  (converse direction of chapter16), `borsukConjecture_zero` (Borsuk holds
  vacuously in dim 0 since diam ≤ 0), `KahnKalaiCertificate.isEmpty_zero`
  (no cert exists in dim 0), `colorClass_biUnion_eq_points` + `_card_sum`
  + `_nonempty_of_mem` + `_nonempty_iff` + `_card_le`.  The Kahn-Kalai
  Frankl-Wilson combinatorial construction for d ≥ 298 remains TODO.
- [x] Chapter19: FTA endpoint `chapter19 (p : ℂ[X]) (hdeg : 1 ≤ p.natDegree)
  : ∃ z : ℂ, p.eval z = 0` is unconditional and proved.  The full chain
  exists: `complex_poly_local_norm_decrease` (real proof via small-t
  perturbation + compactness on `Set.Icc 0 1`), `poly_decompose`,
  `shiftedPolynomial_local_norm_decrease`, `fta_minimum_modulus_contradiction`,
  and the nonconstancy-via-natDegree argument inlined in `chapter19`.
  No sorry, no axiom.  (Updated 2026-05-22; earlier audit entry was stale.)
- [ ] Chapter20: formalize Monsky's parity/Sperner argument and 2-adic color
  construction.  The current file proves the local parity atom, the
  `sum_nat_mod_two_eq_sum_mod_two` helper, the full `sperner_parity_abstract`
  theorem, and the `exists_trichromatic_of_odd_boundary` corollary — all
  sorry-free.

  **Tier 2 progress (2026-05-23):** MonskyColor algebra:
  `MonskyColor.card = 3`, `redGreenEdge_symm`, `redGreenEdge_ne`,
  `redGreenEdge_not_blue`, `redGreenEdge_cases`, `not_redGreenEdge_self`,
  `trichromaticTriangle_cycle/swap_outer/iff_red_green_blue_present`.
  Certificate analysis: `MonskyCertificate.isEmpty_zero` (n=0 cert
  impossible by parity), `MonskyCertificate.boundaryRGCount_pos`,
  `MonskyCertificate.totalRG_pos`.  The 2-adic ℝ extension via Hahn
  series / transcendence basis remains the major Tier 2 gap.
- [ ] Chapter24: extend cotangent symmetries to the full Herglotz functional
  equation / partial-fraction argument.  The current file now proves the
  cotangent symmetries, abstracts the `HerglotzClass` structure with
  `eval_half` and `cancel` lemmas, proves the duplication formula for
  periodic functions, and defines the finite rational partial-sum function.

  **Tier 2 progress (2026-05-23):** The `π·cot(π·)` side is now complete
  as a HerglotzClass + duplication + continuity package:
  `cot_pi_div_two` (= 0), `pi_cot_pi_half_eq_zero` (eval-half anchor),
  `pi_cot_pi_periodic`, `pi_cot_pi_odd`, `pi_cot_pi_HerglotzClass`
  (HerglotzClass instance via periodic + odd), `cot_int_mul_pi` (degenerate
  vanishing), `cot_add_cot_add_pi_div_two` (cot α + cot(α + π/2) = 2·cot 2α,
  proved for ALL α via Lean's 0/0 = 0 convention), `pi_cot_pi_duplication`
  (the Herglotz duplication identity), `cot_continuousAt` /
  `pi_cot_pi_continuousAt` (continuity at non-integers), `cot_pi_div_four = 1`,
  `cot_pi_mul_half_int` (vanishing on half-integer multiples).  The
  remaining gap: build the matching partial-fraction series
  `1/x + Σ 2x/(x²-n²)` as a HerglotzClass member with the same duplication,
  then apply `chapter24` (or a weaker-continuity variant) to conclude
  `π·cot(πx) = 1/x + Σ 2x/(x²-n²)`.  Note `chapter24` currently requires
  `Continuous f` globally; cot is discontinuous at integers, so the chapter
  statement itself may need weakening to `ContinuousOn f (ℝ \ ℤ)`.
- [ ] Chapter25: extend the finite polygonal linearity step to the actual
  Buffon needle probability statement.  The current file now proves the
  single-segment crossing value is in `[0, 1]`, states Buffon's needle
  formula `P = 2ℓ/(πd)`, and proves the noodle generalization for curves.

  **Tier 2 progress (2026-05-23):** Algebraic infrastructure:
  `segmentExpectedCrossings_zero` (= 0 at length 0), `_mono` (monotone
  in length), `_add` (additivity), `_const_mul` (linearity).
  `curveExpectedCrossings_empty/_nonneg/_singleton/_eq_segment_of_total_length`.
  `BuffonProbabilitySpace.canonical` constructor (with caveat: structurally
  trivial — does NOT carry measure-theoretic content; the real Tier 2 goal
  is to derive `expected_eq` from `MeasureTheory.ProbabilityMeasure` on
  `[0, d/2] × [0, π/2]`).
- [ ] Chapter29: connect riffle labels to the Gilbert-Shannon-Reeds shuffle
  distribution.  The current file counts label assignments, proves the
  label piles form a disjoint cover of the deck, defines the stable riffle
  order with irreflexivity, transitivity, and trichotomy, and states the
  pile-size counting interface.

  **Tier 2 progress (2026-05-23):** Pile cardinality bounds:
  `pileOfLabel_card_le`, `pileSizeVector_le`, `pileSizeVector_eq_filter_card`
  (factored out the simp-friendly form).  Pile membership characterizations:
  `mem_pileOfLabel_self`, `pileOfLabel_eq_of_mem`, `pileOfLabel_eq_empty_iff`,
  `pileOfLabel_nonempty_iff`.  Order characterizations:
  `riffleOrder_of_same_label`, `riffleOrder_of_label_lt`.  Canonical
  candidates for the GSR certificate's `permFromLabels` field:
  `riffleSort` via `Tuple.sort labels` (the sorting permutation by labels)
  + `labels_comp_riffleSort_monotone` showing it produces a nondecreasing
  composition.  `constantLabeling` + its pile sizes worked out
  (`pileSizeVector_constantLabeling_zero` = n at pile 0; = 0 elsewhere).
  The combinatorial `count_determined_by_piles` (multinomial count for the
  riffle distribution) remains the open piece for a full
  `GSRShuffleCertificate`.
- [ ] Chapter30: formalize a real Lindstrom-Gessel-Viennot determinant/path
  statement.  The current file exposes the determinant's signed-permutation
  expansion, the diagonal determinant case, abstract sign-reversing
  cancellation with good/bad split, a `BadInvolutionCertificate` package,
  the path-swap sign-change lemma (`path_swap_changes_sign`), and the
  LGV identity-case framework.  It still lacks the concrete path-family
  intersection involution construction.
- [x] Chapter31: construct the actual Prüfer encode/decode bijection.  The
  file now contains `pruferDecode`, `pruferEncode`, and the structural
  correspondence `deleteSmallestLeaf_pruferDecode_v2` linking removal of the
  smallest leaf in the decoded tree to the shifted-code decode on `n - 1`
  vertices.  Combined with `leftInverse_pruferDecode_aux`, this discharges
  `chapter31_tier2_of_correspondence` and gives the unconditional
  `chapter31 : Fintype.card (LabeledTree n) = n ^ (n - 2)`.  Tier 2 closed
  end-to-end (0 sorry, 0 axiom).  (2026-05-22)
- [x] Chapter34: Galvin's theorem (Dinitz conjecture) is unconditional —
  `chapter34 : ∃ color, DinitzSolution lists color` for any `lists` with
  card ≥ n.  Chain: `galvin_theorem` →
  `dinitzSolution_of_dinitzOrient` → `dinitzSolution_of_kernel_perfect_orientation`
  + `dinitzOrient_kernelPerfectOn` (the actual kernel-perfect orientation
  construction is in the file as `stableMatching_exists` →
  `isKernelIn_of_stableMatching`).  No sorry, no axiom.
  (Updated 2026-05-23; earlier audit entry was stale.)
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

  **Tier 2 progress (2026-05-23):** Structural lemmas:
  `kneserVertex_nonempty_of_le` (vertex set nonempty when k ≤ n),
  `kneserGraph_no_vertices_of_lt` (empty when n < k), `kneserVertex_card_zero`
  (= 1 for k = 0), `kneserVertex_card_eq_one_of_eq` (= 1 for k = n),
  `kneserGraph_exists_adj_of_two_mul_le` (edges exist when 2k ≤ n, via
  explicit disjoint k-subsets `{0..k-1}` and `{k..2k-1}`),
  `kneserGraph_no_adj_of_lt` (no edges when n < 2k),
  `kneserGraph_zero_no_adj` + `kneserGraph_zero_eq_bot` (KG(n,0) = ⊥),
  `kneserGraph_one_adj_of_ne` + `kneserGraph_one_eq_completeGraph`
  (KG(n,1) = K_n as a SimpleGraph equality).  The Borsuk-Ulam-based hard
  direction (no (n-2k+1)-coloring when n ≠ 2k) remains the major Tier 2
  gap — requires building Borsuk-Ulam in Mathlib first.
