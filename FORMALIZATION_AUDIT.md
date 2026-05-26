# Formalization Audit

## 2026-05-26 RE-VERIFICATION (the 2026-05-24 classification below is STALE)

Re-checked canonical `chapterNN` endpoints directly (0 sorry / 0 axiom whole
repo confirmed).  Several chapters the 05-24 audit listed as open/Category-B
are now **fully closed and unconditional** — do not spend effort re-opening
them:

- **Ch03** `chapter03` — perfect-power, unconditional (l=2 and l≥3 both internal).
- **Ch10** `chapter10` / `euclidean_sylvester_gallai` — unconditional.
- **Ch11** `chapter11` (line ~10972) — unconditional projective-direction bound;
  the CyclicEndGap blocker was closed 05-25 via the shifted sweep.
- **Ch16** `chapter16 : ∃ d, ¬BorsukConjecture d := ⟨1325, …⟩` — the Kahn-Kalai
  certificate is **constructed** (not assumed); unconditional.
- **Ch24** `cot_pi_partial_fraction_identity` — unconditional (Mathlib transfer).
- **Ch29** `chapter29` — GSR distribution, unconditional.
- **Ch37** `chapter37` — Turán incl. extremal uniqueness/iso, unconditional.

**Genuinely still open** (canonical endpoint takes an escape hypothesis or is a
fragment), each blocked on large missing Mathlib infra — precise walls:

- **Ch13** Cauchy: `chapter13 (cert : CauchyRigidityCertificate …)`. Wall: 3-D
  convex-polyhedron geometry + analytic arm lemma.
- **Ch20** Monsky: `chapter20 (cert : MonskyCertificate n)`. 2-adic-on-ℝ +
  coloring + Sperner parity + real-square-boundary Sperner conclusion ALL built.
  Remaining wall is NARROW & finite/affine (no measure/topology): a "square
  equidissection" object proving interior edges have even Sym2-multiplicity /
  boundary odd, plus equal-area ⟹ oriented doubleArea = ±2/n contradiction with
  the rainbow-triangle valuation lemma. **Best non-live push target.**
- **Ch22** Van der Waerden permanent: only `chapter22_of_le_two` (n≤2). General
  case = Gurvits capacity / real-stable polys. **LIVE (codex-ssem thread).**
- **Ch25** Buffon: `buffonNeedleCrossingProbability` defined combinatorially, no
  measure. Wall: integral-geometry probability measure.
- **Ch35** five-color: `chapter35 (hG : FiveColorReducible G)`. Wall: planar
  graph type + Euler ⟹ degree-≤5 vertex (Mathlib lacks planarity).
- **Ch36** art gallery: `chapter36_artgallery_combinatorial (TriangulatedPolygon)`.
  Wall: simple-polygon triangulation existence (planar geometry).
- **Ch39** Kneser: general case takes `htucker`. **LIVE (codex Tucker thread,
  TuckerLemmaCore.lean).** `chapter39_one` (k=1) is unconditional.
- **Ch09** Dehn: `chapter09` states `…DehnInvariantQ ≠ …` (algebraic core, incl.
  arccos(1/3)/π irrational) but is disconnected from geometric scissors-
  congruence. Wall: 3-D dihedral-angle geometry + Dehn additivity over real
  dissections.

Verdict: ~31 chapters fully closed; ~8 open, all on genuine large infra.
2 of the 8 (Ch22, Ch39) are live codex threads — stay off them to avoid collision.

---

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

## Audit Classification (2026-05-24, playbook point 11)

Whole repo: **0 sorry / 0 axiom / 0 admit / 0 `True := trivial`** (the two
scan hits in Ch24/Ch32 are comment text).  All 40 chapters have a main
theorem.  The honest split on audit points 3/7/8 (no certificate-escape;
end-to-end with raw inputs) is:

**A. Unconditional end-to-end (audit-pass):** ~27 chapters.  All basic
chapters plus Ch04, Ch19, Ch31, Ch34, Ch35, and **Ch24** (cotangent
partial-fraction, closed 2026-05-24 via Mathlib `cot_series_rep'`).
**Ch03 general Sylvester** (`sylvester_general`) is unconditional; only the
Erdős perfect-power corollary remains conditional.

**Axiom audit (point 10) verified 2026-05-24** via `#print axioms` on the
main theorem of each category-A chapter — every one depends ONLY on
`[propext, Classical.choice, Quot.sound]` (no custom axiom, no sorry):
Ch01 `chapter01_euclid`, Ch02 `chapter02_chebyshev`,
Ch05 `chapter05_quadratic_reciprocity`, Ch06 `chapter06_wedderburn`,
Ch07 `chapter07_sqrt_prime`, Ch12 `chapter12_platonic_solids`,
Ch14, Ch15, Ch17 `chapter17_cantor`, Ch18 `chapter18_sq_abs_le`,
Ch19 `chapter19`, Ch21, Ch22, Ch23 `chapter23_sperner_via_lym`,
Ch24 `cot_pi_partial_fraction_identity`, Ch26 `chapter26_erdos_szekeres`,
Ch27 `chapter27_debruijn`, Ch28 `chapter28_sperner`,
Ch31 `chapter31`, Ch32 `chapter32_vandermonde`,
Ch33 `hall_system_of_distinct_representatives`, Ch34 `chapter34`,
Ch35 `chapter35`, Ch37 `chapter37_turan`, Ch38, Ch40 `chapter40_friendship_theorem`.

**B. Conditional — needs MAJOR Mathlib infrastructure (multi-week; not
closable by lemma-adding):**
- Ch16 Borsuk: `KahnKalaiCertificate.no_partition` — needs Frankl–Wilson
  combinatorics (counterexample dimension d ≥ 298).
- Ch20 Monsky: `MonskyCertificate` — needs 2-adic valuation extension to ℝ
  (Hahn series / transcendence basis) + Sperner's lemma for triangulations.
- Ch39 Kneser: `KneserChromaticCertificate.hhard` — needs Borsuk–Ulam
  (absent from Mathlib).
- Ch36 art gallery: takes a `TriangulatedPolygon` input — needs
  simple-polygon triangulation existence (planar geometry).
- Ch25 Buffon: `BuffonProbabilitySpace` — needs integral-geometry
  probability measure on needle placements.
- Ch09 Dehn: abstract monoid elements + hypotheses — needs 3-D dihedral-angle
  geometry + Dehn additivity over real dissections.
- Ch13 Cauchy: `CauchyRigidityCertificate.contradiction : False` — needs 3-D
  convex-polyhedron geometry + the analytic arm lemma.
- Ch11 Ungar: `chapter11` proves the easy direction (injective witness into
  slopes); the `n-1 ≤ |directions|` bound needs the rotating-calipers sweep
  certificate (≈8000 LOC of scaffolding present; sweep construction remains).

**Whole-repo axiom audit (point 10), all 40 chapters verified 2026-05-24:**
`#print axioms chapterNN` on every main theorem reports either
`[propext, Classical.choice, Quot.sound]` or "does not depend on any axioms"
(Ch09, Ch13 — pure projections from their hypotheses).  **No chapter has a
custom axiom or sorry dependency.**  The category-B/C chapters are clean
*modulo their explicit certificate hypotheses* (honestly disclosed below),
which is the maximal audit standard achievable for them without the
multi-week infrastructure builds listed in B.

**C. Conditional — self-contained combinatorics (no external infra; closable
with sustained effort, candidates for genuine closure):**
- Ch03 Erdős perfect-power: `h_l2_contra` (l=2) + `h_ge3` (l≥3).  Injectivity
  (`lPowerFreePart_injective_l2`) and the divisibility step
  (`prod_lPowerFreeParts_dvd_factorial_l2`, now wired in) are done.
- Ch29 GSR: `count_determined_by_piles` (multinomial count of riffle labels).
- Ch30 LGV: `BadInvolutionCertificate` (tail-swap involution on intersecting
  path families).
- [x] **Ch10 Sylvester–Gallai: FULLY CLOSED (2026-05-24).**
  `euclidean_sylvester_gallai (S : Finset EPoint) (T : OffLineTriple S) :`
  `∃ a b, a∈S ∧ b∈S ∧ a≠b ∧ (S.filter (·∈ line[a,b])).card = 2` — a finite
  planar point set with an off-line incidence (= not all collinear) has an
  ordinary line.  Unconditional; no certificate hypothesis.  Kelly's
  minimum-distance proof assembled from steps 1–3d below.  Moves Ch10 from
  category C to fully closed; first from-scratch Euclidean Sylvester–Gallai
  in the repo.  (The earlier abstract `chapter10` for `card = 2 → ordinary`
  also remains.)
  **Kelly's metric proof — all steps done (2026-05-24):**
  - Step 1 (commit fac587d): concrete `EPoint = EuclideanSpace ℝ (Fin 2)`
    foundation — `perpDist` (infDist to `affineSpan ℝ {a,b}`),
    `perpDist_nonneg/_eq_zero_of_mem/_le_dist_*`, `mem_of_perpDist_eq_zero`
    (line closed in finite dim), `perpDist_eq_zero_iff`, `perpDist_pos`.
  - Step 2 (commit 9d0d4ae): `exists_min_perpDist_offLine` — a minimum
    perpendicular-distance off-line incidence exists.  The earlier `whnf`
    blocker (Finset.filter over the undecidable `∉ affineSpan`) was resolved
    by giving `OffLineTriple S` a `Finite` instance (injects into `S×ˢS×ˢS`)
    and minimizing over `Finset.univ` — everything abstract, no concrete
    Finset reduction.
  - Step 3a (commit 076ce77): foot of perpendicular
    `foot P a b := orthogonalProjection (affineSpan ℝ {a,b}) P`, `foot_mem`,
    `perpDist_eq_dist_foot`.  `Nonempty (affineSpan ℝ {a,b})` instance.
  - Step 3b (commit c0c1e48): `dist_sq_eq_foot` (Pythagoras `PR² = RF² + PF²`)
    and `dist_lt_dist_of_wbtw_foot`: if `R` on line, `Q` between foot `F` and
    `R`, `P` off line, then `dist Q R < dist P R`.  (PF>0; QR≤FR via
    `Wbtw.dist_add_dist`; QR² ≤ FR² < FR²+PF² = PR²; `lt_of_pow_lt_pow_left₀`.)
  - Step 3c (commits: projection-length, Gram/apex, area identity): DONE.
    `inner_vsub_pair_sq` (⟪P-ᵥY,Z-ᵥY⟫² = dist Y(foot)²·dist Y Z², via
    orthogonal decomposition + 1-D vectorSpan); `perpDist_sq_mul_dist_sq`
    (Gram/Lagrange: perpDist²·base² = ‖edge‖²·base² − ⟪edge,base⟫²);
    `gram_apex_symm` (apex-invariance, inner-product `ring`);
    `perpDist_mul_dist_eq` (the area identity
    `perpDist Q P R · dist P R = perpDist P Q R · dist Q R`, square roots via
    `Real.sqrt_sq`).  No law-of-sines / determinant needed after all — the
    orthogonal-projection route worked.
  - Step 3d core (commit: strict decrease): DONE.
    `perpDist_lt_perpDist_of_wbtw`: if `P` off line `QR`, `Q` between
    `foot P Q R` and `R`, then `perpDist Q P R < perpDist P Q R`.  This is the
    inequality that contradicts minimality.
  - Step 3d (commits: pigeonhole, plumbing, main theorem): DONE.
    `exists_smul_vadd_foot` + `exists_wbtw_foot_of_three_mem` (sign
    pigeonhole → same-side `Wbtw`); `collinear_coe_affineSpan_pair`,
    `affineSpan_pair_eq_of_mem`, `perpDist_congr`, `foot_congr` (line
    plumbing; `foot_congr` via `orthogonalProjection_congr`); then
    `euclidean_sylvester_gallai` assembles the minimality contradiction.

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

- [~] Chapter03: **general Sylvester is UNCONDITIONAL.**
  `sylvester_general (n k) (hn : 2*k ≤ n) (hk : 0 < k) :`
  `∃ p, k < p ∧ p.Prime ∧ p ∣ n.choose k` is proved outright (via
  `exists_large_prime_factor_choose_of_two_mul_le`), as is the central
  case `chapter03_sylvester`.  The remaining gap is only the Erdős
  "almost never a perfect power" theorem (`chapter03_erdos`), still
  conditional on the l=2 contradiction (`h_l2_contra`) and l≥3 case
  (`h_ge3`).  **2026-05-24:** the `hprod_l2` escape parameter was REMOVED
  from both `chapter03_erdos` and `chapter03` — the divisibility
  `∏ lPowerFreePart 2 (n-j) ∣ k!` is now derived internally from the
  perfect-power equation via the already-proven
  `prod_lPowerFreeParts_dvd_factorial_l2`.  Escape surface reduced from
  3 hypotheses to 2.

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
- [x] Chapter24: the cotangent partial-fraction expansion is now
  UNCONDITIONAL.  `cot_partial_fraction_limit_holds : CotPartialFractionLimit`
  is proved (2026-05-24) by transferring Mathlib's complex Mittag-Leffler
  expansion `Complex.cot_series_rep'` to `ℝ` via `Complex.hasSum_ofReal`:
  `(↑x:ℂ) ∈ ℂ_ℤ` from `x ∉ ℤ`, `HasSum cotTerm (π·cot(πx)-1/x)` from
  `summable_cotTerm`, descend to ℝ (each `cotTerm ↑x n = ↑(real term)`,
  value via `Complex.ofReal_cot`), then `HasSum.tendsto_sum_nat` + prepend
  the `1/x` head gives the `rationalPartialSum` limit.
  `cot_pi_partial_fraction_identity` no longer takes the
  `CotPartialFractionLimit` hypothesis — `π·cot(πx) = 1/x + Σ(1/(x+n)+1/(x-n))`
  is an unconditional end-to-end theorem.  The `HerglotzClass`-based
  `chapter24` uniqueness principle remains as a genuine abstract method
  (its hypotheses are the Herglotz-class conditions themselves, not an
  escape).
  Earlier Tier 2 progress (cotangent symmetries, HerglotzClass, duplication,
  continuity) retained below.

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
