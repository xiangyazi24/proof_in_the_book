2026-06-04 Chapter22 wire status

Implemented and verified the algebraic endgame wiring in
`ProofsInTheBook/Chapter22Gurvits.lean`:

- Added the degree-one `firstReduction` operator via `MvPolynomial.finSuccEquiv`.
- Proved coefficient bookkeeping:
  `coeff_firstReduction`, preservation of nonnegative coefficients, and
  `iteratedFirstReductionCoefficient_eq_squarefreeCoefficient`.
- Added `CapLB` as the lower-bound form of capacity, plus the row-linear base
  `rowLinear_capLB_one_of_capacity`.
- Proved row-linear base hypotheses from the existing capacity assumption:
  nonnegative coefficients, positive row sums, and
  `rowLinearMvPolynomial_realStable_of_capacity`.
- Added section-polynomial interfaces:
  real section evaluation, complex section evaluation, no-UHP roots when the
  other variables are already in the UHP, and nonnegative/positive section
  coefficient lemmas from nonnegative coefficients.
- Added the factored-section per-step theorem:
  `firstReduction_capLB_of_factoredSections`, using the existing
  `univariate_gurvits_factored`.
- Added the final algebraic assembly from per-step capacity data:
  `GurvitsCapacityReductionData`,
  `iteratedCapacityCertificate_of_capacityReductionData`, and
  `chapter22_from_capacityReductionData`.

Verified:

```bash
/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter22Gurvits.lean
/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter22Stable.lean
```

No `sorry`, `admit`, or `axiom` in `Chapter22Gurvits.lean` or
`Chapter22Stable.lean`.

Remaining exact frontier:

```lean
∀ m : ℕ, 3 ≤ m →
  ∀ A : Matrix (Fin m) (Fin m) ℝ,
    (∀ i j, 0 ≤ A i j) →
    RowLinearCapacityAtLeastOne A →
    GurvitsCapacityReductionData m A
```

Equivalently, construct the reduction sequence and prove that every reduced
polynomial has `PositiveFactoredSections`.  The first missing local theorem is
the analytic-free specialization/preservation statement turning
`RealStable p` plus nonnegative coefficients into
`FactoredSectionData (m+1) (sectionPolynomial p x)` for every positive `x`,
and showing the same property survives `firstReduction`.
