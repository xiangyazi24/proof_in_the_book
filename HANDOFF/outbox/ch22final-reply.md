2026-06-04 Chapter22 final attempt status

Implemented and verified the algebraic factorization layer in
`ProofsInTheBook/Chapter22Gurvits.lean`.

Added:

- `coeff_zero_prod_one_add_mul_X`
- `coeff_one_prod_one_add_mul_X`
- `coeff_one_C_mul_prod_one_add_mul_X`
- `root_neg_of_nonnegative_coefficients_of_coeff_zero_pos`
- `roots_enum_toList`, `roots_enum_toList_mem`
- `rootsAsFin`, `rootsAsFin_mem`, `rootsAsFin_enum`
- `factoredSectionData_natDegree_of_realRooted_nonnegative`
- `positiveFactoredSections_of_realRooted_sections`

The new main local constructor is:

```lean
noncomputable def factoredSectionData_natDegree_of_realRooted_nonnegative {q : Polynomial ℝ}
    (hcoeff : ∀ n : ℕ, 0 ≤ q.coeff n) (h0 : 0 < q.coeff 0)
    (hrooted : ProofsInTheBook.Chapter22Stable.RealRooted q)
    (hdeg_pos : 0 < q.natDegree) :
    FactoredSectionData q.natDegree q
```

It carries out the C/D/E part of the recipe: a real-rooted univariate section
with nonnegative coefficients and positive constant term has all roots strictly
negative, hence factors as `q(0) * ∏ (1 + λᵢ t)` with `λᵢ > 0`, and the
linear coefficient is `q(0) * ∑ λᵢ`.

The bridge to the existing step lemma is:

```lean
noncomputable def positiveFactoredSections_of_realRooted_sections {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hrooted :
      ∀ x : Fin m → ℝ, PositiveVector x →
        ProofsInTheBook.Chapter22Stable.RealRooted (sectionPolynomial p x))
    (hconst :
      ∀ x : Fin m → ℝ, PositiveVector x →
        0 < (sectionPolynomial p x).coeff 0)
    (hdegree :
      ∀ x : Fin m → ℝ, PositiveVector x →
        (sectionPolynomial p x).natDegree = m + 1) :
    PositiveFactoredSections p
```

Verified:

```bash
/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter22Gurvits.lean
/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter22Stable.lean
```

No `sorry`, `admit`, or `axiom` in `Chapter22Gurvits.lean` or
`Chapter22Stable.lean`.

Not closed:

The epsilon-section theorem is still missing at the Lean interface needed by
`positiveFactoredSections_of_realRooted_sections`:

```lean
∀ {m : ℕ} {p : MvPolynomial (Fin (m + 1)) ℝ},
  NonnegativeCoefficients p →
  ProofsInTheBook.Chapter22Stable.RealStable p →
  (∀ x : Fin m → ℝ, PositiveVector x →
    0 < (sectionPolynomial p x).coeff 0) →
  (∀ x : Fin m → ℝ, PositiveVector x →
    (sectionPolynomial p x).natDegree = m + 1) →
  ∀ x : Fin m → ℝ, PositiveVector x →
    ProofsInTheBook.Chapter22Stable.RealRooted (sectionPolynomial p x)
```

The reduction chain also still needs the multivariate derivative stability
step:

```lean
∀ {m : ℕ} {p : MvPolynomial (Fin (m + 1)) ℝ},
  ProofsInTheBook.Chapter22Stable.RealStable p →
  ProofsInTheBook.Chapter22Stable.RealStable (firstReduction p)
```

This is the Lieb-Sokal/partial-derivative preservation gap already described
in `Chapter22Stable.lean`; without it, the row-linear base stability cannot be
propagated down the `firstReduction` chain, so `GurvitsCapacityReductionData`
and the unconditional `chapter22` endpoint remain open.
