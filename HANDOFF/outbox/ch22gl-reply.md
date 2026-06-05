2026-06-04 Chapter22 Gauss-Lucas / line-trick status

Implemented and verified in `ProofsInTheBook/Chapter22Stable.lean`:

- `derivative_roots_im_nonpos`
  ```lean
  lemma derivative_roots_im_nonpos (p : Polynomial ℂ)
      (hp : ∀ z ∈ p.roots, z.im ≤ 0) :
      ∀ z ∈ (Polynomial.derivative p).roots, z.im ≤ 0
  ```
  This uses Mathlib's `Splits.eval_derivative_div_eval_of_ne_zero` log-derivative identity and the elementary
  finite-sum imaginary-part argument.
- `eval_ne_zero_of_roots_im_nonpos`
- `roots_im_nonpos_of_tendsto_eventually`

Implemented and verified in `ProofsInTheBook/Chapter22Gurvits.lean`:

- `rowLinearMvPolynomial_isHomogeneous`
- `firstReduction_isHomogeneous`
- `complexLineSection`
- `distinguishedDerivativeAt`
- `complexLineSection_eval`
- `distinguishedDerivativeAt_eval`
- `distinguishedDerivativeLine_eval_ne_zero_of_section_derivative_ne_zero`

The last lemma is the local Gauss-Lucas part of the line trick: if the relevant univariate section derivative
is nonzero, then the perturbed distinguished derivative line section has no UHP zero.

Verified:

```bash
PATH=/data/home/xhuan5/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter22Stable.lean
PATH=/data/home/xhuan5/.elan/bin:$PATH lake env lean -o .lake/build/lib/lean/ProofsInTheBook/Chapter22Stable.olean -i .lake/build/lib/lean/ProofsInTheBook/Chapter22Stable.ilean ProofsInTheBook/Chapter22Stable.lean
PATH=/data/home/xhuan5/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter22Gurvits.lean
grep -nE '\b(sorry|admit|axiom)\b' ProofsInTheBook/Chapter22Stable.lean ProofsInTheBook/Chapter22Gurvits.lean
```

The Lean checks exit 0.  The grep finds no `sorry`, `admit`, or `axiom`.

Not closed:

1. The current `PositiveFactoredSections` interface is too strong for the Gurvits chain:
   it requires `(sectionPolynomial p x).natDegree = m + 1`.  This is false for general
   doubly stochastic matrices with zeros.  Example: a permutation matrix gives a row-linear product
   in which each variable has degree `1`, not `n`; the section degree in a distinguished variable can
   be strictly smaller than the number of variables.  The next required algebraic fix is a padded
   constructor
   ```lean
   FactoredSectionData d q → d ≤ k → FactoredSectionData k q
   ```
   with zero `λ` entries, and then a replacement for
   `positiveFactoredSections_of_realRooted_sections` requiring only
   `(sectionPolynomial p x).natDegree ≤ m + 1` and positive degree when applying the step.

2. The full Lemma B still needs a nonzero/degree-control statement for the perturbed derivative
   sections.  The exact missing local goal after the lemma added here is:
   ```lean
   ∀ {m : ℕ} {p : MvPolynomial (Fin (m + 1)) ℝ},
     NonnegativeCoefficients p →
     p.IsHomogeneous (m + 1) →
     ProofsInTheBook.Chapter22Stable.RealStable p →
     firstReduction p ≠ 0 →
     ∀ (a b : Fin m → ℝ), (∀ j, 0 < b j) →
       ∀ᶠ n in Filter.atTop,
         ∀ t : ℂ, 0 < t.im →
           Polynomial.derivative
             (complexSectionPolynomial p
               (fun j => (a j : ℂ) + (b j : ℂ) * t)) ≠ 0
   ```
   or an equivalent degree-control theorem strong enough to show that
   `complexLineSection (distinguishedDerivativeAt p (I * ε_n)) a b`
   is nonzero, has the same degree as its limit for all large `n`, and has no UHP roots.

Without these two repairs, `GurvitsCapacityReductionData` cannot be constructed honestly from the current
interfaces, so the unconditional `chapter22` endpoint is still not closed.
