2026-06-04 Chapter22 r7 status

Implemented and verified the homogeneous line-section degree-control layer in
`ProofsInTheBook/Chapter22Gurvits.lean`.

Added:

- `coeff_prod_of_natDegree_le_sum`
- `coeff_linear_pow_top`
- `coeff_complexLineSection_monomial_degree`
- `complexLineSection_coeff_of_isHomogeneous`
- `complexLineSection_monomial_natDegree_le_degree`
- `complexLineSection_natDegree_le_of_isHomogeneous`
- `complexLineSection_natDegree_eq_of_isHomogeneous_eval_ne_zero`
- `complexLineSection_firstReduction_natDegree`

The main closed local result is:

```lean
lemma complexLineSection_firstReduction_natDegree {m : ℕ}
    {p : MvPolynomial (Fin (m + 1)) ℝ}
    (hpcoeff : NonnegativeCoefficients p)
    (hhom : p.IsHomogeneous (m + 1))
    (hp_ne : firstReduction p ≠ 0)
    (a b : Fin m → ℝ) (hb : ∀ j, 0 < b j) :
    (complexLineSection ((firstReduction p).map (algebraMap ℝ ℂ))
      (fun j => (a j : ℂ)) (fun j => (b j : ℂ))).natDegree = m
```

This proves the recipe's top-coefficient/positivity part for the limit line
section: the `t^m` coefficient is `eval b (firstReduction p)`, and it is
nonzero by `eval_pos_of_nonnegativeCoefficients`.

Verified:

```bash
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter22Gurvits.lean
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter22Stable.lean
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter22.lean
grep -RIn "\bsorry\b\|\badmit\b\|\baxiom\b" \
  ProofsInTheBook/Chapter22Gurvits.lean \
  ProofsInTheBook/Chapter22Stable.lean \
  ProofsInTheBook/Chapter22.lean
```

All three Lean checks exit 0. The grep finds no `sorry`, `admit`, or `axiom`.

Not closed:

The perturbed `distinguishedDerivativeAt` degree-control still needs the bridge
from the current `finSuccEquiv`/univariate-derivative definition to the cleaner
`pderiv 0` specialization. The exact missing lemma is:

```lean
MvPolynomial.eval z (distinguishedDerivativeAt p c) =
  MvPolynomial.eval (Fin.cons c z)
    (MvPolynomial.pderiv 0 (p.map (algebraMap ℝ ℂ)))
```

I tested this by induction. The additive case reduces, but the monomial case
stops at the product-derivative split for the `0` variable inside
`finSuccEquiv_apply`. Once this bridge is proved, `pderiv` homogeneity should
give the perturbed line-section top coefficient from the full homogeneous
line-section lemma with base `(c,a)` and direction `(0,b)`.

The other remaining blocker is still the genuine derivative-stability/nonzero
step for the perturbed sections. Pointwise Gauss-Lucas gives no UHP roots for
the derivative only when the corresponding univariate derivative is nonzero;
the current files do not yet prove the multivariate Lieb-Sokal/Hurwitz
specialization needed to rule out the zero derivative section at UHP points.
