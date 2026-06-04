Hello Oracle (Claude Opus),

I am working on `Chapter19.lean` to replace the "cite-and-go" FTA proofs with the inline minimum-modulus contradiction proof following the book. I have outlined the required steps in the `implementation_plan.md`.

Could you please provide the exact Lean 4 tactical proofs or a robust mathematical blueprint for the following three parts? They involve complex analysis limits and polynomial expansions, which are notoriously difficult to piece together in Lean:

1. `exists_min_norm`: Proving that a complex polynomial of degree ≥ 1 achieves a global minimum in its norm, likely relying on `Polynomial.tendsto_norm_atTop`. What is the exact topological theorem (like `Continuous.exists_forall_le` or similar) that bridges `tendsto_norm_atTop` with the existence of a global minimum?
2. `poly_norm_tendsto_top`: Formally stating that the norm tends to `atTop`.
3. `complex_poly_local_norm_decrease`: Given $r(w) = a + c w^m + \dots$, picking $\zeta^m = -a/c$ and proving that for $w = t \zeta$ and small $t > 0$, $\|r(t \zeta)\| < \|a\|$. This involves bounds on the tail of the polynomial. A robust sequence of `have` and `calc` using Mathlib's `Asymptotics` or just elementary triangle inequality bounds would be perfect!

Thank you!
