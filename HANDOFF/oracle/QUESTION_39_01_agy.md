I need to upgrade the `chapter39` theorem in `ProofsInTheBook/Chapter39.lean` to a Tier 1 conditional form.

The current file has:
- `kneser_chromatic_upper_bound` proving it is `(n - 2*k + 2)`-colorable.
- `kneser_chromatic_lower_bound` proving it is NOT `(n - 2*k + 1)`-colorable (with `hhard` argument for the `n ≠ 2*k` case).
- A dummy `chapter39` counting vertices.

The user requested: "主定理 chapter39 取 'KneserChromaticCertificate' 作 hypothesis, witnesses chromatic(KG(n,k)) ≥ n - 2k + 2 (hard direction), 用现有 upper bound + base case 推 χ(KG(n,k)) = n - 2k + 2 (Lovász)."

Could you provide the exact Lean 4 code for the Tier 1 `chapter39` theorem and the `KneserChromaticCertificate` structure? Should the certificate just bundle the `hhard` lower bound? Please provide the exact code so I can replace the placeholder.
