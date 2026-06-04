I need to upgrade the `chapter13` theorem in `ProofsInTheBook/Chapter13.lean` to a Tier 1 conditional form.

The current file defines:
- `EdgeSign` and `StrictEdgeSign`
- `StrictSignChangesAroundTriangle` and `strictSignChangesAroundTriangle_even`
- `arm_lemma_abstract` placeholder
- `euler_sign_change_parity` placeholder
- `cauchy_rigidity_outline` (which takes `signChangeContradiction : False`)
- A dummy `chapter13` theorem that proves `SignChangesAroundTriangle a b c ≤ 3`.

The user requested: "主定理取 'arm lemma 成立' + 'Euler sign-change parity 满足' 作 hypothesis, 用已证 sign-count 性质推出 chapter 主结论 (Cauchy rigidity)."

Could you provide the exact Lean 4 code for the Tier 1 `chapter13` theorem? Should I define a structured `CauchyRigidityHypotheses` (similar to Ch16 and Ch30) that wraps the arm lemma and Euler sign-change count contradictions, and then proves `∀ e, edgeSigns e = zero`? Please provide the exact code so I can replace the placeholder.
