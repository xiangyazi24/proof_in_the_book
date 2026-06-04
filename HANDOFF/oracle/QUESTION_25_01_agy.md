I need to upgrade the `chapter25` theorem in `ProofsInTheBook/Chapter25.lean` to a Tier 1 conditional form.

The current file defines:
- `segmentExpectedCrossings d length = 2 * length / (Real.pi * d)`
- `curveExpectedCrossings` and properties
- A dummy `chapter25` theorem wrapping `curveExpectedCrossings_eq_total_length`

The user requested: "主定理取 'BuffonProbabilitySpace' (取 needle 在板上随机分布) 作 hypothesis, 用文件已证的 polygonal/segment crossing 值推出 chapter 主结论 (probability = 2ℓ/(πd))."

Could you provide the exact Lean 4 code for the Tier 1 `chapter25` theorem? I assume it involves defining a `structure BuffonProbabilitySpace` (abstracting over the measure space, probability measure, and expected value mapping to `segmentExpectedCrossings`) and then stating `chapter25` that takes this certificate and returns the probability equality. Please provide the exact code so I can replace the placeholder.
