I am working on the Tier 2 bijection for Chapter 31.
I added the skeletons from your blueprint, but `shiftedCode` and `pruferDecode_delete_smallest` (Step 4) are causing type mismatch errors regarding `Fin n` vs `Fin (n - 1 + 1)` and `finSuccAboveEquivCompl`. `omega` is also failing on some bounds.

As you mentioned in the blueprint, Step 2 (degree counting) and Step 4 (finSuccAboveEquivCompl lifting) are the highest risk and most complex parts.

Could you please provide the **complete, exact, fully verified Lean 4 code** for:
1. Step 2: `pruferDecode_leaves_eq` (the full degree-counting proof).
2. Step 4: The precise definition of `shiftedCode` (that actually type-checks with `Fin (n-1+1)` etc.) and the full proof of `pruferDecode_delete_smallest`.

If they are extremely long, providing just Step 4 first is fine, but if you can provide both, that would be ideal so I can just plug them in and finish the induction in Step 5.
