# QUESTION: Structural induction for deleteSmallestLeaf_pruferDecode_v2

I have defined `shiftedCode_v2` and it builds perfectly. I am now looking at the structural lemma `deleteSmallestLeaf_pruferDecode_v2`. 

As warned in the task description, showing that the edges of `shiftedCode_v2 hm s` directly correspond to the edges of `s` (minus `s(nextLeaf0, s 0)`) under the `finSuccAboveEquivCompl nL` bijection requires a complex induction on the steps of `pruferDecodeAux`. 

Before I sink 300+ LOC into a fragile induction on `pruferDecodeAux`, I am filing this Oracle Question to ask:
1. Do we already have a clean induction invariant lemma for this step in the Oracle's files?
2. Specifically, what is the exact statement of the `pruferDecodeAux` equivalence lemma that connects `(pruferDecodeAux (m+1) (shiftedCode_v2 hm s) k).val` to `(pruferDecodeAux (m+2) s (k+1)).val`? 
3. Are there any missing `finSuccAboveEquivCompl` lemmas I should be aware of?

Thank you!
