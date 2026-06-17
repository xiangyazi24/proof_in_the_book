# TASK Ch36-dichotomy: RayWindingDichotomy (the sharpened single Jordan residue)

Repo: /Users/huangx/repos/proof_in_the_book (branch zinan-overnight). Create ONLY the new file
ProofsInTheBook/ZinanCh36Dichotomy.lean. Do not edit anything else. No git commit.

CONTEXT: ZinanCh36Theta.lean (committed, clean-3, 27 thms) reduced the chapter's Jordan kernel
EXACTLY to one residue. READ FIRST: ZinanCh36Theta.lean in full (esp. §3 windCross_translate
suffix-sum law, §6 alt_of_cut_dichotomy, §7 rayCrossingAlternation_of_ray_dichotomy, §9
lineCrossing_eSign_sum_zero, and the two §8 machine-refutations — the squeeze route and
non-generic base points are DEAD, do not retry them), HANDOFF/outbox/ch36-theta-reply.md,
PolygonWindingBound.lean (windCross, eSign, crossTau, RayCrossingAlternation defs).

GOAL: prove the dichotomy (define it as specced in the reply):
  RayWindingDichotomy P ρ x s := ∀ c ≥ 0, ¬OnBoundary P (x + c•ρ.r) →
    windCross P ρ (x + c•ρ.r) ∈ ({0, s} : Set ℤ)
for some s = ±1 (∃-form over s is fine), for off-boundary x with the vertex-genericity guard
(∀ k, side ρ.r x (P.q k) ≠ 0), under the polygon's existing genericity/simplicity hypotheses.
Then wire through the banked §7 bridge to conclude `RayCrossingAlternation P ρ x` at generic x —
that closes the chapter's geometric side.

SUGGESTED ATTACK (from the §9 budget; design freely beyond it): induct along the ray from the far
end (far point has windCross 0 — exists_far_point/rayCrossingAlternation_far machinery), windCross
jumps by exactly eSign = ±1 across each crossing (suffix-sum law); the content is SIGN-CONSISTENCY:
two nonzero values of opposite sign would force an excursion of the simple closed boundary that
re-crosses the ray with the wrong parity — use the polygon's simplicity (EdgeIntersectionCondition,
crossTau_injOn_crossingEdges) and the ups=downs global balance. Consider strong induction on the
number of crossings beyond c, or a minimal-counterexample argument on the sorted crossTau
enumeration (exists_sorted_enum is banked).

STRICT: no sorry/axiom/admit/native_decide. #print axioms every claimed theorem (⊆ {propext,
Classical.choice, Quot.sound}). This is the genuinely hard heart of Ch36 — grind it; legitimate
stops only: math wrong (explicit counterexample) or missing Mathlib API (exact lemma + goal state).
Bank every compiling sub-lemma (partial sign-consistency lemmas are valuable). Write
HANDOFF/outbox/ch36-dichotomy-reply.md: status, proven list + axioms, exact blockers.

VERIFY (your ONLY loop; Mac has no local lake):
scp -q ProofsInTheBook/ZinanCh36Dichotomy.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ && ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && timeout 1800 lake env lean ProofsInTheBook/ZinanCh36Dichotomy.lean 2>&1 | head -50'
