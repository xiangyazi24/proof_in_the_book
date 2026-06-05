# Bounded crux: orbit-count under right-multiplication by a transposition

GOAL: prove these two lemmas in a NEW standalone file
`ProofsInTheBook/PermTranspositionCycleCount.lean`. Import `Mathlib` only.
STRICT: no sorry, no axiom, no admit, no native_decide. Verify with
`lake env lean ProofsInTheBook/PermTranspositionCycleCount.lean`.

Let `D` be a `Fintype` with `DecidableEq`. For `p : Equiv.Perm D` define the
number of cycles (orbits, fixed points counted as singleton orbits) as the
cardinality of the SameCycle quotient:

```
noncomputable def numCycles (p : Equiv.Perm D) : ℕ :=
  Fintype.card (Quotient p.SameCycle.setoid)
```

(Equiv.Perm.SameCycle.setoid exists in Mathlib:
`Mathlib/GroupTheory/Perm/Cycle/Basic.lean`.)

Prove:

```
theorem numCycles_mul_swap_dichotomy (p : Equiv.Perm D) {a b : D} (hab : a ≠ b) :
    numCycles (p * Equiv.swap a b) = numCycles p + 1 ∨
    numCycles (p * Equiv.swap a b) + 1 = numCycles p

theorem numCycles_mul_swap_of_not_sameCycle (p : Equiv.Perm D)
    {a b : D} (hab : a ≠ b) (hnsc : ¬ p.SameCycle a b) :
    numCycles (p * Equiv.swap a b) + 1 = numCycles p
```

MATH CONTENT (standard "transposition splits or merges a cycle"):
Multiplying a permutation by a transposition `swap a b` either splits one cycle
into two (if a,b are in the same p-cycle) — giving numCycles+1 — or merges two
cycles into one (if a,b in different p-cycles) — giving numCycles-1. The second
theorem is the merge case (different cycles -> count drops by exactly 1).

SUGGESTED ROUTE (you may choose another):
- numCycles p = (#fixed points) + (cycleType card) = (card D - p.cycleType.sum)
  + Multiset.card p.cycleType. Mathlib: `Equiv.Perm.card_fixedPoints`,
  `Equiv.Perm.sum_cycleType`, and cycleType is a multiset of cycle lengths >= 2.
  Actually numCycles = card D - p.support.card + Multiset.card p.cycleType
  (each nontrivial cycle contributes 1 orbit but len darts; fixed points each 1).
  Verify: card D = (#fixed) + support.card; orbits = #fixed + #nontrivial-cycles
  = (cardD - support.card) + cycleType.card. Reduce both theorems to tracking
  support.card and cycleType.card under multiplication by swap a b, using
  `Equiv.Perm.support_swap_mul_eq` and disjoint cycle decomposition.
- ALTERNATIVELY (often cleaner): build an explicit bijection between the
  SameCycle quotients. For the merge case, q := p * swap a b satisfies
  q.SameCycle x y  <->  p.SameCycle x y  OR  (p.SameCycle x a AND p.SameCycle y b)
  OR (p.SameCycle x b AND p.SameCycle y a). The two p-classes [a],[b] fuse into
  one q-class; all other classes unchanged. Then numCycles q = numCycles p - 1
  via a quotient bijection onto {p-classes}/([a]~[b]).

Whatever route: the deliverable is the two theorems, fully proved, file
type-checks clean. Put findings in HANDOFF/outbox/crux-transp-reply.md when done:
status + which route + any Mathlib lemma names that were load-bearing.
