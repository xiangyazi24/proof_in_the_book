status: done

file: `ProofsInTheBook/PermTranspositionCycleCount.lean`

verification:
- `lake env lean ProofsInTheBook/PermTranspositionCycleCount.lean`
- no `sorry`, `axiom`, `admit`, or `native_decide`

route:
- Defined `numCycles` as the cardinality of `Quotient (Equiv.Perm.SameCycle.setoid p)`.
- Built an explicit quotient count bridge:
  `numCycles p = Fintype.card (Function.fixedPoints p) + Multiset.card p.cycleType`.
- Proved the merge case by quotienting `p`-orbits: when `¬ p.SameCycle a b`, the map from
  `p`-orbit quotient with `[b]` removed to the `(p * swap a b)`-orbit quotient is bijective.
- Proved the dichotomy using:
  merge case for the different-cycle branch;
  a quotient surjection for the same-cycle branch;
  parity/sign to rule out unchanged orbit count.

load-bearing Mathlib lemmas/APIs:
- `Equiv.Perm.SameCycle.setoid`
- `Equiv.Perm.SameCycle.exists_nat_pow_eq`
- `Equiv.Perm.cycleOf`
- `Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff`
- `Equiv.Perm.mem_support_cycleOf_iff`
- `Equiv.Perm.cycle_is_cycleOf`
- `Equiv.Perm.card_fixedPoints`
- `Equiv.Perm.sum_cycleType`
- `Equiv.Perm.sign_of_cycleType`
- `Equiv.Perm.sign_swap`
- `Equiv.Perm.sign_mul`
- `Fintype.card_congr`
- `Fintype.card_le_of_surjective`
- `Fintype.card_subtype_compl`
