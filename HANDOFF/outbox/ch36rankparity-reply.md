# Ch36 Rank-Parity — DONE (clean-3)

`ProofsInTheBook/ZinanCh36RankParity.lean` (702 lines) closes the master theorem
`alt_of_twoSide_noncrossing_cycle` via the rank-parity design.  No sorry / axiom / admit /
native_decide.  Final theorem statement matches design §12 exactly (raw inputs S, τ, σ, ν, L;
hypotheses hτinj, hνmem, hcycle, hpm, hflip, hposNI, hnegNI, hnd, hmem, hsort; conclusion
`Alt (L.map σ)`), consumed through the banked `ZinanCh36Comb.alt_map_of_chain`.

`lake env lean ProofsInTheBook/ZinanCh36RankParity.lean` → EXIT 0.
`#print axioms` for BOTH `alt_of_twoSide_noncrossing_cycle` and the master brick
`inside_card_even_of_chord` → `[propext, Classical.choice, Quot.sound]` (clean-3).

## Section map
- §4 `rank`, `Inside`, `mem_inside_iff`, `not_endpoint_of_mem_inside`.
- §5 `nu_surjOn_of_cycle` (preimage = ν^[m] b from `ν^[m+1] b = b`), `nu_bijOn_of_cycle`
  (Set.Finite.surjOn_iff_bijOn_of_mapsTo), `nu_injOn_of_cycle`, `nuPred`/`nuPred_mem`/`nu_nuPred`.
- §6/§7 unified into `mate_together_pos` / `mate_together_neg`: for a same-colour chord and a
  distinct same-colour element, the two endpoints are inside together or not at all (else the two
  same-colour chords TauInterleave → contradiction).  Geometric core `interleave_of_one_in_one_out`
  + `outside_of_not_inside`.
- §8 MASTER BRICK `inside_card_even_of_pos_chord` / `_neg_chord` / unified `inside_card_even_of_chord`:
  ν is a `Finset.card_bij` bijection {σ=+1}∩Inside ↔ {σ=−1}∩Inside (MapsTo by mate_together,
  surj by nuPred + mate_together), so card Inside = 2·card positive-inside ⇒ Even.
- §9 `rank_eq_rank_add_inside_left` (3-way disjoint partition {τ<τa} ⊎ {a} ⊎ Inside),
  `rank_eq_succ_of_adjacent`.
- §10 `rank_parity_flip_of_chord` (rank diff = 1 + even inside-card), `rank_parity_iterate`
  (induction on k, step at ν^[n] a via banked `iterate_mem`).
- §11 `no_same_sign_of_tau_adjacent` (banked `even_of_reaches_same_sign` gives Even k; rank parity
  gives Odd k; contradiction).
- §12 final theorem: `List.isChain_isInfix` + `IsChain.imp` converts each `[x,y] <:+: L` adjacent
  pair (τ-order + empty gap from `pairwise_append` decomposition of the sorted list) to `σ x ≠ σ y`.

Banked clean-3 lemmas from ZinanCh36Comb reused unchanged: TauInterleaves, alt_map_of_chain,
iterate_mem, sigma_iterate, even_of_reaches_same_sign, side_of_adjacent.

No other files edited.  (Concurrent workers' ZinanCh36NonInterleave.lean / ZinanCh35*.lean untouched.)
