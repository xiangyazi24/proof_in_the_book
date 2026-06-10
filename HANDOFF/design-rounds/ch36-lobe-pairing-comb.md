(pbook2 wave-2, 2026-06-10, via tab paste — extended channel still lossy)
CORRECTION confirmed: "two noncrossing matchings ⟹ alternation" is FALSE without connectedness
(counterexample: +,+,−,− both-matchings (1,4),(2,3)). The fix: the two matchings are the two colors
of ONE boundary-successor cycle. Master theorem alt_of_twoSide_noncrossing_cycle (S, τ, σ, ν;
τ-inj, ν closed+single-cycle, σ = ±1, σ(ν a) = −σ a, two-sided TauInterleaves-free) ⟹ Alt sorted.
Proof: component-separation induction — colored chord families are laminar; a same-sign τ-adjacent
pair's gap separates them in the union; peel the outer chord of any ν-path crossing the gap;
base impossible by sign-flip. 11-brick order: nextCrossing (cyclic min-dist), no_crossing_before_next,
sign persistence runs, upperLobeOfPos/lowerLobeOfNeg, boundaryCrossingList + cycle connectedness,
noninterleaving transports (needs the GEOMETRIC lobes theorem — pending ArcSweep+assembly),
Comb master #7, fullLineCrossingAlternation_of_lobes assembly, compose with landed dichotomy.
