# ch36comb reply — pure-combinatorics master theorem of the Ch36 alternation pipeline

File: `ProofsInTheBook/ZinanCh36Comb.lean` (NEW, standalone; imports only
`ProofsInTheBook.ZinanCh36Theta` to reuse `Alt`). 0 sorry / 0 axiom / 0 native_decide.
`lake env lean` clean on uisai2.

## Status: PARTIAL — structural scaffold landed, the laminar crux is NOT closed.

The headline `alt_of_twoSide_noncrossing_cycle` is **not** in the file (I do not ship a
`sorry`'d theorem per STRICT). What IS shipped are the fully-proven, clean-3 building blocks of
its proof. Below: what landed, then the precise sticking point with the reason every shortcut
provably collapses to the same irreducible core.

## Landed (all clean-3: subset of {propext, Classical.choice, Quot.sound}, no sorryAx)

1. `TauInterleaves` — the pinned definition (verbatim from the brief).
2. `alt_map_of_chain (σ) : IsChain (fun a b => σ a ≠ σ b) L → Alt (L.map σ)`
   — the reduction "no two consecutive elements share a sign ⟹ `Alt (L.map σ)`". This is the
   exact wiring that turns the core no-adjacency lemma into the `Alt` conclusion. (`Chain'` is
   deprecated → uses `List.IsChain` + `List.isChain_cons_cons`.)
3. `iterate_mem` — `ν^[k] a ∈ S`.
4. `sigma_iterate : σ (ν^[k] a) = (-1)^k * σ a` — the sign-flip-along-ν formula.
5. `even_of_reaches_same_sign` — **parity**: `ν^[k] a = b`, `σ a = σ b = ±1` ⟹ `Even k`.
6. `side_of_adjacent` — **gap geometry**: with nothing of `S` strictly between `a` and `b`
   (`τ a < τ b`), every `x ∈ S` has `τ x ≤ τ a ∨ τ b ≤ τ x` (the two-sides split).

## The sticking point (precise)

The whole theorem reduces — cleanly, via (2) — to the **core no-adjacency lemma**:

> if `a, b` are τ-adjacent in `S` and `σ a = σ b`, then `¬ ∃ k, ν^[k] a = b`.

(Then `hcycle` supplies such a `k` for every pair, contradiction ⟹ no adjacent same-sign pair
⟹ `IsChain (σ·≠·) L` ⟹ `Alt`.)

The core lemma's content is **a laminar signed-crossing bound**, and that is the unclosed crux.
I attacked it four independent ways; every one provably bottoms out at the *same* laminar core,
so the failure is structural, not a tactic gap:

- **Path-spanning + parity.** Walk `a=x₀→…→x_k=b`. Side(x₀)=Lo, Side(x_k)=Hi, so an odd number
  of steps "span" the empty gap `G=(τa,τb)`. But parity gives nothing usable: same-colour ⟺
  same cycle-parity ⟺ even cycle-distance is *automatic* for every same-colour pair, so the
  contradiction cannot be parity-based. **Two co-spanning chords are NESTED, not interleaved**
  (both intervals ⊇ `[τa,τb]`), so they do NOT violate NI directly. Confirmed.
- **Boundary-chord NI shrink.** `hposNI` (resp `hnegNI`) only relates the two *representative*
  chords `(a,νa)` and `(b,νb)`; the path interior `x₂…x_{k-2}` is uncontrolled by a single NI
  application. No two-chord descent shrinks the minimal-`k` counterexample — the interior needs
  the *whole* same-colour laminar family, not one comparison.
- **Suffix-sum dichotomy** `D c = ∑_{τx≥c} σx ∈ {0, s₀}` (which would finish via the *already
  proven* `alt_of_cut_dichotomy` in `ZinanCh36Theta`!). But `D c ∈ {0,s₀}` for all cuts `c`
  is **logically equivalent to the alternation itself** (the partial sums alternate ⟺ consecutive
  signs alternate). Circular: it relocates, doesn't discharge, the crux.
- **card-induction peel.** Removing the τ-max `M` and reconnecting breaks `hflip` (the new edge
  joins two equal signs: `σ p = -σM = σ(νM)`); peeling one element makes the orbit odd. The
  structure is not preserved by single- or naive two-element peels.

**Conclusion.** The crux is the design's "§9 component-separation induction" = a *laminar family
crossing bound*: the colour-`+1` chords `{x,νx | σx=1}` are pairwise non-interleaving (NI) ⟹ they
form a laminar (nested-or-disjoint) family on the τ-line; combined with the single-cycle
alternation this forces the signed suffix increments to stay in `{0,±1}` with fixed sign. That is
genuine ~200–400 line laminar-family infrastructure (build the nested chain of crossing chords at
each cut; show the innermost spanning chord of the a→b path peels to a strictly smaller spanning
sub-path). It does not collapse to a short proof; connectedness is provably essential (the
`(+,+,-,-)` counterexample is exactly where the laminar family splits into two components and the
suffix sum hits `-2 ∉ {0,s}`).

## Recommended next move

Dispatch the laminar core as a *bounded* sub-goal to a dedicated worker with the interface:
prove `core_no_adjacency` (signature above) — the file already supplies the reduction (2),
parity (5), and side-split (6), so the worker only owns the laminar peel. Alternatively prove the
suffix dichotomy `HW` and finish through the existing `ProofsInTheBook.ZinanCh36Theta.alt_of_cut_dichotomy`.

## MASTER ADDENDUM (2026-06-10, after independent verification)
- Brute force n = 4, 6, 8 over ALL sign patterns with adjacent same-sign pairs and ALL cycle
  assignments: ZERO counterexamples. The statement is TRUE as abstracted; keep pushing the proof.
- Master's induction analysis: (1) an INNERMOST upper chord's endpoints are τ-ADJACENT (proof: any
  element strictly inside its interval carries its own upper chord, which by upper-NI must nest
  strictly inside — contradicting innermost; this is PROVEN-grade, use it); (2) splicing out that
  pair (x,y) preserves: single-cycle (ν' = skip), sign-flip (3-step parity), upper-NI (subset),
  lower-NI (the two dying lower chords merge into (p,q) whose interval ⊆ the union of the dead
  intervals + the empty gap; case analysis closes); (3) the LIFT is where it sticks: sorted-S =
  sorted-S' with block [B1,B2] inserted between consecutive l, r of S'; IH gives σl = −σr and the
  block alternates internally; the ONE missing fact is σB1 ≠ σl (then σB2 ≠ σr is automatic).
  That boundary condition is not locally refutable (NI is consistent with σl = σB1 since the
  empty gap kills strict interleaving) — the information must come from the cycle structure again.
  NEXT ATTACK: strengthen the IH (e.g. prove alternation TOGETHER WITH "every upper chord's left
  endpoint sign pattern" or induct peeling the innermost LOWER chord simultaneously; or track the
  parenthesis depth function and prove σ at τ-sorted position t is determined by the parity of
  the upper-depth at t — a depth-determines-sign invariant would make the lift trivial).
