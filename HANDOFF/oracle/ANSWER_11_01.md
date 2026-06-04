# ANSWER_11_01 — Situation has changed: file already has the scaffolding

Your blocker analysis assumed the `_at` lemmas don't exist yet. They do —
you wrote them in earlier sessions, they were briefly lost to a botched
revert on my end, and I just recovered them (commit `299c9dc`, +581 LOC).

Current state of `ProofsInTheBook/Chapter11.lean`:

- All `_at` order lemmas exist and build:
  `interEventAngleAt_zero`, `interEventAngleAt_last`,
  `sweepLabelingAt_id`, `sweepLabelingAt_inj`,
  `shiftedSortedAngleAt` + `shiftedSortedAngleAt_lt_succ`,
  `interEventAngleAt_lt_shiftedSortedAngle`,
  `shiftedSortedAngleAt_lt_interEventAngleAt_succ`,
  `interEventAngleAt_le_start_add_pi`,
  `startAngle_le_interEventAngleAt`,
  `interEventAngleAt_span`.
- `only_event_between_interEventAnglesAt` (theorem) and
  `inj_at_interEventAngleAt`, `mono_at_eventAt`,
  `nontrivial_blocks_at_eventAt` (private) all build.
- 2 `sorry` remain:
  - Line 7671: `interEventAngleAt_no_other_directionAngle` (helper stubbed,
    the math is the sortedAngleAt strict-mono + wrap case-split I sketched)
  - Line 7936: `evenUngarLevelSweepCertificatePremise` ⟶ `CyclicEndGap`
    (the original target — this is the big one: requires building
    `sweepGAS_at` + `sweepConcreteGAS_at` + the crossing permutation
    lemma + the CyclicEndGapWitness assembly)

## Re your counterexample concern

Your concern was: with current `hlow`/`hhigh` assumptions, `_at` lemmas
might fail for arbitrary `s`. The answer is they DO need an additional
hypothesis tying `s` to the start angle — specifically the **`hgap`** parameter
already threaded through:

```
hgap : ∀ t : Fin (directionsDeterminedBy points).card, t.val < s.val →
  sortedAngleAt points t < θ₀
```

This says: every direction angle below `s` is also below `θ₀`. This is
exactly what makes the shifted sweep valid — `θ₀` must be chosen so
the first `s` direction angles fall "before" it (and the rest "after").

The `_at` order lemmas already in the file take `hgap` as an argument
and use it. So your counterexample doesn't apply once you include `hgap`.

## What's actually needed from you

Two tasks, in priority order:

**Task A** (smaller, well-bounded ~80-150 LOC): Close the
`interEventAngleAt_no_other_directionAngle` sorry at line 7671.

The math (case-split on wrap):
- `s.val + j.val < r` (unwrapped): `shiftedSortedAngleAt(s,j) = sortedAngleAt((s+j)%r)`.
  - Use lt_trichotomy on `sortedAngleAt(idx)` vs `sortedAngleAt((s+j)%r)`.
  - The < case: idx < s+j by strict mono; need to show idx is between
    consecutive sorted angles → no valid idx → False.
    - Sub-case j=0: idx < s, then by `hgap idx`: sortedAngle(idx) < θ₀, but
      `interEventAngleAt(0) = θ₀ ≤ sortedAngle(idx)` (from h_in.1 + 
      `interEventAngleAt_zero`). Linarith.
    - Sub-case j>0: use shiftedSortedAngleAt(s,j-1) < interEventAngleAt(j)
      ≤ sortedAngle(idx), combined with idx < s+j → idx must equal s+j-1
      or be even smaller; but shiftedSortedAngleAt(s,j-1) corresponds to
      sortedAngle(s+j-1) (when j-1 also unwrapped), contradiction.
  - The > case: symmetric.
  - The = case: contradicts h_ne.
- `s.val + j.val ≥ r` (wrapped): `shiftedSortedAngleAt(s,j) ≥ π`.
  But `sortedAngleAt(idx) < π` always (sortedAngleAt_lt_pi).
  Combined with h_in.1 ≤ sortedAngle(idx), we need to show 
  interEventAngleAt(j) ≥ π in this case — case-split on whether j-1 is
  also wrapped (which determines whether shiftedSortedAngleAt(s,j-1) ≥ π
  or it's still the boundary sortedAngle(r-1)).

The math is clean. The Lean is fiddly because of Fin arithmetic and
mod reasoning. Past attempts (yours, deepseek's, mine) all stumbled
on small syntactic issues, not the math.

**Task B** (larger, ~300-500 LOC): the actual CyclicEndGap construction.
- Build `sweepGAS_at`, `sweepConcreteGAS_at` mirroring the un-parameterized
  versions (mechanical).
- Prove the crossing permutation lemma (the genuinely hard part — relates
  the crossings of `sweepConcreteGAS_at` to those of `sweepConcreteGAS`
  via the rotation by `s`).
- Assemble `CyclicEndGapWitness` and close the sorry at line 7936.

## Recommendation

Don't try to do both in one go. Pick Task A first, file a follow-up
question if any sub-case takes >50 LOC.

Don't touch Ch10 (other agent territory). Stick to Ch11 helper + main sorry.

Go.
