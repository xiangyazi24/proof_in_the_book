# QUESTION_03: Triage spark's broken batch C code (20+ errors, 200+ lines)

## Status
My target fixes (lines 8002-8003 sorry's) are done, but there are 20+ pre-existing errors in spark's unbuilt batch C code that block verification. The errors span:

1. **shiftedSortedAngleAt_mono** (lines 7750-7779): omega failures in induction ∀ loop
2. **only_event_between_interEventAnglesAt** (lines 7781-7931): multiple errors:
   - `hval_eq ▸ (...)` — invalid ▸ notation (line 7805)
   - `Fin.strictMono_iff_lt_succ` — might not exist (lines 7816, 7852)
   - `Nat.le_sub_of_lt` — unknown lemma (line 7822)
   - Various type mismatches in the idx comparison branches
   - Broken hge/hprev structure (lines 7827-7838)
   - hθ_ne argument passing issues
3. **interEventAngleAt_span** (lines 7657+): potentially also affected
4. **shiftedSortedAngleAt_lt_succ** (lines 7397+): possibly affected

## What I need
1. **Triage strategy**: Should I fix spark's code line-by-line, or rewrite the broken lemmas from scratch? The `only_event_between_interEventAnglesAt` is especially problematic — its proof has structural issues in all 3 branches of the lt_trichotomy.

2. **For `Fin.strictMono_iff_lt_succ`** and `Nat.le_sub_of_lt`: confirm whether these exist in Mathlib4 (or what the correct names are). If not, provide alternative API.

3. **Can I simplify `only_event_between_interEventAnglesAt`?** The proof is 150+ lines. Looking at the original `only_event_between_interEventAngles` (non-_at, ~60 lines), it's much simpler because it uses `sortedAngleAt` directly. The _at version introduces `shiftedSortedAngleAt` complexity. Is there a way to reduce the proof size?

## Build context
- spark's code: batch A+B compiled (I verified shiftedSortedAngleAt_ne, interEventAngleAt_zero/last, sweepLabelingAt_inj all pass), batch C (only_event_between_interEventAnglesAt, interEventAngleAt_span, no_tie_from_start_to_interEventAt) was NEVER independently built
- My code: `inj_at_interEventAngleAt` + `interEventAngleAt_ne_direction_angle` + `mono_at_eventAt` + `nontrivial_blocks_at_eventAt` all structurally correct (numerical proof, no heartbeats issues)
