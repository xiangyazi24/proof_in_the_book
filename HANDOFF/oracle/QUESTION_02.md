# QUESTION_02: Heartbeat timeout in inj_at_interEventAngleAt (hθ_ne proof)

## What I've done
Rewrote `inj_at_interEventAngleAt` using `orientedLevel_ne_of_ne_mod_pi` (as per ANSWER_01). The proof type-checks structurally but times out at 200k and 400k heartbeats. The timeout location is the `hθ_ne` block (line ~8010), which proves `θ ≠ d.angle` for directions in the non-corner case.

## Current hθ_ne proof structure
The proof does:
```
intro heq  -- assume d.angle = θ (= interEventAngleAt j)
rcases (mem_directionsDeterminedBy_iff_exists_equal_level).mp hdir_mem with
  ⟨p, hp, q, hq, hpq_ne, hlevel⟩  -- get two distinct points with direction d
rcases L.point_surjective_on p hp with ⟨a, ha⟩  -- label p
rcases L.point_surjective_on q hq with ⟨b, hb⟩  -- label q
have htie : orientedLevel(d.angle, L.point a) = orientedLevel(d.angle, L.point b) := ...
rw [heq] at htie  -- now orientedLevel(θ, a) = orientedLevel(θ, b)
-- Build the Set.Icc containment and θ ≠ shiftedSortedAngleAt
-- Then apply only_event_between_interEventAnglesAt to get contradiction
```

The chain `mem_directionsDeterminedBy → point_surjective_on × 2 → only_event_between_interEventAnglesAt` creates large nested proof terms.

## Two options I see

**Option X:** Extract hθ_ne into a separate `private theorem interEventAngleAt_ne_direction` lemma, so the heavy proof is compiled once and referenced by a small term.

**Option Y:** Replace the `only_event_between_interEventAnglesAt` contradiction with a direct numerical bounds argument (comparing `d.angle = sortedAngleAt(idx)` with `shiftedSortedAngleAt(j-1) < interEventAngleAt(j) < shiftedSortedAngleAt(j)`). This avoids labeled points and existentials entirely, but requires relating `sortedAngleAt(idx)` to `shiftedSortedAngleAt` which has the +π wrap complication.

## What I need
1. Which option (X vs Y, or suggest another)?
2. If Option Y: is there an existing lemma connecting sortedAngleAt(idx) to shiftedSortedAngleAt(s, t)?

## Build context
The lemma needs to work for the shifted-sweep (`_at`) version where shiftedSortedAngleAt can be sortedAngleAt + π (wrapped case). The non-_at version's hne_dir proof (lines 7090-7110) is cleanly numeric using sortedAngleAt monotonicity.
