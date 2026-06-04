# QUESTION_01: Strategy for inj_at_interEventAngleAt non-corner case

## What I'm doing
Fixing `inj_at_interEventAngleAt` (lines 7951-8009), the parameterized-shift version of the original (non-_at) lemma. Spark left 3 or more errors in the non-corner branch.

## What I've tried / diagnosed
The non-corner case (0 < j.val < card) needs to prove:
`Function.Injective (orientedLevel (interEventAngleAt θ₀ s j) ∘ L.point)`

The non-_at version (lines 7052-7110) works by:
1. Proving interEventAngle ∈ [0, π) using sortedAngleAt bounds
2. Proving no direction angle equals interEventAngle via lt_trichotomy case split on idx
   - Uses interEventAngle < sortedAngleAt(j) and sortedAngleAt(j-1) < interEventAngle

For the _at version, there's a FUNDAMENTAL DIFFERENCE: shiftedSortedAngleAt can return values ≥ π (when wrapped), so interEventAngleAt can be ≥ π. This means orientedLevel_injective_at_non_direction_angle (which requires angle ∈ [0,π)) can't be used directly.

## Decision point: how to structure the ≥ π case

I see two options:

**Option A — Case split + π-shift:**
- If interEventAngleAt < π: use sweepLabelingAt_inj_at_interEvent (existing lemma) with hne_dir proven via only_event_between_interEventAnglesAt contradiction argument
- If interEventAngleAt ≥ π: shift by π (orientedLevel_add_pi), reduce to [0,π) range, prove hne_dir for shifted angle

**Option B — Use only_event_between_interEventAnglesAt everywhere:**
For the ≥ π case, use the same only_event_between_interEventAnglesAt contradiction argument without case splitting. The lemma only requires the angle to be in some inter-event interval and ≠ shiftedSortedAngleAt.

## What I need from you
1. Confirm the right strategy (A or B, or suggest a better one)
2. For Option A's ≥ π branch: the shifted angle's hne_dir proof. The shifted angle = interEventAngleAt(j) - π. When both surrounding shiftedSortedAngleAt values are ≥ π, subtracting π maps them to plain sortedAngleAt values, and the non-_at proof structure applies. But what about the crossing case (j-1 unwrapped, j wrapped) where interEventAngleAt(j) ≥ π? Then shiftedSortedAngleAt(j-1) - π < 0, destroying the lower bound.

3. Can interEventAngleAt(j) be ≥ π for non-corner j? Confirm the conditions when the shifted sweep crosses π.
