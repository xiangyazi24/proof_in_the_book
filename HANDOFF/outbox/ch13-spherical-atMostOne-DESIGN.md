# Ch13 next file — spherical `AtMostOneZero` for `openedWBS` (DESIGN + truth-risk)

The planar bridge (FFCT110, commit de20bed) reduced Ch13's discrete-Fenchel layer to
ONE hypothesis on `openedWBS`'s gproj image:

    ZinanFFCT110.AtMostOneZero θ ρ n
      — at most one nonincident edge–vertex pair has det3 = 0.

This file scopes the remaining work. It is a genuine geometric subproject, NOT wiring.

## Two pieces

### Piece A (verified-true wiring): spherical-zero ⟹ planar-zero, and the θ/ρ match
- `gnomonic_sign_correspondence` (SphericalGnomonic.lean:195): `sOrient a b c = (pos) ·
  det3 (gproj a) (gproj b) (gproj c)`, so a spherical support zero ⟺ a planar det3 zero.
- Need: `gproj h (openedWBS A B k ·)` equals FFCT110's `vert θ ρ n` up to an
  orientation-preserving rigid motion (translation + rotation), with `θ, ρ` the
  edge-angle/length data from the oriented frame (FFCT106 edge-coordinate bridge,
  `edgeZ`/`liftedAngle`, ZinanFFCT96:303). `cross` is invariant under such motions, so
  `supp` (planar) signs/zeros transfer. This is real but mechanical wiring once the
  frame and the closing-edge correspondence are pinned down. The cyclic index map
  (FFCT110 `nxtV`: n↦0 closing edge) must match the spherical closing edge `Q_n → Q_0`.

### Piece B (THE CRUX — truth NOT established): spherical at-most-one-zero
    openedWBS_atMostOneNonincidentZero :
      [strict convexity of A,B + SZ hypotheses] → SupportStuckWBS A B k →
      ∀ c₁ c₂ : NonIncident n,
        supportConstraint … c₁ (-monitoredSupWBS …) = 0 →
        supportConstraint … c₂ (-monitoredSupWBS …) = 0 → c₁ = c₂

What exists: `supportStuckWBS_vanishingSupport` (ZinanFFCT46:435) gives ≥1 zero;
`supportConstraint_pos_at_sup` (SphericalMonitoredSup:251) gives all-strict in the
NON-stuck branch. Uniqueness in the stuck branch is unproven.

## ⚠ TRUTH-RISK — verify BEFORE grinding (playbook §2.6: never grind an unverified target)

`monitoredSupWBS` is the supremum of the opening angle keeping the finite monitored
support family ≥ 0; at the sup the MINIMUM support over the family is 0. Generically one
constraint binds — but for specific (A,B) **two supports can bind at the exact same
opening angle** (the min is achieved by two family members simultaneously). That is a
measure-zero event in (A,B)-space, so random Monte-Carlo will essentially never see it —
but `AtMostOneZero` quantifies over ALL admissible (A,B), and the SZ induction feeds
specific, possibly-degenerate configs (flat sub-arcs, collinear triples, length
disparities — exactly where measure-zero failures hide).

Therefore `AtMostOneZero` for `openedWBS` is **plausibly FALSE without extra
hypotheses** (general position / strict convexity may not suffice to forbid simultaneous
binding). If false, the FFCT110 bridge is correct but *operationally vacuous for this
application* (its hypothesis is unsatisfiable for the configs that arise) — the §3.3
vacuous-conditional trap at the chain level.

### Required verification (adversarial, before any Lean grind)
1. Construct/seek a strictly-convex (A,B) whose WBS opening sup binds TWO nonincident
   supports simultaneously. Search degenerate configs deliberately (symmetric arms →
   two symmetric tangencies bind together is the obvious candidate). If found ⟹ the
   direction needs a weaker target (see fallback).
2. If no two-binding config exists under the SZ hypotheses, prove WHY (e.g. a strict
   second-order / transversality argument that distinct family members have distinct
   binding angles), and that becomes the core of Piece B.

### Fallback if `AtMostOneZero` is false
The planar bridge only needs at-most-one zero *to derive chord≠0 and b≠π*. If openedWBS
can have ≥2 zeros, re-examine whether the SPECIFIC pairs the bridge needs (collision
pair, final-ray pair) are excludable by the actual stuck structure even when other,
harmless coincidental zeros exist. I.e. weaken `AtMostOneZero` to "no collision-type and
no final-ray-type zero" and prove THAT directly from the WBS geometry — possibly easier
and more likely true than global uniqueness.

## Recommendation
Run the adversarial truth-check (step 1) FIRST. Only commit to the Lean proof of Piece B
once its true statement (and the necessary hypotheses) is pinned down. Piece A wiring can
proceed in parallel (verified-true regardless).
