# Ch13 WBS family — Brick 3 + Brick 7 report (`ZinanFFCT45.lean`)

**Status:** COMPLETE, compiles clean-3 (0 errors, 0 sorry/admit/axiom/native_decide). 488 lines.
**Verified:** `ssh uisai2 'lake env lean ProofsInTheBook/ZinanFFCT45.lean'` — only output is `push_neg`
deprecation warnings (cosmetic, present throughout the FFCT line) and the `#print axioms` block:
every theorem depends on exactly `[propext, Classical.choice, Quot.sound]`.

## What was built (one file, `ProofsInTheBook/ZinanFFCT45.lean`)

Imports `ZinanFFCT42` only (transitively brings FFCT41/40/37/20/3 and the substrate).
**Did NOT touch any other file. Did NOT import/reference `ZinanFFCT44`.**

### Brick 3 — the hemisphere-free WBS family (design §§7-8)

- `monitoredFamilyWBS` — index `(NonIncident n ⊕ Unit) ⊕ Unit`: support (`-θ`), joint slack
  (`jointAngle B k − openedInteriorJointAngle A k (-θ)`), base cap (`baseCapSupportW A k`).
  **No hemisphere member** — this is the entire point of design route (c).
- `continuous_monitoredFamilyWBS`, `monitoredSupWBS`, `monitoredSupWBS_mem`, `monitoredSupWBS_mem_Icc`.
- `monitoredFamilyWBS_zero_nonneg` — init admissibility at θ=0: supports ≥ 0 (`edge_support`), slack > 0
  (deficit), base ≥ 0 (banked `orientedDatum_interior`). Mirrors FFCT41's `monitoredFamilyWB_zero_nonneg`.
- **WBS closure lemmas** (the assembly wave needs these): `supportWBS_sOrient_nonneg`,
  `openedInteriorJoint_le_at_supWBS`, `baseCapSupportW_nonneg_at_supWBS` — supports/slack/base ≥ 0 at δ*.
- `admissibleWBS_le_deficit` — the deficit bound, ported from FFCT37's `admissibleW_le_deficit` via the
  `jointWitness` support member + slack member (both live in the hemi-free family); hence
  `monitoredSupWBS_le_deficit`, `monitoredSupWBS_lt_pi`.
- `GlueWBaseCap_at_supWBS` — the base cap δ* + γbase ≤ π by admissibility (sine-branch argument,
  mirrors FFCT41's `GlueWBaseCap_at_supWB` / `admissibleWB_baseCap` verbatim).
- `ReachWBS` / `SupportStuckWBS` / `BaseStuckWBS`, `opening_boundary_trichotomyWBS` (generic
  `reach_or_stuck`; CAP killed by `monitoredSupWBS_lt_pi`; **no hemi-stuck branch**).
- `glueWBS_clause_ii` (`¬SupportStuckWBS → ReachWBS ∨ BaseStuckWBS`) and `glueWBS_clause_i`
  (endpoint mono at δ*, mirror FFCT41's `glueWB_clause_i`).

### Brick 7 — the FFCT42 base-stuck port (design §11)

- `baseStuckWBS_forces_vanishingSupport` — re-instantiation of FFCT42's `baseStuck_eq_openedDiagonal`
  + `baseDiagonal_zero_is_wrapEdgeSupport_zero` at `δ = monitoredSupWBS A B k`. Both FFCT42 lemmas are
  **family-independent arm-level `det3` algebra** (free in the opening angle δ), so the port is a pure
  re-instantiation — the family enters only through which sup δ* is plugged in (exactly as the design
  prescribed: "re-instantiate").
- `BaseStuckProgressWBS` (Prop) + `BaseStuckProgressWBS_holds` (**theorem**, discharged). The base
  diagonal zero IS the wrap-edge non-incident support zero at `(last, K)`. Unconditional — no
  `OpenedClosingEdge*`, no `SupportStuckMargins`, no straightening completion, no sub-arm IH. This is
  the honest analogue of FFCT42's `BaseStuckProgressW_holds` for the hemi-free family.

## Honesty contract

- Every mirrored theorem carries the same or weaker hypotheses than its WB original. **No strengthening.**
  One structural simplification vs WB: the deficit-bound / closure lemmas take only `(hka, hkt, hkdef)`
  and drop the WB `(h₀, hnorm, hhpos)` hemisphere data — because the hemisphere members are gone, the
  init-admissibility `h0` is now derived internally from `hkdef` rather than assumed (the design's stated
  goal). This is a genuine WEAKENING of the hypothesis surface, not a strengthening.
- `BaseStuckProgressWBS` is a **theorem**, not a named residual (as in WB). This is honest: the FFCT42
  cyclic shortcut genuinely discharges it; the base diagonal zero literally is the wrap-edge support zero.
- No vacuous statements. Five anti-impostor guards land non-vacuity for `ReachWBS`, `BaseStuckWBS`, the
  discharged-payload indices (nondegenerate wrap pair), and the base cap (real range condition at δ=0).

## What the assembly wave plugs in (NOT in this file, sibling-owned)

The design §§9-10 master theorems `openHemisphere_at_WBS_sup`, `supportStuckWBS_weakConvex`,
`reachWBS_strictConvex` are NOT built here (they are the master-tier geometry, owned by `ZinanFFCT44` /
the assembly wave). Where they would produce the open hemisphere, the closure lemmas in §1′
(`supportWBS_sOrient_nonneg` etc.) are the named substrate they consume. The WBS trichotomy +
`BaseStuckProgressWBS_holds` here remove the base-stuck and hemi-stuck branches; the support/reach
branches route into those sibling theorems.

**File:** `/Users/huangx/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT45.lean`
