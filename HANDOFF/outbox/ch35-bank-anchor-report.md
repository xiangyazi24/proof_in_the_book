# Ch35 bank-anchor report — positive bank transport + the boundary-incidence seed residual

**File:** `ProofsInTheBook/ZinanCh35BankAnchor.lean` (NEW, 0 errors, 0 warnings).
**Verify:** `lake env lean ProofsInTheBook/ZinanCh35BankAnchor.lean` on uisai2 — type-checks.
All six `#print axioms` report exactly `[propext, Classical.choice, Quot.sound]` (clean-3): no
`sorryAx`, no `native`, no `axiom`. No `sorry`/`admit`/`native_decide` in the file.

## What was attacked

`ZinanCh35Anchoring.lean`'s residual `Side₁StarBankAnchor` (two fields, `edge_core` +
`oppArc_star_bank`). `oppArc_star_bank` needs the *positive* bank placement
`DualReachableAvoidingCycle M C (dartFace d) face₂` for every non-chord star dart `d` at a
path₂-internal vertex `w`. Every landed `DualReachableAvoidingCycle` lemma produces only the
*negative* direction (the gate refutes reachability; `crossBankBridge_of_dualReachable` and the
engine both *consume* reachability). No positive-walk constructor exists beyond
`ReflTransGen.single/head/tail` over explicit `DualAvoidsCycleStep`s.

## The genuine new content (proved, axiom-clean) — a positive bank-transport tool

The decisive observation: the bank predicate `DualReachableAvoidingCycle M C (starFace x ·) face₂`
is **invariant across every non-`C` step of the vertex rotation**, hence constant along any
`CycleStarDart`-cut-free rotation walk. Four landed lemmas:

* `dualAvoidsCycleStep_of_star_not_cycle` — a non-`C` star dart `d` (its edge ∉ `C.edgeSet`)
  witnesses `DualAvoidsCycleStep` from `starFace x d` to `starFace x (starSigma M x d)`
  (`= dartFace (M.α d)`, via the brick-1 identity `starFace_next_eq_alpha`).
* `dualReach_face₂_star_step_iff` — that step's two faces reach `face₂` avoiding `C` iff each other
  (forward via `ReflTransGen.head` on the step; backward via the `α`-reversed step).
* `starBank_constant_on_cycleStar_free_walk` — instantiates the abstract brick-3 lemma
  `side_constant_on_cutFree_walk` with `Cut := CycleStarDart C x`,
  `Side := DualReachableAvoidingCycle M C (starFace x ·) face₂`.
* `dualReach_face₂_of_starWalk` — **the load-bearing positive transport**: a single seed star dart
  on `face₂`'s bank propagates the bank placement to every star dart joined to it by a `C`-cut-free
  rotation walk. This manufactures positive reachability for a *whole* cut-free star interval out of
  one seed — exactly the tool the earlier waves lacked.

## The reduction (strictly smaller residual `OppArcStarSeed`)

`bankAnchor_of_oppArcStarSeed` derives `Side₁StarBankAnchor` from a strictly smaller residual
`OppArcStarSeed`, and `starConfinement_of_oppArcStarSeed` chains through
`starConfinement_of_bankAnchor` to discharge the consumed `Side₁StarConfinement`.

* `oppArc_star_bank` (placement of *every* star dart at `w`, a whole-rotation statement) is reduced
  to `oppArc_star_seed`: at each path₂-internal `w`, **one** seed star dart on `face₂`'s bank, plus
  a `C`-cut-free `RotationArcWithoutCuts` joining it to the given star dart `d` (the path₂-strip
  connectivity), plus the outer reverse clause. The transport theorem produces the full field.
* `edge_core` is carried verbatim (the engine cannot supply its reachability⟹membership
  back-direction, exactly as in `ZinanCh35Anchoring.lean`).

## Honest status of the remaining residual (why full closure is blocked here)

`OppArcStarSeed` is the genuine irreducible content: the missing **boundary-incidence / arc-
identification layer**. Verified by reading the source:

* `BoundaryArcSplit` (`PlanarMapBoundary.lean`) exposes a path₂-internal vertex `w` only as an
  abstract entry of a `BoundaryPath.vertices` list. The ONLY landed facts about
  `w ∈ path₂.internalVertices` are `internalVertices_subset` (`w ∈ path₂.vertices`),
  `internalVertex_ne_start/_end` (`w ≠ u, v`), and `path₂_boundary_vertices`
  (`w ∈ outerCycle.vertices`). `BoundaryPath` stores no darts; the `arcSplit` certificate is a black
  box over `Sym2`/vertex lists. There is **no lemma** tying `w` to any dart of `M` tailed at `w`,
  to the placement of `w`'s boundary edges relative to `C.edgeSet`, or to a seed face on `face₂`'s
  bank.
* `chordCycleData` (`ZinanCh35ChordCycle.lean`) builds `C`'s arc by `dartArcOfNonBoundaryEdge` — an
  *abstract* cyclic boundary run from `head c₀` to `tail c₀`, **never identified** with
  `path₁`/`path₂`. So path₂-internal vertices are not even known to lie off `C`, and the two
  boundary edges at `w` are not known to be non-`C` (i.e. crossable as `DualAvoidsCycleStep`s).

Both the seed face and the cut-free strip connectivity therefore require this incidence layer, which
is not landed. Per the honesty contract this is isolated, unreduced, as `OppArcStarSeed`, with the
positive bank transport around it fully proved and axiom-clean. The residual is non-vacuous (path₂
carries an internal vertex by `data.arc₂_internal`; in the planar model the seed and strip walk
exist exactly).

## Recommended next target

The single missing brick is a **boundary-incidence layer**: for `w ∈ path₂.internalVertices`,
(a) produce the star darts of `M` tailed at `w` and identify its two boundary edges, (b) the
arc-identification `C`'s arc = `path₁` (so `w ∉ C`'s vertices and the two path₂ boundary edges at
`w` are non-`C`, giving the cut-free interval), (c) the seed: `face₂` connects to a path₂-corner
face avoiding `C`. With that layer, `dualReach_face₂_of_starWalk` (this file) closes
`oppArc_star_bank` immediately; `edge_core` follows from the same arc-identification via the engine's
non-seam star steps.

## Deliverables

* `ProofsInTheBook/ZinanCh35BankAnchor.lean` — compiling, clean-3.
* Main results: `dualAvoidsCycleStep_of_star_not_cycle`, `dualReach_face₂_star_step_iff`,
  `starBank_constant_on_cycleStar_free_walk`, `dualReach_face₂_of_starWalk` (positive transport),
  `bankAnchor_of_oppArcStarSeed` + `starConfinement_of_oppArcStarSeed` (the reductions
  `OppArcStarSeed → Side₁StarBankAnchor → Side₁StarConfinement`).
