# Ch35 anchoring report — the side-1 vertex-star anchoring residual

**File:** `ProofsInTheBook/ZinanCh35Anchoring.lean` (NEW, 0 errors, 0 warnings).
**Verify:** `lake env lean ProofsInTheBook/ZinanCh35Anchoring.lean` on uisai2 — type-checks.
All four `#print axioms` report exactly `[propext, Classical.choice, Quot.sound]` (clean-3): no
`sorryAx`, no `native`, no `axiom`. No `sorry`/`admit`/`native_decide` in the file.

## Inventory (gates / Jordan dichotomy), confirmed by reading the source

* **Separation, face-level only.** `ZinanCh35Gates.jordan_simple_cycle2_unconditional` gives, for a
  sphere map (`hNT.sphere = ⟨Connected, χ=2⟩`), `¬ DualReachableAvoidingCycle M C (faceLeft i) (faceRight i)`
  for every `i`. There is **no dichotomy/totality** lemma ("every face is C-reachable from one of the
  two chord faces") landed — I searched `gateCompat'`, `JordanOracleConstruct`, `ZinanCh35Split`,
  `crossBankBridge_of_dualReachable`. The gate output is purely the *non*-reachability of the two
  sides of one cycle edge.
* **`crossBankBridge_of_dualReachable`** is the *converse* engine (reachability ⟹ cut-map bridge),
  consumed by the gates to refute reachability via Euler; it is not a side-membership tool.
* **`separates_closed` / `separates_of_chordSplitData`** already land full `data.Separates` =
  `face₂ ∉ side₁`. The chord∪arc cycle datum (`ChordCycleData`) is built by `chordCycleData` from
  `dartArcOfNonBoundaryEdge` between the chord endpoints; crucially it does **not** identify which
  of `data.arc.path₁` / `path₂` that arc is, and there is no landed lemma placing a path₂-internal
  vertex off the cycle. (This is the exact gap the previous two waves flagged.)

## What closed (the genuine new content)

The decisive observation the earlier waves missed: **`side₁` is itself a cycle-avoiding
dual-reachability closure**, with avoidance set a *superset* of any chord∪arc cycle's edge set.

* `side₁ = Side u v face₁ = {f | ReflTransGen (ChordSplitAdj u v) face₁ f}`, and a `ChordSplitAdj`
  step crosses an edge that is **neither a boundary edge nor the chord**.
* For the chord∪arc cycle `C`, `hsub : ∀ e ∈ C.edgeSet, e = s(u,v) ∨ IsBoundaryEdge e`.

So a `ChordSplitAdj` step is a `DualAvoidsCycleStep` for `C` (`dualAvoidsCycleStep_of_chordSplitAdj`),
and the closures inherit it. This gives the unconditional **engine**

  `side₁_dualReachable_avoidingCycle : f ∈ side₁ → DualReachableAvoidingCycle M C face₁ f`,

and, composed with `jordan_simple_cycle2_unconditional` (`face₁ = faceLeft i₀`, `face₂ = faceRight i₀`
via `hleft`/`hright`), the sharp **bank tool**

  `notDualReachableToFace₂_of_mem_side₁ : f ∈ side₁ → ¬ DualReachableAvoidingCycle M C f face₂`.

This is the gate vocabulary, one transitivity step from the discharged Jordan separation, and is the
correct lever for the opposite-arc star argument. Both are proved here, axiom-clean.

## The reduction (strictly smaller residual)

`starConfinement_of_bankAnchor` **derives the consumed `Side₁StarConfinement`** from a new, strictly
smaller residual `Side₁StarBankAnchor`, using only the engine + the bank tool:

* **`oppArc_star_core` is FULLY reduced.** The residual field `oppArc_star_bank` asserts only the
  *bank placement* of an opposite-arc vertex's inner star, in gate vocabulary
  (`DualReachableAvoidingCycle … face₂`, a single bank): each non-chord star dart at a
  path₂-internal `w` has its own face reaching `face₂` avoiding `C`, plus a reverse-face clause for
  the outer-boundary sub-case. The bank tool turns each placement bucket into the *side-1 omission*
  the original field demanded — the contradiction with side-1 membership, previously baked into the
  field, is discharged in this file by the engine.
* **`edge_core` is carried verbatim** (NOT reduced). It needs side-1 membership as a *conclusion*,
  i.e. the back direction *reachability ⟹ membership*, which the engine does not provide and which is
  false in general (exactly the "bare dual path is too weak" direction the gate header warns about).
  It stays an honest field of the smaller residual.

### Why the residual is strictly smaller (and honest)

The original `oppArc_star_core` quantified over the global side-1 closure `data.side₁`. The new
`oppArc_star_bank` quantifies over `DualReachableAvoidingCycle … face₂` — a single bank, strictly
weaker and one step from the discharged Jordan gate. The reduction is a genuine theorem
(`starConfinement_of_bankAnchor`), not a restatement: it consumes the bank field and the engine to
*produce* the global side-1 confinement. The residual is satisfiable and non-vacuous (path₂ carries
an internal vertex by `data.arc₂_internal`; `edge_core`'s hypotheses are inhabited by
`sideRegion₁_nonempty`); in the planar model the bank placement is exactly true (the inner star of a
path₂-internal vertex lies on `face₂`'s bank of the chord∪arc cycle).

## Remaining residual + attack sketch

`Side₁StarBankAnchor` has two fields:
1. `edge_core` (verbatim region edge-confinement; the engine cannot touch it).
2. `oppArc_star_bank` (the pure planar bank placement of the opposite-arc inner star).

Closing them needs the one fact still missing at the landed altitude: **the chord∪arc cycle's arc is
`path₁`, so path₂-internal vertices lie off `C`**, and **the inner star at such a `w` is connected to
`face₂` by a `C`-avoiding dual walk along the path₂ strip**. Concretely, to discharge
`oppArc_star_bank`: (a) show `data.arc.path₂` is the arc *not* used by `chordCycleData`'s `C`
(an arc-identification lemma against `BoundaryArcSplit.internally_disjoint`), giving that the two
path₂ boundary edges at `w` are non-`C` edges, hence `DualAvoidsCycleStep`s; (b) walk the inner star
of `w` across these non-`C` edges to a face adjacent to `α(chordDart)`'s side, landing on `face₂`'s
bank — using the StarRotation `side_constant_on_cutFree_walk` with `Cut := C`-edge and the two path₂
edges as the only star cuts at `w`. `edge_core` then follows from the same arc-identification plus the
non-chord region-edge non-crossing argument. This `C`-arc-identification lemma is the genuinely
remaining discrete-Schoenflies content and is the recommended next target.

## Deliverables

* `ProofsInTheBook/ZinanCh35Anchoring.lean` — compiling, clean-3.
* Main results: `dualAvoidsCycleStep_of_chordSplitAdj`, `side₁_dualReachable_avoidingCycle` (engine),
  `notDualReachableToFace₂_of_mem_side₁` (bank tool), `starConfinement_of_bankAnchor` (the reduction
  `Side₁StarBankAnchor → Side₁StarConfinement`).
