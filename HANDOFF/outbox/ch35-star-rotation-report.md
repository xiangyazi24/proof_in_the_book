# Ch35 Schoenflies star-rotation — bricks 1–3 report

**File:** `ProofsInTheBook/ZinanCh35StarRotation.lean` (403 lines, 0 errors, 0 warnings, clean-3).
**Verified on:** uisai2 via `lake env lean`. Imports only stable upstream modules
(`PlanarMapChordSplitData`, `PlanarMapCutCap`) — touches no other file.

## The two danger zones, settled by reading source

### 1. Composition convention: `φ = σ * α` (PlanarMap.lean:39)

`M.φ = M.σ * M.α`, i.e. `M.φ d = M.σ (M.α d)`; `M.dartFace d = ⟦d⟧_φ`; simp lemma
`dartFace_phi : dartFace (φ d) = dartFace d`.

The KEY local identity holds **on the nose, no σ⁻¹/side-flip adaptation needed**:
```
starFace_next_eq_alpha : starFace x (starSigma M x d) = M.dartFace (M.α d.1)
```
because `M.φ (M.α d) = M.σ (M.α (M.α d)) = M.σ d` (α involution), so `σ d` and `α d` share a
φ-orbit, hence `dartFace (σ d) = dartFace (α d)`. The next dart around the vertex reads the
face *across the edge* of `d`, exactly as the design intended.

### 2. The Cut-predicate mismatch — resolved by keeping Cut PARAMETRIC

The design flagged: `star_side₁_next_iff_of_not_seam` needs `¬IsBoundaryEdge ∧ ≠chord` (the full
**seam** = every old boundary edge ∪ the chord), but the cycle `C = chord ∪ ONE arc` only sees
its own `edgeSet` (an opposite-arc dart is a boundary edge but NOT a C-edge). These genuinely
differ, so "cut = seam" ≠ "cut = cycle-dart".

**Resolution.** Brick 3's load-bearing lemma `side_constant_on_cutFree_walk` is stated for an
**arbitrary** `Cut : K → Prop` with the invariance `Inv : ∀ k, ¬Cut k → (Side k ↔ Side (ρ k))`
taken as input — pure permutation combinatorics, zero map theory. The later wave instantiates
`Cut` with the seam predicate (for which brick 1 supplies `Inv` directly) and uses brick 2's
`cycleStarDarts` cardinality only to count the C-edge cuts; the opposite-arc boundary edges are
handled separately in assembly. I also provide the seam-instantiated convenience forms
`starSide₁_constant_on_cut_free_walk` and `star_escape_crosses_seam`, where the Cut is the
explicit seam predicate `IsBoundaryEdge (dartEdge d.1) ∨ dartEdge d.1 = s(u,v)`.

## Adaptations to the real substrate

- `C.vertexSet` does not exist in `SimplePrimalCycle`. Defined the natural
  `CycleVertexMem C x := ∃ i, M.tail (C.dart i) = x` and used it for the brick-2 cardinality
  hypotheses.
- `RotationArcWithoutCuts` made a `def … : Prop := ∃ n, …` (not a `structure`, which would have
  put `n : ℕ` data into Prop and fail projection generation). Composes cleanly.
- `cycleStarDarts_card_eq_two_of_mem` needs `M.IsSimpleGraph` (the `no_parallel` field) to turn
  equal edges into α-`SameCycle` — added as an explicit hypothesis (a genuine input, the cycle
  lives in a simple graph; not a smuggled difficulty).

## Statements proven (all UNCONDITIONAL, clean-3)

**Brick 1 — Star API**
- `StarDart M x := {d // M.tail d = x}` (+ Fintype, DecidableEq instances)
- `starSigma M x : Equiv.Perm (StarDart M x)` (σ restricted; `starSigma_coe` simp)
- `starFace x d := M.dartFace d.1`
- `starFace_next_eq_alpha` — the key local identity (above)
- `starStep_chordSplitAdj_of_not_seam` — non-seam step ⇒ ChordSplitAdj between star faces
- `star_side₁_next_iff_of_not_seam` — side₁ membership invariant across a non-seam star step
  (via `data.side₁_closed` + `chordSplitAdj_symm`)

**Brick 2 — Cycle-star incidence**
- `CycleVertexMem`, `CycleStarDart`, `cycleStarDarts` (`Finset.univ.filter`, classical dec)
- `cut_dart_eq_forward_or_reverse` — a cut dart is `C.dart i` (tail=x) or `α(C.dart i)` (head=x)
- `cycleStarDarts_card_eq_zero_of_not_mem` — x∉cycle ⇒ 0 cut darts
- `StarTwoCuts` structure + `starTwoCuts_of_cycle_mem` — the two cuts are the LEAVING forward
  dart `C.dart j` and the ENTERING reverse dart `α(C.dart (prevIdx j))`; distinct via
  `dart_ne_alpha_dart`; the `cuts_iff` characterisation uses `tail_inj` + `prevIdx/nextIdx`
- `cycleStarDarts_eq_pair`, `cycleStarDarts_card_eq_two_of_mem` — exactly 2 cut darts at a
  cycle vertex (`Finset.card_eq_two` from the pair)

**Brick 3 — Cut-free rotation walks**
- `RotationArcWithoutCuts ρ Cut a b` (∃-def)
- `side_constant_on_cutFree_walk` — **the abstract export** (any ρ/Cut/Side + Inv ⇒ constant on
  cut-free walk; induction on n via `Function.iterate_succ_apply'`). Axioms: `{propext, Quot.sound}`.
- `starSide₁_constant_on_cut_free_walk` — seam-instantiated specialisation
- `starSigma_iterate_coe`, `starSigma_reaches` — star-orbit transitivity: any two darts at a
  vertex are starSigma-iterates (σ-orbit = full star), via `SameCycle.exists_nat_pow_eq` +
  `Equiv.Perm.coe_pow`. This is what gives reachability for the escape lemma's arbitrary target.
- `side_escape_crosses_cut` (abstract) + `star_escape_crosses_seam` (seam-instantiated):
  side a ∧ ¬side b ⇒ the orbit walk a→b crosses a cut/seam.

## Axiom audit

All 8 main results: `[propext, Classical.choice, Quot.sound]`
(`side_constant_on_cutFree_walk` even tighter: `[propext, Quot.sound]`).
No `sorry`/`admit`/`axiom`/`native_decide`.

## Non-vacuity

No residue hypothesis is exposed; bricks 1–3 are fully unconditional. Hypotheses
(`IsSimpleGraph`, `CycleVertexMem`, `RotationArcWithoutCuts`) are inhabited statements about
concrete data, not unsatisfiable premises. The abstract brick-3 lemmas are universally
quantified over genuine permutations.
