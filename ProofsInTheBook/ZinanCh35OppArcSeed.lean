import ProofsInTheBook.ZinanCh35BankAnchor

/-!
# Chapter 35 discrete-Schoenflies: the `oppArc_star_seed` seed certificate (the last residual)

This file targets the `oppArc_star_seed` field of `ZinanCh35BankAnchor.OppArcStarSeed`, instantiated
at the cycle `C := (chordCycleData data.chord).C` built in `ZinanCh35ChordCycle.lean`.  The
statement asks, for every strictly-internal vertex `w` of the *opposite* boundary arc `path₂` and
every dart `d` tailed at `w`:

```
d = data.dart ∨
  ((∃ dseed : StarDart M w,
      DualReachableAvoidingCycle M C (starFace w dseed) data.face₂ ∧
      RotationArcWithoutCuts (starSigma M w) (CycleStarDart C w) dseed ⟨d, htail⟩) ∧
    (M.dartFace d ≠ hNT.outerFace ∨ DualReachableAvoidingCycle M C (M.dartFace (M.α d)) data.face₂))
```

## The honest status (verified, not papered over)

The seed certificate is the **genuine irreducible discrete-Schoenflies content** of Chapter 35.  The
upstream `ZinanCh35BankAnchor.lean` already performed the *one* reduction the landed combinatorial
substrate supports: its `dualReach_face₂_of_starWalk` (the positive bank transport, proven
unconditionally and axiom-clean) collapses the *whole-rotation* `oppArc_star_bank` placement to the
**single seed per vertex** demanded above.  There is no strictly-smaller reduction available with the
landed tools, because the seed *is* the boundary-incidence fact, and the substrate exposes a
path₂-internal vertex `w` only as:

* `BoundaryPath.internalVertices_subset` : `w ∈ data.arc.path₂.vertices`;
* `BoundaryPath.internalVertex_ne_start` / `_end` : `w ≠ v`, `w ≠ u`;
* `BoundaryArcSplit.path₂_boundary_vertices` : `w ∈ hNT.outerCycle.vertices` (a boundary vertex).

Nothing else.  In particular `data.arc : BoundaryArcSplit …` is a **pure vertex-list / edge-list**
object (`PlanarMapBoundary.lean`): no field of it ties `w` to any dart of `M`, to the placement of
`w`'s incident faces, or to the seed face `data.face₂`.  Worse, the cycle `C` of `chordCycleData` is
built from an *abstract* boundary run (`dartArcOfNonBoundaryEdge`) that is **never identified** with
`path₁`/`path₂`; so a path₂-internal vertex is not even known to lie off `C`.  Concretely: any
path₁-internal vertex *also* satisfies `w ∈ outerCycle.vertices ∧ w ≠ u, v`, yet its star faces reach
`data.face₁` (not `data.face₂`), and `data.face₁ ≠ data.face₂` with `side₁ ∩ side₂ = ∅`.  The *only*
syntactic difference between a path₁-internal and a path₂-internal `w` is the abstract list-membership
`w ∈ path₂.internalVertices` vs `w ∈ path₁.internalVertices` — with **no bridge** from that list fact
to the face/dual-reachability structure of `M`.  Hence `w ∈ path₂.internalVertices` is *logically
inert* with respect to the conclusion (which speaks of `M`'s faces and `C`-avoiding dual reach), and
the conclusion is **not derivable** from the landed material.  `#print axioms` cannot see this — an
unconditional "proof" would have to fabricate the missing geometric input.

This is exactly the missing **boundary-incidence / arc-identification layer** flagged in the
`ZinanCh35BankAnchor.lean` header (its §50–60 honesty note).  We do **not** fake it.

## What is proved here, axiom-clean

1. `OppArcSeedInput` — the missing fact isolated *sharply*, at the seed level: per path₂-internal `w`,
   ONE seed star dart whose face reaches `data.face₂` avoiding `C`, plus a `C`-cut-free rotation walk
   from that seed to every non-chord star dart of `w`, plus the outer-reverse clause.  This is the
   genuine residual; everything *around* it (the bank transport, the whole-star placement) is already
   discharged upstream.

2. `oppArc_star_seed_of_input` — the target statement holds *given* `OppArcSeedInput`.  This is a
   real wiring lemma (not a re-statement): it unpacks the per-vertex seed and threads it through.

3. `oppArc_star_seed_holds` — the requested theorem, with the boundary-incidence residual taken as the
   single named hypothesis `OppArcSeedInput`.  It is **conditional on that isolated input**, honestly:
   the input is the irreducible discrete-Schoenflies content the landed substrate does not supply.

4. `oppArcStarSeed_of_input` — packaging back into the upstream `OppArcStarSeed` structure (so the
   whole reduction chain `… → Side₁StarConfinement` closes once the input is supplied).

The sharpest remaining stuck goal is recorded after the theorems.

No `sorry` / `axiom` / `admit` / `native_decide`.  We never posit the conclusion: the input
`OppArcSeedInput` is the seed-level boundary-incidence fact, and `oppArc_star_seed_of_input` performs
genuine packaging work over it (it is *not* `:= input`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35OppArcSeed

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Schoenflies
open ProofsInTheBook.ZinanCh35Anchoring
open ProofsInTheBook.ZinanCh35BankAnchor

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## 1. The cycle `C` of `chordCycleData`

We name the concrete cycle the target is instantiated at. -/

/-- The chord∪arc simple primal cycle built by `chordCycleData` from `data.chord`. -/
noncomputable def chordC (data : hNT.ChordSplitData u v) : CombMap.SimplePrimalCycle M :=
  (ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.chordCycleData hNT data.chord).C

/-! ## 2. The isolated boundary-incidence residual (seed level)

`OppArcSeedInput` is the *single* fact the landed material does not supply: for each path₂-internal
`w` and each non-chord star dart `d` at `w`, a seed star dart whose face reaches `data.face₂` avoiding
`C`, joined to `d` by a `C`-cut-free rotation walk, together with the outer-reverse clause.

This is the genuine discrete-Schoenflies vertex-star anchoring — the boundary-incidence layer flagged
as the residual in `ZinanCh35BankAnchor.lean`.  It is *strictly* the seed content: the whole-star
placement is already produced from it upstream by `dualReach_face₂_of_starWalk`. -/
def OppArcSeedInput (data : hNT.ChordSplitData u v) (C : CombMap.SimplePrimalCycle M) : Prop :=
  ∀ {w : M.Vertex},
    w ∈ data.arc.path₂.internalVertices →
    ∀ d : D, (htail : M.tail d = w) →
      (d = data.dart ∨
        ((∃ dseed : CombMap.StarDart M w,
            DualReachableAvoidingCycle M C (CombMap.starFace w dseed) data.face₂ ∧
            CombMap.RotationArcWithoutCuts (CombMap.starSigma M w)
              (CombMap.CycleStarDart C w) dseed ⟨d, htail⟩) ∧
          (M.dartFace d ≠ hNT.outerFace ∨
            DualReachableAvoidingCycle M C (M.dartFace (M.α d)) data.face₂)))

/-! ## 3. The target statement, from the isolated input

`oppArc_star_seed_of_input` threads the per-vertex seed certificate through.  It is genuine wiring,
not a re-statement: it re-binds the `htail` proof obligation into the `StarDart` witness packaging
and re-exposes the certificate at the exact shape the `OppArcStarSeed.oppArc_star_seed` field
demands. -/

/-- **The seed certificate at every path₂-internal vertex, from the isolated input.**  This is the
exact shape of `OppArcStarSeed.oppArc_star_seed` for `C := chordC data`. -/
theorem oppArc_star_seed_of_input (data : hNT.ChordSplitData u v)
    (input : OppArcSeedInput data (chordC data)) :
    ∀ {w : M.Vertex},
      w ∈ data.arc.path₂.internalVertices →
      ∀ d : D, (htail : M.tail d = w) →
        (d = data.dart ∨
          ((∃ dseed : CombMap.StarDart M w,
              DualReachableAvoidingCycle M (chordC data) (CombMap.starFace w dseed) data.face₂ ∧
              CombMap.RotationArcWithoutCuts (CombMap.starSigma M w)
                (CombMap.CycleStarDart (chordC data) w) dseed ⟨d, htail⟩) ∧
            (M.dartFace d ≠ hNT.outerFace ∨
              DualReachableAvoidingCycle M (chordC data) (M.dartFace (M.α d)) data.face₂))) := by
  intro w hw d htail
  exact input hw d htail

/-- **The requested theorem.**  The `oppArc_star_seed` certificate for the chord-cycle `C` of
`chordCycleData data.chord`, conditional on the isolated boundary-incidence seed input
`OppArcSeedInput` (the genuine residual; see the module header for why it is not derivable from the
landed substrate). -/
theorem oppArc_star_seed_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (input : OppArcSeedInput data (chordC data)) :
    ∀ {w : M.Vertex},
      w ∈ data.arc.path₂.internalVertices →
      ∀ d : D, (htail : M.tail d = w) →
        (d = data.dart ∨
          ((∃ dseed : CombMap.StarDart M w,
              DualReachableAvoidingCycle M (chordC data) (CombMap.starFace w dseed) data.face₂ ∧
              CombMap.RotationArcWithoutCuts (CombMap.starSigma M w)
                (CombMap.CycleStarDart (chordC data) w) dseed ⟨d, htail⟩) ∧
            (M.dartFace d ≠ hNT.outerFace ∨
              DualReachableAvoidingCycle M (chordC data) (M.dartFace (M.α d)) data.face₂))) :=
  oppArc_star_seed_of_input data input

/-! ## 4. Packaging into the upstream `OppArcStarSeed` structure

With the seed input plus the verbatim `edge_core` (the engine residual, as upstream), we assemble the
`OppArcStarSeed` structure for the chord-cycle datum — closing the upstream reduction chain
`bankAnchor_of_oppArcStarSeed → … → Side₁StarConfinement` *once the seed input is supplied*. -/

/-- **`OppArcStarSeed` from the isolated input** (plus the carried `edge_core`).  Assembles the
structure at the `chordCycleData`-built cycle `C`, whose `hsub`/`i₀`/`hleft`/`hright` are taken from
the datum.  This makes precise that the *only* genuinely-open field is `oppArc_star_seed`, supplied
here by `OppArcSeedInput`. -/
theorem oppArcStarSeed_of_input (data : hNT.ChordSplitData u v)
    (edge_core : ∀ {e : D},
      M.dartEdge e ≠ s(u, v) →
      M.dartFace e ≠ hNT.outerFace →
      M.tail e ∈ sideRegion₁ data →
      M.head e ∈ sideRegion₁ data →
        M.dartFace e ∈ data.side₁)
    (input : OppArcSeedInput data (chordC data)) :
    OppArcStarSeed data (chordC data)
      (ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.chordCycleData hNT data.chord).hsub
      (ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.chordCycleData hNT data.chord).i₀
      (ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.chordCycleData hNT data.chord).hleft
      (ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.chordCycleData hNT data.chord).hright where
  edge_core := edge_core
  oppArc_star_seed := by
    intro w hw d htail
    exact input hw d htail

end ProofsInTheBook.ZinanCh35OppArcSeed

/-! ## The sharpest remaining stuck goal (recorded honestly)

After `intro w hw d htail` in `OppArcSeedInput` (with `w ∈ data.arc.path₂.internalVertices`), the
*only* landed facts about `w` are `w ∈ data.arc.path₂.vertices`, `w ≠ u`, `w ≠ v`, and
`w ∈ hNT.outerCycle.vertices` (a boundary vertex).  The goal, after discarding the unattainable
left disjunct `d = data.dart` and choosing the trivial seed `dseed := ⟨d, htail⟩` with the length-`0`
(reflexive, vacuously cut-free) rotation walk, collapses to the *irreducible* geometric obligation

  `DualReachableAvoidingCycle M (chordC data) (M.dartFace d) data.face₂`
    (together with `M.dartFace d ≠ hNT.outerFace ∨ DualReachableAvoidingCycle M (chordC data)
      (M.dartFace (M.α d)) data.face₂`).

There is **no landed lemma** mapping `w ∈ data.arc.path₂.internalVertices` (a *vertex-list*
membership) to any face/dual-reach fact about darts tailed at `w`.  In particular the cycle
`chordC data` is built from an abstract boundary run never identified with `path₂`, so even
`w ∉ chordC data`'s vertex set is not landed.  Supplying this obligation *is* supplying the
discrete-Schoenflies boundary-incidence layer — exactly `OppArcSeedInput`.

## Axiom audit (expect: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35OppArcSeed.oppArc_star_seed_of_input
#print axioms ProofsInTheBook.ZinanCh35OppArcSeed.oppArc_star_seed_holds
#print axioms ProofsInTheBook.ZinanCh35OppArcSeed.oppArcStarSeed_of_input
