# Campaign Audit: Ch13 / Ch35 / Ch36

Date: 2026-06-11.  Scope: the campaign endpoints requested in
`HANDOFF/codex/audit-brief.md`, with the Ch13 tail extended through
`ZinanFFCT59/60/61` as instructed.

## Executive summary

All audited Lean endpoints are axiom-clean in the standard clean-3 sense
(`[propext, Classical.choice, Quot.sound]`; two trivial endpoint-satisfiability lemmas
use no axioms).  No new Lean file was needed.  The audit does **not** find a hidden
`False` on the final surfaces, but it does confirm that none of the three campaigns
is an unconditional book theorem.  Ch13 is an honest conditional spherical-arm
endpoint chain; FFCT61 removes the old reversed-convexity gap for tail cases `j >= 2`,
but `SupportStuckWBSImpossible` is still not proved because raw sign supply and the
tail endpoint cases `j = 0,1` remain.  Ch35 is a chord-side/Jordan/Kempe subroutine,
not the five-color theorem.  Ch36 is the closest to the book claim: it proves the
strict-simple-polygon art-gallery conclusion modulo the explicit `Esplit`, `rest`,
and `M` inputs.

## Verdict table

| Chapter | Audited headline | Verdict | Exact mod-list / blocker |
|---|---|---|---|
| Ch13 | `ProofsInTheBook.ZinanFFCT85.spherical_arm_mono_final_ch13_v10` (UPDATED Jun11 night, FFCT62-85) | CONDITIONAL-honest | ONE input: `CrossPieceNoCollisionAtSup` (the opened arm's cross-piece collision at the WBS sup — sharp, satisfiable, guarded). Everything else of the original surface was DISCHARGED across FFCT62-85 (static b-trichotomy, mirror suites, first-step interior-zero witnesses, stratified consumers). Verified clean-3, final build 8795 jobs. |
| Ch35 | `ProofsInTheBook.ZinanCh35FinalClose.chordSideResidue₁_final` | FRAGMENT | This closes one side-1 `ChordSideResidue` modulo planar inputs.  It is not the book-level five-color theorem.  Root `Chapter35.chapter35` is still the separate `FiveColorReducible` certificate theorem. |
| Ch36 | `ProofsInTheBook.ZinanCh36Assembly.artGallery_strict_mod_M` | CONDITIONAL-honest | `Esplit : EarValueSplitData`, `rest : RemainingResidualData`, and `M : DiagonalAttachInput ...`.  Root `Chapter36.chapter36` remains only the combinatorial triangulation theorem. |

## Full input surfaces

### Ch13

Final campaign headline:

```lean
theorem spherical_arm_mono_reachOnly_honest (res : Ch13ReachOnlyResidues)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n))
```

The final residue bundle is:

```lean
structure Ch13ReachOnlyResidues : Prop where
  hwpc  : WeakPositiveCutReady
  hffct : FoldedFlatCutTransportPlus
  helim : SupportStuckWBSImpossible
```

Expanded:

```lean
def WeakPositiveCutReady : Prop :=
  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
    WeakConvexSphArm A → PositiveJoints A → StrictConvexSphArm B →
    SameSides A B → JointLe A B →
    (∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (A i) (A (i + 1)) (A j) = 0) →
    CutReadyPlus A B

def SupportStuckWBSImpossible : Prop :=
  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
    StrictConvexSphArm A → StrictConvexSphArm B → ∀ k : Fin (n - 1),
    jointAngle A k < jointAngle B k → ¬ SupportStuckWBS A B k
```

`FoldedFlatCutTransportPlus` is the repaired folded-flat CUT transport: for
`n >= 2`, assuming smaller-dimensional `MainPlus`, weak/positive `A`, strict `B`,
same sides, joint monotonicity, a non-incident folded-flat span, and the corresponding
diagonal distance comparison, it concludes `endpt A <= endpt B`.

The FFCT61 tail endpoint surface is:

```lean
theorem nonAxisTailBoundaryResidue_false_of_two_le_j_mirror
    (hA'weak : WeakConvexSphArm (openedWBS A B k))
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hB : StrictConvexSphArm B)
    (hangle' : JointLe (openedWBS A B k) B)
    (hnr : NoNonadjacentRepeat (openedWBS A B k))
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    (hj2 : 2 ≤ j)
    (hres : NonAxisTailBoundaryResidue A B k i j hi hi1 hj) :
    False
```

This is a local branch kill, not a proof of `SupportStuckWBSImpossible`.

### Ch35

Final campaign headline:

```lean
def chordSideResidue₁_final (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (ci : ContiguousInterval data hsep a₀ a₁ hne)
    (hshare : ChordDisk.Side₁AnchorsShareFace data hsep a₀ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1))
    (ha₀ : M.tail a₀.1 = u) (ha₁ : M.tail a₁.1 = v)
    (pₛ qₛ : (data.sideMap₁ hsep a₀ a₁ hne).Vertex) (cpₛ cqₛ : α)
    (hLₛ : ThomassenLists
      (chordSideNearTriangulation_of_share data hsep a₀ a₁ hne hshare ci)
      pₛ qₛ (fun x => L (sideVertexToM₁ data hsep a₀ a₁ hne x)) cpₛ cqₛ)
    (H : Side₁SchoenfliesConfinementInput data hsep) :
    ChordSideResidue data hsep a₀ a₁ hne L
```

The genuinely new final bundle is:

```lean
structure Side₁SchoenfliesConfinementInput (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) : Prop where
  oppArcStarSeed : ∀ {w : M.Vertex},
    w ∈ data.arc.path₂.internalVertices → w ∉ sideRegion₁ data
  edge_core : ∀ {e : D},
    M.tail e ∈ sideRegion₁ data →
    M.head e ∈ sideRegion₁ data →
      ((e ∉ data.keptDel₁ ∧ M.α e ∉ data.keptDel₁) ∨ M.dartEdge e = s(u, v))
```

Canonical upstream supplies read in the audit:

* `side₁AnchorsShareFace_canonical` supplies `Side₁AnchorsShareFace` for canonical anchors.
* `contiguousInterval_canonical` and `contiguousInterval_of_outerTraceInputs` supply `ContiguousInterval`
  for canonical anchors under the outer-trace/simple-graph inputs.
* `ChordContiguous.chordChoice_adj` supplies the ambient chord adjacency `M.Adj u v`; the final theorem
  still carries the anchor-tail equations `ha₀`, `ha₁` to identify that edge with the side anchors.
* `hLₛ : ThomassenLists ...` remains a side-list transport input on this endpoint.

### Ch36

Final campaign headline:

```lean
theorem artGallery_strict_mod_M {n : ℕ}
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esplit : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      4 ≤ m → EarValueSplitData P ρ (ear P))
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      PolygonJordan.RemainingResidualData P ρ (ear P))
    (M : PolygonLast.DiagonalAttachInput (... triangle leaf ...))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, PolygonRayIndep.Sees P ρ (P.q v) x
```

`EarValueSplitData` is Type-valued data, not a Prop:

```lean
structure EarValueSplitData
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n) : Type where
  hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i)
  lax : LeftStrictAxioms P (cyclicPrev i) (cyclicNext i)
  rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i)
  σL : RayDirection (buildLeftPoly hdiag lax)
  σR : RayDirection (buildRightPoly hdiag rax)
  hLr : σL.r = ρ.r
  hRr : σR.r = ρ.r
```

`RemainingResidualData` is also Type-valued data: transversality, left/right strict axioms,
left/right child rays, common-ray equations, disjointness, boundary union, and diagonal
intersection for the chosen cut.

The named Prop input is `DiagonalAttachInput B`, an `AttachesTo` witness for every local
diagonal merge:

```lean
abbrev DiagonalAttachInput (B : BaseTriangleFacts) : Prop :=
  ∀ {m : ℕ} {P : StrictSimplePolygon m} {ρ : RayDirection P}
    (G : LocalCutData' P ρ) {i j : Fin m} (hdiag : IsDiagonal' P ρ i j)
    (tL : EarTriangulation' (G.leftPoly hdiag) (G.leftRay hdiag))
    (tR : EarTriangulation' (G.rightPoly hdiag) (G.rightRay hdiag))
    (gL : CombinatorialGlue B tL) (gR : CombinatorialGlue B tR),
    AttachesTo ...
```

## Hypothesis refutation pass

Verdicts use the requested three labels.  "Refuted" means an actual committed theorem gives a
counterexample or uninhabitedness.  "Satisfiable-guarded" means a committed guard/projection theorem
shows the input is a genuine consequence of a documented stronger datum or nonvacuous model.  "Satisfiable-argued"
means no constant/degenerate refutation was found at the exact quantifier scope, but the current
repo has no full producer.

| Surface item | Verdict | Evidence |
|---|---|---|
| Ch13 legacy `SpliceBodyDiagMono` | REFUTED | `ZinanFFCT58.spliceBodyDiagMono_false : ¬ SpliceBodyDiagMono`. |
| Ch13 legacy `Ch13Residues` | REFUTED | `ZinanFFCT58.ch13Residues_uninhabited : ¬ Nonempty Ch13Residues`, because it carried `SpliceBodyDiagMono`.  This is not on the final surface. |
| `WeakPositiveCutReady` | SATISFIABLE-ARGUED | Degenerate/constant arms do not satisfy the strict/positive/cut premises.  The conclusion `CutReadyPlus` is load-bearing; `weakPositiveCutReady_conclusion_satisfiable` records the real endpoint target reflexively.  No inhabitant is committed. |
| `FoldedFlatCutTransportPlus` | SATISFIABLE-ARGUED | The exact scope includes folded-flat span plus diagonal-distance comparison; constant degeneracies are blocked by weak/positive/strict hypotheses.  No counterexample is committed; no full producer is committed. |
| `SupportStuckWBSImpossible` | SATISFIABLE-ARGUED | FFCT59/61 discharge successor-edge and tail `j >= 2` non-axis residues, but raw sign supply and tail endpoints remain.  No exact-scope refutation is committed. |
| `NonAxisTailBoundaryResidue` with `2 <= j` plus FFCT61 hypotheses | REFUTED | `nonAxisTailBoundaryResidue_false_of_two_le_j_mirror`. |
| `NonAxisTailBoundaryResidue` at `j = 0` or `j = 1` | SATISFIABLE-ARGUED | FFCT61 intentionally leaves these endpoint cases; `mirror_tail_endpoint_conclusion_satisfiable` witnesses the endpoint conclusion shape is consistent. |
| Ch35 `Side₁SchoenfliesConfinementInput` | SATISFIABLE-GUARDED | `confinementInput_of_schoenflies` derives it from `ZinanCh35Schoenflies.Side₁SchoenfliesConfinement`. |
| Ch35 `ContiguousInterval` | SATISFIABLE-GUARDED | `ChordSideNT.contiguousInterval_of_nearTriangulation` and `chordSideClassification_iff_contiguous`; canonical route via `contiguousInterval_canonical` / `contiguousInterval_of_outerTraceInputs`. |
| Ch35 `Side₁AnchorsShareFace` | SATISFIABLE-GUARDED | `ZinanCh35SideAnchors.side₁AnchorsShareFace_canonical`. |
| Ch35 `M.Adj (M.tail a₀.1) (M.tail a₁.1)` and `ha₀`, `ha₁` | SATISFIABLE-ARGUED | `ChordContiguous.chordChoice_adj` gives `M.Adj u v`; the final theorem still requires the anchor-tail identifications to match this to arbitrary `a₀/a₁`.  No contradiction arises; the equations specialize to canonical anchor geometry. |
| Ch35 `ThomassenLists ...` side-list input | SATISFIABLE-ARGUED | This is the standard list-coloring precondition transported to the side map.  It is not refuted by degenerate graph instances, but the final endpoint carries it as an input. |
| Ch36 `DiagonalAttachInput` | SATISFIABLE-GUARDED at the local `AttachesTo` level | `PolygonLast.attachesTo_nonvacuous` gives a concrete two-triangle attach witness.  The universal `DiagonalAttachInput` producer is not committed. |
| Ch36 `Esplit : EarValueSplitData` | SATISFIABLE-ARGUED | Type-valued witness data; not a Prop with a direct `¬` refutation.  Constant degeneracies do not satisfy `StrictSimplePolygon`/diagonal/strict-axiom fields. |
| Ch36 `rest : RemainingResidualData` | SATISFIABLE-ARGUED | Type-valued witness data.  Existing guards (`PolygonGeomInput.polygonGeomResidue_of_oracle`, `PolygonEarExistence.isConvexVertex'_holds`) show the surrounding residue architecture is meaningful, but no full unconditional producer is committed. |

## Exfalso / absurd scan

Command:

```bash
rg -n "\\b(exfalso|absurd)\\b" \
  ProofsInTheBook/ZinanFFCT57.lean ProofsInTheBook/ZinanFFCT58.lean \
  ProofsInTheBook/ZinanFFCT59.lean ProofsInTheBook/ZinanFFCT60.lean \
  ProofsInTheBook/ZinanFFCT61.lean ProofsInTheBook/ZinanCh35FinalClose.lean \
  ProofsInTheBook/ZinanCh35Hclass.lean ProofsInTheBook/ZinanCh35OuterTrace.lean \
  ProofsInTheBook/ZinanCh35SideAnchors.lean ProofsInTheBook/ZinanCh36Assembly.lean \
  ProofsInTheBook/PolygonEarExistence.lean ProofsInTheBook/PolygonGeomInput.lean \
  ProofsInTheBook/PolygonLast.lean ProofsInTheBook/Chapter13.lean \
  ProofsInTheBook/Chapter35.lean ProofsInTheBook/Chapter36.lean
```

Relevant campaign-chain hits:

* `ZinanFFCT57.lean:199`, `ZinanFFCT58.lean:571`, `ZinanFFCT57.lean:324`: the base-stuck vanishing-support subcase is converted into a `SupportStuckWBS` witness by `supportConstraint_apply` and killed by the active non-stuck hypothesis (`hstuck`/`hnotStuck` supplied by the branch or by `SupportStuckWBSImpossible`).  This is not hypothesis smuggling; it is the branch negation being applied to the exact support-stuck witness.
* `ZinanFFCT60.lean:93` and `ZinanFFCT61.lean:478`: the adjacent reversed/mirror fold case is killed by `foldedFlat_adjacent_contradiction` after the arithmetic identifies `n - j = 2`.
* `ZinanFFCT58.lean:277`: finite-case proof of strict nonincident support for the committed counterexample; impossible index cases are closed by `decide`.
* `ZinanFFCT58.lean:333`: `realSides_eq` excludes `t = 0` via the explicit hypothesis `t ≠ 0`.
* `ZinanCh36Assembly.lean:278`: `windCross = 0` branch killed by `windCross_ne_zero_of_odd_crossing`.
* `ZinanCh36Assembly.lean:340`: boundary branch killed by the explicit `¬ OnBoundary` hypothesis.
* Root consumer hits in `Chapter13.lean` and `Chapter36.lean` are ordinary contradiction uses:
  strict inequality vs equality in the abstract arm lemma, shared-edge membership vs apex freshness,
  and single-triangle cardinality vs `S.card >= 2`.

No audited hit is a hidden discharge of a named surface hypothesis by contradiction.

Placeholder scan on the audited campaign files:

```bash
rg -n "\\bsorry\\b|\\badmit\\b|\\baxiom\\b|native_decide" \
  ProofsInTheBook/ZinanFFCT57.lean ProofsInTheBook/ZinanFFCT58.lean \
  ProofsInTheBook/ZinanFFCT59.lean ProofsInTheBook/ZinanFFCT60.lean \
  ProofsInTheBook/ZinanFFCT61.lean ProofsInTheBook/ZinanCh35FinalClose.lean \
  ProofsInTheBook/ZinanCh36Assembly.lean
```

Matches are only documentation/header text mentioning the banned words or "axiom-clean"; no proof
placeholder or new axiom declaration was found.

## Statement faithfulness

### Ch13

The campaign theorem is faithful to the **shape** of the spherical Cauchy arm endpoint monotonicity:
equal sides plus nondecreasing joints imply endpoint distance monotonicity for strict convex
spherical arms.  It is not faithful as an unconditional book lemma because the residue bundle remains.
`Chapter13.lean` itself is a separate finite-sign Cauchy rigidity certificate theorem:
`chapter13` / `chapter13_rigidity` consume `CauchyRigidityCertificate`, not the FFCT campaign theorem.

Verdict: CONDITIONAL-honest, not unconditional.

### Ch35

`chordSideResidue₁_final` is a side-1 chord reconstruction/Kempe-Jordan subroutine.  The book claim
is the five-color theorem.  The root `Chapter35.chapter35` proves `G.Colorable 5` from
`FiveColorReducible G`, and does not consume the campaign endpoint as the full planar-graph
instantiation.

Verdict: FRAGMENT.

### Ch36

`artGallery_strict_mod_M` states the geometric art-gallery conclusion for a `StrictSimplePolygon`
and a ray direction:

```lean
∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
  ∀ x : Pt, ClosedRegion' P ρ x →
    ∃ v ∈ guards, PolygonRayIndep.Sees P ρ (P.q v) x
```

This is the book-level geometric conclusion modulo the explicit `Esplit`, `rest`, and `M` inputs.
The root `Chapter36.chapter36` remains the older closed combinatorial theorem over
`TriangulatedPolygon`, so the campaign is not yet wired as the root chapter theorem.

Verdict: CONDITIONAL-honest.

## Axiom audit output

Remote command used:

```bash
scp ProofsInTheBook/ZinanFFCT57.lean ProofsInTheBook/ZinanFFCT58.lean \
  ProofsInTheBook/ZinanFFCT59.lean ProofsInTheBook/ZinanFFCT60.lean \
  ProofsInTheBook/ZinanFFCT61.lean ProofsInTheBook/ZinanCh35FinalClose.lean \
  ProofsInTheBook/ZinanCh35Hclass.lean ProofsInTheBook/ZinanCh35OuterTrace.lean \
  ProofsInTheBook/ZinanCh35SideAnchors.lean ProofsInTheBook/ZinanCh36Assembly.lean \
  uisai2:~/repos/proof_in_the_book/ProofsInTheBook/

ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean /tmp/audit_campaign_axioms.lean'
```

The three endpoint source files were also checked directly on `uisai2`:

```bash
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT61.lean'
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanCh35FinalClose.lean'
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanCh36Assembly.lean'
```

All three completed with 0 errors and printed only clean-3 axioms on their in-file audit commands.

Verbatim `#print axioms` output:

```text
'ProofsInTheBook.ZinanFFCT59.spherical_arm_mono_reachOnly_honest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ZinanFFCT59.szOpeningStepPlus_reachOnly_honest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ZinanFFCT59.spherical_arm_mono_reachOnly_honest_conclusion_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ZinanFFCT58.spherical_arm_mono_final_v2' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofsInTheBook.ZinanFFCT58.szOpeningStepPlus_honest' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofsInTheBook.ZinanFFCT58.weakPositiveCutReady_conclusion_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ZinanFFCT58.spliceBodyDiagMono_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofsInTheBook.ZinanFFCT58.ch13Residues_uninhabited' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofsInTheBook.ZinanFFCT61.mirror_tail_midFold_forces_endpoint_j' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ZinanFFCT61.nonAxisTailBoundaryResidue_forces_endpoint_j_mirror' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ZinanFFCT61.nonAxisTailBoundaryResidue_false_of_two_le_j_mirror' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ZinanFFCT61.mirror_tail_endpoint_conclusion_satisfiable' does not depend on any axioms
'ProofsInTheBook.ZinanFFCT60.rev_tail_midFold_forces_endpoint_j' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ZinanFFCT60.nonAxisTailBoundaryResidue_false_of_two_le_j_under_reversal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ZinanFFCT60.endpoint_j_conclusion_satisfiable' does not depend on any axioms
'ProofsInTheBook.ZinanCh35FinalClose.chordSideResidue₁_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofsInTheBook.ZinanCh35FinalClose.confinementInput_of_schoenflies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ZinanCh35FinalClose.homit_of_confinementInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ZinanCh35FinalClose.hreflect_of_confinementInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ChordSideNT.contiguousInterval_of_nearTriangulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ChordSideNT.chordSideClassification_iff_contiguous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ZinanCh35SideAnchors.side₁AnchorsShareFace_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ChordContiguous.chordChoice_adj' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofsInTheBook.ZinanCh35Hclass.contiguousInterval_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ZinanCh35OuterTrace.contiguousInterval_of_outerTraceInputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ZinanCh36Assembly.artGallery_strict_mod_M' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofsInTheBook.ZinanCh36Assembly.polygonGeomResidue_of_interiorValues' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ZinanCh36Assembly.EarCutData_of_interiorValues' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.ZinanCh36Assembly.rayOrientedWindData_all_of_earValueSplits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.PolygonLast.attachesTo_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofsInTheBook.PolygonEarExistence.isConvexVertex'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofsInTheBook.PolygonGeomInput.polygonGeomResidue_of_oracle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ProofsInTheBook.Chapter13.chapter13' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofsInTheBook.Chapter13.chapter13_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofsInTheBook.Chapter35.chapter35' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofsInTheBook.Chapter36.chapter36' depends on axioms: [propext, Classical.choice, Quot.sound]
```


## UPDATE 2026-06-13: Ch13 simplicity route REFUTED, true status
The FFCT88-92 "simplicity makes collision vacuous" route is DEAD: weakConvex_boundedJoints_noNonadjacentRepeat
is FALSE (FFCT93 ¬PlanarClosedWeakStrictNoRepeat via the doubled-triangle A,B,C,A,B,C -- a weak-convex
bounded-joint arm CAN wind twice and self-repeat). The FFCT88-92 conditional wrappers rest on a false Prop.
Ch13's STANDING honest headline is FFCT86 `spherical_arm_mono_final_ch13_v11 (CrossPieceCollisionEndpointAtSup)`.
The correct fix (q27 in flight): total-turning < 2*pi simplicity (the doubled triangle has 4*pi; openedWBS,
being a strict single-wind arm with the tail rotated, keeps < 2*pi), OR a continuity-to-the-sup-limit route.
NOT irreducible -- an active design+grind line.
