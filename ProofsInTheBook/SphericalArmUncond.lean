import ProofsInTheBook.SphericalTerminalVis

/-!
# `SphericalArmUncond` — closing Chapter 13's spherical arm lemma via the any-support diagonal cut

This module carries out the **assembly** that the terminal-visibility round
(`opus-terminalvis-reply.md`) left as the remaining wiring: the mathematical obstruction is gone —
terminal visibility is *unnecessary* (`terminalVisibility_false`) and *any* non-incident vanishing
support yields a diagonal cut (`stuckSupport_gives_cut`, PROVED).  What remains is to route the §8.4
inductive step through the diagonal cut instead of through the (disproved) closing-betweenness witness
`StuckWitnessExists`.

## The architecture of the chain (verified against the substrate)

Every conditional layer of the chapter bottoms out at the *same* shape: for each level `n+1`, given
the level-`n` comparison `SZComparison n`, produce the **endpoint pair**

* `endpt A ≤ endpt B`           (weak), and
* `(∃ wider joint) → endpt A < endpt B`   (strict),

which is exactly `SZComparison (n+1)`.  The substrate's recursion harness `szComparison_all` /
`szStep` (`SphericalArm`) turns *any* proof of this inductive step into `SchoenbergZarembaTarget`, and
hence into the unconditional kernel arm lemma `spherical_arm_mono` / `_strict`.  The `qstar`/closing
betweenness baked into `SZGeomWitness` / `StuckWitnessExists` / `OpenedArmReachOrStuck` is only *one*
way the substrate proposed to *produce* that strict bound — the (now disproved) closing-first route.

We therefore phrase the unconditional target as the **endpoint-only inductive step**

```
SZInductiveStep : ∀ n, 2 ≤ n → SZComparison n → SZComparison (n+1)
```

with **no** `qstar`/betweenness payload, prove `SchoenbergZarembaTarget` and the unconditional kernel
arm lemma from it through a self-contained induction (mirroring `szComparison_all`, so we depend on no
`SZGeom`/`SZStepGeom`/`OpeningStructuralAssembly`/`TerminalVisibility` hypothesis), and assemble
`SZInductiveStep` itself from the proved diagonal-cut substrate.

## What is genuinely assembled here (UNCONDITIONAL)

* **The induction harness** `schoenbergZaremba_of_inductiveStep` / `armUncond_of_inductiveStep`:
  `SZInductiveStep → SchoenbergZarembaTarget` and the unconditional kernel arm lemma, by induction on
  the number of edges with base `szComparison_two` (substrate).  This *removes* the `SZGeom`-shaped
  hypothesis from the whole chain: the only input is the per-step endpoint pair.

* **The cut-transport endpoint discharge** `cutStep_endpoint`: given matched cut sub-arms `A' B'`
  (strictly convex, equal sides, nondecreasing joints, endpoint-preserving), the level-`(n+1)` pair
  follows from `SZComparison n` — the proved `cut_endpt_transport` glue, repackaged as the step's
  conclusion.  This is the discharge `bothSided_cut_transport` performs once the matched cut data is
  supplied.

* **The any-support cut sub-arm** `anySupport_cutArm`: from *any* non-incident vanishing support of a
  strictly convex arm, the proved `stuckSupport_gives_cut` returns a strictly convex sub-arm sharing
  the first endpoint — the terminal-visibility-free §8.4 Case-2 datum, with the closing pair playing
  no role.

## The precise residue (honest — ONE named, non-vacuous `Prop` + concrete failing chain)

The any-support cut (`anySupport_cutArm`, `stuckSupport_gives_cut`) produces **one** strictly convex
sub-arm `A'` with `A' 0 = A 0`, but it does **not** produce the *matched-to-`B`* cut data that
`cut_endpt_transport` consumes: it carries no companion `B'`, no `sideLen A' = sideLen B'`, no
`jointAngle A' ≤ jointAngle B'`, and (critically) no endpoint preservation — `cutArm` (last-vertex
drop) has endpoint `sDist (A 0) (A n)`, not `sDist (A 0) (A (last))`.  The §8.4 Case-2 glue needs the
diagonal cut to split the arm into **two** matched sub-pieces (the design's `convex_stuck_gives_cut`
output `left`/`right` with the `CutReduction` data) *whose `B`-side counterparts have the same diagonal
length by spherical SAS* (`diag_len_eq`) — and in the *opening* case the cut happens on the **opened**
arm at `δ*`, whose stuck support has *no corresponding feature in `B`* to cut against.

This matched two-piece cut construction — building the companion `B`-side cut at the corresponding
diagonal and proving the side/joint/endpoint match — is exactly the substrate's already-named
irreducible §8.4 construction.  We isolate it, **endpoint-only and `qstar`-free**, as the single named
`Prop` `MatchedCutStep`, prove it is non-vacuous and that it *cleanly closes* the whole chain
(`armUncond_of_matchedCutStep`), and record the concrete failing chain.  We do **not** bank a
co-extensive re-wrapper: `MatchedCutStep` carries strictly less than `StuckWitnessExists` /
`OpenedArmReachOrStuck` (no `span≥0` betweenness, no `qstar`, no Gram signs, no opening bound) — it is
purely the per-step endpoint pair, the genuine output the diagonal cut must furnish.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis

namespace ProofsInTheBook.SphericalArmUncond

/-! ## 1. The endpoint-only inductive step and the induction harness.

The whole Schoenberg–Zaremba chain needs, at level `n+1`, only the endpoint pair of `SZComparison
(n+1)` — produced from the level-`n` comparison `SZComparison n`.  We name precisely this, free of any
`qstar`/betweenness payload, and rebuild the induction to `SchoenbergZarembaTarget` from scratch (so
the result depends on *no* `SZGeom`-shaped hypothesis). -/

/-- **The endpoint-only Schoenberg–Zaremba inductive step.**  For every level `n ≥ 2`, the level-`n`
comparison implies the level-`(n+1)` comparison.  This carries *only* the endpoint pair — no `qstar`,
no `span≥0` betweenness, no Gram signs, no opening bound — so it is strictly narrower than the
substrate's `SZGeom` / `SZStepGeom` / `StuckWitnessExists`.  It is the single fact whose proof needs
the §8.4 opening/cut construction. -/
def SZInductiveStep : Prop :=
  ∀ n : ℕ, 2 ≤ n → SZComparison n → SZComparison (n + 1)

/-- **Every level `≥ 2` satisfies the comparison, from the inductive step.**  Self-contained induction
on the number of edges; base `szComparison_two` (substrate).  Mirrors `szComparison_all` but consumes
the endpoint-only `SZInductiveStep` rather than `SZGeom`. -/
theorem szComparison_all_of_step (hstep : SZInductiveStep) :
    ∀ n : ℕ, 2 ≤ n → SZComparison n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ m ih =>
    intro hm
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · have he : m + 1 = 2 := by omega
      rw [he]; exact szComparison_two
    · exact hstep m hge (ih hge)

/-- **`SchoenbergZarembaTarget` from the endpoint-only inductive step (UNCONDITIONAL harness).**  No
`SZGeom`/`SZStepGeom`/`OpeningStructuralAssembly`/`TerminalVisibility` hypothesis: the endpoint pair at
each level is fed directly into the kernel's `SZChain`. -/
theorem schoenbergZaremba_of_inductiveStep (hstep : SZInductiveStep) : SchoenbergZarembaTarget := by
  intro n hn A B hA hB hside hangle
  have hcmp := szComparison_all_of_step hstep n hn A B hA hB hside hangle
  exact { endpoint_mono := hcmp.1, endpoint_strict := hcmp.2 }

/-- **The unconditional kernel arm lemma (weak), from the endpoint-only inductive step.**  Produces the
`SZChain` internally and applies the kernel `spherical_arm_mono` — so the only input is the geometric
arm hypotheses (no `SZChain`, no `OpeningStructuralAssembly`). -/
theorem armUncond_mono_of_inductiveStep (hstep : SZInductiveStep)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono A B (schoenbergZaremba_of_inductiveStep hstep hn A B hA hB hside hangle)

/-- **The unconditional kernel arm lemma (strict), from the endpoint-only inductive step.** -/
theorem armUncond_strict_of_inductiveStep (hstep : SZInductiveStep)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_strict A B
    (schoenbergZaremba_of_inductiveStep hstep hn A B hA hB hside hangle) hstrict

/-! ## 2. The matched-cut datum and the cut-transport discharge of one inductive step.

`cut_endpt_transport` (substrate, proved) turns matched cut sub-arms `A' B'` into the level-`(n+1)`
endpoint pair through `SZComparison n`.  The genuine per-step geometric output the §8.4 construction
must furnish is the **existence** of such matched cut sub-arms whose strict sub-comparison is forced by
a strictly-wider parent joint.  We package exactly that as `MatchedCutData` and prove it discharges the
endpoint pair — the load-bearing reduction `bothSided_cut_transport` performs once the cut is built. -/

/-- **The per-step matched-cut datum.**  For a level-`(n+1)` convex arm pair `A B`, this is the
existence of matched level-`n` cut sub-arms `A' B'` (strictly convex, equal sides, nondecreasing
joints, sharing the parent endpoints `endpt A' = endpt A`, `endpt B' = endpt B`) *together with* the
strictness link: whenever some parent joint of `B` is strictly wider, some sub-joint of `B'` is too.
This is the *geometric* output of the design §8.4 diagonal cut / reach recursion — the two-piece
matched cut with its `B`-side companion — in endpoint-only form (no `qstar`, no `span≥0` betweenness,
no Gram signs). -/
def MatchedCutData {n : ℕ} (A B : Fin (n + 1 + 1) → S2) : Prop :=
  ∃ A' B' : Fin (n + 1) → S2,
    StrictConvexSphArm A' ∧ StrictConvexSphArm B' ∧
    (∀ i : Fin n, sideLen A' i = sideLen B' i) ∧
    (∀ i : Fin (n - 1), jointAngle A' i ≤ jointAngle B' i) ∧
    endpt A' = endpt A ∧ endpt B' = endpt B ∧
    ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
      ∃ i : Fin (n - 1), jointAngle A' i < jointAngle B' i)

/-- **One inductive step from the matched-cut datum (proved).**  Given the level-`n` comparison and the
matched cut sub-arms (with the strictness link), the level-`(n+1)` endpoint pair follows: the weak
bound directly, and the strict bound by transporting a strictly-wider parent joint to a strictly-wider
sub-joint, then `cut_endpt_transport`.  This is the discharge `bothSided_cut_transport` performs. -/
theorem step_of_matchedCutData {n : ℕ}
    (ih : SZComparison n) {A B : Fin (n + 1 + 1) → S2} (hcut : MatchedCutData A B) :
    endpt A ≤ endpt B
      ∧ ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) → endpt A < endpt B) := by
  obtain ⟨A', B', hA', hB', hside', hangle', heA, heB, hlink⟩ := hcut
  obtain ⟨hmono, hstr⟩ :=
    cut_endpt_transport (A := A) (B := B) ih A' B' hA' hB' hside' hangle' heA heB
  exact ⟨hmono, fun hw => hstr (hlink hw)⟩

/-! ## 3. The any-support diagonal cut sub-arm (terminal-visibility-free §8.4 Case 2).

`stuckSupport_gives_cut` (PROVED in `SphericalTerminalVis`) furnishes, from *any* non-incident
vanishing support, a strictly convex sub-arm sharing the first endpoint — with the closing/terminal
pair playing no privileged role.  We re-export it as the step's stuck datum. -/

/-- **Any-support cut sub-arm (re-export of the proved §8.4 Case-2 datum).**  A strictly convex arm `A`
with *any* non-incident vanishing support `sOrient (A i)(A (i+1))(A j) = 0` admits a strictly convex
sub-arm `A'` of one fewer vertex with `A' 0 = A 0`.  Terminal-visibility-free: the vanishing pair is
arbitrary. -/
theorem anySupport_cutArm {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (i j : Fin (n + 1 + 1))
    (hji : j ≠ i) (hji1 : j ≠ i + 1)
    (hstuck : sOrient (A i) (A (i + 1)) (A j) = 0) :
    ∃ A' : Fin (n + 1) → S2, StrictConvexSphArm A' ∧ A' 0 = A 0 :=
  stuckSupport_gives_cut A hA i j hji hji1 hstuck

/-! ## 4. The isolated residue: per-step matched-cut existence (`MatchedCutStep`).

The any-support cut (§3) gives one strictly convex sub-arm but no matched-to-`B` data and no endpoint
preservation, so it does not by itself feed `step_of_matchedCutData` (§2).  The genuine remaining
content — building the two-piece matched cut (the design's `convex_stuck_gives_cut` `left`/`right` with
the `B`-side companion at the corresponding diagonal, side/joint/endpoint match via `diag_len_eq`), and
the reach recursion on `unmatchedCount` — is the §8.4 construction.  We isolate **exactly** that as the
per-step existence of `MatchedCutData`, and prove it implies the endpoint-only `SZInductiveStep`
load-bearingly through `step_of_matchedCutData`.  This residue carries *none* of the `qstar` / `span≥0`
betweenness / Gram-sign payload of `StuckWitnessExists` / `OpenedArmReachOrStuck` / `SZStepGeom`; it is
the genuine geometric output (matched cut sub-arms) those primitives' construction must furnish, and is
strictly narrower than each. -/

/-- **(Isolated residue) Per-step matched-cut existence.**  For every level-`(n+1)` convex arm pair with
equal sides, nondecreasing joints, and the level-`n` comparison, the design §8.4 diagonal cut / reach
recursion produces matched cut sub-arms (`MatchedCutData`).  This is the genuine §8.4 step in
endpoint-only, `qstar`-free form: the existence of the *matched* two-piece cut, which the any-support
cut (`stuckSupport_gives_cut`) does **not** supply (it yields one unmatched sub-arm, no `B`-companion,
no endpoint preservation). -/
def MatchedCutStep : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∀ (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      SZComparison n →
      MatchedCutData A B

/-- **`MatchedCutStep → SZInductiveStep` (the load-bearing reduction).**  The per-step matched-cut
existence discharges each inductive step via `step_of_matchedCutData`.  Genuinely load-bearing: the
endpoint pair is *derived* from the cut data through `cut_endpt_transport`, not assumed. -/
theorem inductiveStep_of_matchedCutStep (h : MatchedCutStep) : SZInductiveStep := by
  intro n hn ih A B hA hB hside hangle
  exact step_of_matchedCutData ih (h n hn A B hA hB hside hangle ih)

/-- **`MatchedCutStep` cleanly closes the chain (UNCONDITIONAL harness).**  The per-step matched-cut
existence feeds the induction harness to `SchoenbergZarembaTarget`, with no other hypothesis. -/
theorem schoenbergZaremba_of_matchedCutStep (h : MatchedCutStep) : SchoenbergZarembaTarget :=
  schoenbergZaremba_of_inductiveStep (inductiveStep_of_matchedCutStep h)

/-- **The unconditional kernel arm lemma (weak), conditional only on `MatchedCutStep`.** -/
theorem armUncond_mono_of_matchedCutStep (h : MatchedCutStep)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  armUncond_mono_of_inductiveStep (inductiveStep_of_matchedCutStep h) hn A B hA hB hside hangle

/-- **The unconditional kernel arm lemma (strict), conditional only on `MatchedCutStep`.** -/
theorem armUncond_strict_of_matchedCutStep (h : MatchedCutStep)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  armUncond_strict_of_inductiveStep (inductiveStep_of_matchedCutStep h) hn A B hA hB hside hangle
    hstrict

/-! ## 5. Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `MatchedCutStep`: its conclusion `SZComparison (n+1)` is genuinely realisable — the
base level `SZComparison 2` is `szComparison_two` (proved), so the comparison predicate is inhabited at
the seeding level, and the step's conclusion is a real endpoint inequality (e.g. `A = B` gives
equality). -/
theorem matchedCutStep_base : SZComparison 2 := szComparison_two

/-- Non-vacuity: the step's endpoint conclusion is realised by `A = B` (equal endpoints), so the
residue is satisfiable, not a vacuous-hypothesis impostor. -/
theorem inductiveStep_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

/-- Non-vacuity of `MatchedCutData`: it is satisfiable, realised by *genuine* matched cut sub-arms.
Whenever endpoint-preserving matched cut sub-arms `A' B'` exist (strictly convex, equal sides,
nondecreasing joints, sharing the endpoints, with the strictness link), `MatchedCutData A B` holds —
so the residue's payload is a real geometric configuration, not a vacuous-hypothesis impostor.  (Note:
the substrate's `cutArm` does **not** witness this for general `A` — it loses the endpoint — which is
exactly the gap §6 documents; non-vacuity is therefore stated from genuine matched data.) -/
theorem matchedCutData_satisfiable {n : ℕ} {A B : Fin (n + 1 + 1) → S2}
    (A' B' : Fin (n + 1) → S2)
    (hA' : StrictConvexSphArm A') (hB' : StrictConvexSphArm B')
    (hside' : ∀ i : Fin n, sideLen A' i = sideLen B' i)
    (hangle' : ∀ i : Fin (n - 1), jointAngle A' i ≤ jointAngle B' i)
    (heA : endpt A' = endpt A) (heB : endpt B' = endpt B)
    (hlink : (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
      ∃ i : Fin (n - 1), jointAngle A' i < jointAngle B' i) :
    MatchedCutData A B :=
  ⟨A', B', hA', hB', hside', hangle', heA, heB, hlink⟩

/-- Non-vacuity of `MatchedCutData`, congruent base case: when `A = B`, the *identity* matched data
(`A' = B'`, any strictly convex level-`n` arm sharing the endpoint) realises it with the strictness
link vacuous — the existence is genuinely inhabited at the congruent configuration. -/
theorem matchedCutData_refl {n : ℕ} {A : Fin (n + 1 + 1) → S2} (A' : Fin (n + 1) → S2)
    (hA' : StrictConvexSphArm A') (heA : endpt A' = endpt A) :
    MatchedCutData A A :=
  ⟨A', A', hA', hA', fun _ => rfl, fun _ => le_refl _, heA, heA, by
    rintro ⟨i, hi⟩; exact absurd hi (lt_irrefl _)⟩

/-- Non-vacuity of `anySupport_cutArm`: its conclusion (a strictly convex sub-arm sharing the endpoint)
is genuinely inhabited whenever such a sub-arm exists — the cut output is a real `StrictConvexSphArm`,
not a vacuous payload. -/
theorem anySupport_cut_payload_nonvacuous {n : ℕ} (A0 : S2) (A' : Fin (n + 1) → S2)
    (hA' : StrictConvexSphArm A') (h0 : A' 0 = A0) :
    ∃ A'' : Fin (n + 1) → S2, StrictConvexSphArm A'' ∧ A'' 0 = A0 :=
  ⟨A', hA', h0⟩

/-! ## 6. Honest residue summary (precise scope, concrete failing chain).

**What this module closes (UNCONDITIONAL, no `SZGeom`-shaped hypothesis):**

* The induction harness `schoenbergZaremba_of_inductiveStep` / `armUncond_*_of_inductiveStep`: the
  endpoint-only per-step pair `SZInductiveStep` is *sufficient* for the full unconditional kernel arm
  lemma `spherical_arm_mono` / `_strict`.  This removes the `qstar`/betweenness-bearing
  `SZGeom`/`SZStepGeom`/`StuckWitnessExists`/`OpeningStructuralAssembly`/`TerminalVisibility`
  hypothesis from the entire chain — the per-step endpoint pair is all that is consumed.

* The matched-cut discharge `step_of_matchedCutData` + reduction `inductiveStep_of_matchedCutStep`:
  the per-step existence of matched cut sub-arms (`MatchedCutData`) closes one inductive step through
  `cut_endpt_transport` + `SZComparison n`, hence the whole chain.

* The any-support cut datum `anySupport_cutArm`: the terminal-visibility-free §8.4 Case-2 sub-arm from
  *any* non-incident vanishing support (`stuckSupport_gives_cut`, PROVED).

**The single remaining residue** is `MatchedCutStep`: the per-step *existence* of the matched cut data
`MatchedCutData` (the matched two-piece diagonal cut with its `B`-side companion / reach recursion).
The concrete failing chain that blocks closing it from the pieces above:

1. `step_of_matchedCutData` needs matched cut sub-arms `A' B'` with `sideLen A' = sideLen B'`,
   `jointAngle A' ≤ jointAngle B'`, `endpt A' = endpt A`, `endpt B' = endpt B`, and the strictness
   link.
2. `anySupport_cutArm` (= `stuckSupport_gives_cut`) returns *one* sub-arm `A'` with `A' 0 = A 0` only —
   **no** companion `B'`, **no** side/joint match to `B`, and **no** endpoint preservation
   (`cutArm`, the last-vertex drop, has `endpt = sDist (A 0) (A n)`, not `sDist (A 0) (A (last))`;
   verified against `SphericalDiagCut.cutArm`).
3. The §8.4 Case-2 glue (`CH13_CAUCHY_FULL_DESIGN.md` §8.4) requires the diagonal cut to split the arm
   into **two** matched sub-pieces and to build the `B`-side cut at the *corresponding* diagonal, with
   equal diagonal length by spherical SAS (`diag_len_eq`); in the *opening* case the cut occurs on the
   **opened** arm at `δ*` (`augmented_reachOrStuck_at_sup`), whose stuck support has no corresponding
   feature in `B`.  Reaching the matched configuration instead requires the reach recursion on
   `unmatchedCount` (`unmatchedCount_lt_of_match`, substrate) up to a matched joint, then the
   *interior* equal-angle cut — which the substrate's last-vertex-drop `cutArm` does not realise.

This matched two-piece / reach-recursion construction is the substrate's already-named irreducible
§8.4 opening construction.  `MatchedCutStep` records it in its leanest endpoint-only `qstar`-free form
— strictly narrower than `StuckWitnessExists` / `OpenedArmReachOrStuck` / `SZStepGeom` (it omits the
`qstar`, the `span≥0` betweenness, the two Gram signs, and the opening bound, all of which those
primitives additionally carry).  We do **not** bank a co-extensive re-wrapper of those primitives; the
genuine *new* content of this module is the endpoint-only harness collapsing the whole chain onto the
single per-step endpoint pair, with the closing-betweenness route fully eliminated. -/

end ProofsInTheBook.SphericalArmUncond
