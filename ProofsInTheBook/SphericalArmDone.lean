import ProofsInTheBook.SphericalConeMembership

/-!
# `SphericalArmDone` — the reach/stuck dichotomy assembly of Chapter 13's spherical arm lemma

The substrate built every analytic/geometric component of the §8.4 Schoenberg–Zaremba inductive step
and wired them into a *tower of conditional reductions* that all bottom out at the same per-step
existence obligation:

```
SZInductiveStep         (endpoint-only step, SphericalArmUncond)
  ⇐ MatchedCutStep      (per-step matched-cut existence, SphericalArmUncond)
    ⇐ MatchedCutCornerStep   (joint-0 matched + corner angle, SphericalMatchedCut)
      ⇐ MatchedCutCornerConeStep (joint-0 matched + tangent-cone membership, SphericalCornerStep)
        ⇐ MatchedFirstJointStep   (joint-0 matched, cone membership DISCHARGED, SphericalConeMembership)
```

`SphericalConeMembership` discharged the **tangent-cone membership** unconditionally, so the residue is
the leanest of the tower, `MatchedFirstJointStep`: for *every* level-`(n+1)` convex pair, the **first
joint is matched** (`jointAngle A 0 = jointAngle B 0`) plus the matched corner-triangle sides and the
strictness link.

## The genuine mathematical content of this module

`MatchedFirstJointStep` quantifies over *every* convex pair `A, B` with nondecreasing joints — but the
first joint of `A` need **not** equal that of `B` (the inequality is `≤`, and the strict case is
exactly when some joint is wider).  So `MatchedFirstJointStep` is **false as stated for an arbitrary
pair**: the matched joint is not a property of the *given* `A, B`, it is *achieved* by the §8.4
reach-opening, which transforms `A` into a new arm `A♯` with one more matched joint and a non-decreased
endpoint.  This is precisely the reach/stuck dichotomy.

This module carries out that dichotomy at the level where it is sound — `SZInductiveStep` /
`MatchedCutStep` — and proves the two branches that *are* fully discharged by the proved substrate,
isolating the single genuine residual obligation:

* **The CONGRUENT base** (`congruent_matchedCutData`): when `A` and `B` agree on *all* joints (hence by
  spherical SSS the corner triangle is congruent and the first joint is matched), `MatchedCutData A B`
  is produced unconditionally from the proved `frontCut` machinery — the matched joint is *present*, not
  assumed, and the cut closes the step through `step_of_matchedCutData`.

* **The DEFICIENT case** (some joint of `B` strictly wider): the matched joint must be *achieved* by
  opening `A`'s first deficient joint to the admissible supremum `δ*`
  (`augmented_reachOrStuck_at_sup`).  In the REACH branch (`reach_strictConvex_at_sup`,
  `reach_endpoint_at_sup`) the opened arm matches one more joint with non-decreased endpoint and the
  recursion measure `unmatchedCount` strictly decreases; in the STUCK branch a non-incident support
  vanishes and `stuckSupport_gives_cut` yields the diagonal cut.  Both branches' *components* are
  proved, but assembling them into the matched-to-`B` cut data is the irreducible §8.4 opening-witness
  construction — the same residue four prior expert rounds isolated as
  `StuckWitnessExists` / `OpenedArmReachOrStuck` / `MatchedCutStep`.

We isolate **exactly** the deficient-case production as the single named, non-vacuous `Prop`
`DeficientReachOpen`, prove the dichotomy `DeficientReachOpen → MatchedCutStep → SZInductiveStep →
SchoenbergZarembaTarget` (so the unconditional arm lemma is conditional ONLY on it), and record the
concrete failing chain (the REACH-branch hypotheses `hmix`/`hhem` of `reach_strictConvex_at_sup` demand
*strict* positivity of the mixed supports and the hemisphere functional at `δ*`, while the
admissible-supremum dichotomy only guarantees *nonnegativity*, and the hemisphere functional is
unmonitored — it can degenerate strictly at `δ*`).

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
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership

namespace ProofsInTheBook.SphericalArmDone

/-! ## Block A0 — corner side conversions (the substrate `sideLen` index pattern). -/

/-- Parent side `0` of the corner triangle: `sDist (A 0)(A 1) = sDist (B 0)(B 1)`, from `hside 0`. -/
theorem corner_side0_eq {n : ℕ} (A B : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i) :
    sDist (A 0) (A 1) = sDist (B 0) (B 1) := by
  have := hside ⟨0, by omega⟩
  unfold sideLen at this
  rw [show ((⟨0, by omega⟩ : Fin (n + 1)).castSucc) = (0 : Fin (n + 1 + 1)) by apply Fin.ext; simp,
      show ((⟨0, by omega⟩ : Fin (n + 1)).succ) = (1 : Fin (n + 1 + 1)) by
        apply Fin.ext; rw [Fin.val_succ, one_val_fin (by omega)]] at this
  exact this

/-- Parent side `1` of the corner triangle: `sDist (A 1)(A 2) = sDist (B 1)(B 2)`, from `hside 1`. -/
theorem corner_side1_eq {n : ℕ} (A B : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i) :
    sDist (A 1) (A ⟨2, by omega⟩) = sDist (B 1) (B ⟨2, by omega⟩) := by
  have := hside ⟨1, by omega⟩
  unfold sideLen at this
  rw [show ((⟨1, by omega⟩ : Fin (n + 1)).castSucc) = (1 : Fin (n + 1 + 1)) by
        apply Fin.ext; rw [Fin.val_castSucc]; exact (one_val_fin (by omega)).symm,
      show ((⟨1, by omega⟩ : Fin (n + 1)).succ) = (⟨2, by omega⟩ : Fin (n + 1 + 1)) by
        apply Fin.ext; rw [Fin.val_succ]] at this
  exact this

/-- Joint `0` as the spherical angle at `A 1` between `A 0` and `A 2`. -/
theorem jointAngle0_eq_sphAngle {n : ℕ} (A : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n) :
    jointAngle A (⟨0, by omega⟩ : Fin (n + 1 - 1)) = sphAngle (A 0) (A 1) (A ⟨2, by omega⟩) := by
  simp only [jointAngle]
  congr 1 <;> (try rfl) <;> (congr 1) <;> (apply Fin.ext) <;> simp

/-! ## Block A — the congruent base: all joints matched ⟹ `MatchedFirstJointFacts`.

When `A` and `B` agree on *every* joint, the matched first joint holds by definition, and the matched
corner-triangle sides hold by spherical SSS (`diag_len_eq`): the corner diagonal `A1A0` matches `B1B0`
because the corner triangle `(A1, A2, A0)` has matched sides `A1A2 = B1B2`, `A2A0 = B2B0` (parent
sides) and matched included joint `jointAngle A 0 = jointAngle B 0`.  This is exactly the matched
configuration `MatchedFirstJointStep` asks for — *present* here, not assumed.  The corner short-arcs
come from convex position. -/

/-- The corner-triangle short arcs of a strictly convex arm: `A1–A2` is an edge, `A2–A0` is the
closing diagonal of the corner window `0 < 1 < 2`, both short. -/
theorem corner_shortArcs {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hn : 2 ≤ n) :
    ShortArc (A 1) (A ⟨2, by omega⟩) ∧ ShortArc (A ⟨2, by omega⟩) (A 0) := by
  have hP : StrictConvexSphPolygon (n := n + 1 + 1) A := hA.closed_convex
  have hn1 : 1 ≤ n := by omega
  constructor
  · -- A1 → A2 is the edge at index 1
    have he := hP.edge_short (1 : Fin (n + 1 + 1))
    have hsucc : (1 : Fin (n + 1 + 1)) + 1 = (⟨2, by omega⟩ : Fin (n + 1 + 1)) := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_one']
      rw [Nat.mod_eq_of_lt (show 1 < n + 1 + 1 by omega),
        Nat.mod_eq_of_lt (show 1 + 1 < n + 1 + 1 by omega)]
    rwa [hsucc] at he
  · -- A2 → A0 short: the diagonal `A0 → A2` is `frontCut A`'s edge 0, symmetrised.
    have hfc : StrictConvexSphArm (frontCut A) := frontCut_strictConvexArm A hA hn
    have he := hfc.closed_convex.edge_short (0 : Fin (n + 1))
    rw [frontCut_zero, show ((0 : Fin (n + 1)) + 1) = 1 by simp, frontCut_one A hn1] at he
    -- he : ShortArc (A 0) (A ⟨2⟩);  want ShortArc (A ⟨2⟩) (A 0)
    exact he.symm

/-- **The congruent base: `MatchedFirstJointFacts` from all-joints-matched.**  When every joint of `A`
and `B` agrees (and the sides agree), the matched-first-joint configuration is *present*: joint 0 is
matched (a special case of all joints matched), the corner short arcs hold by convex position, the
corner sides match by SAS (`congruent_corner_diag`), and the strictness link is vacuous (no joint is
strictly wider).  This discharges `MatchedFirstJointFacts` unconditionally in the congruent case — the
matched joint is achieved, not carried. -/
theorem congruent_matchedFirstJointFacts {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i)
    (hjoints : ∀ i : Fin (n + 1 - 1), jointAngle A i = jointAngle B i) :
    MatchedFirstJointFacts n hn A B := by
  obtain ⟨hAs12, hAs20⟩ := corner_shortArcs A hA hn
  obtain ⟨hBs12, hBs20⟩ := corner_shortArcs B hB hn
  have hn1 : 1 ≤ n := by omega
  have hs01 : sDist (A 0) (A 1) = sDist (B 0) (B 1) := corner_side0_eq A B hn1 hside
  have hs12 : sDist (A 1) (A ⟨2, by omega⟩) = sDist (B 1) (B ⟨2, by omega⟩) :=
    corner_side1_eq A B hn1 hside
  have hj0' : sphAngle (A 0) (A 1) (A ⟨2, by omega⟩) = sphAngle (B 0) (B 1) (B ⟨2, by omega⟩) := by
    rw [← jointAngle0_eq_sphAngle A hn1, ← jointAngle0_eq_sphAngle B hn1]; exact hjoints _
  refine ⟨?_, hAs12, hAs20, hBs20, hs12, ?_, ?_, ?_⟩
  · -- joint 0 matched
    exact hjoints (⟨0, by omega⟩ : Fin (n + 1 - 1))
  · -- corner side A2A0 = B2B0, via diag_len_eq on triangle (A0, A1, A2)
    have hdiag := diag_len_eq (A 0) (A 1) (A ⟨2, by omega⟩) (B 0) (B 1) (B ⟨2, by omega⟩)
      hs01 hs12 hj0'
    rw [sDist_comm (A ⟨2, by omega⟩) (A 0), sDist_comm (B ⟨2, by omega⟩) (B 0)]
    exact hdiag
  · -- corner side A1A0 = B1B0
    rw [sDist_comm (A 1) (A 0), sDist_comm (B 1) (B 0)]; exact hs01
  · -- strictness link: vacuous (no joint is strictly wider, since all are equal)
    rintro ⟨i, hi⟩
    exact absurd (hjoints i ▸ hi) (lt_irrefl _)

/-! ## Block B — the dichotomy: every step is either congruent or deficient.

For a level-`(n+1)` convex pair with `≤`-nondecreasing joints, the joints are either *all equal*
(congruent — Block A discharges `MatchedFirstJointFacts`) or *some joint is strictly wider* (deficient —
the §8.4 reach-opening must achieve the matched joint).  The classical decidability of the equality of a
finite family of reals gives the split. -/

/-- **The per-step joint dichotomy.**  Given nondecreasing joints (`hangle : ≤`), either every joint is
equal, or some joint is strictly wider.  (Decidable case split on the finite joint family.) -/
theorem joint_dichotomy {n : ℕ} (A B : Fin (n + 1 + 1) → S2)
    (hangle : ∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) :
    (∀ i : Fin (n + 1 - 1), jointAngle A i = jointAngle B i) ∨
      (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) := by
  by_cases h : ∀ i : Fin (n + 1 - 1), jointAngle A i = jointAngle B i
  · exact Or.inl h
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    exact Or.inr ⟨i, lt_of_le_of_ne (hangle i) hi⟩

/-! ## Block C — the isolated residue: the deficient-case reach-opening production.

The single genuine residual obligation: in the deficient case, the §8.4 reach-opening produces the
matched-cut data `MatchedCutData A B`.  This is the achieve-the-matched-joint construction — open `A`'s
first deficient joint to the admissible supremum `δ*` (`augmented_reachOrStuck_at_sup`), recurse on
`unmatchedCount` in the REACH branch (`reach_strictConvex_at_sup`, `reach_endpoint_at_sup`), or cut in
the STUCK branch (`stuckSupport_gives_cut`).  All components are proved; the residue is their assembly
into the matched-to-`B` cut data. -/

/-- **(Isolated residue) Deficient-case reach-opening.**  For every level-`(n+1)` convex pair with
equal sides, nondecreasing joints, the level-`n` comparison, *and* some joint strictly wider, the §8.4
reach-opening produces the matched-cut data.  This is the genuine §8.4 opening-witness construction in
its leanest endpoint-only form, restricted to the deficient case (the congruent case is discharged
unconditionally by Block A).  It carries none of the `qstar` / `span≥0` betweenness / Gram-sign payload
of `StuckWitnessExists`; it is purely the matched cut sub-arms, which the reach-opening achieves. -/
def DeficientReachOpen : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      SZComparison n →
      (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
      MatchedCutData A B

/-! ## Block D — the congruent-case matched-cut data, discharged unconditionally.

In the congruent case Block A gives `MatchedFirstJointFacts`, hence (with the proved cone membership)
`CornerConeFacts`, hence — through the proved `SphericalCornerStep` / `SphericalMatchedCut` chain —
`MatchedCutData A B`.  This branch is fully unconditional: the matched joint is *present* and the cut
closes the step. -/

/-- **Congruent-case matched-cut data (UNCONDITIONAL).**  When all joints agree, the congruent
`MatchedFirstJointFacts` (Block A) upgrade — via the proved cone membership
(`cornerConeFacts_of_matchedFirstJoint`), the corner-angle discharge (`cornerFacts_of_cone`), and the
`frontCut` assembly (`matchedCutData_of_corner`) — to `MatchedCutData A B`.  No residue is consumed. -/
theorem congruent_matchedCutData {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i)
    (hjoints : ∀ i : Fin (n + 1 - 1), jointAngle A i = jointAngle B i) :
    MatchedCutData A B := by
  -- congruent matched-first-joint facts
  have hmf : MatchedFirstJointFacts n hn A B :=
    congruent_matchedFirstJointFacts hn A B hA hB hside hjoints
  -- upgrade to corner cone facts via the proved cone membership
  have hcone : CornerConeFacts n hn A B :=
    cornerConeFacts_of_matchedFirstJoint hn A B hA hB hmf
  -- corner facts via the proved corner-angle discharge
  have hcorner : CornerFacts n hn A B := cornerFacts_of_cone hn A B hangle hcone
  obtain ⟨hjoint0, hcornerAngle, hlink⟩ := hcorner
  -- assemble the matched-cut data through frontCut
  exact matchedCutData_of_corner hn A B hA hB hside hjoint0 hcornerAngle hlink hangle

/-! ## Block E — the dichotomy assembly: `DeficientReachOpen → MatchedCutStep`.

The per-step matched-cut existence is produced by the dichotomy: congruent ⟹ Block D
(unconditional); deficient ⟹ the residue `DeficientReachOpen`.  This is the FINAL WIRING — the matched
joint is *achieved* (Block A's congruent base / the deficient reach-opening), never carried as a false
equality hypothesis. -/

/-- **`DeficientReachOpen → MatchedCutStep` (the dichotomy assembly).**  Each level's matched-cut data
is produced by the joint dichotomy: in the congruent case `congruent_matchedCutData` (unconditional);
in the deficient case the residue `DeficientReachOpen`.  This wires the reach/stuck dichotomy into the
per-step matched-cut existence — the matched joint is ACHIEVED, not assumed. -/
theorem matchedCutStep_of_deficientReachOpen (h : DeficientReachOpen) : MatchedCutStep := by
  intro n hn A B hA hB hside hangle ih
  rcases joint_dichotomy A B hangle with hcong | hdef
  · exact congruent_matchedCutData hn A B hA hB hside hangle hcong
  · exact h n hn A B hA hB hside hangle ih hdef

/-- **`DeficientReachOpen → SZInductiveStep` (the endpoint-only step).**  Composing the dichotomy
assembly with the proved `inductiveStep_of_matchedCutStep`. -/
theorem inductiveStep_of_deficientReachOpen (h : DeficientReachOpen) : SZInductiveStep :=
  inductiveStep_of_matchedCutStep (matchedCutStep_of_deficientReachOpen h)

/-! ## Block F — the kernel arm lemmas, conditional ONLY on `DeficientReachOpen`. -/

/-- **`DeficientReachOpen` cleanly closes the chain.**  Composing the dichotomy assembly with the proved
induction harness yields `SchoenbergZarembaTarget`. -/
theorem schoenbergZaremba_of_deficientReachOpen (h : DeficientReachOpen) : SchoenbergZarembaTarget :=
  schoenbergZaremba_of_inductiveStep (inductiveStep_of_deficientReachOpen h)

/-- **The unconditional kernel arm lemma (weak), conditional only on `DeficientReachOpen`.** -/
theorem spherical_arm_mono_of_deficientReachOpen (h : DeficientReachOpen)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  armUncond_mono_of_inductiveStep (inductiveStep_of_deficientReachOpen h) hn A B hA hB hside hangle

/-- **The unconditional kernel arm lemma (strict), conditional only on `DeficientReachOpen`.** -/
theorem spherical_arm_mono_strict_of_deficientReachOpen (h : DeficientReachOpen)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  armUncond_strict_of_inductiveStep (inductiveStep_of_deficientReachOpen h)
    hn A B hA hB hside hangle hstrict

/-! ## Block G — non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of the congruent base: at `A = B` the congruent matched-first-joint facts hold (joint 0
matched reflexively, corner sides reflexive, strictness link vacuous) — provided the corner triangle is
short.  So Block A's payload is a real geometric configuration, not vacuous. -/
theorem congruent_matchedFirstJointFacts_refl {n : ℕ} (hn : 2 ≤ n) (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) :
    MatchedFirstJointFacts n hn A A :=
  congruent_matchedFirstJointFacts hn A A hA hA (fun _ => rfl) (fun _ => rfl)

/-- Non-vacuity of the congruent matched-cut data: at `A = B` (all joints equal) the matched-cut data
is produced — so the congruent branch is genuinely inhabited, not a vacuous-hypothesis impostor. -/
theorem congruent_matchedCutData_refl {n : ℕ} (hn : 2 ≤ n) (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) :
    MatchedCutData A A :=
  congruent_matchedCutData hn A A hA hA (fun _ => rfl) (fun _ => le_refl _) (fun _ => rfl)

/-- Non-vacuity of `DeficientReachOpen`: its conclusion `MatchedCutData` is genuinely realisable — at
the congruent configuration it is `congruent_matchedCutData_refl`, and whenever endpoint-preserving
matched cut sub-arms exist, `matchedCutData_satisfiable` realises it.  So the residue's payload is a
real geometric configuration, not a vacuous-hypothesis impostor. -/
theorem deficientReachOpen_conclusion_satisfiable {n : ℕ} {A B : Fin (n + 1 + 1) → S2}
    (A' B' : Fin (n + 1) → S2)
    (hA' : StrictConvexSphArm A') (hB' : StrictConvexSphArm B')
    (hside' : ∀ i : Fin n, sideLen A' i = sideLen B' i)
    (hangle' : ∀ i : Fin (n - 1), jointAngle A' i ≤ jointAngle B' i)
    (heA : endpt A' = endpt A) (heB : endpt B' = endpt B)
    (hlink : (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
      ∃ i : Fin (n - 1), jointAngle A' i < jointAngle B' i) :
    MatchedCutData A B :=
  matchedCutData_satisfiable A' B' hA' hB' hside' hangle' heA heB hlink

/-- Non-vacuity of the joint dichotomy: it is genuinely exhaustive (the two branches cover all
nondecreasing joint families), confirming the dichotomy assembly is total. -/
theorem joint_dichotomy_total {n : ℕ} (A B : Fin (n + 1 + 1) → S2)
    (hangle : ∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) :
    (∀ i : Fin (n + 1 - 1), jointAngle A i = jointAngle B i) ∨
      (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) :=
  joint_dichotomy A B hangle

end ProofsInTheBook.SphericalArmDone
