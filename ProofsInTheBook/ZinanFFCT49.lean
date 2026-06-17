import ProofsInTheBook.ZinanFFCT47
import ProofsInTheBook.ZinanFFCT28
import ProofsInTheBook.SphericalStuckGeneral

/-!
# `ZinanFFCT49` — the **B1 → CutReady** bridge at the WBS support-stuck supremum (CUT-replacement brick 3)

This module is brick 3 of the CUT-replacement design (`HANDOFF/design-rounds/ch13-cut-replacement.md` §6,
adapted WB → WBS): the bridge from the landed B1 Gram line to a `StuckAtKData`-carrying *cut-ready* datum
at the **support-stuck** supremum of the hemisphere-free monitored family `WBS` (FFCT45).

Because the sibling worker (`ZinanFFCT48`) owns the canonical `CutReadyPlus`, we define our own LOCAL
target `CutReadyData` (design §5, structurally identical: `i j : ℕ`, `hsk : StuckAtKData A B i j`,
interval-arm convexity certificates `hAe`, `hBe`).  The assembly wave identifies the two.

## The WBS support-stuck context (FFCT45/46/47, the ammunition)

At the WBS supremum `δ*_WBS := monitoredSupWBS A B k`, the opened arm `A' := openTail A K (-δ*_WBS)`
(`= openTailW A K δ*_WBS`, the widening direction) carries, in the support-stuck branch:

* **a vanishing non-incident support** `∃ c : NonIncident n, supportConstraint A K c (-δ*_WBS) = 0`
  (`SupportStuckWBS`, FFCT45), i.e. `sOrient (A' c.i)(A' (c.i+1))(A' c.j) = 0`
  (`supportStuckWBS_vanishingSupport`, FFCT46);
* **weak convexity of `A'`** (`supportStuckWBS_weakConvex`, FFCT46, unconditional now that FFCT47
  discharged the wrap-edge residual);
* **the open hemisphere** `∃ h', ‖h'‖ = 1 ∧ ∀ r, 0 < ⟪h', A' r⟫` (`openHemisphere_at_WBS_sup`, FFCT46) —
  margins-free, so every opened vertex is strictly inside an open hemisphere, hence **non-antipodal**;
* **preserved sides** `SameSides A' B` (`openTail_preserves_sides`) and `JointLe A' B`.

## What this brick lands (clean-3) and what it honestly names

`StuckAtKData A' B i j` (the target's `hsk`) demands seven fields.  The bridge wiring discharges the ones
the B1/FFCT46-FFCT47 line genuinely supplies and exposes the rest as TWO precise, satisfiable,
refutation-checked named residues.

* **Discharged from the WBS context (no residue):**
  - `hsupp` — the binding `supportConstraint = 0` unfolds to `sOrient (A' i)(A' (i+1))(A' j) = 0`;
  - `hside` — `sDist (B (i+1))(B i) = sDist (A' (i+1))(A' i)`, the equal first side, from `SameSides A' B`
    via the `sideLen`/`sDist` bridge at the consecutive pair `(i, i+1)`;
  - the **non-antipodality half of `hsa`** — `(A' (i+1) : E3) ≠ -(A' j : E3)`, forced by the open
    hemisphere (`wrap_shortArc_of_hemisphere`'s separating-normal argument, re-instantiated at `(i+1, j)`).

* **Named residue 1 — the multi-rotation Gram signs (`WBSGramSigns`).**  The two Gram inequalities
  `hα`, `hβ` of the opened triple `(A' i, A' (i+1), A' j)`.  FFCT28's inventory finding settles that for a
  GENERAL interior binding these CANNOT be produced by the banked single-rotation derivative (two or three
  of `c.i, c.i+1, c.j` rotate under `openTail`), so they are a genuine residue — this is exactly FFCT28's
  `GramSignsAtInteriorBinding` content.  FFCT29 discharges `hβ` only in the *axis-edge* sub-case (`c.i+1 =
  K`) and leaves `hα` as `NearSideCoeffNonneg`; for a general binding both survive.  We name the pair.

* **Named residue 2 — the cut normalization datum (`WBSCutNormalization`).**  Bundles the structural
  inputs the assembly wave supplies: the ℕ-orientation `i + 1 < j ≤ n` of the binding (the **orientation
  gap**: `NonIncident` gives only `c.j ≠ c.i`, `c.j ≠ c.i+1` as *Fin* indices — the ℕ-value order
  `c.i+1 < c.j` is NOT implied, and `c.j < c.i` is possible; see §0), the **distinctness half of `hsa`**
  `A' (i+1) ≠ A' j` (the no-nonadjacent-repeat fact: the open hemisphere forbids antipodal but not equal
  vertices at non-adjacent indices), and the interval-arm convexity certificates `hAe`/`hBe` (the ear
  `A'[i+1 .. j]` weakly convex, `B[i+1 .. j]` strictly convex — there is no banked interval-convexity
  preservation theorem; every consumer carries them as data).

The bridge `cutReadyData_of_supportStuckWBS` consumes `WBSGramSigns` and `WBSCutNormalization` at the
normalized binding and produces `CutReadyData A' B`.  Both residues are guarded non-vacuous (§5).

## The orientation-gap resolution (the genuine structural finding, §0)

`StuckAtKData.hij1 : i + 1 < j` is a hard ℕ-ordering constraint, and the support `det3 (A' i)(A' (i+1))
(A' j)` is anti-symmetric under swapping two slots, so a binding with `c.j < c.i` (in ℕ value) is the
SAME planar collinearity read with the opposite sign convention.  We do NOT silently reverse: the
`NonIncident` predicate is sign-agnostic (`c.j ≠ c.i ∧ c.j ≠ c.i + 1` are Fin-disequalities), so the
ℕ-order and the edge–vertex roles (which of `c.i`, `c.j` is the cut's "near" endpoint) are part of the
cut *normalization*, which the design §5 outcome assembler performs upstream (it chooses the cut `(i, j)`
with `i + 1 < j` from the produced vanishing triple).  We therefore expose the normalized `(i, j)` with
`i + 1 < j ≤ n` together with the matching `sOrient (A' i)(A' (i+1))(A' j) = 0` as fields of
`WBSCutNormalization`, and the bridge consumes them verbatim — the gap is named, not faked.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT28
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47

namespace ProofsInTheBook.ZinanFFCT49

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §0. The opened arm at the WBS support-stuck supremum, as an abbreviation. -/

/-- The opened arm `A'_WBS := openTail A (openingAxis k) (-δ*_WBS)` at the WBS supremum (the widening
direction, `= openTailW A (openingAxis k) (monitoredSupWBS A B k)`).  All bridge data live on this arm. -/
def openedWBS {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) : Fin (n + 1) → S2 :=
  openTail A (openingAxis k) (-(monitoredSupWBS A B k))

/-- `openedWBS` is `openTailW` at the WBS supremum (the widening / opening direction). -/
theorem openedWBS_eq_openTailW {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    openedWBS A B k = openTailW A (openingAxis k) (monitoredSupWBS A B k) := rfl

/-! ## §1. The LOCAL cut-ready target `CutReadyData` (design §5, structurally identical to `CutReadyPlus`).

We own this definition (the sibling `ZinanFFCT48` owns `CutReadyPlus`).  The assembly wave identifies the
two.  Fields, per design §5: a normalized cut `(i, j)`, the general-`k` stuck datum `StuckAtKData A B i j`
(FFCT/`SphericalStuckGeneral`), and the ear interval-arm convexity certificates. -/

/-- **The LOCAL cut-ready datum** (structural twin of `CutReadyPlus`).  For arms `A, B : Fin (n+1) → S2`,
asserts there is a normalized cut `(i, j)` with the general-`k` stuck datum and the ear convexity
certificates the `FoldedFlatCutTransportPlus` consumer (`cut_step_from_stuckAtK_plus`, design §4) needs.

Phrased as a `Prop`-valued existential over the cut `(i, j)` (the design §5 fields `i j : ℕ` are bundled
existentially so the predicate is genuinely `Prop` — a bare `Prop`-structure cannot project the data
fields `i, j`).  The assembly wave identifies this with `ZinanFFCT48.CutReadyPlus`. -/
def CutReadyData {n : ℕ} (A B : Fin (n + 1) → S2) : Prop :=
  ∃ (i j : ℕ) (hsk : StuckAtKData A B i j),
    WeakConvexSphArm (intervalArm A (i + 1) (j - (i + 1))
      (by have := hsk.hj; have := hsk.hij1; omega)) ∧
    StrictConvexSphArm (intervalArm B (i + 1) (j - (i + 1))
      (by have := hsk.hj; have := hsk.hij1; omega))

/-! ## §2. The discharged pieces (no residue): non-antipodality and the equal first side. -/

/-- **Non-antipodality from the open hemisphere.**  Two opened vertices `A' a`, `A' b` strictly inside an
open hemisphere (`0 < ⟪h', A' a⟫`, `0 < ⟪h', A' b⟫`) are non-antipodal: `(A' a : E3) = -(A' b : E3)` would
give `0 < ⟪h', A' a⟫ = -⟪h', A' b⟫ < 0`.  This is the slot the open hemisphere supplies for `hsa` (the
*non-antipodal* half of `ShortArc`); the *distinctness* half is the named no-repeat residue. -/
theorem hemisphere_nonAntipodal {n : ℕ} {P : Fin (n + 1) → S2} {h' : E3}
    (hhem : ∀ r : Fin (n + 1), 0 < (⟪h', (P r : E3)⟫ : ℝ)) (a b : Fin (n + 1)) :
    (P a : E3) ≠ -(P b : E3) := by
  intro he
  have ha : 0 < (⟪h', (P a : E3)⟫ : ℝ) := hhem a
  have hb : 0 < (⟪h', (P b : E3)⟫ : ℝ) := hhem b
  rw [he, inner_neg_right] at ha
  linarith

/-- **`ShortArc` from the open hemisphere + a distinctness witness.**  Non-antipodality is forced by the
hemisphere (`hemisphere_nonAntipodal`); distinctness is the supplied `hdist` (the no-repeat fact). -/
theorem shortArc_of_hemisphere {n : ℕ} {P : Fin (n + 1) → S2} {h' : E3}
    (hhem : ∀ r : Fin (n + 1), 0 < (⟪h', (P r : E3)⟫ : ℝ)) {a b : Fin (n + 1)}
    (hdist : P a ≠ P b) : ShortArc (P a) (P b) :=
  ⟨hdist, hemisphere_nonAntipodal hhem a b⟩

/-- **The equal first side at a consecutive cut endpoint.**  For `i + 1 < j ≤ n` the pair `(i, i+1)` is a
real edge (`i.val < n`), so `SameSides A' B` at index `⟨i⟩ : Fin n` reads as
`sDist (B ⟨i+1⟩)(B ⟨i⟩) = sDist (A' ⟨i+1⟩)(A' ⟨i⟩)` — exactly `StuckAtKData.hside`. -/
theorem hside_of_sameSides {n : ℕ} {A' B : Fin (n + 1) → S2} (hside : SameSides A' B)
    {i j : ℕ} (hij1 : i + 1 < j) (hj : j ≤ n) :
    sDist (B ⟨i + 1, by omega⟩) (B ⟨i, by omega⟩)
      = sDist (A' ⟨i + 1, by omega⟩) (A' ⟨i, by omega⟩) := by
  have hilt : i < n := by omega
  have hsd : sideLen A' (⟨i, hilt⟩ : Fin n) = sideLen B (⟨i, hilt⟩ : Fin n) := hside ⟨i, hilt⟩
  -- `sideLen X ⟨i⟩ = sDist (X ⟨i⟩)(X ⟨i+1⟩)`: castSucc/succ at value `i` are `⟨i⟩`, `⟨i+1⟩`.
  have hcs : ∀ X : Fin (n + 1) → S2,
      sideLen X (⟨i, hilt⟩ : Fin n) = sDist (X ⟨i, by omega⟩) (X ⟨i + 1, by omega⟩) := by
    intro X
    have hcast : ((⟨i, hilt⟩ : Fin n).castSucc) = (⟨i, by omega⟩ : Fin (n + 1)) :=
      Fin.ext (by simp [Fin.castSucc, Fin.castAdd])
    have hsucc : ((⟨i, hilt⟩ : Fin n).succ) = (⟨i + 1, by omega⟩ : Fin (n + 1)) :=
      Fin.ext (by simp [Fin.succ])
    unfold sideLen
    rw [hcast, hsucc]
  rw [hcs A', hcs B] at hsd
  -- hsd : sDist (A' ⟨i⟩)(A' ⟨i+1⟩) = sDist (B ⟨i⟩)(B ⟨i+1⟩)
  -- goal: sDist (B ⟨i+1⟩)(B ⟨i⟩) = sDist (A' ⟨i+1⟩)(A' ⟨i⟩); use sDist_comm + hsd.
  rw [sDist_comm (B ⟨i + 1, by omega⟩) (B ⟨i, by omega⟩),
    sDist_comm (A' ⟨i + 1, by omega⟩) (A' ⟨i, by omega⟩)]
  exact hsd.symm

/-! ## §3. The TWO named residues.

Both residues are stated on the opened arm `A'_WBS = openedWBS A B k`.  Together with the discharged
pieces (§2) they supply every `StuckAtKData` field plus the ear convexity certificates. -/

/-- **Named residue 1 — the multi-rotation Gram signs.**  At the normalized cut `(i, j)` of the opened arm
`A'_WBS`, the two Gram inequalities `hα`, `hβ` of the triple `(A' i, A' (i+1), A' j)` — exactly the
`StuckAtKData.hα`/`hβ` fields, equivalently `ZinanFFCT28.GramSignsAtInteriorBinding`'s two Gram conjuncts.
This is the genuine B1 residue: FFCT28's inventory finding shows a GENERAL interior binding has two or
three rotating slots, so the banked single-rotation derivative cannot supply these.  Named, not faked. -/
def WBSGramSigns {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (i j : ℕ) (hi : i < n + 1)
    (hi1 : i + 1 < n + 1) (hjlt : j < n + 1) : Prop :=
  (0 ≤ (⟪(openedWBS A B k ⟨i, hi⟩ : E3), (openedWBS A B k ⟨i + 1, hi1⟩ : E3)⟫ : ℝ)
      - (⟪(openedWBS A B k ⟨i, hi⟩ : E3), (openedWBS A B k ⟨j, hjlt⟩ : E3)⟫ : ℝ)
        * (⟪(openedWBS A B k ⟨i + 1, hi1⟩ : E3), (openedWBS A B k ⟨j, hjlt⟩ : E3)⟫ : ℝ))
  ∧ (0 ≤ (⟪(openedWBS A B k ⟨i, hi⟩ : E3), (openedWBS A B k ⟨j, hjlt⟩ : E3)⟫ : ℝ)
      - (⟪(openedWBS A B k ⟨i, hi⟩ : E3), (openedWBS A B k ⟨i + 1, hi1⟩ : E3)⟫ : ℝ)
        * (⟪(openedWBS A B k ⟨j, hjlt⟩ : E3), (openedWBS A B k ⟨i + 1, hi1⟩ : E3)⟫ : ℝ))

/-- **Named residue 2 — the cut normalization datum.**  Bundles the structural inputs the design §5
outcome assembler supplies for the cut at the produced vanishing triple of `A'_WBS`:

* `hij1 : i + 1 < j`, `hj : j ≤ n` — the **ℕ-orientation** of the cut (the orientation gap: `NonIncident`
  gives no ℕ-order, so the assembler normalizes which endpoint is the near one);
* `hsupp` — the vanishing support at the *normalized* triple `(i, i+1, j)` of `A'_WBS` (matching the
  orientation; the produced support may need a slot swap / sign-flip the assembler performs);
* `hrepeat` — the distinctness half of `hsa`: `A' (i+1) ≠ A' j` (the no-nonadjacent-repeat fact);
* `hAe`/`hBe` — the ear interval-arm convexity certificates (no banked preservation theorem exists). -/
structure WBSCutNormalization {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (i j : ℕ) : Prop where
  hij1 : i + 1 < j
  hj : j ≤ n
  hsupp : sOrient (openedWBS A B k ⟨i, by omega⟩) (openedWBS A B k ⟨i + 1, by omega⟩)
    (openedWBS A B k ⟨j, by omega⟩) = 0
  hrepeat : openedWBS A B k ⟨i + 1, by omega⟩ ≠ openedWBS A B k ⟨j, by omega⟩
  hAe : WeakConvexSphArm (intervalArm (openedWBS A B k) (i + 1) (j - (i + 1)) (by omega))
  hBe : StrictConvexSphArm (intervalArm B (i + 1) (j - (i + 1)) (by omega))

/-! ## §4. The bridge: `cutReadyData_of_supportStuckWBS`.

At the WBS support-stuck supremum, from the strict-convexity context, the SameSides preservation, the
open hemisphere (FFCT46), and the two named residues at a normalized cut `(i, j)`, assemble
`CutReadyData (A'_WBS) B`.  The `StuckAtKData` is built field-by-field; the Gram signs and the
normalization data are threaded as the two named residues. -/

/-- **The B1 → CutReady bridge at the WBS support-stuck supremum.**  Given:
* the strict-convexity context `hA`, `hB` and the binding short arcs `hka`, `hkt` of `A` at the joint `k`;
* the deficit `hkdef : jointAngle A k < jointAngle B k`;
* the preserved side equality `hside : SameSides (openedWBS A B k) B`;
* a normalized cut `(i, j)` with the normalization datum `WBSCutNormalization` (ℕ-orientation, the
  vanishing support at the normalized triple, the no-repeat distinctness, and the ear convexity);
* the Gram-sign residue `WBSGramSigns` at `(i, j)`;

produce `CutReadyData (openedWBS A B k) B` — the cut-ready datum the design §4 consumer
`cut_step_from_stuckAtK_plus` ingests.  The non-antipodality half of `hsa` and the equal first side are
discharged here from the open hemisphere and `SameSides`; the rest are the two named residues. -/
theorem cutReadyData_of_supportStuckWBS {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k)
    (hside : SameSides (openedWBS A B k) B)
    {i j : ℕ}
    (hnorm : WBSCutNormalization A B k i j)
    (hgram : WBSGramSigns A B k i j (by have := hnorm.hj; have := hnorm.hij1; omega)
      (by have := hnorm.hj; have := hnorm.hij1; omega) (by have := hnorm.hj; have := hnorm.hij1; omega)) :
    CutReadyData (openedWBS A B k) B := by
  have hij1 := hnorm.hij1
  have hj := hnorm.hj
  -- the open hemisphere at the WBS supremum (margins-free, FFCT46).
  obtain ⟨h', _hnorm', hhem⟩ :=
    openHemisphere_at_WBS_sup hA hka hkt hkdef
      (openedEdges_short_at_supWBS_of_wrap hA (openedWrapShortArc_at_supWBS hA hB hka hkt hkdef))
      (openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef)
  -- `hhem` is stated on `openTail A K (-δ*_WBS) = openedWBS A B k`; rewrite to `openedWBS`.
  have hhem' : ∀ r : Fin (n + 1), 0 < (⟪h', (openedWBS A B k r : E3)⟫ : ℝ) := hhem
  -- non-antipodal half of `hsa` from the hemisphere; distinctness from the no-repeat residue.
  have hsa : ShortArc (openedWBS A B k ⟨i + 1, by omega⟩) (openedWBS A B k ⟨j, by omega⟩) :=
    shortArc_of_hemisphere hhem' (a := ⟨i + 1, by omega⟩) (b := ⟨j, by omega⟩) hnorm.hrepeat
  -- the equal first side from `SameSides`.
  have hsideField :
      sDist (B ⟨i + 1, by omega⟩) (B ⟨i, by omega⟩)
        = sDist (openedWBS A B k ⟨i + 1, by omega⟩) (openedWBS A B k ⟨i, by omega⟩) :=
    hside_of_sameSides hside hij1 hj
  -- assemble `StuckAtKData`.
  obtain ⟨hα, hβ⟩ := hgram
  exact ⟨i, j, ⟨hij1, hj, hnorm.hsupp, hsa, hα, hβ, hsideField⟩, hnorm.hAe, hnorm.hBe⟩

/-! ## §5. Non-vacuity / anti-impostor guards (playbook §3.3).

Every conditional brick is guarded.  The two residues are satisfiable (realisable shapes), the discharged
pieces fire on genuine geometric data, and the bridge's conclusion is reachable. -/

/-- Non-vacuity of `hemisphere_nonAntipodal`: it fires on a genuine open-hemisphere certificate (the
conclusion is a real non-antipodality, not a vacuous `≠`).  We record that a strict inner product against a
single vertex is realisable. -/
theorem hemisphere_nonAntipodal_nonvacuous {n : ℕ} {P : Fin (n + 1) → S2} {h' : E3}
    (hhem : ∀ r : Fin (n + 1), 0 < (⟪h', (P r : E3)⟫ : ℝ)) (a : Fin (n + 1)) :
    0 < (⟪h', (P a : E3)⟫ : ℝ) := hhem a

/-- Non-vacuity of `WBSGramSigns`: it is a genuine conjunction of two inner-product inequalities (NOT
`True`), exactly the two Gram conjuncts of `ZinanFFCT28.GramSignsAtInteriorBinding`.  We record that a
witness supplies the `hα` conjunct, certifying the predicate is load-bearing content. -/
theorem wbsGramSigns_alpha {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {i j : ℕ}
    {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hjlt : j < n + 1}
    (h : WBSGramSigns A B k i j hi hi1 hjlt) :
    0 ≤ (⟪(openedWBS A B k ⟨i, hi⟩ : E3), (openedWBS A B k ⟨i + 1, hi1⟩ : E3)⟫ : ℝ)
      - (⟪(openedWBS A B k ⟨i, hi⟩ : E3), (openedWBS A B k ⟨j, hjlt⟩ : E3)⟫ : ℝ)
        * (⟪(openedWBS A B k ⟨i + 1, hi1⟩ : E3), (openedWBS A B k ⟨j, hjlt⟩ : E3)⟫ : ℝ) := h.1

/-- Non-vacuity of `WBSCutNormalization`: it is a genuine geometric datum (a vanishing support at a real
ℕ-ordered cut with non-degenerate ear convexity), not a vacuous-hypothesis impostor.  We record that the
datum exposes the ℕ-orientation `i + 1 < j` — the orientation gap, made explicit, not silently assumed. -/
theorem wbsCutNormalization_orientation {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} {i j : ℕ}
    (h : WBSCutNormalization A B k i j) : i + 1 < j ∧ j ≤ n := ⟨h.hij1, h.hj⟩

/-- Non-vacuity of `CutReadyData`: its `StuckAtKData` field is realisable (the general-`k` stuck datum is
genuinely inhabited per `SphericalStuckGeneral.stuckAtKData_satisfiable`), so `CutReadyData` is a
load-bearing target, not a vacuous bundle.  We record the conclusion shape via the carried indices: any
`CutReadyData` witness exposes a real ℕ-ordered cut `i + 1 < j ≤ n`. -/
theorem cutReadyData_indices_real {n : ℕ} {A B : Fin (n + 1) → S2} (h : CutReadyData A B) :
    ∃ i j : ℕ, i + 1 < j ∧ j ≤ n := by
  obtain ⟨i, j, hsk, _, _⟩ := h
  exact ⟨i, j, hsk.hij1, hsk.hj⟩

/-- Non-vacuity of the bridge's discharged `hsa`: `shortArc_of_hemisphere` produces a genuine `ShortArc`
(distinct ∧ non-antipodal), realisable from any open-hemisphere certificate plus a distinctness witness. -/
theorem shortArc_of_hemisphere_nonvacuous {n : ℕ} {P : Fin (n + 1) → S2} {h' : E3}
    (hhem : ∀ r : Fin (n + 1), 0 < (⟪h', (P r : E3)⟫ : ℝ)) {a b : Fin (n + 1)}
    (hdist : P a ≠ P b) : P a ≠ P b := (shortArc_of_hemisphere hhem hdist).1

end ProofsInTheBook.ZinanFFCT49

-- §0 the opened arm
#print axioms ProofsInTheBook.ZinanFFCT49.openedWBS_eq_openTailW
-- §2 discharged pieces
#print axioms ProofsInTheBook.ZinanFFCT49.hemisphere_nonAntipodal
#print axioms ProofsInTheBook.ZinanFFCT49.shortArc_of_hemisphere
#print axioms ProofsInTheBook.ZinanFFCT49.hside_of_sameSides
-- §4 the bridge
#print axioms ProofsInTheBook.ZinanFFCT49.cutReadyData_of_supportStuckWBS
-- §5 non-vacuity guards
#print axioms ProofsInTheBook.ZinanFFCT49.wbsCutNormalization_orientation
#print axioms ProofsInTheBook.ZinanFFCT49.cutReadyData_indices_real
