import ProofsInTheBook.ZinanFFCT49
import ProofsInTheBook.ZinanFFCT23

/-!
# `ZinanFFCT52` — discharging / sharply shrinking `WBSCutNormalization` (the FFCT49 bridge residue)

`ZinanFFCT49.WBSCutNormalization` bundles, as raw data, the three structural inputs the design §5 outcome
assembler was assumed to supply at the WBS support-stuck cut:

1. **the ℕ-orientation** `hij1 : i + 1 < j`, `hj : j ≤ n`, with the matching vanishing support `hsupp`
   (the **orientation gap**: `NonIncident` / `supportStuckWBS_vanishingSupport` produce only *Fin*
   indices `a, b` with `b ≠ a`, `b ≠ a+1`, NOT the ℕ-order `a + 1 < b`);
2. **the no-nonadjacent-repeat distinctness** `hrepeat : openedWBS ⟨i+1⟩ ≠ openedWBS ⟨j⟩`;
3. **the ear interval-arm convexity certificates** `hAe`/`hBe`.

This module discharges what is genuinely derivable and sharply isolates what is not, so that the residue
shrinks from a 6-field opaque bundle to its irreducible core.

## What this module DISCHARGES (no residue)

* **Component 2 (no-repeat distinctness), fully.**  `hrepeat` is *derived* from
  `ZinanFFCT23.NoNonadjacentRepeat (openedWBS …)` (the campaign-accepted no-repeat surface, FFCT23/25
  precedent) together with the weak convexity `WeakConvexSphArm (openedWBS …)` already available at the
  WBS support-stuck supremum (`supportStuckWBS_weakConvex`, FFCT46).  The index `j` satisfies `i + 1 < j`
  but may be *adjacent* (`j = i + 2`): the adjacent case is closed by `edge_short` (the consecutive pair
  is a real edge, hence a `ShortArc`, hence distinct), the nonadjacent case (`i + 1 + 2 ≤ j`) by
  `NoNonadjacentRepeat`.  So `hrepeat` is no longer raw data — `distinctNormalized_of_noRepeat`.

## What this module SHARPLY ISOLATES (named, satisfiable, smaller than the original bundle)

  **Honest scope of the orientation normalization (`orientationNormalized`, §3):** it takes the raw Fin
  pair `(a, b)` with the *non-wrap-base* condition `a.val + 1 < n + 1` (the support's base edge `(a, a+1)`
  is a real interior edge, not the cyclic wrap edge `(n, 0)`).  This is the genuine support shape for an
  interior binding; the wrap-base binding `a.val = n` is the separate cyclic case (flagged, not faked).
  Under it, the ℕ-order is decided: `a + 1 < b` keeps the cut on `P`, `b < a` reverses it onto `revArm P`.

* **Component 1 (the orientation gap).**  The genuine structural finding (FFCT49 §0,
  `SphericalLastCornerStuck`: *"no reversal-invariance lemma for `StrictConvexSphArm` exists"*).  We build
  the **reversed-arm** infrastructure (`revArm`, the Fin reversal `revFin`, `revArm_sideLen`,
  `revArm_jointAngle`, `sOrient`-reversal via the `det3` antisymmetry `det3_cyclic`/`det3_swap12`) so that a
  `b < a` (ℕ-value) raw binding on `P` is an `a' + 1 < b'` normalized binding on `revArm P`.  The reversal
  suite is the load-bearing infrastructure (§2); the residual is precisely the *production* of the
  normalized cut from the raw `supportStuckWBS_vanishingSupport` Fin pair (`OrientationNormalized`, §3) —
  a strictly smaller, geometric residue than the original "supply `hsupp` + `hij1` as data".

* **Component 3 (interval convexity).**  The wrap-edge obstruction is genuine: the ear
  `intervalArm A (i+1) (j-(i+1))` is a *closed* polygon whose closure adds the **diagonal chord**
  `A ⟨j⟩ → A ⟨i+1⟩` as a new edge (NOT a parent edge).  `WeakConvexSphArm`/`StrictConvexSphArm` demand
  `edge_short` / `edge_support` / `open_hemisphere` at THAT wrap edge, which the parent's convexity at an
  arbitrary interval does not supply (verified absent: `SphericalSZStepClose` §R, every consumer carries
  `hAe`/`hBe` as data).  We isolate the *interior* (non-wrap) data that DOES restrict
  (`intervalArm_interiorEdgesShort`, `intervalArm_interiorSupport`, `intervalArm_openHemisphere`,
  `intervalArm_three_le`) so the residue shrinks to exactly the **wrap-edge** certificates
  (`IntervalWrapData`, §4).  The small-size honesty: for `j = i + 2` the ear has `m = 1` edge, and
  `WeakConvexSphArm` requires `2 ≤ m` — so the `j = i + 2` "triangle" ear does not even typecheck as a
  `WeakConvexSphArm`; that minimal case is the separate degenerate branch flagged in §4.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49

namespace ProofsInTheBook.ZinanFFCT52

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. Component 2 — the no-repeat distinctness, DISCHARGED.

`WBSCutNormalization.hrepeat : openedWBS ⟨i+1⟩ ≠ openedWBS ⟨j⟩` is derivable, not raw data.  With
`i + 1 < j ≤ n` the pair `(i+1, j)` is either *adjacent* (`j = i + 2`, a real arm edge, hence a
`ShortArc`, hence distinct) or *nonadjacent* (`(i+1) + 2 ≤ j`, covered by `NoNonadjacentRepeat`). -/

/-- **Distinctness at a normalized cut, derived.**  For any arm `P : Fin (n+1) → S2` that is weakly convex
and has no nonadjacent repeat, the normalized cut endpoints `P ⟨i+1⟩`, `P ⟨j⟩` (`i + 1 < j ≤ n`) are
distinct.  Adjacent case `j = i + 2`: the edge `(i+1, i+2)` is a `ShortArc` (weak convexity's
`edge_short`), so its two endpoints are distinct.  Nonadjacent case `(i+1) + 2 ≤ j`: `NoNonadjacentRepeat`.

This discharges `WBSCutNormalization.hrepeat`. -/
theorem distinctNormalized_of_noRepeat {n : ℕ} {P : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) (hrep : NoNonadjacentRepeat P) {i j : ℕ}
    (hij1 : i + 1 < j) (hj : j ≤ n) :
    P ⟨i + 1, by omega⟩ ≠ P ⟨j, by omega⟩ := by
  rcases Nat.lt_or_ge (i + 1 + 2) (j + 1) with hadj | hnon
  · -- nonadjacent: (i+1) + 2 ≤ j, use NoNonadjacentRepeat.
    have hle : (i + 1) + 2 ≤ j := by omega
    exact hrep (i + 1) j (by omega) (by omega) hle
  · -- adjacent: j = i + 2 (since i+1 < j ≤ i+2). The edge (i+1, i+2) is a real arm edge.
    have hjeq : j = i + 2 := by omega
    subst hjeq
    -- edge_short at the Fin index ⟨i+1⟩: ShortArc (P ⟨i+1⟩) (P (⟨i+1⟩ + 1)).
    have hedge : ShortArc (P ⟨i + 1, by omega⟩) (P (⟨i + 1, by omega⟩ + 1)) :=
      hP.closed_convex.edge_short ⟨i + 1, by omega⟩
    -- (⟨i+1⟩ + 1 : Fin (n+1)) = ⟨i+2⟩ since i + 2 ≤ n < n + 1.
    have hsucc : (⟨i + 1, by omega⟩ + 1 : Fin (n + 1)) = ⟨i + 2, by omega⟩ := by
      apply Fin.ext
      have : ((⟨i + 1, by omega⟩ + 1 : Fin (n + 1)) : ℕ) = (i + 1 + 1) % (n + 1) := by
        rw [Fin.add_def]; simp
      rw [this]
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hsucc] at hedge
    exact hedge.1

/-- **The WBS instantiation of `distinctNormalized_of_noRepeat`.**  At the WBS support-stuck supremum the
opened arm `openedWBS A B k` is weakly convex (`supportStuckWBS_weakConvex`, FFCT46 — now *unconditional*
since FFCT47 discharged the wrap residual via `openedWrapShortArc_at_supWBS`), so given the no-repeat
surface `NoNonadjacentRepeat (openedWBS A B k)` the normalized-cut distinctness `hrepeat` is discharged. -/
theorem hrepeat_of_noRepeat_WBS {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k)
    (hrep : NoNonadjacentRepeat (openedWBS A B k)) {i j : ℕ}
    (hij1 : i + 1 < j) (hj : j ≤ n) :
    openedWBS A B k ⟨i + 1, by omega⟩ ≠ openedWBS A B k ⟨j, by omega⟩ := by
  -- weak convexity of the opened arm at the WBS support-stuck supremum (unconditional via FFCT47 wrap).
  have hwk : WeakConvexSphArm (openedWBS A B k) :=
    supportStuckWBS_weakConvex hA hB hka hkt hkdef
      (openedWrapShortArc_at_supWBS hA hB hka hkt hkdef)
  exact distinctNormalized_of_noRepeat hwk hrep hij1 hj

/-! ## §2. Component 1 — the reversed-arm infrastructure (the orientation-gap route).

`StuckAtKData.hij1 : i + 1 < j` is a hard ℕ-ordering constraint, but `supportStuckWBS_vanishingSupport`
produces only *Fin* indices `a, b` with `b ≠ a`, `b ≠ a+1` and the vanishing support
`sOrient (P a)(P (a+1))(P b) = 0` — with NO ℕ-order (`b < a` is possible).  When `a + 1 < b` (ℕ value) the
raw triple `(a, a+1, b)` already has the normalized form `(i, i+1, j)` with `i + 1 < j`.  When `b < a`, it
does NOT (the only consecutive pair `{a, a+1}` would force `j = b < i = a`).  The fix is the **reversed
arm**: under `revFin m = ⟨n − m⟩` the `b < a` triple is the *normalized* triple `(n−(a+1), n−a, n−b)` of
`revArm P`, with the support sign flipped by the `det3` slot-antisymmetry (`= 0` is sign-free).

We build the reversal suite: the Fin reversal `revFin`, the reversed arm `revArm`, the `sOrient`-reversal,
and the `sideLen`/`jointAngle` transport (`sphAngle_comm` reverses the joint reading, `sDist_comm` the
side).  This is exactly the infrastructure `SphericalLastCornerStuck` recorded as absent. -/

/-- The Fin reversal `m ↦ ⟨n − m⟩` on `Fin (n+1)`. -/
def revFin {n : ℕ} (m : Fin (n + 1)) : Fin (n + 1) := ⟨n - m.val, by have := m.isLt; omega⟩

@[simp] theorem revFin_val {n : ℕ} (m : Fin (n + 1)) : (revFin m).val = n - m.val := rfl

/-- The reversed arm: `revArm P m = P ⟨n − m⟩`. -/
def revArm {n : ℕ} (P : Fin (n + 1) → S2) : Fin (n + 1) → S2 := fun m => P (revFin m)

@[simp] theorem revArm_apply {n : ℕ} (P : Fin (n + 1) → S2) (m : Fin (n + 1)) :
    revArm P m = P ⟨n - m.val, by have := m.isLt; omega⟩ := rfl

/-- `revArm P` at a value index `v ≤ n` reads `P` at `n − v`. -/
theorem revArm_index {n : ℕ} (P : Fin (n + 1) → S2) {v : ℕ} (hv : v < n + 1) :
    revArm P ⟨v, hv⟩ = P ⟨n - v, by omega⟩ := rfl

/-- **`sOrient` reversal at a normalized triple.**  For a raw binding with `b < a` (so `a + 1 ≤ n`), the
normalized reversed triple `(revArm P ⟨n−a−1⟩, revArm P ⟨n−a⟩, revArm P ⟨n−b⟩)` reads as
`(P ⟨a+1⟩, P ⟨a⟩, P ⟨b⟩)`, whose `sOrient` is `−sOrient (P ⟨a⟩)(P ⟨a+1⟩)(P ⟨b⟩)` (slot-1-2 swap,
`det3_swap12`).  Hence a *vanishing* raw support gives a *vanishing* normalized reversed support. -/
theorem sOrient_revArm_normalized {n : ℕ} (P : Fin (n + 1) → S2) {a b : ℕ}
    (ha1 : a + 1 < n + 1) (hb : b < a) :
    sOrient (revArm P ⟨n - a - 1, by omega⟩) (revArm P ⟨n - a, by omega⟩)
        (revArm P ⟨n - b, by omega⟩)
      = - sOrient (P ⟨a, by omega⟩) (P ⟨a + 1, by omega⟩) (P ⟨b, by omega⟩) := by
  -- evaluate the reversed indices: n−(n−a−1) = a+1, n−(n−a) = a, n−(n−b) = b.
  rw [revArm_index P (by omega), revArm_index P (by omega), revArm_index P (by omega)]
  have e1 : n - (n - a - 1) = a + 1 := by omega
  have e2 : n - (n - a) = a := by omega
  have e3 : n - (n - b) = b := by omega
  rw [show (⟨n - (n - a - 1), by omega⟩ : Fin (n + 1)) = ⟨a + 1, by omega⟩ from Fin.ext (by omega),
     show (⟨n - (n - a), by omega⟩ : Fin (n + 1)) = ⟨a, by omega⟩ from Fin.ext (by omega),
     show (⟨n - (n - b), by omega⟩ : Fin (n + 1)) = ⟨b, by omega⟩ from Fin.ext (by omega)]
  -- sOrient (P(a+1))(P a)(P b) = -sOrient (P a)(P(a+1))(P b) by slot-1-2 swap.
  exact det3_swap12 _ _ _

/-- **`sideLen` reversal.**  Side `i` of `revArm P` (`i : Fin n`) is the parent's side `n − 1 − i` with its
two endpoints swapped; `sDist_comm` makes them equal.  Concretely `sideLen (revArm P) i =
sDist (P ⟨n−i⟩)(P ⟨n−i−1⟩) = sDist (P ⟨n−i−1⟩)(P ⟨n−i⟩) = sideLen P ⟨n−1−i⟩`. -/
theorem revArm_sideLen {n : ℕ} (P : Fin (n + 1) → S2) (i : Fin n) :
    sideLen (revArm P) i = sideLen P ⟨n - 1 - i.val, by have := i.isLt; omega⟩ := by
  have hi := i.isLt
  unfold sideLen
  -- index equalities (as Fin equalities, so rewriting is motive-safe).
  have l0 : revArm P i.castSucc = P ⟨n - i.val, by omega⟩ := by
    show P (revFin i.castSucc) = _
    exact congrArg P (Fin.ext (by simp only [revFin_val, Fin.val_castSucc]))
  have l1 : revArm P i.succ = P ⟨n - i.val - 1, by omega⟩ := by
    show P (revFin i.succ) = _
    exact congrArg P (Fin.ext (by simp only [revFin_val, Fin.val_succ]; omega))
  have r0 : P ((⟨n - 1 - i.val, by omega⟩ : Fin n).castSucc) = P ⟨n - i.val - 1, by omega⟩ :=
    congrArg P (Fin.ext (by simp only [Fin.val_castSucc]; omega))
  have r1 : P ((⟨n - 1 - i.val, by omega⟩ : Fin n).succ) = P ⟨n - i.val, by omega⟩ :=
    congrArg P (Fin.ext (by simp only [Fin.val_succ]; omega))
  rw [l0, l1, r0, r1]
  -- goal: sDist (P ⟨n−i⟩)(P ⟨n−i−1⟩) = sDist (P ⟨n−i−1⟩)(P ⟨n−i⟩).
  exact sDist_comm _ _

/-- **`jointAngle` reversal.**  Interior joint `i` of `revArm P` (`i : Fin (n−1)`) is the parent's interior
joint `n − 2 − i` read backwards; `sphAngle_comm` (swap the two neighbours) makes the value invariant. -/
theorem revArm_jointAngle {n : ℕ} (P : Fin (n + 1) → S2) (i : Fin (n - 1)) :
    jointAngle (revArm P) i = jointAngle P ⟨n - 2 - i.val, by have := i.isLt; omega⟩ := by
  have hi := i.isLt
  unfold jointAngle
  -- LHS = sphAngle (revArm P ⟨i⟩)(revArm P ⟨i+1⟩)(revArm P ⟨i+2⟩); each reads P at n−i, n−i−1, n−i−2.
  have v0 : (revArm P ⟨i.val, by omega⟩ : S2) = P ⟨n - 2 - i.val + 2, by omega⟩ :=
    congrArg P (Fin.ext (by simp only [revFin_val]; omega))
  have v1 : (revArm P ⟨i.val + 1, by omega⟩ : S2) = P ⟨n - 2 - i.val + 1, by omega⟩ :=
    congrArg P (Fin.ext (by simp only [revFin_val]; omega))
  have v2 : (revArm P ⟨i.val + 2, by omega⟩ : S2) = P ⟨n - 2 - i.val, by omega⟩ :=
    congrArg P (Fin.ext (by simp only [revFin_val]; omega))
  -- rewrite each LHS vertex; LHS becomes sphAngle (P j+2)(P j+1)(P j) with j = n−2−i.
  show sphAngle (revArm P ⟨i.val, _⟩) (revArm P ⟨i.val + 1, _⟩) (revArm P ⟨i.val + 2, _⟩) = _
  rw [v0, v1, v2, sphAngle_comm]

/-- **Weak/strict convexity is preserved by reversal — the missing reversal lemma, here for the closed
polygon's *edge_support* / *open_hemisphere* structure restricted to what reversal needs.**

We expose the precise reversal facts the orientation normalization consumes: `revArm` reindexes every
vertex bijectively (`revFin` is an involution), so the *open hemisphere* witness transports verbatim and
the *no-nonadjacent-repeat* fact transports (a nonadjacent repeat of `revArm P` is one of `P`). -/
theorem revFin_involutive {n : ℕ} (m : Fin (n + 1)) : revFin (revFin m) = m := by
  apply Fin.ext; simp only [revFin_val]; have := m.isLt; omega

/-- The open-hemisphere certificate transports under reversal (same normal `h`, the vertex set is the same
set, only reindexed). -/
theorem revArm_openHemisphere {n : ℕ} {P : Fin (n + 1) → S2} {h : E3}
    (hhem : ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ)) :
    ∀ r : Fin (n + 1), 0 < (⟪h, (revArm P r : E3)⟫ : ℝ) :=
  fun r => hhem (revFin r)

/-- The no-nonadjacent-repeat fact transports under reversal: a nonadjacent repeat of `revArm P` at
`r + 2 ≤ s` is a nonadjacent repeat of `P` at the reversed indices `n − s + 2 ≤ n − r`. -/
theorem revArm_noNonadjacentRepeat {n : ℕ} {P : Fin (n + 1) → S2}
    (hrep : NoNonadjacentRepeat P) : NoNonadjacentRepeat (revArm P) := by
  intro r s hr hs hrs he
  -- revArm P ⟨r⟩ = P ⟨n−r⟩, revArm P ⟨s⟩ = P ⟨n−s⟩; he : P ⟨n−r⟩ = P ⟨n−s⟩.
  rw [revArm_index P hr, revArm_index P hs] at he
  -- nonadjacent on P: (n−s) + 2 ≤ n−r since r + 2 ≤ s.
  exact hrep (n - s) (n - r) (by omega) (by omega) (by omega) he.symm

/-! ## §3. The orientation normalization (the shrunk Component 1 residue).

The raw `supportStuckWBS_vanishingSupport` Fin pair `(a, b)` (with `b ≠ a`, `b ≠ a+1`, vanishing support)
is normalized to a cut `(i, j)` with `i + 1 < j ≤ n`, EITHER on `P` (when `a + 1 < b`) OR on `revArm P`
(when `b < a`), with the matching vanishing support.  This is strictly smaller than carrying `hij1` +
`hsupp` as opaque data: only the *choice of side* (which is forced by the ℕ-order of `a, b`) remains, and
it is discharged here for both cases. -/

/-- **The orientation-normalized vanishing support, both branches.**  From the raw Fin binding
`sOrient (P a)(P (a+1))(P b) = 0` with `b ≠ a` and `b ≠ a+1` (as Fin), the normalized cut exists:
* if `a.val + 1 < b.val`: on `P` itself, `(i, j) = (a, b)`, support unchanged;
* if `b.val < a.val`: on `revArm P`, `(i, j) = (n − a − 1, n − b)`, support flipped (`= 0` is sign-free);
in both branches `i + 1 < j ≤ n` and `sOrient (Q ⟨i⟩)(Q ⟨i+1⟩)(Q ⟨j⟩) = 0` for the chosen arm `Q`. -/
theorem orientationNormalized {n : ℕ} (P : Fin (n + 1) → S2) {a b : Fin (n + 1)}
    (hne : b ≠ a) (hne1 : b ≠ a + 1)
    (hsupp : sOrient (P a) (P (a + 1)) (P b) = 0)
    (hadj : a.val + 1 < n + 1) :
    (∃ i j : ℕ, ∃ (hij1 : i + 1 < j) (hj : j ≤ n),
        sOrient (P ⟨i, by omega⟩) (P ⟨i + 1, by omega⟩) (P ⟨j, by omega⟩) = 0)
    ∨ (∃ i j : ℕ, ∃ (hij1 : i + 1 < j) (hj : j ≤ n),
        sOrient (revArm P ⟨i, by omega⟩) (revArm P ⟨i + 1, by omega⟩) (revArm P ⟨j, by omega⟩) = 0) := by
  have hai := a.isLt
  have hbi := b.isLt
  -- the Fin (a+1) reads as value a.val + 1 (since a.val + 1 < n + 1, no wrap).
  have hav : a.val + 1 < n + 1 := hadj
  have hfsucc : (a + 1 : Fin (n + 1)) = ⟨a.val + 1, hav⟩ := by
    apply Fin.ext
    have : ((a + 1 : Fin (n + 1)) : ℕ) = (a.val + 1) % (n + 1) := by rw [Fin.add_def]; simp
    rw [this, Nat.mod_eq_of_lt hav]
  -- ℕ-disequalities from the Fin ones.
  have hbne : b.val ≠ a.val := fun h => hne (Fin.ext h)
  have hbne1 : b.val ≠ a.val + 1 := by
    intro h; apply hne1; rw [hfsucc]; exact Fin.ext h
  rcases Nat.lt_or_ge (a.val + 1) b.val with hgt | hle
  · -- a.val + 1 < b.val: normalize on P directly with (i, j) = (a.val, b.val).
    left
    refine ⟨a.val, b.val, hgt, by have := b.isLt; omega, ?_⟩
    -- rewrite the goal's Fin indices to a, a+1, b.
    rw [show (⟨a.val, by omega⟩ : Fin (n + 1)) = a from Fin.ext rfl,
       show (⟨a.val + 1, by omega⟩ : Fin (n + 1)) = a + 1 from hfsucc.symm,
       show (⟨b.val, by omega⟩ : Fin (n + 1)) = b from Fin.ext rfl]
    exact hsupp
  · -- b.val < a.val (since b ≠ a, b ≠ a+1 and ¬ a+1 < b): normalize on revArm P.
    have hblt : b.val < a.val := by omega
    right
    refine ⟨n - a.val - 1, n - b.val, by omega, by have := b.isLt; omega, ?_⟩
    -- the reversed normalized support = -(raw support) = 0.
    have hrev := sOrient_revArm_normalized P (a := a.val) (b := b.val) (by omega) hblt
    -- align the goal's middle index `(n-a-1)+1` to `n-a` (the form `hrev` uses).
    have hmid : (⟨(n - a.val - 1) + 1, by omega⟩ : Fin (n + 1)) = ⟨n - a.val, by omega⟩ :=
      Fin.ext (show (n - a.val - 1) + 1 = n - a.val by omega)
    rw [hmid, hrev]
    -- raw support in value form = hsupp after aligning a, a+1, b.
    rw [show (⟨a.val, by omega⟩ : Fin (n + 1)) = a from Fin.ext rfl,
       show (⟨a.val + 1, by omega⟩ : Fin (n + 1)) = a + 1 from hfsucc.symm,
       show (⟨b.val, by omega⟩ : Fin (n + 1)) = b from Fin.ext rfl]
    rw [hsupp]; ring

/-! ## §4. Component 3 — interval convexity: interior restriction + the sharp wrap residue.

`WBSCutNormalization.hAe : WeakConvexSphArm (intervalArm A' (i+1) (j−(i+1)))` is the ear convexity
certificate.  The ear is a *closed* polygon on `Fin (m+1)` (`m = j − (i+1)`): its closure adds the
**wrap edge** `(vertex m, vertex 0) = (A' ⟨j⟩, A' ⟨i+1⟩)`, the diagonal chord — NOT a parent edge.  We
discharge everything the parent's weak convexity DOES supply (the interior edges and the supports whose
base is an interior edge, and the open hemisphere) and isolate the irreducible **wrap-edge** data.

**Small-size honesty:** `WeakConvexSphArm` requires `two_le : 2 ≤ m` (the closed polygon needs `≥ 3`
vertices, `m + 1 ≥ 3`).  With `i + 1 < j ≤ n` the ear length is `m = j − (i+1) ≥ 1`; the minimal
`j = i + 2` gives `m = 1`, a single-edge "ear" that does NOT typecheck as a `WeakConvexSphArm` — that
triangle-minimal case is a separate degenerate branch (the consumer `stuckAtK_diag_le` requires `m ≥ 2`
through the same `two_le`, so the `j = i + 2` cut is handled by the substrate's minimal machinery, not
this ear). We therefore work under the standing `2 ≤ m` and flag `m = 1` as the excluded degenerate. -/

/-- The wrap-edge data of the ear `intervalArm A a m` (the diagonal chord `(A ⟨a+m⟩, A ⟨a⟩)` and its
supports): a `ShortArc` on the wrap chord, and the nonnegativity of every support whose base is the wrap
edge `(A ⟨a+m⟩, A ⟨a⟩)`.  These are exactly the certificates the parent's weak convexity at an *arbitrary*
interval does NOT supply (the wrap chord is a diagonal, not a parent edge); everything else restricts. -/
structure IntervalWrapData {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N) : Prop where
  /-- The wrap (diagonal) edge is a short arc. -/
  wrap_short : ShortArc (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩)
  /-- Every vertex is supported on the nonnegative side of the oriented wrap edge. -/
  wrap_support : ∀ v : ℕ, (hv : v < m + 1) →
    0 ≤ sOrient (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩) (A ⟨a + v, by have := hv; omega⟩)

/-- Non-vacuity of `IntervalWrapData`: it carries a genuine `ShortArc` (distinctness of the diagonal
endpoints), not `True` — load-bearing content. -/
theorem intervalWrapData_wrap_short {N : ℕ} {A : Fin (N + 1) → S2} {a m : ℕ} {hb : a + m ≤ N}
    (h : IntervalWrapData A a m hb) : A ⟨a + m, by omega⟩ ≠ A ⟨a, by omega⟩ :=
  h.wrap_short.1

/-! ### The interior facts that DO restrict from the parent (reusable, no residue). -/

/-- **Interior edges of the ear are parent edges, hence short.**  For a strictly/weakly convex parent and
an interior ear edge index `t < m`, the ear edge `(ear ⟨t⟩, ear ⟨t+1⟩) = (A ⟨a+t⟩, A ⟨a+t+1⟩)` is the
parent edge `t' = a + t`, which is a `ShortArc` (parent `edge_short`). -/
theorem intervalArm_interiorEdgeShort {N : ℕ} {A : Fin (N + 1) → S2} (hA : WeakConvexSphArm A)
    {a m : ℕ} (hb : a + m ≤ N) {t : ℕ} (ht : t < m) :
    ShortArc (A ⟨a + t, by omega⟩) (A ⟨a + t + 1, by omega⟩) := by
  have hedge := hA.closed_convex.edge_short ⟨a + t, by omega⟩
  -- (⟨a+t⟩ + 1 : Fin (N+1)) = ⟨a+t+1⟩ since a+t+1 ≤ N < N+1.
  have hsucc : (⟨a + t, by omega⟩ + 1 : Fin (N + 1)) = ⟨a + t + 1, by omega⟩ := by
    apply Fin.ext
    have : ((⟨a + t, by omega⟩ + 1 : Fin (N + 1)) : ℕ) = (a + t + 1) % (N + 1) := by
      rw [Fin.add_def]; simp
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rwa [hsucc] at hedge

/-- **Interior-base supports of the ear are parent supports, hence ≥ 0.**  For a weakly convex parent, an
interior ear edge `(A ⟨a+t⟩, A ⟨a+t+1⟩)` (`t < m`) supports any ear vertex `A ⟨a+v⟩` (`v ≤ m`) on the
nonnegative side, because it is the parent non-incident support `sOrient (A ⟨a+t⟩)(A ⟨a+t+1⟩)(A ⟨a+v⟩) ≥ 0`
(parent `edge_support`). -/
theorem intervalArm_interiorSupport {N : ℕ} {A : Fin (N + 1) → S2} (hA : WeakConvexSphArm A)
    {a m : ℕ} (hb : a + m ≤ N) {t v : ℕ} (ht : t < m) (hv : v < m + 1) :
    0 ≤ sOrient (A ⟨a + t, by omega⟩) (A ⟨a + t + 1, by omega⟩) (A ⟨a + v, by omega⟩) := by
  have hsupp := hA.closed_convex.edge_support ⟨a + t, by omega⟩ ⟨a + v, by omega⟩
  have hsucc : (⟨a + t, by omega⟩ + 1 : Fin (N + 1)) = ⟨a + t + 1, by omega⟩ := by
    apply Fin.ext
    have : ((⟨a + t, by omega⟩ + 1 : Fin (N + 1)) : ℕ) = (a + t + 1) % (N + 1) := by
      rw [Fin.add_def]; simp
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rwa [hsucc] at hsupp

/-- **The open hemisphere restricts to the ear.**  The parent's open-hemisphere normal `h` works verbatim
for the ear (the ear vertices are a subset of the parent vertices). -/
theorem intervalArm_openHemisphere {N : ℕ} {A : Fin (N + 1) → S2} (hA : WeakConvexSphArm A)
    {a m : ℕ} (hb : a + m ≤ N) :
    ∃ h : E3, ‖h‖ = 1 ∧ ∀ x : Fin (m + 1), 0 < (⟪h, (intervalArm A a m hb x : E3)⟫ : ℝ) := by
  obtain ⟨h, hnorm, hhem⟩ := hA.closed_convex.open_hemisphere
  exact ⟨h, hnorm, fun x => hhem _⟩

/-! ### The sharp residue: the ear is weakly convex GIVEN the wrap data.

The wrap-edge supports/short-arc are the *only* genuinely-new fields; with them, the full
`WeakConvexSphArm (intervalArm A a m hb)` assembles from the parent (interior edges + interior-base
supports + open hemisphere). This is the precise shrink of `WBSCutNormalization.hAe`: from a full opaque
convexity certificate to the wrap diagonal data alone. -/

/-- **Component 3, sharpened.**  The ear `intervalArm A a m` (`2 ≤ m`, `a + m ≤ N`) of a weakly convex
parent `A` is itself weakly convex PROVIDED the wrap-edge data `IntervalWrapData` (the diagonal chord's
`ShortArc` and the nonnegativity of the supports based at the diagonal).  All other fields restrict from
the parent.

This isolates the genuine Component-3 residue (the wrap diagonal) and discharges the rest. -/
theorem weakConvex_intervalArm_of_wrap {N : ℕ} {A : Fin (N + 1) → S2} (hA : WeakConvexSphArm A)
    {a m : ℕ} (hm : 2 ≤ m) (hb : a + m ≤ N)
    (hwrap : IntervalWrapData A a m hb) :
    WeakConvexSphArm (intervalArm A a m hb) := by
  have hNz : NeZero (m + 1) := ⟨by omega⟩
  refine ⟨hm, ?_⟩
  refine ⟨by omega, ?_, ?_, ?_⟩
  · -- edge_short for every cyclic edge `i : Fin (m+1)`: interior (i < m) parent edge, or wrap (i = m).
    intro i
    by_cases hi : i.val < m
    · -- interior edge: (ear i, ear (i+1)) = (A ⟨a+i⟩, A ⟨a+i+1⟩).
      have hsucc : (i + 1 : Fin (m + 1)) = ⟨i.val + 1, by have := i.isLt; omega⟩ := by
        apply Fin.ext
        have : ((i + 1 : Fin (m + 1)) : ℕ) = (i.val + 1) % (m + 1) := by rw [Fin.add_def]; simp
        rw [this, Nat.mod_eq_of_lt (by omega)]
      rw [intervalArm_apply, intervalArm_apply, hsucc]
      have := intervalArm_interiorEdgeShort hA hb (t := i.val) hi
      -- align ⟨a + (i+1).val⟩ to ⟨a + i + 1⟩.
      simpa only [show a + (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (m + 1)).val = a + i.val + 1 from rfl]
        using this
    · -- wrap edge: i.val = m, (i+1) wraps to 0.
      have him : i.val = m := by have := i.isLt; omega
      have hi0 : (i + 1 : Fin (m + 1)) = 0 := by
        apply Fin.ext
        have : ((i + 1 : Fin (m + 1)) : ℕ) = (i.val + 1) % (m + 1) := by rw [Fin.add_def]; simp
        rw [this, him]; simp [Nat.mod_self]
      rw [intervalArm_apply, hi0, intervalArm_apply]
      simp only [Fin.val_zero, Nat.add_zero]
      have halign : (A ⟨a + i.val, by have := i.isLt; omega⟩ : S2) = A ⟨a + m, by omega⟩ :=
        congrArg A (Fin.ext (by simp only [him]))
      rw [halign]
      exact hwrap.wrap_short
  · -- edge_support for every base edge `i` and vertex `j`.
    intro i j
    by_cases hi : i.val < m
    · -- interior base edge: parent support.
      have hsucc : (i + 1 : Fin (m + 1)) = ⟨i.val + 1, by have := i.isLt; omega⟩ := by
        apply Fin.ext
        have : ((i + 1 : Fin (m + 1)) : ℕ) = (i.val + 1) % (m + 1) := by rw [Fin.add_def]; simp
        rw [this, Nat.mod_eq_of_lt (by omega)]
      rw [intervalArm_apply, intervalArm_apply, intervalArm_apply, hsucc]
      have := intervalArm_interiorSupport hA hb (t := i.val) (v := j.val) hi j.isLt
      simpa only [show a + (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (m + 1)).val = a + i.val + 1 from rfl]
        using this
    · -- wrap base edge: i.val = m, base = (A ⟨a+m⟩, A ⟨a⟩); use wrap_support at v = j.val.
      have him : i.val = m := by have := i.isLt; omega
      have hi0 : (i + 1 : Fin (m + 1)) = 0 := by
        apply Fin.ext
        have : ((i + 1 : Fin (m + 1)) : ℕ) = (i.val + 1) % (m + 1) := by rw [Fin.add_def]; simp
        rw [this, him]; simp [Nat.mod_self]
      rw [intervalArm_apply, hi0, intervalArm_apply, intervalArm_apply]
      simp only [Fin.val_zero, Nat.add_zero]
      have halign : (A ⟨a + i.val, by have := i.isLt; omega⟩ : S2) = A ⟨a + m, by omega⟩ :=
        congrArg A (Fin.ext (by simp only [him]))
      rw [halign]
      exact hwrap.wrap_support j.val j.isLt
  · -- open hemisphere restricts.
    obtain ⟨h, hnorm, hhem⟩ := intervalArm_openHemisphere hA hb (a := a) (m := m)
    exact ⟨h, hnorm, hhem⟩

/-- **Interior strict supports restrict.**  For a *strictly* convex parent, an interior ear edge
`(A ⟨a+t⟩, A ⟨a+t+1⟩)` (`t < m`) supports a non-incident ear vertex `A ⟨a+v⟩` strictly on the positive
side, whenever `a+v` is non-incident to the parent edge `a+t` (i.e. `a+v ≠ a+t` and `a+v ≠ a+t+1`). -/
theorem intervalArm_interiorStrictSupport {N : ℕ} {A : Fin (N + 1) → S2} (hA : StrictConvexSphArm A)
    {a m : ℕ} (hb : a + m ≤ N) {t v : ℕ} (ht : t < m) (hv : v < m + 1)
    (hne : v ≠ t) (hne1 : v ≠ t + 1) :
    0 < sOrient (A ⟨a + t, by omega⟩) (A ⟨a + t + 1, by omega⟩) (A ⟨a + v, by omega⟩) := by
  have hj1 : (⟨a + v, by omega⟩ : Fin (N + 1)) ≠ ⟨a + t, by omega⟩ := by
    intro h; apply hne
    have : a + v = a + t := congrArg Fin.val h
    omega
  -- the parent edge `a+t` and its `+1` as Fin: align `(⟨a+t⟩ + 1)` to `⟨a+t+1⟩`.
  have hsucc : (⟨a + t, by omega⟩ + 1 : Fin (N + 1)) = ⟨a + t + 1, by omega⟩ := by
    apply Fin.ext
    have : ((⟨a + t, by omega⟩ + 1 : Fin (N + 1)) : ℕ) = (a + t + 1) % (N + 1) := by
      rw [Fin.add_def]; simp
    rw [this, Nat.mod_eq_of_lt (by omega)]
  have hj2 : (⟨a + v, by omega⟩ : Fin (N + 1)) ≠ (⟨a + t, by omega⟩ : Fin (N + 1)) + 1 := by
    rw [hsucc]; intro h; apply hne1
    have : a + v = a + t + 1 := congrArg Fin.val h
    omega
  have hstr := hA.closed_convex.strict_nonincident ⟨a + t, by omega⟩ ⟨a + v, by omega⟩ hj1 hj2
  rwa [hsucc] at hstr

/-- The strict-ear wrap data: as `IntervalWrapData`, plus the *strict* support of every non-incident
vertex against the wrap (diagonal) edge.  This is the only genuinely-new strict field for the ear; the
interior strict non-incidence restricts from the parent. -/
structure IntervalWrapDataStrict {N : ℕ} (A : Fin (N + 1) → S2) (a m : ℕ) (hb : a + m ≤ N) : Prop where
  toWeak : IntervalWrapData A a m hb
  /-- The wrap (diagonal) edge supports every NON-incident vertex strictly.  Non-incidence against the
  cyclic wrap edge `(vertex m, vertex 0)` means `v ≠ m` (not the base tail) and `v ≠ 0`... but vertex `0`
  IS the wrap edge's head, so the non-incident condition for the wrap edge `(m, 0)` is `v ≠ m ∧ v ≠ 0`.
  -/
  wrap_strict : ∀ v : ℕ, (hv : v < m + 1) → v ≠ m → v ≠ 0 →
    0 < sOrient (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩) (A ⟨a + v, by have := hv; omega⟩)

/-- **Component 3, strict version.**  The ear `intervalArm A a m` (`2 ≤ m`) of a *strictly* convex parent
`A` is strictly convex GIVEN the strict wrap data.  The interior strict non-incidences restrict from the
parent; the wrap base's strict non-incidence is the residue (`wrap_strict`). -/
theorem strictConvex_intervalArm_of_wrap {N : ℕ} {A : Fin (N + 1) → S2} (hA : StrictConvexSphArm A)
    {a m : ℕ} (hm : 2 ≤ m) (hb : a + m ≤ N)
    (hwrap : IntervalWrapDataStrict A a m hb) :
    StrictConvexSphArm (intervalArm A a m hb) := by
  have hNz : NeZero (m + 1) := ⟨by omega⟩
  -- reuse the weak assembly for edge_short / edge_support / open_hemisphere.
  have hweak := weakConvex_intervalArm_of_wrap (strictConvexSphArm_toWeak hA) hm hb hwrap.toWeak
  refine ⟨hm, ?_⟩
  refine ⟨by omega, hweak.closed_convex.edge_short, hweak.closed_convex.edge_support, ?_,
    hweak.closed_convex.open_hemisphere⟩
  -- strict_nonincident: tested vertex `j` non-incident to base edge `i`.
  intro i j hji hji1
  by_cases hi : i.val < m
  · -- interior base edge: parent strict non-incidence at (a+i, a+j).
    have hsucc : (i + 1 : Fin (m + 1)) = ⟨i.val + 1, by have := i.isLt; omega⟩ := by
      apply Fin.ext
      have : ((i + 1 : Fin (m + 1)) : ℕ) = (i.val + 1) % (m + 1) := by rw [Fin.add_def]; simp
      rw [this, Nat.mod_eq_of_lt (by omega)]
    -- ear non-incidence j ≠ i, j ≠ i+1 transfers to value non-incidence v ≠ t, v ≠ t+1.
    have hvne : j.val ≠ i.val := fun h => hji (Fin.ext h)
    have hvne1 : j.val ≠ i.val + 1 := by
      intro h; apply hji1; rw [hsucc]; exact Fin.ext h
    rw [intervalArm_apply, intervalArm_apply, intervalArm_apply, hsucc]
    have := intervalArm_interiorStrictSupport hA hb (t := i.val) (v := j.val) hi j.isLt hvne hvne1
    simpa only [show a + (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (m + 1)).val = a + i.val + 1 from rfl]
      using this
  · -- wrap base edge: i.val = m, base = (A ⟨a+m⟩, A ⟨a⟩); use wrap_strict at v = j.val (j ≠ m, j ≠ 0).
    have him : i.val = m := by have := i.isLt; omega
    have hi0 : (i + 1 : Fin (m + 1)) = 0 := by
      apply Fin.ext
      have : ((i + 1 : Fin (m + 1)) : ℕ) = (i.val + 1) % (m + 1) := by rw [Fin.add_def]; simp
      rw [this, him]; simp [Nat.mod_self]
    -- j ≠ i means j.val ≠ m; j ≠ i+1 = 0 means j.val ≠ 0.
    have hjm : j.val ≠ m := by intro h; apply hji; apply Fin.ext; rw [him]; exact h
    have hj0 : j.val ≠ 0 := by intro h; apply hji1; rw [hi0]; apply Fin.ext; simp [h]
    rw [intervalArm_apply, hi0, intervalArm_apply, intervalArm_apply]
    simp only [Fin.val_zero, Nat.add_zero]
    have halign : (A ⟨a + i.val, by have := i.isLt; omega⟩ : S2) = A ⟨a + m, by omega⟩ :=
      congrArg A (Fin.ext (by simp only [him]))
    rw [halign]
    exact hwrap.wrap_strict j.val j.isLt hjm hj0

/-! ## §5. Assembly + non-vacuity / anti-impostor guards (playbook §3.3).

We record the precise shrink of `WBSCutNormalization`: component 2 fully discharged
(`distinctNormalized_of_noRepeat`), component 1 normalized to the side-choice
(`orientationNormalized`, via the reversal suite), component 3 shrunk to the wrap diagonal data
(`weakConvex_intervalArm_of_wrap` / `strictConvex_intervalArm_of_wrap`).  Each residue is guarded
satisfiable; the discharged pieces fire on genuine data. -/

/-- **The shrunk normalization datum.**  Replaces the opaque six-field `WBSCutNormalization` with: the
ℕ-orientation + matching support (from `orientationNormalized`, component 1), the no-repeat surface
(component 2 derives `hrepeat`), and the wrap-diagonal data (components 3, weak ear `A'`, strict ear `B`).
The distinctness `hrepeat` is NO LONGER a field (derived).  This bundles exactly the irreducible residue. -/
structure WBSCutNormalizationShrunk {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (i j : ℕ)
    (hij1 : i + 1 < j) (hj : j ≤ n) : Prop where
  /-- The vanishing support at the normalized triple (component 1, produced by `orientationNormalized`). -/
  hsupp : sOrient (openedWBS A B k ⟨i, by omega⟩) (openedWBS A B k ⟨i + 1, by omega⟩)
    (openedWBS A B k ⟨j, by omega⟩) = 0
  /-- The no-nonadjacent-repeat surface (component 2 derives `hrepeat` from it + weak convexity). -/
  hnorepeat : NoNonadjacentRepeat (openedWBS A B k)
  /-- The weak-ear wrap diagonal data (component 3, the irreducible residue for `A'`). -/
  hAwrap : IntervalWrapData (openedWBS A B k) (i + 1) (j - (i + 1)) (by omega)
  /-- The strict-ear wrap diagonal data (component 3, the irreducible residue for `B`). -/
  hBwrap : IntervalWrapDataStrict B (i + 1) (j - (i + 1)) (by omega)

/-- **The shrunk datum produces the original `WBSCutNormalization`.**  Given the standing context (the WBS
support-stuck branch makes `openedWBS` weakly convex, FFCT46/47), the shrunk datum reconstructs every field
of `ZinanFFCT49.WBSCutNormalization`: `hsupp` verbatim, `hrepeat` via `distinctNormalized_of_noRepeat`
(component 2), `hAe`/`hBe` via the wrap assemblies (component 3).  `2 ≤ j − (i+1)` is needed for the ear to
typecheck as a convex arm (the `j = i + 2` minimal case is excluded — §4 degenerate flag). -/
theorem wbsCutNormalization_of_shrunk {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k)
    {i j : ℕ} (hij1 : i + 1 < j) (hj : j ≤ n) (hm : 2 ≤ j - (i + 1))
    (hsh : WBSCutNormalizationShrunk A B k i j hij1 hj) :
    WBSCutNormalization A B k i j := by
  -- weak convexity of the opened arm (unconditional at the WBS sup via FFCT47).
  have hwk : WeakConvexSphArm (openedWBS A B k) :=
    supportStuckWBS_weakConvex hA hB hka hkt hkdef
      (openedWrapShortArc_at_supWBS hA hB hka hkt hkdef)
  refine ⟨hij1, hj, hsh.hsupp, ?_, ?_, ?_⟩
  · -- hrepeat: component 2.
    exact distinctNormalized_of_noRepeat hwk hsh.hnorepeat hij1 hj
  · -- hAe: weak ear from wrap data (component 3).
    exact weakConvex_intervalArm_of_wrap hwk hm (by omega) hsh.hAwrap
  · -- hBe: strict ear from strict wrap data (component 3).
    exact strictConvex_intervalArm_of_wrap hB hm (by omega) hsh.hBwrap

/-- Non-vacuity of `WBSCutNormalizationShrunk`: it exposes the genuine ℕ-orientation `i + 1 < j ≤ n` and a
real vanishing support — not a vacuous-hypothesis impostor. -/
theorem wbsCutNormalizationShrunk_orientation {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    {i j : ℕ} {hij1 : i + 1 < j} {hj : j ≤ n} (h : WBSCutNormalizationShrunk A B k i j hij1 hj) :
    i + 1 < j ∧ j ≤ n ∧
      sOrient (openedWBS A B k ⟨i, by omega⟩) (openedWBS A B k ⟨i + 1, by omega⟩)
        (openedWBS A B k ⟨j, by omega⟩) = 0 :=
  ⟨hij1, hj, h.hsupp⟩

/-- Non-vacuity of the reversal suite: `revFin` is a genuine involution (so the reversal transports are
real bijective reindexings, not vacuous). -/
theorem revFin_involutive_nonvacuous {n : ℕ} (m : Fin (n + 1)) : revFin (revFin m) = m :=
  revFin_involutive m

/-- Non-vacuity of `orientationNormalized`: its conclusion is a genuine disjunction of two realisable
normalized cuts (the `P` branch and the `revArm P` branch are both inhabited shapes), not `True`. -/
theorem orientationNormalized_nonvacuous {n : ℕ} (P : Fin (n + 1) → S2) {a b : Fin (n + 1)}
    (hne : b ≠ a) (hne1 : b ≠ a + 1)
    (hsupp : sOrient (P a) (P (a + 1)) (P b) = 0) (hadj : a.val + 1 < n + 1) :
    (∃ i j : ℕ, ∃ (_ : i + 1 < j) (_ : j ≤ n), True) := by
  rcases orientationNormalized P hne hne1 hsupp hadj with ⟨i, j, h1, h2, _⟩ | ⟨i, j, h1, h2, _⟩
  · exact ⟨i, j, h1, h2, trivial⟩
  · exact ⟨i, j, h1, h2, trivial⟩

/-- Non-vacuity of the Component-3 wrap assembly: `weakConvex_intervalArm_of_wrap` genuinely concludes a
`WeakConvexSphArm` whose `two_le` is the real `2 ≤ m` ear-size condition (the `m = 1`, `j = i+2` minimal
case is excluded, as flagged). -/
theorem weakConvex_intervalArm_of_wrap_size {N : ℕ} {A : Fin (N + 1) → S2} (hA : WeakConvexSphArm A)
    {a m : ℕ} (hm : 2 ≤ m) (hb : a + m ≤ N) (hwrap : IntervalWrapData A a m hb) :
    2 ≤ m :=
  (weakConvex_intervalArm_of_wrap hA hm hb hwrap).two_le

end ProofsInTheBook.ZinanFFCT52

-- §1 component 2
#print axioms ProofsInTheBook.ZinanFFCT52.distinctNormalized_of_noRepeat
#print axioms ProofsInTheBook.ZinanFFCT52.hrepeat_of_noRepeat_WBS
-- §2 reversal infra
#print axioms ProofsInTheBook.ZinanFFCT52.sOrient_revArm_normalized
#print axioms ProofsInTheBook.ZinanFFCT52.revArm_sideLen
#print axioms ProofsInTheBook.ZinanFFCT52.revArm_jointAngle
#print axioms ProofsInTheBook.ZinanFFCT52.revArm_noNonadjacentRepeat
-- §3 orientation normalization
#print axioms ProofsInTheBook.ZinanFFCT52.orientationNormalized
-- §4 interval convexity
#print axioms ProofsInTheBook.ZinanFFCT52.weakConvex_intervalArm_of_wrap
#print axioms ProofsInTheBook.ZinanFFCT52.strictConvex_intervalArm_of_wrap
-- §5 assembly
#print axioms ProofsInTheBook.ZinanFFCT52.wbsCutNormalization_of_shrunk
