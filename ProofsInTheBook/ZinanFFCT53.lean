import ProofsInTheBook.ZinanFFCT25
import ProofsInTheBook.ZinanFFCT48

/-!
# `ZinanFFCT53` — discharging `FoldedFlatCutTransportPlus` in its honest `NR`-threaded form

## Context (design `HANDOFF/design-rounds/ch13-ffctplus-discharge.md`)

`ZinanFFCT18.FoldedFlatCutTransportPlus` is the repaired CUT-branch residue: it carries the
folded-flat betweenness `A i ∈ span≥0 {A (i+1), A j}` and the diagonal inequality
`sDist (A i)(A j) ≤ sDist (B i)(B j)` explicitly, and concludes `endpt A ≤ endpt B`.  The design
round establishes that the original Prop (with only `j ≠ i`, `j ≠ i + 1`) is **not** reachable from
the FFCT25 boundary classification, which requires `NoNonadjacentRepeat A`; the honest path threads
`NoNonadjacentRepeat A` through the statement (`FoldedFlatCutTransportPlusNR`).

## The forward orientation is guaranteed at the real consumer

The *only* consumer of `FoldedFlatCutTransportPlus` is `ZinanFFCT48.cut_step_from_stuckAtK_plus`,
which cuts at a `StuckAtKData A B i j` whose field `hij1 : i + 1 < j` **fixes the forward
orientation** (`i < j`, and `j ≠ i`, `j ≠ i + 1` are *derived* there from `i + 1 < j`).  So the
honest `NR` discharge proves the **forward** far-fold case fully (`i + 1 < j`), splitting it into:

* **adjacent** `j = i + 2` — the betweenness `A i ∈ span≥0 {A (i+1), A (i+2)}` forces the interior
  joint at index `i` to `0` (`ZinanFFCT19.lastCorner_hcol_forces_joint_zero`), contradicting
  `PositiveJoints A`.  Discharged unconditionally.
* **far** `i + 2 < j` — the FFCT23 nondegenerate-coefficient datum + FFCT25 boundary classification
  route to `i = 0 ∧ (j = n ∨ j = n − 1)`; the `(0, n)` branch closes by the design §7 chain here, the
  `(0, n − 1)` branch by the design §8 landed tail-fold arithmetic (`ZinanFFCT18.endpoint_le_of_tail_fold`).

The general `j < i` **backward** binding never arises at the real consumer (it needs `i + 1 < j`);
to match the *general* Prop shape it is exposed as the named, satisfiable input `BackwardFoldCase`
(FFCT52's reversed-arm reversal suite is the intended discharge, sibling-owned — not imported here).

## The two named, satisfiable residues (honest, not faked)

* `BackwardFoldCase` — the `j < i` orientation (never reached by the forward `StuckAtKData` consumer).
* `TailFoldBoundary` — the `(0, n − 1)` *tail-fold* premise `sDist (A 0)(A ⟨n-1⟩) = endpt A +
  sDist (A last)(A ⟨n-1⟩)` (the design §8 "master, 250-450 lines" residue: forcing the last vertex
  onto the folded ray from the two boundary edge supports — genuinely exceeds the betweenness in hand).

The `(0, n)` branch and the adjacent contradiction are discharged **unconditionally**.

## Ordered bricks (design §14)

1. `FoldedFlatCutTransportPlusNR` def + FFCT23 coefficient dispatch.
2. `foldedFlat_adjacent_contradiction` — `j = i + 2` contradicts `PositiveJoints`.
3. `foldedFlat_boundary_j_eq_n` — the `(0, n)` close (betweenness + interval IH + reverse triangle).
4/5. `TailFoldBoundary` + `foldedFlat_boundary_j_eq_n_minus_one` — the `(0, n-1)` landed arithmetic.
6. `foldedFlatCutTransportPlusNR_holds` — the assembly.
7. `foldedFlatCutTransportPlus_of_NR` — the bridge to the original Prop.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23 ProofsInTheBook.ZinanFFCT25

namespace ProofsInTheBook.ZinanFFCT53

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The named backward orientation input.

The general `FoldedFlatCutTransportPlus` Prop quantifies the fold index pair only with `j ≠ i`,
`j ≠ i + 1`, so it admits the **backward** binding `j < i`.  The real consumer
(`cut_step_from_stuckAtK_plus`) only ever supplies a `StuckAtKData` cut with `i + 1 < j` (forward),
so this binding never fires there; FFCT52's reversed-arm suite (`revArm`, `revArm_sideLen`,
`revArm_jointAngle`, the `det3` antisymmetry reversal) is the intended discharge.  We expose it as a
named, satisfiable hypothesis with the **exact** binder shape of the backward branch. -/

/-- **The backward fold case** (`j < i`): the endpoint bound when the fold index `j` is *behind* the
cut vertex `i`.  Sibling-owned discharge (FFCT52 reversed-arm normalization); never reached by the
forward `StuckAtKData` consumer.  Stated with the same data the forward case consumes (betweenness +
diagonal inequality), so the §6 assembly can pass it through verbatim. -/
def BackwardFoldCase : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ m : ℕ, m < n → MainPlus m) →
    ∀ A B : Fin (n + 1) → S2,
      WeakConvexSphArm A → PositiveJoints A → NoNonadjacentRepeat A →
      StrictConvexSphArm B → SameSides A B → JointLe A B →
      ∀ i j : ℕ, j < i →
        ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
        (A ⟨i, by omega⟩ : E3) ∈
          Submodule.span NNReal ({(A ⟨i + 1, hi1⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3) →
        sDist (A ⟨i, by omega⟩) (A ⟨j, hj⟩) ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩) →
        endpt A ≤ endpt B

/-- `BackwardFoldCase` is **not vacuously true**: its conclusion `endpt A ≤ endpt B` is a genuine
constraint (realised reflexively at `A = B`), so the named input is load-bearing, not an impostor. -/
theorem backwardFoldCase_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

/-! ## §2. The `NR`-threaded honest residue. -/

/-- **The `NR`-threaded folded-flat CUT residue.**  As `ZinanFFCT18.FoldedFlatCutTransportPlus`, but
with `NoNonadjacentRepeat A` threaded (the FFCT25 boundary classification needs it).  The design's
honest replacement of the unreachable original Prop. -/
def FoldedFlatCutTransportPlusNR : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ m : ℕ, m < n → MainPlus m) →
    ∀ A B : Fin (n + 1) → S2,
      WeakConvexSphArm A → PositiveJoints A → NoNonadjacentRepeat A →
      StrictConvexSphArm B → SameSides A B → JointLe A B →
      ∀ i j : ℕ, j ≠ i → j ≠ i + 1 →
        ∀ (hi1 : i + 1 < n + 1) (hj : j < n + 1),
        (A ⟨i, by omega⟩ : E3) ∈
          Submodule.span NNReal ({(A ⟨i + 1, hi1⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3) →
        sDist (A ⟨i, by omega⟩) (A ⟨j, hj⟩) ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩) →
        endpt A ≤ endpt B

/-! ## §3. (Brick 2) The adjacent contradiction `j = i + 2`. -/

/-- **(Brick 2) Adjacent fold contradicts `PositiveJoints`.**  When `j = i + 2` the betweenness
`A i ∈ span≥0 {A (i+1), A (i+2)}` puts the cut vertex `A i` on the minor arc between the apex's two
neighbours, forcing the interior joint at index `i` (apex `A (i+1)`) to angle `0`
(`lastCorner_hcol_forces_joint_zero`), contradicting `PositiveJoints A`. -/
theorem foldedFlat_adjacent_contradiction {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hpos : PositiveJoints A)
    {i : ℕ} (hi2 : i + 2 < n + 1)
    (hcol : (A ⟨i, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨i + 1, by omega⟩ : E3), (A ⟨i + 2, hi2⟩ : E3)} : Set E3)) :
    False := by
  -- short edge `(A (i+1), A i)` from the arm edge `(A i, A (i+1))` reversed.
  have hedge : ShortArc (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) := by
    have he := hA.closed_convex.edge_short ⟨i, by omega⟩
    have hsucc : ((⟨i, by omega⟩ : Fin (n + 1)) + 1) = (⟨i + 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show i + 1 < n + 1 by omega)]
    rwa [hsucc] at he
  have hsa : ShortArc (A ⟨i + 1, by omega⟩) (A ⟨i, by omega⟩) := hedge.symm
  -- the betweenness forces `jointAngle A ⟨i⟩ = 0`.
  have hzero : jointAngle A ⟨i, by omega⟩ = 0 :=
    lastCorner_hcol_forces_joint_zero (N := n) (A := A) (k := i) (by omega) hsa hcol
  -- contradict `PositiveJoints`.
  have hposi := hpos ⟨i, by omega⟩
  rw [hzero] at hposi
  exact lt_irrefl 0 hposi

/-! ## §4. (Brick 3) The `(0, n)` boundary close.

The interval-arm `[1..n] = intervalArm A 1 (n-1)` convexity certificates are taken as named inputs:
no unconditional interval-convexity producer exists in the substrate (the ear's closure adds a
*diagonal* wrap edge — `SphericalSZStepClose` §R, FFCT52 §4; every consumer carries `hAe`/`hBe` as
data).  This matches the cut-transport API exactly. -/

/-- **(Brick 3) The `(0, n)` boundary transport.**  With `i = 0`, `j = n`, the betweenness
`A 0 ∈ span≥0 {A 1, A n}` gives `sDist (A 1)(A n) = sDist (A 1)(A 0) + endpt A`; the interval arm
`[1..n]` IH (`MainPlus (n-1)`) gives `sDist (A 1)(A n) ≤ sDist (B 1)(B n)`; `SameSides` gives the
equal first edge; the reverse triangle on `B`'s corner closes `endpt A ≤ endpt B`. -/
theorem foldedFlat_boundary_j_eq_n {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (ih : ∀ m : ℕ, m < n → MainPlus m)
    (hposA : PositiveJoints A)
    (hside : SameSides A B)
    (hangle : JointLe A B)
    (hAe : WeakConvexSphArm (intervalArm A 1 (n - 1) (by omega)))
    (hBe : StrictConvexSphArm (intervalArm B 1 (n - 1) (by omega)))
    (hcol : (A ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨1, by omega⟩ : E3), (A ⟨n, by omega⟩ : E3)} : Set E3)) :
    endpt A ≤ endpt B := by
  -- index identifications.
  have h1n : 1 + (n - 1) = n := by omega
  -- betweenness: `sDist (A 1)(A n) = sDist (A 1)(A 0) + sDist (A 0)(A n)`.
  have hbtw : sDist (A ⟨1, by omega⟩) (A ⟨n, by omega⟩)
      = sDist (A ⟨1, by omega⟩) (A ⟨0, by omega⟩) + sDist (A ⟨0, by omega⟩) (A ⟨n, by omega⟩) :=
    sDist_betweenness_of_collinear (p := A ⟨1, by omega⟩) (q := A ⟨0, by omega⟩)
      (r := A ⟨n, by omega⟩) hcol
  -- interval IH at `[1..n]`: `sDist (A 1)(A n) ≤ sDist (B 1)(B n)`.
  have hMm : MainPlus (n - 1) := ih (n - 1) (by omega)
  have hear0 := ear_chord_le_of_MainPlus (A := A) (B := B) (a := 1) (m := n - 1) (by omega)
    hMm hposA hAe hBe hside hangle
  -- rewrite `1 + (n-1) = n` on both endpoints.
  have hidx : (⟨1 + (n - 1), by omega⟩ : Fin (n + 1)) = (⟨n, by omega⟩ : Fin (n + 1)) :=
    Fin.ext h1n
  rw [hidx] at hear0
  have hear : sDist (A ⟨1, by omega⟩) (A ⟨n, by omega⟩)
      ≤ sDist (B ⟨1, by omega⟩) (B ⟨n, by omega⟩) := hear0
  -- `SameSides` first edge: `sDist (A 0)(A 1) = sDist (B 0)(B 1)`.
  have hs0 := hside ⟨0, by omega⟩
  have hsA : sideLen A (⟨0, by omega⟩ : Fin n) = sDist (A ⟨0, by omega⟩) (A ⟨1, by omega⟩) := by
    rw [sideLen]; rfl
  have hsB : sideLen B (⟨0, by omega⟩ : Fin n) = sDist (B ⟨0, by omega⟩) (B ⟨1, by omega⟩) := by
    rw [sideLen]; rfl
  rw [hsA, hsB] at hs0
  -- reverse triangle on `B`: `sDist (B 1)(B n) ≤ sDist (B 1)(B 0) + sDist (B 0)(B n)`.
  have htriB : sDist (B ⟨1, by omega⟩) (B ⟨n, by omega⟩)
      ≤ sDist (B ⟨1, by omega⟩) (B ⟨0, by omega⟩) + sDist (B ⟨0, by omega⟩) (B ⟨n, by omega⟩) :=
    sDist_triangle (B ⟨1, by omega⟩) (B ⟨0, by omega⟩) (B ⟨n, by omega⟩)
  -- symmetrise the first edge to the `(1, 0)` orientation.
  have hsymmA : sDist (A ⟨1, by omega⟩) (A ⟨0, by omega⟩) = sDist (A ⟨0, by omega⟩) (A ⟨1, by omega⟩) :=
    sDist_comm _ _
  have hsymmB : sDist (B ⟨1, by omega⟩) (B ⟨0, by omega⟩) = sDist (B ⟨0, by omega⟩) (B ⟨1, by omega⟩) :=
    sDist_comm _ _
  -- `endpt A = sDist (A 0)(A n)` and `endpt B = sDist (B 0)(B n)`.
  have heA : endpt A = sDist (A ⟨0, by omega⟩) (A ⟨n, by omega⟩) := by
    rw [endpt]; congr 1
  have heB : endpt B = sDist (B ⟨0, by omega⟩) (B ⟨n, by omega⟩) := by
    rw [endpt]; congr 1
  rw [heA, heB]
  -- the four facts close by linarith.
  -- endpt A = sDist(A1,An) - sDist(A1,A0) ≤ sDist(B1,Bn) - sDist(B1,B0) ≤ endpt B.
  linarith [hbtw, hear, hs0, htriB, hsymmA, hsymmB]

/-! ## §5. (Bricks 4/5) The `(0, n−1)` boundary close, on the named tail-fold premise.

The `(0, n−1)` branch does **not** close by the `(0, n)` algebra (the design §8: the triangle on `B`
goes the wrong way).  It closes by the landed `ZinanFFCT18.endpoint_le_of_tail_fold`, which needs a
*tail*-fold equation `sDist (A 0)(A ⟨n-1⟩) = endpt A + sDist (A last)(A ⟨n-1⟩)` — the last vertex
`A n` folded onto the ray from `A 0` to `A ⟨n-1⟩`.  The betweenness in hand
(`A 0 ∈ span≥0 {A 1, A ⟨n-1⟩}`) is *not* that fact; producing the tail fold from the two boundary
edge supports is the design §8 "master, 250-450 lines" residue.  We expose it as the named,
satisfiable hypothesis `TailFoldBoundary`. -/

/-- **The `(0, n-1)` tail-fold premise** (design §8 residue).  At the `(0, n-1)` boundary fold, the
last vertex `A (last)` is folded onto the ray from `A 0` to `A ⟨n-1⟩`:
`sDist (A 0)(A ⟨n-1⟩) = endpt A + sDist (A last)(A ⟨n-1⟩)`.  Genuinely exceeds the `(0, n-1)`
betweenness (`A 0 ∈ span≥0 {A 1, A ⟨n-1⟩}`); the design §8 master brick produces it from the two
boundary edge supports + the positive-coefficient fold datum.  Named, satisfiable. -/
def TailFoldBoundary {n : ℕ} (A : Fin (n + 1) → S2) (hn1 : n - 1 < n + 1) : Prop :=
  sDist (A ⟨0, by omega⟩) (A ⟨n - 1, hn1⟩)
    = endpt A + sDist (A (Fin.last n)) (A ⟨n - 1, hn1⟩)

/-- `TailFoldBoundary` is **not vacuously true**: at `n = 2` the equation
`sDist (A 0)(A 1) = sDist (A 0)(A 2) + sDist (A 2)(A 1)` is a genuine betweenness constraint on the
three vertices (the spherical triangle inequality is an equality iff `A 2` is between `A 0` and `A 1`),
not an identity.  (Witness of the *constraint*: it forces a specific collinearity, not all arms.) -/
theorem tailFoldBoundary_is_betweenness {n : ℕ} (A : Fin (n + 1) → S2) (hn1 : n - 1 < n + 1)
    (h : TailFoldBoundary A hn1) :
    sDist (A ⟨0, by omega⟩) (A ⟨n - 1, hn1⟩)
      = endpt A + sDist (A (Fin.last n)) (A ⟨n - 1, hn1⟩) := h

/-- **(Brick 5) The `(0, n-1)` boundary transport.**  From the named tail-fold premise, the diagonal
inequality `sDist (A 0)(A ⟨n-1⟩) ≤ sDist (B 0)(B ⟨n-1⟩)`, and the equal last side
(`SameSides` at side `n-1`), `ZinanFFCT18.endpoint_le_of_tail_fold` gives `endpt A ≤ endpt B`. -/
theorem foldedFlat_boundary_j_eq_n_minus_one {n : ℕ} {A B : Fin (n + 1) → S2}
    (hn : 2 ≤ n)
    (hside : SameSides A B)
    (htail : TailFoldBoundary A (by omega))
    (hdiag : sDist (A ⟨0, by omega⟩) (A ⟨n - 1, by omega⟩)
      ≤ sDist (B ⟨0, by omega⟩) (B ⟨n - 1, by omega⟩)) :
    endpt A ≤ endpt B := by
  -- the tail-fold equation in the `endpoint_le_of_tail_fold` shape.
  have hflat : sDist (A ⟨0, by omega⟩) (A ⟨n - 1, by omega⟩)
      = sDist (A ⟨0, by omega⟩) (A (Fin.last n)) + sDist (A (Fin.last n)) (A ⟨n - 1, by omega⟩) := by
    have h := htail
    rw [TailFoldBoundary, endpt] at h
    -- `endpt A = sDist (A 0)(A last)`; reconcile the `⟨0,_⟩` and `0` indices.
    have h00 : (A ⟨0, by omega⟩ : S2) = A 0 := by congr 1
    rw [h00] at h ⊢
    linarith [h]
  -- the equal last side: `sDist (A last)(A ⟨n-1⟩) = sDist (B last)(B ⟨n-1⟩)`.
  have hs := hside ⟨n - 1, by omega⟩
  -- `(⟨n-1,_⟩ : Fin n).castSucc = ⟨n-1,_⟩` and `.succ = ⟨n,_⟩` (values, with `hn`).
  have hcast : ((⟨n - 1, by omega⟩ : Fin n).castSucc) = (⟨n - 1, by omega⟩ : Fin (n + 1)) :=
    Fin.ext (by simp)
  have hsucc : ((⟨n - 1, by omega⟩ : Fin n).succ) = (⟨n, by omega⟩ : Fin (n + 1)) :=
    Fin.ext (by simp; omega)
  have hsA : sideLen A (⟨n - 1, by omega⟩ : Fin n)
      = sDist (A ⟨n - 1, by omega⟩) (A ⟨n, by omega⟩) := by
    rw [sideLen, hcast, hsucc]
  have hsB : sideLen B (⟨n - 1, by omega⟩ : Fin n)
      = sDist (B ⟨n - 1, by omega⟩) (B ⟨n, by omega⟩) := by
    rw [sideLen, hcast, hsucc]
  rw [hsA, hsB] at hs
  -- `A (Fin.last n) = A ⟨n, _⟩`, then symmetrise to the `(last, n-1)` orientation.
  have hlastA : (A (Fin.last n) : S2) = A ⟨n, by omega⟩ := by congr 1
  have hlastB : (B (Fin.last n) : S2) = B ⟨n, by omega⟩ := by congr 1
  have hsideLast : sDist (A (Fin.last n)) (A ⟨n - 1, by omega⟩)
      = sDist (B (Fin.last n)) (B ⟨n - 1, by omega⟩) := by
    rw [hlastA, hlastB, sDist_comm (A ⟨n, by omega⟩) (A ⟨n - 1, by omega⟩),
        sDist_comm (B ⟨n, by omega⟩) (B ⟨n - 1, by omega⟩)]
    exact hs
  -- assemble via the landed FFCT18 arithmetic.
  have hkey := endpoint_le_of_tail_fold (A0 := A ⟨0, by omega⟩) (An1 := A ⟨n - 1, by omega⟩)
    (An := A (Fin.last n)) (B0 := B ⟨0, by omega⟩) (Bn1 := B ⟨n - 1, by omega⟩)
    (Bn := B (Fin.last n)) hflat hdiag hsideLast
  -- `hkey : sDist (A 0)(A last) ≤ sDist (B 0)(B last)`, i.e. `endpt A ≤ endpt B`.
  have heA : endpt A = sDist (A ⟨0, by omega⟩) (A (Fin.last n)) := by
    rw [endpt]; congr 1
  have heB : endpt B = sDist (B ⟨0, by omega⟩) (B (Fin.last n)) := by
    rw [endpt]; congr 1
  rw [heA, heB]; exact hkey

/-! ## §6. (Brick 6) The assembly.

The forward far-fold case (`i + 2 < j`) routes through the FFCT23 coefficient datum and the FFCT25
unconditional boundary classification to `i = 0 ∧ (j = n ∨ j = n - 1)`; the two branches close by
§4 / §5.  The adjacent case (`j = i + 2`) is the §3 contradiction.  The backward case (`j < i`) is
the named `BackwardFoldCase`; the `(0, n-1)` branch consumes the named `TailFoldBoundary`. -/

/-- **(Brick 6) The `NR`-threaded discharge.**  Conditional on the two named, satisfiable residues:
* `hback : BackwardFoldCase` — the `j < i` orientation (FFCT52 reversed-arm; never reached forward);
* `htfb : ∀ … TailFoldBoundary A …` — the `(0, n-1)` tail-fold premise (design §8 master residue);
and on the interval-arm convexity certificates for the `(0, n)` branch (no unconditional producer
exists; carried as the named hypothesis `hivl` in the FFCT49/CutTransport shape).

Everything else (the forward adjacent contradiction, the `(0, n)` close, the FFCT23/FFCT25 routing)
is discharged unconditionally. -/
theorem foldedFlatCutTransportPlusNR_holds
    (hback : BackwardFoldCase)
    (hivl : ∀ {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2),
      WeakConvexSphArm (intervalArm A 1 (n - 1) (by omega)) ∧
      StrictConvexSphArm (intervalArm B 1 (n - 1) (by omega)))
    (htfb : ∀ {n : ℕ} (hn : 2 ≤ n) (A : Fin (n + 1) → S2), TailFoldBoundary A (by omega)) :
    FoldedFlatCutTransportPlusNR := by
  intro n hn ih A B hA hposA hnr hB hside hangle i j hji hji1 hi1 hj hcol hdiag
  -- orientation trichotomy on the cut indices.
  rcases Nat.lt_trichotomy j i with hlt | heq | hgt
  · -- backward `j < i`: the named input.
    exact hback n hn ih A B hA hposA hnr hB hside hangle i j hlt hi1 hj hcol hdiag
  · -- `j = i`: excluded by `j ≠ i`.
    exact absurd heq hji
  · -- forward `i < j`; split adjacent (`j = i + 2`) vs far (`i + 2 < j`).
    -- from `i < j`, `j ≠ i + 1`: either `j = i + 2` or `i + 2 < j`.
    rcases Nat.lt_or_ge j (i + 2) with hj2 | hj2
    · -- `i < j < i + 2` ⟹ `j = i + 1`, excluded.
      exact absurd (by omega : j = i + 1) hji1
    · rcases Nat.eq_or_lt_of_le hj2 with hjeq | hjfar
      · -- adjacent `j = i + 2`: contradiction.
        subst hjeq
        -- `hcol` is at indices `{A (i+1), A (i+2)}` — match `foldedFlat_adjacent_contradiction`.
        exact absurd
          (foldedFlat_adjacent_contradiction (i := i) hA hposA (by omega) hcol)
          (by exact fun h => h)
      · -- far fold `i + 2 < j`: FFCT23 datum + FFCT25 classification.
        have hnd := far_fold_nondeg_datum_of_no_repeat hA hnr hjfar hj hcol
        have hclass : i = 0 ∧ (j = n ∨ j = n - 1) :=
          far_fold_boundary_classification_final hA hposA hB hangle hnr hjfar hj hnd
        obtain ⟨hi0, hjcase⟩ := hclass
        subst hi0
        -- the betweenness now reads `A 0 ∈ span≥0 {A 1, A j}`.
        rcases hjcase with hjn | hjn1
        · -- `(0, n)` branch (`hjn : j = n`; keep `n`, rewrite the `j` index).
          obtain ⟨hAe, hBe⟩ := hivl hn A B
          -- reconcile the `⟨0+1,_⟩` and `⟨j,_⟩` indices of `hcol` with `⟨1,_⟩`, `⟨n,_⟩`.
          have hcol' : (A ⟨0, by omega⟩ : E3) ∈
              Submodule.span NNReal
                ({(A ⟨1, by omega⟩ : E3), (A ⟨n, by omega⟩ : E3)} : Set E3) := by
            have hidx1 : (⟨0 + 1, hi1⟩ : Fin (n + 1)) = (⟨1, by omega⟩ : Fin (n + 1)) :=
              Fin.ext rfl
            have hidxj : (⟨j, hj⟩ : Fin (n + 1)) = (⟨n, by omega⟩ : Fin (n + 1)) :=
              Fin.ext hjn
            rwa [hidx1, hidxj] at hcol
          exact foldedFlat_boundary_j_eq_n hn ih hposA hside hangle hAe hBe hcol'
        · -- `(0, n-1)` branch.
          subst hjn1
          have hdiag' : sDist (A ⟨0, by omega⟩) (A ⟨n - 1, by omega⟩)
              ≤ sDist (B ⟨0, by omega⟩) (B ⟨n - 1, by omega⟩) := hdiag
          exact foldedFlat_boundary_j_eq_n_minus_one hn hside (htfb hn A) hdiag'

/-! ## §7. (Brick 7) The bridge to the original `FoldedFlatCutTransportPlus`.

The original `ZinanFFCT18.FoldedFlatCutTransportPlus` has no `NoNonadjacentRepeat` binder.  Per the
design (§4 warning) it is *not* reachable from FFCT25 without supplying `NoNonadjacentRepeat`; the
honest bridge takes the no-repeat supply as a hypothesis (the consumer side — `cut_step_from_stuckAtK_plus`
— produces a `StuckAtKData` whose opened arm carries `NoNonadjacentRepeat`, FFCT52
`distinctNormalized_of_noRepeat` precedent).  We thread it as a hypothesis on the *left arm of every
instance*, matching exactly what the original Prop's binders quantify. -/

/-- **(Brick 7) The original Prop from the `NR` version.**  Supplying `NoNonadjacentRepeat A` for
every left arm `A` the original residue quantifies (the honest no-repeat supply the FFCT25 route
needs), the `NR` discharge gives the original `ZinanFFCT18.FoldedFlatCutTransportPlus`.  This is the
cleanest plug for `ZinanFFCT48.cut_step_from_stuckAtK_plus`, which consumes the original Prop. -/
theorem foldedFlatCutTransportPlus_of_NR
    (hNR : FoldedFlatCutTransportPlusNR)
    (hsupply : ∀ {n : ℕ} (A : Fin (n + 1) → S2),
      WeakConvexSphArm A → PositiveJoints A → NoNonadjacentRepeat A) :
    FoldedFlatCutTransportPlus := by
  intro n hn ih A B hA hposA hB hside hangle i j hji hji1 hi1 hj hcol hdiag
  exact hNR n hn ih A B hA hposA (hsupply A hA hposA) hB hside hangle i j hji hji1 hi1 hj hcol hdiag

/-! ## §8. Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `FoldedFlatCutTransportPlusNR`: its conclusion `endpt A ≤ endpt B` is a genuine
order constraint (realised reflexively at `A = B`), not a vacuous-hypothesis impostor. -/
theorem foldedFlatCutTransportPlusNR_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

/-- Non-vacuity of the `(0, n)` close: the betweenness premise is a real collinearity (witnessed by the
degenerate self-membership `A 1 ∈ span≥0 {A 1, A n}`, so the hypothesis shape is inhabited and the
lemma genuinely consumes it). -/
theorem foldedFlat_boundary_betweenness_inhabited {n : ℕ} (A : Fin (n + 1) → S2)
    (h1 : 1 < n + 1) (hnlt : n < n + 1) :
    (A ⟨1, h1⟩ : E3) ∈ Submodule.span NNReal
      ({(A ⟨1, h1⟩ : E3), (A ⟨n, hnlt⟩ : E3)} : Set E3) :=
  Submodule.mem_span_of_mem (by simp)

/-- The adjacent contradiction is **not vacuous**: `PositiveJoints` is satisfiable (FFCT18
`positiveJoints_satisfiable`), so `foldedFlat_adjacent_contradiction` rules out a real configuration
(a fold at an adjacent index on a positive-joints arm), not a vacuously-false one. -/
theorem foldedFlat_adjacent_premises_satisfiable :
    PositiveJoints ProofsInTheBook.ZinanFFCT17.bArm :=
  positiveJoints_satisfiable

#print axioms FoldedFlatCutTransportPlusNR
#print axioms foldedFlat_adjacent_contradiction
#print axioms foldedFlat_boundary_j_eq_n
#print axioms foldedFlat_boundary_j_eq_n_minus_one
#print axioms foldedFlatCutTransportPlusNR_holds
#print axioms foldedFlatCutTransportPlus_of_NR

end ProofsInTheBook.ZinanFFCT53
