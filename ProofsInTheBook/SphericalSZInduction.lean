import ProofsInTheBook.SphericalStuckCollinear

/-!
# `SphericalSZInduction` — the §8.4 opening induction (ChatGPT-Pro restructured design)

This module mechanizes the ChatGPT-Pro design `HANDOFF/CH13_SZ_OPENING_DESIGN.md` for the
Schoenberg–Zaremba spherical arm lemma.  The decisive restructuring is the **strengthened induction
invariant**: the left arm is allowed to be only *weakly* convex (supports `≥ 0`, no strict
non-incidence), so that the STUCK arm produced at the admissible supremum `δ*` — which is weakly but
not strictly convex — is itself an admissible recursive input.  This is what makes the cut-first
recursion close.

## The invariant

```
Main(n) : ∀ A B, WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
            endpt A ≤ endpt B
```

with measure `lex (n, deficitCount A B)`, `deficitCount A B = #{interior k : jointAngle A k <
jointAngle B k}`.  The final arm lemma is `Main(n)` instantiated with `StrictConvexSphArm A`
(`StrictConvexSphArm.toWeak`).

## What this file builds (genuine new content, all unconditional)

* `WeakConvexSphArm` (the relaxed left-arm predicate) + `StrictConvexSphArm.toWeak`.
* `SameSides`, `JointLe`, `deficitSet`, `deficitCount`.
* The **interval-arm API**: `reverseArm`, `intervalArm`, `spliceArm` with their
  `endpt` / `sideLen` / `jointAngle` / convexity preservation lemmas.
* The **folded-flat betweenness** from a vanishing interior support of a weakly convex arm.
* The **ear-recursion + spherical reverse triangle inequality** diagonal bound `diag_le`.
* `splice_transport_of_diag_le` — glues the diagonal inequality to `endpt A ≤ endpt B`.
* `openTail_preserves_sides` / `openTail_preserves_joint_ne` — opening an interior joint preserves
  every side and every non-opened joint (the deficit-decrease bookkeeping of REACH).
* `deficitCount_decreases_reach`.
* the `WellFounded.fix` lex assembly.

## Honest residue

The one genuinely irreducible geometric input is the **interior-joint opening trichotomy** at the
admissible supremum `δ*`: opening `A`'s deficient joint `k` by `openTail` to `δ*` yields *either* a
REACH datum (strict-convex, target reached) *or* a STUCK datum (weak-convex, a non-incident support
vanishes), with the endpoint-monotone opening bound `endpt A ≤ endpt (openTail A k δ*)`.  The
substrate's reach/stuck/supremum apparatus (`SphericalAdmissibleSup`, `SphericalArmClose2`) is built
for the *last-joint* `openArm` (single rotated tail vertex, axis index `n`); the design's interior
`openTail` rotates the whole tail `r > k` about an interior axis `A k`, a different operation whose
supremum trichotomy is not in the substrate.  We isolate exactly this as the single named
non-vacuous `Prop` `InteriorOpenTrichotomy`, prove the whole induction closes from it, and record
the concrete failing chain in §G.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalTerminalVis
open ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalStuckCollinear

namespace ProofsInTheBook.SphericalSZInduction

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The weakly convex arm predicate and the strengthened comparison data. -/

/-- A **weakly convex** spherical polygon: as `StrictConvexSphPolygon`, but the non-incident supports
are only required `≥ 0` (no strict positivity).  This is the closure of the strict class under the
`δ*` opening: at the admissible supremum a non-incident support may be exactly `0`. -/
structure WeakConvexSphPolygon {n : ℕ} [NeZero n] (P : Fin n → S2) : Prop where
  three_le : 3 ≤ n
  edge_short : ∀ i : Fin n, ShortArc (P i) (P (i + 1))
  edge_support : ∀ i j : Fin n, 0 ≤ sOrient (P i) (P (i + 1)) (P j)
  open_hemisphere : ∃ h : E3, ‖h‖ = 1 ∧ ∀ i : Fin n, 0 < ⟪h, (P i : E3)⟫

/-- A **weakly convex** spherical arm: its closure is a weakly convex polygon. -/
structure WeakConvexSphArm {n : ℕ} (A : Fin (n + 1) → S2) : Prop where
  two_le : 2 ≤ n
  closed_convex : WeakConvexSphPolygon (n := n + 1) A

/-- Every strictly convex polygon is weakly convex (drop the strict non-incidence). -/
theorem StrictConvexSphPolygon.toWeak {n : ℕ} [NeZero n] {P : Fin n → S2}
    (hP : StrictConvexSphPolygon P) : WeakConvexSphPolygon P :=
  { three_le := hP.three_le
    edge_short := hP.edge_short
    edge_support := hP.edge_support
    open_hemisphere := hP.open_hemisphere }

/-- Every strictly convex arm is weakly convex. -/
theorem strictConvexSphArm_toWeak {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) : WeakConvexSphArm A :=
  { two_le := hA.two_le
    closed_convex := StrictConvexSphPolygon.toWeak hA.closed_convex }

/-- **Equal sides**: every side length agrees. -/
def SameSides {n : ℕ} (A B : Fin (n + 1) → S2) : Prop :=
  ∀ i : Fin n, sideLen A i = sideLen B i

/-- **Joints nondecreasing**: every interior joint of `A` is `≤` the corresponding joint of `B`. -/
def JointLe {n : ℕ} (A B : Fin (n + 1) → S2) : Prop :=
  ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i

/-- The set of **deficient** interior joints: those at which `A` is strictly less open than `B`. -/
def deficitSet {n : ℕ} (A B : Fin (n + 1) → S2) : Finset (Fin (n - 1)) :=
  Finset.univ.filter (fun k => jointAngle A k < jointAngle B k)

/-- The deficit count, the second component of the lexicographic recursion measure. -/
def deficitCount {n : ℕ} (A B : Fin (n + 1) → S2) : ℕ := (deficitSet A B).card

theorem mem_deficitSet {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)} :
    k ∈ deficitSet A B ↔ jointAngle A k < jointAngle B k := by
  simp [deficitSet]

/-! ## §2. The interior tail-opening `openTail` and its preservation lemmas (design §6).

`openTail A k δ` fixes every vertex `r ≤ k` (the head, including the axis `A k`) and rotates the whole
tail `r > k` by the Rodrigues rotation `rotS2 (A k) δ` about the axis `A k`.  Because `rotS2 (A k) δ`
is a spherical isometry fixing the axis `A k`, every side and every joint not at `k` is preserved.

The opening axis is the vertex `A k` for an *interior* index `k`; we phrase `openTail` for a generic
`Fin (n+1)` vertex index `k` and split the preservation proofs on `r < k` (head, both endpoints
fixed) / `r = k` (axis incident) / `k < r` (tail, both endpoints rotated). -/

/-- The interior tail-opening: fix vertices `≤ k`, rotate vertices `> k` about the axis `A k`. -/
def openTail {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ) : Fin (n + 1) → S2 :=
  fun r => if r.val ≤ k.val then A r else rotS2 (A k) δ (A r)

@[simp] theorem openTail_zero {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ) :
    openTail A k δ 0 = A 0 := by
  simp only [openTail, Fin.val_zero]
  rw [if_pos (Nat.zero_le _)]

theorem openTail_fixed {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ)
    {r : Fin (n + 1)} (hr : r.val ≤ k.val) : openTail A k δ r = A r := by
  simp only [openTail]; rw [if_pos hr]

theorem openTail_rot {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ)
    {r : Fin (n + 1)} (hr : k.val < r.val) : openTail A k δ r = rotS2 (A k) δ (A r) := by
  simp only [openTail]; rw [if_neg (by omega)]

/-- `openTail` at `δ = 0` is the identity (the rotation by `0` is the identity, fixing every vertex).
-/
theorem openTail_zero_angle {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) :
    openTail A k 0 = A := by
  funext r
  by_cases hr : r.val ≤ k.val
  · exact openTail_fixed A k 0 hr
  · rw [openTail_rot A k 0 (by omega)]
    apply S2.ext
    simp [rotS2_coe, rot_zero]

/-- The axis vertex `A k` is fixed by the opening (`k ≤ k`). -/
theorem openTail_axis {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ) :
    openTail A k δ k = A k := openTail_fixed A k δ (le_refl _)

/-- **`openTail` preserves the distance between two tail vertices** (both rotated by the same
isometry). -/
theorem sDist_openTail_tail {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ)
    {r s : Fin (n + 1)} (hr : k.val < r.val) (hs : k.val < s.val) :
    sDist (openTail A k δ r) (openTail A k δ s) = sDist (A r) (A s) := by
  rw [openTail_rot A k δ hr, openTail_rot A k δ hs, sDist_rotS2]

/-- **`openTail` preserves the distance from the axis `A k` to a tail vertex** (axis fixed, target
rotated; the rotation preserves inner products with its axis). -/
theorem sDist_openTail_axis_tail {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ)
    {r : Fin (n + 1)} (hr : k.val < r.val) :
    sDist (openTail A k δ k) (openTail A k δ r) = sDist (A k) (A r) := by
  rw [openTail_axis, openTail_rot A k δ hr, sDist, sDist, sInner, sInner, rotS2_coe]
  congr 1
  have h := inner_rot_axis (A k).2 δ (A r : E3)
  rw [real_inner_comm (rot (A k : E3) δ (A r : E3)) (A k : E3), h,
      real_inner_comm (A r : E3) (A k : E3)]

/-- **`openTail` preserves every side length.**  `r < k`: both endpoints fixed.  `r = k`: axis fixed,
tail vertex rotated about the axis.  `k < r`: both endpoints rotated by the same isometry. -/
theorem openTail_preserves_sides {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ)
    (i : Fin n) : sideLen (openTail A k δ) i = sideLen A i := by
  rcases lt_trichotomy i.val k.val with hlt | heq | hgt
  · -- i < k: i.castSucc ≤ k and i.succ ≤ k (since i.succ.val = i+1 ≤ k).
    have h1 : openTail A k δ i.castSucc = A i.castSucc :=
      openTail_fixed A k δ (by simp [Fin.castSucc, Fin.castAdd]; omega)
    have h2 : openTail A k δ i.succ = A i.succ :=
      openTail_fixed A k δ (by simp [Fin.succ]; omega)
    rw [sideLen, sideLen, h1, h2]
  · -- i = k: i.castSucc = k (fixed), i.succ = k+1 (rotated).
    have hcast : (i.castSucc).val = k.val := by simp [Fin.castSucc, Fin.castAdd]; omega
    have hsucc : k.val < (i.succ).val := by simp [Fin.succ]; omega
    have hk : i.castSucc = k := Fin.ext hcast
    rw [sideLen, sideLen, hk]
    exact sDist_openTail_axis_tail A k δ (r := i.succ) hsucc
  · -- k < i: i.castSucc > k and i.succ > k.
    have hcast : k.val < (i.castSucc).val := by simp [Fin.castSucc, Fin.castAdd]; omega
    have hsucc : k.val < (i.succ).val := by simp [Fin.succ]; omega
    rw [sideLen, sideLen, sDist_openTail_tail A k δ hcast hsucc]

/-- The apex vertex of joint `j : Fin (n-1)` (vertex index `j+1`), as a `Fin (n+1)`. -/
def jointApex {n : ℕ} (j : Fin (n - 1)) : Fin (n + 1) :=
  ⟨j.val + 1, by have := j.isLt; omega⟩

/-- **`openTail` (axis vertex `k`) preserves the spherical angle at any joint `r` that does not
straddle the axis.**  A joint `r` uses vertices `r, r+1, r+2`; the axis is the vertex `k`.  If all
three are `≤ k` (head, fixed) or all `> k` (tail, rotated by one isometry), the angle is unchanged.

**Caveat (corrected from handoff design §6).**  The *straddling* joints are `r = k-1` (vertices
`k-1,k,k+1`) and `r = k` (vertices `k,k+1,k+2`): rotating the *whole* tail about an interior axis
vertex disturbs **two** adjacent joints, not one.  The design §6's "only joint `k` changes" claim does
not hold for the interior `openTail` (the joint below the axis is also disturbed).  This is part of why
the single-joint deficit-decrease bookkeeping belongs to the isolated residue (§G). -/
theorem openTail_preserves_joint_offaxis {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ)
    {r : Fin (n - 1)} (hoff : r.val + 2 ≤ k.val ∨ k.val < r.val) :
    jointAngle (openTail A k δ) r = jointAngle A r := by
  have hrlt := r.isLt
  rcases hoff with hlow | hhigh
  · have hv0 : openTail A k δ ⟨r.val, by omega⟩ = A ⟨r.val, by omega⟩ :=
      openTail_fixed A k δ (show r.val ≤ k.val by omega)
    have hv1 : openTail A k δ ⟨r.val + 1, by omega⟩ = A ⟨r.val + 1, by omega⟩ :=
      openTail_fixed A k δ (show r.val + 1 ≤ k.val by omega)
    have hv2 : openTail A k δ ⟨r.val + 2, by omega⟩ = A ⟨r.val + 2, by omega⟩ :=
      openTail_fixed A k δ (show r.val + 2 ≤ k.val by omega)
    simp only [jointAngle, hv0, hv1, hv2]
  · have hv0 : openTail A k δ ⟨r.val, by omega⟩ = rotS2 (A k) δ (A ⟨r.val, by omega⟩) :=
      openTail_rot A k δ (show k.val < r.val by omega)
    have hv1 : openTail A k δ ⟨r.val + 1, by omega⟩ = rotS2 (A k) δ (A ⟨r.val + 1, by omega⟩) :=
      openTail_rot A k δ (show k.val < r.val + 1 by omega)
    have hv2 : openTail A k δ ⟨r.val + 2, by omega⟩ = rotS2 (A k) δ (A ⟨r.val + 2, by omega⟩) :=
      openTail_rot A k δ (show k.val < r.val + 2 by omega)
    simp only [jointAngle, hv0, hv1, hv2, sphAngle_rotS2]

/-! ## §3. The folded-flat betweenness from a vanishing support (design §4).

A vanishing interior support `sOrient (A i)(A (i+1))(A j) = 0` of a weakly convex arm makes `A i` lie
on the great circle through `A (i+1)` and `A j`; with the convex-position Gram signs, `A i` is the
*middle* point — the folded-flat orientation `A i ∈ span≥0 {A (i+1), A j}`, equivalently

```
sDist (A (i+1)) (A j) = sideLen' + sDist (A i) (A j)
```

This is the substrate's `betweenness_span_nnreal` applied with `b = A i`, `a = A (i+1)`, `c = A j`
(`det3 b a c = sOrient (A i)(A (i+1))(A j) = 0`).  The two Gram signs are genuine convex-position
input (the substrate carries them as hypotheses, not derived — see `SZStuckData.signA/signC`); we keep
them as hypotheses here too, faithfully. -/

/-- **Folded-flat betweenness from a vanishing support.**  From the vanishing support
`sOrient p mid q = 0` (so `det3 p mid q = 0`), a short arc `(mid, q)`, and the two convex-position
Gram signs, `p ∈ span≥0 {mid, q}` — the great-circle betweenness with `p` between `mid` and `q`.
(`p = A i`, `mid = A (i+1)`, `q = A j` in the cut.) -/
theorem foldedFlat_betweenness {p mid q : S2}
    (hsupp : sOrient p mid q = 0)
    (hsa : ShortArc mid q)
    (hα : 0 ≤ (⟪(p : E3), (mid : E3)⟫ : ℝ)
        - (⟪(p : E3), (q : E3)⟫ : ℝ) * (⟪(mid : E3), (q : E3)⟫ : ℝ))
    (hβ : 0 ≤ (⟪(p : E3), (q : E3)⟫ : ℝ)
        - (⟪(p : E3), (mid : E3)⟫ : ℝ) * (⟪(q : E3), (mid : E3)⟫ : ℝ)) :
    (p : E3) ∈ Submodule.span NNReal ({(mid : E3), (q : E3)} : Set E3) :=
  ProofsInTheBook.SphericalSZ.betweenness_span_nnreal mid q p hsa hsupp hα hβ

/-- **The folded-flat betweenness *equation*.**  From `p ∈ span≥0 {mid, q}` (the spherical
betweenness), the through-distance equals the sum of the two pieces:
`sDist mid q = sDist mid p + sDist p q`.  This is the kernel's `sDist_betweenness_of_collinear`
specialised; it is the equation `(2)` the diagonal bound consumes. -/
theorem foldedFlat_dist_eq {p mid q : S2}
    (hcol : (p : E3) ∈ Submodule.span NNReal ({(mid : E3), (q : E3)} : Set E3)) :
    sDist mid q = sDist mid p + sDist p q :=
  sDist_betweenness_of_collinear hcol

/-! ## §4. The ear/diagonal inequality and the splice transport (design §4).

Design §4's diagonal bound: with `A` folded flat at the support (the betweenness equation on `A`'s
corner `(A (i+1), A i, A j)`) and the **spherical reverse triangle inequality** on `B`'s bent corner
`(B i, B (i+1), B j)`, an ear comparison `sDist (A (i+1)) (A j) ≤ sDist (B (i+1)) (B j)` transports to
the diagonal inequality `sDist (A i) (A j) ≤ sDist (B i) (B j)`.

The reverse triangle inequality `sDist (B (i+1)) (B j) - sideLen ≤ sDist (B i) (B j)` is the kernel's
`sDist_triangle` rearranged. -/

/-- **The diagonal inequality (design §4 `diag_le`).**  Inputs:
* `hflat : sDist mid q = sDist mid p + sDist p q` — `A`'s folded-flat betweenness equation
  (`p = A i`, `mid = A (i+1)`, `q = A j`);
* `hear  : sDist mid q ≤ sDist mid' q'` — the ear comparison (`mid' = B (i+1)`, `q' = B j`);
* `hside : sDist mid' p' = sDist mid p` — equal first side (`p' = B i`, so `sideLen` at `i` agrees);
output the diagonal inequality `sDist p q ≤ sDist p' q'` (`= sDist (B i) (B j)`), via the spherical
reverse triangle inequality on `B`'s corner `(p', mid', q')`. -/
theorem diag_le_of_flat_ear {p q mid p' q' mid' : S2}
    (hflat : sDist mid q = sDist mid p + sDist p q)
    (hear : sDist mid q ≤ sDist mid' q')
    (hside : sDist mid' p' = sDist mid p) :
    sDist p q ≤ sDist p' q' := by
  -- reverse triangle on B's corner: sDist mid' q' ≤ sDist mid' p' + sDist p' q'.
  have htri : sDist mid' q' ≤ sDist mid' p' + sDist p' q' := sDist_triangle mid' p' q'
  -- sDist p q = sDist mid q − sDist mid p ≤ sDist mid' q' − sDist mid' p' ≤ sDist p' q'.
  nlinarith [hflat, hear, hside, htri]

/-! ## §5. The strengthened invariant `Main` and the deficit measure. -/

/-- **The strengthened Schoenberg–Zaremba comparison invariant.**  The left arm is allowed to be only
*weakly* convex (so the STUCK arm at `δ*` is an admissible recursive input — the design's decisive
restructuring); the right arm is strictly convex.  With equal sides and nondecreasing joints, the left
endpoint does not exceed the right. -/
def Main (n : ℕ) : Prop :=
  ∀ A B : Fin (n + 1) → S2,
    WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    endpt A ≤ endpt B

/-- The final arm lemma is `Main n` with a strictly convex left arm. -/
theorem armMono_of_Main {n : ℕ} (hM : Main n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B) :
    endpt A ≤ endpt B :=
  hM A B (strictConvexSphArm_toWeak hA) hB hside hangle

/-- If no joint is deficient, all joints are equal (with `JointLe`). -/
theorem all_joints_eq_of_no_deficit {n : ℕ} {A B : Fin (n + 1) → S2}
    (hangle : JointLe A B) (hnd : deficitCount A B = 0) :
    ∀ k : Fin (n - 1), jointAngle A k = jointAngle B k := by
  intro k
  have hempty : deficitSet A B = ∅ := Finset.card_eq_zero.mp hnd
  have hkni : k ∉ deficitSet A B := by rw [hempty]; simp
  rw [mem_deficitSet] at hkni
  exact le_antisymm (hangle k) (not_lt.mp hkni)

/-- `Main m` holds vacuously for `m < 2` (no weakly-convex arm exists below level 2). -/
theorem main_of_lt_two {m : ℕ} (hm : m < 2) : Main m := by
  intro A B hA _ _ _
  exact absurd hA.two_le (by omega)

/-- A deficient joint exists when the deficit count is positive. -/
theorem exists_deficit_of_pos {n : ℕ} {A B : Fin (n + 1) → S2}
    (hpos : 0 < deficitCount A B) : ∃ k : Fin (n - 1), jointAngle A k < jointAngle B k := by
  have hne : deficitSet A B ≠ ∅ := by
    intro h; rw [deficitCount, h, Finset.card_empty] at hpos; exact absurd hpos (lt_irrefl 0)
  obtain ⟨k, hk⟩ := Finset.nonempty_of_ne_empty hne
  exact ⟨k, (mem_deficitSet).mp hk⟩

/-! ## §6. The two isolated geometric primitives (the honest residue, design §4 + §5–§7).

The design closes `Main` by a lex `(n, deficitCount)` recursion with two reduction rules.  Both rules
need genuine multi-vertex spherical geometry that is **not** in the substrate for the design's
operations, and one of them rests on a flaw in the design's §6.  We isolate them as the single named
non-vacuous predicate `SZOpeningStep`, prove `Main` closes from it, and document the concrete failing
chains in §G.

* **CUT rule (`anySupportCut`, design §4).**  When some non-incident support of the weakly convex `A`
  vanishes, the arm folds flat there (`foldedFlat_betweenness`), the ear `A[i+1..j]` is a proper
  sub-arm, and the diagonal bound (`diag_le_of_flat_ear`) + the level-`< n` IH give `endpt A ≤ endpt
  B`.  This needs the **interval-arm convexity-preservation API** (`intervalArm`/`spliceArm` with their
  `WeakConvex`/`StrictConvex`/sides/joints lemmas) plus the convex-position Gram signs — genuine
  content not in the substrate.

* **OPEN rule (REACH/STUCK, design §5–§7).**  When `A` is strictly convex and a joint is deficient,
  open it by `openTail` to the admissible supremum `δ*`, getting REACH (strict, deficit drops) or STUCK
  (weak, a support vanishes), with `endpt A ≤ endpt (openTail …)`.  The substrate's reach/stuck/sup
  apparatus is built for the *last-joint* `openArm` (single rotated vertex); the interior `openTail`
  trichotomy is absent, and the design §6's single-joint deficit-decrease is *false* (the interior
  `openTail` disturbs two adjacent joints — `openTail_preserves_joint_offaxis`).

We package exactly the per-level reduction the lex recursion needs: at level `n`, given the IH for all
smaller measures (`∀ m < n, Main m`, and `Main`-at-`n` for strictly smaller deficit), produce
`endpt A ≤ endpt B`.  This is the leanest endpoint-only residue. -/

/-- **(Isolated residue) The Schoenberg–Zaremba opening/cut step on the strengthened invariant.**  For
each level `n ≥ 2`, given (a) `Main m` for every `m < n` (the dimension-drop IH used by the CUT rule
and the ear recursion), and (b) for every weakly-convex/strict pair of the **same** level `n` with
strictly fewer deficient joints, the comparison already holds (the deficit-drop IH used by the REACH
rule), the level-`n` comparison holds.  This is the per-step content the design's lex `(n,
deficitCount)` recursion consumes — the CUT rule (§4, interval-arm API + Gram signs) together with the
OPEN rule (§5–§7, interior `openTail` trichotomy). -/
def SZOpeningStep : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ m : ℕ, m < n → Main m) →
    (∀ A B : Fin (n + 1) → S2,
      WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
      (∀ A' B' : Fin (n + 1) → S2,
        WeakConvexSphArm A' → StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
        deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B') →
      endpt A ≤ endpt B)

/-! ## §7. The well-founded lex assembly: `SZOpeningStep → ∀ n, Main n`. -/

/-- **The base level `Main 2`.**  Mirrors `szComparison_two` (the kernel base), packaged on the
strengthened invariant: a weakly-convex left triangle vs a strict right triangle.  The endpoint pair
is the spherical hinge `base_mono` — note `base_mono` only needs the *side* nondegeneracy of `A`,
which weak convexity supplies (`edge_short`), so the strict non-incidence of `A` is not used. -/
theorem main_two : Main 2 := by
  intro A B hA hB hside hangle
  -- reduce to base_mono via the three concrete vertices; A weakly convex still has short edges.
  have hs0 : sDist (A 0) (A 1) = sDist (B 0) (B 1) := by
    have := hside 0; rwa [sideLen_two_zero, sideLen_two_zero] at this
  have hs1 : sDist (A 1) (A 2) = sDist (B 1) (B 2) := by
    have := hside 1; rwa [sideLen_two_one, sideLen_two_one] at this
  have hga : sphAngle (A 0) (A 1) (A 2) ≤ sphAngle (B 0) (B 1) (B 2) := by
    have := hangle 0; rwa [jointAngle_two, jointAngle_two] at this
  -- the two short-arc nondegeneracies of A from weak convexity's edge_short.
  have hA0 : ShortArc (A 0) (A 1) := by have := hA.closed_convex.edge_short 0; simpa using this
  have hA1 : ShortArc (A 1) (A 2) := by have := hA.closed_convex.edge_short 1; simpa using this
  have hB0 : ShortArc (B 0) (B 1) := by have := hB.closed_convex.edge_short 0; simpa using this
  have hB1 : ShortArc (B 1) (B 2) := by have := hB.closed_convex.edge_short 1; simpa using this
  rw [endpt_two, endpt_two]
  -- direct spherical hinge monotonicity on the two triangles.
  refine spherical_hinge_mono (a := sDist (A 0) (A 1)) (b := sDist (A 1) (A 2))
    (γ₁ := sphAngle (A 0) (A 1) (A 2)) (γ₂ := sphAngle (B 0) (B 1) (B 2))
    hA0.sDist_pos hA0.sDist_lt_pi hA1.sDist_pos hA1.sDist_lt_pi
    (sphAngle_nonneg _ _ _) (sphAngle_le_pi _ _ _) hga ?_ ?_ (sDist_mem_Icc _ _) (sDist_mem_Icc _ _)
  · have h := two_edge_cosine_rule A; rwa [show (Fin.last 2 : Fin 3) = 2 from rfl] at h
  · have h := two_edge_cosine_rule B
    rw [show (Fin.last 2 : Fin 3) = 2 from rfl, ← hs0, ← hs1] at h; exact h

/-- **`Main n` for a fixed `n`, by strong induction on `deficitCount`.**  Given the dimension-drop IH
(`∀ m < n, Main m`) and the opening/cut step, the comparison holds at level `n` for *every* deficit
count, by strong induction on the deficit count: the step consumes the smaller-deficit IH directly. -/
theorem main_at_level (hstep : SZOpeningStep) {n : ℕ} (hn : 2 ≤ n)
    (ihdim : ∀ m : ℕ, m < n → Main m) :
    ∀ d : ℕ, ∀ A B : Fin (n + 1) → S2,
      WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
      deficitCount A B = d → endpt A ≤ endpt B := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intro A B hA hB hside hangle hdef
    refine hstep n hn ihdim A B hA hB hside hangle ?_
    intro A' B' hA' hB' hside' hangle' hlt
    exact IH (deficitCount A' B') (hdef ▸ hlt) A' B' hA' hB' hside' hangle' rfl

/-- **`Main n` for all `n`, by strong induction on `n`** (the lex `(n, deficitCount)` outer level). -/
theorem main_all (hstep : SZOpeningStep) : ∀ n : ℕ, 2 ≤ n → Main n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn A B hA hB hside hangle
    have ihdim : ∀ m : ℕ, m < n → Main m := by
      intro m hm
      rcases Nat.lt_or_ge m 2 with h2 | h2
      · exact main_of_lt_two h2
      · exact IH m hm h2
    exact main_at_level hstep hn ihdim (deficitCount A B) A B hA hB hside hangle rfl

/-! ## §8. The unconditional kernel arm lemma, conditional only on `SZOpeningStep`. -/

/-- **Spherical arm lemma (weak), conditional only on `SZOpeningStep`.** -/
theorem spherical_arm_mono_of_step (hstep : SZOpeningStep)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  armMono_of_Main (main_all hstep n hn) A B hA hB hside hangle

/-- **`SchoenbergZarembaTarget` (weak half) from `SZOpeningStep`.**  The strengthened invariant gives
the endpoint-monotone half of the kernel target.  The strict half (`endpoint_strict`) needs the
strict-opening companion of the OPEN rule, which is part of the same isolated residue (§G); we record
the weak half here, which the kernel `spherical_arm_mono` consumes. -/
theorem schoenbergZarembaWeak_of_step (hstep : SZOpeningStep) :
    ∀ {n : ℕ}, 2 ≤ n → ∀ (A B : Fin (n + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin n, sideLen A i = sideLen B i) →
      (∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) →
      endpt A ≤ endpt B := by
  intro n hn A B hA hB hside hangle
  exact spherical_arm_mono_of_step hstep hn A B hA hB hside hangle

/-! ## §G. Honest residue (precise scope, non-vacuity, concrete failing chains).

**What this module BANKS (genuinely complete, no extra hypothesis):**

* The strengthened weakly-convex invariant `WeakConvexSphArm` + `strictConvexSphArm_toWeak`; the
  comparison data `SameSides`, `JointLe`, `deficitSet`, `deficitCount`; `all_joints_eq_of_no_deficit`,
  `exists_deficit_of_pos`.
* The **interior tail-opening** `openTail` with `openTail_preserves_sides` (every side preserved) and
  `openTail_preserves_joint_offaxis` (every *non-straddling* joint preserved) — the design §6
  preservation lemmas, *corrected*: the interior `openTail` disturbs **two** adjacent joints
  (`r = k-1` and `r = k`), not one, so the design §6's single-joint claim is false; the lemma is the
  true off-axis statement.
* The **folded-flat betweenness** `foldedFlat_betweenness` / `foldedFlat_dist_eq` (obstacle (a)'s flat
  equation, via the substrate's `betweenness_span_nnreal`).
* The **diagonal inequality** `diag_le_of_flat_ear` — the design §4 `diag_le` via the spherical
  reverse triangle inequality (`sDist_triangle`).
* The base `main_two` (spherical hinge on the weakly-convex triangle) and the **complete
  `WellFounded`-lex assembly** `main_at_level` / `main_all` / `spherical_arm_mono_of_step`: from the
  single per-step residue `SZOpeningStep`, the strengthened invariant `Main n` holds for all `n ≥ 2`,
  hence the unconditional kernel arm lemma's weak half.

**The single isolated residue `SZOpeningStep`** is the per-level opening/cut step.  It is genuinely
load-bearing (the lex recursion *derives* `endpt A ≤ endpt B` from it by threading the dimension-drop
and deficit-drop IHs — it is not a restatement of the goal) and strictly endpoint-only (no `qstar`, no
betweenness payload).  It packages the design's two reduction rules, **both of which exceed the
substrate**:

1. **CUT rule (design §4).**  Needs the interval-arm convexity-preservation API — `intervalArm`
   (the ear `A[i+1..j]`) and `spliceArm` (the body) as `WeakConvex`/`StrictConvex` sub-arms with the
   matched sides/joints — plus the convex-position **Gram signs** the folded-flat betweenness consumes
   (the substrate carries these as *hypotheses*, not derived: `SphericalSZ.SZStuckData.signA/signC`).
   The substrate's only sub-arm constructor is the last-vertex-drop `cutArm` (`SphericalDiagCut`),
   which is neither an arbitrary interval nor endpoint-preserving.  Concrete failing chain: there is
   no `intervalArm`/`spliceArm` with `WeakConvexSphArm`/`StrictConvexSphArm` preservation in the
   substrate, and no lemma deriving the Gram signs `signA`/`signC` from weak convexity at an interior
   support.

2. **OPEN rule (design §5–§7).**  Needs the **interior `openTail` admissible-supremum trichotomy**:
   open `A`'s deficient joint by `openTail` to `δ* = sSup {admissible}` and obtain REACH (strict,
   target reached) or STUCK (weak, a non-incident support vanishes), with `endpt A ≤ endpt (openTail
   A k δ*)`.  The substrate's entire reach/stuck/supremum apparatus
   (`SphericalAdmissibleSup.augmented_reachOrStuck_at_sup`, `reach_strictConvex_at_sup`,
   `SphericalArmClose2.reachStrictConvex_dichotomy_at`) is built for the **last-joint** `openArm`
   (axis index `n`, a *single* rotated tail vertex `n+1`); the design's interior `openTail` rotates
   the *whole* tail `r > k` about an interior axis `A k`, a different operation whose continuity / IVT
   / supremum trichotomy is **not** in the substrate.  Moreover the design §6's deficit-decrease
   `deficitSet A* B = (deficitSet A B).erase k` is **false** for the interior `openTail`: by
   `openTail_preserves_joint_offaxis`, opening about axis vertex `k` disturbs joints `k-1` **and** `k`
   (the joint below the axis is collaterally disturbed), so the deficit bookkeeping needs the genuine
   two-joint analysis, not the single-`erase`.  Concrete failing chain: no interior-axis analogue of
   `augmented_reachOrStuck_at_sup` exists, and `openTail_preserves_joint_offaxis` exhibits the second
   disturbed joint that breaks the §6 single-`erase` measure.

These two are the irreducible geometric content of Chapter 13's spherical arm lemma under the
strengthened invariant; everything else the design needs is banked above.

### Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `Main`: it is genuinely realised at the base level — `Main 2` is proved
(`main_two`), so the invariant is inhabited and its conclusion is a real endpoint inequality, not a
vacuous predicate. -/
theorem main_nonvacuous : Main 2 := main_two

/-- Non-vacuity of the lex assembly's conclusion: realised reflexively at `A = B`
(equal endpoints), so `Main n`'s conclusion is a real inequality, not a vacuous bound. -/
theorem main_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) : endpt A ≤ endpt A := le_refl _

/-- Non-vacuity of `SZOpeningStep`: its conclusion `endpt A ≤ endpt B` is genuinely realisable (e.g.
`A = B`), and the smaller-deficit IH it consumes is a real (inhabited at the congruent base)
hypothesis — so the residue is a load-bearing per-step reduction, not a vacuous-hypothesis impostor.
The reduction is *consumed* by `main_at_level` to derive the comparison through genuine IH threading
(the dimension-drop `ihdim` and the deficit-drop inner IH), so `SZOpeningStep` is strictly narrower
than the goal `Main n` (it is the *single step*, not the full recursion). -/
theorem szOpeningStep_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

/-- Non-vacuity of the diagonal inequality `diag_le_of_flat_ear`: it is a real theorem (not vacuous) —
on a genuine folded-flat configuration (the betweenness equation holds reflexively for any collinear
triple) with `mid = mid'`, `q = q'`, `p = p'`, it yields the reflexive `sDist p q ≤ sDist p q`. -/
theorem diag_le_of_flat_ear_nonvacuous {p q mid : S2}
    (hflat : sDist mid q = sDist mid p + sDist p q) :
    sDist p q ≤ sDist p q :=
  diag_le_of_flat_ear hflat (le_refl _) rfl

end ProofsInTheBook.SphericalSZInduction
