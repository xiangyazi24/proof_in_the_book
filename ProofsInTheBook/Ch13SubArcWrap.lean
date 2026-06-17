import ProofsInTheBook.Ch13ArmVertex

/-!
# `Ch13SubArcWrap` — the WRAPPED contiguous sub-arc constructor (Ch13).

`Ch13SubArc.subArc A s t` builds the contiguous sub-arm `A s, A (s+1), …, A t` for a
*non-wrapping* cut `s < t ≤ n`.  Splitting a CLOSED cyclic link
(`StrictConvexSphArm A : Fin (n+1) → S2`) at two indices produces TWO arcs sharing the diagonal
chord; ONE of them runs *across the closing edge* `A n → A 0` and therefore cannot be presented as a
contiguous `A s … A t` range directly.  This file builds that wrapped arc and its full API.

## The composition `rotPoly ∘ subArc`

A closed strictly convex polygon is invariant (as a polygon) under cyclic relabelling of its
vertices.  `Ch13ArmVertex.rotPoly A k i := A (i + k)` (cyclic `Fin (n+1)` addition) rotates the arm
so vertex `k` becomes the new index `0`, preserving `StrictConvexSphArm`
(`rotPoly_strictConvexArm`), every cyclic edge (`rotPoly_sideLen_eq` / `all_cyclic_edges_eq`), and —
proved here — every interior joint (`rotPoly_jointAngle`).

Given a wrapping cut between indices `t < s ≤ n`, the complementary arc
`A s, A (s+1), …, A n, A 0, …, A t` (start at the larger cut index `s`, run forward THROUGH the
closing edge, end at the smaller cut index `t`) becomes, after rotating index `s` to `0`, the
*non-wrapping* range `[0 .. M]` of the rotated polygon `rotPoly A s`, where the wrap parameter is

  `M := (n + 1) - s + t`   (so `rotPoly A s` at `0` is `A s`, at `M` is `A t`).

Then `subArc (rotPoly A s) 0 M` is a genuine contiguous sub-arm.  Hence

  `subArcWrap A t s hts hsn := subArc (rotPoly A s) 0 M …`

and all of `subArcWrap_strictConvexArm` / `_sideLen` / `_jointAngle` / `_endpt` follow from the
`rotPoly_*` lemmas composed with the `subArc_*` lemmas.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.Ch13SubArc
open ProofsInTheBook.Ch13ArmVertex

namespace ProofsInTheBook.Ch13SubArcWrap

/-! ## `rotPoly_jointAngle` — cyclic rotation preserves interior joint angles.

The interior arm joints of `rotPoly A k` (the spherical angles at consecutive triples) are exactly
the parent's cyclic joints, since `(i + 1) + k = (i + k) + 1` and `(i + 2) + k = (i + k) + 2`. -/

/-- **Cyclic rotation preserves interior joints.**  The `i`-th joint of `rotPoly A k` is the
spherical angle at the parent triple starting at `⟨i.val⟩ + k`. -/
theorem rotPoly_jointAngle {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (i : Fin (n - 1)) :
    jointAngle (rotPoly A k) i
      = sphAngle (A (⟨i.val, by have := i.isLt; omega⟩ + k))
          (A (⟨i.val + 1, by have := i.isLt; omega⟩ + k))
          (A (⟨i.val + 2, by have := i.isLt; omega⟩ + k)) := by
  unfold jointAngle rotPoly
  rfl

/-! ## The wrap parameter and its basic arithmetic. -/

/-- The wrap parameter `M = (n+1) - s + t` for cut indices `t < s ≤ n`.  The wrapped arc has `M + 1`
vertices `A s, …, A n, A 0, …, A t`. -/
def wrapLen (n s t : ℕ) : ℕ := (n + 1) - s + t

/-- For `t < s ≤ n`, the wrap parameter satisfies `0 < M ≤ n`, so `subArc (rotPoly A s) 0 M` is a
valid contiguous sub-arc of the rotated polygon. -/
theorem wrapLen_lt_le {n s t : ℕ} (hts : t < s) (hsn : s ≤ n) :
    0 < wrapLen n s t ∧ wrapLen n s t ≤ n := by
  unfold wrapLen; omega

/-! ## The wrapped sub-arc.

`subArcWrap A t s hts hsn : Fin (M + 1) → S2`, `M = wrapLen n s t = (n+1) - s + t`, is the
contiguous sub-arc `[0 .. M]` of the rotated polygon `rotPoly A s`, i.e. the cyclic family
`A s, A (s+1), …, A n, A 0, …, A t`. -/

/-- The wrapped contiguous sub-arc `A s, A (s+1), …, A n, A 0, …, A t` (`t < s ≤ n`), realized as the
non-wrapping range `[0 .. M]` of the rotated polygon `rotPoly A s` (`M = (n+1) - s + t`). -/
def subArcWrap {n : ℕ} (A : Fin (n + 1) → S2) (t s : ℕ) (hts : t < s) (hsn : s ≤ n) :
    Fin (wrapLen n s t + 1) → S2 :=
  subArc (rotPoly A ⟨s, by omega⟩) 0 (wrapLen n s t)
    (wrapLen_lt_le hts hsn).1 (wrapLen_lt_le hts hsn).2

/-! ### The defining apply equation.

`subArcWrap A t s i = (rotPoly A s) ⟨i.val⟩ = A (⟨i.val⟩ + s)` (cyclic).  This is the single fact
all endpoint/side/joint lemmas reduce through. -/

/-- `subArcWrap A t s i = A (⟨i.val⟩ + s)` (cyclic `Fin (n+1)` addition). -/
theorem subArcWrap_apply {n : ℕ} (A : Fin (n + 1) → S2) (t s : ℕ) (hts : t < s) (hsn : s ≤ n)
    (i : Fin (wrapLen n s t + 1)) :
    subArcWrap A t s hts hsn i
      = A (⟨i.val, by have := i.isLt; unfold wrapLen at this; omega⟩ + ⟨s, by omega⟩) := by
  unfold subArcWrap
  rw [subArc_apply]
  show rotPoly A ⟨s, by omega⟩ ⟨0 + i.val, by have := i.isLt; unfold wrapLen at this; omega⟩ = _
  unfold rotPoly
  congr 2
  apply Fin.ext
  exact Nat.zero_add i.val

/-! ### Endpoints of the wrapped sub-arc. -/

/-- The starting vertex of the wrapped sub-arc is `A s`. -/
@[simp] theorem subArcWrap_zero {n : ℕ} (A : Fin (n + 1) → S2) (t s : ℕ) (hts : t < s)
    (hsn : s ≤ n) :
    subArcWrap A t s hts hsn 0 = A ⟨s, by omega⟩ := by
  rw [subArcWrap_apply]
  congr 1
  apply Fin.ext
  show ((0 : Fin (wrapLen n s t + 1)).val + s) % (n + 1) = s
  simp only [Fin.val_zero, Nat.zero_add, Nat.mod_eq_of_lt (show s < n + 1 by omega)]

/-- The final vertex of the wrapped sub-arc is `A t`. -/
@[simp] theorem subArcWrap_last {n : ℕ} (A : Fin (n + 1) → S2) (t s : ℕ) (hts : t < s)
    (hsn : s ≤ n) :
    subArcWrap A t s hts hsn (Fin.last (wrapLen n s t)) = A ⟨t, by omega⟩ := by
  rw [subArcWrap_apply]
  congr 1
  apply Fin.ext
  show ((Fin.last (wrapLen n s t)).val + s) % (n + 1) = t
  rw [Fin.val_last]
  unfold wrapLen
  -- ((n+1) - s + t + s) % (n+1) = (n + 1 + t) % (n+1) = t
  rw [show (n + 1) - s + t + s = (n + 1) + t by omega, Nat.add_comm (n + 1) t,
    Nat.add_mod_right, Nat.mod_eq_of_lt (show t < n + 1 by omega)]

/-! ## The wrapped sub-arc is a strictly convex arm.

`rotPoly A s` is a `StrictConvexSphArm` (`rotPoly_strictConvexArm`); the contiguous range `[0 .. M]`
of it (with `2 ≤ M`) is again a `StrictConvexSphArm` (`subArc_strictConvexArm`). -/

/-- **The wrapped sub-arc is a strictly convex arm.**  For `t < s ≤ n` with `2 ≤ M = (n+1) - s + t`,
the wrapping range `A s, …, A n, A 0, …, A t` of a strictly convex spherical arm `A` is again a
`StrictConvexSphArm`, closing diagonal `A s → A t`. -/
theorem subArcWrap_strictConvexArm {n : ℕ} (A : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (t s : ℕ) (hts : t < s) (hsn : s ≤ n)
    (hm : 2 ≤ wrapLen n s t) :
    StrictConvexSphArm (subArcWrap A t s hts hsn) := by
  unfold subArcWrap
  exact subArc_strictConvexArm (rotPoly A ⟨s, by omega⟩)
    (rotPoly_strictConvexArm hA ⟨s, by omega⟩) 0 (wrapLen n s t)
    (wrapLen_lt_le hts hsn).1 (wrapLen_lt_le hts hsn).2 (by simpa using hm)

/-! ## Side lengths, joint angles, endpoint of the wrapped sub-arc.

The interior sides/joints of `subArcWrap` are the corresponding sides/joints of the rotated polygon
`rotPoly A s` (via the `subArc_*` lemmas), hence — via `all_cyclic_edges_eq` / `rotPoly_jointAngle`
— genuine cyclic edges/joints of the original `A`. -/

/-- **Interior wrapped sides = rotated parent sides.**  The `i`-th side of `subArcWrap A t s` is the
side `sideLen (rotPoly A s) ⟨i.val⟩` of the rotated polygon, i.e. the cyclic edge
`A (⟨i.val⟩ + s) → A (⟨i.val⟩ + s + 1)`. -/
theorem subArcWrap_sideLen {n : ℕ} (A : Fin (n + 1) → S2) (t s : ℕ) (hts : t < s) (hsn : s ≤ n)
    (i : Fin (wrapLen n s t)) :
    sideLen (subArcWrap A t s hts hsn) i
      = sideLen (rotPoly A ⟨s, by omega⟩)
          ⟨i.val, by have := i.isLt; unfold wrapLen at this; omega⟩ := by
  unfold subArcWrap
  rw [subArc_sideLen]
  congr 1
  apply Fin.ext
  show 0 + i.val = i.val
  exact Nat.zero_add i.val

/-- **Interior wrapped joints = rotated parent joints.**  The `i`-th joint of `subArcWrap A t s` is
the joint `jointAngle (rotPoly A s) ⟨i.val⟩` of the rotated polygon. -/
theorem subArcWrap_jointAngle {n : ℕ} (A : Fin (n + 1) → S2) (t s : ℕ) (hts : t < s) (hsn : s ≤ n)
    (i : Fin (wrapLen n s t - 1)) :
    jointAngle (subArcWrap A t s hts hsn) i
      = jointAngle (rotPoly A ⟨s, by omega⟩)
          ⟨i.val, by have := i.isLt; unfold wrapLen at this; omega⟩ := by
  unfold subArcWrap
  rw [subArc_jointAngle]
  congr 1
  apply Fin.ext
  show 0 + i.val = i.val
  exact Nat.zero_add i.val

/-- **The wrapped arm endpoint chord is the diagonal `A t → A s`.**  `sDist (subArcWrap … 0)
(subArcWrap … (Fin.last M)) = sDist (A t) (A s)`. -/
theorem subArcWrap_endpt {n : ℕ} (A : Fin (n + 1) → S2) (t s : ℕ) (hts : t < s) (hsn : s ≤ n) :
    sDist (subArcWrap A t s hts hsn 0)
        (subArcWrap A t s hts hsn (Fin.last (wrapLen n s t)))
      = sDist (A ⟨t, by omega⟩) (A ⟨s, by omega⟩) := by
  rw [subArcWrap_zero, subArcWrap_last, sDist_comm]

/-! ## A `TwoArcSplitData` builder from a cyclic cut.

The two arcs of a `signChanges = 2` cyclic cut of the link pair `(A, B)` at indices `t < s` are the
NON-wrapping `subArc · t s` (`A t, …, A s`) and the WRAPping `subArcWrap · t s`
(`A s, …, A n, A 0, …, A t`).  Both endpoints are the diagonal chord `A t → A s`.

Everything *structural* — the four `StrictConvexSphArm` certificates, the per-arc side equalities, and
the two shared-diagonal equalities — is discharged here automatically by the `subArc_*` / `subArcWrap_*`
/ `rotPoly_*` lemmas (all genuinely derived, no posit).  The single content NOT mechanically available
from the cut indices is the **per-arc joint monotonicity** (`hmono1` / `hstrict1` / `hmono2`): which
arc opens and which closes, plus the strict witness.  This is exactly the combinatorial transport of
the global `signChanges = 2` sign pattern to the two arcs (the seam-joint comparison lying outside the
`Fin (n-1)` arm-joint family — see the §3.3 note on `TwoArcSplitData`).  So the builder takes those
three facts as genuine geometric inputs and assembles the full `TwoArcSplitData`. -/

open ProofsInTheBook.Ch13ArmVertex in
/-- **`TwoArcSplitData` from a cyclic cut at `t < s`.**  Given the link pair `(A, B)` with equal
sides and equal closing chord, two cut indices `t < s ≤ n` with both arcs non-degenerate
(`2 ≤ s - t`, `2 ≤ wrapLen n s t`), and the per-arc joint monotonicity of the `signChanges = 2`
pattern, assemble the genuine `TwoArcSplitData A B`.  Feeding it to `TwoArcSplitData.contradiction`
yields `False`. -/
noncomputable def twoArcSplitData_of_indices {n : ℕ} (hn : 1 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (t s : ℕ) (hts : t < s) (hsn : s ≤ n)
    (hm1 : 2 ≤ s - t) (hm2 : 2 ≤ wrapLen n s t)
    -- the non-wrap arc opens (`A ≤ B` joints), strictly somewhere; the wrap arc closes (`B ≤ A`).
    (hmono1 : ∀ i : Fin (s - t - 1),
        jointAngle (subArc A t s hts hsn) i ≤ jointAngle (subArc B t s hts hsn) i)
    (hstrict1 : ∃ i : Fin (s - t - 1),
        jointAngle (subArc A t s hts hsn) i < jointAngle (subArc B t s hts hsn) i)
    (hmono2 : ∀ i : Fin (wrapLen n s t - 1),
        jointAngle (subArcWrap B t s hts hsn) i ≤ jointAngle (subArcWrap A t s hts hsn) i) :
    ProofsInTheBook.Ch13ArmVertex.TwoArcSplitData A B where
  m₁ := s - t
  m₂ := wrapLen n s t
  hm₁ := hm1
  hm₂ := hm2
  Arc1 := subArc A t s hts hsn
  Brc1 := subArc B t s hts hsn
  Arc2 := subArcWrap A t s hts hsn
  Brc2 := subArcWrap B t s hts hsn
  harc1A := subArc_strictConvexArm A hA t s hts hsn hm1
  harc1B := subArc_strictConvexArm B hB t s hts hsn hm1
  harc2A := subArcWrap_strictConvexArm A hA t s hts hsn hm2
  harc2B := subArcWrap_strictConvexArm B hB t s hts hsn hm2
  hsides1 := by
    intro i
    rw [subArc_sideLen, subArc_sideLen]
    exact hsides ⟨t + i.val, by have := i.isLt; omega⟩
  hsides2 := by
    intro i
    rw [subArcWrap_sideLen, subArcWrap_sideLen]
    exact rotPoly_sideLen_eq hn A B hsides hclose ⟨s, by omega⟩ ⟨i.val, by
      have := i.isLt; unfold wrapLen at this; omega⟩
  hshareA := by
    rw [subArc_endpt, subArcWrap_endpt, sDist_comm (A ⟨t, by omega⟩) (A ⟨s, by omega⟩)]
  hshareB := by
    rw [subArc_endpt, subArcWrap_endpt, sDist_comm (B ⟨t, by omega⟩) (B ⟨s, by omega⟩)]
  hmono1 := hmono1
  hstrict1 := hstrict1
  hmono2 := hmono2

/-! ## Non-vacuity.

`subArcWrap`'s hypotheses are simultaneously satisfiable: for any `n ≥ 4`, the cut `t = 0`, `s = 2`
gives a non-wrap arc of `2 ≤ s - t` and a wrap arc of `wrapLen n 2 0 = n - 1 ≥ 2`; and the apply/
endpoint/side/joint lemmas are unconditional rewrites on any closed family `A`.  We record the wrap
parameter and the endpoint identity on a generic `A` to confirm the API is not vacuous. -/

example :
    wrapLen 4 2 0 = 3 ∧ (0 : ℕ) < wrapLen 4 2 0 ∧ wrapLen 4 2 0 ≤ 4 := by
  refine ⟨by decide, ?_, ?_⟩ <;> · unfold wrapLen; omega

example {n : ℕ} (A : Fin (n + 1) → S2) (t s : ℕ) (hts : t < s) (hsn : s ≤ n) :
    subArcWrap A t s hts hsn 0 = A ⟨s, by omega⟩
      ∧ subArcWrap A t s hts hsn (Fin.last (wrapLen n s t)) = A ⟨t, by omega⟩ :=
  ⟨subArcWrap_zero A t s hts hsn, subArcWrap_last A t s hts hsn⟩

end ProofsInTheBook.Ch13SubArcWrap

#print axioms ProofsInTheBook.Ch13SubArcWrap.subArcWrap_strictConvexArm
#print axioms ProofsInTheBook.Ch13SubArcWrap.subArcWrap_endpt
#print axioms ProofsInTheBook.Ch13SubArcWrap.subArcWrap_sideLen
#print axioms ProofsInTheBook.Ch13SubArcWrap.subArcWrap_jointAngle
#print axioms ProofsInTheBook.Ch13SubArcWrap.twoArcSplitData_of_indices
