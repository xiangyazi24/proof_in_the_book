import ProofsInTheBook.SphericalDiagCut

/-!
# `Ch13SubArc` — the contiguous sub-arc constructor (the missing substrate API)

For a closed strictly convex spherical arm `A : Fin (n+1) → S2` and two cut indices `s < t ≤ n`, the
contiguous range `A s, A (s+1), …, A t` is itself a strictly convex spherical **arm** (an open chain
whose closing diagonal is `A s → A t`).  This file builds the constructor and its full API:

* `subArc A s t hst htn : Fin ((t - s) + 1) → S2` — the contiguous sub-family
  (arm parameter `m := t - s`, vertices `A s … A t`).
* `subArc_strictConvexArm` — the convexity transport: each of the five `StrictConvexSphPolygon`
  fields of the sub-arm specializes a parent field; the single *new* fact is the closing diagonal
  `A s → A t`, certified by `cut_diagonal_supports` (the `i < j < k` cyclic-triple positivity of a
  strictly convex polygon, unconditional).
* `subArc_sideLen` — interior arm sides are parent sides `A(s+i) → A(s+i+1)`.
* `subArc_jointAngle` — interior arm joints are parent joints at `A(s+i+1)`.
* `subArc_endpt` — the arm endpoint chord is the diagonal `A s → A t`.

This mirrors the single-drop constructors `frontCut` (`SphericalMatchedCut.lean`),
`cutArm` (`SphericalDiagCut.lean`), `tailArm` (`SphericalOpeningProcess.lean`); the only non-restriction
fact is the new closing diagonal edge, handled exactly as `cutArm_strictConvexPolygon`'s closing edge
via `cut_diagonal_supports` / `sOrient_cyclic`.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalHingeCut ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZChain

namespace ProofsInTheBook.Ch13SubArc

/-! ## The contiguous sub-arc family.

`subArc A s t hst htn : Fin ((t - s) + 1) → S2`, `i ↦ A ⟨s + i.val, _⟩`.  The arm parameter is
`m := t - s`; the `m + 1` vertices are `A s, A (s+1), …, A t`.  Unlike the single-drop constructors,
the parent index map `gidx i := ⟨s + i.val, _⟩` is a pure affine shift (no skip, no `if`). -/

/-- The contiguous sub-arc: keep `A s, A (s+1), …, A t`, re-indexed by `i ↦ A (s + i)`. -/
def subArc {n : ℕ} (A : Fin (n + 1) → S2) (s t : ℕ) (hst : s < t) (htn : t ≤ n) :
    Fin ((t - s) + 1) → S2 :=
  fun i => A ⟨s + i.val, by have := i.isLt; omega⟩

@[simp] theorem subArc_apply {n : ℕ} (A : Fin (n + 1) → S2) (s t : ℕ) (hst : s < t) (htn : t ≤ n)
    (i : Fin ((t - s) + 1)) :
    subArc A s t hst htn i = A ⟨s + i.val, by have := i.isLt; omega⟩ := rfl

@[simp] theorem subArc_zero {n : ℕ} (A : Fin (n + 1) → S2) (s t : ℕ) (hst : s < t) (htn : t ≤ n) :
    subArc A s t hst htn 0 = A ⟨s, by omega⟩ := by
  simp only [subArc, Fin.val_zero, Nat.add_zero]

/-- The last vertex of the sub-arc is `A t` (`= A ⟨s + (t - s)⟩`). -/
@[simp] theorem subArc_last {n : ℕ} (A : Fin (n + 1) → S2) (s t : ℕ) (hst : s < t) (htn : t ≤ n) :
    subArc A s t hst htn (Fin.last (t - s)) = A ⟨t, by omega⟩ := by
  simp only [subArc, Fin.val_last]
  congr 1
  apply Fin.ext
  show s + (t - s) = t
  omega

/-! ### Cyclic-successor bookkeeping for `subArc`.

For a non-last index `i ≠ Fin.last m` the cyclic successor of the sub-arc is the parent vertex one
step along, `A ⟨s + i.val + 1⟩` (no wraparound, since `s + i.val + 1 ≤ t ≤ n`); at the last index it
wraps to `A s` (the other endpoint of the closing diagonal). -/

/-- The value of `1 : Fin ((t-s)+1)` is `1` (since `1 ≤ t - s`, so `(t-s)+1 ≥ 2 > 1`). -/
theorem one_val_subArc {t s : ℕ} (hm : 1 ≤ t - s) : ((1 : Fin ((t - s) + 1)) : ℕ) = 1 := by
  rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)

/-- `i ≠ Fin.last (t - s)` forces `i.val < t - s`. -/
theorem subArc_lt_of_ne_last {m : ℕ} {i : Fin (m + 1)} (hi : i ≠ Fin.last m) :
    i.val < m := by
  rcases Nat.lt_or_ge i.val m with h | h
  · exact h
  · exact absurd (Fin.ext (by simp only [Fin.val_last]; omega)) hi

/-- At a NON-last index `i ≠ Fin.last m` the cyclic successor of the sub-arc is `A ⟨s + i.val + 1⟩`
(no wraparound). -/
theorem subArc_succ_of_ne_last {n : ℕ} (A : Fin (n + 1) → S2) {s t : ℕ}
    (hst : s < t) (htn : t ≤ n) {i : Fin ((t - s) + 1)} (hi : i ≠ Fin.last (t - s)) :
    subArc A s t hst htn (i + 1) = A ⟨s + i.val + 1, by
      have := subArc_lt_of_ne_last hi; omega⟩ := by
  have hiv : i.val < t - s := subArc_lt_of_ne_last hi
  show A ⟨s + (i + 1).val, _⟩ = A ⟨s + i.val + 1, _⟩
  congr 1
  apply Fin.ext
  show s + (i + 1).val = s + i.val + 1
  have hsucc : (i + 1 : Fin ((t - s) + 1)).val = i.val + 1 := by
    rw [Fin.val_add, one_val_subArc (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hsucc]; omega

/-- At the last index the cyclic successor wraps to `A s`: `subArc A (Fin.last m + 1) = A s`. -/
theorem subArc_succ_last {n : ℕ} (A : Fin (n + 1) → S2) {s t : ℕ}
    (hst : s < t) (htn : t ≤ n) :
    subArc A s t hst htn (Fin.last (t - s) + 1) = A ⟨s, by omega⟩ := by
  have hzero : (Fin.last (t - s) + 1 : Fin ((t - s) + 1)) = 0 := by
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_last, Fin.val_zero, one_val_subArc (show 1 ≤ t - s by omega)]
    rw [Nat.mod_self]
  rw [hzero, subArc_zero]

/-! ## The new closing diagonal edge `A t → A s`.

The sub-arc polygon's only *new* edge is `subArc A (Fin.last m) → subArc A (Fin.last m + 1) =
A t → A s`, the closing diagonal of the range.  Its `ShortArc` and support certificates come from the
unconditional `cut_diagonal_supports` (the `i < j < k` cyclic-triple positivity of `A`'s closure
polygon), exactly as the last-vertex-drop `cutArm`'s closing edge in `SphericalDiagCut.lean`. -/

/-- The diagonal `A s → A t` strictly supports the predecessor `A s`'s next interior vertex via an
interior witness.  Direct instance of `cut_diagonal_supports`: for `s < k < t` (in `Fin (n+1)`),
`0 < sOrient (A s) (A k) (A t)`. -/
theorem subArc_diag_support {n : ℕ} {A : Fin (n + 1) → S2}
    (hP : StrictConvexSphPolygon A) {s t : ℕ} (hst : s < t) (htn : t ≤ n)
    {k : ℕ} (hsk : s < k) (hkt : k < t) :
    0 < sOrient (A ⟨s, by omega⟩) (A ⟨k, by omega⟩) (A ⟨t, by omega⟩) := by
  have hab : (⟨s, by omega⟩ : Fin (n + 1)) < ⟨k, by omega⟩ := by
    rw [Fin.lt_def]; exact hsk
  have hbk : (⟨k, by omega⟩ : Fin (n + 1)) < ⟨t, by omega⟩ := by
    rw [Fin.lt_def]; exact hkt
  exact cut_diagonal_supports hP hab hbk

/-- The closing diagonal edge `A t → A s` is a short arc, when the range has an interior vertex
(`2 ≤ t - s`): pick the interior witness `A (s+1)` strictly supported by the diagonal `A s → A t`,
which forces `A s ≠ A t` and `A s` non-antipodal to `A t`. -/
theorem subArc_shortArc_closing {n : ℕ} {A : Fin (n + 1) → S2}
    (hP : StrictConvexSphPolygon A) {s t : ℕ} (hst : s < t) (htn : t ≤ n) (hm : 2 ≤ t - s) :
    ShortArc (A ⟨t, by omega⟩) (A ⟨s, by omega⟩) := by
  -- interior witness `k = s + 1` (exists since `2 ≤ t - s` makes `s + 1 < t`).
  have hsk : s < s + 1 := by omega
  have hkt : s + 1 < t := by omega
  have hpos := subArc_diag_support hP hst htn hsk hkt
  -- `0 < sOrient (A s)(A (s+1))(A t)` ⟹ `A s ≠ A t`, non-antipodal; symmetrise to the edge order.
  have hne : A ⟨s, by omega⟩ ≠ A ⟨t, by omega⟩ := ne_of_sOrient_pos_ac hpos
  have hnanti : (A ⟨s, by omega⟩ : E3) ≠ -(A ⟨t, by omega⟩ : E3) :=
    not_antipodal_of_sOrient_pos_ac hpos
  refine ⟨?_, ?_⟩
  · exact fun he => hne he.symm
  · intro he
    apply hnanti
    rw [he, neg_neg]

/-! ## Index bookkeeping for the sub-arc parent index map.

`subArc A s t hst htn i = A (gidx i)` where `gidx i := ⟨s + i.val⟩`.  This affine shift is injective
into `Fin (n+1)`; we record exactly the facts the four edge/support fields need. -/

/-- The parent-index of a sub-arc vertex: `gidx i = ⟨s + i.val⟩`. -/
def gidx {n : ℕ} (s t : ℕ) (hst : s < t) (htn : t ≤ n) (i : Fin ((t - s) + 1)) : Fin (n + 1) :=
  ⟨s + i.val, by have := i.isLt; omega⟩

theorem subArc_eq_gidx {n : ℕ} (A : Fin (n + 1) → S2) (s t : ℕ) (hst : s < t) (htn : t ≤ n)
    (i : Fin ((t - s) + 1)) :
    subArc A s t hst htn i = A (gidx s t hst htn i) := rfl

theorem gidx_val {n : ℕ} (s t : ℕ) (hst : s < t) (htn : t ≤ n) (i : Fin ((t - s) + 1)) :
    (gidx s t hst htn i).val = s + i.val := rfl

/-- `gidx` is injective. -/
theorem gidx_injective {n : ℕ} (s t : ℕ) (hst : s < t) (htn : t ≤ n) :
    Function.Injective (gidx (n := n) s t hst htn) := by
  intro a b hab
  have hv : (gidx s t hst htn a).val = (gidx s t hst htn b).val := by rw [hab]
  rw [gidx_val, gidx_val] at hv
  exact Fin.ext (by omega)

/-! ## The sub-arc polygon is strictly convex.

We transport the four nontrivial `StrictConvexSphPolygon` fields of `A` (modulus `n+1`) to
`subArc A` (modulus `t - s + 1`).  Non-closing edges (`i ≠ last`) inherit directly from `A`'s edges
via `subArc_succ_of_ne_last` and `gidx` injectivity; the single closing edge `A t → A s` is the cut
diagonal, handled by `subArc_shortArc_closing` (short arc) and `cut_diagonal_supports` (supports, via
the cyclic re-indexing `sOrient_cyclic`). -/

/-- **The sub-arc polygon is strictly convex.**  The contiguous range `A s, …, A t` of a strictly
convex spherical arm `A`, with `2 ≤ t - s`, is a strictly convex polygon. -/
theorem subArc_strictConvexPolygon {n : ℕ} (A : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (s t : ℕ) (hst : s < t) (htn : t ≤ n) (hm : 2 ≤ t - s) :
    StrictConvexSphPolygon (subArc A s t hst htn) := by
  have hP := hA.closed_convex
  have hinj : Function.Injective (gidx (n := n) s t hst htn) := gidx_injective s t hst htn
  refine
    { three_le := by omega
      edge_short := ?_
      edge_support := ?_
      strict_nonincident := ?_
      open_hemisphere := ?_ }
  · -- edge_short
    intro i
    by_cases hi : i = Fin.last (t - s)
    · -- closing edge: A t → A s
      subst hi
      rw [subArc_last, subArc_succ_last]
      exact subArc_shortArc_closing hP hst htn hm
    · -- interior edge: A ⟨s+i⟩ → A ⟨s+i+1⟩, a parent edge
      rw [subArc_apply, subArc_succ_of_ne_last A hst htn hi]
      have hiv : i.val < t - s := subArc_lt_of_ne_last hi
      have := hP.edge_short ⟨s + i.val, by omega⟩
      rwa [show (⟨s + i.val, by omega⟩ + 1 : Fin (n + 1)) = ⟨s + i.val + 1, by omega⟩ by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one']
        rw [Nat.mod_eq_of_lt (show 1 < n + 1 by omega),
          Nat.mod_eq_of_lt (show s + i.val + 1 < n + 1 by omega)]] at this
  · -- edge_support
    intro i j
    rw [subArc_eq_gidx A s t hst htn j]
    by_cases hi : i = Fin.last (t - s)
    · -- closing edge: A t → A s
      subst hi
      rw [subArc_last, subArc_succ_last]
      -- closing-edge support: `0 ≤ sOrient (A t)(A s)(A (gidx j))`.
      have hjv : (gidx s t hst htn j).val = s + j.val := gidx_val s t hst htn j
      have hjlt : j.val ≤ t - s := by have := j.isLt; omega
      rcases Nat.lt_trichotomy (gidx s t hst htn j).val s with hlt | heq | hgt
      · -- impossible: gidx j ≥ s
        omega
      · -- gidx j = s: repeated column (third = second)
        have hjs : gidx s t hst htn j = ⟨s, by omega⟩ := Fin.ext (by rw [heq])
        rw [hjs]; simp only [sOrient]; rw [det3_self_mid]
      · -- gidx j > s: either gidx j = t (repeated first/third) or s < gidx j < t (strict, via cyclic)
        by_cases hjt : (gidx s t hst htn j).val = t
        · have hjeqt : gidx s t hst htn j = ⟨t, by omega⟩ := Fin.ext (by rw [hjt])
          rw [hjeqt]; simp only [sOrient]; rw [det3_self_right]
        · -- interior j: strict via cyclic re-indexing of the diagonal support
          have hsk : s < (gidx s t hst htn j).val := hgt
          have hkt : (gidx s t hst htn j).val < t := by
            rw [hjv] at hjt ⊢; have := j.isLt; omega
          have hpos := subArc_diag_support hP hst htn hsk hkt
          -- `sOrient (A t)(A s)(A k) = sOrient (A s)(A k)(A t)`
          have hcyc : sOrient (A ⟨t, by omega⟩) (A ⟨s, by omega⟩) (A (gidx s t hst htn j))
              = sOrient (A ⟨s, by omega⟩) (A (gidx s t hst htn j)) (A ⟨t, by omega⟩) :=
            (sOrient_cyclic _ _ _).1
          rw [hcyc]
          rw [show (A (gidx s t hst htn j)) = A ⟨(gidx s t hst htn j).val, by have := j.isLt; omega⟩ from rfl]
          exact le_of_lt hpos
    · -- interior edge: A's edge at index ⟨s+i⟩
      rw [subArc_apply, subArc_succ_of_ne_last A hst htn hi]
      have hiv : i.val < t - s := subArc_lt_of_ne_last hi
      have hsucc : (⟨s + i.val, by omega⟩ + 1 : Fin (n + 1)) = ⟨s + i.val + 1, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one']
        rw [Nat.mod_eq_of_lt (show 1 < n + 1 by omega),
          Nat.mod_eq_of_lt (show s + i.val + 1 < n + 1 by omega)]
      have := hP.edge_support ⟨s + i.val, by omega⟩ (gidx s t hst htn j)
      rwa [hsucc] at this
  · -- strict_nonincident
    intro i j hji hji1
    rw [subArc_eq_gidx A s t hst htn j]
    by_cases hi : i = Fin.last (t - s)
    · -- closing edge: A t → A s; non-incident means gidx j ∉ {t, s}, so s < gidx j < t.
      subst hi
      rw [subArc_last, subArc_succ_last]
      have hjv : (gidx s t hst htn j).val = s + j.val := gidx_val s t hst htn j
      -- j ≠ last ⟹ gidx j ≠ t; the wraparound successor of last is 0 ⟹ j ≠ 0 ⟹ gidx j ≠ s.
      have hjne_last : j ≠ Fin.last (t - s) := hji
      have hjval_lt : j.val < t - s := subArc_lt_of_ne_last hjne_last
      have hjne_zero : j ≠ 0 := by
        intro h; apply hji1; rw [h]
        symm
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_last, Fin.val_zero,
          one_val_subArc (show 1 ≤ t - s by omega)]
        rw [Nat.mod_self]
      have hjpos : 0 < j.val := Nat.pos_of_ne_zero (fun hc => hjne_zero (Fin.ext (by simp [hc])))
      have hsk : s < (gidx s t hst htn j).val := by rw [hjv]; omega
      have hkt : (gidx s t hst htn j).val < t := by rw [hjv]; omega
      have hpos := subArc_diag_support hP hst htn hsk hkt
      have hcyc : sOrient (A ⟨t, by omega⟩) (A ⟨s, by omega⟩) (A (gidx s t hst htn j))
          = sOrient (A ⟨s, by omega⟩) (A (gidx s t hst htn j)) (A ⟨t, by omega⟩) :=
        (sOrient_cyclic _ _ _).1
      rw [hcyc]
      rw [show (A (gidx s t hst htn j)) = A ⟨(gidx s t hst htn j).val, by have := j.isLt; omega⟩ from rfl]
      exact hpos
    · -- interior edge: A's edge at index ⟨s+i⟩; transport non-incidence via gidx injectivity.
      rw [subArc_apply, subArc_succ_of_ne_last A hst htn hi]
      have hiv : i.val < t - s := subArc_lt_of_ne_last hi
      have hsucc : (⟨s + i.val, by omega⟩ + 1 : Fin (n + 1)) = ⟨s + i.val + 1, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one']
        rw [Nat.mod_eq_of_lt (show 1 < n + 1 by omega),
          Nat.mod_eq_of_lt (show s + i.val + 1 < n + 1 by omega)]
      -- non-incidence: gidx j ≠ gidx i = ⟨s+i⟩ and gidx j ≠ ⟨s+i+1⟩
      have hne1 : gidx s t hst htn j ≠ (⟨s + i.val, by omega⟩ : Fin (n + 1)) := by
        intro h
        apply hji
        have hgi : gidx s t hst htn i = (⟨s + i.val, by omega⟩ : Fin (n + 1)) := rfl
        have : gidx s t hst htn j = gidx s t hst htn i := by rw [h, hgi]
        exact hinj this
      have hne2 : gidx s t hst htn j ≠ (⟨s + i.val + 1, by omega⟩ : Fin (n + 1)) := by
        intro h
        apply hji1
        have hi1ne : (i + 1 : Fin ((t - s) + 1)) ≠ 0 := by
          intro hc
          have : ((i + 1 : Fin ((t - s) + 1)) : ℕ) = 0 := by rw [hc]; rfl
          rw [Fin.val_add, one_val_subArc (show 1 ≤ t - s by omega),
            Nat.mod_eq_of_lt (show i.val + 1 < t - s + 1 by omega)] at this
          omega
        have hgi1 : gidx s t hst htn (i + 1) = (⟨s + i.val + 1, by omega⟩ : Fin (n + 1)) := by
          apply Fin.ext
          rw [gidx_val]
          simp only [Fin.val_add, one_val_subArc (show 1 ≤ t - s by omega),
            Nat.mod_eq_of_lt (show i.val + 1 < t - s + 1 by omega)]
          omega
        have : gidx s t hst htn j = gidx s t hst htn (i + 1) := by rw [h, hgi1]
        exact hinj this
      have hsupp := hP.strict_nonincident ⟨s + i.val, by omega⟩ (gidx s t hst htn j) hne1
        (by rwa [hsucc])
      rwa [hsucc] at hsupp
  · -- open_hemisphere: subArc A = A ∘ gidx, so reindex
    obtain ⟨hh, hhn, hhpos⟩ := open_hemisphere_reindex hP (gidx (n := n) s t hst htn)
    refine ⟨hh, hhn, ?_⟩
    intro j
    rw [show ((subArc A s t hst htn j : S2) : E3) = ((A (gidx s t hst htn j) : S2) : E3) by
      rw [subArc_eq_gidx]]
    exact hhpos j

/-- **The sub-arc is a strictly convex arm.**  The contiguous range `A s, …, A t` of a strictly
convex spherical arm `A`, with `2 ≤ t - s`, is again a `StrictConvexSphArm` (parameter `m = t - s`,
closing diagonal `A s → A t`). -/
theorem subArc_strictConvexArm {n : ℕ} (A : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (s t : ℕ) (hst : s < t) (htn : t ≤ n) (hm : 2 ≤ t - s) :
    StrictConvexSphArm (subArc A s t hst htn) :=
  { two_le := hm
    closed_convex := subArc_strictConvexPolygon A hA s t hst htn hm }

/-! ## Side lengths, joint angles, endpoint.

The interior sides and joints of the sub-arc are exactly the parent's (the edges `A(s+i) → A(s+i+1)`
are parent edges; the joint at `A(s+i+1)` is the parent's joint there).  The new closing diagonal
contributes no interior joint; its chord is the arm endpoint chord. -/

/-- **Interior arm sides = parent sides.**  The `i`-th side of `subArc A s t` is the parent side
`sideLen A ⟨s + i.val⟩` (the edge `A(s+i) → A(s+i+1)`). -/
theorem subArc_sideLen {n : ℕ} (A : Fin (n + 1) → S2) (s t : ℕ) (hst : s < t) (htn : t ≤ n)
    (i : Fin (t - s)) :
    sideLen (subArc A s t hst htn) i = sideLen A ⟨s + i.val, by have := i.isLt; omega⟩ := by
  unfold sideLen
  have hc : (subArc A s t hst htn) i.castSucc = A ⟨s + i.val, by have := i.isLt; omega⟩ := rfl
  have hs : (subArc A s t hst htn) i.succ = A ⟨s + i.val + 1, by have := i.isLt; omega⟩ := rfl
  have hrc : (⟨s + i.val, by have := i.isLt; omega⟩ : Fin n).castSucc
      = (⟨s + i.val, by have := i.isLt; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext; simp
  have hrs : (⟨s + i.val, by have := i.isLt; omega⟩ : Fin n).succ
      = (⟨s + i.val + 1, by have := i.isLt; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext; simp
  rw [hc, hs, hrc, hrs]

/-- **Interior arm joints = parent joints.**  The `i`-th joint of `subArc A s t` is the parent joint
`jointAngle A ⟨s + i.val⟩` (the spherical angle at `A(s+i+1)`).  The new closing diagonal contributes
no interior joint. -/
theorem subArc_jointAngle {n : ℕ} (A : Fin (n + 1) → S2) (s t : ℕ) (hst : s < t) (htn : t ≤ n)
    (i : Fin (t - s - 1)) :
    jointAngle (subArc A s t hst htn) i = jointAngle A ⟨s + i.val, by have := i.isLt; omega⟩ := by
  unfold jointAngle
  have hb : i.val < t - s - 1 := i.isLt
  have e0 : (subArc A s t hst htn) ⟨i.val, by omega⟩ = A ⟨s + i.val, by omega⟩ := rfl
  have e1 : (subArc A s t hst htn) ⟨i.val + 1, by omega⟩ = A ⟨s + i.val + 1, by omega⟩ := rfl
  have e2 : (subArc A s t hst htn) ⟨i.val + 2, by omega⟩ = A ⟨s + i.val + 2, by omega⟩ := rfl
  rw [e0, e1, e2]

/-- **The arm endpoint chord is the diagonal `A s → A t`.**  `sDist (subArc A 0) (subArc A (last m)) =
sDist (A s) (A t)`. -/
theorem subArc_endpt {n : ℕ} (A : Fin (n + 1) → S2) (s t : ℕ) (hst : s < t) (htn : t ≤ n) :
    sDist (subArc A s t hst htn 0) (subArc A s t hst htn (Fin.last (t - s)))
      = sDist (A ⟨s, by omega⟩) (A ⟨t, by omega⟩) := by
  rw [subArc_zero, subArc_last]

end ProofsInTheBook.Ch13SubArc
