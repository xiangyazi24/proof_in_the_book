import ProofsInTheBook.PlanarMapNearTriangulation
import ProofsInTheBook.PlanarMapDelete

/-!
# Filtered cyclic rotations and fresh-dart adjunctions (generic surgery toolkit)

This file is the generic permutation-surgery toolkit used by the upcoming
chord-split and boundary-deletion files (files 5-8 of the Chapter 35 plan).
It contains no chord-specific or fan-specific content; everything is stated for
an abstract permutation `σ` on a fintype together with a *deleted* finite set
`Del` (equivalently, a *kept* subtype `{d // d ∉ Del}`).

## Conventions

We reuse `Equiv.Perm.deleteSet` from `PlanarMapDelete`.  Following the
deletion-layer convention, a surgery is parametrized by the **deleted** finite
set `Del : Finset D`; the **kept** darts are the subtype `{d // d ∉ Del}`.  The
*filtered rotation* `filteredRotation σ Del` is the permutation of the kept
subtype that, starting from a kept dart, advances along `σ` to the first
surviving (kept) dart.  This is exactly `σ.deleteSet Del`, so it composes
directly with `CombMap.deleteVertex` (whose new `σ` is `σ.deleteSet
(deleteVertexSet v)`).

## Main results

* `filteredRotation` — the filtered cyclic rotation on the kept subtype.
* `filteredRotation_apply_of_next_kept` — **the consecutive-successor fact**:
  if `σ x` is kept, the filtered successor of `x` is exactly `σ x`.
* `filteredRotation_sameCycle_iff` — the orbit of the filtered rotation through a
  kept dart is the trace of the `σ`-orbit on the kept subtype.
* `filteredRotation_iterate_eq_of_contiguous` — **the contiguity lemma**: if the
  kept darts of one `σ`-cycle form one contiguous cyclic interval `l`, then the
  `k`-th filtered iterate of the first interval element is the `k`-th interval
  element (cyclically), so the filtered rotation is the interval-shift.
* `freshAlpha`, `freshSigma`, `freshMap` — the fresh-dart adjunction adding a
  `Fin 2` of fresh darts spliced into one vertex rotation, with the fixed-point
  free involution and orbit lemmas.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace FilteredRotation

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Part 1: the filtered cyclic rotation -/

/-- The **filtered cyclic rotation** of a permutation `σ` relative to a deleted
set `Del`: the permutation of the kept subtype `{d // d ∉ Del}` that advances
along `σ` to the first surviving dart.  Thin wrapper around
`Equiv.Perm.deleteSet`, fixed here so the surgery files share one name. -/
noncomputable def filteredRotation (σ : Equiv.Perm D) (Del : Finset D) :
    Equiv.Perm {d : D // d ∉ Del} :=
  σ.deleteSet Del

@[simp]
lemma filteredRotation_apply_coe (σ : Equiv.Perm D) (Del : Finset D)
    (x : {d : D // d ∉ Del}) :
    ((filteredRotation σ Del x : {d : D // d ∉ Del}) : D) =
      (σ ^ Equiv.Perm.DeleteSet.firstOutside σ Del x) x.1 :=
  rfl

/-- The number of `σ`-steps the filtered rotation takes from `x` is `1`
precisely when the immediate `σ`-successor of `x` is also kept. -/
lemma firstOutside_eq_one_of_next_notMem (σ : Equiv.Perm D) (Del : Finset D)
    (x : {d : D // d ∉ Del}) (h : σ x.1 ∉ Del) :
    Equiv.Perm.DeleteSet.firstOutside σ Del x = 1 := by
  have hpos : 0 < Equiv.Perm.DeleteSet.firstOutside σ Del x :=
    Equiv.Perm.DeleteSet.firstOutside_pos σ Del x
  -- `1` satisfies the search predicate, so the minimum is `≤ 1`.
  have hle : Equiv.Perm.DeleteSet.firstOutside σ Del x ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : (1 : ℕ) < Equiv.Perm.DeleteSet.firstOutside σ Del x := hcon
    have hbad := Equiv.Perm.DeleteSet.firstOutside_min σ Del x h1
    apply hbad
    refine ⟨one_pos, ?_⟩
    simpa using h
  omega

/-- **Consecutive-successor fact.**  If the `σ`-successor of a kept dart `x` is
again kept, then the filtered successor of `x` is exactly `σ x`.  This is the
local statement that, on a contiguous run of kept darts, the filtered rotation
agrees with `σ`. -/
lemma filteredRotation_apply_of_next_kept (σ : Equiv.Perm D) (Del : Finset D)
    (x : {d : D // d ∉ Del}) (h : σ x.1 ∉ Del) :
    (filteredRotation σ Del x : {d : D // d ∉ Del}).1 = σ x.1 := by
  rw [filteredRotation_apply_coe, firstOutside_eq_one_of_next_notMem σ Del x h,
    pow_one]

/-- Packaged subtype version of `filteredRotation_apply_of_next_kept`. -/
lemma filteredRotation_apply_eq (σ : Equiv.Perm D) (Del : Finset D)
    (x : {d : D // d ∉ Del}) (y : {d : D // d ∉ Del}) (h : σ x.1 ∉ Del)
    (hy : (y : D) = σ x.1) :
    filteredRotation σ Del x = y := by
  apply Subtype.ext
  rw [filteredRotation_apply_of_next_kept σ Del x h, hy]

/-! ## Part 2: orbit / cycle behavior -/

/-- **Orbit trace.**  The filtered rotation's orbit through a kept dart is the
trace of `σ`'s orbit on the kept subtype: two kept darts are in the same
filtered cycle iff they are in the same `σ`-cycle. -/
lemma filteredRotation_sameCycle_iff (σ : Equiv.Perm D) (Del : Finset D)
    (x y : {d : D // d ∉ Del}) :
    (filteredRotation σ Del).SameCycle x y ↔ σ.SameCycle x.1 y.1 :=
  Equiv.Perm.sameCycle_deleteSet_iff σ Del x y

/-- Every kept dart reachable from `x` by a power of `σ` is in the same filtered
cycle as `x`. -/
lemma filteredRotation_sameCycle_of_pow (σ : Equiv.Perm D) (Del : Finset D)
    (x y : {d : D // d ∉ Del}) {m : ℕ} (h : (σ ^ m) x.1 = y.1) :
    (filteredRotation σ Del).SameCycle x y :=
  Equiv.Perm.sameCycle_deleteSet_of_pow σ Del m x y h

/-! ## Part 3: the contiguity lemma

We model a contiguous cyclic interval of kept darts as a list `l : List D` such
that:

* every element of `l` is kept (not in `Del`);
* consecutive elements are `σ`-successors: `σ (l.get i) = l.get (i+1)` for
  `i < l.length - 1`;
* the immediate `σ`-successors witness contiguity: for each non-last index the
  successor stays in the list.

The conclusion is that the filtered rotation walks `l` in order.  We phrase the
hypothesis through an indexing function to avoid `List.get` index juggling and
to make it directly usable from a boundary cycle's dart enumeration. -/

/-- Contiguity data for one `σ`-cycle relative to a deleted set, indexed by
`Fin n`.  `seq i` is the `i`-th kept dart of the contiguous interval; the
darts are pairwise the `σ`-successors of each other along the interval, and all
of them are kept. -/
structure ContiguousInterval (σ : Equiv.Perm D) (Del : Finset D) (n : ℕ) where
  /-- The darts of the interval, in cyclic order. -/
  seq : Fin n → D
  /-- Every interval dart is kept. -/
  kept : ∀ i, seq i ∉ Del
  /-- The interval is a contiguous `σ`-run: the `σ`-successor of `seq i` is the
  next interval dart, cyclically.  At the last index this wraps to `seq 0`. -/
  step : ∀ i : Fin n, σ (seq i) = seq (⟨(i.1 + 1) % n, Nat.mod_lt _ i.pos⟩ : Fin n)

namespace ContiguousInterval

variable {σ : Equiv.Perm D} {Del : Finset D} {n : ℕ}

/-- The interval, viewed as kept darts (elements of the kept subtype). -/
def keptElt (I : ContiguousInterval σ Del n) (i : Fin n) : {d : D // d ∉ Del} :=
  ⟨I.seq i, I.kept i⟩

/-- The cyclic successor index on `Fin n`. -/
def nextIdx (I : ContiguousInterval σ Del n) (i : Fin n) : Fin n :=
  ⟨(i.1 + 1) % n, Nat.mod_lt _ i.pos⟩

@[simp]
lemma nextIdx_val (I : ContiguousInterval σ Del n) (i : Fin n) :
    (I.nextIdx i).1 = (i.1 + 1) % n :=
  rfl

/-- **One filtered step follows the interval.**  The filtered successor of the
`i`-th interval dart is the `(i+1)`-th interval dart (cyclically). -/
lemma filteredRotation_keptElt (I : ContiguousInterval σ Del n) (i : Fin n) :
    filteredRotation σ Del (I.keptElt i) = I.keptElt (I.nextIdx i) := by
  apply Subtype.ext
  have hnext : σ (I.seq i) ∉ Del := by
    rw [I.step i]; exact I.kept _
  rw [filteredRotation_apply_of_next_kept σ Del (I.keptElt i) (by simpa [keptElt] using hnext)]
  show σ (I.seq i) = I.seq (I.nextIdx i)
  rw [I.step i]; rfl

/-- The cyclic-shift index after `k` filtered steps. -/
lemma nextIdx_iterate (I : ContiguousInterval σ Del n) (i : Fin n) (k : ℕ) :
    (I.nextIdx^[k] i).1 = (i.1 + k) % n := by
  induction k generalizing i with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih (I.nextIdx i)]
      simp only [nextIdx_val]
      conv_lhs => rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl n)]
      rw [← Nat.add_mod]
      congr 1
      omega

/-- **The contiguity / interval-shift lemma.**  If the kept darts of one
`σ`-cycle form one contiguous cyclic interval `I` (length `n`), then the `k`-th
filtered iterate of the `i`-th interval dart is the `(i+k)`-th interval dart,
cyclically.  In particular `filteredRotation^[k]` of the first interval element
(`i = 0`) hits exactly the interval elements in order, so the filtered rotation
on this cycle is precisely the interval-shift. -/
lemma filteredRotation_iterate_keptElt
    (I : ContiguousInterval σ Del n) (i : Fin n) (k : ℕ) :
    (filteredRotation σ Del)^[k] (I.keptElt i) = I.keptElt (I.nextIdx^[k] i) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        I.filteredRotation_keptElt i, ih]

/-- **First-element enumeration form.**  The `k`-th filtered iterate of the first
interval element `seq 0` is the `(k mod n)`-th interval element. -/
lemma filteredRotation_iterate_first
    (I : ContiguousInterval σ Del n) (hn : 0 < n) (k : ℕ) :
    (filteredRotation σ Del)^[k] (I.keptElt ⟨0, hn⟩)
      = I.keptElt ⟨k % n, Nat.mod_lt _ hn⟩ := by
  rw [filteredRotation_iterate_keptElt]
  congr 1
  apply Fin.ext
  rw [nextIdx_iterate]
  simp

/-- The interval darts are exactly the orbit of `seq 0` under the filtered
rotation: every interval element is a filtered iterate of the first. -/
lemma keptElt_mem_filteredRotation_orbit
    (I : ContiguousInterval σ Del n) (hn : 0 < n) (i : Fin n) :
    (filteredRotation σ Del)^[i.1] (I.keptElt ⟨0, hn⟩) = I.keptElt i := by
  rw [filteredRotation_iterate_first I hn i.1]
  congr 1
  apply Fin.ext
  simp [Nat.mod_eq_of_lt i.isLt]

end ContiguousInterval

/-! ## Part 4: the fresh-dart adjunction

Given a kept dart type `K` carrying an edge involution `β` (the filtered `α`)
and a rotation `ρ` (the filtered `σ`), we build a new dart type `K ⊕ Fin 2`
adding two fresh darts `c₀ = inr 0`, `c₁ = inr 1`.  The new edge involution
swaps the two fresh darts and acts as `β` on `K`; the new rotation splices `c₀`
immediately after a chosen anchor `a₀` and `c₁` immediately after a chosen
anchor `a₁` in their vertex rotations.

This is the generic stitching primitive for the side maps: a chord split adds a
fresh duplicated chord edge (the two fresh darts) into each side, splicing one
fresh dart into each endpoint's rotation.  The content here is purely the
permutation bookkeeping (involution, fixed-point freeness, the spliced rotation
is a permutation, and the local orbit steps).
-/

section FreshDart

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The two fresh darts, as `Fin 2` summands of `K ⊕ Fin 2`. -/
abbrev freshDart (k : Fin 2) : K ⊕ Fin 2 := Sum.inr k

/-- **Fresh edge involution.**  Swaps the two fresh darts and acts as `β` on the
kept summand.  Built as a sum of equivalences, hence automatically a
permutation. -/
def freshAlpha (β : Equiv.Perm K) : Equiv.Perm (K ⊕ Fin 2) :=
  Equiv.sumCongr β (Equiv.swap (0 : Fin 2) 1)

@[simp]
lemma freshAlpha_inl (β : Equiv.Perm K) (k : K) :
    freshAlpha β (Sum.inl k) = Sum.inl (β k) := rfl

@[simp]
lemma freshAlpha_inr (β : Equiv.Perm K) (j : Fin 2) :
    freshAlpha β (Sum.inr j) = Sum.inr (Equiv.swap (0 : Fin 2) 1 j) := rfl

/-- `freshAlpha β` is an involution when `β` is. -/
lemma freshAlpha_involutive (β : Equiv.Perm K) (hβ : β * β = 1) :
    freshAlpha β * freshAlpha β = 1 := by
  ext x
  cases x with
  | inl k =>
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, freshAlpha_inl,
        Equiv.Perm.coe_one, id_eq]
      have := congrArg (fun f : Equiv.Perm K => f k) hβ
      simpa [Equiv.Perm.coe_mul, Function.comp_apply] using this
  | inr j =>
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, freshAlpha_inr,
        Equiv.Perm.coe_one, id_eq, Equiv.swap_apply_self]

/-- `freshAlpha β` is fixed-point free when `β` is.  (The fresh darts are swapped
to one another, so they too are not fixed.) -/
lemma freshAlpha_no_fixed (β : Equiv.Perm K) (hβ : ∀ k, β k ≠ k) :
    ∀ x, freshAlpha β x ≠ x := by
  intro x
  cases x with
  | inl k =>
      simp only [freshAlpha_inl, ne_eq, Sum.inl.injEq]
      exact hβ k
  | inr j =>
      simp only [freshAlpha_inr, ne_eq, Sum.inr.injEq]
      fin_cases j <;> decide

/-! ### The spliced rotation

`freshSigmaFun` inserts `c₀ = inr 0` right after `a₀` and `c₁ = inr 1` right
after `a₁` in the rotation `ρ`.  We require the two anchors to be distinct so
the two splices do not collide. -/

variable (ρ : Equiv.Perm K) (a₀ a₁ : K)

/-- Forward map of the spliced rotation. -/
def freshSigmaFun (x : K ⊕ Fin 2) : K ⊕ Fin 2 :=
  match x with
  | Sum.inr j =>
      if j = 0 then Sum.inl (ρ a₀) else Sum.inl (ρ a₁)
  | Sum.inl k =>
      if k = a₀ then Sum.inr 0
      else if k = a₁ then Sum.inr 1
      else Sum.inl (ρ k)

/-- Inverse map of the spliced rotation. -/
def freshSigmaInv (x : K ⊕ Fin 2) : K ⊕ Fin 2 :=
  match x with
  | Sum.inr j =>
      if j = 0 then Sum.inl a₀ else Sum.inl a₁
  | Sum.inl k =>
      if k = ρ a₀ then Sum.inr 0
      else if k = ρ a₁ then Sum.inr 1
      else Sum.inl (ρ⁻¹ k)

variable {ρ a₀ a₁}

lemma freshSigma_left_inv (hne : a₀ ≠ a₁) (x : K ⊕ Fin 2) :
    freshSigmaInv ρ a₀ a₁ (freshSigmaFun ρ a₀ a₁ x) = x := by
  have hρne : ρ a₀ ≠ ρ a₁ := fun h => hne (ρ.injective h)
  cases x with
  | inr j =>
      by_cases hj : j = 0
      · subst hj; simp [freshSigmaFun, freshSigmaInv]
      · have hj1 : j = 1 := by omega
        subst hj1; simp [freshSigmaFun, freshSigmaInv, hρne.symm]
  | inl k =>
      by_cases h0 : k = a₀
      · subst h0; simp [freshSigmaFun, freshSigmaInv]
      · by_cases h1 : k = a₁
        · subst h1; simp [freshSigmaFun, freshSigmaInv, h0]
        · have hk0 : ρ k ≠ ρ a₀ := fun h => h0 (ρ.injective h)
          have hk1 : ρ k ≠ ρ a₁ := fun h => h1 (ρ.injective h)
          simp [freshSigmaFun, freshSigmaInv, h0, h1, hk0, hk1]

lemma freshSigma_right_inv (hne : a₀ ≠ a₁) (x : K ⊕ Fin 2) :
    freshSigmaFun ρ a₀ a₁ (freshSigmaInv ρ a₀ a₁ x) = x := by
  have hρne : ρ a₀ ≠ ρ a₁ := fun h => hne (ρ.injective h)
  cases x with
  | inr j =>
      by_cases hj : j = 0
      · subst hj; simp [freshSigmaFun, freshSigmaInv]
      · have hj1 : j = 1 := by omega
        subst hj1; simp [freshSigmaFun, freshSigmaInv, hne.symm]
  | inl k =>
      by_cases h0 : k = ρ a₀
      · subst h0; simp [freshSigmaFun, freshSigmaInv]
      · by_cases h1 : k = ρ a₁
        · subst h1; simp [freshSigmaFun, freshSigmaInv, h0]
        · have hk0 : ρ.symm k ≠ a₀ := by
            intro h; apply h0; rw [← h]; simp
          have hk1 : ρ.symm k ≠ a₁ := by
            intro h; apply h1; rw [← h]; simp
          simp [freshSigmaFun, freshSigmaInv, h0, h1, hk0, hk1]

variable (ρ a₀ a₁)

/-- **Fresh spliced rotation.**  The rotation `ρ` with `c₀` inserted after `a₀`
and `c₁` inserted after `a₁`.  A permutation of `K ⊕ Fin 2`. -/
def freshSigma (hne : a₀ ≠ a₁) : Equiv.Perm (K ⊕ Fin 2) where
  toFun := freshSigmaFun ρ a₀ a₁
  invFun := freshSigmaInv ρ a₀ a₁
  left_inv := freshSigma_left_inv hne
  right_inv := freshSigma_right_inv hne

@[simp]
lemma freshSigma_apply (hne : a₀ ≠ a₁) (x : K ⊕ Fin 2) :
    freshSigma ρ a₀ a₁ hne x = freshSigmaFun ρ a₀ a₁ x := rfl

/-- The anchor `a₀` now points to the fresh dart `c₀`. -/
@[simp]
lemma freshSigma_anchor_zero (hne : a₀ ≠ a₁) :
    freshSigma ρ a₀ a₁ hne (Sum.inl a₀) = Sum.inr 0 := by
  simp [freshSigma, freshSigmaFun]

/-- The anchor `a₁` now points to the fresh dart `c₁`. -/
@[simp]
lemma freshSigma_anchor_one (hne : a₀ ≠ a₁) :
    freshSigma ρ a₀ a₁ hne (Sum.inl a₁) = Sum.inr 1 := by
  simp [freshSigma, freshSigmaFun, hne.symm]

/-- The fresh dart `c₀` points to the old `ρ`-successor of `a₀`: the new cycle
through `c₀` visits `c₀` then the old cycle segment starting at `ρ a₀`. -/
@[simp]
lemma freshSigma_fresh_zero (hne : a₀ ≠ a₁) :
    freshSigma ρ a₀ a₁ hne (Sum.inr 0) = Sum.inl (ρ a₀) := by
  simp [freshSigma, freshSigmaFun]

/-- The fresh dart `c₁` points to the old `ρ`-successor of `a₁`. -/
@[simp]
lemma freshSigma_fresh_one (hne : a₀ ≠ a₁) :
    freshSigma ρ a₀ a₁ hne (Sum.inr 1) = Sum.inl (ρ a₁) := by
  simp [freshSigma, freshSigmaFun]

/-- Away from the two anchors, the spliced rotation is the old rotation. -/
lemma freshSigma_other (hne : a₀ ≠ a₁) {k : K} (h0 : k ≠ a₀) (h1 : k ≠ a₁) :
    freshSigma ρ a₀ a₁ hne (Sum.inl k) = Sum.inl (ρ k) := by
  simp only [freshSigma_apply, freshSigmaFun, if_neg h0, if_neg h1]

variable {ρ a₀ a₁}

/-- **The fresh CombMap adjunction.**  Given a fixed-point-free involution `β`
and a rotation `ρ` on the kept type `K`, with two distinct anchors, the pair
`(freshAlpha β, freshSigma ρ a₀ a₁)` is a `CombMap` on `K ⊕ Fin 2`. -/
def freshMap (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
    (a₀ a₁ : K) (hne : a₀ ≠ a₁) : CombMap (K ⊕ Fin 2) where
  α := freshAlpha β
  σ := freshSigma ρ a₀ a₁ hne
  α_invol := freshAlpha_involutive β hβinv
  α_no_fixed := freshAlpha_no_fixed β hβfix

@[simp]
lemma freshMap_alpha (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
    (a₀ a₁ : K) (hne : a₀ ≠ a₁) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).α = freshAlpha β := rfl

@[simp]
lemma freshMap_sigma (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
    (a₀ a₁ : K) (hne : a₀ ≠ a₁) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).σ = freshSigma ρ a₀ a₁ hne := rfl

end FreshDart

end FilteredRotation

end ProofsInTheBook.PlanarMap
