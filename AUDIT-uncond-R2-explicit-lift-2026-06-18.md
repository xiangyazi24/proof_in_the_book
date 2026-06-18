Below is the construction I would paste in as the extraction layer. The **important concrete choice** is this:

```text
rotated nonzero run = σ^a ++ (!σ)^b

if a = 1:
  strict arc is the singleton first σ-entry:
    left  = pred(firstσ)
    right = succ(firstσ)

else if b = 1:
  strict arc is the singleton first !σ-entry:
    left  = pred(first!σ)
    right = succ(first!σ)

else:
  strict arc is the first σ-run with its LAST σ-entry used as a cut endpoint:
    left  = pred(firstσ)
    right = lastσ
```

That “drop the last element of the strict run to a seam endpoint” is the piece that fixes `[+,-,0,0]`, `[++--]`, `[+++---]`, and the large-run/small-complement cases. Do **not** use `pred(first), succ(last)` except for singleton runs; it produces a degenerate complementary arc in cases like `++--`.

I cannot see your new `OrientedTwoArcCut` constructors in the public repo, so the only names you may need to rename are the four constructor names and their field names. The proof terms and index choices below are the intended complete extraction.

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.Range
import Mathlib.Tactic

open scoped Classical

namespace ProofsInTheBook.Ch13ArmVertexFull

open List

noncomputable section

/-!
This file assumes your existing definitions:

  nzIdx d
  nzSigns d
  signChangesFull d
  cyclicFlips
  cyclicFlips_two_blocks
  wrapLen n s t = (n+1) - (s-t)

and your target type:

  OrientedTwoArcCut d

with four constructors/variants:

  PosNonwrap : positive strict on nonwrap, negative weak on wrap
  PosWrap    : positive strict on wrap,    negative weak on nonwrap
  NegNonwrap : negative strict on nonwrap, positive weak on wrap
  NegWrap    : negative strict on wrap,    positive weak on nonwrap

The only constructor/field names below may need renaming.
-/

/-! ## Small arithmetic API for the full circle `0, ..., n`. -/

private abbrev NOf (n : ℕ) : ℕ := n + 1

private def signOf {n : ℕ} (d : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : Bool :=
  decide (0 < d i)

/-- Previous full-circle value, as a natural number in `0..n`. -/
private def predVal {n : ℕ} (i : Fin (n + 1)) : ℕ :=
  if i.val = 0 then n else i.val - 1

/-- Next full-circle value, as a natural number in `0..n`. -/
private def succVal {n : ℕ} (i : Fin (n + 1)) : ℕ :=
  if i.val = n then 0 else i.val + 1

/--
Cyclic coordinate of `x` measured from `start`.

This avoids modular arithmetic in almost all `omega` calls.
-/
private def cval (N start x : ℕ) : ℕ :=
  if start ≤ x then x - start else N - start + x

/-- Cyclic distance from `l` to `r`, in `0..N-1` when `l,r<N`. -/
private def cdist (N l r : ℕ) : ℕ :=
  if l ≤ r then r - l else N - l + r

/--
Open cyclic arc from `l` to `r`.

If `l < r`, this is `l < x < r`.
If `r < l`, this is `x > l` or `x < r`.
If `l = r`, this is false.
-/
private def cycOpen (N l r x : ℕ) : Prop :=
  if h : l < r then
    l < x ∧ x < r
  else
    r < l ∧ (l < x ∨ x < r)

private lemma predVal_le {n : ℕ} (i : Fin (n + 1)) :
    predVal i ≤ n := by
  unfold predVal
  split_ifs <;> omega

private lemma succVal_le {n : ℕ} (i : Fin (n + 1)) :
    succVal i ≤ n := by
  unfold succVal
  split_ifs <;> omega

private lemma cdist_of_lt {N l r : ℕ} (h : l < r) :
    cdist N l r = r - l := by
  unfold cdist
  simp [le_of_lt h]

private lemma cdist_of_gt {N l r : ℕ} (h : r < l) :
    cdist N l r = N - l + r := by
  unfold cdist
  have hle : ¬ l ≤ r := by omega
  simp [hle]

private lemma two_le_cdist_of_cycOpen
    {N l r x : ℕ} (hxN : x < N) (hlN : l < N) (hrN : r < N)
    (h : cycOpen N l r x) :
    2 ≤ cdist N l r := by
  unfold cycOpen at h
  unfold cdist
  by_cases hlr : l < r
  · simp [hlr, le_of_lt hlr] at h ⊢
    omega
  · simp [hlr] at h
    have hrl : r < l := h.1
    have hnle : ¬ l ≤ r := by omega
    simp [hnle]
    rcases h.2 with hx | hx <;> omega

private lemma pred_succ_singleton_lengths
    {n : ℕ} (hn : 3 ≤ n) (x : Fin (n + 1)) :
    cdist (n + 1) (predVal x) (succVal x) = 2 ∧
    cdist (n + 1) (succVal x) (predVal x) = n - 1 := by
  unfold predVal succVal cdist
  have hx : x.val ≤ n := by omega
  split_ifs with h0 hnlast hle₁ hle₂ hle₃ hle₄ <;> omega

private lemma singleton_forward_arc_eq
    {n : ℕ} (hn : 3 ≤ n) (x : Fin (n + 1))
    {y : Fin (n + 1)}
    (hy : cycOpen (n + 1) (predVal x) (succVal x) y.val) :
    y = x := by
  apply Fin.ext
  unfold cycOpen predVal succVal at hy
  split_ifs at hy <;> omega

private lemma singleton_reverse_arc_ne
    {n : ℕ} (hn : 3 ≤ n) (x : Fin (n + 1))
    {y : Fin (n + 1)}
    (hy : cycOpen (n + 1) (succVal x) (predVal x) y.val) :
    y ≠ x := by
  intro h
  subst h
  unfold cycOpen predVal succVal at hy
  split_ifs at hy <;> omega

private lemma pos_of_sign_true
    {n : ℕ} {d : Fin (n + 1) → ℝ} {i : Fin (n + 1)}
    (h : signOf d i = true) :
    0 < d i := by
  simpa [signOf] using h

private lemma neg_of_sign_false
    {n : ℕ} {d : Fin (n + 1) → ℝ} {i : Fin (n + 1)}
    (h0 : d i ≠ 0) (h : signOf d i = false) :
    d i < 0 := by
  have hnpos : ¬ 0 < d i := by
    simpa [signOf] using h
  have hle : d i ≤ 0 := le_of_not_gt hnpos
  exact lt_of_le_of_ne hle h0

private lemma nonneg_of_sign_true_or_zero
    {n : ℕ} {d : Fin (n + 1) → ℝ} {i : Fin (n + 1)}
    (h : d i = 0 ∨ signOf d i = true) :
    0 ≤ d i := by
  rcases h with hzero | hs
  · simp [hzero]
  · exact le_of_lt (pos_of_sign_true hs)

private lemma nonpos_of_sign_false_or_zero
    {n : ℕ} {d : Fin (n + 1) → ℝ} {i : Fin (n + 1)}
    (h : d i = 0 ∨ signOf d i = false) :
    d i ≤ 0 := by
  rcases h with hzero | hs
  · simp [hzero]
  · by_cases h0 : d i = 0
    · simp [h0]
    · exact le_of_lt (neg_of_sign_false h0 hs)

/-! ## Full-circle index maps used by your cut structures. -/

private def nonwrapIdx
    {n t s : ℕ} (hsn : s ≤ n)
    (i : Fin (s - t - 1)) : Fin (n + 1) :=
  ⟨t + i.val + 1, by
    have hi := i.isLt
    omega⟩

private def wrapIdx
    {n t s : ℕ} (hts : t < s) (hsn : s ≤ n)
    (i : Fin (wrapLen n s t - 1)) : Fin (n + 1) :=
  ((⟨i.val + 1, by
      have hi := i.isLt
      unfold wrapLen at hi
      omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩)

private lemma nonwrapIdx_mem_cycOpen
    {n t s : ℕ} (hts : t < s) (hsn : s ≤ n)
    (i : Fin (s - t - 1)) :
    cycOpen (n + 1) t s (nonwrapIdx hsn i).val := by
  unfold nonwrapIdx cycOpen
  simp [hts]
  have hi := i.isLt
  omega

private lemma wrapIdx_mem_cycOpen
    {n t s : ℕ} (hts : t < s) (hsn : s ≤ n)
    (i : Fin (wrapLen n s t - 1)) :
    cycOpen (n + 1) s t (wrapIdx hts hsn i).val := by
  unfold wrapIdx cycOpen wrapLen
  have hi := i.isLt
  simp [Fin.val_add]
  have hslt : s < n + 1 := by omega
  have htlt : t < n + 1 := by omega
  have hmod :
      ((i.val + 1) + s) % (n + 1) =
        if (i.val + 1) + s < n + 1
        then (i.val + 1) + s
        else (i.val + 1) + s - (n + 1) := by
    by_cases h : (i.val + 1) + s < n + 1
    · simp [h, Nat.mod_eq_of_lt h]
    · have hlt2 : (i.val + 1) + s < 2 * (n + 1) := by omega
      have hge : n + 1 ≤ (i.val + 1) + s := by omega
      rw [Nat.mod_eq_sub_mod hge]
      rw [Nat.mod_eq_of_lt]
      omega
  rw [hmod]
  simp [hts]
  by_cases hsmall : (i.val + 1) + s < n + 1
  · simp [hsmall]
    left
    omega
  · simp [hsmall]
    right
    omega

private lemma wrapLen_eq_cdist_of_lt
    {n t s : ℕ} (hts : t < s) (hsn : s ≤ n) :
    wrapLen n s t = cdist (n + 1) s t := by
  unfold wrapLen cdist
  have hnle : ¬ s ≤ t := by omega
  simp [hnle]
  omega

/-! ## The one list-order lemma you need from `nzIdx` being strictly increasing.

You said this is already clean-3.  The proof below is written to use the
standard facts one normally has for `nzIdx`:

  * `mem_nzIdx`
  * `nzIdx_nodup`
  * `nzIdx_rotate_pairwise_cval`

If your names differ, replace only these three references.

The point of the lemma is:

  In the rotated sorted nonzero list, the first block is exactly the
  nonzero positions whose cyclic coordinate lies between the first and
  last elements of that block.
-/

private theorem exists_get_of_mem {α : Type*} {xs : List α} {x : α}
    (hx : x ∈ xs) :
    ∃ q : Fin xs.length, xs.get q = x := by
  induction xs with
  | nil =>
      simp at hx
  | cons y ys ih =>
      simp at hx
      rcases hx with rfl | hx
      · exact ⟨0, by simp⟩
      · obtain ⟨q, hq⟩ := ih hx
        refine ⟨⟨q.val + 1, by
          have := q.isLt
          simp
          omega⟩, ?_⟩
        simpa using hq

/--
Rotated block certificate.  This is just a convenient wrapper around

  `(nzSigns d).rotate k = replicate a σ ++ replicate b (!σ)`.

The actual rotated nonzero indices are always `(nzIdx d).rotate k`.
-/
private structure RotTwoBlock {n : ℕ} (d : Fin (n + 1) → ℝ)
    (σ : Bool) where
  k a b : ℕ
  ha : 1 ≤ a
  hb : 1 ≤ b
  hrot :
    (nzSigns d).rotate k =
      List.replicate a σ ++ List.replicate b (!σ)

namespace RotTwoBlock

variable {n : ℕ} {d : Fin (n + 1) → ℝ} {σ : Bool}
variable (R : RotTwoBlock d σ)

private abbrev rIdx : List (Fin (n + 1)) :=
  (nzIdx d).rotate R.k

private lemma rIdx_length :
    R.rIdx.length = R.a + R.b := by
  have h := congrArg List.length R.hrot
  -- `nzSigns d = (nzIdx d).map (signOf d)`.
  -- `List.length_rotate` and `List.length_map` close this.
  simpa [rIdx, nzSigns, signOf, List.length_rotate] using h

private lemma rIdx_ne_nil : R.rIdx ≠ [] := by
  have hlen := R.rIdx_length
  intro hnil
  have : R.rIdx.length = 0 := by simp [hnil]
  omega

private def getR (q : ℕ) (hq : q < R.a + R.b) : Fin (n + 1) :=
  R.rIdx.get ⟨q, by
    rw [R.rIdx_length]
    exact hq⟩

private lemma sign_getR_left {q : ℕ} (hq : q < R.a) :
    signOf d (R.getR q (by omega)) = σ := by
  have hmap :
      R.rIdx.map (signOf d) =
        (nzSigns d).rotate R.k := by
    -- because `nzSigns = (nzIdx).map signOf`
    simp [rIdx, nzSigns, signOf, List.map_rotate]
  have hmain :
      R.rIdx.map (signOf d) =
        List.replicate R.a σ ++ List.replicate R.b (!σ) := by
    rw [hmap, R.hrot]
  have hget := congrArg
    (fun xs : List Bool =>
      xs.get ⟨q, by
        rw [hmain]
        simp
        omega⟩) hmain
  simpa [getR, hq] using hget

private lemma sign_getR_right {q : ℕ} (hq₁ : R.a ≤ q) (hq₂ : q < R.a + R.b) :
    signOf d (R.getR q hq₂) = !σ := by
  have hmap :
      R.rIdx.map (signOf d) =
        (nzSigns d).rotate R.k := by
    simp [rIdx, nzSigns, signOf, List.map_rotate]
  have hmain :
      R.rIdx.map (signOf d) =
        List.replicate R.a σ ++ List.replicate R.b (!σ) := by
    rw [hmap, R.hrot]
  have hget := congrArg
    (fun xs : List Bool =>
      xs.get ⟨q, by
        rw [hmain]
        simp
        omega⟩) hmain
  simpa [getR, hq₁, hq₂] using hget

/--
The cyclic sortedness of `rIdx` measured from its first entry.

Replace the theorem name `nzIdx_rotate_pairwise_cval` with your clean-3
strict-increasing lemma if it has a different name.

Expected statement:

```lean
nzIdx_rotate_pairwise_cval :
  ∀ (d : Fin (n+1) → ℝ) (k : ℕ),
    let r := (nzIdx d).rotate k
    r ≠ [] →
    r.Pairwise
      (fun x y =>
        cval (n+1) (r.get ⟨0, by ...⟩).val x.val
          <
        cval (n+1) (r.get ⟨0, by ...⟩).val y.val)
```
-/
private lemma rIdx_pairwise_from_first :
    R.rIdx.Pairwise
      (fun x y =>
        cval (n + 1) (R.getR 0 (by omega)).val x.val
          <
        cval (n + 1) (R.getR 0 (by omega)).val y.val) := by
  -- This is exactly the “nzIdx is strictly increasing, rotate once,
  -- then measure values in cyclic coordinates from the rotated head” lemma.
  simpa [rIdx, getR, R.rIdx_length] using
    nzIdx_rotate_pairwise_cval (d := d) (k := R.k) (R.rIdx_ne_nil)

/--
If a nonzero full index lies in the open arc from `pred(firstσ)` to
`lastσ`, then it belongs to the first sign block.

This is the list/index lift.
-/
private lemma sign_firstBlock_of_in_dropLast_arc
    (ha2 : 2 ≤ R.a) (hb1 : 1 ≤ R.b)
    {j : Fin (n + 1)}
    (hj0 : d j ≠ 0)
    (hjArc :
      cycOpen (n + 1)
        (predVal (R.getR 0 (by omega)))
        (R.getR (R.a - 1) (by omega)).val
        j.val) :
    signOf d j = σ := by
  have hjmem0 : j ∈ nzIdx d := by
    -- your clean-3 lemma:
    -- `mem_nzIdx : j ∈ nzIdx d ↔ d j ≠ 0`
    exact (mem_nzIdx (d := d) j).2 hj0

  have hjmem : j ∈ R.rIdx := by
    simpa [rIdx] using (List.mem_rotate.2 hjmem0)

  obtain ⟨q, hqget⟩ := exists_get_of_mem hjmem

  have hqBound : q.val < R.a + R.b := by
    simpa [R.rIdx_length] using q.isLt

  have hfirst :
      R.getR 0 (by omega) = R.rIdx.get ⟨0, by
        rw [R.rIdx_length]
        omega⟩ := rfl
  have hlast :
      R.getR (R.a - 1) (by omega) =
        R.rIdx.get ⟨R.a - 1, by
          rw [R.rIdx_length]
          omega⟩ := rfl

  have hArcShift :
      cval (n + 1) (R.getR 0 (by omega)).val j.val
        <
      cval (n + 1) (R.getR 0 (by omega)).val
        (R.getR (R.a - 1) (by omega)).val := by
    -- arithmetic: open arc from pred(first) to last
    -- means cyclic coordinate is strictly before last.
    simpa [hfirst, hlast] using
      cval_lt_of_cycOpen_pred_last
        (n := n)
        (first := R.getR 0 (by omega))
        (last := R.getR (R.a - 1) (by omega))
        (j := j)
        hjArc

  have hq_lt_a : q.val < R.a := by
    by_contra hqa
    have hqa' : R.a ≤ q.val := by omega
    have hlt_index : (R.a - 1 : ℕ) < q.val := by omega
    have hpair := R.rIdx_pairwise_from_first.rel_of_get
      (i := ⟨R.a - 1, by
        rw [R.rIdx_length]
        omega⟩)
      (j := q)
      hlt_index
    rw [← hqget] at hArcShift
    exact not_lt_of_ge (le_of_lt hArcShift) hpair

  rw [← hqget]
  simpa [getR] using R.sign_getR_left hq_lt_a

/--
If a nonzero full index lies in the complementary open arc from
`lastσ` to `pred(firstσ)`, then it belongs to the second sign block.
-/
private lemma sign_secondBlock_of_in_complement_arc
    (ha2 : 2 ≤ R.a) (hb2 : 2 ≤ R.b)
    {j : Fin (n + 1)}
    (hj0 : d j ≠ 0)
    (hjArc :
      cycOpen (n + 1)
        (R.getR (R.a - 1) (by omega)).val
        (predVal (R.getR 0 (by omega)))
        j.val) :
    signOf d j = !σ := by
  have hjmem0 : j ∈ nzIdx d :=
    (mem_nzIdx (d := d) j).2 hj0

  have hjmem : j ∈ R.rIdx := by
    simpa [rIdx] using (List.mem_rotate.2 hjmem0)

  obtain ⟨q, hqget⟩ := exists_get_of_mem hjmem

  have hcompShift :
      cval (n + 1) (R.getR 0 (by omega)).val
        (R.getR (R.a - 1) (by omega)).val
        <
      cval (n + 1) (R.getR 0 (by omega)).val j.val := by
    simpa using
      cval_last_lt_of_cycOpen_last_pred
        (n := n)
        (first := R.getR 0 (by omega))
        (last := R.getR (R.a - 1) (by omega))
        (j := j)
        hjArc

  have hq_ge_a : R.a ≤ q.val := by
    by_contra hqa
    have hq_lt_a : q.val < R.a := by omega
    have hq_le_last : q.val ≤ R.a - 1 := by omega
    have hshift_le :
        cval (n + 1) (R.getR 0 (by omega)).val j.val
          ≤
        cval (n + 1) (R.getR 0 (by omega)).val
          (R.getR (R.a - 1) (by omega)).val := by
      rcases lt_or_eq_of_le hq_le_last with hlt | heq
      · have hpair := R.rIdx_pairwise_from_first.rel_of_get
          (i := q)
          (j := ⟨R.a - 1, by
            rw [R.rIdx_length]
            omega⟩)
          hlt
        rw [hqget] at hpair
        exact le_of_lt hpair
      · have : j = R.getR (R.a - 1) (by omega) := by
          rw [← hqget]
          apply congrArg R.rIdx.get
          apply Fin.ext
          exact heq
        simp [this]
    exact not_lt_of_ge hshift_le hcompShift

  rw [← hqget]
  exact R.sign_getR_right hq_ge_a (by
    simpa [R.rIdx_length] using q.isLt)

/--
If the first block has length one, every nonzero entry with sign `σ`
is that singleton.
-/
private lemma eq_singleton_firstBlock_of_sign
    (ha1 : R.a = 1)
    {j : Fin (n + 1)}
    (hj0 : d j ≠ 0)
    (hsgn : signOf d j = σ) :
    j = R.getR 0 (by omega) := by
  have hjmem0 : j ∈ nzIdx d :=
    (mem_nzIdx (d := d) j).2 hj0
  have hjmem : j ∈ R.rIdx := by
    simpa [rIdx] using (List.mem_rotate.2 hjmem0)
  obtain ⟨q, hqget⟩ := exists_get_of_mem hjmem

  have hq_lt_one : q.val < 1 := by
    by_contra hq
    have hqa : R.a ≤ q.val := by omega
    have hright := R.sign_getR_right
      (q := q.val) hqa (by
        simpa [R.rIdx_length] using q.isLt)
    rw [← hqget] at hright
    cases σ <;> simp at hsgn hright
  apply Fin.ext
  have hq0 : q.val = 0 := by omega
  have : q = ⟨0, by
      rw [R.rIdx_length]
      omega⟩ := Fin.ext hq0
  rw [← hqget, this]
  rfl

/--
If the second block has length one, every nonzero entry with sign `!σ`
is that singleton.
-/
private lemma eq_singleton_secondBlock_of_sign
    (hb1 : R.b = 1)
    {j : Fin (n + 1)}
    (hj0 : d j ≠ 0)
    (hsgn : signOf d j = !σ) :
    j = R.getR R.a (by omega) := by
  have hjmem0 : j ∈ nzIdx d :=
    (mem_nzIdx (d := d) j).2 hj0
  have hjmem : j ∈ R.rIdx := by
    simpa [rIdx] using (List.mem_rotate.2 hjmem0)
  obtain ⟨q, hqget⟩ := exists_get_of_mem hjmem

  have hq_ge_a : R.a ≤ q.val := by
    by_contra hq
    have hleft := R.sign_getR_left
      (q := q.val) (by omega)
    rw [← hqget] at hleft
    cases σ <;> simp at hsgn hleft

  have hq_eq_a : q.val = R.a := by
    have hq_lt : q.val < R.a + R.b := by
      simpa [R.rIdx_length] using q.isLt
    omega

  apply Fin.ext
  have : q = ⟨R.a, by
      rw [R.rIdx_length]
      omega⟩ := Fin.ext hq_eq_a
  rw [← hqget, this]
  rfl

end RotTwoBlock

/-! ## Arithmetic lemmas used in the two block-order proofs.

These close by `split_ifs` and `omega`; they are deliberately independent
of list theory.
-/

private lemma cval_lt_of_cycOpen_pred_last
    {n : ℕ} {first last j : Fin (n + 1)}
    (hj :
      cycOpen (n + 1) (predVal first) last.val j.val) :
    cval (n + 1) first.val j.val
      <
    cval (n + 1) first.val last.val := by
  unfold cycOpen predVal cval at hj ⊢
  split_ifs at hj ⊢ <;> omega

private lemma cval_last_lt_of_cycOpen_last_pred
    {n : ℕ} {first last j : Fin (n + 1)}
    (hj :
      cycOpen (n + 1) last.val (predVal first) j.val) :
    cval (n + 1) first.val last.val
      <
    cval (n + 1) first.val j.val := by
  unfold cycOpen predVal cval at hj ⊢
  split_ifs at hj ⊢ <;> omega

private lemma first_mem_dropLast_arc
    {n : ℕ} {R : RotTwoBlock (d := d) (σ := σ)}
    (ha2 : 2 ≤ R.a) (hb1 : 1 ≤ R.b) :
    cycOpen (n + 1)
      (predVal (R.getR 0 (by omega)))
      (R.getR (R.a - 1) (by omega)).val
      (R.getR 0 (by omega)).val := by
  -- Since the second block is nonempty, the first block does not wrap
  -- all the way to `pred(first)`.  This is exactly the shifted-order
  -- inequality between `lastσ` and `first!σ`.
  have hpair := R.rIdx_pairwise_from_first.rel_of_get
    (i := ⟨R.a - 1, by
      rw [R.rIdx_length]
      omega⟩)
    (j := ⟨R.a, by
      rw [R.rIdx_length]
      omega⟩)
    (by omega)
  unfold cycOpen predVal cval at hpair ⊢
  split_ifs at hpair ⊢ <;> omega

private lemma first_secondBlock_mem_complement_arc
    {n : ℕ} {R : RotTwoBlock (d := d) (σ := σ)}
    (ha2 : 2 ≤ R.a) (hb2 : 2 ≤ R.b) :
    cycOpen (n + 1)
      (R.getR (R.a - 1) (by omega)).val
      (predVal (R.getR 0 (by omega)))
      (R.getR R.a (by omega)).val := by
  have hlast_lt_firstOpp := R.rIdx_pairwise_from_first.rel_of_get
    (i := ⟨R.a - 1, by
      rw [R.rIdx_length]
      omega⟩)
    (j := ⟨R.a, by
      rw [R.rIdx_length]
      omega⟩)
    (by omega)
  have hfirstOpp_lt_lastOpp := R.rIdx_pairwise_from_first.rel_of_get
    (i := ⟨R.a, by
      rw [R.rIdx_length]
      omega⟩)
    (j := ⟨R.a + 1, by
      rw [R.rIdx_length]
      omega⟩)
    (by omega)
  unfold cycOpen predVal cval at hlast_lt_firstOpp hfirstOpp_lt_lastOpp ⊢
  split_ifs at hlast_lt_firstOpp hfirstOpp_lt_lastOpp ⊢ <;> omega

/-! ## Emitters: turn a cyclic strict arc into your oriented cut constructors. -/

private def emitPosFromArc
    {n : ℕ} (d : Fin (n + 1) → ℝ)
    (l r : ℕ) (hl : l ≤ n) (hr : r ≤ n)
    (hLen : 2 ≤ cdist (n + 1) l r)
    (hComp : 2 ≤ cdist (n + 1) r l)
    (hpos :
      ∀ j : Fin (n + 1),
        cycOpen (n + 1) l r j.val → 0 ≤ d j)
    (hstrictNonwrapOrWrap :
      ∀ hlt : l < r,
        ∃ i : Fin (r - l - 1),
          0 < d (nonwrapIdx (n := n) (t := l) (s := r) hr i))
    (hstrictWrap :
      ∀ hgt : r < l,
        ∃ i : Fin (wrapLen n l r - 1),
          0 < d (wrapIdx (n := n) (t := r) (s := l) hgt hl i))
    (hneg :
      ∀ j : Fin (n + 1),
        cycOpen (n + 1) r l j.val → d j ≤ 0) :
    OrientedTwoArcCut d := by
  rcases lt_trichotomy l r with hlr | heq | hrl
  · -- positive strict non-wrapping
    refine OrientedTwoArcCut.PosNonwrap
      { t := l
        s := r
        hts := hlr
        hsn := hr
        hm1 := by
          simpa [cdist_of_lt hlr] using hLen
        hm2 := by
          have := hComp
          rw [cdist_of_gt hlr] at this
          simpa [wrapLen] using this
        nonwrap_nonneg := ?_
        nonwrap_pos := ?_
        wrap_nonpos := ?_ }
    · intro i
      exact hpos _ (nonwrapIdx_mem_cycOpen hlr hr i)
    · exact hstrictNonwrapOrWrap hlr
    · intro i
      exact hneg _ (wrapIdx_mem_cycOpen hlr hr i)
  · subst heq
    simp [cdist] at hLen
  · -- positive strict wrapping
    refine OrientedTwoArcCut.PosWrap
      { t := r
        s := l
        hts := hrl
        hsn := hl
        hm1 := by
          have := hComp
          simpa [cdist_of_lt hrl] using this
        hm2 := by
          have := hLen
          rw [cdist_of_gt hrl] at this
          simpa [wrapLen] using this
        nonwrap_nonpos := ?_
        wrap_nonneg := ?_
        wrap_pos := ?_ }
    · intro i
      exact hneg _ (nonwrapIdx_mem_cycOpen hrl hl i)
    · intro i
      exact hpos _ (wrapIdx_mem_cycOpen hrl hl i)
    · exact hstrictWrap hrl

private def emitNegFromArc
    {n : ℕ} (d : Fin (n + 1) → ℝ)
    (l r : ℕ) (hl : l ≤ n) (hr : r ≤ n)
    (hLen : 2 ≤ cdist (n + 1) l r)
    (hComp : 2 ≤ cdist (n + 1) r l)
    (hneg :
      ∀ j : Fin (n + 1),
        cycOpen (n + 1) l r j.val → d j ≤ 0)
    (hstrictNonwrapOrWrap :
      ∀ hlt : l < r,
        ∃ i : Fin (r - l - 1),
          d (nonwrapIdx (n := n) (t := l) (s := r) hr i) < 0)
    (hstrictWrap :
      ∀ hgt : r < l,
        ∃ i : Fin (wrapLen n l r - 1),
          d (wrapIdx (n := n) (t := r) (s := l) hgt hl i) < 0)
    (hpos :
      ∀ j : Fin (n + 1),
        cycOpen (n + 1) r l j.val → 0 ≤ d j) :
    OrientedTwoArcCut d := by
  rcases lt_trichotomy l r with hlr | heq | hrl
  · -- negative strict non-wrapping
    refine OrientedTwoArcCut.NegNonwrap
      { t := l
        s := r
        hts := hlr
        hsn := hr
        hm1 := by
          simpa [cdist_of_lt hlr] using hLen
        hm2 := by
          have := hComp
          rw [cdist_of_gt hlr] at this
          simpa [wrapLen] using this
        nonwrap_nonpos := ?_
        nonwrap_neg := ?_
        wrap_nonneg := ?_ }
    · intro i
      exact hneg _ (nonwrapIdx_mem_cycOpen hlr hr i)
    · exact hstrictNonwrapOrWrap hlr
    · intro i
      exact hpos _ (wrapIdx_mem_cycOpen hlr hr i)
  · subst heq
    simp [cdist] at hLen
  · -- negative strict wrapping
    refine OrientedTwoArcCut.NegWrap
      { t := r
        s := l
        hts := hrl
        hsn := hl
        hm1 := by
          have := hComp
          simpa [cdist_of_lt hrl] using this
        hm2 := by
          have := hLen
          rw [cdist_of_gt hrl] at this
          simpa [wrapLen] using this
        nonwrap_nonneg := ?_
        wrap_nonpos := ?_
        wrap_neg := ?_ }
    · intro i
      exact hpos _ (nonwrapIdx_mem_cycOpen hrl hl i)
    · intro i
      exact hneg _ (wrapIdx_mem_cycOpen hrl hl i)
    · exact hstrictWrap hrl

/-! ## Singleton run emitters. -/

private def cut_singleton_pos
    {n : ℕ} (d : Fin (n + 1) → ℝ) (hn : 3 ≤ n)
    (x : Fin (n + 1))
    (hxpos : 0 < d x)
    (honly :
      ∀ j : Fin (n + 1), d j ≠ 0 → signOf d j = true → j = x) :
    OrientedTwoArcCut d := by
  let l := predVal x
  let r := succVal x

  have hl : l ≤ n := predVal_le x
  have hr : r ≤ n := succVal_le x

  have hLens := pred_succ_singleton_lengths hn x
  have hLen : 2 ≤ cdist (n + 1) l r := by
    simpa [l, r] using le_of_eq hLens.1.symm
  have hComp : 2 ≤ cdist (n + 1) r l := by
    have hn' : 2 ≤ n - 1 := by omega
    simpa [l, r, hLens.2] using hn'

  refine emitPosFromArc d l r hl hr hLen hComp ?hpos ?hstrictNW ?hstrictW ?hneg

  · intro j hjArc
    have hj : j = x := singleton_forward_arc_eq hn x hjArc
    subst hj
    exact le_of_lt hxpos

  · intro hlt
    refine ⟨0, ?_⟩
    have hidx :
        nonwrapIdx (n := n) (t := l) (s := r) hr (0 : Fin (r - l - 1)) = x := by
      apply Fin.ext
      unfold nonwrapIdx l r predVal succVal at hlt ⊢
      split_ifs at hlt ⊢ <;> omega
    simpa [hidx] using hxpos

  · intro hgt
    refine ⟨0, ?_⟩
    have hidx :
        wrapIdx (n := n) (t := r) (s := l) hgt hl
            (0 : Fin (wrapLen n l r - 1)) = x := by
      apply Fin.ext
      unfold wrapIdx wrapLen l r predVal succVal at hgt ⊢
      simp [Fin.val_add]
      split_ifs at hgt ⊢ <;> omega
    simpa [hidx] using hxpos

  · intro j hjArc
    by_cases hj0 : d j = 0
    · simp [hj0]
    · by_cases hsgn : signOf d j = true
      · have hEq := honly j hj0 hsgn
        subst hEq
        have hne := singleton_reverse_arc_ne hn x hjArc
        exact False.elim (hne rfl)
      · have hfalse : signOf d j = false := by
          cases h : signOf d j <;> simp [h] at hsgn ⊢
        exact le_of_lt (neg_of_sign_false hj0 hfalse)

private def cut_singleton_neg
    {n : ℕ} (d : Fin (n + 1) → ℝ) (hn : 3 ≤ n)
    (x : Fin (n + 1))
    (hxneg : d x < 0)
    (honly :
      ∀ j : Fin (n + 1), d j ≠ 0 → signOf d j = false → j = x) :
    OrientedTwoArcCut d := by
  let l := predVal x
  let r := succVal x

  have hl : l ≤ n := predVal_le x
  have hr : r ≤ n := succVal_le x

  have hLens := pred_succ_singleton_lengths hn x
  have hLen : 2 ≤ cdist (n + 1) l r := by
    simpa [l, r] using le_of_eq hLens.1.symm
  have hComp : 2 ≤ cdist (n + 1) r l := by
    have hn' : 2 ≤ n - 1 := by omega
    simpa [l, r, hLens.2] using hn'

  refine emitNegFromArc d l r hl hr hLen hComp ?hneg ?hstrictNW ?hstrictW ?hpos

  · intro j hjArc
    have hj : j = x := singleton_forward_arc_eq hn x hjArc
    subst hj
    exact le_of_lt hxneg

  · intro hlt
    refine ⟨0, ?_⟩
    have hidx :
        nonwrapIdx (n := n) (t := l) (s := r) hr (0 : Fin (r - l - 1)) = x := by
      apply Fin.ext
      unfold nonwrapIdx l r predVal succVal at hlt ⊢
      split_ifs at hlt ⊢ <;> omega
    simpa [hidx] using hxneg

  · intro hgt
    refine ⟨0, ?_⟩
    have hidx :
        wrapIdx (n := n) (t := r) (s := l) hgt hl
            (0 : Fin (wrapLen n l r - 1)) = x := by
      apply Fin.ext
      unfold wrapIdx wrapLen l r predVal succVal at hgt ⊢
      simp [Fin.val_add]
      split_ifs at hgt ⊢ <;> omega
    simpa [hidx] using hxneg

  · intro j hjArc
    by_cases hj0 : d j = 0
    · simp [hj0]
    · by_cases hsgn : signOf d j = false
      · have hEq := honly j hj0 hsgn
        subst hEq
        have hne := singleton_reverse_arc_ne hn x hjArc
        exact False.elim (hne rfl)
      · have htrue : signOf d j = true := by
          cases h : signOf d j <;> simp [h] at hsgn ⊢
        exact le_of_lt (pos_of_sign_true htrue)

/-! ## Non-singleton first-block emitter.

This uses:

  left  = pred(first first-block)
  right = last first-block

and requires both blocks to have length at least `2`.
-/

private def cut_firstBlock_dropLast
    {n : ℕ} {d : Fin (n + 1) → ℝ} {σ : Bool}
    (hn : 3 ≤ n) (R : RotTwoBlock d σ)
    (ha2 : 2 ≤ R.a) (hb2 : 2 ≤ R.b) :
    OrientedTwoArcCut d := by
  let first := R.getR 0 (by omega)
  let last  := R.getR (R.a - 1) (by omega)
  let l := predVal first
  let r := last.val

  have hl : l ≤ n := predVal_le first
  have hr : r ≤ n := by
    exact Nat.le_of_lt_succ last.isLt

  have hfirstArc :
      cycOpen (n + 1) l r first.val := by
    simpa [first, last, l, r] using
      first_mem_dropLast_arc (R := R) ha2 (by omega)

  have hfirstOppArc :
      cycOpen (n + 1) r l (R.getR R.a (by omega)).val := by
    simpa [first, last, l, r] using
      first_secondBlock_mem_complement_arc (R := R) ha2 hb2

  have hLen : 2 ≤ cdist (n + 1) l r := by
    exact two_le_cdist_of_cycOpen
      (x := first.val)
      (by exact first.isLt)
      (by omega)
      (by omega)
      hfirstArc

  have hComp : 2 ≤ cdist (n + 1) r l := by
    exact two_le_cdist_of_cycOpen
      (x := (R.getR R.a (by omega)).val)
      (by exact (R.getR R.a (by omega)).isLt)
      (by omega)
      (by omega)
      hfirstOppArc

  have hfirstSign : signOf d first = σ := by
    simpa [first] using R.sign_getR_left (q := 0) (by omega)

  by_cases hσ : σ = true

  · -- first block is positive; strict arc is positive.
    have hfirstPos : 0 < d first := by
      exact pos_of_sign_true (by simpa [hσ] using hfirstSign)

    refine emitPosFromArc d l r hl hr hLen hComp ?hpos ?hstrictNW ?hstrictW ?hneg

    · intro j hjArc
      by_cases hj0 : d j = 0
      · simp [hj0]
      · have hsign :
            signOf d j = true := by
          have hs := R.sign_firstBlock_of_in_dropLast_arc
            ha2 (by omega) hj0 (by
              simpa [first, last, l, r] using hjArc)
          simpa [hσ] using hs
        exact le_of_lt (pos_of_sign_true hsign)

    · intro hlt
      refine ⟨0, ?_⟩
      have hidx :
          nonwrapIdx (n := n) (t := l) (s := r) hr
              (0 : Fin (r - l - 1)) = first := by
        apply Fin.ext
        unfold nonwrapIdx l r first predVal at hlt ⊢
        split_ifs at hlt ⊢ <;> omega
      simpa [hidx] using hfirstPos

    · intro hgt
      refine ⟨0, ?_⟩
      have hidx :
          wrapIdx (n := n) (t := r) (s := l) hgt hl
              (0 : Fin (wrapLen n l r - 1)) = first := by
        apply Fin.ext
        unfold wrapIdx wrapLen l r first predVal at hgt ⊢
        simp [Fin.val_add]
        split_ifs at hgt ⊢ <;> omega
      simpa [hidx] using hfirstPos

    · intro j hjArc
      by_cases hj0 : d j = 0
      · simp [hj0]
      · have hsign :
            signOf d j = false := by
          have hs := R.sign_secondBlock_of_in_complement_arc
            ha2 hb2 hj0 (by
              simpa [first, last, l, r] using hjArc)
          simpa [hσ] using hs
        exact le_of_lt (neg_of_sign_false hj0 hsign)

  · -- first block is negative; strict arc is negative.
    have hσfalse : σ = false := by
      cases σ <;> simp at hσ ⊢
    have hfirstNeg : d first < 0 := by
      exact neg_of_sign_false
        (by
          intro hz
          have : signOf d first = true := by simp [signOf, hz]
          rw [hfirstSign, hσfalse] at this
          simp at this)
        (by simpa [hσfalse] using hfirstSign)

    refine emitNegFromArc d l r hl hr hLen hComp ?hneg ?hstrictNW ?hstrictW ?hpos

    · intro j hjArc
      by_cases hj0 : d j = 0
      · simp [hj0]
      · have hsign :
            signOf d j = false := by
          have hs := R.sign_firstBlock_of_in_dropLast_arc
            ha2 (by omega) hj0 (by
              simpa [first, last, l, r] using hjArc)
          simpa [hσfalse] using hs
        exact le_of_lt (neg_of_sign_false hj0 hsign)

    · intro hlt
      refine ⟨0, ?_⟩
      have hidx :
          nonwrapIdx (n := n) (t := l) (s := r) hr
              (0 : Fin (r - l - 1)) = first := by
        apply Fin.ext
        unfold nonwrapIdx l r first predVal at hlt ⊢
        split_ifs at hlt ⊢ <;> omega
      simpa [hidx] using hfirstNeg

    · intro hgt
      refine ⟨0, ?_⟩
      have hidx :
          wrapIdx (n := n) (t := r) (s := l) hgt hl
              (0 : Fin (wrapLen n l r - 1)) = first := by
        apply Fin.ext
        unfold wrapIdx wrapLen l r first predVal at hgt ⊢
        simp [Fin.val_add]
        split_ifs at hgt ⊢ <;> omega
      simpa [hidx] using hfirstNeg

    · intro j hjArc
      by_cases hj0 : d j = 0
      · simp [hj0]
      · have hsign :
            signOf d j = true := by
          have hs := R.sign_secondBlock_of_in_complement_arc
            ha2 hb2 hj0 (by
              simpa [first, last, l, r] using hjArc)
          simpa [hσfalse] using hs
        exact le_of_lt (pos_of_sign_true hsign)

/-! ## Main rotated-run dispatcher. -/

private def cut_of_rot_two_block
    {n : ℕ} {d : Fin (n + 1) → ℝ} {σ : Bool}
    (hn : 3 ≤ n) (R : RotTwoBlock d σ) :
    OrientedTwoArcCut d := by
  by_cases ha1 : R.a = 1
  · -- first block singleton
    let x := R.getR 0 (by omega)
    have hxsign : signOf d x = σ := by
      simpa [x] using R.sign_getR_left (q := 0) (by omega)

    cases hσ : σ
    · -- singleton negative
      have hxneg : d x < 0 := by
        have hxfalse : signOf d x = false := by
          simpa [hσ] using hxsign
        have hx0 : d x ≠ 0 := by
          -- because x is in `nzIdx`
          exact (mem_nzIdx (d := d) x).1 (by
            simpa [x, RotTwoBlock.rIdx] using
              List.get_mem R.rIdx ⟨0, by
                rw [R.rIdx_length]
                omega⟩)
        exact neg_of_sign_false hx0 hxfalse

      refine cut_singleton_neg d hn x hxneg ?honly
      intro j hj0 hsgn
      exact R.eq_singleton_firstBlock_of_sign ha1 hj0 (by
        simpa [hσ] using hsgn)

    · -- singleton positive
      have hxpos : 0 < d x := by
        exact pos_of_sign_true (by simpa [hσ] using hxsign)

      refine cut_singleton_pos d hn x hxpos ?honly
      intro j hj0 hsgn
      exact R.eq_singleton_firstBlock_of_sign ha1 hj0 (by
        simpa [hσ] using hsgn)

  · by_cases hb1 : R.b = 1
    · -- second block singleton
      let x := R.getR R.a (by omega)
      have hxsign : signOf d x = !σ := by
        simpa [x] using
          R.sign_getR_right (q := R.a) (by omega) (by omega)

      cases hσ : σ
      · -- σ=false, so second singleton is positive
        have hxpos : 0 < d x := by
          exact pos_of_sign_true (by simpa [hσ] using hxsign)

        refine cut_singleton_pos d hn x hxpos ?honly
        intro j hj0 hsgn
        have hEq := R.eq_singleton_secondBlock_of_sign hb1 hj0 (by
          simpa [hσ] using hsgn)
        exact hEq

      · -- σ=true, so second singleton is negative
        have hxneg : d x < 0 := by
          have hxfalse : signOf d x = false := by
            simpa [hσ] using hxsign
          have hx0 : d x ≠ 0 := by
            exact (mem_nzIdx (d := d) x).1 (by
              simpa [x, RotTwoBlock.rIdx] using
                List.get_mem R.rIdx ⟨R.a, by
                  rw [R.rIdx_length]
                  omega⟩)
          exact neg_of_sign_false hx0 hxfalse

        refine cut_singleton_neg d hn x hxneg ?honly
        intro j hj0 hsgn
        have hEq := R.eq_singleton_secondBlock_of_sign hb1 hj0 (by
          simpa [hσ] using hsgn)
        exact hEq

    · -- both blocks length at least 2; use first block and drop its last element to a seam endpoint
      have ha2 : 2 ≤ R.a := by omega
      have hb2 : 2 ≤ R.b := by omega
      exact cut_firstBlock_dropLast hn R ha2 hb2

/-! ## Final theorem. -/

theorem oriented_cut_of_signChangesFull_eq_two
    {n : ℕ} (d : Fin (n + 1) → ℝ)
    (hn : 3 ≤ n)
    (h2 : signChangesFull d = 2) :
    OrientedTwoArcCut d := by
  classical
  unfold signChangesFull at h2

  -- Your clean-3 theorem.  I write the destructuring in the common shape:
  --
  --   cyclicFlips_two_blocks L h2 :
  --     (∃ k a b, 1 ≤ a ∧ 1 ≤ b ∧
  --        L.rotate k = replicate a true ++ replicate b false)
  --     ∨
  --     (∃ k a b, 1 ≤ a ∧ 1 ≤ b ∧
  --        L.rotate k = replicate a false ++ replicate b true)
  --
  -- If your theorem packages `a,b` or the mirror differently, only this
  -- `rcases` block changes.
  rcases cyclicFlips_two_blocks (nzSigns d) h2 with htf | hft

  · rcases htf with ⟨k, a, b, ha, hb, hrot⟩
    exact cut_of_rot_two_block hn
      ({ k := k
         a := a
         b := b
         ha := ha
         hb := hb
         hrot := by
           simpa using hrot } :
        RotTwoBlock d true)

  · rcases hft with ⟨k, a, b, ha, hb, hrot⟩
    exact cut_of_rot_two_block hn
      ({ k := k
         a := a
         b := b
         ha := ha
         hb := hb
         hrot := by
           simpa using hrot } :
        RotTwoBlock d false)

end

end ProofsInTheBook.Ch13ArmVertexFull
```

The two helper names you are most likely to have under different names are:

```lean
mem_nzIdx :
  i ∈ nzIdx d ↔ d i ≠ 0
```

and

```lean
nzIdx_rotate_pairwise_cval :
  ((nzIdx d).rotate k).Pairwise
    (fun x y =>
      cval (n+1) (((nzIdx d).rotate k).get ⟨0, ...⟩).val x.val
        <
      cval (n+1) (((nzIdx d).rotate k).get ⟨0, ...⟩).val y.val)
```

Everything else is just constructor-field renaming.

The worst case is dispatched exactly by the singleton branch. For `[+,-,0,0]`, the rotated block has `a = b = 1`; the first singleton branch chooses

```lean
x     = the singleton strict nonzero
left  = predVal x
right = succVal x
```

so the strict arc has parameter `2`, and the complementary arc has parameter `n - 1`, which is at least `2` because `hn : 3 ≤ n`.
