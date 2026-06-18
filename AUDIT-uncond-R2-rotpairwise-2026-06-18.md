Use the rotate lemma. The rotate-free flip-scan route is **not** cleaner in Lean; it avoids `rotate` but then you must re-prove a cyclic interval classification for the two flip gaps. The following isolates the only real list/order fact and avoids `pairwise_append` modular pain by proving the stronger `drop j ++ take j` theorem first.

This uses standard Lean list facts: `List.pairwise_append`, `Pairwise.drop`, `Pairwise.take`, and `Pairwise.rel_of_mem_take_of_mem_drop` from `Init.Data.List.Pairwise`, plus `drop_eq_getElem_cons` and `take_append_getElem` from `Init.Data.List.TakeDrop`. citeturn662411view0turn639029view0

```lean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

open scoped Classical

namespace ProofsInTheBook.Ch13ArmVertexFull

/- Your cyclic coordinate. -/
def cval (N start x : ℕ) : ℕ :=
  if start ≤ x then x - start else N - start + x

namespace ListCyclicOrder

variable {N : ℕ}

/-- The pivot element `l[j]` belongs to `l.drop j`. -/
private lemma getElem_mem_drop
    {l : List (Fin N)} {j : ℕ} (hj : j < l.length) :
    l[j] ∈ l.drop j := by
  rw [List.drop_eq_getElem_cons hj]
  simp

/-- The pivot element `l[j]` belongs to `l.take (j+1)`. -/
private lemma getElem_mem_take_succ
    {l : List (Fin N)} {j : ℕ} (hj : j < l.length) :
    l[j] ∈ l.take (j + 1) := by
  rw [← List.take_append_getElem hj]
  simp

/--
In a strictly increasing list, every element of `drop j` has value at least
the pivot value `l[j].val`.
-/
private lemma getElem_val_le_of_mem_drop
    {l : List (Fin N)}
    (hpair : l.Pairwise (fun a b : Fin N => a.val < b.val))
    {j : ℕ} (hj : j < l.length)
    {a : Fin N} (ha : a ∈ l.drop j) :
    l[j].val ≤ a.val := by
  have hdrop : l.drop j = l[j] :: l.drop (j + 1) :=
    List.drop_eq_getElem_cons hj
  rw [hdrop] at ha
  simp only [List.mem_cons] at ha
  rcases ha with ha | ha
  · subst a
    exact le_rfl
  · have hpivot : l[j] ∈ l.take (j + 1) :=
      getElem_mem_take_succ hj
    have hlt : l[j].val < a.val :=
      hpair.rel_of_mem_take_of_mem_drop
        (i := j + 1) hpivot ha
    exact le_of_lt hlt

/--
In a strictly increasing list, every element of `take j` has value strictly
less than the pivot value `l[j].val`.
-/
private lemma val_lt_getElem_val_of_mem_take
    {l : List (Fin N)}
    (hpair : l.Pairwise (fun a b : Fin N => a.val < b.val))
    {j : ℕ} (hj : j < l.length)
    {a : Fin N} (ha : a ∈ l.take j) :
    a.val < l[j].val := by
  have hpivot : l[j] ∈ l.drop j :=
    getElem_mem_drop hj
  exact
    hpair.rel_of_mem_take_of_mem_drop
      (i := j) ha hpivot

/--
Main no-rotate theorem.

If `l` is strictly increasing by `Fin.val`, then `l.drop j ++ l.take j`
is strictly increasing in the cyclic coordinate measured from the pivot
`l[j]`.

This is the theorem that kills the modular split.
-/
theorem pairwise_cval_drop_append_take
    {l : List (Fin N)}
    (hpair : l.Pairwise (fun a b : Fin N => a.val < b.val))
    {j : ℕ} (hj : j < l.length) :
    (l.drop j ++ l.take j).Pairwise
      (fun a b : Fin N =>
        cval N l[j].val a.val < cval N l[j].val b.val) := by
  rw [List.pairwise_append]

  constructor
  · -- Internal `drop j`: ordinary increasing values, same cval branch.
    refine
      (List.Pairwise.drop (i := j) hpair).imp_of_mem ?_
    intro a b ha hb hab
    have hsa : l[j].val ≤ a.val :=
      getElem_val_le_of_mem_drop hpair hj ha
    have hsb : l[j].val ≤ b.val :=
      getElem_val_le_of_mem_drop hpair hj hb
    have haN : a.val < N := a.isLt
    have hbN : b.val < N := b.isLt
    have hsN : l[j].val < N := (l[j]).isLt
    unfold cval
    simp [hsa, hsb]
    omega

  constructor
  · -- Internal `take j`: ordinary increasing values, other cval branch.
    refine
      (List.Pairwise.take (i := j) hpair).imp_of_mem ?_
    intro a b ha hb hab
    have has : a.val < l[j].val :=
      val_lt_getElem_val_of_mem_take hpair hj ha
    have hbs : b.val < l[j].val :=
      val_lt_getElem_val_of_mem_take hpair hj hb
    have hna : ¬ l[j].val ≤ a.val := by omega
    have hnb : ¬ l[j].val ≤ b.val := by omega
    have haN : a.val < N := a.isLt
    have hbN : b.val < N := b.isLt
    have hsN : l[j].val < N := (l[j]).isLt
    unfold cval
    simp [hna, hnb]
    omega

  · -- Cross term: every drop element has small cval, every take element
    -- has wrapped cval, so drop-part elements precede take-part elements.
    intro a ha b hb
    have hsa : l[j].val ≤ a.val :=
      getElem_val_le_of_mem_drop hpair hj ha
    have hbs : b.val < l[j].val :=
      val_lt_getElem_val_of_mem_take hpair hj hb
    have hnb : ¬ l[j].val ≤ b.val := by omega
    have haN : a.val < N := a.isLt
    have hbN : b.val < N := b.isLt
    have hsN : l[j].val < N := (l[j]).isLt
    unfold cval
    simp [hsa, hnb]
    omega

/--
The head of `l.drop j ++ l.take j` is the pivot `l[j]`.

Use this if your target relation is written using `head`.
-/
private lemma head_drop_append_take_eq_getElem
    {l : List (Fin N)}
    {j : ℕ} (hj : j < l.length)
    (hne : l.drop j ++ l.take j ≠ []) :
    (l.drop j ++ l.take j).head hne = l[j] := by
  rw [List.drop_eq_getElem_cons hj]
  rfl

/--
Same theorem, but with the start written as the actual head of the rotated
presentation `drop j ++ take j`.
-/
theorem pairwise_cval_drop_append_take_head
    {l : List (Fin N)}
    (hpair : l.Pairwise (fun a b : Fin N => a.val < b.val))
    {j : ℕ} (hj : j < l.length)
    (hne : l.drop j ++ l.take j ≠ []) :
    (l.drop j ++ l.take j).Pairwise
      (fun a b : Fin N =>
        cval N ((l.drop j ++ l.take j).head hne).val a.val
          <
        cval N ((l.drop j ++ l.take j).head hne).val b.val) := by
  have hhead :
      (l.drop j ++ l.take j).head hne = l[j] :=
    head_drop_append_take_eq_getElem hj hne
  simpa [hhead] using
    pairwise_cval_drop_append_take
      (N := N) (l := l) hpair hj

/--
Transport through any explicit equality
`r = l.drop j ++ l.take j`.

This is often the least brittle wrapper around whatever exact rotate theorem
your local mathlib exposes.
-/
theorem pairwise_cval_of_eq_drop_append_take
    {l r : List (Fin N)}
    (hpair : l.Pairwise (fun a b : Fin N => a.val < b.val))
    {j : ℕ} (hj : j < l.length)
    (hrot : r = l.drop j ++ l.take j)
    (hne : r ≠ []) :
    r.Pairwise
      (fun a b : Fin N =>
        cval N (r.head hne).val a.val
          <
        cval N (r.head hne).val b.val) := by
  subst r
  exact
    pairwise_cval_drop_append_take_head
      (N := N) (l := l) hpair hj hne

end ListCyclicOrder
```

Now the actual `nzIdx` wrapper is tiny. I am writing it in the exact form that avoids depending on the theorem name for `List.rotate`; you feed it the equality your prover already has.

```lean
namespace ProofsInTheBook.Ch13ArmVertexFull

open ListCyclicOrder

/--
Version that assumes the rotate/drop/take equation explicitly.

Use this if your local theorem is named differently.
-/
theorem nzIdx_rotate_pairwise_cval_of_rotate_eq
    {n : ℕ} (d : Fin (n + 1) → ℝ)
    (k j : ℕ)
    (hj : j < (nzIdx d).length)
    (hrot :
      (nzIdx d).rotate k =
        (nzIdx d).drop j ++ (nzIdx d).take j)
    (hne : (nzIdx d).rotate k ≠ []) :
    ((nzIdx d).rotate k).Pairwise
      (fun a b : Fin (n + 1) =>
        cval (n + 1) (((nzIdx d).rotate k).head hne).val a.val
          <
        cval (n + 1) (((nzIdx d).rotate k).head hne).val b.val) := by
  exact
    pairwise_cval_of_eq_drop_append_take
      (N := n + 1)
      (l := nzIdx d)
      (r := (nzIdx d).rotate k)
      (hpair := nzIdx_pairwise_val (d := d))
      (j := j)
      hj
      hrot
      hne

/--
Final modulo wrapper.

Only the one line proving `hrot` may need renaming depending on your local
`List.rotate` API.
-/
theorem nzIdx_rotate_pairwise_cval
    {n : ℕ} (d : Fin (n + 1) → ℝ)
    (k : ℕ)
    (hne : (nzIdx d).rotate k ≠ []) :
    ((nzIdx d).rotate k).Pairwise
      (fun a b : Fin (n + 1) =>
        cval (n + 1) (((nzIdx d).rotate k).head hne).val a.val
          <
        cval (n + 1) (((nzIdx d).rotate k).head hne).val b.val) := by
  classical

  let l : List (Fin (n + 1)) := nzIdx d

  have hlen_pos : 0 < l.length := by
    by_contra h
    have hlen0 : l.length = 0 := by omega
    have hl : l = [] := List.eq_nil_of_length_eq_zero hlen0
    subst l
    simp at hne

  let j : ℕ := k % l.length

  have hj : j < l.length := by
    exact Nat.mod_lt k hlen_pos

  have hrot :
      (nzIdx d).rotate k =
        (nzIdx d).drop j ++ (nzIdx d).take j := by
    -- Replace this line only if your theorem has a different name/order.
    --
    -- Common local shape:
    --   List.rotate_eq_drop_append_take_mod :
    --     xs.rotate k = xs.drop (k % xs.length) ++ xs.take (k % xs.length)
    --
    simpa [l, j] using
      List.rotate_eq_drop_append_take_mod (nzIdx d) k

  exact
    nzIdx_rotate_pairwise_cval_of_rotate_eq
      (d := d) k j
      (by simpa [l] using hj)
      hrot
      hne

end ProofsInTheBook.Ch13ArmVertexFull
```

If your target uses `get ⟨0, hlen⟩` instead of `head hne`, add this adapter:

```lean
namespace ProofsInTheBook.Ch13ArmVertexFull

open ListCyclicOrder

theorem nzIdx_rotate_pairwise_cval_get_zero
    {n : ℕ} (d : Fin (n + 1) → ℝ)
    (k : ℕ)
    (hlen : 0 < ((nzIdx d).rotate k).length) :
    ((nzIdx d).rotate k).Pairwise
      (fun a b : Fin (n + 1) =>
        cval (n + 1)
            (((nzIdx d).rotate k).get ⟨0, hlen⟩).val
            a.val
          <
        cval (n + 1)
            (((nzIdx d).rotate k).get ⟨0, hlen⟩).val
            b.val) := by
  classical
  let r := (nzIdx d).rotate k

  have hne : (nzIdx d).rotate k ≠ [] := by
    exact List.ne_nil_of_length_pos hlen

  have hhead :
      (((nzIdx d).rotate k).head hne)
        =
      ((nzIdx d).rotate k).get ⟨0, hlen⟩ := by
    cases h : (nzIdx d).rotate k with
    | nil =>
        simp [h] at hlen
    | cons x xs =>
        rfl

  simpa [hhead] using
    nzIdx_rotate_pairwise_cval
      (d := d) k hne

end ProofsInTheBook.Ch13ArmVertexFull
```

The key cross-branch inequality is the third branch of `pairwise_cval_drop_append_take`:

```lean
a ∈ drop j  → l[j].val ≤ a.val → cval = a.val - l[j].val
b ∈ take j  → b.val < l[j].val → cval = N - l[j].val + b.val
a.val < N   → a.val - l[j].val < N - l[j].val ≤ N - l[j].val + b.val
```

That is exactly the modular split the autonomous prover was failing to close.
