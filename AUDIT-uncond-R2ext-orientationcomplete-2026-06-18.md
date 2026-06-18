Decisive answer: **the extraction is not true in the exact two-constructor form you stated if the strict witness is required to lie on the positive/opening arc.**  

The pure combinatorics becomes true for `n ≥ 3` only after you allow the strict block to be on **either** of the two sign-definite arcs, with the builder swapping the roles of `A` and `B` in the closing-strict cases.

Your example

```text
d = [+, -, 0, 0]   -- Fin 4, n = 3
```

is **not** a counterexample if you have a “wrap opens” case: choose `t = 1`, `s = 3`. Then the nonwrap interior is `{2}` with `0`, and the wrap interior is `{0}` with `+`.

But this one **is** a counterexample to the strict-positive-only formulation:

```text
d = [-, +, 0, +]   -- Fin 4, n = 3
```

Here

```text
nzSigns d = [false, true, true]
cyclicFlips (nzSigns d) = 2.
```

For `n = 3`, the only nondegenerate cuts have `s - t = 2`, namely `(t,s) = (0,2)` and `(1,3)`.

For `(0,2)`:

```text
nonwrap interior = {1}  has +
wrap interior    = {3}  has +
```

so the complementary arc is not `≤ 0`.

For `(1,3)`:

```text
nonwrap interior = {2}  has 0
wrap interior    = {0}  has -
```

so there is a strict **negative** witness, but no strict positive/opening witness. Thus neither

```lean
nonwrap ≥ 0 with strict positive, wrap ≤ 0
```

nor

```lean
nonwrap ≤ 0, wrap ≥ 0 with strict positive on wrap
```

works.

This phenomenon persists for all larger `n`:

```text
[-, +, 0, 0, ..., 0, +]
```

So `n ≥ 3` alone is **not enough** for the exact theorem

```lean
signChangesFull d = 2 →
  (∃ TwoArcCut d) ∨ (∃ TwoArcCutWrapOpens d)
```

if those two structures only accept a strict positive/opening witness.

The current repo assembler confirms why this matters: `twoArcSplitData_of_indices` requires both nondegenerate arc lengths and a strict monotonicity witness on the chosen opening arc. Its inputs include `2 ≤ s - t`, `2 ≤ wrapLen n s t`, `hmono1`, `hstrict1`, and `hmono2`. fileciteturn21file0L4-L17 The full vertex construction still takes `htwoArc : signChangesFull A B = 2 → TwoArcSplitData A B`, so this cut extraction is exactly the residual interface. fileciteturn26file0L23-L42

## The minimal honest fix

Do **not** add a geometric “spread” hypothesis. Strict convexity and equal sides should not be used to assert that the positive nonzero signs are distributed away from cut endpoints. That would be artificial and likely harder than the theorem you are proving.

Instead, make the cut certificate orientation-complete.

Use either four constructors:

```lean
inductive OrientedTwoArcCut {n : ℕ} (d : Fin (n + 1) → ℝ) : Prop
| nonwrapOpens :
    TwoArcCutNonwrapOpens d → OrientedTwoArcCut d
| wrapOpens :
    TwoArcCutWrapOpens d → OrientedTwoArcCut d
| nonwrapCloses :
    TwoArcCutNonwrapCloses d → OrientedTwoArcCut d
| wrapCloses :
    TwoArcCutWrapCloses d → OrientedTwoArcCut d
```

or, cleaner, use two sign-separation structures where the strict witness may lie on either arc:

```lean
structure TwoArcCutPlusMinus {n : ℕ} (d : Fin (n + 1) → ℝ) where
  t s : ℕ
  hts : t < s
  hsn : s ≤ n
  hm1 : 2 ≤ s - t
  hm2 : 2 ≤ Ch13SubArcWrap.wrapLen n s t

  nonwrap_nonneg :
    ∀ i : Fin (s - t - 1),
      0 ≤ d ⟨t + i.val + 1, by have := i.isLt; omega⟩

  wrap_nonpos :
    ∀ i : Fin (Ch13SubArcWrap.wrapLen n s t - 1),
      d ((⟨i.val + 1, by
            have := i.isLt
            unfold Ch13SubArcWrap.wrapLen at this
            omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩) ≤ 0

  strict :
      (∃ i : Fin (s - t - 1),
        0 < d ⟨t + i.val + 1, by have := i.isLt; omega⟩)
    ∨
      (∃ i : Fin (Ch13SubArcWrap.wrapLen n s t - 1),
        d ((⟨i.val + 1, by
              have := i.isLt
              unfold Ch13SubArcWrap.wrapLen at this
              omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩) < 0)
```

and the swapped version:

```lean
structure TwoArcCutMinusPlus {n : ℕ} (d : Fin (n + 1) → ℝ) where
  t s : ℕ
  hts : t < s
  hsn : s ≤ n
  hm1 : 2 ≤ s - t
  hm2 : 2 ≤ Ch13SubArcWrap.wrapLen n s t

  nonwrap_nonpos :
    ∀ i : Fin (s - t - 1),
      d ⟨t + i.val + 1, by have := i.isLt; omega⟩ ≤ 0

  wrap_nonneg :
    ∀ i : Fin (Ch13SubArcWrap.wrapLen n s t - 1),
      0 ≤ d ((⟨i.val + 1, by
            have := i.isLt
            unfold Ch13SubArcWrap.wrapLen at this
            omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩)

  strict :
      (∃ i : Fin (s - t - 1),
        d ⟨t + i.val + 1, by have := i.isLt; omega⟩ < 0)
    ∨
      (∃ i : Fin (Ch13SubArcWrap.wrapLen n s t - 1),
        0 < d ((⟨i.val + 1, by
              have := i.isLt
              unfold Ch13SubArcWrap.wrapLen at this
              omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩))
```

Then the true pure theorem is:

```lean
theorem twoArcCut_of_cyclicFlips_eq_two
    {n : ℕ} (hn : 3 ≤ n) (d : Fin (n + 1) → ℝ)
    (h2 : cyclicFlips (nzSigns d) = 2) :
    TwoArcCutPlusMinus d ∨ TwoArcCutMinusPlus d := by
  ...
```

This is the right “last combinatorial lemma.”

## Why the generalized theorem is true for `n ≥ 3`

Let `N = n + 1`, so `4 ≤ N`.

From

```lean
cyclicFlips (nzSigns d) = 2
```

the nonzero signs form exactly two cyclic runs:

```text
++++...++++
----...----
```

with zeros removed. Reinsert the zeros. Each zero can be assigned to either adjacent run, because it satisfies both `0 ≤ d i` and `d i ≤ 0`.

So the full cyclic index set has two sign-definite arcs:

```text
P : all d ≥ 0, contains some d > 0
M : all d ≤ 0, contains some d < 0
```

The only subtlety is that one strict block may be represented only at the cut endpoints if you choose the wrong boundary vertices. That is exactly what happens in

```text
[-, +, 0, +].
```

The cure is not a stronger hypothesis; it is allowing the strict witness to come from whichever sign-definite arc remains interior after choosing nonadjacent cuts.

For `N ≥ 4`, you can always choose two distinct nonadjacent cut vertices separating the two cyclic sign regions so that at least one strict nonzero vertex lies in an interior. If the positive block becomes interior, use the `PlusMinus` orientation. If the negative block becomes interior, use the `MinusPlus` orientation, or build the two-arc data with `A` and `B` swapped on the strict arc.

## List lemma: clean Lean statement

Do this in two layers. First, a pure Boolean list lemma.

Define a local rotation predicate if you do not want to depend on Mathlib’s rotation API:

```lean
def List.Rotates {α : Type*} (xs ys : List α) : Prop :=
  ∃ a b, xs = a ++ b ∧ ys = b ++ a
```

Then prove:

```lean
theorem cyclicFlips_eq_two_two_runs
    (L : List Bool)
    (h2 : cyclicFlips L = 2) :
    (∃ P M : List Bool,
        P ≠ [] ∧ M ≠ [] ∧
        List.Rotates L (P ++ M) ∧
        (∀ x ∈ P, x = true) ∧
        (∀ x ∈ M, x = false))
    ∨
    (∃ M P : List Bool,
        M ≠ [] ∧ P ≠ [] ∧
        List.Rotates L (M ++ P) ∧
        (∀ x ∈ M, x = false) ∧
        (∀ x ∈ P, x = true)) := by
  ...
```

The proof strategy I would use:

1. Show `L ≠ []` and `L.length ≥ 2`; otherwise `cyclicFlips L = 0`.
2. Show both signs occur; otherwise `cyclicFlips L = 0` by the existing `cyclicFlips_eq_zero_iff_all_eq`.
3. Pick a cyclic adjacent unequal pair.
4. Rotate `L` immediately after that pair. The closing edge of the rotated list accounts for one flip, so the linear list has exactly one flip.
5. Prove the simple linear lemma:

```lean
theorem flips_eq_one_split
    (L : List Bool)
    (h : flips L = 1) :
    ∃ b P Q,
      P ≠ [] ∧ Q ≠ [] ∧
      L = P ++ Q ∧
      (∀ x ∈ P, x = b) ∧
      (∀ x ∈ Q, x = !b) := by
  -- induction on L; after the unique first change, the tail has `flips = 0`
  ...
```

This is easier than run-length encoding. You only need the “one linear flip gives two constant runs” lemma.

## Indexed lift: do not lift from `List Bool` alone

For the lift back to `Fin (n+1)`, use indexed nonzero signs:

```lean
noncomputable def nzIdx {m : ℕ} (d : Fin m → ℝ) : List (Fin m) :=
  (List.finRange m).filter (fun i => decide (d i ≠ 0))

noncomputable def nzSignedIdx {m : ℕ} (d : Fin m → ℝ) : List (Fin m × Bool) :=
  (nzIdx d).map (fun i => (i, decide (0 < d i)))
```

and prove:

```lean
theorem nzSigns_eq_map_snd_nzSignedIdx
    {m : ℕ} (d : Fin m → ℝ) :
    nzSigns d = (nzSignedIdx d).map Prod.snd := by
  unfold nzSigns nzSignedIdx nzIdx
  simp
```

Then use the Boolean two-run lemma on `(nzSignedIdx d).map Prod.snd`, but retain the original indices from `nzSignedIdx d`.

The indexed theorem should produce a cyclic, unordered cut first:

```lean
def cyclicDist {N : ℕ} (a b : Fin N) : ℕ :=
  (b.val + N - a.val) % N
```

Then:

```lean
structure CyclicSeparatedCut {N : ℕ} (d : Fin N → ℝ) where
  a b : Fin N
  hab : 2 ≤ cyclicDist a b
  hba : 2 ≤ cyclicDist b a

  ab_nonneg :
    ∀ i : Fin (cyclicDist a b - 1),
      0 ≤ d (a + ⟨i.val + 1, by
        -- from i.isLt and hab
        omega⟩)

  ba_nonpos :
    ∀ i : Fin (cyclicDist b a - 1),
      d (b + ⟨i.val + 1, by omega⟩) ≤ 0

  strict :
      (∃ i : Fin (cyclicDist a b - 1),
        0 < d (a + ⟨i.val + 1, by omega⟩))
    ∨
      (∃ i : Fin (cyclicDist b a - 1),
        d (b + ⟨i.val + 1, by omega⟩) < 0)
```

Then prove the clean combinatorial theorem:

```lean
theorem cyclicSeparatedCut_of_cyclicFlips_eq_two
    {N : ℕ} (hN : 4 ≤ N) (d : Fin N → ℝ)
    (h2 : cyclicFlips (nzSigns d) = 2) :
    CyclicSeparatedCut d ∨
    CyclicSeparatedCut (fun i => - d i) := by
  ...
```

The second disjunct is the sign-swapped case. This avoids fighting `t < s` until the final conversion.

## Convert cyclic cut to `t < s`

Once you have `a b : Fin (n+1)`, sort them by value.

```lean
by_cases habv : a.val < b.val
```

If `a.val < b.val`, set:

```lean
t := a.val
s := b.val
```

Then:

```lean
cyclicDist a b = s - t
cyclicDist b a = Ch13SubArcWrap.wrapLen n s t
```

If `¬ a.val < b.val`, since `a ≠ b` follows from `2 ≤ cyclicDist a b`, you get `b.val < a.val`, and set:

```lean
t := b.val
s := a.val
```

Now the nonwrap and wrap arcs are swapped.

The conversion theorem should look like this:

```lean
theorem twoArcCut_of_cyclicSeparatedCut
    {n : ℕ} (d : Fin (n + 1) → ℝ)
    (c : CyclicSeparatedCut d) :
    TwoArcCutPlusMinus d ∨ TwoArcCutMinusPlus d := by
  classical
  by_cases h : c.a.val < c.b.val
  · -- t = a.val, s = b.val
    ...
  · -- t = b.val, s = a.val; swap nonwrap/wrap orientation
    ...
```

This is where most `omega` work lives, but it is localized.

## Feeding the existing builders

For `d = linkDiff A B`, the sign interpretation is:

```lean
0 ≤ d k    ↔ linkAngle A k ≤ linkAngle B k
d k ≤ 0    ↔ linkAngle B k ≤ linkAngle A k
0 < d k    ↔ linkAngle A k < linkAngle B k
d k < 0    ↔ linkAngle B k < linkAngle A k
```

The existing `twoArcSplitData_of_indices` handles the case where the nonwrap arc opens strictly and the wrap arc closes weakly. Its required hypotheses are exactly the nonwrap monotonicity, strict nonwrap monotonicity, and wrap monotonicity fields. fileciteturn21file0L10-L17

For the closing-strict cases, add mirror assemblers that swap the actual arc families:

```lean
-- original positive/opening case
Arc1 := subArc A ...
Brc1 := subArc B ...
Arc2 := subArcWrap A ...
Brc2 := subArcWrap B ...

-- closing-strict case: use B→A as the strict opening comparison
Arc1 := subArcWrap B ...
Brc1 := subArcWrap A ...
Arc2 := subArc B ...
Brc2 := subArc A ...
```

This is legitimate because `TwoArcSplitData` stores the four sub-arms and their side/joint comparison fields directly; the contradiction theorem consumes those fields, not a definitional proof that `Arc1` came from the first parameter `A`. fileciteturn22file0L123-L152

So the final bridge should be:

```lean
theorem twoArcSplitData_of_orientedCut
    {n : ℕ} (hn : 1 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (cut :
      TwoArcCutPlusMinus (linkDiff A B) ∨
      TwoArcCutMinusPlus (linkDiff A B)) :
    TwoArcSplitData A B := by
  rcases cut with cut | cut
  · rcases cut.strict with hpos | hneg
    · -- existing `twoArcSplitData_of_indices`
      exact twoArcSplitData_of_plusMinus_nonwrapStrict ...
    · -- mirror: wrap closes strictly, swap A/B on the strict arc
      exact twoArcSplitData_of_plusMinus_wrapStrictClosing ...
  · rcases cut.strict with hneg | hpos
    · -- mirror: nonwrap closes strictly
      exact twoArcSplitData_of_minusPlus_nonwrapStrictClosing ...
    · -- wrap opens strictly
      exact twoArcSplitData_of_minusPlus_wrapStrictOpening ...
```

## Final recommended theorem

Use this as the residual-closing theorem:

```lean
theorem twoArcSplitData_of_signChangesFull_eq_two
    {n : ℕ} (hn : 3 ≤ n)
    (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hsides : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hclose : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n)))
    (h2 : signChangesFull A B = 2) :
    TwoArcSplitData A B := by
  have hcut :
      TwoArcCutPlusMinus (linkDiff A B) ∨
      TwoArcCutMinusPlus (linkDiff A B) :=
    twoArcCut_of_cyclicFlips_eq_two hn (linkDiff A B) h2

  exact twoArcSplitData_of_orientedCut
    (by omega) A B hA hB hsides hclose hcut
```

Then replace the old `htwoArc` input by this theorem:

```lean
two_sign_changes_obstruction :=
  fun htwo =>
    twoSignChanges_obstruction
      (twoArcSplitData_of_signChangesFull_eq_two hn A B hA hB hsides hclose htwo)
```

## Bottom line

`cyclicFlips = 2` does give two cyclic sign blocks.  
`n ≥ 3` does let you choose nonadjacent cut vertices.  
But the strict witness may be on the “closing” arc, not the positive/opening arc.

So the clean unconditional fix is:

```lean
cyclicFlips = 2
  ⇒ oriented sign-separated cut, strict on either arc
  ⇒ dispatch through four orientation cases
  ⇒ TwoArcSplitData
  ⇒ contradiction
```

Do **not** try to force the positive block to supply the strict witness. That statement is false.
