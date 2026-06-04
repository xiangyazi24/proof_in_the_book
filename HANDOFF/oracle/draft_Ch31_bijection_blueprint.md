# Draft blueprint: Ch31 bijection — `pruferEncode ∘ pruferDecode = id`

This is a pre-written oracle answer ready for dispatch when deepseek
(or future agy) asks for guidance on closing Ch31's bijection wiring.

## Goal

Upgrade `chapter31` from the trivial placeholder
`Fintype.card (pruferCodeSpace n) = n ^ (n - 2)`
to actual Cayley's formula
`Fintype.card (LabeledTree n) = n ^ (n - 2)`
by constructing `pruferEquiv : LabeledTree n ≃ pruferCodeSpace n`.

## The bridge identity

Prove `pruferEncode hn (pruferDecode hn s) = s` for all `s : pruferCodeSpace n`.
This gives `pruferDecode` injective (since `pruferEncode` is its left inverse).

Then:
- Injective `pruferDecode : pruferCodeSpace n → LabeledTree n` →
  `Fintype.card_le_of_injective` gives `n^(n-2) ≤ card LabeledTree n`.
- Combined with `cayley_upper_bound : card LabeledTree n ≤ n^(n-2)`, we have
  `card LabeledTree n = n^(n-2)`.
- Plus injection + card equality → `Fintype.bijective_iff_injective_and_card`
  gives `pruferDecode` bijective.
- `Equiv.ofBijective pruferDecode (...)` gives `pruferCodeSpace n ≃ LabeledTree n`.
- `.symm` gives `LabeledTree n ≃ pruferCodeSpace n` for `cayley_formula`.

## The four-step proof of `pruferEncode_pruferDecode`

### Step 1: `pruferDecode_first_pick`
The first leaf picked by `pruferDecodeAux` (at iteration 1, from `m = 0`) is
exactly `min(Fin n \ image(s))`:

```lean
lemma pruferDecode_first_pick {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (h1 : 1 ≤ n - 2) :
    ∃ h_nonempty,
      (Finset.univ.filter (fun v : Fin n => ∀ j : Fin (n - 2), 0 ≤ j.val → s j ≠ v)).min'
        h_nonempty
      = (Finset.univ.filter (fun v : Fin n =>
          ∀ j : Fin (n - 2), s j ≠ v)).min' h_nonempty
```

Trivial: `0 ≤ j.val` is vacuous, so the filters coincide.

### Step 2: leaves characterization
Show that the leaves of `pruferDecode hn s` are exactly `Fin n \ image(s)`:

```lean
lemma pruferDecode_leaves_eq {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    {v : Fin n | (pruferDecode hn s).1.degree v = 1} =
      (Finset.univ : Finset (Fin n)).toSet \
        (Finset.image s Finset.univ : Set (Fin n))
```

Proof via degree counting in the decode loop. Each vertex `v` gets degree
`count(v in s) + 1`:
- If `v` is one of the iteratively-picked leaves: +1 from the edge added when
  it's picked, plus +k for each time it appears in s at a later position
  (which would put it on the right side of an edge {later_v, v}).
- If `v` is one of the final 2 vertices: +1 from the final edge, plus +k for
  each appearance in s.

So `v` has degree 1 iff `count(v in s) = 0` iff `v ∉ image(s)`.

This degree lemma is the FUNDAMENTAL technical step. Likely 60-100 lines.

### Step 3: neighbor of smallest leaf

```lean
lemma pruferDecode_smallestLeaf_neighbor {n : ℕ} (hn : 2 ≤ n)
    (s : pruferCodeSpace n) :
    smallestTreeLeafNeighbor n hn (pruferDecode hn s) = s ⟨0, by omega⟩
```

Combines Step 2 + the fact that the smallest leaf has exactly one neighbor
in the tree, which is the `s 0` that was paired with it when the leaf was
first picked at iteration 1.

### Step 4: recursive equality

```lean
lemma pruferDecode_delete_smallest {n : ℕ} (hn : 3 ≤ n)  -- need n ≥ 3 to recurse
    (s : pruferCodeSpace n) :
    deleteSmallestLeafTreeSucc (n - 1) (by omega) (pruferDecode (by omega : 2 ≤ n) s) =
      pruferDecode (by omega : 2 ≤ n - 1) (shifted_code_via_finSuccAboveEquivCompl s)
```

This says: deleting the smallest leaf of the decoded tree is the same as
decoding the "shifted" code on the smaller vertex set.

The "shifted code" needs care — it's `s` with position 0 dropped and
the remaining positions re-indexed via `finSuccAboveEquivCompl`.

This is the recursive bridge. Likely 80-120 lines.

### Step 5: main theorem by induction

```lean
theorem pruferEncode_pruferDecode {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    pruferEncode hn (pruferDecode hn s) = s := by
  -- Pattern-match on n via Nat.le.dest or match
  match n, hn, s with
  | 0,       hn, _ => absurd hn (by decide)
  | 1,       hn, _ => absurd hn (by decide)
  | m + 2,   _,  s => by
    funext i
    induction m generalizing s with
    | zero => exact Fin.elim0 i
    | succ m ih =>
      by_cases h : i.val = 0
      · -- Position 0: use Step 3.
        sorry  -- ~20 lines, mostly unfold + apply Step 3
      · -- Position > 0: recursive case via Step 4 + IH.
        sorry  -- ~30 lines, finSuccAboveEquivCompl lifting
```

### Step 6: bijection and chapter31 upgrade

```lean
theorem pruferDecode_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (pruferDecode hn) :=
  Function.LeftInverse.injective (pruferEncode_pruferDecode hn)

theorem card_labeledTree_eq {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (LabeledTree n) = n ^ (n - 2) := by
  apply le_antisymm
  · exact cayley_upper_bound n hn
  · rw [← pruferCodeSpace_card n]
    exact Fintype.card_le_of_injective _ (pruferDecode_injective hn)

-- BOOK-FAITHFUL: use the EXPLICIT Prüfer bijection, not a non-constructive
-- existential. This is the genuine bijection from the book's argument.
noncomputable def pruferEquiv (n : ℕ) (hn : 2 ≤ n) :
    pruferCodeSpace n ≃ LabeledTree n :=
  Equiv.ofBijective (pruferDecode hn) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨pruferDecode_injective hn, ?_⟩
    rw [pruferCodeSpace_card, card_labeledTree_eq hn]

-- For chapter31 keep the LabeledTree direction (more natural reading).
noncomputable def pruferEquiv' (n : ℕ) (hn : 2 ≤ n) :
    LabeledTree n ≃ pruferCodeSpace n :=
  (pruferEquiv n hn).symm

theorem chapter31_full (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (LabeledTree n) = n ^ (n - 2) := card_labeledTree_eq hn

-- Replace existing chapter31 stub if desired:
-- theorem chapter31 (n : ℕ) (hn : 2 ≤ n) : Fintype.card (LabeledTree n) = n ^ (n - 2) :=
--   chapter31_full n hn
```

## Total scope estimate

- Step 1: ~10 lines (trivial filter equality)
- Step 2: ~80-100 lines (degree counting — the technical core)
- Step 3: ~30 lines (combines Step 2 with neighbor uniqueness)
- Step 4: ~80-120 lines (recursive equality, finSuccAboveEquivCompl gymnastics)
- Step 5: ~50 lines (induction wrap-up)
- Step 6: ~25 lines (cardinality squeeze + Equiv)

**Total: ~275-335 lines.**

## Risk: Step 2 degree counting

The degree-counting argument is straightforward mathematically but Lean-tedious
because it traces through `pruferDecodeAux` iteration-by-iteration. Consider
proving it by strong induction on `m` (iteration count), with invariant:
"after iteration m, for every v ∈ Fin n, degree of v in current edge set
= contributions from iterations [0, m) + (1 if v already picked) + 0 (final edge
not yet added)".

The cleanest framing might be a separate `EdgeContribution` predicate that
counts contributions, and prove the loop preserves the count equation.

If Step 2 takes more than 150 lines, file a follow-up question.

## Risk: Step 4 finSuccAboveEquivCompl lifting

The "shifted code" definition is the trickiest part — going from
`Fin (n - 2) → Fin n` to `Fin ((n - 1) - 2) → Fin (n - 1)` by dropping
position 0 AND re-mapping codomain via `finSuccAboveEquivCompl leaf`.

Define this as a separate function:
```lean
def shiftedCode {n : ℕ} (hn : 3 ≤ n) (s : pruferCodeSpace n) :
    pruferCodeSpace (n - 1) := fun i =>
  let leaf := min(Fin n \ image(s))
  let s_i_plus_1 : Fin n := s ⟨i.val + 1, by omega⟩
  -- s_i_plus_1 ∈ Fin n \ {leaf} (need to prove)
  -- via finSuccAboveEquivCompl, get the corresponding Fin (n-1) value
  sorry
```

Be especially careful with the `s_i_plus_1 ≠ leaf` proof requirement.

Go.
