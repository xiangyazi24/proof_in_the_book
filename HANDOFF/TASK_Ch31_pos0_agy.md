# TASK Ch31: position 0 of round-trip

Step 0 is complete. Now prove the immediate consequence: at position 0,
encode∘decode = identity.

## Task

Append to `scratch_ch31_inverse.lean`:

```lean
theorem pruferEncode_pruferDecode_zero (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (hge : 3 ≤ n) :
    (pruferEncode hn (pruferDecode hn s)) ⟨0, by omega⟩ = s ⟨0, by omega⟩
```

## Proof

`pruferEncode hn` for `n = (n-2) + 2` is `pruferEncodeAux (n-2)`. So
`pruferEncode hn T ⟨0, _⟩ = pruferEncodeAux (n-2) T ⟨0, _⟩`.

`pruferEncodeAux` at `m+1 = (n-2)` (i.e., we need n-2 = m+1, so m = n-3),
position 0:
```
pruferEncodeAux (m+1) T ⟨0, _⟩ = smallestTreeLeafNeighbor (m+3) (by omega) T
```

For `T := pruferDecode hn s`, this equals `s ⟨0, _⟩` by
`smallestTreeLeafNeighbor_pruferDecode`.

The match-with-omega: `n = (n-3) + 3 = (n-2) + 2`, so `pruferEncodeAux` is
called with m = n-3, and the `m+3 = n` in the conclusion matches.

## Suggested ~15 LOC

```lean
theorem pruferEncode_pruferDecode_zero (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (hge : 3 ≤ n) :
    (pruferEncode hn (pruferDecode hn s)) ⟨0, by omega⟩ = s ⟨0, by omega⟩ := by
  -- Set up the n = (n-2)+2 pattern.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hge' : 3 ≤ m + 2 := hge
  -- Now pruferEncode (hn : 2 ≤ m+2) = pruferEncodeAux m.
  show (pruferEncodeAux m (pruferDecode hn s)) ⟨0, by omega⟩ = s ⟨0, by omega⟩
  -- m = (m-1) + 1 since m ≥ 1.
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  -- pruferEncodeAux (m'+1) T ⟨0, _⟩ = smallestTreeLeafNeighbor _ _ T (from line 1432-1435).
  show smallestTreeLeafNeighbor (m' + 3) (by omega) (pruferDecode hn s) = s ⟨0, by omega⟩
  exact smallestTreeLeafNeighbor_pruferDecode (m' + 3) hn s (by omega)
```

The `show ...` lines should be definitionally true because of the pattern-match
structure of pruferEncodeAux at m+1, position 0 (the `if h : i.val = 0` branch).

If the `show` fails on definitional unfolding, use `simp only [pruferEncodeAux]`
to force it.

## Build remotely as usual

Once done, this gives us position 0 of the round-trip. The remaining positions
require structural recursion (the hard delete-leaf-tree equals shift-decode lemma)
— that's the next big task.

Go. Should be a quick one.
