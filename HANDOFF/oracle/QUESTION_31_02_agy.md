My `Chapter31.lean` file ALREADY contains a fully verified definition of `pruferDecodeAux` and `pruferDecode` (it has 0 sorrys up to the point of Cayley's theorem). Your previous answer gave a completely new definition for `pruferDecodeAux` which I cannot use.

My definitions are:
```lean
def pruferDecodeAux {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    (m : ℕ) → (hm : m ≤ n - 2) →
    { state : Finset (Fin n) × Finset (Sym2 (Fin n)) // ... }
```
where it loops `n-2` times, picking `nextLeaf := (state.1.filter (fun v => ∀ j, m ≤ j.val → s j ≠ v)).min' h_nonempty`, adding edge `s(nextLeaf, s m)`, and removing `nextLeaf` from `state.1`. Then `pruferFinalState` is `pruferDecodeAux hn s (n - 2) (by rfl)`.

I need the EXACT FULL LEAN 4 PROOFS for the following 3 things, relative to MY existing `pruferDecodeAux` and `pruferDecode` (not a new definition):

1. **Step 2:**
```lean
lemma pruferDecode_leaves_eq {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    {v : Fin n | (pruferDecode hn s).1.degree v = 1} =
      ↑(Finset.univ : Finset (Fin n)) \ ↑(Finset.image s Finset.univ : Finset (Fin n))
```

2. **Step 4 Definition:** (Note: this is how it maps back using `finSuccAboveEquivCompl`)
```lean
noncomputable def shiftedCode {n : ℕ} (hn : 3 ≤ n) (s : pruferCodeSpace n) :
    pruferCodeSpace (n - 1)
```

3. **Step 4 Lemma:**
```lean
lemma pruferDecode_delete_smallest {n : ℕ} (hn : 3 ≤ n) (s : pruferCodeSpace n) :
    deleteSmallestLeafTreeSucc (n - 1) (by omega)
      (cast (by congr 1; omega) (pruferDecode (by omega : 2 ≤ n) s)) =
    pruferDecode (by omega : 2 ≤ n - 1) (shiftedCode hn s)
```

Please give me ONLY the precise definitions and proofs for these 3 items, assuming my `pruferDecodeAux` definition. If the degree counting lemma (`pruferDecode_leaves_eq`) needs a helper invariant lemma over `m`, please provide it.
