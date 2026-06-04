# ANSWER_30_02_agy — 4 lemma proofs

## Caveat upfront

These proofs assume **paths have no vertex revisit** (the natural property for
N/E lattice paths). If you don't have this as a structural property of your
`LatticePath` type yet, add it now:

```lean
structure LatticePath where
  vertices : List (ℤ × ℤ)
  nonempty : vertices ≠ []
  nodup : vertices.Nodup           -- ← critical for involution proofs
  consecutive : ...
```

For N/E lattice paths, `nodup` follows from monotonicity. State it as
`theorem LatticePath.nodup_of_consecutive` after the fact, or just bake it
into the structure.

Without `nodup`, `idxOf` semantics get hairy (first occurrence vs others)
and `swapTailAt_swapTailAt` fails. With `nodup`, all 4 lemmas become tractable.

---

## Lemma 1: `Path.swapTailAt_swapTailAt`

```lean
lemma Path.swapTailAt_swapTailAt {pi pj : List V} {v : V}
    (hi : v ∈ pi) (hj : v ∈ pj)
    (hpi_nodup : pi.Nodup) (hpj_nodup : pj.Nodup) :
    let (pi', pj') := Path.swapTailAt pi pj v
    Path.swapTailAt pi' pj' v = (pi, pj) := by
  -- Key observation: pi' = pi_head ++ pj_tail, where pi_head ends with v as
  -- its LAST element (idx + 1 elements ending at v), and pj_tail starts AFTER
  -- v in pj (so v ∉ pj_tail by nodup).
  -- Therefore v's first occurrence in pi' is at the same position as in pi_head,
  -- which equals idxOf v in pi.
  unfold Path.swapTailAt Path.splitAtFirst
  -- Critical Mathlib facts:
  -- `List.idxOf_append_of_mem_left : v ∈ a → (a ++ b).idxOf v = a.idxOf v`
  -- `List.take_append_of_le_length : n ≤ a.length → (a ++ b).take n = a.take n`
  -- `List.drop_left' : a.length = n → (a ++ b).drop n = b`
  -- The take/drop of pi' = pi_head ++ pj_tail at position (idx + 1) gives
  -- (pi_head, pj_tail) — both untouched.
  -- Then re-applying swapTailAt swaps tails again: (pi_head ++ pi_tail, pj_head ++ pj_tail)
  -- = (pi, pj) by `List.take_append_drop`.
  sorry  -- ~25 LOC of List manipulation; the structure is mechanical
```

Replace `sorry` with the explicit calc. Critical Mathlib lemmas to chain
(grep them):
- `List.idxOf_append_of_mem_left` (or equivalent)
- `List.take_append_of_le_length`
- `List.drop_append`
- `List.take_append_drop : ∀ (l : List α) (n : ℕ), l.take n ++ l.drop n = l`

## Lemma 2: `PathFamily.tailSwap_firstBadPair`

**This is the hardest** (~50 LOC). The claim:

```lean
lemma PathFamily.tailSwap_firstBadPair [LinearOrder V] [DecidableEq V]
    {F : PathFamily Source Sink V n} (h : F.firstBadPair.isSome) :
    F.tailSwap.firstBadPair = F.firstBadPair
```

### Why it's true

Two things to verify:
(a) The set of "intersecting pairs (i, j)" is the same for F and F.tailSwap.
(b) For the specific (i, j) returned by firstBadPair, the first intersection
    vertex `v` is the same.

For (a): tailSwap only affects paths at indices i₀, j₀ (the firstBadPair).
For any other pair (k, l), paths are unchanged → intersection unchanged.
For pairs (k, i₀) or (k, j₀) with k ≠ i₀, j₀: path_k unchanged; path_{i₀} now
has new tail (which is path_{j₀}'s old tail). The intersection set
`path_k ∩ path_{i₀}'` = `path_k ∩ (pi_head ∪ pj_tail)`. The OLD intersection
was `path_k ∩ (pi_head ∪ pi_tail)`. These can differ! So the set of
intersecting pairs CAN change under swap.

**Therefore the lemma as I stated is WRONG in general.** What's actually
preserved is weaker: there exists a different "canonical" choice that's
invariant. Let me give the correct version:

```lean
-- The pair returned by firstBadPair is the SAME pair for F and F.tailSwap,
-- AND the intersection vertex v is the same.
-- This needs the lexicographic-minimum property: even though OTHER pairs
-- might "become intersecting" after swap, the (i₀, j₀) pair is still
-- intersecting AND there's no smaller pair that became intersecting.
-- 
-- Proof sketch: the swap only adds NEW intersections involving path_{i₀}
-- or path_{j₀} with some third path_k. These pairs (k, i₀), (k, j₀) are
-- all LARGER than (i₀, j₀) in lex order on Fin n × Fin n if k > j₀,
-- or potentially smaller if k < i₀. So in general not invariant.
```

**Practical fix**: pick a different INVOLUTION FRAME. Instead of "first bad pair",
use "**fixed** bad pair after swap". Specifically:

```lean
-- The involution is parameterized by the (i, j, v) data computed FROM the
-- original family, NOT recomputed after swap. The swap is its own inverse
-- because tail-swap at (i, j, v) applied twice cancels.
def PathFamily.tailSwapAt (F : PathFamily ...) (i j : Fin n) (v : V) 
    (hi : v ∈ F.paths i) (hj : v ∈ F.paths j) : PathFamily ... := ...

-- Then the involution-pairing happens via partition: each "intersecting"
-- family F has a canonical "(i, j, v)" computed FROM F, which gives the
-- pairing F ↔ F.tailSwapAt (i, j, v). The KEY is that F.tailSwapAt(i,j,v)
-- has the SAME (i, j, v) as its canonical data — because tail-swap doesn't
-- change which vertices appear in path_i ∪ path_j (just rearranges tails).
```

This is the subtle technical point. The CANONICAL (i, j, v) is preserved
under tail-swap because:
- Vertex sets: `(F.tailSwap).paths_i ∪ (F.tailSwap).paths_j = F.paths_i ∪ F.paths_j` (just rearranged).
- Hence `(F.tailSwap).paths_i ∩ (F.tailSwap).paths_j = F.paths_i ∩ F.paths_j`.
- Same intersection set → same minimum vertex `v`.
- Now firstBadPair preference: we need (i, j) to STILL be the firstBadPair
  of F.tailSwap. **This may fail for other pairs becoming intersecting**.
  
**Correct framing**: Use `firstBadPair` only as a SELECTOR for the canonical
involution data. Then prove `tailSwap (firstBadPair F) F` has the SAME
canonical data when one inspects.

Honestly, this is fiddly. Recommend an alternative architecture:

```lean
-- Don't make tailSwap depend on F's firstBadPair. Make it parameterized:
def PathFamily.tailSwapAt (F : PathFamily ...) 
    (i j : Fin n) (hij : i < j) 
    (v : V) (hi : v ∈ F.paths i) (hj : v ∈ F.paths j) : PathFamily ...

-- Then define the OVERALL involution as: if F.firstBadPair = (i, j) and 
-- firstIntersection = v, swap. Otherwise identity.
def PathFamily.involve (F : PathFamily ...) : PathFamily ... :=
  match h : F.firstBadPair with
  | none => F
  | some ⟨i, j, hij⟩ =>
    F.tailSwapAt i j hij (PathFamily.firstIntersection F i j) ...

-- Now `involve_involve F = F` requires:
-- (a) If F good: involve F = F (trivial).
-- (b) If F bad: involve F has SAME firstBadPair as F, with SAME first intersection.
-- (b) requires the "preservation of (i, j, v)" claim.
```

For (b), the argument is:
- swap doesn't change `path_i ∪ path_j` (as sets) → same intersection vertex `v`
- swap doesn't introduce intersections involving paths < i or with each other
  (those paths unchanged) → no smaller pair than (i, j) becomes intersecting
- swap might create new intersections involving path_i or path_j with k > j,
  BUT firstBadPair returns the LEX MIN — and (i, j) is lex min over all
  intersecting pairs. Even if (i, j) is still intersecting AND no pair 
  smaller becomes intersecting, the firstBadPair stays (i, j).

To verify "no smaller pair becomes intersecting":
- A pair (k, l) becomes intersecting only if path_k ∩ path_l increases.
- path_k unchanged for k ∉ {i, j}; path_l unchanged for l ∉ {i, j}.
- So new intersections only involve i or j.
- Pair (k, i) with k < i is < (i, j) in lex iff k < i. But k must be < i AND
  intersect path_i (new). path_k was already there; path_i's vertices are
  now {old path_i vertices} swap with {old path_j vertices} on the tail —
  but path_k didn't intersect path_i before (by minimality), and the new
  tail of path_i is the OLD tail of path_j... did path_k intersect path_j
  before? If yes, that pair (k, j) was bad, but (i, j) was minimum — so k > i.
  
  But we're considering k < i. So path_k didn't intersect path_j either.
  Hence path_k doesn't intersect (path_j tail part of new path_i either.
  Hence path_k ∩ (new path_i) = path_k ∩ (pi_head) ⊆ path_k ∩ (old path_i) = ∅.

  So no new intersection. ✓

OK so the lemma IS true with `nodup` and the lex-min minimum property.
Proof is ~50-80 LOC of careful Finset/List membership reasoning.

## Lemma 3: `PathFamily.tailSwap_tailSwap`

Follows from Lemma 2 + Lemma 1:
- F.tailSwap.firstBadPair = F.firstBadPair (Lemma 2) → same (i, j, v)
- Apply tailSwap with same (i, j, v) on F.tailSwap = swap back to F (Lemma 1)
- Need careful threading through the Option / matching.

```lean
lemma PathFamily.tailSwap_tailSwap [LinearOrder V] [DecidableEq V]
    (F : PathFamily ...) : F.tailSwap.tailSwap = F := by
  unfold PathFamily.tailSwap
  rcases h : F.firstBadPair with _ | ⟨i, j⟩
  · simp [h]
  · have h' := tailSwap_firstBadPair (h ▸ Option.isSome_some)
    -- h' : F.tailSwap.firstBadPair = some ⟨i, j⟩
    -- apply Path.swapTailAt_swapTailAt at the SAME (i, j) using nodup of paths
    sorry  -- ~20 LOC
```

## Lemma 4: `PathFamily.tailSwap_sign`

```lean
lemma PathFamily.tailSwap_sign [LinearOrder V] [DecidableEq V]
    {F : PathFamily ...} (h : F.firstBadPair.isSome) :
    F.tailSwap.perm.sign = -F.perm.sign := by
  unfold PathFamily.tailSwap
  rcases h : F.firstBadPair with _ | ⟨i, j⟩
  · simp at h  -- contradiction
  · -- F.tailSwap.perm = F.perm * Equiv.swap i j (or swap of F.perm values)
    -- → sign multiplies by Equiv.swap.sign = -1 (since i ≠ j by hij)
    simp [PathFamily.tailSwap, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]
    -- need i ≠ j which is part of firstBadPair's invariant
    sorry  -- ~10 LOC
```

Mathlib: `Equiv.Perm.sign_swap (h : i ≠ j) : (Equiv.swap i j).sign = -1`.
And `Equiv.Perm.sign_mul : (a * b).sign = a.sign * b.sign`.

## Summary

- Lemma 1: ~25 LOC (List manipulation)
- Lemma 2: ~50-80 LOC (the technical heart, intersection-preservation)
- Lemma 3: ~20 LOC (combines Lemmas 1+2)
- Lemma 4: ~10 LOC (algebra of signs)

**Total ~120 LOC.**

If Lemma 2's "no smaller pair becomes intersecting" sub-argument blows past
60 LOC, file Q03 — I'll give a more detailed proof of THAT specific
sub-claim. Don't grind blind.

**Pitfall**: be careful with the `nodup` assumption — make sure it's threaded
through every helper. If you find yourself wanting `nodup_of_swapTailAt`,
that's a separate ~30 LOC lemma you'll need.

Go.
