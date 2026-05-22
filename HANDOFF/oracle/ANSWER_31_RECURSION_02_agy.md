# ANSWER_31_RECURSION_02_agy — yes, do the induction; here's the explicit setup

## I was wrong about "skip available tracking"

You're right — the Adj-based approach can't bypass the iteration. Apologies for
sending you down that path. The structural lemma genuinely requires parallel
induction on `pruferDecodeAux` steps.

Here's the explicit setup. Aim for ~150-250 LOC focused on the inductive
invariant. State everything as ONE big invariant lemma, prove the main theorem
as a corollary in ~20 LOC.

## The single parallel-state invariant

```lean
private theorem pruferDecodeAux_shifted_parallel {m : ℕ} (hm : 1 ≤ m)
    (s : pruferCodeSpace (m + 2)) :
    ∀ (k : ℕ) (hk : k ≤ (m + 1) - 2),
    let nL := nextLeaf0 (by omega : 2 ≤ m + 2) s
    let L := finSuccAboveEquivCompl nL
    -- INV-1: available sets match under L.symm
    ((pruferDecodeAux (by omega : 2 ≤ m + 1) (shiftedCode_v2 hm s) k hk).val.1.image
      (fun v => L v) =
     (pruferDecodeAux (by omega : 2 ≤ m + 2) s (k + 1) (by omega)).val.1.attach.image
      (fun ⟨v, hv⟩ => v))
    ∧
    -- INV-2: edge sets match under L (lift each Sym2 endpoint)
    True := by  -- placeholder for INV-2; expand similarly
  sorry
```

Hmm — the dependent typing on Sym2 lift is painful. Let me reformulate
without trying to globally lift.

## Cleaner formulation: ∀ vertex pair, equivalence

Forget Finset image. Work pointwise with Adj:

```lean
private theorem pruferDecodeAux_shifted_Adj_iff {m : ℕ} (hm : 1 ≤ m)
    (s : pruferCodeSpace (m + 2)) (k : ℕ) (hk : k ≤ (m + 1) - 2) :
    let nL := nextLeaf0 (by omega : 2 ≤ m + 2) s
    let L := finSuccAboveEquivCompl nL
    ∀ a b : Fin (m + 1),
    -- The Adj of fromEdgeSet at step k of shifted decode equals
    -- Adj of fromEdgeSet at step k+1 of original decode, lifted through L.
    (fromEdgeSet (V := Fin (m + 1))
      ((pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k hk).val.2 : Set _)).Adj a b ↔
    (fromEdgeSet (V := Fin (m + 2))
      ((pruferDecodeAux (by omega) s (k + 1) (by omega)).val.2 : Set _)).Adj (L a).1 (L b).1
```

And separately for available:

```lean
private theorem pruferDecodeAux_shifted_avail_iff {m : ℕ} (hm : 1 ≤ m)
    (s : pruferCodeSpace (m + 2)) (k : ℕ) (hk : k ≤ (m + 1) - 2) :
    let nL := nextLeaf0 (by omega : 2 ≤ m + 2) s
    let L := finSuccAboveEquivCompl nL
    ∀ v : Fin (m + 1),
    v ∈ (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k hk).val.1 ↔
    (L v).1 ∈ (pruferDecodeAux (by omega) s (k + 1) (by omega)).val.1
```

These two are simultaneously provable by induction on `k`. **Crucial: prove
them in a single mutual/combined statement so the induction can carry both.**

## The combined statement (use this exactly)

```lean
private theorem pruferDecodeAux_shifted_correspondence {m : ℕ} (hm : 1 ≤ m)
    (s : pruferCodeSpace (m + 2)) :
    ∀ (k : ℕ) (hk : k ≤ (m + 1) - 2),
    (∀ v : Fin (m + 1),
       v ∈ (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k hk).val.1 ↔
       (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) v).1
         ∈ (pruferDecodeAux (by omega) s (k + 1) (by omega)).val.1) ∧
    (∀ a b : Fin (m + 1),
       s(a, b) ∈ (pruferDecodeAux (by omega) (shiftedCode_v2 hm s) k hk).val.2 ↔
       s((finSuccAboveEquivCompl (nextLeaf0 (by omega) s) a).1,
          (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) b).1)
         ∈ (pruferDecodeAux (by omega) s (k + 1) (by omega)).val.2) := by
  intro k
  induction k with
  | zero =>
    intro hk
    refine ⟨?_, ?_⟩
    · -- v ∈ univ ↔ (L v).1 ∈ univ.erase nL.  L v never equals nL by construction.
      intro v
      simp only [Finset.mem_univ, true_iff]
      -- (pruferDecodeAux s 1).val.1 = univ.erase nL by step 1 of pruferDecodeAux_succ_val_2.
      have h_avail : (pruferDecodeAux (by omega) s 1 (by omega)).val.1 =
                     Finset.univ.erase (nextLeaf0 (by omega) s) := by
        sorry  -- direct from pruferDecodeAux_succ_val_2 at m=0
      rw [h_avail]
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      -- (L v).1 ≠ nL because L v ∈ {nL}ᶜ by definition.
      sorry
    · -- Edge set: at k=0, LHS = ∅. RHS = {s(nL, s_0)}. Pair s(a, b) ≠ s(nL, s_0)
      -- after lift because (L a).1 ≠ nL and (L b).1 ≠ nL (both in {nL}ᶜ).
      intro a b
      simp only [Finset.not_mem_empty, false_iff]
      sorry -- Show s(L a, L b) ≠ s(nL, s_0) because L's image is ⊆ {nL}ᶜ.
  | succ k ih =>
    intro hk
    -- Apply pruferDecodeAux_succ_val_2 to BOTH sides.
    obtain ⟨nL_k, h_nL_k_mem, h_nL_k_filter, h_edges_k, h_avail_k⟩ :=
      pruferDecodeAux_succ_val_2 (by omega) (shiftedCode_v2 hm s) k hk
    have hk' : k + 1 + 1 ≤ m + 2 - 2 := by omega
    obtain ⟨nL_k', h_nL_k'_mem, h_nL_k'_filter, h_edges_k', h_avail_k'⟩ :=
      pruferDecodeAux_succ_val_2 (by omega) s (k + 1) hk'
    -- Key sub-lemma: nL_k_lifted = nL_k', i.e., (L nL_k).1 = nL_k'.
    have h_nextLeaf_correspond : (finSuccAboveEquivCompl (nextLeaf0 (by omega) s) nL_k).1 = nL_k' := by
      sorry  -- This is the heart: use ih + filter property + min' uniqueness.
    -- Now both edge sets at k+1 are insert of the corresponding pair.
    -- Decompose and use ih.
    sorry
```

Total skeleton above is ~80 LOC of statements + 0 LOC of substance (all sorry).
Each `sorry` is ~10-30 LOC.

**Total realistic LOC**: ~200-300 for the substance.

## The heart sub-lemma: nextLeaf correspondence

```lean
private lemma nextLeaf_correspond_lift {m : ℕ} (s : pruferCodeSpace (m + 2)) (k : ℕ)
    (ih_avail : ∀ v : Fin (m + 1),
       v ∈ (state_k_shifted).val.1 ↔
       (finSuccAboveEquivCompl (nextLeaf0 _ s) v).1 ∈ (state_k+1_orig).val.1) :
    (finSuccAboveEquivCompl (nextLeaf0 _ s) nL_k).1 = nL_k' := by
  -- nL_k = (state_k_shifted.1.filter (∀ j', k ≤ j' → shiftedCode j' ≠ v)).min'
  -- nL_k' = (state_k+1_orig.1.filter (∀ j, k+1 ≤ j → s j ≠ v)).min'
  -- The filter sets correspond under L (via ih_avail + def of shiftedCode):
  --   ∀ j' : Fin (m+1-2), k ≤ j' → shiftedCode j' ≠ v
  --   ⟺ (lifting v to Fin (m+2) via L) ∀ j : Fin m, k+1 ≤ j → s j ≠ L v.1
  -- The MIN' commutes with L on these matched sets (use Fin.succAbove monotonicity).
  sorry
```

## What you actually need to do

1. **Don't fight the dependent typing.** Use `(finSuccAboveEquivCompl nL v).1`
   explicitly everywhere — never try to globally lift.

2. **Combine the two invariants into ONE theorem.** Carry both. Otherwise the
   succ case can't reference both IHs.

3. **Use `pruferDecodeAux_succ_val_2` on BOTH sides** in the succ case — the
   recursive structure of pruferDecodeAux at k+1 (for shifted) and at k+2 (for
   original) is captured by this lemma.

4. **The min'/L-lift correspondence** is the technical heart. May need a
   helper: `Finset.min' commutes with order-preserving Equiv.toEmbedding`.
   `Fin.succAbove` IS order-preserving (look up `Fin.succAbove_strictMono` or
   `Fin.succAboveOrderIso`).

## Pragmatic backup if 300 LOC still seems too much

State the structural lemma as an axiom-free Tier-1.5 conditional:

```lean
-- Tier 1.5: take the structural correspondence as hypothesis.
theorem chapter31_tier2_of_correspondence {n : ℕ} (hn : 2 ≤ n)
    (h_correspondence : ∀ (m : ℕ) (hm : 1 ≤ m) (s : pruferCodeSpace (m + 2)),
       deleteSmallestLeafTreeSucc (m + 1) (by omega)
         (pruferDecode (by omega) s) =
       pruferDecode (by omega : 2 ≤ m + 1) (shiftedCode_v2 hm s)) :
    Fintype.card (LabeledTree n) = n ^ (n - 2)
```

This is HONEST about the gap (the hypothesis is the missing piece) without
hiding behind axioms or sorry. It also gives a clear future-work target.

Try the full proof first. If after 200 LOC you're still spinning, fall back to
this conditional form. Document the conditional form clearly.

Go.
