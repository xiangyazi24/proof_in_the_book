I am following your blueprint. I have the skeleton perfectly type-checking with `sorry`s. 

I started working on the Support Lemma (`mem_pruferEncode_image_iff`) and it blew up to > 200 lines because manipulating `LabeledTree` degrees across recursive `deleteSmallestLeafTreeSucc` calls is extremely painful in Lean without the right API.

Could you provide the **EXACT, FULL LEAN 4 PROOF** for the Support Lemma?

```lean
theorem mem_pruferEncode_image_iff
    (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) (v : Fin n) :
    (∃ i, pruferEncode hn T i = v) ↔ T.1.degree v ≥ 2
```

If it's easy for you, please also provide the proof for Step 3 (`pruferDecode_smallestLeaf_neighbor`), since it relies directly on this support lemma.
