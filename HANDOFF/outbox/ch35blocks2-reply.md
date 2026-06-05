# ch35blocks2 reply

Worked in `ProofsInTheBook/SimpleGraphBlocks.lean`.

Verified:

```text
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/SimpleGraphBlocks.lean
```

The command exits successfully.  No `sorry` or axioms were added.

Added verified infrastructure toward the finite connected graph enumeration theorem:

- `isBlock_univ_of_twoConnected`
- `twoConnected_of_connected_of_no_cut`
- `RootedBlockEnumeration.StartsAt`
- `exists_rootedBlockEnumeration_one`
- `exists_rootedBlockEnumeration_of_connected_of_no_cut`
- cut-deletion side definitions:
  - `deleteComponentSet`
  - `deleteComponentSide`
  - `deleteComponentOtherSide`
- deletion/separation facts:
  - every walk between vertices disconnected in `G - x` visits `x`
  - every component of `G - x` in a connected graph has a neighbor of `x`
  - `deleteComponentSide` and `deleteComponentOtherSide` are connected
  - the two sides cover `univ`, intersect in `{x}`, and have no non-`x` cross edge
  - a global `BlockCore` meeting one side away from `x` stays inside that side
- induced/global block transfer:
  - `subtypeImage`
  - `blockCore_induce_of_subset`
  - `blockCore_image_of_induce`
  - local blocks in `deleteComponentSide` map to global blocks
  - local blocks in `deleteComponentOtherSide` map to global blocks, assuming another deletion component exists

Remaining:

- Finish the concatenation constructor for two recursive enumerations on
  `G.induce (deleteComponentSide G x C)` and
  `G.induce (deleteComponentOtherSide G x C)`.
- Then add the strong-induction theorem:

```lean
theorem exists_rootedBlockEnumeration_of_connected
    {G : SimpleGraph V} [Finite V] (hG : G.Connected) :
    ∃ E : RootedBlockEnumeration G := ...
```

Suggested next implementation detail:

- Avoid defining the concatenation constructor as a `theorem` returning `RootedBlockEnumeration G`; use `noncomputable def` or build it inside the final existential proof.  Lean will not eliminate `StartsAt`'s existential witness from `Prop` into a `Type` result, so pass the second enumeration's start witness explicitly:

```lean
(t0 : Fin Et.k) (ht0 : t0.1 = 0)
(ht0mem : (⟨x, deleteComponentSet_notMem_self C⟩ :
  deleteComponentOtherSide G x C) ∈ Et.blocks t0)
```

- In the `Fin.addCases` concatenation, avoid relying on `simp` to synthesize subtype-image witnesses.  Manually build witnesses like:

```lean
⟨⟨v, hvSide⟩, hi, rfl⟩
```

and first convert `v ∈ blocks (Fin.castAdd _ i)` to
`v ∈ subtypeImage (Es.blocks i)` before destructing it.
