# opus-blocks reply

Worked in `ProofsInTheBook/SimpleGraphBlocks.lean`. The remaining existence
theorem is now proved with **0 sorry / 0 admit / 0 axiom**.

## Verification

```
rsync -az .../ProofsInTheBook/SimpleGraphBlocks.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=/data/home/xhuan5/.elan/bin:$PATH && lake env lean ProofsInTheBook/SimpleGraphBlocks.lean'
```

Exits cleanly (no output, exit 0). Full module build: `8419/8419 jobs`.

`#print axioms`:
- `exists_rootedBlockEnumeration_of_connected` → `[propext, Classical.choice, Quot.sound]`
- `concat_rootedBlockEnumeration` → `[propext, Classical.choice, Quot.sound]`

No `sorryAx`, no `ofReduceBool`/`trustCompiler`.

## Final theorem (the requested one)

```lean
theorem exists_rootedBlockEnumeration_of_connected {G : SimpleGraph V} [Finite V]
    (hG : G.Connected) : Nonempty (RootedBlockEnumeration G)
```

Only inputs are the primitive `[Finite V]` and `hG : G.Connected`; nothing about
blocks/cuts is smuggled in as a hypothesis. `RootedBlockEnumeration` is a `Type`
structure, so the conclusion is stated as `Nonempty`.

## New API added (all proved)

- `mem_subtypeImage_iff` — membership unfolding for `subtypeImage`.
- `concat_rootedBlockEnumeration` — the concatenation constructor. Given two
  induced sides `S, T` with `S ∪ T = univ`, `S ∩ T = {x}`, no edge crossing
  `(S\{x}) × (T\{x})`, lift functions `IsBlock (G.induce S/T) B → IsBlock G
  (subtypeImage B)`, sub-enumerations `Es` on `S` and `Et` on `T` with
  `Et.StartsAt ⟨x,_⟩`, and `Es.StartsAt ⟨r,_⟩` for `r ∈ S`, it produces
  `∃ E : RootedBlockEnumeration G, E.StartsAt r`. Layout: `S`-blocks first
  (images), then `T`-blocks; the first `T`-block becomes the unique non-root
  block meeting the earlier union exactly at `x`.
- `exists_rootedBlockEnumeration_startsAt_aux` — strong-induction core on
  `Nat.card`: `∀ n, ∀ {W} [Finite W] (H), Nat.card W = n → H.Connected →
  ∀ r, ∃ E, E.StartsAt r`.
- `exists_rootedBlockEnumeration_of_connected` — headline theorem.

## Proof route (as designed in the spec / prior notes)

Strong induction on `Nat.card V` (`Nat.strong_induction_on`), `V` varying.

- **No cut vertex** → `exists_rootedBlockEnumeration_of_connected_of_no_cut`
  (whole graph is one block).
- **Cut vertex `x`** → `¬Preconnected (G - x)` gives two non-reachable
  vertices `a, b`; take `C = comp a`, `D = comp b ≠ C` (supplies `hother`).
  Sides `S₁ = deleteComponentSide`, `S₂ = deleteComponentOtherSide` are
  connected (existing lemmas), cover `univ`, meet in `{x}`, no cross edge, and
  each is **strictly smaller** (`Finite.card_subtype_lt`, witnessed by a
  `D`-vertex `∉ S₁` and a `C`-vertex `∉ S₂`). Recurse on both, then
  concatenate with `concat_rootedBlockEnumeration`, putting the side
  containing `r` first (rooted `r`) and the other side second (rooted `x`).
  Both orderings are handled (`r ∈ S₁` / `r ∈ S₂`) via `Set.union_comm` /
  `Set.inter_comm` and an edge-symmetry wrapper; the `otherSide` lift uses
  `hother` in both branches.

## Implementation notes (per prior worker's hints — followed)

- `Et.StartsAt` witness passed **explicitly** (`t0, ht0val, ht0mem`); no
  Prop→Type elimination.
- In the `Fin.addCases` concatenation, all `blocks`/`roots` reductions go
  through four named `have` equalities (`blocks_castAdd`, `blocks_natAdd`,
  `roots_castAdd`, `roots_natAdd` = `Fin.addCases_left/right`) instead of
  fragile `show … ; rw [Fin.addCases_left]`. Subtype-image witnesses are built
  manually (`⟨⟨v, h⟩, hb, rfl⟩`) and membership is destructed via
  `mem_subtypeImage_iff` before use.
- The crux `meet_prev` iff: a `T`-block vertex `v` that also sits in any
  `S`-block must equal `x` (only shared vertex); and if `v = x ∈ Et.blocks j`
  with `j ≠ 0` then `Et`'s own `meet_prev` (with the start block 0 as an
  earlier block) forces `Et.roots j = x`, so the two characterizations agree.

## Faithfulness verdict

FAITHFUL. The statement is the genuine rooted-enumeration (block-cut tree)
existence result for finite connected graphs; the only hypotheses are the
graph being finite and connected. All geometric/separation facts are proved,
not assumed.
