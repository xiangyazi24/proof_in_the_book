# ch35blocks reply

Created `ProofsInTheBook/SimpleGraphBlocks.lean`.

What is in the file:

- Mathlib-only import; it does not import planar files or `ProofsInTheBook.ListColoring`.
- Definitions on plain `SimpleGraph`:
  - `VertexDeletedPreconnected`
  - `IsCutVertex`
  - `TwoConnected`
  - `BlockCore`
  - `IsBlock`
  - `BlockCutIncidence`
  - `blockCutGraph`
  - `RootedBlockEnumeration`
  - `IsProperColoring`
  - `RootedColorableOn`
- Proved block basics:
  - singleton and adjacent-pair `BlockCore`;
  - every `BlockCore` set in a finite vertex type is contained in a maximal block;
  - every vertex is covered by some block;
  - two blocks with two distinct common vertices are equal;
  - distinct blocks have subsingleton intersection / `encard ≤ 1`.
- Proved rooted coloring glue:
  - `exists_properColoring_of_rootedBlockEnumeration`.
  - This is abstract over the color type and uses the rooted-enumeration form rather than an explicit tree API.

Verification:

```text
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/SimpleGraphBlocks.lean
```

This command exits successfully.

Important gap:

- The file does not yet prove the full universal block-cut tree/rooted-enumeration existence theorem for every finite connected graph.
- It provides the `RootedBlockEnumeration` certificate and the coloring theorem from that certificate, plus the maximal-block cover and pairwise-intersection facts.
