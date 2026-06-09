# FFCT15 reply — GREEN

**Status: COMPLETE.** `ProofsInTheBook/ZinanFFCT15.lean` created and typechecks clean on uisai2
(`lake env lean`, no errors/warnings, no `sorry`/`axiom`/`admit`/`native_decide`).

## #print axioms (verbatim)

```
'ProofsInTheBook.ZinanFFCT15.backward_case' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProofsInTheBook.ZinanFFCT15.planarWeakNoflatStrictEdgeCore_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both are exactly `[propext, Classical.choice, Quot.sound]` — clean-3.

## What was proven

1. `theorem backward_case` — strict support of edge `(i, i+1)` at every vertex `j ≤ i−1`
   (`hji : j + 1 ≤ i`), the mirror of `ZinanFFCT14.forward_case` with reversed normal `-h` and
   apex `f (i+1)`, chain `σs t = f ⟨i − min t i, _⟩ − f ⟨i+1, _⟩`, `N = i − j`.
2. `theorem planarWeakNoflatStrictEdgeCore_holds : PlanarWeakNoflatStrictEdgeCore` — the headline,
   gluing `forward_case` (j ≥ i+2) and `backward_case` (j ≤ i−1) via `Nat.lt_or_ge j i` + `omega`
   on `hji : j ≠ i`, `hji1 : j ≠ i+1`. The carve-outs `hhead`/`htail` introed and ignored.

## Design followed

The backward case follows the spec §"Backward case" and the §htrans/sign-chain design exactly:
- `htrans : det3 (-h) (f u − f ⟨i+1⟩) (f w − f ⟨i+1⟩) = det3 (f ⟨i+1⟩) (f u) (f w) * ‖h‖² * (−1)`
  via `det3_neg_left` + `det3_plane_eq` (apex `f ⟨i+1⟩`) + `ring`.
- `hsupp`: one `det3_swap12` → `hweak i (i−t)`.
- `hturn`: `det3_cyclic` then `det3_swap12`, index identity `i−t−1+1 = i−t` via `congr 1; Fin.ext`
  → `hweak (i−t−1) (i+1)`.
- first joint: `det3_cyclic` then `det3_swap12` → `hnoflat i hipos hi1`.
- `hcons`/`hnotanti`: backward witnesses killed by `ZinanFFCT14.no_beyond_vertex` (its `hcol` shape
  `f ⟨w⟩ − f ⟨i+1⟩ = −(t • (f ⟨i⟩ − f ⟨i+1⟩))` matches the antiparallel witness verbatim, vertices
  `w = i−t`, `i−(t+1)`, `i−N=j`); the degenerate `σs 0 = b'` witness killed by `(1+s) • b' = 0`.
- conclusion: same sign chain as `hsupp` (a final `det3_swap12`) → `nlinarith` with `‖h‖² > 0`.

## Deviations from the design (minor, all forced by Lean reduction quirks)

- The index equality `f ⟨i − 0, _⟩ = f ⟨i, _⟩` is **not** definitional (`i` is a variable, needs
  `Nat.sub_zero`), but `congr 1` discharges it on its own (no `Fin.ext`/`omega` needed); pulled out
  as a local `hi0eq` and reused in `hσ0` and the `t = 0` sub-case.
- `i − (t+1) = i − t − 1` **is** definitional (`Nat.sub_succ`), so `heqw` closes with bare
  `congr 1`.
- Sign transports closed with `nlinarith [hwk/hjoint, hhn]` (rather than `positivity`) because the
  `* (−1)` factor in `htrans` makes the product not manifestly nonneg to `positivity`.

Dependency `ZinanFFCT14` was rebuilt on uisai2 first (clean-3). Touched only
`ProofsInTheBook/ZinanFFCT15.lean`. No git commit.
