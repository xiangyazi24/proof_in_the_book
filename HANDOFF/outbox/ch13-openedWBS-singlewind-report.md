# Ch13 openedWBS single-wind report

File: `ProofsInTheBook/ZinanFFCT97.lean`

Verification on `uisai2`:

```bash
scp ~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT97.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai2 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH && lake build ProofsInTheBook.ZinanFFCT95 ProofsInTheBook.ZinanFFCT68 >/dev/null 2>&1 && lake env lean ProofsInTheBook/ZinanFFCT97.lean'
```

Result: passes.  The printed dependencies for the new declarations are only
`propext`, `Classical.choice`, and `Quot.sound`.

## Unconditional layer

`openedWBS_gnomonicSingleWind` constructs a `GnomonicSingleWind (openedWBS A B k)`
from the one planar lifted-turn residue below.  It is a `noncomputable def`
because the target is Type-valued; the theorem-shaped wrapper is
`openedWBS_gnomonicSingleWind_nonempty`.

The file closes these inputs for `openedWBS A B k` from existing library facts:

- weak convexity via `supportStuckWBS_weakConvex`;
- strict positive joints via `openedJoints_in_Ioo_at_supWBS`;
- strict upper joint bound via `openedWBS_jointAngle_lt_pi`;
- open hemisphere via the `WeakConvexSphArm` certificate;
- orthonormal frame via `ZinanFFCT95.exists_orthoFrame`;
- gnomonic in-plane equations via `inner_gproj`;
- weak planar edge supports via `gnomonic_edge_support_nonneg`;
- nonzero projected cyclic edges via `gproj_ne_of_short`;
- strict consecutive planar turns via `gnomonic_consecutive_turn_pos`.

This also means the possible straight-joint obstruction does not remain in the
current library state: `openedJoints_in_Ioo_at_supWBS` gives every opened WBS
interior joint in `(0, pi)`.

## Isolated residue

Exact statement:

```lean
def OpenedWBSPlanarLiftedTurnSpanExists : Prop :=
  ∀ {n : ℕ} (Q : Fin (n + 1) → E3) (h u v : E3),
    (⟪h, u⟫ : ℝ) = 0 → (⟪h, v⟫ : ℝ) = 0 →
    (⟪u, u⟫ : ℝ) = 1 → (⟪v, v⟫ : ℝ) = 1 → (⟪u, v⟫ : ℝ) = 0 →
    (∀ i : Fin (n + 1), (⟪h, Q i⟫ : ℝ) = 1) →
    (∀ i j : Fin (n + 1), 0 ≤ det3 (Q i) (Q (i + 1)) (Q j)) →
    (∀ i : Fin (n + 1), Q i ≠ Q (i + 1)) →
    (∀ r : ℕ, ∀ hr2 : r + 2 < n + 1,
      0 < det3 (Q ⟨r, by omega⟩) (Q ⟨r + 1, by omega⟩) (Q ⟨r + 2, hr2⟩)) →
    Nonempty (PlanarLiftedTurnSpan Q h u v)
```

Satisfiability witness/justification: `ZinanFFCT94.witChain_certificate`
exhibits a concrete three-vertex planar chain with a `PlanarLiftedTurnSpanHalf`,
hence a `PlanarLiftedTurnSpan`, with positive turns and total span `pi / 4`.
So the certificate type and its planar geometry are realised by an explicit
strict convex chain; the residue is the universal planar theorem extending that
construction to every weakly supported chain satisfying the listed inputs.

## Stretch reduction

Defined the separate downstream planar target:

```lean
def PlanarOneWindNoRepeat : Prop :=
  ∀ {N : ℕ} [NeZero N] {Q : Fin N → E3} {h u v : E3},
    PlanarLiftedTurnSpan Q h u v → PlanarNoNonadjacentRepeat Q
```

Then proved:

- `noNonadjacentRepeat_of_gnomonicSingleWind`;
- `crossPieceNoCollisionAtSup_of_openedWBS_gnomonicSingleWind`.

Precise remaining goals:

1. prove `OpenedWBSPlanarLiftedTurnSpanExists` to get the opened WBS
   `GnomonicSingleWind` certificate;
2. prove `PlanarOneWindNoRepeat` to turn that certificate into
   `CrossPieceNoCollisionAtSup`.
