# Ch13 wrap-base report -- ZinanFFCT70

Delivered:

- `ProofsInTheBook/ZinanFFCT70.lean`
- `HANDOFF/outbox/ch13-wrapbase-report.md`

## What landed

### `bpos_aneg` successor-edge collapse

New names:

```lean
def BPosAPosEndpointCase : Prop := ...
def BPosANegTailCornerResidue : Prop := ...

theorem bpos_aneg_false_of_successor : ...
theorem bpos_aneg_endpointConsumer_of_tail
    (res : BPosANegTailCornerResidue) :
    BPosANegEndpointConsumer := ...
```

`bpos_aneg_false_of_successor` closes the `a < 0`, `0 < b` endpoint branch whenever the far endpoint still has a normalized successor edge, i.e. `j + 1 < n + 1`.

The proof uses the weak support inequalities on the predecessor and successor edges at `j`, reads out the signed coefficients with `nearSide_a_readout` and `nearSide_a_readout_succ`, obtains both witness coefficients zero, and contradicts `not_both_witness_zero`.

The remaining `bpos_aneg` tail is isolated as:

```lean
def BPosANegTailCornerResidue : Prop :=
  ∀ {n : ℕ} {P B : Fin (n + 1) → S2},
    WeakConvexSphArm P → PositiveJoints P → StrictConvexSphArm B →
    SameSides P B → JointLe P B → NoNonadjacentRepeat P →
    (∃ h : E3, ‖h‖ = 1 ∧ ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ)) →
    ∀ {i : ℕ}, i + 1 < n →
    ∀ (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hn : n < n + 1),
    ∀ {a b : ℝ},
      (P ⟨i, hi⟩ : E3) = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨n, hn⟩ : E3) →
      0 < b → a < 0 → endpt P ≤ endpt B
```

### FFCT70 final wrapper

New final surface:

```lean
structure Ch13FinalSurface70 : Prop where
  hmirrorSeed : SupportStuckWBSMirrorVanishingSpanSeedSupply
  hcross : CrossPieceNoCollisionAtSup
  hbpos_apos : BPosAPosEndpointCase
  hbpos_aneg_tail : BPosANegTailCornerResidue
```

New assembly theorem:

```lean
theorem btrichotomyEndpointCases_of_surface70
    (res : Ch13FinalSurface70) :
    BTrichotomyEndpointCases := ...
```

New headline theorem:

```lean
theorem spherical_arm_mono_final_ch13_v4
    (res : Ch13FinalSurface70) :
    SphericalArmMonotone := ...
```

This headline now routes through the FFCT69 theorem after assembling `BTrichotomyEndpointCases` from FFCT70 fields.

## Exact remaining surface

The requested "mod only `CrossPieceNoCollisionAtSup`" endpoint did not land honestly from the current library. The exact FFCT70 surface is:

```lean
structure Ch13FinalSurface70 : Prop where
  hmirrorSeed : SupportStuckWBSMirrorVanishingSpanSeedSupply
  hcross : CrossPieceNoCollisionAtSup
  hbpos_apos : BPosAPosEndpointCase
  hbpos_aneg_tail : BPosANegTailCornerResidue
```

So the remaining proof surface is still:

- mirror/wrap seed supply,
- cross-piece no collision,
- `bpos_apos` endpoint case,
- `bpos_aneg` final tail corner.

## What still resists

### Wrap-base seed

`SupportStuckWBS` gives a nonincident support witness via `supportStuckWBS_vanishingSupport`, but for a wrap binding edge with base vertex `n`, the existing `orientationNormalized` hypothesis is unavailable in the needed shape because it requires a normalized forward edge `a.val + 1 < n + 1`.

FFCT42/FFCT45 contain cyclic wrap identities and a base-stuck vanishing support theorem, but the landed theorem there is for `BaseStuckWBS`, not for an arbitrary `SupportStuckWBS` witness whose binding edge is the wrap edge. I did not find a current theorem that converts a generic wrap-edge `SupportStuckWBS` directly into a normalized non-wrap seed. The raw wrap corner therefore remains inside `hmirrorSeed`.

### `bpos_apos`

FFCT68 contains stronger consumers for the `bpos_apos` branch, including the FFCT-plus variants, but their statements require additional IH/diagonal hypotheses. No unconditional `BPosAPosEndpointCase` follows from the currently exposed surface without adding such data, so this field remains explicit in FFCT70.

### `bpos_aneg` tail corner

FFCT70 closes the `bpos_aneg` branch whenever the far endpoint has a real successor edge. The surviving case is exactly `j = n`, where the normalized linear arm has no successor edge `(j, j+1)` available for the two-zero contradiction.

The brief suggested mirror/tail machinery; the current FFCT60/FFCT61 tail-boundary facts are tied to WBS non-axis/tail residue and `mirrorArm` data. I did not find a landed statement converting this general `BTrichotomyEndpointCases` tail corner into contradiction without additional WBS-specific residue data, so it is isolated as `BPosANegTailCornerResidue`.

## Verification

Remote verification on `uisai2`:

```bash
scp ProofsInTheBook/ZinanFFCT70.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT70.lean
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake build ProofsInTheBook.ZinanFFCT69 && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT70.lean'
```

Result:

- `ProofsInTheBook.ZinanFFCT69` built successfully on `uisai2`.
- `ProofsInTheBook/ZinanFFCT70.lean` checked successfully on `uisai2`.
- `#print axioms` for the new main theorems is clean-3 only:
  `[propext, Classical.choice, Quot.sound]`.
- Local placeholder-token scan passed for `ZinanFFCT70.lean`.

No commit was made.
