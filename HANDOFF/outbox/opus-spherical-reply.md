# Spherical kernel — Chapter 13 extrinsic S² layer (opus reply)

**Status: DELIVERED — clean compile, 0 sorry / 0 axiom / 0 admit.**
File: `ProofsInTheBook/SphericalKernel.lean` (501 lines, new, untracked on `main`, no commit per rules).
Imports `ProofsInTheBook.TetDihedral` and reuses its `projOut` machinery throughout.

## Verification

- `lake env lean ProofsInTheBook/SphericalKernel.lean` → EXIT 0, zero errors.
  (Only 2 warnings, both `push_neg` deprecation — matches existing repo style; `push_neg` is
  already used in Chapter20Colors / Chapter22Stable.)
- `lake build ProofsInTheBook.SphericalKernel` → Build completed successfully (8422 jobs).
- `#print axioms` on all load-bearing theorems → every one depends ONLY on
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no `ofReduceBool`/`native_decide`.
  Checked: `spherical_cosine_rule`, `spherical_hinge_mono`, `spherical_hinge_strict`,
  `norm_tangentTo`, `sDist_eq_zero_iff`, `tangentTo_ne_zero_iff`, `spherical_arm_mono`,
  `spherical_arm_mono_strict`.
- `grep sorry|admit|axiom|native_decide` → none (the three hits are inside doc-comment prose).
- Non-vacuity check (anti-impostor): `SZChain A A` is constructively provable
  (`endpoint_mono := le_refl`, `endpoint_strict` discharged by `lt_irrefl`), so the arm-lemma
  hypothesis is satisfiable, NOT a vacuous unsatisfiable premise.

All verification ran EXCLUSIVELY on uisai1. Nothing was built/run locally.

## What was delivered (per design Layers A–D)

**Layer A — sphere basics (all unconditional, FAITHFUL):**
`E3`, `S2`, `sInner`, `sDist`, `ShortArc`. Lemmas: `sInner_mem_Icc`, `cos_sDist`,
`sin_sq_sDist`, `sDist_nonneg`, `sDist_le_pi`, `sin_sDist_nonneg`, `sDist_comm`,
`sDist_eq_zero_iff` (= iff for unit vectors), `sDist_pos_of_ne`,
`sDist_lt_pi_of_not_antipodal`, and `ShortArc.{symm, sDist_pos, sDist_lt_pi, sin_sDist_pos}`.

**Layer B — tangent projections + spherical angle (all unconditional, FAITHFUL):**
`tangentTo p q := projOut (p:E3) (q:E3)` (reuses TetDihedral), `sphAngle u v w` via
`InnerProductGeometry.angle` of the two tangent projections (the projOut pattern from the design).
Lemmas: `tangentTo_eq`, `tangentTo_orthogonal`, `decompose_unit_along_tangent`,
`norm_sq_tangentTo`, `norm_tangentTo` (‖tangent‖ = sin sDist), `tangentTo_eq_zero_iff` /
`tangentTo_ne_zero_iff` (nonvanishing ⟺ ShortArc, i.e. non-equal AND non-antipodal —
the key well-definedness lemma), `sphAngle_comm/_nonneg/_le_pi`.

**Layer C — the load-bearing computation (all unconditional, FAITHFUL):**
- `spherical_cosine_rule (a b c : S2)` :
  `cos(sDist a c) = cos(ab)·cos(bc) + sin(ab)·sin(bc)·cos(sphAngle a b c)`.
  Proved EXACTLY by the design's explicit construction: decompose `a` and `c` in the tangent
  frame at `b` (`q = cos·b + tangent`), expand `⟪a,c⟫`, kill the two cross terms via tangent⊥b,
  and identify `⟪tan ba, tan bc⟫ = ‖·‖‖·‖cos γ` (`cos_angle_mul_norm_mul_norm`) with
  `‖tan‖ = sin`. No frame/basis hand-waving — pure inner-product algebra. This is the single
  most load-bearing theorem and it is fully closed and unconditional.
- `spherical_hinge_mono` and `spherical_hinge_strict` — the n=3 spherical-arm base:
  with a,b ∈ (0,π) fixed, the opposite side is (strictly) increasing in γ ∈ [0,π].
  Via `sin a, sin b > 0` + antitonicity of `cos` on [0,π] (`cos_le/lt_cos_of_nonneg_of_le_pi`).

**Layer D — convex arm structure + arm-lemma statement:**
- `det3` (explicit coordinate triple product), `sOrient`.
- `StrictConvexSphPolygon` (three_le, edge_short, edge_support via `0 ≤ sOrient`,
  strict_nonincident via `0 < sOrient`, open_hemisphere) — faithful to design §3.
  (Carries `[NeZero n]` so the cyclic successor `i+1 : Fin n` elaborates; `Fin (n+1)` supplies
  it automatically for arms.)
- `StrictConvexSphArm`, `sideLen`, `jointAngle`.
- `spherical_arm_mono` / `spherical_arm_mono_strict` — STATED and proved CONDITIONAL on an
  explicit `SZChain A B` hypothesis (the hinge-opening-chain data). These are honest conditionals,
  not impostors: `SZChain` is satisfiable (verified above), and the theorems faithfully say
  "given the opening chain, endpoint distance is (strictly) monotone."

## Isolated next-round target (ONE truly resistant piece — honestly flagged)

The full Schoenberg–Zaremba hinge induction (design §8) exceeds one file, exactly as the design
sanctions. It is isolated as a NAMED, explicit, UNPROVED obligation:

```
def SchoenbergZarembaTarget : Prop :=
  ∀ {n} (hn : 2 ≤ n) (A B : Fin (n+1) → S2),
    StrictConvexSphArm A → StrictConvexSphArm B →
    (∀ i, sideLen A i = sideLen B i) →
    (∀ i, jointAngle A i ≤ jointAngle B i) →
    SZChain A B
```

Discharging `SchoenbergZarembaTarget` turns `spherical_arm_mono`/`_strict` unconditional. Its proof
factors (design §8) through `rotAbout` (Rodrigues), `HingeMove`/`hinge_endpoint_mono` (built on the
already-proved `spherical_hinge_mono`), `convex_hinge_open_small`, and `convex_stuck_gives_cut`
(the planar "stuck case" — coplanarity `det3 = 0` cuts the arm). Its **n = 2 base IS
`spherical_hinge_strict`, already proved here.** I used `def : Prop` (not `theorem … := sorry`)
deliberately so the file is genuinely sorry-free AND the obligation is unmistakable.

## Honest classification (playbook Group C)

- Layers A, B, C: **FAITHFUL, UNCONDITIONAL.** The spherical law of cosines and both hinge
  monotonicities are complete, no weakening.
- `spherical_arm_mono` / `_strict`: **CONDITIONAL-honest** on `SZChain` (satisfiable, non-vacuous).
- `SchoenbergZarembaTarget`: **STATEMENT ONLY** — the next round's named target. Not claimed proved.

No vertex-link / Cauchy-bridge layers (design §9–§12) attempted this round — those sit above the
arm lemma and were out of scope for the foundational kernel.
