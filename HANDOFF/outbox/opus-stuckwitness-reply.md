# opus-stuckwitness-reply — Chapter 13 §8.4 `StuckWitnessExists`, the closing-support identification

## Status: `spherical_arm_mono(_strict)` is **NOT** made unconditional.

The round's proposed sharp angle — that the convex-position ordering (`cyclicTriplePos`) forces the
**closing** support `det3 (A 0)(A 1)(qstar)` to be the **first** mixed support to vanish as the joint
opens, thereby identifying the closing witness — is **mathematically false**, and the refutation is
*internal to the design substrate* (`CH13_HINGE_DESIGN.md §6`) and is now **machine-checked**.

New file: `ProofsInTheBook/SphericalStuckWitness.lean` (RC=0, builds clean, 8443 jobs). No upstream
files edited. I own only this file.

## The decisive finding (verified against the design AND numerically AND in Lean)

`CH13_HINGE_DESIGN.md §6` gives an explicit six-vertex determinant counterexample. Opening the head
ray backwards about the pivot `q₂`, a **non-terminal** mixed support `D(t) = [v₅,v₆,a(t)]` vanishes
first while the **closing/terminal** support `E(t) = [R₋ₜv₆,v₁,v₂]` stays strictly positive. I
recomputed both determinants from the raw vertices and proved, in Lean:

* `ce_D_closed` : `D(t) = 207/100 − (99/50)cos t − (9/5)sin t`;
* `ce_E_closed` : `E(t) = (21/5)sin t + (1/50)cos t`;
* `ce_D_zero_pos` : `D(0) = 9/100 > 0`;  `ce_D_at_052_neg` : `D(0.052) < 0` (sharp Taylor bounds —
  the margin is ~9·10⁻⁴, so `cos 0.052 ≥ 1−0.052²/2` and `sin 0.052 > 0.052−0.052³/4` are *both*
  needed; loose rounding fails);
* `ce_D_has_zero` : IVT ⟹ `∃ t₀ ∈ [0,0.052], D(t₀)=0`;
* `ce_E_pos_on` : `E(t) > 0` for all `t ∈ [0,0.052]`;
* **`closing_not_first`** : `∃ t₀ ∈ [0,0.052], D(t₀)=0 ∧ E(t₀)>0` — a non-terminal support vanishes
  while the closing one is still strictly positive.

So the convex-position ordering does **not** force the closing support to vanish first. The augmented
trichotomy's "*some* vanishing support" cannot be upgraded to "*the closing* one" by `cyclicTriplePos`.
(I also confirmed the counterexample numerically: `t₀ ≈ 0.0515`, `E(t₀) ≈ 0.236 > 0`.)

## What I BANKED (genuine new content, clean-3)

1. **The Grassmann–Plücker deficit identity at the closing configuration** (`gp_closing_deficit`,
   `interiorTailSupport_invariant`, `closing_Afamily_link`). The GP syzygy with shared apex `q₂`,
   specialised to the closing triple `(q₁, qₖᵗ, qₙᵗ)`; the interior tail support `[q₂,qkt,qnt]` is the
   rotation-invariant positive coefficient (via `sOrient_rotS2` + `cyclicTriplePos`). `closing_Afamily_link`
   (probe `x=q₁`) is the clean two-term sign link `[q₂,q₁,qnt]·[q₂,qkt,q₁] = [q₂,q₁,qkt]·[q₂,qnt,q₁]`
   — the algebraic engine behind §8's A-family ("first-edge") monotonicity, the *one* monotonicity
   the convex ordering genuinely supplies. (Verified a true identity numerically.) The B-family
   `[Rₜqᵢ,Rₜqᵢ₊₁,q₁]` and C-family `[Rₜqₙ,q₁,Rₜqₖ]` — "exactly where the counterexample fails" (§8) —
   are NOT controlled by it; this is the honest boundary of what the ordering gives.

2. **The named residue `TerminalVisibility`** (= design §7's `terminal_visibility`):
   `0 < closingMixedSupport A θ ⟹ ∀ ij, 0 < mixedSupport A ij θ`, and the reduction
   **`closingFirst_of_terminalVisibility_admissible`** : under `TerminalVisibility` + admissibility
   (`closing ≥ 0`), a STUCK supremum's vanishing support **is** the closing one
   (`closingMixedSupport A δ = 0`) — exactly the input `betweenness_span_nnreal` consumes. This is the
   genuine missing theorem; `closing_not_first` proves it is strictly stronger than the convex ordering.
   It is non-vacuous (`terminalVisibility_hypothesis_realisable`: the closing support is `> 0` at θ=0)
   and strictly narrower than `StuckWitnessExists` (it carries only the cross-support sign implication,
   none of the opening construction / betweenness extraction / endpoint bookkeeping). No re-wrapper.

3. Conditional re-exports `spherical_arm_mono_complete'` / `_strict_complete'` (unchanged content,
   conditional on `OpeningStructuralAssembly`).

## The single remaining residue (honest, ONE named non-vacuous Prop + concrete failing chain)

`SphericalOpeningProcess.StuckWitnessExists` (the open half of `OpeningStructuralAssembly`). The
closing-witness identification it needs reduces — via `closingFirst_of_terminalVisibility_admissible`
— to `TerminalVisibility`, which `closing_not_first` proves is **not** implied by the convex-position
ordering this round was directed to attack. The concrete failing chain:

1. `StuckWitnessExists` needs `qstar` with `A 0 ∈ span≥0{A 1,qstar}`, from `betweenness_span_nnreal`
   on the vanishing **closing** support `det3 (A 0)(A 1) qstar = 0`.
2. The augmented STUCK branch (`augmented_reachOrStuck_at_sup`) gives `∃ ij, mixedSupport A ij δ* = 0`
   — *some* support.
3. Upgrading "some" → "the closing one" requires `TerminalVisibility` (design §7), **NOT** derivable
   from `cyclicTriplePos`: `closing_not_first` exhibits a strictly convex configuration where a
   non-terminal support vanishes (`D(t₀)=0`) while the closing support is still positive (`E(t₀)>0`).
   This refutes the round's angle directly.

## Verification

* `rsync` + `ssh uisai1 ... lake env lean ProofsInTheBook/SphericalStuckWitness.lean` → **RC=0**.
* `lake build ProofsInTheBook.SphericalStuckWitness` → "Build completed successfully (8443 jobs)".
* `#print axioms` (scratch importer on server, removed after) → **clean-3 `[propext, Classical.choice,
  Quot.sound]`** on: `closing_not_first`, `gp_closing_deficit`, `closing_Afamily_link`,
  `closingFirst_of_terminalVisibility_admissible`, `ce_D_has_zero`, `ce_E_pos_on`,
  `terminalVisibility_hypothesis_realisable`, `spherical_arm_mono_strict_complete'`.
* `grep -nE 'sorry|admit|^axiom|native_decide|:= rfl$|:= trivial'` → only the module-doc prose; 0 in code.

## Honest verdict

FRAGMENT (toward FAITHFUL). The headline `spherical_arm_mono(_strict)` is **NOT** unconditional. The
round's specific angle (cyclicTriplePos ⟹ closing-support-first) is **refuted** — now machine-checked
against the design's own §6 counterexample. Net progress: (a) the refutation is formalized (no future
round need re-litigate the closing-first idea — it is provably false in Lean); (b) the GP deficit
engine + the A-family sign link are banked (the *true* part the angle gestured at); (c) the residue's
resistance is narrowed to the precise, counterexample-backed `terminal_visibility` obstruction (design
§7), isolated as the non-vacuous `TerminalVisibility` with the exact reduction that *would* discharge
the closing-witness identification. No vacuous coupling or co-extensive re-wrapper banked.
