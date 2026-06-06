# opus-terminalvis-reply — Chapter 13 terminal-visibility residue, resolved globally

## Status

`spherical_arm_mono(_strict)` is **NOT** made unconditional this round — but the terminal-visibility
**obstruction is dissolved**, and the prior round's named residue `TerminalVisibility` is **proved
false** (it was a vacuous-conditional impostor). The genuine global resolution (CAUCHY §8.4 Case 2,
diagonal cut, terminal-visibility-FREE) is banked. New file:
`ProofsInTheBook/SphericalTerminalVis.lean` (RC=0, build clean 8444 jobs). I own only this file; no
upstream edits; no commits; branch main.

## The decisive finding: the directive's target `TerminalVisibility` is FALSE — proved.

The task asked to "prove `TerminalVisibility` directly via a global argument." On inspecting the
substrate, `TerminalVisibility` (the prior round's `Prop`, = design §7 `terminal_visibility`) is

```
∀ n A, StrictConvexSphArm A → ∀ θ, 0 < closingMixedSupport A θ →
    ∀ ij : Fin (n+1+1) × Fin (n+1+1), 0 < mixedSupport A ij θ
```

with `mixedSupport A ij θ = det3 (A ij.1)(A ij.2)(rot(axis) θ (A last))`. This is **identically
unsatisfiable**: `mixedSupport` is antisymmetric in its first two slots
(`mixedSupport A (1,0) θ = − closingMixedSupport A θ`), so where the closing support is positive the
`(1,0)` support is negative — the all-pairs conclusion cannot hold. This is exactly the playbook §3.3
"VACUOUS conditional theorem" failure mode: `#print axioms` cannot detect the unsatisfiable premise, so
the prior round banked a conditional (`closingFirst_of_terminalVisibility_admissible`) whose hypothesis
is never met. **It was the wrong target.**

Proved unconditionally as `terminalVisibility_false : ¬ TerminalVisibility`, on a **concrete witness**
— a strictly convex spherical quadrilateral `quadArm` with rational unit vertices `(±3/5,0,4/5)`,
`(0,±3/5,4/5)` in the open north hemisphere (all edge supports `= 72/125 > 0`, full
`StrictConvexSphArm` certified field-by-field). The witness's closing support is `+72/125 > 0` at
`θ=0` (`quadArm_closing_pos`), so the contradiction comes from a *satisfied* premise — not a vacuous
one. (This is on top of the prior round's geometric `closing_not_first`; and I numerically reconfirmed
that even for the substrate's single-vertex opening the closing support is *not* first to vanish — the
support `(0, axis, last)` vanishes earlier.)

## The genuine global resolution: terminal visibility is UNNECESSARY (CAUCHY §8.4 Case 2).

The authoritative chapter route (`CH13_CAUCHY_FULL_DESIGN.md` §8.4 Case 2) never identifies the
closing support: *any* non-incident vanishing support `sOrient(P i)(P(i+1))(P j)=0` (terminal or not)
gives a **diagonal cut** into two smaller convex arms, "this needs NO terminal-first identification."
I bank:

* **`stuckSupport_gives_cut`** — a strictly convex arm with *any* non-incident vanishing support admits
  a diagonal-cut sub-arm that is again `StrictConvexSphArm` sharing `A 0`. The vanishing pair is
  arbitrary; the closing identification plays no role. (Application of the substrate's proved
  `diagonalCutArm_holds`; stated honestly as such, not as new content.)
* **`vanishingSupport_planar_collinear`** — the global hemisphere/gnomonic content (NEW): via the
  proved `gnomonic_sign_correspondence`, a vanishing spherical support of a strictly convex polygon
  projects to a vanishing *planar* orientation of the gnomonic image (the sign factor is strictly
  positive in the open hemisphere). So the stuck support is a genuine planar diagonal — cuttable —
  with **no** order/terminal assumption. The promised gnomonic-to-planar reduction, but applied to
  *dissolve* the obstruction rather than to prove the false terminal-first statement.
* **`terminalVisibility_unnecessary`** — the headline pairing: for any strictly convex arm, (any
  non-incident stuck support gives the cut) ∧ (`¬ TerminalVisibility`). The §8.4 stuck branch is
  discharged without terminal visibility, and the terminal-first target is provably false.

Numerically verified (200 random convex configs): the first vanishing support of the substrate opening
is **always** a non-incident edge–vertex support, hence always cuttable — never needs terminal-first.

## What I BANKED (genuine new content, clean-3)

1. `terminalVisibility_false` / `terminalVisibility_false_on_arm` — the unconditional refutation of the
   prior round's named residue, on the concrete `quadArm` witness (full `StrictConvexSphArm`
   construction: `quadArm_strictConvex`, `quad_edge_short/_support/_strict/_hemisphere`,
   `mixedSupport_swap`).
2. `vanishingSupport_planar_collinear` + `vanishingSupport_transport_genuine` — the gnomonic transport
   of a stuck support to a planar collinearity (the global open-hemisphere content).
3. `stuckSupport_gives_cut` / `terminalVisibility_unnecessary` — the §8.4-Case-2 terminal-visibility-
   free resolution (application of `diagonalCutArm_holds`, honestly labelled).

## The remaining residue (precise, honest, outside this file's ownership)

The arm lemma stays conditional on the substrate primitive `OpeningStructuralAssembly` (≡
`StuckWitnessExists`). The obstruction is no longer mathematical (terminal visibility is dissolved) but
**architectural**: `StuckWitnessExists`, as the substrate *defines* it, demands the **closing**
betweenness `A 0 ∈ span≥0 {A 1, qstar}` from the *opening-witness* route — the very closing-first route
disproved here. Discharging it requires replacing that primitive's opening-witness reduction by the
**diagonal-cut induction** now shown available (cut at any stuck support, recurse on the two smaller
`StrictConvexSphArm`s, glue with the spherical hinge lemma). That re-architecting edits
`SphericalOpeningProcess` / `SphericalAdmissibleSup` / `SphericalReachStuck` (not owned by this file).
It is wiring, unblocked of its only genuine mathematical obstruction.

## Verification

* `rsync` + `ssh uisai1 ... lake env lean ProofsInTheBook/SphericalTerminalVis.lean` → **RC=0**.
* `lake build ProofsInTheBook.SphericalTerminalVis` → "Build completed successfully (8444 jobs)".
* `#print axioms` (scratch importer, removed after) → **clean-3 `[propext, Classical.choice,
  Quot.sound]`** on: `terminalVisibility_false`, `terminalVisibility_false_on_arm`,
  `quadArm_strictConvex`, `quadArm_closing_pos`, `stuckSupport_gives_cut`,
  `vanishingSupport_planar_collinear`, `vanishingSupport_transport_genuine`,
  `terminalVisibility_unnecessary`, `mixedSupport_one_zero`, `spherical_arm_mono_strict_terminalvis`.
* `grep -nE 'sorry|admit|^axiom|native_decide'` → only the module-doc prose; 0 in code. (Two `:= rfl`
  lemmas `quad_sOrient`/`quad_inner` are legitimate definitional coercion/unfold equalities, not
  trivially-true target impostors.)

## Honest verdict

FAITHFUL refutation + FRAGMENT toward closure. The directive's literal target (`prove
TerminalVisibility`) is **impossible** — `TerminalVisibility` is provably false (machine-checked,
unconditional, concrete witness); proving it would have required a false theorem. The correct global
move is to **eliminate** terminal visibility via the diagonal cut (CAUCHY §8.4 Case 2), now banked with
its gnomonic/hemisphere justification. The §8.4 stuck branch needs no terminal-first identification;
the headline arm lemma's only remaining residue is the architectural re-wiring of the substrate's
opening reduction to consume the cut instead of the (dead) closing-witness route. No vacuous coupling
or co-extensive re-wrapper banked; the one application of `diagonalCutArm_holds` is labelled as such.
