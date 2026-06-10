# Ch35 Gates — repair reply

**Status: GREEN.** `ProofsInTheBook/ZinanCh35Gates.lean` compiles clean (0 errors) on uisai2.
No `sorry`/`axiom`/`admit`/`native_decide` (the only grep hit is the module-header prose at
line 66). DESIGN unchanged; no theorem statement weakened. Edited ONLY this file.

## Fixes applied (4 errors → 0)

1. **line 109** — `Equiv.Perm.inv_apply_self` does not exist in this Mathlib. Probed the
   real goal (`extract_goal`): it is `C.seamSwap⁻¹ (C.seamSwap y) = y`. Replaced the call
   with `exact inv_eq_iff_eq.mpr rfl` (confirmed by `exact?`).
2. **line 119** — duplicate `sameCycle_phi_of_dartFace_eq`. The lemma already lives in
   `ChordGateCompat.lean:116` in the SAME namespace
   (`...CombMap.SimplePrimalCycle`) with the same signature, and is transitively imported
   via `ZinanCh35Split`. DELETED the in-file duplicate (incl. its doc comment); the
   downstream use at the old line 140 now resolves to the existing lemma. No rename needed.
3. **line 177** — induction motive bug. `hpath : DualReachableAvoidingCycle M C f g` was
   left in context when `induction hpath'` generalized `g`, so the recursor reverted
   `hpath` into the motive and `ih` acquired a spurious leading
   `DualReachableAvoidingCycle M C f b` argument (the type clash with `h₁`). Added
   `clear hpath` before `induction hpath'` (the copy `hpath'` carries the path). Both
   `refl`/`tail` cases now elaborate.
4. **line 324** — `example (C : SimplePrimalCycle M) ...` sits inside
   `namespace ...CombMap.SimplePrimalCycle`, where the bare name `SimplePrimalCycle`
   resolves to the open namespace, not the type. Qualified it to
   `CombMap.SimplePrimalCycle M` (matching the style used at line 280/292).

No further hidden errors surfaced.

## Semantic guard (the headline is FAITHFUL, not vacuous)

`chordJordanInput'_holds (C : SimplePrimalCycle M) : C.ChordJordanInput'` concludes the
REAL `ChordJordanInput'` (def: `ChordSeparationClose.lean:190`) with NO hypotheses beyond
`C : SimplePrimalCycle M` (plus the ambient `M`/`D`/instances). Its two fields are
discharged by genuine math:

- `faceCore : C.NumCyclesCutPhi2` ← `numCyclesCutPhi2_holds` (ZinanCh35Split, clean-3).
- `gateCompat' : ∀ i, DualReachableAvoidingCycle M C (faceLeft i) (faceRight i) →
   ∃ P, EndpointCapLink i P ∧ InteriorTriangleGates P` ← `gateCompat'_of_dualReachable`,
   instantiating `P := nil`.

Anti-impostor checks (per playbook §3.3):
- `EndpointCapLink i nil` is NOT trivially true: by `EndpointCapLink`'s def
  (`ChordGateCompat.lean:454`) the `n>0` conjuncts are vacuous on nil but the THIRD
  conjunct `(P.n = 0 → cutReach2 (inl (dart i)) (inl (α (dart i))))` is exactly the
  cross-bank bridge — supplied by `crossBankBridge_of_dualReachable`, which is built by
  induction on `hpath` and is provably UNPROVABLE without it (kernel anchors: cut sphere
  map has 2 components). So `hpath` is genuinely consumed.
- `InteriorTriangleGates nil` is vacuous legitimately: its two fields range over
  `Fin P.n` with `j+1 < P.n`; on nil `P.n = 0` so `Fin 0` is empty. This is the
  structure's own n=0 boundary, not a weakening of the general predicate.

No new hypotheses required; STOP-and-report condition not triggered.

## Axiom outputs (verbatim, all 13 headline `#print axioms`)

```
'...SimplePrimalCycle.cutCapPhi2_eq_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'...SimplePrimalCycle.cutCapPhi2_sameCycle_of_seamModel' depends on axioms: [propext, Classical.choice, Quot.sound]
'...SimplePrimalCycle.cutReach2_seamCarrier_of_dartFace_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'...SimplePrimalCycle.cutReach2_of_dartFace_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'...SimplePrimalCycle.cutReach2_seamCarrier_of_dualReachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'...SimplePrimalCycle.crossBankBridge_of_dualReachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'...SimplePrimalCycle.endpointCapLink_of_dualReachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'...SimplePrimalCycle.gateCompat'_of_dualReachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'...SimplePrimalCycle.chordJordanInput'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'...SimplePrimalCycle.jordan_simple_cycle2_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'...SimplePrimalCycle.jordan_simple_cycle2_of_sphere' depends on axioms: [propext, Classical.choice, Quot.sound]
'...NearTriangulation.sphereChordSeparation_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'...NearTriangulation.separates_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All 13 = `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no `ofReduceBool`,
no `trustCompiler`.

## Deviations from the original worker draft
None to the design or any statement. Only the four mechanical repairs above. The local
copy of `sameCycle_phi_of_dartFace_eq` was removed in favor of the pre-existing one
(no logical change).
