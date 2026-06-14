import ProofsInTheBook.ZinanCh35Split

/-!
# `ZinanCh35Residue` — confirmation that the Ch35 actual-split count residue is closed

This file is an **audit / confirmation** module owned by this session.  It does not
introduce new mathematics: it re-states the single open Chapter-35 count-route residue
flagged by `UNDERSTANDING.md` (dated 2026-06-09) and exhibits the already-existing
unconditional, genus-free proof from `ZinanCh35Split.lean`, so that a fresh
`#print axioms` over rebuilt oleans certifies it clean-3.

## The residue (as worded in the task / `ZinanCh35CountRoute.lean`)

`ZinanCh35CountRoute.lean` reduces the chapter's topological side to the single
hypothesis `hsplitsAll`:

```
∀ Ls : List (List C.CutDart), C.FaceCorrCycleLists Ls →
  FaceCorrWord.concatLen Ls + 2 ≤ 2 * (C.actualSplitFinset Ls).card + 2 * C.len
```

## Status: CLOSED (unconditional, genus-free)

`ZinanCh35Split.lean` proves the **exact split-count identity**
`concatLen Ls + 2 = 2·card(actualSplitFinset) + 2·len` (slack 0, every cut, every genus)
via the seam conjugacy

  `seamSwap · φ'₂ · seamSwap⁻¹ = φ ⊕ (nextIdx ⊕ prevIdx)`   (`seamSwap_phi2_conj`),

whence `numCycles φ'₂ = F + 1 + 1 = F + 2` (`numCycles_cutCapPhi2`), and the telescope
(`sum_stepDelta_eq_neg_m_add_two_actualSplits`) read backwards yields the split-count
identity.  The `+2` is the two cap chains, each a genuine single `len`-cycle of the
cyclic `nextIdxEquiv` (`numCycles_nextIdxEquiv = 1`).  The conjugacy uses **no** `χ = 2`
hypothesis — which is exactly why the count survives the K₄ torus (`χ = 0`,
`ZinanCh35TorusAnchor.k4_torus_count`: `F = 2`, `F' = 4`, `F' − F = 2`).

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

namespace ProofsInTheBook.ZinanCh35Residue

open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

variable {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}

/-- **The Chapter-35 actual-split count residue `hsplitsAll`, discharged.**  This is the
`∀`-form hypothesis left open by `ZinanCh35CountRoute.lean`; it is proven unconditionally
in `ZinanCh35Split.lean` (`splitsEnough_all`). -/
theorem ch35_actualSplit_count_residue (C : SimplePrimalCycle M) :
    ∀ Ls : List (List C.CutDart), C.FaceCorrCycleLists Ls →
      FaceCorrWord.concatLen Ls + 2
        ≤ 2 * (C.actualSplitFinset Ls).card + 2 * C.len :=
  C.splitsEnough_all

/-- The residue holds with **slack 0**: the inequality is in fact an equality, for every
cycle-list certificate (the exact split-count identity). -/
theorem ch35_actualSplit_count_residue_eq (C : SimplePrimalCycle M)
    {Ls : List (List C.CutDart)} (H : C.FaceCorrCycleLists Ls) :
    FaceCorrWord.concatLen Ls + 2
      = 2 * (C.actualSplitFinset Ls).card + 2 * C.len :=
  C.concatLen_add_two_eq_splits H

/-- The face core the residue is equivalent to, `numCycles φ'₂ = F + 2`, genus-free. -/
theorem ch35_faceCore (C : SimplePrimalCycle M) : C.NumCyclesCutPhi2 :=
  C.numCyclesCutPhi2_holds

/-! ## Axiom audit (clean-3 expected) -/

#print axioms ch35_actualSplit_count_residue
#print axioms ch35_actualSplit_count_residue_eq
#print axioms ch35_faceCore

end ProofsInTheBook.ZinanCh35Residue
