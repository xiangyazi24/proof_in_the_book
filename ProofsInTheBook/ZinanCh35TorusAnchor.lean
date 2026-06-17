import ProofsInTheBook.PlanarMapSeamInst

/-!
# `ZinanCh35TorusAnchor` — kernel-checked cross-genus anchors for the corrected face count

`PlanarMapSeamInst.lean` records the decisive structural facts as `#eval`s (print-only).  This file
upgrades the load-bearing ones to **kernel-checked** equalities (`rfl` through the computable
`SeamInstEval` mirror), because the corrected Ch35 count route (`ZinanCh35CountRoute.lean`) leans on
exactly this dichotomy:

* the corrected face count `F' = F + 2` holds **across genus** — sphere AND torus — so the remaining
  split-count residue is conjecturally genus-free (NOT an Euler/`χ = 2` fact);
* while the two-cap-chain `SeamDecomposition` factorisation genuinely fails at genus 1 (the
  `ZinanCh35F` header's "no unconditional count" claim conflated these two — the count survives the
  torus, the seam does not).

Anchors: triangle-sphere `(F, F') = (2, 4)`; `K₄`-sphere cut `A→B→D` `(4, 6)`; `K₄`-torus cut
`A→B→D` `(2, 4)`.  In all three `F' − F = 2`.

No `sorry`, `axiom`, `admit`, or `native_decide` (plain `rfl`, kernel-reduced).
-/

namespace ProofsInTheBook.ZinanCh35TorusAnchor

open ProofsInTheBook.PlanarMap.SeamInstEval

/-- Triangle-sphere: `F = 2`, `F' = 4`. -/
theorem triangle_sphere_count :
    cycleCountC (List.finRange 6) (fun d => sigmaTri (alphaTri d)) = 2
      ∧ cycleCountC (allCD 6) (phi2 alphaTri sigmaTri dartTri) = 4 :=
  ⟨rfl, rfl⟩

/-- `K₄`-sphere cut `A→B→D`: `F = 4`, `F' = 6`. -/
theorem k4_sphere_count :
    cycleCountC (List.finRange 12) (fun d => sigmaSphere (alphaK4 d)) = 4
      ∧ cycleCountC (allCD 12) (phi2 alphaK4 sigmaSphere dartABD) = 6 :=
  ⟨rfl, rfl⟩

/-- **`K₄`-torus cut `A→B→D` (genus 1): `F = 2`, `F' = 4` — the count `F' = F + 2` SURVIVES
the torus**, even though the two cap signs thread into one `faceCorr₂`-cycle there (no
`SeamDecomposition`).  This is the kernel witness that the corrected face count is not a
genus-0 phenomenon. -/
theorem k4_torus_count :
    cycleCountC (List.finRange 12) (fun d => sigmaTorus (alphaK4 d)) = 2
      ∧ cycleCountC (allCD 12) (phi2 alphaK4 sigmaTorus dartABD) = 4 :=
  ⟨rfl, rfl⟩

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35TorusAnchor.k4_torus_count
#print axioms ProofsInTheBook.ZinanCh35TorusAnchor.k4_sphere_count
#print axioms ProofsInTheBook.ZinanCh35TorusAnchor.triangle_sphere_count

end ProofsInTheBook.ZinanCh35TorusAnchor
