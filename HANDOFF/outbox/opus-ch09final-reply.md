# opus-ch09final reply — Chapter 9 headline composed (geometric Bricard route), CLEAN

**Status: DONE.** New file `ProofsInTheBook/Chapter09Final.lean` (159 lines) composes the proven
Σ₁=Σ₂ machinery into the Chapter 9 geometric headline. Pure composition — zero new mathematics.
Build clean, axioms clean, 0 sorry / 0 axiom / 0 admit / 0 native_decide. Branch `main`, no commits,
library root untouched.

## Verification (uisai1)

- `lake env lean ProofsInTheBook/Chapter09Final.lean` → **0 errors** (only the `#print axioms` info
  lines).
- `lake build ProofsInTheBook.Chapter09Final` → **Build completed successfully (8437 jobs)**, olean
  produced. (Deps `BricardCubePearls`, `BricardAggregate`, `BricardAssemble` built first, 8436 jobs.)
- `#print axioms` on all three headline theorems (`chapter09_final`, `chapter09_no_equidecomp`,
  `hilbert_third_problem_geometric`) → all exactly `{propext, Classical.choice, Quot.sound}`. No
  `sorryAx`, no `ofReduceBool`/`native_decide`.
- `grep sorry|admit|axiom|native_decide|:= rfl|:= trivial` → only doc-string mentions + the audit
  `#print axioms` lines; 0 real occurrences.

## The three proven links composed (1 → 2 → 3)

1. **`edgeCorrespondence_ofEquidecomp`** (BricardAssemble): `decomp : TetEquidecomp regularTetSolid
   cubeSolid` + `EdgeCountBalance` ⟹ `EdgeCorrespondence` (angle field = proven
   `isoVertexPerm_dihedralAngle`; bijection = `edgeOccFwd/Bwd` with proven two-sided inverse).
2. **`EdgeCorrespondence.sigma_match`** (BricardPearls): the by-edge double count ⟹
   `Sigma regularTetSolid … = Sigma cubeSolid …` (the book's Σ₁=Σ₂), by `Finset.sum_bij'`.
3. **`regularTet_cube_no_equidecomp_final`** (BricardCubePearls): Σ₁=Σ₂ ⟹ `False`, cube side closed
   by the *constructed* `cubePearlAngleData`, regular-tet side by proven `regularTetLocationData` /
   `regularTet_pearlExtAngle_arccos`, cube external part vanishing mod ℚπ by proven-unconditional
   `angleClassQ_cube_externalPart_eq_zero_unconditional`.

## Final theorem statements (exact)

```lean
theorem chapter09_final
    (decomp : TetEquidecomp regularTetSolid.toTetSolid cubeSolid.toTetSolid)
    (hcount : EdgeCountBalance decomp (canonicalPearls regularTetSolid) (canonicalPearls cubeSolid)) :
    False

theorem chapter09_no_equidecomp :
    ¬ ∃ decomp : TetEquidecomp regularTetSolid.toTetSolid cubeSolid.toTetSolid,
        EdgeCountBalance decomp (canonicalPearls regularTetSolid) (canonicalPearls cubeSolid)

theorem hilbert_third_problem_geometric :
    ¬ Nonempty { decomp : TetEquidecomp regularTetSolid.toTetSolid cubeSolid.toTetSolid //
        EdgeCountBalance decomp (canonicalPearls regularTetSolid) (canonicalPearls cubeSolid) }
```
(`canonicalPearls S := Pearls (PieceEdges S.toTetSolid)`.)

## Honest classification (playbook §3.1 Group C)

**Verdict: CONDITIONAL-honest**, on the single explicit residual hypothesis `EdgeCountBalance`
(the Pearl-Lemma equal-pearl-count on corresponding edges, indexed through the constructed bijection).
This residue is the *genuine remaining geometric content* of the Bricard argument as documented in
`BricardAssemble.lean` — it is **not** derivable from the isometry pairing alone (the two solids'
global pearl sets have no pointwise correspondence; its proven core is `pearlBalance_of_equalLengths`).
Everything else is proven/constructed: cube-side classification (`cubePearlAngleData`), both
faithfulness bridges, both `LocationData`s, both angle normalizations, regular-tet pearl-nonemptiness.

**Non-vacuity (§3.3):** `edgeCountBalance_satisfiable` exhibits the reflexive equidecomposition
satisfying `EdgeCountBalance` on any pearl set — so the residual hypothesis is a genuine inhabited
constraint, **not** an unsatisfiable premise making the headline vacuous. `#print axioms` cannot
detect an unsatisfiable premise; this check does.

## Two design choices made (with reasons)

1. **Corrected route, not weighted/aggregated.** The weighted endpoint
   `regularTet_cube_no_equidecomp_aggregated` consumes `hQ_pi2` ("every cube pearl on a π/2 external
   edge"), which is **FALSE** on the Kuhn cube (space diagonal = interior edge, angle 2π; face
   diagonals = facet-interior, angle π). Instantiating it for `cubeSolid` is impossible. The corrected
   route (cubepearls `_final` via `_corrected`) replaces `hQ_pi2` by the satisfiable, proven cube fact
   and is the only route that actually closes this concrete cube. This is why the headline routes
   through the *unweighted* Σ₁=Σ₂ (hence needs `EdgeCountBalance`, not the auto-discharged weighted
   `WeightedEdgeBalance`).

2. **Volume / scaling honesty.** The Bricard obstruction is purely angular — no volume hypothesis
   enters, and dihedral angles are scale-invariant. The headline is therefore the faithful geometric
   non-equidecomposability of these two specific concrete solids (regular tet vs Kuhn unit cube),
   robust to their relative sizes; it is **not** a volume-mismatch artefact. I did **not** state a
   general ∀-edge-length form: the imported `regularTetSolid`/`cubeSolid` are fixed concrete-coordinate
   objects and the 36 Kuhn dihedral computations + `regularTetLocationData` are tied to those exact
   coordinates; a parametrized similarity-action variant would require re-deriving that proven
   substrate and is out of scope for a pure-composition file. The fixed-size theorem + the honest
   scale-invariance remark is the faithful achievable form (documented in the module header).

## Files
- Owned & written: `ProofsInTheBook/Chapter09Final.lean` (imports `BricardCubePearls`,
  `BricardAssemble`). No other file touched; lib root `ProofsInTheBook.lean` NOT edited (left to the
  orchestrator to wire if desired).
