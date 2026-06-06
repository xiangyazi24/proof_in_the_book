# Ch09 WEIGHTED headline — reply (opus)

## Status: DONE — fully weighted, NO residual hypotheses, axioms clean.

The raw-count residual `EdgeCountBalance` of `Chapter09Final.lean` is **eliminated**.  The new file
`ProofsInTheBook/Chapter09Weighted.lean` (198 lines, 0 sorry/axiom/admit) composes the proven weighted
chain end-to-end and delivers the headline with **no residual hypotheses**.

## Final statement

```lean
theorem chapter09_weighted :
    ¬ Nonempty (TetEquidecomp regularTetSolid.toTetSolid cubeSolid.toTetSolid)
```

Unconditional: the only input is the type of equidecompositions itself. No `EdgeCountBalance`, no
`hQ_pi2`, no weight/balance/faithfulness hypotheses — all constructed or proven from the imports.

## The weighted chain composed

```
decomp : TetEquidecomp regularTetSolid cubeSolid
  ⟹ (aggregate)  weightedEdgeBalance_of_equidecomp decomp
                   edgeSourceFaithful_regularTetSolid edgeSourceFaithful_cubeSolid
                 ⟶ positive νP, νQ  with  WeightedEdgeBalance
                   (pearl-level Pearl Lemma exists_balanced_pearl_weights + both proven bridges)
  ⟹ (balance)    sigmaW_match_of_weightedEdgeBalance ⟶ SigmaW₁ = SigmaW₂
  ⟹ (location)   angleClassQ_sigmaW (both solids):
                   regular: externalPartW_eq_total_mul + regularTet_pearlExtAngle_arccos
                            ⟶ SigmaW₁ ≡ (Σ νP)·arccos(1/3)
                   cube:    angleClassQ_cube_externalPartW_eq_zero  ⟶ SigmaW₂ ≡ 0   (mod ℚπ)
  ⟹ (irrationality, Σ νP ≥ 1 from νP>0 + pearls nonempty)
                   angleClassQ_arccos_one_third_ne_zero ⟶ False
```

## The ONE new lemma (the genuine new content)

`angleClassQ_cube_externalPartW_eq_zero` — the **weighted** analogue of the unweighted
`BricardLocation.angleClassQ_cube_externalPart_eq_zero_unconditional`.  This is the fix that makes the
weighted route instantiable for the *Kuhn* cube:

- The pre-existing weighted headline `Bricard.regularTet_cube_no_equidecomp_weighted` consumes the
  literal `hQ_pi2` (every cube pearl on an external edge of angle π/2), which is **false** on the Kuhn
  six-orthoscheme cube (space diagonal: interior edge, angle 2π; face diagonals: facet-interior, angle
  π).  So that headline is NOT instantiable for `cubeSolid` + `cubePearlAngleData`.
- The corrected lemma: for any `LocationData` over the cube and any integer ν, the weighted external
  part `externalPartW L ν = ∑_p (ν p)·pearlExtAngle(cert)` vanishes mod ℚπ.  Proof: each
  `pearlExtAngle` is q·π (rational, via the proven `cube_pearlExtAngle_rat_mul_pi`), so
  `(ν p)·(q·π) = ((ν p · q : ℚ))·π` is again a rational multiple of π; `angleClassQ_rat_mul_pi` kills
  every summand.

Everything else is reused verbatim from the proven weighted chain (`SigmaW`, `externalPartW`,
`sigmaW_match_of_weightedEdgeBalance`, `angleClassQ_sigmaW`, `externalPartW_eq_total_mul`,
`weightedEdgeBalance_of_equidecomp`).  No genuine gap remained to isolate.

## Verification (uisai1, NEVER built locally)

```
# dependency oleans:
nohup lake build ProofsInTheBook.BricardCubePearls   → Build completed successfully (8436 jobs)
# the new file:
lake env lean ProofsInTheBook/Chapter09Weighted.lean
  → 'ProofsInTheBook.Chapter09Weighted.chapter09_weighted' depends on axioms:
    [propext, Classical.choice, Quot.sound]
```

Clean-3 axioms (no sorryAx, no ofReduceBool/trustCompiler, no custom axiom). 0 sorry/admit/native_decide.

## Notes on environment / scope

- Stayed on git branch `main`; no branch switches; no commits (file written, not committed —
  awaiting your wiring into `ProofsInTheBook.lean` / `Audit.lean` if desired).
- I own only `ProofsInTheBook/Chapter09Weighted.lean`; no other file touched.
- All eight Bricard dependency files verified byte-identical (git hash-object) between local working
  tree and uisai1 before building, so the verification is against exactly the machinery read locally.
- No codex / OpenAI tooling used.

## Non-vacuity (playbook §3.3)

The headline is unconditional, so there is no conditional premise to be vacuous.  The intermediate
weighted layer is non-vacuous by construction: `exists_balanced_pearl_weights` produces everywhere-
positive multiplicities for *any* equidecomposition, `Σ νP ≥ 1` is forced by `νP > 0` and the proven
pearl-nonemptiness, and the existing `weightedEdgeBalance_refl` / `sigmaW_match_refl` witnesses inhabit
the weighted-balance interface.
