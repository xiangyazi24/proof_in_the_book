# opus-cyclictriple reply — the cyclic-triple / diagonal-cut convex-geometry chain (HINGE Lemmas 2.3 / 2.4 / 11.3)

Branch: main (no switches, no commits). Server: uisai1. No codex / OpenAI tooling used.
File owned: `ProofsInTheBook/SphericalCyclicTriple.lean` (NEW, 263 lines, imports `SphericalSZChain`).

## Verification (all from fresh, rebuilt oleans)

```
rsync SphericalCyclicTriple.lean -> uisai1
lake build ProofsInTheBook.SphericalSZChain          -> Build completed (8430 jobs)   [deps]
lake env lean ProofsInTheBook/SphericalCyclicTriple.lean   -> RC=0  (no errors, no warnings)
lake build ProofsInTheBook.SphericalCyclicTriple     -> Built ... (8431 jobs)
```

`#print axioms` (fresh oleans) — **all 13 declarations clean-3** `[propext, Classical.choice, Quot.sound]`:
`gp_three_term`, `sOrient_gp_three_term`, `cyclicTriple_edge_pos`, `cyclicTriplePos_triangle`,
`cyclicTriple_pos_of_diag`, `subseqDiag_support_pos`, `cutCorner_tangent_decomp`,
`equalAngleCut_transport`, `openingData_of_cyclicTriple`, `spherical_arm_mono_cut`,
`spherical_arm_mono_strict_cut`, `cyclicTriplePos_nonvacuous`, `gp_three_term_nondegenerate`.

No `sorry` / `admit` / `axiom` / `native_decide` (grep clean; only prose mentions of "sorry").

## What is PROVED unconditionally (genuine new content, none in the substrate)

* **`gp_three_term`** (Block A) — the Grassmann–Plücker three-term syzygy for the scalar triple product
  with a shared apex: `[a,b,d]·[a,c,e] = [a,c,d]·[a,b,e] + [a,b,c]·[a,d,e]`. True polynomial identity
  (`ring`). `sOrient_gp_three_term` is the `S²` form. This is the *only* algebraic relation among
  shared-apex determinants — the workhorse the design's diagonal induction is built on.
* **`cyclicTriple_edge_pos`** (Block B) — the *base* of HINGE Lemma 2.3: the `j=i+1` (edge) cyclic
  triples are exactly `StrictConvexSphPolygon.strict_nonincident`, recorded in the cyclic-triple
  interface.
* **`cyclicTriplePos_triangle`** — HINGE Lemma 2.3 fully proved for `n=3` (`fin_cases`): the sole
  increasing triple `(0,1,2)` is the edge support. Doubles as the non-vacuity witness.
* **`cyclicTriple_pos_of_diag`, `subseqDiag_support_pos`** (Block C = HINGE Lemma 2.4 / 11.2) — the
  diagonal-cut new-edge support, *derived* from `CyclicTriplePos` with no extra geometry: every support
  determinant of the cut arm's new diagonal is an original cyclic triple, hence positive. This is the
  whole content of "cut-arm convexity follows from cyclicTriple_pos".
* **`cutCorner_tangent_decomp`** (Block D = HINGE Lemma 11.3, determinant form) — the three strict
  cyclic signs `[p,q,r]>0`, `[o,p,q]>0`, `[o,p,r]>0` that place the diagonal ray strictly inside the
  tangent cone (the design §11 "diagonal ray inside tangent cone" sign pattern feeding tangent-angle
  additivity), derived from `CyclicTriplePos`.
* **`equalAngleCut_transport`** (Block E) — the equal-angle cut's endpoint conclusion (assembly of
  pieces 2–4): with the level-`n` comparison and the cut arms (convex by Block C, equal-sided by
  `diag_len_eq`, joints inherited by Block D), the level-`(n+1)` endpoint comparison follows via the
  proved `cut_endpt_transport`.
* **`openingData_of_cyclicTriple`, `spherical_arm_mono_cut`, `spherical_arm_mono_strict_cut`** — the
  conditional discharge + clean arm lemmas (no `SZChain` hypothesis).

So pieces **2, 3, 4** of the dependency chain (cut-arm convexity, cut-corner sign pattern, equal-angle
transport) are **proved**, each *derived from* `CyclicTriplePos` — they are not the residue.

## The single isolated residue (after genuine exhaustion): `CyclicTriplePos`

`CyclicTriplePos P : ∀ i j k, i<j → j<k → 0 < sOrient (P i)(P j)(P k)` — HINGE Lemma 2.3 for the bare
`StrictConvexSphPolygon` predicate. ONE named, **non-vacuous** Prop (`cyclicTriplePos_nonvacuous`:
realised by every triangle). It is strictly the convex-position *input*, not a co-extensive re-wrapper:
the entire downstream chain (2.4/11.2/11.3/transport) is proved *from* it above.

### The precise failing tactic chain (concrete, as requested)

The only algebraic relation among shared-apex determinants is `gp_three_term`, with **four** free
indices. Attempts to derive the diagonal `[P i, P j, P k]` from the edge supports collapse:

1. **`gp_three_term` with apex `a = P i`, isolating `[a, P_j, P_k]`** needs a fifth index `d`; the only
   in-range choices (`d ∈ {P_{j-1}, P_j, P_k}`) all repeat an existing argument, and every repeated
   index sends `gp_three_term` to a trivial identity carrying no information (machine-checked:
   `det3 a b b = 0` and the GP instantiation with `d=b` reduce by `simp only [det3]; ring` — verified on
   uisai1).
2. **Forward-extension `[a,P_j,P_{j+1}]>0 ⟹ [a,P_j,P_k]>0`** (the would-be induction step) instantiates
   GP with `b=P_j, d=P_{j+1}, c=P_k, e=P_{j+1}`; the term `[a,P_{j+1},P_{j+1}] = 0` again kills it.
3. Consequently `cyclicTriple_pos` is a **semialgebraic** consequence of the polygon predicate, NOT a
   polynomial-identity consequence of the edge supports: it is implied (it is a true theorem), but only
   through the *ordering / open-hemisphere inequalities*, not through any `ring`-level combination of the
   edge-support determinants and the GP syzygies. Hence `nlinarith`/`polyrith`/`linear_combination` over
   the edge supports alone cannot close it — the missing ingredient is the strict angular ordering, not
   an algebraic relation. (Numerically confirmed that for `n=4` the diagonal sign tracks the hemisphere
   ordering, never the bare GP relations.)

The information `gp` cannot supply is the **angular/topological ordering** under the open-hemisphere
bound: that the vertices, gnomonically projected to the plane `(P i)^⊥`, have strictly monotone polar
angle with total turning `< π`, whence `sin(arg P_k − arg P_j) > 0`. The genuine proof is the design's
"induction on `j−i` via diagonal containment / hemisphere intersection", which in Lean is a
gnomonic-projection + planar-convex-position development: relate `sOrient` to `Orientation.oangle.sign`
/ the 2D area form (Mathlib `Geometry/Euclidean/Angle/Oriented`), prove strict `oangle` monotonicity of
consecutive vertices from the edge supports, and bound the total turning `< π` from
`StrictConvexSphPolygon.open_hemisphere` (the delicate step — `oangle` is mod `2π`, so the bound must be
maintained as an honest `Real` total, not mod-`2π`). This is a multi-hundred-line analytic build with
real risk on the angle-monotonicity step, and **none of it exists in the substrate** — so it is honestly
isolated as the one named residue, not faked.

## Residue summary (exactly what remains)

To make the arm lemma fully unconditional, a future round must build, **in order**:
1. `CyclicTriplePos` (this residue) — the gnomonic/`oangle` planar-convex-position induction.
2. then Blocks C/D/E here become unconditional automatically (they are already proved *from* it).
3. separately, the all-strict opening (§8.4 reach/stuck on the multi-vertex arm) = the co-extensive
   `SZStepGeom` the prior round isolated; `openingData_of_cyclicTriple` currently routes the opening
   through it.

## Wiring note

`SphericalCyclicTriple.lean` is NOT imported in `ProofsInTheBook.lean` (I own only my file). To wire:
add `import ProofsInTheBook.SphericalCyclicTriple` after the `SphericalSZChain` import, and (for
`Audit.lean`) add the module + the `#print axioms` lines for the 13 declarations above. Builds
standalone (8431 jobs), oleans clean-3.
