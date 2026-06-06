# opus-planardiag reply — the planar convex-position primitive `PlanarConvexDiagPos`, PROVED

Branch: main (no switches, no commits). Server: uisai1. No codex / OpenAI tooling used.
File owned: `ProofsInTheBook/PlanarConvexDiag.lean` (NEW, imports `SphericalGnomonic`).

## Status: SOLVED — no residue

`PlanarConvexDiagPos` (the last analytic core blocking Chapter 13's spherical arm lemma) is proved
**unconditionally**:

```
theorem planarConvexDiagPos_holds : PlanarConvexDiagPos
```

This is the exact target `Prop` from `SphericalGnomonic.lean:236` (used verbatim, NOT re-wrapped).
Feeding it through the prior round's `cyclicTriplePos_holds` / `spherical_arm_mono_cut_holds` makes the
cut-branch arm lemmas unconditional (modulo only the separate opening primitive `SZStepGeom`).

## The key idea (the angular/winding order, realised purely on `det3`)

The prior round's four obstructions all refute *first-order* certificates (no nonnegative-coefficient
combination of edge supports, sign-indefinite cocycle `(+)+(+)-(+)`, same-gap `gp`, circular
ear-removal). None of them refutes the **quadratic** shared-apex Grassmann–Plücker syzygy, which is
the genuine algebraic carrier of the "monotone polar order in a half-plane" winding fact:

* **`det3_apex_plucker`** (pure `ring` identity, holds for all five vectors):
  `det3 A P Q · det3 A E M = det3 A M Q · det3 A E P + det3 A P M · det3 A E Q`.

With apex `A = f i` and reference `E = f (i+1)`, the three `det3 A E ·` factors are exactly the
**edge supports of the cyclic edge `(f i, f (i+1))`** (strictly positive on non-incident vertices —
the strict half-plane / "all points left of edge i"). Solving the syzygy for the diagonal:

  `det3 (f i)(f p)(f q) = [ det3(f i)(f (q-1))(f q)·det3(f i)(f (i+1))(f p)
                          + det3(f i)(f p)(f (q-1))·det3(f i)(f (i+1))(f q) ]
                         / det3(f i)(f (i+1))(f (q-1))`,

a **positive combination of strictly smaller-gap diagonals over a positive edge support**. This founds
a clean strong induction on the gap `q - p`, with consecutive base `det3 (f i)(f t)(f (t+1)) > 0`
(a cyclic rotation `det3_cyclic` of the edge support of edge `(t, t+1)`). The two boundary cases
(`p = i+1` direct strict half-plane; `p = q-1` consecutive base) close the induction. The half-plane
confinement (all edge-`i` supports positive) is what supplies the `< 2π` winding bound the handoff
flagged, here entering as the strictly-positive `det3 A E ·` denominator/numerator factors that make
the recursion sign-definite — no `Real.Angle`/`oangle`/mod-`2π` machinery needed.

The numeric pre-check confirmed `det3_apex_plucker` is a genuine polynomial identity, and that it is
the correct sign-definite recursion (verified over random convex configs).

## Structure of the file

* **Block A** — `det3_apex_plucker` (Plücker syzygy), `det3_cyclic` (cyclic invariance). Both `ring`.
* **Block B** — `det3_diag_pos_nat`: the core strong induction on a `ℕ`-indexed family `g` in a
  window `[i, N)`, from the consecutive base `hbase` + strict half-plane `hedge`. The Plücker step is
  one `nlinarith` over the positive products.
* **Block C** — `fin_succ_val`: `Fin`-cyclic successor = linear successor inside the window.
* **Block D** — `planarConvexDiagPos_holds`: lift `f : Fin n → E3` to `g : ℕ → E3` (agreeing on
  `[0,n)`), translate the cyclic edge supports into `hbase`/`hedge`, invoke the core.
* **Block E** — the unconditional cut-branch outputs:
  `cyclicTriplePos_unconditional`, `spherical_arm_mono_cut_unconditional`,
  `spherical_arm_mono_strict_cut_unconditional`.

## Verification (fresh, rebuilt oleans, server uisai1)

```
rsync PlanarConvexDiag.lean -> uisai1
lake build ProofsInTheBook.SphericalGnomonic     -> Build completed (8432 jobs)   [deps]
lake env lean ProofsInTheBook/PlanarConvexDiag.lean -> RC=0  (0 errors, 0 warnings)
lake build ProofsInTheBook.PlanarConvexDiag       -> Build completed (8433 jobs)
```

`#print axioms` (fresh oleans) — **clean-3** `[propext, Classical.choice, Quot.sound]` for:
`planarConvexDiagPos_holds`, `det3_apex_plucker`, `det3_diag_pos_nat`,
`cyclicTriplePos_unconditional`, `spherical_arm_mono_cut_unconditional`,
`spherical_arm_mono_strict_cut_unconditional`. No `sorryAx`, no `ofReduceBool`/`native_decide`.

No `sorry` / `admit` / `axiom` / `native_decide` (grep clean; only docstring prose says "No sorry").

## Faithfulness (playbook §3.3)

* `planarConvexDiagPos_holds` proves the **verbatim** `PlanarConvexDiagPos` def from
  `SphericalGnomonic.lean:236` — not a co-extensive re-wrapper, not an `abbrev`/`def : Prop` dodge.
* No hypothesis-laundering: the only inputs are the original `f`, `h`, the plane/edge/strict-support
  hypotheses (exactly the convex-polygon data); the conclusion is the full `∀ i<j<k` diagonal
  positivity. The hard content (the angular ordering) is genuinely discharged inside, via the Plücker
  induction, not assumed.
* Non-vacuity was already machine-checked upstream (`planarConvexDiagPos_realisable` /
  `planarConvexDiagPos_triangle`); this round proves the universally-quantified statement.

## Wiring note (for the orchestrator; I own only my file)

`PlanarConvexDiag.lean` is NOT imported in `ProofsInTheBook.lean`. To wire: add
`import ProofsInTheBook.PlanarConvexDiag`, and in `Audit.lean` add `#print axioms` for
`planarConvexDiagPos_holds`, `cyclicTriplePos_unconditional`,
`spherical_arm_mono_cut_unconditional`, `spherical_arm_mono_strict_cut_unconditional`,
`det3_apex_plucker`, `det3_diag_pos_nat`. Builds standalone (8433 jobs), oleans clean-3.

## Residue

None on the planar side. The convex-position input to Chapter 13's arm lemma is fully discharged. The
only remaining cut-branch hypothesis is the separate opening primitive `SZStepGeom` (§8.4), unchanged.
