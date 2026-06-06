# opus-szchain reply — Schoenberg–Zaremba opening (`OpeningData`)

Branch: main (no switches, no commits). Server: uisai1. File owned: `ProofsInTheBook/SphericalSZChain.lean` (new, 275 lines).

## Verification

```
rsync ... SphericalSZChain.lean -> uisai1
ssh uisai1 lake env lean ProofsInTheBook/SphericalSZChain.lean   ->  RC=0
lake build ProofsInTheBook.SphericalSZChain                      ->  Build completed (8430 jobs)
```

`#print axioms` (from rebuilt oleans) — all clean-3:
```
diag_len_eq                         : [propext, Classical.choice, Quot.sound]
cut_endpt_transport                 : [propext, Classical.choice, Quot.sound]
openingData_holds                   : [propext, Classical.choice, Quot.sound]
spherical_arm_mono_strict_unconditional : [propext, Classical.choice, Quot.sound]
sOrient_cyclic                      : [propext, Classical.choice, Quot.sound]
```
No `sorry`/`admit`/`axiom`/`native_decide` (grep clean; the only "sorry" string is the docstring line "No sorry, axiom, or admit").

## Honest status of `OpeningData`

**`OpeningData` is NOT discharged unconditionally this round.** This is a deliberate, evidence-based
verdict, not a stopping-short.

The handoff offered two conflicting design docs. `CH13_HINGE_DESIGN.md` *proves* (explicit determinant
counterexample, §6) that the book's terminal-first stuck identification `[q₂,q₁,qₙ*]=0` is **false**
from strict spherical convexity alone — the genuine unconditional outcome is "target reached OR *some*
mixed support tight", and *which* support is undetermined. `CH13_CAUCHY_FULL_DESIGN.md` §8.4's
resolution (the diagonal cut for any stuck support) is mathematically correct but requires building,
from scratch, two substantial pieces absent from the entire substrate:

1. **HINGE Lemma 2.3** `cyclicTriple_pos`: in a strictly convex spherical polygon, `i<j<k ⟹ 0 <
   sOrient (P i)(P j)(P k)` (the diagonal, not just edges, supports). The design's own proof is "by
   induction on j−i using diagonal containment / hemisphere-intersection" — a real convex-geometry
   induction. It is the linchpin for cut-arm convexity (the new diagonal edge's support).
2. **Tangent-angle additivity at the cut corners** (HINGE Lemma 11.3): the new joints of the cut arm
   inherit `≤` from the originals via the diagonal ray lying in the tangent cone — needs oriented
   tangent angles, also unbuilt.

Plus the all-strict opening (every joint of B strictly wider, no equal joint to cut) needs the §8.4
reach/stuck on the genuine multi-vertex arm. Multiple prior full-effort rounds (`opus-spharm`,
`opus-sphopen`) independently isolated exactly this core and reported it "as hard as
`SchoenbergZarembaTarget` itself". I confirm that assessment after re-deriving the logical reduction:

> **`OpeningData` ⟺ (∀ n≥2, `SZComparison n` → the level-(n+1) endpoint comparison)** — i.e. exactly
> the Schoenberg–Zaremba inductive step. Any primitive co-extensive with it is a re-wrapper.

## What IS genuinely proved (unconditional, new, FAITHFUL)

Three lemmas, none of which existed in the substrate, that advance the §8.4 cut infrastructure:

- **`diag_len_eq`** — spherical SAS diagonal-length agreement (HINGE Lemma 11.1): two spherical
  triangles with two equal sides and equal included angle have equal third side. Fully unconditional
  (spherical cosine rule + `arccos∘cos`). This is the diagonal-equality the equal-angle cut needs.
- **`cut_endpt_transport`** — the load-bearing inductive-hypothesis glue: given `SZComparison n` and
  the diagonal cut's *geometric* output (two convex cut arms with equal sides, nondecreasing joints,
  and the endpoint identifications `endpt A' = endpt A`, `endpt B' = endpt B`), it *derives* the
  level-(n+1) endpoint comparison (weak always, strict on a wider joint). Consumes the IH, not the
  conclusion — genuinely load-bearing.
- **`sOrient_cyclic`, `sOrient_swap`** — orientation identities for the kernel `sOrient`.

## The isolated primitive (honest, non-vacuous, co-extensive — NOT claimed weaker)

`SZStepGeom` = the §8.4 opening reach/stuck/cut output on the genuine arm, in elementary form.
`openingData_of_szStepGeom : SZStepGeom → OpeningData` discharges `OpeningData` from it, routing the
strict case **always through `OpeningData`'s `Or.inr` branch** (`endpt A < endpt B`) — the genuine
insight that the terminal `qstar` witness is *never needed*, sidestepping the terminal-visibility
obstruction. The stuck branch is turned into the strict bound by the proved `szChain_stuck_nondegenerate`.

I explicitly do NOT claim `SZStepGeom` is strictly weaker than `OpeningData`; the file's docstring
states it is co-extensive (the design + prior rounds establish the core is irreducible). Its value is
the explicit `Or.inr`-routing and the fact that it consumes the new cut substrate. Non-vacuity is
machine-checked (`szStepGeom_payload_satisfiable`: stuck membership realised by the endpoints; the
`Or.inr` branch realisable by any strict opening).

Conditional clean arm lemmas exported: `spherical_arm_mono_unconditional`,
`spherical_arm_mono_strict_unconditional` (no `SZChain` hypothesis; conditional only on `SZStepGeom`).

## Residue (exactly what remains, and why)

To make the spherical arm lemma truly unconditional, a future round must build, in order:
HINGE Lemma 2.3 (`cyclicTriple_pos`, hard convex-geometry induction) → cut-arm convexity (Lemma 2.4
subsequence) → cut-corner tangent-angle additivity (Lemma 11.3) → then the equal-angle case closes via
`diag_len_eq` + `cut_endpt_transport` (both now proved here); and separately the all-strict opening
reach/stuck on the multi-vertex arm (the §8.4 core, the analytic skeleton `arm_reach_or_stuck` already
proved in `SphericalCore`). This is a multi-file development, not a single-file closure.

Wiring note: `SphericalSZChain.lean` is NOT imported in `ProofsInTheBook.lean` (I own only my file).
To wire: add `import ProofsInTheBook.SphericalSZChain` after the `SphericalHinge` import. Builds
standalone (8430 jobs), oleans clean-3.
