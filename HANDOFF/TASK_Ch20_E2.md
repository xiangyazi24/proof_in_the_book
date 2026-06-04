# TASK Ch20 E2 — interior atomic segment borders exactly two triangles

You are completing the faithful (T-vertex-allowing) version of Monsky's theorem.
Everything except this geometric core is already proved upstream.

## Your file (you own it; do NOT edit any other .lean file)

`ProofsInTheBook/Chapter20DissectionEngine.lean`. You may create additional NEW
helper files `ProofsInTheBook/Chapter20E2*.lean` that import the engine if useful.
Do NOT touch `Chapter20.lean`, `Chapter20Dissection.lean`, or `ProofsInTheBook.lean`.

## Self-verify

`cd ~/repos/proof_in_the_book && lake env lean ProofsInTheBook/Chapter20DissectionEngine.lean`
(plus any helper file). Do NOT run `lake build` (it clobbers in-flight files).

## Tasks, in order

1. **Make the definitions type-check.** The engine file has the `SquareDissection`
   structure and atomic-incidence defs (`OnSide`, `sideParam`, `sideInteriorChain`,
   `sideAtomicEdges`, `triAtomicEdges`, `atomicMult`, `IsAtomicEdge`,
   `OnSquareBoundary`). They were written without a local Lean check — fix any
   type errors, instance issues, or `Sym2.lift` well-definedness obligations.
   Keep the mathematical meaning identical; if a definition is genuinely wrong
   for the math (not just a Lean nit), report it precisely rather than papering over.

2. **Sanity witness (validates the definition).** In a helper file, construct the
   diagonal split of the unit square as a `SquareDissection` with `n = 2`
   (vertices `(0,0),(1,0),(1,1),(0,1)`, triangles `(0,1,2)` and `(0,2,3)`), proving
   `cover`, `disjoint_int`, `nondeg`, `equalArea`. If you cannot prove `cover` or
   `disjoint_int` for this concrete witness, that is a signal the definition is
   wrong — report the exact obstruction.

3. **Prove E2** — the two `sorry`s:
   ```
   atomicMult_even_of_interior (e) (he : IsAtomicEdge e) (hint : ¬ OnSquareBoundary e) : Even (atomicMult e)
   atomicMult_eq_one_of_boundary (e) (he : IsAtomicEdge e) (hbd : OnSquareBoundary e) : atomicMult e = 1
   ```

## Proof of E2 (full sketch — formalize it; the math is correct)

Fix atomic `e = s(p,q)`, `m` a relative-interior point of `[coord p, coord q]`,
no vertex on the open segment. Pick `ε>0` below the distance from `m` to every
vertex and to every triangle edge not on line `L = affineSpan ℝ {coord p, coord q}`.

1. **No transversal crossing at `m`.** A triangle edge not on `L` meeting the
   open disk `B(m,ε)` would force two triangles' interiors to overlap a quadrant,
   contradicting `disjoint_int`. So every triangle edge meeting `B(m,ε)` lies on
   `L`; `L` splits `B(m,ε)` into two open half-disks `B⁺,B⁻`, both edge-free.
2. **Each half-disk lies in one triangle interior.** A half-disk is connected,
   edge-free, and ⊆ `S = ⋃ closures` (for `m` interior to the square); each of its
   points is in some triangle closure but on no edge ⇒ in exactly one interior
   (disjoint interiors); the assignment is locally constant on the connected
   half-disk ⇒ `B⁺ ⊆ interior T⁺`, `B⁻ ⊆ interior T⁻`, with `T⁺ ≠ T⁻`.
3. **`e` borders exactly `{T⁺,T⁻}`.** Points of `[coord p,coord q]` near `m` are
   limits of `interior T⁺` and of its complement (`B⁻ ⊆ interior T⁻`), so lie on
   `∂T⁺`; being on `∂` of a triangle and atomic ⇒ `e ⊆` one edge of `T⁺`; same for
   `T⁻`. Any third triangle bordering `e` would fill part of `B⁺` or `B⁻`, already
   occupied ⇒ equals `T⁺` or `T⁻`. So `atomicMult e = 2` (even).
4. **Boundary case.** `m ∈ ∂S` ⇒ one half-disk is outside `S` ⇒ exactly one
   triangle ⇒ `atomicMult e = 1`.

Mathlib: `convexHull`, `segment`, `Wbtw`/`Sbtw`, `Convex.*`/half-plane separation,
`interior_convexHull` facts, `IsConnected`/`IsPreconnected`,
`volume_convexHull_triangle` (already in Chapter20, to rule out degenerate overlap).

## Rules (hard)

- NO effort cap. This is a hard geometry grind; grind it. The ONLY acceptable
  stop conditions are: (a) the mathematics is actually wrong (give the
  counterexample), or (b) a required Mathlib API genuinely does not exist (name
  the exact missing lemma and what you searched).
- NO faking: no `sorry`, no `axiom`, no `native_decide`, no trivially-true
  restatement, no weakening the statement, no moving the hard part into a
  hypothesis. Attack the sorry; do not bank a rewrapper.
- Report progress + the exact tactic chain that blocks (if any) to
  `HANDOFF/outbox/ch20-e2-reply.md`. Be precise: which lemma, which goal state.
