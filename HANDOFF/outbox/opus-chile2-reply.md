# opus-chile2 reply — Euler inequality `chi ≤ 2` for connected combinatorial maps

## STATUS: DONE — fully proved, 0 sorry / 0 axiom, clean-3 axioms.

Target theorem delivered (exact repo names/types):

```lean
theorem ProofsInTheBook.PlanarMap.CombMap.chi_le_two_of_connected
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombMap D) (hconn : M.Connected) : M.eulerChar ≤ 2
```

`eulerChar : ℤ = V - E + F`, `Connected` = `∀ a b, Relation.ReflTransGen M.dartStep a b`,
all as defined in `PlanarMap.lean`. No extra hypotheses — fully end-to-end over all
connected combinatorial maps.

## Route taken: PURE PERMUTATION / ORBIT-COUNTING (no spanning trees, no surgery)

I did NOT follow the design's spanning-tree + leaf-induction + edge-insertion route
(that needs SimpleGraph spanning-tree API + face-permutation surgery through `freshMap`).
Instead the genus-zero bound is proved entirely by orbit counting on raw permutation
pairs, which needs zero new map constructions:

Work over raw pairs `(σ, α)` with `α*α = 1` (involution, **fixed points allowed**).
Set `V = #orbits σ`, `F = #orbits(σα)`, `Ehalf = (support α).card/2`,
`c = #components` of the dart relation `dartStepRel σ α := σ.SameCycle ∨ b = α a`.

Genus slack `g(σ,α) := 2c - V + Ehalf - F`. Prove `g ≥ 0` for ALL involution pairs by
**strong induction on `(support α).card`**. Inductive step deletes one α-transposition
`{a,b}` (replace `α` by `α' = α * swap a b`, which fixes a,b): `Ehalf` drops by 1, `V`
unchanged, `F` changes by ±1 (transposition cycle-count fact), `c` changes by 0 or +1.
A two-case split (whether a,b are in the same `(σ,α')`-component) keeps `g ≥ 0`.

Base case `α = 1`: `c = V`, `F = V`, `Ehalf = 0`, so `g = 0`.

For a genuine `CombMap` (fixed-point-free α): `Ehalf = E`; connectivity ⟹ `c = 1`;
hence `V - E + F ≤ 2c = 2`. (Empty dart set handled separately: χ = 0.)

## Two isolated cruxes dispatched to codex (gpt-5.5) on uisai1, both clean:

1. `ProofsInTheBook/PermTranspositionCycleCount.lean` (431 lines) — the transposition
   cycle-count fact. Public (root) theorems:
   - `numCycles_mul_swap_dichotomy : a≠b → numCycles(p*swap a b)=numCycles p+1 ∨ +1=numCycles p`
   - `numCycles_mul_swap_of_not_sameCycle : a≠b → ¬p.SameCycle a b → numCycles(p*swap a b)+1=numCycles p`
   Load-bearing: explicit `mergeRel` quotient bijection (merge direction), and a `sign`-parity
   argument (`numCycles ≡ support.card + cycleType.card`, swap flips sign) for the dichotomy.

2. `ProofsInTheBook/RelationComponentCount.lean` (299 lines) — abstract component count of a
   symmetric relation under adding one edge:
   - `numComp_addEdge_of_eqvGen : EqvGen r a b → numComp (addEdge r a b) = numComp r`
   - `numComp_addEdge_of_not_eqvGen : ¬EqvGen r a b → numComp (addEdge r a b) + 1 = numComp r`
   Load-bearing: `eqvGen_addEdge_iff` relational identity + a quotient-of-quotient pair-merge
   cardinality lemma.

I wrote the connective scaffolding in the main file myself: the `EqvGen`↔`ReflTransGen`
bridge for symmetric relations, the `cycleSetoid`↔`SameCycle.setoid` count bridge,
`Ehalf` bookkeeping, the pointwise identity `dartStepRel σ α = addEdge (dartStepRel σ α') a b`,
the involution-after-deletion lemma, the genus induction, and the final assembly.

## VERIFICATION (run on uisai1 per protocol — NO local lake build)

```
lake env lean ProofsInTheBook/PlanarMapEulerInequality.lean   # exit 0, 0 errors
grep sorry/admit/axiom/native_decide                          # none in any of the 3 files
#print axioms chi_le_two_of_connected
  → [propext, Classical.choice, Quot.sound]                   # clean-3, no sorryAx
#print axioms numCycles_mul_swap_dichotomy                    → clean-3
#print axioms numComp_addEdge_of_not_eqvGen                   → clean-3
```

## FILES (all NEW, all owned by this task)
- `ProofsInTheBook/PlanarMapEulerInequality.lean` (539 lines) — the target theorem + scaffolding
- `ProofsInTheBook/PermTranspositionCycleCount.lean` (431 lines) — transposition cycle-count crux
- `ProofsInTheBook/RelationComponentCount.lean` (299 lines) — edge-addition component-count crux

No existing repo files were modified. The downstream Jordan files (`PlanarMapCutCap`,
`jordan_simple_cycle_of_chi_two`, ...) can now `import ProofsInTheBook.PlanarMapEulerInequality`
and apply `chi_le_two_of_connected`.

Note: the repo root `ProofsInTheBook.lean` does not yet import these three modules (I do not
own it). Whoever wires the Jordan argument should add the import there (or it builds on-demand
when a downstream file imports it).
