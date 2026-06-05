# Cut-and-cap surgery (Chapter 35 Jordan lemma) — reply

**File:** `ProofsInTheBook/PlanarMapCutCap.lean` (NEW, sole writer; no other file touched).
**Status:** compiles clean on uisai1 (`lake env lean` + full `lake build ProofsInTheBook.PlanarMapCutCap`, 8429 jobs OK). 0 sorry / 0 axiom / 0 admit / 0 native_decide. 632 lines.
**Axiom audit:** every headline theorem depends on exactly `{propext, Classical.choice, Quot.sound}`.

## Verification

```
rsync -az .../PlanarMapCutCap.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=...:$PATH && lake env lean ProofsInTheBook/PlanarMapCutCap.lean'   # no output = OK
ssh uisai1 '... lake build ProofsInTheBook.PlanarMapCutCap'   # Build completed successfully
# #print axioms on jordan_simple_cycle / edge_count / eulerChar_eq /
#   sphereChordSeparation_of_jordan / separates_of_jordan / cutAlpha_involutive /
#   cutAlpha_no_fixed  ->  all {propext, Classical.choice, Quot.sound}
```

## What is PROVED unconditionally (genuine new content)

1. **`SimplePrimalCycle`** (Task 1): directed-dart cycle, length `≥ 3` (rules out
   the digon/loop degeneracy faithfully for a simple-graph cycle; satisfiable in
   the application since chord+arc has length ≥ 3 — both boundary arcs of a chord
   have an internal vertex), `tail`-injective, consecutive incidence. Full cyclic
   index theory + the simplicity-derived disjointness/injectivity lemmas
   (`dart_inj`, `alpha_dart_inj`, `dart_ne_alpha_dart`, `dart_ne_alpha_self`).

2. **The new edge involution `cutAlpha`** (Task 2, the α half): new dart type
   `D ⊕ (Fin k ⊕ Fin k)` (2k fresh caps `c_i^+, c_i^-`); cycle classifier
   `cycleKind` with full characterization; **proved** fixed-point-free involution
   (`cutAlpha_involutive`, `cutAlpha_no_fixed`) as `cutAlphaPerm`. The re-pairing
   is exactly the design §3.1: `d_i ↦ c_i^+`, `α d_i ↦ c_i^-`, non-cycle darts
   keep `α`.

3. **`edge_count : E' = E + k`** (Task 3, edge part) — *a theorem*, not a
   hypothesis. From the fixed-point-free involution alone:
   `2·E(N) = |D|+2k = 2·E(M)+2k`.

4. **`eulerChar_eq : χ' = χ + 2`** (Task 4).

5. **`jordan_simple_cycle`** (Task 6): the `χ=4` vs `χ≤2` contradiction. Takes the
   Euler inequality as the explicit parameter `chi_le : N.Connected → N.eulerChar ≤ 2`
   (the cleanest conditional shape you specified).

6. **Chord application** (Task 7): the generic step/path lift
   `reachable_dualAvoidsCycle_of_chordSplitAdj` (a `ChordSplitAdj` edge — non-chord,
   non-boundary — is not a cycle edge when `C.edgeSet ⊆ {chord} ∪ boundary`), then
   `sphereChordSeparation_of_jordan` producing `NearTriangulation.SphereChordSeparation`,
   and `separates_of_jordan` wiring through the existing
   `ChordSplitData.separates_of_nearTriangulation` to the Chapter-35 target
   `data.Separates`.

## What is ISOLATED (honest, named, satisfiable — NOT faked)

The new **vertex rotation `σ'`** (bank-splitting at each cycle vertex via the two
σ-intervals at `p_i = α d_{i-1}`, `q_i = d_i`, with the `2k` caps spliced so the
caps form two new φ'-faces, one reversed — design §3.1) and the two count facts
that genuinely depend on it — **`V' = V + k`** (orbit splitting) and
**`F' = F + 2`** (φ'-orbit tracing at the seam) — plus the design §4
**connectivity lifting**, are bundled as the fields of the structure
`CutCapSurgery M C`:

```
structure CutCapSurgery (M : CombMap D) (C : SimplePrimalCycle M) where
  N : CombMap C.CutDart
  alpha_eq : N.α = C.cutAlphaPerm          -- α' is the PROVED construction
  vertex_count : N.V = M.V + C.len         -- design §3.2 (needs σ')
  face_count   : N.F = M.F + 2             -- design §3.2 (needs σ')
  connected_of_dual_path : ∀ i, Dual…Reachable… → N.Connected   -- design §4
```

This is the genus-0 combinatorial-Jordan core. It is **satisfiable / not vacuous**
— the genuine cut-and-cap map (which mathematically exists) instantiates every
field; in particular `alpha_eq` pins N's edge involution to the *already
constructed and verified* `cutAlpha`, so the bundle is not free to cheat on edges
(`edge_count` is then derived as a theorem). This isolation matches the repo's
established discipline (`PlanarMapSeparation.SphereChordSeparation`,
`ChordSplitData.SidesDisjoint`).

Why isolated, honestly: constructing `σ'` correctly requires first establishing
the bank decomposition (the σ-orbit at each cycle vertex splits at exactly `p_i,
q_i` into two contiguous intervals — itself a substantial lemma even with the
`ContiguousInterval` machinery), and the `F' = F + 2` count then requires tracing
φ' = σ'∘α' orbits across the seam. Under the hard environment constraint (no
local builds; each remote `lake env lean` is the only feedback loop), I judged
that committing a concrete-but-possibly-subtly-wrong `σ'` risked making the
count fields *unsatisfiable* (the playbook's worst failure mode: a vacuous
conditional theorem). Keeping `σ'`+counts as an abstract, satisfiable bundle is
the honest and safe encoding. The α half — which is fully independent of σ' — is
constructed and proved in full, and the edge count is discharged from it.

## Net

The entire pipeline Jordan-lemma → chord-separation type-checks and is faithful;
the only un-discharged mathematics is (a) the sanctioned `chi_le` parameter and
(b) the σ'-dependent V/F counts + connectivity, isolated as the satisfiable
`CutCapSurgery` bundle. Next step for full unconditionality: construct `σ'` (the
bank-split rotation) and prove `vertex_count` / `face_count` / `connected_of_dual_path`,
yielding `CutCapSurgery` for every simple primal cycle of a connected χ=2 map.
