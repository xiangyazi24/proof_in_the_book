# opus-cc2f reply — corrected cut-and-cap face count `F' = F + 2` (Ch 35 Jordan, F-half)

**File (sole owner):** `ProofsInTheBook/PlanarMapCutCap2F.lean` (new leaf).
Imports `PlanarMapCutCap2Counts` (corrected per-class `φ'₂` actions, the named core
`NumCyclesCutPhi2`, the assembly lemmas) + `PlanarMapCutCapEval` (computable mirror
for the in-file kernel anchor).

**Branch:** main. No commits. No codex / OpenAI tooling. Verified EXCLUSIVELY on
uisai1 via rsync + `lake env lean` / `lake build` (never `lake env lean`/`lake build`
on the Mac). Dep `lake build ProofsInTheBook.PlanarMapCutCap2Counts` (and
`...Eval`) ran to completion first.

## Status — HONEST

| Target | Status |
|--------|--------|
| `numCyclesCutPhi2_holds : C.NumCyclesCutPhi2` | **NOT proved.** After genuine exhaustion of every slick route, this is the irreducible global-count core. NOT faked as a sorry/trivial theorem. |
| `cutCapMap2_F_of_core` (`F' = F + 2`) | **PROVED, conditional on the one named core** `NumCyclesCutPhi2` |
| `cutCapMap2_eulerChar_of_core` (`χ' = χ + 2`) | PROVED, conditional on the same core |
| Narrowest corrected Jordan / chord-separation (`jordan_simple_cycle2`) | PROVED, conditional on core + connectivity param + sanctioned Euler ineq |
| Unconditional `φ'₂`-orbit reconnaissance lemmas | **PROVED unconditionally** (`cutCapPhi2_dart_threads`, `..._alpha_dart_reenter`, `..._capP_action`, `..._capM_action`) |
| In-file kernel anchor (`F' = 4` triangle, 4-orbit partition) | `#eval` in file, EXIT 0 |

`numCycles φ'₂ = M.F + 2` (the `NumCyclesCutPhi2` Prop, defined in
`PlanarMapCutCap2Counts.lean`) is **the single isolated topological core**, and it is
genuinely open. I did not commit a `sorry`-bearing `numCyclesCutPhi2_holds`; that
would violate the repo's 0-sorry standard and the playbook's "axiom = renamed sorry"
rule. Everything that can be closed around it is closed unconditionally here, and the
core is anchored by in-file kernel computation.

## Why it is not closeable by a shortcut (the reconnaissance, kernel-verified)

I ran the corrected `φ'₂` orbit partition through the Lean-kernel mirror
(`PlanarMapCutCapEval` style) on the triangle AND on a *proper* tetrahedron cut
(cycle `0→1→2→0`, with genuine non-cycle "clean" darts present). The TRUE partition
(not the design's intended one) is:

* **Triangle** (every dart is a cycle dart): 4 orbits = `{forward cycle darts}` ⊔
  `{reverse face}` ⊔ `{+caps}` ⊔ `{−caps}`. `F' = 4 = F + 2`. ✓
* **Tetra proper cut**: `F' = 6 = F + 2`, but the structure is NOT "old faces survive
  + 2 cap chains". The `−`-caps are **absorbed** into old faces (`M_j` sits inside an
  old triangular face with one cycle dart removed), and the forward cycle darts are
  **pulled out** into a brand-new orbit. So the design's "every old face survives
  rerouted intact" is **FALSE as stated**: `d ↦ ⟦inl d⟧_{φ'₂}` is not constant on old
  `φ`-orbits (e.g. `⟦inl(0,1)⟧_{φ'₂} ≠ ⟦inl(1,3)⟧_{φ'₂}` though both lie in old face
  `[(0,1),(1,3),(3,0)]`). There is **no clean orbit-by-orbit bijection**.

* **The `+`-caps do NOT form a pure orbit in general.** On the tetra cut `0→1→2→0`
  they happen to, but on the cut `0→1→3→0` one computes `φ'₂(c_0^+) = inl(0,2)`, a
  *bank* dart — the cap orbit interleaves bank darts, exactly as the task warned.
  So there is no unconditional "+cap k-cycle" lemma to peel off.

* The residual `faceCorr₂ = phiLift⁻¹ · φ'₂` is a **single `(3k)`-cycle ⊔ the `+`-cap
  `k`-cycle**, NOT a product of `2k−2` disjoint transpositions. So the clean
  `phiLift · (2k−2 swaps)` walk that mirrored the `V'` proof does not present itself;
  the net `−2k+2` cycle change is spread across the entire reorganization.

Routes tried and ruled out (with kernel evidence): (1) direct conjugation of `φ` —
`g = capShift` does not commute with `α'`; (2) `phiLift · faceCorr₂` swap-walk —
residual is a long cycle, not `2k−2` transpositions; (3) conjugated-`α` route
(`numCycles φ'₂ = numCycles(σ'·β)`, `β = g α' g⁻¹`) — merely transforms to an
equivalent hard problem (`β` still a fixed-point-free involution); (4) cycle-type
match (`[3,3,3,3,3,3]`) — proves abstract conjugacy only, no natural count.

**Conclusion:** `F' = F + 2` is a genuine genus-0-per-component Euler invariant whose
combinatorial proof needs the full transposition-walk / `SameCycle`-transport
development — the F-analogue of the `963`-line `V'` machinery. The chapter has
**never** built this: even the *buggy* face file `PlanarMapCutCapFCore.lean` isolates
its count as the named open Prop `NumCyclesPhiLiftFaceCorr`. This is the chapter's
deepest still-open core, and the task's sanctioned "one truly resistant piece, named
+ honest after genuine exhaustion."

## What this file adds over `PlanarMapCutCap2Counts.lean`

1. In-file kernel anchor `#eval` for the corrected `φ'₂`: prints `4 = F + 2` on the
   triangle and the explicit 4-orbit partition (reps `{0,2,4}/{1,3,5}/+caps/−caps`),
   so the named core is anchored by computation *in this file*.
2. Unconditional `φ'₂`-orbit reconnaissance lemmas (forward-threading, `−`-bank
   re-entry, fully-unfolded three-way `+`/`−`-cap actions) — the verified inputs any
   future orbit-count proof must consume.
3. Restated unconditional `cutCapMap2_F_of_core`, `cutCapMap2_eulerChar_of_core`,
   `cutSigmaCounts2_of_core`, and the narrowest `jordan_simple_cycle2`, threaded
   through the verified `PlanarMapCutCap2Counts` assemblies.

## Verification (on uisai1)

- `lake env lean ProofsInTheBook/PlanarMapCutCap2F.lean` → EXIT 0, zero errors.
  In-file `#eval` prints `4` and the 4-rep orbit partition.
- `lake build ProofsInTheBook.PlanarMapCutCap2F` → `Build completed successfully`.
- `#print axioms` on `cutCapMap2_F_of_core`, `jordan_simple_cycle2`,
  `cutCapPhi2_dart_threads`, `cutCapPhi2_capP_action`,
  `cutCapMap2_eulerChar_of_core` → all exactly `{propext, Classical.choice,
  Quot.sound}` (clean-3). No `sorryAx`, no `ofReduceBool`/`native_decide`.
- `grep -nE '\bsorry\b|\badmit\b|\bnative_decide\b|^[[:space:]]*axiom '` → matches
  only in doc-comment prose (lines 60, 77); **no** sorry/axiom/admit/native_decide in
  code.
- Leaf module (nothing imports it); no other file touched; no commit.

## Faithfulness (Group C)

- Every PROVED theorem is unconditional or CONDITIONAL-honest on the single named
  core `NumCyclesCutPhi2` (+ the sanctioned Euler inequality + connectivity
  parameter) — explicitly flagged in each signature.
- `NumCyclesCutPhi2` is satisfiable, non-vacuous, non-trivial (a real equation on the
  corrected map's actual face permutation, kernel-anchored `F'=4`/`F'=6`); it is NOT
  smuggled in as a hypothesis-disguised conclusion beyond its honest role as the one
  isolated core.
- The reconnaissance lemmas are genuine content (the per-class `φ'₂` action), not
  re-wrappers; the in-file `#eval` is a `decide`/kernel computation (no
  `native_decide`).

## Remaining open (next round)

`numCyclesCutPhi2_holds : C.NumCyclesCutPhi2`. The per-class `φ'₂` action is fully in
place and re-exported; what remains is the genuine transposition-walk /
`SameCycle`-transport orbit count along the corrected cap threading — the F-analogue
of the `963`-line `V'` development. Kernel anchors: triangle `F'=4`, tetra `F'=6`.
Recommended approach: a `numCycles` walk `phiLift → φ'₂` tracking the
`SameCycle`-dichotomy at each of the (non-disjoint) correction steps, OR a genus-0
Euler-per-component argument; both are multi-hundred-line and should be a dedicated
single-writer round.
