# Reply: PlanarMapBridge.lean — the two-layer fragment bridge for the CORRECTED map (Ch35 Part B)

**Status:** new file `ProofsInTheBook/PlanarMapBridge.lean` (797 lines) created, compiles
clean, all headline theorems depend on `[propext, Classical.choice, Quot.sound]` only.
Branch `main`; file untracked; no commit. Targets the **corrected** `cutCapMap2`
(`PlanarMapCutCapSigma2.lean`), not the buggy `cutCapMap`. Implements
`HANDOFF/CH35_BRIDGE_DESIGN.md` in full.

## What is implemented (0 sorry/axiom/admit/native_decide)

### Layer 0 — corrected-map reachability calculus `cutReach2`
Ported from cccon to `cutCapMap2`. Since `cutCapMap2.α = cutAlphaPerm` is **unchanged**,
all `α'`-bridges transfer verbatim; only `σ'₂` differs (and its three-way divert shape
`cutSigma2_inl_cases` matches). Provided: `cutReach2_{rfl,trans,symm,of_sigma,of_alpha,
of_phi_step,of_phi_pow,of_phi_sameCycle}`, `cutReach2_uncut_bridge`, `cutReach2_cap{P,M}`,
and the corrected forward step-lifts `cutReach2_sigma_{clean,divertPlus,divertMinus}`.
**The corrected `+`-cap diverts into the *previous* cap `c_{prevIdx j}^+`** (the σ'₂ fix);
that cap still `α'`-attaches to a `+`-bank dart, so it still reaches a bank — the
side-coherence core `SidesReach2` absorbs the `prevIdx` shift (this is the one place the
proof differs from the buggy map).

### Part A — `reachesBank2_of_connected` (fully proved)
Backward induction on an `M`-`dartStep` walk to `dart i` (mirroring the dps skeleton),
ported to the corrected map: every cut-dart of `cutCapMap2` reaches a bank of `e_i`, from
`M.Connected` + `SidesReach2`. Plus the connectivity reduction
`cutCapMap2_connected_of_reachesBank_of_bridge` (Part A + bridge ⇒ `(cutCapMap2).Connected`).

### Layer 1 — the bridge (design §1–§4)
- Fragment formalism: `SurvivingFaceStep` (the φ'₂-internal intra-face adjacency, the
  *only* safe one), `SameFragment` (its `ReflTransGen`), with `survivingFaceStep_symm`,
  `sameFragment_{symm,trans}`. Core lemmas `cutReach2_of_survivingFaceStep` and
  `cutReach2_of_sameFragment` ("same fragment ⇒ cut-connected" — never "same old face").
- Uncut gates: `cutAlpha2_old_of_not_cycle`, `cutReach2_across_uncut_dual_gate`.
- `FragmentDualPath2` / `…BetweenCycleSides` structures with the no-teleport
  `exit_sameFrag`/`entry_sameFrag` fields baked in (one fragment per position).
- `banks_connected2_of_fragment_dual_path` : a fragment-level dual path between the two
  sides of `e_i` ⇒ the bridge `cutReach2 (inl (dart i)) (inl (α (dart i)))`. Proof by
  step lemma `fragmentDualPath2_step` (exit-fragment → uncut α'-gate → entry-fragment) +
  position induction `fragmentDualPath2_rep_connected`.

### Layer 2 — refinement (design §7, Option C)
- `OrdinaryDualPath2` (a bare face sequence with explicit crossing darts) +
  `FragmentCompatible2` (the no-teleport `SameFragment` data: start_link, mid_link,
  end_link, with `n = 0` handled via the `dite` endpoint).
- `fragmentDualPath2_of_ordinary` : refines the pair into a
  `FragmentDualPath2BetweenCycleSides`, choosing `rep 0 := dart i`, `rep (j+1) :=
  α (edge j)` (entry dart), so `entry_sameFrag` is reflexive and `exit_sameFrag` is
  exactly start/mid link. **This is where consecutive gates through the same old face are
  forced into the same fragment — supplied as input, never derived from the bare face
  sequence (the design's central correction).**

### Combined / discharge of the `hconn` parameter
- `banks_connected2_of_ordinary_dual_path`, `cutCapMap2_connected_of_{fragment,ordinary}
  _dual_path`.
- `CutBridgeWitness2` (per-edge: `SidesReach2` + "dual-reachable ⇒ a fragment path
  exists") and `cutCapMap2_connected_of_bridgeWitness`, which **exactly discharges the
  connectivity parameter of `jordan_simple_cycle2_walk`**:
  `∀ i, DualReachableAvoidingCycle … → (cutCapMap2).Connected`.
- `jordan_simple_cycle2_bridge` : the corrected Jordan lemma with that parameter
  discharged, conditional only on the named face core `NumCyclesCutPhi2` (ground in
  parallel), the per-edge fragment witnesses, `M.Connected`, `hchi`, and the sanctioned
  `chi_le`.

## Design fidelity / honest isolation

The bare `DualReachableAvoidingCycle` face sequence is, by the design, too weak to lift on
its own (a straddling old face teleports it). Accordingly the no-teleport content is taken
as **input** (the fragment-path / `FragmentCompatible2` data inside `CutBridgeWitness2`),
not faked. The forbidden statement "entry and exit fragment of one old face are connected"
is **never** proved; only "same fragment ⇒ cut-connected" is. The two residual inputs are
`SidesReach2` (a finite cycle-bank `cutReach2` fact, the Part-A driver) and the per-edge
fragment witness — both concrete, neither mentioning `Connected`.

## Verification

- Dep build (uisai1): `lake build ProofsInTheBook.PlanarMapCutCap2FWalk
  ProofsInTheBook.PlanarMapDualPathSep` → 8444 jobs OK; then `lake build
  ProofsInTheBook.PlanarMapBridge` → 8445 jobs OK (7.9 s).
- `lake env lean PlanarMapBridge.lean` → no errors, no warnings.
- `grep -nE '\bsorry\b|\badmit\b|\bnative_decide\b|^axiom '` → none (only the doc line).
- `#print axioms` on `banks_connected2_of_fragment_dual_path`, `fragmentDualPath2_of_ordinary`,
  `banks_connected2_of_ordinary_dual_path`, `cutCapMap2_connected_of_bridgeWitness`,
  `reachesBank2_of_connected`, `jordan_simple_cycle2_bridge` → `[propext, Classical.choice,
  Quot.sound]` only.
- Local: never ran lake (kernel-panic rule); verified exclusively via rsync→uisai1.
- Branch `main`; `PlanarMapBridge.lean` untracked; no other file touched; no commit.

## No isolated resistant joint

Every design lemma closed faithfully; no joint was left as an axiom or `sorry`. The two
named *inputs* (`NumCyclesCutPhi2`, `CutBridgeWitness2`) are the design's intended
hypotheses, not gaps in this file.
