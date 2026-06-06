# WitnessFinal.lean — CutBridgeWitness2 for the concrete chord∪arc cycle (Ch35)

## Status: COMPLETE. 0 sorry / 0 axiom / 0 admit / 0 native_decide. Axioms clean.

New file `ProofsInTheBook/WitnessFinal.lean` (462 lines). Imports `DartArc`,
`PlanarMapBridge`, `PlanarMapBridgeWitness` only. Verified EXCLUSIVELY on uisai1
(`lake env lean` → RC=0, **zero errors, zero warnings**; full `lake build
ProofsInTheBook.WitnessFinal` → **8456 jobs OK**). NEVER ran lake/lean on the Mac
(kernel-panic rule). Branch `main` throughout; no commit; no branch switch. No
codex/OpenAI tooling. Leaf file — nothing imports it; import graph + Audit.lean untouched
(one-file-one-writer). Dep oleans built clean first.

## The decisive result: `SidesReach2` is UNCONDITIONAL (the prior verdict was wrong)

The bwitness handoff (`opus-bwitness-reply.md`) declared `SidesReach2` "irreducibly an
isolated side-coherence core, not a finite σ-walk", arguing distinct forward cycle darts
`dart j`, `dart i` sit in **distinct σ'₂-cycles** and connect only via `M.Connected` —
making any derivation circular with Part A.

**That verdict was correct only at the bare `σ'₂` layer.** `SidesReach2` asks for
`cutReach2`, whose generators are `σ'₂.SameCycle ∨ α'-step` — i.e. the full `φ'₂`
reachability (`cutReach2_of_phi_step`). And the *corrected* `σ'₂` wiring threads the cycle
darts into one `φ'₂`-orbit. The two proven closed forms close it:

- `cutCapPhi2_dart`       : `φ'₂ (inl (dart i)) = inl (dart (nextIdx i))`  (THE FIX)
- `cutCapPhi2_alpha_dart` : `φ'₂ (inl (α dart i)) = inl (pDart i)`, and
  `pDart i = α (dart (prevIdx i))` (rfl).

A single `φ'₂`-step is one `α'` then one `σ'₂` — both `cutReach2` generators. Hence
`inl (dart i)` reaches `inl (dart (nextIdx i))` in one `cutReach2` step; iterating
`nextIdx` (a cyclic permutation of `Fin C.len`) connects every forward bank dart to the
reference. The `−` side threads backwards (`i → prevIdx i`) but still forms one connected
loop. So `SidesReach2` is a finite symbolic `φ'₂`-walk after all — **proved with no appeal
to `M.Connected`**.

### What was built (Task 1 — fully closed, unconditional)

- `cutReach2_dart_nextIdx` / `cutReach2_alphaDart_prevIdx` : the single thread steps.
- `nextIdx_iterate_val` / `prevIdx_iterate_val` : closed form `(a+m)%len`, `(a+m(len-1))%len`.
- `cutReach2_dart_nextIdx_iterate` / `cutReach2_alphaDart_prevIdx_iterate` : ℕ-induction lift.
- `cutReach2_dart_all` / `cutReach2_alphaDart_all` : any bank dart reaches any other
  (pick `m` to hit the target index; cyclic-modular arithmetic via `Nat.ModEq`).
- **`sidesReach2_concrete : ∀ C i, C.SidesReach2 i`** — total theorem, no hypotheses.

## Task 2 — `FragmentCompatible2`: the honest triangle-gate constructors

Per the bridge design (`CH35_BRIDGE_DESIGN.md` §6–§7) the no-teleport `SameFragment` data
is genuine *input* — it is FALSE to derive "entry/exit fragment of one old face are
connected" from a bare face sequence (a straddling face teleports the lift). I did not
fake it. What I built is the **finite triangle lever** that makes the gate data local and
the honest constructors that package it:

- `sameFragment_of_phi_edge` / `sameFragment_of_phi_edge'` : the atomic fact — a single
  `φ'₂`-edge inside an old face is a `SameFragment` step (the triangle's two non-cut gate
  darts joined by one φ'₂-edge; the third edge being the cut cycle edge — the avoiding order).
- `fragmentCompatible2_of_links` : assembles `FragmentCompatible2` from per-position
  triangle-gate `SameFragment` witnesses (start/mid/end links) + the two endpoint-face
  equalities. The design's Option C made concrete.
- `fragmentCompatible2_singleFace` : the `n = 0` single-triangle case (forward and reverse
  cycle darts in one fragment of one face).

The data still enters as input (it must, per the design), but now through clean,
non-vacuous constructors whose atomic step is a single triangle `φ'₂`-edge.

## Task 3 — assembly: the unconditional-Part-A chord separation

- `cutBridgeWitness2_concrete` : `CutBridgeWitness2 i` with `SidesReach2` discharged
  internally by `sidesReach2_concrete` — the **only** per-edge input is now the
  no-teleport fragment supplier.
- **`separates_final`** (`NearTriangulation`) : the assembled chord-separation theorem.
  Conclusion `data.Separates` — identical to `separates2_of_dartArc` — but with the
  `∀ i, CutBridgeWitness2 i` parameter REPLACED by the strictly weaker `hcompat` fragment
  supplier (the side-coherence half is gone, now a theorem). A genuine interface
  strengthening, not a weakening.

## Chapter 35 chord wall: remaining surface

With `SidesReach2` closed, the chord-wall residue is reduced to exactly:
1. **F-side seam steps** (`nonarc_step`/`revbank_step`/`offcycle_step`/`capP_step`/
   `capM_step`, the `Ls`/`factor`/`gen` decomposition) — chord-local, pinned to the chord
   caps' generator edges (SeamIncidence layer).
2. **Interior-dual fragment supplier** (`hcompat`) — the design's irreducible no-teleport
   input, now local to triangle faces via the constructors above.
3. **Deletion-side orientation data + f13–16 side-map assembly** — the named corrected face
   core `NumCyclesCutPhi2` (closing in parallel) and the standard sphere/Euler inputs
   (`hNT.sphere`, `chi_le`).

The side-coherence core (`SidesReach2`) that the bwitness layer had to leave open is no
longer on this list.

## Verification

- `lake env lean ProofsInTheBook/WitnessFinal.lean` → RC=0, no errors, no warnings.
- `lake build ProofsInTheBook.WitnessFinal` → Build completed successfully (8456 jobs).
- `grep -nE '\bsorry\b|\badmit\b|\bnative_decide\b|^axiom '` → none (only the doc line).
- `#print axioms` on `sidesReach2_concrete`, `cutReach2_dart_all`, `cutReach2_alphaDart_all`,
  `fragmentCompatible2_of_links`, `fragmentCompatible2_singleFace`,
  `cutBridgeWitness2_concrete`, `separates_final` → `[propext, Classical.choice,
  Quot.sound]` only.
- Non-vacuity examples confirm `sidesReach2_concrete` is a total no-hypothesis theorem and
  the thread step is a genuine (non-reflexive) `cutReach2` step.
- Branch `main`; file untracked; no commit; no other file touched.

## No isolated resistant gate left as sorry/axiom

Everything dispatched compiled. No single resistant case required isolation; the modular
arithmetic for the reverse `prevIdx` walk was the only real friction and was closed via
`Nat.ModEq` cancellation.
