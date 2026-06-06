# Ch35 chord-side σ-contiguity: the `keptPhi`-wrap residue is REFUTED at the
σ-rotation level; the correct residue is the post-splice `tracePhi` 2-cycle.
New file `ProofsInTheBook/ChordSigmaContig.lean`, RC=0, clean-3, no sorry/axiom.

## TL;DR (honest verdict: the proposed route is mathematically WRONG)

The spec / `opus-bigonwrap-reply.md` asked to discharge `ChordBigonWrap.bigon_wrap`
(`keptPhi d₂ = d₁`) by building a `FilteredRotation.ContiguousInterval` for vertex
`u`'s kept side-1 darts and applying `filteredRotation_iterate_eq_of_contiguous`.

**That route cannot work, because `keptPhi d₂ = d₁` is FALSE.**  I proved the
refutation unconditionally inside the kernel:

* `keptPhi d₂` (= `sideSigma₁ (sideAlpha₁ d₂)`) lives at vertex **`tail dart = u`**.
* `d₁ = M.φ dart` lives at vertex **`head dart = v`** (the OTHER chord endpoint).
* `u ≠ v` (the chord is a real edge / no loop).
* ⟹ `keptPhi d₂ ≠ d₁`  (`keptPhi_face₁Dart₂_ne_face₁Dart₁`).

The mechanism: `sideSigma₁ = filteredRotation M.σ keptDel₁`, whose underlying
action is a **power of `M.σ`** (`filteredRotation_apply_coe`).  A `σ`-power keeps
`tail` (the vertex / σ-orbit) fixed, so the filtered rotation NEVER leaves vertex
`u`.  `d₁` sits at `v`.  No `ContiguousInterval` for `u`'s rotation — no matter how
the kept darts are arranged — can make a vertex-`u` filtered step land on a
vertex-`v` dart.  The σ-contiguity route is the wrong residue shape.

This forces `ChordBigonWrap` and `ChordCapData` to be **vacuous** (their
`bigon_wrap`/`bigon_close` field is an unsatisfiable equation over the genuine
surgery darts): `chordBigonWrap_isEmpty`, `chordCapData_isEmpty`.

## Why the wrap is at the wrong layer (the geometry)

For the `M`-triangle `face₁ = {dart, φ dart, φ² dart}` over vertices `u,v,w`
(`dart : u→v`, `φ dart : v→w`, `φ² dart : w→u`):

* `keptPhi d₁ = d₂` (the PROVED easy half) is a single `σ`-step **at vertex `w`**:
  `α(φ dart) : w→v`, `σ` of it = `φ² dart : w→u`.  Self-consistent.
* `keptPhi d₂` is a `σ`-walk **at vertex `u`**: `α(φ² dart) : u→w`, first `σ`-step
  is `dart : u→v` (DELETED, skipped), all further steps stay at `u`.  The target
  `d₁ : v→w` is at `v`.  The pre-splice face permutation `keptPhi` continues the
  side face at `u` and never returns to `d₁`.

The bigon `{d₁, d₂}` is closed **only after the fresh chord edge is spliced in**:
`tracePhi = swap (ρ a₀) (ρ a₁) · keptPhi`, whose swap connects the two endpoints'
rotations through the spliced fresh chord darts at anchors `a₀ @ u`, `a₁ @ v`.  A
swap CAN carry a value from vertex `u` to vertex `v` — `keptPhi` alone cannot.  So
the genuine residue is the **post-splice `tracePhi` 2-cycle on `sideMap₁`**, not a
`keptPhi`-wrap.

## What this file proves (genuinely new, all UNCONDITIONAL where stated)

* `tail_pow_sigma`, `tail_filteredRotation` — the filtered rotation preserves the
  vertex (σ-orbit).  The core mechanism.
* `tail_alpha_phiSq_dart` — `tail (M.α (M.φ² dart)) = tail dart` (= `u`).
* `keptPhi_face₁Dart₂_tail` — `keptPhi d₂` is at vertex `tail dart = u`.
* `face₁Dart₁_tail` — `d₁ = M.φ dart` is at vertex `head dart = v`.
* `u_ne_v` — `tail dart ≠ head dart`.
* **`keptPhi_face₁Dart₂_ne_face₁Dart₁`** — `keptPhi d₂ ≠ d₁` (the refutation).
* `chordBigonWrap_isEmpty`, `chordCapData_isEmpty` — both residue structures vacuous.

## The CORRECT residue + the SAME downstream chain (bypassing the false wrap)

* **`SideTracePhiTwoCycle`** — the single named TRUE residue: the post-splice
  `tracePhi` 2-cycle on the actual `face₁` darts (`trace12 : tracePhi d₁ = d₂`,
  `trace21 : tracePhi d₂ = d₁`) + distinct chord-cap anchors + rep face +
  one-fresh indicator.  Non-vacuous (`SideTracePhiTwoCycle.mk'`): unlike the
  `keptPhi`-wrap, `tracePhi`'s swap crosses `u ↔ v`, so the equation is satisfiable.
* **`correctAnchorTwoCycle_ofTrace`** — `CorrectAnchorTwoCycle` built directly from
  the post-splice 2-cycle (via `correctAnchorTwoCycle_ofFace₁`), *not* via the false
  `keptPhi`-wrap / `tracePhi_twoCycle_of_bigon`.
* **`face₁_sideTriangle_ofTrace`**, **`contiguousInterval_ofTrace`** — the
  end-to-end `ContiguousInterval` drop-in, threading to
  `ChordSideReconstruction → chord_case_recursive → nearTriangulation_five_colorable`.
* `trace_discharge_eq`, `SideTracePhiTwoCycle.mk'` — §3.3 no-rewrapper /
  satisfiability certificates.

This re-routes the chord-side discharge through a residue that is **not refuted**,
restoring a faithful (still conditional) path to the headline.

## Impact on the prior chain (`ChordAnchorInst` / `ChordBigonWrap`)

`tracePhi_twoCycle_of_bigon` (in `ChordAnchorInst`) is still a TRUE pure-algebra
lemma, but it cannot be *applied* on the genuine darts, because its hypothesis
`keptPhi d₂ = d₁` is false (`chordCapData_isEmpty`).  So the prior
`correctAnchorTwoCycle_ofBigon`/`...ofWrap` discharge route is vacuous in practice.
`ChordSigmaContig.correctAnchorTwoCycle_ofTrace` is the replacement that goes
through the post-splice trace directly.  (I did NOT edit `ChordAnchorInst.lean` or
`ChordBigonWrap.lean` — one-writer rule; the refutation lives entirely in my file.)

## §3.3 self-audit

- **NOT an unconditional discharge.**  The chord-side discharge remains conditional
  on the geometric residue `SideTracePhiTwoCycle` (the post-splice `tracePhi`
  2-cycle), which the abstract `CombMap` does not synthesize.  No overclaim.
- **Honest correction, not fabrication.**  The prior round's residue shape
  (`keptPhi`-wrap) is PROVED false; I did not paper over it.  The new residue is the
  geometrically correct one (post-splice, crosses `u↔v`).
- **Non-vacuous.**  `SideTracePhiTwoCycle.mk'` inhabits the new residue from
  component data; the refutation `chordBigonWrap_isEmpty` shows the old one was the
  vacuous one.
- **Headline not regressed.**  No upstream file edited.
  `nearTriangulation_five_colorable` re-checked: clean-3
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, UNCHANGED (conditional on
  the `JordanOracle` parameter, as before).

## Verification (server uisai1, real olean chain)

- Dependency `lake build ProofsInTheBook.ChordBigonWrap` → Build completed
  successfully (8465 jobs).
- `lake env lean ProofsInTheBook/ChordSigmaContig.lean` → **RC = 0**, zero errors,
  zero warnings.  All **13** `#print axioms` results **clean-3
  `[propext, Classical.choice, Quot.sound]`**, zero `sorryAx`.
- `grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom '` → none in code (docstring
  only).
- `#print axioms ...nearTriangulation_five_colorable` → clean-3, no `sorryAx`,
  UNCHANGED.

## New file (owned, fresh; NOT wired into ProofsInTheBook.lean — one-writer rule)

`ProofsInTheBook/ChordSigmaContig.lean` — imports `ChordBigonWrap`.  13 audited
results.  Branch `main`; no commits; no branch switch; no codex/OpenAI tooling;
never ran lake/lean on the Mac (kernel-panic rule observed — verified exclusively
on uisai1).

## Precise residue going forward

The Chapter-35 chord-side wall is now **`SideTracePhiTwoCycle`**: the post-splice
`tracePhi` 2-cycle on `sideMap₁` (`tracePhi d₁ = d₂`, `tracePhi d₂ = d₁`).  This is
strictly the correct shape — it crosses the two chord endpoints `u, v` through the
spliced fresh chord edge, which the refuted `keptPhi`-wrap could not.  The remaining
geometric content is to produce this 2-cycle from the planar embedding (the order in
which the fresh chord dart re-enters the two endpoints' rotations relative to the
kept side-1 darts) — i.e. the genuine discrete-planarity (Jordan) datum, the same
single isolated input the whole campaign carries, now correctly located at the
post-splice `tracePhi` layer rather than the (vacuous) pre-splice `keptPhi` layer.
