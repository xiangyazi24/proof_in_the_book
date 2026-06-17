# Ch13 — the convergence wiring (ZinanFFCT54): final surviving surface

**File:** `ProofsInTheBook/ZinanFFCT54.lean` (NEW; imports only `ZinanFFCT52` + `ZinanFFCT53`).
**Status:** compiles 0 errors / 0 warnings; all **19** `#print axioms` report clean-3
(`[propext, Classical.choice, Quot.sound]` only — `backward_revArm_not_forward` is even cleaner,
`[propext, Quot.sound]`).  No `sorry`/`admit`/`axiom`/`native_decide`.
**Verify:** `scp … uisai2 && ssh uisai2 'lake env lean ProofsInTheBook/ZinanFFCT54.lean'` (FFCT52+53
oleans built first, BUILDEXIT=0).  Did NOT git commit.

This module wires FFCT52's reversal/interval suite into FFCT53's four surviving inputs
(`BackwardFoldCase`, `hivl`, `TailFoldBoundary`, `hsupply`) and reports, with full honesty about what
is genuinely derivable, the FINAL surviving surface.

## Job 1 — BackwardFoldCase: the reversal does NOT discharge it (honest finding)

**Verdict: the literal-reversal discharge is mathematically impossible; the case is excluded at the
real consumer instead.**

The fold betweenness `A i ∈ span≥0 {A (i+1), A j}` has the cut vertex's **successor** `A (i+1)` as a
span generator.  Under `revArm` (the index map `v ↦ n − v`) the successor becomes the cut vertex's
**predecessor**: the reversed cut `revArm A ⟨n−i⟩` has its generators at `⟨n−i−1⟩` (predecessor) and
`⟨n−j⟩` — **never** at the successor `⟨n−i+1⟩` the forward Prop demands.  So a backward fold is *not*
a forward fold on `(revArm A, revArm B)`, and re-applying FFCT53's forward discharge is impossible.
This matches the design's recorded warning (`ch13-ffctplus-discharge.md` §6: *"backward `j < i` needs
cyclic reindexing or should be excluded by the actual support-stuck normalizer"*).

What I DID land here (all clean-3, load-bearing):
- The genuine **reversal pair transports**: `endpt_revArm` (endpt is reversal-invariant, `sDist_comm`),
  `sameSides_revArm`, `jointLe_revArm`, `positiveJoints_revArm` (via FFCT52's `revArm_sideLen`/
  `revArm_jointAngle`).  These are exactly what a reversal discharge *would* consume.
- `backward_revArm_not_forward` — a lemma that **mechanically certifies** the index incompatibility
  (`n−i−1 ≠ (n−i)+1` and `n−i < n−j`), so the impossibility is checked, not just asserted in prose.
- **The operative fix:** `FoldedFlatCutTransportPlusForward` (the binder `i + 1 < j`, exactly the
  consumer's `StuckAtKData.hij1`) + `foldedFlatCutTransportPlusForward_holds`, which discharges the
  consumer's real need WITHOUT ever touching `BackwardFoldCase`.  The real consumer
  (`ZinanFFCT48.cut_step_from_stuckAtK_plus`) always supplies `i + 1 < j`, so `BackwardFoldCase` is
  **operationally dead** — it survives only at the level of the *general* Prop's binder shape.

## Job 2 — interval certs: A-side DISCHARGED via the row expansion, B-side is the genuine residue

**A side (weak ear `hAe`) — DISCHARGED unconditionally** (no named input):
In the `(0, n)` boundary-fold context the betweenness `A 0 ∈ span≥0 {A 1, A n}` gives (via FFCT23's
`far_fold_nondeg_datum_of_no_repeat`) the nondegenerate decomposition `a•A 1 + b•A n = A 0` with
`a, b > 0`.  The interval `[1..n]`'s wrap diagonal `(A n, A 1)` supports are then derivable by the
FFCT24-style det3 row expansion (`det3_rowExpand_wrap`):

`det3 (A n)(A 0)(A m) = a·det3 (A n)(A 1)(A m) + b·det3 (A n)(A n)(A m) = a·det3 (A n)(A 1)(A m)`

(the `b•A n` term dies, `det3 x x y = 0`), so `det3 (A n)(A 1)(A m) = (1/a)·det3 (A n)(A 0)(A m) ≥ 0`
since `a > 0` and the parent wrap-edge `(n, 0)` support gives `det3 (A n)(A 0)(A m) ≥ 0`.  Chain:
`intervalWrap_support_of_betweenness` → `intervalWrapData_of_betweenness` (with the wrap `ShortArc`
from NoNonadjacentRepeat + hemisphere, `intervalWrap_shortArc_of_parent`) → `weakEar_of_betweenness`
→ `weakEar_of_span` (end-to-end from the raw NNReal span membership, FULLY discharged).

**B side (strict ear `hBe`) — the genuine named residue `StrictDiagonalSupport`** (honesty contract's
predicted survivor):
`B` carries **no** betweenness (it is the comparison arm), so the A-side row expansion does not apply.
`B`'s interval-closure strictness needs the wrap diagonal `(B n, B 1)` to support every interior
vertex strictly — the classical convex-position fact (*a diagonal of a strictly convex polygon has all
other vertices strictly on one side*).  FFCT52 §4 confirmed the wrap diagonal is **not** a parent edge,
so `StrictConvexSphPolygon.strict_nonincident` does not supply it (it tests parent edges, not
diagonals).  Named cleanly as `StrictDiagonalSupport` (satisfiable, non-vacuous guard
`strictDiagonalSupport_conclusion_satisfiable`).  The rest of `IntervalWrapDataStrict` IS derived:
`intervalWrapDataStrict_of_diagonal` assembles the strict wrap data from the parent (the two diagonal
endpoints `v=0`/`v=n−1` give `sOrient = 0` by repeated-argument vanishing; interior vertices use the
residue) + the named residue; `strictEar_of_diagonal` then produces `hBe` via FFCT52's
`strictConvex_intervalArm_of_wrap`.

## Job 3 — TailFoldBoundary: confirmed genuine residue (row expansion does NOT shrink it)

The `(0, n-1)` betweenness `A 0 ∈ span≥0 {A 1, A ⟨n-1⟩}` is a fold at the *first* edge; it places
`A 0`, not the last vertex.  `TailFoldBoundary` forces the **last** vertex `A n` onto the ray
`A 0 → A ⟨n-1⟩` (`sDist (A 0)(A ⟨n-1⟩) = endpt A + sDist (A n)(A ⟨n-1⟩)`) — a metric collinearity of
`(A 0, A n, A ⟨n-1⟩)`.  The §2 row-expansion machinery produces *supports* (which side of a diagonal
vertices lie), NOT a metric collinearity of three specific vertices.  So the betweenness in hand does
not yield it: `TailFoldBoundary` is the genuine design §8 master residue (FFCT53's exposure stands;
`tailFoldBoundary_involves_last` records that it genuinely involves `A (Fin.last n)`).

## Job 4 — assembly: the final surviving surface

- `intervalCerts_of_betweenness_and_strictDiagonal` — supplies `hivl`'s `(hAe, hBe)` pair: A side
  discharged, B side = `StrictDiagonalSupport`.
- `foldedFlatCutTransportPlusForward_holds` — the consumer's real transport (no `BackwardFoldCase`),
  modulo `hivl` + `TailFoldBoundary`.
- `foldedFlatCutTransportPlusNR_of_forward` — reconstructs the full NR Prop from the forward transport
  + `BackwardFoldCase`, isolating `BackwardFoldCase` as the **only** extra input beyond forward.
- `cutReady_chain_complete` — threads everything into the original
  `ZinanFFCT18.FoldedFlatCutTransportPlus` (via FFCT53's bridge `foldedFlatCutTransportPlus_of_NR` +
  the no-repeat supply), documenting the final surface.

### FINAL SURVIVING SURFACE (everything else discharged)

1. **`StrictDiagonalSupport`** (B-side wrap diagonal) — the **genuine** new survivor.  The classical
   convex-position fact for the comparison arm; not banked in the substrate (true, clean, worth its own
   brick).  *This is the honesty-contract's predicted B-side survivor.*
2. **`TailFoldBoundary`** — the design §8 tail-fold master residue (forcing the last vertex onto the
   ray; genuinely beyond the `(0, n-1)` betweenness).
3. **`BackwardFoldCase`** — survives only on the *general* Prop binder; **operationally dead** (the
   real consumer's `StuckAtKData.hij1 : i + 1 < j` excludes it; the operative transport
   `foldedFlatCutTransportPlusForward_holds` is `BackwardFoldCase`-free).
4. **`hsupply`** (`NoNonadjacentRepeat` supply) — the FFCT25-route cost (satisfiable on injective arms,
   FFCT23 `noNonadjacentRepeat_of_injective`).

### What this wave eliminated from FFCT53's four inputs

- The A-side of `hivl` (weak ear `hAe`) is **no longer a named input** — discharged by the row
  expansion (`weakEar_of_span`).
- `BackwardFoldCase` is downgraded from "FFCT52-reversal-tax (next wave)" to "general-Prop-only,
  operationally dead" — the reversal route is proved impossible, the consumer-exclusion is the truth.

## Honesty audit (playbook §3.3)

Every new `Prop` carries a non-vacuity guard
(`foldedFlatCutTransportPlusForward_conclusion_satisfiable`,
`strictDiagonalSupport_conclusion_satisfiable`, `cutReady_chain_conclusion_satisfiable`).  No vacuous
statements: `StrictDiagonalSupport`'s conclusion is a genuine strict `0 < det3 …`; `TailFoldBoundary`'s
is a real metric collinearity; the transports conclude genuine `endpt A ≤ endpt B` order bounds.  The
reversal-impossibility is mechanically certified (`backward_revArm_not_forward`), not hand-waved — I
did **not** fake a reversal discharge of `BackwardFoldCase`.
