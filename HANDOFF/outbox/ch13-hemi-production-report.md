# Ch13 hemisphere-production kernel — WBS bricks 1–2 report

**File:** `ProofsInTheBook/ZinanFFCT44.lean` (395 lines, NEW; imports only `ProofsInTheBook.ZinanFFCT36`).
**Status:** compiles 0 errors / 0 warnings (modulo the harmless upstream `push_neg` deprecation note).
**Axioms:** all three public theorems are **clean-3** (`propext, Classical.choice, Quot.sound` only).
No `sorry`/`admit`/`axiom`/`native_decide`.

## Deliverables (design `ch13-wbs-family.md`)

1. **§4 kernel — `commonLine_collapse_forces_flat_joint`** (`hn : 2 ≤ n`, `hside`, `hallplanes`, `hjopen` ⟹ `False`).
   The meridian-pencil collapse, with the pole-vertex corner handled in full (see below).
2. **§3 brick 1 — `equatorTangentExists_of_weakSupports_jointOpen`** — weak (`≥ 0`) supports + open joints
   ⟹ `∃ t, ∀ r, ⟪h₀, P r⟫ = 0 → 0 < ⟪t, P r⟫` (the `EquatorTangentExists`-shaped conclusion).
3. **brick 2 — `openHemisphere_of_weakSupports_jointOpen`** — same hypotheses + weak hemisphere margins
   ⟹ `∃ h', ‖h'‖ = 1 ∧ ∀ r, 0 < ⟪h', P r⟫` (the §15.2 consumer shape).

## How it was built (reuse, not re-derivation)

* **Separation core reused from FFCT36** (`exists_inner_pos_of_zero_notMem_convexHull`,
  `det3_edge_centerSum`) — no Hahn-Banach/Riesz plumbing re-derived. The §3 proof is a `by_cases` on
  `0 ∈ convexHull ℝ Z`: outside ⟹ separation gives `t` directly; inside ⟹ the edge functional pushed
  through the convex combination forces a common edge-plane axis `z = P r₀` (positive-weight equator
  vertex), which is exactly the §4 kernel input ⟹ `False`.
* **§4 collapse** uses FFCT25 `lin_indep_span_of_det3_zero` (span extraction over the independent base
  pair `{z, apex}`), FFCT22 `coplanar_triple_det3_zero`, and FFCT21
  `sphAngle_eq_zero_or_pi_of_det3_zero` (flat-joint bridge) — the same machinery as FFCT22's
  `far_fold_tail_not_interior`.
* **Brick 2** feeds the §3 tangent into FFCT30 `exists_unit_perturbed_normal_of_tangent`.

## The §4 pole-vertex corner (the honesty-contract danger zone) — handled, NOT faked

The kernel produces ONE interior joint with a vanishing consecutive triple, then fires the flat-joint
bridge against `0 < joint < π`. The case split is exhaustive and every branch closes:

* **CASE (a) — some interior apex `P m` (m∈1..n-1) is non-pole** (`(P m :E3) ≠ ± z`): the two edges
  adjacent to the apex both contain the independent pair `{z, P m}`, so both planes equal
  `span{z, P m}`; all three consecutive vertices land in it ⟹ `det3 = 0` ⟹ flat joint.
* **CASE (b) — every interior apex is a pole `P m = ± z`**:
  - **n ≥ 3**: interior apexes at joints 0,1 are the ADJACENT vertices `P 1, P 2`; both `± z` forces the
    edge `(P 1, P 2)` equal (`P 1 = P 2`) or antipodal (`P 1 = -P 2`), BOTH excluded by `ShortArc`.
    (Resolved with NO joint needed — the pencil vacuity is sidestepped.)
  - **n = 2**: single interior apex `P 1` a pole; the pencil IS vacuous at the pole, so the **wrap edge**
    `i = 2` (`det3 (P 2) (P 0) z = 0`) is used: with `P 1 = ± z`, the cyclic identity
    `det3 (P 0)(P 1)(P 2) = ± det3 (P 2)(P 0) z = 0` collapses the single joint directly. This is the
    FFCT42-style cyclic-wrap trick; the n=2 corner the prompt flagged is **not vacuous and not residual**.

## Refutation-resistance / faithfulness guards

* **`hn : 2 ≤ n` is necessary, not gratuitous**: for `n ≤ 1` the interior-joint set `Fin (n-1)` is empty,
  `hjopen` is vacuous, and the statement is genuinely FALSE (a flat closed chain with a common axis
  exists). The bound is supplied by the consumers (`StrictConvexSphArm ⟹ 2 ≤ n`). Without it the kernel
  would be an unsatisfiable-premise impostor; with it, the hypotheses are satisfiable in shape and the
  contradiction is real geometric content (the open joints, not a degenerate premise).
* No hypothesis is the conclusion in disguise; no certificate-parameter packaging of the hard half.
* The §3 nonneg sign of each convex-combination term is index-keyed to `hsupp` exactly (incident
  indices ⟹ `det3` self-vanishing; non-incident ⟹ `hsupp ≥ 0`), faithful to the weak-support
  semantics — no silent strengthening to strict supports.

## Verify command

```
scp ~/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT44.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ \
  && ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT44.lean'
```

Not git-committed (per instructions). Wiring `ZinanFFCT44` into the import graph / `Audit.lean` is left
to the orchestrator. The §3/brick-2 theorems are stated on a generic closed chain `P`, ready to
instantiate at `P := openTail A (openingAxis k) (-(monitoredSupWBS …))` for `openHemisphere_at_WBS_sup`
(design §9) by the WBS sibling worker.
