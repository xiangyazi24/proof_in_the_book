# Satisfiability (non-vacuity) audit — playbook §3.3 reinforcement

**Why:** `#print axioms` clean + build green does NOT certify non-vacuity. A headline
theorem `(h : STRUCT) → Goal` is *vacuous* (proves nothing) if `STRUCT` is uninhabited.
This is invisible to every mechanical check. Demonstrated live: Ch35's `NearTriangulation`
was provably empty (a self-contradictory `↔` field), silently making the headline
five-colour theorem vacuous. Found + fixed 2026-06-15 (commit 7998ab7).

## The reinforced procedure (per headline premise structure)

1. **Enumerate** every headline theorem's premise structure(s) (the things it's conditional on).
2. **Emptiness probe** — the only reliable Ch35-class detector: actively attempt to prove
   `STRUCT → False`, building it on uisai2. NOT greppable; requires reading the field
   semantics (esp. `↔` fields, heavily-coupled bundles). If it succeeds ⇒ RED (real vacuity).
3. **Positive witness** — if not provably empty, exhibit a concrete inhabitant (`Nonempty STRUCT`)
   ⇒ GREEN; or confirm it is openly documented as an out-of-scope input ⇒ YELLOW (honest conditional).
4. **Labeling rule** — no theorem conditional on an un-inhabited STRUCT may be labelled
   "UNCONDITIONAL"/"CLOSED" without either a GREEN witness or an explicit YELLOW "honestly-open" tag.
5. **Independence** (§3.3): the orchestrator/author cannot be the sole auditor. RED/uncertain
   verdicts must be confirmed by an independent cold engine attempting the refutation.

## Scope (triaged): only structure-premise chapters are vacuity-capable

Concrete-statement headlines (most number-theory/combinatorics chapters) cannot be vacuous this
way. Vacuity-capable (define certificate/residue/realization/assembly premises): **Ch09, Ch11,
Ch13, Ch14, Ch16, Ch20, Ch22Gurvits, Ch30, Ch39Tucker, and the Zinan campaigns Ch35 / Ch36 / FFCT.**

## Ledger (status 2026-06-15 — source-level pass COMPLETE over vacuity-capable set)

| Chapter | Headline premise | Verdict | Evidence / notes |
|---|---|---|---|
| **Ch35** | `NearTriangulation` | **RED → FIXED** | was provably empty (self-contradictory `↔` field); fixed @7998ab7, build green. Still want a GREEN positive witness to fully close. |
| **Ch13** | `ConvexPolytopeRealization` (top); `CauchyMarkedTriangulatedSphere`, `CauchyArmVertex` (mid) | **YELLOW** | NOT provably empty (no `→False`; positive geometric data; degenerate P=Q inhabits). Arm lemma `spherical_arm_mono_final_ch13` unconditional+faithful+clean-3. Open part = ℝ³ realization (documented out-of-scope). FFCT57 `Ch13Residues` = superseded dead scaffolding. "UNCONDITIONAL/CLOSED" labels overstate → "closed mod ℝ³ realization". |
| **Ch14** | `PerlesFacetSeparationData` + `FixedCoordinateCompletions`/antipodal-free | **YELLOW** | sharp `2^d` bound (`chapter14_sharp_of_*`, Chapter14.lean:3028/3043) openly conditional; docstring itself says "the unproved frontier is deriving this … from the raw touching-simplex geometry". Honest conditional, not hidden vacuity. |
| **Ch20** | `RealEqualAreaUnitSquareTriangulation` | **GREEN** | Monsky `not_odd_size` (Chapter20.lean:2401). Structure has an EXPLICIT inhabitant — the diagonal-split `RealEqualAreaUnitSquareTriangulation (Fin 4) 2` (the file's own "non-vacuity check"). |
| **Ch16** | `KahnKalaiCertificate` | **GREEN** | headline `not_borsukConjecture_iff_exists_certificate` (Chapter16.lean:2666) is an IFF (logically cannot be vacuous); certificate has real constructors (`ofPrimeFranklWilsonSquaredConfiguration` …) + per-dim emptiness reasoning (`isEmpty_zero`). |
| **Ch36** | `TriangulatedPolygon` | **GREEN** | `chapter36_artgallery_combinatorial` (Chapter36.lean:297). Premise has explicit inhabitants `unitTriangle`/`unitQuadrilateral`/`unitPentagonFan` (Chapter36.lean:371-408). NB: the `ZinanCh36*` topology cluster is SEPARATE from this headline (possibly dead scaffolding). |
| Ch09 | — (concrete) | **GREEN** | `chapter09 : unitCubeDehnInvariantQ ≠ regularTetrahedronDehnInvariantQ` — concrete inequality, no structure premise. |
| Ch11 | — (concrete) | **GREEN** | `chapter11 (points : Finset Point2) …` — Ungar direction bound, concrete. |
| Ch22Gurvits | — (concrete) | **GREEN** | `chapter22_unconditional (A : doublyStochastic)` — Van der Waerden permanent bound, concrete unconditional. |
| Ch30 | — (concrete) | **GREEN** | `allOnesPathSystem_chapter30` — concrete LGV determinant identity. |
| Ch39Tucker | — (concrete) | **GREEN** | `chapter39_unconditional (hk : 1≤k)(hn : 2k≤n)` — concrete nat hypotheses, unconditional. |

**Verdict of the pass:** across all vacuity-capable chapters, **only Ch35 had a genuine hidden vacuity** (now fixed). Remaining conditionals (Ch13 realization, Ch14 antipodal-free) are HONEST, openly-documented out-of-scope frontiers — not hidden self-contradictions. Several chapters ship explicit positive witnesses (Ch20, Ch36). Concrete-statement headlines (Ch09/11/16/22/30/39) are not vacuity-capable.

**Independence caveat (§3.3):** this pass was done by the orchestrator (not an independent cold engine). GREEN-with-cited-witness and YELLOW-self-documented verdicts are objectively checkable from the cited file:line. The RED-candidate hunt (attempting `→False` on each structure's fields) surfaced no new self-contradiction, but an independent cold re-pass on the structure fields — esp. `PerlesFacetSeparationData` (Ch14) and the Ch13 spherical/realization ecosystem — would harden the result.

## Cleanup debt surfaced

- Dead vacuous scaffolding (FFCT57 `Ch13Residues`, the v1–v12 arm-lemma chain) clutters the tree
  and creates false vacuity alarms. Should be marked dead or removed.
- Over-claim labels ("UNCONDITIONAL", "CLOSED") on structure-conditional theorems should be requalified.
