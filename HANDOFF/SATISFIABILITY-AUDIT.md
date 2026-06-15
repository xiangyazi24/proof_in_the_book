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

## Ledger (status 2026-06-15)

| Chapter | Headline premise structure | Verdict | Notes |
|---|---|---|---|
| **Ch35** | `NearTriangulation` | **RED → fixed** | was provably empty; fixed @7998ab7. Needs a GREEN positive witness to fully close. |
| **Ch13** | `ConvexPolytopeRealization` (top); `CauchyMarkedTriangulatedSphere`, `CauchyArmVertex` (mid) | **YELLOW** | NOT provably empty (no `→False`; fields are positive geometric data; degenerate P=Q inhabits). Arm lemma `spherical_arm_mono_final_ch13` is unconditional+faithful+clean-3. Honest open part = ℝ³ realization (documented out-of-scope). FFCT57 `Ch13Residues` = superseded dead scaffolding (provably empty, but not consumed by headline). "UNCONDITIONAL/CLOSED" labels overstate; should read "closed mod ℝ³ realization". |
| Ch36 | `chapter36_artgallery_combinatorial` premise `h` | TODO | headline does NOT use NearTriangulation; combinatorial over `Finset (AbsTriangle n)`. Check `h`. |
| Ch09/11/14/16/20/22Gurvits/30/39Tucker | TODO | UNCHECKED | source-level emptiness pass pending. |

## Cleanup debt surfaced

- Dead vacuous scaffolding (FFCT57 `Ch13Residues`, the v1–v12 arm-lemma chain) clutters the tree
  and creates false vacuity alarms. Should be marked dead or removed.
- Over-claim labels ("UNCONDITIONAL", "CLOSED") on structure-conditional theorems should be requalified.
