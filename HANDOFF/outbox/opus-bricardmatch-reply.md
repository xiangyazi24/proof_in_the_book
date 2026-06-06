# `sigma_match` discharged by-pieces — `ProofsInTheBook/BricardMatch.lean`

**Status: DONE. 0 sorry / 0 axiom / 0 admit. Verifies clean on uisai2. Axioms = core three only.**

I own only the NEW file `ProofsInTheBook/BricardMatch.lean` (`import ProofsInTheBook.Bricard`). Stayed
on `main`; no commits; touched nothing else; no codex/OpenAI tooling; never built locally (kernel-panic
rule respected). 312 lines.

## Verification (uisai2)

- Dep oleans: `lake build ProofsInTheBook.Bricard` → 8426 jobs OK; then `lake build
  ProofsInTheBook.BricardMatch` → `Built ProofsInTheBook.BricardMatch`, 8427 jobs OK.
- `ssh uisai2 'lake env lean ProofsInTheBook/BricardMatch.lean'` → **no output (clean), exit 0**.
- `#print axioms` on all eight headline results → each `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`, no `ofReduceBool`/`trustCompiler`, no custom axiom):
  `Sigma_eq_incidenceSum`, `Sigma_eq_byEdge`, `IncidenceMatch.sigma_match`, `bricardDoubleCount_ofMatch`,
  `exists_bricardDoubleCount_of_inducesMatch`, `mapIso_edge_dihedralAngle_eq`, `incidenceMatch_empty`,
  `inducesIncidenceMatch_empty`.
- `grep sorry/admit/axiom/native_decide` → only the docstring line "No `sorry`, `axiom`, or `admit`".
  One `:= rfl` (`bricardDoubleCount_ofMatch_empty_sigma`) is a definitional sanity check, not a result.

## What the file proves (book's "Σ by pieces", Ch. 9 p. 57)

`Bricard.lean` had reduced everything to one opaque field `sigma_match : Sigma SP Pset = Sigma SQ Qset`.
This file discharges it from an equidecomposition via the book's second evaluation of `Σ`.

**Item 1 — the regrouping (UNCONDITIONAL, real new math).**
- `Incidences S P` — the finite set of incidence pairs `(pearl p, edge-occurrence E)` with `p ∈ P` and
  `E` incident along `p`. The index set of the by-pieces double count.
- `Sigma_eq_paddedSum` / `Sigma_eq_incidenceSum`: `Σ = ∑_{(p,E)∈Incidences} dihedralAngle E` — the
  pearl-indexed double sum `∑_p ∑_{E incident} angle` unfolded onto the incidence relation.
- `Sigma_eq_byEdge`: exchanging the order of summation (`Finset.sum_comm` on the padded form),
  `Σ = ∑_E (#pearls on E) · dihedralAngle E` — exactly the book's "an edge of a piece contributes its
  dihedral angle once per pearl lying on it." `pearlCountOnEdge P E` is the per-edge pearl multiplicity.

**Item 2 — the matched-decomposition certificate.**
- `structure IncidenceMatch SP SQ Pset Qset` — an **angle-preserving incidence bijection**: forward/
  backward maps on incidence pairs, two-sided inverse, and `angle_eq` (matched incidences carry equal
  dihedral angles). This is exactly what the book's by-pieces matching produces: equal angles on
  corresponding edges (isometry invariance) + equal pearl counts (Pearl Lemma, encoded as the
  bijection's fiberwise equinumerosity).
- `IncidenceMatch.sigma_match`: from such a bijection, `Σ₁ = Σ₂` — **proved** by `Finset.sum_bij'` on
  the `Sigma_eq_incidenceSum` form (the bijection identifies the two single sums summand-for-summand).
  This is the genuine new content discharging the residue.
- `mapIso_edge_dihedralAngle_eq`: anchors `angle_eq` in real geometry — mapping a piece by a Euclidean
  isometry (reflections allowed) preserves every edge's dihedral angle (`TetDihedral.dihedralAngle_mapIso`,
  proven upstream). The `angle_eq` field is not an arbitrary hypothesis; it is this invariance.

**Item 3 — the constructor + the matched-decomposition theorem.**
- `bricardDoubleCount_ofMatch Ldata Rdata M : BricardDoubleCount SP SQ` — builds a genuine
  `BricardDoubleCount`, discharging `sigma_match` via `M.sigma_match`. This makes the Bricard condition
  and the headline regular-tet-vs-cube contradiction in `Bricard.lean` consume a *matched
  decomposition* directly, instead of an opaque `Σ₁ = Σ₂`.
- `exists_bricardDoubleCount_of_inducesMatch`: an equidecomposition that induces a matching yields a
  `BricardDoubleCount` (hence Bricard's condition, via `Bricard.lean`).

## The single isolated 3D residue (named, honest)

`InducesIncidenceMatch Pset Qset (h : TetEquidecomp …) := Nonempty (IncidenceMatch …)` — the one
genuinely-3D joint: that a *raw* `TetEquidecomp` (which records only carrier-image equalities
`iso T '' T.carrier = (e T).carrier`) **induces** the angle-preserving incidence bijection. Building it
needs the vertex/edge correspondence extracted from carrier-image equality (an isometry mapping a tet
carrier onto a tet carrier maps extreme points → extreme points → vertices → edges) **plus** the
Pearl-Lemma pearl-count balance on corresponding edges. This is precisely the design's §8 residue
("one homogeneous system is enough") and mirrors `Bricard.lean`'s own isolation of `sigma_match`.
Everything else — regrouping, sum-over-bijection, the certificate assembly, the angle invariance — is
proved unconditionally.

## Faithfulness / non-vacuity audit (playbook §3.3, self-performed)

- **Regrouping (items 1) is fully unconditional** — no certificate hypotheses; it is the book's
  by-pieces identity, proved both as incidence-sum and edge-indexed (angle × count) forms.
- **`sigma_match` from a matching is real content**, not a re-wrapper: `Finset.sum_bij'` over the
  regrouped incidence sums, with the angle-preservation field consumed pointwise. The angle field is
  anchored in the proven `dihedralAngle_mapIso` (`mapIso_edge_dihedralAngle_eq`).
- **Not VACUOUS.** `IncidenceMatch`, `InducesIncidenceMatch`, and the constructor are exhibited
  inhabited on empty pearl sets (`incidenceMatch_empty`, `inducesIncidenceMatch_empty`,
  `bricardDoubleCount_ofMatch_empty_sigma`); `sigma_match` there genuinely produces `0 = 0`. The
  non-trivial (nonempty-pearl) instances are exactly what require the named geometric residue, and the
  headline in `Bricard.lean` already gates its contradiction on `Pset.Nonempty`.
- **Verdict: CONDITIONAL-honest.** The by-pieces regrouping is unconditional; `sigma_match` is proved
  from an angle-preserving incidence bijection; the sole remaining external input is the named residue
  `InducesIncidenceMatch` (TetEquidecomp ⇒ incidence matching), the genuinely-3D scissors-congruence
  joint flagged by the design. No hidden weakening; statements stated exactly as `Bricard.lean` consumes.

## Wiring note (for whoever updates the import graph / Audit.lean — I did not touch them)

`BricardMatch.lean` imports `ProofsInTheBook.Bricard`. To surface it, add it to the library root and add
`#print axioms ProofsInTheBook.Bricard.IncidenceMatch.sigma_match` (et al.) to `Audit.lean` (keeping
Audit's own import list updated). Verified output is the core three axioms.
