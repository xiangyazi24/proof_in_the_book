# Bricard's condition — assembled in `ProofsInTheBook/Bricard.lean`

**Status: DONE. 0 sorry / 0 axiom / 0 admit. Verifies clean on uisai2. Axioms = core three only.**

## Verification (uisai2; never built locally — kernel-panic rule respected)

- Dep oleans built first: `lake build PearlClassification PearlLemma Chapter09 TetDihedral SectorSum TetPearls` → `Build completed successfully (8425 jobs)`.
- `ssh uisai2 'cd ~/repos/proof_in_the_book && lake env lean ProofsInTheBook/Bricard.lean'` → **no output (clean)**.
- `#print axioms` on all five headline results — each:
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `ofReduceBool`/`trustCompiler`, no custom axiom).
  Audited: `bricard_sigma_locationClass`, `bricard_condition_angleClassQ`, `bricard_condition_real`,
  `bricard_regularTet_cube_contradiction`, `bricardDoubleCount_nonvacuous`.
- `grep sorry/admit/axiom/native_decide` → only the docstring line "No `sorry`, `axiom`, or `admit`".
- 408 lines. I own only this NEW file; touched nothing else; stayed on `main`; no commits; no codex/OpenAI tooling.

## What the file proves (the book's Σ₁ = Σ₂ double count, pp. 57–58)

The dihedral angles at all pearls are summed **two ways**, exactly per the book:

**Evaluation (a) — by pearls (location), fully UNCONDITIONAL.**
- `Sigma S P := ∑_{p∈P} PearlAngleSum S p` — the book's Σ.
- `pearlAngleSum_eq_ext_add_piMult`: each pearl's angle sum `= pearlExtAngle + (pearlPiMult)·π`,
  read straight off the existing `PearlClassification.pearl_angle_sum_classification` trichotomy
  (external edge → external angle `α_e`; boundary facet → `π`; solid interior → `2π = 2·π`). The
  `π`/`2π` cases are folded into an **integer** multiplicity `pearlPiMult ∈ {0,1,2}`.
- `bricard_sigma_locationClass`: summing, `Σ = externalPart + (piMultTotal)·π` with
  `piMultTotal ∈ ℤ` — the book's `Σ₁ = m₁α₁+…+m_rα_r + k₁π`. The `m_e ≥ 1` multiplicities are
  realized by accumulating one external-angle summand per pearl on each external edge.

**Mod-ℚπ collapse — the bridge into Chapter09, UNCONDITIONAL.**
- `angleClassQ_sigma`: `angleClassQ Σ = angleClassQ (externalPart)` — the `k·π` term **vanishes mod ℚπ**
  via the proven `Chapter09.angleClassQ_int_mul_pi`. This is precisely the form `Chapter09`'s
  `angleClassQ`/Dehn layer consumes.

**Evaluation (b) + the double count — isolated geometric residue (design §8).**
- `structure BricardDoubleCount SP SQ` packages an equidecomposition's two-way count: `LocationData`
  on each side (evaluation (a)) plus the load-bearing field `sigma_match : Sigma SP = Sigma SQ`
  (book's "Σ₁ = Σ₂ by piece-matching": congruent pieces measure equal dihedral angles —
  `TetDihedral.dihedralAngle_mapIso`, reflections allowed — and the Pearl Lemma `pearl_lemma`
  gives equal pearl counts on matched edges). This single equality is the honestly-named 3D residue.

**Bricard's condition — UNCONDITIONAL given the certificate.**
- `bricard_condition_angleClassQ`: `angleClassQ(externalPart_P) = angleClassQ(externalPart_Q)`
  (Σ₁ ≡ Σ₂ mod ℚπ) — `∑ m_e α_e ≡ ∑ n_f β_f`, the kπ invisible. **The exact input the Dehn obstruction wants.**
- `bricard_condition_real`: raw form `externalPart_P = externalPart_Q + k·π`, `k = piMultTotal_Q − piMultTotal_P ∈ ℤ`
  (book's `k = k₂ − k₁`).

**Headline (regular tetrahedron vs cube) — UNCONDITIONAL given the certificate.**
- `externalPart_eq_card_mul` / `angleClassQ_cube_externalPart_eq_zero`: when every pearl sits on an
  external edge of one fixed angle, `externalPart = (#pearls)·α`; for the cube `α = π/2` it is `0 mod ℚπ`.
- `bricard_regularTet_cube_contradiction`: a `BricardDoubleCount` between a solid with all external
  angles `arccos(1/3)` (regular tet) and one with all `π/2` (cube), with at least one pearl on the
  tet side, yields **`False`** — because Bricard forces `(#pearls)·arccos(1/3) ≡ 0 mod ℚπ`, impossible
  by the proven `Chapter09.angleClassQ_arccos_one_third_ne_zero` (the smul of a nonzero ℚ-vector by a
  nonzero integer is nonzero). This is the formal Bricard contradiction solving Hilbert III.

## Faithfulness / non-vacuity audit (playbook §3.3, self-performed)

- **Not VACUOUS.** Building blocks proven inhabited: `emptySolidWithAngles`, `emptyLocationData`,
  `bricardDoubleCount_nonvacuous` (empty pearl sets, `Σ₁ = Σ₂` holds reflexively as `0 = 0`). Hence
  `bricard_condition_angleClassQ`/`_real` are operationally meaningful, not vacuously discharged
  (`bricard_condition_angleClassQ_empty` exhibits the conclusion genuinely produced as `0 = 0`).
- **Headline premise correctly unsatisfiable = the theorem, not a bug.** `bricard_regularTet_cube_contradiction`
  concludes `False`; its premise set MUST be unsatisfiable (that is Bricard's theorem). It would be a
  bug to inhabit *those* premises. The `Nonempty` premise does real work:
  `bricardDoubleCount_empty_Pset_not_nonempty` confirms the empty witness does not meet it.
- **Verdict: CONDITIONAL-honest.** The whole algebraic double count + Bricard condition + the headline
  contradiction are proven; the only external assumption is the named geometric residue
  `BricardDoubleCount.sigma_match` (Σ₁=Σ₂ under piece-matching), which the design (§8) and Chapter09's
  own frontier note flag as the unfinished 3D scissors-congruence geometry. No hidden weakening: the
  conclusion is stated exactly as Chapter09's `angleClassQ` layer consumes it.

## Wiring note (for whoever updates the import graph / Audit.lean — I did not touch them)
`Bricard.lean` imports `PearlClassification`, `PearlLemma`, `Chapter09`. To surface it, add it to the
library root and add `#print axioms ProofsInTheBook.Bricard.bricard_condition_angleClassQ` (et al.) to
`Audit.lean` (keeping Audit's own import list updated). Verified output is the core three axioms.
