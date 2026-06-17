# Ch13 B1 final wave — hemiStuck master brick (ZinanFFCT30)

**File:** `ProofsInTheBook/ZinanFFCT30.lean` (334 lines). Compiles 0 errors, 0 warnings, clean-3.
`#print axioms` on all three main results: `[propext, Classical.choice, Quot.sound]` only — no
`sorryAx`, no custom axioms, no `native_decide`.

## Inventory findings (settled FIRST, per honesty contract)

1. **The admissible set requires hemiMargins STRICTLY `> 0`** (`SphericalMonitoredSup`: `Monitored δ`
   is "all hemisphere constraints `> 0`"). At `δ*` closure gives only `≥ 0`. This is decisive: it is
   why a vanishing margin (`hemiMargin = 0`) genuinely breaks `h₀` as a hemisphere witness for the
   opened arm.

2. **`WeakConvexSphPolygon.open_hemisphere` requires STRICT `> 0`** (`SphericalSZInduction:79`), the
   SAME field as the strict class. So the weak outcome still needs SOME unit normal strict at every
   vertex — but not necessarily the fixed `h₀`.

3. **`reach_strictConvex_interior`** (SphericalMonitoredSup) builds full `StrictConvexSphArm` from
   strict supports + strict hemisphere `hhem`; the hemisphere is a *hypothesis*, **not derivable from
   supports** — grep found NO `hemisphere_of_supports`/`open_hemisphere` producer that takes only
   strict supports. So the "forget h₀, rebuild strictness from supports" route the design floated is
   **closed**: the hemisphere genuinely needs a margin or a tilt.

4. **The brick collapses to plumbing around an existing reduction.** `SphericalOpeningGlue` already has
   `weakConvex_of_supportStuck_of_hemiPos`: from weak supports (`≥ 0`), edge distinctness, and a strict
   hemisphere margin for SOME unit normal, it assembles `WeakConvexSphArm`. The sibling closed the
   *support-stuck* case down to `HemiMarginStrictPosAtSup` (h₀ stays strict). The genuinely-missing
   **hemi-stuck** case (h₀ touches the equator) is exactly where h₀ fails, so it needs a *different
   normal* — a tilt. That tilt construction is the new content; everything else reuses the sibling.

## Route taken

**(a) PERTURB THE HEMISPHERE** — the clean tilt route. Three sections:

- **§1 (axiom-free inner-product core).** `exists_perturbed_normal_of_tangent`: for finite
  `P : Fin m → E3`, base `h₀` with `⟪h₀,P i⟫ ≥ 0` everywhere, and a tangent `t` strictly positive
  against every equator vertex (`⟪h₀,P i⟫ = 0`), the tilt `h₀ + ε·t` is strictly positive at EVERY
  vertex for a single uniform `ε > 0` (per-index `ε i` via an explicit bound
  `⟪h₀,P i⟫/(1+|⟪t,P i⟫|)` off the equator, `ε = 1` on it; then `Finset.inf'`).
  `exists_unit_perturbed_normal_of_tangent` normalizes to `‖·‖ = 1` (the open_hemisphere field demands
  unit norm) — nonzero from `m > 0` and positivity, strictness scales by `‖·‖⁻¹ > 0`.

- **§2 (Z ⊆ tail).** `hemiMargin_eq_orig_of_le_axis` + `axis_lt_of_hemiMargin_zero`: a fixed vertex
  (`r.val ≤ K.val`) keeps its original margin `⟪h₀, A r⟫ > 0`, so the equator set lies strictly on the
  rotated tail. (Confirmed `h₀` enters `monitoredSup` as the FIXED original hemisphere witness, so
  fixed vertices are genuinely strict.) This is delivered as a clean supporting lemma; it is the
  structural fact the design flagged, available if the residue's downstream consumer wants it.

- **§3 (the dichotomy).** `hemiStuck_dichotomy_of_glue` (strongest generic-δ form) and
  `hemiStuck_forces_supportStuck_or_weakConvex` (the design's named `monitoredSup` wrapper). Split on
  whether a support vanishes: if yes → left disjunct; if no → all supports strict → edge distinctness
  (`openTail_edge_ne_of_strict`, the `i+2` argument from `reach_strictConvex_interior`) + the residue's
  tilt + §1 → strict unit normal `h'` → `weakConvex_of_supportStuck_of_hemiPos` →
  `WeakConvexSphArm`. The conclusion matches the prompt verbatim:
  `(∃ c, supportConstraint c δ* = 0) ∨ WeakConvexSphArm (openTail A K δ*)`.

## The ONE named residual

`EquatorTangentExists A K h₀ δ` : `∃ t, ∀ r, ⟪h₀, A' r⟫ = 0 → 0 < ⟪t, A' r⟫` — a tilt direction
strictly positive against the equator vertices (equivalently: the rotated-tail vertices the opening
pushed onto the `h₀`-equator lie strictly within an open half of the equator circle).

This is the honest irreducible geometric content. It is **non-vacuous**: `equatorTangentExists_base`
proves it at `δ = 0` (empty equator set, take `t = h₀`). The §2 structural lemmas (Z ⊆ tail,
fixed-vertex strictness) and the edge-distinctness lemma are all discharged unconditionally — the
residue is purely "the equator vertices admit a common positive tilt", nothing else.

**Note on the strongest form.** `hemiStuck_dichotomy_of_glue` is true *whether or not* a margin
actually vanishes — the precise mathematical content is that **hemi-stuck is harmless**: the only
obstruction to weak convexity is a vanishing support, given the tangent. The `monitoredSup` wrapper
keeps the design's `hhem` (hemi-stuck) and `hnorm`/`hhpos` hypotheses as context markers
(underscore-prefixed, since the dichotomy subsumes them); the load-bearing inputs are the closure
hypotheses + `EquatorTangentExists`.

## Downstream wiring (not done here — sibling/master territory)

`HemiMarginStrictPosAtSup` (the support-stuck residue in SphericalOpeningGlue) and
`EquatorTangentExists` (this hemi-stuck residue) together are exactly what
`InteriorOpeningGlue` clause (iii) needs to be fully discharged: a `Stuck` supremum is either
support-stuck (→ sibling's route) or hemi-stuck (→ this brick), and both now reduce to a single
geometric tilt/positivity fact. No file other than ZinanFFCT30.lean was touched.
