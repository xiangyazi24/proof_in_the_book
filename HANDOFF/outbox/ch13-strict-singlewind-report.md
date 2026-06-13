# Ch13 strict single-wind certificate — report (`ZinanFFCT95`)

**File:** `ProofsInTheBook/ZinanFFCT95.lean` (imports `ZinanFFCT94`).
**Status:** compiles 0 errors on uisai2 (HEAD 59e6293). Clean-3 axioms
(`propext, Classical.choice, Quot.sound`) on **every** theorem — no `sorry`,
`admit`, `axiom`, or `native_decide`.

## What landed (verified, axiom-clean)

### Brick C — the structure
`GnomonicSingleWind {n} (P : Fin (n+1) → S2) : Type` exactly as designed:
fields `h, hnorm (‖h‖=1), hpos (∀ i, 0 < ⟪h, P i⟫), u, v`, and
`lifted : FFCT94.PlanarLiftedTurnSpan (fun i => gproj h (P i)) h u v`. It is
`Type`-valued and carries FFCT94's lifted certificate, matching FFCT94's
`Type`-valued `PlanarLiftedTurnSpan`.

### The orthonormal frame (the load-bearing geometric lemma)
- `orthoFrame_of_seed` : from any nonzero seed `s ⊥ h` (unit `h`),
  `(u, v) := (‖s‖⁻¹•s, cross h u)` is orthonormal and ⊥ `h`. Pure
  cross-product algebra: `⟪v,v⟫ = ‖cross h u‖² = ‖h‖²‖u‖² − ⟪h,u⟫² = 1`
  via the Lagrange identity `norm_sq_cross`.
- `exists_orthoFrame {h} (‖h‖=1)` : a uniform construction valid for **every**
  unit `h` (no parallel-axis case-split hole): one of `cross h e₀/e₁/e₂` is
  nonzero (else all coordinates of `h` vanish, contradicting `‖h‖=1`), feed it
  to `orthoFrame_of_seed`.

### Gnomonic-image facts for a strict arm
- `gnomonic_image_in_plane` : `⟪h, gproj h (A i)⟫ = 1` (FFCT92 `inner_gproj`).
- `gnomonic_image_edge_ne` : strict arm ⟹ `gproj h (A i) ≠ gproj h (A (i+1))`
  (FFCT92 `gproj_ne_of_short` + `edge_short`).

### Brick D-strict — the reduction
`strictConvexSphArm_gnomonicSingleWind` :
```
StrictPlanarChainLiftedTurnSpanExists →
  StrictConvexSphArm A → Nonempty (GnomonicSingleWind A)
```
Fully proves the hemisphere/frame/transport layer: pulls the open-hemisphere
normal `h` and frame `(u,v)`, projects gnomonically, and transports **both** the
weak edge supports (`0 ≤ det3 Q`) and the strict non-incident supports
(`0 < det3 Q`) from the spherical strict supports through the gnomonic sign
correspondence (`gnomonic_sign_correspondence` / `sOrient_pos_iff_planar_pos`),
plus the nondegenerate-edge facts. These planar facts are fed to the residue.

## The isolated residue (the real content)

`StrictPlanarChainLiftedTurnSpanExists : Prop` — a single named **planar**
proposition: every strictly convex open planar chain in a common affine plane
`⟨h,·⟩=1` with an orthonormal frame `(u,v) ⊥ h`, all directed edges weakly
supporting all vertices, all non-incident vertices strictly supported, all edges
nondegenerate, carries a `FFCT94.PlanarLiftedTurnSpan` — i.e. a lifted real turn
function `θ` with `turn_pos`, `turn_lt_pi`, and the decisive
`one_wind : θ N − θ 0 < 2π`.

This isolation follows the established repo convention (`ZinanFFCT92`'s
`PlanarClosedWeakStrictNoRepeat`, `SphericalGnomonic`'s `PlanarConvexDiagPos`):
the hemisphere/transport scaffold is unconditional, the genuinely-analytic core
is one explicit non-axiom `Prop`.

**Non-vacuity:** `FFCT94.witChain_certificate` exhibits an explicit strictly
convex planar chain that *does* carry such a lifted certificate (total turning
`π/4 < 2π`), so the residue is satisfiable, not vacuous. The design's §3.3
satisfiability note is therefore witnessed concretely.

## Precise remaining goal

The single open inequality is `one_wind : θ N − θ 0 < 2π` for the lifted turn
function of a strictly convex **open** planar chain in convex position — the
total turning of an open strictly-convex arc is strictly below one full turn.
Concretely, to discharge `StrictPlanarChainLiftedTurnSpanExists` one must:
1. express each edge `Q(m+1)−Q m` in the `(u,v)` plane as
   `ρ_m (cos θ_m • u + sin θ_m • v)`, `ρ_m = ‖edge‖ > 0` (nondegenerate);
2. define `θ` by accumulating the per-joint signed turn angles, each in `(0,π)`
   from `det2(e_m, e_{m+1}) > 0` (the planar shadow of the strict supports via
   the `det3→det2` positive-multiple identity) — giving `turn_pos`, `turn_lt_pi`
   and strict monotonicity by construction;
3. bound the telescoped total `θ N − θ 0 = Σ turns < 2π` using convex position
   (all vertices strictly left of every edge ⟹ edge directions strictly
   monotone and the open chain does not close). This last `< 2π` bound is the
   sole analytic content not yet formalized.

## Verify

```
scp .../ZinanFFCT95.lean uisai2:.../ProofsInTheBook/ &&
ssh uisai2 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH &&
  lake build ProofsInTheBook.ZinanFFCT94 &&
  lake env lean ProofsInTheBook/ZinanFFCT95.lean'
```
