# Ch13 ProperCrossPieceNoCollisionAtSup / SubarmIHContra — clean-close status

Session: Opus overnight, 2026-06-13. Goal: discharge the last Ch13 residue (`SubarmIHContra`
in `ZinanFFCT111.lean`, the `r<K<s` proper cross-collision case) → make
`spherical_arm_mono_final_ch13 : SphericalArmMonotone` unconditional.

## RESULT: reduced the ENTIRE residue to ONE classical planar lemma (all scaffolding built & verified)

`ProofsInTheBook/ZinanFFCT111.lean` now contains, ALL compiling (`lake build ProofsInTheBook.ZinanFFCT111`
succeeds; every new lemma below is `clean-3` except it transitively uses the single `sorry` in the nut):

1. `orientedDatum_sin_general`, `support_openNeg_sin_general` — general-triple ports of FFCT37's
   `joint_orientedDatum_eq` / `support_openNeg_eq_sin`:
   `sOrient a0 axis (rotS2 axis (-θ) tail) = ‖u‖‖w‖ · sin(sphAngle a0 axis tail + θ)`.  ✅ proven.
2. `angle_cap_of_rotated_support_nonneg` : strict original support + weak rotated support + `0≤θ≤π`
   ⟹ `θ + sphAngle a0 axis tail ≤ π`.  ✅ proven (sin(α+θ)≥0 ∧ α∈(0,π) ∧ θ∈[0,π] ⟹ α+θ≤π).
3. `weakCyclicTripleNonneg` : `WeakConvexSphPolygon P → i<j<k → 0 ≤ sOrient (P i)(P j)(P k)`
   — gnomonic transport (mirror of `cyclicTriplePos_of_planar`, weak version).  ✅ proven MODULO the nut.
4. `openedWBS_subarm_angle_cap` : `δ* + sphAngle (A r)(A K)(A s) ≤ π` for `r<K<s` (the subarm cap
   `endpt_openTail_interior_mono` needs).  ✅ proven from (2)+(3)+`supportStuckWBS_weakConvex`+
   `cut_diagonal_supports`.
5. `subarmIHContra_holds : SubarmIHContra`  ✅ proven from (4) + `endpt_openTail_interior_mono` +
   `intervalArm`/`strictConvex_subarm` + endpoint identification (`openTail_fixed`/`openTail_rot`) +
   strict no-repeat.
6. `spherical_arm_mono_final_ch13 : SphericalArmMonotone := spherical_arm_mono_final_ch13_v12 subarmIHContra_holds`.

So the WHOLE of Ch13 is now unconditional **except** the single residue:

```lean
theorem planarConvexDiagNonneg_holds : PlanarConvexDiagNonneg := by sorry   -- THE ONLY GAP
```
where (the WEAK analogue of the proven strict `PlanarConvexDiag.PlanarConvexDiagPos`):
```lean
def PlanarConvexDiagNonneg : Prop :=
  ∀ (n) [NeZero n] (h : E3) (_ : h ≠ 0) (f : Fin n → E3),
    (∀ i, ⟪h, f i⟫ = 1) → (∀ i j, 0 ≤ det3 (f i) (f (i+1)) (f j)) →
    ∀ i j k, i<j → j<k → 0 ≤ det3 (f i) (f j) (f k)
```
i.e. **a weakly convex planar polygon (all edges weakly support every vertex) has every increasing
triple non-negatively oriented.** A true, classical fact; the weak version of the repo's
`planarConvexDiagPos_holds`.

## TWO prior-session claims, ADJUDICATED

- "Subarm base angle EXCEEDS full base angle (α>β)": **CORRECT.** Verified with explicit geometry:
  the rays `A_K→A_{K±1}` (inner vertices, adjacent to the axis) fan *wider* (toward π, the
  straight-through direction) than `A_K→A_0`, `A_K→A_last` (outer endpoints). So
  `sphAngle(A_r,A_K,A_s) ≥ sphAngle(A_0,A_K,A_last)`. ⟹ the **monitored full base cap is NOT enough**;
  the subarm cap is a genuinely stronger constraint. (So the "α≤β shortcut" is FALSE — do not try it.)
- "The cap route is DEAD / the cap is false": **WRONG.** The cap `δ*+α ≤ π` IS TRUE. It holds because
  the opened arm at the support-stuck supremum is **weakly convex** (`supportStuckWBS_weakConvex`), so
  ALL its diagonals are `≥0` (weak cyclic triple), in particular the `(r,K,s)` diagonal
  `sOrient(A_r,A_K,rotS2(A_K,-δ*)A_s) = ‖·‖‖·‖ sin(α+δ*) ≥ 0` ⟹ `α+δ* ≤ π`. The prior session simply
  lacked the weak cyclic triple and mistook "not monitored / α>β" for "false".

## Why the nut is hard (and why NOT faked)

- The monitored WBS family only constrains **edge** supports `(c.1, c.1+1, c.1.2)` + slack + the
  **full** base cap `(0,K,last)`. The `(r,K,s)` subarm diagonal with `r<K-1` or `s>K+1` is NOT
  monitored → must come from the weak cyclic triple.
- The strict planar core `det3_diag_pos_nat` proves the STRICT version by Grassmann–Plücker division by
  an edge support `e_m`; **weakly this division fails when `e_m = 0`** (collinear/flat vertices).
- The single-apex weakening is **FALSE** (counterexample: `g0=O,g1=(1,0),g2=(-1,1),g3=(0,0),g4=(1,1)`
  satisfies apex-0 supports but has a negative diagonal; excluded only by edge `(1,2)`'s support). So the
  proof MUST use ALL edge supports.
- The degenerate (all-collinear-pivot) case reduces to a scalar-sign / vertex-ordering question that is
  exactly the **half-plane / total-turning `<π` (winding) bound** — pure local Plücker algebra cannot
  see it. This is genuinely the planar-convexity "Umlaufsatz-adjacent" content (cf. the repo's
  multi-file `PolygonUmlaufsatz`/`PolygonTurning`/`PolygonWindingNumber` development, which proves the
  analogous turning=±2π for `StrictSimplePolygon`).

This is a real, multi-hundred-line theorem, NOT a one-liner. Closing it with `sorry`/`axiom` would
violate the discipline; it is left as the single honest residue.

## Routes to finish the nut (for codex / next session)

`HANDOFF/outbox/ch13-weakdiag-spec.md` + `ProofsInTheBook/ScratchWeakDiag.lean` are set up to prove
`PlanarConvexDiagNonneg` in isolation (no FFCT111 edit needed; codex self-verifies with
`lake env lean ProofsInTheBook/ScratchWeakDiag.lean`). Once proven there, port the single theorem body
into `planarConvexDiagNonneg_holds` in FFCT111.

Recommended attack (in order):
1. **Oriented-angle / winding**: reduce the plane `⟪h,·⟫=1` to 2-D (`h^⊥`), use `Orientation.oangle`
   (Mathlib) for polar angle about `f_i`; edge supports ⟹ each vertex in a closed half-turn + monotone
   consecutive turning ⟹ `arg`-ordering ⟹ triples `≥0`. The repo already uses `Orientation.oangle` /
   `Real.Angle` in `PolygonTurning`/`PolygonUmlaufsatz` — reuse that idiom.
2. **det3 strong-induction with degenerate handling**: gap-induction, Plücker-divide when some pivot
   `e_m>0`; in the all-collinear pivot case prove the proportionality `det3(g_i,g_b,g_c)=λ·E(c)` with
   `λ≥0` from the run-ordering (the hard sub-step — needs the no-leave-and-return convexity fact).
3. **Leverage `PolygonUmlaufsatz`/`PolygonConvexVertex`** if a "convex ⟹ oriented" lemma can be
   connected (they are `StrictSimplePolygon`-based — connection is itself nontrivial).

DO NOT: use Filter.Tendsto on admissible sets / admissible-interval / MainPlusNR / α≤β shortcut.

## Build / verify
```
cd ~/repos/proof_in_the_book && export PATH="$HOME/.elan/bin:$PATH"
command lake build ProofsInTheBook.ZinanFFCT111 2>&1 | grep -iE "error|sorry|Build completed"
```
Currently: builds OK; one `sorry` at `planarConvexDiagNonneg_holds`. `#print axioms
spherical_arm_mono_final_ch13` shows `sorryAx` (from the nut) + the core 3. When the nut is closed,
re-check `#print axioms` = `{propext, Classical.choice, Quot.sound}` ⟹ Ch13 CLOSED.

## NOT committed
Working tree only (scaffolding + the 1 nut `sorry`). Committed state is unchanged (clean `d90a719`).
codex was rate-limited (resets 2026-06-18) so heavy-artillery dispatch on the nut was unavailable.
