# Reply: TetDihedral.lean — dihedral-angle layer COMPLETE

**Status: DONE. 0 sorry / 0 axiom / 0 admit. Clean-3 axioms. Verified on uisai1.**

File: `ProofsInTheBook/TetDihedral.lean` (574 lines, new module).
Imports: `ProofsInTheBook.TetPearls` (base `Tet` API) + `ProofsInTheBook.Chapter09`
(reuses the concrete `regularTetrahedronVertex` coordinate model and its dot-product facts;
no namespace collision — this module lives in `ProofsInTheBook.TetDihedral`).

## What was implemented (all proved, no gaps)

1. **Definition.** `dihedralAngle (T : Tet) (i j : Fin 4) : ℝ` via the projection form requested:
   `projOut d x := x - (⟪x,d⟫/⟪d,d⟫)•d` (orthogonal-to-edge projection), edge direction
   `d := T.v j − T.v i`, base point `T.v i`, complementary pair `otherTwo i j` (the two indices
   ≠ i,j). `dihedralAngle := InnerProductGeometry.angle (projOut d (T.v k − T.v i)) (projOut d (T.v l − T.v i))`.
   `otherTwo` is an explicit reducible table (List.filter over `[0,1,2,3]`) so `fin_cases`/`decide`
   evaluate it.

2. **Nonvanishing + strict bounds.** The crux is `not_projOut_parallel`: if `projOut d u = r • projOut d w`
   for ANY real `r`, the four vertices are affinely dependent (the weight function has coefficient `1`
   on `T.v k` summing to `0`), contradicting `T.affIndep` via `AffineIndependent.eq_zero_of_sum_eq_zero`.
   This single lemma (covering all signs of `r`) yields both:
   - `projOut_fst_ne_zero` / `projOut_snd_ne_zero` (take `r = 0`);
   - `dihedralAngle_mem_Ioo : 0 < dihedralAngle T i j < π` — angle = 0 or π would force
     parallelism, excluded. (Your antiparallel worry resolved exactly as conjectured: `u' = −c·w'`
     IS an affine dependence with coefficient sum 0.) Convenience: `dihedralAngle_pos`,
     `dihedralAngle_lt_pi`.

3. **Symmetry / well-definedness.** `dihedralAngle_comm (hij : i ≠ j) : dihedralAngle T i j = dihedralAngle T j i`.
   Uses `projOut_neg_left` (projection onto the line is `d ↦ −d` invariant) and
   `projOut_sub_smul_self` (base-point shift along the edge is killed by `projOut`, since
   `projOut d d = 0`).

4. **Isometry invariance (reflections allowed).** `Tet.mapIso (f : Pt3 ≃ᵢ Pt3) (T : Tet) : Tet`
   (vertices `f ∘ T.v`; affine independence preserved via `f.toRealAffineIsometryEquiv` +
   `AffineEquiv.affineIndependent_iff`). `dihedralAngle_mapIso : dihedralAngle (Tet.mapIso f T) i j = dihedralAngle T i j`,
   proved through the Mazur–Ulam linear isometry `g := f.toRealLinearIsometryEquiv` (so
   `g (a−b) = f a − f b`), `projOut_linearIsometryEquiv`, and `LinearIsometry.angle_map`.

5. **Concrete values.**
   - `regularTet` (= Chapter09's coordinate regular tetrahedron). `regularTet_dihedralAngle (hij : i ≠ j) :
     dihedralAngle regularTet i j = Real.arccos (1/3)` for EVERY edge. The projection cosine reduces
     to rational arithmetic: ⟪d,d⟫=8, ⟪u,d⟫=⟪w,d⟫=4, ⟪u,w⟫=4, ⟪u,u⟫=⟪w,w⟫=8 ⟹
     ⟪U,W⟫=2, ‖U‖=‖W‖=√6, cos = 2/6 = 1/3 (helper `inner_projOut_projOut` gives the closed form;
     dot products reused from Chapter09). Verified numerically (all 6 edges) before formalizing.
   - `cornerTet` (vertices `0, e₀, e₁, e₂`; affine independence proved by pairing against basis
     points). `cornerTet_dihedralAngle_right (hj : j ≠ 0) : dihedralAngle cornerTet 0 j = π/2` for the
     three corner edges — proved via `inner_eq_zero_iff_angle_eq_pi_div_two` (projected opposite
     vertices are orthogonal), no norm computation. (The three hypotenuse-face edges are
     `arccos(1/√3)`; not needed for the cube instantiation, so not proved, per brief.)

## Verification

- `lake env lean ProofsInTheBook/TetDihedral.lean` → exit 0 (no errors, no warnings).
- `lake build ProofsInTheBook.TetDihedral` → "Build completed successfully (8421 jobs)".
- `#print axioms` on `dihedralAngle_mem_Ioo`, `dihedralAngle_comm`, `dihedralAngle_mapIso`,
  `regularTet_dihedralAngle`, `cornerTet_dihedralAngle_right`, `projOut_fst_ne_zero` →
  ALL `[propext, Classical.choice, Quot.sound]` (clean-3, no sorryAx / no custom / no native_decide).
- `grep` for `sorry|admit|axiom` → only the prose in the module docstring.

## Notes for downstream wiring

- No `Audit.lean` / library-root edits made (one file, one writer). To wire into the import graph
  and the repo-wide audit, add `import ProofsInTheBook.TetDihedral` where needed and a
  `#print axioms` line for these theorems in `Audit.lean`.
- `dihedralAngle` is the unoriented angle in [0,π], matching the Dehn-invariant angle convention.
  `regularTet_dihedralAngle` feeds directly into the existing `angleClassQ (arccos (1/3))` layer in
  Chapter09 (`regularTetrahedron_arccos_one_third_has_dihedral_cosine` uses the face-normal route;
  this module supplies the *projection-definition* dihedral angle and proves it equals the same
  `arccos(1/3)`, so they agree).
