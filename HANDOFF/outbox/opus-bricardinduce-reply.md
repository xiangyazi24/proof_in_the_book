# `InducesIncidenceMatch` backbone discharged — `ProofsInTheBook/BricardInduce.lean`

**Status: DONE. 0 sorry / 0 axiom / 0 admit. Verifies clean on uisai2. Axioms = core three only.**

I own only the NEW file `ProofsInTheBook/BricardInduce.lean` (`import ProofsInTheBook.BricardMatch`).
Stayed on `main`; no commits; touched nothing else; no codex/OpenAI tooling; never built locally
(kernel-panic rule respected); uisai2 used (uisai1 down). 587 lines.

## Verification (uisai2)

- Dep oleans: `lake build ProofsInTheBook.BricardMatch` (8427 jobs OK) then `lake build
  ProofsInTheBook.BricardInduce` → `Built ProofsInTheBook.BricardInduce`, **8428 jobs OK**.
- `ssh uisai2 'lake env lean ProofsInTheBook/BricardInduce.lean'` → **no output (clean), exit 0**.
- `#print axioms` on the nine headline results → each `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`, no `ofReduceBool`/`trustCompiler`, no custom axiom):
  `Tet.vertices_eq_extremePoints`, `iso_image_vertices`, `isoVertexPerm_apply`,
  `isoVertexPerm_dihedralAngle`, `iso_image_edgeSeg_carrier`, `pearlBalance_of_equalLengths`,
  `regularTet_cube_no_equidecomp`, `inducesIncidenceMatch_refl`, `incidenceMatch_id`.
- `grep sorry/admit/axiom/native_decide` → only two docstring lines; no real occurrence.

## What the file proves (the four task items)

**Item 1 — induced vertex permutation (real new math, the isolated-then-proved 3D fact).**
- `Tet.vertex_notMem_convexHull_others` — a vertex is **not** a convex combination of the other
  three (barycentric obstruction: a convex relation avoiding index `i` is an affine dependence with a
  `-1` coefficient at `i`, contradicting `affIndep`). Proved via `Finset.convexHull_eq` +
  `affIndep.eq_zero_of_sum_eq_zero`.
- `Tet.exists_barycentric` — `Fin 4`-indexed convex-coordinate form of carrier membership.
- `Tet.vertices_eq_extremePoints` : `extremePoints ℝ T.carrier = range T.v`. **This is the simplex
  fact Mathlib lists as the open TODO `AffineIndependent.convexIndependent`** — `⊆` is Mathlib's
  `extremePoints_convexHull_subset`; `⊇` is proved here via the open-segment characterization
  `mem_extremePoints` + barycentric uniqueness (`affIndep.eq_of_sum_eq_sum`). **Proved, not isolated.**
- `iso_image_extremePoints` — a Euclidean isometry (affine via Mazur–Ulam, `isoAffineMap`) carries
  extreme points to extreme points (open-segment transport; no Mathlib affine-equiv version exists,
  only the linear `image_extremePoints`).
- `iso_image_vertices` : `f '' range T.v = range U.v` from `f '' T.carrier = U.carrier`.
- `isoVertexPerm hf : Fin 4 ≃ Fin 4` with `isoVertexPerm_apply : f (T.v i) = U.v (π i)` — the
  induced vertex bijection (`Equiv.ofBijective` from injectivity on the finite `Fin 4`).

**Item 2 — edge correspondence + angle preservation (proved).**
- `iso_dist_vertices` : `dist (f (T.v i)) (f (T.v j)) = dist (T.v i) (T.v j)` (length/congruence).
- `iso_image_edgeSeg_carrier` : `f` maps `T`'s edge segment `{i,j}` onto `U`'s edge segment
  `{π i, π j}` (affine image of a segment, `image_segment`).
- `dihedralAngle_relabel` : permutation invariance of the dihedral angle (`W.v = Y.v ∘ σ` ⇒
  `dihedralAngle W i j = dihedralAngle Y (σ i) (σ j)`), via `otherTwo` complementary-set bookkeeping
  + `InnerProductGeometry.angle_comm` for the opposite-vertex swap.
- `isoVertexPerm_dihedralAngle` : `dihedralAngle U (π i) (π j) = dihedralAngle T i j` — the
  edge-by-edge angle preservation, combining `dihedralAngle_relabel` with the proven
  `TetDihedral.dihedralAngle_mapIso` (`U.v ∘ π = (mapIso f T).v`). **This is exactly the content the
  `IncidenceMatch.angle_eq` field demands.**

**Item 3 — Pearl-Lemma count balance from congruent edges (proved).**
- `pearlBalance_of_equalLengths` : given positive real edge lengths `len` and a matching `mt` with
  `len i = len (mt i)` (an isometry preserves length, so corresponding edges are congruent = **equal
  length**), `pearl_lemma` instantiated with the singleton-pair constraint system
  `({i}, {mt i})` returns a positive **integer** pearl assignment `m` with `m i = m (mt i)` on every
  matched pair. Equal individual lengths ⟹ each singleton-pair balance holds ⟹ matched pearl counts.

**Item 4 — assembly + headline.**
- `exists_bricardDoubleCount_of_inducesMatch'` — re-export: a `TetEquidecomp` inducing an incidence
  matching yields a `BricardDoubleCount` (through `BricardMatch`'s constructor).
- `regularTet_cube_no_equidecomp` — **the sharpest end-to-end statement.** From an equidecomposition
  inducing a matching on the chosen pearl sets, the regular-tet angle data (`arccos(1/3)`), the cube
  angle data (`π/2`), and `Pset.Nonempty`, derive `False`. Routes
  `exists_bricardDoubleCount_of_inducesMatch` → `bricardDoubleCount_ofMatch` →
  `bricard_regularTet_cube_contradiction`. The only non-algebraic input is the named residue
  `InducesIncidenceMatch` (whose angle content is the proven `isoVertexPerm_dihedralAngle`).

## The residue, named honestly (and why it cannot be proved *unconditionally* for arbitrary sets)

`InducesIncidenceMatch Pset Qset h := Nonempty (IncidenceMatch SP SQ Pset Qset)` is the one remaining
3D joint. It is consumed exactly once, as the design (§8) prescribes. I did **not** prove it
unconditionally for *arbitrary* `Pset, Qset`, and that is correct: for independently chosen pearl
sets (e.g. `|Pset|=1`, `|Qset|=2` with distinct incident angles) **no** angle-preserving incidence
bijection exists, so the predicate is genuinely *false* in general. The book's matching lives on the
*refined* decomposition's specific pearl sets; the count balance there is exactly `item 3`. What this
file delivers is the full **geometric backbone** that any honest construction of that matching feeds
on (vertex/edge/angle correspondence + count balance), plus the end-to-end assembly.

## Strengthened non-vacuity (playbook §3.3)

`BricardMatch` exhibited `IncidenceMatch` inhabited only on *empty* pearl sets. Here:
- `incidenceMatch_id S P` — the **identity** incidence matching of a solid with itself on **any**
  pearl set `P` (`angle_eq` is `rfl`); genuinely nonempty incidence sets.
- `tetEquidecomp_refl` — the reflexive equidecomposition.
- `inducesIncidenceMatch_refl S P` : `InducesIncidenceMatch P P (refl)` for **any** `P` (incl.
  `P.Nonempty`). So the conditional matching layer is non-vacuous beyond the empty witness.

## Faithfulness / non-vacuity audit (self-performed, §3.3)

- **Item 1 is the genuinely-3D fact, fully proved** — `vertices_eq_extremePoints` is the Mathlib-TODO
  simplex result, derived from affine independence (two barycentric arguments). No axiom; not a
  re-wrapper.
- **Item 2 angle preservation is real geometry** — anchored in the proven `dihedralAngle_mapIso` and a
  freshly-proved permutation-invariance lemma; `isoVertexPerm_dihedralAngle` is exactly the
  `angle_eq` content.
- **Item 3 is a faithful Pearl-Lemma instantiation** — singleton-pair constraints, equal lengths;
  hypothesis `len i = len (mt i)` is satisfiable (e.g. `mt = id`), not vacuous.
- **Item 4 headline is CONDITIONAL-honest** — premise set is *correctly* unsatisfiable (that is
  Bricard's theorem); gated on `Pset.Nonempty`; the one external input is the named residue
  `InducesIncidenceMatch`, whose satisfiability (on matchable pearl sets) is witnessed by
  `inducesIncidenceMatch_refl`.
- **Verdict: FAITHFUL** for items 1–3 (unconditional proven backbone) and **CONDITIONAL-honest** for
  item 4 (sole external input = the design's named 3D residue). No hidden weakening; statements as
  `BricardMatch`/`Bricard` consume them.

## Wiring note (for whoever updates the import graph / Audit.lean — I did not touch them)

`BricardInduce.lean` imports `ProofsInTheBook.BricardMatch`. To surface it, add it to the library root
and add `#print axioms ProofsInTheBook.Bricard.regularTet_cube_no_equidecomp` (et al.) to `Audit.lean`
(keeping Audit's own import list updated). Verified output is the core three axioms.
