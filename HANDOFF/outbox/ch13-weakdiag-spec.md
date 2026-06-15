# TASK: prove the WEAK planar convex-position diagonal nonnegativity primitive

## File (edit ONLY this file)
`/Users/huangx/repos/proof_in_the_book/ProofsInTheBook/ScratchWeakDiag.lean`

Replace the single `sorry` in `planarConvexDiagNonneg_holds` with a real proof.
STRICT: NO `sorry`, NO `axiom`, NO `admit`, NO `native_decide` (use `decide`/`rfl` only).
Self-verify with `lake env lean ProofsInTheBook/ScratchWeakDiag.lean` ONLY.
Do NOT run `lake build` (another writer is editing other files; `lake build` corrupts the shared cache).
`export PATH="$HOME/.elan/bin:$PATH"` first. cd to `/Users/huangx/repos/proof_in_the_book`.

## The statement
```lean
def PlanarConvexDiagNonneg : Prop :=
  ∀ (n : ℕ) [NeZero n] (h : E3) (_ : h ≠ 0) (f : Fin n → E3),
    (∀ i : Fin n, (⟪h, f i⟫ : ℝ) = 1) →                              -- all points in the plane ⟪h,·⟫ = 1
    (∀ i j : Fin n, 0 ≤ det3 (f i) (f (i + 1)) (f j)) →              -- EVERY edge weakly supports EVERY vertex
    ∀ i j k : Fin n, i < j → j < k → 0 ≤ det3 (f i) (f j) (f k)      -- every increasing triple weakly oriented
```
This is the weak (`0 ≤`) analogue of the PROVEN strict `ProofsInTheBook.PlanarConvexDiag.PlanarConvexDiagPos`
/ `planarConvexDiagPos_holds`. `E3`, `det3`, `ShortArc`, etc. live in `ProofsInTheBook.SphericalKernel`.
`⟪x,y⟫` is the real inner product (`open scoped RealInnerProductSpace`).

## Already proven & imported (reference / reuse them)
In `ProofsInTheBook.PlanarConvexDiag` (open it if helpful):
- `det3_apex_plucker (A E P M Q : E3) : det3 A P Q * det3 A E M = det3 A M Q * det3 A E P + det3 A P M * det3 A E Q`
  — the Grassmann–Plücker syzygy (pure `ring` identity). THE algebraic engine.
- `det3_cyclic (a b c : E3) : det3 a b c = det3 b c a`.
- `det3_diag_pos_nat` — the STRICT ℕ-indexed core (read its proof; it is the template):
  `(g : ℕ → E3) (i N) (hbase : ∀ t, i<t → t+1<N → 0 < det3 (g i)(g t)(g (t+1)))`
  `(hedge : ∀ t, i+1<t → t<N → 0 < det3 (g i)(g (i+1))(g t)) : ∀ q p, i<p → p<q → q<N → 0 < det3 (g i)(g p)(g q)`.
- `planarConvexDiagPos_holds : PlanarConvexDiagPos` — the strict headline; read it to see the Fin↔ℕ window
  conversion (lift `f : Fin n → E3` to `g : ℕ → E3` by `g t := f ⟨t % n, _⟩`, `fin_succ_val`, etc.).
`det3` is the explicit 3x3 determinant; `simp only [det3]; ring`/`nlinarith` close pure-coordinate goals.

## CRITICAL math facts (read before attempting)

1. **You MUST use ALL edge supports, not just one apex.** The single-apex weakening of `det3_diag_pos_nat`
   (only `hbase`/`hedge` from apex `i`) is **FALSE**. Counterexample (apex `g0=(0,0,?)`):
   `g0=O, g1=(1,0), g2=(-1,1), g3=(0,0), g4=(1,1)` (2-D coords) satisfies apex-0 `hbase`/`hedge` (all `0 ≤`)
   but `det3(g0,g2,g4) < 0`. It is excluded only because edge `(g1,g2)` does NOT weakly support `g4`.
   So the proof must consume the full hypothesis `∀ i j, 0 ≤ det3 (f i)(f (i+1))(f j)`.

2. **The strict-core induction divides by an edge support `e_m = det3(g i)(g (i+1))(g m)` and FAILS weakly**
   when `e_m = 0` (i.e. `g m` collinear with the reference edge in the gnomonic plane). Handling that
   degeneracy is the entire difficulty. The fact is the classical "a convex polygon's vertices are in
   consistent cyclic orientation"; the obstruction is the half-plane / total-turning `< π` bound which
   pure local Plücker division cannot see.

3. The **plane non-degeneracy** `⟪h, f i⟫ = 1` (h ≠ 0) is essential (rules out points at infinity / lets
   you treat `f` as genuine affine points; `det3(f a, f b, f c)` is then a positive multiple of the 2-D
   signed area of the affine triangle).

## Suggested routes (pick whichever closes; you have full latitude)

**Route A — direct ℕ-core with the degenerate escape.** Prove a weak ℕ core that, IN ADDITION to weak
`hbase`/`hedge`, takes the full weak edge supports `∀ a b, (window) → 0 ≤ det3 (g a)(g (a+1))(g b)` (any
`b`, both sides). Gap-induction on `q - p` (so ANY pivot `m ∈ (p,q)` is allowed by gap-IH). If some
`m ∈ (p,q)` has `e_m = det3(g i)(g (i+1))(g m) > 0`, divide via `det3_apex_plucker` (template). Else all
intermediate `g m` are collinear with the line `L = line(g i, g (i+1))`; in that degenerate case use the
edge supports of an interior edge `(p, p+1)` or `(q-1, q)` (which support `g i` and `g q` on BOTH sides)
plus the collinearity to force `det3(g i)(g p)(g q) ≥ 0` directly (case-split on which side along `L` the
collinear points lie; collinear points give `det3(g i)(g m)(g x)` proportional with a SIGNED factor to an
edge support). Grind the degenerate algebra with `nlinarith`/`det3_apex_plucker` instantiations.

**Route B — oriented-angle / winding.** Reduce to 2-D (the plane is 2-dimensional), use Mathlib
`Orientation.oangle` (or `Complex.arg`) for the polar angle of `f_t` about `f_i`; the edge supports give
each angle in a closed half-turn and monotone consecutive turning, so `arg(f_q-f_i) - arg(f_p-f_i) ∈ [0,π]`,
i.e. the cross product (= `det3` up to positive scale) is `≥ 0`. Heavier setup but conceptually clean.

**Route C — perturbation to strict.** If you can construct an in-plane strict perturbation `f^ε` with
`f^ε → f` and apply `planarConvexDiagPos_holds` then pass `ε → 0` by polynomial continuity of `det3`.
(Constructing the strict perturbation is itself nontrivial; only attempt if A/B stall.)

## Deliverable
`ProofsInTheBook/ScratchWeakDiag.lean` typechecks under `lake env lean` with zero `sorry`/`axiom`.
Append a one-line `echo "WEAKDIAG_DONE" >> /tmp/weakdiag-progress.log` when fully closed (and
`echo "WEAKDIAG_BLOCKED: <reason>" >> /tmp/weakdiag-progress.log` if you must stop — state exactly what
blocks, no faking). Work continuously; do not stop to ask.
