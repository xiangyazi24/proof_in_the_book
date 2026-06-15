# Ch13 — Planar Cyclic One-Wind No-Repeat (`ZinanFFCT102`)

## Status: CLOSED (clean-3), one honestly-isolated geometric field

File: `ProofsInTheBook/ZinanFFCT102.lean` (234 lines). Verified on uisai2:
`lake env lean ProofsInTheBook/ZinanFFCT102.lean` → 0 errors.

`#print axioms` for both deliverables:
```
ProofsInTheBook.ZinanFFCT102.planar_oneWind_repeat_false :
  [propext, Classical.choice, Quot.sound]
ProofsInTheBook.ZinanFFCT102.planarWeakConvex_strictTurns_oneWind_noNonadjacentRepeat :
  [propext, Classical.choice, Quot.sound]
```
No `sorryAx`, no `ofReduceBool`/`trustCompiler`. No `sorry/admit/axiom/native_decide`.

## What closed UNCONDITIONALLY

The entire **3-case local determinant argument** of `planar_oneWind_repeat_false`,
on top of the single isolated field below, plus the corollary packaging it as the
local predicate `NoNonadjacentRepeat f := ∀ r s, r.val+2 ≤ s.val → f r ≠ f s`.

The cyclic hypotheses are `hedge` (no zero edge), `hsupp` (global cyclic weak
support), `hturn` (strict positive turns), and the certificate `hone`.

Three cases on a nonadjacent repeat `f r = f s`, `r.val+2 ≤ s.val`:
- **wrap** `s+1 = r`: then `f(s+1) = f r = f s`, so edge `s` is zero, contradicting `hedge s`.
- **minimal** `s.val = r.val+2`: then `f r = f(r+2)`, so the turn
  `det3 (f r)(f(r+1))(f(r+2)) = det3 a b a = 0` (`det3_self_right`), contradicting `hturn r`.
- **generic** `r.val+2 < s.val`: Step 1 — `hsupp r (s+1)` gives `0 ≤ D` and
  `hsupp s (r+1)` (with `f s = f r`, `det3_swap23`) gives `0 ≤ -D`, so `D = 0` where
  `D := det3 (f r)(f(r+1))(f(s+1))`. Step 2 — feed `D=0` to the isolated field to get
  `c < 0` with `f(s+1) - f s = c • (f(r+1) - f r)`. Step 3 — `hsupp s (r+2)` gives
  `0 ≤ det3 (f s)(f(s+1))(f(r+2))`; rewriting `f s = f r` and
  `f(s+1) = f r + c•(f(r+1)-f r)`, det3 multilinearity in slot 2 collapses this to
  `c · det3 (f r)(f(r+1))(f(r+2))`. With `c < 0` and `hturn r > 0` this is `< 0`,
  contradicting `0 ≤`. (`nlinarith`.)

All Fin side-conditions (`(s+1)≠r`, `(s+1)≠r+1`, `(r+1)≠s`, `(r+1)≠s+1`,
`(r+2)≠s`, `(r+2)≠s+1`, and the non-wrap of `r+1`, `r+1+1`) are derived locally
from `r.val+2 < s.val`, `s.val < N`, via `Fin.val_add` / `omega`. The cyclic
successors near `r` provably do not wrap (`r.val+2 < s.val < N`); `s+1` may wrap
but is never `.val`-decomposed (only Fin-equalities `s+1 ≠ …` are used).

## det3 multilinearity lemmas used (local copies, proved off `det3`'s definition)

- `det3_self_left a b : det3 a a b = 0`           (`simp[det3]; ring`)
- `det3_self_mid a b : det3 a b b = 0`
- `det3_self_right a b : det3 a b a = 0`
- `det3_swap23 a b c : det3 a c b = -det3 a b c`
- `det3_add_mid a b c d : det3 a (b+c) d = det3 a b d + det3 a c d`  (`simp[det3, PiLp.add_apply]; ring`)
- `det3_smul_mid a b d t : det3 a (t•b) d = t * det3 a b d`         (`simp[det3, PiLp.smul_apply, smul_eq_mul]; ring`)

The step-3 collapse `det3 (f r)(f r + c•(f(r+1)-f r))(w) = c·det3 (f r)(f(r+1))(w)`
uses `det3_add_mid` (split slot 2), `det3_self_left` (kills `det3 (f r)(f r)(w)`),
`det3_smul_mid` (pull out `c`), then a second `det3_add_mid`/`det3_smul_mid`/
`det3_self_left` to discard the `−f r` term of `f(r+1)-f r`.

## The single ISOLATED residue (honest §3.3 isolation)

`PlanarCyclicLiftedTurnSpan f h u v` is a `Prop` structure with **one field**:
```
neg_smul_edge_of_det3_zero : ∀ {r s : Fin N}, r.val < s.val →
  det3 (f r) (f (r+1)) (f (s+1)) = 0 →
    ∃ c : ℝ, c < 0 ∧ (f (s+1) - f s) = c • (f (r+1) - f r)
```
This is the genuine one-wind content: det3 = 0 ⇒ edges `e_r, e_s` collinear; the
strictly-increasing lifted-angle gap `θ_s − θ_r ∈ (0, 2π)` together with det3 = 0
⇒ gap = π ⇒ `e_s` is a NEGATIVE multiple of `e_r` (`c = −ρ_s/ρ_r < 0`). The
full `θ → sin → π` machinery is heavy, so it is exposed as the single field rather
than re-derived. It is NOT faked as a free theorem.

**Satisfiability witness.** It is realised by any real convex single-wind planar
arm: with the FFCT94 `PlanarLiftedTurnSpan` data `edge_i = ρ_i•(cosθ_i u + sinθ_i v)`,
det3 = 0 forces the two edge directions to be antiparallel (the only collinear
configuration available under strictly-increasing θ with total span < 2π is a
half-turn `θ_s − θ_r = π`), whence `e_s = (ρ_s/ρ_r)(cos(θ_r+π)…) = −(ρ_s/ρ_r) e_r`,
giving `c = −ρ_s/ρ_r < 0`. The equilateral N=4 chain that refutes the OPEN-span
version (FFCT99) does not satisfy the cyclic hypotheses (`hedge`/`hturn` fail on
the wrap), so there is no conflict.

## Key step-3 contradiction (one line)

`0 ≤ det3 (f s)(f(s+1))(f(r+2)) = c · det3 (f r)(f(r+1))(f(r+2))` with `c < 0` and
`det3 (f r)(f(r+1))(f(r+2)) > 0` (=`hturn r`) ⇒ RHS `< 0` ⇒ `False`.
