# Ch13 `no_repeat` brick — report (ZinanFFCT23)

**File:** `ProofsInTheBook/ZinanFFCT23.lean` (new, sole writer). Compiles clean-3 on uisai2
(`lake env lean`, 0 errors). All seven `#print axioms` results = `[propext, Classical.choice,
Quot.sound]`. No `sorry`/`admit`/`axiom`/`native_decide`.

## The consumption site (exact)

The DAG names the brick `no_repeat_of_positiveJoints`, supplying the `a > 0` strictness that
`ZinanFFCT21` left as an explicit hypothesis. The precise site is:

- `ZinanFFCT21.far_fold_i_eq_zero` — argument `hapos : 0 < (a : ℝ)`; and
- the `0 < (a : ℝ)` conjunct of the `hnd` datum of
  `ZinanFFCT21.far_fold_boundary_classification_of_nondeg`.

FFCT21's own comment (line 358) flags this exact slot: *"`a > 0` is the supplied hypothesis (the
`no_repeat` master brick supplying it is out of scope)."*

## What was proven

The fold datum is `(a:ℝ)•A(i+1) + (b:ℝ)•A j = A i`, `a,b : ℝ≥0`, `i+2 < j < n+1`.

1. `repeat_of_a_eq_zero` — **unconditional**: `a = 0 ⟹ A i = A j`. (With `a = 0` the datum is
   `A i = b•A j`, both unit, `b ≥ 0`; FFCT21 Brick 2 `nnreal_smul_unit_eq_unit` gives `b = 1` and the
   vertex equality.) Since `i + 2 < j`, this is a *nonadjacent* repeat.

2. `no_repeat_of_positiveJoints` — **the deliverable**: `0 < (a:ℝ)` from the fold datum +
   `NoNonadjacentRepeat A`. (`a ≥ 0` always; if `a = 0`, (1) yields the nonadjacent repeat, killed by
   `NoNonadjacentRepeat` at `(i,j)`.)

3. `far_fold_nondeg_datum_of_no_repeat` — **drop-in assembly**: from the *raw* span membership
   `A i ∈ span≥0 {A(i+1), A j}` + weak convexity + `NoNonadjacentRepeat`, builds the full
   `∃ a b, 0<a ∧ 0<b ∧ …` datum that `far_fold_boundary_classification_of_nondeg` consumes.
   `b > 0` reuses FFCT21 Brick 3; `a > 0` is (2). Eliminates `hapos` entirely.

4. `far_fold_i_eq_zero_of_no_repeat`, `far_fold_boundary_i_eq_zero_of_span` — the FFCT21 wrappers with
   `hapos` discharged, giving unconditional `i = 0` on the no-repeat class (the latter takes the raw
   span membership directly).

## The one named conditional input — and why (honest scope)

`NoNonadjacentRepeat A` := `∀ r s, r + 2 ≤ s < n+1 → A r ≠ A s`.

The reduction `a = 0 ⟹ A i = A j` is **unconditional and clean**. The remaining step — that a
nonadjacent repeat is geometrically impossible — is supplied as the explicit, *satisfiable*
hypothesis `NoNonadjacentRepeat A`, **not** derived from `PositiveJoints` alone. This is deliberate
and matches the audited scope:

- FFCT21 Brick 4's determinant-collapse (opposite-sign multiples of one `det3`) does **not** fire for
  the `a > 0` direction. The two weak supports of the predecessor edge of `j` evaluate to
  `det3 (A(j-1)) (A j) (A i) = a · det3 (A(j-1)) (A j) (A(i+1))` — the **same** sign for `a ≥ 0`, so
  no contradiction is forced locally. (Verified by the same row-swap algebra as Brick 4; the sign
  flip that powers Brick 4 is absent here.)
- Hence certifying no-repeat from `PositiveJoints` needs the **global / out-of-plane** argument — the
  identical master obstruction the audit (`ch13-B5-B1-audit.md`, line 3) scoped out, and that FFCT22
  already packaged as the named `TailConePropagates` hypothesis for the tail half. I follow that same
  honest CONDITIONAL pattern.

**Non-vacuity guards** (so this is not an impostor conditional):
- `noNonadjacentRepeat_of_injective` — every injective-vertex arm satisfies it (it is *satisfiable*;
  the strictly convex comparison class lives here).
- `noNonadjacentRepeat_can_fail` — a constant arm on `n=2` violates it at `(0,2)` (it is a *real
  constraint*, not vacuously true — so `0 < a` is not asserted under a false premise).
- `repeat_reduction_nonvacuous` — `a = 0` is realisable, so the reduction is non-vacuous.

## Blocked item (single, named)

Deriving `NoNonadjacentRepeat A` from `WeakConvexSphArm A ∧ PositiveJoints A` unconditionally is the
out-of-plane sign-certification master brick (same as FFCT22's `TailConePropagates`; audit estimates
250–450 lines, needs strict convexity at the relevant edge which the weak arm `A` lacks pointwise). I
prove everything *downstream* of it unconditionally and expose it as the single explicit satisfiable
hypothesis.

## Alternatives considered

The DAG phrasing ("opened arm never returns to a previously visited configuration") admits a
configuration-level reading, but the actual consumption site is purely the scalar `0 < (a:ℝ)` at the
far-fold span representation. I formalized THAT (the strongest directly-consumed statement), plus the
assembly wrappers, rather than a configuration-trajectory predicate that nothing downstream consumes.

## Verify

```
scp ProofsInTheBook/ZinanFFCT23.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ \
  && ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT23.lean'
```
(FFCT22 oleans were built first via `lake build ProofsInTheBook.ZinanFFCT22`.)
