# Ch13 signed-line tail propagation — worker report (FFCT24)

File: `ProofsInTheBook/ZinanFFCT24.lean` — compiles clean (0 errors, 0 warnings), all 8 results clean-3
(`#print axioms` = `[propext, Classical.choice, Quot.sound]` only; no sorry/admit/axiom/native_decide).
Imports `ProofsInTheBook.ZinanFFCT23` (transitively FFCT22/21/18/12/3). Verified on uisai2.

## THE SUPPORT-ORIENTATION CONVENTION (verified against the landed kernel — quote)

From `ProofsInTheBook/SphericalKernel.lean`:

```
def sOrient (a b c : S2) : ℝ := det3 (a : E3) (b : E3) (c : E3)        -- line 395
structure StrictConvexSphPolygon ... where
  edge_support : ∀ i j : Fin n, 0 ≤ sOrient (P i) (P (i + 1)) (P j)   -- line 404
```
`WeakConvexSphPolygon` ships the same `edge_support` field. So:

> **Support of edge `(A r, A (r+1))` at a vertex `A k` is `0 ≤ det3 (A r) (A (r+1)) (A k)`** —
> first two `det3` slots = the edge endpoints **in order**, third slot = the probed vertex.

This is exactly the orientation FFCT21 (`far_fold_no_predecessor`) and FFCT22
(`far_fold_tail_collinear_step`, with `hsupp1 : 0 ≤ det3 z₀ v z'` and `hsupp2 : 0 ≤ det3 zt z' v`)
already used. Concretely: edge `(A0,A1)` at `A2` is `0 ≤ det3 A0 A1 A2`; edge `(A1,A2)` at `Ar` is
`0 ≤ det3 A1 A2 Ar`. The design's assumed orientations (`0 ≤ det3 A1 A2 Ar` in T2) match the landed
convention — NO flip was needed. Every sign chain below is anchored here.

## Statements proven (all clean-3)

- `OnFoldLineCoeff A j hj r hr h1` — **structure** (NOT Prop: it carries data fields `c d : ℝ` with
  real projections, which a Prop forbids; the design's `: Prop` had to be dropped so `hcurr.d` works
  in T6). Fields: `c d : ℝ`, `hd_nonneg : 0 ≤ d`, `repr : A r = c • A 1 + d • A j`. Plus
  `OnFoldLineCoeffPos` (bundles `0 < toLine.d`).
- `det3_add_fst` / `det3_smul_fst` — first-slot multilinearity (kernel ships only mid/right).
- **T5** `tail_line_start_at_j` — seed `A j = 0•A1 + 1•Aj`, `d = 1 > 0`. ✅ unconditional.
- **T1** `fold_A2_witness_negative` — fold `A0 = a•A1 + b•Aj` (`b>0`) ⟹ `det3 A1 Aj A2 < 0`. ✅
  unconditional (under WeakConvex+PositiveJoints+StrictConvex B+JointLe). Sign chain landed:
  `det3 A0 A1 A2 = b·det3 Aj A1 A2 = -b·det3 A1 Aj A2 ≥ 0` ⟹ `det3 A1 Aj A2 ≤ 0`; equality ⟹
  `det3 A0 A1 A2 = 0` ⟹ flat joint at `A1` (index 0) via `sphAngle_eq_zero_or_pi_of_det3_zero`,
  refuted by `hposA`/`jointAngle_lt_pi`. NOTE: `2 < j` (`_hjfar`) turned out **unused** by the
  proved route (kept in the signature for the consumer interface).
- **T2** `fold_coeff_d_nonneg_of_A2_witness` — `D2 < 0` + `Ar = c•A1 + d•Aj` +
  `0 ≤ det3 A1 A2 Ar` ⟹ `0 ≤ d`. ✅ unconditional. Chain: `det3 A1 A2 Ar = -d·D2 ≥ 0`.
- **T3/T4** `tail_step_collinear` — thin FFCT22 wrapper: fold + current datum + the two supports ⟹
  `det3 A1 Aj A(t+1) = 0`. ✅ unconditional.
- **T3/T4** `tail_line_step` — **def** producing `OnFoldLineCoeff` at `t+1` with `0 ≤ d'`, given the
  witness sign `D2<0`, the named real-span representation `hrepr_next`, and the edge-(1,2) support at
  `A(t+1)`. The `d'≥0` is T2; the representation is the named residue (see below).
- `tail_step_absorb_refuted` — `d'=0` (so `A(t+1)=c'•A1`) ⟹ `c'=±1` ⟹ `A(t+1)=±A1`; both refuted
  from two named inputs (`hnorepeat`, `hnotanti`). ✅
- `tail_step_d_pos_or_absorb` — packages the strict upgrade `0 < hnext.d ∨ False`, dispatching the
  `d'=0` branch into `tail_step_absorb_refuted`. ✅

## Named residues (exact blocking goals for T6 to supply)

1. **The real-span representation `hrepr_next`** (in `tail_line_step`):
   `(A ⟨t+1,ht2⟩ : E3) = c' • (A ⟨1,h1⟩ : E3) + d' • (A ⟨j,hj⟩ : E3)` for some `c' d' : ℝ`.
   Blocking fact: it follows from `det3 A1 Aj A(t+1) = 0` (which `tail_step_collinear` GIVES
   unconditionally) **iff** `A1, Aj` are linearly independent, i.e. `A 1 ≠ ± A j`. I did not derive
   linear independence here (the design explicitly permits taking it as a named hypothesis). T6
   should discharge it from `det3_zero_of_mem_span_pair`-style span extraction once `A1 ≠ ±A j` is in
   hand. `A 1 ≠ A j` is a nonadjacent repeat (`NoNonadjacentRepeat`, since `2 < j`); `A1 ≠ -A j`
   (non-antipodal) is `weakConvex_no_antipodal` (FFCT18) or the `ShortArc` 2nd conjunct.

2. **`hnorepeat : A ⟨1,h1⟩ ≠ A ⟨t+1,ht2⟩`** and **`hnotanti : (A⟨t+1⟩:E3) ≠ -(A⟨1⟩:E3)`**
   (in `tail_step_absorb_refuted` / `tail_step_d_pos_or_absorb`):
   - `hnorepeat`: from `NoNonadjacentRepeat A` (FFCT23) at indices `1` and `t+1` with `1 + 2 ≤ t+1`,
     i.e. `t ≥ 2` (the `_ht_ge : 2 ≤ t` slot records exactly this nonadjacency requirement).
   - `hnotanti`: from `weakConvex_no_antipodal` (FFCT18) — no two vertices of a weakly convex arm are
     antipodal — or the second conjunct of `ShortArc (A⟨t+1⟩) (A⟨1⟩)` if that edge is short.

   Both are the SAME audited master obstruction as FFCT22/23 (out-of-plane sign / no-repeat), already
   named-and-satisfiable there. They are NOT new gaps.

## Advice for the T6 master induction

- **Start at `t = j`** (T5), not `t = 1`: the seed at `1` has `d = 0` and cannot drive the FFCT22
  determinant step (`hd : 0 < d` is required). The design's warning is real and load-bearing.
- **`far_fold_tail_collinear_step` does NOT need the previous vertex** `A(t-1)`. It needs only the
  fold at `0` (`hb`), the current datum at `t` (`hd`), and the two supports at `A(t+1)`. So the
  design's `hprev_line` hypothesis is droppable — the first step from `t=j` (where `A(j-1)` is OFF
  the line) is fine. My `tail_step_collinear`/`tail_line_step` take no `hprev_line`. (Confirmed
  design gap (a).)
- **The two supports T6 must feed `tail_step_collinear`** are, in the landed convention:
  `0 ≤ det3 A0 A1 A(t+1)` = `edge_support ⟨0⟩ ⟨t+1⟩` (after `(⟨0⟩+1)=⟨1⟩`), and
  `0 ≤ det3 At A(t+1) A1` = `edge_support ⟨t⟩ ⟨1⟩` (after `(⟨t⟩+1)=⟨t+1⟩`). The successor-rewrite
  pattern is in T1 (`hsucc01`/`hsucc12`) and FFCT21.
- **The edge-(1,2) support for T2/`tail_line_step`** is `0 ≤ det3 A1 A2 A(t+1)` =
  `edge_support ⟨1⟩ ⟨t+1⟩` (after `(⟨1⟩+1)=⟨2⟩`).
- **Induction shape**: carry `OnFoldLineCoeffPos A j hj t htt h1` (datum + `0 < d`). Step: get
  `det3 A1 Aj A(t+1)=0` (`tail_step_collinear`), supply `hrepr_next` (residue 1), build the next
  datum (`tail_line_step`), then `tail_step_d_pos_or_absorb` either continues (`0 < d'`) or closes
  (`False`). Terminate when three consecutive line vertices accumulate and FFCT22's
  `far_fold_tail_not_interior` fires (you have `OnFoldLineCoeff` ⟹ `coplanar_triple_det3_zero` over
  `{A1,Aj}` ⟹ `det3 A(t-1) At A(t+1)=0`). Because `j ≤ n-2`, at least one step exists.
- **Defeq Nat indices**: `(t+1)-1 = t` closes by `rfl`/`omega`; `jointAngle A ⟨0,_⟩` unfolds to the
  `sphAngle` triple with `0+1`,`0+2` reducing definitionally to `1`,`2` (in T1 the `hjoint_eq` proof
  is just `rw [jointAngle]` — no Fin.ext needed at base 0).

## Pitfalls hit & fixed (for the record)

- `OnFoldLineCoeff` cannot be `: Prop` with data projections — made it a plain `structure`
  (Type-valued); `tail_line_step` is therefore a `def`, not a `theorem`.
- A `/-! ... -/` section comment containing the literal `-/` substring (e.g. "right-/mid-") silently
  terminates the comment block — avoid `-/` inside doc comments.
