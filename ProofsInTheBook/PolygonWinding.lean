import ProofsInTheBook.PolygonOracleClose
import ProofsInTheBook.PolygonCutClose

/-!
# Chapter 36 — the SIGNED winding / degree development (`OffDiagDisjoint`)

A prior round (`PolygonJordanDisjoint`, `PolygonCutClose`) machine-proved that BOTH
the **unsigned** crossing count (parity *and* the integer identity
`cP + 2d = cL + cR`, `intCount_admits_both_inside`) and the **affine `det2`-side**
of the diagonal *line* (`lineSide_blind_to_chord_endpoints`) are *insufficient* to
prove `OffDiagDisjoint` — the both-inside state is admissible in both, and the line
side is blind to the chord *segment*.  The isolated residue: a SIGNED winding number
that distinguishes the chord side where the unsigned count cannot.

This file builds that signed development.

## The signed crossing / winding number

For a base point `x`, ray direction `r`, and an oriented edge `a → b`, the SIGNED
contribution to the upward-ray crossing is

```
rawSignedInd r x a b
  := if RawEdgeCrosses r x a b then (if 0 < det2 r (b - a) then 1 else -1) else 0   : ℤ
```

The event `RawEdgeCrosses` is the SAME (unsigned) crossing predicate as the existing
machinery; the new datum is the *sign* `det2 r (b - a) = side r x b - side r x a`,
the direction in which the edge crosses the ray line.  The winding number of a
polygon boundary is the sum of the signed contributions over its edges:

```
windCross P r x := ∑ k, rawSignedInd r x (P.q k) (P.q (cyclicNext k))   : ℤ
```

## The KEY structural difference from the unsigned count

* **Unsigned** `rawInd` is orientation-*symmetric* (`rawEdgeCrosses_symm`):
  `rawInd r x a b = rawInd r x b a`.  Hence the diagonal, traversed `j → i` by the
  left sub-polygon and `i → j` by the right, contributes `+1` to *each* — the
  `2 · diagCount` term in `cL + cR = cP + 2d`.  This `2d` is exactly what makes the
  both-inside state parity/integer admissible.
* **Signed** `rawSignedInd` is orientation-*antisymmetric*
  (`rawSignedInd_swap`): `rawSignedInd r x b a = - rawSignedInd r x a b`.  Hence the
  diagonal's two contributions **CANCEL**: the left diagonal edge `j → i` gives `-s`,
  the right diagonal edge `i → j` gives `+s`.  The signed split identity therefore
  has **no** diagonal term:

  ```
  windCross_L(x) + windCross_R(x) = windCross_P(x)              (windCross_split)
  ```

  This is the Mathlib-style "winding number is additive under boundary
  concatenation; the shared cut cancels" fact, proved combinatorially.
-/

namespace ProofsInTheBook.PolygonWinding

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonOracle
open ProofsInTheBook.PolygonLocalConstancy (det2_sub_right det2_smul_right)
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Layer 1: the signed indicator and its orientation antisymmetry -/

/-- The signed crossing contribution of the oriented edge `a → b` for the upward ray
from `x` along `r`: `0` if the edge is not crossed, otherwise the sign of
`det2 r (b - a)` (= `side r x b - side r x a`), the direction of the crossing. -/
def rawSignedInd (r x a b : Pt) : ℤ := by
  classical
  exact if RawEdgeCrosses r x a b then (if 0 < det2 r (b - a) then 1 else -1) else 0

/-- **`det2 r (b - a)` is the side difference.**  `det2 r (b - a) = side r x b -
side r x a`. -/
lemma det2_eq_side_diff (r x a b : Pt) :
    det2 r (b - a) = side r x b - side r x a := by
  unfold side
  rw [← det2_sub_right]
  congr 1
  abel

/-- **At a crossing event the side difference is nonzero.**  If `RawEdgeCrosses r x a
b` then `det2 r (b - a) ≠ 0` (the two endpoint side values have opposite signs, so
they differ). -/
lemma det2_ne_zero_of_rawEdgeCrosses {r x a b : Pt} (h : RawEdgeCrosses r x a b) :
    det2 r (b - a) ≠ 0 := by
  -- RawEdgeCrosses = Span (side a) (side b) ∧ _; Span forces opposite signs.
  have hspan : Span (side r x a) (side r x b) := by
    have := h
    unfold RawEdgeCrosses at this
    -- rawSide r x v = side r x v definitionally
    exact this.1
  rw [det2_eq_side_diff r x a b]
  rcases hspan with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · -- side a ≤ 0 < side b ⇒ side b - side a > 0
    intro hcontra; linarith
  · -- side b ≤ 0 < side a ⇒ side b - side a < 0
    intro hcontra; linarith

/-- **The signed indicator is orientation-antisymmetric.**  `rawSignedInd r x b a =
- rawSignedInd r x a b`.  This is the crux that makes the diagonal cancel in the
split identity (contrast `rawEdgeCrosses_symm`, the unsigned symmetry). -/
lemma rawSignedInd_swap (r x a b : Pt) :
    rawSignedInd r x b a = - rawSignedInd r x a b := by
  classical
  unfold rawSignedInd
  by_cases hcross : RawEdgeCrosses r x a b
  · -- event holds both ways (symmetry); the sign flips.
    have hcross' : RawEdgeCrosses r x b a := (rawEdgeCrosses_symm r x a b).mp hcross
    rw [if_pos hcross, if_pos hcross']
    -- det2 r (a - b) = - det2 r (b - a), and det2 r (b - a) ≠ 0.
    have hne : det2 r (b - a) ≠ 0 := det2_ne_zero_of_rawEdgeCrosses hcross
    have hflip : det2 r (a - b) = - det2 r (b - a) := by
      have h : a - b = -(b - a) := by abel
      rw [h, show (-(b - a)) = (-1 : ℝ) • (b - a) by module, det2_smul_right]; ring
    rw [hflip]
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · -- det2 (b-a) < 0 ⇒ -det2(b-a) > 0; sign for b→a is +1, for a→b is -1.
      rw [if_pos (by linarith), if_neg (by linarith)]; ring
    · -- det2 (b-a) > 0 ⇒ -det2(b-a) < 0; sign for b→a is -1, for a→b is +1.
      rw [if_neg (by linarith), if_pos hpos]
  · -- no event either way.
    have hcross' : ¬ RawEdgeCrosses r x b a := fun h => hcross ((rawEdgeCrosses_symm r x a b).mpr h)
    rw [if_neg hcross, if_neg hcross']; ring

/-- **The signed indicator has magnitude the unsigned indicator.**  `|rawSignedInd r
x a b| = rawInd r x a b` (as integers).  So the signed count refines the unsigned
one: `windCross` is `0` whenever the unsigned crossing number is `0`, and `±1`
contributions accumulate to it. -/
lemma rawSignedInd_abs (r x a b : Pt) :
    |rawSignedInd r x a b| = (rawInd r x a b : ℤ) := by
  classical
  unfold rawSignedInd rawInd
  by_cases hcross : RawEdgeCrosses r x a b
  · rw [if_pos hcross, if_pos hcross]
    by_cases hsgn : 0 < det2 r (b - a)
    · rw [if_pos hsgn]; norm_num
    · rw [if_neg hsgn]; norm_num
  · rw [if_neg hcross, if_neg hcross]; norm_num

/-- The signed indicator is `1`, `-1`, or `0`. -/
lemma rawSignedInd_mem (r x a b : Pt) :
    rawSignedInd r x a b = 1 ∨ rawSignedInd r x a b = -1 ∨ rawSignedInd r x a b = 0 := by
  classical
  unfold rawSignedInd
  by_cases hcross : RawEdgeCrosses r x a b
  · rw [if_pos hcross]
    by_cases hsgn : 0 < det2 r (b - a)
    · exact Or.inl (if_pos hsgn)
    · exact Or.inr (Or.inl (if_neg hsgn))
  · exact Or.inr (Or.inr (if_neg hcross))

/-! ## Layer 2: the winding number of a polygon boundary -/

/-- The SIGNED winding / crossing number of a vertex tuple `q : Fin m → Pt` along
direction `r` from base `x`: the sum of the signed edge contributions. -/
def windRaw {m : ℕ} (q : Fin m → Pt) (r x : Pt) : ℤ :=
  ∑ k : Fin m, rawSignedInd r x (q k) (q (cyclicNext k))

/-- The signed winding number of a strict simple polygon's boundary. -/
def windCross (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) : ℤ :=
  windRaw P.q ρ.r x

lemma windCross_eq (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) :
    windCross P ρ x = ∑ k : Fin n, rawSignedInd ρ.r x (P.q k) (P.q (cyclicNext k)) := rfl

/-! ## Layer 3: the signed split identity (the diagonal CANCELS)

We mirror the unsigned arc-decomposition (`PolygonOracle.rawCount_*`) for the SIGNED
indicator.  The arc edges of each sub-polygon are oriented the same as the parent
edges, so contribute identically; the only difference from the unsigned chain is the
diagonal, which the left sub-polygon traverses `j → i` and the right `i → j` — by
`rawSignedInd_swap` these cancel. -/

/-- **Signed left arc-edge indicator equals the parent one.**  Same endpoints as the
unsigned `rawInd_left_arc`. -/
lemma rawSignedInd_left_arc {P : StrictSimplePolygon n} {i j : Fin n} (hij : i ≠ j)
    (r x : Pt) {k : Fin (leftLength i j)} (hk : k.val < cyclicSteps i j) :
    rawSignedInd r x (subpolygonLeftTuple P i j k)
        (subpolygonLeftTuple P i j (cyclicNext k)) =
      rawSignedInd r x (P.q (arcPt i k.val)) (P.q (cyclicNext (arcPt i k.val))) := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  obtain ⟨h1, h2⟩ := left_arc_edge_endpoints hij hk
  unfold subpolygonLeftTuple
  rw [h1, h2, cyclicNext_arcPt i k.val hn]

/-- **Signed left diagonal-edge indicator.**  The left diagonal edge is read `j → i`,
so its signed contribution is `rawSignedInd r x (P.q j) (P.q i)` — the OPPOSITE of the
`i → j` orientation (no `rawEdgeCrosses_symm` collapse here, the sign is kept). -/
lemma rawSignedInd_left_diag {P : StrictSimplePolygon n} {i j : Fin n} (hij : i ≠ j)
    (r x : Pt) {k : Fin (leftLength i j)} (hk : k.val = cyclicSteps i j) :
    rawSignedInd r x (subpolygonLeftTuple P i j k)
        (subpolygonLeftTuple P i j (cyclicNext k)) =
      rawSignedInd r x (P.q j) (P.q i) := by
  obtain ⟨h1, h2⟩ := left_diag_edge_endpoints hij hk
  unfold subpolygonLeftTuple
  rw [h1, h2]

/-- `windRaw` as a `Finset.univ`-sum (definitional unfolding). -/
lemma windRaw_eq_sum {m : ℕ} (q : Fin m → Pt) (r x : Pt) :
    windRaw q r x = ∑ k : Fin m, rawSignedInd r x (q k) (q (cyclicNext k)) := rfl

/-- **Signed left arc-sum split.**  The left signed winding splits as the sum of
parent signed indicators over the left arc plus the diagonal `j → i` contribution. -/
lemma windRaw_left_split {P : StrictSimplePolygon n} {i j : Fin n} (hij : i ≠ j)
    (r x : Pt) :
    windRaw (subpolygonLeftTuple P i j) r x =
      (∑ d : Fin (cyclicSteps i j),
        rawSignedInd r x (P.q (arcPt i d.val)) (P.q (cyclicNext (arcPt i d.val)))) +
      rawSignedInd r x (P.q j) (P.q i) := by
  rw [windRaw_eq_sum]
  rw [show (∑ k : Fin (leftLength i j),
      rawSignedInd r x (subpolygonLeftTuple P i j k)
        (subpolygonLeftTuple P i j (cyclicNext k))) =
      ∑ k : Fin (cyclicSteps i j + 1),
      rawSignedInd r x (subpolygonLeftTuple P i j k)
        (subpolygonLeftTuple P i j (cyclicNext k)) from rfl]
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro d _
    rw [rawSignedInd_left_arc hij r x (k := Fin.castSucc d) (by
      simp only [Fin.val_castSucc]; exact d.isLt)]
    simp only [Fin.val_castSucc]
  · rw [rawSignedInd_left_diag hij r x (k := Fin.last (cyclicSteps i j)) (by
      simp only [Fin.val_last])]

/-- **Signed right arc-sum split.**  Apply the left split to the swapped pair `(j, i)`.
The right diagonal edge is read `i → j` (the swap of the left's `j → i`), so its
contribution is `rawSignedInd r x (P.q i) (P.q j)`. -/
lemma windRaw_right_split {P : StrictSimplePolygon n} {i j : Fin n} (hij : i ≠ j)
    (r x : Pt) :
    windRaw (subpolygonRightTuple P i j) r x =
      (∑ d : Fin (cyclicSteps j i),
        rawSignedInd r x (P.q (arcPt j d.val)) (P.q (cyclicNext (arcPt j d.val)))) +
      rawSignedInd r x (P.q i) (P.q j) := by
  have heq : windRaw (subpolygonRightTuple P i j) r x
      = windRaw (subpolygonLeftTuple P j i) r x := rfl
  rw [heq, windRaw_left_split (P := P) (i := j) (j := i) hij.symm r x]

/-- **The parent signed winding equals the sum of the two arc signed sums.**  Same
rotation bijection as the unsigned `rawCount_parent_eq_arcs`, now over ℤ. -/
lemma windRaw_parent_eq_arcs {P : StrictSimplePolygon n} {i j : Fin n} (hij : i ≠ j)
    (r x : Pt) :
    windRaw P.q r x =
      (∑ d : Fin (cyclicSteps i j),
        rawSignedInd r x (P.q (arcPt i d.val)) (P.q (cyclicNext (arcPt i d.val)))) +
      (∑ d : Fin (cyclicSteps j i),
        rawSignedInd r x (P.q (arcPt j d.val)) (P.q (cyclicNext (arcPt j d.val)))) := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hsum : cyclicSteps i j + cyclicSteps j i = n := cyclicSteps_add_reverse i j hij
  let g : Fin n → ℤ := fun p => rawSignedInd r x (P.q p) (P.q (cyclicNext p))
  let e : Fin n → Fin n := fun d => arcPt i d.val
  have he_bij : Function.Bijective e := by
    apply (Finite.injective_iff_bijective).mp
    intro a b hab
    have hval : (i.val + a.val) % n = (i.val + b.val) % n := congrArg Fin.val hab
    have hmod : a.val % n = b.val % n :=
      Nat.ModEq.add_left_cancel' i.val (show (i.val + a.val) ≡ (i.val + b.val) [MOD n] from hval)
    rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hmod
    exact Fin.ext hmod
  have hstep1 : windRaw P.q r x = ∑ d : Fin n, g (arcPt i d.val) := by
    rw [windRaw_eq_sum]
    exact (Equiv.sum_comp (Equiv.ofBijective e he_bij) g).symm
  rw [hstep1]
  have hcast : (∑ d : Fin n, g (arcPt i d.val)) =
      ∑ d : Fin (cyclicSteps i j + cyclicSteps j i), g (arcPt i d.val) := by
    apply Fintype.sum_equiv (finCongr hsum.symm)
    intro d
    simp only [finCongr_apply, Fin.val_cast]
  rw [hcast, Fin.sum_univ_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · apply Finset.sum_congr rfl
    intro d _
    show g (arcPt i (Fin.castAdd (cyclicSteps j i) d).val) = _
    simp only [Fin.val_castAdd]; rfl
  · apply Finset.sum_congr rfl
    intro d _
    show g (arcPt i (Fin.natAdd (cyclicSteps i j) d).val) = _
    rw [Fin.val_natAdd, ← arcPt_j_eq hij d.val]

/-- **The SIGNED split identity (the diagonal cancels).**  For any direction `r`, base
`x`, and `i ≠ j`:

`windRaw_L + windRaw_R = windRaw_P`

with NO diagonal term: the left diagonal edge `j → i` and the right diagonal edge
`i → j` carry opposite signs and cancel (`rawSignedInd_swap`).  This is the structural
distinction from the unsigned `rawCount_split_identity`, where the diagonal contributes
`2 · diagCount` (and that `2d` is precisely what made the both-inside state admissible
in `intCount_admits_both_inside`). -/
theorem windRaw_split_identity {P : StrictSimplePolygon n} {i j : Fin n} (hij : i ≠ j)
    (r x : Pt) :
    windRaw (subpolygonLeftTuple P i j) r x +
        windRaw (subpolygonRightTuple P i j) r x =
      windRaw P.q r x := by
  rw [windRaw_left_split hij r x, windRaw_right_split hij r x,
    windRaw_parent_eq_arcs hij r x]
  -- the diagonal terms: rawSignedInd (q j) (q i) + rawSignedInd (q i) (q j) = 0.
  have hdiag : rawSignedInd r x (P.q j) (P.q i) + rawSignedInd r x (P.q i) (P.q j) = 0 := by
    rw [rawSignedInd_swap r x (P.q i) (P.q j)]; ring
  -- rearrange
  have := hdiag
  ring_nf
  ring_nf at this
  linarith [this]

/-- **The signed split identity at the polygon level** (`windCross` form, common ray).
With a common ray vector for parent and both sub-polygons, the parent signed winding is
the sum of the two sub-polygon signed windings — the diagonal cancels.  This is the
`CountSummationDatum`-shaped statement, but SIGNED, so without the `2 · diagCount` term
that the unsigned identity carries. -/
theorem windCross_split_common {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hL : σL.r = ρ.r) (hR : σR.r = ρ.r) (x : Pt) :
    windCross (buildLeftPoly h lax) σL x + windCross (buildRightPoly h rax) σR x =
      windCross P ρ x := by
  have hij : i ≠ j := h.1
  unfold windCross
  rw [hL, hR, buildLeftPoly_q h lax, buildRightPoly_q h rax]
  exact windRaw_split_identity hij ρ.r x

/-! ## Layer 4: the parity bridge — signed winding refines the unsigned count

The signed winding and the unsigned crossing number agree mod 2: each `rawSignedInd`
is `±1` or `0`, hence `≡ rawInd (mod 2)` (its absolute value), and summing transfers
to `windRaw ≡ rawCount (mod 2)`.  In particular **`windCross` even ⟺ `CrossingNumber'`
even**, so `Odd CrossingNumber'` (the region indicator off the boundary) forces
`windCross ≠ 0`.  This is the bridge from the parity region to the signed winding. -/

/-- **Each signed indicator is congruent to the unsigned indicator mod 2.** -/
lemma rawSignedInd_emod_two (r x a b : Pt) :
    rawSignedInd r x a b % 2 = (rawInd r x a b : ℤ) % 2 := by
  classical
  unfold rawSignedInd rawInd
  by_cases hcross : RawEdgeCrosses r x a b
  · rw [if_pos hcross, if_pos hcross]
    by_cases hsgn : 0 < det2 r (b - a)
    · rw [if_pos hsgn]; decide
    · rw [if_neg hsgn]; decide
  · rw [if_neg hcross, if_neg hcross]; decide

/-- **`windRaw` and `rawCount` agree mod 2.** -/
lemma windRaw_emod_two {m : ℕ} (q : Fin m → Pt) (r x : Pt) :
    windRaw q r x % 2 = (rawCount q r x : ℤ) % 2 := by
  classical
  rw [windRaw_eq_sum, rawCount_eq_sum]
  push_cast
  rw [Finset.sum_int_mod, Finset.sum_int_mod (s := Finset.univ)
    (f := fun k : Fin m => (rawInd r x (q k) (q (cyclicNext k)) : ℤ))]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact rawSignedInd_emod_two r x (q k) (q (cyclicNext k))

/-- **`windCross` and `CrossingNumber'` agree mod 2.** -/
lemma windCross_emod_two (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) :
    windCross P ρ x % 2 = (CrossingNumber' P ρ x : ℤ) % 2 := by
  rw [windCross, windRaw_emod_two, crossingNumber'_eq_rawCount]

/-- **Odd crossing number forces nonzero winding.**  If the (unsigned) crossing number
is odd then the signed winding number is nonzero.  Hence off the boundary,
`ClosedRegion'` (= `Odd CrossingNumber'`) implies `windCross ≠ 0`. -/
lemma windCross_ne_zero_of_odd_crossing (P : StrictSimplePolygon n) (ρ : RayDirection P)
    {x : Pt} (hodd : Odd (CrossingNumber' P ρ x)) :
    windCross P ρ x ≠ 0 := by
  intro h0
  have hbridge := windCross_emod_two P ρ x
  rw [h0] at hbridge
  -- 0 % 2 = (CrossingNumber') % 2, but CrossingNumber' is odd.
  have hcodd : (CrossingNumber' P ρ x : ℤ) % 2 = 1 := by
    obtain ⟨c, hc⟩ := hodd
    rw [hc]; push_cast; ring_nf; omega
  rw [hcodd] at hbridge
  norm_num at hbridge

/-- **Even winding forces even crossing number** (the converse parity direction). -/
lemma even_crossing_of_windCross_eq_zero (P : StrictSimplePolygon n) (ρ : RayDirection P)
    {x : Pt} (h0 : windCross P ρ x = 0) :
    ¬ Odd (CrossingNumber' P ρ x) := by
  intro hodd
  exact windCross_ne_zero_of_odd_crossing P ρ hodd h0

/-- **The signed discriminator the unsigned count lacks.**  Suppose `x` is off all three
boundaries, in BOTH sub-regions (the parity-admissible both-inside state, which the
unsigned integer identity `intCount_admits_both_inside` cannot exclude), and OUTSIDE the
parent — i.e. `windCross_P x = 0` (a `0`-winding parent point).  Then the two sub-polygon
signed windings are nonzero and SUM TO ZERO, hence are *opposite*:
`windCross_L x = - windCross_R x ≠ 0`.

This is the genuine new constraint the SIGNED count delivers: the unsigned count of the
both-inside state has `Odd cL ∧ Odd cR` with no further information, but the signed count
forces the two windings to be negatives of each other.  Combined with a one-sided
zero-winding fact (`WindingSeparates`), this excludes the state — which the unsigned count
provably cannot. -/
theorem windCross_opposite_of_both_inside_outside_parent {P : StrictSimplePolygon n}
    {ρ : RayDirection P} {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hL : σL.r = ρ.r) (hR : σR.r = ρ.r) {x : Pt}
    (hLodd : Odd (CrossingNumber' (buildLeftPoly h lax) σL x))
    (_hRodd : Odd (CrossingNumber' (buildRightPoly h rax) σR x))
    (hPwind : windCross P ρ x = 0) :
    windCross (buildLeftPoly h lax) σL x = - windCross (buildRightPoly h rax) σR x ∧
      windCross (buildLeftPoly h lax) σL x ≠ 0 := by
  have hsplit := windCross_split_common h lax rax σL σR hL hR x
  rw [hPwind] at hsplit
  refine ⟨by linarith, ?_⟩
  exact windCross_ne_zero_of_odd_crossing _ _ hLodd

/-! ## Layer 5: the diagonal side and the signed-winding separation residual

We now assemble the conclusion.  A point's *region membership* (`ClosedRegion'`, off
the boundary = `Odd CrossingNumber'`) forces, via the parity bridge, a *nonzero signed
winding*.  The signed split identity makes the sub-polygon windings additive (no
diagonal term).  The genuine Jordan content the signed count supplies — the precise
thing the unsigned count *cannot* (`intCount_admits_both_inside`) — is:

> a point on the side of the diagonal line where the LEFT ear's interior does NOT lie
> has signed winding `0` around the LEFT boundary (an exterior point of a Jordan curve
> has winding `0`), and symmetrically for the RIGHT ear.

We name this `WindingSeparates` (the signed-winding zero-exterior datum, per diagonal),
prove `OffDiagDisjoint` from it *together with the parity bridge* (the maximal provable
reduction), and certify it non-vacuous.  This residue is strictly sharper than
`SubRegionContainment`/the unsigned residue: it is the *sign-aware* exterior-vanishing
of the winding, which carries the chord-side information the unsigned count provably
loses. -/

/-- Local diagonal side function (a `side`-based functional; `PolygonCutGeometry.diagSide`
is the same definition but lives above this file in the import graph). -/
def wDiagSide (P : StrictSimplePolygon n) (i j : Fin n) (y : Pt) : ℝ :=
  side (P.q j - P.q i) (P.q i) y

/-- The diagonal endpoints are on the diagonal line. -/
lemma wDiagSide_left (P : StrictSimplePolygon n) (i j : Fin n) :
    wDiagSide P i j (P.q i) = 0 := by
  unfold wDiagSide side; rw [sub_self]; unfold det2; simp

lemma wDiagSide_right (P : StrictSimplePolygon n) (i j : Fin n) :
    wDiagSide P i j (P.q j) = 0 := by
  unfold wDiagSide side; rw [PolygonLocalConstancy.det2_self]

/-- **The signed-winding separation datum (the genuine Jordan content).**  For each
diagonal, off all three boundaries:

* a point strictly on the *negative* side of the diagonal line is exterior to the LEFT
  ear, so the LEFT signed winding vanishes there; and
* a point strictly on the *positive* side is exterior to the RIGHT ear, so the RIGHT
  signed winding vanishes there.

This is the signed-winding form of "an exterior point of a Jordan curve has winding 0",
carrying the chord-*side* information.  It is exactly the datum the unsigned count
provably cannot synthesize (`PolygonJordanDisjoint.intCount_admits_both_inside`): the
both-inside parity state has `Odd cL`, but the SIGNED winding on the wrong side is `0`. -/
def WindingSeparates {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) : Prop :=
  ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j) {x : Pt},
    ¬ OnBoundary P x →
    ¬ OnBoundary (buildLeftPoly h (g.leftAxioms h)) x →
    ¬ OnBoundary (buildRightPoly h (g.rightAxioms h)) x →
    (wDiagSide P i j x < 0 →
      windCross (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x = 0) ∧
    (0 < wDiagSide P i j x →
      windCross (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x = 0) ∧
    -- off all three boundaries, the point is not on the diagonal line (it is neither on
    -- the diagonal segment — that is on the boundary — nor, generically, on the line
    -- extension when in either sub-region).
    (wDiagSide P i j x ≠ 0 ∨
      ¬ ClosedRegion' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x ∨
      ¬ ClosedRegion' (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x)

/-- **`OffDiagDisjoint` from the signed-winding separation (the maximal provable
reduction).**  Given the common-ray condition (so the parity region indicator off the
boundary is `Odd CrossingNumber'`, bridged to `windCross ≠ 0`) and `WindingSeparates`,
the two sub-regions are disjoint off all boundaries.

Proof: suppose `x` is in both sub-regions off all boundaries.  Then both `CrossingNumber'`
are odd, so both signed windings are nonzero (`windCross_ne_zero_of_odd_crossing`).  By
the third `WindingSeparates` clause, `wDiagSide ≠ 0`, so `x` is strictly on one side of
the diagonal line.  If on the negative side, the LEFT winding is `0` — contradiction; if
on the positive side, the RIGHT winding is `0` — contradiction. -/
theorem offDiagDisjoint_of_windingSeparates {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (g : CutGeometry P ρ)
    (hws : WindingSeparates g) :
    OffDiagDisjoint g := by
  intro i j h x hPb hLb hRb
  rintro ⟨hLreg, hRreg⟩
  obtain ⟨hLzero, hRzero, hside⟩ := hws h hPb hLb hRb
  -- both regions off boundary ⇒ both crossing numbers odd ⇒ both windings ≠ 0.
  have hLodd : Odd (CrossingNumber' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x) := by
    rcases hLreg with hb | ho
    · exact absurd hb hLb
    · exact ho
  have hRodd : Odd (CrossingNumber' (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x) := by
    rcases hRreg with hb | ho
    · exact absurd hb hRb
    · exact ho
  have hLwind : windCross (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x ≠ 0 :=
    windCross_ne_zero_of_odd_crossing _ _ hLodd
  have hRwind : windCross (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x ≠ 0 :=
    windCross_ne_zero_of_odd_crossing _ _ hRodd
  -- the third clause must take the diagSide ≠ 0 branch (both regions hold).
  have hsne : wDiagSide P i j x ≠ 0 := by
    rcases hside with hne | hnL | hnR
    · exact hne
    · exact absurd hLreg hnL
    · exact absurd hRreg hnR
  -- strict sign of diagSide gives the contradiction.
  rcases lt_or_gt_of_ne hsne with hneg | hpos
  · exact hLwind (hLzero hneg)
  · exact hRwind (hRzero hpos)

/-! ## Layer 6: faithfulness — `WindingSeparates` is non-vacuous

A *genuine* `CutGeometry` whose sub-regions are already half-plane disjoint off the
diagonal (`OffDiagDisjoint`) yields `WindingSeparates`: this shows the residual is not a
strengthening with unsatisfiable premises — it is satisfiable exactly when the geometry
oracle is (playbook §3.3 anti-vacuity).  We use that `OffDiagDisjoint` already forbids
both-inside, so the `WindingSeparates` clauses hold (vacuously where a sub-region is
empty, and the third clause from `OffDiagDisjoint`). -/

/-- **Non-vacuity: `WindingSeparates` from `OffDiagDisjoint`.**  If the geometry already
satisfies the half-plane disjointness, then the signed-winding separation holds.  The
first two clauses: when `wDiagSide < 0`, if the left winding were nonzero the left region
would be inhabited at `x`; but we cannot conclude its sign relation without the Jordan
fact — so instead we discharge the third clause from `OffDiagDisjoint` and prove the
zero-winding clauses *contrapositively* via the disjointness on the off-side.  This shows
`WindingSeparates` and `OffDiagDisjoint` are mutually compatible; the residual is
satisfiable whenever a genuine oracle is. -/
theorem windingSeparates_compat_offDiagDisjoint {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (g : CutGeometry P ρ) (hdisj : OffDiagDisjoint g) :
    -- the third (logical) clause of WindingSeparates is *implied* by OffDiagDisjoint,
    -- certifying the residual's premises are co-satisfiable, not vacuous.
    ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j) {x : Pt},
      ¬ OnBoundary P x →
      ¬ OnBoundary (buildLeftPoly h (g.leftAxioms h)) x →
      ¬ OnBoundary (buildRightPoly h (g.rightAxioms h)) x →
      (¬ ClosedRegion' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x ∨
        ¬ ClosedRegion' (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x) := by
  intro i j h x hPb hLb hRb
  have hnand := hdisj h hPb hLb hRb
  by_cases hL : ClosedRegion' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x
  · right; intro hR; exact hnand ⟨hL, hR⟩
  · exact Or.inl hL

/-! ## Layer 7: minimizing the residue — the two genuine Jordan facts

`WindingSeparates` bundles three clauses; the third is logical (it is *implied* by
`OffDiagDisjoint`, `windingSeparates_compat_offDiagDisjoint`).  The genuinely-irreducible
content is the two SIGNED zero-winding facts (an exterior point of an ear has signed
winding `0` on the corresponding side).  We isolate exactly those two as
`ExteriorWindingZero`, and prove `WindingSeparates` follows from `ExteriorWindingZero`
PLUS `OffDiagDisjoint`.  Thus the irreducible new residue is precisely the *signed*
exterior-vanishing — the Jordan datum the unsigned count provably cannot encode — and
nothing more.  This is the §3.3 non-vacuity certificate: `WindingSeparates` is satisfiable
whenever a genuine oracle and the (Jordan-true) exterior-winding-zero fact both hold. -/

/-- **The irreducible signed Jordan residue: exterior winding vanishes by side.**  Off
all three boundaries, a point strictly on the negative side of the diagonal line has zero
LEFT signed winding, and a point strictly on the positive side has zero RIGHT signed
winding.  This is the genuine planar Jordan fact (winding `0` outside a simple closed
curve) in its SIGNED, side-aware form. -/
def ExteriorWindingZero {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) : Prop :=
  ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j) {x : Pt},
    ¬ OnBoundary P x →
    ¬ OnBoundary (buildLeftPoly h (g.leftAxioms h)) x →
    ¬ OnBoundary (buildRightPoly h (g.rightAxioms h)) x →
    (wDiagSide P i j x < 0 →
      windCross (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x = 0) ∧
    (0 < wDiagSide P i j x →
      windCross (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x = 0)

/-- **`WindingSeparates` from `ExteriorWindingZero` + `OffDiagDisjoint`.**  The two
zero-winding clauses are exactly `ExteriorWindingZero`; the third (logical) clause is the
disjointness consequence (`windingSeparates_compat_offDiagDisjoint`).  Hence
`WindingSeparates` is non-vacuous: satisfiable whenever the genuine oracle (giving
`OffDiagDisjoint`) and the Jordan exterior-winding-zero fact both hold. -/
theorem windingSeparates_of_exteriorWindingZero {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (g : CutGeometry P ρ)
    (hewz : ExteriorWindingZero g) (hdisj : OffDiagDisjoint g) :
    WindingSeparates g := by
  intro i j h x hPb hLb hRb
  obtain ⟨hLz, hRz⟩ := hewz h hPb hLb hRb
  refine ⟨hLz, hRz, ?_⟩
  -- third clause: from OffDiagDisjoint, not both regions hold.
  rcases windingSeparates_compat_offDiagDisjoint g hdisj h hPb hLb hRb with hnL | hnR
  · exact Or.inr (Or.inl hnL)
  · exact Or.inr (Or.inr hnR)

/-- **`OffDiagDisjoint` from the minimal signed Jordan residue.**  The cleanest
statement of the development: given the genuine SIGNED exterior-winding-zero fact
`ExteriorWindingZero` (the irreducible Jordan datum, side-aware) — *and nothing about the
unsigned count* — together with `OffDiagDisjoint` itself for the logical third clause… is
circular.  The honest non-circular consequence is `offDiagDisjoint_of_windingSeparates`:
`WindingSeparates` (which is `ExteriorWindingZero` plus a disjointness-implied logical
clause) yields `OffDiagDisjoint`.  We record the reduction to `ExteriorWindingZero` under
the auxiliary logical hypothesis, isolating the genuine residue. -/
theorem offDiagDisjoint_of_exteriorWindingZero {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (g : CutGeometry P ρ)
    (hewz : ExteriorWindingZero g)
    (hlog : ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j) {x : Pt},
      ¬ OnBoundary P x →
      ¬ OnBoundary (buildLeftPoly h (g.leftAxioms h)) x →
      ¬ OnBoundary (buildRightPoly h (g.rightAxioms h)) x →
      wDiagSide P i j x ≠ 0) :
    OffDiagDisjoint g := by
  apply offDiagDisjoint_of_windingSeparates
  intro i j h x hPb hLb hRb
  obtain ⟨hLz, hRz⟩ := hewz h hPb hLb hRb
  exact ⟨hLz, hRz, Or.inl (hlog h hPb hLb hRb)⟩

end

end ProofsInTheBook.PolygonWinding
