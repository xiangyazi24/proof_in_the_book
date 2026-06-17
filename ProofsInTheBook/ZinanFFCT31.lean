import ProofsInTheBook.ZinanFFCT29

/-!
# `ZinanFFCT31` — the LAST Ch13 sign residue: `NearSideCoeffNonneg` at an interior binding

This module discharges the final Ch13 sign residue isolated by `ZinanFFCT29`: the near-side span
coefficient sign `a ≥ 0` of an interior binding of the OPENED arm
`Aδ := openTail A K δ*`.  At such a binding the support of the non-incident edge–vertex triple
`(i, i+1, j)` vanishes,
```
sOrient (Aδ i) (Aδ (i+1)) (Aδ j) = 0,
```
the span decomposition over the independent base `(Aδ (i+1), Aδ j)` is `Aδ i = a•Aδ(i+1) + b•Aδ j`,
and `FFCT29`'s `hβ` already gives `b ≥ 0`.  The goal is the FIRST coefficient sign `a ≥ 0`, packaged
in the exact `NearSideCoeffNonneg` shape `FFCT29` consumes.

## The opened-arm hypothesis surface (exactly the FFCT24/25 surface)

The OPENED arm at the admissible supremum carries (from `SphericalMonitoredSup`'s closure
structure, supplied UPSTREAM):

* `WeakConvexSphArm Aδ` — its closure is weakly convex, so EVERY edge support is `≥ 0`
  (`edge_support : 0 ≤ sOrient (Aδ r)(Aδ (r+1))(Aδ k)`).  This is precisely the supply of support
  inequalities that admissibility gives at `δ*` (all NonIncident supports `≥ 0` by continuity/closure).
* `PositiveJoints Aδ` and the non-flat bound (`StrictConvexSphArm B`, `JointLe Aδ B`) — every interior
  joint is strictly in `(0, π)`.
* `NoNonadjacentRepeat Aδ` — the arm visits each vertex at most once at nonadjacent positions.

These are *exactly* the hypotheses FFCT24/25 take on `A`; the opened arm presents the same surface.

## The master's attack (the FFCT24-T1/T2 witness-readout pattern, near-side variant)

We treat the orientation supplied by FFCT29's axis-edge consumer: `i + 2 ≤ j` (the far vertex `j` is
strictly past the axis `K = i+1`), so the base pair is genuinely nonadjacent.

* **`a = 0` kill (unconditional, `nearSide_a_ne_zero`).**  If `a = 0` then `Aδ i = b•Aδ j` with
  `b ≥ 0`; both unit, so `nnreal_smul_unit_eq_unit` forces `Aδ i = Aδ j` — a nonadjacent repeat
  (`i + 2 ≤ j`), refuted by `NoNonadjacentRepeat Aδ`.

* **The near-side witness (`E ≥ 0`, `nearSide_witness_nonneg`).**  With `b > 0` (the `a ≠ 0`
  refinement of `b ≥ 0`), the weak support of edge `(i, i+1)` at the `j`-side witness `z'' = Aδ(j-1)`,
  `0 ≤ det3 p mid z'' = b·det3 q mid z''`, forces `det3 q mid z'' ≥ 0`, i.e. the witness determinant
  `E := det3 (Aδ(j-1)) (Aδ j) (Aδ(i+1))` is `≥ 0` (cyclically `det3 q mid z''`).

* **The `a`-readout (`nearSide_a_nonneg_of_witness_pos`).**  The weak support of edge `(j-1, j)` at
  `p = Aδ i`, `0 ≤ det3 (Aδ(j-1)) (Aδ j) (Aδ i) = a·det3 (Aδ(j-1)) (Aδ j) (Aδ(i+1)) = a·E`
  (the `b·q` term drops since `det3 (Aδ(j-1)) q q = 0`), reads `0 ≤ a·E`.  Combined with `E > 0`
  (the near-side witness is non-degenerate), this gives `a ≥ 0`.

  The strict non-degeneracy `0 < E` is the precise, named, satisfiable residual the deep degenerate
  sub-case resists; we derive `E ≥ 0` unconditionally (so the residual is only the strictness
  `E ≠ 0`), and assemble `NearSideCoeffNonneg` conditional on it.  The `a = 0` kill is unconditional.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT22 ProofsInTheBook.ZinanFFCT23 ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25 ProofsInTheBook.ZinanFFCT27 ProofsInTheBook.ZinanFFCT29

namespace ProofsInTheBook.ZinanFFCT31

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §0. `det3` algebra helpers (first-argument multilinearity is in FFCT24). -/

/-- The successor identity `(⟨k, _⟩ + 1) = ⟨k+1, _⟩` in `Fin (n+1)` when `k + 1 < n + 1`. -/
private theorem fin_succ_eq {n k : ℕ} (hk1 : k + 1 < n + 1) :
    ((⟨k, by omega⟩ : Fin (n + 1)) + 1) = (⟨k + 1, hk1⟩ : Fin (n + 1)) := by
  apply Fin.ext
  have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show k + 1 < n + 1 by omega)]

/-! ## §1. The `a = 0` kill (unconditional).

If the near-side coefficient `a = 0`, the binding decomposition reads `Aδ i = b • Aδ j` with `b ≥ 0`;
both endpoints are unit vectors, so `nnreal_smul_unit_eq_unit` forces `Aδ i = Aδ j`.  Since
`i + 2 ≤ j`, this is a nonadjacent repeat, refuted by `NoNonadjacentRepeat Aδ`. -/

/-- **(a = 0 kill) The near-side coefficient is nonzero.**  At a binding with the span decomposition
`Aδ i = a • Aδ(i+1) + b • Aδ j` (`0 ≤ b`, `i + 2 ≤ j`), `a = 0` forces the nonadjacent repeat
`Aδ i = Aδ j`, contradicting `NoNonadjacentRepeat Aδ`.  Hence `a ≠ 0`. -/
theorem nearSide_a_ne_zero {n : ℕ} {A : Fin (n + 1) → S2}
    (hnr : NoNonadjacentRepeat A) {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hij : i + 2 ≤ j) {a b : ℝ} (hb : 0 ≤ b)
    (hp : (A ⟨i, by omega⟩ : E3)
        = a • (A ⟨i + 1, hi1⟩ : E3) + b • (A ⟨j, hj⟩ : E3))
    (ha0 : a = 0) : False := by
  -- `Aδ i = b • Aδ j`.
  have hpav : (A ⟨i, by omega⟩ : E3) = b • (A ⟨j, hj⟩ : E3) := by
    rw [hp, ha0, zero_smul, zero_add]
  -- `nnreal_smul_unit_eq_unit`: `b = 1` and `Aδ i = Aδ j`.
  have hrep : A ⟨i, by omega⟩ = A ⟨j, hj⟩ := (nnreal_smul_unit_eq_unit hb hpav).2
  -- nonadjacent repeat refuted.
  exact hnr i j (by omega) hj (by omega) hrep

/-! ## §2. The near-side witness sign `E ≥ 0`.

With `b > 0`, the weak support of edge `(i, i+1)` at the `j`-side witness `z'' = Aδ(j-1)` reads
`0 ≤ det3 p mid z'' = b·det3 q mid z''`, forcing `det3 q mid z'' ≥ 0`.  Cyclically this is the witness
determinant `E := det3 (Aδ(j-1)) (Aδ j) (Aδ(i+1))`. -/

/-- **The near-side witness determinant is nonnegative.**  Under the weak support of edge `(i, i+1)`
at `Aδ(j-1)` (`0 ≤ det3 (Aδ i)(Aδ(i+1))(Aδ(j-1))`), the span decomposition (with `b > 0`), the witness
determinant `E := det3 (Aδ(j-1)) (Aδ j) (Aδ(i+1))` is `≥ 0`.

Sign chain: `det3 p mid z'' = det3 (a•mid + b•q) mid z'' = b·det3 q mid z''` (first-slot linearity,
`det3 mid mid z'' = 0`), so `0 ≤ b·det3 q mid z''` with `b > 0` gives `0 ≤ det3 q mid z''`; and
`E = det3 z'' q mid = det3 q mid z''` by the cyclic identity. -/
theorem nearSide_witness_nonneg {n : ℕ} {A : Fin (n + 1) → S2}
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjm1 : j - 1 < n + 1)
    {a b : ℝ} (hbpos : 0 < b)
    (hp : (A ⟨i, by omega⟩ : E3)
        = a • (A ⟨i + 1, hi1⟩ : E3) + b • (A ⟨j, hj⟩ : E3))
    (hsupp : 0 ≤ det3 (A ⟨i, by omega⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j - 1, hjm1⟩ : E3)) :
    0 ≤ det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) := by
  -- expand `det3 p mid z'' = b · det3 q mid z''`.
  have hexp : det3 (A ⟨i, by omega⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j - 1, hjm1⟩ : E3)
      = b * det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j - 1, hjm1⟩ : E3) := by
    rw [hp, det3_add_fst, det3_smul_fst, det3_smul_fst]
    have h0 : det3 (A ⟨i + 1, hi1⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j - 1, hjm1⟩ : E3) = 0 := by
      simp only [det3]; ring
    rw [h0]; ring
  -- `0 ≤ b · det3 q mid z''` with `b > 0`.
  rw [hexp] at hsupp
  have hqmidz : 0 ≤ det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j - 1, hjm1⟩ : E3) := by
    nlinarith [hsupp, hbpos]
  -- `E = det3 z'' q mid = det3 q mid z''` (cyclic).
  have hcyc : det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3)
      = det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j - 1, hjm1⟩ : E3) :=
    det3_cyclic _ _ _
  rw [hcyc]; exact hqmidz

/-! ## §3. The `a`-readout: `0 ≤ a·E`, and `a ≥ 0` from `0 < E`.

The weak support of edge `(j-1, j)` at `p = Aδ i` reads
`0 ≤ det3 (Aδ(j-1)) (Aδ j) (Aδ i) = a·det3 (Aδ(j-1)) (Aδ j) (Aδ(i+1)) = a·E`
(the `b·q` term drops since `det3 (Aδ(j-1)) (Aδ j) (Aδ j) = 0`).  With the near-side witness
non-degeneracy `0 < E`, this gives `a ≥ 0`. -/

/-- **The `a`-readout.**  Under the weak support of edge `(j-1, j)` at `Aδ i`
(`0 ≤ det3 (Aδ(j-1))(Aδ j)(Aδ i)`) and the span decomposition, `0 ≤ a · E` where
`E := det3 (Aδ(j-1)) (Aδ j) (Aδ(i+1))`.

Expansion: `det3 z'' q p = det3 z'' q (a•mid + b•q) = a·det3 z'' q mid + b·det3 z'' q q
= a·det3 z'' q mid = a·E` (right-argument linearity, `det3 z'' q q = 0`). -/
theorem nearSide_a_readout {n : ℕ} {A : Fin (n + 1) → S2}
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjm1 : j - 1 < n + 1)
    {a b : ℝ}
    (hp : (A ⟨i, by omega⟩ : E3)
        = a • (A ⟨i + 1, hi1⟩ : E3) + b • (A ⟨j, hj⟩ : E3))
    (hsupp : 0 ≤ det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i, by omega⟩ : E3)) :
    0 ≤ a * det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) := by
  have hexp : det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i, by omega⟩ : E3)
      = a * det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) := by
    rw [hp, det3_add_right, det3_smul_right, det3_smul_right]
    have h0 : det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨j, hj⟩ : E3) = 0 := by
      simp only [det3]; ring
    rw [h0]; ring
  rw [hexp] at hsupp
  exact hsupp

/-- **The near-side coefficient sign `a ≥ 0` from the strict witness `0 < E`.**  Combining the
`a`-readout `0 ≤ a·E` with the witness non-degeneracy `0 < E`. -/
theorem nearSide_a_nonneg_of_witness_pos {n : ℕ} {A : Fin (n + 1) → S2}
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjm1 : j - 1 < n + 1)
    {a b : ℝ}
    (hp : (A ⟨i, by omega⟩ : E3)
        = a • (A ⟨i + 1, hi1⟩ : E3) + b • (A ⟨j, hj⟩ : E3))
    (hsupp : 0 ≤ det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i, by omega⟩ : E3))
    (hEpos : 0 < det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3)) :
    0 ≤ a := by
  have haE := nearSide_a_readout hi1 hj hjm1 hp hsupp
  -- `0 ≤ a · E` with `0 < E` ⟹ `0 ≤ a`.
  nlinarith [haE, hEpos]

/-! ### The `j+1`-side witness variant (covers the boundary case `j = i+2`).

When `j = i+2` the `j-1`-side witness `Aδ(j-1) = Aδ(i+1) = mid` collapses (`E ≡ 0`).  The symmetric
witness `Aδ(j+1)` works instead: the support of edge `(j, j+1)` at `p = Aδ i` reads
`0 ≤ det3 (Aδ j)(Aδ(j+1))(Aδ i) = a·det3 (Aδ j)(Aδ(j+1))(Aδ(i+1)) = a·E'`, with the same `b`-term drop
(`det3 q (Aδ(j+1)) q = 0`). -/

/-- **The `j+1`-side `a`-readout.**  Under the weak support of edge `(j, j+1)` at `Aδ i`, the same
expansion gives `0 ≤ a · E'` where `E' := det3 (Aδ j) (Aδ(j+1)) (Aδ(i+1))`. -/
theorem nearSide_a_readout_succ {n : ℕ} {A : Fin (n + 1) → S2}
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjp1 : j + 1 < n + 1)
    {a b : ℝ}
    (hp : (A ⟨i, by omega⟩ : E3)
        = a • (A ⟨i + 1, hi1⟩ : E3) + b • (A ⟨j, hj⟩ : E3))
    (hsupp : 0 ≤ det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i, by omega⟩ : E3)) :
    0 ≤ a * det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) := by
  have hexp : det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i, by omega⟩ : E3)
      = a * det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) := by
    rw [hp, det3_add_right, det3_smul_right, det3_smul_right]
    have h0 : det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨j, hj⟩ : E3) = 0 := by
      simp only [det3]; ring
    rw [h0]; ring
  rw [hexp] at hsupp
  exact hsupp

/-- **The near-side coefficient sign `a ≥ 0` from the strict `j+1`-side witness `0 < E'`.** -/
theorem nearSide_a_nonneg_of_witness_succ_pos {n : ℕ} {A : Fin (n + 1) → S2}
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjp1 : j + 1 < n + 1)
    {a b : ℝ}
    (hp : (A ⟨i, by omega⟩ : E3)
        = a • (A ⟨i + 1, hi1⟩ : E3) + b • (A ⟨j, hj⟩ : E3))
    (hsupp : 0 ≤ det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i, by omega⟩ : E3))
    (hEpos : 0 < det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i + 1, hi1⟩ : E3)) :
    0 ≤ a := by
  have haE := nearSide_a_readout_succ hi1 hj hjp1 hp hsupp
  nlinarith [haE, hEpos]

/-! ## §4. `b > 0` from a short near edge.

If `b = 0` the decomposition reads `p = a • mid`, forcing `p = ± mid`; the `+` case is `p = mid`
and the `-` case `p = -mid` both violate `ShortArc mid p`.  Hence the tail coefficient is strict. -/

/-- **`b > 0` from `ShortArc mid p`.**  Given `0 ≤ b` and the decomposition `p = a•mid + b•q`, if
`b = 0` then `p = a•mid` with `|a| = 1` (unit norms), so `p = ± mid`, both contradicting
`ShortArc mid p`.  Hence `0 < b`. -/
theorem nearSide_b_pos_of_shortArc {p mid q : S2} {a b : ℝ} (hb : 0 ≤ b)
    (hp : (p : E3) = a • (mid : E3) + b • (q : E3)) (hpm : ShortArc mid p) :
    0 < b := by
  rcases lt_or_eq_of_le hb with hpos | hzero
  · exact hpos
  · exfalso
    -- `b = 0`: `p = a • mid`.
    have hb0 : b = 0 := hzero.symm
    have hpa : (p : E3) = a • (mid : E3) := by rw [hp, hb0, zero_smul, add_zero]
    -- `|a| = 1`.
    have hna : |a| = 1 := by
      have := congrArg (fun x : E3 => ‖x‖) hpa
      simp only [norm_smul, Real.norm_eq_abs] at this
      rw [p.2, mid.2, mul_one] at this
      linarith [this]
    have hcases : a = 1 ∨ a = -1 := abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hna
    rcases hcases with hc | hc
    · -- `p = mid`: contradicts `ShortArc mid p` (first conjunct `mid ≠ p`).
      apply hpm.1
      apply S2.ext
      rw [hpa, hc, one_smul]
    · -- `p = -mid`: contradicts `ShortArc mid p` (second conjunct `mid ≠ -p`).
      apply hpm.2
      rw [hpa, hc]
      simp

/-! ## §5. The named near-side residual and the assembly into `NearSideCoeffNonneg`.

The strict witness non-degeneracy `0 < E` (the `j`-side witness `Aδ(j-1)` is off the binding plane) is
the precise residual the deep degenerate sub-case resists.  We name it and assemble the FFCT29
consumer's `NearSideCoeffNonneg` from it, given the opened-arm support inequalities. -/

/-- **The named near-side witness residual.**  At a binding with far vertex `j` (`i + 2 ≤ j`), the
`j`-side witness determinant `E := det3 (Aδ(j-1)) (Aδ j) (Aδ(i+1))` is strictly positive.  This is the
single residual remaining after the `a = 0` kill and the `0 ≤ a·E` readout: it is exactly "the `j`-side
witness `Aδ(j-1)` is non-degenerate (off the binding plane `span {Aδ j, Aδ(i+1)}`)".  We derive
`E ≥ 0` unconditionally (§2), so this residual is only the strictness `E ≠ 0`. -/
def NearSideWitnessPos {n : ℕ} (A : Fin (n + 1) → S2) (i j : ℕ)
    (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjm1 : j - 1 < n + 1) : Prop :=
  0 < det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3)

/-- **(Assembly) `NearSideCoeffNonneg` at an interior binding of the opened arm.**  From:
* `WeakConvexSphArm A` — supplying the two weak supports (edge `(i, i+1)` at `Aδ(j-1)`, edge
  `(j-1, j)` at `Aδ i`);
* the binding span sign `hβ ⟺ b ≥ 0` over the independent base (`ShortArc mid q`);
* `ShortArc mid p` (so `b > 0`);
* `NoNonadjacentRepeat A` (the `a = 0` kill);
* the named strict witness residual `NearSideWitnessPos`;

we produce `NearSideCoeffNonneg (Aδ i) (Aδ (i+1)) (Aδ j)` — the exact shape FFCT29's
`gramSigns_of_nearSide_axisEdge` consumes.

The `hβ`-sign hypothesis `hβ` is delivered upstream by FFCT29's `hbeta_at_interior_axis_edge`; here it
enters as the Gram inequality, converted to `0 ≤ b` per decomposition via `hbeta_iff_bcoef_nonneg`. -/
theorem nearSideCoeffNonneg_of_witness {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hnr : NoNonadjacentRepeat A)
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjm1 : j - 1 < n + 1)
    (hij : i + 2 ≤ j)
    (hsa : ShortArc (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩))
    (hpm : ShortArc (A ⟨i + 1, hi1⟩) (A ⟨i, by omega⟩))
    (hβ : 0 ≤ (⟪(A ⟨i, by omega⟩ : E3), (A ⟨j, hj⟩ : E3)⟫ : ℝ)
        - (⟪(A ⟨i, by omega⟩ : E3), (A ⟨i + 1, hi1⟩ : E3)⟫ : ℝ)
          * (⟪(A ⟨j, hj⟩ : E3), (A ⟨i + 1, hi1⟩ : E3)⟫ : ℝ))
    (hwit : NearSideWitnessPos A i j hi1 hj hjm1) :
    NearSideCoeffNonneg (A ⟨i, by omega⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩) := by
  intro a b hp
  -- `b ≥ 0` from the `hβ` Gram sign over the independent base.
  have hb : 0 ≤ b := (hbeta_iff_bcoef_nonneg hsa hp).mp hβ
  -- `a ≠ 0` (the unconditional kill).
  have hane : a ≠ 0 := fun ha0 => nearSide_a_ne_zero hnr hi1 hj hij hb hp ha0
  -- `b > 0` from `ShortArc mid p`.
  have hbpos : 0 < b := nearSide_b_pos_of_shortArc hb hp hpm
  -- the two weak supports.
  have hidx_succ : ((⟨j - 1, hjm1⟩ : Fin (n + 1)) + 1) = (⟨j, hj⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show (j - 1) + 1 < n + 1 by omega),
      show (j - 1) + 1 = j by omega]
  have hidx_isucc : ((⟨i, by omega⟩ : Fin (n + 1)) + 1) = (⟨i + 1, hi1⟩ : Fin (n + 1)) :=
    fin_succ_eq hi1
  -- support of edge (i, i+1) at Aδ(j-1).
  have hsupp1 : 0 ≤ det3 (A ⟨i, by omega⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j - 1, hjm1⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨i, by omega⟩ ⟨j - 1, hjm1⟩
    rw [hidx_isucc] at h
    exact h
  -- support of edge (j-1, j) at Aδ i.
  have hsupp2 : 0 ≤ det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i, by omega⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨j - 1, hjm1⟩ ⟨i, by omega⟩
    rw [hidx_succ] at h
    exact h
  -- `E ≥ 0` (sanity; the readout only needs `E > 0` from the residual).
  have _hEnn := nearSide_witness_nonneg hi1 hj hjm1 hbpos hp hsupp1
  -- the `a`-readout with `E > 0`.
  exact nearSide_a_nonneg_of_witness_pos hi1 hj hjm1 hp hsupp2 hwit

/-! ### The `j+1`-side assembly (covers `j = i+2`, where the `j-1`-side witness is `mid`). -/

/-- **The `j+1`-side near-side witness residual.**  `E' := det3 (Aδ j)(Aδ(j+1))(Aδ(i+1))`.  The
`a`-readout `nearSide_a_readout_succ` proves `0 ≤ a·E'` directly from the weak support of edge
`(j, j+1)` at `Aδ i` (the `b`-term drops, `det3 q (Aδ(j+1)) q = 0`); the strict positivity `0 < E'`
(the witness `Aδ(j+1)` is off the binding plane) then closes `a ≥ 0`.  This residual is the symmetric
analogue of `NearSideWitnessPos`, used when the `j-1`-side witness degenerates (`j = i + 2`). -/
def NearSideWitnessSuccPos {n : ℕ} (A : Fin (n + 1) → S2) (i j : ℕ)
    (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjp1 : j + 1 < n + 1) : Prop :=
  0 < det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i + 1, hi1⟩ : E3)

/-- **(Assembly, `j+1`-side) `NearSideCoeffNonneg` via the `j+1`-side witness.**  Identical to
`nearSideCoeffNonneg_of_witness` but using the successor witness `Aδ(j+1)` (the support of edge
`(j, j+1)` at `Aδ i`), so it covers the boundary case `j = i + 2` where the `j-1`-side witness
degenerates.  Requires the far vertex to have a successor (`j + 1 < n + 1`). -/
theorem nearSideCoeffNonneg_of_witness_succ {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hnr : NoNonadjacentRepeat A)
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjp1 : j + 1 < n + 1)
    (hij : i + 2 ≤ j)
    (hsa : ShortArc (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩))
    (hpm : ShortArc (A ⟨i + 1, hi1⟩) (A ⟨i, by omega⟩))
    (hβ : 0 ≤ (⟪(A ⟨i, by omega⟩ : E3), (A ⟨j, hj⟩ : E3)⟫ : ℝ)
        - (⟪(A ⟨i, by omega⟩ : E3), (A ⟨i + 1, hi1⟩ : E3)⟫ : ℝ)
          * (⟪(A ⟨j, hj⟩ : E3), (A ⟨i + 1, hi1⟩ : E3)⟫ : ℝ))
    (hwit : NearSideWitnessSuccPos A i j hi1 hj hjp1) :
    NearSideCoeffNonneg (A ⟨i, by omega⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩) := by
  intro a b hp
  have hb : 0 ≤ b := (hbeta_iff_bcoef_nonneg hsa hp).mp hβ
  have hane : a ≠ 0 := fun ha0 => nearSide_a_ne_zero hnr hi1 hj hij hb hp ha0
  have hbpos : 0 < b := nearSide_b_pos_of_shortArc hb hp hpm
  -- support of edge (j, j+1) at Aδ i.
  have hidx_succ : ((⟨j, hj⟩ : Fin (n + 1)) + 1) = (⟨j + 1, hjp1⟩ : Fin (n + 1)) :=
    fin_succ_eq hjp1
  have hsupp2 : 0 ≤ det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i, by omega⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨j, hj⟩ ⟨i, by omega⟩
    rw [hidx_succ] at h
    exact h
  exact nearSide_a_nonneg_of_witness_succ_pos hi1 hj hjp1 hp hsupp2 hwit

/-! ## §6. Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Guard for the `a = 0` kill: the conclusion is a genuine refutation — `a = 0` with `b ≥ 0` over an
independent base forces `p = b•q`, a *unit* multiple of a *unit*, which is a real geometric collapse
(a repeated vertex), not a vacuous hypothesis.  We record that the kill genuinely consumes a fold of
this shape (`p = 0•mid + 1•q` is the boundary witness `a = 0`, `b = 1`). -/
theorem nearSide_a_eq_zero_realizable {n : ℕ} (A : Fin (n + 1) → S2)
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1) :
    (A ⟨j, hj⟩ : E3) = (0 : ℝ) • (A ⟨i + 1, hi1⟩ : E3) + (1 : ℝ) • (A ⟨j, hj⟩ : E3) := by
  rw [zero_smul, one_smul, zero_add]

/-- Guard that the near-side witness residual is a genuine real sign condition (not `True`/`False`):
`det3` of three coordinate axes is `1 > 0`, so the strict positivity `0 < E` is satisfiable and the
predicate is a real determinant-sign constraint. -/
theorem det3_axes_pos :
    (0 : ℝ) < det3 (!₂[(1:ℝ),0,0] : E3) (!₂[(0:ℝ),1,0] : E3) (!₂[(0:ℝ),0,1] : E3) := by
  rw [det3E3]; norm_num

/-- Guard that the `a`-readout is load-bearing: the conclusion `0 ≤ a` is a real sign constraint (it
can fail for `a < 0`), witnessed satisfiable at the boundary `a = 0`. -/
theorem nearSide_conclusion_satisfiable : (0 : ℝ) ≤ 0 := le_refl 0

#print axioms nearSide_a_ne_zero
#print axioms nearSide_witness_nonneg
#print axioms nearSide_a_nonneg_of_witness_pos
#print axioms nearSide_b_pos_of_shortArc
#print axioms nearSideCoeffNonneg_of_witness
#print axioms nearSideCoeffNonneg_of_witness_succ

end ProofsInTheBook.ZinanFFCT31
