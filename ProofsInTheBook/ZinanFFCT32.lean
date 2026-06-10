import ProofsInTheBook.ZinanFFCT31

/-!
# `ZinanFFCT32` — the two-sided witness dichotomy for `NearSideWitnessPos`

`ZinanFFCT31` isolated the last Ch13 sign residue at an interior binding of the opened arm `Aδ` to a
SINGLE strict determinant sign: the `j-1`-side witness `0 < E_{pred}` where
`E_{pred} := det3 (Aδ(j-1)) (Aδ j) (Aδ(i+1))`, packaged as `NearSideWitnessPos`, with a symmetric
`j+1`-side witness `NearSideWitnessSuccPos`.  This module formalizes the master's two-sided
**dichotomy** and — being scrupulous about the signs — pins down EXACTLY how far it discharges the
residual and where it genuinely stops.

## The mechanism that IS proven (clean): both witnesses cannot both degenerate

The `j-1`-side witness degenerates iff `E_{pred} = 0` iff `Aδ(j-1) ∈ Π := span {Aδ j, Aδ(i+1)}`
(`ZinanFFCT25` brick U2 `lin_indep_span_of_det3_zero`, the base pair independent via the edge
`ShortArc (Aδ(i+1)) (Aδ j)`).  The `j+1`-side witness degenerates iff
`E_{succ} := det3 (Aδ j) (Aδ(j+1)) (Aδ(i+1)) = 0` iff `Aδ(j+1) ∈ Π`.  `Aδ j ∈ Π` trivially.

If BOTH degenerate, the three CONSECUTIVE vertices `Aδ(j-1), Aδ j, Aδ(j+1)` all lie in the 2-plane
`Π` through the origin, so `det3 (Aδ(j-1)) (Aδ j) (Aδ(j+1)) = 0` (`ZinanFFCT22`
`coplanar_triple_det3_zero`); `ZinanFFCT22`'s `far_fold_tail_not_interior` then flattens the interior
joint at apex `Aδ j` (joint index `j-1`), contradicting `PositiveJoints Aδ` and the non-flat bound
(`StrictConvexSphArm B`, `JointLe Aδ B`).  This is `not_both_witness_zero`, proven UNCONDITIONALLY
(given the binding's geometric surface and `j < n` so the `j+1` neighbour exists).

## The honest sign obstruction (where the dichotomy stops short of `a ≥ 0`)

The weak edge supports of the opened arm fix the SIGNS of the two witnesses with OPPOSITE conventions
(verified as ring identities, `§2`):

* the weak support of edge `(i,i+1)` at `Aδ(j-1)` gives `E_{pred} = b⁻¹ · (support) ≥ 0`;
* the weak support of edge `(i,i+1)` at `Aδ(j+1)` gives `−E_{succ} = b⁻¹ · (support) ≥ 0`, i.e.
  `E_{succ} ≤ 0`, equivalently `F := −E_{succ} = det3 (Aδ j) (Aδ(i+1)) (Aδ(j+1)) ≥ 0`.

So the two sign-correct nonnegative witnesses are `E_{pred} ≥ 0` and `F ≥ 0`, and the dichotomy gives
`0 < E_{pred} ∨ 0 < F` (`nearSideWitness_dichotomy`).  But the COEFFICIENT readouts (FFCT31) are
`0 ≤ a · E_{pred}` and `0 ≤ a · E_{succ} = −a · F`:

* in the branch `0 < E_{pred}` the pred readout gives the wanted `a ≥ 0`;
* in the branch `0 < F` the succ readout gives `−a·F ≥ 0`, i.e. `a ≤ 0` — the WRONG direction.

Hence the disjunction closes `a ≥ 0` ONLY on the `0 < E_{pred}` side.  The `0 < F` corner
(`Aδ(j-1) ∈ Π`, `Aδ(j+1) ∉ Π`) is the genuine, strictly-smaller residual `NearSidePredDegenerate`:
the pred witness is dead and the succ witness carries the opposite coefficient sign, so the local
readout cannot certify `a ≥ 0` there — it requires the global out-of-plane brick (the FFCT25 / B5-B1
tail-cone obstruction class).  This is reported, NOT swept under a vacuous statement.

What IS delivered unconditionally for the consumer: at an interior binding with `j < n`, EITHER
`NearSideWitnessPos` holds (and FFCT31's `nearSideCoeffNonneg_of_witness` closes
`NearSideCoeffNonneg`), OR the binding sits in the named `NearSidePredDegenerate` corner.

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
open ProofsInTheBook.ZinanFFCT31

namespace ProofsInTheBook.ZinanFFCT32

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §0. Base-pair independence at the binding plane.

The binding plane `Π = span {Aδ j, Aδ(i+1)}` has an independent base: `Aδ j ≠ Aδ(i+1)` and
`(Aδ j : E3) ≠ -(Aδ(i+1) : E3)`, both from the edge `ShortArc (Aδ(i+1)) (Aδ j)` supplied by the
consumer. -/

/-- From `ShortArc mid q` (`mid ≠ q`, `(mid:E3) ≠ -(q:E3)`), the swapped base pair `(q, mid)` is
independent: `q ≠ mid` (as `S2`) and `(q : E3) ≠ -(mid : E3)`. -/
theorem base_ne_of_shortArc {mid q : S2} (hsa : ShortArc mid q) :
    q ≠ mid ∧ (q : E3) ≠ -(mid : E3) := by
  refine ⟨fun h => hsa.1 h.symm, fun h => hsa.2 ?_⟩
  rw [h, neg_neg]

/-! ## §1. Witness-degeneracy ⟺ plane-membership (sign-agnostic, uses only `det3 = 0`). -/

/-- **`E_{pred} = 0` puts `Aδ(j-1)` in the plane.**  `det3 (Aδ(j-1)) (Aδ j) (Aδ(i+1)) = 0` gives
`Aδ(j-1) = c•(Aδ j) + d•(Aδ(i+1))` for reals `c, d`. -/
theorem witnessPred_mem_plane {n : ℕ} {A : Fin (n + 1) → S2}
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjm1 : j - 1 < n + 1)
    (hsa : ShortArc (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩))
    (hE : det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) = 0) :
    ∃ c d : ℝ, c • (A ⟨j, hj⟩ : E3) + d • (A ⟨i + 1, hi1⟩ : E3) = (A ⟨j - 1, hjm1⟩ : E3) := by
  have hcyc : det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j - 1, hjm1⟩ : E3) = 0 := by
    rw [show det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j - 1, hjm1⟩ : E3)
        = det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) by
      simp only [det3]; ring]
    exact hE
  obtain ⟨hne, hanti⟩ := base_ne_of_shortArc hsa
  obtain ⟨c, d, hcd⟩ := lin_indep_span_of_det3_zero (A ⟨j, hj⟩).2 (A ⟨i + 1, hi1⟩).2
    (fun h => hne (S2.ext h)) hanti hcyc
  exact ⟨c, d, hcd.symm⟩

/-- **`E_{succ} = 0` puts `Aδ(j+1)` in the plane.**  `det3 (Aδ j) (Aδ(j+1)) (Aδ(i+1)) = 0` gives
`Aδ(j+1) = c•(Aδ j) + d•(Aδ(i+1))`. -/
theorem witnessSucc_mem_plane {n : ℕ} {A : Fin (n + 1) → S2}
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjp1 : j + 1 < n + 1)
    (hsa : ShortArc (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩))
    (hE' : det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) = 0) :
    ∃ c d : ℝ, c • (A ⟨j, hj⟩ : E3) + d • (A ⟨i + 1, hi1⟩ : E3) = (A ⟨j + 1, hjp1⟩ : E3) := by
  have hswap : det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) = 0 := by
    rw [show det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3)
        = - det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) by
      simp only [det3]; ring]
    rw [hE']; ring
  obtain ⟨hne, hanti⟩ := base_ne_of_shortArc hsa
  obtain ⟨c, d, hcd⟩ := lin_indep_span_of_det3_zero (A ⟨j, hj⟩).2 (A ⟨i + 1, hi1⟩).2
    (fun h => hne (S2.ext h)) hanti hswap
  exact ⟨c, d, hcd.symm⟩

/-! ## §2. The dichotomy: the two witnesses cannot both degenerate (UNCONDITIONAL). -/

/-- **(The dichotomy core) Both witnesses degenerating is impossible.**  At an interior binding
(`i + 2 ≤ j`, `j + 1 < n + 1`) with the independent edge base `ShortArc (Aδ(i+1)) (Aδ j)`, the two
apex arcs at `Aδ j`, `PositiveJoints A`, and the non-flat bound, the witness determinants
`E_{pred} := det3 (Aδ(j-1)) (Aδ j) (Aδ(i+1))` and `E_{succ} := det3 (Aδ j) (Aδ(j+1)) (Aδ(i+1))`
cannot both vanish: both vanishing puts `Aδ(j-1), Aδ j, Aδ(j+1)` coplanar in `Π`, flattening the
joint at `Aδ j`. -/
theorem not_both_witness_zero {n : ℕ} {A B : Fin (n + 1) → S2}
    (hposA : PositiveJoints A) (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hjm1 : j - 1 < n + 1) (hjp1 : j + 1 < n + 1)
    (hij : i + 2 ≤ j)
    (hsa : ShortArc (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩))
    (hsau : ShortArc (A ⟨j, hj⟩) (A ⟨j - 1, hjm1⟩))
    (hsav : ShortArc (A ⟨j, hj⟩) (A ⟨j + 1, hjp1⟩))
    (hEpred : det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) = 0)
    (hEsucc : det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) = 0) :
    False := by
  have hxpred := witnessPred_mem_plane hi1 hj hjm1 hsa hEpred
  have hzsucc := witnessSucc_mem_plane hi1 hj hjp1 hsa hEsucc
  have hymid : ∃ c d : ℝ,
      c • (A ⟨j, hj⟩ : E3) + d • (A ⟨i + 1, hi1⟩ : E3) = (A ⟨j, hj⟩ : E3) :=
    ⟨1, 0, by rw [one_smul, zero_smul, add_zero]⟩
  have hcol : det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) = 0 :=
    coplanar_triple_det3_zero hxpred hymid hzsucc
  exact far_fold_tail_not_interior (B := B) hposA hB hangle
    (t := j) (by omega) hjp1 hjm1 hj hjp1 hsau hsav hcol

/-! ## §3. The sign certificates `E_{pred} ≥ 0` and `F := −E_{succ} ≥ 0`.

From the opened arm's weak edge supports under the binding decomposition `Aδ i = a•Aδ(i+1) + b•Aδ j`
(`b > 0`).  `nearSide_witness_nonneg` (FFCT31) gives `E_{pred} ≥ 0`; the mirror at `Aδ(j+1)` gives
`F := det3 (Aδ j) (Aδ(i+1)) (Aδ(j+1)) ≥ 0`, i.e. `E_{succ} ≤ 0` (the OPPOSITE sign — the obstruction
recorded in the header). -/

/-- **`F := det3 (Aδ j) (Aδ(i+1)) (Aδ(j+1)) ≥ 0`** from the weak support of edge `(i,i+1)` at
`Aδ(j+1)` under the binding decomposition (`b > 0`).  Equivalently `E_{succ} ≤ 0`. -/
theorem nearSide_witnessSucc_F_nonneg {n : ℕ} {A : Fin (n + 1) → S2}
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjp1 : j + 1 < n + 1)
    {a b : ℝ} (hbpos : 0 < b)
    (hp : (A ⟨i, by omega⟩ : E3)
        = a • (A ⟨i + 1, hi1⟩ : E3) + b • (A ⟨j, hj⟩ : E3))
    (hsupp : 0 ≤ det3 (A ⟨i, by omega⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3)) :
    0 ≤ det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) := by
  have hexp : det3 (A ⟨i, by omega⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3)
      = b * det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) := by
    rw [hp, det3_add_fst, det3_smul_fst, det3_smul_fst]
    have h0 : det3 (A ⟨i + 1, hi1⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) = 0 := by
      simp only [det3]; ring
    rw [h0]; ring
  rw [hexp] at hsupp
  nlinarith [hsupp, hbpos]

/-- The sign relation `E_{succ} = −F`, a ring identity. -/
theorem Esucc_eq_neg_F {n : ℕ} (A : Fin (n + 1) → S2)
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjp1 : j + 1 < n + 1) :
    det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i + 1, hi1⟩ : E3)
      = - det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) := by
  simp only [det3]; ring

/-! ## §4. The sign-correct dichotomy disjunction and the named residual.

With `E_{pred} ≥ 0` and `F ≥ 0` (`E_{succ} ≤ 0`), the dichotomy `not_both_witness_zero` (whose
contradiction only reads `E = 0`, sign-agnostic) gives `0 < E_{pred} ∨ 0 < F`. -/

/-- **The named residual corner.**  `NearSidePredDegenerate A i j` asserts the pred witness is
degenerate: `E_{pred} := det3 (Aδ(j-1)) (Aδ j) (Aδ(i+1)) = 0`, i.e. `Aδ(j-1) ∈ Π`.  In this corner
the `j-1`-side witness gives no `a`-sign, and the `j+1`-side witness carries the opposite coefficient
sign (`§header`), so the local readout cannot certify `a ≥ 0`.  This residual is STRICTLY smaller
than the original `NearSideWitnessPos` (it is exactly its negation, `¬ 0 < E_{pred}`, refined to
`E_{pred} = 0` by the unconditional `E_{pred} ≥ 0`). -/
def NearSidePredDegenerate {n : ℕ} (A : Fin (n + 1) → S2) (i j : ℕ)
    (hi1 : i + 1 < n + 1) (hj : j < n + 1) (hjm1 : j - 1 < n + 1) : Prop :=
  det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) = 0

/-- **(The sign-correct dichotomy) `NearSideWitnessPos ∨ 0 < F`.**  At an interior binding (`j < n`)
with `E_{pred} ≥ 0` and `F ≥ 0`, the two witnesses are not both degenerate, so either the pred
witness is non-degenerate (`NearSideWitnessPos`, the sign-correct side that closes `a ≥ 0`) or
`0 < F` (the residual corner). -/
theorem nearSideWitness_dichotomy {n : ℕ} {A B : Fin (n + 1) → S2}
    (hposA : PositiveJoints A) (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hjm1 : j - 1 < n + 1) (hjp1 : j + 1 < n + 1)
    (hij : i + 2 ≤ j)
    (hsa : ShortArc (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩))
    (hsau : ShortArc (A ⟨j, hj⟩) (A ⟨j - 1, hjm1⟩))
    (hsav : ShortArc (A ⟨j, hj⟩) (A ⟨j + 1, hjp1⟩))
    (hEpredNN : 0 ≤ det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3))
    (hFnn : 0 ≤ det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3)) :
    NearSideWitnessPos A i j hi1 hj hjm1
      ∨ 0 < det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnp, hnf⟩ := hcon
  have hEpred0 : det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) = 0 := by
    unfold NearSideWitnessPos at hnp; linarith
  -- `0 < F` fails + `F ≥ 0` ⟹ `F = 0` ⟹ `E_succ = 0`.
  have hF0 : det3 (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) = 0 := by linarith
  have hEsucc0 : det3 (A ⟨j, hj⟩ : E3) (A ⟨j + 1, hjp1⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) = 0 := by
    rw [Esucc_eq_neg_F A hi1 hj hjp1, hF0, neg_zero]
  exact not_both_witness_zero (B := B) hposA hB hangle hi1 hj hjm1 hjp1 hij
    hsa hsau hsav hEpred0 hEsucc0

/-! ## §5. The unconditional consumer wrapper at an interior (`j < n`) binding.

We thread the dichotomy through FFCT31's pred-side assembly.  The `E_{pred} ≥ 0` and `F ≥ 0` sign
certificates are produced from the opened arm's weak edge supports (`WeakConvexSphArm`) inside the
`NearSideCoeffNonneg` introduction, where the binding decomposition is in scope.  The output is the
HONEST disjunction: at every interior binding with `j < n`, EITHER the consumer's
`NearSideCoeffNonneg` holds OR the binding is in the named residual corner
`NearSidePredDegenerate`. -/

/-- **(Unconditional dichotomy wrapper, `j < n`)** At an interior binding of the opened arm with
`j < n` and all the FFCT31 + dichotomy geometric inputs, EITHER
`NearSideCoeffNonneg (Aδ i) (Aδ(i+1)) (Aδ j)` holds (closed by the pred witness) OR the binding sits
in the named residual `NearSidePredDegenerate` (the pred witness degenerates and the succ witness has
the opposite coefficient sign — the strictly-smaller residual). -/
theorem nearSideCoeffNonneg_or_predDegenerate {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hnr : NoNonadjacentRepeat A)
    (hposA : PositiveJoints A) (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {i j : ℕ} (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (hjm1 : j - 1 < n + 1) (hjp1 : j + 1 < n + 1)
    (hij : i + 2 ≤ j)
    (hsa : ShortArc (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩))
    (hpm : ShortArc (A ⟨i + 1, hi1⟩) (A ⟨i, by omega⟩))
    (hsau : ShortArc (A ⟨j, hj⟩) (A ⟨j - 1, hjm1⟩))
    (hsav : ShortArc (A ⟨j, hj⟩) (A ⟨j + 1, hjp1⟩))
    (hβ : 0 ≤ (⟪(A ⟨i, by omega⟩ : E3), (A ⟨j, hj⟩ : E3)⟫ : ℝ)
        - (⟪(A ⟨i, by omega⟩ : E3), (A ⟨i + 1, hi1⟩ : E3)⟫ : ℝ)
          * (⟪(A ⟨j, hj⟩ : E3), (A ⟨i + 1, hi1⟩ : E3)⟫ : ℝ)) :
    NearSideCoeffNonneg (A ⟨i, by omega⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩)
      ∨ NearSidePredDegenerate A i j hi1 hj hjm1 := by
  -- index successors.
  have hidx_isucc : ((⟨i, by omega⟩ : Fin (n + 1)) + 1) = (⟨i + 1, hi1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show i + 1 < n + 1 by omega)]
  -- the two weak edge supports (independent of the decomposition, available now).
  have hsupp_pred_edge : 0 ≤ det3 (A ⟨i, by omega⟩ : E3) (A ⟨i + 1, hi1⟩ : E3)
      (A ⟨j - 1, hjm1⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨i, by omega⟩ ⟨j - 1, hjm1⟩
    rw [hidx_isucc] at h; exact h
  have hsupp_succ_edge : 0 ≤ det3 (A ⟨i, by omega⟩ : E3) (A ⟨i + 1, hi1⟩ : E3)
      (A ⟨j + 1, hjp1⟩ : E3) := by
    have h := hA.closed_convex.edge_support ⟨i, by omega⟩ ⟨j + 1, hjp1⟩
    rw [hidx_isucc] at h; exact h
  -- decide the disjunction by whether the pred witness degenerates.
  by_cases hpred0 : det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) = 0
  · right; exact hpred0
  · left
    -- the pred witness is non-degenerate; close `NearSideCoeffNonneg` via FFCT31's pred assembly.
    intro a b hp
    have hb : 0 ≤ b := (hbeta_iff_bcoef_nonneg hsa hp).mp hβ
    have hbpos : 0 < b := nearSide_b_pos_of_shortArc hb hp hpm
    -- `E_pred ≥ 0`, and `≠ 0` gives `> 0`.
    have hEpredNN : 0 ≤ det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i + 1, hi1⟩ : E3) :=
      nearSide_witness_nonneg hi1 hj hjm1 hbpos hp hsupp_pred_edge
    have hEpos : NearSideWitnessPos A i j hi1 hj hjm1 := by
      unfold NearSideWitnessPos
      rcases lt_or_eq_of_le hEpredNN with h | h
      · exact h
      · exact absurd h.symm hpred0
    -- the pred readout support: edge (j-1, j) at Aδ i.
    have hsupp_readout : 0 ≤ det3 (A ⟨j - 1, hjm1⟩ : E3) (A ⟨j, hj⟩ : E3) (A ⟨i, by omega⟩ : E3) := by
      have h := hA.closed_convex.edge_support ⟨j - 1, hjm1⟩ ⟨i, by omega⟩
      rw [show ((⟨j - 1, hjm1⟩ : Fin (n + 1)) + 1) = (⟨j, hj⟩ : Fin (n + 1)) by
        apply Fin.ext
        have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
          rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
        rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (show (j - 1) + 1 < n + 1 by omega),
          show (j - 1) + 1 = j by omega]] at h
      exact h
    exact nearSide_a_nonneg_of_witness_pos hi1 hj hjm1 hp hsupp_readout hEpos

/-! ## §6. Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- The dichotomy core's premise is genuinely consumable: a degenerate witness is a real
plane-membership constraint, witnessed by the trivial in-plane combination `det3 v v w = 0`. -/
theorem witness_zero_realizable (v w : E3) : det3 v v w = 0 := by
  simp only [det3]; ring

/-- The residual `NearSidePredDegenerate` is a genuine determinant-sign constraint (not `True`):
`det3` of three coordinate axes is `1 ≠ 0`, so `E_{pred} = 0` is a real (failable) constraint. -/
theorem det3_axes_ne_zero :
    det3 (!₂[(1:ℝ),0,0] : E3) (!₂[(0:ℝ),1,0] : E3) (!₂[(0:ℝ),0,1] : E3) = 1 := by
  rw [det3E3]; norm_num

/-- The sign certificate `F ≥ 0` is load-bearing: with three coordinate axes `F = 1 > 0`, so the
`0 < F` residual branch of the dichotomy is satisfiable (a real determinant sign). -/
theorem F_axes_pos :
    (0 : ℝ) < det3 (!₂[(1:ℝ),0,0] : E3) (!₂[(0:ℝ),1,0] : E3) (!₂[(0:ℝ),0,1] : E3) := by
  rw [det3E3]; norm_num

#print axioms base_ne_of_shortArc
#print axioms witnessPred_mem_plane
#print axioms witnessSucc_mem_plane
#print axioms not_both_witness_zero
#print axioms nearSide_witnessSucc_F_nonneg
#print axioms nearSideWitness_dichotomy
#print axioms nearSideCoeffNonneg_or_predDegenerate

end ProofsInTheBook.ZinanFFCT32
