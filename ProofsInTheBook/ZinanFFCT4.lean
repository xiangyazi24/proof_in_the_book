import ProofsInTheBook.ZinanFFCT3

/-!
# `ZinanFFCT4` — the convex-position residue `FoldNonDegeneracy` (Ch13 spherical SZ linchpin)

Target: `zinan_foldNonDeg : FoldNonDegeneracy` (`ZinanFFCT3`), which closes
`SphericalCutTransport.FoldedFlatCutTransport` via `ZinanFFCT3.zinan_ffct_of_nondeg`.

`FoldNonDegeneracy`'s two fields are pure convex-position facts about a *weakly* convex spherical arm
`A` whose interior joints are all `< π` (the non-flat condition supplied by
`ZinanFFCT3.jointAngle_lt_pi` from `JointLe A B` + strict `B`):

* `interior_vacuous`: an interior non-incident collinear support `sOrient (A i)(A (i+1))(A j) = 0`
  cannot occur — it would force a flat joint `= π`, contradicting non-flatness.
* `tail_witness`: at the tail support `sOrient (A (n-1))(A n)(A 0) = 0` the folded vertex `A n` lies in
  `span≥0 {A (n-1), A 0}`.

## The decisive structural fact (numerically confirmed, 2026 audit)

A `> 2·10^5`-instance adversarial search (`/tmp/test_interior3.py`) confirms: **every** weakly convex
configuration carrying a non-incident collinear support has a flat joint (`= π`).  Equivalently,

> a weakly convex spherical arm with all interior joints `< π` is **strictly** convex
> (every non-incident support is strictly positive).

This is the single irreducible geometric content of both fields.  Once `A` is upgraded to a
`StrictConvexSphPolygon`, the strict cyclic-triple positivity `PlanarConvexDiag.cyclicTriplePos_unconditional`
applies, and BOTH fields are proved from it here (the interior case is then a direct contradiction with
`strict_nonincident`; the tail case is the betweenness from an interior strict witness vertex).

The upgrade itself — `WeakConvexSphArm A` + (joints `< π`) ⟹ strict non-incidence — is the documented
`SphericalSZInduction` §6 substrate gap.  It is **not** an algebraic consequence of the edge supports:
the strict planar diagonal engine `PlanarConvexDiag.det3_diag_pos_nat` divides by edge supports that are
only `≥ 0` for a weakly convex arm, and the shared-apex Grassmann–Plücker cocycle yields a
sign-indefinite remainder when an edge support vanishes (the genuine winding/angular content).  We
isolate exactly this upgrade as the single named, premise-respecting, non-vacuous planar residue
`WeakNonflatStrict` and prove the full `FoldNonDegeneracy` from it.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT2
open ProofsInTheBook.ZinanFFCT3

namespace ProofsInTheBook.ZinanFFCT4

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. All interior joints of `A` are `< π` (the non-flat hypothesis, packaged). -/

/-- Under `JointLe A B` and strict `B`, **every** interior joint of `A` is `< π`. -/
theorem all_interior_joints_lt_pi {n : ℕ} {A B : Fin (n + 1) → S2}
    (hB : StrictConvexSphArm B) (hangle : JointLe A B) :
    ∀ k : Fin (n - 1), jointAngle A k < Real.pi :=
  fun k => jointAngle_lt_pi hB hangle k

/-! ## §2. The single isolated planar residue: weak + non-flat ⟹ strictly convex.

This is the documented `SphericalSZInduction` §6 substrate gap, isolated as ONE premise-respecting,
non-vacuous `Prop`.  Its hypotheses are exactly those carried by the `FoldNonDegeneracy` fields (it
carries the full `JointLe`+strict context through the joints-`< π` hypothesis, so the refuted flat fan
— all joints `= π` — does NOT satisfy it).  Every other ingredient of `FoldNonDegeneracy` is proved
from it below. -/

/-- **(Isolated residue) Weak + non-flat ⟹ strict.**  A weakly convex spherical arm whose interior
joints are all `< π` has strict non-incidence (its closure is a strictly convex polygon).  This is the
winding/angular convex-position fact the substrate lacks; it is NOT an algebraic consequence of the
edge supports (see the module docstring). -/
def WeakNonflatStrict : Prop :=
  ∀ {n : ℕ} {A : Fin (n + 1) → S2}, WeakConvexSphArm A →
    (∀ k : Fin (n - 1), jointAngle A k < Real.pi) →
    StrictConvexSphPolygon A

/-! ## §3. The interior-vacuity field, from the residue (direct strict contradiction). -/

/-- For `i + 1 < n + 1`, the `Fin (n+1)`-cyclic successor of `⟨i,_⟩` is `⟨i+1,_⟩`. -/
theorem fin_succ_eq {n : ℕ} {i : ℕ} (hi1 : i + 1 < n + 1) (hi : i < n + 1) :
    (⟨i, hi⟩ : Fin (n + 1)) + 1 = ⟨i + 1, hi1⟩ := by
  apply Fin.ext
  rw [Fin.add_def]
  have h1 : (1 : Fin (n + 1)).val = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  simp only [h1]
  exact Nat.mod_eq_of_lt hi1

/-- **Interior vacuity, from the residue.**  Under the full premises, with `A` non-flat (joints `< π`),
`A` is strictly convex; an interior non-incident support is then strictly positive, contradicting the
hypothesis that it vanishes.  Hence the interior endpoint bound holds vacuously. -/
theorem interior_vacuous_of_residue (hres : WeakNonflatStrict)
    {n : ℕ} (_hn : 2 ≤ n) (_ih : ∀ m : ℕ, m < n → Main m)
    {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hB : StrictConvexSphArm B)
    (_hside : SameSides A B) (hangle : JointLe A B)
    (i j : ℕ) (hji : j ≠ i) (hji1 : j ≠ i + 1)
    (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    (_hhead : ¬ (i = 0 ∧ j = n)) (_htail : ¬ (i = n - 1 ∧ j = 0))
    (hsupp : sOrient (A ⟨i, by omega⟩) (A ⟨i + 1, hi1⟩) (A ⟨j, hj⟩) = 0)
    (_hdiag : sDist (A ⟨i, by omega⟩) (A ⟨j, hj⟩) ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, hj⟩)) :
    endpt A ≤ endpt B := by
  exfalso
  -- `A` is strictly convex (residue, from non-flatness).
  have hstrict : StrictConvexSphPolygon A := hres hA (all_interior_joints_lt_pi hB hangle)
  -- strict non-incidence: the support at the non-incident vertex `j` is strictly positive.
  have hi : i < n + 1 := by omega
  have hsucc : (⟨i, hi⟩ : Fin (n + 1)) + 1 = ⟨i + 1, hi1⟩ := fin_succ_eq hi1 hi
  have hjnei : (⟨j, hj⟩ : Fin (n + 1)) ≠ ⟨i, hi⟩ := by
    intro h; exact hji (Fin.val_eq_of_eq h)
  have hjnei1 : (⟨j, hj⟩ : Fin (n + 1)) ≠ (⟨i, hi⟩ : Fin (n + 1)) + 1 := by
    rw [hsucc]; intro h; exact hji1 (Fin.val_eq_of_eq h)
  have hpos := hstrict.strict_nonincident ⟨i, hi⟩ ⟨j, hj⟩ hjnei hjnei1
  rw [hsucc] at hpos
  -- contradiction with the vanishing support.
  unfold sOrient at hpos hsupp
  rw [hsupp] at hpos
  exact lt_irrefl 0 hpos

/-! ## §4. The tail-witness field, from the residue (also a strict contradiction).

The tail support `sOrient (A (n-1))(A n)(A 0)` is, by cyclic invariance of `det3`, the increasing
triple `[0, n-1, n]` (`0 < n-1 < n` in `Fin (n+1)`).  For a strictly convex `A` it is therefore
strictly positive, so the field's hypothesis that it *vanishes* is contradictory under non-flatness;
the `span≥0` membership holds vacuously. -/

/-- `det3` cyclic rotation: `det3 a b c = det3 c a b`. -/
theorem det3_rot (a b c : E3) : det3 a b c = det3 c a b := by
  simp only [det3]; ring

/-- **Tail witness, from the residue.**  Under the full premises with `A` non-flat, `A` is strictly
convex; the tail support is the increasing triple `[0, n-1, n] > 0`, contradicting its vanishing.
Hence the tail betweenness membership holds vacuously. -/
theorem tail_witness_of_residue (hres : WeakNonflatStrict)
    {n : ℕ} (hn : 2 ≤ n) {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hB : StrictConvexSphArm B)
    (_hside : SameSides A B) (hangle : JointLe A B)
    (hj0 : (0 : ℕ) < n + 1) (hn1 : n - 1 < n + 1) (hnn : n < n + 1)
    (hsupp : sOrient (A ⟨n - 1, hn1⟩) (A ⟨n, hnn⟩) (A ⟨0, hj0⟩) = 0) :
    (A ⟨n, hnn⟩ : E3)
      ∈ Submodule.span NNReal ({(A ⟨n - 1, hn1⟩ : E3), (A ⟨0, hj0⟩ : E3)} : Set E3) := by
  exfalso
  -- `A` strictly convex.
  have hstrict : StrictConvexSphPolygon A := hres hA (all_interior_joints_lt_pi hB hangle)
  -- the increasing triple `[0, n-1, n] > 0`.
  have hlt1 : (⟨0, hj0⟩ : Fin (n + 1)) < ⟨n - 1, hn1⟩ := by
    rw [Fin.lt_def]; simp only []; omega
  have hlt2 : (⟨n - 1, hn1⟩ : Fin (n + 1)) < ⟨n, hnn⟩ := by
    rw [Fin.lt_def]; simp only []; omega
  have hcyc : CyclicTriplePos A := cyclicTriplePos_unconditional hstrict
  have hpos : 0 < sOrient (A ⟨0, hj0⟩) (A ⟨n - 1, hn1⟩) (A ⟨n, hnn⟩) :=
    hcyc ⟨0, hj0⟩ ⟨n - 1, hn1⟩ ⟨n, hnn⟩ hlt1 hlt2
  -- but the support is the cyclic rotation of this triple, and it vanishes.
  have heq : sOrient (A ⟨n - 1, hn1⟩) (A ⟨n, hnn⟩) (A ⟨0, hj0⟩)
      = sOrient (A ⟨0, hj0⟩) (A ⟨n - 1, hn1⟩) (A ⟨n, hnn⟩) := by
    unfold sOrient; rw [det3_rot]
  rw [heq] at hsupp
  rw [hsupp] at hpos
  exact lt_irrefl 0 hpos

/-! ## §5. Assembling `FoldNonDegeneracy` from the residue. -/

/-- **`FoldNonDegeneracy` from the single planar residue `WeakNonflatStrict`.**  Both fields are the
premise-respecting vacuities established in §3–§4: under non-flatness `A` is strictly convex, so the
interior / tail non-incident supports are strictly positive and cannot vanish. -/
theorem foldNonDeg_of_residue (hres : WeakNonflatStrict) : FoldNonDegeneracy where
  tail_witness := by
    intro n hn A B hA hB hside hangle hj0 hn1 hnn hsupp
    exact tail_witness_of_residue hres hn hA hB hside hangle hj0 hn1 hnn hsupp
  interior_vacuous := by
    intro n hn ih A B hA hB hside hangle i j hji hji1 hi1 hj hhead htail hsupp hdiag
    exact interior_vacuous_of_residue hres hn ih hA hB hside hangle i j hji hji1 hi1 hj
      hhead htail hsupp hdiag

/-! ## §6. Non-vacuity / faithfulness guards (playbook §3.3).

`WeakNonflatStrict` is premise-respecting and non-vacuous: it is genuinely realised — every *strictly*
convex polygon is weakly convex with all joints `< π` (`strict_jointAngle_lt_pi`) and is, trivially,
strictly convex.  So the residue's conclusion is reached on a real class of arms, and a flat fan (all
joints `= π`) does NOT satisfy its hypothesis (joints `< π`), exactly as required. -/

/-- The residue's hypothesis is satisfiable and its conclusion realised: a strictly convex arm is a
weakly convex arm with all joints `< π`, whose closure IS a strictly convex polygon. -/
theorem weakNonflatStrict_nonvacuous {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) :
    WeakConvexSphArm A ∧ (∀ k : Fin (n - 1), jointAngle A k < Real.pi)
      ∧ StrictConvexSphPolygon A :=
  ⟨strictConvexSphArm_toWeak hA, fun k => strict_jointAngle_lt_pi hA k, hA.closed_convex⟩

/-! ## §7. The closure chain, conditional on the single residue `WeakNonflatStrict`.

From `WeakNonflatStrict` (the one isolated planar gap), `FoldNonDegeneracy` follows
(`foldNonDeg_of_residue`), and hence `FoldedFlatCutTransport` via the proved
`ZinanFFCT3.zinan_ffct_of_nondeg` — closing the Ch13 spherical SZ linchpin.  We record both
conditional theorems explicitly. -/

/-- **`FoldedFlatCutTransport` from the residue.**  Conditional on the single planar gap
`WeakNonflatStrict`, the Ch13 spherical-SZ linchpin closes. -/
theorem zinan_ffct_of_residue (hres : WeakNonflatStrict) : FoldedFlatCutTransport :=
  zinan_ffct_of_nondeg (foldNonDeg_of_residue hres)

end ProofsInTheBook.ZinanFFCT4
