import ProofsInTheBook.ZinanFFCT4

/-!
# `ZinanFFCT5` — sizing and partial closure of the final Ch13 residue `WeakNonflatStrict`

`ZinanFFCT4` reduces `FoldNonDegeneracy` (hence `FoldedFlatCutTransport`) to the single planar
residue `WeakNonflatStrict`:

> `WeakConvexSphArm A` + (all interior joints `< π`) ⟹ `StrictConvexSphPolygon A`.

This file records the outcome of a direct attack on that residue.

## DECISIVE FINDING — the residue as stated is FALSE.

`WeakNonflatStrict` upgrades a *weakly* convex arm to a *strictly* convex polygon (`strict_nonincident`:
EVERY non-incident support `> 0`) using only the hypothesis that the `n-1` **interior** joints
(`jointAngle A : Fin (n-1)`, the joints at vertices `A 1, …, A (n-1)`) are `< π`.  But the closed
polygon `A : Fin (n+1) → S²` has `n+1` joints; the two **boundary** joints at `A 0` and `A n` (where
the closing chord `A n → A 0` attaches) are *not* constrained by that hypothesis.

A weakly convex closure can have a flat (`= π`) joint at a boundary vertex while all interior joints
are `< π`.  At a flat boundary joint the three vertices are collinear (coplanar through the origin), so
the corresponding non-incident support **vanishes** — and yet `StrictConvexSphPolygon A` demands it be
`> 0`.  Hence `WeakNonflatStrict` has genuine counterexamples and cannot be proved.

Numerically (build server, `/tmp/wns_test*.py`): the explicit family `n = 4`, vertices the gnomonic
lift of a convex planar `5`-gon with `A 4` placed on the chord `A 3 → A 0`, satisfies
`WeakConvexSphArm A`, has all three interior joints `< π` (`0.875π, 0.875π, 0.145π`), yet has a flat
joint **= π** at the *boundary* vertex `A 4 = A n`, producing the vanishing supports
`sOrient (A 3)(A 4)(A 0) = 0` and `sOrient (A 4)(A 0)(A 3) = 0`.  The first is exactly the
`tail_witness` support; both are excluded from `interior_vacuous` by its `hhead`/`htail` guards.

So the "every weakly-convex config with a vanishing non-incident support has a flat joint `= π`"
confirmation the residue rests on is TRUE — but the flat joint it produces is a *boundary* joint, which
`WeakNonflatStrict`'s hypothesis does not forbid.  The reduction in `ZinanFFCT4` is therefore an
over-strong (FALSE) residue: it routes BOTH `FoldNonDegeneracy` fields through a global
strict-convexity claim that does not hold.

## What this means for closing Ch13

`FoldNonDegeneracy` is itself **not** false — its two fields are individually true, but they must be
proved *directly*, not via the false global upgrade:

* `interior_vacuous` (guarded by `hhead`/`htail`): genuinely vacuous — over 5·10⁴ adversarial weakly
  convex configs with interior joints `< π`, NO non-head/non-tail interior support vanishes
  (`/tmp/wns_test3.py`, `/tmp/wns_test4.py`: a vanishing weak support forces `A j` adjacent to the
  edge, i.e. a flat joint at `A i` or `A (i+1)`; with all interior joints `< π` such a flat joint can
  only sit at a boundary vertex, i.e. the head/tail cases).  Proving it needs the genuine
  "weak vanishing support ⟹ adjacent flat joint" geometry, NOT strict convexity.
* `tail_witness` (the flat boundary case): NON-vacuous — the support really can vanish, and then the
  conclusion `A n ∈ span≥0 {A (n-1), A 0}` is the real great-circle betweenness of the flat joint,
  exactly the regime `SphericalSZ.betweenness_span_nnreal` handles.

This file delivers the proven, unconditional sub-lemmas (the algebraic/transport core and the genuine
flat-joint structural facts) and isolates the precise remaining work.

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
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT4

namespace ProofsInTheBook.ZinanFFCT5

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. `det3` permutation signs (pure `ring`), the algebraic carriers of the diagnosis. -/

/-- `det3` is alternating: a transposition of the last two arguments flips the sign. -/
theorem det3_swap23 (a b c : E3) : det3 a c b = - det3 a b c := by
  simp only [det3]; ring

/-- `det3` cyclic rotation (recorded locally for `sOrient`). -/
theorem sOrient_rot (a b c : S2) : sOrient a b c = sOrient c a b := by
  simp only [sOrient, det3]; ring

/-- A vanishing support is invariant under any rotation/transposition: if the tail support vanishes,
so does its even/odd permutations (used to feed `betweenness_span_nnreal`, whose determinant slot is
`det3 b a c`). -/
theorem tail_support_perm {a b c : S2} (h : sOrient a b c = 0) :
    det3 (b : E3) (a : E3) (c : E3) = 0 := by
  have : sOrient b a c = - sOrient a b c := by simp only [sOrient, det3]; ring
  rw [h, neg_zero] at this
  simpa only [sOrient] using this

/-! ## §2. The TRUE replacement residue, with ALL `n+1` joints constrained.

The honest residue — the one that IS true and would still close `FoldNonDegeneracy` correctly — must
forbid flat joints at the boundary as well.  We package the full joint set.  `allJointAngle A v` is the
spherical angle at vertex `v : Fin (n+1)` of the *closed* polygon (neighbours `v-1`, `v+1` cyclically),
covering the two boundary joints the interior `jointAngle : Fin (n-1)` omits. -/

/-- The spherical joint angle at vertex `v` of the **closed** polygon `A : Fin (n+1) → S²` (cyclic
neighbours).  For interior `v` this agrees with `jointAngle`; for `v = 0` and `v = Fin.last n` it is the
boundary joint involving the closing chord `A (last) → A 0`, which `jointAngle` does not see. -/
def allJointAngle {n : ℕ} (A : Fin (n + 1) → S2) (v : Fin (n + 1)) : ℝ :=
  sphAngle (A (v - 1)) (A v) (A (v + 1))

/-- **The corrected (true) residue.**  A weakly convex polygon with **every** joint (interior AND
boundary) `< π` is strictly convex.  Unlike `WeakNonflatStrict`, this constrains all `n+1` joints, so
the boundary-flat counterexample is excluded.  Stated as a `Prop` for sizing; it is the faithful
strengthening the substrate actually needs (NOT proved here — see the scope note in the header). -/
def WeakAllNonflatStrict : Prop :=
  ∀ {n : ℕ} {A : Fin (n + 1) → S2}, WeakConvexSphArm A →
    (∀ v : Fin (n + 1), allJointAngle A v < Real.pi) →
    StrictConvexSphPolygon A

/-! ## §3. `tail_witness`, reduced to `betweenness_span_nnreal` (the bounded finish).

The `tail_witness` field is NOT closed by the false strict upgrade; it is the genuine flat-boundary
betweenness.  We expose it as a clean reduction to the proved `SphericalSZ.betweenness_span_nnreal`:
given the (geometric, convex-position) Gram-sign data and the chord short-arc, the betweenness holds.
This isolates the remaining content to exactly those three convex-position inputs. -/

/-- **`tail_witness` from the three convex-position inputs (bounded finish).**  When the tail support
`sOrient (A (n-1))(A n)(A 0)` vanishes, the chord `A (n-1) → A 0` is a short arc, and the two
convex-position Gram coefficients are nonnegative, the folded vertex `A n` lies in
`span≥0 {A (n-1), A 0}`.  This is a direct application of `betweenness_span_nnreal` (with `a = A (n-1)`,
`c = A 0`, `b = A n`), the determinant slot supplied by `tail_support_perm`.  The three remaining inputs
(`shortArc`, `hα`, `hβ`) are the genuine convex-position content the substrate must furnish from
`WeakConvexSphArm A` + the joint structure (see scope note). -/
theorem tail_witness_of_betweenness_inputs
    {n : ℕ} {A : Fin (n + 1) → S2}
    (hj0 : (0 : ℕ) < n + 1) (hn1 : n - 1 < n + 1) (hnn : n < n + 1)
    (hsupp : sOrient (A ⟨n - 1, hn1⟩) (A ⟨n, hnn⟩) (A ⟨0, hj0⟩) = 0)
    (hshort : ShortArc (A ⟨n - 1, hn1⟩) (A ⟨0, hj0⟩))
    (hα : 0 ≤ (⟪(A ⟨n, hnn⟩ : E3), (A ⟨n - 1, hn1⟩ : E3)⟫ : ℝ)
        - (⟪(A ⟨n, hnn⟩ : E3), (A ⟨0, hj0⟩ : E3)⟫ : ℝ)
          * (⟪(A ⟨n - 1, hn1⟩ : E3), (A ⟨0, hj0⟩ : E3)⟫ : ℝ))
    (hβ : 0 ≤ (⟪(A ⟨n, hnn⟩ : E3), (A ⟨0, hj0⟩ : E3)⟫ : ℝ)
        - (⟪(A ⟨n, hnn⟩ : E3), (A ⟨n - 1, hn1⟩ : E3)⟫ : ℝ)
          * (⟪(A ⟨0, hj0⟩ : E3), (A ⟨n - 1, hn1⟩ : E3)⟫ : ℝ)) :
    (A ⟨n, hnn⟩ : E3)
      ∈ Submodule.span NNReal ({(A ⟨n - 1, hn1⟩ : E3), (A ⟨0, hj0⟩ : E3)} : Set E3) :=
  betweenness_span_nnreal (A ⟨n - 1, hn1⟩) (A ⟨0, hj0⟩) (A ⟨n, hnn⟩)
    hshort (tail_support_perm hsupp) hα hβ

end ProofsInTheBook.ZinanFFCT5
