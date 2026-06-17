import ProofsInTheBook.ZinanCh35OuterDual
import ProofsInTheBook.RelationComponentCount
import ProofsInTheBook.PlanarMapEulerInequality

/-!
# Chapter 35: the dual component count `numComp (OuterDualStep) = 2`

This file closes the **easy half** of the outer-cycle dual route to the Chapter-35
keystone unconditionally, and isolates the **hard half** as a single, clean, satisfiable
residual.

## The two halves

The keystone `InnerFacesDualConnected hNT` (defined in `ZinanCh35OuterDual.lean`) says:
any two non-outer faces are `OuterDualStep`-reachable.  The dual route reduces it to the
single component-count fact

```
outerDual_numComp_two : numComp (OuterDualStep hNT) = 2.
```

This file proves, **fully and clean-3, with no hypotheses on `numComp`**, the implication

```
numComp (OuterDualStep hNT) = 2  ⟹  InnerFacesDualConnected hNT
```

(`innerFacesDualConnected_of_outerDual_numComp_two`).  This is the "easy
`numComp=2 → connectivity`" step the route calls for.  The argument is purely the
combinatorics of the equivalence-class quotient:

* `OuterDualStep` is symmetric, so its equivalence closure `EqvGen` coincides with its
  reflexive-transitive closure `ReflTransGen` (`PlanarMapEulerInequality.eqvGen_iff_reflTransGen`).
  Hence `numComp (OuterDualStep) = Nat.card (Quotient (compSetoid (OuterDualStep)))`
  counts `ReflTransGen`-components.
* `outerFace` is `OuterDualStep`-isolated (`ZinanCh35OuterDual.outerFace_isolated` and its
  symmetric form): the *only* face in `outerFace`'s class is `outerFace` itself, because
  any face that reaches `outerFace` IS `outerFace`.
* If `numComp = 2`, the quotient has exactly two classes.  `outerFace` occupies one of
  them, alone.  Every non-outer face lies in a class `≠ ⟦outerFace⟧` (else it would reach
  the outer face and equal it); with only two classes total, all non-outer faces share the
  **single** remaining class, hence are mutually `EqvGen`- (= `ReflTransGen`-) related.

This needs **no** non-emptiness or extra structural hypothesis: it is the bare statement
"a 2-class symmetric relation with one isolated point has all other points in one class".

## The isolated hard residual

`outerDual_numComp_two` itself — the count `= 2` — is the genuine Jordan/Euler content
(the weak dual of a triangulated disk has exactly the inner component and the outer face).
It is carried here as the **single named hypothesis** of the conditional keystone
`innerFacesDualConnected_via_numComp` and is *not* posited as proved.  The intended supplier
is the cut-cap Euler machinery (`PlanarMapCutCap2*`, `numCyclesCutPhi2_holds`,
`jordan_simple_cycle2_unconditional`) through the vocabulary bridge
`OuterDualStep = DualAvoidsCycleStep Couter`; that bridge + the per-component Euler identity
is the remaining subproject and is **not** done here.

## Honesty (§3.3)

`outerDual_numComp_two` is the TRUE statement (`numComp = 2` for the inner-dual-plus-outer
graph of a triangulated disk), it is clean (defined purely from `OuterDualStep`, no
reference to the conclusion), and it is the exact content the cut-cap machinery is built to
supply.  The implication proved here is unconditional, clean-3, no
`sorry`/`axiom`/`admit`/`native_decide`; the count is carried as a named hypothesis only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35OuterCount

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35InnerConn
open ProofsInTheBook.ZinanCh35Coverage
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35OuterDual

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M}

/-! ## The symmetric-closure bridge for `OuterDualStep`

`OuterDualStep` is symmetric (`ZinanCh35OuterDual.outerDualStep_symm`), so its equivalence
closure `EqvGen` agrees with its reflexive-transitive closure `ReflTransGen`. -/

/-- `OuterDualStep` packaged as a plain symmetry statement (`∀ a b, r a b → r b a`),
the form `eqvGen_iff_reflTransGen` wants. -/
lemma outerDualStep_symm' :
    ∀ a b : M.Face, OuterDualStep hNT a b → OuterDualStep hNT b a :=
  fun _ _ h => outerDualStep_symm h

/-- `EqvGen (OuterDualStep)` coincides with `ReflTransGen (OuterDualStep)`. -/
lemma eqvGen_outerDualStep_iff {f g : M.Face} :
    Relation.EqvGen (OuterDualStep hNT) f g ↔
      Relation.ReflTransGen (OuterDualStep hNT) f g :=
  eqvGen_iff_reflTransGen (outerDualStep_symm' (hNT := hNT)) f g

/-! ## The outer face's class is a singleton

In the component quotient `Quotient (compSetoid (OuterDualStep))`, the class of any
non-outer face is distinct from the class of `outerFace`: a face whose class equals
`⟦outerFace⟧` is `EqvGen`- (= `ReflTransGen`-) related to `outerFace`, hence equals it by
`eq_outerFace_of_reachesOuter`. -/

/-- If a face's quotient class equals `outerFace`'s class, the face IS `outerFace`. -/
lemma eq_outerFace_of_class_eq {f : M.Face}
    (h : Quotient.mk (compSetoid (OuterDualStep hNT)) f
        = Quotient.mk (compSetoid (OuterDualStep hNT)) hNT.outerFace) :
    f = hNT.outerFace := by
  have hEqv : Relation.EqvGen (OuterDualStep hNT) f hNT.outerFace := Quotient.exact h
  have hReach : Relation.ReflTransGen (OuterDualStep hNT) f hNT.outerFace :=
    (eqvGen_outerDualStep_iff (hNT := hNT)).1 hEqv
  exact eq_outerFace_of_reachesOuter hReach

/-- Contrapositive form: a non-outer face's class differs from `outerFace`'s class. -/
lemma class_ne_outerFace_class {f : M.Face} (hf : f ≠ hNT.outerFace) :
    Quotient.mk (compSetoid (OuterDualStep hNT)) f
      ≠ Quotient.mk (compSetoid (OuterDualStep hNT)) hNT.outerFace :=
  fun h => hf (eq_outerFace_of_class_eq (hNT := hNT) h)

/-! ## The 2-class consequence: all non-outer faces share one class

With exactly two classes, and `⟦outerFace⟧` occupying one of them, every class distinct
from `⟦outerFace⟧` is the unique other class.  Hence any two non-outer faces have equal
classes, i.e. are `EqvGen`-related, i.e. `ReflTransGen`-related. -/

/-- **Two elements of a 2-element Fintype, both different from a fixed `c`, are equal.** -/
lemma eq_of_card_two_of_ne {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 2) {x y c : α} (hx : x ≠ c) (hy : y ≠ c) : x = y := by
  by_contra hxy
  -- `x, y, c` would be three distinct elements, forcing `card ≥ 3`.
  have h3 : ({x, y, c} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp [hy]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy, hx⟩
  have hle : ({x, y, c} : Finset α).card ≤ Fintype.card α := Finset.card_le_univ _
  omega

/-- **The two quotient classes of non-outer faces coincide.**  Under `numComp = 2`, any
two non-outer faces lie in the same component class. -/
lemma class_eq_of_numComp_two
    (hnum : numComp (OuterDualStep hNT) = 2)
    {f g : M.Face} (hf : f ≠ hNT.outerFace) (hg : g ≠ hNT.outerFace) :
    Quotient.mk (compSetoid (OuterDualStep hNT)) f
      = Quotient.mk (compSetoid (OuterDualStep hNT)) g := by
  classical
  haveI : Fintype (Quotient (compSetoid (OuterDualStep hNT))) :=
    Quotient.fintype (compSetoid (OuterDualStep hNT))
  have hcard : Fintype.card (Quotient (compSetoid (OuterDualStep hNT))) = 2 := by
    have := hnum
    unfold numComp at this
    rwa [Nat.card_eq_fintype_card] at this
  exact eq_of_card_two_of_ne hcard
    (class_ne_outerFace_class (hNT := hNT) hf)
    (class_ne_outerFace_class (hNT := hNT) hg)

/-! ## The easy half: `numComp = 2 ⟹ InnerFacesDualConnected` -/

/-- **Easy half (unconditional, clean-3).**  If the outer-dual component count is `2`,
then the inner faces are dual-connected. -/
theorem innerFacesDualConnected_of_outerDual_numComp_two
    (hnum : numComp (OuterDualStep hNT) = 2) :
    InnerFacesDualConnected hNT := by
  intro f g hf hg
  -- equal quotient classes ⟹ `EqvGen` ⟹ `ReflTransGen`
  have hclass := class_eq_of_numComp_two (hNT := hNT) hnum hf hg
  have hEqv : Relation.EqvGen (OuterDualStep hNT) f g := Quotient.exact hclass
  exact (eqvGen_outerDualStep_iff (hNT := hNT)).1 hEqv

/-! ## The isolated hard residual and the conditional keystone

`outerDual_numComp_two` (the count `= 2`) is the genuine Jordan/Euler content and the
single remaining input.  It is carried as a named hypothesis below, never posited as
proved. -/

/-- **The single isolated residual** : the outer-dual component count is `2`.  This is the
Euler/Jordan fact (the weak dual of a triangulated disk = the inner component ⊔ outer
face).  The cut-cap Euler machinery is the intended supplier; it is **not** discharged in
this file. -/
def OuterDualNumCompTwo (hNT : NearTriangulation M) : Prop :=
  numComp (OuterDualStep hNT) = 2

variable {u v : M.Vertex}

/-- **The keystone via the dual component count**, conditional on the single residual
`OuterDualNumCompTwo`.  Combines the easy half proved here with the lift assembled in
`ZinanCh35OuterDual.lean`. -/
theorem innerFacesDualConnected_via_numComp
    (hnum : OuterDualNumCompTwo hNT) :
    InnerFacesDualConnected hNT :=
  innerFacesDualConnected_of_outerDual_numComp_two hnum

/-- **Keystone `InnerFaceConnectedFromFace₁`** via the dual count, conditional on
`OuterDualNumCompTwo`. -/
theorem innerFaceConnectedFromFace₁_via_numComp
    (data : hNT.ChordSplitData u v) (hnum : OuterDualNumCompTwo hNT) :
    InnerFaceConnectedFromFace₁ data :=
  innerFaceConnectedFromFace₁_via_outerDual data
    (innerFacesDualConnected_via_numComp hnum)

/-- **End-to-end cascade** : `BoundedFacePartition` via the dual count, conditional on
`OuterDualNumCompTwo`. -/
theorem boundedFacePartition_via_numComp
    (data : hNT.ChordSplitData u v) (hnum : OuterDualNumCompTwo hNT) :
    BoundedFacePartition data :=
  boundedFacePartition_via_outerDual data
    (innerFacesDualConnected_via_numComp hnum)

end ProofsInTheBook.ZinanCh35OuterCount

/-! ## Axiom audit (expect: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35OuterCount.eqvGen_outerDualStep_iff
#print axioms ProofsInTheBook.ZinanCh35OuterCount.eq_outerFace_of_class_eq
#print axioms ProofsInTheBook.ZinanCh35OuterCount.class_ne_outerFace_class
#print axioms ProofsInTheBook.ZinanCh35OuterCount.eq_of_card_two_of_ne
#print axioms ProofsInTheBook.ZinanCh35OuterCount.class_eq_of_numComp_two
#print axioms ProofsInTheBook.ZinanCh35OuterCount.innerFacesDualConnected_of_outerDual_numComp_two
#print axioms ProofsInTheBook.ZinanCh35OuterCount.innerFacesDualConnected_via_numComp
#print axioms ProofsInTheBook.ZinanCh35OuterCount.innerFaceConnectedFromFace₁_via_numComp
#print axioms ProofsInTheBook.ZinanCh35OuterCount.boundedFacePartition_via_numComp
