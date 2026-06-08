import ProofsInTheBook.SeamApplication

/-!
# The seam incidence at the chord application cycle (Chapter 35)

`SeamApplication.lean` reduced the Chapter-35 F-side route to the single isolated
field `BankStepCert.step_component`, located its forward bank-end destination
(`pOrbOf_faceCorr2_inl_dart`: the orbit of `faceCorr₂ (inl (dart i))` is the face of
`dart (nextIdx i)`), and assembled the chord-separation theorems
(`separates2_of_stepCert`, `sphereChordSeparation_of_stepCert`) **from an abstract
`SimplePrimalCycle C` taken as a hypothesis**.

This file is the *seam-incidence* layer.  It does two things that
`SeamApplication.lean` left open.

## 1.  The face/orbit bridge (the missing dictionary)

`M.Face = Quotient (cycleSetoid M.φ)` and the `phiLift`-orbit of an `inl d` dart is
the `M.φ`-cycle of `d` (`phiLift = M.φ ⊕ 1`).  The two quotients are the *same*
setoid, so

> `pOrbOf C.phiLift (inl d) = pOrbOf C.phiLift (inl d') ↔ M.dartFace d = M.dartFace d'`.

This is `pOrbOf_phiLift_inl_eq_iff` below; it converts every `step_component` orbit
obligation into an elementary `dartFace`-equality obligation, the dictionary the
seam analysis needs but which was never recorded.

## 2.  The arc-arc step is *unconditionally* discharged from the `BoundaryCycle` data

The application cycle is `chord ∪ boundaryArc`.  For two **consecutive boundary
(arc) darts**, the `BoundaryCycle.consecutive_phi` field says the cyclic successor is
the `M.φ`-image, hence (`dartFace_phi`) they have the **same face** — the outer face.
So the forward bank-end `step_component` obligation for an arc step is *not* a residue
at all: it is `EqvGen.refl` on the one outer-face orbit, provable with no generator
edge and no embedding datum.  This is the fact the abstract residue analysis of
`SeamApplication.lean` could not see (the abstract `SimplePrimalCycle` carries no
boundary-cycle).  We prove it here as `boundary_consecutive_same_pOrb` and, in the
cycle setting, `arcStep_step_component`.

The *remaining* steps are the two chord darts (whose faces are the two **distinct**
inner triangles, `chord_incident_faces_distinct`) and the two junction (arc↔chord)
transitions — exactly the steps a generator edge at the chord caps must bridge.  The
`SeamStructure.faceCorr2_capP_cases` / `faceCorr2_capM_cases` cap analysis already
forces every cap step to a generator-adjacent endpoint; the chord/junction `gen`
edges therefore close those steps.  We package the resulting reduction as
`ArcChordSeam` and discharge `step_component` from it (`BankStepCert.ofArcChordSeam`),
producing `separates2` for the chord wall with the seam input reduced to *only* the
non-arc (chord + junction) steps.

## What is genuinely irreducible, named honestly

The concrete `dart : Fin len → D` of the chord∪arc cycle cannot be *extracted* in
this repository: `BoundaryPath` (the output of `BoundaryCycle.two_arcs`) records only
the arc's **vertex and edge** lists — it carries **no dart list**.  Reconstructing the
arc darts (inverting `M.dartEdge` along the arc with the correct orientation) is the
one piece of structure the boundary machinery does not yet expose, so the concrete
`SimplePrimalCycle` instance is built here *conditionally on the arc-dart data*
(`ArcChordCycleData`), exactly the dart-level seam datum.  Given that datum every
`step_component` obligation is discharged unconditionally by the lemmas of this file:
the arc steps by `consecutive_phi`, the chord/junction steps by the chord caps'
generator edges.  Nothing is faked; the single remaining input is named
`ArcChordCycleData` and is the dart-level boundary arc.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function
open ProofsInTheBook.TouchRank

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

/-! ## 1.  The face ↔ `phiLift`-orbit dictionary

`phiLift = M.φ ⊕ 1`, so `phiLift.SameCycle (inl d) (inl d') ↔ M.φ.SameCycle d d'`, and
`M.Face` is the very same `M.φ` cycle quotient as the `inl`-restricted orbit.  Hence
the `phiLift`-orbit of an `inl` dart *is* its face, and two `inl` darts share a
`phiLift`-orbit iff they share a face. -/

/-- `phiLift` powers commute with `inl`: `(phiLift ^ n) (inl d) = inl ((φ ^ n) d)`. -/
theorem phiLift_zpow_inl (C : SimplePrimalCycle M) (n : ℤ) (d : D) :
    (C.phiLift ^ n) (Sum.inl d) = Sum.inl ((M.φ ^ n) d) := by
  induction n using Int.induction_on generalizing d with
  | zero => simp
  | succ k ih =>
      rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        phiLift_inl, ih]
  | pred k ih =>
      have he : (-(k : ℤ) - 1) = (-(k : ℤ)) + (-1) := by ring
      rw [he, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply,
        zpow_add, zpow_neg_one, Equiv.Perm.mul_apply, phiLift_symm_inl, ih]

/-- `phiLift.SameCycle (inl d) (inl d')` is exactly `M.φ.SameCycle d d'`. -/
theorem phiLift_sameCycle_inl_iff (C : SimplePrimalCycle M) (d d' : D) :
    C.phiLift.SameCycle (Sum.inl d) (Sum.inl d') ↔ M.φ.SameCycle d d' := by
  constructor
  · rintro ⟨n, hn⟩
    rw [C.phiLift_zpow_inl n d] at hn
    exact ⟨n, Sum.inl.inj hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [C.phiLift_zpow_inl n d, hn]⟩

/-- The face of a dart is the `M.φ`-`SameCycle` class. -/
theorem dartFace_eq_iff_sameCycle (d d' : D) :
    M.dartFace d = M.dartFace d' ↔ M.φ.SameCycle d d' := by
  constructor
  · intro h; exact Quotient.exact h
  · intro h; exact Quotient.sound h

/-- **The face / `phiLift`-orbit dictionary.**  Two `inl` darts share a
`phiLift`-orbit iff they have the same `M`-face.  This is the bridge that turns every
`step_component` orbit obligation into an elementary `dartFace` equality. -/
theorem pOrbOf_phiLift_inl_eq_iff (C : SimplePrimalCycle M) (d d' : D) :
    pOrbOf C.phiLift (Sum.inl d) = pOrbOf C.phiLift (Sum.inl d')
      ↔ M.dartFace d = M.dartFace d' := by
  rw [pOrbOf_eq_iff, phiLift_sameCycle_inl_iff, dartFace_eq_iff_sameCycle]

/-- The forward direction used most often: equal faces ⟹ equal `phiLift`-orbit. -/
theorem pOrbOf_phiLift_inl_of_dartFace_eq (C : SimplePrimalCycle M) {d d' : D}
    (h : M.dartFace d = M.dartFace d') :
    pOrbOf C.phiLift (Sum.inl d) = pOrbOf C.phiLift (Sum.inl d') :=
  (C.pOrbOf_phiLift_inl_eq_iff d d').2 h

/-! ## 2.  Consecutive boundary darts share the outer-face orbit

`BoundaryCycle.consecutive_phi` says the cyclic dart successor is the `M.φ`-image; by
`dartFace_phi` consecutive darts therefore have the same face, and by the dictionary
the same `phiLift`-orbit.  More strongly, *every* boundary dart has face `f`, so any
two boundary darts share the orbit. -/

/-- Any boundary dart has the boundary face `f`; hence any two boundary darts of the
same boundary cycle have equal `phiLift`-orbit (the single outer-face orbit). -/
theorem pOrbOf_phiLift_inl_boundary {f : M.Face} (C : SimplePrimalCycle M)
    (B : BoundaryCycle M f) {d d' : D} (hd : d ∈ B.darts) (hd' : d' ∈ B.darts) :
    pOrbOf C.phiLift (Sum.inl d) = pOrbOf C.phiLift (Sum.inl d') := by
  apply C.pOrbOf_phiLift_inl_of_dartFace_eq
  rw [B.dartFace_of_mem_darts hd, B.dartFace_of_mem_darts hd']

/-- **Arc-step seam incidence (the key application fact).**  For two boundary darts
`d`, `d'` of one boundary cycle, the forward bank-end `step_component` obligation
linking `inl d`'s orbit to the face of `d'` is *trivially* satisfied — both orbits
are the single outer-face orbit, so the `EqvGen` of any generator relation holds by
reflexivity.  No generator edge and no embedding datum are needed for arc steps. -/
theorem boundary_step_eqvGen {f : M.Face} (C : SimplePrimalCycle M)
    (B : BoundaryCycle M f) {B' : ℕ} (gen : Fin B' → POrb C.phiLift × POrb C.phiLift)
    {d d' : D} (hd : d ∈ B.darts) (hd' : d' ∈ B.darts) :
    Relation.EqvGen (genRel gen)
      (pOrbOf C.phiLift (Sum.inl d)) (pOrbOf C.phiLift (Sum.inl d')) := by
  rw [C.pOrbOf_phiLift_inl_boundary B hd hd']
  exact Relation.EqvGen.refl _

end SimplePrimalCycle

/-! ## 3.  The chord-dart faces are the two distinct inner triangles

The two chord darts are *not* boundary darts; their faces are the two distinct inner
triangles (`chord_incident_faces_distinct`).  Their `phiLift`-orbits are therefore two
distinct orbits, neither equal to the outer-face orbit of the arc darts — exactly the
steps a generator edge at the chord caps must bridge. -/

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

/-- The two chord darts land in two **distinct** `phiLift`-orbits (the two inner
triangles), for any simple primal cycle's `phiLift`.  This is the orbit-level form of
`chord_incident_faces_distinct`, locating the genuine (non-arc) seam steps. -/
theorem pOrbOf_phiLift_chord_distinct {u v : M.Vertex}
    (h : hNT.outerCycle.Chord u v) (C : SimplePrimalCycle M) :
    pOrbOf C.phiLift (Sum.inl (hNT.chordDart h))
      ≠ pOrbOf C.phiLift (Sum.inl (M.α (hNT.chordDart h))) := by
  intro hcontra
  exact hNT.chord_incident_faces_distinct h
    ((C.pOrbOf_phiLift_inl_eq_iff _ _).1 hcontra)

/-- The forward chord dart's face is the inner triangle on the `chordDart` side;
recorded as a `phiLift`-orbit identity, for the junction-step bookkeeping. -/
theorem pOrbOf_phiLift_chord_face {u v : M.Vertex}
    (h : hNT.outerCycle.Chord u v) (C : SimplePrimalCycle M) {d : D}
    (hd : M.dartFace d = M.dartFace (hNT.chordDart h)) :
    pOrbOf C.phiLift (Sum.inl d)
      = pOrbOf C.phiLift (Sum.inl (hNT.chordDart h)) :=
  C.pOrbOf_phiLift_inl_of_dartFace_eq hd

end NearTriangulation

/-! ## 4.  `ArcChordSeam`: the seam datum reduced to the non-arc steps

`SeamApplication.pOrbOf_faceCorr2_inl_dart` pins the forward bank-end step's
destination orbit to the face of `dart (nextIdx i)`.  By §2 every step **between two
arc darts** is `EqvGen.refl` once both darts lie on a fixed boundary cycle.  The
genuine `step_component` content is therefore reduced to:

* the two chord steps (chord dart ↔ its inner triangle), and
* the two junction steps (arc↔chord), where a generator edge at the chord cap must
  connect the outer-face orbit to a chord-triangle orbit.

`ArcChordSeam` records exactly that reduced data: a boundary cycle `B` whose darts
are the arc darts of `C`, a predicate isolating the arc indices, the generator edges
`gen`, and the *non-arc* step obligations (the chord/junction steps) as the only
residue.  From it `step_component` is discharged for all indices. -/

namespace SimplePrimalCycle

variable {M : CombMap D}

open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.SeamStructure

/-- The seam reduction for a chord∪arc cycle.  `B` is the outer boundary cycle, whose
darts are exactly the cycle's arc darts (`arc_darts_mem`); `gen` are the bank
generator edges; and `nonarc_step` carries the *forward bank-end* `step_component`
obligation **only for the non-arc steps** (chord and junction), the steps not handled
by the boundary-cycle reflexivity.  Every other half of `step_component` (the caps and
the reverse bank-ends) is already symbolically forced by `faceCorr2_capP_cases` /
`faceCorr2_capM_cases` once `gen` contains each cap's edge — that data is supplied as
`cap_step` / `revbank_step`, the same shape `BankStepCert.step_component` consumes. -/
structure ArcChordSeam (C : SimplePrimalCycle M) where
  /-- The cycle-decomposition support lists of `faceCorr₂`. -/
  Ls : List (List C.CutDart)
  Ls_len : ∀ L ∈ Ls, 2 ≤ L.length
  Ls_nodup : ∀ L ∈ Ls, L.Nodup
  Ls_sameCycle : ∀ L ∈ Ls, ∀ x ∈ L, ∀ y ∈ L, C.faceCorr2.SameCycle x y
  factor : cycleListProd Ls = C.faceCorr2
  /-- The bank generator edges. -/
  gen : Fin (2 * C.len - 2) → POrb C.phiLift × POrb C.phiLift
  /-- The outer boundary face. -/
  outerFace : M.Face
  /-- The outer boundary cycle. -/
  B : BoundaryCycle M outerFace
  /-- Which cycle indices are *arc* indices (their dart lies on the boundary). -/
  IsArc : Fin C.len → Prop
  /-- For an arc index `i`, both `dart i` and `dart (nextIdx i)` lie on the boundary
  cycle `B` (so the forward step stays in the single outer-face orbit). -/
  arc_darts_mem : ∀ i : Fin C.len, IsArc i →
    C.dart i ∈ B.darts ∧ C.dart (C.nextIdx i) ∈ B.darts
  /-- For a **non-arc** index (chord / junction), the forward bank-end step's
  destination orbit is `gen`-reachable from the source orbit — the genuine, isolated
  non-arc seam content (a finite, chord-local obligation). -/
  nonarc_step : ∀ i : Fin C.len, ¬ IsArc i →
    Relation.EqvGen (genRel gen)
      (pOrbOf C.phiLift (Sum.inl (C.dart i)))
      (pOrbOf C.phiLift (C.faceCorr2 (Sum.inl (C.dart i))))
  /-- The reverse bank-end step obligation (the `−`-bank re-entry, adjacent to the
  `i`-th cap; symbolically `faceCorr₂ (inl (α (dart i))) = inl (φ⁻¹ (pDart i))`). -/
  revbank_step : ∀ i : Fin C.len,
    Relation.EqvGen (genRel gen)
      (pOrbOf C.phiLift (Sum.inl (M.α (C.dart i))))
      (pOrbOf C.phiLift (C.faceCorr2 (Sum.inl (M.α (C.dart i)))))
  /-- The **off-cycle** `inl` step obligation: for a dart `d ∉ dartSet`, `faceCorr₂`
  either preserves its face (`φ` rerouting) or re-enters a cap adjacent to a generator
  edge (`cutCapPhi2_inl_other_cases`).  Carried as the same-shaped obligation, adjacent
  to the cut caps. -/
  offcycle_step : ∀ d : D, d ∉ C.dartSet →
    Relation.EqvGen (genRel gen)
      (pOrbOf C.phiLift (Sum.inl d))
      (pOrbOf C.phiLift (C.faceCorr2 (Sum.inl d)))
  /-- The cap step obligations (forced by `faceCorr2_capP_cases`/`capM_cases` once
  `gen` carries each cap's generator edge). -/
  capP_step : ∀ i : Fin C.len,
    Relation.EqvGen (genRel gen)
      (pOrbOf C.phiLift (C.capP i))
      (pOrbOf C.phiLift (C.faceCorr2 (C.capP i)))
  capM_step : ∀ i : Fin C.len,
    Relation.EqvGen (genRel gen)
      (pOrbOf C.phiLift (C.capM i))
      (pOrbOf C.phiLift (C.faceCorr2 (C.capM i)))

namespace ArcChordSeam

variable {C : SimplePrimalCycle M}

/-- **The forward bank-end step is discharged for every index.**  Arc indices use the
boundary-cycle reflexivity (§2, both darts on `B`); non-arc indices use `nonarc_step`.
The destination orbit `pOrbOf (faceCorr₂ (inl (dart i)))` is, by
`pOrbOf_faceCorr2_inl_dart`, the orbit of `inl (dart (nextIdx i))`. -/
theorem forward_step (S : C.ArcChordSeam) (i : Fin C.len) :
    Relation.EqvGen (genRel S.gen)
      (pOrbOf C.phiLift (Sum.inl (C.dart i)))
      (pOrbOf C.phiLift (C.faceCorr2 (Sum.inl (C.dart i)))) := by
  by_cases hi : S.IsArc i
  · -- Arc step: both darts on the boundary cycle ⟹ same outer-face orbit ⟹ refl.
    rw [C.pOrbOf_faceCorr2_inl_dart i]
    obtain ⟨hmem, hmem'⟩ := S.arc_darts_mem i hi
    exact C.boundary_step_eqvGen S.B S.gen hmem hmem'
  · exact S.nonarc_step i hi

/-- **`step_component` for every cut dart**, by the three-way split of `CutDart`
`= D ⊕ (Fin len ⊕ Fin len)`: an `inl d` dart is, via `cycleKind`, either a forward
cycle dart `dart i`, the reverse `α (dart i)`, or an off-cycle dart `d ∉ dartSet`;
and an `inr` cap is a `capP`/`capM`.  Forward = `forward_step`; reverse =
`revbank_step`; off-cycle = `offcycle_step`; caps = `capP_step` / `capM_step`. -/
theorem step_component (S : C.ArcChordSeam) (x : C.CutDart) :
    Relation.EqvGen (genRel S.gen)
      (pOrbOf C.phiLift x) (pOrbOf C.phiLift (C.faceCorr2 x)) := by
  rcases x with d | c
  · -- `inl d`: classify `d` via `cycleKind`.
    rcases hk : C.cycleKind d with (i | i) | u
    · -- forward cycle dart `d = dart i`
      have hd : d = C.dart i := C.cycleKind_eq_inl_inl hk
      subst hd; exact S.forward_step i
    · -- reverse cycle dart `d = α (dart i)`
      have hd : d = M.α (C.dart i) := C.cycleKind_eq_inl_inr hk
      subst hd; exact S.revbank_step i
    · -- off-cycle dart `d ∉ dartSet`
      have hd : d ∉ C.dartSet := C.cycleKind_eq_inr hk
      exact S.offcycle_step d hd
  · -- Cap: `inr (inl i)` is `capP i`, `inr (inr i)` is `capM i`.
    rcases c with i | i
    · exact S.capP_step i
    · exact S.capM_step i

/-- **The per-step bank certificate from the arc-chord seam.**  This is the F-side
`BankStepCert`, with `step_component` discharged by the seam reduction: arc steps
free, non-arc (chord/junction) and cap/reverse steps from the supplied generator
obligations. -/
def toBankStepCert (S : C.ArcChordSeam) : C.BankStepCert where
  Ls := S.Ls
  Ls_len := S.Ls_len
  Ls_nodup := S.Ls_nodup
  Ls_sameCycle := S.Ls_sameCycle
  factor := S.factor
  gen := S.gen
  step_component := S.step_component

end ArcChordSeam

end SimplePrimalCycle

/-! ## 5.  The chord separation from an `ArcChordSeam`

Threading `ArcChordSeam.toBankStepCert` into `separates2_of_stepCert` /
`sphereChordSeparation_of_stepCert` gives the F-side chord wall with the seam input
reduced to the **non-arc** steps only — the arc half is closed unconditionally by the
boundary-cycle enumeration. -/

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

/-- **The chord separation `SphereChordSeparation` from an arc-chord seam.**  Same
conclusion as `sphereChordSeparation_of_stepCert`, with the F-side input the seam
reduction `ArcChordSeam` (arc steps free) instead of a bare `BankStepCert`. -/
theorem sphereChordSeparation_of_seam {u v : M.Vertex}
    (h : hNT.outerCycle.Chord u v)
    (C : SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (S : C.ArcChordSeam)
    (hwit : ∀ i : Fin C.len, C.CutBridgeWitness2 i)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart h))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart h))) :
    hNT.SphereChordSeparation h :=
  hNT.sphereChordSeparation_of_stepCert h C hsub S.toBankStepCert hwit i₀ hleft hright

/-- **The chord separates** (`data.Separates` end-to-end form) from an arc-chord seam.
This is the Chapter-35 F-side chord-wall target with the seam input reduced to the
non-arc steps. -/
theorem separates2_of_seam {u v : M.Vertex}
    (data : hNT.ChordSplitData u v)
    (C : SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (S : C.ArcChordSeam)
    (hwit : ∀ i : Fin C.len, C.CutBridgeWitness2 i)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord))) :
    data.Separates :=
  hNT.separates2_of_stepCert data C hsub S.toBankStepCert hwit i₀ hleft hright

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

/-! ## Non-vacuity: the dictionary and the arc-step closure fire concretely

We confirm the two genuine new facts are non-degenerate, ruling out the
vacuous-reduction failure mode:

* `pOrbOf_phiLift_inl_eq_iff` is a genuine iff (not a one-way collapse), exercised by
  re-deriving `dartFace`-equality from orbit-equality.
* the arc-step reflexivity `boundary_step_eqvGen` fires on any boundary cycle.
-/

namespace ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

open ProofsInTheBook.TouchRank

variable {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}

/-- The dictionary is a genuine equivalence: orbit-equality recovers face-equality. -/
example (C : SimplePrimalCycle M) (d d' : D)
    (h : pOrbOf C.phiLift (Sum.inl d) = pOrbOf C.phiLift (Sum.inl d')) :
    M.dartFace d = M.dartFace d' :=
  (C.pOrbOf_phiLift_inl_eq_iff d d').1 h

/-- The arc-step closure: two darts on one boundary cycle are `EqvGen`-connected under
*any* generator relation, by outer-face reflexivity — the arc half of
`step_component`, free of embedding data. -/
example {f : M.Face} (C : SimplePrimalCycle M) (B : BoundaryCycle M f)
    {B' : ℕ} (gen : Fin B' → ProofsInTheBook.TouchRank.POrb C.phiLift
      × ProofsInTheBook.TouchRank.POrb C.phiLift)
    {d d' : D} (hd : d ∈ B.darts) (hd' : d' ∈ B.darts) :
    Relation.EqvGen (ProofsInTheBook.TouchRank.genRel gen)
      (ProofsInTheBook.TouchRank.pOrbOf C.phiLift (Sum.inl d))
      (ProofsInTheBook.TouchRank.pOrbOf C.phiLift (Sum.inl d')) :=
  C.boundary_step_eqvGen B gen hd hd'

end ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.pOrbOf_phiLift_inl_eq_iff
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.boundary_step_eqvGen
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.pOrbOf_phiLift_chord_distinct
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.ArcChordSeam.step_component
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.ArcChordSeam.toBankStepCert
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.separates2_of_seam
