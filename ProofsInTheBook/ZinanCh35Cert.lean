import ProofsInTheBook.Chapter35
import ProofsInTheBook.JordanOracleConstruct
import ProofsInTheBook.ChordSplitFinal
import ProofsInTheBook.ZinanCh35FinalClose
import ProofsInTheBook.ChordlessFinal

/-!
# Chapter 35 certificate assembly

This leaf records the current honest certificate chain for Chapter 35.

The campaign endpoint `ZinanCh35FinalClose.chordSideResidue₁_final` closes one
side-1 `ChordSideResidue` modulo its named planar-input bundle.  The induction
surface still needs a uniform supplier for every recursive call: either a chord
recursion datum for both sides or a chordless oracle.  We therefore expose:

* `Side₁CertificateInputs`, the exact input list consumed by the landed side-1
  final close;
* `side₁Reconstruction_of_certificateInputs`, threading that side-1 result into
  the `ChordSideReconstruction` shape used by the recursive chord induction;
* `PlanarInputs`, the remaining uniform `ChordRecursiveDichotomy` bundle;
* `fiveColor_of_planarInputs`, the sharp five-color theorem currently available
  for near-triangulations from that bundle; and
* `fiveColor_of_bookCertificate`, the separate `Chapter35.chapter35` surface,
  whose hypothesis is `FiveColorReducible`.

No unconditional side-2 mirror or chordless oracle producer is fabricated here.
-/

set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35Cert

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ChordDisk
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ListColoring

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {u v : M.Vertex} {α : Type u} [DecidableEq α]

/-! ## The landed side-1 certificate, in the recursion shape -/

/-- The exact side-1 input list consumed by
`ZinanCh35FinalClose.chordSideResidue₁_final`.

This is deliberately side-1 only.  A side-2 mirror would need the same kind of
final residue producer for `sideMap₂`; no such theorem is landed in this checkout.
-/
structure Side₁CertificateInputs (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁})
    (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α) where
  ci : ContiguousInterval data hsep a₀ a₁ hne
  hshare : Side₁AnchorsShareFace data hsep a₀ a₁
  hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1)
  ha₀ : M.tail a₀.1 = u
  ha₁ : M.tail a₁.1 = v
  pₛ : (data.sideMap₁ hsep a₀ a₁ hne).Vertex
  qₛ : (data.sideMap₁ hsep a₀ a₁ hne).Vertex
  cpₛ : α
  cqₛ : α
  hLₛ : ThomassenLists
    (chordSideNearTriangulation_of_share data hsep a₀ a₁ hne hshare ci)
    pₛ qₛ (fun x => L (sideVertexToM₁ data hsep a₀ a₁ hne x)) cpₛ cqₛ
  confinement :
    ProofsInTheBook.ZinanCh35FinalClose.Side₁SchoenfliesConfinementInput data hsep

/-- The campaign's closed side-1 residue, repackaged with its exact input list. -/
def side₁Residue_of_certificateInputs (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁})
    (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (I : Side₁CertificateInputs data hsep a₀ a₁ hne L) :
    ChordSideResidue data hsep a₀ a₁ hne L :=
  ProofsInTheBook.ZinanCh35FinalClose.chordSideResidue₁_final data hsep a₀ a₁ hne L
    I.ci I.hshare I.hchord I.ha₀ I.ha₁ I.pₛ I.qₛ I.cpₛ I.cqₛ I.hLₛ I.confinement

/-- The landed side-1 certificate in the exact `ChordSideReconstruction` shape
consumed by the recursive chord induction. -/
noncomputable def side₁Reconstruction_of_certificateInputs
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (L : M.Vertex → Finset α)
    (I : Side₁CertificateInputs data hsep a₀ a₁ hne L) :
    ChordSideReconstruction hNT (sideRegion₁ data) L :=
  chordSideReconstruction_of_chord data hsep a₀ a₁ hne L
    (side₁Residue_of_certificateInputs data hsep a₀ a₁ hne L I)

/-! ## The remaining uniform planar input and the five-color corollary -/

/-- The exact remaining Chapter-35 planar input at the induction level.

It is a uniform supplier, for every recursive near-triangulation with Thomassen
lists, of either:

* a chord recursion datum, which includes both side reconstructions; or
* a chordless oracle, including the fan/deletion reconstruction and deleted-list
  bookkeeping.
-/
structure PlanarInputs (α : Type u) [DecidableEq α] : Type (u + 1) where
  recursiveDichotomy : ChordRecursiveDichotomy α

/-- `PlanarInputs` is just the named remaining induction-level supplier; it is
inhabited whenever that supplier is supplied. -/
theorem PlanarInputs_nonvacuous {α : Type u} [DecidableEq α]
    (O : ChordRecursiveDichotomy α) : Nonempty (PlanarInputs α) :=
  ⟨⟨O⟩⟩

/-- A list-coloring from the constant `Fin 5` list gives ordinary
`SimpleGraph.Colorable 5`. -/
theorem colorable_of_univ_listColorable {V : Type u} (G : SimpleGraph V)
    (h : ListColorable G (fun _ : V => (Finset.univ : Finset (Fin 5)))) :
    G.Colorable 5 := by
  rcases h with ⟨c, hc⟩
  exact ⟨SimpleGraph.Coloring.mk c (by
    intro a b hab
    exact hc.2 hab)⟩

/-- The same conversion when the five colors are universe-lifted to match the
dart universe used by the Thomassen machinery. -/
theorem colorable_of_ulift_univ_listColorable {V : Type u} (G : SimpleGraph V)
    (h : ListColorable G (fun _ : V => (Finset.univ : Finset (ULift.{u} (Fin 5))))) :
    G.Colorable 5 := by
  rcases h with ⟨c, hc⟩
  exact ⟨SimpleGraph.Coloring.mk (fun x => (c x).down) (by
    intro a b hab hsame
    exact hc.2 hab (ULift.ext _ _ hsame))⟩

/-- Five-colorability of a near-triangulation from the named remaining planar
input.  This is the sharp current `fiveColor_of_planarInputs` theorem: side-1
can be supplied by `side₁Reconstruction_of_certificateInputs`, but the induction
still needs a uniform two-sided/chordless `ChordRecursiveDichotomy`. -/
theorem fiveColor_of_planarInputs
    (hNT : NearTriangulation M) (input : PlanarInputs (ULift.{u} (Fin 5))) :
    M.toSimpleGraph.Colorable 5 :=
  colorable_of_ulift_univ_listColorable M.toSimpleGraph
    (nearTriangulation_five_colorable_unified (M := M) (α := ULift.{u} (Fin 5)) hNT
      (by simp)
      (fun _ _ _ _ => input.recursiveDichotomy))

/-- The older `JordanInput` surface also yields ordinary five-colorability; this
records the relation to `JordanOracleConstruct`. -/
theorem fiveColor_of_jordanInput
    (hNT : NearTriangulation M)
    (input : ProofsInTheBook.JordanOracleConstruct.JordanInput (ULift.{u} (Fin 5))) :
    M.toSimpleGraph.Colorable 5 :=
  colorable_of_ulift_univ_listColorable M.toSimpleGraph
    (ProofsInTheBook.JordanOracleConstruct.nearTriangulation_five_colorable_of_input
      (M := M) (α := ULift.{u} (Fin 5)) hNT (by simp) input)

/-! ## The separate book-level `Chapter35.chapter35` surface -/

/-- The book-level Chapter 35 certificate surface is the existing recursive
`FiveColorReducible` predicate on an arbitrary finite graph. -/
abbrev BookCertificate {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ProofsInTheBook.Chapter35.FiveColorReducible G

/-- The book-level theorem itself, under the explicit certificate surface.

This is separate from the near-triangulation/Jordan-input chain above: the current
repository does not produce `FiveColorReducible G` from the chord-side campaign
endpoint alone. -/
theorem fiveColor_of_bookCertificate {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (cert : BookCertificate G) :
    G.Colorable 5 :=
  ProofsInTheBook.Chapter35.chapter35 G cert

end ProofsInTheBook.ZinanCh35Cert

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35Cert.side₁Residue_of_certificateInputs
#print axioms ProofsInTheBook.ZinanCh35Cert.side₁Reconstruction_of_certificateInputs
#print axioms ProofsInTheBook.ZinanCh35Cert.fiveColor_of_planarInputs
#print axioms ProofsInTheBook.ZinanCh35Cert.fiveColor_of_jordanInput
#print axioms ProofsInTheBook.ZinanCh35Cert.fiveColor_of_bookCertificate
