import ProofsInTheBook.OrbitLabelCert
import ProofsInTheBook.PlanarMapCutCap2FWalk
import ProofsInTheBook.PlanarMapSeamInst

/-!
# The genus-free orbit-label layer for `numCycles φ'₂` (Chapter 35, F-count)

This file is the intended *closing* layer of the genus-free F-count design
(`HANDOFF/CH35_GENUSFREE_DESIGN.md`, route B), which proposed to discharge the named
core `NumCyclesCutPhi2 : numCycles φ'₂ = M.F + 2` **unconditionally** via the proven
abstract engine `OrbitLabelCert` (`OrbitLabelCert.lean`) instantiated at the label
type `β = OldFace(φ) ⊕ Side`, with a label function

  `cutFaceLabel : C.CutDart → OldFace(φ) ⊕ Side`

required to be `φ'₂`-invariant (`cutFaceLabel (φ'₂ x) = cutFaceLabel x`) and to send
each old cut dart `inl d` to `Sum.inl (faceOf d)` (the design's §§4–7).

## Honest status: the design's label is mathematically *unrealizable* (not merely hard)

We carried out the design's Layer-4/6 construction and discovered — and then
**verified inside Lean on the repository's own computable surgery mirror**
(`SeamInstEval`, the `#eval` probes at the end of this file, reproduced clause-for-
clause from `cutAlpha`/`cutSigma2`) — that the two structural fields the design
demands have **no instance**, because they assert a `φ'₂`-orbit structure that
*contradicts the actual `φ'₂`-orbits*.

Concretely, on the `K₄` **sphere** cut `A→B→D` (`χ = 2`, `F = 4`, so `F' = 6`), the
Lean-computed data is:

* old `φ`-faces (`F = 4`):
  `{0,8,5}`, `{1,2,7}`, `{3,4,11}`, `{6,10,9}`;
* `φ'₂`-orbits (`F' = 6`, with `100+i = c_i^+`, `200+i = c_i^-`):
  `{0,8,5}`, `{1,4,9}`, `{2,7,c_0^+}`, `{3,c_2^+,11}`, `{6,10,c_1^+}`,
  `{c_0^-,c_1^-,c_2^-}`.

Two facts are then forced and are *both fatal* to the design:

1. **The `φ'₂`-orbit `{inl 1, inl 4, inl 9}` mixes three distinct old faces** (dart `1`
   lies in face `{1,2,7}`, dart `4` in `{3,4,11}`, dart `9` in `{6,10,9}`).  A
   `φ'₂`-invariant label is *constant on each `φ'₂`-orbit*; so a label of the design's
   form (`inl d ↦ Sum.inl (faceOf d)`) would have to assign one single old face to all
   of `1, 4, 9` — impossible, since they sit in three different faces.  Hence
   `cutFaceLabel_phi'2` together with `cutFaceLabel (inl d) = Sum.inl (faceOf d)` is
   **unsatisfiable**.

2. **The old face `{1,2,7}` is split across two `φ'₂`-orbits** (`inl 1 ∈ {1,4,9}`,
   `inl 2, inl 7 ∈ {2,7,c_0^+}`).  The design's Layer-6 connectivity keystone
   `oldFaceLift_phi_step : SameCycle φ'₂ (oldFaceLift d) (oldFaceLift (φ d))` would, for
   `d = 1` (with `φ 1 = 2`), require `SameCycle φ'₂ (oldFaceLift 1) (oldFaceLift 2)`;
   but with any lift landing on the corresponding `inl` darts these are in **different**
   `φ'₂`-orbits, so no `oldFaceLift : D → C.CutDart` can make this hold — no choice of
   representative can merge two genuinely distinct `φ'₂`-orbits.

This is exactly the obstruction already recorded (without the orbit-label vocabulary)
in `PlanarMapCutCap2F.lean`'s reconnaissance — *"the map `d ↦ ⟦inl d⟧_{φ'₂}` is not
constant on old `φ`-orbits … the naive face-survival bijection of the design is false
as stated; old faces do not survive intact"* — now pinned to the precise failing
fields and the precise Lean-verified witness.

The abstract engine `OrbitLabelCert` is sound and proven; the failure is solely that
the **specific** instantiation `β = OldFace(φ) ⊕ Side` with the `faceOf`-based label
**has no instance**: `φ'₂` reorganises the darts so that its orbits are *not* the old
faces (rerouted or otherwise) plus two caps — they genuinely merge and split old
faces.  No genus-uniform, closed-form `φ'₂`-invariant label onto a type of independent
cardinality `F + 2` is available (the only natural such target the design identified,
`OldFace(φ) ⊕ Side`, is the refuted one).

Consequently **layers 4–9 cannot be built as designed**, and `NumCyclesCutPhi2` is
*not* closed unconditionally by this route.  The strongest honest result for the core
remains the already-formalised **conditional** one in `PlanarMapSeamInst.lean`:
`SeamInst.SeamDecomposition.numCyclesCutPhi2`, which discharges `NumCyclesCutPhi2` from
a concrete two-cap-chain seam decomposition — an instance of which exists at genus `0`
and **provably fails at genus `1`** (the `K₄` torus threads both cap signs into one
`faceCorr₂`-cycle).  This repository commits no `sorry`/`axiom`/`admit`, so no fake
certificate, no unsatisfiable-hypothesis theorem, and no false label lemma is recorded
here.

## What this file *does* contribute (all unconditional and genus-free)

The genus-free **label type** and the **cardinality bridge** are correct and reusable
for any future `φ'₂`-invariant label (should one be found): the side type `Side`, the
old-face quotient `OldFace`, the face-class map `faceOf` with its `φ`-invariance
`faceOf_phi`, the side anchors, and the *true* count

  `Fintype.card (OldFace M.φ ⊕ Side) = M.F + 2`.

These are exactly the pieces the engine would consume *after* a valid label; they are
established here unconditionally so that the one genuinely missing input — a
`φ'₂`-invariant label, refuted above for the `faceOf` form — is isolated cleanly.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount

/-! ## Layer 3/4 (type level): the genus-free face-label type

`OldFace M.φ` is the `φ`-orbit quotient (`= M.F` classes); `Side` is the two cap
faces; `CutFaceLabel` is their sum, of cardinality `M.F + 2`.  These are correct and
unconditional regardless of the realisability of the label *function*. -/

/-- The two new cap faces of the cut-and-cap surgery. -/
inductive Side
  | plus
  | minus
  deriving DecidableEq

instance : Fintype Side := ⟨{Side.plus, Side.minus}, fun s => by cases s <;> simp⟩

@[simp] lemma card_side : Fintype.card Side = 2 := rfl

/-- The old-face type: the `φ`-orbit quotient on `D` (one class per old face). -/
abbrev OldFace (M : CombMap D) : Type _ := Quotient (cycleSetoid M.φ)

/-- The old face of a dart. -/
def faceOf (d : D) : OldFace M := Quotient.mk (cycleSetoid M.φ) d

/-- **Old faces are `φ`-invariant**: a `φ`-step keeps a dart in its old face. -/
@[simp] lemma faceOf_phi (d : D) : faceOf (M.φ d) = (faceOf d : OldFace M) :=
  Quotient.sound (Equiv.Perm.SameCycle.symm ⟨1, by simp⟩)

/-- Two darts share an old face iff they are `φ`-`SameCycle`. -/
lemma faceOf_eq_iff {d e : D} :
    (faceOf d : OldFace M) = faceOf e ↔ M.φ.SameCycle d e :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- **The genus-free face-label type** `CutFaceLabel := OldFace(φ) ⊕ Side`. -/
abbrev CutFaceLabel (C : SimplePrimalCycle M) : Type _ := OldFace M ⊕ Side

/-! ## The cardinality bridge `card (OldFace ⊕ Side) = M.F + 2`

This is the *true* counting content the engine would consume after a valid label:
`card OldFace = numCycles φ = M.F` (`card_cycleSetoid_eq_numCycles`, `F_eq_numCycles`)
and `card Side = 2`.  Unconditional and genus-free. -/

/-- `card (OldFace M) = M.F`. -/
lemma card_oldFace : Fintype.card (OldFace M) = M.F := by
  rw [CombMap.card_cycleSetoid_eq_numCycles, ← CombMap.F_eq_numCycles]

/-- **The cardinality bridge.**  The genus-free label type has exactly `M.F + 2`
elements — the value the orbit-label engine would deliver as `numCycles φ'₂` *if* a
`φ'₂`-invariant label onto it existed.  (It does not, for the `faceOf` form; see the
file header.) -/
theorem card_cutFaceLabel (C : SimplePrimalCycle M) :
    Fintype.card C.CutFaceLabel = M.F + 2 := by
  show Fintype.card (OldFace M ⊕ Side) = M.F + 2
  rw [Fintype.card_sum, card_oldFace, card_side]

/-! ## Side anchors

The two cap representatives `c_0^+`, `c_0^-`.  These are the anchors the engine would
use for the two `Side` labels; they are well-defined unconditionally. -/

/-- The `+`-cap anchor `c_0^+` (well-defined since `0 < C.len`). -/
def plusAnchor (C : SimplePrimalCycle M) : C.CutDart :=
  C.capP ⟨0, C.len_pos⟩

/-- The `−`-cap anchor `c_0^-`. -/
def minusAnchor (C : SimplePrimalCycle M) : C.CutDart :=
  C.capM ⟨0, C.len_pos⟩

@[simp] lemma plusAnchor_eq (C : SimplePrimalCycle M) :
    C.plusAnchor = Sum.inr (Sum.inl ⟨0, C.len_pos⟩) := rfl

@[simp] lemma minusAnchor_eq (C : SimplePrimalCycle M) :
    C.minusAnchor = Sum.inr (Sum.inr ⟨0, C.len_pos⟩) := rfl

/-! ## The missing input, isolated

The engine `OrbitLabelCert.numCycles_eq_card` would give, from a certificate
`C : OrbitLabelCert φ'₂ C.CutFaceLabel`,

  `numCycles φ'₂ = Fintype.card C.CutFaceLabel = M.F + 2`  (`card_cutFaceLabel`),

i.e. exactly `C.NumCyclesCutPhi2`.  The *only* missing piece is the certificate
itself, whose `label`/`label_invariant`/`same_anchor` fields the file header shows are
**unsatisfiable** for the design's `faceOf`-based label (Lean-verified on the `K₄`
sphere: the `φ'₂`-orbit `{1,4,9}` mixes three old faces, and the old face `{1,2,7}`
splits across two `φ'₂`-orbits).  We therefore do **not** construct such a certificate
(doing so would require an unsatisfiable hypothesis or a `sorry`).  The strongest
honest discharge of the core is the conditional
`SeamInst.SeamDecomposition.numCyclesCutPhi2` (genus-`0`, refuted at genus-`1`).

The bridge below records the exact reduction the engine *would* provide, as a clean
statement of "what a valid label buys", with no false content. -/

/-- **The engine reduction made explicit.**  *Any* orbit-label certificate for `φ'₂`
over `C.CutFaceLabel` discharges the named core `NumCyclesCutPhi2`.  This is an
honest, unconditional consequence of the proven engine and the cardinality bridge; it
carries the certificate as an explicit hypothesis precisely because — per the file
header — no such certificate exists for the design's `faceOf`-based label, so this is
*not* a closed proof of the core but a faithful statement of the route's remaining
obligation. -/
theorem numCyclesCutPhi2_of_orbitLabelCert (C : SimplePrimalCycle M)
    (cert : OrbitLabelCert (C.cutCapMap2).φ C.CutFaceLabel) :
    C.NumCyclesCutPhi2 := by
  rw [NumCyclesCutPhi2, cert.numCycles_eq_card, card_cutFaceLabel]

end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

/-! ## In-file Lean verification of the refutation (reproducible kernel anchors)

The `#eval`s below run the repository's own computable surgery mirror (`SeamInstEval`,
identical clause-for-clause to `cutAlpha`/`cutSigma2`) on the `K₄` **sphere** cut
`A→B→D` and print the actual `φ'₂`-orbits and old `φ`-faces.  They are the Lean
witnesses for the file-header refutation:

* `φ'₂`-orbit `[1, 4, 9]` mixes the three old faces `[1,2,7]`, `[3,4,11]`, `[6,10,9]`;
* old face `[1,2,7]` splits across `φ'₂`-orbits `[1,4,9]` and `[2,7,100]`
  (`100 = c_0^+`).

Hence no `φ'₂`-invariant `faceOf`-based label exists, and the design's
`oldFaceLift_phi_step` is false (e.g. `φ 1 = 2` with `inl 1`, `inl 2` in different
`φ'₂`-orbits). -/

namespace ProofsInTheBook.PlanarMap

namespace SeamInstEval

open List

-- `φ'₂`-orbits on the `K₄`-sphere cut `A→B→D` (encoded: `100+i = c_i^+`,
-- `200+i = c_i^-`).  Six orbits = `F' = F + 2 = 6`.
#eval ("K4-sphere φ'₂-orbits",
  (allCD 12).filterMap (fun x =>
    let f := phi2 alphaK4 sigmaSphere dartABD
    if orbitRep (allCD 12) f x = some x then
      some ((orbitOf (allCD 12).length f x).dedup.map enc)
    else none))
-- ("K4-sphere φ'₂-orbits", [[0,8,5],[1,4,9],[2,7,100],[3,102,11],[6,10,101],[200,201,202]])

-- Old `φ`-faces on `K₄`-sphere (`φ = σ ∘ α`).  Four faces = `F = 4`.
#eval ("K4-sphere old φ-faces",
  (List.finRange 12).filterMap (fun d =>
    let f := fun e => sigmaSphere (alphaK4 e)
    if ((List.finRange 12).filter (fun y => decide (y ∈ orbitOf 12 f d))).head? = some d then
      some ((orbitOf 12 f d).dedup.map (fun e => (e : Int)))
    else none))
-- ("K4-sphere old φ-faces", [[0,8,5],[1,2,7],[3,4,11],[6,10,9]])
--   ⇒ φ'₂-orbit [1,4,9] mixes faces [1,2,7],[3,4,11],[6,10,9];
--     face [1,2,7] splits across φ'₂-orbits [1,4,9] and [2,7,100].

end SeamInstEval

end ProofsInTheBook.PlanarMap
