import ProofsInTheBook.ChordFaceCount
import ProofsInTheBook.PlanarMapEulerInequality

/-!
# The two local genus-0 disk facts of a chord split (Chapter 35 — discrete Jordan–Schoenflies)

`ChordFaceCount.lean` reduced the chord-split side map's `IsSphereMap` to TWO purely-local
genus-0 disk facts of the *kept* side (the side submap before the duplicated chord edge is
spliced):

1. **(`KeptSideIsDisk`)** the kept side map `keptCombMap β ρ` is a sphere map
   (`Connected ∧ eulerChar = 2`) — *each side of the chord split is a combinatorial disk*;
2. **(`AnchorsShareBoundaryFace`)** the two chord anchors' rotation successors `ρ a₀`, `ρ a₁`
   lie on a common kept face (the shared boundary face the chord splits).

These two facts are *exactly* the hypotheses `hkept_sphere`, `hsame` of
`ChordFaceCount.chordFaceCount_closed_of_genus0`.  This file is the discrete
Jordan–Schoenflies layer that addresses them.

## What is proved here (everything derivable), and what is the irreducible residue

The face count `FreshFaceCount` is no longer the residue — `ChordFaceCount` proved it from
fact 1 + fact 2 via the explicit face-orbit bijection.  This file:

* **`keptSide_eulerChar_le_two`** — proves the **lower-bound (≤) half of fact 1
  unconditionally**: a connected kept side has `eulerChar ≤ 2` (the genus `≥ 0` bound,
  `chi_le_two_of_connected`).  So fact 1's content is *exactly* the **reverse** inequality
  `eulerChar ≥ 2`: the kept side has **no handle** (genus exactly 0).  This pins fact 1 to a
  single no-handle disk statement, and shows it is a `chi ≤ 2`-and-`≥ 2` squeeze whose lower
  half is free and whose upper half (`χ ≥ 2`) is the genuine Schoenflies content.

* **`keptSideIsDisk_iff_eulerChar_ge_two`** — fact 1 is *equivalent*, given connectivity, to
  `2 ≤ eulerChar` (combined with the free `≤ 2`).  This is the precise reduction of the disk
  fact to its no-handle core.

* **`chordDisk_produces_isSphereMap`** / **`chordDisk_produces_freshFaceCount`** — the two
  facts produce the side map's full `IsSphereMap` *and* the face count `FreshFaceCount`
  **unconditionally on the count** (re-exporting `ChordFaceCount`), threading the disk facts
  to the genus-0 side structure.

* **`chordSideJordanData_of_disk`** — the two facts produce the `ChordSideRecon`
  `ChordSideJordanData` bundle of one side (connectivity + face count + vertex bound),
  the chord analogue of `FanSurgeryReconstruction`'s isolated Jordan fields.

* **Section F (non-vacuity)** — both facts hold simultaneously on the concrete genus-0
  sphere witness of `ChordSplitEuler`, so the producers genuinely fire (no unsatisfiable
  premise; §3.3 satisfiability obligation discharged).

* **Section G (the unconditional Five Color Theorem headline, conditional scope)** — the
  clean statement that, *with the two local disk facts of each side*, the chord case of the
  Thomassen induction closes; the precise residue blocking a fully unconditional
  `nearTriangulation_listColorable_chordRecursive` is isolated and named.

## The irreducible residue (honest §3.3 verdict)

Fact 1's reverse inequality `2 ≤ eulerChar(keptSide)` — *the kept side has no handle* — is
the genuine discrete Jordan–Schoenflies content and is **not** derivable at the
combinatorial-map layer, confirmed against the repository's own kernel-decided
counterexample (`CutFaceLabel.lean`, `PlanarMapSeamInst.lean`):

* M's `eulerChar = 2` is a **global** numeric constraint.  Transferring it to the **per-side**
  value requires the side-face additivity `F₁ + F₂ = F + 1`, which `CutFaceLabel` verified
  *inside the Lean kernel* is **genus-dependent**: the cut/chord face permutation genuinely
  **merges and splits** old faces (the `φ'₂`-orbit `{1,4,9}` mixes three old faces; the old
  face `{1,2,7}` splits across two orbits), so **no genus-uniform `φ'₂`-invariant orbit
  label** of the right cardinality exists.  Hence no orbit-bijection carries M's genus-0
  value onto the side, and `χ(keptSide) ≥ 2` is genuinely the Jordan-curve separation
  content, not orbit bookkeeping.

* The repo's `chi_le_two_of_connected` is the *only* Euler (in)equality available; it gives
  the `≤ 2` half but **provably not** the `≥ 2` half (a connected map can have a handle,
  `χ = 0`).  The repo has no "single boundary cycle ⟹ disk" lemma, and constructing one is
  precisely the discrete Schoenflies theorem, requiring the actual planar embedding the
  abstract `CombMap` does not carry.

So fact 1 (its `≥ 2` half) and fact 2 are isolated here as two named, satisfiable Props
(`KeptSideIsDisk`, `AnchorsShareBoundaryFace`); the face count is *proved* from them; and the
producers fire on the genus-0 witness.  This is the same single Jordan joint the whole Ch35
route carries, now reduced to the minimal local disk facts with the count discharged — the
strictly finer state the orchestration sought, with the residue stated honestly rather than
faked (per playbook §3.3: no fake disk lemma, no unsatisfiable-hypothesis theorem).

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordDisk

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]

/-! ## Section A.  The two local genus-0 disk facts, named

These are *exactly* the hypotheses of `ChordFaceCount.chordFaceCount_closed_of_genus0`.  We
name them as standalone Props so the residue is isolated cleanly (§3.3). -/

section Facts

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  (a₀ a₁ : K)

/-- **Fact 1 (the disk fact).**  The kept side of the chord split — the kept combinatorial
map `keptCombMap β ρ` (the side submap *before* the duplicated chord edge is spliced) — is a
combinatorial disk: a sphere map (`Connected ∧ eulerChar = 2`).  This is the discrete
Schoenflies content: a simple closed curve (chord ∪ boundary arc) on the genus-0 sphere M
bounds a disk on each side. -/
def KeptSideIsDisk : Prop := (keptCombMap β ρ hβinv hβfix).IsSphereMap

/-- **Fact 2 (the anchor incidence fact).**  The two chord anchors' rotation successors
`ρ a₀`, `ρ a₁` lie on a common kept face (the same `keptPhi = ρ * β`-cycle): the shared outer
boundary face that the chord splits.  This is a local incidence fact about the chord
endpoints' position on the side's boundary cycle. -/
def AnchorsShareBoundaryFace : Prop := (keptPhi β ρ).SameCycle (ρ a₀) (ρ a₁)

end Facts

/-! ## Section B.  The derivable half of fact 1 (the `≤ 2` genus bound, unconditional)

`chi_le_two_of_connected` gives `eulerChar(keptSide) ≤ 2` from connectivity alone (the genus
`≥ 0` bound).  So fact 1's only genuinely missing content is the **reverse** inequality
`2 ≤ eulerChar`: the kept side has *no handle* (genus exactly `0`).  This isolates fact 1 to
a single no-handle disk statement. -/

section LowerHalf

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)

/-- **The genus `≤ 2` half of the disk fact, unconditional.**  A connected kept side has
`eulerChar ≤ 2` (the genus-zero upper bound, from `chi_le_two_of_connected`).  This is the
half of fact 1 the combinatorial layer *does* supply. -/
theorem keptSide_eulerChar_le_two
    (hconn : (keptCombMap β ρ hβinv hβfix).Connected) :
    (keptCombMap β ρ hβinv hβfix).eulerChar ≤ 2 :=
  chi_le_two_of_connected _ hconn

/-- **Fact 1 is the no-handle squeeze.**  Given connectivity, the kept side is a disk
(`KeptSideIsDisk`) *iff* its Euler characteristic is at least `2`.  The `≤ 2` half is free
(`keptSide_eulerChar_le_two`); the `≥ 2` half is the genuine discrete-Schoenflies content
(no handle).  This pins fact 1 to one reverse inequality. -/
theorem keptSideIsDisk_iff_eulerChar_ge_two
    (hconn : (keptCombMap β ρ hβinv hβfix).Connected) :
    KeptSideIsDisk β ρ hβinv hβfix ↔ 2 ≤ (keptCombMap β ρ hβinv hβfix).eulerChar := by
  unfold KeptSideIsDisk IsSphereMap
  constructor
  · rintro ⟨_, heuler⟩; exact le_of_eq heuler.symm
  · intro hge
    exact ⟨hconn, le_antisymm (keptSide_eulerChar_le_two β ρ hβinv hβfix hconn) hge⟩

end LowerHalf

/-! ## Section C.  The two facts produce the side's genus-0 structure (the threading)

Given fact 1 (`KeptSideIsDisk`) and fact 2 (`AnchorsShareBoundaryFace`), `ChordFaceCount`
produces — *unconditionally on the face count* — the side map's full `IsSphereMap` and the
face count `FreshFaceCount` itself (via the explicit face-orbit bijection
`freshMap_F_eq_tracePhi` plus the genus-0 transposition sign).  We thread the named facts
through `ChordFaceCount.freshMap_isSphereMap_of_genus0` / `freshFaceCount_of_genus0`. -/

section Threading

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- **The two disk facts produce the side map's `IsSphereMap`.**  Fact 1 (kept side is a
disk) + fact 2 (anchors share the boundary face) give the *full* genus-0 structure of the
spliced side map: connectivity (transferred across the splice in `ChordSideRecon`) and
`eulerChar = 2` (the face count `FreshFaceCount`, proved from the bijection in
`ChordFaceCount`).  The face count is **not** a hypothesis. -/
theorem chordDisk_produces_isSphereMap
    (hdisk : KeptSideIsDisk β ρ hβinv hβfix)
    (hshare : AnchorsShareBoundaryFace β ρ a₀ a₁) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).IsSphereMap :=
  freshMap_isSphereMap_of_genus0 β ρ hβinv hβfix hne hdisk hshare

/-- **The two disk facts produce the face count `FreshFaceCount`.**  This is the discharge of
the kernel-confirmed genus-dependent residue from the two local disk facts (the splice
*splits* the shared boundary face, `+1`, and the kept disk's `V − E + F = 2` closes the
arithmetic). -/
theorem chordDisk_produces_freshFaceCount
    (hdisk : KeptSideIsDisk β ρ hβinv hβfix)
    (hshare : AnchorsShareBoundaryFace β ρ a₀ a₁) :
    FreshFaceCount β ρ hβinv hβfix hne :=
  freshFaceCount_of_genus0 β ρ hβinv hβfix hne hdisk.2 hshare

/-- **The two disk facts produce the `ChordSideRecon.ChordSideJordanData` bundle.**  This is
the chord analogue of `FanSurgeryReconstruction`'s isolated Jordan fields: connectivity
(from fact 1), the face count (proved from facts 1+2), and the vertex bound (derived from
fact 1's Euler identity).  Hence the producer `freshMap_isSphereMap_of_jordan` fires on it. -/
theorem chordSideJordanData_of_disk
    (hdisk : KeptSideIsDisk β ρ hβinv hβfix)
    (hshare : AnchorsShareBoundaryFace β ρ a₀ a₁) :
    ChordSideJordanData β ρ hβinv hβfix a₀ a₁ hne where
  kept_connected := hdisk.1
  face_count := chordDisk_produces_freshFaceCount β ρ hβinv hβfix hne hdisk hshare
  vbound := vbound_of_kept_euler β ρ hβinv hβfix hdisk.2

end Threading

/-! ## Section D.  Instantiation at the genuine chord-split side maps

The side map `sideMapᵢ = freshMap (sideAlphaᵢ) (sideSigmaᵢ) …`, so the named facts and their
producers apply verbatim, with the kept side being `sideKeptMapᵢ` and the anchors being the
splice anchors' `sideSigmaᵢ`-successors. -/

section ChordApplication

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **Fact 1 at side 1.**  The kept side-1 map `sideKeptMap₁` is a disk. -/
def Side₁IsDisk (data : hNT.ChordSplitData u v) (hsep : data.Separates) : Prop :=
  (sideKeptMap₁ data hsep).IsSphereMap

/-- **Fact 2 at side 1.**  The side-1 splice anchors' `sideSigma₁`-successors share a kept
face. -/
def Side₁AnchorsShareFace (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) : Prop :=
  (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁).SameCycle
    (data.sideSigma₁ a₀) (data.sideSigma₁ a₁)

/-- **Side-1 map is a genus-0 sphere map, from side 1's two disk facts** — face count
discharged (no longer a hypothesis), via `ChordFaceCount`. -/
theorem side₁_isSphereMap_of_disk
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hdisk : Side₁IsDisk data hsep)
    (hshare : Side₁AnchorsShareFace data hsep a₀ a₁) :
    (data.sideMap₁ hsep a₀ a₁ hne).IsSphereMap :=
  chordDisk_produces_isSphereMap _ _ _ _ hne hdisk hshare

/-- **Side-1 face count `FreshFaceCount`, discharged from side 1's two disk facts.** -/
theorem side₁_freshFaceCount_of_disk
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hdisk : Side₁IsDisk data hsep)
    (hshare : Side₁AnchorsShareFace data hsep a₀ a₁) :
    FreshFaceCount (data.sideAlpha₁ hsep) data.sideSigma₁
      (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne :=
  chordDisk_produces_freshFaceCount _ _ _ _ hne hdisk hshare

/-- **Fact 1 at side 2.** -/
def Side₂IsDisk (data : hNT.ChordSplitData u v) (hsep : data.Separates) : Prop :=
  (sideKeptMap₂ data hsep).IsSphereMap

/-- **Fact 2 at side 2.** -/
def Side₂AnchorsShareFace (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) : Prop :=
  (keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂).SameCycle
    (data.sideSigma₂ a₀) (data.sideSigma₂ a₁)

/-- **Side-2 map is a genus-0 sphere map, from side 2's two disk facts.** -/
theorem side₂_isSphereMap_of_disk
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (hdisk : Side₂IsDisk data hsep)
    (hshare : Side₂AnchorsShareFace data hsep a₀ a₁) :
    (data.sideMap₂ hsep a₀ a₁ hne).IsSphereMap :=
  chordDisk_produces_isSphereMap _ _ _ _ hne hdisk hshare

/-- **The `≤ 2` half of side 1's disk fact, unconditional** (from side-1 connectivity).
Isolates side 1's residue to the reverse inequality `2 ≤ eulerChar(sideKeptMap₁)`. -/
theorem side₁_keptSide_eulerChar_le_two
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hconn : (sideKeptMap₁ data hsep).Connected) :
    (sideKeptMap₁ data hsep).eulerChar ≤ 2 :=
  chi_le_two_of_connected _ hconn

end ChordApplication

/-! ## Section E.  Non-vacuity (the §3.3 satisfiability obligation)

Both facts hold simultaneously on the concrete genus-0 sphere witness of `ChordSplitEuler`
(`K = Fin 2`, `β = swap 0 1`, `ρ = 1`, anchors `0, 1`).  Hence the producers genuinely fire
and the two-fact conditional is *not* vacuous. -/

section NonVacuity

/-- **Fact 1 holds on the concrete witness.**  The witness's kept side is a disk
(`ChordFaceCount.witness_kept_isSphereMap`). -/
theorem witness_KeptSideIsDisk :
    KeptSideIsDisk (Equiv.swap (0 : Fin 2) 1) (1 : Equiv.Perm (Fin 2))
      (by decide) (by decide) :=
  witness_kept_isSphereMap

/-- **Fact 2 holds on the concrete witness.**  The witness's chord successors share a kept
face (`ChordFaceCount.witness_same_face`). -/
theorem witness_AnchorsShareBoundaryFace :
    AnchorsShareBoundaryFace (Equiv.swap (0 : Fin 2) 1) (1 : Equiv.Perm (Fin 2)) 0 1 :=
  witness_same_face

/-- **The two-fact producer genuinely fires** on the concrete witness: `sphereWitness` is a
sphere map, produced from facts 1+2 via the explicit face-orbit bijection.  Hence
`chordDisk_produces_isSphereMap` is not a vacuous conditional (§3.3). -/
theorem sphereWitness_isSphereMap_via_disk :
    ChordSplitEuler.sphereWitness.IsSphereMap :=
  chordDisk_produces_isSphereMap _ _ _ _ (show (0 : Fin 2) ≠ 1 by decide)
    witness_KeptSideIsDisk witness_AnchorsShareBoundaryFace

/-- The face count is genuinely produced from the two facts on the witness. -/
theorem witness_freshFaceCount_via_disk :
    FreshFaceCount (Equiv.swap (0 : Fin 2) 1) (1 : Equiv.Perm (Fin 2))
      (by decide) (by decide) (show (0 : Fin 2) ≠ 1 by decide) :=
  chordDisk_produces_freshFaceCount _ _ _ _ (show (0 : Fin 2) ≠ 1 by decide)
    witness_KeptSideIsDisk witness_AnchorsShareBoundaryFace

/-- The `ChordSideJordanData` bundle is genuinely produced from the two facts on the witness
(certifying the bundle producer fires; §3.3 non-vacuity). -/
theorem witness_chordSideJordanData_via_disk :
    ChordSideJordanData (Equiv.swap (0 : Fin 2) 1) (1 : Equiv.Perm (Fin 2))
      (by decide) (by decide) 0 1 (show (0 : Fin 2) ≠ 1 by decide) :=
  chordSideJordanData_of_disk _ _ _ _ (show (0 : Fin 2) ≠ 1 by decide)
    witness_KeptSideIsDisk witness_AnchorsShareBoundaryFace

end NonVacuity

/-! ## Section F.  Headline + the precise residue blocking the unconditional FCT

The chord-split genus-0 side structure is now reduced to **two named, satisfiable, local disk
facts** with the face count *proved* from them.  `chordDisk_side_genus0_certificate` is the
headline: from the two facts of one side, the side map is a genus-0 sphere map AND its face
count holds — the entire `IsSphereMap` field of a `ChordSideReconstruction`, with the count
no longer assumed. -/

section Headline

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The chord-split genus-0 side certificate, from the two local disk facts.**  Given side
1's two disk facts (it is a disk, and its anchors share the boundary face), side 1's map is a
genus-0 sphere map AND its face count `FreshFaceCount` holds — *the face count discharged from
the explicit face-orbit bijection, no longer assumed*.  This is the genus-0 `IsSphereMap`
field of a `ChordSideReconstruction`, reduced to the two minimal local Jordan facts. -/
theorem chordDisk_side_genus0_certificate
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hdisk : Side₁IsDisk data hsep)
    (hshare : Side₁AnchorsShareFace data hsep a₀ a₁) :
    (data.sideMap₁ hsep a₀ a₁ hne).IsSphereMap ∧
      FreshFaceCount (data.sideAlpha₁ hsep) data.sideSigma₁
        (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne :=
  ⟨side₁_isSphereMap_of_disk data hsep a₀ a₁ hne hdisk hshare,
    side₁_freshFaceCount_of_disk data hsep a₀ a₁ hne hdisk hshare⟩

end Headline

/-! ## Section G.  Verdict (§3.3) and the precise residue

### Verdict

* **FAITHFUL (the reduction + threading + count discharge).**  `KeptSideIsDisk` and
  `AnchorsShareBoundaryFace` are *exactly* the two hypotheses `ChordFaceCount` isolated;
  the face count `FreshFaceCount` is **proved** from them (`chordDisk_produces_freshFaceCount`,
  via the explicit face-orbit bijection of `ChordFaceCount`), not re-wrapped.  The full side
  `IsSphereMap` is produced (`chordDisk_produces_isSphereMap`), and the `≤ 2` genus half of
  the disk fact is proved unconditionally (`keptSide_eulerChar_le_two`), pinning the disk fact
  to its single reverse-inequality no-handle core (`keptSideIsDisk_iff_eulerChar_ge_two`).

* **Non-vacuous.**  Both facts hold simultaneously on the concrete genus-0 sphere witness
  (`witness_KeptSideIsDisk`, `witness_AnchorsShareBoundaryFace`), and every producer fires on
  it (`sphereWitness_isSphereMap_via_disk`, `witness_freshFaceCount_via_disk`,
  `witness_chordSideJordanData_via_disk`).  No unsatisfiable premise.

* **The two facts are NOT derivable at this layer (honest residue, kernel-confirmed).**
  `KeptSideIsDisk`'s reverse inequality `2 ≤ eulerChar(keptSide)` — *the kept side has no
  handle* — is the genuine discrete Jordan–Schoenflies content.  It is **refuted** that it
  follows from `Separates` + M's `eulerChar = 2` value by counting alone, against the repo's
  own kernel-decided counterexample (`CutFaceLabel`/`PlanarMapSeamInst`):

    - The per-side additivity `F₁ + F₂ = F + 1` needed to transfer M's global `eulerChar = 2`
      to the side is **genus-dependent** — verified *inside the Lean kernel* on the `K₄`
      sphere/torus probes: the cut/chord face permutation **merges and splits** old faces, so
      no genus-uniform orbit label of cardinality `F + 2` exists.  Concrete failing tactic
      chain (the exact obstruction `CutFaceLabel.lean` records): the would-be label
      `cutFaceLabel (inl d) = Sum.inl (faceOf d)` with `cutFaceLabel (φ'₂ x) = cutFaceLabel x`
      is **unsatisfiable** because the `φ'₂`-orbit `{inl 1, inl 4, inl 9}` forces one old face
      onto darts `1 ∈ {1,2,7}`, `4 ∈ {3,4,11}`, `9 ∈ {6,10,9}` — three distinct old faces.

    - `chi_le_two_of_connected` (the *only* Euler (in)equality in the repo) supplies the `≤ 2`
      half but **not** the `≥ 2` half: a connected `CombMap` may carry a handle (`χ = 0`).
      The repo has no "single boundary cycle ⟹ `χ = 2`" disk lemma; building one is the
      discrete Schoenflies theorem itself, requiring the planar embedding the abstract
      `CombMap` does not carry.

  Per playbook §3.3 (no fake disk lemma, no unsatisfiable-hypothesis theorem), the two facts
  are isolated here as named satisfiable Props, the count is proved from them, and the
  producers fire — the maximal honest reduction.

### Residue blocking the fully unconditional `nearTriangulation_listColorable_chordRecursive`

A fully unconditional `ChordRecursiveDichotomy` further needs, beyond the two disk facts, the
remaining `ChordSideReconstruction` fields — the side's `outerCycle`/`outer_simple`/
`outer_len`/`inner_tri` (the side boundary = arc + duplicated chord, a `BoundaryCycle` of the
side map) and the vertex correspondence `ι`'s surjectivity onto the region (`ι_surj`).  These
are the *same* discrete Jordan/Schoenflies classification layer as the two disk facts (the
side-face ↔ M-face correspondence the kernel campaign proved does not exist genus-uniformly);
they are not fabricated here (doing so would require a fake outer cycle / fake face
correspondence, forbidden by §3.3).  So `five_colorable` stays CONDITIONAL on the chord-side
disk data, now with the genus-0 `IsSphereMap` field's *face count proved* from the two named
local facts and its connectivity half proved (`ChordSideRecon`) — the strictly finer state.
-/

end ProofsInTheBook.ChordDisk

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ChordDisk.keptSide_eulerChar_le_two
#print axioms ProofsInTheBook.ChordDisk.keptSideIsDisk_iff_eulerChar_ge_two
#print axioms ProofsInTheBook.ChordDisk.chordDisk_produces_isSphereMap
#print axioms ProofsInTheBook.ChordDisk.chordDisk_produces_freshFaceCount
#print axioms ProofsInTheBook.ChordDisk.chordSideJordanData_of_disk
#print axioms ProofsInTheBook.ChordDisk.side₁_isSphereMap_of_disk
#print axioms ProofsInTheBook.ChordDisk.side₁_freshFaceCount_of_disk
#print axioms ProofsInTheBook.ChordDisk.side₂_isSphereMap_of_disk
#print axioms ProofsInTheBook.ChordDisk.sphereWitness_isSphereMap_via_disk
#print axioms ProofsInTheBook.ChordDisk.witness_freshFaceCount_via_disk
#print axioms ProofsInTheBook.ChordDisk.witness_chordSideJordanData_via_disk
#print axioms ProofsInTheBook.ChordDisk.chordDisk_side_genus0_certificate
