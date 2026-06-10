import ProofsInTheBook.ChordSigmaContig

/-!
# The canonical chord-cap anchors of side 1, and their basic equations
  (Chapter 35 — the `ContiguousInterval` campaign: anchor bricks)

`ChordSigmaContig.lean` established the HONEST geometric correction of the chord-side
discharge: the literal `keptPhi`-bigon wrap `keptPhi d₂ = d₁` is **FALSE** (`keptPhi d₂`
sits at vertex `u = tail dart`, `d₁ = M.φ dart` at `v = head dart`, and `u ≠ v`), so the
residue is the *post-splice* `tracePhi` 2-cycle (`SideTracePhiTwoCycle`), which DOES cross
`u ↔ v` through the spliced fresh chord edge.  It left the anchors `a₀, a₁` of
`data.sideMap₁` as FREE parameters.

This file pins those anchors at the **canonical** chord-cap choice prescribed by the
`ContiguousInterval` design round, expressed in the repo's actual names:

  `a₀ = (sideSigma₁).symm (keptPhi d₂)`,   `a₁ = (sideSigma₁).symm d₁`,

where `d₁ = face₁Dart₁ = ⟨M.φ dart, _⟩`, `d₂ = face₁Dart₂ = ⟨M.φ² dart, _⟩`, and
`keptPhi = keptPhi (sideAlpha₁ hsep) sideSigma₁ = sideSigma₁ ∘ sideAlpha₁` is the
pre-splice kept-side face permutation.  Note this canonical choice does NOT presuppose
the false wrap `keptPhi d₂ = d₁`; it uses the value `keptPhi d₂` and the dart `d₁` as
genuinely distinct kept darts (distinct exactly because `keptPhi d₂ ≠ d₁`).

## What is proved here (all UNCONDITIONAL, no `sorry`/`axiom`/`admit`/`native_decide`)

**Brick 1 — the canonical anchors and their `sideSigma₁`-images.**

* `side₁Anchor₀`, `side₁Anchor₁` — the canonical anchors (defeq via `Equiv.symm`).
* `sideSigma₁_side₁Anchor₀ : sideSigma₁ a₀ = keptPhi d₂`,
  `sideSigma₁_side₁Anchor₁ : sideSigma₁ a₁ = d₁` — definitional, via
  `Equiv.apply_symm_apply`.
* `side₁Anchors_ne : a₀ ≠ a₁` — from `keptPhi d₂ ≠ d₁`
  (`ChordSigmaContig.keptPhi_face₁Dart₂_ne_face₁Dart₁`, the proven geometric fact) and the
  injectivity of `(sideSigma₁).symm`.

**Brick 2 — the anchor-incidence fact for the canonical anchors.**

* `side₁AnchorsShareFace_canonical : Side₁AnchorsShareFace data hsep a₀ a₁` — i.e.
  `keptPhi.SameCycle (keptPhi d₂) d₁`.  Both `keptPhi d₂` and `d₁` lie on the shared
  pre-splice boundary face (the `face₁` `keptPhi`-orbit): `keptPhi d₁ = d₂`
  (`keptPhi_face₁Dart₁`) and `keptPhi d₂ = keptPhi (keptPhi d₂)`'s predecessor place the
  three darts `d₁, d₂, keptPhi d₂` in one `keptPhi`-cycle.  This is exactly the fact-2
  hypothesis `ChordDisk.Side₁AnchorsShareFace` consumes (e.g. in
  `ChordSideNT.side₁_sphere_unconditional`), now SUPPLIED for the canonical anchors.

**Brick 3 — the post-splice `tracePhi` 2-cycle for the canonical anchors.**

The two `SideTracePhiTwoCycle` "splice-swap" fields are definitional consequences of the
anchor equations and `tracePhi = swap (ρ a₀) (ρ a₁) ∘ keptPhi`
(`ChordAnchorInst.tracePhi_eq_swap_keptPhi`):

* `side₁Anchors_trace21 : tracePhi … a₀ a₁ d₂ = d₁` — the easy direction:
  `tracePhi d₂ = swap (keptPhi d₂) d₁ (keptPhi d₂) = d₁` by `Equiv.swap_apply_left`.
* `side₁Anchors_trace12 : tracePhi … a₀ a₁ d₁ = d₂` — `tracePhi d₁ = swap (keptPhi d₂) d₁
  (keptPhi d₁) = swap (keptPhi d₂) d₁ d₂ = d₂`, using `keptPhi d₁ = d₂`
  (`keptPhi_face₁Dart₁`), `d₂ ≠ keptPhi d₂` (`keptPhi_face₁Dart₂_ne_self`), and `d₂ ≠ d₁`
  (`face₁Dart_distinct`).
* `side₁Anchors_traceTwoCycle` — the pair, the full 2-cycle on the canonical anchors.

The full `SideTracePhiTwoCycle` structure additionally carries the `one_fresh` indicator
and a chosen rep face `f` with `hkf`; those two are the splice-orbit-reduction data the
`tracePhi` algebra alone does not pin (they depend on `dartFace`/`SameCycle` of the fresh
darts on the assembled `sideMap₁`), so they remain inputs.  We deliver the two splice-swap
equations as standalone lemmas and a packaging constructor
`sideTracePhiTwoCycle_canonical` that takes `f`, `hkf`, `one_fresh` and supplies
`trace12`/`trace21` from here.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ZinanCh35SideAnchors

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordAnchorInst
open ProofsInTheBook.ChordSigmaContig

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## Section 1.  The canonical anchors and their `sideSigma₁`-images

`a₀ = (sideSigma₁).symm (keptPhi d₂)`, `a₁ = (sideSigma₁).symm d₁`: the kept darts whose
`sideSigma₁`-successors are, respectively, `keptPhi d₂` (the pre-splice face value at `u`)
and `d₁ = M.φ dart` (the kept `face₁` dart at `v`).  Their `sideSigma₁`-images are then
those two darts by `Equiv.apply_symm_apply`. -/

/-- **The canonical side-1 anchor `a₀`** — the kept dart whose `sideSigma₁`-successor is
`keptPhi d₂`. -/
noncomputable def side₁Anchor₀ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    {d : D // d ∉ data.keptDel₁} :=
  (data.sideSigma₁).symm
    (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data))

/-- **The canonical side-1 anchor `a₁`** — the kept dart whose `sideSigma₁`-successor is
`d₁ = M.φ dart`. -/
noncomputable def side₁Anchor₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    {d : D // d ∉ data.keptDel₁} :=
  (data.sideSigma₁).symm (face₁Dart₁ data)

/-- **`sideSigma₁ a₀ = keptPhi d₂`** (definitional, `Equiv.apply_symm_apply`). -/
@[simp] theorem sideSigma₁_side₁Anchor₀ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideSigma₁ (side₁Anchor₀ data hsep)
      = keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) := by
  rw [side₁Anchor₀, Equiv.apply_symm_apply]

/-- **`sideSigma₁ a₁ = d₁`** (definitional, `Equiv.apply_symm_apply`). -/
@[simp] theorem sideSigma₁_side₁Anchor₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideSigma₁ (side₁Anchor₁ data hsep) = face₁Dart₁ data := by
  rw [side₁Anchor₁, Equiv.apply_symm_apply]

/-- **The canonical anchors are distinct.**  If `a₀ = a₁` then their `sideSigma₁`-images
agree, i.e. `keptPhi d₂ = d₁` — refuted by the proven geometric fact
`ChordSigmaContig.keptPhi_face₁Dart₂_ne_face₁Dart₁` (the false-wrap correction). -/
theorem side₁Anchors_ne (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    side₁Anchor₀ data hsep ≠ side₁Anchor₁ data hsep := by
  intro h
  -- equal anchors ⇒ equal `sideSigma₁`-images ⇒ `keptPhi d₂ = d₁`, contradiction.
  have himg : data.sideSigma₁ (side₁Anchor₀ data hsep)
      = data.sideSigma₁ (side₁Anchor₁ data hsep) := by rw [h]
  rw [sideSigma₁_side₁Anchor₀, sideSigma₁_side₁Anchor₁] at himg
  exact keptPhi_face₁Dart₂_ne_face₁Dart₁ data hsep himg

/-! ## Section 2.  The anchor-incidence fact for the canonical anchors

`Side₁AnchorsShareFace data hsep a₀ a₁` unfolds to
`keptPhi.SameCycle (sideSigma₁ a₀) (sideSigma₁ a₁) = keptPhi.SameCycle (keptPhi d₂) d₁`.
The three darts `d₁, d₂, keptPhi d₂` lie in one `keptPhi`-cycle: `keptPhi d₁ = d₂`
(`keptPhi_face₁Dart₁`) gives `SameCycle d₁ d₂`, and `SameCycle d₂ (keptPhi d₂)` is one
forward step; symmetry/transitivity assemble `SameCycle (keptPhi d₂) d₁`. -/

/-- **`d₁` and `keptPhi d₂` lie on a common `keptPhi`-cycle.**  `keptPhi.SameCycle d₁
(keptPhi d₂)`: `keptPhi d₁ = d₂` (`keptPhi_face₁Dart₁`), and `keptPhi d₂` is one further
forward step from `d₂`, so `d₁ → d₂ → keptPhi d₂` is a `keptPhi`-walk. -/
theorem keptPhi_sameCycle_d₁_keptPhi_d₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁).SameCycle
      (face₁Dart₁ data)
      (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data)) := by
  -- peel the outer `keptPhi` on the right: reduce to `SameCycle d₁ d₂`.
  rw [Equiv.Perm.sameCycle_apply_right]
  -- `SameCycle d₁ d₂` from `keptPhi d₁ = d₂`.
  rw [← keptPhi_face₁Dart₁ data hsep]
  exact (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))

/-- **The anchor-incidence fact for the canonical anchors** (`Side₁AnchorsShareFace`).  The
canonical anchors' `sideSigma₁`-successors `keptPhi d₂` and `d₁` lie on a common kept
(`keptPhi`) face — the shared pre-splice boundary face (the `face₁` orbit).  This is the
proven fact-2 instance the chord-side disk/sphere machinery
(`ChordDisk.side₁_isSphereMap_of_disk`, `ChordSideNT.side₁_sphere_unconditional`) consumes,
now SUPPLIED for the canonical anchors. -/
theorem side₁AnchorsShareFace_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ProofsInTheBook.ChordDisk.Side₁AnchorsShareFace data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) := by
  -- unfold to `keptPhi.SameCycle (sideSigma₁ a₀) (sideSigma₁ a₁)`,
  show (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁).SameCycle
    (data.sideSigma₁ (side₁Anchor₀ data hsep)) (data.sideSigma₁ (side₁Anchor₁ data hsep))
  rw [sideSigma₁_side₁Anchor₀, sideSigma₁_side₁Anchor₁]
  -- i.e. `SameCycle (keptPhi d₂) d₁`, the symmetric of `keptPhi_sameCycle_d₁_keptPhi_d₂`.
  exact (keptPhi_sameCycle_d₁_keptPhi_d₂ data hsep).symm

/-! ## Section 3.  The post-splice `tracePhi` 2-cycle for the canonical anchors

`tracePhi a₀ a₁ = swap (ρ a₀) (ρ a₁) ∘ keptPhi` (`tracePhi_eq_swap_keptPhi`), with
`ρ a₀ = keptPhi d₂`, `ρ a₁ = d₁`.  The two splice-swap equations follow:

* `tracePhi d₂ = swap (keptPhi d₂) d₁ (keptPhi d₂) = d₁` (`Equiv.swap_apply_left`);
* `tracePhi d₁ = swap (keptPhi d₂) d₁ (keptPhi d₁) = swap (keptPhi d₂) d₁ d₂ = d₂`, using
  `keptPhi d₁ = d₂`, `d₂ ≠ keptPhi d₂`, `d₂ ≠ d₁`. -/

/-- **The easy splice-swap direction `tracePhi d₂ = d₁`** for the canonical anchors.  Since
`ρ a₀ = keptPhi d₂`, the swap `swap (keptPhi d₂) (ρ a₁)` sends `keptPhi d₂ ↦ ρ a₁ = d₁`. -/
theorem side₁Anchors_trace21 (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (face₁Dart₂ data)
      = face₁Dart₁ data := by
  rw [tracePhi_eq_swap_keptPhi, sideSigma₁_side₁Anchor₀, sideSigma₁_side₁Anchor₁]
  -- `swap (keptPhi d₂) d₁ (keptPhi d₂) = d₁`.
  exact Equiv.swap_apply_left _ _

/-- **The other splice-swap direction `tracePhi d₁ = d₂`** for the canonical anchors.
`tracePhi d₁ = swap (keptPhi d₂) d₁ (keptPhi d₁)`; `keptPhi d₁ = d₂`
(`keptPhi_face₁Dart₁`), and `d₂ ∉ {keptPhi d₂, d₁}` (`keptPhi_face₁Dart₂_ne_self`,
`face₁Dart_distinct`), so the swap fixes `d₂`. -/
theorem side₁Anchors_trace12 (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (face₁Dart₁ data)
      = face₁Dart₂ data := by
  rw [tracePhi_eq_swap_keptPhi, sideSigma₁_side₁Anchor₀, sideSigma₁_side₁Anchor₁,
    keptPhi_face₁Dart₁ data hsep]
  -- `swap (keptPhi d₂) d₁ d₂ = d₂` since `d₂ ≠ keptPhi d₂` and `d₂ ≠ d₁`.
  refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
  · -- `d₂ ≠ keptPhi d₂` (symm of `keptPhi_face₁Dart₂_ne_self`).
    exact (keptPhi_face₁Dart₂_ne_self data hsep).symm
  · -- `d₂ ≠ d₁` (symm of `face₁Dart_distinct`).
    exact (face₁Dart_distinct data).symm

/-- **The post-splice `tracePhi` 2-cycle on the kept `face₁` darts**, for the canonical
anchors: `d₁ ↦ d₂` and `d₂ ↦ d₁`.  This is the genuine `SideTracePhiTwoCycle` orbit
content (crossing `u ↔ v` through the spliced fresh chord edge), now SUPPLIED for the
canonical anchors — the post-splice replacement of the false `keptPhi`-wrap. -/
theorem side₁Anchors_traceTwoCycle (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (face₁Dart₁ data)
        = face₁Dart₂ data ∧
      tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (face₁Dart₂ data)
        = face₁Dart₁ data :=
  ⟨side₁Anchors_trace12 data hsep, side₁Anchors_trace21 data hsep⟩

/-! ## Section 4.  Packaging into `SideTracePhiTwoCycle`

The `trace12`/`trace21` fields are now CANONICAL (supplied above); the remaining fields of
`ChordSigmaContig.SideTracePhiTwoCycle` are the chosen rep face `f`, its membership
witness `hkf`, and the `one_fresh` indicator — splice-orbit data on the assembled
`sideMap₁` that the anchor algebra alone does not pin.  This constructor takes those three
and supplies the 2-cycle from here, yielding the full post-splice residue for the canonical
anchors. -/

/-- **The canonical-anchor `SideTracePhiTwoCycle`**, with `trace12`/`trace21` SUPPLIED.  The
remaining inputs `f`, `hkf`, `one_fresh` are the splice-orbit rep/indicator data (depending
on `sideMap₁`'s `dartFace`/`SameCycle`), not pinnable from the `tracePhi` algebra alone;
given them, the canonical anchors yield the full post-splice 2-cycle residue, which threads
into `ChordSigmaContig.correctAnchorTwoCycle_ofTrace → … → ContiguousInterval`. -/
noncomputable def sideTracePhiTwoCycle_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (f : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).Face)
    (hkf : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data)) = f)
    (one_fresh :
      ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
              (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep)) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
              (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) then 1 else 0)) = 1) :
    SideTracePhiTwoCycle data hsep :=
  SideTracePhiTwoCycle.mk' data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
    (side₁Anchors_ne data hsep) f
    (side₁Anchors_trace12 data hsep) (side₁Anchors_trace21 data hsep) hkf one_fresh

end ProofsInTheBook.ZinanCh35SideAnchors

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35SideAnchors.sideSigma₁_side₁Anchor₀
#print axioms ProofsInTheBook.ZinanCh35SideAnchors.sideSigma₁_side₁Anchor₁
#print axioms ProofsInTheBook.ZinanCh35SideAnchors.side₁Anchors_ne
#print axioms ProofsInTheBook.ZinanCh35SideAnchors.keptPhi_sameCycle_d₁_keptPhi_d₂
#print axioms ProofsInTheBook.ZinanCh35SideAnchors.side₁AnchorsShareFace_canonical
#print axioms ProofsInTheBook.ZinanCh35SideAnchors.side₁Anchors_trace21
#print axioms ProofsInTheBook.ZinanCh35SideAnchors.side₁Anchors_trace12
#print axioms ProofsInTheBook.ZinanCh35SideAnchors.side₁Anchors_traceTwoCycle
#print axioms ProofsInTheBook.ZinanCh35SideAnchors.sideTracePhiTwoCycle_canonical
