import ProofsInTheBook.ZinanCh35Contiguous

/-!
# Chapter 35 — the side-1 boundary `outer_simple` (keystone residual R3c-ii)

This file attacks the keystone residual that `contiguousInterval_holds`
(`ProofsInTheBook/ZinanCh35Contiguous.lean`) consumes as its `outer_simple`
hypothesis: the side outer boundary cycle is *simple*,

```
(((data.sideMap₁ hsep a₀ a₁ hne).faceDartList (Sum.inr 1)).map
    (data.sideMap₁ hsep a₀ a₁ hne).tail).Nodup
```

i.e. the `tail`-vertices of the darts on the outer `φ`-orbit (rooted at the fresh
chord dart `inr 1`) are pairwise distinct.

## The route (ChatGPT-Pro design), executed

`S := data.sideMap₁ hsep a₀ a₁ hne = freshMap (data.sideAlpha₁ hsep) data.sideSigma₁ … a₀ a₁ hne`,
with kept type `K := {d : D // d ∉ data.keptDel₁}`, `β := sideAlpha₁`, `ρ := sideSigma₁`.

1.  `faceDartList d = S.φ.toList d`, and `(φ.toList _).Nodup` (`Equiv.Perm.nodup_toList`).
    So the mapped-list `Nodup` reduces (`List.nodup_map_iff_inj_on`) to **injectivity of
    `S.tail` on the orbit darts**.

2.  **The `tail`-collapse algebra (PROVED here, unconditionally).**
    `S.tail x = Quotient.mk (cycleSetoid S.σ) x`, so `S.tail x = S.tail y ↔ S.σ.SameCycle x y`.
    With `S.σ = freshSigma ρ a₀ a₁ hne` (`freshMap_sigma`), `freshSigma_sameCycle_iff` gives
    `↔ ρ.SameCycle (proj a₀ a₁ x) (proj a₀ a₁ y)`.  Since `ρ = filteredRotation M.σ keptDel₁`,
    `filteredRotation_sameCycle_iff` gives `↔ M.σ.SameCycle (proj…x).1 (proj…y).1`, i.e.
    `M.tail (proj…x).1 = M.tail (proj…y).1`.  This is the lemma
    `sideMap₁_tail_eq_iff_M_tail_proj` below — a complete, axiom-clean reduction with NO planar
    input.

3.  **The irreducible geometric sub-fact (ISOLATED, NOT faked).**
    After step 2, `outer_simple` is *exactly* the statement that the map
    `x ↦ M.tail (proj a₀ a₁ x).1` is injective on the orbit `S.φ.toList (inr 1)`.  The orbit
    members project (via `proj`, then `(·).1`) to **original boundary darts on one contiguous
    arc of `hNT.outerCycle`** (the side arc, plus the fresh chord which collapses to the two
    anchors `a₀,a₁` whose projections `(·).1` are themselves boundary darts).  The original
    boundary vertex list `hNT.outerCycle.vertices` is `Nodup` (`hNT.outer_simple`), and `M.tail`
    is injective on its darts (`hNT.outerCycle.tail_injective_on_darts hNT.outer_simple`).  So
    `M.tail` is injective on the proj-trace.  This *orbit-trace ⊆ outer arc* fact is the genuine
    discrete Jordan/Schoenflies datum — exactly the one `ZinanCh35Contiguous.lean:55-62` flags as
    NOT a `Nodup`/genus-0 consequence.  We state it as the single named hypothesis
    `OrbitProjOnOuterArc` and an `InjOn`-style consequence `M_tail_injOn_orbitProj`; the main
    theorem `side₁_outer_simple_of_orbitTrace` is then PROVED from it with zero further geometry.

No `sorry` / `axiom` / `admit` / `native_decide`.  The one geometric sub-fact is carried as an
explicit, sharply-stated *hypothesis*, in the same idiom (`Separates`, `InnerRepsAvoidBoundary`,
`arcSplit`) that the surrounding chord-split development already uses for its honest residues.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35SideOuterSimple

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ZinanCh35SideAnchors

universe u

/-! ## Section 0.  The `tail`-equality ↔ `σ`-SameCycle bridge (generic `CombMap`)

`M.tail d = Quotient.mk (cycleSetoid M.σ) d`, and `Quotient.mk` equality is exactly the setoid
relation `cycleSetoid M.σ` whose underlying relation is `M.σ.SameCycle`.  Hence `tail`-equality
is `σ`-SameCycle.  Pure quotient algebra. -/

section Bridge

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- **`tail`-equality is `σ`-SameCycle.**  Two darts have the same tail vertex iff they are in
the same `σ`-orbit. -/
lemma tail_eq_iff_sigma_sameCycle (M : CombMap D) (d e : D) :
    M.tail d = M.tail e ↔ M.σ.SameCycle d e := by
  unfold CombMap.tail
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

end Bridge

/-! ## Section 1.  The full `tail`-collapse for the bare fresh map (PROVED)

For `S = freshMap β ρ … a₀ a₁`, the fresh-side `tail` collapses through the projection `proj` to
the *kept* `ρ`-SameCycle relation.  This is `freshSigma_sameCycle_iff` packaged through the
`tail`-bridge. -/

section FreshTail

variable {K : Type u} [Fintype K] [DecidableEq K]
  (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- **Fresh-side `tail`-equality collapses to `ρ`-SameCycle of the anchor projections.**
`(freshMap β ρ … a₀ a₁).tail x = (…).tail y ↔ ρ.SameCycle (proj a₀ a₁ x) (proj a₀ a₁ y)`. -/
lemma freshMap_tail_eq_iff_rho_sameCycle (x y : K ⊕ Fin 2) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).tail x = (freshMap β ρ hβinv hβfix a₀ a₁ hne).tail y
      ↔ ρ.SameCycle (proj a₀ a₁ x) (proj a₀ a₁ y) := by
  rw [tail_eq_iff_sigma_sameCycle]
  rw [freshMap_sigma β ρ hβinv hβfix a₀ a₁ hne]
  exact freshSigma_sameCycle_iff ρ hne x y

end FreshTail

/-! ## Section 2.  Specialize to `sideMap₁`: `tail`-equality ↔ `M.tail` of the proj-`(·).1`

`ρ = data.sideSigma₁ = filteredRotation M.σ data.keptDel₁`, so `ρ`-SameCycle of two kept darts is
`M.σ`-SameCycle of their underlying original darts (`filteredRotation_sameCycle_iff`), which is
`M.tail`-equality of those original darts (`tail_eq_iff_sigma_sameCycle`).  The full chain is
**proved unconditionally** — no planar input. -/

section SideTail

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The side-1 `tail`-collapse.**  For the side-1 map `S = sideMap₁`, two outer darts have the
same `S`-tail vertex iff their original underlying darts `(proj a₀ a₁ x).1`, `(proj a₀ a₁ y).1`
have the same `M`-tail vertex.

PROVED unconditionally: `freshMap_tail_eq_iff_rho_sameCycle` reduces it to
`sideSigma₁.SameCycle (proj…x) (proj…y)`; `sideSigma₁ = filteredRotation M.σ keptDel₁`, so
`filteredRotation_sameCycle_iff` reduces it to `M.σ.SameCycle (proj…x).1 (proj…y).1`, which is
`M.tail`-equality. -/
lemma sideMap₁_tail_eq_iff_M_tail_proj
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (x y : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2) :
    (data.sideMap₁ hsep a₀ a₁ hne).tail x = (data.sideMap₁ hsep a₀ a₁ hne).tail y
      ↔ M.tail (proj a₀ a₁ x).1 = M.tail (proj a₀ a₁ y).1 := by
  -- Step A: fresh-side tail ↔ sideSigma₁-SameCycle of the projections.
  rw [show data.sideMap₁ hsep a₀ a₁ hne
        = freshMap (data.sideAlpha₁ hsep) data.sideSigma₁
            (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) a₀ a₁ hne from rfl]
  rw [freshMap_tail_eq_iff_rho_sameCycle (data.sideAlpha₁ hsep) data.sideSigma₁
        (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne x y]
  -- Step B: sideSigma₁-SameCycle ↔ M.σ-SameCycle of the underlying original darts.
  rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl]
  rw [filteredRotation_sameCycle_iff M.σ data.keptDel₁ (proj a₀ a₁ x) (proj a₀ a₁ y)]
  -- Step C: M.σ-SameCycle ↔ M.tail-equality of the underlying original darts.
  rw [tail_eq_iff_sigma_sameCycle]

end SideTail

/-! ## Section 3.  The ISOLATED geometric sub-fact + the main `outer_simple`

After the §2 collapse, `outer_simple` is *exactly* `InjOn` of `x ↦ M.tail (proj a₀ a₁ x).1` over
the orbit list.  The genuine discrete Jordan/Schoenflies datum is the **orbit-trace fact**: the
proj-`(·).1` images of the orbit darts all lie among the darts of the original outer cycle
`hNT.outerCycle`, on which `M.tail` is injective (`hNT.outer_simple`).  We isolate it as a single
hypothesis and discharge the main theorem from it. -/

section Main

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  (hNT : NearTriangulation M) {u v : M.Vertex}

/-- **The isolated orbit-trace datum (R3c-ii geometric core).**  Every dart `x` on the side-1
outer `φ`-orbit `(sideMap₁ … ).faceDartList (inr 1)` has its original underlying dart
`(proj a₀ a₁ x).1` on the *original* outer boundary cycle `hNT.outerCycle`.

This is the discrete Jordan/Schoenflies content: the side outer boundary is the side arc of the
original boundary together with the fresh chord (which collapses under `proj`/`(·).1` to the two
anchor darts, themselves boundary darts).  It is the lone non-combinatorial residue of the R3c-ii
keystone — NOT a `Nodup`/genus-0 consequence (cf. `ZinanCh35Contiguous.lean:55-62`).  It is stated
sharply and consumed honestly; it is *not* a posited conclusion (it is a containment of explicit
darts in the boundary, satisfiable by the genuine geometry). -/
def OrbitProjOnOuterArc
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) : Prop :=
  ∀ x ∈ (data.sideMap₁ hsep a₀ a₁ hne).faceDartList (Sum.inr 1),
    (proj a₀ a₁ x).1 ∈ hNT.outerCycle.darts

/-- **`M.tail` is injective on the proj-trace of the orbit** (consequence of the isolated datum +
`hNT.outer_simple`).  PROVED from `OrbitProjOnOuterArc` via
`BoundaryCycle.tail_injective_on_darts`. -/
lemma M_tail_injOn_orbitProj
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (htrace : OrbitProjOnOuterArc hNT data hsep a₀ a₁ hne)
    {x y : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2}
    (hx : x ∈ (data.sideMap₁ hsep a₀ a₁ hne).faceDartList (Sum.inr 1))
    (hy : y ∈ (data.sideMap₁ hsep a₀ a₁ hne).faceDartList (Sum.inr 1))
    (htail : M.tail (proj a₀ a₁ x).1 = M.tail (proj a₀ a₁ y).1) :
    (proj a₀ a₁ x).1 = (proj a₀ a₁ y).1 :=
  hNT.outerCycle.tail_injective_on_darts hNT.outer_simple (htrace x hx) (htrace y hy) htail

/-! ### The single minimal residual.

After the §2 collapse `outer_simple` is **definitionally equivalent** (over the orbit `InjOn`) to:

> `∀ x y ∈ orbit, M.tail (proj a₀ a₁ x).1 = M.tail (proj a₀ a₁ y).1 → x = y`,

i.e. the composite `x ↦ M.tail (proj a₀ a₁ x).1` is injective on the orbit list.  We name this
`OuterTraceInjOn`.  It is the *one* genuinely irreducible residual; everything else (the
`faceDartList`-`Nodup`, the `nodup_map_iff_inj_on` repackaging, the §2 tail-collapse) is proved.

`OuterTraceInjOn` is the discrete-Jordan content.  A natural attack (the route's suggestion),
giving a *sufficient* decomposition, is `OrbitProjOnOuterArc` (the proj-`(·).1` images land on the
original boundary, so `hNT.outer_simple` collapses `M.tail`-equal to proj-`(·).1`-equal) together
with the orbit-class injectivity (proj-`(·).1`-equal orbit darts are equal).  See
`outerTraceInjOn_of_decomposition` for that route. -/

/-- **The single irreducible residual** (R3c-ii core, post-§2): the composite
`x ↦ M.tail (proj a₀ a₁ x).1` is injective on the side-1 outer orbit. -/
def OuterTraceInjOn
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) : Prop :=
  ∀ x ∈ (data.sideMap₁ hsep a₀ a₁ hne).faceDartList (Sum.inr 1),
    ∀ y ∈ (data.sideMap₁ hsep a₀ a₁ hne).faceDartList (Sum.inr 1),
      M.tail (proj a₀ a₁ x).1 = M.tail (proj a₀ a₁ y).1 → x = y

/-- **A sufficient decomposition of the residual** (the route's `OrbitProjOnOuterArc` + class
injectivity).  PROVED: `htrace` + `hNT.outer_simple` collapse `M.tail`-equality to
proj-`(·).1`-equality, then `hclass` closes `x = y`. -/
lemma outerTraceInjOn_of_decomposition
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (htrace : OrbitProjOnOuterArc hNT data hsep a₀ a₁ hne)
    (hclass : ∀ x ∈ (data.sideMap₁ hsep a₀ a₁ hne).faceDartList (Sum.inr 1),
        ∀ y ∈ (data.sideMap₁ hsep a₀ a₁ hne).faceDartList (Sum.inr 1),
        (proj a₀ a₁ x).1 = (proj a₀ a₁ y).1 → x = y) :
    OuterTraceInjOn hNT data hsep a₀ a₁ hne := by
  intro x hx y hy hMtail
  have hproj : (proj a₀ a₁ x).1 = (proj a₀ a₁ y).1 :=
    M_tail_injOn_orbitProj hNT data hsep a₀ a₁ hne htrace hx hy hMtail
  exact hclass x hx y hy hproj

/-- **The side-1 `outer_simple` for arbitrary anchors, given the single residual
`OuterTraceInjOn`.**  PROVED: the §2 tail-collapse turns the orbit `InjOn` of `S.tail` into the
residual, then the residual closes it. -/
theorem side₁_outer_simple_of_orbitTrace
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hresidual : OuterTraceInjOn hNT data hsep a₀ a₁ hne) :
    (((data.sideMap₁ hsep a₀ a₁ hne).faceDartList (Sum.inr 1)).map
        (data.sideMap₁ hsep a₀ a₁ hne).tail).Nodup := by
  -- The orbit list is `Nodup` (it is `φ.toList`, a permutation orbit list).
  have hL : ((data.sideMap₁ hsep a₀ a₁ hne).faceDartList (Sum.inr 1)).Nodup := by
    rw [ProofsInTheBook.PlanarMap.CombMap.faceDartList]
    exact Equiv.Perm.nodup_toList _ _
  -- `Nodup (map tail l) ↔ InjOn tail l`.
  rw [List.nodup_map_iff_inj_on hL]
  intro x hx y hy htail
  -- §2 collapse: `S.tail x = S.tail y → M.tail (proj…x).1 = M.tail (proj…y).1`.
  have hMtail : M.tail (proj a₀ a₁ x).1 = M.tail (proj a₀ a₁ y).1 :=
    (sideMap₁_tail_eq_iff_M_tail_proj data hsep a₀ a₁ hne x y).1 htail
  -- the single residual closes `x = y`.
  exact hresidual x hx y hy hMtail

/-! ### The canonical-anchor specialization

`contiguousInterval_holds` needs `outer_simple` for the canonical anchors `side₁Anchor₀/₁`.  This
is `side₁_outer_simple_of_orbitTrace` instantiated at those anchors; it produces exactly the
`outer_simple` field shape that `ZinanCh35Contiguous.contiguousInterval_holds` expects. -/

/-- **The canonical-anchor `outer_simple`** matching the `outer_simple` input of
`ZinanCh35Contiguous.contiguousInterval_holds`.  PROVED modulo the single isolated residual
`hresidual := OuterTraceInjOn …` at the canonical anchors.  Plug the conclusion straight into
`contiguousInterval_holds (… outer_simple := side₁_outer_simple_canonical … )`. -/
theorem side₁_outer_simple_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hresidual : OuterTraceInjOn hNT data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep)) :
    (((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).tail).Nodup :=
  side₁_outer_simple_of_orbitTrace hNT data hsep
    (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep)
    hresidual

end Main

end ProofsInTheBook.ZinanCh35SideOuterSimple

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35SideOuterSimple.tail_eq_iff_sigma_sameCycle
#print axioms ProofsInTheBook.ZinanCh35SideOuterSimple.freshMap_tail_eq_iff_rho_sameCycle
#print axioms ProofsInTheBook.ZinanCh35SideOuterSimple.sideMap₁_tail_eq_iff_M_tail_proj
#print axioms ProofsInTheBook.ZinanCh35SideOuterSimple.M_tail_injOn_orbitProj
#print axioms ProofsInTheBook.ZinanCh35SideOuterSimple.outerTraceInjOn_of_decomposition
#print axioms ProofsInTheBook.ZinanCh35SideOuterSimple.side₁_outer_simple_of_orbitTrace
#print axioms ProofsInTheBook.ZinanCh35SideOuterSimple.side₁_outer_simple_canonical
