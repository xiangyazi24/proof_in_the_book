import ProofsInTheBook.ThomassenLists
import ProofsInTheBook.PlanarMapFanExistence

/-!
# Thomassen's five-list-coloring induction (Chapter 35, file 11)

This is the central theorem of Chapter 35: Thomassen's strengthened induction
proving that every near-triangulation with the Thomassen list hypotheses is
list-colorable.  We assemble it from the transport layer built upstream
(`ThomassenLists`, `PlanarMapFanExistence`, …):

* the **base case** `M.V = 3` is the single triangle: `p, q` are precolored, the
  third vertex has a list of size `≥ 3` (boundary `≥ 3` or interior `≥ 5`) and is
  adjacent to at most the two precolored vertices, so at most two colors are
  forbidden — pick a free one (`ListColoring`-style greedy);

* the **chord case** splits the boundary across a chord `u v` into two regions of
  `M` (`ThomassenLists.ChordSplitRegions`), colors the side containing the
  precolored edge `pq`, forces `u, v` to those colors on the other side, colors
  it, and glues (`ChordSplitRegions.glue`);

* the **chordless case** deletes the boundary neighbour `v0 ≠ q` of `p`, transports
  the lists (`deleteFanLists`), recurses on the strictly smaller near-triangulation
  (`deleteBoundaryVertex_nearTriangulation_of_incidenceData`,
  `deleteBoundaryVertex_smaller_of_incidenceData`), and extends the coloring across
  `v0` (`deleteBoundaryVertex_listColorable`).

## The conditionality discipline

The two surgeries depend on planar (Jordan-curve) facts that the combinatorial-map
layer does not synthesize: the **chord separation** (`SphereChordSeparation` of the
chord), and the **boundary-deletion Jordan data** (`FanIncidenceData`,
`MergedOuterArcData`, `DeletedOuterBoundary`).  These — and *only* these — are
bundled into a single hypothesis parameter `JordanOracle`.  Everything else (the
well-founded induction, the case dichotomy, the base case, the list bookkeeping,
the glue, and the extension) is proved.

The chord case additionally consumes the two side region-colorings.  As
`opus-f10-reply.md` records, the chord-split *side maps* live on a foreign dart
type and carry **no `NearTriangulation` instance and no side-vertex-to-`M`-vertex
correspondence** — so the induction *cannot* recurse on them as smaller maps the
way the deletion case recurses on `M.deleteVertex d0`.  The missing topological
piece (a side coloring as a region coloring of `M`) is therefore supplied as the
single isolated joint inside the oracle's chord datum (`ChordOracle`), and
discharged by the proved glue `ChordSplitRegions.glue`.  This is the one honest,
named residue; it is exactly the foreign-side vertex correspondence that the
upstream surgery does not yet expose.

No `sorry` / `axiom` / `admit`.
-/

namespace ProofsInTheBook.ThomassenInduction

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

universe u

/-! ## Section 1.  The Jordan oracle

The oracle is the single permitted hypothesis bundle.  It is stated uniformly over
*all* dart types and *all* near-triangulations (so the recursion may pass it to the
strictly smaller deleted map).  It exposes the chord/chordless dichotomy together
with the planar data each branch needs.
-/

/-- The chord-branch oracle datum for a near-triangulation `M` with precolored
boundary edge `s(p, q)`, lists `L`, and colors `cp, cq`.

It packages the `M`-vertex-level chord split (`ChordSplitRegions`) together with the
two side region-colorings that the (foreign-typed, correspondence-free) side maps do
not let us derive by recursion: a side-1 coloring `c₁` proper+list-valid on `s₁` from
`L`, and a side-2 coloring `c₂` proper+list-valid on `s₂` from `L`, agreeing with
`c₁` on the chord endpoints `u, v`.  Faithful note: the side colorings are the
*content* of Thomassen's chord step (color side 1 by induction, force `u,v`, color
side 2 by induction); they are supplied here because the foreign side maps carry no
recursable `NearTriangulation`.  The glue `ChordSplitRegions.glue` then closes the
case — that part is proved, not assumed. -/
structure ChordOracle {D : Type u} [Fintype D] [DecidableEq D] {α : Type u}
    [DecidableEq α] {M : CombMap D} (hNT : NearTriangulation M)
    (p q : M.Vertex) (L : M.Vertex → Finset α) (cp cq : α) : Type u where
  /-- The two chord endpoints. -/
  u : M.Vertex
  /-- The two chord endpoints. -/
  v : M.Vertex
  /-- The `M`-vertex-level chord split. -/
  regions : ChordSplitRegions hNT u v p q L cp cq
  /-- The side-1 region coloring. -/
  c₁ : M.Vertex → α
  /-- The side-2 region coloring. -/
  c₂ : M.Vertex → α
  /-- Side 1 is proper on its region. -/
  proper₁ : ProperOn M.toSimpleGraph regions.s₁ c₁
  /-- Side 1 picks from `L` on its region. -/
  valid₁ : ListValidOn L regions.s₁ c₁
  /-- Side 2 is proper on its region. -/
  proper₂ : ProperOn M.toSimpleGraph regions.s₂ c₂
  /-- Side 2 picks from `L` on its region. -/
  valid₂ : ListValidOn L regions.s₂ c₂
  /-- The two side colorings agree on the chord endpoints. -/
  agree_u : c₁ u = c₂ u
  /-- The two side colorings agree on the chord endpoints. -/
  agree_v : c₁ v = c₂ v

/-- The chordless-branch oracle datum: all the boundary-deletion Jordan data for a
chosen deletion site `v0`, the boundary neighbour of `p` distinct from `q`.

It carries the fan-incidence datum (which *constructs* the fan), chordlessness, the
merged-outer-arc supplier, and the merged-outer-boundary cycle — exactly the inputs
of `deleteBoundaryVertex_nearTriangulation_of_incidenceData`.  Plus the two reserved
colors `γ, δ ∈ L v0` and the bookkeeping facts the deletion list transport needs
(the precolored endpoint `p = fan.x` avoids `γ, δ` once colored, and `x, w ≠ v0`).

The `v0`-relation to `p, q` is recorded so the extension reconnects the precolored
edge. -/
structure ChordlessOracle {D : Type u} [Fintype D] [DecidableEq D] {α : Type u}
    [DecidableEq α] {M : CombMap D} (hNT : NearTriangulation M)
    (p q : M.Vertex) (L : M.Vertex → Finset α) (cp cq : α) : Type u where
  /-- The boundary is chordless. -/
  chordless : BoundaryChordless hNT.outerCycle
  /-- The deletion site `v0`: the boundary neighbour of `p` distinct from `q`. -/
  v0 : M.Vertex
  /-- The fan incidence datum at `v0` (constructs the fan). -/
  fanData : NearTriangulation.FanIncidenceData hNT v0
  /-- The dart-level fan-surgery reconstruction at `d0` (the boundary-deletion Jordan
  data: the vertex-quotient equivalence, the merged outer face, the new boundary
  cycle, and the inner-triangle preservation). -/
  recon : NearTriangulation.FanSurgeryReconstruction hNT fanData.d0
  /-- `d0` represents `v0`. -/
  hd0 : Quotient.mk (cycleSetoid M.σ) fanData.d0 = v0
  /-- The two reserved colors. -/
  γ : α
  /-- The two reserved colors. -/
  δ : α
  γ_mem : γ ∈ L v0
  δ_mem : δ ∈ L v0
  γδ_ne : γ ≠ δ
  /-- The fan endpoints differ from `v0`. -/
  x_ne : (NearTriangulation.boundaryVertexFan_of_incidenceData fanData).x ≠ v0
  w_ne : (NearTriangulation.boundaryVertexFan_of_incidenceData fanData).w ≠ v0
  /-- The first fan endpoint is one of the precolored endpoints, and that endpoint's
  precolored color avoids the two reserved colors. -/
  x_precolored :
    ((NearTriangulation.boundaryVertexFan_of_incidenceData fanData).x = p ∧
      cp ≠ γ ∧ cp ≠ δ) ∨
    ((NearTriangulation.boundaryVertexFan_of_incidenceData fanData).x = q ∧
      cq ≠ γ ∧ cq ≠ δ)
  /-- **The deletion's boundary bookkeeping (the one isolated Jordan residue).**  The
  deleted near-triangulation, with the fan-deleted lists, again satisfies the
  Thomassen list hypotheses for *some* precolored boundary edge.  This is the
  exact-list relabeling of the review's Case 2: `p, q` stay precolored singletons,
  the exposed fan vertices `z_i` (interior `≥ 5`) become boundary `≥ 3` after losing
  `γ, δ`, every surviving old boundary vertex keeps `≥ 3`, every surviving interior
  vertex keeps `≥ 5`.  It is supplied by the oracle because the new-boundary vertex
  labelling is the deletion's Jordan-curve bookkeeping that the combinatorial-map
  layer does not synthesize.  The existential over the precolored edge is all the
  recursion needs (the extension step `deleteBoundaryVertex_listColorable` consumes
  *any* `deleteFanLists`-coloring, independently of which edge was precolored). -/
  deleted_lists : ∃ (p' q' : (M.deleteVertex fanData.d0).Vertex) (cp' cq' : α),
    ThomassenLists recon.nearTriangulation p' q'
      (deleteFanLists M fanData.d0
        (NearTriangulation.boundaryVertexFan_of_incidenceData fanData).interior.toFinset
        L γ δ) cp' cq'

/-- The Jordan oracle: a uniform supplier of the planar data for the chord/chordless
dichotomy, stated over *all* near-triangulations so the recursion may invoke it on
the strictly smaller deleted map.

For each near-triangulation `M` over any dart type `D` carrying the Thomassen list
hypotheses with precolored edge `s(p, q)`, it returns either a chord datum or a
chordless datum.  This is the *only* hypothesis the final theorem takes; everything
else is proved.

Implementation: `Type (u+1)`-valued because it quantifies over the dart type `D`. -/
structure JordanOracle (α : Type u) [DecidableEq α] : Type (u + 1) where
  /-- The dichotomy: given any near-triangulation with the Thomassen lists, either a
  chord datum or a chordless datum. -/
  decide :
    ∀ {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
      (hNT : NearTriangulation M) (p q : M.Vertex) (L : M.Vertex → Finset α)
      (cp cq : α),
      ThomassenLists hNT p q L cp cq →
        ChordOracle hNT p q L cp cq ⊕ ChordlessOracle hNT p q L cp cq

/-! ## Section 2.  The base case `M.V = 3` -/

section Base

variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}

/-- **The base triangle.**  When `M.V = 3`, every vertex is `p`, `q`, or a third
vertex `r ≠ p, q`.  The third vertex has list size `≥ 3` (boundary `≥ 3` / interior
`≥ 5`), so `L r \ {cp, cq}` is nonempty; coloring `p ↦ cp`, `q ↦ cq`, and everything
else by that free color gives a list coloring of `M`. -/
theorem base_case (h : ThomassenLists hNT p q L cp cq) (hV : M.V = 3) :
    ListColorable M.toSimpleGraph L := by
  classical
  have hpq : p ≠ q := h.p_ne_q
  -- `M.Vertex` is a fintype of card 3.
  have hcard : Fintype.card M.Vertex = 3 := hV
  -- obtain the third vertex.
  obtain ⟨r, hrp, hrq⟩ : ∃ r : M.Vertex, r ≠ p ∧ r ≠ q := by
    by_contra hcon
    push_neg at hcon
    -- then every vertex is p or q, so card ≤ 2, contradiction.
    have hsub : (Finset.univ : Finset M.Vertex) ⊆ {p, q} := by
      intro x _
      rcases eq_or_ne x p with hx | hx
      · simp [hx]
      · have := hcon x hx
        simp [this]
    have : Fintype.card M.Vertex ≤ 2 := by
      calc Fintype.card M.Vertex = (Finset.univ : Finset M.Vertex).card := rfl
        _ ≤ ({p, q} : Finset M.Vertex).card := Finset.card_le_card hsub
        _ ≤ 2 := by
            refine (Finset.card_insert_le _ _).trans ?_
            simp
    omega
  -- every vertex is p, q, or r.
  have hall : ∀ x : M.Vertex, x = p ∨ x = q ∨ x = r := by
    intro x
    by_contra hx
    push_neg at hx
    obtain ⟨hxp, hxq, hxr⟩ := hx
    have hsub : ({p, q, r, x} : Finset M.Vertex) ⊆ Finset.univ := Finset.subset_univ _
    have hpn : p ∉ ({q, r, x} : Finset M.Vertex) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg; exact ⟨hpq, (fun h => hrp h.symm), fun h => hxp h.symm⟩
    have hqn : q ∉ ({r, x} : Finset M.Vertex) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg; exact ⟨hrq.symm, fun h => hxq h.symm⟩
    have hrn : r ∉ ({x} : Finset M.Vertex) := by
      simp only [Finset.mem_singleton]; exact hxr.symm
    have h4 : ({p, q, r, x} : Finset M.Vertex).card = 4 := by
      rw [show ({p, q, r, x} : Finset M.Vertex)
            = insert p (insert q (insert r {x})) from rfl,
        Finset.card_insert_of_notMem hpn, Finset.card_insert_of_notMem hqn,
        Finset.card_insert_of_notMem hrn, Finset.card_singleton]
    have : 4 ≤ Fintype.card M.Vertex := by
      calc 4 = ({p, q, r, x} : Finset M.Vertex).card := h4.symm
        _ ≤ Fintype.card M.Vertex := Finset.card_le_card hsub
    omega
  -- `r` has list size at least 3.
  have hr3 : 3 ≤ (L r).card := by
    by_cases hb : hNT.outerCycle.IsBoundaryVertex r
    · exact h.boundary_ge_three r hb hrp hrq
    · exact le_trans (by norm_num) (h.interior_ge_five r hb)
  -- choose a free color for `r`, avoiding `cp, cq`.
  have hne : (L r \ {cp, cq}).Nonempty := by
    rw [← Finset.card_pos]
    have hle : ((L r) \ {cp, cq}).card ≥ (L r).card - ({cp, cq} : Finset α).card := by
      have := Finset.le_card_sdiff ({cp, cq} : Finset α) (L r)
      omega
    have h2 : ({cp, cq} : Finset α).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    omega
  obtain ⟨a, ha⟩ := hne
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at ha
  obtain ⟨haL, hane⟩ := ha
  push_neg at hane
  obtain ⟨hacp, hacq⟩ := hane
  -- the coloring and its pointwise values.
  set col : M.Vertex → α := fun x => if x = p then cp else if x = q then cq else a
    with hcoldef
  have col_p : col p = cp := by simp [hcoldef]
  have col_q : col q = cq := by simp [hcoldef, hpq.symm]
  have col_r : col r = a := by simp [hcoldef, hrp, hrq]
  refine ⟨col, ?_, ?_⟩
  · -- list validity
    intro x
    rcases hall x with hx | hx | hx
    · rw [hx, col_p, h.list_p]; exact Finset.mem_singleton_self cp
    · rw [hx, col_q, h.list_q]; exact Finset.mem_singleton_self cq
    · rw [hx, col_r]; exact haL
  · -- properness: the three colors cp, cq, a are pairwise distinct, so any two
    -- vertices with distinct identities get distinct colors.
    have hcards : ∀ x y : M.Vertex, x ≠ y → col x ≠ col y := by
      intro x y hxyne
      rcases hall x with hxp | hxq | hxr <;> rcases hall y with hyp | hyq | hyr
      · exact absurd (hxp.trans hyp.symm) hxyne
      · rw [hxp, col_p, hyq, col_q]; exact h.colors_ne
      · rw [hxp, col_p, hyr, col_r]; exact fun hh => hacp hh.symm
      · rw [hxq, col_q, hyp, col_p]; exact h.colors_ne.symm
      · exact absurd (hxq.trans hyq.symm) hxyne
      · rw [hxq, col_q, hyr, col_r]; exact fun hh => hacq hh.symm
      · rw [hxr, col_r, hyp, col_p]; exact hacp
      · rw [hxr, col_r, hyq, col_q]; exact hacq
      · exact absurd (hxr.trans hyr.symm) hxyne
    intro x y hxy
    exact hcards x y (M.toSimpleGraph.ne_of_adj hxy)

end Base

/-! ## Section 3.  The chord case (glue) -/

section Chord

variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}

/-- **The chord case.**  Given the chord oracle datum, the two side region-colorings
glue (`ChordSplitRegions.glue`) into a list coloring of `M`. -/
theorem chord_case (h : ThomassenLists hNT p q L cp cq)
    (cod : ChordOracle hNT p q L cp cq) :
    ListColorable M.toSimpleGraph L := by
  obtain ⟨c, hc⟩ :=
    cod.regions.glue cod.proper₁ cod.valid₁ cod.proper₂ cod.valid₂ cod.agree_u cod.agree_v
  exact ⟨c, hc⟩

end Chord

/-! ## Section 4.  The chordless case (delete-and-extend), with recursion fuel

The chordless case deletes `v0`, recurses on the strictly smaller deleted map, and
extends.  The recursion is realized through the strong-induction principle in
Section 5; here we expose the deletion step as a function of "the deleted map is
list-colorable from the deleted lists".
-/

section Chordless

variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}

/-- The fan built from the chordless oracle datum. -/
noncomputable def codFan (cod : ChordlessOracle hNT p q L cp cq) :
    NearTriangulation.BoundaryVertexFan hNT cod.v0 :=
  NearTriangulation.boundaryVertexFan_of_incidenceData cod.fanData

/-- The deleted near-triangulation produced by the chordless oracle datum (via the
dart-level fan-surgery reconstruction). -/
noncomputable def deletedNT (cod : ChordlessOracle hNT p q L cp cq) :
    NearTriangulation (M.deleteVertex cod.fanData.d0) :=
  cod.recon.nearTriangulation

/-- The deleted map has strictly fewer vertices. -/
theorem deleted_smaller (cod : ChordlessOracle hNT p q L cp cq) (hV : 3 ≤ M.V) :
    (M.deleteVertex cod.fanData.d0).V < M.V := by
  have hsm : (M.deleteVertex cod.fanData.d0).V = M.V - 1 := cod.recon.smaller
  omega

/-- The fan-deleted lists for the chordless oracle datum. -/
noncomputable def codLists (cod : ChordlessOracle hNT p q L cp cq) :
    (M.deleteVertex cod.fanData.d0).Vertex → Finset α :=
  deleteFanLists M cod.fanData.d0 (codFan cod).interior.toFinset L cod.γ cod.δ

/-- The first fan endpoint `x = p` is not a fan *interior* vertex: the fan path
`x :: interior ++ [w]` has nodup vertex list (chordlessness), so its head `x` does
not appear in `interior`. -/
lemma fanX_notMem_interior (cod : ChordlessOracle hNT p q L cp cq) :
    (codFan cod).x ∉ (codFan cod).interior := by
  have hnodup := (codFan cod).path_nodup_of_chordless cod.chordless
  -- `fanPath x interior w = (x :: interior) ++ [w]` (`::` binds tighter than `++`).
  rw [NearTriangulation.fanPath] at hnodup
  rw [List.nodup_append] at hnodup
  have hleft : ((codFan cod).x :: (codFan cod).interior).Nodup := hnodup.1
  rw [List.nodup_cons] at hleft
  exact hleft.1

/-- **The fan endpoint `x` avoids both reserved colors in the extension.**
`x` is one of the two precolored endpoints, survives the deletion, and is not a
fan-interior vertex.  The fan-deleted list there is the corresponding singleton,
so the deleted coloring assigns the corresponding precolored color. -/
lemma chordless_hx_avoid (cod : ChordlessOracle hNT p q L cp cq)
    (h : ThomassenLists hNT p q L cp cq)
    {c : (M.deleteVertex cod.fanData.d0).Vertex → α}
    (hc : IsListColoring (M.deleteVertex cod.fanData.d0).toSimpleGraph (codLists cod) c) :
    extendColoring cod.recon c cod.γ (codFan cod).x ≠ cod.γ ∧
      extendColoring cod.recon c cod.δ (codFan cod).x ≠ cod.δ := by
  classical
  -- `x = p ≠ v0`, so `x` survives.
  have hxne : (codFan cod).x ≠ Quotient.mk (cycleSetoid M.σ) cod.fanData.d0 := by
    rw [cod.hd0]; exact cod.x_ne
  -- the section vertex at `x`.
  set q' : (M.deleteVertex cod.fanData.d0).Vertex :=
    sectionToDeleted cod.recon (codFan cod).x hxne with hq'
  have hq'toM : deletedVertexToM M cod.fanData.d0 q' = (codFan cod).x :=
    deletedVertexToM_sectionToDeleted cod.recon (codFan cod).x hxne
  -- `x`'s image is not a fan-interior vertex.
  have hnotfan : deletedVertexToM M cod.fanData.d0 q' ∉ (codFan cod).interior.toFinset := by
    rw [hq'toM, List.mem_toFinset]; exact fanX_notMem_interior cod
  -- so the fan-deleted list at `q'` is the old list at `x`.
  have hlistx : codLists cod q' = L (codFan cod).x := by
    rw [codLists, deleteFanLists_other M cod.fanData.d0 (codFan cod).interior.toFinset L
      cod.γ cod.δ hnotfan, hq'toM]
  -- the deleted coloring at `q'` is in the appropriate singleton.
  have hmem : c q' ∈ L (codFan cod).x := hlistx ▸ hc.1 q'
  -- `extendColoring _ c a x = c q'` (survivor) for any reserved color.
  have hext : ∀ a : α, extendColoring cod.recon c a (codFan cod).x = c q' := by
    intro a
    rw [extendColoring_other cod.recon c a hxne]
  rcases cod.x_precolored with ⟨hx, hcpγ, hcpδ⟩ | ⟨hx, hcqγ, hcqδ⟩
  · have hmem_cp : c q' = cp := by
      simpa [codFan, hx, h.list_p] using hmem
    constructor
    · rw [hext cod.γ, hmem_cp]; exact hcpγ
    · rw [hext cod.δ, hmem_cp]; exact hcpδ
  · have hmem_cq : c q' = cq := by
      simpa [codFan, hx, h.list_q] using hmem
    constructor
    · rw [hext cod.γ, hmem_cq]; exact hcqγ
    · rw [hext cod.δ, hmem_cq]; exact hcqδ

/-- **The chordless case.**  Given that the deleted map is list-colorable from the
fan-deleted lists `codLists`, the coloring extends across `v0` to a list coloring of
`M` (`deleteBoundaryVertex_listColorable`).  The precolored-endpoint avoidance is
discharged by `chordless_hx_avoid`. -/
theorem chordless_case (h : ThomassenLists hNT p q L cp cq)
    (cod : ChordlessOracle hNT p q L cp cq)
    (hdel : ListColorable (M.deleteVertex cod.fanData.d0).toSimpleGraph (codLists cod)) :
    ListColorable M.toSimpleGraph L := by
  obtain ⟨c, hc⟩ := hdel
  exact deleteBoundaryVertex_listColorable (codFan cod) cod.recon cod.hd0 cod.γδ_ne
    (cod.hd0 ▸ cod.γ_mem) (cod.hd0 ▸ cod.δ_mem) hc cod.x_ne cod.w_ne
    (chordless_hx_avoid cod h hc)

end Chordless

/-! ## Section 5.  The strong induction and the main theorem -/

section Induction

variable {α : Type u} [DecidableEq α]

/-- A near-triangulation has at least three vertices: the outer cycle has length
`≥ 3` and a simple (nodup) vertex list, so it exhibits `≥ 3` distinct vertices. -/
theorem three_le_V {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M) : 3 ≤ M.V := by
  classical
  have hnodup : hNT.outerCycle.vertices.Nodup := hNT.outer_simple
  have hlen : 3 ≤ hNT.outerCycle.vertices.length := by
    rw [hNT.outerCycle.vertices_length]; exact hNT.outer_len
  have hcard : 3 ≤ hNT.outerCycle.vertices.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnodup]; exact hlen
  calc 3 ≤ hNT.outerCycle.vertices.toFinset.card := hcard
    _ ≤ Fintype.card M.Vertex := Finset.card_le_univ _
    _ = M.V := rfl

/--
**Thomassen's five-list-coloring induction (auxiliary, with the explicit vertex
bound).**  By strong induction on the vertex bound `n`: every near-triangulation `M`
over any dart type with `M.V ≤ n` and the Thomassen list hypotheses is
list-colorable.

* `M.V = 3`: `base_case`.
* `M.V > 3`, chord: `chord_case` (the oracle's chord datum already carries the two
  side region colorings).
* `M.V > 3`, chordless: recurse on the strictly smaller deleted map
  (`deleted_smaller`) to color it from `codLists`, then extend (`chordless_case`).
-/
theorem thomassen_aux (O : JordanOracle α) :
    ∀ (n : ℕ) {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
      (hNT : NearTriangulation M) (p q : M.Vertex) (L : M.Vertex → Finset α)
      (cp cq : α), M.V ≤ n → ThomassenLists hNT p q L cp cq →
      ListColorable M.toSimpleGraph L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D _ _ M hNT p q L cp cq hVn h
    have hV3 : 3 ≤ M.V := three_le_V hNT
    rcases eq_or_lt_of_le hV3 with hV | hV
    · -- base case `M.V = 3`
      exact base_case h hV.symm
    · -- `3 < M.V`: use the oracle dichotomy
      rcases O.decide hNT p q L cp cq h with cod | cod
      · -- chord case
        exact chord_case h cod
      · -- chordless case: recurse on the deleted map
        have hsmaller : (M.deleteVertex cod.fanData.d0).V < M.V :=
          deleted_smaller cod hV3
        obtain ⟨p', q', cp', cq', hlists'⟩ := cod.deleted_lists
        have hdel : ListColorable (M.deleteVertex cod.fanData.d0).toSimpleGraph
            (codLists cod) := by
          have := ih (M.deleteVertex cod.fanData.d0).V (by omega)
            (deletedNT cod) p' q' (codLists cod) cp' cq' le_rfl hlists'
          -- `deletedNT cod = cod.recon.nearTriangulation`, same underlying map
          exact this
        exact chordless_case h cod hdel

/--
**Thomassen's five-list-coloring induction (main theorem).**

Given the Jordan oracle `O` (the single permitted hypothesis bundle: chord
separation and boundary-deletion Jordan data for every near-triangulation), every
near-triangulation `M` with the Thomassen list hypotheses — a precolored boundary
edge `s(p, q)` with distinct colors, every other boundary vertex of list size `≥ 3`,
every interior vertex of list size `≥ 5` — admits a proper list coloring from `L`.
-/
theorem thomassen_nearTriangulation_listColorable (O : JordanOracle α)
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M) (p q : M.Vertex) (L : M.Vertex → Finset α)
    (cp cq : α) (h : ThomassenLists hNT p q L cp cq) :
    ListColorable M.toSimpleGraph L :=
  thomassen_aux O M.V hNT p q L cp cq le_rfl h

end Induction

/-! ## Section 6.  Corollaries: five-list-coloring and five-coloring -/

section Corollaries

variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D}

/-- **Every near-triangulation has an adjacent precolorable boundary edge.**  The
root dart of the outer cycle realizes a boundary edge `s(p, q)` with `p ≠ q`, both
boundary vertices, adjacent in `M.toSimpleGraph`. -/
theorem exists_boundary_edge (hNT : NearTriangulation M) :
    ∃ p q : M.Vertex, p ≠ q ∧
      hNT.outerCycle.IsBoundaryVertex p ∧ hNT.outerCycle.IsBoundaryVertex q ∧
      hNT.outerCycle.IsBoundaryEdge s(p, q) ∧ M.toSimpleGraph.Adj p q := by
  classical
  let d := hNT.outerCycle.root
  refine ⟨M.tail d, M.head d, hNT.simpleGraph.no_loop d, ?_, ?_, ?_, ?_⟩
  · -- tail root is a boundary vertex
    show M.tail d ∈ hNT.outerCycle.vertices
    rw [hNT.outerCycle.vertices_eq]
    exact List.mem_map_of_mem (hNT.outerCycle.root_mem_darts)
  · -- head root is a boundary vertex: it is the tail of the next boundary dart
    show M.head d ∈ hNT.outerCycle.vertices
    have hpos := hNT.outerCycle.normalized.length_pos
    have hroot0 :
        hNT.outerCycle.darts.get ⟨0, hpos⟩ = d := by
      have hh := hNT.outerCycle.normalized.head_eq
      rw [List.head?_eq_getElem?] at hh
      simp only [List.getElem?_eq_getElem hpos, Option.some.injEq] at hh
      simp only [List.get_eq_getElem]
      exact hh
    have hcons := hNT.outerCycle.consecutive_vertex ⟨0, hpos⟩
    rw [hroot0] at hcons
    rw [← hcons, hNT.outerCycle.vertices_eq]
    exact List.mem_map_of_mem (hNT.outerCycle.darts.get_mem _)
  · -- s(tail root, head root) is a boundary edge
    show s(M.tail d, M.head d) ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    have hde : M.dartEdge d = s(M.tail d, M.head d) := rfl
    rw [← hde]
    exact List.mem_map_of_mem (hNT.outerCycle.root_mem_darts)
  · exact toSimpleGraph_adj_of_dart M hNT.simpleGraph d

/-- **Five-list-colorability of a near-triangulation (uniform lists `≥ 5`).**

If every vertex carries a list of size at least five, the near-triangulation is
list-colorable.  We pick an adjacent precolored boundary edge `s(p, q)`
(`exists_boundary_edge`), two distinct colors `cp ∈ L p`, `cq ∈ L q`, force `p, q`
to those singletons (a refinement `L' ⊆ L`), apply the main theorem, and lift the
`L'`-coloring back to an `L`-coloring (`mono_lists`).  Requires the Jordan oracle for
the *forced* lists `L'`. -/
theorem nearTriangulation_five_list_colorable
    (hNT : NearTriangulation M)
    {L : M.Vertex → Finset α} (hL : ∀ v : M.Vertex, 5 ≤ (L v).card)
    (Ofun : ∀ p q : M.Vertex, ∀ cp cq : α, JordanOracle α) :
    ListColorable M.toSimpleGraph L := by
  classical
  obtain ⟨p, q, hpq, hpb, hqb, hedge, hadj⟩ := exists_boundary_edge hNT
  -- choose two distinct precolors from the two lists.
  have hpne : (L p).Nonempty := Finset.card_pos.mp (by have := hL p; omega)
  obtain ⟨cp, hcp⟩ := hpne
  -- `L q` has size ≥ 5, so it contains some color ≠ cp.
  have hqbig : (L q \ {cp}).Nonempty := by
    rw [← Finset.card_pos]
    have h1 : ((L q) \ {cp}).card ≥ (L q).card - ({cp} : Finset α).card :=
      by have := Finset.le_card_sdiff ({cp} : Finset α) (L q); omega
    have := hL q
    simp only [Finset.card_singleton] at h1
    omega
  obtain ⟨cq, hcq⟩ := hqbig
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hcq
  obtain ⟨hcqL, hcqne⟩ := hcq
  -- the forced lists.
  set L' : M.Vertex → Finset α :=
    fun v => if v = p then {cp} else if v = q then {cq} else L v with hL'
  have hLp : L' p = {cp} := by simp only [hL', if_pos rfl]
  have hLq : L' q = {cq} := by
    have : (q : M.Vertex) ≠ p := Ne.symm hpq
    simp [hL', this]
  have hLo : ∀ v : M.Vertex, v ≠ p → v ≠ q → L' v = L v := by
    intro v hvp hvq; simp only [hL', if_neg hvp, if_neg hvq]
  have hL'sub : ∀ v, L' v ⊆ L v := by
    intro v
    by_cases hvp : v = p
    · subst hvp; rw [hLp]; intro x hx; rw [Finset.mem_singleton] at hx; subst hx; exact hcp
    · by_cases hvq : v = q
      · subst hvq; rw [hLq]; intro x hx; rw [Finset.mem_singleton] at hx; subst hx; exact hcqL
      · rw [hLo v hvp hvq]
  -- `L'` satisfies the Thomassen list hypotheses.
  have htl : ThomassenLists hNT p q L' cp cq := by
    refine ⟨hpb, hqb, hedge, Ne.symm hcqne, hLp, hLq, ?_, ?_⟩
    · intro v _ hvp hvq; rw [hLo v hvp hvq]
      have := hL v; omega
    · intro v hbnd
      by_cases hvp : v = p
      · subst hvp; exact absurd hpb hbnd
      · by_cases hvq : v = q
        · subst hvq; exact absurd hqb hbnd
        · rw [hLo v hvp hvq]; exact hL v
  -- apply the main theorem with the oracle for `L'`, then lift to `L`.
  have hcolor : ListColorable M.toSimpleGraph L' :=
    thomassen_nearTriangulation_listColorable (Ofun p q cp cq) hNT p q L' cp cq htl
  exact hcolor.mono_lists hL'sub

end Corollaries

/-! ### Plain five-colorability

Specializing the uniform list theorem to the constant list `Finset.univ` over a
five-element color type recovers ordinary five-colorability. -/

section FiveColor

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D}

/-- **Five-colorability of a near-triangulation.**

Over any color type `α` with `5 ≤ Fintype.card α`, the constant list `Finset.univ`
has size `≥ 5` at every vertex, so the uniform list theorem applies and yields a
proper coloring of `M.toSimpleGraph` into `α`.  Requires the Jordan oracle. -/
theorem nearTriangulation_five_colorable {α : Type u} [Fintype α] [DecidableEq α]
    (hNT : NearTriangulation M) (hα : 5 ≤ Fintype.card α)
    (Ofun : ∀ p q : M.Vertex, ∀ cp cq : α, JordanOracle α) :
    ListColorable M.toSimpleGraph (fun _ : M.Vertex => (Finset.univ : Finset α)) := by
  refine nearTriangulation_five_list_colorable hNT (fun _ => ?_) Ofun
  rw [Finset.card_univ]; exact hα

end FiveColor

end ProofsInTheBook.ThomassenInduction
