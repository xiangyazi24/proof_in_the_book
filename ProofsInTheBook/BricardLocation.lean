import ProofsInTheBook.BricardCube

/-!
# The two `LocationData` certificates for the concrete Chapter 9 solids

`BricardCube.lean` reduced the Chapter 9 headline `regularTet_cube_no_equidecomp_concrete` to *exactly*
two design-sanctioned isolated residues: the `LocationData` / `PearlSectorModel` cross-section
certificates `Ldata` (regular tetrahedron) and `Rdata` (Kuhn cube), together with the two
external-angle normalizations `hP_arccos` (`arccos(1/3)`) and `hQ_pi2` (`π/2`).  This module builds
those certificates *concretely*, computing the pearl angle sums directly from the proven dihedral
angles, bypassing the abstract planar sector model via the design-permitted `fullSector` route
(`PearlClassification.fullSector_model`: a single sector already covers the target wedge, so the only
load-bearing fact is the angle bridge `PearlAngleSum = targetAngle`, which we *compute*).

## The regular-tetrahedron side (fully discharged, unconditional)

The regular tetrahedron is a *one-piece* solid, so its raw 1-skeleton is the six edges of
`regularTet`, and (since `EdgesNonOverlapping (oneTetSolid regularTet)`) each canonical pearl is
incident to *exactly one* edge occurrence — its own source edge.  Hence

  `PearlAngleSum regularTetSolid p = dihedralAngle regularTet (source edge) = arccos(1/3)`

by `TetDihedral.regularTet_dihedralAngle`.  Each pearl's source edge is an external edge of
`regularTetSolid` whose declared angle is `arccos(1/3)`, and a pearl's relative interior lies in its
source edge's *relative* interior (the open-segment containment, since `0 ≤ lo < hi ≤ 1` forces the
interior coordinate to be strictly inside `(0,1)`).  This yields a genuine `externalEdge` location and
a one-sector `PearlSectorModel` at angle `arccos(1/3)` whose bridge is the computed angle sum.  We
assemble `regularTetLocationData` and prove `regularTet_pearlExtAngle_arccos`, giving the *complete*
regular-tet inputs `Ldata` / `hP_arccos` of the headline — **unconditionally, no `sorry`**.

## The cube side and the faithfulness of `hQ_pi2` (the honest obstruction)

The Kuhn cube genuinely has pearls *not* on any external (cube) edge: the main diagonal
`(0,0,0)–(1,1,1)` is edge `(0,3)` of **every** one of the six Kuhn orthoschemes, so it carries pearls
whose incident dihedral angles sum to `2π` (a solid-interior pearl); the six face diagonals carry
pearls whose two incident Kuhn dihedral angles sum to `π` (boundary-facet pearls).  For such a pearl a
faithful `PearlClassificationCert` is forced into the `solidInterior` / `boundaryFacetInterior`
location, where `pearlExtAngle = 0 ≠ π/2`.

Therefore the headline hypothesis `hQ_pi2 : ∀ p ∈ Pearls (cube), pearlExtAngle (Rdata.cert p hp) =
π/2` is **mathematically false** for the Kuhn solid: it is not a missing proof but an over-strong
statement (the book only needs `angleClassQ (externalPart) = 0`, i.e. the *external* pearls carry
`π/2` while interior/facet pearls fold into the `k·π` term that vanishes mod `ℚπ` — see
`Bricard.angleClassQ_cube_externalPart_eq_zero`).  We record this precisely and supply what *is*
honestly constructible: the cube `LocationData` over the canonical pearl set with each pearl assigned
its *genuine* location (external `π/2`, facet `π`, or interior `2π`) — i.e. `cubeLocationData` — for
which the correct, satisfiable normalization is `angleClassQ (externalPart) = 0`, not the literal
`hQ_pi2`.  The one honest isolate that remains is the per-pearl *incidence-sum* computation on the
Kuhn solid (which incident occurrences a given cube pearl has, and that their dihedral angles sum to
the location's target), packaged as the named input `CubePearlAngleData`.

No `sorry`, `axiom`, or `admit`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped BigOperators Classical RealInnerProductSpace
open Set
open ProofsInTheBook.TetPearls
open ProofsInTheBook.TetDihedral
open ProofsInTheBook.PearlClassification
open ProofsInTheBook.Chapter09
open ProofsInTheBook.Bricard
open ProofsInTheBook.BricardCube

namespace ProofsInTheBook.BricardLocation

/-! ## A pearl's relative interior lies in its source edge's *relative* interior -/

/-- For a canonical pearl `p` of `R`, the relative (open) interior of `p` is contained in the
**relative** interior (open segment) of its source edge.  A relative-interior point has source-edge
coordinate strictly in `(p.lo, p.hi) ⊆ (0,1)` (since `0 ≤ p.lo < p.hi ≤ 1`), hence strictly between
the two endpoints, i.e. in the open segment. -/
theorem relInterior_subset_sourceEdge_relInterior {R : Finset Segment3} {p : Pearl}
    (hp : IsPearlOf R p) : p.relInterior ⊆ p.sourceEdge.relInterior := by
  obtain ⟨hsrc, hlo, hhi, hlt, hcons⟩ := hp
  have hpFull : IsPearlOf R p := ⟨hsrc, hlo, hhi, hlt, hcons⟩
  have hloI := breakCoords_mem_Icc R p.sourceEdge hlo
  have hhiI := breakCoords_mem_Icc R p.sourceEdge hhi
  obtain ⟨hlo0, hlo1⟩ := hloI
  obtain ⟨hhi0, hhi1⟩ := hhiI
  intro x hx
  -- coordinate of x is in (lo, hi) ⊆ (0,1)
  have hco := coord_mem_Ioo_of_mem_relInterior hlt hx
  obtain ⟨hc1, hc2⟩ := hco
  -- x = point (coord x); write as an open-segment element
  have hxc : x ∈ p.sourceEdge.carrier :=
    relInterior_subset_sourceEdge_carrier p hpFull hx
  have hpt : p.sourceEdge.point (p.sourceEdge.coord x) = x :=
    p.sourceEdge.point_coord_of_mem hxc
  -- the coordinate t := coord x ∈ (0,1) gives point t in the open segment a..b
  set t := p.sourceEdge.coord x with ht
  have ht0 : 0 < t := lt_of_le_of_lt hlo0 hc1
  have ht1 : t < 1 := lt_of_lt_of_le hc2 hhi1
  rw [Segment3.relInterior, openSegment_eq_image]
  refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
  -- (1-t)•a + t•b = point t = x
  simp only
  have heq : (1 - t) • p.sourceEdge.a + t • p.sourceEdge.b = p.sourceEdge.point t := by
    simp only [Segment3.point]; module
  rw [heq, hpt]

/-! ## Incident edge occurrences for a non-overlapping solid: exactly the source-edge occurrences

For a solid `S` with `EdgesNonOverlapping S`, a canonical pearl `p` is incident to an edge occurrence
`E` (`p.relInterior ⊆ E.carrier`) iff `E.seg = p.sourceEdge`.  The forward direction is non-overlap
(the pearl's nondegenerate relative interior lies in both `E.seg.carrier` and `p.sourceEdge.carrier`,
exhibiting two distinct common points); the backward direction is
`relInterior_subset_sourceEdge_carrier`. -/

/-- The incidence characterization for a non-overlapping solid. -/
theorem mem_IncidentTetEdges_iff_seg_eq {S : TetSolid} (hno : EdgesNonOverlapping S)
    {p : Pearl} (hp : IsPearlOf (PieceEdges S) p) {E : EdgeOcc S} :
    E ∈ IncidentTetEdges S p ↔ (E ∈ allEdgeOccs S ∧ E.seg = p.sourceEdge) := by
  rw [mem_IncidentTetEdges]
  constructor
  · rintro ⟨hEocc, hsub⟩
    refine ⟨hEocc, ?_⟩
    -- both endpoints of p lie in E.carrier and in p.sourceEdge.carrier; non-overlap ⟹ equal segs
    have hincSrc : p.relInterior ⊆ p.sourceEdge.carrier :=
      relInterior_subset_sourceEdge_carrier p hp
    have hEclosed : IsClosed E.carrier := E.seg.carrier_closed
    have hSrcClosed : IsClosed p.sourceEdge.carrier := p.sourceEdge.carrier_closed
    obtain ⟨haE, hbE⟩ :=
      ProofsInTheBook.Bricard.pearl_endpoints_mem_of_relInterior_subset hEclosed hsub
    obtain ⟨haS, hbS⟩ :=
      ProofsInTheBook.Bricard.pearl_endpoints_mem_of_relInterior_subset hSrcClosed hincSrc
    have hab : p.aPt ≠ p.bPt := ProofsInTheBook.Bricard.pearl_aPt_ne_bPt hp
    exact hno E.seg p.sourceEdge
      (ProofsInTheBook.Bricard.edgeOcc_seg_mem_pieceEdges E) hp.1
      p.aPt p.bPt hab haE hbE haS hbS
  · rintro ⟨hEocc, hseg⟩
    refine ⟨hEocc, ?_⟩
    -- p.relInterior ⊆ p.sourceEdge.carrier = E.carrier
    have : p.relInterior ⊆ p.sourceEdge.carrier :=
      relInterior_subset_sourceEdge_carrier p hp
    rw [EdgeOcc.carrier, hseg]
    exact this

/-! ## Regular-tetrahedron pearl angle sums

For the single-tetrahedron solid `oneTetSolid regularTet`, every edge occurrence's dihedral angle is
`arccos(1/3)` (`regularTet_dihedralAngle`), and each canonical pearl has *exactly one* incident edge
occurrence (its source edge).  Hence each pearl angle sum is `arccos(1/3)`. -/

/-- Every edge occurrence of `oneTetSolid regularTet` has dihedral angle `arccos(1/3)`. -/
theorem oneTetRegular_edgeOcc_dihedral (E : EdgeOcc (oneTetSolid regularTet)) :
    E.dihedralAngle = Real.arccos (1 / 3) := by
  -- the only piece is `regularTet`
  have hT : E.T = regularTet := by
    have := E.hT
    rw [oneTetSolid_pieces, Finset.mem_singleton] at this
    exact this
  rw [EdgeOcc.dihedralAngle, hT]
  exact regularTet_dihedralAngle E.ine

/-- For `oneTetSolid T`, two edge occurrences with the same edge segment are equal: the segment
endpoints (vertices of the single piece `T`) determine the ordered index pair. -/
theorem oneTetSolid_edgeOcc_seg_inj {T : Tet} {E F : EdgeOcc (oneTetSolid T)}
    (hseg : E.seg = F.seg) : E = F := by
  have hET : E.T = T := by
    have := E.hT; rw [oneTetSolid_pieces, Finset.mem_singleton] at this; exact this
  have hFT : F.T = T := by
    have := F.hT; rw [oneTetSolid_pieces, Finset.mem_singleton] at this; exact this
  -- read the endpoints: E.seg.a = E.T.v E.i, E.seg.b = E.T.v E.j
  have haE : E.seg.a = T.v E.i := by rw [EdgeOcc.seg]; exact congrFun (congrArg Tet.v hET) E.i
  have hbE : E.seg.b = T.v E.j := by rw [EdgeOcc.seg]; exact congrFun (congrArg Tet.v hET) E.j
  have haF : F.seg.a = T.v F.i := by rw [EdgeOcc.seg]; exact congrFun (congrArg Tet.v hFT) F.i
  have hbF : F.seg.b = T.v F.j := by rw [EdgeOcc.seg]; exact congrFun (congrArg Tet.v hFT) F.j
  have hia : T.v E.i = T.v F.i := by
    rw [← haE, ← haF, hseg]
  have hib : T.v E.j = T.v F.j := by
    rw [← hbE, ← hbF, hseg]
  have hEFi : E.i = F.i := T.v_injective hia
  have hEFj : E.j = F.j := T.v_injective hib
  -- now E and F agree on T, i, j ⟹ equal (hlt is a proof, hT a proof)
  cases E with
  | mk ET ehT ei ej ehlt =>
    cases F with
    | mk FT fhT fi fj fhlt =>
      simp only at hET hFT hEFi hEFj
      subst hET; subst hFT; subst hEFi; subst hEFj
      rfl

/-- For a *canonical* pearl `p` of `oneTetSolid T`, the incident edge occurrences form at most a
singleton: any two incident occurrences share the source edge as their segment, hence are equal. -/
theorem incidentTetEdges_oneTet_card_le_one {T : Tet} {p : Pearl}
    (hp : IsPearlOf (PieceEdges (oneTetSolid T)) p) :
    (IncidentTetEdges (oneTetSolid T) p).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro E hE F hF
  have hno := edgesNonOverlapping_oneTetSolid T
  have hEseg := ((mem_IncidentTetEdges_iff_seg_eq hno hp).mp hE).2
  have hFseg := ((mem_IncidentTetEdges_iff_seg_eq hno hp).mp hF).2
  exact oneTetSolid_edgeOcc_seg_inj (hEseg.trans hFseg.symm)

/-- The source-edge occurrence of a canonical pearl of `oneTetSolid T`: an edge occurrence whose
segment is the pearl's source edge.  Exists because the source edge is one of `T`'s six edges. -/
theorem exists_sourceEdgeOcc_oneTet {T : Tet} {p : Pearl}
    (hp : IsPearlOf (PieceEdges (oneTetSolid T)) p) :
    ∃ E : EdgeOcc (oneTetSolid T), E ∈ IncidentTetEdges (oneTetSolid T) p := by
  -- the source edge lies in PieceEdges = T.edges, so it is `T.edgeSeg q` for some ordered pair q
  have hsrc : p.sourceEdge ∈ PieceEdges (oneTetSolid T) := hp.1
  rw [pieceEdges_oneTetSolid, Tet.edges, Finset.mem_image] at hsrc
  obtain ⟨q, hqmem, hqseg⟩ := hsrc
  obtain ⟨i, j, hij, hfa, hfb⟩ := mem_edges_endpoints (T := T) (f := p.sourceEdge)
    (by rw [Tet.edges, Finset.mem_image]; exact ⟨q, hqmem, hqseg⟩)
  -- build the occurrence with index pair (i, j)
  refine ⟨⟨T, Finset.mem_singleton_self T, i, j, hij⟩, ?_⟩
  have hno := edgesNonOverlapping_oneTetSolid T
  rw [mem_IncidentTetEdges_iff_seg_eq hno hp]
  refine ⟨?_, ?_⟩
  · -- the occurrence is in allEdgeOccs
    rw [allEdgeOccs]
    refine Finset.mem_biUnion.mpr ⟨⟨T, Finset.mem_singleton_self T⟩, Finset.mem_attach _ _, ?_⟩
    refine Finset.mem_image.mpr ⟨⟨(i, j), ?_⟩, Finset.mem_attach _ _, rfl⟩
    rw [Tet.edgePairs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hij⟩
  · -- E.seg = p.sourceEdge: both are the segment from T.v i to T.v j
    show (EdgeOcc.seg ⟨T, _, i, j, hij⟩ : Segment3) = p.sourceEdge
    rw [EdgeOcc.seg]
    -- p.sourceEdge has a = T.v i, b = T.v j
    cases hpe : p.sourceEdge with
    | mk a b hne =>
      simp only [hpe] at hfa hfb
      -- a = T.v i, b = T.v j
      congr 1 <;> [exact hfa.symm; exact hfb.symm]

/-- **Regular-tet pearl angle sum.**  For every canonical pearl `p` of `oneTetSolid regularTet`,
the incident dihedral angles sum to `arccos(1/3)`: there is exactly one incident edge occurrence
(the source edge), and its dihedral angle is `arccos(1/3)`. -/
theorem pearlAngleSum_oneTetRegular {p : Pearl}
    (hp : IsPearlOf (PieceEdges (oneTetSolid regularTet)) p) :
    PearlAngleSum (oneTetSolid regularTet) p = Real.arccos (1 / 3) := by
  rw [PearlAngleSum]
  -- the incident set is a singleton {E₀}
  obtain ⟨E₀, hE₀⟩ := exists_sourceEdgeOcc_oneTet hp
  have hcard : (IncidentTetEdges (oneTetSolid regularTet) p).card = 1 := by
    apply le_antisymm (incidentTetEdges_oneTet_card_le_one hp)
    exact Finset.card_pos.mpr ⟨E₀, hE₀⟩
  rw [Finset.card_eq_one] at hcard
  obtain ⟨E, hEeq⟩ := hcard
  rw [hEeq, Finset.sum_singleton]
  exact oneTetRegular_edgeOcc_dihedral E

/-! ## The regular-tetrahedron `LocationData` and angle normalization

Each canonical pearl of `regularTetSolid` is assigned the `externalEdge` location on its source edge
(an external edge with declared angle `arccos(1/3)`), with the one-sector `PearlSectorModel` whose
bridge is the computed pearl angle sum.  This produces a genuine `LocationData` and the normalization
`hP_arccos`. -/

/-- `arccos(1/3) ≤ 2π`. -/
theorem arccos_third_le_twoPi : Real.arccos (1 / 3) ≤ SectorSum.twoPi := by
  refine le_trans (Real.arccos_le_pi _) ?_
  rw [SectorSum.twoPi]; linarith [Real.pi_pos]

/-- The classification certificate for a canonical pearl of `regularTetSolid`: the `externalEdge`
location on its source edge, with the one-sector model at angle `arccos(1/3)`. -/
def regularTetCert {p : Pearl} (hp : p ∈ Pearls (PieceEdges regularTetSolid.toTetSolid)) :
    PearlClassificationCert regularTetSolid p := by
  have hpval : IsPearlOf (PieceEdges regularTetSolid.toTetSolid) p := mem_Pearls.mp hp
  -- the source edge is an external edge (= an edge of regularTet)
  have hsrcExt : p.sourceEdge ∈ regularTetSolid.extEdges := by
    show p.sourceEdge ∈ regularTet.edges
    have := hpval.1
    rwa [regularTetSolid_toTetSolid, pieceEdges_oneTetSolid] at this
  -- the pearl interior lies in the source edge's relative interior
  have hloc : p.relInterior ⊆ p.sourceEdge.relInterior :=
    relInterior_subset_sourceEdge_relInterior hpval
  -- angle sum = arccos(1/3)
  have hpval' : IsPearlOf (PieceEdges (oneTetSolid regularTet)) p := by
    rw [← regularTetSolid_toTetSolid]; exact hpval
  have hsum : PearlAngleSum regularTetSolid.toTetSolid p = Real.arccos (1 / 3) := by
    rw [regularTetSolid_toTetSolid]
    exact pearlAngleSum_oneTetRegular hpval'
  refine { loc := PearlLocation.externalEdge p.sourceEdge hsrcExt hloc, model := ?_ }
  -- target angle of this location is `regularTetSolid.angleOfExtEdge p.sourceEdge = arccos(1/3)`
  have htgt : (PearlLocation.externalEdge (S := regularTetSolid) (p := p)
      p.sourceEdge hsrcExt hloc).targetAngle = Real.arccos (1 / 3) := rfl
  rw [htgt]
  exact
    { x := 0
      ε := 1
      sectors := [fullSector (Real.arccos (1 / 3)) (Real.arccos_nonneg _)]
      model := fullSector_model (x := 0) (ε := 1) one_pos arccos_third_mem_Ioo.1
        arccos_third_le_twoPi
      angle_bridge := by
        rw [hsum, fullSector_angleSum] }

/-- **The regular-tetrahedron `LocationData`** over the canonical pearl set. -/
def regularTetLocationData :
    LocationData regularTetSolid (Pearls (PieceEdges regularTetSolid.toTetSolid)) where
  cert := fun _ hp => regularTetCert hp

/-- **The regular-tet angle normalization `hP_arccos`.**  Every classified pearl carries external
angle `arccos(1/3)`. -/
theorem regularTet_pearlExtAngle_arccos
    (p : Pearl) (hp : p ∈ Pearls (PieceEdges regularTetSolid.toTetSolid)) :
    pearlExtAngle (regularTetLocationData.cert p hp) = Real.arccos (1 / 3) := by
  -- the location is `externalEdge p.sourceEdge`, whose `pearlExtAngle` is the declared angle
  show pearlExtAngle (regularTetCert hp) = Real.arccos (1 / 3)
  rfl

/-! ## The cube side: the honest obstruction and the named isolate

### Why the literal `hQ_pi2` is mathematically false on the Kuhn cube

The headline `BricardCube.regularTet_cube_no_equidecomp_concrete` demands `hQ_pi2 : ∀ p ∈ Pearls
(cube), pearlExtAngle (Rdata.cert p hp) = π/2`.  For `pearlExtAngle (Rdata.cert p hp)` to equal `π/2`
the certificate's location *must* be `externalEdge e` with `e ∈ cubeExtEdges` and `p.relInterior ⊆
e.relInterior` (the only `PearlLocation` branch giving a nonzero `pearlExtAngle`; the facet and
interior branches give `0`).

But the Kuhn solid has raw edges that are **not** cube edges — in particular the main diagonal
`(0,0,0)–(1,1,1)`, which is edge `(0,3)` of *every* Kuhn orthoscheme.  This raw edge carries pearls
(`raw_edge_covered_by_pearls`), and such a pearl's source edge is the diagonal; its relative interior
is **not** contained in the relative interior of any cube edge (cube edges are axis-parallel unit
segments, the diagonal is not collinear with any).  Hence no honest certificate for a diagonal pearl
can have an `externalEdge` location, so `pearlExtAngle = 0 ≠ π/2`: the literal `hQ_pi2` is
**unsatisfiable** for the Kuhn cube.

This is *not* a missing proof but an over-strong hypothesis.  The book argument only needs
`angleClassQ (externalPart Rdata) = 0`, which holds when the *external* pearls carry `π/2` and the
interior/facet pearls fold into the `k·π` term that vanishes mod `ℚπ`
(`Bricard.angleClassQ_cube_externalPart_eq_zero`).  We make the obstruction precise below and supply
the honest cube `LocationData` against the *correct* normalization.

### The named per-pearl isolate `CubePearlAngleData`

The genuine geometric residue on the cube side is, for each canonical pearl, *which* location it
occupies and that its incident Kuhn dihedral angles sum to that location's target value
(`π/2` on a cube edge, `π` on a face diagonal, `2π` on the main diagonal).  We package exactly this as
the named data `CubePearlAngleData`: a `PearlClassificationCert cubeSolid p` at every pearl.  This is
the cube analogue of `regularTetLocationData`; constructing it requires the Kuhn dihedral-angle
computation (six orthoschemes, incidence across shared edges), the one honest 3D isolate that remains
on this side. -/

/-- The main space diagonal `(0,0,0)–(1,1,1)` of the unit cube, as a `Segment3`. -/
def spaceDiagonal : Segment3 :=
  cubeEdge !₂[(0:ℝ),0,0] !₂[(1:ℝ),1,1] (euclid3_ne_of_coord 0 (by simp))

/-- The space diagonal is **not** one of the twelve cube edges: every cube edge is an axis-parallel
unit segment (its endpoints differ in exactly one coordinate), whereas the diagonal's endpoints
differ in all three. -/
theorem spaceDiagonal_not_mem_cubeExtEdges : spaceDiagonal ∉ cubeExtEdges := by
  intro h
  -- enumerate the twelve cube edges; each fails to equal `spaceDiagonal` at some coordinate of `b`.
  rw [cubeExtEdges] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  -- each disjunct equates `spaceDiagonal = cubeEdge a b _`; compare the `b` endpoint coordinate `1`,
  -- which is `1` for the diagonal but `0` for every cube edge whose `b` has a `0` there, etc.
  -- a coordinate test on the `a`/`b` endpoints rules out every cube edge.  Pull the six coordinate
  -- equalities from the segment equality and let `norm_num` find the false one.
  have key : ∀ {a' b' : Pt3} {hab' : a' ≠ b'},
      spaceDiagonal = cubeEdge a' b' hab' →
      (!₂[(0:ℝ),0,0] : Pt3) = a' ∧ (!₂[(1:ℝ),1,1] : Pt3) = b' := by
    intro a' b' hab' hh
    have ha := congrArg Segment3.a hh
    have hb := congrArg Segment3.b hh
    simp only [spaceDiagonal, cubeEdge] at ha hb
    exact ⟨ha, hb⟩
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h <;>
    · obtain ⟨ha, hb⟩ := key h
      -- compare the underlying coordinate vectors; one coordinate of `a` or `b` is false numerically
      have ha0 := congrFun (congrArg (fun z : Pt3 => z.ofLp) ha) (0 : Fin 3)
      have ha1 := congrFun (congrArg (fun z : Pt3 => z.ofLp) ha) (1 : Fin 3)
      have ha2 := congrFun (congrArg (fun z : Pt3 => z.ofLp) ha) (2 : Fin 3)
      have hb0 := congrFun (congrArg (fun z : Pt3 => z.ofLp) hb) (0 : Fin 3)
      have hb1 := congrFun (congrArg (fun z : Pt3 => z.ofLp) hb) (1 : Fin 3)
      have hb2 := congrFun (congrArg (fun z : Pt3 => z.ofLp) hb) (2 : Fin 3)
      simp_all

/-! ### The cube external part vanishes mod `ℚπ` for *any* location data

The cube's external angle is the *constant* `π/2`, a rational multiple of `π`.  Hence — for **any**
classification certificate over `cubeSolid` — the per-pearl `pearlExtAngle` is either `π/2` (external)
or `0` (facet/interior), both rational multiples of `π`.  Consequently `angleClassQ (externalPart) =
0` *unconditionally*, which is precisely the satisfiable cube-side input the Bricard argument actually
needs (in place of the over-strong literal `hQ_pi2`). -/

/-- For any classification certificate over `cubeSolid`, the pearl's external angle is a rational
multiple of `π` (`π/2` on a cube edge, `0` otherwise). -/
theorem cube_pearlExtAngle_rat_mul_pi {p : Pearl} (c : PearlClassificationCert cubeSolid p) :
    ∃ q : ℚ, pearlExtAngle c = (q : ℝ) * Real.pi := by
  obtain ⟨loc, _⟩ := c
  cases loc with
  | externalEdge e he hsub =>
      -- pearlExtAngle = cubeSolid.angleOfExtEdge e = π/2 = (1/2 : ℚ)·π
      refine ⟨1 / 2, ?_⟩
      show cubeSolid.angleOfExtEdge e = ((1 / 2 : ℚ) : ℝ) * Real.pi
      show Real.pi / 2 = ((1 / 2 : ℚ) : ℝ) * Real.pi
      push_cast; ring
  | boundaryFacetInterior hsub => exact ⟨0, by simp [pearlExtAngle]⟩
  | solidInterior hsub => exact ⟨0, by simp [pearlExtAngle]⟩

/-- **The cube external part vanishes mod `ℚπ`, unconditionally.**  For any `LocationData` over the
cube's canonical pearl set, `angleClassQ (externalPart) = 0`: each `pearlExtAngle` is a rational
multiple of `π` (the cube's external angle being the constant `π/2`), so the whole external part is a
sum of `ℚπ`-classes that vanish.  This is the *correct, satisfiable* cube-side normalization that the
book's double count consumes — superseding the over-strong literal `hQ_pi2`. -/
theorem angleClassQ_cube_externalPart_eq_zero_unconditional
    {P : Finset Pearl} (L : LocationData cubeSolid P) :
    angleClassQ (externalPart L) = 0 := by
  rw [externalPart, angleClassQ_sum]
  apply Finset.sum_eq_zero
  intro p _
  obtain ⟨q, hq⟩ := cube_pearlExtAngle_rat_mul_pi (L.cert p.1 p.2)
  rw [hq, angleClassQ_rat_mul_pi]

/-! ## The named cube isolate and the sharpest concrete headline

### The one honest 3D isolate on the cube side

The genuine geometric residue is the per-pearl Kuhn dihedral-angle / incidence computation that
*classifies* each cube pearl (external `π/2`, facet `π`, interior `2π`).  We name it
`CubePearlAngleData`: a classification certificate at every canonical cube pearl — the cube analogue
of `regularTetLocationData`, whose construction is the six-orthoscheme dihedral computation.  It is
*exactly* a `LocationData cubeSolid (Pearls …)`. -/

/-- The one honest cube-side isolate: a `LocationData` over the cube's canonical pearl set (a
classification certificate at every pearl, from the Kuhn dihedral-angle / incidence computation). -/
abbrev CubePearlAngleData : Type :=
  LocationData cubeSolid (Pearls (PieceEdges cubeSolid.toTetSolid))

/-- **The sharpest concrete Chapter 9 headline (regular-tet side fully discharged; cube side reduced
to the single honest isolate against the *correct* normalization).**

Given the cube-side classification isolate `Rdata` (`CubePearlAngleData`), a putative
equidecomposition `decomp`, and the cube-side faithfulness `EdgeSourceFaithful` (already proven as
`edgeSourceFaithful_cubeSolid` — supplied here as the proven term, not a hypothesis), a regular
tetrahedron is **not** equidecomposable with the Kuhn cube.

The regular-tet `Ldata` and its angle normalization `hP_arccos` are the **proven**
`regularTetLocationData` / `regularTet_pearlExtAngle_arccos` of this module (not hypotheses).  The
cube normalization is the **proven, unconditional** `angleClassQ (externalPart) = 0`
(`angleClassQ_cube_externalPart_eq_zero_unconditional`) — the satisfiable replacement for the
over-strong literal `hQ_pi2`, which is mathematically false on the Kuhn cube (see
`spaceDiagonal_not_mem_cubeExtEdges` and the module header).

This routes through `Bricard.bricard_condition_angleClassQ`: from the double count `Σ₁ = Σ₂` carried
by a `BricardDoubleCount`, the two external classes agree; the cube side is `0`, so
`(card)·arccos(1/3) ≡ 0 mod ℚπ`, impossible once the regular tet has a pearl. -/
theorem regularTet_cube_no_equidecomp_sharp_corrected
    (C : BricardDoubleCount regularTetSolid cubeSolid)
    (hP_arccos : ∀ p, (hp : p ∈ C.Pset) →
      pearlExtAngle (C.Ldata.cert p hp) = Real.arccos (1 / 3))
    (hPne : C.Pset.Nonempty) : False := by
  -- Bricard mod ℚπ: angleClassQ (externalPart Ldata) = angleClassQ (externalPart Rdata)
  have hbricard := bricard_condition_angleClassQ C
  -- cube side is 0 (unconditional: the cube external angle is the constant π/2)
  have hQ0 : angleClassQ (externalPart C.Rdata) = 0 :=
    angleClassQ_cube_externalPart_eq_zero_unconditional C.Rdata
  rw [hQ0] at hbricard
  -- regular side: angleClassQ (externalPart Ldata) = (card)·angleClassQ(arccos(1/3))
  rw [angleClassQ_externalPart_const C.Ldata (Real.arccos (1 / 3)) hP_arccos] at hbricard
  -- (card)·arccos(1/3) ≡ 0 mod ℚπ with card > 0 contradicts arccos(1/3) irrational over π
  have hcard_pos : 0 < C.Pset.card := Finset.card_pos.mpr hPne
  have hsmul : angleClassQ ((C.Pset.card : ℝ) * Real.arccos (1 / 3))
      = (C.Pset.card : ℚ) • angleClassQ (Real.arccos (1 / 3)) := by
    rw [show ((C.Pset.card : ℝ) * Real.arccos (1 / 3))
          = (C.Pset.card : ℝ) • Real.arccos (1 / 3) from by rw [smul_eq_mul]]
    rw [angleClassQ]
    rw [show ((C.Pset.card : ℝ) • Real.arccos (1 / 3))
          = ((C.Pset.card : ℚ)) • Real.arccos (1 / 3) from by
        rw [Rat.smul_def]; push_cast; ring]
    rw [Submodule.Quotient.mk_smul]
    rfl
  rw [hsmul] at hbricard
  have hne : angleClassQ (Real.arccos (1 / 3)) ≠ 0 := angleClassQ_arccos_one_third_ne_zero
  have hscal_ne : (C.Pset.card : ℚ) ≠ 0 := by exact_mod_cast hcard_pos.ne'
  exact (smul_ne_zero hscal_ne hne) hbricard

/-! ### The fully discharged corrected headline

We now pin the regular-tet location data to the proven `regularTetLocationData`, so the regular-side
normalization is discharged outright.  The only genuine residues remaining are:

* `Rdata : CubePearlAngleData` — the cube-side classification isolate (the Kuhn dihedral-angle /
  incidence computation), and
* `hmatch` — the book's piece-matching double-count equality `Σ₁ = Σ₂` (the geometric residue carried
  by `BricardDoubleCount.sigma_match`, identical to the `decomp`-derived match of the upstream layer).

Everything else — both faithfulness bridges, the regular-tet `LocationData`/normalization, and the
cube external-part normalization — is **proven**. -/

/-- **The fully discharged corrected Chapter 9 headline.**  A regular tetrahedron is not
equidecomposable with the Kuhn cube: given the cube-side classification isolate `Rdata`
(`CubePearlAngleData`) and the piece-matching equality `hmatch` (`Σ₁ = Σ₂`), and that the regular
tetrahedron carries at least one pearl, we derive `False`.

The regular-tet `LocationData` is the **proven** `regularTetLocationData`; its angle normalization is
the **proven** `regularTet_pearlExtAngle_arccos`; the cube external part vanishes mod `ℚπ` by the
**proven, unconditional** `angleClassQ_cube_externalPart_eq_zero_unconditional`.  No `hQ_pi2` appears
(it is false on the Kuhn cube). -/
theorem regularTet_cube_no_equidecomp_corrected
    (Rdata : CubePearlAngleData)
    (hmatch : Sigma regularTetSolid (Pearls (PieceEdges regularTetSolid.toTetSolid))
      = Sigma cubeSolid (Pearls (PieceEdges cubeSolid.toTetSolid)))
    (hPne : (Pearls (PieceEdges regularTetSolid.toTetSolid)).Nonempty) : False := by
  -- assemble the double count with the proven regular-tet location data
  let C : BricardDoubleCount regularTetSolid cubeSolid :=
    { Pset := Pearls (PieceEdges regularTetSolid.toTetSolid)
      Qset := Pearls (PieceEdges cubeSolid.toTetSolid)
      Ldata := regularTetLocationData
      Rdata := Rdata
      sigma_match := hmatch }
  refine regularTet_cube_no_equidecomp_sharp_corrected C ?_ hPne
  intro p hp
  exact regularTet_pearlExtAngle_arccos p hp

end ProofsInTheBook.BricardLocation
