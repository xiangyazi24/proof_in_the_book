import ProofsInTheBook.BricardAggregate

/-!
# Concrete instantiation of the Chapter 9 aggregation layer: `EdgeSourceFaithful` for
non-overlapping-edge solids, and the single-tetrahedron concrete solid

`BricardAggregate.lean` reduced the Chapter 9 headline
(`regularTet_cube_no_equidecomp_aggregated`) to the classification-layer `LocationData`/
`PearlSectorModel` certificates, the concrete external-angle normalizations, and **two faithfulness
bridges** `EdgeSourceFaithful SP.toTetSolid` / `EdgeSourceFaithful SQ.toTetSolid`.  This module closes
the second of those inputs — the faithfulness bridge — for a *robust* and *honestly characterized*
class of solids, and supplies a concrete single-tetrahedron solid in that class.

## What `EdgeSourceFaithful` really asks (re-read, exact)

`EdgeSourceFaithful S` says: for every edge occurrence `E ∈ allEdgeOccs S`, the canonical pearls of
`S` *incident* to `E` (those `p` with `p.relInterior ⊆ E.carrier`) are *exactly* the pearls of `S`
*sourced on* the edge segment `E.seg` (those `p` with `p.sourceEdge = E.seg`).

The inclusion **source ⊆ incidence** is unconditional (`pearlsOnSource_subset_incident` of
`BricardAggregate.lean`).  The converse can fail only by the following mechanism: a canonical pearl
`p`, *sourced on a distinct raw edge* `f = p.sourceEdge ≠ E.seg`, whose relative interior nevertheless
lies inside `E.seg.carrier`.  Since a pearl's relative interior is a *nondegenerate* open segment
(`p.lo < p.hi`), this forces `f` and `E.seg` to **share two distinct points**, hence (both being
segments) to be **collinear-overlapping**.  For two *distinct* edges of one and the same tetrahedron
this is impossible: any two edges of an affinely-independent tetrahedron meet in at most a vertex
(three of its four vertices would otherwise be collinear, contradicting affine independence).

So the exact geometric hypothesis on which `EdgeSourceFaithful` rests is:

> `EdgesNonOverlapping S` — distinct raw edges of `S` never share two distinct points.

This is the *collinear-edge non-degeneracy* flagged honestly in `BricardAggregate.lean`.  We:

1. prove `edgeSourceFaithful_of_nonOverlapping : EdgesNonOverlapping S → EdgeSourceFaithful S`
   (the converse, **unconditional** modulo the named non-overlap predicate);
2. prove `EdgesNonOverlapping` **outright** for any solid all of whose pieces are a *single*
   affinely-independent tetrahedron — in particular for the regular tetrahedron `regularTet` — by
   reducing a two-point overlap of two distinct edges to three collinear vertices and contradicting
   `affineIndependent_iff_not_collinear_of_ne`;
3. assemble the single-tetrahedron concrete solid `oneTetSolid T` and discharge its
   `EdgeSourceFaithful` bridge with no remaining geometric hypothesis.

The cube side genuinely *does* have collinear-overlapping edges (adjacent tets of any simplicial
subdivision share edges, and boundary edges are split), so `EdgesNonOverlapping` is the honest place
where that side's faithfulness must be supplied; we record exactly what remains there.

No `sorry`, `axiom`, or `admit`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped BigOperators Classical RealInnerProductSpace
open Set
open ProofsInTheBook.TetPearls
open ProofsInTheBook.PearlClassification
open ProofsInTheBook.TetDihedral
open ProofsInTheBook.Chapter09

namespace ProofsInTheBook.Bricard

/-! ## Collinearity infrastructure: a segment carrier is collinear -/

/-- The carrier of a `Segment3` is a collinear set: every point is `a + t•(b-a)`. -/
theorem segment_carrier_collinear (s : Segment3) : Collinear ℝ s.carrier := by
  rw [collinear_iff_of_mem (s.a_mem_carrier)]
  refine ⟨s.b - s.a, ?_⟩
  intro x hx
  rw [Segment3.carrier, segment_eq_image] at hx
  obtain ⟨t, _, rfl⟩ := hx
  refine ⟨t, ?_⟩
  -- `(1-t)•a + t•b = t•(b-a) +ᵥ a`.
  simp only [vadd_eq_add]
  match_scalars <;> ring

/-- If two distinct points `x ≠ y` both lie on a `Segment3` carrier, then both endpoints of the
segment lie on the line `affineSpan ℝ {x, y}`. -/
theorem endpoints_mem_line_of_two_mem {s : Segment3} {x y : Pt3} (hxy : x ≠ y)
    (hx : x ∈ s.carrier) (hy : y ∈ s.carrier) :
    s.a ∈ line[ℝ, x, y] ∧ s.b ∈ line[ℝ, x, y] := by
  have hcol := segment_carrier_collinear s
  refine ⟨?_, ?_⟩
  · exact hcol.mem_affineSpan_of_mem_of_ne hx hy s.a_mem_carrier hxy
  · exact hcol.mem_affineSpan_of_mem_of_ne hx hy s.b_mem_carrier hxy

/-! ## The non-overlap predicate and the faithfulness converse -/

/-- **Edge non-overlap.**  Distinct raw edges of `S` never share two distinct points: any two
segments in `PieceEdges S` that contain two distinct common points are equal.  This is exactly the
collinear-edge non-degeneracy that makes incidence faithful to source. -/
def EdgesNonOverlapping (S : TetSolid) : Prop :=
  ∀ f g : Segment3, f ∈ PieceEdges S → g ∈ PieceEdges S →
    ∀ x y : Pt3, x ≠ y → x ∈ f.carrier → y ∈ f.carrier → x ∈ g.carrier → y ∈ g.carrier → f = g

/-- A canonical pearl's two endpoints are distinct (since `lo < hi` and `point` is injective). -/
theorem pearl_aPt_ne_bPt {R : Finset Segment3} {p : Pearl} (hp : IsPearlOf R p) :
    p.aPt ≠ p.bPt := by
  intro h
  have : p.lo = p.hi := p.sourceEdge.point_injective h
  exact absurd this (ne_of_lt hp.2.2.2.1)

/-- A canonical pearl's closed carrier lies in any closed set containing its relative interior; in
particular, if `p.relInterior ⊆ E.carrier`, then both endpoints `aPt`, `bPt` lie in `E.carrier`
(closure of `relInterior` ⊆ closed `E.carrier`). -/
theorem pearl_endpoints_mem_of_relInterior_subset {p : Pearl} {C : Set Pt3} (hC : IsClosed C)
    (hsub : p.relInterior ⊆ C) : p.aPt ∈ C ∧ p.bPt ∈ C := by
  -- `aPt, bPt ∈ closure (openSegment) = segment` (nondegenerate), and `closure relInterior ⊆ C`.
  have hcl : closure p.relInterior ⊆ C := hC.closure_subset_iff.mpr hsub
  have hcar : p.carrier ⊆ closure p.relInterior := by
    rw [Pearl.carrier, Pearl.relInterior]
    exact segment_subset_closure_openSegment
  refine ⟨hcl (hcar ?_), hcl (hcar ?_)⟩
  · exact left_mem_segment ℝ p.aPt p.bPt
  · exact right_mem_segment ℝ p.aPt p.bPt

/-! ## Three distinct vertices of a tetrahedron are not collinear -/

/-- **Any three distinct vertices of an affinely-independent tetrahedron are not collinear.**  Restrict
the vertex map along the embedding `![i, j, k] : Fin 3 ↪ Fin 4` and apply
`affineIndependent_iff_not_collinear`. -/
theorem tet_three_vertices_not_collinear (T : Tet) {i j k : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ Collinear ℝ ({T.v i, T.v j, T.v k} : Set Pt3) := by
  -- the embedding `Fin 3 ↪ Fin 4` picking out `i, j, k`.
  have hinj : Function.Injective (![i, j, k] : Fin 3 → Fin 4) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  let emb : Fin 3 ↪ Fin 4 := ⟨![i, j, k], hinj⟩
  have hai : AffineIndependent ℝ (T.v ∘ (emb : Fin 3 → Fin 4)) := T.affIndep.comp_embedding emb
  rw [affineIndependent_iff_not_collinear] at hai
  -- `range (T.v ∘ emb) = {T.v i, T.v j, T.v k}`.
  have hrange : Set.range (T.v ∘ (emb : Fin 3 → Fin 4)) = ({T.v i, T.v j, T.v k} : Set Pt3) := by
    ext z
    simp only [Set.mem_range, Function.comp_apply, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, rfl⟩
      fin_cases a <;> simp [emb]
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by simp [emb]⟩
      · exact ⟨1, by simp [emb]⟩
      · exact ⟨2, by simp [emb]⟩
  rwa [hrange] at hai

/-! ## Edges of a single tetrahedron do not overlap -/

/-- The endpoints of an edge segment of a tetrahedron are vertices of that tetrahedron. -/
theorem edgeSeg_endpoints {T : Tet} {q : Fin 4 × Fin 4} (h : q.1 ≠ q.2) :
    (T.edgeSeg q h).a = T.v q.1 ∧ (T.edgeSeg q h).b = T.v q.2 := ⟨rfl, rfl⟩

/-- A member of `T.edges` arises from a strictly-ordered index pair: there are `i < j` with
`f.a = T.v i`, `f.b = T.v j`. -/
theorem mem_edges_endpoints {T : Tet} {f : Segment3} (hf : f ∈ T.edges) :
    ∃ i j : Fin 4, i < j ∧ f.a = T.v i ∧ f.b = T.v j := by
  rw [Tet.edges, Finset.mem_image] at hf
  obtain ⟨q, _, rfl⟩ := hf
  exact ⟨q.1.1, q.1.2, edgePairs_lt q.2, rfl, rfl⟩

/-- **Two distinct edges of a single tetrahedron do not overlap.**  If `f, g` are distinct edges of
`T` sharing two distinct points `x ≠ y`, then all four endpoints lie on `line[x,y]`; since the edges
differ there are three distinct vertices among them, which would then be collinear — contradicting
affine independence. -/
theorem tet_edges_nonoverlap {T : Tet} {f g : Segment3} (hf : f ∈ T.edges) (hg : g ∈ T.edges)
    (hne : f ≠ g) {x y : Pt3} (hxy : x ≠ y)
    (hxf : x ∈ f.carrier) (hyf : y ∈ f.carrier) (hxg : x ∈ g.carrier) (hyg : y ∈ g.carrier) :
    False := by
  obtain ⟨i, j, hijlt, hfa, hfb⟩ := mem_edges_endpoints hf
  obtain ⟨k, l, hkllt, hga, hgb⟩ := mem_edges_endpoints hg
  have hij : i ≠ j := ne_of_lt hijlt
  have hkl : k ≠ l := ne_of_lt hkllt
  -- the index pairs differ (else the segments would coincide).
  have hpair : (i, j) ≠ (k, l) := by
    intro h
    apply hne
    rw [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    -- both segments have the same endpoints, hence are equal (`hne` is proof-irrelevant).
    have hab : f.a = g.a := by rw [hfa, hga]
    have hbb : f.b = g.b := by rw [hfb, hgb]
    cases f; cases g; simp_all
  -- all four endpoints lie on `line[x,y]`.
  have hmem : ∀ {s : Segment3}, x ∈ s.carrier → y ∈ s.carrier →
      s.a ∈ line[ℝ, x, y] ∧ s.b ∈ line[ℝ, x, y] := fun hx hy =>
    endpoints_mem_line_of_two_mem hxy hx hy
  obtain ⟨hfaL, hfbL⟩ := hmem hxf hyf
  obtain ⟨hgaL, hgbL⟩ := hmem hxg hyg
  rw [hfa] at hfaL; rw [hfb] at hfbL; rw [hga] at hgaL; rw [hgb] at hgbL
  -- pick three distinct indices among `i, j, k, l`.
  -- since `(i,j) ≠ (k,l)` with `i ≠ j`, `k ≠ l`, at least three are distinct.
  have hcol3 : ∀ {a b c : Fin 4}, a ≠ b → a ≠ c → b ≠ c →
      T.v a ∈ line[ℝ, x, y] → T.v b ∈ line[ℝ, x, y] → T.v c ∈ line[ℝ, x, y] → False := by
    intro a b c hab hac hbc ha hb hc
    apply tet_three_vertices_not_collinear T hab hac hbc
    -- `va, vb, x, y` collinear; add `vc ∈ line[x,y] ⊆ affineSpan{va,vb,x,y}`.
    have h4 : Collinear ℝ ({T.v a, T.v b, x, y} : Set Pt3) :=
      collinear_insert_insert_of_mem_affineSpan_pair ha hb
    have hcin : T.v c ∈ affineSpan ℝ ({T.v a, T.v b, x, y} : Set Pt3) := by
      refine (AffineSubspace.le_def' _ _).1 ?_ _ hc
      refine affineSpan_mono ℝ ?_
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl <;> simp
    have h5 : Collinear ℝ (insert (T.v c) ({T.v a, T.v b, x, y} : Set Pt3)) :=
      (collinear_insert_iff_of_mem_affineSpan hcin).mpr h4
    exact h5.subset (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl <;> simp)
  -- case analysis: which indices coincide?
  by_cases hik : i = k
  · subst hik
    -- then `j ≠ l` (else pairs equal).  indices `i, j, l` distinct.
    have hjl : j ≠ l := by rintro rfl; exact hpair rfl
    exact hcol3 hij hkl hjl hfaL hfbL hgbL
  · by_cases hil : i = l
    · -- `i = l`; then `i, j, k` distinct (`j ≠ k`? maybe `j = k`).
      by_cases hjk : j = k
      · -- `i = l`, `j = k`: indices `i, j` and `k=j, l=i`: vertices are `{i,j}`; but `i<j`, `k<l`
        -- means `j < i` from `k<l` i.e. `j<i`, contradicting `i<j`.
        subst hil; subst hjk
        exact absurd (lt_trans hijlt hkllt) (lt_irrefl i)
      · exact hcol3 hij hik hjk hfaL hfbL hgaL
    · -- `i ∉ {k,l}`; indices `i, k, l` distinct.
      exact hcol3 hik hil hkl hfaL hgaL hgbL

/-! ## The single-tetrahedron solid and its non-overlap -/

/-- The tetrahedral solid consisting of a single tetrahedron `T`. -/
def oneTetSolid (T : Tet) : TetSolid where
  pieces := {T}
  interior_disjoint := by
    intro A hA B hB hAB
    rw [Finset.mem_singleton] at hA hB
    exact absurd (hA.trans hB.symm) hAB

@[simp] theorem oneTetSolid_pieces (T : Tet) : (oneTetSolid T).pieces = {T} := rfl

theorem oneTetSolid_pieces_nonempty (T : Tet) : (oneTetSolid T).pieces.Nonempty :=
  ⟨T, Finset.mem_singleton_self T⟩

/-- The raw 1-skeleton of `oneTetSolid T` is exactly the six edges of `T`. -/
theorem pieceEdges_oneTetSolid (T : Tet) : PieceEdges (oneTetSolid T) = T.edges := by
  rw [PieceEdges, oneTetSolid_pieces, Finset.singleton_biUnion]

/-- **The single-tetrahedron solid has non-overlapping edges.**  Every raw edge of `oneTetSolid T` is
an edge of `T`, and distinct edges of one affinely-independent tetrahedron never share two distinct
points (`tet_edges_nonoverlap`). -/
theorem edgesNonOverlapping_oneTetSolid (T : Tet) : EdgesNonOverlapping (oneTetSolid T) := by
  intro f g hf hg x y hxy hxf hyf hxg hyg
  rw [pieceEdges_oneTetSolid] at hf hg
  by_contra hne
  exact tet_edges_nonoverlap hf hg hne hxy hxf hyf hxg hyg

/-! ## The faithfulness converse: `EdgesNonOverlapping ⟹ EdgeSourceFaithful` -/

/-- **The faithfulness converse.**  If distinct raw edges of `S` never overlap (`EdgesNonOverlapping`),
then on the canonical pearl set the incidence relation coincides with the source relation:
`EdgeSourceFaithful S`.  Source ⊆ incidence is the unconditional `pearlsOnSource_subset_incident`; the
converse holds because a canonical pearl incident to `E` has a *nondegenerate* relative interior lying
in both its source edge's carrier and `E.carrier`, exhibiting two distinct common points of those two
raw edges — so non-overlap forces `p.sourceEdge = E.seg`. -/
theorem edgeSourceFaithful_of_nonOverlapping {S : TetSolid} (hno : EdgesNonOverlapping S) :
    EdgeSourceFaithful S := by
  intro E hE
  apply Finset.Subset.antisymm
  · -- incidence ⊆ source.
    intro p hp
    rw [Finset.mem_filter, mem_Pearls] at hp
    obtain ⟨hpval, hinc⟩ := hp
    rw [mem_pearlsOnSource]
    refine ⟨hpval, ?_⟩
    -- `p.sourceEdge` and `E.seg` share the two distinct endpoints `aPt ≠ bPt` of the pearl.
    have hincE : p.relInterior ⊆ E.carrier := (mem_IncidentTetEdges.mp hinc).2
    have hincSrc : p.relInterior ⊆ p.sourceEdge.carrier :=
      relInterior_subset_sourceEdge_carrier p hpval
    -- both endpoints lie in `E.carrier` (= `E.seg.carrier`, closed) and in `p.sourceEdge.carrier`.
    have hEclosed : IsClosed E.carrier := E.seg.carrier_closed
    have hSrcClosed : IsClosed p.sourceEdge.carrier := p.sourceEdge.carrier_closed
    obtain ⟨haE, hbE⟩ := pearl_endpoints_mem_of_relInterior_subset hEclosed hincE
    obtain ⟨haS, hbS⟩ := pearl_endpoints_mem_of_relInterior_subset hSrcClosed hincSrc
    have hab : p.aPt ≠ p.bPt := pearl_aPt_ne_bPt hpval
    -- non-overlap: `p.sourceEdge = E.seg`.
    exact hno p.sourceEdge E.seg hpval.1 (edgeOcc_seg_mem_pieceEdges E)
      p.aPt p.bPt hab haS hbS haE hbE
  · -- source ⊆ incidence.
    have hsub : pearlsOnSource (PieceEdges S) E.seg ⊆ Pearls (PieceEdges S) := by
      intro p hp
      exact mem_Pearls.mpr (mem_pearlsOnSource.mp hp).1
    exact pearlsOnSource_subset_incident (Pearls (PieceEdges S)) E hsub

/-- **`EdgeSourceFaithful` for the single-tetrahedron solid** (no remaining hypothesis). -/
theorem edgeSourceFaithful_oneTetSolid (T : Tet) : EdgeSourceFaithful (oneTetSolid T) :=
  edgeSourceFaithful_of_nonOverlapping (edgesNonOverlapping_oneTetSolid T)

/-! ## The concrete regular-tetrahedron solid as a `SolidWithAngles`

The regular tetrahedron, as a one-piece solid, with all six edges declared external and carrying the
external dihedral angle `arccos(1/3)`.  The `LocalDihedralModel` validation is the bound
`0 < arccos(1/3) < π` (which holds since `1/3 ∈ (-1, 1)`).  This packages the `SolidWithAngles`
datum the Chapter 9 headline consumes on the regular-tet side; its `EdgeSourceFaithful` bridge is the
unconditional `edgeSourceFaithful_oneTetSolid`. -/

/-- `arccos(1/3)` is a valid dihedral angle: `0 < arccos(1/3) < π`. -/
theorem arccos_third_mem_Ioo : Real.arccos (1 / 3) ∈ Set.Ioo (0 : ℝ) Real.pi :=
  ⟨Real.arccos_pos.mpr (by norm_num), Real.arccos_lt_pi.mpr (by norm_num)⟩

/-- **The regular tetrahedron as a `SolidWithAngles`.**  One piece (`regularTet`); all six edges
external with external angle `arccos(1/3)`. -/
def regularTetSolid : SolidWithAngles where
  toTetSolid := oneTetSolid regularTet
  extEdges := regularTet.edges
  angleOfExtEdge := fun _ => Real.arccos (1 / 3)
  extEdge_local_model := by
    intro e _
    exact ⟨arccos_third_mem_Ioo.1, arccos_third_mem_Ioo.2⟩

@[simp] theorem regularTetSolid_toTetSolid : regularTetSolid.toTetSolid = oneTetSolid regularTet := rfl

/-- `EdgeSourceFaithful` for the regular-tet solid (no remaining hypothesis). -/
theorem edgeSourceFaithful_regularTetSolid :
    EdgeSourceFaithful regularTetSolid.toTetSolid :=
  edgeSourceFaithful_oneTetSolid regularTet

theorem regularTetSolid_pieces_nonempty : regularTetSolid.toTetSolid.pieces.Nonempty :=
  oneTetSolid_pieces_nonempty regularTet

/-! ## The sharpest concrete headline (regular-tet side fully discharged)

Specializing `regularTet_cube_no_equidecomp_aggregated` to `SP = regularTetSolid`, the
regular-tet-side faithfulness bridge `hFP` and nonemptiness `hSP` are **discharged by the proven
facts** of this module (`edgeSourceFaithful_regularTetSolid`, `regularTetSolid_pieces_nonempty`).

What remains, honestly:

* `SQ`, `Rdata`, `hFQ` — the **cube side**: a `SolidWithAngles` packaging a tetrahedral subdivision of
  the cube, its `LocationData` certificates, and its `EdgeSourceFaithful` bridge.  The cube side's
  faithfulness is *not* discharged here: a genuine simplicial subdivision of the cube has
  collinear-overlapping raw edges (adjacent tets share edges; boundary edges are split), so
  `EdgesNonOverlapping` *fails* for it — the converse route used for the single tetrahedron does not
  apply, and the faithful regrouping of incidence-weights over collinear edge classes is the isolated
  residue documented in `BricardAggregate.lean`.  We keep it as an honest hypothesis `hFQ`.
* `Ldata` — the regular-tet `LocationData` (the `PearlSectorModel` cross-section certificates: the
  design-sanctioned isolated 3D residue of `PearlClassification.lean`).
* `hP_arccos`, `hQ_pi2` — the concrete external-angle normalizations, which are properties of the
  `LocationData` certificates (each pearl is classified onto an external edge whose angle is the
  declared value), not of the solids alone. -/

/-- **The sharpest concrete Chapter 9 headline.**  A regular tetrahedron is not equidecomposable with
any cube-side solid `SQ` realizing the `π/2` external-angle normalization, with the regular-tet side
entirely concrete: its faithfulness bridge and nonemptiness are the proven
`edgeSourceFaithful_regularTetSolid` / `regularTetSolid_pieces_nonempty`, **not** hypotheses.

Remaining honest inputs: the regular-tet `LocationData` `Ldata` (the `PearlSectorModel` residue), the
cube-side `SQ`/`Rdata`/`hFQ` (its `SolidWithAngles`, `LocationData`, and faithfulness bridge — the
latter being the genuinely-collinear cube-edge non-degeneracy), and the two angle normalizations. -/
theorem regularTet_cube_no_equidecomp_concreteP
    {SQ : SolidWithAngles}
    (Ldata : LocationData regularTetSolid (Pearls (PieceEdges regularTetSolid.toTetSolid)))
    (Rdata : LocationData SQ (Pearls (PieceEdges SQ.toTetSolid)))
    (decomp : TetEquidecomp regularTetSolid.toTetSolid SQ.toTetSolid)
    (hP_arccos : ∀ p, (hp : p ∈ Pearls (PieceEdges regularTetSolid.toTetSolid)) →
      pearlExtAngle (Ldata.cert p hp) = Real.arccos (1 / 3))
    (hQ_pi2 : ∀ p, (hp : p ∈ Pearls (PieceEdges SQ.toTetSolid)) →
      pearlExtAngle (Rdata.cert p hp) = Real.pi / 2)
    (hFQ : EdgeSourceFaithful SQ.toTetSolid) : False :=
  regularTet_cube_no_equidecomp_aggregated Ldata Rdata decomp hP_arccos hQ_pi2
    regularTetSolid_pieces_nonempty edgeSourceFaithful_regularTetSolid hFQ

end ProofsInTheBook.Bricard
