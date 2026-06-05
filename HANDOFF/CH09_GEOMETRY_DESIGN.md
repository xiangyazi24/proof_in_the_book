Executive recommendation

Use a simplices-only geometric layer.

Do not try to build a general polyhedron API. Define decompositions into closed nondegenerate tetrahedra with pairwise disjoint relative interiors, define equidecomposability by a bijection plus Euclidean isometries between tetrahedral pieces, prove the Pearl/Bricard angle condition in that language, and instantiate it for:

lean
regularTetrahedron a
cubeOfEqualVolume a

This is faithful enough for the book headline and avoids a huge general-polyhedra detour.

The single hardest lemma is:

lean
lemma pearl_angle_sum_classification

because it packages the entire local 3D geometry of the refinement: around each refined segment, the incident tetrahedral dihedral angles sum to either an original boundary dihedral angle, π, or 2π.

Everything else should be engineered so this lemma has a small, rigid interface.

1. Simplices-only reduction
Recommendation

Define scissors congruence using tetrahedral decompositions only.

lean
abbrev Pt3 := EuclideanSpace ℝ (Fin 3)

A tetrahedron should be:

lean
structure Tet where
  v : Fin 4 → Pt3
  affIndep : AffineIndependent ℝ v

Its closed carrier:

lean
def Tet.carrier (T : Tet) : Set Pt3 :=
  convexHull ℝ (Set.range T.v)

Its relative/open interior:

lean
def Tet.relInterior (T : Tet) : Set Pt3 :=
  relativeInterior T.carrier

Since a nondegenerate tetrahedron is full-dimensional in ℝ³, also prove:

lean
lemma Tet.relativeInterior_eq_interior :
  T.relInterior = interior T.carrier

A tetrahedral solid:

lean
structure TetSolid where
  pieces : Finset Tet
  interior_disjoint :
    ∀ A ∈ pieces, ∀ B ∈ pieces, A ≠ B →
      Disjoint A.relInterior B.relInterior

Carrier:

lean
def TetSolid.carrier (S : TetSolid) : Set Pt3 :=
  ⋃ T ∈ S.pieces, T.carrier

Equidecomposability:

lean
structure TetEquidecomp (P Q : TetSolid) : Prop where
  e : P.pieces ≃ Q.pieces
  iso : ∀ T : P.pieces, EuclideanIsometry Pt3 Pt3
  maps_piece :
    ∀ T : P.pieces,
      (iso T) '' T.val.carrier = (e T).val.carrier

Allow reflections. So use full Euclidean isometries, not just orientation-preserving motions.

Is this equivalent to the book notion?

For the headline, yes.

What you gain:

cube can be decomposed into tetrahedra;

regular tetrahedron is already one tetrahedron;

every usual finite polyhedral dissection can be barycentrically refined into tetrahedra;

Bricard’s condition only needs tetrahedral pieces and their dihedral angles.

What you lose:

you do not formalize arbitrary polyhedra as first-class objects;

you do not prove the most general statement “all polyhedra equidecomposable implies Bricard condition”;

you prove instead the theorem for tetrahedrally decomposed solids.

This is the right Lean tradeoff. The final theorem can honestly be:

lean
theorem regular_tetrahedron_not_tetEquidecomp_cube_equal_volume :
  ¬ TetEquidecomp (regularTetrahedronSolid a) (cubeTetSolidOfEqualVolume a)

Then optionally define a wrapper:

lean
def ScissorsCongruent (A B : Set Pt3) : Prop :=
  ∃ P Q : TetSolid,
    P.carrier = A ∧ Q.carrier = B ∧ TetEquidecomp P Q

and state the headline in terms of ScissorsCongruent.

2. Polyhedron objects: use TetSolid, not general faces

You still need boundary edges and dihedral angles of the external solid. For this layer, define only what is needed for a tetrahedral solid.

A face occurrence:

lean
structure FaceOcc (S : TetSolid) where
  T : S.pieces
  face : Finset (Fin 4)
  hcard : face.card = 3

An edge occurrence:

lean
structure EdgeOcc (S : TetSolid) where
  T : S.pieces
  edge : Finset (Fin 4)
  hcard : edge.card = 2

Carrier of an edge occurrence:

lean
def EdgeOcc.carrier (e : EdgeOcc S) : Set Pt3 :=
  convexHull ℝ ((e.T.val.v) '' (e.edge : Set (Fin 4)))

Carrier of a face occurrence:

lean
def FaceOcc.carrier (f : FaceOcc S) : Set Pt3 :=
  convexHull ℝ ((f.T.val.v) '' (f.face : Set (Fin 4)))

Two face occurrences are glued if their carriers agree and they lie on opposite sides locally. But for the Bricard route, you can avoid global face-gluing classification. You only need:

external boundary facets;

external boundary edges;

local pearl classification.

Define external boundary by local neighborhood:

lean
def IsBoundaryPoint (S : TetSolid) (x : Pt3) : Prop :=
  x ∈ S.carrier ∧ x ∈ frontier S.carrier

def IsInteriorPoint (S : TetSolid) (x : Pt3) : Prop :=
  x ∈ interior S.carrier

Define a boundary edge of the external solid as a segment e such that its relative interior lies in the frontier and locally two boundary facets meet along it.

For the cube and regular tetrahedron, avoid proving a generic boundary-edge extractor. Define their external edges explicitly and prove they satisfy the needed local classification.

So have a general theorem parameterized by an external edge list:

lean
structure SolidWithAngles extends TetSolid where
  extEdges : Finset Segment3
  angleOfExtEdge : extEdges → ℝ
  extEdge_local_model :
    ∀ e : extEdges, LocalDihedralModel carrier e.val (angleOfExtEdge e)

Then instantiate:

lean
def regularTetWithAngles : SolidWithAngles
def cubeWithAngles : SolidWithAngles

This avoids a general polyhedron boundary theory.

3. Segments / pearls

The book refines the 1-skeleton of both decompositions. Formalize pearls as a finite partition of all piece-edges into subsegments whose relative interiors have constant incidence data.

Segment type

Use a normalized unordered segment with endpoints distinct.

lean
structure Segment3 where
  a b : Pt3
  hne : a ≠ b

Carrier and relative interior:

lean
def Segment3.carrier (s : Segment3) : Set Pt3 :=
  segment ℝ s.a s.b

def Segment3.relInterior (s : Segment3) : Set Pt3 :=
  openSegment ℝ s.a s.b

Two segments are equivalent if they have the same carrier. Either quotient this, or easier: store endpoints with a canonical order only if you have a decidable lexicographic order on coordinates. I would avoid canonicalization and use set equality in statements.

Piece edges

For a tetrahedral decomposition:

lean
def PieceEdges (S : TetSolid) : Finset Segment3

consisting of the six edges of every tetrahedron.

For two decompositions of the same solid, or for P and Q with paired pieces, define the combined edge set:

lean
def RawEdges (D : PairedDecompData) : Finset Segment3

where D contains all tetrahedral pieces on the relevant side, including complements for equicomplementability.

Breakpoint set on an edge

For a raw edge e, collect all points on e where the incidence can change:

endpoints of e;

intersections with every other raw edge;

intersections with every raw triangular face boundary;

points where e enters/leaves a tetrahedron carrier.

The cleanest finite definition is actually stronger:

lean
def BreakpointsOnEdge (R : Finset Segment3) (F : Finset Triangle3) (e : Segment3) :
    Finset Pt3 :=
  {e.a, e.b}
  ∪ all intersections of line(e) with planes of faces in F, restricted to e.carrier
  ∪ all intersections of line(e) with raw edges in R, restricted to e.carrier

For tetrahedra, plane intersections are finite: a line either is contained in a face plane or meets it in one point. If contained, its interaction with the triangular face changes only at intersections with that triangle’s edges, already included from raw edges.

So the robust version is:

lean
BreakpointsOnEdge = endpoints
  ∪ intersections with all raw edge carriers
  ∪ intersections with all raw face boundary edges

Since all face boundary edges are already raw tetrahedron edges, this reduces to:

lean
def BreakpointsOnEdge (R : Finset Segment3) (e : Segment3) : Finset Pt3 :=
  {e.a, e.b} ∪ {x | ∃ r ∈ R, x ∈ e.carrier ∩ r.carrier}

But to stay finite, do not use a set comprehension directly. Define pairwise segment intersection as finite:

lean
def segmentIntersectionPoints (e r : Segment3) : Finset Pt3

Then:

lean
def BreakpointsOnEdge (R : Finset Segment3) (e : Segment3) : Finset Pt3 :=
  {e.a, e.b} ∪
  R.biUnion fun r => segmentIntersectionPoints e r

This is finite and enough.

Pearls

Sort breakpoints along e by affine coordinate.

Define coordinate:

lean
def Segment3.coord (e : Segment3) (x : Pt3) : ℝ

with:

lean
x = (1 - t) • e.a + t • e.b

for x ∈ e.carrier.

Then pearls are consecutive subsegments between consecutive breakpoint coordinates.

lean
structure Pearl where
  s : Segment3
  sourceEdge : Segment3
  endpoints_are_consecutive_breakpoints :
    ConsecutiveInSegmentOrder s.a s.b (BreakpointsOnEdge R sourceEdge)

Global pearl set:

lean
def Pearls (R : Finset Segment3) : Finset Pearl
Needed partition lemmas
lean
lemma pearls_finite :
  (Pearls R).Finite
lean
lemma raw_edge_covered_by_pearls :
  ∀ e ∈ R,
    e.carrier =
      ⋃ p ∈ Pearls R, p.sourceEdge = e ∧ p.s.carrier
lean
lemma pearl_interiors_disjoint_on_same_edge :
  ∀ p q ∈ Pearls R,
    p ≠ q →
    Disjoint p.s.relInterior q.s.relInterior
lean
lemma incidence_constant_on_pearl :
  ∀ p ∈ Pearls R,
  ∀ x y ∈ p.s.relInterior,
    IncidentPieceEdgesAt R x = IncidentPieceEdgesAt R y

This is the formal reason pearls work.

4. Dihedral angles of tetrahedra

For a tetrahedron edge, two faces meet along that edge. Define the internal dihedral angle.

lean
def Tet.dihedralAngle (T : Tet) (e : Finset (Fin 4)) (he : e.card = 2) : ℝ

Recommended definition:

let L be the affine line through the edge;

take the two outward or inward face normals projected to the orthogonal plane Lᗮ;

define the angle between the two halfplanes inside the tetrahedron.

But for Lean, the most stable definition is cross-sectional:

lean
def Tet.dihedralAngle T e :=
  planarSectorAngle obtained by intersecting T.carrier
  with an affine plane perpendicular to e at an interior point of e.

Then prove independence of the chosen interior point.

Key lemmas:

lean
lemma Tet.dihedralAngle_mem_Ioo :
  0 < T.dihedralAngle e he ∧ T.dihedralAngle e he < Real.pi
lean
lemma regularTet_dihedralAngle :
  regularTet.dihedralAngle e he = Real.arccos (1 / 3)
lean
lemma cube_dihedralAngle :
  cubeSolid.angleOfExtEdge e = Real.pi / 2
5. Pearl-angle classification

For a pearl p, define incident tetrahedral edge occurrences:

lean
def IncidentTetEdges (S : TetSolid) (p : Pearl) : Finset (EdgeOcc S) :=
  {E | p.s.relInterior ⊆ E.carrier}

Then define the local angle sum:

lean
def PearlAngleSum (S : TetSolid) (p : Pearl) : ℝ :=
  ∑ E ∈ IncidentTetEdges S p,
    E.T.val.dihedralAngle E.edge E.hcard

Now classify by the location of the pearl in the external solid.

lean
inductive PearlLocation (S : SolidWithAngles) (p : Pearl) where
| externalEdge (e : S.extEdges) :
    p.s.relInterior ⊆ e.val.relInterior →
    PearlLocation S p
| boundaryFacetInterior :
    p.s.relInterior ⊆ relativeInteriorOfSomeBoundaryFacet S →
    PearlLocation S p
| solidInterior :
    p.s.relInterior ⊆ interior S.carrier →
    PearlLocation S p
| artificialFacetPlane :
    p.s.relInterior ⊆ interior S.carrier →
    p lies in a face plane of some tetrahedron →
    PearlLocation S p

Actually the fourth case does not need to be separate for the final angle sum if solidInterior always gives 2π. The book sometimes mentions π for a segment lying in an interior face plane because if you count only one side of a refinement sheet, you get π; but for the full decomposition of the solid, the total around an interior pearl is 2π. For formalization, use only three external-solid cases:

external edge: sum is external dihedral angle;

boundary facet interior: sum is π;

solid interior: sum is 2π.

Interior piece-face-plane cases are internal subcases of the proof of case 3.

Main lemma:

lean
lemma pearl_angle_sum_classification
  (S : SolidWithAngles)
  (p : Pearl)
  (hp : p ∈ Pearls (PieceEdges S.toTetSolid)) :
    (∃ e : S.extEdges,
      p.s.relInterior ⊆ e.val.relInterior ∧
      PearlAngleSum S.toTetSolid p = S.angleOfExtEdge e)
    ∨
    (p.s.relInterior ⊆ frontier S.carrier ∧
      PearlAngleSum S.toTetSolid p = Real.pi)
    ∨
    (p.s.relInterior ⊆ interior S.carrier ∧
      PearlAngleSum S.toTetSolid p = 2 * Real.pi)

This is the heart.

6. Normal form for the hardest geometry

Yes: reduce everything to a 2D cross-section orthogonal to the pearl.

For a pearl segment p, choose:

a point x ∈ p.s.relInterior;

a unit vector u along the pearl;

the affine plane

lean
Π := {y | inner (y - x) u = 0}

Every tetrahedron incident to p intersects a sufficiently small disk in Π in a planar sector. The dihedral angle equals the sector angle.

3D-to-2D reduction lemmas
lean
lemma exists_orthogonal_cross_section :
  ∃ Π : AffineSubspace ℝ Pt3,
    x ∈ Π ∧ direction Π = {v | inner v u = 0}
lean
lemma incident_tet_cross_section_sector :
  If a tetrahedron edge contains the pearl, then near x its carrier
  intersects Π in a closed planar sector whose angle equals the
  tetrahedral dihedral angle at that edge.
lean
lemma disjoint_tet_interiors_give_disjoint_sector_interiors :
  Pairwise disjoint tetrahedron interiors imply pairwise disjoint
  relative interiors of the corresponding planar sectors.
lean
lemma local_solid_cross_section_full_disk :
  If x is an interior point of S.carrier, then for sufficiently small ε,
  S.carrier ∩ closedBall x ε ∩ Π is the full closed disk in Π.
lean
lemma local_solid_cross_section_half_disk :
  If x is in the relative interior of a boundary facet, then locally
  the cross-section is a closed half-disk.
lean
lemma local_solid_cross_section_wedge :
  If x is in the relative interior of an external edge e, then locally
  the cross-section is a wedge of angle angleOfExtEdge e.
2D sector-sum lemmas

This is the correct normal form.

lean
lemma planar_sectors_disjoint_cover_disk_angle_sum :
  For finitely many closed planar sectors with common apex, pairwise
  disjoint interiors, and union equal to a closed disk locally,
  the sum of their angles is 2π.
lean
lemma planar_sectors_disjoint_cover_halfdisk_angle_sum :
  For finitely many closed planar sectors with common apex, pairwise
  disjoint interiors, and union equal to a half-disk locally,
  the sum of their angles is π.
lean
lemma planar_sectors_disjoint_cover_wedge_angle_sum :
  For finitely many closed planar sectors with common apex, pairwise
  disjoint interiors, and union equal to a wedge of angle θ locally,
  the sum of their angles is θ.

Proof route in Mathlib terms:

identify the orthogonal plane Π with EuclideanSpace ℝ (Fin 2) using a linear isometry;

represent each sector by an interval of polar angles on Real.Angle or by normalized real angles in [0, 2π);

disjoint interiors become disjoint open intervals;

covering a disk/halfdisk/wedge becomes covering the corresponding angular interval;

finite disjoint interval length additivity gives the angle sum.

This avoids measure theory if you prove interval-length additivity directly for finite sorted endpoints.

7. Congruence

Use full Euclidean isometry, including reflections.

lean
abbrev Isom3 := Pt3 ≃ᵢ Pt3

or the Mathlib equivalent for affine isometries.

Piece congruence:

lean
def TetCongruent (T U : Tet) : Prop :=
  ∃ f : Isom3, f '' T.carrier = U.carrier

Needed angle-invariance lemma:

lean
lemma dihedralAngle_isometry_invariant
  (f : Isom3)
  (T U : Tet)
  (hmap : f '' T.carrier = U.carrier)
  (e : EdgeOcc T)
  (e' : EdgeOcc U)
  (hedge : f '' e.carrier = e'.carrier) :
  T.dihedralAngle e = U.dihedralAngle e'

Reflections are fine because the dihedral angle is the unoriented angle in [0,π]. The proof via orthogonal cross-sections is best: isometries preserve cross-sections, sectors, and unoriented sector angles.

8. Pearl Lemma as a linear system

You want to derive a homogeneous linear system whose positive real solution comes from pearl lengths, then apply the already-proven Cone Lemma to get positive integer coefficients.

Let the unknowns be pearl weights:

lean
x_p > 0

For each original external edge angle class, the total length/count contribution from pearls lying on it is a linear expression in the x_p.

For Bricard’s condition, you do not actually need metric lengths if your algebraic obstruction layer only uses angle multiplicities. But the book’s Pearl Lemma usually uses positive weights assigned to pearls and equations expressing equality under congruent dissections. Since your Cone Lemma is homogeneous, use unknowns indexed by paired piece-edges or pearl orbits and build equations that force balance.

Equidecomposable case

Given TetEquidecomp P Q, refine both decompositions into corresponding pearls. Congruent tetrahedra have matching tetrahedral dihedral angles. Summing pearl classifications over all pearls gives:

lean
∑_{external edges of P} m_e * α_e
=
∑_{external edges of Q} n_f * β_f + k * π

with positive integer m_e,n_f.

Formal theorem:

lean
theorem bricard_condition_tetEquidecomp
  (P Q : SolidWithAngles)
  (h : TetEquidecomp P.toTetSolid Q.toTetSolid) :
  ∃ m : P.extEdges → ℕ,
  ∃ n : Q.extEdges → ℕ,
  ∃ k : ℤ,
    (∀ e, 0 < m e) ∧
    (∀ f, 0 < n f) ∧
    (∑ e, (m e : ℤ) • AngleClass.ofReal (P.angleOfExtEdge e))
      =
    (∑ f, (n f : ℤ) • AngleClass.ofReal (Q.angleOfExtEdge f))
      + (k : ℤ) • AngleClass.ofReal Real.pi

If your angle class already quotients by ℚ * π, then the kπ term vanishes:

lean
∑ e, (m e : ℤ) • ⟦P.angleOfExtEdge e⟧
=
∑ f, (n f : ℤ) • ⟦Q.angleOfExtEdge f⟧

For the regular tetrahedron versus cube, this reduces to:

lean
M • ⟦arccos (1/3)⟧ = 0

with M > 0, contradiction.

Equicomplementability

Formalize equicomplementability by adding common complements.

lean
structure TetEquicomplementable (P Q : SolidWithAngles) : Prop where
  C₁ C₂ : TetSolid
  left  : SolidWithAngles
  right : SolidWithAngles
  left_carrier  : left.carrier = P.carrier ∪ C₁.carrier
  right_carrier : right.carrier = Q.carrier ∪ C₂.carrier
  complements_equidecomp : TetEquidecomp C₁ C₂
  totals_equidecomp : TetEquidecomp left.toTetSolid right.toTetSolid
  complement_edge_balance :
    ComplementPearlBalance P Q C₁ C₂

But the book’s point is that one can avoid proving complement equality manually by adding balance equations.

The strengthened Pearl Lemma should be:

lean
theorem strengthened_pearl_lemma_equicomplementable
  (P Q : SolidWithAngles)
  (E : EquicomplementData P Q) :
  ∃ system : HomogeneousIntegerLinearSystem,
    PositiveRealSolution system ∧
    SystemEquationsEncode
      -- original P external edge coefficients
      -- original Q external edge coefficients
      -- complement pearl-balance constraints

Then Cone Lemma gives a positive integer solution.

A more final statement:

lean
theorem bricard_condition_tetEquicomplementable
  (P Q : SolidWithAngles)
  (h : TetEquicomplementable P Q) :
  ∃ m : P.extEdges → ℕ,
  ∃ n : Q.extEdges → ℕ,
  ∃ k : ℤ,
    (∀ e, 0 < m e) ∧
    (∀ f, 0 < n f) ∧
    ∑ e, (m e : ℤ) • AngleClass.ofReal (P.angleOfExtEdge e)
      =
    ∑ f, (n f : ℤ) • AngleClass.ofReal (Q.angleOfExtEdge f)
      + (k : ℤ) • AngleClass.ofReal Real.pi

Your Cone Lemma suffices because all constraints are homogeneous linear equations:

equality of matched piece-pearl contributions;

equality of complement pearl totals;

cancellation of internal π and 2π terms;

positivity constraints on all external-edge coefficients.

So yes: one homogeneous system is enough.

9. Volume

For the formal headline, this is enough:

lean
theorem regular_tetrahedron_not_scissors_congruent_cube_same_volume :
  ¬ ScissorsCongruent
      (regularTetrahedronCarrier a)
      (cubeCarrier (cubeSideForEqualVolume a))

This is faithful. The book’s examples “same base and height” are a way to ensure equal volume, but Hilbert’s third problem headline is exactly equal-volume non-equidecomposability.

Use MeasureTheory.volume if convenient, but I recommend proving explicit volume formulas first and only then connecting to volume.

Needed lemmas:

lean
lemma volume_tet :
  volume (Tet.carrier T)
    =
  ENNReal.ofReal
    (|det3 (T.v 1 - T.v 0) (T.v 2 - T.v 0) (T.v 3 - T.v 0)| / 6)
lean
lemma volume_regular_tetrahedron :
  volume (regularTetrahedronCarrier a)
    =
  ENNReal.ofReal (Real.sqrt 2 / 12 * a^3)
lean
lemma volume_cube :
  volume (cubeCarrier s)
    =
  ENNReal.ofReal (s^3)
lean
lemma cube_side_for_equal_regularTet_volume :
  0 < a →
  volume (cubeCarrier ((Real.sqrt 2 / 12 * a^3) ^ (1/3)))
    =
  volume (regularTetrahedronCarrier a)

If cube side involving real cube roots is annoying, parameterize the theorem by any s > 0 satisfying equal volume:

lean
theorem regularTet_not_scissors_cube_of_equal_volume
  (ha : 0 < a) (hs : 0 < s)
  (hvol :
    volume (regularTetrahedronCarrier a) = volume (cubeCarrier s)) :
  ¬ ScissorsCongruent (regularTetrahedronCarrier a) (cubeCarrier s)

The proof of non-equidecomposability does not actually use volume; volume only makes the statement faithful.

10. Dependency-ordered lemma list
Layer G0: affine and simplex primitives
lean
def Pt3

Pt3 := EuclideanSpace ℝ (Fin 3).

lean
structure Tet

A tetrahedron is four affinely independent points in Pt3.

lean
def Tet.carrier

The closed convex hull of the four vertices.

lean
def Tet.relInterior

The relative interior of the carrier.

lean
lemma Tet.carrier_convex

The carrier of a tetrahedron is convex.

lean
lemma Tet.carrier_compact

The carrier of a tetrahedron is compact.

lean
lemma Tet.relInterior_nonempty

The relative interior of a nondegenerate tetrahedron is nonempty.

lean
lemma Tet.boundary_decomposes_into_faces

The frontier of a tetrahedron carrier is the union of its four triangular faces.

lean
lemma Tet.edge_face_incidence

Each tetrahedron edge is contained in exactly two tetrahedron faces.

Layer G1: tetrahedral solids and decompositions
lean
structure TetSolid

A finite family of tetrahedra with pairwise disjoint interiors.

lean
def TetSolid.carrier

The union of the carriers of all pieces.

lean
lemma TetSolid.carrier_closed

A tetrahedral solid carrier is closed.

lean
lemma TetSolid.carrier_compact

A tetrahedral solid carrier is compact.

lean
structure TetEquidecomp

Two tetrahedral solids are equidecomposable if their tetrahedral pieces are paired by Euclidean isometries.

lean
lemma TetEquidecomp.volume_eq

Equidecomposable tetrahedral solids have equal volume.

This is optional for the obstruction but useful for sanity.

Layer G2: edges, faces, and dihedral angles
lean
structure Segment3

A nondegenerate closed segment in Pt3.

lean
def Segment3.carrier
def Segment3.relInterior

Closed segment and open segment.

lean
structure Triangle3

A nondegenerate triangle in Pt3.

lean
structure EdgeOcc
structure FaceOcc

Occurrences of tetrahedron edges and faces inside a tetrahedral solid.

lean
def Tet.dihedralAngle

The internal dihedral angle of a tetrahedron along one of its six edges.

lean
lemma Tet.dihedralAngle_pos

A tetrahedral dihedral angle is positive.

lean
lemma Tet.dihedralAngle_lt_pi

A tetrahedral dihedral angle is strictly less than π.

lean
lemma Tet.dihedralAngle_cross_section

The dihedral angle equals the planar sector angle obtained by slicing perpendicular to the edge.

lean
lemma dihedralAngle_isometry_invariant

Euclidean isometries, including reflections, preserve tetrahedral dihedral angles.

Layer G3: external solids with named boundary angles
lean
structure SolidWithAngles extends TetSolid

A tetrahedral solid equipped with a finite list of external edges and an assigned external dihedral angle for each, plus local-model certificates.

lean
def LocalDihedralModel

At a relative interior point of an external edge, the carrier locally equals a wedge with the given angle.

lean
lemma regularTet_solidWithAngles

The regular tetrahedron forms a SolidWithAngles.

lean
lemma cube_solidWithAngles

The cube tetrahedralization forms a SolidWithAngles.

lean
lemma regularTet_all_angles_arccos_one_third

Every external edge of the regular tetrahedron has angle arccos (1/3).

lean
lemma cube_all_angles_pi_div_two

Every external edge of the cube has angle π / 2.

Layer G4: raw edge refinement and pearls
lean
def PieceEdges

The finite set of all tetrahedron edge segments in a tetrahedral solid.

lean
def segmentIntersectionPoints

The finite set of intersection points of two closed segments.

lean
def BreakpointsOnEdge

For a raw edge, the finite set consisting of its endpoints and its intersections with all other raw edges.

lean
def Pearls

The finite set of consecutive subsegments between breakpoints on raw edges.

lean
lemma pearls_finite

There are finitely many pearls.

lean
lemma raw_edge_covered_by_pearls

Every raw edge is the union of its pearls.

lean
lemma pearl_interiors_disjoint

Distinct pearls on the same raw edge have disjoint relative interiors.

lean
lemma incidence_constant_on_pearl

The set of tetrahedron edge occurrences containing an interior point of a pearl is independent of the chosen interior point.

Layer G5: local cross-section geometry
lean
lemma orthogonal_plane_to_segment_exists

At an interior point of a segment, there is a 2D affine plane perpendicular to the segment.

lean
lemma incident_tet_slice_is_sector

The slice of a tetrahedron incident along the pearl is a planar sector.

lean
lemma incident_tet_sector_angle_eq_dihedral

The sector angle in the orthogonal slice equals the tetrahedral dihedral angle.

lean
lemma disjoint_tet_interiors_disjoint_sector_interiors

Disjoint tetrahedron interiors give disjoint sector interiors in the slice.

lean
lemma local_slice_interior_point_full_disk

At a solid interior pearl point, the local slice is a full disk.

lean
lemma local_slice_boundary_facet_halfdisk

At a boundary-facet pearl point, the local slice is a half-disk.

lean
lemma local_slice_external_edge_wedge

At an external-edge pearl point, the local slice is a wedge whose angle is the external dihedral angle.

Layer G6: planar sector sums
lean
structure PlanarSector

A closed sector in a 2D Euclidean plane with a common apex.

lean
def PlanarSector.angle

The angle of a sector in [0, 2π].

lean
lemma planar_sector_angle_nonneg

Sector angles are nonnegative.

lean
lemma planar_sectors_cover_wedge_angle_sum

If finitely many sectors with disjoint interiors cover a wedge of angle θ, their angle sum is θ.

lean
lemma planar_sectors_cover_halfdisk_angle_sum

If they cover a half-disk, their angle sum is π.

lean
lemma planar_sectors_cover_disk_angle_sum

If they cover a full disk, their angle sum is 2π.

Layer G7: Pearl angle classification
lean
def IncidentTetEdges

The tetrahedron edge occurrences whose carriers contain a given pearl.

lean
def PearlAngleSum

The sum of the tetrahedral dihedral angles around a pearl.

lean
lemma pearl_location_trichotomy

Every pearl lies either on an external edge, in a boundary facet interior, or in the solid interior.

lean
lemma pearl_angle_sum_external_edge

If a pearl lies in an external edge e, its incident tetrahedral dihedral angles sum to the external angle at e.

lean
lemma pearl_angle_sum_boundary_facet

If a pearl lies in the relative interior of a boundary facet, its incident tetrahedral dihedral angles sum to π.

lean
lemma pearl_angle_sum_interior

If a pearl lies in the interior of the solid, its incident tetrahedral dihedral angles sum to 2π.

lean
lemma pearl_angle_sum_classification

For every pearl, the angle sum is one of: external edge angle, π, or 2π.

This is the single hardest lemma.

Layer G8: Pearl balance and Bricard condition
lean
def PearlLinearSystem

The homogeneous integer linear system whose variables are pearl weights and whose equations encode equality of matched pieces and complement-balance constraints.

lean
lemma pearl_system_positive_real_solution_equidecomp

An equidecomposition gives a positive real solution to the pearl linear system.

lean
lemma pearl_system_positive_real_solution_equicomplementable

An equicomplementability datum gives a positive real solution to the strengthened pearl linear system.

lean
lemma coneLemma_applied_to_pearl_system

By the already-proven Cone Lemma, the pearl system has a positive integer solution.

lean
theorem bricard_condition_equidecomp

If two SolidWithAngles are tetrahedrally equidecomposable, then there are positive integers multiplying their external dihedral angles such that the two sums differ by an integer multiple of π.

lean
theorem bricard_condition_equicomplementable

The same conclusion holds under tetrahedral equicomplementability, using the strengthened pearl system.

Layer G9: cube and regular tetrahedron instantiation
lean
def regularTetrahedronSolid

The regular tetrahedron as a SolidWithAngles.

lean
def cubeTetSolid

A tetrahedral decomposition of the cube as a SolidWithAngles.

lean
lemma cube_tetrahedralization_carrier

The carrier of the cube tetrahedralization is the closed cube.

lean
lemma regularTet_angle_classes

All regular tetrahedron external angle classes equal ⟦arccos (1/3)⟧.

lean
lemma cube_angle_classes

All cube external angle classes equal ⟦π / 2⟧, hence vanish in the quotient modulo ℚπ.

lean
lemma bricard_regularTet_cube_forces_rational_angle

Bricard’s condition for a regular tetrahedron and cube implies arccos (1/3) is a rational multiple of π.

lean
theorem regularTet_not_tetEquidecomp_cube

A regular tetrahedron is not tetrahedrally equidecomposable with any cube.

lean
theorem regularTet_not_tetEquicomplementable_cube

A regular tetrahedron is not tetrahedrally equicomplementable with any cube.

Layer G10: volume headline
lean
lemma volume_tet

The volume of a tetrahedron is |det| / 6.

lean
lemma volume_regular_tetrahedron

The regular tetrahedron of side length a has volume sqrt 2 / 12 * a^3.

lean
lemma volume_cube

The cube of side length s has volume s^3.

lean
theorem regular_tetrahedron_not_scissors_congruent_cube_equal_volume

For a,s > 0, if the regular tetrahedron of side a and cube of side s have equal volume, then they are not scissors congruent.

lean
theorem hilbert_third_problem_book_headline

There exist two polyhedral solids of equal volume, namely a regular tetrahedron and a cube, that are not equidecomposable and not equicomplementable.

Final scope choice

The minimal honest final layer should prove:

lean
theorem bricard_condition_equidecomp
theorem bricard_condition_equicomplementable
theorem regularTet_not_tetEquidecomp_cube
theorem regularTet_not_tetEquicomplementable_cube
theorem regular_tetrahedron_not_scissors_congruent_cube_equal_volume

Do not spend effort building arbitrary polyhedra. The simplices-only formalization is strong enough for Hilbert’s third problem, faithful to the Pearl/Cone route, and exactly matches the algebraic obstruction layer you already have.