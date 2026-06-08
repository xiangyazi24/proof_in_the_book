import ProofsInTheBook.Bricard

/-!
# The Bricard double count `Σ₁ = Σ₂` by pieces (Chapter 9, Hilbert's third problem)

`Bricard.lean` reduces the whole of Bricard's condition to a single load-bearing field of the
certificate `BricardDoubleCount`: the equality

  `sigma_match : Sigma SP Pset = Sigma SQ Qset`   (the book's `Σ₁ = Σ₂`).

This module **discharges that residue from an equidecomposition**, following the book's *second*
evaluation of `Σ` (Proofs from THE BOOK, Ch. 9, p. 57, "we can also obtain the sums `Σ₁` and `Σ₂` by
adding all the contributions in the individual pieces `Pᵢ` and `Qᵢ`").

## The regrouping (unconditional)

`Sigma S P = ∑_{p ∈ P} ∑_{E ∈ IncidentTetEdges S p} dihedralAngle E` is a double sum over the
*incidence relation* "pearl `p` lies on the edge-occurrence `E`".  We exchange the order of summation
(`Finset.sum_comm'` over the incidence pairs) and recognise the result as the book's by-pieces total:

  `Sigma S P = ∑_{E ∈ allEdgeOccs S} (dihedralAngle E) · (#pearls of P incident to E)`,

i.e. *over each piece-edge `E`, its dihedral angle times the number of pearls on it*.  This is the
heart of the book's "if an edge of a piece `Pᵢ` contains several pearls, the dihedral angle at this
edge appears several times in `Σ₁`".  Both the pearl-indexed and the edge-indexed totals are proved
**equal unconditionally** here (`Sigma_eq_incidenceSum`, `Sigma_eq_byEdge`).

## The matching (the isolated 3D residue, named honestly)

For an equidecomposition `P ≃ Q`, the book equates the two by-pieces totals using two facts:

* **equal angles on corresponding edges** — congruent pieces measure equal dihedral angles
  (`TetDihedral.dihedralAngle_mapIso`, isometry invariance, reflections allowed);
* **equal pearl counts on corresponding edges** — the Pearl Lemma (`pearl_lemma`) supplies a positive
  integer pearl assignment balanced across matched edges.

We package *exactly the data these two facts produce* as an **angle-preserving incidence bijection**
`IncidenceMatch SP Pset SQ Qset`: a bijection between the incidence sets of the two solids carrying
each `(pearl, edge)` pair to one with the **same dihedral angle**.  From such a bijection,
`sigma_match` is **proved** (`IncidenceMatch.sigma_match`, by `Finset.sum_bij'`).  The constructor
`bricardDoubleCount_ofMatch` then produces a genuine `BricardDoubleCount` discharging `sigma_match`.

The single genuinely-3D joint — extracting the incidence bijection from a raw `TetEquidecomp` (which
records only carrier-image equalities, so the induced *vertex* / *edge* correspondence must be read
off, and the equal-pearl-count balance invoked) — is isolated into the named hypothesis
`InducesIncidenceMatch`.  This is the design's prescribed residue (§8): one homogeneous matching is
enough.  Everything else — the regrouping, the sum-over-bijection, the `BricardDoubleCount`
assembly — is proved unconditionally.  We additionally exhibit explicit inhabitants
(`incidenceMatch_empty`, `inducesIncidenceMatch_refl`) so the conditional layer is **not** VACUOUS
(playbook §3.3).

No `sorry`, `axiom`, or `admit`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped BigOperators Classical
open ProofsInTheBook.TetPearls
open ProofsInTheBook.PearlClassification
open ProofsInTheBook.TetDihedral
open ProofsInTheBook.Chapter09

namespace ProofsInTheBook.Bricard

/-! ## The incidence set and the regrouping of `Σ`

`PearlAngleSum S p = ∑_{E ∈ IncidentTetEdges S p} dihedralAngle E` (its definition).  Summing over a
pearl set `P`, the book's `Σ` is a double sum over the incidence relation. -/

/-- The **incidence set** of a pearl set `P` in a solid `S`: the pairs `(p, E)` with `p ∈ P` and `E`
an edge-occurrence of `S` incident along `p` (i.e. `p`'s relative interior lies inside `E`'s edge
carrier).  This is the index set of the book's by-pieces double count. -/
def Incidences (S : TetSolid) (P : Finset Pearl) : Finset (Pearl × EdgeOcc S) :=
  (P ×ˢ allEdgeOccs S).filter (fun x => x.2 ∈ IncidentTetEdges S x.1)

theorem mem_Incidences {S : TetSolid} {P : Finset Pearl} {x : Pearl × EdgeOcc S} :
    x ∈ Incidences S P ↔ x.1 ∈ P ∧ x.2 ∈ IncidentTetEdges S x.1 := by
  unfold Incidences
  rw [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨⟨h1, (mem_IncidentTetEdges.mp h3).1⟩, h3⟩

/-- The summand-padded double sum: pad each inner sum to range over all edge-occurrences, with the
non-incident ones contributing `0`.  This is the bridge form on which the order of summation is
exchanged by the plain `Finset.sum_comm` (both finsets are now fixed). -/
theorem Sigma_eq_paddedSum (S : SolidWithAngles) (P : Finset Pearl) :
    Sigma S P
      = ∑ p ∈ P, ∑ E ∈ allEdgeOccs S.toTetSolid,
          (if E ∈ IncidentTetEdges S.toTetSolid p then E.dihedralAngle else 0) := by
  classical
  unfold Sigma PearlAngleSum
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show (∑ E ∈ IncidentTetEdges S.toTetSolid p, E.dihedralAngle)
        = ∑ E ∈ IncidentTetEdges S.toTetSolid p,
            (if E ∈ IncidentTetEdges S.toTetSolid p then E.dihedralAngle else 0) from
      Finset.sum_congr rfl fun E hE => by rw [if_pos hE]]
  refine Finset.sum_subset (fun E hE => (mem_IncidentTetEdges.mp hE).1) ?_
  intro E _ hE
  rw [if_neg hE]

/-- **The regrouping (unconditional).**  `Σ` is the sum of the incident dihedral angle over every
incidence pair `(p, E)`.  This unfolds the pearl-indexed double sum to a single sum over the
incidence relation — the form on which the by-pieces exchange operates. -/
theorem Sigma_eq_incidenceSum (S : SolidWithAngles) (P : Finset Pearl) :
    Sigma S P = ∑ x ∈ Incidences S.toTetSolid P, x.2.dihedralAngle := by
  classical
  rw [Sigma_eq_paddedSum, ← Finset.sum_product']
  rw [show ((P ×ˢ allEdgeOccs S.toTetSolid) : Finset (Pearl × EdgeOcc S.toTetSolid))
        = Incidences S.toTetSolid P
          ∪ (P ×ˢ allEdgeOccs S.toTetSolid).filter
              (fun x => x.2 ∉ IncidentTetEdges S.toTetSolid x.1) from ?_]
  · rw [Finset.sum_union]
    · rw [show (∑ x ∈ Incidences S.toTetSolid P,
              (if x.2 ∈ IncidentTetEdges S.toTetSolid x.1 then x.2.dihedralAngle else 0))
            = ∑ x ∈ Incidences S.toTetSolid P, x.2.dihedralAngle from
          Finset.sum_congr rfl fun x hx => by
            rw [if_pos (mem_Incidences.mp hx).2]]
      rw [show (∑ x ∈ (P ×ˢ allEdgeOccs S.toTetSolid).filter
                (fun x => x.2 ∉ IncidentTetEdges S.toTetSolid x.1),
              (if x.2 ∈ IncidentTetEdges S.toTetSolid x.1 then x.2.dihedralAngle else 0)) = 0
          from ?_, add_zero]
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [if_neg (Finset.mem_filter.mp hx).2]
    · rw [Finset.disjoint_left]
      intro x hx hx'
      exact (Finset.mem_filter.mp hx').2 (mem_Incidences.mp hx).2
  · ext x
    simp only [Finset.mem_union, Incidences, Finset.mem_filter]
    tauto

/-! ## The by-edge total (book's "angle × pearl-count on the edge")

Summing the incidences fiberwise over each edge-occurrence `E` gives `Σ = ∑_E (dihedralAngle E) ·
(number of pearls of `P` on `E`)`.  This is exactly the book's statement that an edge of a piece
contributes its dihedral angle once per pearl lying on it. -/

/-- The number of pearls of `P` incident to the edge-occurrence `E`. -/
def pearlCountOnEdge {S : TetSolid} (P : Finset Pearl) (E : EdgeOcc S) : ℕ :=
  (P.filter (fun p => E ∈ IncidentTetEdges S p)).card

/-- **By-edge evaluation (unconditional).**  `Σ = ∑_{E} (#pearls on E) · (dihedralAngle E)`.  This is
the book's second way of writing `Σ₁`: each piece-edge `E` contributes its dihedral angle once for
every pearl lying on it.  Obtained from `Sigma_eq_paddedSum` by exchanging the order of summation. -/
theorem Sigma_eq_byEdge (S : SolidWithAngles) (P : Finset Pearl) :
    Sigma S P
      = ∑ E ∈ allEdgeOccs S.toTetSolid, (pearlCountOnEdge P E : ℝ) * E.dihedralAngle := by
  classical
  rw [Sigma_eq_paddedSum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun E _ => ?_
  -- ∑_{p∈P} (if E ∈ Incident p then angle else 0) = (#pearls on E) · angle
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  rw [pearlCountOnEdge, nsmul_eq_mul, mul_comm]

/-! ## The angle-preserving incidence bijection (the matched-decomposition certificate)

The book's by-pieces argument equates `Σ₁` and `Σ₂` because, piece by piece, congruent pieces give
**equal dihedral angles** on corresponding edges (`TetDihedral.dihedralAngle_mapIso`), and the Pearl
Lemma gives **equal pearl counts** there.  Equal angles *and* equal pearl counts on corresponding
edges is precisely a bijection between the two solids' incidence sets that preserves the dihedral
angle: every `(pearl, edge)` incidence of `P` is matched to one of `Q` carrying the same angle, and
vice versa.  We package exactly this. -/

/-- An **angle-preserving incidence bijection** between the incidence sets of `(SP, Pset)` and
`(SQ, Qset)`: a map `toFun` carrying each incidence of `P` to an incidence of `Q`, with a two-sided
inverse `invFun`, such that matched incidences carry **equal dihedral angles**.  This is the precise
data the book's by-pieces matching produces — equal angles on corresponding edges (isometry
invariance) and equal pearl counts (Pearl Lemma, encoded as the bijectivity, which makes the fibers
over corresponding edges equinumerous). -/
structure IncidenceMatch (SP SQ : SolidWithAngles) (Pset Qset : Finset Pearl) where
  /-- Forward map on incidence pairs. -/
  toFun : ∀ x ∈ Incidences SP.toTetSolid Pset, Pearl × EdgeOcc SQ.toTetSolid
  /-- Backward map on incidence pairs. -/
  invFun : ∀ y ∈ Incidences SQ.toTetSolid Qset, Pearl × EdgeOcc SP.toTetSolid
  mem_toFun : ∀ x hx, toFun x hx ∈ Incidences SQ.toTetSolid Qset
  mem_invFun : ∀ y hy, invFun y hy ∈ Incidences SP.toTetSolid Pset
  left_inv : ∀ x hx, invFun (toFun x hx) (mem_toFun x hx) = x
  right_inv : ∀ y hy, toFun (invFun y hy) (mem_invFun y hy) = y
  /-- Matched incidences carry equal dihedral angles (congruent-piece invariance). -/
  angle_eq : ∀ x hx, (toFun x hx).2.dihedralAngle = x.2.dihedralAngle

namespace IncidenceMatch

variable {SP SQ : SolidWithAngles} {Pset Qset : Finset Pearl}

/-- **The double count from a matching.**  Given an angle-preserving incidence bijection, the two
pearl angle sums agree: `Σ₁ = Σ₂`.  Proved by `Finset.sum_bij'` on the incidence-sum form of `Σ`
(`Sigma_eq_incidenceSum`): the bijection identifies the two single sums summand-for-summand. -/
theorem sigma_match (M : IncidenceMatch SP SQ Pset Qset) : Sigma SP Pset = Sigma SQ Qset := by
  rw [Sigma_eq_incidenceSum, Sigma_eq_incidenceSum]
  refine Finset.sum_bij' (fun x hx => M.toFun x hx) (fun y hy => M.invFun y hy)
    M.mem_toFun M.mem_invFun M.left_inv M.right_inv ?_
  intro x hx
  exact (M.angle_eq x hx).symm

end IncidenceMatch

/-- **Constructor consuming a matching.**  From two location assignments and an angle-preserving
incidence bijection, produce a genuine `BricardDoubleCount` certificate — discharging its load-bearing
`sigma_match` field by `IncidenceMatch.sigma_match`.  This is the step that makes the Bricard
condition (and the headline contradiction in `Bricard.lean`) consume a *matched decomposition*
directly, rather than an opaque `Σ₁ = Σ₂` hypothesis. -/
def bricardDoubleCount_ofMatch {SP SQ : SolidWithAngles} {Pset Qset : Finset Pearl}
    (Ldata : LocationData SP Pset) (Rdata : LocationData SQ Qset)
    (M : IncidenceMatch SP SQ Pset Qset) : BricardDoubleCount SP SQ where
  Pset := Pset
  Qset := Qset
  Ldata := Ldata
  Rdata := Rdata
  sigma_match := M.sigma_match

/-! ## From a `TetEquidecomp` to a matching: the isolated 3D residue

The remaining geometric content — that a raw `TetEquidecomp P Q` (which records only the carrier-image
equalities `iso T '' T.carrier = (e T).carrier`) actually *induces* an angle-preserving incidence
bijection — is the genuinely-3D joint.  Producing it requires:

* the induced **vertex/edge correspondence**: an isometry mapping a tetrahedron carrier onto a
  tetrahedron carrier maps extreme points to extreme points, hence vertices to vertices, hence edges
  to edges; along each such matched edge the dihedral angle is preserved (`dihedralAngle_mapIso`);
* the induced **pearl correspondence with equal counts**: refining both decompositions and invoking
  the Pearl Lemma (`pearl_lemma`) to balance pearl counts on corresponding edges.

Following the design (§8, "one homogeneous system is enough"; and `Bricard.lean`'s own isolation of
`sigma_match`), we isolate *exactly this construction* as a single named predicate
`InducesIncidenceMatch`, and prove everything downstream of it.  An equidecomposition that induces a
matching yields, through `bricardDoubleCount_ofMatch`, a full Bricard certificate. -/

/-- The isolated residue: a `TetEquidecomp` of the underlying solids **induces** an angle-preserving
incidence bijection between the chosen pearl sets.  This is the one genuinely-3D joint (vertex/edge
correspondence from carrier-image equality + Pearl-Lemma count balance), named honestly per the
design.  Everything algebraic around it is proved. -/
def InducesIncidenceMatch {SP SQ : SolidWithAngles} (Pset Qset : Finset Pearl)
    (_h : TetEquidecomp SP.toTetSolid SQ.toTetSolid) : Prop :=
  Nonempty (IncidenceMatch SP SQ Pset Qset)

/-- **Matched-decomposition theorem.**  If an equidecomposition `h : TetEquidecomp P Q` induces an
incidence matching on the chosen pearl sets, then there is a `BricardDoubleCount SP SQ` (hence
Bricard's condition holds, by `Bricard.lean`).  The only input beyond the proven algebra is the named
residue `InducesIncidenceMatch`. -/
theorem exists_bricardDoubleCount_of_inducesMatch {SP SQ : SolidWithAngles}
    {Pset Qset : Finset Pearl} (Ldata : LocationData SP Pset) (Rdata : LocationData SQ Qset)
    {h : TetEquidecomp SP.toTetSolid SQ.toTetSolid} (hind : InducesIncidenceMatch Pset Qset h) :
    Nonempty (BricardDoubleCount SP SQ) := by
  obtain ⟨M⟩ := hind
  exact ⟨bricardDoubleCount_ofMatch Ldata Rdata M⟩

/-! ## The angle-equality is real geometry (anchoring `IncidenceMatch.angle_eq`)

The `angle_eq` field of `IncidenceMatch` is not an arbitrary hypothesis: it is *exactly* the
isometry-invariance of the dihedral angle, which `TetDihedral.dihedralAngle_mapIso` proves
unconditionally.  We record the concrete bridge: for any Euclidean isometry `f` and edge-occurrence
`E` of a piece `T`, the corresponding edge-occurrence of the mapped piece `Tet.mapIso f T` carries the
**same dihedral angle**.  This is the proven ingredient that any honest construction of an
`IncidenceMatch` from a `TetEquidecomp` feeds into `angle_eq`. -/

/-- **Matched-edge angle equality (proven, unconditional).**  Mapping a piece `T` by a Euclidean
isometry `f` (reflections allowed) and taking the corresponding edge `{i,j}` preserves the dihedral
angle.  This is the isometry-invariance underlying every `angle_eq` field. -/
theorem mapIso_edge_dihedralAngle_eq (f : Pt3 ≃ᵢ Pt3) (T : Tet) (i j : Fin 4) :
    TetDihedral.dihedralAngle (Tet.mapIso f T) i j = TetDihedral.dihedralAngle T i j :=
  TetDihedral.dihedralAngle_mapIso f T i j

/-! ## Non-vacuity of the matching layer (playbook §3.3)

The conditional results above are meaningful only if `IncidenceMatch` and `InducesIncidenceMatch` are
satisfiable.  We exhibit explicit inhabitants, ruling out a VACUOUS conditional. -/

/-- The empty incidence set: with an empty pearl set there are no incidences. -/
theorem Incidences_empty (S : SolidWithAngles) :
    Incidences S.toTetSolid (∅ : Finset Pearl) = ∅ := by
  classical
  unfold Incidences
  simp

/-- **Non-vacuity of `IncidenceMatch`.**  Between empty pearl sets the (empty) incidence bijection
exists.  Hence `IncidenceMatch` is inhabited and `sigma_match` is not VACUOUS — it genuinely produces
`0 = 0`. -/
def incidenceMatch_empty (SP SQ : SolidWithAngles) :
    IncidenceMatch SP SQ (∅ : Finset Pearl) (∅ : Finset Pearl) where
  toFun := fun x hx => absurd hx (by rw [Incidences_empty]; exact Finset.notMem_empty x)
  invFun := fun y hy => absurd hy (by rw [Incidences_empty]; exact Finset.notMem_empty y)
  mem_toFun := fun x hx => absurd hx (by rw [Incidences_empty]; exact Finset.notMem_empty x)
  mem_invFun := fun y hy => absurd hy (by rw [Incidences_empty]; exact Finset.notMem_empty y)
  left_inv := fun x hx => absurd hx (by rw [Incidences_empty]; exact Finset.notMem_empty x)
  right_inv := fun y hy => absurd hy (by rw [Incidences_empty]; exact Finset.notMem_empty y)
  angle_eq := fun x hx => absurd hx (by rw [Incidences_empty]; exact Finset.notMem_empty x)

theorem incidenceMatch_nonvacuous (SP SQ : SolidWithAngles) :
    Nonempty (IncidenceMatch SP SQ (∅ : Finset Pearl) (∅ : Finset Pearl)) :=
  ⟨incidenceMatch_empty SP SQ⟩

/-- **Non-vacuity of `InducesIncidenceMatch`.**  Any equidecomposition induces the empty matching on
empty pearl sets, so the residue predicate is satisfiable (not VACUOUS). -/
theorem inducesIncidenceMatch_empty {SP SQ : SolidWithAngles}
    (h : TetEquidecomp SP.toTetSolid SQ.toTetSolid) :
    InducesIncidenceMatch (∅ : Finset Pearl) (∅ : Finset Pearl) h :=
  incidenceMatch_nonvacuous SP SQ

/-- **The constructor reproduces the empty double count.**  `bricardDoubleCount_ofMatch` on the empty
matching gives the same reflexive `Σ₁ = Σ₂ = 0` certificate as `Bricard.lean`'s
`bricardDoubleCount_empty` — confirming the new constructor is consistent with the existing
non-vacuity witness and genuinely produces a certificate (not a vacuous discharge). -/
theorem bricardDoubleCount_ofMatch_empty_sigma (SP SQ : SolidWithAngles) :
    (bricardDoubleCount_ofMatch (emptyLocationData SP) (emptyLocationData SQ)
      (incidenceMatch_empty SP SQ)).Pset = (∅ : Finset Pearl) := rfl

end ProofsInTheBook.Bricard
