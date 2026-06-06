import ProofsInTheBook.BricardLocation

/-!
# `CubePearlAngleData`: the per-pearl Kuhn-cube classification (Chapter 9, final geometry)

This module discharges the one remaining honest 3D isolate of the Chapter 9 cube side, named
`BricardLocation.CubePearlAngleData`: a `LocationData cubeSolid (Pearls (PieceEdges cubeSolid.toTetSolid))`,
i.e. a `PearlClassificationCert cubeSolid p` at *every* canonical cube pearl.  Constructing it is the
six-orthoscheme Kuhn dihedral-angle / incidence computation.

## The edge inventory of the Kuhn solid

Every raw edge of the Kuhn solid is a full segment between two cube vertices; by squared length it is
exactly one of three classes (computed coordinate-by-coordinate):

* **cube edge** (`‖b-a‖² = 1`, axis-parallel unit segment): one of the twelve `cubeExtEdges`.  Its
  incident Kuhn dihedral angles sum to `π/2` (either a single orthoscheme contributing `π/2`, or two
  contributing `π/4 + π/4`).  Location: `externalEdge` → target `π/2`.
* **face diagonal** (`‖b-a‖² = 2`): in exactly two orthoschemes, each contributing `π/2`, summing to
  `π`.  Location: `boundaryFacetInterior` → target `π`.
* **space diagonal** (`‖b-a‖² = 3`, the main diagonal `(0,0,0)–(1,1,1)`): in all six orthoschemes,
  each contributing `π/3`, summing to `2π`.  Location: `solidInterior` → target `2π`.

Since the Kuhn solid is non-overlapping (`edgesNonOverlapping_kuhnSolid`), the incident edge
occurrences of a pearl are *exactly* the occurrences whose segment equals the pearl's source edge
(`BricardLocation.mem_IncidentTetEdges_iff_seg_eq`), so the angle sum depends only on the source-edge
class — which we compute per class.

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
open ProofsInTheBook.BricardLocation

namespace ProofsInTheBook.BricardCubePearls

/-! ## Computing the dihedral angle of an explicit tetrahedron from inner products

The dihedral angle `dihedralAngle T i j` is `InnerProductGeometry.angle U W` with
`U = projOut d (v k - v i)`, `W = projOut d (v l - v i)`, `d = v j - v i`, and `{k,l} = otherTwo i j`.
For an *explicit* tetrahedron we compute the six scalar inner products
`dd = ⟪d,d⟫, ud = ⟪u,d⟫, wd = ⟪w,d⟫, uw = ⟪u,w⟫, uu = ⟪u,u⟫, ww = ⟪w,w⟫`
and read off the cosine `(uw - ud*wd/dd) / sqrt((uu - ud²/dd)*(ww - ww²/dd))`. -/

/-- The inner product of two explicit `Pt3` vectors equals the coordinate dot product. -/
theorem inner_pt3 (x y : Pt3) :
    (⟪x, y⟫ : ℝ) = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- **The dihedral-angle value from the three projected inner products.**  With `d = T.v j - T.v i`,
`u = T.v k - T.v i`, `w = T.v l - T.v i` and `{k,l} = otherTwo i j`, let `U = projOut d u`,
`W = projOut d w`.  If `⟪U,U⟫ = uu`, `⟪W,W⟫ = ww` (both positive) and `⟪U,W⟫ = uw`, then the
dihedral angle is `arccos (uw / (√uu · √ww))`. -/
theorem dihedralAngle_eq_arccos {T : Tet} (i j : Fin 4) {uu ww uw : ℝ}
    (hUU : (⟪projOut (T.v j - T.v i) (T.v (otherTwo i j).1 - T.v i),
              projOut (T.v j - T.v i) (T.v (otherTwo i j).1 - T.v i)⟫ : ℝ) = uu)
    (hWW : (⟪projOut (T.v j - T.v i) (T.v (otherTwo i j).2 - T.v i),
              projOut (T.v j - T.v i) (T.v (otherTwo i j).2 - T.v i)⟫ : ℝ) = ww)
    (hUW : (⟪projOut (T.v j - T.v i) (T.v (otherTwo i j).1 - T.v i),
              projOut (T.v j - T.v i) (T.v (otherTwo i j).2 - T.v i)⟫ : ℝ) = uw) :
    dihedralAngle T i j = Real.arccos (uw / (Real.sqrt uu * Real.sqrt ww)) := by
  rw [dihedralAngle, InnerProductGeometry.angle]
  set U := projOut (T.v j - T.v i) (T.v (otherTwo i j).1 - T.v i) with hU
  set W := projOut (T.v j - T.v i) (T.v (otherTwo i j).2 - T.v i) with hW
  congr 1
  rw [hUW]
  have hnU : ‖U‖ = Real.sqrt uu := by
    rw [← Real.sqrt_sq (norm_nonneg U), ← real_inner_self_eq_norm_sq, hUU]
  have hnW : ‖W‖ = Real.sqrt ww := by
    rw [← Real.sqrt_sq (norm_nonneg W), ← real_inner_self_eq_norm_sq, hWW]
  rw [hnU, hnW]

/-! ## The pearl angle sum as a filtered sum over all edge occurrences

For a non-overlapping solid the incident edge occurrences of a canonical pearl `p` are exactly the
occurrences whose segment equals `p.sourceEdge` (`mem_IncidentTetEdges_iff_seg_eq`).  Hence the pearl
angle sum is the sum of `dihedralAngle` over all such occurrences. -/

/-- For a non-overlapping solid, `IncidentTetEdges S p = (allEdgeOccs S).filter (E.seg = p.sourceEdge)`
for a canonical pearl `p`. -/
theorem incidentTetEdges_eq_filter {S : TetSolid} (hno : EdgesNonOverlapping S) {p : Pearl}
    (hp : IsPearlOf (PieceEdges S) p) :
    IncidentTetEdges S p = (allEdgeOccs S).filter (fun E => E.seg = p.sourceEdge) := by
  ext E
  rw [Finset.mem_filter, mem_IncidentTetEdges_iff_seg_eq hno hp]

/-- For a non-overlapping solid, the pearl angle sum is the sum of the dihedral angles over all edge
occurrences whose segment equals the pearl's source edge. -/
theorem pearlAngleSum_eq_filter_sum {S : TetSolid} (hno : EdgesNonOverlapping S) {p : Pearl}
    (hp : IsPearlOf (PieceEdges S) p) :
    PearlAngleSum S p
      = ∑ E ∈ (allEdgeOccs S).filter (fun E => E.seg = p.sourceEdge), E.dihedralAngle := by
  rw [PearlAngleSum, incidentTetEdges_eq_filter hno hp]

/-! ## Per-occurrence dihedral angles of the Kuhn orthoschemes

The dihedral angle along an edge of a Kuhn orthoscheme takes one of three values:
`π/3` (along the space diagonal `0–3`), `π/2` (along a "corner-orthogonal" edge), and `π/4` (along a
cube edge shared by two orthoschemes).  We compute the projected inner products from explicit
coordinates and feed `dihedralAngle_eq_arccos`. -/

/-- Helper: the projected inner product `⟪projOut d u, projOut d w⟫` in closed coordinate form, for
explicit `Pt3` vectors, assuming `d ≠ 0`. -/
theorem inner_projOut_coord (d u w : Pt3) (hd : d ≠ 0) :
    (⟪projOut d u, projOut d w⟫ : ℝ)
      = (u 0 * w 0 + u 1 * w 1 + u 2 * w 2)
        - (u 0 * d 0 + u 1 * d 1 + u 2 * d 2) * (w 0 * d 0 + w 1 * d 1 + w 2 * d 2)
          / (d 0 * d 0 + d 1 * d 1 + d 2 * d 2) := by
  rw [inner_projOut_projOut d u w hd, inner_pt3 u w, inner_pt3 u d, inner_pt3 w d, inner_pt3 d d]

/-- The edge direction of a tetrahedron is nonzero for distinct indices. -/
theorem edgeDir_ne_zero (T : Tet) {i j : Fin 4} (hij : i ≠ j) : T.v j - T.v i ≠ 0 :=
  sub_ne_zero.mpr (fun h => hij (T.v_injective h.symm))

-- **Tactic for a Kuhn dihedral inner-product side goal.**  Given the tet/vertex def names `t v`,
-- discharges one of the three projected-inner-product equalities via `inner_projOut_coord` and
-- coordinate `norm_num`.
macro "kuhn_diheq " t:term ", " v:term : tactic =>
  `(tactic|
    (rw [inner_projOut_coord _ _ _ (by assumption)]
     simp only [$t:term, $v:term, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
       Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
     norm_num))

/-! ### The three arccos targets as named angles -/

theorem arccos_zero_eq (x : ℝ) : Real.arccos (0 / x) = Real.pi / 2 := by
  rw [zero_div, Real.arccos_zero]

theorem arccos_half_eq : Real.arccos ((1/3) / (Real.sqrt (2/3) * Real.sqrt (2/3))) = Real.pi / 3 := by
  rw [← Real.sqrt_mul (by norm_num), show (2:ℝ)/3 * (2/3) = (2/3)^2 by ring,
    Real.sqrt_sq (by norm_num)]
  rw [show ((1:ℝ)/3) / (2/3) = 1/2 by norm_num]
  -- arccos(1/2) = π/3
  have : Real.cos (Real.pi / 3) = 1 / 2 := by
    rw [show Real.pi / 3 = Real.pi / 3 from rfl]
    have := Real.cos_pi_div_three; linarith [this]
  rw [← this, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

theorem arccos_quarter_aux : Real.arccos (1 / Real.sqrt 2) = Real.pi / 4 := by
  have h12 : (1:ℝ) / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    rw [div_eq_div_iff (by positivity) (by norm_num), one_mul,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [h12, ← Real.cos_pi_div_four,
    Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

theorem arccos_quarter_eq :
    Real.arccos ((1) / (Real.sqrt 1 * Real.sqrt 2)) = Real.pi / 4 := by
  rw [Real.sqrt_one, one_mul, arccos_quarter_aux]

theorem arccos_quarter_eq' :
    Real.arccos ((1) / (Real.sqrt 2 * Real.sqrt 1)) = Real.pi / 4 := by
  rw [Real.sqrt_one, mul_one, arccos_quarter_aux]

/-! ### The 36 per-occurrence Kuhn dihedral angles -/

theorem dih_012_01 : dihedralAngle kt012 0 1 = Real.pi / 4 := by
  have hd : kt012.v 1 - kt012.v 0 ≠ 0 := edgeDir_ne_zero kt012 (by decide)
  have hot : otherTwo (0 : Fin 4) 1 = (2, 3) := by decide
  rw [dihedralAngle_eq_arccos 0 1 (uu := 1) (ww := 2) (uw := 1)
    (by rw [hot]; kuhn_diheq kt012, kv012) (by rw [hot]; kuhn_diheq kt012, kv012)
    (by rw [hot]; kuhn_diheq kt012, kv012), arccos_quarter_eq]

theorem dih_012_02 : dihedralAngle kt012 0 2 = Real.pi / 2 := by
  have hd : kt012.v 2 - kt012.v 0 ≠ 0 := edgeDir_ne_zero kt012 (by decide)
  have hot : otherTwo (0 : Fin 4) 2 = (1, 3) := by decide
  rw [dihedralAngle_eq_arccos 0 2 (uu := 1/2) (ww := 1) (uw := 0)
    (by rw [hot]; kuhn_diheq kt012, kv012) (by rw [hot]; kuhn_diheq kt012, kv012)
    (by rw [hot]; kuhn_diheq kt012, kv012), arccos_zero_eq]

theorem dih_012_03 : dihedralAngle kt012 0 3 = Real.pi / 3 := by
  have hd : kt012.v 3 - kt012.v 0 ≠ 0 := edgeDir_ne_zero kt012 (by decide)
  have hot : otherTwo (0 : Fin 4) 3 = (1, 2) := by decide
  rw [dihedralAngle_eq_arccos 0 3 (uu := 2/3) (ww := 2/3) (uw := 1/3)
    (by rw [hot]; kuhn_diheq kt012, kv012) (by rw [hot]; kuhn_diheq kt012, kv012)
    (by rw [hot]; kuhn_diheq kt012, kv012), arccos_half_eq]

theorem dih_012_12 : dihedralAngle kt012 1 2 = Real.pi / 2 := by
  have hd : kt012.v 2 - kt012.v 1 ≠ 0 := edgeDir_ne_zero kt012 (by decide)
  have hot : otherTwo (1 : Fin 4) 2 = (0, 3) := by decide
  rw [dihedralAngle_eq_arccos 1 2 (uu := 1) (ww := 1) (uw := 0)
    (by rw [hot]; kuhn_diheq kt012, kv012) (by rw [hot]; kuhn_diheq kt012, kv012)
    (by rw [hot]; kuhn_diheq kt012, kv012), arccos_zero_eq]

theorem dih_012_13 : dihedralAngle kt012 1 3 = Real.pi / 2 := by
  have hd : kt012.v 3 - kt012.v 1 ≠ 0 := edgeDir_ne_zero kt012 (by decide)
  have hot : otherTwo (1 : Fin 4) 3 = (0, 2) := by decide
  rw [dihedralAngle_eq_arccos 1 3 (uu := 1) (ww := 1/2) (uw := 0)
    (by rw [hot]; kuhn_diheq kt012, kv012) (by rw [hot]; kuhn_diheq kt012, kv012)
    (by rw [hot]; kuhn_diheq kt012, kv012), arccos_zero_eq]

theorem dih_012_23 : dihedralAngle kt012 2 3 = Real.pi / 4 := by
  have hd : kt012.v 3 - kt012.v 2 ≠ 0 := edgeDir_ne_zero kt012 (by decide)
  have hot : otherTwo (2 : Fin 4) 3 = (0, 1) := by decide
  rw [dihedralAngle_eq_arccos 2 3 (uu := 2) (ww := 1) (uw := 1)
    (by rw [hot]; kuhn_diheq kt012, kv012) (by rw [hot]; kuhn_diheq kt012, kv012)
    (by rw [hot]; kuhn_diheq kt012, kv012), arccos_quarter_eq']

theorem dih_021_01 : dihedralAngle kt021 0 1 = Real.pi / 4 := by
  have hd : kt021.v 1 - kt021.v 0 ≠ 0 := edgeDir_ne_zero kt021 (by decide)
  have hot : otherTwo (0 : Fin 4) 1 = (2, 3) := by decide
  rw [dihedralAngle_eq_arccos 0 1 (uu := 1) (ww := 2) (uw := 1)
    (by rw [hot]; kuhn_diheq kt021, kv021) (by rw [hot]; kuhn_diheq kt021, kv021)
    (by rw [hot]; kuhn_diheq kt021, kv021), arccos_quarter_eq]

theorem dih_021_02 : dihedralAngle kt021 0 2 = Real.pi / 2 := by
  have hd : kt021.v 2 - kt021.v 0 ≠ 0 := edgeDir_ne_zero kt021 (by decide)
  have hot : otherTwo (0 : Fin 4) 2 = (1, 3) := by decide
  rw [dihedralAngle_eq_arccos 0 2 (uu := 1/2) (ww := 1) (uw := 0)
    (by rw [hot]; kuhn_diheq kt021, kv021) (by rw [hot]; kuhn_diheq kt021, kv021)
    (by rw [hot]; kuhn_diheq kt021, kv021), arccos_zero_eq]

theorem dih_021_03 : dihedralAngle kt021 0 3 = Real.pi / 3 := by
  have hd : kt021.v 3 - kt021.v 0 ≠ 0 := edgeDir_ne_zero kt021 (by decide)
  have hot : otherTwo (0 : Fin 4) 3 = (1, 2) := by decide
  rw [dihedralAngle_eq_arccos 0 3 (uu := 2/3) (ww := 2/3) (uw := 1/3)
    (by rw [hot]; kuhn_diheq kt021, kv021) (by rw [hot]; kuhn_diheq kt021, kv021)
    (by rw [hot]; kuhn_diheq kt021, kv021), arccos_half_eq]

theorem dih_021_12 : dihedralAngle kt021 1 2 = Real.pi / 2 := by
  have hd : kt021.v 2 - kt021.v 1 ≠ 0 := edgeDir_ne_zero kt021 (by decide)
  have hot : otherTwo (1 : Fin 4) 2 = (0, 3) := by decide
  rw [dihedralAngle_eq_arccos 1 2 (uu := 1) (ww := 1) (uw := 0)
    (by rw [hot]; kuhn_diheq kt021, kv021) (by rw [hot]; kuhn_diheq kt021, kv021)
    (by rw [hot]; kuhn_diheq kt021, kv021), arccos_zero_eq]

theorem dih_021_13 : dihedralAngle kt021 1 3 = Real.pi / 2 := by
  have hd : kt021.v 3 - kt021.v 1 ≠ 0 := edgeDir_ne_zero kt021 (by decide)
  have hot : otherTwo (1 : Fin 4) 3 = (0, 2) := by decide
  rw [dihedralAngle_eq_arccos 1 3 (uu := 1) (ww := 1/2) (uw := 0)
    (by rw [hot]; kuhn_diheq kt021, kv021) (by rw [hot]; kuhn_diheq kt021, kv021)
    (by rw [hot]; kuhn_diheq kt021, kv021), arccos_zero_eq]

theorem dih_021_23 : dihedralAngle kt021 2 3 = Real.pi / 4 := by
  have hd : kt021.v 3 - kt021.v 2 ≠ 0 := edgeDir_ne_zero kt021 (by decide)
  have hot : otherTwo (2 : Fin 4) 3 = (0, 1) := by decide
  rw [dihedralAngle_eq_arccos 2 3 (uu := 2) (ww := 1) (uw := 1)
    (by rw [hot]; kuhn_diheq kt021, kv021) (by rw [hot]; kuhn_diheq kt021, kv021)
    (by rw [hot]; kuhn_diheq kt021, kv021), arccos_quarter_eq']

theorem dih_102_01 : dihedralAngle kt102 0 1 = Real.pi / 4 := by
  have hd : kt102.v 1 - kt102.v 0 ≠ 0 := edgeDir_ne_zero kt102 (by decide)
  have hot : otherTwo (0 : Fin 4) 1 = (2, 3) := by decide
  rw [dihedralAngle_eq_arccos 0 1 (uu := 1) (ww := 2) (uw := 1)
    (by rw [hot]; kuhn_diheq kt102, kv102) (by rw [hot]; kuhn_diheq kt102, kv102)
    (by rw [hot]; kuhn_diheq kt102, kv102), arccos_quarter_eq]

theorem dih_102_02 : dihedralAngle kt102 0 2 = Real.pi / 2 := by
  have hd : kt102.v 2 - kt102.v 0 ≠ 0 := edgeDir_ne_zero kt102 (by decide)
  have hot : otherTwo (0 : Fin 4) 2 = (1, 3) := by decide
  rw [dihedralAngle_eq_arccos 0 2 (uu := 1/2) (ww := 1) (uw := 0)
    (by rw [hot]; kuhn_diheq kt102, kv102) (by rw [hot]; kuhn_diheq kt102, kv102)
    (by rw [hot]; kuhn_diheq kt102, kv102), arccos_zero_eq]

theorem dih_102_03 : dihedralAngle kt102 0 3 = Real.pi / 3 := by
  have hd : kt102.v 3 - kt102.v 0 ≠ 0 := edgeDir_ne_zero kt102 (by decide)
  have hot : otherTwo (0 : Fin 4) 3 = (1, 2) := by decide
  rw [dihedralAngle_eq_arccos 0 3 (uu := 2/3) (ww := 2/3) (uw := 1/3)
    (by rw [hot]; kuhn_diheq kt102, kv102) (by rw [hot]; kuhn_diheq kt102, kv102)
    (by rw [hot]; kuhn_diheq kt102, kv102), arccos_half_eq]

theorem dih_102_12 : dihedralAngle kt102 1 2 = Real.pi / 2 := by
  have hd : kt102.v 2 - kt102.v 1 ≠ 0 := edgeDir_ne_zero kt102 (by decide)
  have hot : otherTwo (1 : Fin 4) 2 = (0, 3) := by decide
  rw [dihedralAngle_eq_arccos 1 2 (uu := 1) (ww := 1) (uw := 0)
    (by rw [hot]; kuhn_diheq kt102, kv102) (by rw [hot]; kuhn_diheq kt102, kv102)
    (by rw [hot]; kuhn_diheq kt102, kv102), arccos_zero_eq]

theorem dih_102_13 : dihedralAngle kt102 1 3 = Real.pi / 2 := by
  have hd : kt102.v 3 - kt102.v 1 ≠ 0 := edgeDir_ne_zero kt102 (by decide)
  have hot : otherTwo (1 : Fin 4) 3 = (0, 2) := by decide
  rw [dihedralAngle_eq_arccos 1 3 (uu := 1) (ww := 1/2) (uw := 0)
    (by rw [hot]; kuhn_diheq kt102, kv102) (by rw [hot]; kuhn_diheq kt102, kv102)
    (by rw [hot]; kuhn_diheq kt102, kv102), arccos_zero_eq]

theorem dih_102_23 : dihedralAngle kt102 2 3 = Real.pi / 4 := by
  have hd : kt102.v 3 - kt102.v 2 ≠ 0 := edgeDir_ne_zero kt102 (by decide)
  have hot : otherTwo (2 : Fin 4) 3 = (0, 1) := by decide
  rw [dihedralAngle_eq_arccos 2 3 (uu := 2) (ww := 1) (uw := 1)
    (by rw [hot]; kuhn_diheq kt102, kv102) (by rw [hot]; kuhn_diheq kt102, kv102)
    (by rw [hot]; kuhn_diheq kt102, kv102), arccos_quarter_eq']

theorem dih_120_01 : dihedralAngle kt120 0 1 = Real.pi / 4 := by
  have hd : kt120.v 1 - kt120.v 0 ≠ 0 := edgeDir_ne_zero kt120 (by decide)
  have hot : otherTwo (0 : Fin 4) 1 = (2, 3) := by decide
  rw [dihedralAngle_eq_arccos 0 1 (uu := 1) (ww := 2) (uw := 1)
    (by rw [hot]; kuhn_diheq kt120, kv120) (by rw [hot]; kuhn_diheq kt120, kv120)
    (by rw [hot]; kuhn_diheq kt120, kv120), arccos_quarter_eq]

theorem dih_120_02 : dihedralAngle kt120 0 2 = Real.pi / 2 := by
  have hd : kt120.v 2 - kt120.v 0 ≠ 0 := edgeDir_ne_zero kt120 (by decide)
  have hot : otherTwo (0 : Fin 4) 2 = (1, 3) := by decide
  rw [dihedralAngle_eq_arccos 0 2 (uu := 1/2) (ww := 1) (uw := 0)
    (by rw [hot]; kuhn_diheq kt120, kv120) (by rw [hot]; kuhn_diheq kt120, kv120)
    (by rw [hot]; kuhn_diheq kt120, kv120), arccos_zero_eq]

theorem dih_120_03 : dihedralAngle kt120 0 3 = Real.pi / 3 := by
  have hd : kt120.v 3 - kt120.v 0 ≠ 0 := edgeDir_ne_zero kt120 (by decide)
  have hot : otherTwo (0 : Fin 4) 3 = (1, 2) := by decide
  rw [dihedralAngle_eq_arccos 0 3 (uu := 2/3) (ww := 2/3) (uw := 1/3)
    (by rw [hot]; kuhn_diheq kt120, kv120) (by rw [hot]; kuhn_diheq kt120, kv120)
    (by rw [hot]; kuhn_diheq kt120, kv120), arccos_half_eq]

theorem dih_120_12 : dihedralAngle kt120 1 2 = Real.pi / 2 := by
  have hd : kt120.v 2 - kt120.v 1 ≠ 0 := edgeDir_ne_zero kt120 (by decide)
  have hot : otherTwo (1 : Fin 4) 2 = (0, 3) := by decide
  rw [dihedralAngle_eq_arccos 1 2 (uu := 1) (ww := 1) (uw := 0)
    (by rw [hot]; kuhn_diheq kt120, kv120) (by rw [hot]; kuhn_diheq kt120, kv120)
    (by rw [hot]; kuhn_diheq kt120, kv120), arccos_zero_eq]

theorem dih_120_13 : dihedralAngle kt120 1 3 = Real.pi / 2 := by
  have hd : kt120.v 3 - kt120.v 1 ≠ 0 := edgeDir_ne_zero kt120 (by decide)
  have hot : otherTwo (1 : Fin 4) 3 = (0, 2) := by decide
  rw [dihedralAngle_eq_arccos 1 3 (uu := 1) (ww := 1/2) (uw := 0)
    (by rw [hot]; kuhn_diheq kt120, kv120) (by rw [hot]; kuhn_diheq kt120, kv120)
    (by rw [hot]; kuhn_diheq kt120, kv120), arccos_zero_eq]

theorem dih_120_23 : dihedralAngle kt120 2 3 = Real.pi / 4 := by
  have hd : kt120.v 3 - kt120.v 2 ≠ 0 := edgeDir_ne_zero kt120 (by decide)
  have hot : otherTwo (2 : Fin 4) 3 = (0, 1) := by decide
  rw [dihedralAngle_eq_arccos 2 3 (uu := 2) (ww := 1) (uw := 1)
    (by rw [hot]; kuhn_diheq kt120, kv120) (by rw [hot]; kuhn_diheq kt120, kv120)
    (by rw [hot]; kuhn_diheq kt120, kv120), arccos_quarter_eq']

theorem dih_201_01 : dihedralAngle kt201 0 1 = Real.pi / 4 := by
  have hd : kt201.v 1 - kt201.v 0 ≠ 0 := edgeDir_ne_zero kt201 (by decide)
  have hot : otherTwo (0 : Fin 4) 1 = (2, 3) := by decide
  rw [dihedralAngle_eq_arccos 0 1 (uu := 1) (ww := 2) (uw := 1)
    (by rw [hot]; kuhn_diheq kt201, kv201) (by rw [hot]; kuhn_diheq kt201, kv201)
    (by rw [hot]; kuhn_diheq kt201, kv201), arccos_quarter_eq]

theorem dih_201_02 : dihedralAngle kt201 0 2 = Real.pi / 2 := by
  have hd : kt201.v 2 - kt201.v 0 ≠ 0 := edgeDir_ne_zero kt201 (by decide)
  have hot : otherTwo (0 : Fin 4) 2 = (1, 3) := by decide
  rw [dihedralAngle_eq_arccos 0 2 (uu := 1/2) (ww := 1) (uw := 0)
    (by rw [hot]; kuhn_diheq kt201, kv201) (by rw [hot]; kuhn_diheq kt201, kv201)
    (by rw [hot]; kuhn_diheq kt201, kv201), arccos_zero_eq]

theorem dih_201_03 : dihedralAngle kt201 0 3 = Real.pi / 3 := by
  have hd : kt201.v 3 - kt201.v 0 ≠ 0 := edgeDir_ne_zero kt201 (by decide)
  have hot : otherTwo (0 : Fin 4) 3 = (1, 2) := by decide
  rw [dihedralAngle_eq_arccos 0 3 (uu := 2/3) (ww := 2/3) (uw := 1/3)
    (by rw [hot]; kuhn_diheq kt201, kv201) (by rw [hot]; kuhn_diheq kt201, kv201)
    (by rw [hot]; kuhn_diheq kt201, kv201), arccos_half_eq]

theorem dih_201_12 : dihedralAngle kt201 1 2 = Real.pi / 2 := by
  have hd : kt201.v 2 - kt201.v 1 ≠ 0 := edgeDir_ne_zero kt201 (by decide)
  have hot : otherTwo (1 : Fin 4) 2 = (0, 3) := by decide
  rw [dihedralAngle_eq_arccos 1 2 (uu := 1) (ww := 1) (uw := 0)
    (by rw [hot]; kuhn_diheq kt201, kv201) (by rw [hot]; kuhn_diheq kt201, kv201)
    (by rw [hot]; kuhn_diheq kt201, kv201), arccos_zero_eq]

theorem dih_201_13 : dihedralAngle kt201 1 3 = Real.pi / 2 := by
  have hd : kt201.v 3 - kt201.v 1 ≠ 0 := edgeDir_ne_zero kt201 (by decide)
  have hot : otherTwo (1 : Fin 4) 3 = (0, 2) := by decide
  rw [dihedralAngle_eq_arccos 1 3 (uu := 1) (ww := 1/2) (uw := 0)
    (by rw [hot]; kuhn_diheq kt201, kv201) (by rw [hot]; kuhn_diheq kt201, kv201)
    (by rw [hot]; kuhn_diheq kt201, kv201), arccos_zero_eq]

theorem dih_201_23 : dihedralAngle kt201 2 3 = Real.pi / 4 := by
  have hd : kt201.v 3 - kt201.v 2 ≠ 0 := edgeDir_ne_zero kt201 (by decide)
  have hot : otherTwo (2 : Fin 4) 3 = (0, 1) := by decide
  rw [dihedralAngle_eq_arccos 2 3 (uu := 2) (ww := 1) (uw := 1)
    (by rw [hot]; kuhn_diheq kt201, kv201) (by rw [hot]; kuhn_diheq kt201, kv201)
    (by rw [hot]; kuhn_diheq kt201, kv201), arccos_quarter_eq']

theorem dih_210_01 : dihedralAngle kt210 0 1 = Real.pi / 4 := by
  have hd : kt210.v 1 - kt210.v 0 ≠ 0 := edgeDir_ne_zero kt210 (by decide)
  have hot : otherTwo (0 : Fin 4) 1 = (2, 3) := by decide
  rw [dihedralAngle_eq_arccos 0 1 (uu := 1) (ww := 2) (uw := 1)
    (by rw [hot]; kuhn_diheq kt210, kv210) (by rw [hot]; kuhn_diheq kt210, kv210)
    (by rw [hot]; kuhn_diheq kt210, kv210), arccos_quarter_eq]

theorem dih_210_02 : dihedralAngle kt210 0 2 = Real.pi / 2 := by
  have hd : kt210.v 2 - kt210.v 0 ≠ 0 := edgeDir_ne_zero kt210 (by decide)
  have hot : otherTwo (0 : Fin 4) 2 = (1, 3) := by decide
  rw [dihedralAngle_eq_arccos 0 2 (uu := 1/2) (ww := 1) (uw := 0)
    (by rw [hot]; kuhn_diheq kt210, kv210) (by rw [hot]; kuhn_diheq kt210, kv210)
    (by rw [hot]; kuhn_diheq kt210, kv210), arccos_zero_eq]

theorem dih_210_03 : dihedralAngle kt210 0 3 = Real.pi / 3 := by
  have hd : kt210.v 3 - kt210.v 0 ≠ 0 := edgeDir_ne_zero kt210 (by decide)
  have hot : otherTwo (0 : Fin 4) 3 = (1, 2) := by decide
  rw [dihedralAngle_eq_arccos 0 3 (uu := 2/3) (ww := 2/3) (uw := 1/3)
    (by rw [hot]; kuhn_diheq kt210, kv210) (by rw [hot]; kuhn_diheq kt210, kv210)
    (by rw [hot]; kuhn_diheq kt210, kv210), arccos_half_eq]

theorem dih_210_12 : dihedralAngle kt210 1 2 = Real.pi / 2 := by
  have hd : kt210.v 2 - kt210.v 1 ≠ 0 := edgeDir_ne_zero kt210 (by decide)
  have hot : otherTwo (1 : Fin 4) 2 = (0, 3) := by decide
  rw [dihedralAngle_eq_arccos 1 2 (uu := 1) (ww := 1) (uw := 0)
    (by rw [hot]; kuhn_diheq kt210, kv210) (by rw [hot]; kuhn_diheq kt210, kv210)
    (by rw [hot]; kuhn_diheq kt210, kv210), arccos_zero_eq]

theorem dih_210_13 : dihedralAngle kt210 1 3 = Real.pi / 2 := by
  have hd : kt210.v 3 - kt210.v 1 ≠ 0 := edgeDir_ne_zero kt210 (by decide)
  have hot : otherTwo (1 : Fin 4) 3 = (0, 2) := by decide
  rw [dihedralAngle_eq_arccos 1 3 (uu := 1) (ww := 1/2) (uw := 0)
    (by rw [hot]; kuhn_diheq kt210, kv210) (by rw [hot]; kuhn_diheq kt210, kv210)
    (by rw [hot]; kuhn_diheq kt210, kv210), arccos_zero_eq]

theorem dih_210_23 : dihedralAngle kt210 2 3 = Real.pi / 4 := by
  have hd : kt210.v 3 - kt210.v 2 ≠ 0 := edgeDir_ne_zero kt210 (by decide)
  have hot : otherTwo (2 : Fin 4) 3 = (0, 1) := by decide
  rw [dihedralAngle_eq_arccos 2 3 (uu := 2) (ww := 1) (uw := 1)
    (by rw [hot]; kuhn_diheq kt210, kv210) (by rw [hot]; kuhn_diheq kt210, kv210)
    (by rw [hot]; kuhn_diheq kt210, kv210), arccos_quarter_eq']


/-! ## Summing over all edge occurrences of the Kuhn solid

`allEdgeOccs S = S.pieces.attach.biUnion (fun T => edgePairs.attach.image (mkOcc T ·))`.  We decompose
any sum over `allEdgeOccs` into a double sum over the (6) pieces and their (6) edge pairs, using the
disjointness of the per-piece images (occurrences from different pieces differ in their `.T` field)
and the injectivity of the pair-to-occurrence map within a piece. -/

/-- The edge occurrence of a Kuhn piece for an ordered pair. -/
def mkOcc (T : Tet) (hT : T ∈ kuhnSolid.pieces) (q : Fin 4 × Fin 4) (h : q.1 < q.2) :
    EdgeOcc kuhnSolid := ⟨T, hT, q.1, q.2, h⟩

/-- A sum over `allEdgeOccs kuhnSolid` decomposes into a sum over pieces and edge pairs. -/
theorem sum_allEdgeOccs_kuhn (g : EdgeOcc kuhnSolid → ℝ) :
    ∑ E ∈ allEdgeOccs kuhnSolid, g E
      = ∑ T ∈ kuhnSolid.pieces.attach, ∑ q ∈ Tet.edgePairs.attach,
          g (mkOcc T.1 T.2 q.1 (edgePairs_lt q.2)) := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑kuhnSolid.pieces.attach)
      (fun (T : kuhnSolid.pieces) => (Tet.edgePairs.attach).image
        (fun p => (⟨T.val, T.property, p.val.1, p.val.2, edgePairs_lt p.property⟩ : EdgeOcc kuhnSolid))) := by
    intro T _ T' _ hTT'
    rw [Function.onFun, Finset.disjoint_left]
    rintro E hE hE'
    rw [Finset.mem_image] at hE hE'
    obtain ⟨q, _, hq⟩ := hE
    obtain ⟨q', _, hq'⟩ := hE'
    have hTeq : (T : Tet) = (T' : Tet) := by
      have h1 : E.T = (T : Tet) := by rw [← hq]
      have h2 : E.T = (T' : Tet) := by rw [← hq']
      rw [← h1, h2]
    exact hTT' (Subtype.ext hTeq)
  rw [allEdgeOccs, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [Finset.sum_image]
  · rfl
  · -- injectivity of the pair → occurrence map within a piece
    intro q _ q' _ hqq
    have hi : q.1.1 = q'.1.1 := congrArg EdgeOcc.i hqq
    have hj : q.1.2 = q'.1.2 := congrArg EdgeOcc.j hqq
    exact Subtype.ext (Prod.ext hi hj)

/-- The dihedral angle of `mkOcc T hT q h` is `dihedralAngle T q.1 q.2`. -/
@[simp] theorem mkOcc_dihedralAngle (T : Tet) (hT : T ∈ kuhnSolid.pieces) (q : Fin 4 × Fin 4)
    (h : q.1 < q.2) : (mkOcc T hT q h).dihedralAngle = dihedralAngle T q.1 q.2 := rfl

/-- The segment of `mkOcc T hT q h` has endpoints `T.v q.1`, `T.v q.2`. -/
@[simp] theorem mkOcc_seg_a (T : Tet) (hT : T ∈ kuhnSolid.pieces) (q : Fin 4 × Fin 4)
    (h : q.1 < q.2) : (mkOcc T hT q h).seg.a = T.v q.1 := rfl

@[simp] theorem mkOcc_seg_b (T : Tet) (hT : T ∈ kuhnSolid.pieces) (q : Fin 4 × Fin 4)
    (h : q.1 < q.2) : (mkOcc T hT q h).seg.b = T.v q.2 := rfl

/-- Two segments are equal iff their endpoints coincide (the nondegeneracy proof is irrelevant). -/
theorem segment3_eq_iff {s t : Segment3} : s = t ↔ s.a = t.a ∧ s.b = t.b := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨ha, hb⟩; cases s; cases t; simp_all

/-- `mkOcc T hT q h).seg = e` iff `T.v q.1 = e.a ∧ T.v q.2 = e.b`. -/
theorem mkOcc_seg_eq_iff (T : Tet) (hT : T ∈ kuhnSolid.pieces) (q : Fin 4 × Fin 4)
    (h : q.1 < q.2) (e : Segment3) :
    (mkOcc T hT q h).seg = e ↔ T.v q.1 = e.a ∧ T.v q.2 = e.b := by
  rw [segment3_eq_iff]
  exact Iff.rfl

/-- **The Kuhn pearl angle sum as an explicit 36-term coordinate expression.**  For a canonical pearl
`p` of the Kuhn solid, the angle sum is the sum over the six pieces and six edge pairs of the
occurrence's dihedral angle, gated by whether that occurrence's segment equals `p.sourceEdge`. -/
theorem pearlAngleSum_kuhn_expand {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p) :
    PearlAngleSum kuhnSolid p
      = ∑ T ∈ kuhnSolid.pieces.attach, ∑ q ∈ Tet.edgePairs.attach,
          (if (mkOcc T.1 T.2 q.1 (edgePairs_lt q.2)).seg = p.sourceEdge
            then dihedralAngle T.1 q.1.1 q.1.2 else 0) := by
  rw [pearlAngleSum_eq_filter_sum edgesNonOverlapping_kuhnSolid hp, Finset.sum_filter,
    sum_allEdgeOccs_kuhn (fun E => if E.seg = p.sourceEdge then E.dihedralAngle else 0)]
  refine Finset.sum_congr rfl (fun T _ => Finset.sum_congr rfl (fun q _ => ?_))
  simp only [mkOcc_dihedralAngle]

/-! ### Expanding the attach-sums over the six pieces and six pairs -/

theorem kt012_notMem : (kt012 : Tet) ∉ ({kt021, kt102, kt120, kt201, kt210} : Finset Tet) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨kt012_ne_kt021, kt012_ne_kt102, kt012_ne_kt120, kt012_ne_kt201, kt012_ne_kt210⟩

theorem kt021_notMem : (kt021 : Tet) ∉ ({kt102, kt120, kt201, kt210} : Finset Tet) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨kt021_ne_kt102, kt021_ne_kt120, kt021_ne_kt201, kt021_ne_kt210⟩

theorem kt102_notMem : (kt102 : Tet) ∉ ({kt120, kt201, kt210} : Finset Tet) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨kt102_ne_kt120, kt102_ne_kt201, kt102_ne_kt210⟩

theorem kt120_notMem : (kt120 : Tet) ∉ ({kt201, kt210} : Finset Tet) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨kt120_ne_kt201, kt120_ne_kt210⟩

theorem kt201_notMem : (kt201 : Tet) ∉ ({kt210} : Finset Tet) := by
  simp only [Finset.mem_singleton]
  exact kt201_ne_kt210

/-- Expand a sum over `kuhnSolid.pieces.attach` (with a membership-dependent summand) into the six
explicit pieces. -/
theorem sum_pieces_attach (F : (T : Tet) → T ∈ kuhnSolid.pieces → ℝ) :
    ∑ T ∈ kuhnSolid.pieces.attach, F T.1 T.2
      = F kt012 (by simp) + F kt021 (by simp) + F kt102 (by simp) + F kt120 (by simp) +
        F kt201 (by simp) + F kt210 (by simp) := by
  classical
  rw [show (∑ T ∈ kuhnSolid.pieces.attach, F T.1 T.2)
      = ∑ T ∈ kuhnSolid.pieces.attach,
          (fun T' : Tet => if h : T' ∈ kuhnSolid.pieces then F T' h else 0) T.1 from
    Finset.sum_congr rfl (fun T _ => by simp only; rw [dif_pos T.2])]
  rw [Finset.sum_attach kuhnSolid.pieces
    (fun T' => if h : T' ∈ kuhnSolid.pieces then F T' h else 0)]
  simp only [kuhnSolid_pieces]
  rw [Finset.sum_insert kt012_notMem, Finset.sum_insert kt021_notMem,
    Finset.sum_insert kt102_notMem, Finset.sum_insert kt120_notMem,
    Finset.sum_insert kt201_notMem, Finset.sum_singleton]
  rw [dif_pos (by simp), dif_pos (by simp), dif_pos (by simp), dif_pos (by simp),
    dif_pos (by simp), dif_pos (by simp)]
  ring

/-- Expand a sum over `Tet.edgePairs.attach` into the six explicit ordered pairs. -/
theorem sum_edgePairs_attach (g : Fin 4 × Fin 4 → ℝ) :
    ∑ q ∈ Tet.edgePairs.attach, g q.1
      = g (0, 1) + g (0, 2) + g (0, 3) + g (1, 2) + g (1, 3) + g (2, 3) := by
  rw [Finset.sum_attach Tet.edgePairs (fun q => g q)]
  rw [show Tet.edgePairs = {((0 : Fin 4), (1 : Fin 4)), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)}
    from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- The inner edge-pair sum over one Kuhn piece, expanded into its six ordered pairs with the
occurrence-segment conditions rewritten to coordinate form. -/
theorem inner_pair_sum (T : Tet) (hT : T ∈ kuhnSolid.pieces) (e : Segment3) :
    (∑ q ∈ Tet.edgePairs.attach,
        (if (mkOcc T hT q.1 (edgePairs_lt q.2)).seg = e then dihedralAngle T q.1.1 q.1.2 else 0))
      = (if T.v 0 = e.a ∧ T.v 1 = e.b then dihedralAngle T 0 1 else 0)
      + (if T.v 0 = e.a ∧ T.v 2 = e.b then dihedralAngle T 0 2 else 0)
      + (if T.v 0 = e.a ∧ T.v 3 = e.b then dihedralAngle T 0 3 else 0)
      + (if T.v 1 = e.a ∧ T.v 2 = e.b then dihedralAngle T 1 2 else 0)
      + (if T.v 1 = e.a ∧ T.v 3 = e.b then dihedralAngle T 1 3 else 0)
      + (if T.v 2 = e.a ∧ T.v 3 = e.b then dihedralAngle T 2 3 else 0) := by
  rw [show (∑ q ∈ Tet.edgePairs.attach,
        (if (mkOcc T hT q.1 (edgePairs_lt q.2)).seg = e then dihedralAngle T q.1.1 q.1.2 else 0))
      = ∑ q ∈ Tet.edgePairs.attach,
          (if T.v q.1.1 = e.a ∧ T.v q.1.2 = e.b then dihedralAngle T q.1.1 q.1.2 else 0) from
    Finset.sum_congr rfl (fun q _ => by simp only [mkOcc_seg_eq_iff])]
  rw [sum_edgePairs_attach (fun pr : Fin 4 × Fin 4 =>
    if T.v pr.1 = e.a ∧ T.v pr.2 = e.b then dihedralAngle T pr.1 pr.2 else 0)]

/-- **The Kuhn pearl angle sum, fully expanded over the six orthoschemes (36 occurrences).**  Each
edge occurrence contributes its (proven) dihedral angle exactly when its segment equals the pearl's
source edge.  This is the master coordinate identity from which every per-class angle sum follows. -/
theorem pearlAngleSum_kuhn_terms {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p) :
    PearlAngleSum kuhnSolid p
      = (if (kt012.v 0 = p.sourceEdge.a ∧ kt012.v 1 = p.sourceEdge.b) then Real.pi / 4 else 0) +
        (if (kt012.v 0 = p.sourceEdge.a ∧ kt012.v 2 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt012.v 0 = p.sourceEdge.a ∧ kt012.v 3 = p.sourceEdge.b) then Real.pi / 3 else 0) +
        (if (kt012.v 1 = p.sourceEdge.a ∧ kt012.v 2 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt012.v 1 = p.sourceEdge.a ∧ kt012.v 3 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt012.v 2 = p.sourceEdge.a ∧ kt012.v 3 = p.sourceEdge.b) then Real.pi / 4 else 0) +
        (if (kt021.v 0 = p.sourceEdge.a ∧ kt021.v 1 = p.sourceEdge.b) then Real.pi / 4 else 0) +
        (if (kt021.v 0 = p.sourceEdge.a ∧ kt021.v 2 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt021.v 0 = p.sourceEdge.a ∧ kt021.v 3 = p.sourceEdge.b) then Real.pi / 3 else 0) +
        (if (kt021.v 1 = p.sourceEdge.a ∧ kt021.v 2 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt021.v 1 = p.sourceEdge.a ∧ kt021.v 3 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt021.v 2 = p.sourceEdge.a ∧ kt021.v 3 = p.sourceEdge.b) then Real.pi / 4 else 0) +
        (if (kt102.v 0 = p.sourceEdge.a ∧ kt102.v 1 = p.sourceEdge.b) then Real.pi / 4 else 0) +
        (if (kt102.v 0 = p.sourceEdge.a ∧ kt102.v 2 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt102.v 0 = p.sourceEdge.a ∧ kt102.v 3 = p.sourceEdge.b) then Real.pi / 3 else 0) +
        (if (kt102.v 1 = p.sourceEdge.a ∧ kt102.v 2 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt102.v 1 = p.sourceEdge.a ∧ kt102.v 3 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt102.v 2 = p.sourceEdge.a ∧ kt102.v 3 = p.sourceEdge.b) then Real.pi / 4 else 0) +
        (if (kt120.v 0 = p.sourceEdge.a ∧ kt120.v 1 = p.sourceEdge.b) then Real.pi / 4 else 0) +
        (if (kt120.v 0 = p.sourceEdge.a ∧ kt120.v 2 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt120.v 0 = p.sourceEdge.a ∧ kt120.v 3 = p.sourceEdge.b) then Real.pi / 3 else 0) +
        (if (kt120.v 1 = p.sourceEdge.a ∧ kt120.v 2 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt120.v 1 = p.sourceEdge.a ∧ kt120.v 3 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt120.v 2 = p.sourceEdge.a ∧ kt120.v 3 = p.sourceEdge.b) then Real.pi / 4 else 0) +
        (if (kt201.v 0 = p.sourceEdge.a ∧ kt201.v 1 = p.sourceEdge.b) then Real.pi / 4 else 0) +
        (if (kt201.v 0 = p.sourceEdge.a ∧ kt201.v 2 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt201.v 0 = p.sourceEdge.a ∧ kt201.v 3 = p.sourceEdge.b) then Real.pi / 3 else 0) +
        (if (kt201.v 1 = p.sourceEdge.a ∧ kt201.v 2 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt201.v 1 = p.sourceEdge.a ∧ kt201.v 3 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt201.v 2 = p.sourceEdge.a ∧ kt201.v 3 = p.sourceEdge.b) then Real.pi / 4 else 0) +
        (if (kt210.v 0 = p.sourceEdge.a ∧ kt210.v 1 = p.sourceEdge.b) then Real.pi / 4 else 0) +
        (if (kt210.v 0 = p.sourceEdge.a ∧ kt210.v 2 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt210.v 0 = p.sourceEdge.a ∧ kt210.v 3 = p.sourceEdge.b) then Real.pi / 3 else 0) +
        (if (kt210.v 1 = p.sourceEdge.a ∧ kt210.v 2 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt210.v 1 = p.sourceEdge.a ∧ kt210.v 3 = p.sourceEdge.b) then Real.pi / 2 else 0) +
        (if (kt210.v 2 = p.sourceEdge.a ∧ kt210.v 3 = p.sourceEdge.b) then Real.pi / 4 else 0) := by
  rw [pearlAngleSum_kuhn_expand hp]
  rw [sum_pieces_attach (fun T hT => ∑ q ∈ Tet.edgePairs.attach,
    (if (mkOcc T hT q.1 (edgePairs_lt q.2)).seg = p.sourceEdge then dihedralAngle T q.1.1 q.1.2 else 0))]
  rw [inner_pair_sum, inner_pair_sum, inner_pair_sum, inner_pair_sum, inner_pair_sum,
    inner_pair_sum]
  simp only [dih_012_01, dih_012_02, dih_012_03, dih_012_12, dih_012_13, dih_012_23, dih_021_01, dih_021_02, dih_021_03, dih_021_12, dih_021_13, dih_021_23, dih_102_01, dih_102_02, dih_102_03, dih_102_12, dih_102_13, dih_102_23, dih_120_01, dih_120_02, dih_120_03, dih_120_12, dih_120_13, dih_120_23, dih_201_01, dih_201_02, dih_201_03, dih_201_12, dih_201_13, dih_201_23, dih_210_01, dih_210_02, dih_210_03, dih_210_12, dih_210_13, dih_210_23]
  ring

/-! ## The per-class angle sums

Plugging the source edge's coordinates into the 36-term identity collapses all but the matching
occurrences.  We record the three class values.  The Kuhn vertices are cube vertices, so each
condition `ktσ.v i = e.a` is a coordinate equality decidable by `norm_num` once `e`'s endpoints are
concrete. -/

/-- Coordinate helper: a Kuhn vertex equals a given explicit cube point iff their three coordinates
agree; reduces a point equality `ktσ.v i = !₂[a,b,c]` to numerals. -/
theorem kuhnVertex_eq_iff (x y : Pt3) :
    x = y ↔ x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2⟩
    apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
    funext i; fin_cases i <;> assumption

example {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(0:ℝ),0,0]) (hb : p.sourceEdge.b = !₂[(1:ℝ),1,1]) :
    PearlAngleSum kuhnSolid p = SectorSum.twoPi := by
  rw [pearlAngleSum_kuhn_terms hp, ha, hb, SectorSum.twoPi]
  simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
    kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  norm_num
  ring


/-! ## The Kuhn solid carrier is the unit cube -/

/-- The closed unit cube `[0,1]³` as a subset of `Pt3`. -/
def closedCube : Set Pt3 := {x | ∀ i : Fin 3, x i ∈ Set.Icc (0:ℝ) 1}

/-- The open unit cube `(0,1)³`. -/
def openCube : Set Pt3 := {x | ∀ i : Fin 3, x i ∈ Set.Ioo (0:ℝ) 1}

theorem closedCube_convex : Convex ℝ closedCube := by
  intro x hx y hy s t hs ht hst
  intro i
  have hxi := hx i; have hyi := hy i
  simp only [Set.mem_Icc] at hxi hyi ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  constructor
  · nlinarith [hxi.1, hyi.1, hs, ht]
  · nlinarith [hxi.2, hyi.2, hs, ht, hst]

/-- Every Kuhn piece's carrier is contained in the closed unit cube. -/
theorem kt_carrier_subset_cube {T : Tet} (hT : T ∈ kuhnSolid.pieces) :
    T.carrier ⊆ closedCube := by
  apply convexHull_min _ closedCube_convex
  rintro y ⟨k, rfl⟩
  intro c
  have := kuhn_vertex_isCubeVertex hT k c
  rcases this with h | h <;> rw [h] <;> norm_num

/-- The Kuhn solid carrier is contained in the closed unit cube. -/
theorem kuhnSolid_carrier_subset_cube : kuhnSolid.carrier ⊆ closedCube := by
  rw [TetSolid.carrier]
  apply Set.iUnion₂_subset
  intro T hT
  exact kt_carrier_subset_cube hT


/-- A point that is a nonnegative-weight convex combination (weights summing to 1) of a
tetrahedron's four vertices lies in its carrier. -/
theorem tet_mem_carrier_of_weights (T : Tet) (w : Fin 4 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (x : Pt3) (hx : x = ∑ i, w i • T.v i) : x ∈ T.carrier := by
  rw [Tet.carrier, hx]
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 4)), T.v i ∈ Set.range T.v :=
    fun i _ => Set.mem_range_self i
  have := Finset.centerMass_mem_convexHull (Finset.univ) (fun i _ => hw i)
    (by rw [hsum]; norm_num) (z := T.v) hz
  rwa [Finset.centerMass, hsum, inv_one, one_smul] at this


theorem mem_kt012_of_order (x : Pt3) (hx : x ∈ closedCube)
    (h1 : x 1 ≤ x 0) (h2 : x 2 ≤ x 1) : x ∈ kt012.carrier := by
  apply tet_mem_carrier_of_weights kt012 ![1 - x 0, x 0 - x 1, x 1 - x 2, x 2]
    (by obtain ⟨hx0l, hx0r⟩ := hx 0; obtain ⟨hx1l, hx1r⟩ := hx 1; obtain ⟨hx2l, hx2r⟩ := hx 2;
        intro i; fin_cases i <;> simp only [List.ofFn, Matrix.cons_val] <;> norm_num <;> linarith)
    (by simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]; ring)
  rw [kuhnVertex_eq_iff]
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [Fin.sum_univ_four]
    simp only [kt012, kv012, Tet.v, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons]
    ring

theorem mem_kt021_of_order (x : Pt3) (hx : x ∈ closedCube)
    (h1 : x 2 ≤ x 0) (h2 : x 1 ≤ x 2) : x ∈ kt021.carrier := by
  apply tet_mem_carrier_of_weights kt021 ![1 - x 0, x 0 - x 2, x 2 - x 1, x 1]
    (by obtain ⟨hx0l, hx0r⟩ := hx 0; obtain ⟨hx1l, hx1r⟩ := hx 1; obtain ⟨hx2l, hx2r⟩ := hx 2;
        intro i; fin_cases i <;> simp only [List.ofFn, Matrix.cons_val] <;> norm_num <;> linarith)
    (by simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]; ring)
  rw [kuhnVertex_eq_iff]
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [Fin.sum_univ_four]
    simp only [kt021, kv021, Tet.v, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons]
    ring

theorem mem_kt102_of_order (x : Pt3) (hx : x ∈ closedCube)
    (h1 : x 0 ≤ x 1) (h2 : x 2 ≤ x 0) : x ∈ kt102.carrier := by
  apply tet_mem_carrier_of_weights kt102 ![1 - x 1, x 1 - x 0, x 0 - x 2, x 2]
    (by obtain ⟨hx0l, hx0r⟩ := hx 0; obtain ⟨hx1l, hx1r⟩ := hx 1; obtain ⟨hx2l, hx2r⟩ := hx 2;
        intro i; fin_cases i <;> simp only [List.ofFn, Matrix.cons_val] <;> norm_num <;> linarith)
    (by simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]; ring)
  rw [kuhnVertex_eq_iff]
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [Fin.sum_univ_four]
    simp only [kt102, kv102, Tet.v, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons]
    ring

theorem mem_kt120_of_order (x : Pt3) (hx : x ∈ closedCube)
    (h1 : x 2 ≤ x 1) (h2 : x 0 ≤ x 2) : x ∈ kt120.carrier := by
  apply tet_mem_carrier_of_weights kt120 ![1 - x 1, x 1 - x 2, x 2 - x 0, x 0]
    (by obtain ⟨hx0l, hx0r⟩ := hx 0; obtain ⟨hx1l, hx1r⟩ := hx 1; obtain ⟨hx2l, hx2r⟩ := hx 2;
        intro i; fin_cases i <;> simp only [List.ofFn, Matrix.cons_val] <;> norm_num <;> linarith)
    (by simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]; ring)
  rw [kuhnVertex_eq_iff]
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [Fin.sum_univ_four]
    simp only [kt120, kv120, Tet.v, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons]
    ring

theorem mem_kt201_of_order (x : Pt3) (hx : x ∈ closedCube)
    (h1 : x 0 ≤ x 2) (h2 : x 1 ≤ x 0) : x ∈ kt201.carrier := by
  apply tet_mem_carrier_of_weights kt201 ![1 - x 2, x 2 - x 0, x 0 - x 1, x 1]
    (by obtain ⟨hx0l, hx0r⟩ := hx 0; obtain ⟨hx1l, hx1r⟩ := hx 1; obtain ⟨hx2l, hx2r⟩ := hx 2;
        intro i; fin_cases i <;> simp only [List.ofFn, Matrix.cons_val] <;> norm_num <;> linarith)
    (by simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]; ring)
  rw [kuhnVertex_eq_iff]
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [Fin.sum_univ_four]
    simp only [kt201, kv201, Tet.v, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons]
    ring

theorem mem_kt210_of_order (x : Pt3) (hx : x ∈ closedCube)
    (h1 : x 1 ≤ x 2) (h2 : x 0 ≤ x 1) : x ∈ kt210.carrier := by
  apply tet_mem_carrier_of_weights kt210 ![1 - x 2, x 2 - x 1, x 1 - x 0, x 0]
    (by obtain ⟨hx0l, hx0r⟩ := hx 0; obtain ⟨hx1l, hx1r⟩ := hx 1; obtain ⟨hx2l, hx2r⟩ := hx 2;
        intro i; fin_cases i <;> simp only [List.ofFn, Matrix.cons_val] <;> norm_num <;> linarith)
    (by simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]; ring)
  rw [kuhnVertex_eq_iff]
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [Fin.sum_univ_four]
    simp only [kt210, kv210, Tet.v, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons]
    ring

/-- A point in a Kuhn piece's carrier is in the Kuhn solid carrier. -/
theorem kt_carrier_subset_kuhn {T : Tet} (hT : T ∈ kuhnSolid.pieces) :
    T.carrier ⊆ kuhnSolid.carrier := by
  intro y hy; rw [TetSolid.carrier]; exact Set.mem_biUnion hT hy

/-- **The covering: the closed unit cube is contained in the Kuhn solid carrier.**  Every cube point
lies in the order-simplex of the permutation sorting its coordinates descending. -/
theorem closedCube_subset_kuhnSolid_carrier : closedCube ⊆ kuhnSolid.carrier := by
  intro x hx
  rcases le_total (x 1) (x 0) with h01 | h01
  · rcases le_total (x 2) (x 1) with h12 | h12
    · exact kt_carrier_subset_kuhn (by simp) (mem_kt012_of_order x hx h01 h12)
    · rcases le_total (x 2) (x 0) with h02 | h02
      · exact kt_carrier_subset_kuhn (by simp) (mem_kt021_of_order x hx h02 h12)
      · exact kt_carrier_subset_kuhn (by simp) (mem_kt201_of_order x hx h02 h01)
  · rcases le_total (x 2) (x 0) with h02 | h02
    · exact kt_carrier_subset_kuhn (by simp) (mem_kt102_of_order x hx h01 h02)
    · rcases le_total (x 2) (x 1) with h12 | h12
      · exact kt_carrier_subset_kuhn (by simp) (mem_kt120_of_order x hx h12 h02)
      · exact kt_carrier_subset_kuhn (by simp) (mem_kt210_of_order x hx h12 h01)



/-! ### The interior and frontier of the Kuhn carrier -/

theorem openCube_open : IsOpen openCube := by
  have : openCube = ⋂ i : Fin 3, {x : Pt3 | x i ∈ Set.Ioo (0:ℝ) 1} := by
    ext x; simp only [openCube, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  exact isOpen_iInter_of_finite
    (fun i => ((EuclideanSpace.proj i).continuous.isOpen_preimage _ isOpen_Ioo))

theorem openCube_subset_closedCube : openCube ⊆ closedCube :=
  fun x hx i => ⟨le_of_lt (hx i).1, le_of_lt (hx i).2⟩

/-- The interior of the closed cube lands in the open cube (a coordinate-boundary point cannot be
interior). -/
theorem interior_closedCube_subset_openCube : interior closedCube ⊆ openCube := by
  intro x hx i
  have hmem : x ∈ closedCube := interior_subset hx
  have hxi := hmem i
  rw [Set.mem_Ioo]
  refine ⟨?_, ?_⟩
  · rcases lt_or_eq_of_le hxi.1 with h | h
    · exact h
    · exfalso
      have hnhds := isOpen_interior.mem_nhds hx
      have hcont : Continuous (fun t : ℝ => x - t • (EuclideanSpace.single i (1:ℝ))) := by fun_prop
      have hpre : (fun t : ℝ => x - t • (EuclideanSpace.single i (1:ℝ))) ⁻¹' interior closedCube
          ∈ nhds (0:ℝ) := by
        apply hcont.continuousAt.preimage_mem_nhds; simpa using hnhds
      rw [Metric.mem_nhds_iff] at hpre
      obtain ⟨ε, hε, hball⟩ := hpre
      have htmem : (ε/2) ∈ Metric.ball (0:ℝ) ε := by
        rw [Metric.mem_ball, Real.dist_eq]; simp only [sub_zero]
        rw [abs_of_pos (by linarith)]; linarith
      have hin := interior_subset (hball htmem)
      have hh := hin i
      simp only [PiLp.sub_apply, PiLp.smul_apply, EuclideanSpace.single_apply, smul_eq_mul] at hh
      rw [if_true] at hh
      rw [← h] at hh
      simp only [Set.mem_Icc] at hh
      linarith [hh.1]
  · rcases lt_or_eq_of_le hxi.2 with h | h
    · exact h
    · exfalso
      have hnhds := isOpen_interior.mem_nhds hx
      have hcont : Continuous (fun t : ℝ => x + t • (EuclideanSpace.single i (1:ℝ))) := by fun_prop
      have hpre : (fun t : ℝ => x + t • (EuclideanSpace.single i (1:ℝ))) ⁻¹' interior closedCube
          ∈ nhds (0:ℝ) := by
        apply hcont.continuousAt.preimage_mem_nhds; simpa using hnhds
      rw [Metric.mem_nhds_iff] at hpre
      obtain ⟨ε, hε, hball⟩ := hpre
      have htmem : (ε/2) ∈ Metric.ball (0:ℝ) ε := by
        rw [Metric.mem_ball, Real.dist_eq]; simp only [sub_zero]
        rw [abs_of_pos (by linarith)]; linarith
      have hin := interior_subset (hball htmem)
      have hh := hin i
      simp only [PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply, smul_eq_mul] at hh
      rw [if_true] at hh
      simp only [Set.mem_Icc] at hh
      linarith [hh.2, h]

/-- The open cube is contained in the interior of the Kuhn carrier (it is open and inside the
carrier by the covering). -/
theorem openCube_subset_interior_kuhn : openCube ⊆ interior kuhnSolid.carrier := by
  rw [← interior_eq_iff_isOpen.mpr openCube_open]
  exact interior_mono (openCube_subset_closedCube.trans closedCube_subset_kuhnSolid_carrier)

/-- The interior of the Kuhn carrier is contained in the open cube. -/
theorem interior_kuhn_subset_openCube : interior kuhnSolid.carrier ⊆ openCube :=
  (interior_mono kuhnSolid_carrier_subset_cube).trans interior_closedCube_subset_openCube

/-- **The interior of the Kuhn carrier is exactly the open unit cube.** -/
theorem interior_kuhn_eq_openCube : interior kuhnSolid.carrier = openCube :=
  Set.Subset.antisymm interior_kuhn_subset_openCube openCube_subset_interior_kuhn



/-! ### Pearl-source-edge containments per class -/

/-- A source edge's carrier is contained in the Kuhn solid carrier. -/
theorem sourceEdge_carrier_subset_kuhn {e : Segment3} (he : e ∈ PieceEdges kuhnSolid) :
    e.carrier ⊆ kuhnSolid.carrier := by
  rw [PieceEdges, Finset.mem_biUnion] at he
  obtain ⟨T, hT, heT⟩ := he
  obtain ⟨i, j, hij, hea, heb⟩ := mem_edges_endpoints heT
  intro y hy
  rw [Segment3.carrier] at hy
  have hsub : segment ℝ e.a e.b ⊆ T.carrier := by
    rw [hea, heb]
    exact (T.carrier_convex).segment_subset (T.vertex_mem_carrier i) (T.vertex_mem_carrier j)
  exact Set.mem_biUnion hT (hsub hy)

/-- **Space-diagonal containment.**  The open segment from `(0,0,0)` to `(1,1,1)` lies in the open
cube, hence in the interior of the Kuhn carrier (the point `(t,t,t)` has every coordinate in `(0,1)`).
-/
theorem spaceDiag_relInterior_subset_interior {e : Segment3}
    (ha : e.a = !₂[(0:ℝ),0,0]) (hb : e.b = !₂[(1:ℝ),1,1]) :
    e.relInterior ⊆ interior kuhnSolid.carrier := by
  rw [interior_kuhn_eq_openCube, Segment3.relInterior, openSegment_eq_image]
  rintro y ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
  rw [ha, hb]
  intro i
  fin_cases i <;>
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons]
    constructor <;> · push_cast; nlinarith [hθ0, hθ1]

/-- **Face-diagonal containment.**  A face diagonal whose `k`-th endpoint coordinates are both `c`
(with `c = 0` or `c = 1`, i.e. the diagonal lies on the cube face `x_k = c`) has its open segment in
the frontier of the Kuhn carrier: it is in the carrier (on the edge) but not in the open cube (its
`k`-th coordinate is constantly `c ∉ (0,1)`). -/
theorem faceDiag_relInterior_subset_frontier {e : Segment3} (he : e ∈ PieceEdges kuhnSolid)
    {k : Fin 3} {c : ℝ} (hc : c = 0 ∨ c = 1) (hak : e.a k = c) (hbk : e.b k = c) :
    e.relInterior ⊆ frontier kuhnSolid.carrier := by
  intro y hy
  rw [frontier, kuhnSolid.carrier_closed.closure_eq]
  refine ⟨sourceEdge_carrier_subset_kuhn he (e.relInterior_subset_carrier hy), ?_⟩
  rw [interior_kuhn_eq_openCube]
  intro hyo
  rw [Segment3.relInterior, openSegment_eq_image] at hy
  obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hy
  have hk := hyo k
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hk
  rw [hak, hbk] at hk
  rcases hc with rfl | rfl <;>
    (rw [Set.mem_Ioo] at hk; obtain ⟨h1, h2⟩ := hk) <;> nlinarith [hθ0, hθ1, h1, h2]



/-! ## The per-pearl classification certificate

For each canonical cube pearl we build a `PearlClassificationCert cubeSolid p` via the design-permitted
`fullSector` route: a single sector covers the target wedge, so the only load-bearing field is the
angle bridge `PearlAngleSum = loc.targetAngle`, which we computed per class.  The location is the
honest one dictated by the source-edge class. -/

/-- A one-sector `PearlClassificationCert` from a location whose target angle `θ` satisfies
`0 < θ ≤ 2π` and whose pearl angle sum equals `θ`. -/
def certOfLocation {p : Pearl} (loc : PearlLocation cubeSolid p)
    (hθ0 : 0 < loc.targetAngle) (hθ2 : loc.targetAngle ≤ SectorSum.twoPi)
    (hsum : PearlAngleSum cubeSolid.toTetSolid p = loc.targetAngle) :
    PearlClassificationCert cubeSolid p where
  loc := loc
  model :=
    { x := 0
      ε := 1
      sectors := [fullSector loc.targetAngle (le_of_lt hθ0)]
      model := fullSector_model (x := 0) (ε := 1) one_pos hθ0 hθ2
      angle_bridge := by rw [hsum, fullSector_angleSum] }

theorem pi_div_two_le_twoPi : Real.pi / 2 ≤ SectorSum.twoPi := by
  rw [SectorSum.twoPi]; linarith [Real.pi_pos]

theorem pi_le_twoPi : Real.pi ≤ SectorSum.twoPi := by
  rw [SectorSum.twoPi]; linarith [Real.pi_pos]

/-- **Cube-edge certificate.**  A pearl on a cube edge (`source ∈ cubeExtEdges`, angle sum `π/2`)
classifies as `externalEdge`. -/
def cubeEdgeCert {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (hmem : p.sourceEdge ∈ cubeExtEdges) (hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi / 2) :
    PearlClassificationCert cubeSolid p := by
  have hloc : p.relInterior ⊆ p.sourceEdge.relInterior :=
    relInterior_subset_sourceEdge_relInterior hp
  refine certOfLocation (PearlLocation.externalEdge p.sourceEdge hmem hloc) ?_ ?_ ?_
  · show 0 < cubeSolid.angleOfExtEdge p.sourceEdge; exact pi_div_two_mem_Ioo.1
  · show cubeSolid.angleOfExtEdge p.sourceEdge ≤ _; exact pi_div_two_le_twoPi
  · show PearlAngleSum cubeSolid.toTetSolid p = cubeSolid.angleOfExtEdge p.sourceEdge; exact hsum

/-- **Face-diagonal certificate.**  A pearl on a face diagonal (relInterior in the frontier, angle
sum `π`) classifies as `boundaryFacetInterior`. -/
def faceCert {p : Pearl} (hsub : p.relInterior ⊆ frontier cubeSolid.toTetSolid.carrier)
    (hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi) :
    PearlClassificationCert cubeSolid p :=
  certOfLocation (PearlLocation.boundaryFacetInterior hsub) Real.pi_pos pi_le_twoPi hsum

/-- **Space-diagonal certificate.**  A pearl on the main diagonal (relInterior in the interior, angle
sum `2π`) classifies as `solidInterior`. -/
def spaceCert {p : Pearl} (hsub : p.relInterior ⊆ interior cubeSolid.toTetSolid.carrier)
    (hsum : PearlAngleSum cubeSolid.toTetSolid p = SectorSum.twoPi) :
    PearlClassificationCert cubeSolid p :=
  certOfLocation (PearlLocation.solidInterior hsub)
    (show 0 < SectorSum.twoPi by rw [SectorSum.twoPi]; positivity) (le_refl _) hsum


/-! ## Per-edge classification certificates (one per the 19 distinct Kuhn edges) -/

def cert_000_100 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(0:ℝ),0,0]) (hb : p.sourceEdge.b = !₂[(1:ℝ),0,0]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi / 2 := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hmem : p.sourceEdge ∈ cubeExtEdges := by
    rw [cubeExtEdges]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    left
    rw [segment3_eq_iff]; exact ⟨ha, hb⟩
  exact cubeEdgeCert hp hmem hsum

def cert_000_110 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(0:ℝ),0,0]) (hb : p.sourceEdge.b = !₂[(1:ℝ),1,0]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hsub : p.relInterior ⊆ frontier cubeSolid.toTetSolid.carrier := by
    rw [cubeSolid_toTetSolid]
    refine (relInterior_subset_sourceEdge_relInterior hp).trans ?_
    refine faceDiag_relInterior_subset_frontier hp.1 (k := 2) (c := 0) (by norm_num) ?_ ?_
    · rw [ha]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    · rw [hb]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  exact faceCert hsub hsum

def cert_000_111 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(0:ℝ),0,0]) (hb : p.sourceEdge.b = !₂[(1:ℝ),1,1]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = SectorSum.twoPi := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb, SectorSum.twoPi]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    ring
  have hsub : p.relInterior ⊆ interior cubeSolid.toTetSolid.carrier := by
    rw [cubeSolid_toTetSolid]
    exact (relInterior_subset_sourceEdge_relInterior hp).trans
      (spaceDiag_relInterior_subset_interior ha hb)
  exact spaceCert hsub hsum

def cert_100_110 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(1:ℝ),0,0]) (hb : p.sourceEdge.b = !₂[(1:ℝ),1,0]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi / 2 := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hmem : p.sourceEdge ∈ cubeExtEdges := by
    rw [cubeExtEdges]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    right
    right
    right
    right
    left
    rw [segment3_eq_iff]; exact ⟨ha, hb⟩
  exact cubeEdgeCert hp hmem hsum

def cert_100_111 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(1:ℝ),0,0]) (hb : p.sourceEdge.b = !₂[(1:ℝ),1,1]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hsub : p.relInterior ⊆ frontier cubeSolid.toTetSolid.carrier := by
    rw [cubeSolid_toTetSolid]
    refine (relInterior_subset_sourceEdge_relInterior hp).trans ?_
    refine faceDiag_relInterior_subset_frontier hp.1 (k := 0) (c := 1) (by norm_num) ?_ ?_
    · rw [ha]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    · rw [hb]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  exact faceCert hsub hsum

def cert_110_111 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(1:ℝ),1,0]) (hb : p.sourceEdge.b = !₂[(1:ℝ),1,1]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi / 2 := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hmem : p.sourceEdge ∈ cubeExtEdges := by
    rw [cubeExtEdges]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    rw [segment3_eq_iff]; exact ⟨ha, hb⟩
  exact cubeEdgeCert hp hmem hsum

def cert_000_101 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(0:ℝ),0,0]) (hb : p.sourceEdge.b = !₂[(1:ℝ),0,1]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hsub : p.relInterior ⊆ frontier cubeSolid.toTetSolid.carrier := by
    rw [cubeSolid_toTetSolid]
    refine (relInterior_subset_sourceEdge_relInterior hp).trans ?_
    refine faceDiag_relInterior_subset_frontier hp.1 (k := 1) (c := 0) (by norm_num) ?_ ?_
    · rw [ha]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    · rw [hb]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  exact faceCert hsub hsum

def cert_100_101 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(1:ℝ),0,0]) (hb : p.sourceEdge.b = !₂[(1:ℝ),0,1]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi / 2 := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hmem : p.sourceEdge ∈ cubeExtEdges := by
    rw [cubeExtEdges]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    rw [segment3_eq_iff]; exact ⟨ha, hb⟩
  exact cubeEdgeCert hp hmem hsum

def cert_101_111 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(1:ℝ),0,1]) (hb : p.sourceEdge.b = !₂[(1:ℝ),1,1]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi / 2 := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hmem : p.sourceEdge ∈ cubeExtEdges := by
    rw [cubeExtEdges]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    right
    right
    right
    right
    right
    right
    left
    rw [segment3_eq_iff]; exact ⟨ha, hb⟩
  exact cubeEdgeCert hp hmem hsum

def cert_000_010 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(0:ℝ),0,0]) (hb : p.sourceEdge.b = !₂[(0:ℝ),1,0]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi / 2 := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hmem : p.sourceEdge ∈ cubeExtEdges := by
    rw [cubeExtEdges]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    right
    right
    right
    left
    rw [segment3_eq_iff]; exact ⟨ha, hb⟩
  exact cubeEdgeCert hp hmem hsum

def cert_010_110 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(0:ℝ),1,0]) (hb : p.sourceEdge.b = !₂[(1:ℝ),1,0]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi / 2 := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hmem : p.sourceEdge ∈ cubeExtEdges := by
    rw [cubeExtEdges]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    left
    rw [segment3_eq_iff]; exact ⟨ha, hb⟩
  exact cubeEdgeCert hp hmem hsum

def cert_010_111 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(0:ℝ),1,0]) (hb : p.sourceEdge.b = !₂[(1:ℝ),1,1]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hsub : p.relInterior ⊆ frontier cubeSolid.toTetSolid.carrier := by
    rw [cubeSolid_toTetSolid]
    refine (relInterior_subset_sourceEdge_relInterior hp).trans ?_
    refine faceDiag_relInterior_subset_frontier hp.1 (k := 1) (c := 1) (by norm_num) ?_ ?_
    · rw [ha]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    · rw [hb]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  exact faceCert hsub hsum

def cert_000_011 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(0:ℝ),0,0]) (hb : p.sourceEdge.b = !₂[(0:ℝ),1,1]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hsub : p.relInterior ⊆ frontier cubeSolid.toTetSolid.carrier := by
    rw [cubeSolid_toTetSolid]
    refine (relInterior_subset_sourceEdge_relInterior hp).trans ?_
    refine faceDiag_relInterior_subset_frontier hp.1 (k := 0) (c := 0) (by norm_num) ?_ ?_
    · rw [ha]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    · rw [hb]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  exact faceCert hsub hsum

def cert_010_011 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(0:ℝ),1,0]) (hb : p.sourceEdge.b = !₂[(0:ℝ),1,1]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi / 2 := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hmem : p.sourceEdge ∈ cubeExtEdges := by
    rw [cubeExtEdges]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    rw [segment3_eq_iff]; exact ⟨ha, hb⟩
  exact cubeEdgeCert hp hmem hsum

def cert_011_111 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(0:ℝ),1,1]) (hb : p.sourceEdge.b = !₂[(1:ℝ),1,1]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi / 2 := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hmem : p.sourceEdge ∈ cubeExtEdges := by
    rw [cubeExtEdges]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    right
    right
    left
    rw [segment3_eq_iff]; exact ⟨ha, hb⟩
  exact cubeEdgeCert hp hmem hsum

def cert_000_001 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(0:ℝ),0,0]) (hb : p.sourceEdge.b = !₂[(0:ℝ),0,1]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi / 2 := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hmem : p.sourceEdge ∈ cubeExtEdges := by
    rw [cubeExtEdges]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    right
    right
    right
    right
    right
    right
    right
    left
    rw [segment3_eq_iff]; exact ⟨ha, hb⟩
  exact cubeEdgeCert hp hmem hsum

def cert_001_101 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(0:ℝ),0,1]) (hb : p.sourceEdge.b = !₂[(1:ℝ),0,1]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi / 2 := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hmem : p.sourceEdge ∈ cubeExtEdges := by
    rw [cubeExtEdges]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    right
    left
    rw [segment3_eq_iff]; exact ⟨ha, hb⟩
  exact cubeEdgeCert hp hmem hsum

def cert_001_111 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(0:ℝ),0,1]) (hb : p.sourceEdge.b = !₂[(1:ℝ),1,1]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hsub : p.relInterior ⊆ frontier cubeSolid.toTetSolid.carrier := by
    rw [cubeSolid_toTetSolid]
    refine (relInterior_subset_sourceEdge_relInterior hp).trans ?_
    refine faceDiag_relInterior_subset_frontier hp.1 (k := 2) (c := 1) (by norm_num) ?_ ?_
    · rw [ha]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    · rw [hb]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  exact faceCert hsub hsum

def cert_001_011 {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p)
    (ha : p.sourceEdge.a = !₂[(0:ℝ),0,1]) (hb : p.sourceEdge.b = !₂[(0:ℝ),1,1]) :
    PearlClassificationCert cubeSolid p := by
  have hsum : PearlAngleSum cubeSolid.toTetSolid p = Real.pi / 2 := by
    rw [cubeSolid_toTetSolid, pearlAngleSum_kuhn_terms hp, ha, hb]
    simp only [kuhnVertex_eq_iff, kt012, kt021, kt102, kt120, kt201, kt210, kv012, kv021, kv102,
      kv120, kv201, kv210, Tet.v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    norm_num
    try ring
  have hmem : p.sourceEdge ∈ cubeExtEdges := by
    rw [cubeExtEdges]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    right
    right
    right
    right
    right
    left
    rw [segment3_eq_iff]; exact ⟨ha, hb⟩
  exact cubeEdgeCert hp hmem hsum


/-! ## The cube classification certificate at every pearl, and `CubePearlAngleData`

The dispatcher cases the source edge of an arbitrary canonical Kuhn pearl into its six-piece /
six-pair representations; the endpoints are concrete cube vertices, so the matching per-edge
certificate fires.  Since `PearlClassificationCert` is data, we target `Nonempty` (eliminating the
existential decomposition of the `PieceEdges` membership into `Prop`) and extract the certificate by
choice when assembling the `LocationData`. -/

/-- **Every canonical Kuhn pearl admits a classification certificate.**  Casing on the source edge's
representation among the six orthoschemes and six edge pairs, each of the nineteen distinct edges
dispatches to its per-class certificate (cube edge → `externalEdge π/2`, face diagonal →
`boundaryFacetInterior π`, space diagonal → `solidInterior 2π`). -/
theorem cubePearlCert_nonempty {p : Pearl} (hp : IsPearlOf (PieceEdges kuhnSolid) p) :
    Nonempty (PearlClassificationCert cubeSolid p) := by
  have hsrc := hp.1
  rw [PieceEdges, Finset.mem_biUnion] at hsrc
  obtain ⟨T, hT, heT⟩ := hsrc
  obtain ⟨i, j, hij, hea, heb⟩ := mem_edges_endpoints heT
  simp only [kuhnSolid_pieces, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases i <;> fin_cases j <;>
    first
      | exact absurd hij (by decide)
      | exact ⟨cert_000_100 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_000_110 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_000_111 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_100_110 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_100_111 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_110_111 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_000_101 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_100_101 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_101_111 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_000_010 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_010_110 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_010_111 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_000_011 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_010_011 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_011_111 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_000_001 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_001_101 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_001_111 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩
      | exact ⟨cert_001_011 hp (by rw [hea]; rfl) (by rw [heb]; rfl)⟩

/-- The cube classification certificate at a canonical pearl (extracted by choice). -/
noncomputable def cubePearlCert {p : Pearl}
    (hp : p ∈ Pearls (PieceEdges cubeSolid.toTetSolid)) : PearlClassificationCert cubeSolid p :=
  (cubePearlCert_nonempty (by rw [cubeSolid_toTetSolid] at hp; exact mem_Pearls.mp hp)).some

/-- **`CubePearlAngleData`: the cube-side classification isolate, fully constructed.**  A
`LocationData cubeSolid` over the canonical cube pearl set — a classification certificate at every
pearl, from the six-orthoscheme Kuhn dihedral-angle / incidence computation. -/
noncomputable def cubePearlAngleData : CubePearlAngleData where
  cert := fun p hp => cubePearlCert hp



/-! ## The fully discharged Chapter 9 headline (cube side closed)

With `cubePearlAngleData` constructed, the cube-side classification isolate is no longer a hypothesis.
The only remaining genuine input to the Chapter 9 obstruction is the book's piece-matching double
count `Σ₁ = Σ₂` (`hmatch`); the regular-tet pearl-nonemptiness is the proven
`pearls_nonempty_of_pieces_nonempty regularTetSolid_pieces_nonempty`. -/

/-- **The Chapter 9 headline with the cube side fully discharged.**  Given only the book's
piece-matching double count `Σ₁ = Σ₂` (`hmatch`, the geometric residue carried by
`BricardDoubleCount.sigma_match`), a regular tetrahedron is **not** equidecomposable with the Kuhn
cube.  Every other input is proven here:

* the cube-side classification isolate `Rdata` is the **constructed** `cubePearlAngleData` (the
  six-orthoscheme Kuhn dihedral-angle / incidence computation of this module);
* the regular-tet `LocationData`/normalization are the proven `regularTetLocationData` /
  `regularTet_pearlExtAngle_arccos`;
* the cube external part vanishes mod `ℚπ` by the proven, unconditional
  `angleClassQ_cube_externalPart_eq_zero_unconditional`;
* the regular tetrahedron carries a pearl by `pearls_nonempty_of_pieces_nonempty`. -/
theorem regularTet_cube_no_equidecomp_final
    (hmatch : Sigma regularTetSolid (Pearls (PieceEdges regularTetSolid.toTetSolid))
      = Sigma cubeSolid (Pearls (PieceEdges cubeSolid.toTetSolid))) : False :=
  regularTet_cube_no_equidecomp_corrected cubePearlAngleData hmatch
    (pearls_nonempty_of_pieces_nonempty regularTetSolid_pieces_nonempty)

end ProofsInTheBook.BricardCubePearls
