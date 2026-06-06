import ProofsInTheBook.BricardCubePearls

/-!
# Chapter 9, the WEIGHTED headline: a regular tetrahedron is not equidecomposable with a cube

This module composes the **fully weighted** Bricard chain into the Chapter 9 headline, eliminating
every residual hypothesis of `Chapter09Final.lean`.  Where `Chapter09Final` left the *raw geometric*
count balance `EdgeCountBalance` as an honest residue (the Pearl Lemma never supplies equal geometric
counts on independently-refined solids), this module consumes instead the **weighted** chain whose
every link is proven:

  `decomp : TetEquidecomp regularTetSolid cubeSolid`
    ⟹ (aggregate)  positive integer pearl weights `νP, νQ` with `WeightedEdgeBalance`
                   (`weightedEdgeBalance_of_equidecomp`, from the pearl-level Pearl Lemma
                   `exists_balanced_pearl_weights` + the proven faithfulness bridges
                   `edgeSourceFaithful_regularTetSolid` / `edgeSourceFaithful_cubeSolid`);
    ⟹ (balance)    `SigmaW₁ = SigmaW₂`  (`sigmaW_match_of_weightedEdgeBalance`);
    ⟹ (location)   `SigmaW₁ ≡ (Σν)·arccos(1/3)`,  `SigmaW₂ ≡ 0`  (mod `ℚπ`)
                   (`angleClassQ_sigmaW` + `externalPartW_eq_total_mul` on the regular side with the
                   proven normalization `regularTet_pearlExtAngle_arccos`; the cube side via the
                   *weighted* corrected normalization proved here,
                   `angleClassQ_cube_externalPartW_eq_zero`);
    ⟹ (irrationality, `Σν ≥ 1`)  `False`  (`angleClassQ_arccos_one_third_ne_zero`).

## The one new weighted-location lemma (the corrected cube normalization, weighted form)

`BricardBalance.regularTet_cube_no_equidecomp_weighted` (the existing weighted headline) consumes the
literal normalization `hQ_pi2` — *every* cube pearl sits on an external edge of angle `π/2`.  As
documented in `Chapter09Final.lean`, **this is false on the Kuhn (six-orthoscheme) cube**: the main
space diagonal is an interior edge with angle sum `2π`, and the face diagonals are facet-interior
edges with angle sum `π`.  So the existing weighted headline is *not* instantiable for `cubeSolid` +
`cubePearlAngleData`.

The fix is the weighted analogue of `BricardLocation.angleClassQ_cube_externalPart_eq_zero_unconditional`:
for *any* `LocationData` over the cube, the **weighted** external part `externalPartW L ν` vanishes mod
`ℚπ`, because each pearl's external angle is a rational multiple of `π`
(`BricardLocation.cube_pearlExtAngle_rat_mul_pi`: `π/2` on a cube edge, `0` otherwise) and an integer
multiple of a rational multiple of `π` is again a rational multiple of `π`.  This is the single new
weighted-location lemma `angleClassQ_cube_externalPartW_eq_zero`; everything else is reused verbatim
from the proven weighted chain.

## Result

`chapter09_weighted : ¬ Nonempty (TetEquidecomp regularTetSolid.toTetSolid cubeSolid.toTetSolid)` —
with **no residual hypotheses**: the pearl multiplicities, the weighted edge balance, both
faithfulness bridges, both `LocationData`s, both angle normalizations, the positive total multiplicity
(`Σν ≥ 1`), and the regular-tet pearl-nonemptiness are all proven/constructed in the imported modules.

No `sorry`, `axiom`, or `admit`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped BigOperators Classical RealInnerProductSpace
open ProofsInTheBook.TetPearls
open ProofsInTheBook.PearlClassification
open ProofsInTheBook.Chapter09
open ProofsInTheBook.Bricard
open ProofsInTheBook.BricardLocation
open ProofsInTheBook.BricardCube
open ProofsInTheBook.BricardCubePearls

namespace ProofsInTheBook.Chapter09Weighted

/-! ## The one new weighted-location lemma: the cube's weighted external part vanishes mod `ℚπ` -/

/-- **The cube's WEIGHTED external part vanishes mod `ℚπ`, unconditionally.**

For *any* `LocationData` over the cube's pearl set and any integer multiplicity `ν`, the weighted
external part `externalPartW L ν = ∑_p (ν p)·pearlExtAngle(cert p)` has `angleClassQ = 0`.  Each
`pearlExtAngle` is a rational multiple of `π` (`cube_pearlExtAngle_rat_mul_pi`: `π/2` on a cube edge,
`0` otherwise), hence `(ν p)·pearlExtAngle = ((ν p)·q : ℚ)·π` is again a rational multiple of `π`, so
every summand's class vanishes.  This is the *weighted* analogue of the unweighted
`angleClassQ_cube_externalPart_eq_zero_unconditional`, and the satisfiable replacement for the
over-strong literal `hQ_pi2` (false on the Kuhn cube). -/
theorem angleClassQ_cube_externalPartW_eq_zero {P : Finset Pearl}
    (L : LocationData cubeSolid P) (ν : Pearl → ℤ) :
    angleClassQ (externalPartW L ν) = 0 := by
  rw [externalPartW, angleClassQ_sum]
  apply Finset.sum_eq_zero
  intro p _
  obtain ⟨q, hq⟩ := cube_pearlExtAngle_rat_mul_pi (L.cert p.1 p.2)
  -- `(ν p)·pearlExtAngle = (ν p)·(q·π) = ((ν p · q : ℚ))·π`, a rational multiple of `π`.
  rw [hq, show (ν p.1 : ℝ) * ((q : ℝ) * Real.pi)
        = (((ν p.1 : ℚ) * q : ℚ) : ℝ) * Real.pi from by push_cast; ring,
      angleClassQ_rat_mul_pi]

/-! ## The corrected weighted headline (cube side discharged by the weighted lemma above)

The verbatim weighted re-derivation of `regularTet_cube_no_equidecomp_weighted`, with the cube branch
`hQ0` supplied by `angleClassQ_cube_externalPartW_eq_zero` (no `hQ_pi2`), and the regular-tet
`LocationData`/normalization pinned to the proven `regularTetLocationData` /
`regularTet_pearlExtAngle_arccos`. -/

/-- **The corrected weighted headline.**  From positive pearl multiplicities `νP`, `νQ`, a weighted
edge balance against `cubePearlAngleData` on the cube side, the proven regular-tet location data, and
the regular tet carrying at least one pearl, derive `False`.

The matched-pearl input is the **faithful** Pearl-Lemma residue `WeightedEdgeBalance` (equal chosen
weights on corresponding congruent edges).  The cube side is closed by the *weighted* corrected
normalization `angleClassQ_cube_externalPartW_eq_zero`; the regular side by `externalPartW_eq_total_mul`
with the proven `arccos(1/3)` normalization; the contradiction by the proven irrationality of
`arccos(1/3)` over `π` together with the positive total multiplicity `Σ νP ≥ 1`. -/
theorem regularTet_cube_no_equidecomp_weighted_corrected
    (Rdata : CubePearlAngleData)
    (decomp : TetEquidecomp regularTetSolid.toTetSolid cubeSolid.toTetSolid)
    {νP νQ : Pearl → ℤ} (hνP : ∀ p, 0 < νP p)
    (hbal : WeightedEdgeBalance decomp νP νQ
      (Pearls (PieceEdges regularTetSolid.toTetSolid)) (Pearls (PieceEdges cubeSolid.toTetSolid)))
    (hPne : (Pearls (PieceEdges regularTetSolid.toTetSolid)).Nonempty) : False := by
  -- the weighted double count: SigmaW₁ = SigmaW₂.
  have hmatch : SigmaW regularTetSolid νP (Pearls (PieceEdges regularTetSolid.toTetSolid))
      = SigmaW cubeSolid νQ (Pearls (PieceEdges cubeSolid.toTetSolid)) :=
    sigmaW_match_of_weightedEdgeBalance decomp hbal
  -- mod ℚπ: each weighted SigmaW collapses to its weighted external part.
  have hP : angleClassQ (SigmaW regularTetSolid νP (Pearls (PieceEdges regularTetSolid.toTetSolid)))
      = angleClassQ (externalPartW regularTetLocationData νP) :=
    angleClassQ_sigmaW regularTetLocationData νP
  have hQ : angleClassQ (SigmaW cubeSolid νQ (Pearls (PieceEdges cubeSolid.toTetSolid)))
      = angleClassQ (externalPartW Rdata νQ) :=
    angleClassQ_sigmaW Rdata νQ
  have hclass : angleClassQ (externalPartW regularTetLocationData νP)
      = angleClassQ (externalPartW Rdata νQ) := by
    rw [← hP, ← hQ, hmatch]
  -- the cube side is 0 (weighted corrected normalization — no hQ_pi2).
  have hQ0 : angleClassQ (externalPartW Rdata νQ) = 0 :=
    angleClassQ_cube_externalPartW_eq_zero Rdata νQ
  rw [hQ0] at hclass
  -- the regular-tet side is (total weight)·arccos(1/3).
  rw [externalPartW_eq_total_mul regularTetLocationData νP (Real.arccos (1 / 3))
        regularTet_pearlExtAngle_arccos] at hclass
  -- total weight is a positive integer.
  have htw_pos : 0 < totalWeight νP (Pearls (PieceEdges regularTetSolid.toTetSolid)) := by
    rw [totalWeight]
    exact Finset.sum_pos (fun p _ => hνP p) hPne
  -- (total)·arccos(1/3) ≡ 0 mod ℚπ forces a contradiction (arccos(1/3) irrational over π).
  set M : ℤ := totalWeight νP (Pearls (PieceEdges regularTetSolid.toTetSolid)) with hM
  have hsmul : angleClassQ ((M : ℝ) * Real.arccos (1 / 3))
      = (M : ℚ) • angleClassQ (Real.arccos (1 / 3)) := by
    rw [show ((M : ℝ) * Real.arccos (1 / 3)) = (M : ℝ) • Real.arccos (1 / 3) from by rw [smul_eq_mul]]
    rw [angleClassQ]
    rw [show ((M : ℝ) • Real.arccos (1 / 3)) = ((M : ℚ)) • Real.arccos (1 / 3) from by
        rw [Rat.smul_def]; push_cast; ring]
    rw [Submodule.Quotient.mk_smul]
    rfl
  rw [hsmul] at hclass
  have hne : angleClassQ (Real.arccos (1 / 3)) ≠ 0 := angleClassQ_arccos_one_third_ne_zero
  have hscal_ne : (M : ℚ) ≠ 0 := by exact_mod_cast htw_pos.ne'
  exact (smul_ne_zero hscal_ne hne) hclass

/-! ## The fully discharged weighted headline (no residual hypotheses) -/

/-- **The Chapter 9 weighted headline (composed): `False` from a putative equidecomposition.**

Composing `weightedEdgeBalance_of_equidecomp` (the aggregation joint — the pearl-level Pearl Lemma
plus the two proven faithfulness bridges) with the corrected weighted headline above.  Every input is
proven/constructed:

* the positive pearl multiplicities `νP`, `νQ` and the weighted edge balance are **constructed** from
  `decomp` by `weightedEdgeBalance_of_equidecomp` using `edgeSourceFaithful_regularTetSolid` and
  `edgeSourceFaithful_cubeSolid`;
* the cube-side `LocationData` is the **constructed** `cubePearlAngleData`;
* the regular-tet `LocationData`/normalization are the **proven** `regularTetLocationData` /
  `regularTet_pearlExtAngle_arccos`;
* the cube external part vanishes mod `ℚπ` by the **proven weighted** `angleClassQ_cube_externalPartW_eq_zero`;
* the regular tetrahedron carries a pearl by `pearls_nonempty_of_pieces_nonempty` /
  `regularTetSolid_pieces_nonempty`.

The raw-count residual `EdgeCountBalance` of `Chapter09Final` is **eliminated**. -/
theorem chapter09_weighted_of_decomp
    (decomp : TetEquidecomp regularTetSolid.toTetSolid cubeSolid.toTetSolid) : False := by
  obtain ⟨νP, νQ, hνP, _, hbal⟩ :=
    weightedEdgeBalance_of_equidecomp decomp
      edgeSourceFaithful_regularTetSolid edgeSourceFaithful_cubeSolid
  exact regularTet_cube_no_equidecomp_weighted_corrected cubePearlAngleData decomp hνP hbal
    (pearls_nonempty_of_pieces_nonempty regularTetSolid_pieces_nonempty)

/-- **THE WEIGHTED CHAPTER 9 HEADLINE (`¬ Nonempty` form, no residual hypotheses).**

A regular tetrahedron is **not** equidecomposable with the Kuhn unit cube.  The type of
equidecompositions `TetEquidecomp regularTetSolid cubeSolid` is empty — established with **no residual
hypotheses**: the raw-count `EdgeCountBalance` residue of `Chapter09Final` is replaced throughout by
the proven weighted chain (positive integer pearl multiplicities from the Pearl Lemma, the weighted
edge balance, the weighted location classification on both solids, and the irrationality of
`arccos(1/3)` over `π`).  This is the faithful geometric form of Hilbert's third problem for this
concrete pair. -/
theorem chapter09_weighted :
    ¬ Nonempty (TetEquidecomp regularTetSolid.toTetSolid cubeSolid.toTetSolid) := by
  rintro ⟨decomp⟩
  exact chapter09_weighted_of_decomp decomp

end ProofsInTheBook.Chapter09Weighted

-- Axiom audit: the weighted headline depends only on the core three axioms.
#print axioms ProofsInTheBook.Chapter09Weighted.chapter09_weighted
