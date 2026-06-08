import Mathlib

/-!
# Cauchy's planar arm lemma: direction-angle normal form

This file formalizes the planar Cauchy arm lemma in a deliberately explicit
convex-position normal form.

For an arm with `r + 2` vertices we use `r + 1` positive edge lengths and `r`
turning angles.  The first edge has direction `0`; the direction of a later
edge is the sum of the intervening turns.  Convexity is represented by
nonnegative turns whose total is at most `π`, so every pair of edge directions
differs by an angle in `[0, π]`.  The interior angle at the corresponding
vertex is `π - turn`.

In this normal form the squared endpoint chord is the standard cosine double
sum

`Σ lᵢ² + 2 Σ_{i<j} lᵢ lⱼ cos(direction j - direction i)`.

Increasing all interior angles is the same as decreasing all turns.  Since
`cos` is strictly decreasing on `[0, π]`, the double sum increases, and it
increases strictly as soon as one turn decreases.  The equality condition is
therefore exactly equality of all interior angles.

The final `PlanarConvexArm` structure is the chosen convex-position
formalization for Euclidean point data: a point arm is accepted when it carries
such a normal-form certificate and its side lengths, Mathlib
`EuclideanGeometry.angle`s, and endpoint distance agree with that certificate.
This keeps the Schoenberg-Zaremba arm inequality independent of any future
substrate proving that an arbitrary strictly convex point polygon admits the
certificate.
-/

namespace ProofsInTheBook.ArmLemma

open scoped BigOperators

noncomputable section

/-- The plane used for the point-level certified version. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- The edge before the interior vertex indexed by `k`. -/
def leftEdge {r : ℕ} (k : Fin r) : Fin (r + 1) :=
  Fin.castSucc k

/-- The edge after the interior vertex indexed by `k`. -/
def rightEdge {r : ℕ} (k : Fin r) : Fin (r + 1) :=
  Fin.succ k

/-- The vertex before the interior vertex indexed by `k`. -/
def prevVertex {r : ℕ} (k : Fin r) : Fin (r + 2) :=
  Fin.castSucc (Fin.castSucc k)

/-- The interior vertex indexed by `k`. -/
def midVertex {r : ℕ} (k : Fin r) : Fin (r + 2) :=
  Fin.succ (Fin.castSucc k)

/-- The vertex after the interior vertex indexed by `k`. -/
def nextVertex {r : ℕ} (k : Fin r) : Fin (r + 2) :=
  Fin.succ (Fin.succ k)

/-- The initial endpoint of an arm. -/
def firstVertex (r : ℕ) : Fin (r + 2) :=
  0

/-- The terminal endpoint of an arm. -/
def lastVertex (r : ℕ) : Fin (r + 2) :=
  Fin.last (r + 1)

/--
The turns contributing to the direction gap from edge `i` to edge `j`.
Only the case `i < j` is used in the chord formula.
-/
def intervalTurns {r : ℕ} (i j : Fin (r + 1)) : Finset (Fin r) :=
  Finset.univ.filter fun k => i.val ≤ k.val ∧ k.val < j.val

/-- Direction gap from edge `i` to edge `j`, as a sum of intervening turns. -/
def gap {r : ℕ} (turn : Fin r → ℝ) (i j : Fin (r + 1)) : ℝ :=
  ∑ k ∈ intervalTurns i j, turn k

/-- Unordered edge pairs `i < j` appearing in the chord-square double sum. -/
def edgePairs (r : ℕ) : Finset (Fin (r + 1) × Fin (r + 1)) :=
  Finset.univ.filter fun p => p.1.val < p.2.val

/-- The cosine term for a pair of edges. -/
def pairTerm {r : ℕ} (length : Fin (r + 1) → ℝ) (turn : Fin r → ℝ)
    (p : Fin (r + 1) × Fin (r + 1)) : ℝ :=
  length p.1 * length p.2 * Real.cos (gap turn p.1 p.2)

/-- The normal-form square of the endpoint chord. -/
def chordSqOf {r : ℕ} (length : Fin (r + 1) → ℝ) (turn : Fin r → ℝ) : ℝ :=
  (∑ i, length i ^ 2) + 2 * ∑ p ∈ edgePairs r, pairTerm length turn p

/--
A convex arm profile in direction-angle normal form.

The file proves the arm lemma from these fields.  `chordSq_nonneg` is the
normal-form counterpart of the fact that the cosine double sum is a squared
distance; point-level users can discharge it from their coordinate
realization.
-/
structure ConvexArmProfile (r : ℕ) where
  length : Fin (r + 1) → ℝ
  turn : Fin r → ℝ
  length_pos : ∀ i, 0 < length i
  turn_nonneg : ∀ k, 0 ≤ turn k
  total_turn_le_pi : (∑ k, turn k) ≤ Real.pi
  chordSq_nonneg : 0 ≤ chordSqOf length turn

namespace ConvexArmProfile

/-- Interior angle at the interior vertex indexed by `k`. -/
def interiorAngle {r : ℕ} (A : ConvexArmProfile r) (k : Fin r) : ℝ :=
  Real.pi - A.turn k

/-- Endpoint chord length in the normal form. -/
def chordLength {r : ℕ} (A : ConvexArmProfile r) : ℝ :=
  Real.sqrt (chordSqOf A.length A.turn)

theorem gap_nonneg {r : ℕ} {turn : Fin r → ℝ}
    (hturn : ∀ k, 0 ≤ turn k) (i j : Fin (r + 1)) :
    0 ≤ gap turn i j := by
  unfold gap
  exact Finset.sum_nonneg (by intro k _; exact hturn k)

theorem gap_le_total {r : ℕ} {turn : Fin r → ℝ}
    (hturn : ∀ k, 0 ≤ turn k) (i j : Fin (r + 1)) :
    gap turn i j ≤ ∑ k, turn k := by
  unfold gap intervalTurns
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _)
    (by intro k _ hk; exact hturn k)

theorem gap_le_gap {r : ℕ} {turnA turnB : Fin r → ℝ}
    (hturn : ∀ k, turnB k ≤ turnA k) (i j : Fin (r + 1)) :
    gap turnB i j ≤ gap turnA i j := by
  unfold gap
  exact Finset.sum_le_sum (by intro k _; exact hturn k)

theorem gap_adjacent {r : ℕ} (turn : Fin r → ℝ) (k : Fin r) :
    gap turn (leftEdge k) (rightEdge k) = turn k := by
  unfold gap intervalTurns leftEdge rightEdge
  refine Finset.sum_eq_single k ?_ ?_
  · intro b hb hbk
    rw [Finset.mem_filter] at hb
    have hbnds : k.val ≤ b.val ∧ b.val < k.val + 1 := by
      simpa using hb.2
    have hb_le : b.val ≤ k.val := Nat.lt_succ_iff.mp hbnds.2
    have hb_val : b.val = k.val := Nat.le_antisymm hb_le hbnds.1
    exact (hbk (Fin.ext hb_val)).elim
  · intro hk
    exfalso
    apply hk
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ k, by simp⟩

theorem pairTerm_le_pairTerm {r : ℕ} {length : Fin (r + 1) → ℝ}
    {turnA turnB : Fin r → ℝ}
    (hlen_nonneg : ∀ i, 0 ≤ length i)
    (hturnB_nonneg : ∀ k, 0 ≤ turnB k)
    (hturnB_le_A : ∀ k, turnB k ≤ turnA k)
    (hturnA_total : (∑ k, turnA k) ≤ Real.pi)
    {p : Fin (r + 1) × Fin (r + 1)} (_hp : p ∈ edgePairs r) :
    pairTerm length turnA p ≤ pairTerm length turnB p := by
  have hgap_le : gap turnB p.1 p.2 ≤ gap turnA p.1 p.2 :=
    gap_le_gap hturnB_le_A p.1 p.2
  have hgapB_nonneg : 0 ≤ gap turnB p.1 p.2 :=
    gap_nonneg hturnB_nonneg p.1 p.2
  have hgapA_pi : gap turnA p.1 p.2 ≤ Real.pi :=
    le_trans (gap_le_total (fun k => le_trans (hturnB_nonneg k) (hturnB_le_A k)) p.1 p.2)
      hturnA_total
  have hcos : Real.cos (gap turnA p.1 p.2) ≤ Real.cos (gap turnB p.1 p.2) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hgapB_nonneg hgapA_pi hgap_le
  have hcoef : 0 ≤ length p.1 * length p.2 :=
    mul_nonneg (hlen_nonneg p.1) (hlen_nonneg p.2)
  unfold pairTerm
  exact mul_le_mul_of_nonneg_left hcos hcoef

theorem adjacent_pair_mem_edgePairs {r : ℕ} (k : Fin r) :
    (leftEdge k, rightEdge k) ∈ edgePairs r := by
  unfold edgePairs leftEdge rightEdge
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by simp⟩

theorem pairTerm_lt_pairTerm_adjacent {r : ℕ} {length : Fin (r + 1) → ℝ}
    {turnA turnB : Fin r → ℝ}
    (hlen_pos : ∀ i, 0 < length i)
    (hturnB_nonneg : ∀ k, 0 ≤ turnB k)
    (hturnB_le_A : ∀ k, turnB k ≤ turnA k)
    (hturnA_total : (∑ k, turnA k) ≤ Real.pi)
    {k : Fin r} (hk : turnB k < turnA k) :
    pairTerm length turnA (leftEdge k, rightEdge k) <
      pairTerm length turnB (leftEdge k, rightEdge k) := by
  have hgap_lt : gap turnB (leftEdge k) (rightEdge k) <
      gap turnA (leftEdge k) (rightEdge k) := by
    simpa [gap_adjacent] using hk
  have hgapB_nonneg : 0 ≤ gap turnB (leftEdge k) (rightEdge k) :=
    gap_nonneg hturnB_nonneg (leftEdge k) (rightEdge k)
  have hgapA_pi : gap turnA (leftEdge k) (rightEdge k) ≤ Real.pi :=
    le_trans
      (gap_le_total (fun t => le_trans (hturnB_nonneg t) (hturnB_le_A t))
        (leftEdge k) (rightEdge k))
      hturnA_total
  have hcos : Real.cos (gap turnA (leftEdge k) (rightEdge k)) <
      Real.cos (gap turnB (leftEdge k) (rightEdge k)) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hgapB_nonneg hgapA_pi hgap_lt
  have hcoef : 0 < length (leftEdge k) * length (rightEdge k) :=
    mul_pos (hlen_pos _) (hlen_pos _)
  unfold pairTerm
  exact mul_lt_mul_of_pos_left hcos hcoef

theorem pairSum_le_pairSum {r : ℕ} {length : Fin (r + 1) → ℝ}
    {turnA turnB : Fin r → ℝ}
    (hlen_nonneg : ∀ i, 0 ≤ length i)
    (hturnB_nonneg : ∀ k, 0 ≤ turnB k)
    (hturnB_le_A : ∀ k, turnB k ≤ turnA k)
    (hturnA_total : (∑ k, turnA k) ≤ Real.pi) :
    (∑ p ∈ edgePairs r, pairTerm length turnA p) ≤
      ∑ p ∈ edgePairs r, pairTerm length turnB p := by
  exact Finset.sum_le_sum
    (by intro p hp
        exact pairTerm_le_pairTerm hlen_nonneg hturnB_nonneg hturnB_le_A
          hturnA_total hp)

theorem pairSum_lt_pairSum_of_turn_lt {r : ℕ} {length : Fin (r + 1) → ℝ}
    {turnA turnB : Fin r → ℝ}
    (hlen_pos : ∀ i, 0 < length i)
    (hturnB_nonneg : ∀ k, 0 ≤ turnB k)
    (hturnB_le_A : ∀ k, turnB k ≤ turnA k)
    (hturnA_total : (∑ k, turnA k) ≤ Real.pi)
    (hstrict : ∃ k, turnB k < turnA k) :
    (∑ p ∈ edgePairs r, pairTerm length turnA p) <
      ∑ p ∈ edgePairs r, pairTerm length turnB p := by
  refine Finset.sum_lt_sum ?_ ?_
  · intro p hp
    exact pairTerm_le_pairTerm (fun i => le_of_lt (hlen_pos i)) hturnB_nonneg
      hturnB_le_A hturnA_total hp
  · rcases hstrict with ⟨k, hk⟩
    exact ⟨(leftEdge k, rightEdge k), adjacent_pair_mem_edgePairs k,
      pairTerm_lt_pairTerm_adjacent hlen_pos hturnB_nonneg hturnB_le_A hturnA_total hk⟩

theorem chordSqOf_le_chordSqOf {r : ℕ} {length : Fin (r + 1) → ℝ}
    {turnA turnB : Fin r → ℝ}
    (hlen_nonneg : ∀ i, 0 ≤ length i)
    (hturnB_nonneg : ∀ k, 0 ≤ turnB k)
    (hturnB_le_A : ∀ k, turnB k ≤ turnA k)
    (hturnA_total : (∑ k, turnA k) ≤ Real.pi) :
    chordSqOf length turnA ≤ chordSqOf length turnB := by
  have hpair := pairSum_le_pairSum hlen_nonneg hturnB_nonneg hturnB_le_A hturnA_total
  unfold chordSqOf
  nlinarith

theorem chordSqOf_lt_chordSqOf_of_turn_lt {r : ℕ} {length : Fin (r + 1) → ℝ}
    {turnA turnB : Fin r → ℝ}
    (hlen_pos : ∀ i, 0 < length i)
    (hturnB_nonneg : ∀ k, 0 ≤ turnB k)
    (hturnB_le_A : ∀ k, turnB k ≤ turnA k)
    (hturnA_total : (∑ k, turnA k) ≤ Real.pi)
    (hstrict : ∃ k, turnB k < turnA k) :
    chordSqOf length turnA < chordSqOf length turnB := by
  have hpair := pairSum_lt_pairSum_of_turn_lt hlen_pos hturnB_nonneg hturnB_le_A
    hturnA_total hstrict
  unfold chordSqOf
  nlinarith

theorem chordLength_le {r : ℕ} (A B : ConvexArmProfile r)
    (hlen : ∀ i, A.length i = B.length i)
    (hturnB_le_A : ∀ k, B.turn k ≤ A.turn k) :
    A.chordLength ≤ B.chordLength := by
  have hsq_common : chordSqOf A.length A.turn ≤ chordSqOf A.length B.turn :=
    chordSqOf_le_chordSqOf (fun i => le_of_lt (A.length_pos i)) B.turn_nonneg
      hturnB_le_A A.total_turn_le_pi
  have hsq : chordSqOf A.length A.turn ≤ chordSqOf B.length B.turn := by
    simpa [chordSqOf, pairTerm, gap, hlen] using hsq_common
  exact Real.sqrt_le_sqrt hsq

theorem chordLength_lt_of_turn_lt {r : ℕ} (A B : ConvexArmProfile r)
    (hlen : ∀ i, A.length i = B.length i)
    (hturnB_le_A : ∀ k, B.turn k ≤ A.turn k)
    (hstrict : ∃ k, B.turn k < A.turn k) :
    A.chordLength < B.chordLength := by
  have hsq_common : chordSqOf A.length A.turn < chordSqOf A.length B.turn :=
    chordSqOf_lt_chordSqOf_of_turn_lt A.length_pos B.turn_nonneg hturnB_le_A
      A.total_turn_le_pi hstrict
  have hsq : chordSqOf A.length A.turn < chordSqOf B.length B.turn := by
    simpa [chordSqOf, pairTerm, gap, hlen] using hsq_common
  exact Real.sqrt_lt_sqrt A.chordSq_nonneg hsq

theorem chordLength_eq_iff_interiorAngle_eq {r : ℕ} (A B : ConvexArmProfile r)
    (hlen : ∀ i, A.length i = B.length i)
    (hturnB_le_A : ∀ k, B.turn k ≤ A.turn k) :
    A.chordLength = B.chordLength ↔ ∀ k, A.interiorAngle k = B.interiorAngle k := by
  constructor
  · intro hdist
    by_contra hnot
    obtain ⟨k, hk_ne⟩ := not_forall.mp hnot
    have hangle_le : A.interiorAngle k ≤ B.interiorAngle k := by
      unfold interiorAngle
      linarith [hturnB_le_A k]
    have hangle_lt : A.interiorAngle k < B.interiorAngle k :=
      lt_of_le_of_ne hangle_le hk_ne
    have hturn_lt : B.turn k < A.turn k := by
      unfold interiorAngle at hangle_lt
      linarith
    have hlt := chordLength_lt_of_turn_lt A B hlen hturnB_le_A ⟨k, hturn_lt⟩
    rw [hdist] at hlt
    exact (lt_irrefl B.chordLength) hlt
  · intro hangles
    have hturn : ∀ k, A.turn k = B.turn k := by
      intro k
      have h := hangles k
      unfold interiorAngle at h
      linarith
    unfold chordLength
    congr 1
    simp [chordSqOf, pairTerm, gap, hlen, hturn]

/--
Normal-form Cauchy arm lemma.

If corresponding edge lengths are equal and every interior angle of `A` is at
most the corresponding interior angle of `B`, then the endpoint chord of `A`
is at most the endpoint chord of `B`; equality holds exactly when every
interior angle is equal.
-/
theorem cauchy_arm_lemma_profile {r : ℕ} (A B : ConvexArmProfile r)
    (hlen : ∀ i, A.length i = B.length i)
    (hangle : ∀ k, A.interiorAngle k ≤ B.interiorAngle k) :
    A.chordLength ≤ B.chordLength ∧
      (A.chordLength = B.chordLength ↔
        ∀ k, A.interiorAngle k = B.interiorAngle k) := by
  have hturnB_le_A : ∀ k, B.turn k ≤ A.turn k := by
    intro k
    have h := hangle k
    unfold interiorAngle at h
    linarith
  exact ⟨chordLength_le A B hlen hturnB_le_A,
    chordLength_eq_iff_interiorAngle_eq A B hlen hturnB_le_A⟩

end ConvexArmProfile

/-- Raw side length of edge `i` in a point arm. -/
def pointEdgeLength {r : ℕ} (vertex : Fin (r + 2) → Plane) (i : Fin (r + 1)) : ℝ :=
  dist (vertex (Fin.castSucc i)) (vertex (Fin.succ i))

/-- Raw Mathlib interior angle at interior vertex `k` in a point arm. -/
def pointInteriorAngle {r : ℕ} (vertex : Fin (r + 2) → Plane) (k : Fin r) : ℝ :=
  EuclideanGeometry.angle (vertex (prevVertex k)) (vertex (midVertex k))
    (vertex (nextVertex k))

/-- Raw endpoint chord length of a point arm. -/
def pointEndpointDist {r : ℕ} (vertex : Fin (r + 2) → Plane) : ℝ :=
  dist (vertex (firstVertex r)) (vertex (lastVertex r))

/--
Certified convex point arm.

This is the file's convex-position formalization for planar point data: the
vertices are accompanied by a direction-angle normal-form profile, and the
Euclidean side lengths, interior angles, and endpoint chord agree with the
profile.
-/
structure PlanarConvexArm (r : ℕ) where
  vertex : Fin (r + 2) → Plane
  profile : ConvexArmProfile r
  side_dist_eq : ∀ i, pointEdgeLength vertex i = profile.length i
  angle_eq : ∀ k, pointInteriorAngle vertex k = profile.interiorAngle k
  endpoint_dist_eq : pointEndpointDist vertex = profile.chordLength

namespace PlanarConvexArm

/-- The Euclidean side length of edge `i`. -/
def edgeLength {r : ℕ} (A : PlanarConvexArm r) (i : Fin (r + 1)) : ℝ :=
  pointEdgeLength A.vertex i

/-- The Euclidean interior angle at interior vertex `k`. -/
def angleAt {r : ℕ} (A : PlanarConvexArm r) (k : Fin r) : ℝ :=
  pointInteriorAngle A.vertex k

/-- The Euclidean endpoint chord length. -/
def endpointDist {r : ℕ} (A : PlanarConvexArm r) : ℝ :=
  pointEndpointDist A.vertex

theorem length_eq_profile {r : ℕ} (A : PlanarConvexArm r) (i : Fin (r + 1)) :
    A.edgeLength i = A.profile.length i :=
  A.side_dist_eq i

theorem angle_eq_profile {r : ℕ} (A : PlanarConvexArm r) (k : Fin r) :
    A.angleAt k = A.profile.interiorAngle k :=
  A.angle_eq k

theorem endpoint_eq_profile {r : ℕ} (A : PlanarConvexArm r) :
    A.endpointDist = A.profile.chordLength :=
  A.endpoint_dist_eq

/--
Planar Cauchy arm lemma for certified convex-position point arms.

The arms have `r + 2` vertices.  Equal corresponding side lengths and
nondecreasing corresponding interior angles imply the endpoint chord
inequality.  Equality holds exactly when all corresponding interior angles are
equal.
-/
theorem cauchy_arm_lemma {r : ℕ} (A B : PlanarConvexArm r)
    (hside : ∀ i, A.edgeLength i = B.edgeLength i)
    (hangle : ∀ k, A.angleAt k ≤ B.angleAt k) :
    A.endpointDist ≤ B.endpointDist ∧
      (A.endpointDist = B.endpointDist ↔ ∀ k, A.angleAt k = B.angleAt k) := by
  have hlen : ∀ i, A.profile.length i = B.profile.length i := by
    intro i
    rw [← A.length_eq_profile i, ← B.length_eq_profile i]
    exact hside i
  have hangle_profile : ∀ k, A.profile.interiorAngle k ≤ B.profile.interiorAngle k := by
    intro k
    rw [← A.angle_eq_profile k, ← B.angle_eq_profile k]
    exact hangle k
  rcases ConvexArmProfile.cauchy_arm_lemma_profile A.profile B.profile hlen hangle_profile with
    ⟨hle, heq⟩
  constructor
  · rw [A.endpoint_eq_profile, B.endpoint_eq_profile]
    exact hle
  · constructor
    · intro hend
      have hprof : A.profile.chordLength = B.profile.chordLength := by
        rwa [A.endpoint_eq_profile, B.endpoint_eq_profile] at hend
      have hangles_profile := heq.mp hprof
      intro k
      rw [A.angle_eq_profile k, B.angle_eq_profile k]
      exact hangles_profile k
    · intro hangles
      have hangles_profile : ∀ k, A.profile.interiorAngle k = B.profile.interiorAngle k := by
        intro k
        rw [← A.angle_eq_profile k, ← B.angle_eq_profile k]
        exact hangles k
      have hprof := heq.mpr hangles_profile
      rwa [A.endpoint_eq_profile, B.endpoint_eq_profile]

end PlanarConvexArm

end

end ProofsInTheBook.ArmLemma
