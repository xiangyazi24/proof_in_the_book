import Mathlib

/-!
# Chapter 10: Lines in the plane and decompositions of graphs

From "Proofs from THE BOOK":

**Sylvester-Gallai theorem**: Given a finite set of points in the plane,
not all collinear, there exists a line passing through exactly two of them.

The book's proof (by T. Gallai): Among all pairs (P, ℓ) where P is a point
not on line ℓ (spanned by other points), choose the pair minimizing
dist(P, ℓ). If ℓ contains ≥ 3 points, one can find a closer pair,
contradicting minimality.

The chapter also discusses graph decompositions and the related
theorem about bipartite graphs.
-/

namespace ProofsInTheBook.Chapter10

/-!
### Sylvester-Gallai theorem

The proof by Gallai's extremal argument is a beautiful application of
the well-ordering principle. The formalization requires:
1. A finite point set in ℝ² (or an affine plane)
2. The notion of a line through two points
3. The distance from a point to a line
4. The extremal argument

This geometric result is not yet in Mathlib.
-/

/-- The points of a finite configuration lying on a candidate line. -/
def pointsOnLine {Point Line : Type*} [DecidableEq Point] (points : Finset Point)
    (onLine : Point → Line → Prop) [DecidableRel onLine] (line : Line) : Finset Point :=
  points.filter fun p => onLine p line

/--
Finite candidate set for Gallai's extremal proof: pairs `(P, l)` where `P`
is one of the configuration points and does not lie on the candidate line `l`.
-/
def offLinePairs {Point Line : Type*} [DecidableEq Point] [DecidableEq Line]
    (points : Finset Point) (lines : Finset Line)
    (onLine : Point → Line → Prop) [DecidableRel onLine] : Finset (Point × Line) :=
  (points.product lines).filter fun pl => ¬ onLine pl.1 pl.2

theorem mem_offLinePairs {Point Line : Type*} [DecidableEq Point] [DecidableEq Line]
    {points : Finset Point} {lines : Finset Line}
    {onLine : Point → Line → Prop} [DecidableRel onLine] {p : Point} {line : Line} :
    (p, line) ∈ offLinePairs points lines onLine ↔
      p ∈ points ∧ line ∈ lines ∧ ¬ onLine p line := by
  simp [offLinePairs, and_assoc]

theorem offLinePairs_nonempty_of_exists {Point Line : Type*}
    [DecidableEq Point] [DecidableEq Line] {points : Finset Point}
    {lines : Finset Line} {onLine : Point → Line → Prop} [DecidableRel onLine]
    (h : ∃ p ∈ points, ∃ line ∈ lines, ¬ onLine p line) :
    (offLinePairs points lines onLine).Nonempty := by
  rcases h with ⟨p, hp, line, hline, hoff⟩
  exact ⟨(p, line), mem_offLinePairs.mpr ⟨hp, hline, hoff⟩⟩

/--
The finite extremal step in Gallai's proof: once the candidate set of
point-line pairs is nonempty, any ordered distance value has a minimizing
candidate.
-/
theorem exists_minimal_offLinePair {Point Line Dist : Type*}
    [DecidableEq Point] [DecidableEq Line] [LinearOrder Dist]
    (points : Finset Point) (lines : Finset Line)
    (onLine : Point → Line → Prop) [DecidableRel onLine]
    (dist : Point → Line → Dist)
    (hne : (offLinePairs points lines onLine).Nonempty) :
    ∃ p line,
      p ∈ points ∧ line ∈ lines ∧ ¬ onLine p line ∧
      ∀ p' line', p' ∈ points → line' ∈ lines → ¬ onLine p' line' →
        dist p line ≤ dist p' line' := by
  obtain ⟨pair, hpair, hmin⟩ :=
    Finset.exists_min_image (offLinePairs points lines onLine)
      (fun pl : Point × Line => dist pl.1 pl.2) hne
  rcases pair with ⟨p, line⟩
  rcases mem_offLinePairs.mp hpair with ⟨hp, hline, hoff⟩
  refine ⟨p, line, hp, hline, hoff, ?_⟩
  intro p' line' hp' hline' hoff'
  exact hmin (p', line') (mem_offLinePairs.mpr ⟨hp', hline', hoff'⟩)

/--
An ordinary line for a finite point configuration: exactly two configuration
points lie on the line.
-/
def OrdinaryLine {Point Line : Type*} [DecidableEq Point] (points : Finset Point)
    (onLine : Point → Line → Prop) [DecidableRel onLine] (line : Line) : Prop :=
  ∃ p q, p ∈ points ∧ q ∈ points ∧ p ≠ q ∧ onLine p line ∧ onLine q line ∧
    ∀ r ∈ points, onLine r line → r = p ∨ r = q

theorem ordinaryLine_of_two_points_on_line {Point Line : Type*} [DecidableEq Point]
    (points : Finset Point) (onLine : Point → Line → Prop) [DecidableRel onLine]
    (line : Line) (hcard : (pointsOnLine points onLine line).card = 2) :
    OrdinaryLine points onLine line := by
  obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hcard
  have hp : p ∈ points ∧ onLine p line := by
    have : p ∈ pointsOnLine points onLine line := by simp [hset]
    simpa [pointsOnLine] using this
  have hq : q ∈ points ∧ onLine q line := by
    have : q ∈ pointsOnLine points onLine line := by simp [hset]
    simpa [pointsOnLine] using this
  refine ⟨p, q, hp.1, hq.1, hpq, hp.2, hq.2, ?_⟩
  intro r hr hline
  have hrset : r ∈ pointsOnLine points onLine line := by simp [pointsOnLine, hr, hline]
  simpa [hset] using hrset

/-- Converse of `ordinaryLine_of_two_points_on_line`: an ordinary line has
exactly two configuration points on it. -/
theorem card_pointsOnLine_eq_two_of_ordinaryLine {Point Line : Type*}
    [DecidableEq Point] (points : Finset Point)
    (onLine : Point → Line → Prop) [DecidableRel onLine] (line : Line)
    (h : OrdinaryLine points onLine line) :
    (pointsOnLine points onLine line).card = 2 := by
  obtain ⟨p, q, hp, hq, hpq, hpl, hql, hall⟩ := h
  refine Finset.card_eq_two.mpr ⟨p, q, hpq, ?_⟩
  ext r
  simp only [pointsOnLine, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hr, hrl⟩
    exact hall r hr hrl
  · rintro (rfl | rfl)
    · exact ⟨hp, hpl⟩
    · exact ⟨hq, hql⟩

/-- `OrdinaryLine` iff exactly two configuration points lie on the line. -/
theorem ordinaryLine_iff_card_pointsOnLine_eq_two {Point Line : Type*}
    [DecidableEq Point] (points : Finset Point)
    (onLine : Point → Line → Prop) [DecidableRel onLine] (line : Line) :
    OrdinaryLine points onLine line ↔ (pointsOnLine points onLine line).card = 2 :=
  ⟨card_pointsOnLine_eq_two_of_ordinaryLine points onLine line,
   ordinaryLine_of_two_points_on_line points onLine line⟩

/-- `pointsOnLine` is a subset of the configuration points. -/
theorem pointsOnLine_subset {Point Line : Type*} [DecidableEq Point]
    (points : Finset Point) (onLine : Point → Line → Prop) [DecidableRel onLine]
    (line : Line) :
    pointsOnLine points onLine line ⊆ points :=
  Finset.filter_subset _ _

/-- `pointsOnLine` is bounded above by `points.card`. -/
theorem pointsOnLine_card_le {Point Line : Type*} [DecidableEq Point]
    (points : Finset Point) (onLine : Point → Line → Prop) [DecidableRel onLine]
    (line : Line) :
    (pointsOnLine points onLine line).card ≤ points.card :=
  Finset.card_le_card (pointsOnLine_subset points onLine line)

/-- `pointsOnLine` is empty iff no point lies on the line. -/
theorem pointsOnLine_eq_empty_iff {Point Line : Type*} [DecidableEq Point]
    (points : Finset Point) (onLine : Point → Line → Prop) [DecidableRel onLine]
    (line : Line) :
    pointsOnLine points onLine line = ∅ ↔ ∀ p ∈ points, ¬ onLine p line := by
  rw [Finset.eq_empty_iff_forall_notMem]
  simp [pointsOnLine, Finset.mem_filter]

/-- `offLinePairs` is nonempty iff some point is off some line — biconditional
form of `offLinePairs_nonempty_of_exists`. -/
theorem offLinePairs_nonempty_iff {Point Line : Type*}
    [DecidableEq Point] [DecidableEq Line] {points : Finset Point}
    {lines : Finset Line} {onLine : Point → Line → Prop} [DecidableRel onLine] :
    (offLinePairs points lines onLine).Nonempty ↔
      ∃ p ∈ points, ∃ line ∈ lines, ¬ onLine p line := by
  constructor
  · rintro ⟨⟨p, line⟩, hpair⟩
    rcases mem_offLinePairs.mp hpair with ⟨hp, hline, hoff⟩
    exact ⟨p, hp, line, hline, hoff⟩
  · exact offLinePairs_nonempty_of_exists

/-- `OrdinaryLine` implies `≥ 2` configuration points lie on the line. -/
theorem two_le_card_pointsOnLine_of_ordinaryLine {Point Line : Type*}
    [DecidableEq Point] (points : Finset Point)
    (onLine : Point → Line → Prop) [DecidableRel onLine] (line : Line)
    (h : OrdinaryLine points onLine line) :
    2 ≤ (pointsOnLine points onLine line).card := by
  rw [card_pointsOnLine_eq_two_of_ordinaryLine points onLine line h]


/-- `offLinePairs` is empty iff every configuration point lies on every
candidate line — the "trivially collinear" degenerate case. -/
theorem offLinePairs_eq_empty_iff {Point Line : Type*}
    [DecidableEq Point] [DecidableEq Line]
    (points : Finset Point) (lines : Finset Line)
    (onLine : Point → Line → Prop) [DecidableRel onLine] :
    offLinePairs points lines onLine = ∅ ↔
      ∀ p ∈ points, ∀ line ∈ lines, onLine p line := by
  constructor
  · intro h p hp line hline
    by_contra hoff
    have : (p, line) ∈ offLinePairs points lines onLine :=
      mem_offLinePairs.mpr ⟨hp, hline, hoff⟩
    rw [h] at this
    exact absurd this (Finset.notMem_empty _)
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    rintro ⟨p, line⟩ hmem
    rcases mem_offLinePairs.mp hmem with ⟨hp, hline, hoff⟩
    exact hoff (h p hp line hline)

/--
The key contradiction step in Gallai's proof: if a line contains ≥ 3 points
and is part of a minimal-distance off-line pair, then a strictly closer
off-line pair can be found. This is the geometric heart of the argument.
-/
theorem gallai_closer_pair_contradiction {Point Line : Type*}
    [DecidableEq Point] [DecidableEq Line]
    (points : Finset Point) (lines : Finset Line)
    (onLine : Point → Line → Prop) [DecidableRel onLine]
    (dist : Point → Line → ℕ)
    (p : Point) (line : Line)
    (_hp : p ∈ points) (_hline : line ∈ lines)
    (_hoff : ¬ onLine p line)
    (hmin : ∀ p' line', p' ∈ points → line' ∈ lines → ¬ onLine p' line' →
      dist p line ≤ dist p' line')
    (_hge3 : 2 < (pointsOnLine points onLine line).card)
    (footLine : Point → Line → Point)
    (_hFoot : ∀ pt l, footLine pt l ∈ points → onLine (footLine pt l) l)
    (closerPoint : Point → Line → Line → Point)
    (hCloser : ∀ pt l q, closerPoint pt l q ∈ points →
      ¬ onLine (closerPoint pt l q) q →
      dist (closerPoint pt l q) q < dist pt l)
    (newLine : Line) (hnewLine : newLine ∈ lines)
    (hCloserMem : closerPoint p line newLine ∈ points)
    (hCloserOff : ¬ onLine (closerPoint p line newLine) newLine) :
    False :=
  absurd (hmin _ _ hCloserMem hnewLine hCloserOff)
    (Nat.not_le.mpr (hCloser p line newLine hCloserMem hCloserOff))

/--
Sylvester-Gallai theorem (abstract): given a finite point set with at
least one line containing ≥ 2 points and an off-line pair, some line
passes through exactly two points.
-/
theorem sylvester_gallai_abstract {Point Line : Type*}
    [DecidableEq Point] [DecidableEq Line]
    (points : Finset Point) (lines : Finset Line)
    (onLine : Point → Line → Prop) [DecidableRel onLine]
    (dist : Point → Line → ℕ)
    (hne : (offLinePairs points lines onLine).Nonempty)
    (gallai : ∀ line ∈ lines, 2 < (pointsOnLine points onLine line).card →
      ∃ line' ∈ lines, (pointsOnLine points onLine line').card ≤
        (pointsOnLine points onLine line).card ∧
        (pointsOnLine points onLine line').card ≤ 2) :
    ∃ line ∈ lines, (pointsOnLine points onLine line).card = 2 ∨
      (pointsOnLine points onLine line).card ≤ 1 := by
  obtain ⟨⟨p, line⟩, hpair, hmin_pair⟩ :=
    Finset.exists_min_image _ (fun pl => dist pl.1 pl.2) hne
  have hmem := mem_offLinePairs.mp hpair
  by_cases hcard : (pointsOnLine points onLine line).card ≤ 2
  · exact ⟨line, hmem.2.1, by omega⟩
  · push Not at hcard
    obtain ⟨line', hline', _, hle⟩ := gallai line hmem.2.1 (by omega)
    exact ⟨line', hline', by omega⟩

theorem ordinaryLine_of_card_pointsOnLine_eq_two {Point Line : Type*} [DecidableEq Point]
    (points : Finset Point) (onLine : Point → Line → Prop) [DecidableRel onLine]
    (line : Line) (hcard : (pointsOnLine points onLine line).card = 2) :
    OrdinaryLine points onLine line :=
  ordinaryLine_of_two_points_on_line points onLine line hcard

/-- Direct existential constructor for `OrdinaryLine`: two configuration points
on a line, plus a "no third point" guarantee, suffice. -/
theorem ordinaryLine_of_two_distinct_points {Point Line : Type*} [DecidableEq Point]
    (points : Finset Point) (onLine : Point → Line → Prop) [DecidableRel onLine]
    (line : Line) {p q : Point}
    (hp : p ∈ points) (hq : q ∈ points) (hpq : p ≠ q)
    (hpL : onLine p line) (hqL : onLine q line)
    (hno_third : ∀ r ∈ points, onLine r line → r = p ∨ r = q) :
    OrdinaryLine points onLine line :=
  ⟨p, q, hp, hq, hpq, hpL, hqL, hno_third⟩

/-- An `OrdinaryLine` always has its on-line point set equal to the two-point
set of its witnesses. -/
theorem pointsOnLine_eq_pair_of_ordinaryLine {Point Line : Type*}
    [DecidableEq Point] (points : Finset Point)
    (onLine : Point → Line → Prop) [DecidableRel onLine] (line : Line)
    (h : OrdinaryLine points onLine line) :
    ∃ p q : Point, p ∈ points ∧ q ∈ points ∧ p ≠ q ∧
      pointsOnLine points onLine line = {p, q} := by
  obtain ⟨p, q, hp, hq, hpq, hpL, hqL, hall⟩ := h
  refine ⟨p, q, hp, hq, hpq, ?_⟩
  ext r
  simp only [pointsOnLine, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hr, hrl⟩; exact hall r hr hrl
  · rintro (rfl | rfl)
    · exact ⟨hp, hpL⟩
    · exact ⟨hq, hqL⟩

/-- Stronger packaging of `sylvester_gallai_abstract`: there exists a line
with at most 2 configuration points (combining the `card = 2 ∨ card ≤ 1`
conclusion into a single bound). -/
theorem sylvester_gallai_abstract_card_le {Point Line : Type*}
    [DecidableEq Point] [DecidableEq Line]
    (points : Finset Point) (lines : Finset Line)
    (onLine : Point → Line → Prop) [DecidableRel onLine]
    (dist : Point → Line → ℕ)
    (hne : (offLinePairs points lines onLine).Nonempty)
    (gallai : ∀ line ∈ lines, 2 < (pointsOnLine points onLine line).card →
      ∃ line' ∈ lines, (pointsOnLine points onLine line').card ≤
        (pointsOnLine points onLine line).card ∧
        (pointsOnLine points onLine line').card ≤ 2) :
    ∃ line ∈ lines, (pointsOnLine points onLine line).card ≤ 2 := by
  obtain ⟨line, hline, h⟩ := sylvester_gallai_abstract points lines onLine dist hne gallai
  exact ⟨line, hline, by rcases h with h | h <;> omega⟩

/-! ## Concrete Euclidean Sylvester–Gallai (Kelly's proof — step 1)

The abstract development above reduces Sylvester–Gallai to the `gallai`
extremal step, supplied as a hypothesis.  To discharge that hypothesis we
work in the concrete plane `EuclideanSpace ℝ (Fin 2)` and follow L. M. Kelly's
metric proof: among all (point, spanned-line) pairs with the point off the
line, a pair of *minimum perpendicular distance* must determine an ordinary
line.

This section builds the metric foundation: the perpendicular distance to the
line through two points, its basic properties, and existence of a minimizing
pair over a finite non-collinear set. -/

section EuclideanSylvesterGallai

open Metric

/-- A point in the Euclidean plane. -/
abbrev EPoint := EuclideanSpace ℝ (Fin 2)

/-- Perpendicular distance from `P` to the line through `a` and `b`
(`= 0` when `a = b`, since the "line" degenerates to a point/`infDist` to it). -/
noncomputable def perpDist (P a b : EPoint) : ℝ :=
  Metric.infDist P (affineSpan ℝ {a, b} : Set EPoint)

/-- Perpendicular distance is nonnegative. -/
theorem perpDist_nonneg (P a b : EPoint) : 0 ≤ perpDist P a b :=
  Metric.infDist_nonneg

/-- A point on the line has zero perpendicular distance to it. -/
theorem perpDist_eq_zero_of_mem {P a b : EPoint}
    (h : P ∈ affineSpan ℝ {a, b}) : perpDist P a b = 0 :=
  Metric.infDist_zero_of_mem h

/-- The perpendicular distance to a line is bounded by the distance to any
point on that line — in particular to each spanning point. -/
theorem perpDist_le_dist_left (P a b : EPoint) : perpDist P a b ≤ dist P a :=
  Metric.infDist_le_dist_of_mem (left_mem_affineSpan_pair ℝ a b)

theorem perpDist_le_dist_right (P a b : EPoint) : perpDist P a b ≤ dist P b :=
  Metric.infDist_le_dist_of_mem (right_mem_affineSpan_pair ℝ a b)

/-- The line through two points is a closed set (finite-dimensional affine
subspace), so a point with zero perpendicular distance actually lies on it. -/
theorem mem_of_perpDist_eq_zero {P a b : EPoint}
    (h : perpDist P a b = 0) : P ∈ affineSpan ℝ {a, b} := by
  have hclosed : IsClosed (affineSpan ℝ {a, b} : Set EPoint) :=
    (affineSpan ℝ {a, b}).closed_of_finiteDimensional
  have hne : (affineSpan ℝ {a, b} : Set EPoint).Nonempty :=
    ⟨a, left_mem_affineSpan_pair ℝ a b⟩
  rw [← SetLike.mem_coe, hclosed.mem_iff_infDist_zero hne]
  exact h

/-- Perpendicular distance is zero **iff** the point lies on the line. -/
theorem perpDist_eq_zero_iff {P a b : EPoint} :
    perpDist P a b = 0 ↔ P ∈ affineSpan ℝ {a, b} :=
  ⟨mem_of_perpDist_eq_zero, perpDist_eq_zero_of_mem⟩

/-- A point off the line has strictly positive perpendicular distance. -/
theorem perpDist_pos {P a b : EPoint}
    (h : P ∉ affineSpan ℝ {a, b}) : 0 < perpDist P a b :=
  lt_of_le_of_ne (perpDist_nonneg P a b) fun hz => h (mem_of_perpDist_eq_zero hz.symm)

/-- An "off-line incidence" of a finite point set `S`: two distinct points
`a, b ∈ S` and a third point `P ∈ S` not on the line they span.  This is the
constructive content of `S` being non-collinear, and the genuine hypothesis of
Sylvester–Gallai. -/
structure OffLineTriple (S : Finset EPoint) where
  P : EPoint
  a : EPoint
  b : EPoint
  hP : P ∈ S
  ha : a ∈ S
  hb : b ∈ S
  hab : a ≠ b
  hoff : P ∉ affineSpan ℝ {a, b}

/-- The incidences of `S` form a finite type: the map to `(P, a, b)` is
injective (the remaining fields are propositions) and lands in the finite set
`S ×ˢ S ×ˢ S`. -/
instance (S : Finset EPoint) : Finite (OffLineTriple S) := by
  apply Finite.of_injective
    (β := {x : EPoint × EPoint × EPoint // x ∈ S ×ˢ S ×ˢ S})
    (fun t => ⟨(t.P, t.a, t.b),
      Finset.mem_product.mpr ⟨t.hP, Finset.mem_product.mpr ⟨t.ha, t.hb⟩⟩⟩)
  rintro ⟨P₁, a₁, b₁, _, _, _, _, _⟩ ⟨P₂, a₂, b₂, _, _, _, _, _⟩ h
  simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨hP, ha, hb⟩ := h
  subst hP; subst ha; subst hb; rfl

/-- The line through two points, as a nonempty affine subspace instance. -/
instance instNonemptyLinePair (a b : EPoint) :
    Nonempty (affineSpan ℝ {a, b} : AffineSubspace ℝ EPoint) :=
  ⟨a, left_mem_affineSpan_pair ℝ a b⟩

/-- Foot of the perpendicular from `P` to the line through `a` and `b`. -/
noncomputable def foot (P a b : EPoint) : EPoint :=
  EuclideanGeometry.orthogonalProjection (affineSpan ℝ {a, b}) P

/-- The foot of the perpendicular lies on the line. -/
theorem foot_mem (P a b : EPoint) : foot P a b ∈ affineSpan ℝ {a, b} :=
  EuclideanGeometry.orthogonalProjection_mem P

/-- The perpendicular distance equals the distance to the foot of the
perpendicular (`orthogonalProjection` realises the infimum). -/
theorem perpDist_eq_dist_foot (P a b : EPoint) :
    perpDist P a b = dist P (foot P a b) :=
  (EuclideanGeometry.dist_orthogonalProjection_eq_infDist (affineSpan ℝ {a, b}) P).symm

/-- Pythagorean identity for the foot: `PR² = RF² + PF²` when `R` lies on the
line and `F` is the foot of the perpendicular from `P`. -/
theorem dist_sq_eq_foot {P a b R : EPoint} (hR : R ∈ affineSpan ℝ {a, b}) :
    dist R P * dist R P
      = dist R (foot P a b) * dist R (foot P a b)
        + dist P (foot P a b) * dist P (foot P a b) :=
  EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    (s := affineSpan ℝ {a, b}) P hR

/-- **Kelly step 3b: the closer point is strictly nearer on the cross-line.**
If `R` is on the line and `Q` lies between the foot `F` and `R`, while `P` is
off the line, then `dist Q R < dist P R`.  (Pythagoras: `PR² = RF² + PF²` with
`PF > 0`, and `QR ≤ FR` since `Q` is between `F` and `R`.) -/
theorem dist_lt_dist_of_wbtw_foot {P a b Q R : EPoint}
    (hP : P ∉ affineSpan ℝ {a, b}) (hR : R ∈ affineSpan ℝ {a, b})
    (hQ : Wbtw ℝ (foot P a b) Q R) : dist Q R < dist P R := by
  have hPF : 0 < dist P (foot P a b) := by
    rw [← perpDist_eq_dist_foot]; exact perpDist_pos hP
  -- `QR ≤ FR` from betweenness
  have hQR : dist Q R ≤ dist (foot P a b) R := by
    have hadd := hQ.dist_add_dist
    have hfq : 0 ≤ dist (foot P a b) Q := dist_nonneg
    -- dist F Q + dist Q R = dist F R
    rw [dist_comm Q R] at hadd ⊢
    nlinarith [hadd, hfq]
  -- Pythagoras, normalised to `dist P R` and `dist (foot) R`: PR² = FR² + PF²
  have hpyth : dist P R * dist P R
      = dist (foot P a b) R * dist (foot P a b) R
        + dist P (foot P a b) * dist P (foot P a b) := by
    have h := dist_sq_eq_foot (P := P) (a := a) (b := b) hR
    rwa [dist_comm R P, dist_comm R (foot P a b)] at h
  have hQRnn : 0 ≤ dist Q R := dist_nonneg
  have hFRnn : 0 ≤ dist (foot P a b) R := dist_nonneg
  -- squared inequality, then square-root monotonicity
  have hsq : dist Q R ^ 2 < dist P R ^ 2 := by
    rw [sq, sq]
    nlinarith [hpyth, mul_le_mul hQR hQR hQRnn hFRnn, mul_pos hPF hPF]
  exact lt_of_pow_lt_pow_left₀ 2 dist_nonneg hsq

open scoped RealInnerProductSpace in
/-- **Projection-length identity (Kelly step 3c core).**
The squared inner product `⟪P -ᵥ Y, Z -ᵥ Y⟫²` equals `(dist Y F)² · (dist Y Z)²`
where `F` is the foot of the perpendicular from `P` to line `YZ` — because the
component of `P -ᵥ Y` along the line direction is exactly `F -ᵥ Y`. -/
theorem inner_vsub_pair_sq (P Y Z : EPoint) :
    ⟪P -ᵥ Y, Z -ᵥ Y⟫ ^ 2 = dist Y (foot P Y Z) ^ 2 * dist Y Z ^ 2 := by
  set F := foot P Y Z with hF
  -- `F -ᵥ Y` lies in the line direction, so it is a multiple `t • (Z -ᵥ Y)`.
  have hFY : F -ᵥ Y ∈ vectorSpan ℝ ({Y, Z} : Set EPoint) := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction (foot_mem P Y Z) (left_mem_affineSpan_pair ℝ Y Z)
  obtain ⟨t, ht⟩ := mem_vectorSpan_pair_rev.mp hFY   -- t • (Z -ᵥ Y) = F -ᵥ Y
  -- `P -ᵥ F` is orthogonal to the line direction.
  have hv : P -ᵥ F ∈ (vectorSpan ℝ ({Y, Z} : Set EPoint))ᗮ := by
    rw [← direction_affineSpan]
    exact EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
      (affineSpan ℝ {Y, Z}) P
  have hu : Z -ᵥ Y ∈ vectorSpan ℝ ({Y, Z} : Set EPoint) := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction
      (right_mem_affineSpan_pair ℝ Y Z) (left_mem_affineSpan_pair ℝ Y Z)
  have horth : ⟪P -ᵥ F, Z -ᵥ Y⟫ = 0 :=
    real_inner_comm (Z -ᵥ Y) (P -ᵥ F) ▸ Submodule.inner_right_of_mem_orthogonal hu hv
  -- inner product collapses to `t · ‖Z -ᵥ Y‖²`
  have hinner : ⟪P -ᵥ Y, Z -ᵥ Y⟫ = t * ‖Z -ᵥ Y‖ ^ 2 := by
    have hdecomp : P -ᵥ Y = (P -ᵥ F) + (F -ᵥ Y) := (vsub_add_vsub_cancel P F Y).symm
    rw [hdecomp, inner_add_left, horth, zero_add, ← ht, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
  -- distances in terms of `‖Z -ᵥ Y‖`
  have hYZ : dist Y Z = ‖Z -ᵥ Y‖ := by
    rw [dist_eq_norm_vsub' EPoint Y Z]
  have hYF : dist Y F = |t| * ‖Z -ᵥ Y‖ := by
    rw [dist_eq_norm_vsub' EPoint Y F, ← ht, norm_smul, Real.norm_eq_abs]
  rw [hinner, hYZ, hYF]
  rw [mul_pow, mul_pow, sq_abs]
  ring

open scoped RealInnerProductSpace in
/-- **Gram / Lagrange identity for the perpendicular distance.**
`perpDist² · base² = ‖edge‖²·base² − ⟪edge, base⟫²` — i.e. doubled triangle
area squared, with apex `P` over base `YZ` (edge `P-ᵥY`). -/
theorem perpDist_sq_mul_dist_sq (P Y Z : EPoint) :
    perpDist P Y Z ^ 2 * dist Y Z ^ 2
      = dist P Y ^ 2 * dist Y Z ^ 2 - ⟪P -ᵥ Y, Z -ᵥ Y⟫ ^ 2 := by
  have hpyth := dist_sq_eq_foot (P := P) (a := Y) (b := Z) (left_mem_affineSpan_pair ℝ Y Z)
  have hkey := inner_vsub_pair_sq P Y Z
  have hfoot := perpDist_eq_dist_foot P Y Z
  rw [dist_comm Y P] at hpyth
  rw [hfoot]
  linear_combination hkey - dist Y Z ^ 2 * hpyth

open scoped RealInnerProductSpace in
/-- **Apex-invariance of the Gram quantity.**
The doubled-area-squared is independent of which vertex is the apex:
swapping apex `P`↔`Q` (bases `QR`↔`PR`) preserves the value.  Pure
inner-product algebra. -/
theorem gram_apex_symm (P Q R : EPoint) :
    dist P Q ^ 2 * dist Q R ^ 2 - ⟪P -ᵥ Q, R -ᵥ Q⟫ ^ 2
      = dist Q P ^ 2 * dist P R ^ 2 - ⟪Q -ᵥ P, R -ᵥ P⟫ ^ 2 := by
  have e1 : dist P Q ^ 2 = ⟪P -ᵥ Q, P -ᵥ Q⟫ := by
    rw [dist_eq_norm_vsub EPoint P Q, real_inner_self_eq_norm_sq]
  have e2 : dist Q R ^ 2 = ⟪R -ᵥ Q, R -ᵥ Q⟫ := by
    rw [dist_eq_norm_vsub' EPoint Q R, real_inner_self_eq_norm_sq]
  have e3 : dist Q P ^ 2 = ⟪P -ᵥ Q, P -ᵥ Q⟫ := by
    rw [dist_eq_norm_vsub' EPoint Q P, real_inner_self_eq_norm_sq]
  have e4 : dist P R ^ 2 = ⟪R -ᵥ P, R -ᵥ P⟫ := by
    rw [dist_eq_norm_vsub' EPoint P R, real_inner_self_eq_norm_sq]
  -- express the two cross-edge vectors via `a = P -ᵥ Q`, `b = R -ᵥ Q`
  have hQP : Q -ᵥ P = -(P -ᵥ Q) := (neg_vsub_eq_vsub_rev P Q).symm
  have hRP : R -ᵥ P = (R -ᵥ Q) - (P -ᵥ Q) := by
    rw [← vsub_sub_vsub_cancel_right R P Q]
  rw [e1, e2, e3, e4, hQP, hRP]
  simp only [inner_sub_left, inner_sub_right, inner_neg_left]
  rw [real_inner_comm (R -ᵥ Q) (P -ᵥ Q)]
  ring

open scoped RealInnerProductSpace in
/-- **Area identity (Kelly step 3c).**
`perpDist Q P R · dist P R = perpDist P Q R · dist Q R` — doubled triangle
area is base-independent.  Combines the Gram identity (both apexes) with
apex-invariance, then takes square roots. -/
theorem perpDist_mul_dist_eq (P Q R : EPoint) :
    perpDist Q P R * dist P R = perpDist P Q R * dist Q R := by
  have hsq : (perpDist Q P R * dist P R) ^ 2 = (perpDist P Q R * dist Q R) ^ 2 := by
    rw [mul_pow, mul_pow]
    rw [perpDist_sq_mul_dist_sq Q P R, perpDist_sq_mul_dist_sq P Q R]
    -- both equal the Gram quantity at the respective apex; apex-invariance links them
    have := gram_apex_symm P Q R
    nlinarith [this]
  have h1 : 0 ≤ perpDist Q P R * dist P R :=
    mul_nonneg (perpDist_nonneg _ _ _) dist_nonneg
  have h2 : 0 ≤ perpDist P Q R * dist Q R :=
    mul_nonneg (perpDist_nonneg _ _ _) dist_nonneg
  calc perpDist Q P R * dist P R
      = Real.sqrt ((perpDist Q P R * dist P R) ^ 2) := (Real.sqrt_sq h1).symm
    _ = Real.sqrt ((perpDist P Q R * dist Q R) ^ 2) := by rw [hsq]
    _ = perpDist P Q R * dist Q R := Real.sqrt_sq h2

/-- **Kelly's strict decrease (step 3d core).**
If `P` is off line `QR`, `Q ≠ R`, and `Q` lies between the foot of the
perpendicular from `P` and `R`, then the perpendicular distance from `Q` to
line `PR` is strictly smaller than that from `P` to line `QR`.  This is the
inequality that contradicts minimality in Kelly's proof. -/
theorem perpDist_lt_perpDist_of_wbtw {P Q R : EPoint}
    (hP : P ∉ affineSpan ℝ {Q, R}) (hw : Wbtw ℝ (foot P Q R) Q R) :
    perpDist Q P R < perpDist P Q R := by
  have hlt := dist_lt_dist_of_wbtw_foot hP (right_mem_affineSpan_pair ℝ Q R) hw
  have harea := perpDist_mul_dist_eq P Q R
  have hPR : 0 < dist P R :=
    dist_pos.mpr (fun h => hP (h ▸ right_mem_affineSpan_pair ℝ Q R))
  have hpos : 0 < perpDist P Q R := perpDist_pos hP
  nlinarith [harea, hlt, hPR, hpos, mul_lt_mul_of_pos_left hlt hpos]

/-- The carrier of the line through two points is a collinear set. -/
theorem collinear_coe_affineSpan_pair (a b : EPoint) :
    Collinear ℝ (↑(affineSpan ℝ ({a, b} : Set EPoint)) : Set EPoint) := by
  have hv : vectorSpan ℝ (↑(affineSpan ℝ ({a, b} : Set EPoint)) : Set EPoint)
      = vectorSpan ℝ ({a, b} : Set EPoint) := by
    rw [← direction_affineSpan, AffineSubspace.affineSpan_coe, direction_affineSpan]
  unfold Collinear
  rw [hv]
  exact collinear_pair ℝ a b

/-- Two distinct points on the line span the same line. -/
theorem affineSpan_pair_eq_of_mem {a b Q R : EPoint}
    (hQ : Q ∈ affineSpan ℝ ({a, b} : Set EPoint))
    (hR : R ∈ affineSpan ℝ ({a, b} : Set EPoint)) (hQR : Q ≠ R) :
    affineSpan ℝ ({Q, R} : Set EPoint) = affineSpan ℝ ({a, b} : Set EPoint) := by
  have h := (collinear_coe_affineSpan_pair a b).affineSpan_eq_of_ne
    (SetLike.mem_coe.mpr hQ) (SetLike.mem_coe.mpr hR) hQR
  rwa [AffineSubspace.affineSpan_coe] at h

/-- `perpDist` depends only on the line: equal spans give equal distances. -/
theorem perpDist_congr {P a b Q R : EPoint}
    (h : affineSpan ℝ ({Q, R} : Set EPoint) = affineSpan ℝ ({a, b} : Set EPoint)) :
    perpDist P Q R = perpDist P a b := by
  unfold perpDist
  rw [h]

/-- The foot of the perpendicular depends only on the line. -/
theorem foot_congr {P a b Q R : EPoint}
    (h : affineSpan ℝ ({Q, R} : Set EPoint) = affineSpan ℝ ({a, b} : Set EPoint)) :
    foot P Q R = foot P a b := by
  unfold foot
  exact EuclideanGeometry.orthogonalProjection_congr h rfl

/-- A point on the line is a scalar multiple of the direction `b -ᵥ a`, offset
from the foot of the perpendicular. -/
theorem exists_smul_vadd_foot {P a b X : EPoint} (hX : X ∈ affineSpan ℝ {a, b}) :
    ∃ r : ℝ, r • (b -ᵥ a) +ᵥ foot P a b = X := by
  have hmem : X -ᵥ foot P a b ∈ vectorSpan ℝ ({a, b} : Set EPoint) := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction hX (foot_mem P a b)
  obtain ⟨r, hr⟩ := mem_vectorSpan_pair_rev.mp hmem
  exact ⟨r, by rw [hr, vsub_vadd]⟩

/-- **Pigeonhole (Kelly step 3d).** Among any three points on the line, two lie
on the same closed ray from the foot of the perpendicular — i.e. one is weakly
between the foot and the other. -/
theorem exists_wbtw_foot_of_three_mem {P a b x y z : EPoint}
    (hx : x ∈ affineSpan ℝ {a, b}) (hy : y ∈ affineSpan ℝ {a, b})
    (hz : z ∈ affineSpan ℝ {a, b}) :
    (Wbtw ℝ (foot P a b) x y ∨ Wbtw ℝ (foot P a b) y x) ∨
      (Wbtw ℝ (foot P a b) y z ∨ Wbtw ℝ (foot P a b) z y) ∨
      (Wbtw ℝ (foot P a b) x z ∨ Wbtw ℝ (foot P a b) z x) := by
  obtain ⟨rx, hrx⟩ := exists_smul_vadd_foot (P := P) hx
  obtain ⟨ry, hry⟩ := exists_smul_vadd_foot (P := P) hy
  obtain ⟨rz, hrz⟩ := exists_smul_vadd_foot (P := P) hz
  rcases le_total 0 rx with hx0 | hx0 <;> rcases le_total 0 ry with hy0 | hy0 <;>
    rcases le_total 0 rz with hz0 | hz0
  · exact Or.inl (hrx ▸ hry ▸ wbtw_or_wbtw_smul_vadd_of_nonneg _ _ hx0 hy0)
  · exact Or.inl (hrx ▸ hry ▸ wbtw_or_wbtw_smul_vadd_of_nonneg _ _ hx0 hy0)
  · exact Or.inr (Or.inr (hrx ▸ hrz ▸ wbtw_or_wbtw_smul_vadd_of_nonneg _ _ hx0 hz0))
  · exact Or.inr (Or.inl (hry ▸ hrz ▸ wbtw_or_wbtw_smul_vadd_of_nonpos _ _ hy0 hz0))
  · exact Or.inr (Or.inl (hry ▸ hrz ▸ wbtw_or_wbtw_smul_vadd_of_nonneg _ _ hy0 hz0))
  · exact Or.inr (Or.inr (hrx ▸ hrz ▸ wbtw_or_wbtw_smul_vadd_of_nonpos _ _ hx0 hz0))
  · exact Or.inl (hrx ▸ hry ▸ wbtw_or_wbtw_smul_vadd_of_nonpos _ _ hx0 hy0)
  · exact Or.inl (hrx ▸ hry ▸ wbtw_or_wbtw_smul_vadd_of_nonpos _ _ hx0 hy0)

/-- **Kelly step 2: a minimum-perpendicular-distance off-line pair exists.**
Over a finite point set with at least one off-line incidence, the perpendicular
distances of all off-line incidences attain a minimum — the well-ordering
(extremal) ingredient of Kelly's proof of Sylvester–Gallai.  Proved by
minimizing over `Finset.univ` of the finite incidence type (no `Finset.filter`
over the undecidable affine-membership predicate). -/
theorem exists_min_perpDist_offLine (S : Finset EPoint) (T : OffLineTriple S) :
    ∃ t : OffLineTriple S, ∀ t' : OffLineTriple S,
      perpDist t.P t.a t.b ≤ perpDist t'.P t'.a t'.b := by
  classical
  haveI : Fintype (OffLineTriple S) := Fintype.ofFinite _
  obtain ⟨t, _, hmin⟩ := Finset.univ.exists_min_image
    (fun t : OffLineTriple S => perpDist t.P t.a t.b) ⟨T, Finset.mem_univ T⟩
  exact ⟨t, fun t' => hmin t' (Finset.mem_univ t')⟩

open scoped Classical

/-- **The Euclidean Sylvester–Gallai theorem.**
A finite planar point set with at least one off-line incidence (equivalently,
not all collinear) determines an *ordinary line*: two of its points whose line
contains exactly those two points of the set.  Proved by Kelly's
minimum-distance argument. -/
theorem euclidean_sylvester_gallai (S : Finset EPoint) (T : OffLineTriple S) :
    ∃ a b : EPoint, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      (S.filter (· ∈ affineSpan ℝ ({a, b} : Set EPoint))).card = 2 := by
  classical
  obtain ⟨T₀, hmin⟩ := exists_min_perpDist_offLine S T
  refine ⟨T₀.a, T₀.b, T₀.ha, T₀.hb, T₀.hab, ?_⟩
  set pts := S.filter (· ∈ affineSpan ℝ ({T₀.a, T₀.b} : Set EPoint)) with hpts
  have haS : T₀.a ∈ pts :=
    Finset.mem_filter.mpr ⟨T₀.ha, left_mem_affineSpan_pair ℝ _ _⟩
  have hbS : T₀.b ∈ pts :=
    Finset.mem_filter.mpr ⟨T₀.hb, right_mem_affineSpan_pair ℝ _ _⟩
  -- the contradiction engine: no off-line incidence Q,R on the line can beat the minimum
  have contra : ∀ Q R, Q ∈ pts → R ∈ pts → Q ≠ R →
      Wbtw ℝ (foot T₀.P T₀.a T₀.b) Q R → False := by
    intro Q R hQ hR hQR hw
    have hQline : Q ∈ affineSpan ℝ {T₀.a, T₀.b} := (Finset.mem_filter.mp hQ).2
    have hRline : R ∈ affineSpan ℝ {T₀.a, T₀.b} := (Finset.mem_filter.mp hR).2
    have hspan : affineSpan ℝ ({Q, R} : Set EPoint) = affineSpan ℝ {T₀.a, T₀.b} :=
      affineSpan_pair_eq_of_mem hQline hRline hQR
    have hP_off : T₀.P ∉ affineSpan ℝ ({Q, R} : Set EPoint) := by rw [hspan]; exact T₀.hoff
    have hw' : Wbtw ℝ (foot T₀.P Q R) Q R := by rw [foot_congr hspan]; exact hw
    have hdec := perpDist_lt_perpDist_of_wbtw hP_off hw'
    rw [perpDist_congr hspan] at hdec
    -- (Q, T₀.P, R) is an off-line incidence
    have hPR : T₀.P ≠ R := fun h => T₀.hoff (h ▸ hRline)
    have hQ_off : Q ∉ affineSpan ℝ ({T₀.P, R} : Set EPoint) := by
      intro hQin
      have hRin : R ∈ affineSpan ℝ ({T₀.P, R} : Set EPoint) :=
        right_mem_affineSpan_pair ℝ _ _
      have he : affineSpan ℝ ({Q, R} : Set EPoint) = affineSpan ℝ {T₀.P, R} :=
        affineSpan_pair_eq_of_mem hQin hRin hQR
      rw [hspan] at he
      exact T₀.hoff (he ▸ left_mem_affineSpan_pair ℝ T₀.P R)
    let T' : OffLineTriple S :=
      ⟨Q, T₀.P, R, (Finset.mem_filter.mp hQ).1, T₀.hP, (Finset.mem_filter.mp hR).1, hPR, hQ_off⟩
    have := hmin T'
    -- this : perpDist T₀.P T₀.a T₀.b ≤ perpDist Q T₀.P R ;  hdec : perpDist Q T₀.P R < perpDist T₀.P T₀.a T₀.b
    exact absurd this (not_le.mpr hdec)
  -- card pts = 2: at least 2 (a,b), and a third point would contradict via pigeonhole
  have hge2 : 2 ≤ pts.card := by
    have hsub : ({T₀.a, T₀.b} : Finset EPoint) ⊆ pts := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · exact h ▸ haS
      · exact (Finset.mem_singleton.mp h) ▸ hbS
    calc 2 = ({T₀.a, T₀.b} : Finset EPoint).card := (Finset.card_pair T₀.hab).symm
      _ ≤ pts.card := Finset.card_le_card hsub
  rcases lt_or_eq_of_le hge2 with hlt | heq
  · exfalso
    have hlt2 : ({T₀.a, T₀.b} : Finset EPoint).card < pts.card := by
      rw [Finset.card_pair T₀.hab]; exact hlt
    obtain ⟨c, hc, hcab⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt2
    have hca : c ≠ T₀.a := fun h => hcab (h ▸ Finset.mem_insert_self _ _)
    have hcb : c ≠ T₀.b := fun h =>
      hcab (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hcline : c ∈ affineSpan ℝ {T₀.a, T₀.b} := (Finset.mem_filter.mp hc).2
    rcases exists_wbtw_foot_of_three_mem (P := T₀.P)
      (left_mem_affineSpan_pair ℝ T₀.a T₀.b) (right_mem_affineSpan_pair ℝ T₀.a T₀.b) hcline with
      (h | h) | (h | h) | (h | h)
    · exact contra _ _ haS hbS T₀.hab h
    · exact contra _ _ hbS haS T₀.hab.symm h
    · exact contra _ _ hbS hc hcb.symm h
    · exact contra _ _ hc hbS hcb h
    · exact contra _ _ haS hc hca.symm h
    · exact contra _ _ hc haS hca h
  · exact heq.symm

/-- **Sylvester-Gallai theorem in the Euclidean plane.**
A finite planar point set with an off-line triple determines a line containing
exactly two points of the set.  The off-line triple is the constructive
non-collinearity hypothesis.
-/
theorem chapter10 (S : Finset EPoint) (T : OffLineTriple S) :
    ∃ a b : EPoint, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      (S.filter (· ∈ affineSpan ℝ ({a, b} : Set EPoint))).card = 2 :=
  euclidean_sylvester_gallai S T

end EuclideanSylvesterGallai

end ProofsInTheBook.Chapter10
