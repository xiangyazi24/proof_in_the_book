import ProofsInTheBook.Chapter20DissectionEngine

/-!
# Chapter 20 E2 sanity witness

The diagonal split of the unit square, packaged as a `SquareDissection`.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor
open scoped Topology

namespace Chapter20E2Diagonal

abbrev P := ℝ × ℝ

def diagCoord : Fin 4 → P :=
  ![(0, 0), (1, 0), (1, 1), (0, 1)]

def diagTri : Fin 2 → Fin 4 × Fin 4 × Fin 4 :=
  ![(0, 1, 2), (0, 2, 3)]

lemma diagCoord_inj : Function.Injective diagCoord := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [diagCoord] at h ⊢

lemma convexHull_diagLower :
    convexHull ℝ ({((0, 0) : P), (1, 0), (1, 1)} : Set P) =
      {p : P | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1} := by
  rw [convexHull_eq_triangleAffine_image]
  ext p
  constructor
  · rintro ⟨⟨s, t⟩, hst, rfl⟩
    rcases hst with ⟨hs, ht, hst⟩
    simp [triangleAffine]
    constructor
    · exact ht
    constructor
    · linarith
    · linarith
  · intro hp
    rcases hp with ⟨hy0, hyx, hx1⟩
    refine ⟨(p.1 - p.2, p.2), ?_, ?_⟩
    · simp [filled2Simplex]
      constructor
      · linarith
      constructor
      · exact hy0
      · linarith
    · ext <;> simp [triangleAffine]

lemma convexHull_diagUpper :
    convexHull ℝ ({((0, 0) : P), (1, 1), (0, 1)} : Set P) =
      {p : P | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1} := by
  rw [convexHull_eq_triangleAffine_image]
  ext p
  constructor
  · rintro ⟨⟨s, t⟩, hst, rfl⟩
    rcases hst with ⟨hs, ht, hst⟩
    simp [triangleAffine]
    constructor
    · exact hs
    constructor
    · linarith
    · linarith
  · intro hp
    rcases hp with ⟨hx0, hxy, hy1⟩
    refine ⟨(p.1, p.2 - p.1), ?_, ?_⟩
    · simp [filled2Simplex]
      constructor
      · exact hx0
      constructor
      · linarith
      · linarith
    · ext <;> simp [triangleAffine]

lemma diagonal_cover_union :
    convexHull ℝ ({((0, 0) : P), (1, 0), (1, 1)} : Set P) ∪
      convexHull ℝ ({((0, 0) : P), (1, 1), (0, 1)} : Set P) =
        Set.Icc ((0, 0) : P) (1, 1) := by
  rw [convexHull_diagLower, convexHull_diagUpper]
  ext p
  constructor
  · intro hp
    rcases hp with hp | hp
    · rcases hp with ⟨hy0, hyx, hx1⟩
      simp [Set.mem_Icc, Prod.le_def]
      exact ⟨⟨by linarith, hy0⟩, ⟨hx1, by linarith⟩⟩
    · rcases hp with ⟨hx0, hxy, hy1⟩
      simp [Set.mem_Icc, Prod.le_def]
      exact ⟨⟨hx0, by linarith⟩, ⟨by linarith, hy1⟩⟩
  · intro hp
    simp [Set.mem_Icc, Prod.le_def] at hp
    rcases hp with ⟨⟨hx0, hy0⟩, ⟨hx1, hy1⟩⟩
    by_cases hle : p.2 ≤ p.1
    · left
      exact ⟨hy0, hle, hx1⟩
    · right
      have hxle : p.1 ≤ p.2 := le_of_lt (lt_of_not_ge hle)
      exact ⟨hx0, hxle, hy1⟩

lemma diagonal_iUnion_eq :
    (⋃ i : Fin 2, convexHull ℝ
      ({diagCoord (diagTri i).1, diagCoord (diagTri i).2.1,
        diagCoord (diagTri i).2.2} : Set P)) =
      convexHull ℝ ({((0, 0) : P), (1, 0), (1, 1)} : Set P) ∪
        convexHull ℝ ({((0, 0) : P), (1, 1), (0, 1)} : Set P) := by
  ext p
  constructor
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (by simpa [diagCoord, diagTri] using hi)
    · exact Or.inr (by simpa [diagCoord, diagTri] using hi)
  · intro hp
    rcases hp with hp | hp
    · exact Set.mem_iUnion.mpr ⟨0, by simpa [diagCoord, diagTri] using hp⟩
    · exact Set.mem_iUnion.mpr ⟨1, by simpa [diagCoord, diagTri] using hp⟩

lemma diagonal_cover :
    (⋃ i : Fin 2, convexHull ℝ
      ({diagCoord (diagTri i).1, diagCoord (diagTri i).2.1,
        diagCoord (diagTri i).2.2} : Set P)) =
        Set.Icc ((0, 0) : P) (1, 1) := by
  rw [diagonal_iUnion_eq, diagonal_cover_union]

lemma interior_diagLower_subset_strict :
    interior (convexHull ℝ ({((0, 0) : P), (1, 0), (1, 1)} : Set P)) ⊆
      {p : P | p.2 < p.1} := by
  rw [convexHull_diagLower]
  intro p hp
  have hpSet : p ∈ {p : P | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1} :=
    interior_subset hp
  by_contra hnot
  have hge : p.1 ≤ p.2 := le_of_not_gt hnot
  have heq : p.1 = p.2 := le_antisymm hge hpSet.2.1
  have hnhds :
      {p : P | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1} ∈ 𝓝 p :=
    mem_interior_iff_mem_nhds.mp hp
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hε, hball⟩
  let q : P := (p.1, p.2 + ε / 2)
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · simp [q, hε]
    · rw [Real.dist_eq]
      have hdist : q.2 - p.2 = ε / 2 := by simp [q]
      rw [hdist, abs_of_nonneg (by linarith : 0 ≤ ε / 2)]
      linarith
  have hqSet := hball hqball
  have hyx : q.2 ≤ q.1 := hqSet.2.1
  simp [q, heq] at hyx
  linarith

lemma interior_diagUpper_subset_strict :
    interior (convexHull ℝ ({((0, 0) : P), (1, 1), (0, 1)} : Set P)) ⊆
      {p : P | p.1 < p.2} := by
  rw [convexHull_diagUpper]
  intro p hp
  have hpSet : p ∈ {p : P | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1} :=
    interior_subset hp
  by_contra hnot
  have hge : p.2 ≤ p.1 := le_of_not_gt hnot
  have heq : p.1 = p.2 := le_antisymm hpSet.2.1 hge
  have hnhds :
      {p : P | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1} ∈ 𝓝 p :=
    mem_interior_iff_mem_nhds.mp hp
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hε, hball⟩
  let q : P := (p.1 + ε / 2, p.2)
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · rw [Real.dist_eq]
      have hdist : q.1 - p.1 = ε / 2 := by simp [q]
      rw [hdist, abs_of_nonneg (by linarith : 0 ≤ ε / 2)]
      linarith
    · simp [q, hε]
  have hqSet := hball hqball
  have hxy : q.1 ≤ q.2 := hqSet.2.1
  simp [q, heq] at hxy
  linarith

lemma diagonal_disjoint_interiors :
    Disjoint
      (interior (convexHull ℝ ({((0, 0) : P), (1, 0), (1, 1)} : Set P)))
      (interior (convexHull ℝ ({((0, 0) : P), (1, 1), (0, 1)} : Set P))) := by
  rw [Set.disjoint_left]
  intro p hpLower hpUpper
  have hltLower : p.2 < p.1 := by
    simpa using interior_diagLower_subset_strict hpLower
  have hltUpper : p.1 < p.2 := by
    simpa using interior_diagUpper_subset_strict hpUpper
  exact not_lt_of_ge hltUpper.le hltLower

/-- The diagonal split of the unit square into two triangles. -/
def diagonalSquareDissection : SquareDissection where
  n := 2
  vtx := Fin 4
  vtxFin := inferInstance
  vtxDec := inferInstance
  coord := diagCoord
  coord_inj := diagCoord_inj
  tri := diagTri
  nondeg := by
    intro i
    fin_cases i <;> simp [diagCoord, diagTri, doubleArea]
  cover := diagonal_cover
  disjoint_int := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa [diagCoord, diagTri] using diagonal_disjoint_interiors
    · simpa [diagCoord, diagTri] using diagonal_disjoint_interiors.symm
    · exact (hij rfl).elim
  equalArea := by
    intro i
    fin_cases i
    · show realTriangleArea ((0, 0) : P) (1, 0) (1, 1) =
        (((1 : ℚ) / 2 : ℚ) : ℝ)
      simp [realTriangleArea, doubleArea]
    · show realTriangleArea ((0, 0) : P) (1, 1) (0, 1) =
        (((1 : ℚ) / 2 : ℚ) : ℝ)
      simp [realTriangleArea, doubleArea]

end Chapter20E2Diagonal

end ProofsInTheBook.Chapter20
