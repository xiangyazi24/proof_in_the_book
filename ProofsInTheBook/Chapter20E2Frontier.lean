import ProofsInTheBook.Chapter20

/-!
# Chapter 20 E2 frontier geometry

Auxiliary planar convex-geometry lemmas for the E2 incidence proof.
-/

namespace ProofsInTheBook.Chapter20

open scoped Topology

namespace Chapter20E2Frontier

abbrev P := ℝ × ℝ

lemma interior_filled2Simplex_subset_strict :
    interior filled2Simplex ⊆
      {p : P | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1} := by
  intro p hp
  have hpSet : p ∈ filled2Simplex := interior_subset hp
  rcases hpSet with ⟨hx0, hy0, hsum⟩
  have hnhds : filled2Simplex ∈ 𝓝 p := mem_interior_iff_mem_nhds.mp hp
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hε, hball⟩
  have hxpos : 0 < p.1 := by
    by_contra hxnot
    have hxle : p.1 ≤ 0 := le_of_not_gt hxnot
    have hx : p.1 = 0 := le_antisymm hxle hx0
    let q : P := (p.1 - ε / 2, p.2)
    have hqball : q ∈ Metric.ball p ε := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · rw [Real.dist_eq]
        have hdist : p.1 - q.1 = ε / 2 := by simp [q]
        rw [show q.1 - p.1 = -(p.1 - q.1) by ring, hdist, abs_neg,
          abs_of_nonneg (by linarith : 0 ≤ ε / 2)]
        linarith
      · simp [q, hε]
    have hqSet := hball hqball
    have hq0 : 0 ≤ q.1 := hqSet.1
    simp [q, hx] at hq0
    linarith
  have hypos : 0 < p.2 := by
    by_contra hynot
    have hyle : p.2 ≤ 0 := le_of_not_gt hynot
    have hy : p.2 = 0 := le_antisymm hyle hy0
    let q : P := (p.1, p.2 - ε / 2)
    have hqball : q ∈ Metric.ball p ε := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · simp [q, hε]
      · rw [Real.dist_eq]
        have hdist : p.2 - q.2 = ε / 2 := by simp [q]
        rw [show q.2 - p.2 = -(p.2 - q.2) by ring, hdist, abs_neg,
          abs_of_nonneg (by linarith : 0 ≤ ε / 2)]
        linarith
    have hqSet := hball hqball
    have hq0 : 0 ≤ q.2 := hqSet.2.1
    simp [q, hy] at hq0
    linarith
  have hsumlt : p.1 + p.2 < 1 := by
    by_contra hsnot
    have hsge : 1 ≤ p.1 + p.2 := le_of_not_gt hsnot
    have hs : p.1 + p.2 = 1 := le_antisymm hsum hsge
    let q : P := (p.1 + ε / 2, p.2 + ε / 2)
    have hqball : q ∈ Metric.ball p ε := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · rw [Real.dist_eq]
        have hdist : q.1 - p.1 = ε / 2 := by simp [q]
        rw [hdist, abs_of_nonneg (by linarith : 0 ≤ ε / 2)]
        linarith
      · rw [Real.dist_eq]
        have hdist : q.2 - p.2 = ε / 2 := by simp [q]
        rw [hdist, abs_of_nonneg (by linarith : 0 ≤ ε / 2)]
        linarith
    have hqSet := hball hqball
    have hqsum : q.1 + q.2 ≤ 1 := hqSet.2.2
    simp [q] at hqsum
    linarith
  exact ⟨hxpos, hypos, hsumlt⟩

lemma strict_subset_interior_filled2Simplex :
    {p : P | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1} ⊆
      interior filled2Simplex := by
  intro p hp
  rcases hp with ⟨hx, hy, hsum⟩
  have hgap : 0 < min (min p.1 p.2) (1 - (p.1 + p.2)) := by
    exact lt_min (lt_min hx hy) (sub_pos.mpr hsum)
  let δ : ℝ := min (min p.1 p.2) (1 - (p.1 + p.2)) / 4
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  refine mem_interior_iff_mem_nhds.mpr ?_
  rw [Metric.mem_nhds_iff]
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hq
  have hxabs : |q.1 - p.1| < δ := by
    rw [Real.dist_eq] at hq
    exact hq.1
  have hyabs : |q.2 - p.2| < δ := by
    rw [Real.dist_eq] at hq
    exact hq.2
  have hδx : δ < p.1 := by
    have hmin : min (min p.1 p.2) (1 - (p.1 + p.2)) ≤ p.1 :=
      (min_le_left _ _).trans (min_le_left _ _)
    dsimp [δ]
    nlinarith [hgap, hmin]
  have hδy : δ < p.2 := by
    have hmin : min (min p.1 p.2) (1 - (p.1 + p.2)) ≤ p.2 :=
      (min_le_left _ _).trans (min_le_right _ _)
    dsimp [δ]
    nlinarith [hgap, hmin]
  have hδsum : 2 * δ < 1 - (p.1 + p.2) := by
    have hmin : min (min p.1 p.2) (1 - (p.1 + p.2)) ≤ 1 - (p.1 + p.2) :=
      min_le_right _ _
    dsimp [δ]
    nlinarith [hgap, hmin]
  have hqx : 0 ≤ q.1 := by
    have hlt : p.1 - q.1 < δ := by
      have hxabs' : |p.1 - q.1| < δ := by
        rwa [abs_sub_comm] at hxabs
      exact lt_of_le_of_lt (le_abs_self _) hxabs'
    linarith
  have hqy : 0 ≤ q.2 := by
    have hlt : p.2 - q.2 < δ := by
      have hyabs' : |p.2 - q.2| < δ := by
        rwa [abs_sub_comm] at hyabs
      exact lt_of_le_of_lt (le_abs_self _) hyabs'
    linarith
  have hqsum : q.1 + q.2 ≤ 1 := by
    have hqxle : q.1 - p.1 < δ := lt_of_le_of_lt (le_abs_self _) hxabs
    have hqyle : q.2 - p.2 < δ := lt_of_le_of_lt (le_abs_self _) hyabs
    linarith
  exact ⟨hqx, hqy, hqsum⟩

lemma interior_filled2Simplex_eq :
    interior filled2Simplex =
      {p : P | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1} :=
  le_antisymm interior_filled2Simplex_subset_strict strict_subset_interior_filled2Simplex

lemma mem_segment_std_bottom (p : P) :
    p ∈ segment ℝ ((0, 0) : P) (1, 0) ↔ 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 0 := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa using ht
  · intro hp
    refine ⟨p.1, ⟨hp.1, hp.2.1⟩, ?_⟩
    ext <;> simp [hp.2.2]

lemma mem_segment_std_diag (p : P) :
    p ∈ segment ℝ ((1, 0) : P) (0, 1) ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1 := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa using ⟨ht.2, ht.1⟩
  · intro hp
    refine ⟨p.2, ⟨hp.2.1, ?_⟩, ?_⟩
    · linarith
    · ext <;> simp
      linarith

lemma mem_segment_std_left (p : P) :
    p ∈ segment ℝ ((0, 1) : P) (0, 0) ↔ p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa using ⟨ht.2, ht.1⟩
  · intro hp
    refine ⟨1 - p.2, ⟨?_, ?_⟩, ?_⟩
    · linarith
    · linarith
    · ext <;> simp [hp.1]

theorem frontier_filled2Simplex :
    frontier filled2Simplex =
      segment ℝ ((0, 0) : P) (1, 0) ∪
        segment ℝ ((1, 0) : P) (0, 1) ∪
          segment ℝ ((0, 1) : P) (0, 0) := by
  rw [isClosed_filled2Simplex.frontier_eq, interior_filled2Simplex_eq]
  ext p
  constructor
  · rintro ⟨hpFill, hpNotInt⟩
    rcases hpFill with ⟨hx0, hy0, hsum⟩
    simp only [Set.mem_setOf_eq, not_and, not_lt] at hpNotInt
    have hcases : p.1 = 0 ∨ p.2 = 0 ∨ p.1 + p.2 = 1 := by
      by_cases hx : 0 < p.1
      · by_cases hy : 0 < p.2
        · have hge : 1 ≤ p.1 + p.2 := hpNotInt hx hy
          right; right
          exact le_antisymm hsum hge
        · right; left
          exact le_antisymm (le_of_not_gt hy) hy0
      · left
        exact le_antisymm (le_of_not_gt hx) hx0
    rcases hcases with hx | hy | hsumEq
    · right
      rw [mem_segment_std_left]
      exact ⟨hx, hy0, by linarith⟩
    · left; left
      rw [mem_segment_std_bottom]
      exact ⟨hx0, by linarith, hy⟩
    · left; right
      rw [mem_segment_std_diag]
      exact ⟨hx0, hy0, hsumEq⟩
  · intro hp
    rcases hp with hp | hp
    · rcases hp with hp | hp
      · rw [mem_segment_std_bottom] at hp
        refine ⟨⟨hp.1, by linarith, by linarith⟩, ?_⟩
        simp [hp.2.2]
      · rw [mem_segment_std_diag] at hp
        refine ⟨⟨hp.1, hp.2.1, by linarith⟩, ?_⟩
        simp [hp.2.2]
    · rw [mem_segment_std_left] at hp
      refine ⟨⟨by linarith, hp.2.1, by linarith⟩, ?_⟩
      simp [hp.1]

noncomputable def triangleAffineMap (a b c : P) : P →ᵃ[ℝ] P where
  toFun := triangleAffine a b c
  linear := triangleEdgeMap a b c
  map_vadd' := by
    intro p v
    ext <;> simp [triangleAffine, triangleEdgeMap_apply] <;> ring

@[simp]
lemma triangleAffineMap_apply (a b c p : P) :
    triangleAffineMap a b c p = triangleAffine a b c p := rfl

noncomputable def triangleAffineHomeomorph (a b c : P)
    (hnd : doubleArea a b c ≠ 0) : P ≃ₜ P :=
  let e : P ≃ₗ[ℝ] P :=
    LinearMap.equivOfDetNeZero (triangleEdgeMap a b c) (by
      rwa [det_triangleEdgeMap])
  e.toContinuousLinearEquiv.toHomeomorph.trans (Homeomorph.addLeft a)

@[simp]
lemma triangleAffineHomeomorph_apply (a b c : P)
    (hnd : doubleArea a b c ≠ 0) (p : P) :
    triangleAffineHomeomorph a b c hnd p = triangleAffine a b c p := by
  simp [triangleAffineHomeomorph, triangleAffine_eq_add_triangleEdgeMap]

lemma triangleAffineHomeomorph_image_filled2Simplex (a b c : P)
    (hnd : doubleArea a b c ≠ 0) :
    triangleAffineHomeomorph a b c hnd '' filled2Simplex =
      convexHull ℝ ({a, b, c} : Set P) := by
  rw [convexHull_eq_triangleAffine_image]
  ext p
  simp

lemma triangleAffineHomeomorph_image_bottom (a b c : P)
    (hnd : doubleArea a b c ≠ 0) :
    triangleAffineHomeomorph a b c hnd ''
        segment ℝ ((0, 0) : P) (1, 0) =
      segment ℝ a b := by
  calc
    triangleAffineHomeomorph a b c hnd '' segment ℝ ((0, 0) : P) (1, 0)
        = triangleAffineMap a b c '' segment ℝ ((0, 0) : P) (1, 0) := by
          ext p; simp
    _ = segment ℝ (triangleAffineMap a b c ((0, 0) : P))
          (triangleAffineMap a b c (1, 0)) := by
          rw [image_segment]
    _ = segment ℝ a b := by simp

lemma triangleAffineHomeomorph_image_diag (a b c : P)
    (hnd : doubleArea a b c ≠ 0) :
    triangleAffineHomeomorph a b c hnd ''
        segment ℝ ((1, 0) : P) (0, 1) =
      segment ℝ b c := by
  calc
    triangleAffineHomeomorph a b c hnd '' segment ℝ ((1, 0) : P) (0, 1)
        = triangleAffineMap a b c '' segment ℝ ((1, 0) : P) (0, 1) := by
          ext p; simp
    _ = segment ℝ (triangleAffineMap a b c ((1, 0) : P))
          (triangleAffineMap a b c (0, 1)) := by
          rw [image_segment]
    _ = segment ℝ b c := by simp

lemma triangleAffineHomeomorph_image_left (a b c : P)
    (hnd : doubleArea a b c ≠ 0) :
    triangleAffineHomeomorph a b c hnd ''
        segment ℝ ((0, 1) : P) (0, 0) =
      segment ℝ c a := by
  calc
    triangleAffineHomeomorph a b c hnd '' segment ℝ ((0, 1) : P) (0, 0)
        = triangleAffineMap a b c '' segment ℝ ((0, 1) : P) (0, 0) := by
          ext p; simp
    _ = segment ℝ (triangleAffineMap a b c ((0, 1) : P))
          (triangleAffineMap a b c (0, 0)) := by
          rw [image_segment]
    _ = segment ℝ c a := by simp

theorem interior_convexHull_triangle_of_doubleArea_ne_zero (a b c : P)
    (hnd : doubleArea a b c ≠ 0) :
    interior (convexHull ℝ ({a, b, c} : Set P)) =
      triangleAffine a b c ''
        {p : P | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1} := by
  let h := triangleAffineHomeomorph a b c hnd
  have himg := h.image_interior filled2Simplex
  rw [interior_filled2Simplex_eq] at himg
  rw [triangleAffineHomeomorph_image_filled2Simplex a b c hnd] at himg
  rw [← himg]
  ext p
  constructor
  · rintro ⟨q, hq, hqp⟩
    refine ⟨q, hq, ?_⟩
    simpa [h] using hqp
  · rintro ⟨q, hq, hqp⟩
    refine ⟨q, hq, ?_⟩
    simpa [h] using hqp

lemma doubleArea_edge_triangleAffine (a b c : P) (s t : ℝ) :
    doubleArea a b (triangleAffine a b c (s, t)) =
      t * doubleArea a b c := by
  unfold doubleArea triangleAffine
  simp
  ring

lemma doubleArea_edge_mul_nonneg_of_mem_convexHull (a b c x : P)
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set P)) :
    0 ≤ doubleArea a b x * doubleArea a b c := by
  rw [convexHull_eq_triangleAffine_image] at hx
  rcases hx with ⟨⟨s, t⟩, hst, rfl⟩
  rw [doubleArea_edge_triangleAffine]
  have ht : 0 ≤ t := hst.2.1
  have hsq : 0 ≤ doubleArea a b c * doubleArea a b c := by nlinarith
  nlinarith

lemma doubleArea_edge_mul_pos_of_mem_interior_convexHull
    (a b c x : P) (hnd : doubleArea a b c ≠ 0)
    (hx : x ∈ interior (convexHull ℝ ({a, b, c} : Set P))) :
    0 < doubleArea a b x * doubleArea a b c := by
  rw [interior_convexHull_triangle_of_doubleArea_ne_zero a b c hnd] at hx
  rcases hx with ⟨⟨s, t⟩, hst, rfl⟩
  rw [doubleArea_edge_triangleAffine]
  have ht : 0 < t := hst.2.1
  have hsq : 0 < doubleArea a b c * doubleArea a b c := by
    nlinarith [sq_pos_of_ne_zero hnd]
  nlinarith

lemma doubleArea_eq_zero_of_mem_segment {a b m : P}
    (hm : m ∈ segment ℝ a b) : doubleArea a b m = 0 := by
  rw [segment_eq_image] at hm
  rcases hm with ⟨t, ht, rfl⟩
  unfold doubleArea
  simp [Prod.smul_def]
  ring

lemma doubleArea_direction_combo
    (a b m u v : P) (α β : ℝ)
    (hm : doubleArea a b m = 0) :
    doubleArea a b (m + α • (b - a) + β • (v - u)) =
      β * doubleArea a b (m + (v - u)) := by
  unfold doubleArea at hm ⊢
  simp [Prod.smul_def] at hm ⊢
  ring_nf at hm ⊢
  linear_combination (1 - β) * hm

lemma doubleArea_direction_combo_uv
    (u v m a b : P) (α β : ℝ)
    (hm : doubleArea u v m = 0) :
    doubleArea u v (m + α • (b - a) + β • (v - u)) =
      α * doubleArea u v (m + (b - a)) := by
  unfold doubleArea at hm ⊢
  simp [Prod.smul_def] at hm ⊢
  ring_nf at hm ⊢
  linear_combination (1 - α) * hm

lemma openSegment_edge_to_opposite_subset_interior_convexHull
    (a b c m : P) (hnd : doubleArea a b c ≠ 0)
    (hm : m ∈ openSegment ℝ a b) :
    openSegment ℝ m c ⊆ interior (convexHull ℝ ({a, b, c} : Set P)) := by
  rw [openSegment_eq_image] at hm
  rcases hm with ⟨s, hs, rfl⟩
  intro x hx
  rw [openSegment_eq_image] at hx
  rcases hx with ⟨t, ht, rfl⟩
  rw [interior_convexHull_triangle_of_doubleArea_ne_zero a b c hnd]
  refine ⟨((1 - t) * s, t), ?_, ?_⟩
  · constructor
    · nlinarith [hs.1, ht.2]
    · constructor
      · exact ht.1
      · nlinarith [hs.1, hs.2, ht.1, ht.2]
  · rw [triangleAffine_eq_combo]
    ext <;> simp [smul_add] <;> ring

lemma exists_openSegment_to_sameSide_mem_interior_convexHull
    (a b c d m : P) (hnd : doubleArea a b c ≠ 0)
    (hm : m ∈ openSegment ℝ a b)
    (hsame : 0 < doubleArea a b d * doubleArea a b c) :
    ∃ x : P,
      x ∈ openSegment ℝ m d ∧
        x ∈ interior (convexHull ℝ ({a, b, c} : Set P)) := by
  rw [openSegment_eq_image] at hm
  rcases hm with ⟨s, hs, hm⟩
  let h := triangleAffineHomeomorph a b c hnd
  let uv : P := h.symm d
  have hd : triangleAffine a b c uv = d := by
    have hd0 : h uv = d := Homeomorph.apply_symm_apply h d
    change triangleAffineHomeomorph a b c hnd uv = d at hd0
    simpa using hd0
  have hm_tri : triangleAffine a b c (s, 0) = (1 - s) • a + s • b := by
    rw [triangleAffine_eq_combo]
    ext <;> simp <;> ring
  have hm' : triangleAffine a b c (s, 0) = m := by
    rw [hm_tri]
    simpa using hm
  have hd_area : doubleArea a b d = uv.2 * doubleArea a b c := by
    rw [← hd]
    obtain ⟨u, v⟩ := uv
    exact doubleArea_edge_triangleAffine a b c u v
  have huv₂_pos : 0 < uv.2 := by
    rw [hd_area] at hsame
    have hsq : 0 < doubleArea a b c * doubleArea a b c := by
      nlinarith [sq_pos_of_ne_zero hnd]
    nlinarith [hsame, hsq]
  let M : ℝ := |uv.1| + |uv.2| + |s| + 1
  have hMpos : 0 < M := by
    dsimp [M]
    nlinarith [abs_nonneg uv.1, abs_nonneg uv.2, abs_nonneg s]
  have hden_pos : 0 < 2 * M := by nlinarith
  let t : ℝ := min (1 / 2) (min (s / (2 * M)) ((1 - s) / (2 * M)))
  have ht_pos : 0 < t := by
    dsimp [t]
    refine lt_min ?_ (lt_min ?_ ?_)
    · norm_num
    · exact div_pos hs.1 hden_pos
    · exact div_pos (sub_pos.mpr hs.2) hden_pos
  have ht_lt_one : t < 1 := by
    dsimp [t]
    exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
  have ht_le_s : t ≤ s / (2 * M) := by
    dsimp [t]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have ht_le_one_sub_s : t ≤ (1 - s) / (2 * M) := by
    dsimp [t]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have htM_le_s_half : t * M ≤ s / 2 := by
    have h := mul_le_mul_of_nonneg_right ht_le_s (le_of_lt hMpos)
    have hcalc : s / (2 * M) * M = s / 2 := by
      field_simp [ne_of_gt hMpos]
    nlinarith [h, hcalc]
  have htM_le_gap_half : t * M ≤ (1 - s) / 2 := by
    have h := mul_le_mul_of_nonneg_right ht_le_one_sub_s (le_of_lt hMpos)
    have hcalc : (1 - s) / (2 * M) * M = (1 - s) / 2 := by
      field_simp [ne_of_gt hMpos]
    nlinarith [h, hcalc]
  have h_us_lower : -M ≤ uv.1 - s := by
    dsimp [M]
    nlinarith [neg_le_abs uv.1, le_abs_self s, abs_nonneg uv.2]
  have h_uvs_upper : uv.1 + uv.2 - s ≤ M := by
    dsimp [M]
    nlinarith [le_abs_self uv.1, le_abs_self uv.2, neg_le_abs s]
  have hparam₁_pos : 0 < (1 - t) * s + t * uv.1 := by
    have hmul : -t * M ≤ t * (uv.1 - s) := by
      nlinarith [mul_le_mul_of_nonneg_left h_us_lower ht_nonneg]
    nlinarith [hs.1, htM_le_s_half, hmul]
  have hparam₂_pos : 0 < t * uv.2 := by
    positivity
  have hparam_sum_lt :
      (1 - t) * s + t * uv.1 + t * uv.2 < 1 := by
    have hmul : t * (uv.1 + uv.2 - s) ≤ t * M := by
      exact mul_le_mul_of_nonneg_left h_uvs_upper ht_nonneg
    nlinarith [hs.2, htM_le_gap_half, hmul]
  let x : P := (1 - t) • m + t • d
  refine ⟨x, ?_, ?_⟩
  · rw [openSegment_eq_image]
    exact ⟨t, ⟨ht_pos, ht_lt_one⟩, rfl⟩
  · rw [interior_convexHull_triangle_of_doubleArea_ne_zero a b c hnd]
    refine ⟨((1 - t) * s + t * uv.1, t * uv.2), ?_, ?_⟩
    · exact ⟨hparam₁_pos, hparam₂_pos, hparam_sum_lt⟩
    · calc
        triangleAffine a b c ((1 - t) * s + t * uv.1, t * uv.2)
            = triangleAffine a b c ((1 - t) • (s, 0) + t • uv) := by
                congr 1
                ext <;> simp [Prod.smul_def] <;> ring
        _ = (1 - t) • triangleAffine a b c (s, 0) +
              t • triangleAffine a b c uv := by
                exact triangleAffine_convex_combo a b c (s, 0) uv (by ring)
        _ = x := by
              simp [x, hm', hd]

lemma exists_common_interior_of_common_sameSide
    (a b c u v w d m : P)
    (habc : doubleArea a b c ≠ 0) (huvw : doubleArea u v w ≠ 0)
    (hmab : m ∈ openSegment ℝ a b) (hmuv : m ∈ openSegment ℝ u v)
    (hdab : 0 < doubleArea a b d * doubleArea a b c)
    (hduv : 0 < doubleArea u v d * doubleArea u v w) :
    ∃ x : P,
      x ∈ interior (convexHull ℝ ({a, b, c} : Set P)) ∧
        x ∈ interior (convexHull ℝ ({u, v, w} : Set P)) := by
  obtain ⟨x₁, hx₁seg, hx₁int⟩ :=
    exists_openSegment_to_sameSide_mem_interior_convexHull a b c d m habc hmab hdab
  obtain ⟨x₂, hx₂seg, hx₂int⟩ :=
    exists_openSegment_to_sameSide_mem_interior_convexHull u v w d m huvw hmuv hduv
  rw [openSegment_eq_image] at hx₁seg hx₂seg
  rcases hx₁seg with ⟨t₁, ht₁, hx₁⟩
  rcases hx₂seg with ⟨t₂, ht₂, hx₂⟩
  let t : ℝ := min t₁ t₂ / 2
  have htpos : 0 < t := by
    dsimp [t]
    exact half_pos (lt_min ht₁.1 ht₂.1)
  have htt₁ : t < t₁ := by
    dsimp [t]
    have hmin : min t₁ t₂ ≤ t₁ := min_le_left _ _
    nlinarith [ht₁.1, hmin]
  have htt₂ : t < t₂ := by
    dsimp [t]
    have hmin : min t₁ t₂ ≤ t₂ := min_le_right _ _
    nlinarith [ht₂.1, hmin]
  let x : P := (1 - t) • m + t • d
  have hmab_seg : m ∈ segment ℝ a b :=
    openSegment_subset_segment ℝ a b hmab
  have hmuv_seg : m ∈ segment ℝ u v :=
    openSegment_subset_segment ℝ u v hmuv
  have hm₁ : m ∈ convexHull ℝ ({a, b, c} : Set P) := by
    exact segment_subset_convexHull (by simp) (by simp) hmab_seg
  have hm₂ : m ∈ convexHull ℝ ({u, v, w} : Set P) := by
    exact segment_subset_convexHull (by simp) (by simp) hmuv_seg
  have hx_open₁ : x ∈ openSegment ℝ m x₁ := by
    rw [openSegment_eq_image]
    refine ⟨t / t₁, ⟨div_pos htpos ht₁.1, ?_⟩, ?_⟩
    · exact (div_lt_one ht₁.1).mpr htt₁
    · rw [← hx₁]
      ext <;> simp [x] <;> field_simp [ne_of_gt ht₁.1] <;> ring
  have hx_open₂ : x ∈ openSegment ℝ m x₂ := by
    rw [openSegment_eq_image]
    refine ⟨t / t₂, ⟨div_pos htpos ht₂.1, ?_⟩, ?_⟩
    · exact (div_lt_one ht₂.1).mpr htt₂
    · rw [← hx₂]
      ext <;> simp [x] <;> field_simp [ne_of_gt ht₂.1] <;> ring
  refine ⟨x, ?_, ?_⟩
  · exact (convex_convexHull ℝ ({a, b, c} : Set P)).openSegment_self_interior_subset_interior
      hm₁ hx₁int hx_open₁
  · exact (convex_convexHull ℝ ({u, v, w} : Set P)).openSegment_self_interior_subset_interior
      hm₂ hx₂int hx_open₂

lemma exists_common_sameSide_of_transversal_directions
    (a b c u v w m : P)
    (habc : doubleArea a b c ≠ 0) (huvw : doubleArea u v w ≠ 0)
    (hmab : m ∈ openSegment ℝ a b) (hmuv : m ∈ openSegment ℝ u v)
    (habuv : doubleArea a b (m + (v - u)) ≠ 0)
    (huvab : doubleArea u v (m + (b - a)) ≠ 0) :
    ∃ d : P,
      0 < doubleArea a b d * doubleArea a b c ∧
        0 < doubleArea u v d * doubleArea u v w := by
  let δab : ℝ := doubleArea a b (m + (v - u))
  let δuv : ℝ := doubleArea u v (m + (b - a))
  let s₁ : ℝ := doubleArea a b c
  let s₂ : ℝ := doubleArea u v w
  let α : ℝ := s₂ * δuv
  let β : ℝ := s₁ * δab
  let d : P := m + α • (b - a) + β • (v - u)
  have hmab0 : doubleArea a b m = 0 :=
    doubleArea_eq_zero_of_mem_segment (openSegment_subset_segment ℝ a b hmab)
  have hmuv0 : doubleArea u v m = 0 :=
    doubleArea_eq_zero_of_mem_segment (openSegment_subset_segment ℝ u v hmuv)
  have hdab_eq : doubleArea a b d = β * δab := by
    simpa [d, δab] using doubleArea_direction_combo a b m u v α β hmab0
  have hduv_eq : doubleArea u v d = α * δuv := by
    simpa [d, δuv] using doubleArea_direction_combo_uv u v m a b α β hmuv0
  refine ⟨d, ?_, ?_⟩
  · rw [hdab_eq]
    have hs₁sq : 0 < s₁ * s₁ := by
      dsimp [s₁]
      nlinarith [sq_pos_of_ne_zero habc]
    have hδabsq : 0 < δab * δab := by
      dsimp [δab]
      nlinarith [sq_pos_of_ne_zero habuv]
    dsimp [β, s₁]
    nlinarith
  · rw [hduv_eq]
    have hs₂sq : 0 < s₂ * s₂ := by
      dsimp [s₂]
      nlinarith [sq_pos_of_ne_zero huvw]
    have hδuvsq : 0 < δuv * δuv := by
      dsimp [δuv]
      nlinarith [sq_pos_of_ne_zero huvab]
    dsimp [α, s₂]
    nlinarith

theorem frontier_unitSquare :
    frontier (Set.Icc ((0, 0) : P) (1, 1)) =
      {p : P | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 ∧
        (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1)} := by
  have hsquare :
      Set.Icc ((0, 0) : P) (1, 1) =
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp [Set.mem_Icc, Prod.le_def]
  rw [hsquare, frontier_prod_eq,
    frontier_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
  simp [closure_Icc]
  ext p
  simp [Set.mem_Icc]
  aesop

theorem frontier_convexHull_triangle_of_doubleArea_ne_zero (a b c : P)
    (hnd : doubleArea a b c ≠ 0) :
    frontier (convexHull ℝ ({a, b, c} : Set P)) =
      segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a := by
  let h := triangleAffineHomeomorph a b c hnd
  have hfront := h.image_frontier filled2Simplex
  rw [frontier_filled2Simplex] at hfront
  rw [triangleAffineHomeomorph_image_filled2Simplex a b c hnd] at hfront
  rw [← hfront]
  rw [Set.image_union, Set.image_union,
    triangleAffineHomeomorph_image_bottom,
    triangleAffineHomeomorph_image_diag,
    triangleAffineHomeomorph_image_left]

end Chapter20E2Frontier

export Chapter20E2Frontier
  (frontier_convexHull_triangle_of_doubleArea_ne_zero
   interior_convexHull_triangle_of_doubleArea_ne_zero
   doubleArea_edge_triangleAffine
   doubleArea_edge_mul_nonneg_of_mem_convexHull
   doubleArea_edge_mul_pos_of_mem_interior_convexHull
   doubleArea_eq_zero_of_mem_segment
   doubleArea_direction_combo
   doubleArea_direction_combo_uv
   openSegment_edge_to_opposite_subset_interior_convexHull
   exists_openSegment_to_sameSide_mem_interior_convexHull
   exists_common_interior_of_common_sameSide
   exists_common_sameSide_of_transversal_directions
   frontier_unitSquare)

end ProofsInTheBook.Chapter20
