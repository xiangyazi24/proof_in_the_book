import Mathlib

/-!
# Planar sector sums

This file provides the two-dimensional normal form used by the Chapter 9
pearl-angle route.  Sectors are represented by normalized real angle intervals;
the geometric carriers are the corresponding polar images in
`EuclideanSpace ℝ (Fin 2)`.

The local model contains only geometric data: common radius, normalized
nondegenerate intervals, pairwise disjoint open carriers, and equality between
the finite union of closed carriers and the target wedge.  The sorted angular
chain is derived below from those set-level hypotheses.

For `θ = 2π`, the carrier is still periodic at the cut.  The proof therefore
uses coverage of the open target arc `(0, θ)`; this avoids pretending that the
points at angles `0` and `2π` have a unique linear representative.  The finite
gap argument then forces the first and last sorted interval endpoints to be
`0` and `2π`.
-/

namespace ProofsInTheBook
namespace SectorSum

open scoped BigOperators

noncomputable section

/-- The 2D Euclidean plane used for sector cross-sections. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- `2π`, used as the normalized full-turn angle. -/
def twoPi : ℝ := 2 * Real.pi

/-- The unit vector with polar angle `φ`. -/
def polarUnit (φ : ℝ) : Plane :=
  WithLp.toLp 2 fun i : Fin 2 => if i = 0 then Real.cos φ else Real.sin φ

/-- The point with polar coordinates `(r, φ)` about the apex `x`. -/
def polarPoint (x : Plane) (r φ : ℝ) : Plane :=
  x + r • polarUnit φ

/-- A closed nonempty angular interval. -/
structure SectorInterval where
  lo : ℝ
  hi : ℝ
  lo_le_hi : lo ≤ hi

namespace SectorInterval

/-- The angular size of a sector interval. -/
def angle (I : SectorInterval) : ℝ :=
  I.hi - I.lo

/-- Closed angle interval as a set of real polar angles. -/
def closedAngles (I : SectorInterval) : Set ℝ :=
  Set.Icc I.lo I.hi

/-- Open angle interval as a set of real polar angles. -/
def openAngles (I : SectorInterval) : Set ℝ :=
  Set.Ioo I.lo I.hi

/-- Closed polar sector with common apex `x` and radius `ε`. -/
def closedCarrier (x : Plane) (ε : ℝ) (I : SectorInterval) : Set Plane :=
  {p | ∃ r φ : ℝ,
    0 ≤ r ∧ r ≤ ε ∧ φ ∈ I.closedAngles ∧ p = polarPoint x r φ}

/-- The corresponding open radial and angular sector interior. -/
def openCarrier (x : Plane) (ε : ℝ) (I : SectorInterval) : Set Plane :=
  {p | ∃ r φ : ℝ,
    0 < r ∧ r < ε ∧ φ ∈ I.openAngles ∧ p = polarPoint x r φ}

theorem angle_nonneg (I : SectorInterval) : 0 ≤ I.angle := by
  exact sub_nonneg.mpr I.lo_le_hi

end SectorInterval

/-- Sum of sector angles for a finite labelled sector family. -/
def sectorAngleSum (sectors : List SectorInterval) : ℝ :=
  (sectors.map SectorInterval.angle).sum

/-- Union of the closed carriers of a finite sector family. -/
def sectorUnion (x : Plane) (ε : ℝ) (sectors : List SectorInterval) : Set Plane :=
  {p | ∃ I, I ∈ sectors ∧ p ∈ SectorInterval.closedCarrier x ε I}

/-- The normalized closed wedge `[0, θ]` of radius `ε` about `x`. -/
def closedWedgeCarrier (x : Plane) (ε θ : ℝ) : Set Plane :=
  {p | ∃ r φ : ℝ,
    0 ≤ r ∧ r ≤ ε ∧ 0 ≤ φ ∧ φ ≤ θ ∧ p = polarPoint x r φ}

/-- The half-disk local model, normalized as angles in `[0, π]`. -/
def closedHalfDiskCarrier (x : Plane) (ε : ℝ) : Set Plane :=
  closedWedgeCarrier x ε Real.pi

/-- The disk local model, normalized as angles in `[0, 2π]`. -/
def closedDiskCarrier (x : Plane) (ε : ℝ) : Set Plane :=
  closedWedgeCarrier x ε twoPi

/--
`IsChainFrom a θ sectors` means that the sectors form a sorted interval chain
starting at angle `a` and ending at `θ`.
-/
def IsChainFrom (a θ : ℝ) : List SectorInterval → Prop
  | [] => a = θ
  | I :: rest => I.lo = a ∧ IsChainFrom I.hi θ rest

private theorem angle_sum_of_chainFrom
    {a θ : ℝ} {sectors : List SectorInterval}
    (h : IsChainFrom a θ sectors) :
    sectorAngleSum sectors = θ - a := by
  induction sectors generalizing a with
  | nil =>
      dsimp [IsChainFrom] at h
      rw [h]
      simp [sectorAngleSum]
  | cons I rest ih =>
      dsimp [IsChainFrom] at h
      rcases h with ⟨hlo, hrest⟩
      calc
        sectorAngleSum (I :: rest)
            = (I.hi - I.lo) + sectorAngleSum rest := by
                simp [sectorAngleSum, SectorInterval.angle]
        _ = (I.hi - a) + (θ - I.hi) := by
                rw [hlo, ih hrest]
        _ = θ - a := by ring

private def loLE (I J : SectorInterval) : Prop :=
  I.lo ≤ J.lo

private instance : DecidableRel loLE :=
  fun I J => inferInstanceAs (Decidable (I.lo ≤ J.lo))

private instance : IsTrans SectorInterval loLE where
  trans := by
    intro I J K hIJ hJK
    exact le_trans hIJ hJK

private instance : Std.Total loLE where
  total := by
    intro I J
    exact le_total I.lo J.lo

private def sortByLo (sectors : List SectorInterval) : List SectorInterval :=
  sectors.mergeSort (loLE · ·)

private def NormalizedFrom (a θ : ℝ) (sectors : List SectorInterval) : Prop :=
  ∀ I, I ∈ sectors → a ≤ I.lo ∧ I.lo < I.hi ∧ I.hi ≤ θ

private def CoversOpenArc (a θ : ℝ) (sectors : List SectorInterval) : Prop :=
  ∀ φ, a < φ → φ < θ → ∃ I, I ∈ sectors ∧ φ ∈ I.closedAngles

private theorem sectorAngleSum_perm
    {s t : List SectorInterval} (h : s.Perm t) :
    sectorAngleSum s = sectorAngleSum t := by
  simpa [sectorAngleSum] using (h.map SectorInterval.angle).sum_eq

private theorem chain_of_sorted_open_cover_from
    {a θ : ℝ} {sectors : List SectorInterval}
    (haθ : a ≤ θ)
    (hsorted : sectors.Pairwise loLE)
    (hnorm : NormalizedFrom a θ sectors)
    (hdisj : sectors.Pairwise
      (fun I J => Disjoint I.openAngles J.openAngles))
    (hcover : CoversOpenArc a θ sectors) :
    IsChainFrom a θ sectors := by
  induction sectors generalizing a with
  | nil =>
      dsimp [IsChainFrom]
      have hnot : ¬ a < θ := by
        intro ha_lt
        let φ := (a + θ) / 2
        have haφ : a < φ := by
          dsimp [φ]
          linarith
        have hφθ : φ < θ := by
          dsimp [φ]
          linarith
        rcases hcover φ haφ hφθ with ⟨I, hI, _⟩
        cases hI
      exact le_antisymm haθ (le_of_not_gt hnot)
  | cons I rest ih =>
      dsimp [IsChainFrom]
      have hsort_cons := List.pairwise_cons.mp hsorted
      have hI_le_rest : ∀ J, J ∈ rest → I.lo ≤ J.lo := by
        intro J hJ
        exact hsort_cons.1 J hJ
      have hsorted_rest : rest.Pairwise loLE := hsort_cons.2
      have hdisj_cons := List.pairwise_cons.mp hdisj
      have hI_disj_rest :
          ∀ J, J ∈ rest → Disjoint I.openAngles J.openAngles := by
        intro J hJ
        exact hdisj_cons.1 J hJ
      have hdisj_rest : rest.Pairwise
          (fun I J => Disjoint I.openAngles J.openAngles) := hdisj_cons.2
      have hInorm : a ≤ I.lo ∧ I.lo < I.hi ∧ I.hi ≤ θ :=
        hnorm I (by simp)
      have hIlo_eq : I.lo = a := by
        have hnot : ¬ a < I.lo := by
          intro hgap
          let φ := (a + I.lo) / 2
          have haφ : a < φ := by
            dsimp [φ]
            linarith
          have hφIlo : φ < I.lo := by
            dsimp [φ]
            linarith
          have hφθ : φ < θ := by
            linarith [hφIlo, hInorm.2.1, hInorm.2.2]
          rcases hcover φ haφ hφθ with ⟨K, hK, hKφ⟩
          have hKclosed := Set.mem_Icc.mp hKφ
          rw [List.mem_cons] at hK
          rcases hK with hK | hKrest
          · subst K
            linarith
          · have hIleK : I.lo ≤ K.lo := hI_le_rest K hKrest
            linarith
        exact le_antisymm (le_of_not_gt hnot) hInorm.1
      refine ⟨hIlo_eq, ?_⟩
      cases rest with
      | nil =>
          dsimp [IsChainFrom]
          have hnot : ¬ I.hi < θ := by
            intro hgap
            let φ := (I.hi + θ) / 2
            have hIhiφ : I.hi < φ := by
              dsimp [φ]
              linarith
            have hφθ : φ < θ := by
              dsimp [φ]
              linarith
            have haφ : a < φ := by
              rw [← hIlo_eq]
              linarith [hInorm.2.1, hIhiφ]
            rcases hcover φ haφ hφθ with ⟨K, hK, hKφ⟩
            have hKclosed := Set.mem_Icc.mp hKφ
            rw [List.mem_cons] at hK
            rcases hK with hK | hKnil
            · subst K
              linarith
            · cases hKnil
          exact le_antisymm hInorm.2.2 (le_of_not_gt hnot)
      | cons J tail =>
          have hrest_pair := List.pairwise_cons.mp hsorted_rest
          have hJ_le_tail : ∀ K, K ∈ tail → J.lo ≤ K.lo := by
            intro K hK
            exact hrest_pair.1 K hK
          have hJnorm : a ≤ J.lo ∧ J.lo < J.hi ∧ J.hi ≤ θ :=
            hnorm J (by simp)
          have hnot_overlap : ¬ J.lo < I.hi := by
            intro hover
            let φ := (J.lo + min I.hi J.hi) / 2
            have hJlo_lt_min : J.lo < min I.hi J.hi := by
              exact lt_min hover hJnorm.2.1
            have hJloφ : J.lo < φ := by
              dsimp [φ]
              linarith
            have hφmin : φ < min I.hi J.hi := by
              dsimp [φ]
              linarith
            have hIloφ : I.lo < φ := by
              have hIleJ : I.lo ≤ J.lo := hI_le_rest J (by simp)
              linarith
            have hφIhi : φ < I.hi := lt_of_lt_of_le hφmin (min_le_left _ _)
            have hφJhi : φ < J.hi := lt_of_lt_of_le hφmin (min_le_right _ _)
            have hnotdisj : ¬ Disjoint I.openAngles J.openAngles := by
              rw [Set.not_disjoint_iff]
              exact ⟨φ, ⟨hIloφ, hφIhi⟩, ⟨hJloφ, hφJhi⟩⟩
            exact hnotdisj (hI_disj_rest J (by simp))
          have hnot_gap : ¬ I.hi < J.lo := by
            intro hgap
            let φ := (I.hi + J.lo) / 2
            have hIhiφ : I.hi < φ := by
              dsimp [φ]
              linarith
            have hφJlo : φ < J.lo := by
              dsimp [φ]
              linarith
            have haφ : a < φ := by
              rw [← hIlo_eq]
              linarith [hInorm.2.1, hIhiφ]
            have hφθ : φ < θ := by
              linarith [hφJlo, hJnorm.2.2]
            rcases hcover φ haφ hφθ with ⟨K, hK, hKφ⟩
            have hKclosed := Set.mem_Icc.mp hKφ
            rw [List.mem_cons] at hK
            rcases hK with hK | hKrest
            · subst K
              linarith
            · rw [List.mem_cons] at hKrest
              rcases hKrest with hK | hKtail
              · subst K
                linarith
              · have hJleK : J.lo ≤ K.lo := hJ_le_tail K hKtail
                linarith
          have hbridge : I.hi = J.lo :=
            le_antisymm (le_of_not_gt hnot_overlap) (le_of_not_gt hnot_gap)
          have hIhiθ : I.hi ≤ θ := hInorm.2.2
          have hnorm_rest : NormalizedFrom I.hi θ (J :: tail) := by
            intro K hK
            have hKnorm : a ≤ K.lo ∧ K.lo < K.hi ∧ K.hi ≤ θ :=
              hnorm K (by simp [hK])
            rw [List.mem_cons] at hK
            have hIhi_le_Klo : I.hi ≤ K.lo := by
              rcases hK with hK | hKtail
              · subst K
                exact le_of_eq hbridge
              · have hJleK : J.lo ≤ K.lo := hJ_le_tail K hKtail
                exact le_trans (le_of_eq hbridge) hJleK
            exact ⟨hIhi_le_Klo, hKnorm.2.1, hKnorm.2.2⟩
          have hcover_rest : CoversOpenArc I.hi θ (J :: tail) := by
            intro φ hIhiφ hφθ
            have haφ : a < φ := by
              rw [← hIlo_eq]
              linarith [hInorm.2.1, hIhiφ]
            rcases hcover φ haφ hφθ with ⟨K, hK, hKφ⟩
            rw [List.mem_cons] at hK
            rcases hK with hK | hKrest
            · subst K
              have hKclosed := Set.mem_Icc.mp hKφ
              linarith
            · exact ⟨K, hKrest, hKφ⟩
          exact ih hIhiθ hsorted_rest hnorm_rest hdisj_rest hcover_rest

private theorem angle_sum_of_open_cover
    {θ : ℝ} {sectors : List SectorInterval}
    (hθ : 0 ≤ θ)
    (hnorm : NormalizedFrom 0 θ sectors)
    (hdisj : sectors.Pairwise
      (fun I J => Disjoint I.openAngles J.openAngles))
    (hcover : CoversOpenArc 0 θ sectors) :
    sectorAngleSum sectors = θ := by
  let sorted := sortByLo sectors
  have hperm : sorted.Perm sectors := by
    simpa [sorted, sortByLo] using
      (List.mergeSort_perm sectors (loLE · ·))
  have hsorted : sorted.Pairwise loLE := by
    simpa [sorted, sortByLo] using List.pairwise_mergeSort' loLE sectors
  have hnorm_sorted : NormalizedFrom 0 θ sorted := by
    intro I hI
    exact hnorm I (by simpa [sorted, sortByLo] using hI)
  have hdisj_sorted : sorted.Pairwise
      (fun I J => Disjoint I.openAngles J.openAngles) := by
    exact (List.Perm.pairwise_iff (fun h => h.symm) hperm).2 hdisj
  have hcover_sorted : CoversOpenArc 0 θ sorted := by
    intro φ h0φ hφθ
    rcases hcover φ h0φ hφθ with ⟨I, hI, hφI⟩
    exact ⟨I, by simpa [sorted, sortByLo] using hI, hφI⟩
  have hchain : IsChainFrom 0 θ sorted :=
    chain_of_sorted_open_cover_from hθ hsorted hnorm_sorted hdisj_sorted hcover_sorted
  have hsum_sorted : sectorAngleSum sorted = θ := by
    simpa using
      (angle_sum_of_chainFrom (a := 0) (θ := θ) (sectors := sorted) hchain)
  calc
    sectorAngleSum sectors = sectorAngleSum sorted := (sectorAngleSum_perm hperm).symm
    _ = θ := hsum_sorted

private theorem polarPoint_angle_eq_of_eq
    {x : Plane} {r s φ ψ : ℝ} (hr : 0 < r) (hs_nonneg : 0 ≤ s)
    (h : polarPoint x r φ = polarPoint x s ψ) :
    (φ : Real.Angle) = ψ := by
  have h0coord := congrArg (fun p : Plane => p.ofLp 0) h
  have h1coord := congrArg (fun p : Plane => p.ofLp 1) h
  simp [polarPoint, polarUnit] at h0coord h1coord
  have hcos_scaled : r * Real.cos φ = s * Real.cos ψ := by linarith
  have hsin_scaled : r * Real.sin φ = s * Real.sin ψ := by linarith
  have hsqr : r ^ 2 = s ^ 2 := by
    calc
      r ^ 2 = r ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2) := by
        rw [Real.cos_sq_add_sin_sq, mul_one]
      _ = (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 := by ring
      _ = (s * Real.cos ψ) ^ 2 + (s * Real.sin ψ) ^ 2 := by
        rw [hcos_scaled, hsin_scaled]
      _ = s ^ 2 * (Real.cos ψ ^ 2 + Real.sin ψ ^ 2) := by ring
      _ = s ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
  have hrs : r = s := by nlinarith [hr, hs_nonneg, hsqr]
  have hspos : 0 < s := by linarith
  have hcos : Real.cos φ = Real.cos ψ := by
    rw [hrs] at hcos_scaled
    exact mul_left_cancel₀ (ne_of_gt hspos) hcos_scaled
  have hsin : Real.sin φ = Real.sin ψ := by
    rw [hrs] at hsin_scaled
    exact mul_left_cancel₀ (ne_of_gt hspos) hsin_scaled
  exact Real.Angle.cos_sin_inj hcos hsin

private theorem real_eq_of_angle_eq_of_mem_open
    {φ ψ θ : ℝ} (hθle : θ ≤ twoPi)
    (hφ0 : 0 < φ) (hφθ : φ < θ)
    (hψ0 : 0 ≤ ψ) (hψθ : ψ ≤ θ)
    (hangle : (φ : Real.Angle) = ψ) :
    φ = ψ := by
  rcases Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hangle with ⟨k, hk⟩
  have hθle' : θ ≤ 2 * Real.pi := by simpa [twoPi] using hθle
  have hdiff_low : -(2 * Real.pi) < φ - ψ := by
    linarith [hφ0, hψθ, hθle']
  have hdiff_high : φ - ψ < 2 * Real.pi := by
    linarith [hφθ, hθle', hψ0]
  have hk0 : k = 0 := by
    refine IsStrictOrderedRing.int_eq_of_mul_mem_Ioo
      (r := 2 * Real.pi) Real.two_pi_pos (m := 0) ?_
    constructor
    · rw [← hk]
      norm_num
      linarith
    · rw [← hk]
      norm_num
      linarith
  rw [hk0, Int.cast_zero, mul_zero] at hk
  linarith

private theorem openAngles_disjoint_of_openCarrier_disjoint
    {x : Plane} {ε : ℝ} {I J : SectorInterval}
    (hε : 0 < ε)
    (h : Disjoint
      (SectorInterval.openCarrier x ε I)
      (SectorInterval.openCarrier x ε J)) :
    Disjoint I.openAngles J.openAngles := by
  by_contra hnot
  rw [Set.not_disjoint_iff] at hnot
  rcases hnot with ⟨φ, hφI, hφJ⟩
  let r := ε / 2
  have hr0 : 0 < r := by
    dsimp [r]
    linarith
  have hrε : r < ε := by
    dsimp [r]
    linarith
  let p := polarPoint x r φ
  have hpI : p ∈ SectorInterval.openCarrier x ε I :=
    ⟨r, φ, hr0, hrε, hφI, rfl⟩
  have hpJ : p ∈ SectorInterval.openCarrier x ε J :=
    ⟨r, φ, hr0, hrε, hφJ, rfl⟩
  have hnotCarrier :
      ¬ Disjoint
        (SectorInterval.openCarrier x ε I)
        (SectorInterval.openCarrier x ε J) := by
    rw [Set.not_disjoint_iff]
    exact ⟨p, hpI, hpJ⟩
  exact hnotCarrier h

private theorem open_angle_cover_of_local_cover
    {x : Plane} {ε θ : ℝ} {sectors : List SectorInterval}
    (hε : 0 < ε)
    (hθle : θ ≤ twoPi)
    (hnorm : ∀ I, I ∈ sectors → 0 ≤ I.lo ∧ I.hi ≤ θ)
    (hcover : sectorUnion x ε sectors = closedWedgeCarrier x ε θ) :
    CoversOpenArc 0 θ sectors := by
  intro φ hφ0 hφθ
  let r := ε / 2
  let p := polarPoint x r φ
  have hr0 : 0 < r := by
    dsimp [r]
    linarith
  have hrε : r ≤ ε := by
    dsimp [r]
    linarith
  have hpWedge : p ∈ closedWedgeCarrier x ε θ :=
    ⟨r, φ, le_of_lt hr0, hrε, le_of_lt hφ0, le_of_lt hφθ, rfl⟩
  have hpUnion : p ∈ sectorUnion x ε sectors := by
    simpa [hcover] using hpWedge
  rcases hpUnion with ⟨I, hI, ρ, ψ, hρ0, hρε, hψI, hp_eq⟩
  have hpoint : polarPoint x r φ = polarPoint x ρ ψ := by
    simpa [p] using hp_eq
  have hangle : (φ : Real.Angle) = ψ :=
    polarPoint_angle_eq_of_eq hr0 hρ0 hpoint
  have hInorm := hnorm I hI
  have hψclosed := Set.mem_Icc.mp hψI
  have hψ0 : 0 ≤ ψ := le_trans hInorm.1 hψclosed.1
  have hψθ : ψ ≤ θ := le_trans hψclosed.2 hInorm.2
  have hφeqψ : φ = ψ :=
    real_eq_of_angle_eq_of_mem_open hθle hφ0 hφθ hψ0 hψθ hangle
  exact ⟨I, hI, by simpa [hφeqψ] using hψI⟩

/--
A finite sector family whose local geometry is a target wedge.

The sorted angle chain is intentionally not a field: it is derived from
`interiors_disjoint` and `local_cover`.
-/
structure PlanarSectorLocalModel
    (x : Plane) (ε θ : ℝ) (sectors : List SectorInterval) : Prop where
  radius_pos : 0 < ε
  target_nonneg : 0 ≤ θ
  target_le_twoPi : θ ≤ twoPi
  intervals_normalized :
    ∀ I, I ∈ sectors → 0 ≤ I.lo ∧ I.hi ≤ θ
  intervals_nondegenerate :
    ∀ I, I ∈ sectors → I.lo < I.hi
  interiors_disjoint :
    sectors.Pairwise
      (fun I J => Disjoint
        (SectorInterval.openCarrier x ε I)
        (SectorInterval.openCarrier x ε J))
  local_cover :
    sectorUnion x ε sectors = closedWedgeCarrier x ε θ

private theorem sector_angle_sum_of_model
    {x : Plane} {ε θ : ℝ} {sectors : List SectorInterval}
    (hmodel : PlanarSectorLocalModel x ε θ sectors) :
    sectorAngleSum sectors = θ := by
  have hnorm : NormalizedFrom 0 θ sectors := by
    intro I hI
    rcases hmodel.intervals_normalized I hI with ⟨hlo, hhi⟩
    exact ⟨hlo, hmodel.intervals_nondegenerate I hI, hhi⟩
  have hdisj_angles : sectors.Pairwise
      (fun I J => Disjoint I.openAngles J.openAngles) := by
    exact hmodel.interiors_disjoint.imp (fun h =>
      openAngles_disjoint_of_openCarrier_disjoint hmodel.radius_pos h)
  have hcover_angles : CoversOpenArc 0 θ sectors :=
    open_angle_cover_of_local_cover hmodel.radius_pos hmodel.target_le_twoPi
      hmodel.intervals_normalized hmodel.local_cover
  exact angle_sum_of_open_cover hmodel.target_nonneg hnorm hdisj_angles hcover_angles

/--
Finite closed sectors with common apex whose interiors are disjoint and whose
local union is the normalized full disk have angle sum `2π`.
-/
theorem planar_sectors_disjoint_cover_disk_angle_sum
    {x : Plane} {ε : ℝ} {sectors : List SectorInterval}
    (hmodel : PlanarSectorLocalModel x ε twoPi sectors) :
    sectorAngleSum sectors = twoPi :=
  sector_angle_sum_of_model hmodel

/--
Finite closed sectors with common apex whose interiors are disjoint and whose
local union is the normalized half-disk have angle sum `π`.
-/
theorem planar_sectors_disjoint_cover_halfdisk_angle_sum
    {x : Plane} {ε : ℝ} {sectors : List SectorInterval}
    (hmodel : PlanarSectorLocalModel x ε Real.pi sectors) :
    sectorAngleSum sectors = Real.pi :=
  sector_angle_sum_of_model hmodel

/--
Finite closed sectors with common apex whose interiors are disjoint and whose
local union is a normalized wedge of angle `θ` have angle sum `θ`.

This is stated for the Chapter 9 use range `0 < θ < π`; the model itself
supports all `0 ≤ θ ≤ 2π`.
-/
theorem planar_sectors_disjoint_cover_wedge_angle_sum
    {x : Plane} {ε θ : ℝ} {sectors : List SectorInterval}
    (_hθ_pos : 0 < θ) (_hθ_lt_pi : θ < Real.pi)
    (hmodel : PlanarSectorLocalModel x ε θ sectors) :
    sectorAngleSum sectors = θ :=
  sector_angle_sum_of_model hmodel

end

end SectorSum
end ProofsInTheBook
