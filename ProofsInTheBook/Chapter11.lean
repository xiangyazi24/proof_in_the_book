import Mathlib

/-!
# Chapter 11: The slope problem

From "Proofs from THE BOOK":

**The slope problem (Ungar's theorem)**: Given n points in the plane,
not all on a line, the number of distinct slopes determined by
connecting pairs of points is at least n - 1.

The book's proof uses an elegant inductive argument combined with
a "rotating calipers" technique: consider the convex hull and analyze
how slopes change as we rotate a direction vector.

This is closely related to the Sylvester-Gallai theorem (Chapter 10).
-/

namespace ProofsInTheBook.Chapter11

abbrev Point2 := ℝ × ℝ

inductive Direction where
  | vertical
  | finite (m : ℝ)

noncomputable instance : DecidableEq Direction :=
  Classical.decEq Direction

/-- The slope determined by an ordered pair of planar points. -/
noncomputable def slope (p q : Point2) : ℝ :=
  (q.2 - p.2) / (q.1 - p.1)

/-- The projective direction determined by a pair of points, including vertical lines. -/
noncomputable def direction (p q : Point2) : Direction :=
  if p.1 = q.1 then Direction.vertical else Direction.finite (slope p q)

theorem slope_comm {p q : Point2} : slope p q = slope q p := by
  by_cases hx : q.1 - p.1 = 0
  · have hx' : p.1 - q.1 = 0 := by linarith
    simp [slope, hx, hx']
  · have hx' : p.1 - q.1 ≠ 0 := by
      intro h
      exact hx (by linarith)
    unfold slope
    field_simp [hx, hx']
    ring

theorem direction_comm {p q : Point2} : direction p q = direction q p := by
  by_cases hx : p.1 = q.1
  · have hx' : q.1 = p.1 := hx.symm
    unfold direction
    rw [if_pos hx, if_pos hx']
  · have hx' : q.1 ≠ p.1 := by exact fun h => hx h.symm
    unfold direction
    rw [if_neg hx, if_neg hx', slope_comm]

/-- Coordinate of the line parallel to a projective direction through `p`. -/
noncomputable def directionLevel (d : Direction) (p : Point2) : ℝ :=
  match d with
  | Direction.vertical => p.1
  | Direction.finite m => p.2 - m * p.1

/-- Oriented projection level: the signed projection of point `p` onto the
line perpendicular to angle `θ`. Unlike `directionLevel`, this is continuous
in `θ` across the vertical direction. -/
noncomputable def orientedLevel (θ : ℝ) (p : Point2) : ℝ :=
  -p.1 * Real.sin θ + p.2 * Real.cos θ

theorem orientedLevel_zero (p : Point2) : orientedLevel 0 p = p.2 := by
  simp [orientedLevel]

theorem orientedLevel_add_pi (θ : ℝ) (p : Point2) :
    orientedLevel (θ + Real.pi) p = -orientedLevel θ p := by
  simp [orientedLevel, Real.sin_add, Real.cos_add, Real.sin_pi, Real.cos_pi]
  ring

theorem orientedLevel_pi_div_two (p : Point2) :
    orientedLevel (Real.pi / 2) p = -p.1 := by
  simp [orientedLevel, Real.sin_pi_div_two, Real.cos_pi_div_two]

theorem orientedLevel_sub_eq (θ : ℝ) (p q : Point2) :
    orientedLevel θ p - orientedLevel θ q =
      -(p.1 - q.1) * Real.sin θ + (p.2 - q.2) * Real.cos θ := by
  simp [orientedLevel]; ring

theorem orientedLevel_eq_cos_mul_directionLevel {θ : ℝ} (hcos : Real.cos θ ≠ 0)
    (p : Point2) :
    orientedLevel θ p = Real.cos θ * directionLevel (Direction.finite (Real.tan θ)) p := by
  simp [orientedLevel, directionLevel, Real.tan_eq_sin_div_cos]
  field_simp; ring

theorem directionLevel_eq_of_orientedLevel_eq {θ : ℝ} (hcos : Real.cos θ ≠ 0)
    {p q : Point2} (h : orientedLevel θ p = orientedLevel θ q) :
    directionLevel (Direction.finite (Real.tan θ)) p =
      directionLevel (Direction.finite (Real.tan θ)) q := by
  have hp := orientedLevel_eq_cos_mul_directionLevel hcos p
  have hq := orientedLevel_eq_cos_mul_directionLevel hcos q
  linarith [mul_left_cancel₀ hcos (by linarith : Real.cos θ *
    directionLevel (Direction.finite (Real.tan θ)) p =
    Real.cos θ * directionLevel (Direction.finite (Real.tan θ)) q)]

noncomputable def Direction.angle : Direction → ℝ
  | .vertical => Real.pi / 2
  | .finite m => if 0 ≤ Real.arctan m then Real.arctan m else Real.arctan m + Real.pi

theorem Direction.angle_nonneg (d : Direction) : 0 ≤ d.angle := by
  cases d with
  | vertical => exact le_of_lt (div_pos Real.pi_pos two_pos)
  | finite m =>
    simp only [Direction.angle]
    split_ifs with h
    · exact h
    · linarith [Real.neg_pi_div_two_lt_arctan m]

theorem Direction.angle_lt_pi (d : Direction) : d.angle < Real.pi := by
  cases d with
  | vertical => show Real.pi / 2 < Real.pi; linarith [Real.pi_pos]
  | finite m =>
    simp only [Direction.angle]
    split_ifs with h
    · linarith [Real.arctan_lt_pi_div_two m]
    · linarith [Real.neg_pi_div_two_lt_arctan m]

theorem Direction.angle_injective : Function.Injective Direction.angle := by
  intro d1 d2 h
  match d1, d2 with
  | .vertical, .vertical => rfl
  | .vertical, .finite m =>
    simp only [Direction.angle] at h
    split_ifs at h with hm
    · linarith [Real.arctan_lt_pi_div_two m]
    · linarith [Real.neg_pi_div_two_lt_arctan m]
  | .finite m, .vertical =>
    simp only [Direction.angle] at h
    split_ifs at h with hm
    · linarith [Real.arctan_lt_pi_div_two m]
    · linarith [Real.neg_pi_div_two_lt_arctan m]
  | .finite m1, .finite m2 =>
    simp only [Direction.angle] at h
    split_ifs at h with h1 h2 h1 h2
    · exact congr_arg _ (Real.arctan_injective h)
    · linarith [Real.arctan_lt_pi_div_two m1, Real.neg_pi_div_two_lt_arctan m2]
    · linarith [Real.arctan_lt_pi_div_two m2, Real.neg_pi_div_two_lt_arctan m1]
    · exact congr_arg _ (Real.arctan_injective (by linarith))

theorem Direction.angle_ne_of_ne {d₁ d₂ : Direction} (h : d₁ ≠ d₂) :
    d₁.angle ≠ d₂.angle := by
  exact fun h_eq => h (Direction.angle_injective h_eq)

/--
The finite set of slopes determined by nonvertical ordered pairs of distinct
points in a configuration.
-/
noncomputable def slopesDeterminedBy (points : Finset Point2) : Finset ℝ :=
  ((points.product points).filter fun pq => pq.1 ≠ pq.2 ∧ pq.1.1 ≠ pq.2.1).image
    (fun pq => slope pq.1 pq.2)

/-- The finite set of all directions determined by distinct pairs of points. -/
noncomputable def directionsDeterminedBy (points : Finset Point2) : Finset Direction :=
  ((points.product points).filter fun pq => pq.1 ≠ pq.2).image
    (fun pq => direction pq.1 pq.2)

noncomputable def sortedDirectionAngles (points : Finset Point2) : List ℝ :=
  ((directionsDeterminedBy points).image Direction.angle).sort (· ≤ ·)

noncomputable def genericAngleBetween (θ₁ θ₂ : ℝ) : ℝ := (θ₁ + θ₂) / 2

theorem genericAngleBetween_lt {θ₁ θ₂ : ℝ} (h : θ₁ < θ₂) :
    θ₁ < genericAngleBetween θ₁ θ₂ := by
  simp [genericAngleBetween]; linarith

theorem genericAngleBetween_lt' {θ₁ θ₂ : ℝ} (h : θ₁ < θ₂) :
    genericAngleBetween θ₁ θ₂ < θ₂ := by
  simp [genericAngleBetween]; linarith

/-- Three points are non-collinear, expressed by a nonzero determinant. -/
def NoncollinearTriple (p q r : Point2) : Prop :=
  ¬ (q.2 - p.2) * (r.1 - p.1) = (r.2 - p.2) * (q.1 - p.1)

/-- A finite point configuration is not contained in one line. -/
def NoncollinearSet (points : Finset Point2) : Prop :=
  ∃ p ∈ points, ∃ q ∈ points, ∃ r ∈ points, NoncollinearTriple p q r

/-- The configuration determines the vertical direction. -/
def HasVerticalPair (points : Finset Point2) : Prop :=
  ∃ p ∈ points, ∃ q ∈ points, p ≠ q ∧ p.1 = q.1

/-- No two distinct points in the configuration have the same x-coordinate. -/
def NoVerticalPairs (points : Finset Point2) : Prop :=
  ∀ ⦃p q⦄, p ∈ points → q ∈ points → p ≠ q → p.1 ≠ q.1

structure PointLabeling (points : Finset Point2) (k : ℕ) where
  point : Fin (2 * k) → Point2
  mem_point : ∀ a, point a ∈ points
  point_injective : Function.Injective point
  point_surjective_on : ∀ p ∈ points, ∃ a, point a = p

structure DirectionLabeling (points : Finset Point2) where
  dir : Fin (directionsDeterminedBy points).card → Direction
  mem_dir : ∀ j, dir j ∈ directionsDeterminedBy points
  dir_injective : Function.Injective dir
  dir_surjective_on : ∀ d ∈ directionsDeterminedBy points, ∃ j, dir j = d

namespace PointLabeling

noncomputable def ofCard {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k) : PointLabeling points k where
  point := fun a => (Finset.equivFinOfCardEq hcard).symm a
  mem_point := fun a => ((Finset.equivFinOfCardEq hcard).symm a).2
  point_injective := by
    intro a b h
    have hsub :
        (Finset.equivFinOfCardEq hcard).symm a =
          (Finset.equivFinOfCardEq hcard).symm b := by
      exact Subtype.ext h
    exact (Finset.equivFinOfCardEq hcard).symm.injective hsub
  point_surjective_on := by
    intro p hp
    refine ⟨(Finset.equivFinOfCardEq hcard) ⟨p, hp⟩, ?_⟩
    simp

end PointLabeling

namespace DirectionLabeling

noncomputable def ofDirections (points : Finset Point2) : DirectionLabeling points where
  dir := fun j => (Finset.equivFin (directionsDeterminedBy points)).symm j
  mem_dir := fun j => ((Finset.equivFin (directionsDeterminedBy points)).symm j).2
  dir_injective := by
    intro i j h
    have hsub :
        (Finset.equivFin (directionsDeterminedBy points)).symm i =
          (Finset.equivFin (directionsDeterminedBy points)).symm j := by
      exact Subtype.ext h
    exact (Finset.equivFin (directionsDeterminedBy points)).symm.injective hsub
  dir_surjective_on := by
    intro d hd
    refine ⟨(Finset.equivFin (directionsDeterminedBy points)) ⟨d, hd⟩, ?_⟩
    simp

end DirectionLabeling

/-! ### Sweep construction via oriented levels -/

noncomputable def sweepSort {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ : ℝ) : Equiv.Perm (Fin (2 * k)) :=
  Tuple.sort (fun a : Fin (2 * k) => orientedLevel θ (L.point a))

theorem sweepSort_monotone {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ : ℝ) :
    Monotone (fun i => orientedLevel θ (L.point (sweepSort L θ i))) := by
  have := Tuple.monotone_sort (fun a : Fin (2 * k) => orientedLevel θ (L.point a))
  exact this

noncomputable def PointLabeling.reindex {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (σ : Equiv.Perm (Fin (2 * k))) :
    PointLabeling points k where
  point := L.point ∘ σ
  mem_point := fun a => L.mem_point (σ a)
  point_injective := L.point_injective.comp σ.injective
  point_surjective_on := fun p hp => by
    rcases L.point_surjective_on p hp with ⟨a, ha⟩
    exact ⟨σ.symm a, by simp [Function.comp, ha]⟩

theorem sweepSort_reindex_eq_refl {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ₀ : ℝ) :
    sweepSort (L.reindex (sweepSort L θ₀)) θ₀ = Equiv.refl _ :=
  Tuple.sort_eq_refl_iff_monotone.mpr (sweepSort_monotone L θ₀)

theorem sort_neg_eq_revPerm {N : ℕ} {f : Fin N → ℝ}
    (hf : StrictMono f) :
    Tuple.sort (fun a => -f a) = Fin.revPerm := by
  symm
  rw [Tuple.eq_sort_iff]
  refine ⟨?_, ?_⟩
  · intro i j hij
    simp only [Function.comp, Fin.revPerm_apply]
    have : Fin.rev j ≤ Fin.rev i := Fin.rev_le_rev.mpr hij
    linarith [hf.monotone this]
  · intro i j hij heq
    exfalso
    simp only [Fin.revPerm_apply] at heq
    have h1 : f (Fin.rev i) = f (Fin.rev j) := by linarith
    exact absurd (Fin.rev_injective (hf.injective h1)) (ne_of_lt hij)

theorem sweepSort_strictMono_of_injective {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ : ℝ)
    (hinj : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ (L.point a))) :
    StrictMono (fun i => orientedLevel θ (L.point (sweepSort L θ i))) := by
  intro i j hij
  have hle := sweepSort_monotone L θ hij.le
  have hne : orientedLevel θ (L.point (sweepSort L θ i)) ≠
      orientedLevel θ (L.point (sweepSort L θ j)) :=
    fun h => absurd ((hinj.comp (sweepSort L θ).injective) h) (ne_of_lt hij)
  exact lt_of_le_of_ne hle hne

theorem sweepSort_reindex_add_pi_eq_revPerm {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ₀ : ℝ)
    (hinj : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₀ (L.point a))) :
    sweepSort (L.reindex (sweepSort L θ₀)) (θ₀ + Real.pi) = Fin.revPerm := by
  have key : (fun a => orientedLevel (θ₀ + Real.pi) (L.point ((sweepSort L θ₀) a))) =
      (fun a => -(orientedLevel θ₀ (L.point ((sweepSort L θ₀) a)))) := by
    ext a; exact orientedLevel_add_pi θ₀ (L.point ((sweepSort L θ₀) a))
  show Tuple.sort (fun a => orientedLevel (θ₀ + Real.pi)
    (L.point ((sweepSort L θ₀) a))) = Fin.revPerm
  rw [key]
  exact sort_neg_eq_revPerm (sweepSort_strictMono_of_injective L θ₀ hinj)

theorem sinusoid_at_most_one_zero_in_Ico_pi {a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0)
    {θ₁ θ₂ : ℝ} (hθ₁ : 0 ≤ θ₁) (hθ₁' : θ₁ < Real.pi)
    (hθ₂ : 0 ≤ θ₂) (hθ₂' : θ₂ < Real.pi)
    (h1 : a * Real.sin θ₁ + b * Real.cos θ₁ = 0)
    (h2 : a * Real.sin θ₂ + b * Real.cos θ₂ = 0) :
    θ₁ = θ₂ := by
  by_contra hne
  have hsin : Real.sin (θ₁ - θ₂) = 0 := by
    have hsub : Real.sin θ₁ * Real.cos θ₂ - Real.sin θ₂ * Real.cos θ₁ =
        Real.sin (θ₁ - θ₂) := by rw [Real.sin_sub]; ring
    rcases hab with ha | hb
    · have h3 : a * (Real.sin θ₁ * Real.cos θ₂ - Real.sin θ₂ * Real.cos θ₁) = 0 := by
        linear_combination Real.cos θ₂ * h1 - Real.cos θ₁ * h2
      rw [hsub] at h3
      exact (mul_eq_zero.mp h3).resolve_left ha
    · have h3 : b * (Real.sin θ₁ * Real.cos θ₂ - Real.sin θ₂ * Real.cos θ₁) = 0 := by
        linear_combination -(Real.sin θ₂ * h1 - Real.sin θ₁ * h2)
      rw [hsub] at h3
      exact (mul_eq_zero.mp h3).resolve_left hb
  rw [Real.sin_eq_zero_iff] at hsin
  rcases hsin with ⟨n, hn⟩
  have hbound : |θ₁ - θ₂| < Real.pi := by
    rw [abs_lt]; constructor <;> linarith
  have : n = 0 := by
    by_contra hn0
    have h1le : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    have h1le_r : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast h1le
    have hpi_le : Real.pi ≤ |↑n * Real.pi| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      exact le_mul_of_one_le_left (le_of_lt Real.pi_pos) h1le_r
    linarith [show |↑n * Real.pi| = |θ₁ - θ₂| from by rw [hn]]
  have h0 : (0 : ℝ) = θ₁ - θ₂ := by rw [← hn]; simp [this]
  exact hne (by linarith)

theorem orientedLevel_unique_tie_angle {p q : Point2} (hpq : p ≠ q)
    {θ₁ θ₂ : ℝ} (hθ₁ : 0 ≤ θ₁) (hθ₁' : θ₁ < Real.pi)
    (hθ₂ : 0 ≤ θ₂) (hθ₂' : θ₂ < Real.pi)
    (h1 : orientedLevel θ₁ p = orientedLevel θ₁ q)
    (h2 : orientedLevel θ₂ p = orientedLevel θ₂ q) :
    θ₁ = θ₂ := by
  have hab : -(p.1 - q.1) ≠ 0 ∨ (p.2 - q.2) ≠ 0 := by
    by_contra h; push Not at h
    exact hpq (Prod.ext (by linarith [h.1]) (by linarith [h.2]))
  have heq1 : -(p.1 - q.1) * Real.sin θ₁ + (p.2 - q.2) * Real.cos θ₁ = 0 := by
    have := orientedLevel_sub_eq θ₁ p q; linarith
  have heq2 : -(p.1 - q.1) * Real.sin θ₂ + (p.2 - q.2) * Real.cos θ₂ = 0 := by
    have := orientedLevel_sub_eq θ₂ p q; linarith
  exact sinusoid_at_most_one_zero_in_Ico_pi hab hθ₁ hθ₁' hθ₂ hθ₂' heq1 heq2

theorem sweepSort_eq_of_same_pairwise_order {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) {θ₁ θ₂ : ℝ}
    (hinj₁ : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₁ (L.point a)))
    (hinj₂ : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₂ (L.point a)))
    (hsame : ∀ a b : Fin (2 * k),
      orientedLevel θ₁ (L.point a) < orientedLevel θ₁ (L.point b) →
        orientedLevel θ₂ (L.point a) < orientedLevel θ₂ (L.point b)) :
    sweepSort L θ₁ = sweepSort L θ₂ := by
  suffices h : sweepSort L θ₁ =
      Tuple.sort (fun a => orientedLevel θ₂ (L.point a)) from h
  rw [Tuple.eq_sort_iff]
  refine ⟨?_, ?_⟩
  · intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_refl _
    · exact le_of_lt (hsame _ _ (sweepSort_strictMono_of_injective L θ₁ hinj₁ hlt))
  · intro i j hij heq
    exact absurd ((hinj₂.comp (sweepSort L θ₁).injective) heq) (ne_of_lt hij)

theorem monotone_contiguity {N : ℕ} {g : Fin N → ℝ}
    (hg : Monotone g) {a b c : Fin N} (hab : a ≤ b) (hbc : b ≤ c)
    (hac : g a = g c) : g a = g b := by
  linarith [hg hab, hg hbc]

theorem neg_of_neg_of_continuousOn_of_no_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hfa : f a < 0) (hno_zero : ∀ x ∈ Set.Icc a b, f x ≠ 0) :
    f b < 0 := by
  by_contra hge
  push Not at hge
  have hfb_pos : 0 < f b :=
    lt_of_le_of_ne hge (Ne.symm (hno_zero b (Set.right_mem_Icc.mpr hab)))
  exact hno_zero _ (intermediate_value_Icc hab hcont
    (⟨le_of_lt hfa, le_of_lt hfb_pos⟩ : (0 : ℝ) ∈ Set.Icc (f a) (f b))).choose_spec.1
    (intermediate_value_Icc hab hcont
    (⟨le_of_lt hfa, le_of_lt hfb_pos⟩ : (0 : ℝ) ∈ Set.Icc (f a) (f b))).choose_spec.2

theorem orientedLevel_diff_continuous (p q : Point2) :
    Continuous (fun θ => orientedLevel θ p - orientedLevel θ q) := by
  simp only [orientedLevel]; fun_prop

theorem neg_at_start_of_neg_at_end {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hfb : f b < 0) (hno_zero : ∀ x ∈ Set.Icc a b, f x ≠ 0) :
    f a < 0 := by
  by_contra hge
  push Not at hge
  have hfa_pos : 0 < f a :=
    lt_of_le_of_ne hge (Ne.symm (hno_zero a (Set.left_mem_Icc.mpr hab)))
  exact hno_zero _ (intermediate_value_Icc' hab hcont
    (⟨le_of_lt hfb, le_of_lt hfa_pos⟩ : (0 : ℝ) ∈ Set.Icc (f b) (f a))).choose_spec.1
    (intermediate_value_Icc' hab hcont
    (⟨le_of_lt hfb, le_of_lt hfa_pos⟩ : (0 : ℝ) ∈ Set.Icc (f b) (f a))).choose_spec.2

theorem orientedLevel_order_preserved {p q : Point2}
    {θ₁ θ₂ : ℝ} (h12 : θ₁ ≤ θ₂)
    (hlt : orientedLevel θ₁ p < orientedLevel θ₁ q)
    (hno_tie : ∀ θ ∈ Set.Icc θ₁ θ₂,
      orientedLevel θ p ≠ orientedLevel θ q) :
    orientedLevel θ₂ p < orientedLevel θ₂ q := by
  have hcont := (orientedLevel_diff_continuous p q).continuousOn (s := Set.Icc θ₁ θ₂)
  linarith [neg_of_neg_of_continuousOn_of_no_zero h12 hcont (by linarith : (fun θ =>
    orientedLevel θ p - orientedLevel θ q) θ₁ < 0)
    (fun x hx h => hno_tie x hx (by linarith))]

theorem orientedLevel_order_preserved_backward {p q : Point2}
    {θ₁ θ₂ : ℝ} (h12 : θ₁ ≤ θ₂)
    (hlt : orientedLevel θ₂ p < orientedLevel θ₂ q)
    (hno_tie : ∀ θ ∈ Set.Icc θ₁ θ₂,
      orientedLevel θ p ≠ orientedLevel θ q) :
    orientedLevel θ₁ p < orientedLevel θ₁ q := by
  have hcont := (orientedLevel_diff_continuous p q).continuousOn (s := Set.Icc θ₁ θ₂)
  linarith [neg_at_start_of_neg_at_end h12 hcont (by linarith : (fun θ =>
    orientedLevel θ p - orientedLevel θ q) θ₂ < 0)
    (fun x hx h => hno_tie x hx (by linarith))]

theorem sinusoid_product_formula {a b : ℝ}
    {θ₁ θ₀ θ₂ : ℝ}
    (hzero : a * Real.sin θ₀ + b * Real.cos θ₀ = 0) :
    (a * Real.sin θ₁ + b * Real.cos θ₁) * (a * Real.sin θ₂ + b * Real.cos θ₂) =
      (a ^ 2 + b ^ 2) * Real.sin (θ₁ - θ₀) * Real.sin (θ₂ - θ₀) := by
  have h1 : (a * Real.sin θ₁ + b * Real.cos θ₁) * Real.cos θ₀ =
      a * Real.sin (θ₁ - θ₀) := by
    rw [Real.sin_sub]; linear_combination Real.cos θ₁ * hzero
  have h2 : (a * Real.sin θ₂ + b * Real.cos θ₂) * Real.cos θ₀ =
      a * Real.sin (θ₂ - θ₀) := by
    rw [Real.sin_sub]; linear_combination Real.cos θ₂ * hzero
  have h3 : (a * Real.sin θ₁ + b * Real.cos θ₁) * Real.sin θ₀ =
      -(b * Real.sin (θ₁ - θ₀)) := by
    rw [Real.sin_sub]; linear_combination Real.sin θ₁ * hzero
  have h4 : (a * Real.sin θ₂ + b * Real.cos θ₂) * Real.sin θ₀ =
      -(b * Real.sin (θ₂ - θ₀)) := by
    rw [Real.sin_sub]; linear_combination Real.sin θ₂ * hzero
  set d₁ := a * Real.sin θ₁ + b * Real.cos θ₁
  set d₂ := a * Real.sin θ₂ + b * Real.cos θ₂
  set s₁ := Real.sin (θ₁ - θ₀)
  set s₂ := Real.sin (θ₂ - θ₀)
  have h12 : d₁ * d₂ * Real.cos θ₀ ^ 2 = a ^ 2 * s₁ * s₂ := by
    calc d₁ * d₂ * Real.cos θ₀ ^ 2
        = (d₁ * Real.cos θ₀) * (d₂ * Real.cos θ₀) := by ring
      _ = (a * s₁) * (a * s₂) := by rw [h1, h2]
      _ = a ^ 2 * s₁ * s₂ := by ring
  have h34 : d₁ * d₂ * Real.sin θ₀ ^ 2 = b ^ 2 * s₁ * s₂ := by
    calc d₁ * d₂ * Real.sin θ₀ ^ 2
        = (d₁ * Real.sin θ₀) * (d₂ * Real.sin θ₀) := by ring
      _ = (-(b * s₁)) * (-(b * s₂)) := by rw [h3, h4]
      _ = b ^ 2 * s₁ * s₂ := by ring
  calc d₁ * d₂
      = d₁ * d₂ * 1 := by ring
    _ = d₁ * d₂ * (Real.sin θ₀ ^ 2 + Real.cos θ₀ ^ 2) := by
        rw [Real.sin_sq_add_cos_sq]
    _ = d₁ * d₂ * Real.sin θ₀ ^ 2 + d₁ * d₂ * Real.cos θ₀ ^ 2 := by ring
    _ = b ^ 2 * s₁ * s₂ + a ^ 2 * s₁ * s₂ := by linarith
    _ = (a ^ 2 + b ^ 2) * s₁ * s₂ := by ring

theorem sinusoid_sign_change_at_zero {a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0)
    {θ₁ θ₀ θ₂ : ℝ}
    (h10 : θ₁ < θ₀) (h02 : θ₀ < θ₂) (h_span : θ₂ - θ₁ < Real.pi)
    (hzero : a * Real.sin θ₀ + b * Real.cos θ₀ = 0)
    (hneg : a * Real.sin θ₁ + b * Real.cos θ₁ < 0) :
    0 < a * Real.sin θ₂ + b * Real.cos θ₂ := by
  have hab2 : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · positivity
    · positivity
  have hsin1 : Real.sin (θ₁ - θ₀) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  have hsin2 : 0 < Real.sin (θ₂ - θ₀) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hprod := sinusoid_product_formula hzero (θ₁ := θ₁) (θ₂ := θ₂)
  by_contra hge
  push Not at hge
  have hprod_neg : (a ^ 2 + b ^ 2) * Real.sin (θ₁ - θ₀) * Real.sin (θ₂ - θ₀) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hab2 hsin1) hsin2
  linarith [mul_nonneg (le_of_lt (neg_pos.mpr hneg)) (neg_nonneg.mpr hge),
            show -(a * Real.sin θ₁ + b * Real.cos θ₁) *
              -(a * Real.sin θ₂ + b * Real.cos θ₂) =
              (a * Real.sin θ₁ + b * Real.cos θ₁) *
              (a * Real.sin θ₂ + b * Real.cos θ₂) from by ring]

theorem orientedLevel_order_reversed_at_event {p q : Point2} (hpq : p ≠ q)
    {θ₁ θ_e θ₂ : ℝ} (h1e : θ₁ < θ_e) (he2 : θ_e < θ₂)
    (h_span : θ₂ - θ₁ < Real.pi)
    (hlt : orientedLevel θ₁ p < orientedLevel θ₁ q)
    (htie : orientedLevel θ_e p = orientedLevel θ_e q)
    (hne2 : orientedLevel θ₂ p ≠ orientedLevel θ₂ q) :
    orientedLevel θ₂ q < orientedLevel θ₂ p := by
  have hab : -(p.1 - q.1) ≠ 0 ∨ (p.2 - q.2) ≠ 0 := by
    by_contra h; push Not at h
    exact hpq (Prod.ext (by linarith [h.1]) (by linarith [h.2]))
  have heq_e : -(p.1 - q.1) * Real.sin θ_e + (p.2 - q.2) * Real.cos θ_e = 0 := by
    have := orientedLevel_sub_eq θ_e p q; linarith
  have hneg : -(p.1 - q.1) * Real.sin θ₁ + (p.2 - q.2) * Real.cos θ₁ < 0 := by
    have := orientedLevel_sub_eq θ₁ p q; linarith
  have hpos := sinusoid_sign_change_at_zero hab h1e he2 h_span heq_e hneg
  have hsub := orientedLevel_sub_eq θ₂ p q
  linarith

theorem orientedLevel_order_preserved_across_event {p q : Point2} (hpq : p ≠ q)
    {θ₁ θ_e θ₂ : ℝ}
    (hθ₁ : 0 ≤ θ₁) (hθ₂ : θ₂ < Real.pi)
    (h1e : θ₁ < θ_e) (he2 : θ_e < θ₂)
    (hlt : orientedLevel θ₁ p < orientedLevel θ₁ q)
    (hno_tie_at_event : orientedLevel θ_e p ≠ orientedLevel θ_e q)
    (hno_tie_between : ∀ θ ∈ Set.Icc θ₁ θ₂,
      θ ≠ θ_e → orientedLevel θ p ≠ orientedLevel θ q) :
    orientedLevel θ₂ p < orientedLevel θ₂ q := by
  apply orientedLevel_order_preserved (le_of_lt (lt_trans h1e he2)) hlt
  intro θ hθ
  rcases eq_or_ne θ θ_e with rfl | hne
  · exact hno_tie_at_event
  · exact hno_tie_between θ hθ hne

theorem sweepSort_eq_of_strictMono {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) {θ : ℝ}
    (σ : Equiv.Perm (Fin (2 * k)))
    (hstrict : StrictMono (fun i => orientedLevel θ (L.point (σ i)))) :
    sweepSort L θ = σ := by
  show Tuple.sort (fun a => orientedLevel θ (L.point a)) = σ
  symm; rw [Tuple.eq_sort_iff]
  exact ⟨hstrict.monotone, fun i j hij heq =>
    absurd heq (ne_of_lt (hstrict hij))⟩

/-! ### Level-block extraction from monotone functions -/

noncomputable def levelBlockLo {N : ℕ} (f : Fin N → ℝ) (i : Fin N) : Fin N :=
  (Finset.univ.filter (fun j : Fin N => f j = f i ∧ j ≤ i)).min'
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, le_refl _⟩⟩

noncomputable def levelBlockHi {N : ℕ} (f : Fin N → ℝ) (i : Fin N) : Fin N :=
  (Finset.univ.filter (fun j : Fin N => f j = f i ∧ i ≤ j)).max'
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, le_refl _⟩⟩

private theorem levelBlockLo_mem {N : ℕ} {f : Fin N → ℝ} {i : Fin N} :
    f (levelBlockLo f i) = f i ∧ levelBlockLo f i ≤ i := by
  have h := Finset.min'_mem (Finset.univ.filter (fun j : Fin N => f j = f i ∧ j ≤ i))
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, le_refl _⟩⟩
  exact (Finset.mem_filter.mp h).2

theorem levelBlockLo_le {N : ℕ} {f : Fin N → ℝ} {i : Fin N} :
    levelBlockLo f i ≤ i := levelBlockLo_mem.2

theorem levelBlockLo_val {N : ℕ} {f : Fin N → ℝ} {i : Fin N} :
    f (levelBlockLo f i) = f i := levelBlockLo_mem.1

private theorem levelBlockHi_mem {N : ℕ} {f : Fin N → ℝ} {i : Fin N} :
    f (levelBlockHi f i) = f i ∧ i ≤ levelBlockHi f i := by
  have h := Finset.max'_mem (Finset.univ.filter (fun j : Fin N => f j = f i ∧ i ≤ j))
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, le_refl _⟩⟩
  exact (Finset.mem_filter.mp h).2

theorem levelBlockHi_ge {N : ℕ} {f : Fin N → ℝ} {i : Fin N} :
    i ≤ levelBlockHi f i := levelBlockHi_mem.2

theorem levelBlockHi_val {N : ℕ} {f : Fin N → ℝ} {i : Fin N} :
    f (levelBlockHi f i) = f i := levelBlockHi_mem.1

theorem monotone_levelBlock_eq {N : ℕ} {f : Fin N → ℝ} (hf : Monotone f)
    {i j : Fin N} (hij : levelBlockLo f i ≤ j) (hji : j ≤ levelBlockHi f i) :
    f j = f i := by
  linarith [monotone_contiguity hf hij hji
    (levelBlockLo_val (i := i) |>.trans (levelBlockHi_val (i := i) |>.symm)),
    levelBlockLo_val (f := f) (i := i)]

noncomputable def levelBlockMirror {N : ℕ} (f : Fin N → ℝ) (p : Fin N) : Fin N :=
  ⟨(levelBlockLo f p).val + (levelBlockHi f p).val - p.val, by
    have hlo := levelBlockLo_le (f := f) (i := p)
    have hhi := levelBlockHi_ge (f := f) (i := p)
    omega⟩

theorem levelBlockMirror_mem_block {N : ℕ} {f : Fin N → ℝ} (p : Fin N) :
    (levelBlockLo f p).val ≤ (levelBlockMirror f p).val ∧
      (levelBlockMirror f p).val ≤ (levelBlockHi f p).val := by
  simp [levelBlockMirror]
  have hlo := levelBlockLo_le (f := f) (i := p)
  have hhi := levelBlockHi_ge (f := f) (i := p)
  exact ⟨by omega, by omega⟩

theorem levelBlockMirror_val {N : ℕ} {f : Fin N → ℝ} (hf : Monotone f) (p : Fin N) :
    f (levelBlockMirror f p) = f p := by
  apply monotone_levelBlock_eq hf
  · exact Fin.le_def.mpr (levelBlockMirror_mem_block p).1
  · exact Fin.le_def.mpr (levelBlockMirror_mem_block p).2

theorem sweepSort_event_level_monotone {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) {θ₁ θ_e : ℝ}
    (hinj : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₁ (L.point a)))
    (h1e : θ₁ ≤ θ_e)
    (hno_tie_before : ∀ a b : Fin (2 * k), a ≠ b →
      ∀ θ ∈ Set.Ioo θ₁ θ_e, orientedLevel θ (L.point a) ≠ orientedLevel θ (L.point b)) :
    Monotone (fun i => orientedLevel θ_e (L.point (sweepSort L θ₁ i))) := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · have hstrict := sweepSort_strictMono_of_injective L θ₁ hinj hlt
    by_cases heq : orientedLevel θ_e (L.point (sweepSort L θ₁ i)) =
        orientedLevel θ_e (L.point (sweepSort L θ₁ j))
    · exact le_of_eq heq
    · apply le_of_lt
      apply orientedLevel_order_preserved h1e hstrict
      intro θ hθ
      rcases eq_or_lt_of_le hθ.1 with rfl | h_lt₁
      · exact fun h => absurd h (ne_of_lt hstrict)
      · rcases eq_or_lt_of_le hθ.2 with rfl | h_lt_e
        · exact heq
        · exact hno_tie_before _ _ (fun h =>
            ne_of_lt hlt ((sweepSort L θ₁).injective h)) θ ⟨h_lt₁, h_lt_e⟩

theorem levelBlockMirror_reverses_within_block {N : ℕ} {f : Fin N → ℝ}
    (hf : Monotone f) {i j : Fin N} (hij : i < j) (hfij : f i = f j) :
    levelBlockMirror f j < levelBlockMirror f i := by
  simp [levelBlockMirror]
  have hlo_i := levelBlockLo_le (f := f) (i := i)
  have hhi_i := levelBlockHi_ge (f := f) (i := i)
  have hlo_j := levelBlockLo_le (f := f) (i := j)
  have hhi_j := levelBlockHi_ge (f := f) (i := j)
  have h_i_in_j_lo : i ∈ Finset.univ.filter (fun k : Fin N => f k = f j ∧ k ≤ j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfij, le_of_lt hij⟩
  have h_j_in_i_hi : j ∈ Finset.univ.filter (fun k : Fin N => f k = f i ∧ i ≤ k) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfij.symm, le_of_lt hij⟩
  have hlo_j_le_i : levelBlockLo f j ≤ i :=
    Finset.min'_le _ _ h_i_in_j_lo
  have hlo_eq : levelBlockLo f i = levelBlockLo f j := by
    apply le_antisymm
    · apply Finset.min'_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (levelBlockLo_val (i := j)).trans hfij.symm, hlo_j_le_i⟩
    · apply Finset.min'_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (levelBlockLo_val (i := i)).trans hfij,
        (levelBlockLo_le (i := i)).trans (le_of_lt hij)⟩
  have hhi_i_ge_j : j ≤ levelBlockHi f i :=
    Finset.le_max' _ _ h_j_in_i_hi
  have hhi_eq : levelBlockHi f i = levelBlockHi f j := by
    apply le_antisymm
    · apply Finset.le_max'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (levelBlockHi_val (i := i)).trans hfij,
        hhi_i_ge_j⟩
    · apply Finset.le_max'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (levelBlockHi_val (i := j)).trans hfij.symm,
        (le_of_lt hij).trans (levelBlockHi_ge (i := j))⟩
  omega

theorem levelBlockMirror_preserves_across_blocks {N : ℕ} {f : Fin N → ℝ}
    (hf : Monotone f) {i j : Fin N} (hij : i < j) (hfij : f i < f j) :
    levelBlockMirror f i < levelBlockMirror f j := by
  have hlo_i := levelBlockLo_le (f := f) (i := i)
  have hhi_i := levelBlockHi_ge (f := f) (i := i)
  have hlo_j := levelBlockLo_le (f := f) (i := j)
  have hhi_j := levelBlockHi_ge (f := f) (i := j)
  have hhi_lt_lo : levelBlockHi f i < levelBlockLo f j := by
    by_contra h
    push Not at h
    linarith [hf h, levelBlockLo_val (f := f) (i := j),
              levelBlockHi_val (f := f) (i := i)]
  simp only [levelBlockMirror, Fin.lt_def, Fin.val_mk]
  omega

theorem levelBlockLo_of_mem_block {N : ℕ} {f : Fin N → ℝ}
    {i j : Fin N} (hfij : f j = f i)
    (hlo : (levelBlockLo f i).val ≤ j.val) :
    levelBlockLo f j = levelBlockLo f i := by
  have h1 : levelBlockLo f j ≤ levelBlockLo f i :=
    Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (levelBlockLo_val (i := i)).trans hfij.symm, Fin.le_def.mpr hlo⟩)
  have h2 : levelBlockLo f i ≤ levelBlockLo f j :=
    Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (levelBlockLo_val (i := j)).trans hfij,
      h1.trans levelBlockLo_le⟩)
  exact le_antisymm h1 h2

theorem levelBlockHi_of_mem_block {N : ℕ} {f : Fin N → ℝ}
    {i j : Fin N} (hfij : f j = f i)
    (hhi : j.val ≤ (levelBlockHi f i).val) :
    levelBlockHi f j = levelBlockHi f i := by
  have h1 : levelBlockHi f i ≤ levelBlockHi f j :=
    Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (levelBlockHi_val (i := i)).trans hfij.symm, Fin.le_def.mpr hhi⟩)
  have h2 : levelBlockHi f j ≤ levelBlockHi f i :=
    Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (levelBlockHi_val (i := j)).trans hfij,
      levelBlockHi_ge.trans h1⟩)
  exact le_antisymm h2 h1

theorem levelBlockMirror_involutive {N : ℕ} {f : Fin N → ℝ} (hf : Monotone f)
    (p : Fin N) : levelBlockMirror f (levelBlockMirror f p) = p := by
  have hmem := levelBlockMirror_mem_block (f := f) p
  have hval := levelBlockMirror_val hf p
  have hlo_eq := levelBlockLo_of_mem_block hval hmem.1
  have hhi_eq := levelBlockHi_of_mem_block hval hmem.2
  have hlo_v := congrArg Fin.val hlo_eq
  have hhi_v := congrArg Fin.val hhi_eq
  apply Fin.ext
  show (levelBlockLo f (levelBlockMirror f p)).val +
    (levelBlockHi f (levelBlockMirror f p)).val -
    (levelBlockMirror f p).val = p.val
  rw [hlo_v, hhi_v]; simp [levelBlockMirror]
  have := (Fin.le_def.mp (levelBlockLo_le (f := f) (i := p)))
  have := (Fin.le_def.mp (levelBlockHi_ge (f := f) (i := p)))
  omega

noncomputable def levelBlockMirrorPerm {N : ℕ} (f : Fin N → ℝ) (hf : Monotone f) :
    Equiv.Perm (Fin N) where
  toFun := levelBlockMirror f
  invFun := levelBlockMirror f
  left_inv := levelBlockMirror_involutive hf
  right_inv := levelBlockMirror_involutive hf

theorem sweepSort_event_compose {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k)
    {θ₁ θ_e θ₂ : ℝ}
    (hinj₁ : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₁ (L.point a)))
    (hinj₂ : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₂ (L.point a)))
    (h1e : θ₁ < θ_e) (he2 : θ_e < θ₂) (h_span : θ₂ - θ₁ < Real.pi)
    (honly_event : ∀ a b : Fin (2 * k), L.point a ≠ L.point b →
      ∀ θ ∈ Set.Icc θ₁ θ₂, θ ≠ θ_e →
        orientedLevel θ (L.point a) ≠ orientedLevel θ (L.point b))
    (hg_mono : Monotone (fun i => orientedLevel θ_e (L.point (sweepSort L θ₁ i)))) :
    sweepSort L θ₂ =
      (levelBlockMirrorPerm (fun i => orientedLevel θ_e (L.point (sweepSort L θ₁ i))) hg_mono).trans
        (sweepSort L θ₁) := by
  set σ₁ := sweepSort L θ₁
  set g : Fin (2 * k) → ℝ := fun i => orientedLevel θ_e (L.point (σ₁ i))
  apply sweepSort_eq_of_strictMono
  intro i j hij
  show orientedLevel θ₂ (L.point (σ₁ (levelBlockMirror g i))) <
    orientedLevel θ₂ (L.point (σ₁ (levelBlockMirror g j)))
  by_cases hcase : g i = g j
  · -- Same block: mirror reverses, then event reverses back
    have hm := levelBlockMirror_reverses_within_block hg_mono hij hcase
    have hord := sweepSort_strictMono_of_injective L θ₁ hinj₁ hm
    have hne : L.point (σ₁ (levelBlockMirror g j)) ≠ L.point (σ₁ (levelBlockMirror g i)) :=
      fun h => ne_of_lt hord (congr_arg (orientedLevel θ₁) h)
    have htie : orientedLevel θ_e (L.point (σ₁ (levelBlockMirror g j))) =
        orientedLevel θ_e (L.point (σ₁ (levelBlockMirror g i))) := by
      show g (levelBlockMirror g j) = g (levelBlockMirror g i)
      simp only [levelBlockMirror_val hg_mono, hcase]
    have hne₂ : orientedLevel θ₂ (L.point (σ₁ (levelBlockMirror g j))) ≠
        orientedLevel θ₂ (L.point (σ₁ (levelBlockMirror g i))) :=
      fun h => ne_of_lt hm (σ₁.injective (hinj₂ h))
    exact orientedLevel_order_reversed_at_event hne h1e he2 h_span hord htie hne₂
  · -- Different blocks: mirror preserves, event preserves
    have hlt : g i < g j := lt_of_le_of_ne (hg_mono hij.le) hcase
    have hm := levelBlockMirror_preserves_across_blocks hg_mono hij hlt
    have hord := sweepSort_strictMono_of_injective L θ₁ hinj₁ hm
    have hne : L.point (σ₁ (levelBlockMirror g i)) ≠ L.point (σ₁ (levelBlockMirror g j)) :=
      fun h => ne_of_lt hord (congr_arg (orientedLevel θ₁) h)
    apply orientedLevel_order_preserved (le_of_lt (lt_trans h1e he2)) hord
    intro θ hθ
    rcases eq_or_ne θ θ_e with rfl | hne_θ
    · exact fun h => ne_of_lt hlt (by
        have h1 := levelBlockMirror_val hg_mono (f := g) (p := i)
        have h2 := levelBlockMirror_val hg_mono (f := g) (p := j)
        change g (levelBlockMirror g i) = g (levelBlockMirror g j) at h
        linarith)
    · exact honly_event _ _ hne θ hθ hne_θ

theorem label_index_lt_of_orientedLevel_lt {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ₀ : ℝ)
    (hid : sweepSort L θ₀ = Equiv.refl _)
    {a b : Fin (2 * k)}
    (h : orientedLevel θ₀ (L.point a) < orientedLevel θ₀ (L.point b)) :
    a.val < b.val := by
  by_contra hge
  push Not at hge
  linarith [(show Monotone (fun a => orientedLevel θ₀ (L.point a)) from
    Tuple.sort_eq_refl_iff_monotone.mp hid) (Fin.le_def.mpr hge)]

theorem sweepSort_increasing_within_block {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) {θ₀ θ_j θ_ej : ℝ}
    (hid : sweepSort L θ₀ = Equiv.refl _)
    (hinj₀ : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₀ (L.point a)))
    (hinj_j : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ_j (L.point a)))
    (hθ₀ : 0 ≤ θ₀) (hθ_ej : θ_ej < Real.pi)
    (h0j : θ₀ ≤ θ_j) (hj_ej : θ_j < θ_ej)
    (hno_tie : ∀ a b : Fin (2 * k), L.point a ≠ L.point b →
      orientedLevel θ_ej (L.point a) = orientedLevel θ_ej (L.point b) →
        ∀ θ ∈ Set.Icc θ₀ θ_j, orientedLevel θ (L.point a) ≠ orientedLevel θ (L.point b))
    {p q : Fin (2 * k)} (hpq : p < q)
    (htie : orientedLevel θ_ej (L.point (sweepSort L θ_j p)) =
      orientedLevel θ_ej (L.point (sweepSort L θ_j q))) :
    (sweepSort L θ_j p).val < (sweepSort L θ_j q).val := by
  let σ := sweepSort L θ_j
  have hstrict := sweepSort_strictMono_of_injective L θ_j hinj_j hpq
  have hne : L.point (σ p) ≠ L.point (σ q) :=
    fun h => ne_of_lt hstrict (congr_arg (orientedLevel θ_j) h)
  have hord₀ := orientedLevel_order_preserved_backward h0j hstrict
    (fun θ hθ => hno_tie (σ p) (σ q) hne htie θ hθ)
  exact label_index_lt_of_orientedLevel_lt L θ₀ hid hord₀

noncomputable def blockStarts {N : ℕ} (g : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun p =>
    p = levelBlockLo g p ∧ (levelBlockLo g p).val < (levelBlockHi g p).val)

theorem blockStarts_nonempty_of_tie {N : ℕ} {g : Fin N → ℝ} (hg : Monotone g)
    {i j : Fin N} (hij : i < j) (hgij : g i = g j) :
    (blockStarts g).Nonempty := by
  have hlo_idem : levelBlockLo g (levelBlockLo g i) = levelBlockLo g i := by
    apply levelBlockLo_of_mem_block
    · exact levelBlockLo_val
    · exact le_refl _
  have h_j_in : j.val ≤ (levelBlockHi g i).val :=
    Fin.le_def.mp (Finset.le_max' _ _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hgij.symm, le_of_lt hij⟩))
  refine ⟨levelBlockLo g i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlo_idem.symm, ?_⟩⟩
  have h_lo := (Fin.le_def.mp (levelBlockLo_le (f := g) (i := i)))
  rw [hlo_idem]
  have hhi_eq : levelBlockHi g (levelBlockLo g i) = levelBlockHi g i := by
    apply levelBlockHi_of_mem_block
    · exact levelBlockLo_val
    · exact Fin.le_def.mp (levelBlockLo_le.trans levelBlockHi_ge)
  rw [hhi_eq]; omega

theorem left_ne_right_of_noncollinear {p q r : Point2}
    (h : NoncollinearTriple p q r) : p ≠ q := by
  intro hpq
  subst q
  exact h (by ring)

theorem left_ne_third_of_noncollinear {p q r : Point2}
    (h : NoncollinearTriple p q r) : p ≠ r := by
  intro hpr
  subst r
  exact h (by ring)

theorem determinant_eq_zero_of_same_direction_from_left {p q r : Point2}
    (hdir : direction p q = direction p r) :
    (q.2 - p.2) * (r.1 - p.1) = (r.2 - p.2) * (q.1 - p.1) := by
  classical
  by_cases hxq : p.1 = q.1
  · by_cases hxr : p.1 = r.1
    · have hqzero : q.1 - p.1 = 0 := by rw [← hxq, sub_self]
      have hrzero : r.1 - p.1 = 0 := by rw [← hxr, sub_self]
      rw [hqzero, hrzero, mul_zero, mul_zero]
    · simp [direction, hxq] at hdir
      exact False.elim (hxr (hxq.trans hdir))
  · by_cases hxr : p.1 = r.1
    · simp [direction, hxr] at hdir
      exact False.elim (hxq (hxr.trans hdir))
    · have hslope : slope p q = slope p r := by
        simpa [direction, hxq, hxr] using hdir
      have hqden : q.1 - p.1 ≠ 0 := by
        exact sub_ne_zero.mpr (Ne.symm hxq)
      have hrden : r.1 - p.1 ≠ 0 := by
        exact sub_ne_zero.mpr (Ne.symm hxr)
      unfold slope at hslope
      field_simp [hqden, hrden] at hslope
      linarith

theorem directionLevel_eq_of_direction_eq {p q : Point2} {d : Direction}
    (hdir : direction p q = d) :
    directionLevel d p = directionLevel d q := by
  cases d with
  | vertical =>
      by_cases hx : p.1 = q.1
      · simp [directionLevel, hx]
      · simp [direction, hx] at hdir
  | finite m =>
      by_cases hx : p.1 = q.1
      · simp [direction, hx] at hdir
      · have hslope : slope p q = m := by
          simpa [direction, hx] using hdir
        have hden : q.1 - p.1 ≠ 0 := by
          exact sub_ne_zero.mpr (Ne.symm hx)
        unfold slope at hslope
        field_simp [hden] at hslope
        simp [directionLevel]
        linarith

theorem direction_eq_of_directionLevel_eq {p q : Point2} {d : Direction}
    (hpq : p ≠ q) (hlevel : directionLevel d p = directionLevel d q) :
    direction p q = d := by
  cases d with
  | vertical =>
      simp [directionLevel] at hlevel
      simp [direction, hlevel]
  | finite m =>
      simp [directionLevel] at hlevel
      by_cases hx : p.1 = q.1
      · have hy : p.2 = q.2 := by
          rw [hx] at hlevel
          linarith
        exact False.elim (hpq (Prod.ext hx hy))
      · have hden : q.1 - p.1 ≠ 0 := by
          exact sub_ne_zero.mpr (Ne.symm hx)
        simp [direction, hx, slope]
        field_simp [hden]
        linarith

theorem directionLevel_eq_iff_direction_eq {p q : Point2} {d : Direction}
    (hpq : p ≠ q) :
    directionLevel d p = directionLevel d q ↔ direction p q = d := by
  constructor
  · exact direction_eq_of_directionLevel_eq hpq
  · exact directionLevel_eq_of_direction_eq

theorem orientedLevel_eq_iff_direction_finite {p q : Point2} (hpq : p ≠ q)
    {θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    orientedLevel θ p = orientedLevel θ q ↔
      direction p q = Direction.finite (Real.tan θ) := by
  rw [orientedLevel_eq_cos_mul_directionLevel hcos p,
      orientedLevel_eq_cos_mul_directionLevel hcos q]
  constructor
  · intro h
    exact direction_eq_of_directionLevel_eq hpq (mul_left_cancel₀ hcos h)
  · intro h
    congr 1; exact directionLevel_eq_of_direction_eq h

theorem direction_mem_directionsDeterminedBy {points : Finset Point2} {p q : Point2}
    (hp : p ∈ points) (hq : q ∈ points) (hpq : p ≠ q) :
    direction p q ∈ directionsDeterminedBy points := by
  exact Finset.mem_image.mpr ⟨(p, q), by simp [hp, hq, hpq], rfl⟩

theorem mem_directionsDeterminedBy_iff_exists_equal_level {points : Finset Point2}
    {d : Direction} :
    d ∈ directionsDeterminedBy points ↔
      ∃ p ∈ points, ∃ q ∈ points, p ≠ q ∧
        directionLevel d p = directionLevel d q := by
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨pq, hpq_mem, hpq_dir⟩
    rcases pq with ⟨p, q⟩
    rcases Finset.mem_filter.mp hpq_mem with ⟨hpq_prod, hpq_ne⟩
    rcases Finset.mem_product.mp hpq_prod with ⟨hp, hq⟩
    exact ⟨p, hp, q, hq, hpq_ne, directionLevel_eq_of_direction_eq hpq_dir⟩
  · rintro ⟨p, hp, q, hq, hpq_ne, hlevel⟩
    have hdir : direction p q = d :=
      direction_eq_of_directionLevel_eq hpq_ne hlevel
    rw [← hdir]
    exact direction_mem_directionsDeterminedBy hp hq hpq_ne

theorem PointLabeling.direction_mem {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) {a b : Fin (2 * k)}
    (hab : a ≠ b) :
    direction (L.point a) (L.point b) ∈ directionsDeterminedBy points := by
  exact direction_mem_directionsDeterminedBy (L.mem_point a) (L.mem_point b)
    (fun hp => hab (L.point_injective hp))

theorem DirectionLabeling.exists_dir_eq_labeled_pair {points : Finset Point2} {k : ℕ}
    (D : DirectionLabeling points) (L : PointLabeling points k)
    {a b : Fin (2 * k)} (hab : a ≠ b) :
    ∃ j, D.dir j = direction (L.point a) (L.point b) := by
  rcases D.dir_surjective_on (direction (L.point a) (L.point b))
      (L.direction_mem hab) with ⟨j, hj⟩
  exact ⟨j, hj⟩

theorem directionLevel_ne_of_not_mem_directions {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) {d : Direction}
    (hd : d ∉ directionsDeterminedBy points) {a b : Fin (2 * k)}
    (hab : a ≠ b) :
    directionLevel d (L.point a) ≠ directionLevel d (L.point b) := by
  intro hlevel
  have hdir : direction (L.point a) (L.point b) = d :=
    direction_eq_of_directionLevel_eq
      (by
        intro hpoint
        exact hab (L.point_injective hpoint))
      hlevel
  exact hd (by
    rw [← hdir]
    exact L.direction_mem hab)

theorem mem_directionsDeterminedBy_iff_exists_labeled_equal_level
    {points : Finset Point2} {k : ℕ} (L : PointLabeling points k)
    {d : Direction} :
    d ∈ directionsDeterminedBy points ↔
      ∃ a b : Fin (2 * k), a ≠ b ∧
        directionLevel d (L.point a) = directionLevel d (L.point b) := by
  constructor
  · intro hd
    rcases mem_directionsDeterminedBy_iff_exists_equal_level.mp hd with
      ⟨p, hp, q, hq, hpq, hlevel⟩
    rcases L.point_surjective_on p hp with ⟨a, ha⟩
    rcases L.point_surjective_on q hq with ⟨b, hb⟩
    refine ⟨a, b, ?_, ?_⟩
    · intro hab
      exact hpq (by rw [← ha, ← hb, hab])
    · rw [ha, hb]
      exact hlevel
  · rintro ⟨a, b, hab, hlevel⟩
    exact mem_directionsDeterminedBy_iff_exists_equal_level.mpr
      ⟨L.point a, L.mem_point a, L.point b, L.mem_point b,
        (by
          intro hpoint
          exact hab (L.point_injective hpoint)),
        hlevel⟩

namespace DirectionLabeling

noncomputable def tieLabelPair {points : Finset Point2} {k : ℕ}
    (D : DirectionLabeling points) (L : PointLabeling points k)
    (j : Fin (directionsDeterminedBy points).card) :
    {ab : Fin (2 * k) × Fin (2 * k) //
      ab.1 ≠ ab.2 ∧
        directionLevel (D.dir j) (L.point ab.1) =
          directionLevel (D.dir j) (L.point ab.2)} := by
  classical
  let h :=
    (mem_directionsDeterminedBy_iff_exists_labeled_equal_level L).mp
      (D.mem_dir j)
  let a := Classical.choose h
  let hb := Classical.choose_spec h
  let b := Classical.choose hb
  let hspec := Classical.choose_spec hb
  exact ⟨(a, b), hspec.1, hspec.2⟩

theorem tieLabelPair_ne {points : Finset Point2} {k : ℕ}
    (D : DirectionLabeling points) (L : PointLabeling points k)
    (j : Fin (directionsDeterminedBy points).card) :
    (D.tieLabelPair L j).1.1 ≠ (D.tieLabelPair L j).1.2 :=
  (D.tieLabelPair L j).2.1

theorem tieLabelPair_level_eq {points : Finset Point2} {k : ℕ}
    (D : DirectionLabeling points) (L : PointLabeling points k)
    (j : Fin (directionsDeterminedBy points).card) :
    directionLevel (D.dir j) (L.point (D.tieLabelPair L j).1.1) =
      directionLevel (D.dir j) (L.point (D.tieLabelPair L j).1.2) :=
  (D.tieLabelPair L j).2.2

end DirectionLabeling

theorem directions_from_noncollinear_triple_ne {p q r : Point2}
    (hnon : NoncollinearTriple p q r) :
    direction p q ≠ direction p r := by
  intro hdir
  exact hnon (determinant_eq_zero_of_same_direction_from_left hdir)

theorem not_all_pair_directions_eq_of_noncollinearSet {points : Finset Point2}
    (hncoll : NoncollinearSet points) :
    ¬ ∃ d : Direction,
      ∀ p ∈ points, ∀ q ∈ points, p ≠ q → direction p q = d := by
  rintro ⟨d, hall⟩
  rcases hncoll with ⟨p, hp, q, hq, r, hr, hnon⟩
  have hpq : p ≠ q := left_ne_right_of_noncollinear hnon
  have hpr : p ≠ r := left_ne_third_of_noncollinear hnon
  have hdir_pq : direction p q = d := hall p hp q hq hpq
  have hdir_pr : direction p r = d := hall p hp r hr hpr
  exact directions_from_noncollinear_triple_ne hnon (hdir_pq.trans hdir_pr.symm)

theorem not_all_directionLevels_eq_of_noncollinearSet {points : Finset Point2}
    (hncoll : NoncollinearSet points) (d : Direction) :
    ¬ ∃ c : ℝ, ∀ p ∈ points, directionLevel d p = c := by
  rintro ⟨c, hall⟩
  exact not_all_pair_directions_eq_of_noncollinearSet hncoll
    ⟨d, by
      intro p hp q hq hpq
      exact direction_eq_of_directionLevel_eq hpq
        ((hall p hp).trans (hall q hq).symm)⟩

theorem slopesDeterminedBy_mono {A B : Finset Point2} (hAB : A ⊆ B) :
    slopesDeterminedBy A ⊆ slopesDeterminedBy B := by
  classical
  intro m hm
  rcases Finset.mem_image.mp hm with ⟨pq, hpq_mem, hpq_slope⟩
  rcases pq with ⟨p, q⟩
  rcases Finset.mem_filter.mp hpq_mem with ⟨hpq_prod, hpq_cond⟩
  rcases Finset.mem_product.mp hpq_prod with ⟨hpA, hqA⟩
  refine Finset.mem_image.mpr ⟨(p, q), ?_, hpq_slope⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hAB hpA, hAB hqA⟩, hpq_cond⟩

theorem directionsDeterminedBy_mono {A B : Finset Point2} (hAB : A ⊆ B) :
    directionsDeterminedBy A ⊆ directionsDeterminedBy B := by
  classical
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨pq, hpq_mem, hpq_dir⟩
  rcases pq with ⟨p, q⟩
  rcases Finset.mem_filter.mp hpq_mem with ⟨hpq_prod, hpq_ne⟩
  rcases Finset.mem_product.mp hpq_prod with ⟨hpA, hqA⟩
  refine Finset.mem_image.mpr ⟨(p, q), ?_, hpq_dir⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hAB hpA, hAB hqA⟩, hpq_ne⟩

theorem noncollinearSet_mono {A B : Finset Point2} (hAB : A ⊆ B)
    (hA : NoncollinearSet A) : NoncollinearSet B := by
  rcases hA with ⟨p, hp, q, hq, r, hr, hnon⟩
  exact ⟨p, hAB hp, q, hAB hq, r, hAB hr, hnon⟩

theorem exists_erase_noncollinear {points : Finset Point2}
    (hcard : 3 < points.card) (hncoll : NoncollinearSet points) :
    ∃ x ∈ points, NoncollinearSet (points.erase x) := by
  classical
  rcases hncoll with ⟨p, hp, q, hq, r, hr, hnon⟩
  let T : Finset Point2 := {p, q, r}
  have hexists : ∃ x ∈ points, x ∉ T := by
    by_contra hnot
    push Not at hnot
    have hsub : points ⊆ T := by
      intro x hx
      exact hnot x hx
    have hle : points.card ≤ T.card := Finset.card_le_card hsub
    have hT : T.card ≤ 3 := by
      dsimp [T]
      exact Finset.card_le_three
    omega
  rcases hexists with ⟨x, hxpoints, hxnotT⟩
  have hxnep : x ≠ p := by
    intro h
    exact hxnotT (by simp [T, h])
  have hxneq : x ≠ q := by
    intro h
    exact hxnotT (by simp [T, h])
  have hxner : x ≠ r := by
    intro h
    exact hxnotT (by simp [T, h])
  refine ⟨x, hxpoints, p, ?_, q, ?_, r, ?_, hnon⟩
  · exact Finset.mem_erase.mpr ⟨hxnep.symm, hp⟩
  · exact Finset.mem_erase.mpr ⟨hxneq.symm, hq⟩
  · exact Finset.mem_erase.mpr ⟨hxner.symm, hr⟩

theorem finite_slope_mem_directionsDeterminedBy {points : Finset Point2} {m : ℝ}
    (hm : m ∈ slopesDeterminedBy points) :
    Direction.finite m ∈ directionsDeterminedBy points := by
  rcases Finset.mem_image.mp hm with ⟨pq, hpq_mem, hpq_slope⟩
  rcases pq with ⟨p, q⟩
  rcases Finset.mem_filter.mp hpq_mem with ⟨hpq_prod, hpq_cond⟩
  rcases hpq_cond with ⟨hpq_ne, hx_ne⟩
  refine Finset.mem_image.mpr ⟨(p, q), ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hpq_prod, hpq_ne⟩
  · simp [direction, hx_ne, hpq_slope]

theorem slopes_card_le_directions_card (points : Finset Point2) :
    (slopesDeterminedBy points).card ≤ (directionsDeterminedBy points).card := by
  classical
  exact Finset.card_le_card_of_injOn Direction.finite
    (fun _ hm => finite_slope_mem_directionsDeterminedBy hm)
    (by intro a _ b _ h; simpa using h)

theorem finite_slope_mem_of_finite_direction {points : Finset Point2} {m : ℝ}
    (hm : Direction.finite m ∈ directionsDeterminedBy points) :
    m ∈ slopesDeterminedBy points := by
  classical
  rcases Finset.mem_image.mp hm with ⟨pq, hpq_mem, hpq_dir⟩
  rcases pq with ⟨p, q⟩
  rcases Finset.mem_filter.mp hpq_mem with ⟨hpq_prod, hpq_ne⟩
  by_cases hx : p.1 = q.1
  · simp [direction, hx] at hpq_dir
  · refine Finset.mem_image.mpr ⟨(p, q), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hpq_prod, hpq_ne, hx⟩
    · simpa [direction, hx] using hpq_dir

theorem vertical_mem_directionsDeterminedBy_iff {points : Finset Point2} :
    Direction.vertical ∈ directionsDeterminedBy points ↔ HasVerticalPair points := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨pq, hpq_mem, hpq_dir⟩
    rcases pq with ⟨p, q⟩
    rcases Finset.mem_filter.mp hpq_mem with ⟨hpq_prod, hpq_ne⟩
    rcases Finset.mem_product.mp hpq_prod with ⟨hp, hq⟩
    by_cases hx : p.1 = q.1
    · exact ⟨p, hp, q, hq, hpq_ne, hx⟩
    · simp [direction, hx] at hpq_dir
  · rintro ⟨p, hp, q, hq, hpq_ne, hx⟩
    refine Finset.mem_image.mpr ⟨(p, q), ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hpq_ne⟩
    · simp [direction, hx]

/-- Removing the vertical direction leaves exactly the finite slopes. -/
theorem directions_erase_vertical_card_eq_slopes_card (points : Finset Point2) :
    ((directionsDeterminedBy points).erase Direction.vertical).card =
      (slopesDeterminedBy points).card := by
  classical
  let finiteDirs := (directionsDeterminedBy points).erase Direction.vertical
  have hfinite_le : finiteDirs.card ≤ (slopesDeterminedBy points).card := by
    refine Finset.card_le_card_of_injOn
      (fun d => match d with | Direction.vertical => 0 | Direction.finite m => m) ?_ ?_
    · intro d hd
      have hdmem : d ∈ directionsDeterminedBy points := Finset.mem_of_mem_erase hd
      cases d with
      | vertical =>
          exact False.elim ((Finset.mem_erase.mp hd).1 rfl)
      | finite m =>
          exact finite_slope_mem_of_finite_direction hdmem
    · intro a ha b hb hab
      cases a with
      | vertical =>
          exact False.elim ((Finset.mem_erase.mp ha).1 rfl)
      | finite ma =>
          cases b with
          | vertical =>
              exact False.elim ((Finset.mem_erase.mp hb).1 rfl)
          | finite mb =>
              simp at hab
              simp [hab]
  have hslopes_le : (slopesDeterminedBy points).card ≤ finiteDirs.card := by
    refine Finset.card_le_card_of_injOn Direction.finite ?_ ?_
    · intro m hm
      apply Finset.mem_erase.mpr
      constructor
      · simp
      · exact finite_slope_mem_directionsDeterminedBy hm
    · intro a _ b _ h
      simpa using h
  have hfinite_card : finiteDirs.card = (slopesDeterminedBy points).card :=
    le_antisymm hfinite_le hslopes_le
  exact hfinite_card

theorem directions_card_eq_slopes_card_add_one_of_hasVerticalPair {points : Finset Point2}
    (hvert : HasVerticalPair points) :
    (directionsDeterminedBy points).card = (slopesDeterminedBy points).card + 1 := by
  classical
  have hv : Direction.vertical ∈ directionsDeterminedBy points :=
    vertical_mem_directionsDeterminedBy_iff.mpr hvert
  have hcard :
      ((directionsDeterminedBy points).erase Direction.vertical).card + 1 =
        (directionsDeterminedBy points).card :=
    Finset.card_erase_add_one hv
  rw [directions_erase_vertical_card_eq_slopes_card] at hcard
  exact hcard.symm

theorem directions_card_eq_slopes_card_of_not_hasVerticalPair {points : Finset Point2}
    (hvert : ¬ HasVerticalPair points) :
    (directionsDeterminedBy points).card = (slopesDeterminedBy points).card := by
  classical
  have hv : Direction.vertical ∉ directionsDeterminedBy points := by
    intro hv
    exact hvert (vertical_mem_directionsDeterminedBy_iff.mp hv)
  have hcard :
      ((directionsDeterminedBy points).erase Direction.vertical).card =
        (directionsDeterminedBy points).card := by
    rw [Finset.erase_eq_of_notMem hv]
  rw [directions_erase_vertical_card_eq_slopes_card] at hcard
  exact hcard.symm

/--
The full projective direction set contains exactly the finite slopes, with
possibly one additional vertical direction.
-/
theorem directions_card_le_slopes_card_succ (points : Finset Point2) :
    (directionsDeterminedBy points).card ≤ (slopesDeterminedBy points).card + 1 := by
  classical
  by_cases hvert : HasVerticalPair points
  · rw [directions_card_eq_slopes_card_add_one_of_hasVerticalPair hvert]
  · rw [directions_card_eq_slopes_card_of_not_hasVerticalPair hvert]
    omega

theorem not_hasVerticalPair_of_noVerticalPairs {points : Finset Point2}
    (hnv : NoVerticalPairs points) : ¬ HasVerticalPair points := by
  rintro ⟨p, hp, q, hq, hpq, hx⟩
  exact hnv hp hq hpq hx

theorem directions_card_eq_slopes_card_of_noVerticalPairs {points : Finset Point2}
    (hnv : NoVerticalPairs points) :
    (directionsDeterminedBy points).card = (slopesDeterminedBy points).card := by
  exact directions_card_eq_slopes_card_of_not_hasVerticalPair
    (not_hasVerticalPair_of_noVerticalPairs hnv)

/--
Ungar's direction-counting form implies the finite-slope form because at most
one determined direction is vertical.
-/
theorem slopes_lower_bound_of_directions_lower_bound (points : Finset Point2)
    (hdirs : points.card ≤ (directionsDeterminedBy points).card) :
    points.card - 1 ≤ (slopesDeterminedBy points).card := by
  have hle := directions_card_le_slopes_card_succ points
  omega

/--
Book reduction, direction version: if every even non-collinear set determines
at least as many directions as points, then every non-collinear set of size at
least four determines at least `n - 1` directions.
-/
theorem directions_lower_bound_of_even_direction_bound (points : Finset Point2)
    (hcard : 4 ≤ points.card) (hncoll : NoncollinearSet points)
    (heven_bound : ∀ S : Finset Point2, Even S.card → NoncollinearSet S →
      S.card ≤ (directionsDeterminedBy S).card) :
    points.card - 1 ≤ (directionsDeterminedBy points).card := by
  classical
  by_cases hEven : Even points.card
  · have hdirs := heven_bound points hEven hncoll
    omega
  · obtain ⟨x, hx, hncollErase⟩ :=
      exists_erase_noncollinear (points := points) (by omega) hncoll
    have hcardErase : (points.erase x).card = points.card - 1 :=
      Finset.card_erase_of_mem hx
    have hEvenErase : Even (points.erase x).card := by
      rw [hcardErase, Nat.even_sub (by omega : 1 ≤ points.card)]
      simp [hEven]
    have hdirsErase := heven_bound (points.erase x) hEvenErase hncollErase
    have hmono : directionsDeterminedBy (points.erase x) ⊆ directionsDeterminedBy points :=
      directionsDeterminedBy_mono (Finset.erase_subset x points)
    have hcardDirs :
        (directionsDeterminedBy (points.erase x)).card ≤
          (directionsDeterminedBy points).card :=
      Finset.card_le_card hmono
    omega

theorem directions_lower_bound_three (points : Finset Point2)
    (hcard : points.card = 3) (hncoll : NoncollinearSet points) :
    points.card - 1 ≤ (directionsDeterminedBy points).card := by
  classical
  rcases hncoll with ⟨p, hp, q, hq, r, hr, hnon⟩
  let witness : Bool → Direction := fun b => cond b (direction p r) (direction p q)
  have hwitness : ∀ b, witness b ∈ directionsDeterminedBy points := by
    intro b
    cases b
    · exact direction_mem_directionsDeterminedBy hp hq
        (left_ne_right_of_noncollinear hnon)
    · exact direction_mem_directionsDeterminedBy hp hr
        (left_ne_third_of_noncollinear hnon)
  have hinj : Function.Injective witness := by
    intro a b hab
    cases a <;> cases b
    · rfl
    · exfalso
      have hdir : direction p q = direction p r := by
        simpa [witness] using hab
      exact hnon (determinant_eq_zero_of_same_direction_from_left hdir)
    · exfalso
      have hdir : direction p q = direction p r := by
        simpa [witness] using hab.symm
      exact hnon (determinant_eq_zero_of_same_direction_from_left hdir)
    · rfl
  have htwo : Fintype.card Bool ≤ (directionsDeterminedBy points).card := by
    exact Finset.card_le_card_of_injOn witness (by intro b _hb; exact hwitness b)
      (by intro a _ha b _hb h; exact hinj h)
  rw [hcard]
  norm_num at htwo ⊢
  exact htwo

theorem one_lt_directions_card_of_noncollinear (points : Finset Point2)
    (hncoll : NoncollinearSet points) :
    1 < (directionsDeterminedBy points).card := by
  classical
  rcases hncoll with ⟨p, hp, q, hq, r, hr, hnon⟩
  let witness : Bool → Direction := fun b => cond b (direction p r) (direction p q)
  have hwitness : ∀ b, witness b ∈ directionsDeterminedBy points := by
    intro b
    cases b
    · exact direction_mem_directionsDeterminedBy hp hq
        (left_ne_right_of_noncollinear hnon)
    · exact direction_mem_directionsDeterminedBy hp hr
        (left_ne_third_of_noncollinear hnon)
  have hinj : Function.Injective witness := by
    intro a b hab
    cases a <;> cases b
    · rfl
    · exfalso
      have hdir : direction p q = direction p r := by
        simpa [witness] using hab
      exact hnon (determinant_eq_zero_of_same_direction_from_left hdir)
    · exfalso
      have hdir : direction p q = direction p r := by
        simpa [witness] using hab.symm
      exact hnon (determinant_eq_zero_of_same_direction_from_left hdir)
    · rfl
  have htwo : Fintype.card Bool ≤ (directionsDeterminedBy points).card := by
    exact Finset.card_le_card_of_injOn witness (by intro b _hb; exact hwitness b)
      (by intro a _ha b _hb h; exact hinj h)
  norm_num at htwo
  omega

theorem directions_lower_bound_of_even_direction_bound_all (points : Finset Point2)
    (hcard : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (heven_bound : ∀ S : Finset Point2, Even S.card → NoncollinearSet S →
      S.card ≤ (directionsDeterminedBy S).card) :
    points.card - 1 ≤ (directionsDeterminedBy points).card := by
  by_cases hthree : points.card = 3
  · exact directions_lower_bound_three points hthree hncoll
  · exact directions_lower_bound_of_even_direction_bound points (by omega) hncoll heven_bound

/--
The numerical core of Ungar's even-cardinality proof.  The crossing moves have
orders `d_i`; every letter crosses the central barrier at least once, giving
`n ≤ Σ 2 d_i`, while the T/O/C block argument fits disjoint blocks of total
length `Σ 2 d_i` inside one period of length `t`.
-/
structure UngarCountingCertificate (n t : ℕ) where
  crossingCount : ℕ
  order : Fin crossingCount → ℕ
  letters_cross : n ≤ ∑ i : Fin crossingCount, 2 * order i
  blocks_fit : (∑ i : Fin crossingCount, 2 * order i) ≤ t

theorem UngarCountingCertificate.length_lower_bound {n t : ℕ}
    (cert : UngarCountingCertificate n t) : n ≤ t :=
  le_trans cert.letters_cross cert.blocks_fit

/-- Integer telescoping identity for Ungar's adjacent crossing-order sums. -/
theorem ungar_adjacent_order_sum_identity_int (c : ℕ) (hc : 2 ≤ c) (d : ℕ → ℤ) :
    (d 0 + d (c - 1) - 1)
        + ∑ i ∈ Finset.range (c - 1), (d i + d (i + 1) - 1)
      =
    2 * (∑ i ∈ Finset.range c, d i) - c := by
  induction c with
  | zero => omega
  | succ c ih =>
      by_cases hc2 : 2 ≤ c
      · have ihc := ih hc2
        rw [Finset.sum_range_succ]
        rw [show c + 1 - 1 = c by omega]
        have hsum_adj :
            (∑ i ∈ Finset.range c, (d i + d (i + 1) - 1)) =
              (∑ i ∈ Finset.range (c - 1), (d i + d (i + 1) - 1)) +
                (d (c - 1) + d c - 1) := by
          rw [← show c - 1 + 1 = c by omega]
          rw [Finset.sum_range_succ]
          simp [Nat.sub_add_cancel (by omega : 1 ≤ c)]
        rw [hsum_adj]
        have hrewrite :
            (d 0 + d c - 1) +
                ((∑ i ∈ Finset.range (c - 1), (d i + d (i + 1) - 1)) +
                  (d (c - 1) + d c - 1))
              =
            ((d 0 + d (c - 1) - 1) +
                ∑ i ∈ Finset.range (c - 1), (d i + d (i + 1) - 1))
              + 2 * d c - 1 := by ring
        rw [hrewrite, ihc]
        rw [show ((c + 1 : ℕ) : ℤ) = (c : ℤ) + 1 by norm_num]
        ring_nf
      · have hc_eq : c = 1 := by omega
        subst c
        simp [Finset.sum_range_succ]
        ring

/-- Telescoping identity for adjacent index gaps. -/
theorem ungar_adjacent_gap_sum_identity_int (c : ℕ) (hc : 1 ≤ c) (a : ℕ → ℤ) :
    (∑ i ∈ Finset.range (c - 1), (a (i + 1) - a i - 1))
      = a (c - 1) - a 0 - (c - 1 : ℤ) := by
  induction c with
  | zero => omega
  | succ c ih =>
      by_cases hc1 : 1 ≤ c
      · have ihc := ih hc1
        rw [show c + 1 - 1 = c by omega]
        have hsum :
            (∑ i ∈ Finset.range c, (a (i + 1) - a i - 1)) =
              (∑ i ∈ Finset.range (c - 1), (a (i + 1) - a i - 1)) +
                (a c - a (c - 1) - 1) := by
          rw [← show c - 1 + 1 = c by omega]
          rw [Finset.sum_range_succ]
          simp [Nat.sub_add_cancel hc1]
        rw [hsum, ihc]
        rw [show ((c + 1 : ℕ) : ℤ) = (c : ℤ) + 1 by norm_num]
        ring
      · have hc_eq : c = 0 := by omega
        subst c
        simp

/--
Finite schedule of crossing moves in Ungar's middle-barrier proof.  The
`idx` and gap fields are the data coming from the T/O/C pattern; the
`blocks_fit` part of the downstream counting certificate is proved from
these gap assumptions by `UngarMoveSchedule.sum_orders_le_moves`.
-/
structure UngarMoveSchedule (k r : ℕ) where
  crossingCount : ℕ
  order : Fin crossingCount → ℕ
  letters_cross : 2 * k ≤ ∑ i : Fin crossingCount, 2 * order i
  two_le_crossingCount : 2 ≤ crossingCount
  idx : Fin crossingCount → Fin r
  idx_strict : ∀ {i j : Fin crossingCount}, i < j → (idx i).val < (idx j).val
  order_pos : ∀ i, 0 < order i
  gap_between :
    ∀ (i : ℕ) (hi : i + 1 < crossingCount),
      order ⟨i, by omega⟩ + order ⟨i + 1, by omega⟩ - 1 ≤
        (idx ⟨i + 1, by omega⟩).val - (idx ⟨i, by omega⟩).val - 1
  gap_ends :
    order ⟨0, by omega⟩ + order ⟨crossingCount - 1, by omega⟩ - 1 ≤
      (idx ⟨0, by omega⟩).val +
        (r - 1 - (idx ⟨crossingCount - 1, by omega⟩).val)

theorem UngarMoveSchedule.crossingCount_le_moves {k r : ℕ}
    (C : UngarMoveSchedule k r) :
    C.crossingCount ≤ r := by
  have hinj : Function.Injective C.idx := by
    intro i j hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have hval_lt := C.idx_strict hlt
      have hval_eq : (C.idx i).val = (C.idx j).val := congrArg Fin.val hij
      omega
    · exact heq
    · have hval_lt := C.idx_strict hgt
      have hval_eq : (C.idx j).val = (C.idx i).val := congrArg Fin.val hij.symm
      omega
  simpa [Fintype.card_fin] using Fintype.card_le_of_injective C.idx hinj

theorem UngarMoveSchedule.two_le_moves {k r : ℕ}
    (C : UngarMoveSchedule k r) :
    2 ≤ r := by
  exact le_trans C.two_le_crossingCount C.crossingCount_le_moves

theorem UngarMoveSchedule.first_idx_lt_last_idx {k r : ℕ}
    (C : UngarMoveSchedule k r) :
    (C.idx ⟨0, lt_of_lt_of_le (by norm_num : 0 < 2) C.two_le_crossingCount⟩).val <
      (C.idx ⟨C.crossingCount - 1,
        Nat.sub_lt (lt_of_lt_of_le (by norm_num : 0 < 2) C.two_le_crossingCount)
          (by norm_num : 0 < 1)⟩).val := by
  have hfin :
      (⟨0, lt_of_lt_of_le (by norm_num : 0 < 2) C.two_le_crossingCount⟩ :
        Fin C.crossingCount) <
        (⟨C.crossingCount - 1,
          Nat.sub_lt (lt_of_lt_of_le (by norm_num : 0 < 2) C.two_le_crossingCount)
            (by norm_num : 0 < 1)⟩ : Fin C.crossingCount) := by
    change 0 < C.crossingCount - 1
    have hc2 : 2 ≤ C.crossingCount := C.two_le_crossingCount
    omega
  exact C.idx_strict hfin

theorem UngarMoveSchedule.sum_orders_le_moves_from_gaps_int {k r : ℕ}
    (C : UngarMoveSchedule k r) :
    (2 * (∑ i : Fin C.crossingCount, (C.order i : ℤ)) : ℤ) ≤ r := by
  classical
  let c := C.crossingCount
  let d : ℕ → ℤ := fun i =>
    if h : i < c then (C.order ⟨i, h⟩ : ℤ) else 0
  let a : ℕ → ℤ := fun i =>
    if h : i < c then ((C.idx ⟨i, h⟩).val : ℤ) else 0
  have horder_sum :
      (∑ i ∈ Finset.range c, d i) =
        ∑ i : Fin c, (C.order i : ℤ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _hi
    simp [d]
  have hbetween :
      (∑ i ∈ Finset.range (c - 1), (d i + d (i + 1) - 1)) ≤
        ∑ i ∈ Finset.range (c - 1), (a (i + 1) - a i - 1) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    have hi0 : i < c := by omega
    have hi1 : i + 1 < c := by omega
    have hg := C.gap_between i (by omega)
    have hpos0 : 0 < C.order ⟨i, hi0⟩ := C.order_pos ⟨i, hi0⟩
    have hpos1 : 0 < C.order ⟨i + 1, hi1⟩ := C.order_pos ⟨i + 1, hi1⟩
    simp [d, a, hi0, hi1]
    omega
  have hgap_sum :
      (∑ i ∈ Finset.range (c - 1), (a (i + 1) - a i - 1)) =
        a (c - 1) - a 0 - (c - 1 : ℤ) := by
    have hc1 : 1 ≤ c := le_trans (by norm_num : 1 ≤ 2) C.two_le_crossingCount
    exact ungar_adjacent_gap_sum_identity_int c hc1 a
  have hbetween' :
      (∑ i ∈ Finset.range (c - 1), (d i + d (i + 1) - 1)) ≤
        a (c - 1) - a 0 - (c - 1 : ℤ) := by
    exact le_trans hbetween (le_of_eq hgap_sum)
  have hends :
      d 0 + d (c - 1) - 1 ≤ a 0 + ((r : ℤ) - 1 - a (c - 1)) := by
    have h0 : 0 < c := lt_of_lt_of_le (by norm_num : 0 < 2) C.two_le_crossingCount
    have hlast : c - 1 < c := Nat.sub_lt h0 (by norm_num)
    have hg := C.gap_ends
    have hpos0 : 0 < C.order ⟨0, h0⟩ := C.order_pos ⟨0, h0⟩
    have hpos_last : 0 < C.order ⟨c - 1, hlast⟩ := C.order_pos ⟨c - 1, hlast⟩
    have hlast_eq :
        (⟨c - 1, hlast⟩ : Fin C.crossingCount) =
          ⟨C.crossingCount - 1, by
            have hcpos : 0 < C.crossingCount :=
              lt_of_lt_of_le (by norm_num : 0 < 2) C.two_le_crossingCount
            exact Nat.sub_lt hcpos (by norm_num)⟩ := by
      apply Fin.ext
      simp [c]
    rw [← hlast_eq] at hg
    simp [d, a, h0, hlast]
    omega
  have hleft_le :
      (d 0 + d (c - 1) - 1) +
          ∑ i ∈ Finset.range (c - 1), (d i + d (i + 1) - 1)
        ≤
      (a 0 + ((r : ℤ) - 1 - a (c - 1))) +
          (a (c - 1) - a 0 - (c - 1 : ℤ)) := by
    exact add_le_add hends hbetween'
  have hidentity :=
    ungar_adjacent_order_sum_identity_int c C.two_le_crossingCount d
  rw [hidentity] at hleft_le
  rw [horder_sum] at hleft_le
  have hright_eq :
      (a 0 + ((r : ℤ) - 1 - a (c - 1))) +
          (a (c - 1) - a 0 - (c - 1 : ℤ)) =
        (r : ℤ) - c := by
    have hc_cast : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by
      have hc1 : 1 ≤ c := le_trans (by norm_num : 1 ≤ 2) C.two_le_crossingCount
      omega
    ring
  rw [hright_eq] at hleft_le
  linarith

theorem UngarMoveSchedule.sum_orders_le_moves_from_gaps {k r : ℕ}
    (C : UngarMoveSchedule k r) :
    (∑ i : Fin C.crossingCount, 2 * C.order i) ≤ r := by
  have hint := C.sum_orders_le_moves_from_gaps_int
  have hsum :
      ((∑ i : Fin C.crossingCount, 2 * C.order i : ℕ) : ℤ) =
        2 * (∑ i : Fin C.crossingCount, (C.order i : ℤ)) := by
    simp [Finset.mul_sum]
  have hcast : ((∑ i : Fin C.crossingCount, 2 * C.order i : ℕ) : ℤ) ≤ (r : ℤ) := by
    rw [hsum]
    exact hint
  exact_mod_cast hcast

theorem UngarMoveSchedule.sum_orders_le_moves {k r : ℕ}
    (C : UngarMoveSchedule k r) :
    (∑ i : Fin C.crossingCount, 2 * C.order i) ≤ r :=
  C.sum_orders_le_moves_from_gaps

def UngarMoveSchedule.toCountingCertificate {k r : ℕ}
    (C : UngarMoveSchedule k r) : UngarCountingCertificate (2 * k) r where
  crossingCount := C.crossingCount
  order := C.order
  letters_cross := C.letters_cross
  blocks_fit := C.sum_orders_le_moves

/--
Discrete intermediate-value lemma for a Boolean/decidable property on a Nat
interval.  If `P` is false at `a` and true at `a + n + 1`, then at some
adjacent step it switches from false to true.
-/
theorem exists_false_true_switch {P : ℕ → Prop} [DecidablePred P]
    (a n : ℕ) (h0 : ¬ P a) (h1 : P (a + n + 1)) :
    ∃ m : ℕ, a ≤ m ∧ m ≤ a + n ∧ ¬ P m ∧ P (m + 1) := by
  induction n with
  | zero =>
      refine ⟨a, le_rfl, by omega, h0, ?_⟩
      simpa using h1
  | succ n ih =>
      by_cases hmid : P (a + n + 1)
      · rcases ih hmid with ⟨m, hma, hmn, hmfalse, hmtrue⟩
        refine ⟨m, hma, ?_, hmfalse, hmtrue⟩
        omega
      · refine ⟨a + n + 1, by omega, by omega, hmid, ?_⟩
        simpa [Nat.add_assoc] using h1

theorem exists_false_true_switch_between {P : ℕ → Prop} [DecidablePred P]
    {a b : ℕ} (hab : a ≤ b) (h0 : ¬ P a) (h1 : P b) :
    ∃ m : ℕ, a ≤ m ∧ m < b ∧ ¬ P m ∧ P (m + 1) := by
  by_cases hlt : a < b
  · let n := b - a - 1
    have hend : P (a + n + 1) := by
      have hsum : a + n + 1 = b := by
        dsimp [n]
        omega
      simpa [hsum] using h1
    rcases exists_false_true_switch a n h0 hend with ⟨m, hma, hmn, hmfalse, hmtrue⟩
    refine ⟨m, hma, ?_, hmfalse, hmtrue⟩
    dsimp [n] at hmn
    omega
  · have hba : b = a := by omega
    subst b
    exact False.elim (h0 h1)

/--
A finite packing certificate for the T/O/C block argument: the `i`th crossing
move of order `dᵢ` owns a block of `2dᵢ` slots, and all these slots inject
into one period of length `t`.
-/
structure UngarBlockPacking (t crossingCount : ℕ) (order : Fin crossingCount → ℕ) where
  slot : (Σ i : Fin crossingCount, Fin (2 * order i)) → Fin t
  injective_slot : Function.Injective slot

theorem UngarBlockPacking.blocks_fit {t crossingCount : ℕ}
    {order : Fin crossingCount → ℕ}
    (packing : UngarBlockPacking t crossingCount order) :
    (∑ i : Fin crossingCount, 2 * order i) ≤ t := by
  have hcard := Fintype.card_le_of_injective packing.slot packing.injective_slot
  simpa [Fintype.card_sigma, Fintype.card_fin] using hcard

/--
An equivalent, more geometric way to certify the T/O/C block packing: assign
to each crossing move a block of positions inside one period, with the blocks
pairwise disjoint and of the prescribed size.
-/
structure UngarDisjointBlockPacking (t crossingCount : ℕ)
    (order : Fin crossingCount → ℕ) where
  block : Fin crossingCount → Finset (Fin t)
  block_card : ∀ i, (block i).card = 2 * order i
  pairwise_disjoint :
    ((Finset.univ : Finset (Fin crossingCount)) : Set (Fin crossingCount)).PairwiseDisjoint block

theorem UngarDisjointBlockPacking.blocks_fit {t crossingCount : ℕ}
    {order : Fin crossingCount → ℕ}
    (packing : UngarDisjointBlockPacking t crossingCount order) :
    (∑ i : Fin crossingCount, 2 * order i) ≤ t := by
  classical
  have hcard :
      ((Finset.univ : Finset (Fin crossingCount)).biUnion packing.block).card =
        ∑ i : Fin crossingCount, (packing.block i).card := by
    simpa using
      (Finset.card_biUnion (s := (Finset.univ : Finset (Fin crossingCount)))
        (t := packing.block) packing.pairwise_disjoint)
  have hle :
      ((Finset.univ : Finset (Fin crossingCount)).biUnion packing.block).card ≤ t := by
    simpa [Fintype.card_fin] using
      (((Finset.univ : Finset (Fin crossingCount)).biUnion packing.block).card_le_univ)
  rw [hcard] at hle
  simpa [packing.block_card] using hle

/--
The finite sweep certificate that remains to be extracted from the rotating
projection sequence: crossing orders, enough letter crossings, and a block
packing inside one period.
-/
structure UngarSweepCertificate (n t : ℕ) where
  crossingCount : ℕ
  order : Fin crossingCount → ℕ
  letters_cross : n ≤ ∑ i : Fin crossingCount, 2 * order i
  packing : UngarBlockPacking t crossingCount order

/--
Same sweep certificate, but using explicit disjoint blocks in the period.
This is usually the easier object to extract from the T/O/C pattern.
-/
structure UngarFinsetSweepCertificate (n t : ℕ) where
  crossingCount : ℕ
  order : Fin crossingCount → ℕ
  letters_cross : n ≤ ∑ i : Fin crossingCount, 2 * order i
  packing : UngarDisjointBlockPacking t crossingCount order

def UngarSweepCertificate.toCountingCertificate {n t : ℕ}
    (cert : UngarSweepCertificate n t) : UngarCountingCertificate n t where
  crossingCount := cert.crossingCount
  order := cert.order
  letters_cross := cert.letters_cross
  blocks_fit := cert.packing.blocks_fit

theorem UngarSweepCertificate.length_lower_bound {n t : ℕ}
    (cert : UngarSweepCertificate n t) : n ≤ t :=
  cert.toCountingCertificate.length_lower_bound

def UngarFinsetSweepCertificate.toCountingCertificate {n t : ℕ}
    (cert : UngarFinsetSweepCertificate n t) : UngarCountingCertificate n t where
  crossingCount := cert.crossingCount
  order := cert.order
  letters_cross := cert.letters_cross
  blocks_fit := cert.packing.blocks_fit

theorem UngarFinsetSweepCertificate.length_lower_bound {n t : ℕ}
    (cert : UngarFinsetSweepCertificate n t) : n ≤ t :=
  cert.toCountingCertificate.length_lower_bound

theorem even_direction_bound_of_ungar_counting_certificate (points : Finset Point2)
    (cert : UngarCountingCertificate points.card (directionsDeterminedBy points).card) :
    points.card ≤ (directionsDeterminedBy points).card :=
  cert.length_lower_bound

theorem even_direction_bound_of_ungar_sweep_certificate (points : Finset Point2)
    (cert : UngarSweepCertificate points.card (directionsDeterminedBy points).card) :
    points.card ≤ (directionsDeterminedBy points).card :=
  cert.length_lower_bound

theorem even_direction_bound_of_ungar_finset_sweep_certificate (points : Finset Point2)
    (cert : UngarFinsetSweepCertificate points.card (directionsDeterminedBy points).card) :
    points.card ≤ (directionsDeterminedBy points).card :=
  cert.length_lower_bound

theorem even_direction_bound_of_ungar_move_schedule (points : Finset Point2) {k : ℕ}
    (hcard : points.card = 2 * k)
    (cert : UngarMoveSchedule k (directionsDeterminedBy points).card) :
    points.card ≤ (directionsDeterminedBy points).card := by
  rw [hcard]
  exact cert.toCountingCertificate.length_lower_bound

theorem directions_lower_bound_of_even_ungar_certificates (points : Finset Point2)
    (hcard : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : ∀ S : Finset Point2, Even S.card → NoncollinearSet S →
      UngarCountingCertificate S.card (directionsDeterminedBy S).card) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  directions_lower_bound_of_even_direction_bound_all points hcard hncoll
    (fun S hEven hS =>
      even_direction_bound_of_ungar_counting_certificate S (hcert S hEven hS))

theorem directions_lower_bound_of_even_ungar_sweep_certificates (points : Finset Point2)
    (hcard : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : ∀ S : Finset Point2, Even S.card → NoncollinearSet S →
      UngarSweepCertificate S.card (directionsDeterminedBy S).card) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  directions_lower_bound_of_even_direction_bound_all points hcard hncoll
    (fun S hEven hS =>
      even_direction_bound_of_ungar_sweep_certificate S (hcert S hEven hS))

theorem directions_lower_bound_of_even_ungar_move_schedules (points : Finset Point2)
    (hcard : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : ∀ S : Finset Point2, ∀ k : ℕ, S.card = 2 * k → NoncollinearSet S →
      UngarMoveSchedule k (directionsDeterminedBy S).card) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  directions_lower_bound_of_even_direction_bound_all points hcard hncoll
    (fun S hEven hS => by
      rcases hEven with ⟨k, hk⟩
      have hcardS : S.card = 2 * k := by omega
      exact even_direction_bound_of_ungar_move_schedule S hcardS (hcert S k hcardS hS))

/-! ### Finite allowable-sequence vocabulary -/

/-- A permutation state maps position to label. -/
abbrev State (N : ℕ) := Equiv.Perm (Fin N)

/-- The left side of the middle barrier in `2 * k` positions. -/
def middleLeft (k : ℕ) (p : Fin (2 * k)) : Prop :=
  p.val < k

/-- A label crosses the middle barrier between two permutation states. -/
def crossesMiddle (k : ℕ) (π ρ : State (2 * k)) (a : Fin (2 * k)) : Prop :=
  middleLeft k (π.symm a) ↔ ¬ middleLeft k (ρ.symm a)

/-- The source index of step `j` in a sequence of `r + 1` states. -/
def stepFrom {r : ℕ} (j : Fin r) : Fin (r + 1) :=
  ⟨j.val, lt_trans j.isLt (Nat.lt_succ_self r)⟩

/-- The target index of step `j` in a sequence of `r + 1` states. -/
def stepTo {r : ℕ} (j : Fin r) : Fin (r + 1) :=
  ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩

/-- The reverse permutation on `Fin N`. -/
def reverseFin (N : ℕ) : State N :=
  Fin.revPerm

theorem middleLeft_reverseFin_symm_iff_not {k : ℕ} (a : Fin (2 * k)) :
    middleLeft k ((reverseFin (2 * k)).symm a) ↔ ¬ middleLeft k a := by
  simp [reverseFin, middleLeft, Fin.revPerm_symm]
  omega

/--
A finite generalized allowable sequence, reduced to the data needed for the
middle-barrier counting layer: a list of permutation states beginning at the
identity and ending at the reverse permutation.
-/
structure GeneralizedAllowableSequence (k r : ℕ) where
  π : Fin (r + 1) → State (2 * k)
  start : π ⟨0, Nat.succ_pos r⟩ = Equiv.refl (Fin (2 * k))
  finish : π ⟨r, Nat.lt_succ_self r⟩ = reverseFin (2 * k)

namespace GeneralizedAllowableSequence

/-- If a Boolean value changes between the endpoints of a finite sequence,
then it changes across some adjacent step. -/
theorem every_label_crosses {k r : ℕ} (A : GeneralizedAllowableSequence k r)
    (a : Fin (2 * k)) :
    ∃ j : Fin r,
      crossesMiddle k (A.π (stepFrom j)) (A.π (stepTo j)) a := by
  classical
  by_contra hnone
  push Not at hnone
  have hsame_step :
      ∀ j : Fin r,
        middleLeft k ((A.π (stepFrom j)).symm a) ↔
          middleLeft k ((A.π (stepTo j)).symm a) := by
    intro j
    have hnot := hnone j
    unfold crossesMiddle at hnot
    by_cases hfrom : middleLeft k ((A.π (stepFrom j)).symm a) <;>
      by_cases hto : middleLeft k ((A.π (stepTo j)).symm a) <;>
      simp [hfrom, hto] at hnot ⊢
  let b (i : ℕ) (hi : i ≤ r) : Prop :=
    middleLeft k ((A.π ⟨i, Nat.lt_succ_of_le hi⟩).symm a)
  have hsame_to_start :
      ∀ i : ℕ, ∀ hi : i ≤ r, b i hi ↔ b 0 (Nat.zero_le r) := by
    intro i
    induction i with
    | zero =>
        intro hi
        rfl
    | succ i ih =>
        intro hi
        have hi_prev : i ≤ r := Nat.le_of_succ_le hi
        have hi_lt : i < r := Nat.lt_of_succ_le hi
        have hstep := hsame_step ⟨i, hi_lt⟩
        have hprev := ih hi_prev
        change b i hi_prev ↔ b (i + 1) hi at hstep
        exact hstep.symm.trans hprev
  have hend_same :
      middleLeft k ((A.π ⟨r, Nat.lt_succ_self r⟩).symm a) ↔
        middleLeft k ((A.π ⟨0, Nat.succ_pos r⟩).symm a) := by
    simpa [b] using hsame_to_start r (le_rfl : r ≤ r)
  have hstart :
      middleLeft k ((A.π ⟨0, Nat.succ_pos r⟩).symm a) ↔ middleLeft k a := by
    rw [A.start]
    simp
  have hend :
      middleLeft k ((A.π ⟨r, Nat.lt_succ_self r⟩).symm a) ↔
        ¬ middleLeft k a := by
    rw [A.finish]
    exact middleLeft_reverseFin_symm_iff_not a
  have hbad :
      middleLeft k ((A.π ⟨0, Nat.succ_pos r⟩).symm a) ↔
        ¬ middleLeft k ((A.π ⟨0, Nat.succ_pos r⟩).symm a) := by
    exact hend_same.symm.trans (hend.trans (not_congr hstart.symm))
  by_cases h0 : middleLeft k ((A.π ⟨0, Nat.succ_pos r⟩).symm a)
  · exact (hbad.mp h0) h0
  · exact h0 (hbad.mpr h0)

/-- The number of labels crossing the middle barrier in one step. -/
noncomputable def crossingLabelsCard {k r : ℕ} (A : GeneralizedAllowableSequence k r)
    (j : Fin r) : ℕ := by
  classical
  exact Fintype.card
    {a : Fin (2 * k) //
      crossesMiddle k (A.π (stepFrom j)) (A.π (stepTo j)) a}

theorem crossingLabelsCard_eq_two_mul_of_refl_reverse {k r : ℕ}
    (A : GeneralizedAllowableSequence k r) (j : Fin r)
    (hsource : A.π (stepFrom j) = Equiv.refl (Fin (2 * k)))
    (htarget : A.π (stepTo j) = reverseFin (2 * k)) :
    A.crossingLabelsCard j = 2 * k := by
  classical
  unfold crossingLabelsCard
  rw [hsource, htarget]
  simp [crossesMiddle, middleLeft_reverseFin_symm_iff_not]

/--
Step-level crossing counts for a generalized allowable sequence.  The
geometric block-reversal layer will prove `crossed_labels_card`; this finite
layer only uses the count.
-/
structure StepCounting {k r : ℕ} (A : GeneralizedAllowableSequence k r) where
  order : Fin r → ℕ
  crossed_labels_card :
    ∀ j : Fin r, crossingLabelsCard A j = 2 * order j

/--
Every label crosses the middle at least once, so the sum of step crossing
counts is at least the number of labels.
-/
theorem StepCounting.letters_cross {k r : ℕ} {A : GeneralizedAllowableSequence k r}
    (C : StepCounting A) :
    2 * k ≤ ∑ j : Fin r, 2 * C.order j := by
  classical
  let pick : Fin (2 * k) → Fin r := fun a =>
    Classical.choose (A.every_label_crosses a)
  let packed :
      Fin (2 * k) →
        Σ j : Fin r,
          {a : Fin (2 * k) //
            crossesMiddle k (A.π (stepFrom j)) (A.π (stepTo j)) a} :=
    fun a => ⟨pick a, ⟨a, Classical.choose_spec (A.every_label_crosses a)⟩⟩
  let unpack :
      (Σ j : Fin r,
        {a : Fin (2 * k) //
          crossesMiddle k (A.π (stepFrom j)) (A.π (stepTo j)) a}) →
        Fin (2 * k) :=
    fun x => x.2.1
  have hinj : Function.Injective packed := by
    intro a b h
    have hval := congrArg unpack h
    simpa [packed, unpack] using hval
  have hcard := Fintype.card_le_of_injective packed hinj
  have hcard' :
      2 * k ≤
        ∑ j : Fin r, crossingLabelsCard A j := by
    simpa [crossingLabelsCard, Fintype.card_fin, Fintype.card_sigma] using hcard
  have hsum :
      (∑ j : Fin r, crossingLabelsCard A j) =
        ∑ j : Fin r, 2 * C.order j := by
    apply Finset.sum_congr rfl
    intro j _hj
    exact C.crossed_labels_card j
  rwa [hsum] at hcard'

/-- A step-counting proof plus a packing proof gives the sweep certificate. -/
def StepCounting.toSweepCertificate {k r : ℕ} {A : GeneralizedAllowableSequence k r}
    (C : StepCounting A) (packing : UngarBlockPacking r r C.order) :
    UngarSweepCertificate (2 * k) r where
  crossingCount := r
  order := C.order
  letters_cross := C.letters_cross
  packing := packing

/-- A step-counting proof plus a packing proof gives the counting certificate. -/
def StepCounting.toCountingCertificate {k r : ℕ} {A : GeneralizedAllowableSequence k r}
    (C : StepCounting A) (packing : UngarBlockPacking r r C.order) :
    UngarCountingCertificate (2 * k) r :=
  (C.toSweepCertificate packing).toCountingCertificate

end GeneralizedAllowableSequence

/-! ### Sweep → GeneralizedAllowableSequence bridge -/

theorem reverseFin_eq_revPerm (N : ℕ) : reverseFin N = Fin.revPerm := rfl

theorem sweepSort_reindex_refl {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ : ℝ) :
    sweepSort (L.reindex (Equiv.refl _)) θ = sweepSort L θ := rfl

theorem sweepSort_add_pi_eq_reverseFin {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ₀ : ℝ)
    (hstart : sweepSort L θ₀ = Equiv.refl _)
    (hinj : Function.Injective (fun a : Fin (2 * k) =>
      orientedLevel θ₀ (L.point a))) :
    sweepSort L (θ₀ + Real.pi) = reverseFin (2 * k) := by
  rw [reverseFin_eq_revPerm]
  have h := sweepSort_reindex_add_pi_eq_revPerm L θ₀ hinj
  rwa [hstart, sweepSort_reindex_refl] at h

noncomputable def GeneralizedAllowableSequence.ofSweepAngles
    {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k)
    (θ : Fin ((directionsDeterminedBy points).card + 1) → ℝ)
    (hstart : sweepSort L (θ ⟨0, Nat.succ_pos _⟩) = Equiv.refl _)
    (hfinish_eq : θ ⟨(directionsDeterminedBy points).card, Nat.lt_succ_self _⟩ =
      θ ⟨0, Nat.succ_pos _⟩ + Real.pi)
    (hinj : Function.Injective (fun a : Fin (2 * k) =>
      orientedLevel (θ ⟨0, Nat.succ_pos _⟩) (L.point a))) :
    GeneralizedAllowableSequence k (directionsDeterminedBy points).card where
  π := fun j => sweepSort L (θ j)
  start := hstart
  finish := by
    rw [hfinish_eq]
    exact sweepSort_add_pi_eq_reverseFin L _ hstart hinj

/-! ### Consecutive block moves -/

/-- A consecutive interval of positions in `Fin N`. -/
structure PositionInterval (N : ℕ) where
  lo : ℕ
  hi : ℕ
  lo_le_hi : lo ≤ hi
  hi_lt : hi < N

namespace PositionInterval

/-- Membership of a position in a consecutive interval. -/
def Mem {N : ℕ} (I : PositionInterval N) (p : Fin N) : Prop :=
  I.lo ≤ p.val ∧ p.val ≤ I.hi

/-- The set of positions in a consecutive interval. -/
def toSet {N : ℕ} (I : PositionInterval N) : Set (Fin N) :=
  {p | I.Mem p}

/-- The finite set of positions in a consecutive interval. -/
noncomputable def toFinset {N : ℕ} (I : PositionInterval N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter I.Mem

theorem mem_toFinset {N : ℕ} {I : PositionInterval N} {p : Fin N} :
    p ∈ I.toFinset ↔ I.Mem p := by
  simp [toFinset]

/-- Mirror a position across the midpoint of a consecutive interval. -/
def mirror {N : ℕ} (I : PositionInterval N) (p : Fin N) (hp : I.Mem p) : Fin N :=
  ⟨I.lo + I.hi - p.val, by
    rcases hp with ⟨hlo, hhi⟩
    have hle_hi : I.lo + I.hi - p.val ≤ I.hi := by omega
    exact lt_of_le_of_lt hle_hi I.hi_lt⟩

theorem mirror_mem {N : ℕ} (I : PositionInterval N) (p : Fin N) (hp : I.Mem p) :
    I.Mem (I.mirror p hp) := by
  rcases hp with ⟨hlo, hhi⟩
  constructor
  · dsimp [mirror]
    omega
  · dsimp [mirror]
    omega

theorem mirror_val {N : ℕ} (I : PositionInterval N) (p : Fin N) (hp : I.Mem p) :
    (I.mirror p hp).val = I.lo + I.hi - p.val := rfl

theorem mirror_mirror {N : ℕ} (I : PositionInterval N) (p : Fin N) (hp : I.Mem p) :
    I.mirror (I.mirror p hp) (I.mirror_mem p hp) = p := by
  apply Fin.ext
  rcases hp with ⟨hlo, hhi⟩
  dsimp [mirror]
  omega

theorem mirror_strictAnti {N : ℕ} (I : PositionInterval N)
    {p q : Fin N} (hp : I.Mem p) (hq : I.Mem q) (hpq : p < q) :
    I.mirror q hq < I.mirror p hp := by
  rcases hp with ⟨hplo, hphi⟩
  rcases hq with ⟨hqlo, hqhi⟩
  change (I.mirror q ⟨hqlo, hqhi⟩).val < (I.mirror p ⟨hplo, hphi⟩).val
  dsimp [mirror]
  omega

theorem le_mirror_iff_le_sub {N k : ℕ} (I : PositionInterval N)
    (p : Fin N) (hp : I.Mem p) (hk : k ≤ I.hi) :
    k ≤ (I.mirror p hp).val ↔ p.val ≤ I.lo + I.hi - k := by
  rcases hp with ⟨hlo, hhi⟩
  dsimp [mirror]
  omega

theorem mirror_lt_iff_sub_lt {N k : ℕ} (I : PositionInterval N)
    (p : Fin N) (hp : I.Mem p) :
    (I.mirror p hp).val < k ↔ I.lo + I.hi - p.val < k := by
  rfl

/-- The number of positions in a consecutive interval. -/
def length {N : ℕ} (I : PositionInterval N) : ℕ :=
  I.hi + 1 - I.lo

theorem toFinset_card {N : ℕ} (I : PositionInterval N) :
    I.toFinset.card = I.length := by
  classical
  let e : Fin N ↪ ℕ := ⟨Fin.val, by intro a b h; exact Fin.ext h⟩
  have hmap : I.toFinset.map e = Finset.Icc I.lo I.hi := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
      rw [mem_toFinset] at hp
      simp [e] at hpval
      subst n
      exact Finset.mem_Icc.mpr hp
    · intro hn
      rcases Finset.mem_Icc.mp hn with ⟨hlo, hhi⟩
      have hnlt : n < N := lt_of_le_of_lt hhi I.hi_lt
      refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
      · rw [mem_toFinset]
        exact ⟨hlo, hhi⟩
      · simp [e]
  have hcard_map : (I.toFinset.map e).card = I.toFinset.card :=
    Finset.card_map e
  rw [hmap] at hcard_map
  rw [← hcard_map]
  simp [length]

theorem left_of_middle_card_of_crossing {k : ℕ} (I : PositionInterval (2 * k))
    (hcross : I.lo < k ∧ k ≤ I.hi) :
    (I.toFinset.filter fun p => p.val < k).card = k - I.lo := by
  classical
  let e : Fin (2 * k) ↪ ℕ := ⟨Fin.val, by intro a b h; exact Fin.ext h⟩
  have hmap :
      (I.toFinset.filter fun p => p.val < k).map e = Finset.Icc I.lo (k - 1) := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
      rw [Finset.mem_filter, mem_toFinset] at hp
      simp [e] at hpval
      subst n
      exact Finset.mem_Icc.mpr ⟨hp.1.1, Nat.le_sub_one_of_lt hp.2⟩
    · intro hn
      rcases Finset.mem_Icc.mp hn with ⟨hlo, hle⟩
      have hnlt_k : n < k := by omega
      have hnlt : n < 2 * k := lt_trans hnlt_k (by omega : k < 2 * k)
      refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
      · rw [Finset.mem_filter, mem_toFinset]
        exact ⟨⟨hlo, le_trans hnlt_k.le hcross.2⟩, hnlt_k⟩
      · simp [e]
  have hcard_map :
      ((I.toFinset.filter fun p => p.val < k).map e).card =
        (I.toFinset.filter fun p => p.val < k).card :=
    Finset.card_map e
  rw [hmap] at hcard_map
  rw [← hcard_map]
  simp
  omega

theorem right_of_middle_card_of_crossing {k : ℕ} (I : PositionInterval (2 * k))
    (hcross : I.lo < k ∧ k ≤ I.hi) :
    (I.toFinset.filter fun p => k ≤ p.val).card = I.hi + 1 - k := by
  classical
  let e : Fin (2 * k) ↪ ℕ := ⟨Fin.val, by intro a b h; exact Fin.ext h⟩
  have hmap :
      (I.toFinset.filter fun p => k ≤ p.val).map e = Finset.Icc k I.hi := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
      rw [Finset.mem_filter, mem_toFinset] at hp
      simp [e] at hpval
      subst n
      exact Finset.mem_Icc.mpr ⟨hp.2, hp.1.2⟩
    · intro hn
      rcases Finset.mem_Icc.mp hn with ⟨hk, hhi⟩
      have hnlt : n < 2 * k := lt_of_le_of_lt hhi I.hi_lt
      refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
      · rw [Finset.mem_filter, mem_toFinset]
        exact ⟨⟨le_trans hcross.1.le hk, hhi⟩, hk⟩
      · simp [e]
  have hcard_map :
      ((I.toFinset.filter fun p => k ≤ p.val).map e).card =
        (I.toFinset.filter fun p => k ≤ p.val).card :=
    Finset.card_map e
  rw [hmap] at hcard_map
  rw [← hcard_map]
  simp

/--
For `2 * k` positions, the order of an interval crossing the middle barrier.
The barrier is between positions `k - 1` and `k`.
-/
def crossOrder (k : ℕ) (I : PositionInterval (2 * k)) : ℕ :=
  if I.lo < k ∧ k ≤ I.hi then
    Nat.min (k - I.lo) (I.hi + 1 - k)
  else
    0

theorem crossOrder_eq_zero_of_not_crossing {k : ℕ} {I : PositionInterval (2 * k)}
    (h : ¬ (I.lo < k ∧ k ≤ I.hi)) :
    I.crossOrder k = 0 := by
  simp [crossOrder, h]

theorem crossOrder_eq_min_of_crossing {k : ℕ} {I : PositionInterval (2 * k)}
    (h : I.lo < k ∧ k ≤ I.hi) :
    I.crossOrder k = Nat.min (k - I.lo) (I.hi + 1 - k) := by
  simp [crossOrder, h]

/-- Positions in `I` on the left of the middle whose mirror lies on the right. -/
noncomputable def leftMirrorCrossingPositions (k : ℕ) (I : PositionInterval (2 * k)) :
    Finset (Fin (2 * k)) := by
  classical
  exact I.toFinset.filter fun p => p.val < k ∧ p.val ≤ I.lo + I.hi - k

theorem leftMirrorCrossingPositions_card_eq_crossOrder_of_crossing {k : ℕ}
    (I : PositionInterval (2 * k)) (hcross : I.lo < k ∧ k ≤ I.hi) :
    (leftMirrorCrossingPositions k I).card = I.crossOrder k := by
  classical
  let e : Fin (2 * k) ↪ ℕ := ⟨Fin.val, by intro a b h; exact Fin.ext h⟩
  by_cases hle : k - I.lo ≤ I.hi + 1 - k
  · have hmap :
        (leftMirrorCrossingPositions k I).map e = Finset.Icc I.lo (k - 1) := by
      ext n
      constructor
      · intro hn
        rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
        rw [leftMirrorCrossingPositions, Finset.mem_filter, mem_toFinset] at hp
        simp [e] at hpval
        subst n
        exact Finset.mem_Icc.mpr ⟨hp.1.1, Nat.le_sub_one_of_lt hp.2.1⟩
      · intro hn
        rcases Finset.mem_Icc.mp hn with ⟨hlo, hhi⟩
        have hnlt_k : n < k := by omega
        have hnlt : n < 2 * k := by omega
        have hbound : k - 1 ≤ I.lo + I.hi - k := by omega
        refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
        · rw [leftMirrorCrossingPositions, Finset.mem_filter, mem_toFinset]
          exact ⟨⟨hlo, le_trans hnlt_k.le hcross.2⟩, hnlt_k, le_trans hhi hbound⟩
        · simp [e]
    have hcard_map :
        ((leftMirrorCrossingPositions k I).map e).card =
          (leftMirrorCrossingPositions k I).card :=
      Finset.card_map e
    rw [hmap] at hcard_map
    rw [← hcard_map, crossOrder_eq_min_of_crossing hcross]
    have hmin : Nat.min (k - I.lo) (I.hi + 1 - k) = k - I.lo :=
      Nat.min_eq_left hle
    rw [hmin]
    simp
    omega
  · have hle' : I.hi + 1 - k < k - I.lo := Nat.lt_of_not_ge hle
    have hmap :
        (leftMirrorCrossingPositions k I).map e = Finset.Icc I.lo (I.lo + I.hi - k) := by
      ext n
      constructor
      · intro hn
        rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
        rw [leftMirrorCrossingPositions, Finset.mem_filter, mem_toFinset] at hp
        simp [e] at hpval
        subst n
        exact Finset.mem_Icc.mpr ⟨hp.1.1, hp.2.2⟩
      · intro hn
        rcases Finset.mem_Icc.mp hn with ⟨hlo, hhi⟩
        have hbound : I.lo + I.hi - k < k := by omega
        have hnlt_k : n < k := lt_of_le_of_lt hhi hbound
        have hklt : k < 2 * k := by omega
        have hnlt : n < 2 * k := lt_trans hnlt_k hklt
        have hupper : I.lo + I.hi - k ≤ I.hi := by omega
        refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
        · rw [leftMirrorCrossingPositions, Finset.mem_filter, mem_toFinset]
          exact ⟨⟨hlo, le_trans hhi hupper⟩, hnlt_k, hhi⟩
        · simp [e]
    have hcard_map :
        ((leftMirrorCrossingPositions k I).map e).card =
          (leftMirrorCrossingPositions k I).card :=
      Finset.card_map e
    rw [hmap] at hcard_map
    rw [← hcard_map, crossOrder_eq_min_of_crossing hcross]
    have hmin : Nat.min (k - I.lo) (I.hi + 1 - k) = I.hi + 1 - k :=
      Nat.min_eq_right hle'.le
    rw [hmin]
    simp
    omega

/-- Positions in `I` on the right of the middle whose mirror lies on the left. -/
noncomputable def rightMirrorCrossingPositions (k : ℕ) (I : PositionInterval (2 * k)) :
    Finset (Fin (2 * k)) := by
  classical
  exact I.toFinset.filter fun p => k ≤ p.val ∧ I.lo + I.hi + 1 - k ≤ p.val

theorem rightMirrorCrossingPositions_card_eq_crossOrder_of_crossing {k : ℕ}
    (I : PositionInterval (2 * k)) (hcross : I.lo < k ∧ k ≤ I.hi) :
    (rightMirrorCrossingPositions k I).card = I.crossOrder k := by
  classical
  let e : Fin (2 * k) ↪ ℕ := ⟨Fin.val, by intro a b h; exact Fin.ext h⟩
  by_cases hle : k - I.lo ≤ I.hi + 1 - k
  · have hmap :
        (rightMirrorCrossingPositions k I).map e =
          Finset.Icc (I.lo + I.hi + 1 - k) I.hi := by
      ext n
      constructor
      · intro hn
        rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
        rw [rightMirrorCrossingPositions, Finset.mem_filter, mem_toFinset] at hp
        simp [e] at hpval
        subst n
        exact Finset.mem_Icc.mpr ⟨hp.2.2, hp.1.2⟩
      · intro hn
        rcases Finset.mem_Icc.mp hn with ⟨hlo, hhi⟩
        have hlow_ge_k : k ≤ I.lo + I.hi + 1 - k := by omega
        have hnlt : n < 2 * k := lt_of_le_of_lt hhi I.hi_lt
        refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
        · rw [rightMirrorCrossingPositions, Finset.mem_filter, mem_toFinset]
          exact ⟨⟨le_trans hcross.1.le (le_trans hlow_ge_k hlo), hhi⟩,
            le_trans hlow_ge_k hlo, hlo⟩
        · simp [e]
    have hcard_map :
        ((rightMirrorCrossingPositions k I).map e).card =
          (rightMirrorCrossingPositions k I).card :=
      Finset.card_map e
    rw [hmap] at hcard_map
    rw [← hcard_map, crossOrder_eq_min_of_crossing hcross]
    have hmin : Nat.min (k - I.lo) (I.hi + 1 - k) = k - I.lo :=
      Nat.min_eq_left hle
    rw [hmin]
    simp
    omega
  · have hle' : I.hi + 1 - k < k - I.lo := Nat.lt_of_not_ge hle
    have hmap :
        (rightMirrorCrossingPositions k I).map e = Finset.Icc k I.hi := by
      ext n
      constructor
      · intro hn
        rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
        rw [rightMirrorCrossingPositions, Finset.mem_filter, mem_toFinset] at hp
        simp [e] at hpval
        subst n
        exact Finset.mem_Icc.mpr ⟨hp.2.1, hp.1.2⟩
      · intro hn
        rcases Finset.mem_Icc.mp hn with ⟨hk, hhi⟩
        have hthreshold_le_k : I.lo + I.hi + 1 - k ≤ k := by omega
        have hnlt : n < 2 * k := lt_of_le_of_lt hhi I.hi_lt
        refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
        · rw [rightMirrorCrossingPositions, Finset.mem_filter, mem_toFinset]
          exact ⟨⟨le_trans hcross.1.le hk, hhi⟩, hk, le_trans hthreshold_le_k hk⟩
        · simp [e]
    have hcard_map :
        ((rightMirrorCrossingPositions k I).map e).card =
          (rightMirrorCrossingPositions k I).card :=
      Finset.card_map e
    rw [hmap] at hcard_map
    rw [← hcard_map, crossOrder_eq_min_of_crossing hcross]
    have hmin : Nat.min (k - I.lo) (I.hi + 1 - k) = I.hi + 1 - k :=
      Nat.min_eq_right hle'.le
    rw [hmin]
    simp

/-- Positions in `I` whose interval mirror crosses the middle barrier. -/
noncomputable def mirrorCrossingPositions (k : ℕ) (I : PositionInterval (2 * k)) :
    Finset (Fin (2 * k)) :=
  leftMirrorCrossingPositions k I ∪ rightMirrorCrossingPositions k I

theorem left_right_mirrorCrossingPositions_disjoint {k : ℕ}
    (I : PositionInterval (2 * k)) :
    Disjoint (leftMirrorCrossingPositions k I) (rightMirrorCrossingPositions k I) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp_left hp_right
  rw [leftMirrorCrossingPositions, Finset.mem_filter] at hp_left
  rw [rightMirrorCrossingPositions, Finset.mem_filter] at hp_right
  exact not_lt_of_ge hp_right.2.1 hp_left.2.1

theorem mirrorCrossingPositions_card_eq_two_mul_crossOrder_of_crossing {k : ℕ}
    (I : PositionInterval (2 * k)) (hcross : I.lo < k ∧ k ≤ I.hi) :
    (mirrorCrossingPositions k I).card = 2 * I.crossOrder k := by
  classical
  rw [mirrorCrossingPositions, Finset.card_union_of_disjoint
    (left_right_mirrorCrossingPositions_disjoint I)]
  rw [leftMirrorCrossingPositions_card_eq_crossOrder_of_crossing I hcross,
    rightMirrorCrossingPositions_card_eq_crossOrder_of_crossing I hcross]
  omega

theorem crossOrder_eq_min_side_cards_of_crossing {k : ℕ} (I : PositionInterval (2 * k))
    (hcross : I.lo < k ∧ k ≤ I.hi) :
    I.crossOrder k =
      Nat.min
        (I.toFinset.filter fun p => p.val < k).card
        (I.toFinset.filter fun p => k ≤ p.val).card := by
  rw [crossOrder_eq_min_of_crossing hcross,
    left_of_middle_card_of_crossing I hcross,
    right_of_middle_card_of_crossing I hcross]

theorem crossOrder_le_left {k : ℕ} (I : PositionInterval (2 * k)) :
    I.crossOrder k ≤ k - I.lo := by
  by_cases h : I.lo < k ∧ k ≤ I.hi
  · rw [crossOrder_eq_min_of_crossing h]
    exact Nat.min_le_left _ _
  · rw [crossOrder_eq_zero_of_not_crossing h]
    omega

theorem crossOrder_le_right {k : ℕ} (I : PositionInterval (2 * k)) :
    I.crossOrder k ≤ I.hi + 1 - k := by
  by_cases h : I.lo < k ∧ k ≤ I.hi
  · rw [crossOrder_eq_min_of_crossing h]
    exact Nat.min_le_right _ _
  · rw [crossOrder_eq_zero_of_not_crossing h]
    omega

theorem eq_full_of_crossOrder_eq_middle {k : ℕ} (I : PositionInterval (2 * k))
    (hk : 0 < k) (horder : I.crossOrder k = k) :
    I.lo = 0 ∧ I.hi = 2 * k - 1 := by
  have hleft := I.crossOrder_le_left
  have hright := I.crossOrder_le_right
  have hhi := I.hi_lt
  rw [horder] at hleft hright
  omega

/-- The `crossOrder` positions immediately to the left of the middle barrier inside `I`. -/
noncomputable def leftCentralPositions (k : ℕ) (I : PositionInterval (2 * k)) :
    Finset (Fin (2 * k)) := by
  classical
  exact I.toFinset.filter fun p => k - I.crossOrder k ≤ p.val ∧ p.val < k

/-- The `crossOrder` positions immediately to the right of the middle barrier inside `I`. -/
noncomputable def rightCentralPositions (k : ℕ) (I : PositionInterval (2 * k)) :
    Finset (Fin (2 * k)) := by
  classical
  exact I.toFinset.filter fun p => k ≤ p.val ∧ p.val < k + I.crossOrder k

theorem mem_leftCentralPositions {k : ℕ} {I : PositionInterval (2 * k)}
    {p : Fin (2 * k)} :
    p ∈ I.leftCentralPositions k ↔
      I.Mem p ∧ k - I.crossOrder k ≤ p.val ∧ p.val < k := by
  simp [leftCentralPositions, mem_toFinset]

theorem mem_rightCentralPositions {k : ℕ} {I : PositionInterval (2 * k)}
    {p : Fin (2 * k)} :
    p ∈ I.rightCentralPositions k ↔
      I.Mem p ∧ k ≤ p.val ∧ p.val < k + I.crossOrder k := by
  simp [rightCentralPositions, mem_toFinset]

/-- The `d` positions immediately to the left of the middle barrier. -/
noncomputable def leftBarrierPositions (k d : ℕ) : Finset (Fin (2 * k)) := by
  classical
  exact Finset.univ.filter fun p => k - d ≤ p.val ∧ p.val < k

/-- The `d` positions immediately to the right of the middle barrier. -/
noncomputable def rightBarrierPositions (k d : ℕ) : Finset (Fin (2 * k)) := by
  classical
  exact Finset.univ.filter fun p => k ≤ p.val ∧ p.val < k + d

/-- The `2d` positions centered at the middle barrier. -/
noncomputable def centralBarrierPositions (k d : ℕ) : Finset (Fin (2 * k)) :=
  leftBarrierPositions k d ∪ rightBarrierPositions k d

theorem mem_leftBarrierPositions {k d : ℕ} {p : Fin (2 * k)} :
    p ∈ leftBarrierPositions k d ↔ k - d ≤ p.val ∧ p.val < k := by
  simp [leftBarrierPositions]

theorem mem_rightBarrierPositions {k d : ℕ} {p : Fin (2 * k)} :
    p ∈ rightBarrierPositions k d ↔ k ≤ p.val ∧ p.val < k + d := by
  simp [rightBarrierPositions]

theorem mem_centralBarrierPositions {k d : ℕ} {p : Fin (2 * k)} :
    p ∈ centralBarrierPositions k d ↔
      (k - d ≤ p.val ∧ p.val < k) ∨ (k ≤ p.val ∧ p.val < k + d) := by
  simp [centralBarrierPositions, mem_leftBarrierPositions, mem_rightBarrierPositions]

theorem left_rightBarrierPositions_disjoint {k d : ℕ} :
    Disjoint (leftBarrierPositions k d) (rightBarrierPositions k d) := by
  rw [Finset.disjoint_left]
  intro p hp_left hp_right
  rw [mem_leftBarrierPositions] at hp_left
  rw [mem_rightBarrierPositions] at hp_right
  omega

theorem leftBarrierPositions_card_eq {k d : ℕ} (hd : d ≤ k) :
    (leftBarrierPositions k d).card = d := by
  classical
  let e : Fin (2 * k) ↪ ℕ := ⟨Fin.val, by intro a b h; exact Fin.ext h⟩
  have hmap :
      (leftBarrierPositions k d).map e = Finset.Ico (k - d) k := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
      rw [mem_leftBarrierPositions] at hp
      simp [e] at hpval
      subst n
      exact Finset.mem_Ico.mpr hp
    · intro hn
      rcases Finset.mem_Ico.mp hn with ⟨hlo, hhi⟩
      have hnlt : n < 2 * k := lt_trans hhi (by omega : k < 2 * k)
      refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
      · rw [mem_leftBarrierPositions]
        exact ⟨hlo, hhi⟩
      · simp [e]
  have hcard_map : ((leftBarrierPositions k d).map e).card =
      (leftBarrierPositions k d).card := Finset.card_map e
  rw [hmap] at hcard_map
  rw [← hcard_map]
  simp
  omega

theorem rightBarrierPositions_card_eq {k d : ℕ} (hd : d ≤ k) :
    (rightBarrierPositions k d).card = d := by
  classical
  let e : Fin (2 * k) ↪ ℕ := ⟨Fin.val, by intro a b h; exact Fin.ext h⟩
  have hmap :
      (rightBarrierPositions k d).map e = Finset.Ico k (k + d) := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
      rw [mem_rightBarrierPositions] at hp
      simp [e] at hpval
      subst n
      exact Finset.mem_Ico.mpr hp
    · intro hn
      rcases Finset.mem_Ico.mp hn with ⟨hlo, hhi⟩
      have hnlt : n < 2 * k := by omega
      refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
      · rw [mem_rightBarrierPositions]
        exact ⟨hlo, hhi⟩
      · simp [e]
  have hcard_map : ((rightBarrierPositions k d).map e).card =
      (rightBarrierPositions k d).card := Finset.card_map e
  rw [hmap] at hcard_map
  rw [← hcard_map]
  simp

theorem centralBarrierPositions_card_eq {k d : ℕ} (hd : d ≤ k) :
    (centralBarrierPositions k d).card = 2 * d := by
  rw [centralBarrierPositions, Finset.card_union_of_disjoint left_rightBarrierPositions_disjoint]
  rw [leftBarrierPositions_card_eq hd, rightBarrierPositions_card_eq hd]
  omega

theorem leftBarrierPositions_mono {k d e : ℕ} (hde : d ≤ e) :
    leftBarrierPositions k d ⊆ leftBarrierPositions k e := by
  intro p hp
  rw [mem_leftBarrierPositions] at hp ⊢
  omega

theorem rightBarrierPositions_mono {k d e : ℕ} (hde : d ≤ e) :
    rightBarrierPositions k d ⊆ rightBarrierPositions k e := by
  intro p hp
  rw [mem_rightBarrierPositions] at hp ⊢
  omega

theorem centralBarrierPositions_mono {k d e : ℕ} (hde : d ≤ e) :
    centralBarrierPositions k d ⊆ centralBarrierPositions k e := by
  intro p hp
  rw [mem_centralBarrierPositions] at hp ⊢
  rcases hp with hp | hp
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem pred_mem_centralBarrierPositions_of_mem_pred {k d : ℕ}
    {p : Fin (2 * k)} (hp : p ∈ centralBarrierPositions k (d - 1))
    (hp_pos : 0 < p.val) :
    (⟨p.val - 1, by omega⟩ : Fin (2 * k)) ∈ centralBarrierPositions k d := by
  rw [mem_centralBarrierPositions] at hp ⊢
  rcases hp with hp | hp
  · refine Or.inl ?_
    change k - d ≤ p.val - 1 ∧ p.val - 1 < k
    omega
  · by_cases hpk : p.val = k
    · refine Or.inl ?_
      change k - d ≤ p.val - 1 ∧ p.val - 1 < k
      omega
    · refine Or.inr ?_
      change k ≤ p.val - 1 ∧ p.val - 1 < k + d
      omega

theorem succ_mem_centralBarrierPositions_of_mem_pred {k d : ℕ}
    {p : Fin (2 * k)} (hp : p ∈ centralBarrierPositions k (d - 1))
    (hp_succ : p.val + 1 < 2 * k) :
    (⟨p.val + 1, hp_succ⟩ : Fin (2 * k)) ∈ centralBarrierPositions k d := by
  rw [mem_centralBarrierPositions] at hp ⊢
  rcases hp with hp | hp
  · by_cases hpk : p.val + 1 = k
    · refine Or.inr ?_
      change k ≤ p.val + 1 ∧ p.val + 1 < k + d
      omega
    · refine Or.inl ?_
      change k - d ≤ p.val + 1 ∧ p.val + 1 < k
      omega
  · refine Or.inr ?_
    change k ≤ p.val + 1 ∧ p.val + 1 < k + d
    omega

theorem leftCentralPositions_eq_leftBarrierPositions_of_crossing {k : ℕ}
    (I : PositionInterval (2 * k)) (hcross : I.lo < k ∧ k ≤ I.hi) :
    I.leftCentralPositions k = leftBarrierPositions k (I.crossOrder k) := by
  ext p
  rw [mem_leftCentralPositions, mem_leftBarrierPositions]
  constructor
  · intro hp
    exact hp.2
  · intro hp
    have horder_le_left : I.crossOrder k ≤ k - I.lo := I.crossOrder_le_left
    have hlo : I.lo ≤ p.val := by omega
    have hhi : p.val ≤ I.hi := le_trans hp.2.le hcross.2
    exact ⟨⟨hlo, hhi⟩, hp⟩

theorem rightCentralPositions_eq_rightBarrierPositions_of_crossing {k : ℕ}
    (I : PositionInterval (2 * k)) (hcross : I.lo < k ∧ k ≤ I.hi) :
    I.rightCentralPositions k = rightBarrierPositions k (I.crossOrder k) := by
  ext p
  rw [mem_rightCentralPositions, mem_rightBarrierPositions]
  constructor
  · intro hp
    exact hp.2
  · intro hp
    have horder_le_right : I.crossOrder k ≤ I.hi + 1 - k := I.crossOrder_le_right
    have hlo : I.lo ≤ p.val := le_trans hcross.1.le hp.1
    have hhi : p.val ≤ I.hi := by omega
    exact ⟨⟨hlo, hhi⟩, hp⟩

theorem leftCentralPositions_card_eq_crossOrder {k : ℕ} (I : PositionInterval (2 * k)) :
    (I.leftCentralPositions k).card = I.crossOrder k := by
  classical
  let e : Fin (2 * k) ↪ ℕ := ⟨Fin.val, by intro a b h; exact Fin.ext h⟩
  have hmap :
      (I.leftCentralPositions k).map e =
        Finset.Ico (k - I.crossOrder k) k := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
      rw [mem_leftCentralPositions] at hp
      simp [e] at hpval
      subst n
      exact Finset.mem_Ico.mpr ⟨hp.2.1, hp.2.2⟩
    · intro hn
      rcases Finset.mem_Ico.mp hn with ⟨hlo, hnlt_k⟩
      have hnlt : n < 2 * k := lt_trans hnlt_k (by omega : k < 2 * k)
      refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
      · rw [mem_leftCentralPositions]
        by_cases hcross : I.lo < k ∧ k ≤ I.hi
        · have horder_le_left : I.crossOrder k ≤ k - I.lo := I.crossOrder_le_left
          have hloI : I.lo ≤ n := by omega
          have hhiI : n ≤ I.hi := le_trans hnlt_k.le hcross.2
          exact ⟨⟨hloI, hhiI⟩, hlo, hnlt_k⟩
        · have hzero : I.crossOrder k = 0 :=
            PositionInterval.crossOrder_eq_zero_of_not_crossing hcross
          exfalso
          rw [hzero] at hlo
          omega
      · simp [e]
  have hcard_map : ((I.leftCentralPositions k).map e).card =
      (I.leftCentralPositions k).card := Finset.card_map e
  rw [hmap] at hcard_map
  rw [← hcard_map]
  by_cases hzero : I.crossOrder k = 0
  · simp [hzero]
  · have hpos : 0 < I.crossOrder k := by omega
    have hle : I.crossOrder k ≤ k := le_trans I.crossOrder_le_left (by omega)
    simp
    omega

theorem rightCentralPositions_card_eq_crossOrder {k : ℕ} (I : PositionInterval (2 * k)) :
    (I.rightCentralPositions k).card = I.crossOrder k := by
  classical
  let e : Fin (2 * k) ↪ ℕ := ⟨Fin.val, by intro a b h; exact Fin.ext h⟩
  have hmap :
      (I.rightCentralPositions k).map e =
        Finset.Ico k (k + I.crossOrder k) := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
      rw [mem_rightCentralPositions] at hp
      simp [e] at hpval
      subst n
      exact Finset.mem_Ico.mpr ⟨hp.2.1, hp.2.2⟩
    · intro hn
      rcases Finset.mem_Ico.mp hn with ⟨hk, hnlt_order⟩
      have hnlt : n < 2 * k := by
        have horder_le_k : I.crossOrder k ≤ k := by
          by_cases hcross : I.lo < k ∧ k ≤ I.hi
          · exact le_trans I.crossOrder_le_right (by
              have hhi2 : I.hi < 2 * k := I.hi_lt
              omega)
          · rw [PositionInterval.crossOrder_eq_zero_of_not_crossing hcross]
            omega
        omega
      refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
      · rw [mem_rightCentralPositions]
        by_cases hcross : I.lo < k ∧ k ≤ I.hi
        · have horder_le_right : I.crossOrder k ≤ I.hi + 1 - k := I.crossOrder_le_right
          have hloI : I.lo ≤ n := le_trans hcross.1.le hk
          have hhiI : n ≤ I.hi := by omega
          exact ⟨⟨hloI, hhiI⟩, hk, hnlt_order⟩
        · have hzero : I.crossOrder k = 0 :=
            PositionInterval.crossOrder_eq_zero_of_not_crossing hcross
          exfalso
          rw [hzero] at hnlt_order
          omega
      · simp [e]
  have hcard_map : ((I.rightCentralPositions k).map e).card =
      (I.rightCentralPositions k).card := Finset.card_map e
  rw [hmap] at hcard_map
  rw [← hcard_map]
  by_cases hzero : I.crossOrder k = 0
  · simp [hzero]
  · simp

theorem crossOrder_pos_iff {k : ℕ} (I : PositionInterval (2 * k)) :
    0 < I.crossOrder k ↔ I.lo < k ∧ k ≤ I.hi := by
  constructor
  · intro hpos
    by_contra hcross
    have hzero := crossOrder_eq_zero_of_not_crossing (I := I) hcross
    omega
  · intro hcross
    rw [crossOrder_eq_min_of_crossing hcross]
    have hleft : 0 < k - I.lo := by omega
    have hright : 0 < I.hi + 1 - k := by omega
    exact Nat.lt_min.mpr ⟨hleft, hright⟩

theorem two_mul_crossOrder_le_length {k : ℕ} (I : PositionInterval (2 * k)) :
    2 * I.crossOrder k ≤ I.length := by
  by_cases h : I.lo < k ∧ k ≤ I.hi
  · rw [crossOrder_eq_min_of_crossing h]
    have hleft : Nat.min (k - I.lo) (I.hi + 1 - k) ≤ k - I.lo :=
      Nat.min_le_left _ _
    have hright : Nat.min (k - I.lo) (I.hi + 1 - k) ≤ I.hi + 1 - k :=
      Nat.min_le_right _ _
    have hlen : I.length = (k - I.lo) + (I.hi + 1 - k) := by
      dsimp [length]
      omega
    rw [hlen]
    omega
  · rw [crossOrder_eq_zero_of_not_crossing h]
    omega

theorem exists_two_mem_of_two_le_length {N : ℕ} (I : PositionInterval N)
    (hlen : 2 ≤ I.length) :
    ∃ p q : Fin N, I.Mem p ∧ I.Mem q ∧ p ≠ q := by
  let p : Fin N := ⟨I.lo, lt_of_le_of_lt I.lo_le_hi I.hi_lt⟩
  have hlo_succ_le_hi : I.lo + 1 ≤ I.hi := by
    dsimp [length] at hlen
    omega
  let q : Fin N := ⟨I.lo + 1, lt_of_le_of_lt hlo_succ_le_hi I.hi_lt⟩
  refine ⟨p, q, ?_, ?_, ?_⟩
  · dsimp [p, Mem]
    omega
  · dsimp [q, Mem]
    omega
  · intro hpq
    have hval := congrArg Fin.val hpq
    dsimp [p, q] at hval
    omega

end PositionInterval

/--
A simultaneous move reverses several pairwise-disjoint consecutive blocks.
The actual permutation is kept as data; later lemmas prove its middle-barrier
crossing count from the block fields.
-/
structure BlockMove (N : ℕ) where
  blockCount : ℕ
  blockCount_pos : 0 < blockCount
  block : Fin blockCount → PositionInterval N
  pairwise_disjoint :
    ((Finset.univ : Finset (Fin blockCount)) : Set (Fin blockCount)).PairwiseDisjoint
      (fun i => (block i).toSet)
  nontrivial : ∀ i : Fin blockCount, 2 ≤ (block i).length
  map : State N

namespace BlockMove

/-- Two positions lie in the same reversed block of a block move. -/
def SameBlock {N : ℕ} (M : BlockMove N) (p q : Fin N) : Prop :=
  ∃ b : Fin M.blockCount, (M.block b).Mem p ∧ (M.block b).Mem q

/--
Semantic predicate for a block move: inside each block the map is the interval
mirror, and outside all blocks it fixes positions.
-/
def ReversesBlocks {N : ℕ} (M : BlockMove N) : Prop :=
  (∀ i : Fin M.blockCount, ∀ p : Fin N, ∀ hp : (M.block i).Mem p,
    M.map p = (M.block i).mirror p hp) ∧
  ∀ p : Fin N, (∀ i : Fin M.blockCount, ¬ (M.block i).Mem p) → M.map p = p

theorem map_mem_of_reversesBlocks {N : ℕ} {M : BlockMove N}
    (hM : M.ReversesBlocks) {i : Fin M.blockCount} {p : Fin N}
    (hp : (M.block i).Mem p) :
    (M.block i).Mem (M.map p) := by
  rw [hM.1 i p hp]
  exact (M.block i).mirror_mem p hp

theorem map_map_eq_of_reversesBlocks_mem {N : ℕ} {M : BlockMove N}
    (hM : M.ReversesBlocks) {i : Fin M.blockCount} {p : Fin N}
    (hp : (M.block i).Mem p) :
    M.map (M.map p) = p := by
  have hmap : M.map p = (M.block i).mirror p hp := hM.1 i p hp
  have hpmap : (M.block i).Mem (M.map p) := map_mem_of_reversesBlocks hM hp
  have hvalmap : (M.map p).val = (M.block i).lo + (M.block i).hi - p.val :=
    congrArg Fin.val hmap
  apply Fin.ext
  rw [hM.1 i (M.map p) hpmap]
  dsimp [PositionInterval.mirror]
  rcases hp with ⟨hlo, hhi⟩
  omega

theorem map_map_eq_of_reversesBlocks {N : ℕ} {M : BlockMove N}
    (hM : M.ReversesBlocks) (p : Fin N) :
    M.map (M.map p) = p := by
  classical
  by_cases hp : ∃ i : Fin M.blockCount, (M.block i).Mem p
  · rcases hp with ⟨i, hi⟩
    exact map_map_eq_of_reversesBlocks_mem hM hi
  · have hfix : M.map p = p := hM.2 p (by
      intro i
      exact fun hi => hp ⟨i, hi⟩)
    rw [hfix]
    exact hfix

theorem map_middleLeft_iff_of_reversesBlocks_no_crossing {k : ℕ}
    {M : BlockMove (2 * k)} (hM : M.ReversesBlocks)
    (hnone : ∀ i : Fin M.blockCount, ¬ ((M.block i).lo < k ∧ k ≤ (M.block i).hi))
    (p : Fin (2 * k)) :
    middleLeft k (M.map p) ↔ middleLeft k p := by
  classical
  by_cases hp : ∃ i : Fin M.blockCount, (M.block i).Mem p
  · rcases hp with ⟨i, hpi⟩
    have hmap : M.map p = (M.block i).mirror p hpi := hM.1 i p hpi
    rw [hmap]
    rcases hpi with ⟨hlo, hhi⟩
    have hnot := hnone i
    simp [middleLeft, PositionInterval.mirror]
    omega
  · have hfix : M.map p = p := hM.2 p (by
      intro i
      exact fun hpi => hp ⟨i, hpi⟩)
    rw [hfix]

theorem pairwise_disjoint_toFinset {N : ℕ} (M : BlockMove N) :
    ((Finset.univ : Finset (Fin M.blockCount)) : Set (Fin M.blockCount)).PairwiseDisjoint
      (fun i => (M.block i).toFinset) := by
  classical
  intro i _hi j _hj hij
  change Disjoint (M.block i).toFinset (M.block j).toFinset
  rw [Finset.disjoint_left]
  intro p hpi hpj
  have hset_dis : Disjoint ((M.block i).toSet) ((M.block j).toSet) :=
    M.pairwise_disjoint (by simp) (by simp) hij
  have hpi_set : p ∈ (M.block i).toSet := by
    simpa [PositionInterval.toSet, PositionInterval.mem_toFinset] using hpi
  have hpj_set : p ∈ (M.block j).toSet := by
    simpa [PositionInterval.toSet, PositionInterval.mem_toFinset] using hpj
  exact hset_dis.le_bot ⟨hpi_set, hpj_set⟩

/-- Pairwise-disjoint blocks in `Fin N` have total length at most `N`. -/
theorem sum_block_lengths_le {N : ℕ} (M : BlockMove N) :
    (∑ i : Fin M.blockCount, (M.block i).length) ≤ N := by
  classical
  have hcard :
      ((Finset.univ : Finset (Fin M.blockCount)).biUnion
        (fun i => (M.block i).toFinset)).card =
        ∑ i : Fin M.blockCount, ((M.block i).toFinset).card := by
    simpa using
      (Finset.card_biUnion (s := (Finset.univ : Finset (Fin M.blockCount)))
        (t := fun i => (M.block i).toFinset) M.pairwise_disjoint_toFinset)
  have hle :
      ((Finset.univ : Finset (Fin M.blockCount)).biUnion
        (fun i => (M.block i).toFinset)).card ≤ N := by
    simpa [Fintype.card_fin] using
      (((Finset.univ : Finset (Fin M.blockCount)).biUnion
        (fun i => (M.block i).toFinset)).card_le_univ)
  rw [hcard] at hle
  simpa [PositionInterval.toFinset_card] using hle

/-- In a disjoint block move, at most one block can cross the middle barrier. -/
theorem crossing_blocks_eq {k : ℕ} (M : BlockMove (2 * k))
    {i j : Fin M.blockCount}
    (hi : (M.block i).lo < k ∧ k ≤ (M.block i).hi)
    (hj : (M.block j).lo < k ∧ k ≤ (M.block j).hi) :
    i = j := by
  by_contra hij
  have hklt : k < 2 * k := lt_of_le_of_lt hi.2 (M.block i).hi_lt
  let p : Fin (2 * k) := ⟨k, hklt⟩
  have hpi : p ∈ (M.block i).toSet := by
    exact ⟨hi.1.le, hi.2⟩
  have hpj : p ∈ (M.block j).toSet := by
    exact ⟨hj.1.le, hj.2⟩
  have hdis : Disjoint ((M.block i).toSet) ((M.block j).toSet) :=
    M.pairwise_disjoint (by simp) (by simp) hij
  exact hdis.le_bot ⟨hpi, hpj⟩

end BlockMove

/-! ### BlockMove from level function -/

noncomputable def levelBlockMoveInterval {N : ℕ} (g : Fin N → ℝ) (p : Fin N)
    (hp : (levelBlockLo g p).val < (levelBlockHi g p).val) :
    PositionInterval N where
  lo := (levelBlockLo g p).val
  hi := (levelBlockHi g p).val
  lo_le_hi := le_of_lt hp
  hi_lt := (levelBlockHi g p).isLt

theorem levelBlockMoveInterval_nontrivial {N : ℕ} {g : Fin N → ℝ} {p : Fin N}
    (hp : (levelBlockLo g p).val < (levelBlockHi g p).val) :
    2 ≤ (levelBlockMoveInterval g p hp).hi - (levelBlockMoveInterval g p hp).lo + 1 := by
  simp [levelBlockMoveInterval]; omega

theorem levelBlockMoveInterval_disjoint {N : ℕ} {g : Fin N → ℝ} (hg : Monotone g)
    {p q : Fin N}
    (hp : (levelBlockLo g p).val < (levelBlockHi g p).val)
    (hq : (levelBlockLo g q).val < (levelBlockHi g q).val)
    (hne : g p ≠ g q) :
    Disjoint (levelBlockMoveInterval g p hp).toSet (levelBlockMoveInterval g q hq).toSet := by
  intro S hSp hSq
  simp only [Set.le_eq_subset, Set.bot_eq_empty, Set.subset_empty_iff]
  ext x; simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hxp := hSp hx
  have hxq := hSq hx
  simp [PositionInterval.toSet, PositionInterval.Mem, levelBlockMoveInterval] at hxp hxq
  have h1 := monotone_levelBlock_eq hg (Fin.le_def.mpr hxp.1) (Fin.le_def.mpr hxp.2)
  have h2 := monotone_levelBlock_eq hg (Fin.le_def.mpr hxq.1) (Fin.le_def.mpr hxq.2)
  exact hne (h1.symm.trans h2)

/--
One legal step of a generalized allowable sequence.  The increasing-block
condition is the finite Goodman--Pollack/Ungar rule before reversal.
-/
structure ReversalStep (k : ℕ) (π ρ : State (2 * k)) where
  move : BlockMove (2 * k)
  step_apply : ∀ p : Fin (2 * k), ρ p = π (move.map p)
  increasing_before :
    ∀ i : Fin move.blockCount,
      StrictMonoOn (fun p : Fin (2 * k) => (π p).val) ((move.block i).toSet)

namespace ReversalStep

/-- The total middle-barrier order of a reversal step. -/
def order {k : ℕ} {π ρ : State (2 * k)} (M : ReversalStep k π ρ) : ℕ :=
  ∑ i : Fin M.move.blockCount, (M.move.block i).crossOrder k

/-- A reversal step is crossing exactly when its total order is positive. -/
def IsCrossing {k : ℕ} {π ρ : State (2 * k)} (M : ReversalStep k π ρ) : Prop :=
  0 < M.order

theorem label_decreases_after_block_of_reversesBlocks {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (i : Fin M.move.blockCount)
    {p q : Fin (2 * k)} (hp : (M.move.block i).Mem p) (hq : (M.move.block i).Mem q)
    (hpq : p < q) :
    (ρ q).val < (ρ p).val := by
  have hmirror_lt :
      (M.move.block i).mirror q hq < (M.move.block i).mirror p hp :=
    (M.move.block i).mirror_strictAnti hp hq hpq
  have hmono :=
    M.increasing_before i ((M.move.block i).mirror_mem q hq)
      ((M.move.block i).mirror_mem p hp) hmirror_lt
  rw [M.step_apply q, M.step_apply p]
  rw [hrev.1 i q hq, hrev.1 i p hp]
  exact hmono

/-- A state is strictly decreasing on a finite set of positions. -/
def DecreasingOnPositions {N : ℕ} (π : State N) (s : Finset (Fin N)) : Prop :=
  ∀ ⦃p⦄, p ∈ s → ∀ ⦃q⦄, q ∈ s → p < q → (π q).val < (π p).val

/-- A state is strictly increasing on a finite set of positions. -/
def IncreasingOnPositions {N : ℕ} (π : State N) (s : Finset (Fin N)) : Prop :=
  ∀ ⦃p⦄, p ∈ s → ∀ ⦃q⦄, q ∈ s → p < q → (π p).val < (π q).val

theorem DecreasingOnPositions.mono {N : ℕ} {π : State N} {s t : Finset (Fin N)}
    (hdec : DecreasingOnPositions π t) (hst : s ⊆ t) :
    DecreasingOnPositions π s := by
  intro p hp q hq hpq
  exact hdec (hst hp) (hst hq) hpq

theorem IncreasingOnPositions.mono {N : ℕ} {π : State N} {s t : Finset (Fin N)}
    (hinc : IncreasingOnPositions π t) (hst : s ⊆ t) :
    IncreasingOnPositions π s := by
  intro p hp q hq hpq
  exact hinc (hst hp) (hst hq) hpq

theorem state_eq_refl_of_increasingOn_univ {N : ℕ} {π : State N}
    (hinc : IncreasingOnPositions π Finset.univ) :
    π = Equiv.refl (Fin N) := by
  apply Equiv.ext
  intro p
  have hmono : StrictMono (fun x : Fin N => π x) := by
    intro a b hab
    change (π a).val < (π b).val
    exact hinc (by simp) (by simp) hab
  have hπ :
      (fun x : Fin N => π x) =
        (Finset.univ : Finset (Fin N)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin N)))
      (k := N) (by simp) (fun _ => by simp) hmono
  have hid :
      (fun x : Fin N => x) =
        (Finset.univ : Finset (Fin N)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin N)))
      (k := N) (by simp) (fun _ => by simp) (by intro a b hab; exact hab)
  have hfun : (fun x : Fin N => π x) = fun x : Fin N => x := hπ.trans hid.symm
  exact congrFun hfun p

theorem state_eq_reverseFin_of_decreasingOn_univ {N : ℕ} {π : State N}
    (hdec : DecreasingOnPositions π Finset.univ) :
    π = reverseFin N := by
  apply Equiv.ext
  intro p
  have hmono : StrictMono (fun x : Fin N => π (Fin.rev x)) := by
    intro a b hab
    have hrev : Fin.rev b < Fin.rev a := by
      rw [← Fin.rev_lt_rev]
      simpa using hab
    change (π (Fin.rev a)).val < (π (Fin.rev b)).val
    exact hdec (by simp) (by simp) hrev
  have hπ :
      (fun x : Fin N => π (Fin.rev x)) =
        (Finset.univ : Finset (Fin N)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin N)))
      (k := N) (by simp) (fun _ => by simp) hmono
  have hid :
      (fun x : Fin N => x) =
        (Finset.univ : Finset (Fin N)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin N)))
      (k := N) (by simp) (fun _ => by simp) (by intro a b hab; exact hab)
  have hfun : (fun x : Fin N => π (Fin.rev x)) = fun x : Fin N => x :=
    hπ.trans hid.symm
  have hp := congrFun hfun (Fin.rev p)
  simpa [reverseFin] using hp

def middleLeftPosition (k : ℕ) (hk : 0 < k) : Fin (2 * k) :=
  ⟨k - 1, by omega⟩

def middleRightPosition (k : ℕ) (hk : 0 < k) : Fin (2 * k) :=
  ⟨k, by omega⟩

def leftOffsetPosition (k s : ℕ) (hs : s < k) : Fin (2 * k) :=
  ⟨k - 1 - s, by omega⟩

def rightOffsetPosition (k s : ℕ) (_hs : s < k) : Fin (2 * k) :=
  ⟨k + s, by omega⟩

def MiddlePairIncreasing (π : State (2 * k)) (hk : 0 < k) : Prop :=
  (π (middleLeftPosition k hk)).val < (π (middleRightPosition k hk)).val

def MiddlePairDecreasing (π : State (2 * k)) (hk : 0 < k) : Prop :=
  (π (middleRightPosition k hk)).val < (π (middleLeftPosition k hk)).val

def OffsetPairIncreasing (π : State (2 * k)) (s : ℕ) (hs : s < k) : Prop :=
  (π (leftOffsetPosition k s hs)).val < (π (rightOffsetPosition k s hs)).val

def OffsetPairDecreasing (π : State (2 * k)) (s : ℕ) (hs : s < k) : Prop :=
  (π (rightOffsetPosition k s hs)).val < (π (leftOffsetPosition k s hs)).val

theorem middlePair_increasing_or_decreasing {k : ℕ} (π : State (2 * k)) (hk : 0 < k) :
    MiddlePairIncreasing π hk ∨ MiddlePairDecreasing π hk := by
  have hpos_ne : middleLeftPosition k hk ≠ middleRightPosition k hk := by
    intro h
    have hval := congrArg Fin.val h
    change k - 1 = k at hval
    omega
  have hlabel_ne :
      (π (middleLeftPosition k hk)).val ≠ (π (middleRightPosition k hk)).val := by
    intro hval
    have hlabel_eq :
        π (middleLeftPosition k hk) = π (middleRightPosition k hk) := Fin.ext hval
    exact hpos_ne (π.injective hlabel_eq)
  rcases lt_or_gt_of_ne hlabel_ne with hlt | hgt
  · exact Or.inl hlt
  · exact Or.inr hgt

theorem offsetPair_increasing_or_decreasing {k s : ℕ} (π : State (2 * k))
    (hs : s < k) :
    OffsetPairIncreasing π s hs ∨ OffsetPairDecreasing π s hs := by
  have hpos_ne : leftOffsetPosition k s hs ≠ rightOffsetPosition k s hs := by
    intro h
    have hval := congrArg Fin.val h
    change k - 1 - s = k + s at hval
    omega
  have hlabel_ne :
      (π (leftOffsetPosition k s hs)).val ≠
        (π (rightOffsetPosition k s hs)).val := by
    intro hval
    have hlabel_eq :
        π (leftOffsetPosition k s hs) = π (rightOffsetPosition k s hs) := Fin.ext hval
    exact hpos_ne (π.injective hlabel_eq)
  rcases lt_or_gt_of_ne hlabel_ne with hlt | hgt
  · exact Or.inl hlt
  · exact Or.inr hgt

theorem not_middlePair_increasing_and_decreasing {k : ℕ}
    {π : State (2 * k)} (hk : 0 < k) :
    ¬ (MiddlePairIncreasing π hk ∧ MiddlePairDecreasing π hk) := by
  rintro ⟨hinc, hdec⟩
  change (π (middleLeftPosition k hk)).val < (π (middleRightPosition k hk)).val at hinc
  change (π (middleRightPosition k hk)).val < (π (middleLeftPosition k hk)).val at hdec
  omega

theorem not_offsetPair_increasing_and_decreasing {k s : ℕ}
    {π : State (2 * k)} (hs : s < k) :
    ¬ (OffsetPairIncreasing π s hs ∧ OffsetPairDecreasing π s hs) := by
  rintro ⟨hinc, hdec⟩
  change (π (leftOffsetPosition k s hs)).val <
      (π (rightOffsetPosition k s hs)).val at hinc
  change (π (rightOffsetPosition k s hs)).val <
      (π (leftOffsetPosition k s hs)).val at hdec
  omega

theorem middlePair_decreasing_of_not_increasing {k : ℕ}
    {π : State (2 * k)} (hk : 0 < k)
    (hnot : ¬ MiddlePairIncreasing π hk) :
    MiddlePairDecreasing π hk := by
  rcases middlePair_increasing_or_decreasing π hk with hinc | hdec
  · exact False.elim (hnot hinc)
  · exact hdec

theorem offsetPair_decreasing_of_not_increasing {k s : ℕ}
    {π : State (2 * k)} (hs : s < k)
    (hnot : ¬ OffsetPairIncreasing π s hs) :
    OffsetPairDecreasing π s hs := by
  rcases offsetPair_increasing_or_decreasing π hs with hinc | hdec
  · exact False.elim (hnot hinc)
  · exact hdec

theorem not_increasing_and_decreasing_on_two_positions {N : ℕ}
    {π : State N} {s : Finset (Fin N)}
    (hinc : IncreasingOnPositions π s) (hdec : DecreasingOnPositions π s)
    (hcard : 2 ≤ s.card) :
    False := by
  have hcard' : 1 < s.card := by omega
  rcases Finset.one_lt_card.mp hcard' with ⟨p, hp, q, hq, hpq⟩
  rcases lt_or_gt_of_ne hpq with hpq_lt | hqp_lt
  · have hlt1 := hinc hp hq hpq_lt
    have hlt2 := hdec hp hq hpq_lt
    omega
  · have hlt1 := hinc hq hp hqp_lt
    have hlt2 := hdec hq hp hqp_lt
    omega

theorem card_inter_le_one_of_increasing_decreasing {N : ℕ}
    {π : State N} {s t : Finset (Fin N)}
    (hinc : IncreasingOnPositions π t) (hdec : DecreasingOnPositions π s) :
    (s ∩ t).card ≤ 1 := by
  by_contra hnot
  have htwo : 2 ≤ (s ∩ t).card := by omega
  have hinc_inter : IncreasingOnPositions π (s ∩ t) :=
    hinc.mono (by intro p hp; exact (Finset.mem_inter.mp hp).2)
  have hdec_inter : DecreasingOnPositions π (s ∩ t) :=
    hdec.mono (by intro p hp; exact (Finset.mem_inter.mp hp).1)
  exact not_increasing_and_decreasing_on_two_positions hinc_inter hdec_inter htwo

theorem increasing_before_block {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (i : Fin M.move.blockCount) :
    IncreasingOnPositions π (M.move.block i).toFinset := by
  intro p hp q hq hpq
  rw [PositionInterval.mem_toFinset] at hp hq
  exact M.increasing_before i hp hq hpq

theorem block_inter_central_le_one_of_decreasing_before {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (i : Fin M.move.blockCount)
    (hdec : DecreasingOnPositions π (PositionInterval.centralBarrierPositions k d)) :
    (PositionInterval.centralBarrierPositions k d ∩ (M.move.block i).toFinset).card ≤ 1 :=
  card_inter_le_one_of_increasing_decreasing (M.increasing_before_block i) hdec

theorem ne_of_mem_block_and_central_contradicts_decreasing_before {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (i : Fin M.move.blockCount)
    (hdec : DecreasingOnPositions π (PositionInterval.centralBarrierPositions k d))
    {p q : Fin (2 * k)}
    (hpC : p ∈ PositionInterval.centralBarrierPositions k d)
    (hqC : q ∈ PositionInterval.centralBarrierPositions k d)
    (hpB : (M.move.block i).Mem p) (hqB : (M.move.block i).Mem q)
    (hpq : p ≠ q) :
    False := by
  have hle := M.block_inter_central_le_one_of_decreasing_before i hdec
  have hp_inter :
      p ∈ PositionInterval.centralBarrierPositions k d ∩ (M.move.block i).toFinset := by
    rw [Finset.mem_inter, PositionInterval.mem_toFinset]
    exact ⟨hpC, hpB⟩
  have hq_inter :
      q ∈ PositionInterval.centralBarrierPositions k d ∩ (M.move.block i).toFinset := by
    rw [Finset.mem_inter, PositionInterval.mem_toFinset]
    exact ⟨hqC, hqB⟩
  have htwo :
      1 < (PositionInterval.centralBarrierPositions k d ∩
        (M.move.block i).toFinset).card :=
    Finset.one_lt_card.mpr ⟨p, hp_inter, q, hq_inter, hpq⟩
  omega

theorem fixed_on_smaller_central_of_decreasing_before_nonCrossing {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (hM : ¬ M.IsCrossing)
    (hdec : DecreasingOnPositions π (PositionInterval.centralBarrierPositions k d))
    {p : Fin (2 * k)} (hp : p ∈ PositionInterval.centralBarrierPositions k (d - 1)) :
    M.move.map p = p := by
  classical
  have hp_big : p ∈ PositionInterval.centralBarrierPositions k d :=
    PositionInterval.centralBarrierPositions_mono (Nat.sub_le d 1) hp
  by_cases hmem : ∃ i : Fin M.move.blockCount, (M.move.block i).Mem p
  · rcases hmem with ⟨i, hpi⟩
    have hnot_cross_i :
        ¬ ((M.move.block i).lo < k ∧ k ≤ (M.move.block i).hi) := by
      intro hi
      apply hM
      unfold IsCrossing order
      rw [Finset.sum_pos_iff]
      exact ⟨i, by simp, (M.move.block i).crossOrder_pos_iff.mpr hi⟩
    have hmap : M.move.map p = (M.move.block i).mirror p hpi := hrev.1 i p hpi
    by_contra hneq
    have hval_ne : (M.move.map p).val ≠ p.val := by
      intro hval
      exact hneq (Fin.ext hval)
    rcases lt_or_gt_of_ne hval_ne with hlt | hgt
    · have hp_pos : 0 < p.val := by
        rw [hmap] at hlt
        change (M.move.block i).lo + (M.move.block i).hi - p.val < p.val at hlt
        omega
      let q : Fin (2 * k) := ⟨p.val - 1, by omega⟩
      have hq_block : (M.move.block i).Mem q := by
        rw [hmap] at hlt
        change (M.move.block i).lo + (M.move.block i).hi - p.val < p.val at hlt
        rcases hpi with ⟨hlo, hhi⟩
        dsimp [q]
        change (M.move.block i).lo ≤ p.val - 1 ∧
          p.val - 1 ≤ (M.move.block i).hi
        constructor <;> omega
      have hq_big : q ∈ PositionInterval.centralBarrierPositions k d := by
        dsimp [q]
        exact PositionInterval.pred_mem_centralBarrierPositions_of_mem_pred hp hp_pos
      have hpq : p ≠ q := by
        intro hpq
        have hval := congrArg Fin.val hpq
        dsimp [q] at hval
        omega
      exact M.ne_of_mem_block_and_central_contradicts_decreasing_before i hdec
        hp_big hq_big hpi hq_block hpq
    · have hp_succ : p.val + 1 < 2 * k := by
        rw [hmap] at hgt
        have hmirror_lt : ((M.move.block i).mirror p hpi).val < 2 * k :=
          (M.move.block i).mirror p hpi |>.isLt
        change p.val < (M.move.block i).lo + (M.move.block i).hi - p.val at hgt
        rcases hpi with ⟨hlo, hhi⟩
        have hhi_lt := (M.move.block i).hi_lt
        omega
      let q : Fin (2 * k) := ⟨p.val + 1, hp_succ⟩
      have hq_block : (M.move.block i).Mem q := by
        rw [hmap] at hgt
        change p.val < (M.move.block i).lo + (M.move.block i).hi - p.val at hgt
        rcases hpi with ⟨hlo, hhi⟩
        dsimp [q]
        change (M.move.block i).lo ≤ p.val + 1 ∧
          p.val + 1 ≤ (M.move.block i).hi
        constructor <;> omega
      have hq_big : q ∈ PositionInterval.centralBarrierPositions k d := by
        dsimp [q]
        exact PositionInterval.succ_mem_centralBarrierPositions_of_mem_pred hp hp_succ
      have hpq : p ≠ q := by
        intro hpq
        have hval := congrArg Fin.val hpq
        dsimp [q] at hval
        omega
      exact M.ne_of_mem_block_and_central_contradicts_decreasing_before i hdec
        hp_big hq_big hpi hq_block hpq
  · exact hrev.2 p (by
      intro i hi
      exact hmem ⟨i, hi⟩)

theorem decreasing_after_smaller_central_of_decreasing_before_nonCrossing {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (hM : ¬ M.IsCrossing)
    (hdec : DecreasingOnPositions π (PositionInterval.centralBarrierPositions k d)) :
    DecreasingOnPositions ρ (PositionInterval.centralBarrierPositions k (d - 1)) := by
  intro p hp q hq hpq
  have hp_big : p ∈ PositionInterval.centralBarrierPositions k d :=
    PositionInterval.centralBarrierPositions_mono (Nat.sub_le d 1) hp
  have hq_big : q ∈ PositionInterval.centralBarrierPositions k d :=
    PositionInterval.centralBarrierPositions_mono (Nat.sub_le d 1) hq
  have hfixp := M.fixed_on_smaller_central_of_decreasing_before_nonCrossing
    hrev hM hdec hp
  have hfixq := M.fixed_on_smaller_central_of_decreasing_before_nonCrossing
    hrev hM hdec hq
  rw [M.step_apply q, M.step_apply p, hfixq, hfixp]
  exact hdec hp_big hq_big hpq

theorem decreasing_after_block_of_reversesBlocks {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (i : Fin M.move.blockCount) :
    DecreasingOnPositions ρ (M.move.block i).toFinset := by
  intro p hp q hq hpq
  rw [PositionInterval.mem_toFinset] at hp hq
  exact M.label_decreases_after_block_of_reversesBlocks hrev i hp hq hpq

theorem block_inter_central_le_one_of_increasing_after {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (i : Fin M.move.blockCount)
    (hinc : IncreasingOnPositions ρ (PositionInterval.centralBarrierPositions k d)) :
    (PositionInterval.centralBarrierPositions k d ∩ (M.move.block i).toFinset).card ≤ 1 :=
  by
    have hle := card_inter_le_one_of_increasing_decreasing hinc
      (M.decreasing_after_block_of_reversesBlocks hrev i)
    simpa [Finset.inter_comm] using hle

theorem ne_of_mem_block_and_central_contradicts_increasing_after {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (i : Fin M.move.blockCount)
    (hinc : IncreasingOnPositions ρ (PositionInterval.centralBarrierPositions k d))
    {p q : Fin (2 * k)}
    (hpC : p ∈ PositionInterval.centralBarrierPositions k d)
    (hqC : q ∈ PositionInterval.centralBarrierPositions k d)
    (hpB : (M.move.block i).Mem p) (hqB : (M.move.block i).Mem q)
    (hpq : p ≠ q) :
    False := by
  have hle := M.block_inter_central_le_one_of_increasing_after hrev i hinc
  have hp_inter :
      p ∈ PositionInterval.centralBarrierPositions k d ∩ (M.move.block i).toFinset := by
    rw [Finset.mem_inter, PositionInterval.mem_toFinset]
    exact ⟨hpC, hpB⟩
  have hq_inter :
      q ∈ PositionInterval.centralBarrierPositions k d ∩ (M.move.block i).toFinset := by
    rw [Finset.mem_inter, PositionInterval.mem_toFinset]
    exact ⟨hqC, hqB⟩
  have htwo :
      1 < (PositionInterval.centralBarrierPositions k d ∩
        (M.move.block i).toFinset).card :=
    Finset.one_lt_card.mpr ⟨p, hp_inter, q, hq_inter, hpq⟩
  omega

theorem fixed_on_smaller_central_of_increasing_after_nonCrossing {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (hM : ¬ M.IsCrossing)
    (hinc : IncreasingOnPositions ρ (PositionInterval.centralBarrierPositions k d))
    {p : Fin (2 * k)} (hp : p ∈ PositionInterval.centralBarrierPositions k (d - 1)) :
    M.move.map p = p := by
  classical
  have hp_big : p ∈ PositionInterval.centralBarrierPositions k d :=
    PositionInterval.centralBarrierPositions_mono (Nat.sub_le d 1) hp
  by_cases hmem : ∃ i : Fin M.move.blockCount, (M.move.block i).Mem p
  · rcases hmem with ⟨i, hpi⟩
    have hnot_cross_i :
        ¬ ((M.move.block i).lo < k ∧ k ≤ (M.move.block i).hi) := by
      intro hi
      apply hM
      unfold IsCrossing order
      rw [Finset.sum_pos_iff]
      exact ⟨i, by simp, (M.move.block i).crossOrder_pos_iff.mpr hi⟩
    have hmap : M.move.map p = (M.move.block i).mirror p hpi := hrev.1 i p hpi
    by_contra hneq
    have hval_ne : (M.move.map p).val ≠ p.val := by
      intro hval
      exact hneq (Fin.ext hval)
    rcases lt_or_gt_of_ne hval_ne with hlt | hgt
    · have hp_pos : 0 < p.val := by
        rw [hmap] at hlt
        change (M.move.block i).lo + (M.move.block i).hi - p.val < p.val at hlt
        omega
      let q : Fin (2 * k) := ⟨p.val - 1, by omega⟩
      have hq_block : (M.move.block i).Mem q := by
        rw [hmap] at hlt
        change (M.move.block i).lo + (M.move.block i).hi - p.val < p.val at hlt
        rcases hpi with ⟨hlo, hhi⟩
        dsimp [q]
        change (M.move.block i).lo ≤ p.val - 1 ∧
          p.val - 1 ≤ (M.move.block i).hi
        constructor <;> omega
      have hq_big : q ∈ PositionInterval.centralBarrierPositions k d := by
        dsimp [q]
        exact PositionInterval.pred_mem_centralBarrierPositions_of_mem_pred hp hp_pos
      have hpq : p ≠ q := by
        intro hpq
        have hval := congrArg Fin.val hpq
        dsimp [q] at hval
        omega
      exact M.ne_of_mem_block_and_central_contradicts_increasing_after hrev i hinc
        hp_big hq_big hpi hq_block hpq
    · have hp_succ : p.val + 1 < 2 * k := by
        rw [hmap] at hgt
        change p.val < (M.move.block i).lo + (M.move.block i).hi - p.val at hgt
        rcases hpi with ⟨hlo, hhi⟩
        have hhi_lt := (M.move.block i).hi_lt
        omega
      let q : Fin (2 * k) := ⟨p.val + 1, hp_succ⟩
      have hq_block : (M.move.block i).Mem q := by
        rw [hmap] at hgt
        change p.val < (M.move.block i).lo + (M.move.block i).hi - p.val at hgt
        rcases hpi with ⟨hlo, hhi⟩
        dsimp [q]
        change (M.move.block i).lo ≤ p.val + 1 ∧
          p.val + 1 ≤ (M.move.block i).hi
        constructor <;> omega
      have hq_big : q ∈ PositionInterval.centralBarrierPositions k d := by
        dsimp [q]
        exact PositionInterval.succ_mem_centralBarrierPositions_of_mem_pred hp hp_succ
      have hpq : p ≠ q := by
        intro hpq
        have hval := congrArg Fin.val hpq
        dsimp [q] at hval
        omega
      exact M.ne_of_mem_block_and_central_contradicts_increasing_after hrev i hinc
        hp_big hq_big hpi hq_block hpq
  · exact hrev.2 p (by
      intro i hi
      exact hmem ⟨i, hi⟩)

theorem increasing_before_smaller_central_of_increasing_after_nonCrossing {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (hM : ¬ M.IsCrossing)
    (hinc : IncreasingOnPositions ρ (PositionInterval.centralBarrierPositions k d)) :
    IncreasingOnPositions π (PositionInterval.centralBarrierPositions k (d - 1)) := by
  intro p hp q hq hpq
  have hp_big : p ∈ PositionInterval.centralBarrierPositions k d :=
    PositionInterval.centralBarrierPositions_mono (Nat.sub_le d 1) hp
  have hq_big : q ∈ PositionInterval.centralBarrierPositions k d :=
    PositionInterval.centralBarrierPositions_mono (Nat.sub_le d 1) hq
  have hfixp := M.fixed_on_smaller_central_of_increasing_after_nonCrossing
    hrev hM hinc hp
  have hfixq := M.fixed_on_smaller_central_of_increasing_after_nonCrossing
    hrev hM hinc hq
  have hp_step := M.step_apply p
  have hq_step := M.step_apply q
  rw [hfixp] at hp_step
  rw [hfixq] at hq_step
  have h := hinc hp_big hq_big hpq
  rwa [hp_step, hq_step] at h

theorem isCrossing_iff_exists_crossing_block {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) :
    M.IsCrossing ↔
      ∃ i : Fin M.move.blockCount, (M.move.block i).lo < k ∧ k ≤ (M.move.block i).hi := by
  classical
  unfold IsCrossing order
  rw [Finset.sum_pos_iff]
  constructor
  · rintro ⟨i, _hi, hpos⟩
    exact ⟨i, (M.move.block i).crossOrder_pos_iff.mp hpos⟩
  · rintro ⟨i, hcross⟩
    exact ⟨i, by simp, (M.move.block i).crossOrder_pos_iff.mpr hcross⟩

theorem order_eq_crossOrder_of_crossing_block {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) {i : Fin M.move.blockCount}
    (hi : (M.move.block i).lo < k ∧ k ≤ (M.move.block i).hi) :
    M.order = (M.move.block i).crossOrder k := by
  classical
  unfold order
  rw [Finset.sum_eq_single i]
  · intro j _hj hji
    have hnot : ¬ ((M.move.block j).lo < k ∧ k ≤ (M.move.block j).hi) := by
      intro hjcross
      exact hji ((M.move.crossing_blocks_eq hi hjcross).symm)
    exact PositionInterval.crossOrder_eq_zero_of_not_crossing hnot
  · intro hi_not
    exact False.elim (hi_not (by simp))

noncomputable def crossingBlockIndex {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) : Fin M.move.blockCount :=
  Classical.choose (M.isCrossing_iff_exists_crossing_block.mp hM)

theorem crossingBlockIndex_spec {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) :
    (M.move.block (M.crossingBlockIndex hM)).lo < k ∧
      k ≤ (M.move.block (M.crossingBlockIndex hM)).hi :=
  Classical.choose_spec (M.isCrossing_iff_exists_crossing_block.mp hM)

theorem crossingBlockIndex_unique {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) {i : Fin M.move.blockCount}
    (hi : (M.move.block i).lo < k ∧ k ≤ (M.move.block i).hi) :
    i = M.crossingBlockIndex hM :=
  M.move.crossing_blocks_eq hi (M.crossingBlockIndex_spec hM)

theorem order_eq_crossingBlockIndex_crossOrder {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) :
    M.order = (M.move.block (M.crossingBlockIndex hM)).crossOrder k :=
  M.order_eq_crossOrder_of_crossing_block (M.crossingBlockIndex_spec hM)

theorem crossingBlock_eq_full_of_order_eq_middle {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing)
    (hk : 0 < k) (horder : M.order = k) :
    (M.move.block (M.crossingBlockIndex hM)).lo = 0 ∧
      (M.move.block (M.crossingBlockIndex hM)).hi = 2 * k - 1 := by
  have hcrossOrder :
      (M.move.block (M.crossingBlockIndex hM)).crossOrder k = k := by
    rw [← M.order_eq_crossingBlockIndex_crossOrder hM, horder]
  exact PositionInterval.eq_full_of_crossOrder_eq_middle
    (M.move.block (M.crossingBlockIndex hM)) hk hcrossOrder

theorem increasing_before_univ_of_order_eq_middle {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing)
    (hk : 0 < k) (horder : M.order = k) :
    IncreasingOnPositions π Finset.univ := by
  intro p _hp q _hq hpq
  have hfull := M.crossingBlock_eq_full_of_order_eq_middle hM hk horder
  let b := M.crossingBlockIndex hM
  have hb_lo : (M.move.block b).lo = 0 := by
    simpa [b] using hfull.1
  have hb_hi : (M.move.block b).hi = 2 * k - 1 := by
    simpa [b] using hfull.2
  have hp : (M.move.block b).Mem p := by
    dsimp [PositionInterval.Mem]
    omega
  have hq : (M.move.block b).Mem q := by
    dsimp [PositionInterval.Mem]
    omega
  exact M.increasing_before b hp hq hpq

theorem decreasing_after_univ_of_order_eq_middle {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing)
    (hk : 0 < k) (horder : M.order = k) :
    DecreasingOnPositions ρ Finset.univ := by
  intro p _hp q _hq hpq
  have hfull := M.crossingBlock_eq_full_of_order_eq_middle hM hk horder
  let b := M.crossingBlockIndex hM
  have hb_lo : (M.move.block b).lo = 0 := by
    simpa [b] using hfull.1
  have hb_hi : (M.move.block b).hi = 2 * k - 1 := by
    simpa [b] using hfull.2
  have hp : (M.move.block b).Mem p := by
    dsimp [PositionInterval.Mem]
    omega
  have hq : (M.move.block b).Mem q := by
    dsimp [PositionInterval.Mem]
    omega
  exact M.label_decreases_after_block_of_reversesBlocks hrev b hp hq hpq

theorem source_eq_refl_of_order_eq_middle {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing)
    (hk : 0 < k) (horder : M.order = k) :
    π = Equiv.refl (Fin (2 * k)) :=
  state_eq_refl_of_increasingOn_univ
    (M.increasing_before_univ_of_order_eq_middle hM hk horder)

theorem target_eq_reverseFin_of_order_eq_middle {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing)
    (hk : 0 < k) (horder : M.order = k) :
    ρ = reverseFin (2 * k) :=
  state_eq_reverseFin_of_decreasingOn_univ
    (M.decreasing_after_univ_of_order_eq_middle hrev hM hk horder)

theorem decreasing_after_leftMirrorCrossingPositions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing) :
    DecreasingOnPositions ρ
      ((M.move.block (M.crossingBlockIndex hM)).leftMirrorCrossingPositions k) := by
  intro p hp q hq hpq
  have hpB : (M.move.block (M.crossingBlockIndex hM)).Mem p := by
    rw [PositionInterval.leftMirrorCrossingPositions, Finset.mem_filter,
      PositionInterval.mem_toFinset] at hp
    exact hp.1
  have hqB : (M.move.block (M.crossingBlockIndex hM)).Mem q := by
    rw [PositionInterval.leftMirrorCrossingPositions, Finset.mem_filter,
      PositionInterval.mem_toFinset] at hq
    exact hq.1
  exact M.label_decreases_after_block_of_reversesBlocks hrev (M.crossingBlockIndex hM)
    hpB hqB hpq

theorem decreasing_after_rightMirrorCrossingPositions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing) :
    DecreasingOnPositions ρ
      ((M.move.block (M.crossingBlockIndex hM)).rightMirrorCrossingPositions k) := by
  intro p hp q hq hpq
  have hpB : (M.move.block (M.crossingBlockIndex hM)).Mem p := by
    rw [PositionInterval.rightMirrorCrossingPositions, Finset.mem_filter,
      PositionInterval.mem_toFinset] at hp
    exact hp.1
  have hqB : (M.move.block (M.crossingBlockIndex hM)).Mem q := by
    rw [PositionInterval.rightMirrorCrossingPositions, Finset.mem_filter,
      PositionInterval.mem_toFinset] at hq
    exact hq.1
  exact M.label_decreases_after_block_of_reversesBlocks hrev (M.crossingBlockIndex hM)
    hpB hqB hpq

theorem decreasing_after_leftCentralPositions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing) :
    DecreasingOnPositions ρ
      ((M.move.block (M.crossingBlockIndex hM)).leftCentralPositions k) := by
  intro p hp q hq hpq
  have hpB : (M.move.block (M.crossingBlockIndex hM)).Mem p := by
    exact (PositionInterval.mem_leftCentralPositions.mp hp).1
  have hqB : (M.move.block (M.crossingBlockIndex hM)).Mem q := by
    exact (PositionInterval.mem_leftCentralPositions.mp hq).1
  exact M.label_decreases_after_block_of_reversesBlocks hrev (M.crossingBlockIndex hM)
    hpB hqB hpq

theorem decreasing_after_rightCentralPositions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing) :
    DecreasingOnPositions ρ
      ((M.move.block (M.crossingBlockIndex hM)).rightCentralPositions k) := by
  intro p hp q hq hpq
  have hpB : (M.move.block (M.crossingBlockIndex hM)).Mem p := by
    exact (PositionInterval.mem_rightCentralPositions.mp hp).1
  have hqB : (M.move.block (M.crossingBlockIndex hM)).Mem q := by
    exact (PositionInterval.mem_rightCentralPositions.mp hq).1
  exact M.label_decreases_after_block_of_reversesBlocks hrev (M.crossingBlockIndex hM)
    hpB hqB hpq

theorem increasing_before_leftMirrorCrossingPositions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) :
    IncreasingOnPositions π
      ((M.move.block (M.crossingBlockIndex hM)).leftMirrorCrossingPositions k) := by
  intro p hp q hq hpq
  have hpB : (M.move.block (M.crossingBlockIndex hM)).Mem p := by
    rw [PositionInterval.leftMirrorCrossingPositions, Finset.mem_filter,
      PositionInterval.mem_toFinset] at hp
    exact hp.1
  have hqB : (M.move.block (M.crossingBlockIndex hM)).Mem q := by
    rw [PositionInterval.leftMirrorCrossingPositions, Finset.mem_filter,
      PositionInterval.mem_toFinset] at hq
    exact hq.1
  exact M.increasing_before (M.crossingBlockIndex hM) hpB hqB hpq

theorem increasing_before_rightMirrorCrossingPositions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) :
    IncreasingOnPositions π
      ((M.move.block (M.crossingBlockIndex hM)).rightMirrorCrossingPositions k) := by
  intro p hp q hq hpq
  have hpB : (M.move.block (M.crossingBlockIndex hM)).Mem p := by
    rw [PositionInterval.rightMirrorCrossingPositions, Finset.mem_filter,
      PositionInterval.mem_toFinset] at hp
    exact hp.1
  have hqB : (M.move.block (M.crossingBlockIndex hM)).Mem q := by
    rw [PositionInterval.rightMirrorCrossingPositions, Finset.mem_filter,
      PositionInterval.mem_toFinset] at hq
    exact hq.1
  exact M.increasing_before (M.crossingBlockIndex hM) hpB hqB hpq

theorem increasing_before_leftCentralPositions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) :
    IncreasingOnPositions π
      ((M.move.block (M.crossingBlockIndex hM)).leftCentralPositions k) := by
  intro p hp q hq hpq
  have hpB : (M.move.block (M.crossingBlockIndex hM)).Mem p := by
    exact (PositionInterval.mem_leftCentralPositions.mp hp).1
  have hqB : (M.move.block (M.crossingBlockIndex hM)).Mem q := by
    exact (PositionInterval.mem_leftCentralPositions.mp hq).1
  exact M.increasing_before (M.crossingBlockIndex hM) hpB hqB hpq

theorem increasing_before_rightCentralPositions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) :
    IncreasingOnPositions π
      ((M.move.block (M.crossingBlockIndex hM)).rightCentralPositions k) := by
  intro p hp q hq hpq
  have hpB : (M.move.block (M.crossingBlockIndex hM)).Mem p := by
    exact (PositionInterval.mem_rightCentralPositions.mp hp).1
  have hqB : (M.move.block (M.crossingBlockIndex hM)).Mem q := by
    exact (PositionInterval.mem_rightCentralPositions.mp hq).1
  exact M.increasing_before (M.crossingBlockIndex hM) hpB hqB hpq

theorem leftMirrorCrossingPositions_card_eq_order {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) :
    ((M.move.block (M.crossingBlockIndex hM)).leftMirrorCrossingPositions k).card =
      M.order := by
  rw [PositionInterval.leftMirrorCrossingPositions_card_eq_crossOrder_of_crossing
    (M.move.block (M.crossingBlockIndex hM)) (M.crossingBlockIndex_spec hM)]
  rw [M.order_eq_crossingBlockIndex_crossOrder hM]

theorem rightMirrorCrossingPositions_card_eq_order {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) :
    ((M.move.block (M.crossingBlockIndex hM)).rightMirrorCrossingPositions k).card =
      M.order := by
  rw [PositionInterval.rightMirrorCrossingPositions_card_eq_crossOrder_of_crossing
    (M.move.block (M.crossingBlockIndex hM)) (M.crossingBlockIndex_spec hM)]
  rw [M.order_eq_crossingBlockIndex_crossOrder hM]

theorem leftCentralPositions_card_eq_order {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) :
    ((M.move.block (M.crossingBlockIndex hM)).leftCentralPositions k).card =
      M.order := by
  rw [PositionInterval.leftCentralPositions_card_eq_crossOrder]
  rw [M.order_eq_crossingBlockIndex_crossOrder hM]

theorem rightCentralPositions_card_eq_order {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) :
    ((M.move.block (M.crossingBlockIndex hM)).rightCentralPositions k).card =
      M.order := by
  rw [PositionInterval.rightCentralPositions_card_eq_crossOrder]
  rw [M.order_eq_crossingBlockIndex_crossOrder hM]

theorem decreasing_after_leftBarrierPositions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing) :
    DecreasingOnPositions ρ (PositionInterval.leftBarrierPositions k M.order) := by
  have hcentral := M.decreasing_after_leftCentralPositions hrev hM
  rw [PositionInterval.leftCentralPositions_eq_leftBarrierPositions_of_crossing
    (M.move.block (M.crossingBlockIndex hM)) (M.crossingBlockIndex_spec hM)] at hcentral
  rw [M.order_eq_crossingBlockIndex_crossOrder hM]
  exact hcentral

theorem decreasing_after_rightBarrierPositions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing) :
    DecreasingOnPositions ρ (PositionInterval.rightBarrierPositions k M.order) := by
  have hcentral := M.decreasing_after_rightCentralPositions hrev hM
  rw [PositionInterval.rightCentralPositions_eq_rightBarrierPositions_of_crossing
    (M.move.block (M.crossingBlockIndex hM)) (M.crossingBlockIndex_spec hM)] at hcentral
  rw [M.order_eq_crossingBlockIndex_crossOrder hM]
  exact hcentral

theorem increasing_before_leftBarrierPositions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) :
    IncreasingOnPositions π (PositionInterval.leftBarrierPositions k M.order) := by
  have hcentral := M.increasing_before_leftCentralPositions hM
  rw [PositionInterval.leftCentralPositions_eq_leftBarrierPositions_of_crossing
    (M.move.block (M.crossingBlockIndex hM)) (M.crossingBlockIndex_spec hM)] at hcentral
  rw [M.order_eq_crossingBlockIndex_crossOrder hM]
  exact hcentral

theorem increasing_before_rightBarrierPositions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) :
    IncreasingOnPositions π (PositionInterval.rightBarrierPositions k M.order) := by
  have hcentral := M.increasing_before_rightCentralPositions hM
  rw [PositionInterval.rightCentralPositions_eq_rightBarrierPositions_of_crossing
    (M.move.block (M.crossingBlockIndex hM)) (M.crossingBlockIndex_spec hM)] at hcentral
  rw [M.order_eq_crossingBlockIndex_crossOrder hM]
  exact hcentral

theorem increasing_before_centralBarrierPositions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) :
    IncreasingOnPositions π (PositionInterval.centralBarrierPositions k M.order) := by
  intro p hp q hq hpq
  let b := M.crossingBlockIndex hM
  have hcross : (M.move.block b).lo < k ∧ k ≤ (M.move.block b).hi := by
    simpa [b] using M.crossingBlockIndex_spec hM
  have horder : M.order = (M.move.block b).crossOrder k := by
    simpa [b] using M.order_eq_crossingBlockIndex_crossOrder hM
  have hleft : (M.move.block b).crossOrder k ≤ k - (M.move.block b).lo :=
    (M.move.block b).crossOrder_le_left
  have hright : (M.move.block b).crossOrder k ≤ (M.move.block b).hi + 1 - k :=
    (M.move.block b).crossOrder_le_right
  have hpB : (M.move.block b).Mem p := by
    rw [PositionInterval.mem_centralBarrierPositions] at hp
    rw [horder] at hp
    rcases hp with hp | hp
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  have hqB : (M.move.block b).Mem q := by
    rw [PositionInterval.mem_centralBarrierPositions] at hq
    rw [horder] at hq
    rcases hq with hq | hq
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  exact M.increasing_before b hpB hqB hpq

theorem decreasing_after_centralBarrierPositions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing) :
    DecreasingOnPositions ρ (PositionInterval.centralBarrierPositions k M.order) := by
  intro p hp q hq hpq
  let b := M.crossingBlockIndex hM
  have hcross : (M.move.block b).lo < k ∧ k ≤ (M.move.block b).hi := by
    simpa [b] using M.crossingBlockIndex_spec hM
  have horder : M.order = (M.move.block b).crossOrder k := by
    simpa [b] using M.order_eq_crossingBlockIndex_crossOrder hM
  have hleft : (M.move.block b).crossOrder k ≤ k - (M.move.block b).lo :=
    (M.move.block b).crossOrder_le_left
  have hright : (M.move.block b).crossOrder k ≤ (M.move.block b).hi + 1 - k :=
    (M.move.block b).crossOrder_le_right
  have hpB : (M.move.block b).Mem p := by
    rw [PositionInterval.mem_centralBarrierPositions] at hp
    rw [horder] at hp
    rcases hp with hp | hp
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  have hqB : (M.move.block b).Mem q := by
    rw [PositionInterval.mem_centralBarrierPositions] at hq
    rw [horder] at hq
    rcases hq with hq | hq
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  exact M.label_decreases_after_block_of_reversesBlocks hrev b hpB hqB hpq

theorem increasing_before_centralBarrierPositions_of_le_order {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) (hd : d ≤ M.order) :
    IncreasingOnPositions π (PositionInterval.centralBarrierPositions k d) :=
  (M.increasing_before_centralBarrierPositions hM).mono
    (PositionInterval.centralBarrierPositions_mono hd)

theorem decreasing_after_centralBarrierPositions_of_le_order {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (hM : M.IsCrossing) (hd : d ≤ M.order) :
    DecreasingOnPositions ρ (PositionInterval.centralBarrierPositions k d) :=
  (M.decreasing_after_centralBarrierPositions hrev hM).mono
    (PositionInterval.centralBarrierPositions_mono hd)

theorem middlePair_decreasing_after_crossing {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (hM : M.IsCrossing) (hk : 0 < k) :
    MiddlePairDecreasing ρ hk := by
  let p := middleLeftPosition k hk
  let q := middleRightPosition k hk
  have hcross := M.crossingBlockIndex_spec hM
  have hp : (M.move.block (M.crossingBlockIndex hM)).Mem p := by
    dsimp [p, middleLeftPosition]
    change (M.move.block (M.crossingBlockIndex hM)).lo ≤ k - 1 ∧
      k - 1 ≤ (M.move.block (M.crossingBlockIndex hM)).hi
    constructor <;> omega
  have hq : (M.move.block (M.crossingBlockIndex hM)).Mem q := by
    dsimp [q, middleRightPosition]
    change (M.move.block (M.crossingBlockIndex hM)).lo ≤ k ∧
      k ≤ (M.move.block (M.crossingBlockIndex hM)).hi
    constructor <;> omega
  have hpq : p < q := by
    change k - 1 < k
    omega
  exact M.label_decreases_after_block_of_reversesBlocks hrev (M.crossingBlockIndex hM)
    hp hq hpq

theorem middlePair_increasing_before_crossing {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) (hk : 0 < k) :
    MiddlePairIncreasing π hk := by
  let p := middleLeftPosition k hk
  let q := middleRightPosition k hk
  have hcross := M.crossingBlockIndex_spec hM
  have hp : (M.move.block (M.crossingBlockIndex hM)).Mem p := by
    dsimp [p, middleLeftPosition]
    change (M.move.block (M.crossingBlockIndex hM)).lo ≤ k - 1 ∧
      k - 1 ≤ (M.move.block (M.crossingBlockIndex hM)).hi
    constructor <;> omega
  have hq : (M.move.block (M.crossingBlockIndex hM)).Mem q := by
    dsimp [q, middleRightPosition]
    change (M.move.block (M.crossingBlockIndex hM)).lo ≤ k ∧
      k ≤ (M.move.block (M.crossingBlockIndex hM)).hi
    constructor <;> omega
  have hpq : p < q := by
    change k - 1 < k
    omega
  exact M.increasing_before (M.crossingBlockIndex hM) hp hq hpq

theorem offsetPair_decreasing_after_crossing {k s : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (hM : M.IsCrossing) (hsk : s < k) (hs : s < M.order) :
    OffsetPairDecreasing ρ s hsk := by
  let p := leftOffsetPosition k s hsk
  let q := rightOffsetPosition k s hsk
  let b := M.crossingBlockIndex hM
  have hcross : (M.move.block b).lo < k ∧ k ≤ (M.move.block b).hi := by
    simpa [b] using M.crossingBlockIndex_spec hM
  have horder : M.order = (M.move.block b).crossOrder k := by
    simpa [b] using M.order_eq_crossingBlockIndex_crossOrder hM
  have hleft : (M.move.block b).crossOrder k ≤ k - (M.move.block b).lo :=
    (M.move.block b).crossOrder_le_left
  have hright : (M.move.block b).crossOrder k ≤ (M.move.block b).hi + 1 - k :=
    (M.move.block b).crossOrder_le_right
  have hs_cross : s < (M.move.block b).crossOrder k := by
    rwa [horder] at hs
  have hp : (M.move.block b).Mem p := by
    dsimp [p, leftOffsetPosition]
    change (M.move.block b).lo ≤ k - 1 - s ∧
      k - 1 - s ≤ (M.move.block b).hi
    constructor <;> omega
  have hq : (M.move.block b).Mem q := by
    dsimp [q, rightOffsetPosition]
    change (M.move.block b).lo ≤ k + s ∧ k + s ≤ (M.move.block b).hi
    constructor <;> omega
  have hpq : p < q := by
    change k - 1 - s < k + s
    omega
  exact M.label_decreases_after_block_of_reversesBlocks hrev b hp hq hpq

theorem offsetPair_increasing_before_crossing {k s : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) (hsk : s < k) (hs : s < M.order) :
    OffsetPairIncreasing π s hsk := by
  let p := leftOffsetPosition k s hsk
  let q := rightOffsetPosition k s hsk
  let b := M.crossingBlockIndex hM
  have hcross : (M.move.block b).lo < k ∧ k ≤ (M.move.block b).hi := by
    simpa [b] using M.crossingBlockIndex_spec hM
  have horder : M.order = (M.move.block b).crossOrder k := by
    simpa [b] using M.order_eq_crossingBlockIndex_crossOrder hM
  have hleft : (M.move.block b).crossOrder k ≤ k - (M.move.block b).lo :=
    (M.move.block b).crossOrder_le_left
  have hright : (M.move.block b).crossOrder k ≤ (M.move.block b).hi + 1 - k :=
    (M.move.block b).crossOrder_le_right
  have hs_cross : s < (M.move.block b).crossOrder k := by
    rwa [horder] at hs
  have hp : (M.move.block b).Mem p := by
    dsimp [p, leftOffsetPosition]
    change (M.move.block b).lo ≤ k - 1 - s ∧
      k - 1 - s ≤ (M.move.block b).hi
    constructor <;> omega
  have hq : (M.move.block b).Mem q := by
    dsimp [q, rightOffsetPosition]
    change (M.move.block b).lo ≤ k + s ∧ k + s ≤ (M.move.block b).hi
    constructor <;> omega
  have hpq : p < q := by
    change k - 1 - s < k + s
    omega
  exact M.increasing_before b hp hq hpq

theorem move_middleLeft_iff_of_not_isCrossing {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (hM : ¬ M.IsCrossing) (p : Fin (2 * k)) :
    middleLeft k (M.move.map p) ↔ middleLeft k p := by
  exact M.move.map_middleLeft_iff_of_reversesBlocks_no_crossing hrev (by
    intro i hi
    exact hM ((M.isCrossing_iff_exists_crossing_block).mpr ⟨i, hi⟩)) p

theorem new_position_eq_map_old_position_of_reversesBlocks {k : ℕ}
    {π ρ : State (2 * k)} (M : ReversalStep k π ρ)
    (hrev : M.move.ReversesBlocks) (a : Fin (2 * k)) :
    ρ.symm a = M.move.map (π.symm a) := by
  apply ρ.injective
  rw [Equiv.apply_symm_apply]
  rw [M.step_apply]
  rw [M.move.map_map_eq_of_reversesBlocks hrev]
  exact (Equiv.apply_symm_apply π a).symm

theorem crossesMiddle_iff_map_old_position {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (a : Fin (2 * k)) :
    crossesMiddle k π ρ a ↔
      (middleLeft k (π.symm a) ↔ ¬ middleLeft k (M.move.map (π.symm a))) := by
  rw [crossesMiddle, M.new_position_eq_map_old_position_of_reversesBlocks hrev a]

theorem not_crossesMiddle_of_not_isCrossing {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (hM : ¬ M.IsCrossing) (a : Fin (2 * k)) :
    ¬ crossesMiddle k π ρ a := by
  rw [M.crossesMiddle_iff_map_old_position hrev a]
  have hside := M.move_middleLeft_iff_of_not_isCrossing hrev hM (π.symm a)
  by_cases hleft : middleLeft k (π.symm a)
  · simp [hleft, hside.mpr hleft]
  · simp [hleft, hside.not.mpr hleft]

theorem middleLeft_new_position_iff_of_not_isCrossing {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (hM : ¬ M.IsCrossing) (a : Fin (2 * k)) :
    middleLeft k (ρ.symm a) ↔ middleLeft k (π.symm a) := by
  rw [M.new_position_eq_map_old_position_of_reversesBlocks hrev a]
  exact M.move_middleLeft_iff_of_not_isCrossing hrev hM (π.symm a)

noncomputable def positionCrossingCard (k : ℕ) (σ : State (2 * k)) : ℕ := by
  classical
  exact Fintype.card {p : Fin (2 * k) // middleLeft k p ↔ ¬ middleLeft k (σ p)}

noncomputable def labelCrossingCard (k : ℕ) (π ρ : State (2 * k)) : ℕ := by
  classical
  exact Fintype.card {a : Fin (2 * k) // crossesMiddle k π ρ a}

theorem crossingLabelsCard_eq_positionCrossingCard_of_reversesBlocks {k : ℕ}
    {π ρ : State (2 * k)} (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) :
    labelCrossingCard k π ρ = positionCrossingCard k M.move.map := by
  classical
  unfold labelCrossingCard positionCrossingCard
  refine Fintype.card_congr ?_
  refine
  { toFun := fun a =>
      ⟨π.symm a.1, (M.crossesMiddle_iff_map_old_position hrev a.1).mp a.2⟩
    invFun := fun p =>
      ⟨π p.1, (M.crossesMiddle_iff_map_old_position hrev (π p.1)).mpr ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · simpa using p.2
  · intro a
    apply Subtype.ext
    exact Equiv.apply_symm_apply π a.1
  · intro p
    apply Subtype.ext
    exact Equiv.symm_apply_apply π p.1

theorem positionCrossingCard_eq_zero_of_no_crossing_block {k : ℕ}
    {M : BlockMove (2 * k)} (hrev : M.ReversesBlocks)
    (hnone : ∀ i : Fin M.blockCount, ¬ ((M.block i).lo < k ∧ k ≤ (M.block i).hi)) :
    positionCrossingCard k M.map = 0 := by
  classical
  unfold positionCrossingCard
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun x => ?_⟩
  rcases x with ⟨p, hp⟩
  by_cases hmem : ∃ i : Fin M.blockCount, (M.block i).Mem p
  · rcases hmem with ⟨i, hpi⟩
    have hpmap : (M.block i).Mem (M.map p) :=
      M.map_mem_of_reversesBlocks hrev hpi
    have hside : (M.block i).hi < k ∨ k ≤ (M.block i).lo := by
      have hlohi := (M.block i).lo_le_hi
      have hnot := hnone i
      omega
    rcases hside with hleft | hright
    · have hp_left : middleLeft k p := by
        exact lt_of_le_of_lt hpi.2 hleft
      have hmap_left : middleLeft k (M.map p) := by
        exact lt_of_le_of_lt hpmap.2 hleft
      exact (hp.mp hp_left) hmap_left
    · have hp_not_left : ¬ middleLeft k p := by
        intro hp_left
        exact not_lt_of_ge (le_trans hright hpi.1) hp_left
      have hmap_not_left : ¬ middleLeft k (M.map p) := by
        intro hmap_left
        exact not_lt_of_ge (le_trans hright hpmap.1) hmap_left
      exact hp_not_left (hp.mpr hmap_not_left)
  · have hfix : M.map p = p := hrev.2 p (by
      intro i
      exact fun hi => hmem ⟨i, hi⟩)
    rw [hfix] at hp
    by_cases hp_left : middleLeft k p
    · exact (hp.mp hp_left) hp_left
    · exact hp_left (hp.mpr hp_left)

theorem exists_crossing_block_of_position_crosses {k : ℕ}
    {M : BlockMove (2 * k)} (hrev : M.ReversesBlocks) {p : Fin (2 * k)}
    (hp : middleLeft k p ↔ ¬ middleLeft k (M.map p)) :
    ∃ i : Fin M.blockCount, (M.block i).lo < k ∧ k ≤ (M.block i).hi := by
  classical
  by_contra hnone
  have hnone' :
      ∀ i : Fin M.blockCount, ¬ ((M.block i).lo < k ∧ k ≤ (M.block i).hi) := by
    intro i hi
    exact hnone ⟨i, hi⟩
  have hz := positionCrossingCard_eq_zero_of_no_crossing_block
    (k := k) (M := M) hrev hnone'
  unfold positionCrossingCard at hz
  have hmem : (⟨p, hp⟩ :
      {p : Fin (2 * k) // middleLeft k p ↔ ¬ middleLeft k (M.map p)}) ∈
        (Finset.univ :
          Finset {p : Fin (2 * k) // middleLeft k p ↔ ¬ middleLeft k (M.map p)}) := by
    simp
  have hcard_pos :
      0 < Fintype.card
        {p : Fin (2 * k) // middleLeft k p ↔ ¬ middleLeft k (M.map p)} := by
    exact Fintype.card_pos_iff.mpr ⟨⟨p, hp⟩⟩
  omega

theorem exists_mem_crossing_block_of_position_crosses {k : ℕ}
    {M : BlockMove (2 * k)} (hrev : M.ReversesBlocks) {p : Fin (2 * k)}
    (hp : middleLeft k p ↔ ¬ middleLeft k (M.map p)) :
    ∃ i : Fin M.blockCount,
      (M.block i).Mem p ∧ (M.block i).lo < k ∧ k ≤ (M.block i).hi := by
  classical
  by_cases hmem : ∃ i : Fin M.blockCount, (M.block i).Mem p
  · rcases hmem with ⟨i, hpi⟩
    refine ⟨i, hpi, ?_⟩
    by_contra hnotcross
    have hpmap : (M.block i).Mem (M.map p) :=
      M.map_mem_of_reversesBlocks hrev hpi
    have hside : (M.block i).hi < k ∨ k ≤ (M.block i).lo := by
      have hlohi := (M.block i).lo_le_hi
      omega
    rcases hside with hleft | hright
    · have hp_left : middleLeft k p := lt_of_le_of_lt hpi.2 hleft
      have hmap_left : middleLeft k (M.map p) := lt_of_le_of_lt hpmap.2 hleft
      exact (hp.mp hp_left) hmap_left
    · have hp_not_left : ¬ middleLeft k p := by
        intro hp_left
        exact not_lt_of_ge (le_trans hright hpi.1) hp_left
      have hmap_not_left : ¬ middleLeft k (M.map p) := by
        intro hmap_left
        exact not_lt_of_ge (le_trans hright hpmap.1) hmap_left
      exact hp_not_left (hp.mpr hmap_not_left)
  · have hfix : M.map p = p := hrev.2 p (by
      intro i hi
      exact hmem ⟨i, hi⟩)
    rw [hfix] at hp
    by_cases hleft : middleLeft k p
    · exact False.elim ((hp.mp hleft) hleft)
    · exact False.elim (hleft (hp.mpr hleft))

theorem position_crosses_mem_crossingBlockIndex {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing)
    {p : Fin (2 * k)}
    (hp : middleLeft k p ↔ ¬ middleLeft k (M.move.map p)) :
    (M.move.block (M.crossingBlockIndex hM)).Mem p := by
  rcases exists_mem_crossing_block_of_position_crosses (M := M.move) hrev hp with
    ⟨i, hpi, hcross⟩
  have hi : i = M.crossingBlockIndex hM :=
    M.crossingBlockIndex_unique hM hcross
  rwa [hi] at hpi

theorem positionCrossingCard_le_crossingBlock_length {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing) :
    positionCrossingCard k M.move.map ≤
      (M.move.block (M.crossingBlockIndex hM)).length := by
  classical
  unfold positionCrossingCard
  let B := M.move.block (M.crossingBlockIndex hM)
  let f :
      {p : Fin (2 * k) // middleLeft k p ↔ ¬ middleLeft k (M.move.map p)} →
        {p : Fin (2 * k) // p ∈ B.toFinset} :=
    fun p => ⟨p.1, PositionInterval.mem_toFinset.mpr
      (M.position_crosses_mem_crossingBlockIndex hrev hM p.2)⟩
  have hinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x : {p : Fin (2 * k) // p ∈ B.toFinset} => (x : Fin (2 * k))) h
  have hcard := Fintype.card_le_of_injective f hinj
  have hBcard : Fintype.card {p : Fin (2 * k) // p ∈ B.toFinset} = B.length := by
    simpa using B.toFinset_card
  rwa [hBcard] at hcard

theorem positionCrossingCard_eq_two_mul_order_of_reversesBlocks {k : ℕ}
    {π ρ : State (2 * k)} (M : ReversalStep k π ρ)
    (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing) :
    positionCrossingCard k M.move.map = 2 * M.order := by
  classical
  let B := M.move.block (M.crossingBlockIndex hM)
  have hBcross : B.lo < k ∧ k ≤ B.hi :=
    M.crossingBlockIndex_spec hM
  have hcard :
      positionCrossingCard k M.move.map =
        (B.mirrorCrossingPositions k).card := by
    have hcardSubtype :
        Fintype.card
          {p : Fin (2 * k) // middleLeft k p ↔ ¬ middleLeft k (M.move.map p)} =
          Fintype.card {p : Fin (2 * k) // p ∈ B.mirrorCrossingPositions k} := by
      refine Fintype.card_congr ?_
      refine
      { toFun := ?_
        invFun := ?_
        left_inv := ?_
        right_inv := ?_ }
      · intro p
        refine ⟨p.1, ?_⟩
        have hpB : B.Mem p.1 :=
        M.position_crosses_mem_crossingBlockIndex hrev hM p.2
        by_cases hleft : middleLeft k p.1
        · have hmap_not_left : ¬ middleLeft k (M.move.map p.1) := p.2.mp hleft
          have hmap_eq : M.move.map p.1 = B.mirror p.1 hpB :=
            hrev.1 (M.crossingBlockIndex hM) p.1 hpB
          have hmirror_right : k ≤ (B.mirror p.1 hpB).val := by
            rw [← hmap_eq]
            exact not_lt.mp hmap_not_left
          have hle_sub : p.1.val ≤ B.lo + B.hi - k :=
            (B.le_mirror_iff_le_sub p.1 hpB hBcross.2).mp hmirror_right
          rw [PositionInterval.mirrorCrossingPositions, Finset.mem_union,
            PositionInterval.leftMirrorCrossingPositions,
            PositionInterval.rightMirrorCrossingPositions, Finset.mem_filter,
            Finset.mem_filter, PositionInterval.mem_toFinset]
          exact Or.inl ⟨hpB, hleft, hle_sub⟩
        · have hp_right : k ≤ p.1.val := not_lt.mp hleft
          have hmap_left : middleLeft k (M.move.map p.1) := by
            by_contra hmap_not_left
            exact hleft (p.2.mpr hmap_not_left)
          have hmap_eq : M.move.map p.1 = B.mirror p.1 hpB :=
            hrev.1 (M.crossingBlockIndex hM) p.1 hpB
          have hmirror_left : (B.mirror p.1 hpB).val < k := by
            rw [← hmap_eq]
            exact hmap_left
          have hthreshold : B.lo + B.hi + 1 - k ≤ p.1.val := by
            rw [B.mirror_lt_iff_sub_lt p.1 hpB] at hmirror_left
            rcases hpB with ⟨hlo, hhi⟩
            omega
          rw [PositionInterval.mirrorCrossingPositions, Finset.mem_union,
            PositionInterval.leftMirrorCrossingPositions,
            PositionInterval.rightMirrorCrossingPositions, Finset.mem_filter,
            Finset.mem_filter, PositionInterval.mem_toFinset]
          exact Or.inr ⟨hpB, hp_right, hthreshold⟩
      · intro p
        refine ⟨p.1, ?_⟩
        have hp_mem : p.1 ∈ B.mirrorCrossingPositions k := p.2
        simp [PositionInterval.mirrorCrossingPositions,
          PositionInterval.leftMirrorCrossingPositions,
          PositionInterval.rightMirrorCrossingPositions,
          PositionInterval.mem_toFinset] at hp_mem
        rcases hp_mem with hp_left | hp_right
        · rcases hp_left with ⟨hpB, hp_left, hle_sub⟩
          have hmap_eq : M.move.map p.1 = B.mirror p.1 hpB :=
            hrev.1 (M.crossingBlockIndex hM) p.1 hpB
          have hmirror_right : k ≤ (B.mirror p.1 hpB).val :=
            (B.le_mirror_iff_le_sub p.1 hpB hBcross.2).mpr hle_sub
          have hmap_not_left : ¬ middleLeft k (M.move.map p.1) := by
            rw [hmap_eq]
            exact not_lt.mpr hmirror_right
          exact iff_of_true hp_left hmap_not_left
        · rcases hp_right with ⟨hpB, hp_right, hthreshold⟩
          have hmap_eq : M.move.map p.1 = B.mirror p.1 hpB :=
            hrev.1 (M.crossingBlockIndex hM) p.1 hpB
          have hmirror_left : (B.mirror p.1 hpB).val < k := by
            rw [B.mirror_lt_iff_sub_lt p.1 hpB]
            rcases hpB with ⟨hlo, hhi⟩
            omega
          have hp_not_left : ¬ middleLeft k p.1 := not_lt.mpr hp_right
          have hmap_left : middleLeft k (M.move.map p.1) := by
            rw [hmap_eq]
            exact hmirror_left
          exact iff_of_false hp_not_left (not_not.mpr hmap_left)
      · intro p
        apply Subtype.ext
        rfl
      · intro p
        apply Subtype.ext
        rfl
    have hfinset :
        Fintype.card {p : Fin (2 * k) // p ∈ B.mirrorCrossingPositions k} =
          (B.mirrorCrossingPositions k).card := by
      simp
    exact (by
      simpa [positionCrossingCard] using hcardSubtype.trans hfinset)
  rw [hcard]
  rw [B.mirrorCrossingPositions_card_eq_two_mul_crossOrder_of_crossing hBcross]
  rw [M.order_eq_crossingBlockIndex_crossOrder hM]

/-- The labels crossing in one reversal step fit inside the full position set. -/
theorem two_mul_order_le_positions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) :
    2 * M.order ≤ 2 * k := by
  calc
    2 * M.order =
        ∑ i : Fin M.move.blockCount, 2 * (M.move.block i).crossOrder k := by
          simp [order, Finset.mul_sum]
    _ ≤ ∑ i : Fin M.move.blockCount, (M.move.block i).length := by
          exact Finset.sum_le_sum
            (by intro i _hi; exact PositionInterval.two_mul_crossOrder_le_length (M.move.block i))
    _ ≤ 2 * k := M.move.sum_block_lengths_le

theorem order_le_middle {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) :
    M.order ≤ k := by
  have h := M.two_mul_order_le_positions
  omega

theorem leftBarrierPositions_card_eq_order {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) :
    (PositionInterval.leftBarrierPositions k M.order).card = M.order :=
  PositionInterval.leftBarrierPositions_card_eq M.order_le_middle

theorem rightBarrierPositions_card_eq_order {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) :
    (PositionInterval.rightBarrierPositions k M.order).card = M.order :=
  PositionInterval.rightBarrierPositions_card_eq M.order_le_middle

theorem not_increasing_and_decreasing_leftBarrierPositions {k d : ℕ}
    {π : State (2 * k)} (hd : 2 ≤ d) (hdk : d ≤ k)
    (hinc : IncreasingOnPositions π (PositionInterval.leftBarrierPositions k d))
    (hdec : DecreasingOnPositions π (PositionInterval.leftBarrierPositions k d)) :
    False :=
  not_increasing_and_decreasing_on_two_positions hinc hdec (by
    rw [PositionInterval.leftBarrierPositions_card_eq hdk]
    exact hd)

theorem not_increasing_and_decreasing_rightBarrierPositions {k d : ℕ}
    {π : State (2 * k)} (hd : 2 ≤ d) (hdk : d ≤ k)
    (hinc : IncreasingOnPositions π (PositionInterval.rightBarrierPositions k d))
    (hdec : DecreasingOnPositions π (PositionInterval.rightBarrierPositions k d)) :
    False :=
  not_increasing_and_decreasing_on_two_positions hinc hdec (by
    rw [PositionInterval.rightBarrierPositions_card_eq hdk]
    exact hd)

theorem not_increasing_and_decreasing_centralBarrierPositions {k d : ℕ}
    {π : State (2 * k)} (hd : 0 < d) (hdk : d ≤ k)
    (hinc : IncreasingOnPositions π (PositionInterval.centralBarrierPositions k d))
    (hdec : DecreasingOnPositions π (PositionInterval.centralBarrierPositions k d)) :
    False :=
  not_increasing_and_decreasing_on_two_positions hinc hdec (by
    rw [PositionInterval.centralBarrierPositions_card_eq hdk]
    omega)

end ReversalStep

/-- The number of labels crossing the middle barrier in one concrete step. -/
noncomputable def stepCrossingLabelsCard (k : ℕ) (π ρ : State (2 * k)) : ℕ := by
  classical
  exact Fintype.card {a : Fin (2 * k) // crossesMiddle k π ρ a}

theorem stepCrossingLabelsCard_eq_labelCrossingCard
    (k : ℕ) (π ρ : State (2 * k)) :
    stepCrossingLabelsCard k π ρ = ReversalStep.labelCrossingCard k π ρ := by
  classical
  simp [stepCrossingLabelsCard, ReversalStep.labelCrossingCard]

theorem stepCrossingLabelsCard_eq_positionCrossingCard_of_reversesBlocks {k : ℕ}
    {π ρ : State (2 * k)} (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) :
    stepCrossingLabelsCard k π ρ = ReversalStep.positionCrossingCard k M.move.map := by
  rw [stepCrossingLabelsCard_eq_labelCrossingCard]
  exact M.crossingLabelsCard_eq_positionCrossingCard_of_reversesBlocks hrev

theorem crossed_labels_card_of_reversesBlocks {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) :
    stepCrossingLabelsCard k π ρ = 2 * M.order := by
  by_cases hM : M.IsCrossing
  · rw [stepCrossingLabelsCard_eq_positionCrossingCard_of_reversesBlocks M hrev]
    exact M.positionCrossingCard_eq_two_mul_order_of_reversesBlocks hrev hM
  · have horder : M.order = 0 := by
      unfold ReversalStep.IsCrossing at hM
      omega
    have hnone :
        ∀ i : Fin M.move.blockCount,
          ¬ ((M.move.block i).lo < k ∧ k ≤ (M.move.block i).hi) := by
      intro i hi
      exact hM ((M.isCrossing_iff_exists_crossing_block).mpr ⟨i, hi⟩)
    have hzero := ReversalStep.positionCrossingCard_eq_zero_of_no_crossing_block
      (k := k) (M := M.move) hrev hnone
    rw [stepCrossingLabelsCard_eq_positionCrossingCard_of_reversesBlocks M hrev,
      hzero, horder]

/--
A reversal step together with the key finite counting theorem for that step.
The block-reversal geometry should eventually prove this field.
-/
structure CountedReversalStep (k : ℕ) (π ρ : State (2 * k)) extends
    ReversalStep k π ρ where
  crossed_labels_card : stepCrossingLabelsCard k π ρ = 2 * toReversalStep.order

noncomputable def CountedReversalStep.ofReversesBlocks {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) :
    CountedReversalStep k π ρ where
  toReversalStep := M
  crossed_labels_card := crossed_labels_card_of_reversesBlocks M hrev

/-- A generalized allowable sequence with counted reversal data on every step. -/
structure CountedGeneralizedAllowableSequence (k r : ℕ) where
  seq : GeneralizedAllowableSequence k r
  step : ∀ j : Fin r, CountedReversalStep k (seq.π (stepFrom j)) (seq.π (stepTo j))

namespace CountedGeneralizedAllowableSequence

noncomputable def ofReversesBlocks {k r : ℕ} (A : GeneralizedAllowableSequence k r)
    (step : ∀ j : Fin r, ReversalStep k (A.π (stepFrom j)) (A.π (stepTo j)))
    (hrev : ∀ j : Fin r, (step j).move.ReversesBlocks) :
    CountedGeneralizedAllowableSequence k r where
  seq := A
  step := fun j => CountedReversalStep.ofReversesBlocks (step j) (hrev j)

/-- Counted reversal steps produce the `StepCounting` data used above. -/
noncomputable def toStepCounting {k r : ℕ} (A : CountedGeneralizedAllowableSequence k r) :
    GeneralizedAllowableSequence.StepCounting A.seq where
  order := fun j => (A.step j).toReversalStep.order
  crossed_labels_card := by
    intro j
    simpa [GeneralizedAllowableSequence.crossingLabelsCard, stepCrossingLabelsCard]
      using (A.step j).crossed_labels_card

def moveOrder {k r : ℕ} (A : CountedGeneralizedAllowableSequence k r) (j : Fin r) : ℕ :=
  (A.step j).toReversalStep.order

def IsCrossing {k r : ℕ} (A : CountedGeneralizedAllowableSequence k r) (j : Fin r) : Prop :=
  0 < A.moveOrder j

def ConsecutiveCrossing {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) (i j : Fin r) : Prop :=
  A.IsCrossing i ∧ A.IsCrossing j ∧ i.val < j.val ∧
    ∀ l : Fin r, i.val < l.val → l.val < j.val → ¬ A.IsCrossing l

def FirstCrossing {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) (i : Fin r) : Prop :=
  A.IsCrossing i ∧ ∀ l : Fin r, l.val < i.val → ¬ A.IsCrossing l

def LastCrossing {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) (i : Fin r) : Prop :=
  A.IsCrossing i ∧ ∀ l : Fin r, i.val < l.val → ¬ A.IsCrossing l

noncomputable def crossingMoves {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter A.IsCrossing

theorem mem_crossingMoves {k r : ℕ} {A : CountedGeneralizedAllowableSequence k r}
    {j : Fin r} :
    j ∈ A.crossingMoves ↔ A.IsCrossing j := by
  classical
  simp [crossingMoves]

theorem crossingLabelsCard_eq_two_mul_moveOrder {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) (j : Fin r) :
    GeneralizedAllowableSequence.crossingLabelsCard A.seq j = 2 * A.moveOrder j := by
  exact A.toStepCounting.crossed_labels_card j

theorem moveOrder_eq_middle_of_directFullMove {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) {j : Fin r}
    (hsource : A.seq.π (stepFrom j) = Equiv.refl (Fin (2 * k)))
    (htarget : A.seq.π (stepTo j) = reverseFin (2 * k)) :
    A.moveOrder j = k := by
  have hcount := A.crossingLabelsCard_eq_two_mul_moveOrder j
  have hfull := A.seq.crossingLabelsCard_eq_two_mul_of_refl_reverse j hsource htarget
  rw [hfull] at hcount
  omega

theorem isCrossing_of_directFullMove {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) (hk : 0 < k) {j : Fin r}
    (hsource : A.seq.π (stepFrom j) = Equiv.refl (Fin (2 * k)))
    (htarget : A.seq.π (stepTo j) = reverseFin (2 * k)) :
    A.IsCrossing j := by
  unfold IsCrossing
  rw [A.moveOrder_eq_middle_of_directFullMove hsource htarget]
  exact hk

theorem not_isCrossing_iff_moveOrder_eq_zero {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) (j : Fin r) :
    ¬ A.IsCrossing j ↔ A.moveOrder j = 0 := by
  unfold IsCrossing
  omega

theorem crossingLabelsCard_eq_zero_of_not_isCrossing {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) {j : Fin r}
    (hj : ¬ A.IsCrossing j) :
    GeneralizedAllowableSequence.crossingLabelsCard A.seq j = 0 := by
  rw [A.crossingLabelsCard_eq_two_mul_moveOrder j]
  rw [(A.not_isCrossing_iff_moveOrder_eq_zero j).mp hj]

theorem letters_cross {k r : ℕ} (A : CountedGeneralizedAllowableSequence k r) :
    2 * k ≤ ∑ j : Fin r, 2 * A.moveOrder j := by
  exact A.toStepCounting.letters_cross

theorem sum_moveOrder_eq_sum_crossingMoves {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) :
    (∑ j : Fin r, 2 * A.moveOrder j) =
      ∑ j ∈ A.crossingMoves, 2 * A.moveOrder j := by
  classical
  exact (Finset.sum_subset (Finset.subset_univ A.crossingMoves) (by
    intro j _hj hnot
    have hnotCross : ¬ A.IsCrossing j := by
      intro hjCross
      exact hnot (A.mem_crossingMoves.mpr hjCross)
    unfold IsCrossing at hnotCross
    have hzero : A.moveOrder j = 0 := by omega
    simp [hzero])).symm

theorem letters_cross_crossingMoves {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) :
    2 * k ≤ ∑ j ∈ A.crossingMoves, 2 * A.moveOrder j := by
  rw [← A.sum_moveOrder_eq_sum_crossingMoves]
  exact A.letters_cross

theorem exists_crossing_move {k r : ℕ} (A : CountedGeneralizedAllowableSequence k r)
    (hk : 0 < k) :
    ∃ j : Fin r, A.IsCrossing j := by
  classical
  let a : Fin (2 * k) := ⟨0, by omega⟩
  rcases A.seq.every_label_crosses a with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  have hcard_pos :
      0 < GeneralizedAllowableSequence.crossingLabelsCard A.seq j := by
    unfold GeneralizedAllowableSequence.crossingLabelsCard
    exact Fintype.card_pos_iff.mpr ⟨⟨a, hj⟩⟩
  have hcount := A.crossingLabelsCard_eq_two_mul_moveOrder j
  unfold IsCrossing
  omega

theorem crossingMoves_nonempty {k r : ℕ} (A : CountedGeneralizedAllowableSequence k r)
    (hk : 0 < k) :
    A.crossingMoves.Nonempty := by
  rcases A.exists_crossing_move hk with ⟨j, hj⟩
  exact ⟨j, A.mem_crossingMoves.mpr hj⟩

theorem crossingMoves_card_pos {k r : ℕ} (A : CountedGeneralizedAllowableSequence k r)
    (hk : 0 < k) :
    0 < A.crossingMoves.card := by
  exact Finset.card_pos.mpr (A.crossingMoves_nonempty hk)

noncomputable def crossingIdx {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) :
    Fin A.crossingMoves.card → Fin r :=
  A.crossingMoves.orderEmbOfFin rfl

theorem crossingIdx_mem {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) (i : Fin A.crossingMoves.card) :
    A.crossingIdx i ∈ A.crossingMoves := by
  classical
  simp [crossingIdx]

theorem crossingIdx_isCrossing {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) (i : Fin A.crossingMoves.card) :
    A.IsCrossing (A.crossingIdx i) := by
  exact A.mem_crossingMoves.mp (A.crossingIdx_mem i)

theorem crossingIdx_strict {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) {i j : Fin A.crossingMoves.card}
    (hij : i < j) :
    (A.crossingIdx i).val < (A.crossingIdx j).val := by
  change A.crossingIdx i < A.crossingIdx j
  exact (A.crossingMoves.orderEmbOfFin rfl).strictMono hij

theorem not_isCrossing_between_crossingIdx_succ {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (i : ℕ) (hi : i + 1 < A.crossingMoves.card) {j : Fin r}
    (hlo : (A.crossingIdx ⟨i, by omega⟩).val < j.val)
    (hhi : j.val < (A.crossingIdx ⟨i + 1, by omega⟩).val) :
    ¬ A.IsCrossing j := by
  classical
  intro hjCross
  have hjmem : j ∈ A.crossingMoves := A.mem_crossingMoves.mpr hjCross
  have hmap :
      Finset.map (A.crossingMoves.orderEmbOfFin rfl).toEmbedding Finset.univ =
        A.crossingMoves :=
    Finset.map_orderEmbOfFin_univ A.crossingMoves rfl
  have hjmap : j ∈ Finset.map (A.crossingMoves.orderEmbOfFin rfl).toEmbedding Finset.univ := by
    rwa [hmap]
  rcases Finset.mem_map.mp hjmap with ⟨l, _hlmem, hlj⟩
  have hlj' : A.crossingIdx l = j := by
    simpa [crossingIdx] using hlj
  have hcases : l.val ≤ i ∨ i + 1 ≤ l.val := by omega
  rcases hcases with hle | hle
  · have hfinle : l ≤ (⟨i, by omega⟩ : Fin A.crossingMoves.card) := by
      change l.val ≤ i
      exact hle
    have hidxle : A.crossingIdx l ≤ A.crossingIdx ⟨i, by omega⟩ := by
      change (A.crossingMoves.orderEmbOfFin rfl l) ≤
        A.crossingMoves.orderEmbOfFin rfl ⟨i, by omega⟩
      exact (A.crossingMoves.orderEmbOfFin rfl).monotone hfinle
    have hvalle : j.val ≤ (A.crossingIdx ⟨i, by omega⟩).val := by
      have hvaleq : (A.crossingIdx l).val = j.val := congrArg Fin.val hlj'
      have hidxle_val : (A.crossingIdx l).val ≤ (A.crossingIdx ⟨i, by omega⟩).val :=
        hidxle
      omega
    omega
  · have hfinle : (⟨i + 1, by omega⟩ : Fin A.crossingMoves.card) ≤ l := by
      change i + 1 ≤ l.val
      exact hle
    have hidxle : A.crossingIdx ⟨i + 1, by omega⟩ ≤ A.crossingIdx l := by
      change (A.crossingMoves.orderEmbOfFin rfl ⟨i + 1, by omega⟩) ≤
        A.crossingMoves.orderEmbOfFin rfl l
      exact (A.crossingMoves.orderEmbOfFin rfl).monotone hfinle
    have hvalle : (A.crossingIdx ⟨i + 1, by omega⟩).val ≤ j.val := by
      have hvaleq : (A.crossingIdx l).val = j.val := congrArg Fin.val hlj'
      have hidxle_val : (A.crossingIdx ⟨i + 1, by omega⟩).val ≤
          (A.crossingIdx l).val :=
        hidxle
      omega
    omega

theorem not_isCrossing_before_first_crossingIdx {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (hpos : 0 < A.crossingMoves.card) {j : Fin r}
    (hbefore : j.val < (A.crossingIdx ⟨0, hpos⟩).val) :
    ¬ A.IsCrossing j := by
  classical
  intro hjCross
  have hjmem : j ∈ A.crossingMoves := A.mem_crossingMoves.mpr hjCross
  have hmap :
      Finset.map (A.crossingMoves.orderEmbOfFin rfl).toEmbedding Finset.univ =
        A.crossingMoves :=
    Finset.map_orderEmbOfFin_univ A.crossingMoves rfl
  have hjmap : j ∈ Finset.map (A.crossingMoves.orderEmbOfFin rfl).toEmbedding Finset.univ := by
    rwa [hmap]
  rcases Finset.mem_map.mp hjmap with ⟨l, _hlmem, hlj⟩
  have hlj' : A.crossingIdx l = j := by
    simpa [crossingIdx] using hlj
  have hfinle : (⟨0, hpos⟩ : Fin A.crossingMoves.card) ≤ l := by
    change 0 ≤ l.val
    omega
  have hidxle : A.crossingIdx ⟨0, hpos⟩ ≤ A.crossingIdx l := by
    change (A.crossingMoves.orderEmbOfFin rfl ⟨0, hpos⟩) ≤
      A.crossingMoves.orderEmbOfFin rfl l
    exact (A.crossingMoves.orderEmbOfFin rfl).monotone hfinle
  have hvaleq : (A.crossingIdx l).val = j.val := congrArg Fin.val hlj'
  have hidxle_val : (A.crossingIdx ⟨0, hpos⟩).val ≤ (A.crossingIdx l).val :=
    hidxle
  omega

theorem not_isCrossing_after_last_crossingIdx {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (hpos : 0 < A.crossingMoves.card) {j : Fin r}
    (hafter : (A.crossingIdx ⟨A.crossingMoves.card - 1, by omega⟩).val < j.val) :
    ¬ A.IsCrossing j := by
  classical
  intro hjCross
  have hjmem : j ∈ A.crossingMoves := A.mem_crossingMoves.mpr hjCross
  have hmap :
      Finset.map (A.crossingMoves.orderEmbOfFin rfl).toEmbedding Finset.univ =
        A.crossingMoves :=
    Finset.map_orderEmbOfFin_univ A.crossingMoves rfl
  have hjmap : j ∈ Finset.map (A.crossingMoves.orderEmbOfFin rfl).toEmbedding Finset.univ := by
    rwa [hmap]
  rcases Finset.mem_map.mp hjmap with ⟨l, _hlmem, hlj⟩
  have hlj' : A.crossingIdx l = j := by
    simpa [crossingIdx] using hlj
  have hfinle : l ≤ (⟨A.crossingMoves.card - 1, by omega⟩ :
      Fin A.crossingMoves.card) := by
    change l.val ≤ A.crossingMoves.card - 1
    omega
  have hidxle : A.crossingIdx l ≤
      A.crossingIdx ⟨A.crossingMoves.card - 1, by omega⟩ := by
    change (A.crossingMoves.orderEmbOfFin rfl l) ≤
      A.crossingMoves.orderEmbOfFin rfl ⟨A.crossingMoves.card - 1, by omega⟩
    exact (A.crossingMoves.orderEmbOfFin rfl).monotone hfinle
  have hvaleq : (A.crossingIdx l).val = j.val := congrArg Fin.val hlj'
  have hidxle_val : (A.crossingIdx l).val ≤
      (A.crossingIdx ⟨A.crossingMoves.card - 1, by omega⟩).val :=
    hidxle
  omega

theorem consecutive_crossingIdx_succ {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (i : ℕ) (hi : i + 1 < A.crossingMoves.card) :
    A.ConsecutiveCrossing (A.crossingIdx ⟨i, by omega⟩)
      (A.crossingIdx ⟨i + 1, by omega⟩) := by
  refine ⟨A.crossingIdx_isCrossing _, A.crossingIdx_isCrossing _, ?_, ?_⟩
  · have hfinlt :
        (⟨i, by omega⟩ : Fin A.crossingMoves.card) <
          (⟨i + 1, by omega⟩ : Fin A.crossingMoves.card) := by
        change i < i + 1
        omega
    exact A.crossingIdx_strict hfinlt
  · intro l hlo hhi
    exact A.not_isCrossing_between_crossingIdx_succ i hi hlo hhi

theorem first_crossingIdx {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (hpos : 0 < A.crossingMoves.card) :
    A.FirstCrossing (A.crossingIdx ⟨0, hpos⟩) := by
  refine ⟨A.crossingIdx_isCrossing _, ?_⟩
  intro l hlt
  exact A.not_isCrossing_before_first_crossingIdx hpos hlt

theorem last_crossingIdx {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (hpos : 0 < A.crossingMoves.card) :
    A.LastCrossing (A.crossingIdx ⟨A.crossingMoves.card - 1, by omega⟩) := by
  refine ⟨A.crossingIdx_isCrossing _, ?_⟩
  intro l hlt
  exact A.not_isCrossing_after_last_crossingIdx hpos hlt

theorem sum_crossingIdx_eq_sum_crossingMoves {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) :
    (∑ i : Fin A.crossingMoves.card, 2 * A.moveOrder (A.crossingIdx i)) =
      ∑ j ∈ A.crossingMoves, 2 * A.moveOrder j := by
  classical
  calc
    (∑ i : Fin A.crossingMoves.card, 2 * A.moveOrder (A.crossingIdx i)) =
        ∑ j ∈ Finset.map (A.crossingMoves.orderEmbOfFin rfl).toEmbedding Finset.univ,
          2 * A.moveOrder j := by
          exact (Finset.univ.sum_map (A.crossingMoves.orderEmbOfFin rfl).toEmbedding
            (fun j => 2 * A.moveOrder j)).symm
    _ = ∑ j ∈ A.crossingMoves, 2 * A.moveOrder j := by
          rw [Finset.map_orderEmbOfFin_univ]

theorem letters_cross_crossingIdx {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) :
    2 * k ≤ ∑ i : Fin A.crossingMoves.card, 2 * A.moveOrder (A.crossingIdx i) := by
  rw [A.sum_crossingIdx_eq_sum_crossingMoves]
  exact A.letters_cross_crossingMoves

theorem crossingMoves_card_ne_one_of_no_full_crossing {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (hnoFull : ∀ j : Fin r, A.IsCrossing j → A.moveOrder j < k) :
    A.crossingMoves.card ≠ 1 := by
  intro hcard
  have hpos : 0 < A.crossingMoves.card := by omega
  let i0 : Fin A.crossingMoves.card := ⟨0, hpos⟩
  have hall : ∀ i : Fin A.crossingMoves.card, i = i0 := by
    intro i
    apply Fin.ext
    dsimp [i0]
    omega
  have hsum_eq :
      (∑ i : Fin A.crossingMoves.card, 2 * A.moveOrder (A.crossingIdx i)) =
        2 * A.moveOrder (A.crossingIdx i0) := by
    rw [Finset.sum_eq_single i0]
    · intro b _hb hbne
      exact False.elim (hbne (hall b))
    · intro hnot
      exact False.elim (hnot (by simp))
  have hletters := A.letters_cross_crossingIdx
  rw [hsum_eq] at hletters
  have hlt : A.moveOrder (A.crossingIdx i0) < k :=
    hnoFull (A.crossingIdx i0) (A.crossingIdx_isCrossing i0)
  omega

theorem two_le_crossingMoves_card_of_no_full_crossing {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) (hk : 0 < k)
    (hnoFull : ∀ j : Fin r, A.IsCrossing j → A.moveOrder j < k) :
    2 ≤ A.crossingMoves.card := by
  have hpos := A.crossingMoves_card_pos hk
  by_contra hnot
  have hcard : A.crossingMoves.card = 1 := by omega
  exact A.crossingMoves_card_ne_one_of_no_full_crossing hnoFull hcard

noncomputable def toMoveSchedule {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (htwo : 2 ≤ A.crossingMoves.card)
    (hgap_between :
      ∀ (i : ℕ) (hi : i + 1 < A.crossingMoves.card),
        A.moveOrder (A.crossingIdx ⟨i, by omega⟩) +
            A.moveOrder (A.crossingIdx ⟨i + 1, by omega⟩) - 1 ≤
          (A.crossingIdx ⟨i + 1, by omega⟩).val -
            (A.crossingIdx ⟨i, by omega⟩).val - 1)
    (hgap_ends :
      A.moveOrder (A.crossingIdx ⟨0, by omega⟩) +
          A.moveOrder (A.crossingIdx ⟨A.crossingMoves.card - 1, by omega⟩) - 1 ≤
        (A.crossingIdx ⟨0, by omega⟩).val +
          (r - 1 - (A.crossingIdx ⟨A.crossingMoves.card - 1, by omega⟩).val)) :
    UngarMoveSchedule k r where
  crossingCount := A.crossingMoves.card
  order := fun i => A.moveOrder (A.crossingIdx i)
  letters_cross := A.letters_cross_crossingIdx
  two_le_crossingCount := htwo
  idx := A.crossingIdx
  idx_strict := by
    intro i j hij
    exact A.crossingIdx_strict hij
  order_pos := by
    intro i
    exact A.crossingIdx_isCrossing i
  gap_between := hgap_between
  gap_ends := hgap_ends

/--
The finite Ungar conclusion extracted from a counted sequence once the T/O/C
gap inequalities have been proved for the ordered crossing moves.
-/
theorem length_lower_bound_from_gaps {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (htwo : 2 ≤ A.crossingMoves.card)
    (hgap_between :
      ∀ (i : ℕ) (hi : i + 1 < A.crossingMoves.card),
        A.moveOrder (A.crossingIdx ⟨i, by omega⟩) +
            A.moveOrder (A.crossingIdx ⟨i + 1, by omega⟩) - 1 ≤
          (A.crossingIdx ⟨i + 1, by omega⟩).val -
            (A.crossingIdx ⟨i, by omega⟩).val - 1)
    (hgap_ends :
      A.moveOrder (A.crossingIdx ⟨0, by omega⟩) +
          A.moveOrder (A.crossingIdx ⟨A.crossingMoves.card - 1, by omega⟩) - 1 ≤
        (A.crossingIdx ⟨0, by omega⟩).val +
          (r - 1 - (A.crossingIdx ⟨A.crossingMoves.card - 1, by omega⟩).val)) :
    2 * k ≤ r :=
  (A.toMoveSchedule htwo hgap_between hgap_ends).toCountingCertificate.length_lower_bound

/-- Counted reversal steps plus a packing proof give a counting certificate. -/
noncomputable def toCountingCertificate {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (packing : UngarBlockPacking r r A.toStepCounting.order) :
    UngarCountingCertificate (2 * k) r :=
  A.toStepCounting.toCountingCertificate packing

/-- The finite Ungar conclusion extracted from a counted sequence and packing. -/
theorem length_lower_bound {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (packing : UngarBlockPacking r r A.toStepCounting.order) :
    2 * k ≤ r :=
  (A.toCountingCertificate packing).length_lower_bound

end CountedGeneralizedAllowableSequence

/--
A counted generalized allowable sequence that still remembers the concrete
block-reversal semantics of every step.  The counting layer alone is enough
for `letters_cross`; the gap proof needs this pointwise reversal information.
-/
structure ConcreteGeneralizedAllowableSequence (k r : ℕ) extends
    CountedGeneralizedAllowableSequence k r where
  reversesBlocks :
    ∀ j : Fin r, (step j).toReversalStep.move.ReversesBlocks

namespace ConcreteGeneralizedAllowableSequence

def stateAt {k r : ℕ} (A : ConcreteGeneralizedAllowableSequence k r)
    (m : ℕ) (hm : m ≤ r) : State (2 * k) :=
  A.seq.π ⟨m, Nat.lt_succ_of_le hm⟩

theorem stateAt_eq_of_proofs {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r)
    {m : ℕ} (hm₁ hm₂ : m ≤ r) :
    A.stateAt m hm₁ = A.stateAt m hm₂ := by
  simp [stateAt]

def NoDirectFullMove {k r : ℕ} (A : ConcreteGeneralizedAllowableSequence k r) : Prop :=
  ∀ j : Fin r,
    A.seq.π (stepFrom j) ≠ Equiv.refl (Fin (2 * k)) ∨
      A.seq.π (stepTo j) ≠ reverseFin (2 * k)

def FullMoveForcesCommonDirection {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) (points : Finset Point2) : Prop :=
  ∀ j : Fin r,
    A.seq.π (stepFrom j) = Equiv.refl (Fin (2 * k)) →
      A.seq.π (stepTo j) = reverseFin (2 * k) →
        ∃ d : Direction,
          ∀ p ∈ points, ∀ q ∈ points, p ≠ q → direction p q = d

def DirectFullMoveForcesCommonLevel {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {points : Finset Point2}
    (L : PointLabeling points k) (stepDir : Fin r → Direction) : Prop :=
  ∀ j : Fin r,
    A.seq.π (stepFrom j) = Equiv.refl (Fin (2 * k)) →
      A.seq.π (stepTo j) = reverseFin (2 * k) →
        ∃ c : ℝ, ∀ a : Fin (2 * k), directionLevel (stepDir j) (L.point a) = c

def StepDirectionsEnumerate (points : Finset Point2)
    (stepDir : Fin (directionsDeterminedBy points).card → Direction) : Prop :=
  (∀ j, stepDir j ∈ directionsDeterminedBy points) ∧ Function.Injective stepDir

def BlocksHaveCommonLevel {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {points : Finset Point2}
    (L : PointLabeling points k) (stepDir : Fin r → Direction) : Prop :=
  ∀ j : Fin r, ∀ b : Fin (A.step j).toReversalStep.move.blockCount,
    ∃ c : ℝ, ∀ p : Fin (2 * k),
      ((A.step j).toReversalStep.move.block b).Mem p →
        directionLevel (stepDir j)
          (L.point (A.seq.π (stepFrom j) p)) = c

theorem directFullMoveForcesCommonLevel_of_blocksHaveCommonLevel {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) (hk : 0 < k)
    {points : Finset Point2} (L : PointLabeling points k)
    (stepDir : Fin r → Direction)
    (hblocks : A.BlocksHaveCommonLevel L stepDir) :
    A.DirectFullMoveForcesCommonLevel L stepDir := by
  intro j hsource htarget
  have hj :
      (A.step j).toReversalStep.IsCrossing := by
    have hjA :=
      A.toCountedGeneralizedAllowableSequence.isCrossing_of_directFullMove
        hk hsource htarget
    simpa [CountedGeneralizedAllowableSequence.IsCrossing,
      CountedGeneralizedAllowableSequence.moveOrder, ReversalStep.IsCrossing] using hjA
  let b := (A.step j).toReversalStep.crossingBlockIndex hj
  rcases hblocks j b with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro a
  have hfull :=
    (A.step j).toReversalStep.crossingBlock_eq_full_of_order_eq_middle hj hk
      (A.toCountedGeneralizedAllowableSequence.moveOrder_eq_middle_of_directFullMove
        hsource htarget)
  have ha_mem :
      ((A.step j).toReversalStep.move.block b).Mem a := by
    dsimp [PositionInterval.Mem, b]
    constructor
    · rw [hfull.1]
      exact Nat.zero_le _
    · rw [hfull.2]
      exact Nat.le_sub_one_of_lt a.isLt
  have hstate : A.seq.π (stepFrom j) a = a := by
    rw [hsource]
    rfl
  simpa [hstate] using hc a ha_mem

theorem direction_eq_stepDir_of_same_block {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {points : Finset Point2}
    (L : PointLabeling points k) (stepDir : Fin r → Direction)
    (hblocks : A.BlocksHaveCommonLevel L stepDir) {j : Fin r}
    {b : Fin (A.step j).toReversalStep.move.blockCount} {p q : Fin (2 * k)}
    (hp : ((A.step j).toReversalStep.move.block b).Mem p)
    (hq : ((A.step j).toReversalStep.move.block b).Mem q)
    (hlabels :
      A.seq.π (stepFrom j) p ≠ A.seq.π (stepFrom j) q) :
    direction
        (L.point (A.seq.π (stepFrom j) p))
        (L.point (A.seq.π (stepFrom j) q)) = stepDir j := by
  rcases hblocks j b with ⟨c, hc⟩
  have hpoints :
      L.point (A.seq.π (stepFrom j) p) ≠
        L.point (A.seq.π (stepFrom j) q) := by
    intro hpoint
    exact hlabels (L.point_injective hpoint)
  exact direction_eq_of_directionLevel_eq hpoints ((hc p hp).trans (hc q hq).symm)

theorem stepDir_mem_of_blocksHaveCommonLevel {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {points : Finset Point2}
    (L : PointLabeling points k) (stepDir : Fin r → Direction)
    (hblocks : A.BlocksHaveCommonLevel L stepDir) (j : Fin r) :
    stepDir j ∈ directionsDeterminedBy points := by
  let b : Fin (A.step j).toReversalStep.move.blockCount :=
    ⟨0, (A.step j).toReversalStep.move.blockCount_pos⟩
  rcases PositionInterval.exists_two_mem_of_two_le_length
      ((A.step j).toReversalStep.move.block b)
      ((A.step j).toReversalStep.move.nontrivial b) with
    ⟨p, q, hp, hq, hpq⟩
  have hlabels :
      A.seq.π (stepFrom j) p ≠ A.seq.π (stepFrom j) q := by
    intro h
    exact hpq ((A.seq.π (stepFrom j)).injective h)
  have hdir :=
    A.direction_eq_stepDir_of_same_block L stepDir hblocks hp hq hlabels
  rw [← hdir]
  exact direction_mem_directionsDeterminedBy
    (L.mem_point (A.seq.π (stepFrom j) p))
    (L.mem_point (A.seq.π (stepFrom j) q))
    (by
      intro hpoint
      exact hlabels (L.point_injective hpoint))

theorem stepDirectionsEnumerate_of_blocksHaveCommonLevel_of_injective
    {points : Finset Point2} {k : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy points).card)
    (L : PointLabeling points k)
    (stepDir : Fin (directionsDeterminedBy points).card → Direction)
    (hblocks : A.BlocksHaveCommonLevel L stepDir)
    (hinj : Function.Injective stepDir) :
    StepDirectionsEnumerate points stepDir :=
  ⟨A.stepDir_mem_of_blocksHaveCommonLevel L stepDir hblocks, hinj⟩

theorem stepDirectionsEnumerate_surjective_on {points : Finset Point2}
    {stepDir : Fin (directionsDeterminedBy points).card → Direction}
    (henum : StepDirectionsEnumerate points stepDir) :
    ∀ d ∈ directionsDeterminedBy points, ∃ j, stepDir j = d := by
  intro d hd
  by_contra hnot
  simp at hnot
  have hsub :
      (Finset.univ.image stepDir) ⊆ directionsDeterminedBy points := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
    exact henum.1 j
  have hd_not_image : d ∉ Finset.univ.image stepDir := by
    intro hdimg
    rcases Finset.mem_image.mp hdimg with ⟨j, _hj, hj⟩
    exact hnot j hj
  have hproper :
      (Finset.univ.image stepDir) ⊂ directionsDeterminedBy points := by
    exact ⟨hsub, by
      intro hle
      exact hd_not_image (hle hd)⟩
  have hcard_lt :
      (Finset.univ.image stepDir).card < (directionsDeterminedBy points).card :=
    Finset.card_lt_card hproper
  have hcard_image :
      (Finset.univ.image stepDir).card =
        Fintype.card (Fin (directionsDeterminedBy points).card) := by
    rw [Finset.card_image_of_injective _ henum.2]
    simp
  rw [hcard_image, Fintype.card_fin] at hcard_lt
  omega

theorem fullMoveForcesCommonDirection_of_directFullMoveForcesCommonLevel {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {points : Finset Point2}
    (L : PointLabeling points k) (stepDir : Fin r → Direction)
    (hlevel : A.DirectFullMoveForcesCommonLevel L stepDir) :
    A.FullMoveForcesCommonDirection points := by
  intro j hsource htarget
  rcases hlevel j hsource htarget with ⟨c, hcommon⟩
  refine ⟨stepDir j, ?_⟩
  intro p hp q hq hpq
  rcases L.point_surjective_on p hp with ⟨a, ha⟩
  rcases L.point_surjective_on q hq with ⟨b, hb⟩
  rw [← ha, ← hb]
  have hab : L.point a ≠ L.point b := by
    intro hsame
    exact hpq (by rw [← ha, ← hb, hsame])
  exact direction_eq_of_directionLevel_eq hab ((hcommon a).trans (hcommon b).symm)

theorem noDirectFullMove_of_directFullMoveForcesCommonLevel {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {points : Finset Point2}
    (L : PointLabeling points k) (stepDir : Fin r → Direction)
    (hncoll : NoncollinearSet points)
    (hlevel : A.DirectFullMoveForcesCommonLevel L stepDir) :
    A.NoDirectFullMove := by
  intro j
  by_cases hsource : A.seq.π (stepFrom j) = Equiv.refl (Fin (2 * k))
  · right
    intro htarget
    rcases hlevel j hsource htarget with ⟨c, hcommon⟩
    exact not_all_directionLevels_eq_of_noncollinearSet hncoll (stepDir j)
      ⟨c, by
        intro p hp
        rcases L.point_surjective_on p hp with ⟨a, ha⟩
        rw [← ha]
        exact hcommon a⟩
  · exact Or.inl hsource

theorem noDirectFullMove_of_fullMoveForcesCommonDirection {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {points : Finset Point2}
    (hncoll : NoncollinearSet points)
    (hfull : A.FullMoveForcesCommonDirection points) :
    A.NoDirectFullMove := by
  intro j
  by_cases hsource : A.seq.π (stepFrom j) = Equiv.refl (Fin (2 * k))
  · right
    intro htarget
    exact not_all_pair_directions_eq_of_noncollinearSet hncoll
      (hfull j hsource htarget)
  · exact Or.inl hsource

theorem moveOrder_lt_middle_of_noDirectFullMove {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) (hk : 0 < k)
    (hnoFull : A.NoDirectFullMove) :
    ∀ j : Fin r, A.toCountedGeneralizedAllowableSequence.IsCrossing j →
      A.toCountedGeneralizedAllowableSequence.moveOrder j < k := by
  intro j hj
  by_contra hnot_lt
  have hle :
      A.toCountedGeneralizedAllowableSequence.moveOrder j ≤ k :=
    (A.step j).toReversalStep.order_le_middle
  have horder :
      A.toCountedGeneralizedAllowableSequence.moveOrder j = k := by
    omega
  have hsource :
      A.seq.π (stepFrom j) = Equiv.refl (Fin (2 * k)) :=
    (A.step j).toReversalStep.source_eq_refl_of_order_eq_middle hj hk horder
  have htarget :
      A.seq.π (stepTo j) = reverseFin (2 * k) :=
    (A.step j).toReversalStep.target_eq_reverseFin_of_order_eq_middle
      (A.reversesBlocks j) hj hk horder
  rcases hnoFull j with hbad | hbad
  · exact hbad hsource
  · exact hbad htarget

theorem crossingBlock_eq_full_of_directFullMove {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) (hk : 0 < k) {j : Fin r}
    (hsource : A.seq.π (stepFrom j) = Equiv.refl (Fin (2 * k)))
    (htarget : A.seq.π (stepTo j) = reverseFin (2 * k)) :
    ((A.step j).toReversalStep.move.block
          ((A.step j).toReversalStep.crossingBlockIndex (by
            have hj :=
              A.toCountedGeneralizedAllowableSequence.isCrossing_of_directFullMove
                hk hsource htarget
            simpa [CountedGeneralizedAllowableSequence.IsCrossing,
              CountedGeneralizedAllowableSequence.moveOrder, ReversalStep.IsCrossing] using hj))).lo = 0 ∧
      ((A.step j).toReversalStep.move.block
          ((A.step j).toReversalStep.crossingBlockIndex (by
            have hj :=
              A.toCountedGeneralizedAllowableSequence.isCrossing_of_directFullMove
                hk hsource htarget
            simpa [CountedGeneralizedAllowableSequence.IsCrossing,
              CountedGeneralizedAllowableSequence.moveOrder, ReversalStep.IsCrossing] using hj))).hi =
        2 * k - 1 := by
  have hj :
      (A.step j).toReversalStep.IsCrossing := by
    have hjA :=
      A.toCountedGeneralizedAllowableSequence.isCrossing_of_directFullMove
        hk hsource htarget
    simpa [CountedGeneralizedAllowableSequence.IsCrossing,
      CountedGeneralizedAllowableSequence.moveOrder, ReversalStep.IsCrossing] using hjA
  have horder :
      (A.step j).toReversalStep.order = k :=
    A.toCountedGeneralizedAllowableSequence.moveOrder_eq_middle_of_directFullMove
      hsource htarget
  simpa using
    (A.step j).toReversalStep.crossingBlock_eq_full_of_order_eq_middle hj hk horder

noncomputable def ofReversesBlocks {k r : ℕ} (A : GeneralizedAllowableSequence k r)
    (step : ∀ j : Fin r, ReversalStep k (A.π (stepFrom j)) (A.π (stepTo j)))
    (hrev : ∀ j : Fin r, (step j).move.ReversesBlocks) :
    ConcreteGeneralizedAllowableSequence k r where
  seq := A
  step := fun j => CountedReversalStep.ofReversesBlocks (step j) (hrev j)
  reversesBlocks := hrev

theorem noncrossing_step_preserves_label_side {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {j : Fin r}
    (hj : ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing j) (a : Fin (2 * k)) :
    middleLeft k ((A.seq.π (stepTo j)).symm a) ↔
      middleLeft k ((A.seq.π (stepFrom j)).symm a) := by
  exact (A.step j).toReversalStep.middleLeft_new_position_iff_of_not_isCrossing
    (A.reversesBlocks j) hj a

theorem noncrossing_range_preserves_label_side {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ r)
    (hnc : ∀ l : Fin r, i ≤ l.val → l.val < j →
      ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing l)
    (a : Fin (2 * k)) :
      middleLeft k ((A.stateAt j hj).symm a) ↔
      middleLeft k ((A.stateAt i (le_trans hij hj)).symm a) := by
  have hmain :
      ∀ (n : ℕ) (hn : n ≤ j - i),
        middleLeft k ((A.stateAt (i + n) (by omega)).symm a) ↔
          middleLeft k ((A.stateAt i (by omega)).symm a) := by
    intro n
    induction n with
    | zero =>
        refine fun _hn => ?_
        simp [stateAt]
    | succ n ih =>
        refine fun hn => ?_
        have hnlt : i + n < r := by omega
        have hnc_step :
            ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing ⟨i + n, hnlt⟩ :=
          hnc ⟨i + n, hnlt⟩
            (by
              change i ≤ i + n
              omega)
            (by
              change i + n < j
              omega)
        have hstep :=
          A.noncrossing_step_preserves_label_side (j := ⟨i + n, hnlt⟩) hnc_step a
        have ih_n := ih (by omega)
        change middleLeft k ((A.stateAt (i + (n + 1)) (by omega)).symm a) ↔
          middleLeft k ((A.stateAt i (by omega)).symm a)
        exact hstep.trans ih_n
  have hsum : i + (j - i) = j := Nat.add_sub_of_le hij
  have h := hmain (j - i) (by omega)
  simpa [hsum] using h

theorem decreasing_persists_over_noncrossing_steps {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r)
    (a n d : ℕ) (hend : a + n ≤ r)
    (hnc : ∀ l : Fin r, a ≤ l.val → l.val < a + n →
      ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing l)
    (hdec :
      ReversalStep.DecreasingOnPositions (A.stateAt a (by omega))
        (PositionInterval.centralBarrierPositions k d)) :
    ReversalStep.DecreasingOnPositions (A.stateAt (a + n) hend)
      (PositionInterval.centralBarrierPositions k (d - n)) := by
  induction n generalizing a d with
  | zero =>
      simpa [stateAt]
  | succ n ih =>
      have hend_n : a + n ≤ r := by omega
      have hnc_n :
          ∀ l : Fin r, a ≤ l.val → l.val < a + n →
            ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing l := by
        intro l hla hln
        exact hnc l hla (by omega)
      have hdec_n := ih a d hend_n hnc_n hdec
      have hnlt : a + n < r := by omega
      let j : Fin r := ⟨a + n, hnlt⟩
      have hnc_j : ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing j :=
        hnc j (by dsimp [j]; omega) (by dsimp [j]; omega)
      have hsource :
          A.stateAt (a + n) hend_n = A.seq.π (stepFrom j) := by
        apply congrArg A.seq.π
        apply Fin.ext
        simp [stepFrom, j]
      have htarget :
          A.stateAt (a + (n + 1)) hend = A.seq.π (stepTo j) := by
        apply congrArg A.seq.π
        apply Fin.ext
        simp [stepTo, j]
        omega
      rw [hsource] at hdec_n
      have hstep :=
        (A.step j).toReversalStep.decreasing_after_smaller_central_of_decreasing_before_nonCrossing
          (A.reversesBlocks j) hnc_j hdec_n
      rw [← htarget] at hstep
      have hrad : d - (n + 1) = d - n - 1 := by omega
      simpa [Nat.add_assoc, hrad] using hstep

theorem increasing_persists_back_over_noncrossing_steps {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r)
    (a n d : ℕ) (hend : a + n ≤ r)
    (hnc : ∀ l : Fin r, a ≤ l.val → l.val < a + n →
      ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing l)
    (hinc :
      ReversalStep.IncreasingOnPositions (A.stateAt (a + n) hend)
        (PositionInterval.centralBarrierPositions k d)) :
    ReversalStep.IncreasingOnPositions (A.stateAt a (by omega))
      (PositionInterval.centralBarrierPositions k (d - n)) := by
  induction n generalizing a d with
  | zero =>
      simpa [stateAt] using hinc
  | succ n ih =>
      have hend_n : a + n ≤ r := by omega
      have hnlt : a + n < r := by omega
      let j : Fin r := ⟨a + n, hnlt⟩
      have hnc_j : ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing j :=
        hnc j (by dsimp [j]; omega) (by dsimp [j]; omega)
      have htarget :
          A.stateAt (a + (n + 1)) hend = A.seq.π (stepTo j) := by
        apply congrArg A.seq.π
        apply Fin.ext
        simp [stepTo, j]
        omega
      rw [htarget] at hinc
      have hprev_step :=
        (A.step j).toReversalStep.increasing_before_smaller_central_of_increasing_after_nonCrossing
          (A.reversesBlocks j) hnc_j hinc
      have hsource :
          A.stateAt (a + n) hend_n = A.seq.π (stepFrom j) := by
        apply congrArg A.seq.π
        apply Fin.ext
        simp [stepFrom, j]
      rw [← hsource] at hprev_step
      have hnc_n :
          ∀ l : Fin r, a ≤ l.val → l.val < a + n →
            ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing l := by
        intro l hla hln
        exact hnc l hla (by omega)
      have hstart := ih a (d - 1) hend_n hnc_n hprev_step
      have hrad : d - (n + 1) = d - 1 - n := by omega
      simpa [Nat.add_assoc, hrad] using hstart

theorem crossing_step_decreases_left_barrier {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {j : Fin r}
    (hj : A.toCountedGeneralizedAllowableSequence.IsCrossing j) :
    ReversalStep.DecreasingOnPositions (A.seq.π (stepTo j))
      (PositionInterval.leftBarrierPositions k
        (A.toCountedGeneralizedAllowableSequence.moveOrder j)) := by
  exact (A.step j).toReversalStep.decreasing_after_leftBarrierPositions
    (A.reversesBlocks j) hj

theorem crossing_step_decreases_right_barrier {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {j : Fin r}
    (hj : A.toCountedGeneralizedAllowableSequence.IsCrossing j) :
    ReversalStep.DecreasingOnPositions (A.seq.π (stepTo j))
      (PositionInterval.rightBarrierPositions k
        (A.toCountedGeneralizedAllowableSequence.moveOrder j)) := by
  exact (A.step j).toReversalStep.decreasing_after_rightBarrierPositions
    (A.reversesBlocks j) hj

theorem crossing_step_needs_left_barrier_increasing {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {j : Fin r}
    (hj : A.toCountedGeneralizedAllowableSequence.IsCrossing j) :
    ReversalStep.IncreasingOnPositions (A.seq.π (stepFrom j))
      (PositionInterval.leftBarrierPositions k
        (A.toCountedGeneralizedAllowableSequence.moveOrder j)) := by
  exact (A.step j).toReversalStep.increasing_before_leftBarrierPositions hj

theorem crossing_step_needs_right_barrier_increasing {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {j : Fin r}
    (hj : A.toCountedGeneralizedAllowableSequence.IsCrossing j) :
    ReversalStep.IncreasingOnPositions (A.seq.π (stepFrom j))
      (PositionInterval.rightBarrierPositions k
        (A.toCountedGeneralizedAllowableSequence.moveOrder j)) := by
  exact (A.step j).toReversalStep.increasing_before_rightBarrierPositions hj

theorem crossing_step_decreases_central_barrier {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {j : Fin r}
    (hj : A.toCountedGeneralizedAllowableSequence.IsCrossing j) :
    ReversalStep.DecreasingOnPositions (A.seq.π (stepTo j))
      (PositionInterval.centralBarrierPositions k
        (A.toCountedGeneralizedAllowableSequence.moveOrder j)) := by
  exact (A.step j).toReversalStep.decreasing_after_centralBarrierPositions
    (A.reversesBlocks j) hj

theorem crossing_step_needs_central_barrier_increasing {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {j : Fin r}
    (hj : A.toCountedGeneralizedAllowableSequence.IsCrossing j) :
    ReversalStep.IncreasingOnPositions (A.seq.π (stepFrom j))
      (PositionInterval.centralBarrierPositions k
        (A.toCountedGeneralizedAllowableSequence.moveOrder j)) := by
  exact (A.step j).toReversalStep.increasing_before_centralBarrierPositions hj

theorem crossing_step_decreases_smaller_central_barrier {k r d : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {j : Fin r}
    (hj : A.toCountedGeneralizedAllowableSequence.IsCrossing j)
    (hd : d ≤ A.toCountedGeneralizedAllowableSequence.moveOrder j) :
    ReversalStep.DecreasingOnPositions (A.seq.π (stepTo j))
      (PositionInterval.centralBarrierPositions k d) := by
  exact (A.step j).toReversalStep.decreasing_after_centralBarrierPositions_of_le_order
    (A.reversesBlocks j) hj hd

theorem crossing_step_needs_smaller_central_barrier_increasing {k r d : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {j : Fin r}
    (hj : A.toCountedGeneralizedAllowableSequence.IsCrossing j)
    (hd : d ≤ A.toCountedGeneralizedAllowableSequence.moveOrder j) :
    ReversalStep.IncreasingOnPositions (A.seq.π (stepFrom j))
      (PositionInterval.centralBarrierPositions k d) := by
  exact (A.step j).toReversalStep.increasing_before_centralBarrierPositions_of_le_order hj hd

theorem crossing_step_middlePair_decreasing_after {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {j : Fin r}
    (hj : A.toCountedGeneralizedAllowableSequence.IsCrossing j) (hk : 0 < k) :
    ReversalStep.MiddlePairDecreasing (A.seq.π (stepTo j)) hk :=
  (A.step j).toReversalStep.middlePair_decreasing_after_crossing
    (A.reversesBlocks j) hj hk

theorem crossing_step_middlePair_increasing_before {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {j : Fin r}
    (hj : A.toCountedGeneralizedAllowableSequence.IsCrossing j) (hk : 0 < k) :
    ReversalStep.MiddlePairIncreasing (A.seq.π (stepFrom j)) hk :=
  (A.step j).toReversalStep.middlePair_increasing_before_crossing hj hk

theorem crossing_step_offsetPair_decreasing_after {k r s : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {j : Fin r}
    (hj : A.toCountedGeneralizedAllowableSequence.IsCrossing j)
    (hsk : s < k)
    (hs : s < A.toCountedGeneralizedAllowableSequence.moveOrder j) :
    ReversalStep.OffsetPairDecreasing (A.seq.π (stepTo j)) s hsk :=
  (A.step j).toReversalStep.offsetPair_decreasing_after_crossing
    (A.reversesBlocks j) hj hsk hs

theorem crossing_step_offsetPair_increasing_before {k r s : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {j : Fin r}
    (hj : A.toCountedGeneralizedAllowableSequence.IsCrossing j)
    (hsk : s < k)
    (hs : s < A.toCountedGeneralizedAllowableSequence.moveOrder j) :
    ReversalStep.OffsetPairIncreasing (A.seq.π (stepFrom j)) s hsk :=
  (A.step j).toReversalStep.offsetPair_increasing_before_crossing hj hsk hs

theorem consecutive_crossing_middlePair_decreasing_after_first {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {i j : Fin r}
    (hij : A.toCountedGeneralizedAllowableSequence.ConsecutiveCrossing i j)
    (hk : 0 < k) :
    ReversalStep.MiddlePairDecreasing (A.seq.π (stepTo i)) hk :=
  A.crossing_step_middlePair_decreasing_after hij.1 hk

theorem consecutive_crossing_middlePair_increasing_before_second {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {i j : Fin r}
    (hij : A.toCountedGeneralizedAllowableSequence.ConsecutiveCrossing i j)
    (hk : 0 < k) :
    ReversalStep.MiddlePairIncreasing (A.seq.π (stepFrom j)) hk :=
  A.crossing_step_middlePair_increasing_before hij.2.1 hk

theorem consecutive_crossing_offsetPair_decreasing_after_first {k r s : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {i j : Fin r}
    (hij : A.toCountedGeneralizedAllowableSequence.ConsecutiveCrossing i j)
    (hsk : s < k)
    (hs : s < A.toCountedGeneralizedAllowableSequence.moveOrder i) :
    ReversalStep.OffsetPairDecreasing (A.seq.π (stepTo i)) s hsk :=
  A.crossing_step_offsetPair_decreasing_after hij.1 hsk hs

theorem consecutive_crossing_offsetPair_increasing_before_second {k r s : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {i j : Fin r}
    (hij : A.toCountedGeneralizedAllowableSequence.ConsecutiveCrossing i j)
    (hsk : s < k)
    (hs : s < A.toCountedGeneralizedAllowableSequence.moveOrder j) :
    ReversalStep.OffsetPairIncreasing (A.seq.π (stepFrom j)) s hsk :=
  A.crossing_step_offsetPair_increasing_before hij.2.1 hsk hs

theorem consecutive_crossing_decreases_common_central_after_first {k r d : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {i j : Fin r}
    (hij : A.toCountedGeneralizedAllowableSequence.ConsecutiveCrossing i j)
    (hdi : d ≤ A.toCountedGeneralizedAllowableSequence.moveOrder i) :
    ReversalStep.DecreasingOnPositions (A.seq.π (stepTo i))
      (PositionInterval.centralBarrierPositions k d) :=
  A.crossing_step_decreases_smaller_central_barrier hij.1 hdi

theorem consecutive_crossing_increases_common_central_before_second {k r d : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {i j : Fin r}
    (hij : A.toCountedGeneralizedAllowableSequence.ConsecutiveCrossing i j)
    (hdj : d ≤ A.toCountedGeneralizedAllowableSequence.moveOrder j) :
    ReversalStep.IncreasingOnPositions (A.seq.π (stepFrom j))
      (PositionInterval.centralBarrierPositions k d) :=
  A.crossing_step_needs_smaller_central_barrier_increasing hij.2.1 hdj

theorem exists_middlePair_switch_between_consecutive_crossings {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {i j : Fin r}
    (hij : A.toCountedGeneralizedAllowableSequence.ConsecutiveCrossing i j)
    (hk : 0 < k) :
    ∃ m : Fin r,
      i.val < m.val ∧ m.val < j.val ∧
        ReversalStep.MiddlePairDecreasing (A.seq.π (stepFrom m)) hk ∧
        ReversalStep.MiddlePairIncreasing (A.seq.π (stepTo m)) hk ∧
        ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing m := by
  classical
  let a : ℕ := i.val + 1
  let b : ℕ := j.val
  let P : ℕ → Prop := fun t =>
    if h : t ≤ r then
      ReversalStep.MiddlePairIncreasing (A.stateAt t h) hk
    else
      False
  have ha_le_r : a ≤ r := by
    dsimp [a]
    exact Nat.succ_le_of_lt i.isLt
  have hb_le_r : b ≤ r := by
    dsimp [b]
    exact le_of_lt j.isLt
  have hijlt : i.val < j.val := hij.2.2.1
  have hab : a ≤ b := by
    dsimp [a, b]
    omega
  have hdec_a :
      ReversalStep.MiddlePairDecreasing (A.stateAt a ha_le_r) hk := by
    have hdec := A.consecutive_crossing_middlePair_decreasing_after_first hij hk
    have hstate : A.stateAt a ha_le_r = A.seq.π (stepTo i) := by
      apply congrArg A.seq.π
      apply Fin.ext
      simp [stepTo, a]
    rw [hstate]
    exact hdec
  have hnot_a : ¬ P a := by
    intro hPa
    unfold P at hPa
    rw [dif_pos ha_le_r] at hPa
    exact ReversalStep.not_middlePair_increasing_and_decreasing hk ⟨hPa, hdec_a⟩
  have hP_b : P b := by
    have hinc := A.consecutive_crossing_middlePair_increasing_before_second hij hk
    have hinc_b :
        ReversalStep.MiddlePairIncreasing (A.stateAt b hb_le_r) hk := by
      have hstate : A.stateAt b hb_le_r = A.seq.π (stepFrom j) := by
        apply congrArg A.seq.π
        apply Fin.ext
        simp [stepFrom, b]
      rw [hstate]
      exact hinc
    unfold P
    rw [dif_pos hb_le_r]
    exact hinc_b
  rcases exists_false_true_switch_between (P := P) hab hnot_a hP_b with
    ⟨m, hma, hmb, hmfalse, hmtrue⟩
  have hm_lt_r : m < r := lt_trans hmb j.isLt
  have him : i.val < m := by
    dsimp [a] at hma
    omega
  let mFin : Fin r := ⟨m, hm_lt_r⟩
  refine ⟨mFin, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [mFin] using him
  · simpa [mFin] using hmb
  · have hm_le_r : m ≤ r := le_of_lt hm_lt_r
    have hnot_inc :
        ¬ ReversalStep.MiddlePairIncreasing (A.stateAt m hm_le_r) hk := by
      intro hinc
      have hPm : P m := by
        unfold P
        rw [dif_pos hm_le_r]
        exact hinc
      exact hmfalse hPm
    have hdec := ReversalStep.middlePair_decreasing_of_not_increasing hk hnot_inc
    have hstate :
        A.stateAt m hm_le_r = A.seq.π (stepFrom mFin) := by
      apply congrArg A.seq.π
      apply Fin.ext
      simp [stepFrom, mFin]
    rw [hstate] at hdec
    exact hdec
  · have hm1_le_r : m + 1 ≤ r := by omega
    unfold P at hmtrue
    rw [dif_pos hm1_le_r] at hmtrue
    have hstate :
        A.stateAt (m + 1) hm1_le_r = A.seq.π (stepTo mFin) := by
      apply congrArg A.seq.π
      apply Fin.ext
      simp [stepTo, mFin]
    rw [hstate] at hmtrue
    exact hmtrue
  · exact hij.2.2.2 mFin (by simpa [mFin] using him) (by simpa [mFin] using hmb)

theorem exists_offsetPair_switch_between_consecutive_crossings {k r s : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {i j : Fin r}
    (hij : A.toCountedGeneralizedAllowableSequence.ConsecutiveCrossing i j)
    (hsk : s < k)
    (hsi : s < A.toCountedGeneralizedAllowableSequence.moveOrder i)
    (hsj : s < A.toCountedGeneralizedAllowableSequence.moveOrder j) :
    ∃ m : Fin r,
      i.val < m.val ∧ m.val < j.val ∧
        ReversalStep.OffsetPairDecreasing (A.seq.π (stepFrom m)) s hsk ∧
        ReversalStep.OffsetPairIncreasing (A.seq.π (stepTo m)) s hsk ∧
        ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing m := by
  classical
  let a : ℕ := i.val + 1
  let b : ℕ := j.val
  let P : ℕ → Prop := fun t =>
    if h : t ≤ r then
      ReversalStep.OffsetPairIncreasing (A.stateAt t h) s hsk
    else
      False
  have ha_le_r : a ≤ r := by
    dsimp [a]
    exact Nat.succ_le_of_lt i.isLt
  have hb_le_r : b ≤ r := by
    dsimp [b]
    exact le_of_lt j.isLt
  have hijlt : i.val < j.val := hij.2.2.1
  have hab : a ≤ b := by
    dsimp [a, b]
    omega
  have hdec_a :
      ReversalStep.OffsetPairDecreasing (A.stateAt a ha_le_r) s hsk := by
    have hdec := A.consecutive_crossing_offsetPair_decreasing_after_first hij hsk hsi
    have hstate : A.stateAt a ha_le_r = A.seq.π (stepTo i) := by
      apply congrArg A.seq.π
      apply Fin.ext
      simp [stepTo, a]
    rw [hstate]
    exact hdec
  have hnot_a : ¬ P a := by
    intro hPa
    unfold P at hPa
    rw [dif_pos ha_le_r] at hPa
    exact ReversalStep.not_offsetPair_increasing_and_decreasing hsk ⟨hPa, hdec_a⟩
  have hP_b : P b := by
    have hinc := A.consecutive_crossing_offsetPair_increasing_before_second hij hsk hsj
    have hinc_b :
        ReversalStep.OffsetPairIncreasing (A.stateAt b hb_le_r) s hsk := by
      have hstate : A.stateAt b hb_le_r = A.seq.π (stepFrom j) := by
        apply congrArg A.seq.π
        apply Fin.ext
        simp [stepFrom, b]
      rw [hstate]
      exact hinc
    unfold P
    rw [dif_pos hb_le_r]
    exact hinc_b
  rcases exists_false_true_switch_between (P := P) hab hnot_a hP_b with
    ⟨m, hma, hmb, hmfalse, hmtrue⟩
  have hm_lt_r : m < r := lt_trans hmb j.isLt
  have him : i.val < m := by
    dsimp [a] at hma
    omega
  let mFin : Fin r := ⟨m, hm_lt_r⟩
  refine ⟨mFin, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [mFin] using him
  · simpa [mFin] using hmb
  · have hm_le_r : m ≤ r := le_of_lt hm_lt_r
    have hnot_inc :
        ¬ ReversalStep.OffsetPairIncreasing (A.stateAt m hm_le_r) s hsk := by
      intro hinc
      have hPm : P m := by
        unfold P
        rw [dif_pos hm_le_r]
        exact hinc
      exact hmfalse hPm
    have hdec := ReversalStep.offsetPair_decreasing_of_not_increasing hsk hnot_inc
    have hstate :
        A.stateAt m hm_le_r = A.seq.π (stepFrom mFin) := by
      apply congrArg A.seq.π
      apply Fin.ext
      simp [stepFrom, mFin]
    rw [hstate] at hdec
    exact hdec
  · have hm1_le_r : m + 1 ≤ r := by omega
    unfold P at hmtrue
    rw [dif_pos hm1_le_r] at hmtrue
    have hstate :
        A.stateAt (m + 1) hm1_le_r = A.seq.π (stepTo mFin) := by
      apply congrArg A.seq.π
      apply Fin.ext
      simp [stepTo, mFin]
    rw [hstate] at hmtrue
    exact hmtrue
  · exact hij.2.2.2 mFin (by simpa [mFin] using him) (by simpa [mFin] using hmb)

theorem one_le_gap_between_consecutive_crossings {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {i j : Fin r}
    (hij : A.toCountedGeneralizedAllowableSequence.ConsecutiveCrossing i j)
    (hk : 0 < k) :
    1 ≤ j.val - i.val - 1 := by
  rcases A.exists_middlePair_switch_between_consecutive_crossings hij hk with
    ⟨m, him, hmj, _hdec, _hinc, _hnc⟩
  omega

theorem consecutive_crossings_not_adjacent {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {i j : Fin r}
    (hij : A.toCountedGeneralizedAllowableSequence.ConsecutiveCrossing i j)
    (hk : 0 < k) :
    i.val + 1 < j.val := by
  have hgap := A.one_le_gap_between_consecutive_crossings hij hk
  omega

theorem gap_between_consecutive_crossings {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {i j : Fin r}
    (hij : A.toCountedGeneralizedAllowableSequence.ConsecutiveCrossing i j) :
    A.toCountedGeneralizedAllowableSequence.moveOrder i +
        A.toCountedGeneralizedAllowableSequence.moveOrder j - 1 ≤
      j.val - i.val - 1 := by
  classical
  by_contra hnot
  let di := A.toCountedGeneralizedAllowableSequence.moveOrder i
  let dj := A.toCountedGeneralizedAllowableSequence.moveOrder j
  let g := j.val - i.val - 1
  have hijlt : i.val < j.val := hij.2.2.1
  have hgap_lt : g < di + dj - 1 := by
    dsimp [g, di, dj]
    omega
  have hdi_pos : 0 < di := by
    dsimp [di]
    exact hij.1
  have hdj_pos : 0 < dj := by
    dsimp [dj]
    exact hij.2.1
  let n₁ := Nat.min g (di - 1)
  have hn₁_le_g : n₁ ≤ g := Nat.min_le_left _ _
  have hn₁_lt_di : n₁ < di := by
    dsimp [n₁]
    have hmin_le : Nat.min g (di - 1) ≤ di - 1 := Nat.min_le_right _ _
    omega
  have hg_sub_lt_dj : g - n₁ < dj := by
    dsimp [n₁]
    by_cases hg_le : g ≤ di - 1
    · have hn : Nat.min g (di - 1) = g := Nat.min_eq_left hg_le
      rw [hn]
      omega
    · have hdi_le_g : di ≤ g := by omega
      have hn : Nat.min g (di - 1) = di - 1 := Nat.min_eq_right (by omega)
      rw [hn]
      omega
  let D := Nat.min (di - n₁) (dj - (g - n₁))
  have hD_pos : 0 < D := by
    dsimp [D]
    have hleft : 0 < di - n₁ := by omega
    have hright : 0 < dj - (g - n₁) := by omega
    exact Nat.lt_min.mpr ⟨hleft, hright⟩
  have hD_le_left : D ≤ di - n₁ := Nat.min_le_left _ _
  have hD_le_right : D ≤ dj - (g - n₁) := Nat.min_le_right _ _
  let a := i.val + 1
  have ha_eq_to : A.stateAt a (by
      dsimp [a]
      exact Nat.succ_le_of_lt i.isLt) = A.seq.π (stepTo i) := by
    apply congrArg A.seq.π
    apply Fin.ext
    simp [a, stepTo]
  have hb_eq_from : A.stateAt j.val (le_of_lt j.isLt) = A.seq.π (stepFrom j) := by
    apply congrArg A.seq.π
    apply Fin.ext
    simp [stepFrom]
  have ha_add_g : a + g = j.val := by
    dsimp [a, g]
    omega
  have hend_dec : a + n₁ ≤ r := by
    have hjle : j.val ≤ r := le_of_lt j.isLt
    omega
  have hnc_dec :
      ∀ l : Fin r, a ≤ l.val → l.val < a + n₁ →
        ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing l := by
    intro l hla hln
    exact hij.2.2.2 l (by dsimp [a] at hla; omega) (by
      have hng : n₁ ≤ g := hn₁_le_g
      dsimp [a, g] at hln hng
      omega)
  have hdec_start :
      ReversalStep.DecreasingOnPositions (A.stateAt a (by
        dsimp [a]
        exact Nat.succ_le_of_lt i.isLt))
        (PositionInterval.centralBarrierPositions k di) := by
    have hdec := A.crossing_step_decreases_central_barrier hij.1
    rw [ha_eq_to]
    simpa [di] using hdec
  have hdec_mid :=
    A.decreasing_persists_over_noncrossing_steps a n₁ di hend_dec hnc_dec hdec_start
  have hend_inc : a + n₁ + (g - n₁) ≤ r := by
    have hjle : j.val ≤ r := le_of_lt j.isLt
    omega
  have hnc_inc :
      ∀ l : Fin r, a + n₁ ≤ l.val → l.val < a + n₁ + (g - n₁) →
        ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing l := by
    intro l hla hln
    exact hij.2.2.2 l (by dsimp [a] at hla; omega) (by
      dsimp [a, g] at hln
      omega)
  have hinc_end :
      ReversalStep.IncreasingOnPositions
        (A.stateAt (a + n₁ + (g - n₁)) hend_inc)
        (PositionInterval.centralBarrierPositions k dj) := by
    have hsum : a + n₁ + (g - n₁) = j.val := by
      omega
    have hinc := A.crossing_step_needs_central_barrier_increasing hij.2.1
    have hstate :
        A.stateAt (a + n₁ + (g - n₁)) hend_inc = A.seq.π (stepFrom j) := by
      have hstateAt :
          A.stateAt (a + n₁ + (g - n₁)) hend_inc =
            A.stateAt j.val (le_of_lt j.isLt) := by
        apply congrArg A.seq.π
        apply Fin.ext
        exact hsum
      exact hstateAt.trans hb_eq_from
    rw [hstate]
    simpa [dj] using hinc
  have hinc_mid :=
    A.increasing_persists_back_over_noncrossing_steps
      (a + n₁) (g - n₁) dj hend_inc hnc_inc hinc_end
  have hmid_same :
      A.stateAt (a + n₁) (by omega) = A.stateAt (a + n₁) hend_dec := by
    apply A.stateAt_eq_of_proofs
  rw [hmid_same] at hinc_mid
  have hdec_D :
      ReversalStep.DecreasingOnPositions (A.stateAt (a + n₁) hend_dec)
        (PositionInterval.centralBarrierPositions k D) :=
    hdec_mid.mono (PositionInterval.centralBarrierPositions_mono hD_le_left)
  have hinc_D :
      ReversalStep.IncreasingOnPositions (A.stateAt (a + n₁) hend_dec)
        (PositionInterval.centralBarrierPositions k D) :=
    hinc_mid.mono (PositionInterval.centralBarrierPositions_mono hD_le_right)
  have hD_le_k : D ≤ k := by
    have hdi_le : di ≤ k := by
      dsimp [di]
      exact (A.step i).toReversalStep.order_le_middle
    omega
  exact ReversalStep.not_increasing_and_decreasing_centralBarrierPositions
    hD_pos hD_le_k hinc_D hdec_D

theorem gap_between_consecutive_crossings_of_unit_orders {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {i j : Fin r}
    (hij : A.toCountedGeneralizedAllowableSequence.ConsecutiveCrossing i j)
    (hk : 0 < k)
    (hi_order :
      A.toCountedGeneralizedAllowableSequence.moveOrder i = 1)
    (hj_order :
      A.toCountedGeneralizedAllowableSequence.moveOrder j = 1) :
    A.toCountedGeneralizedAllowableSequence.moveOrder i +
        A.toCountedGeneralizedAllowableSequence.moveOrder j - 1 ≤
      j.val - i.val - 1 := by
  have hgap := A.one_le_gap_between_consecutive_crossings hij hk
  omega

theorem gap_between_crossingIdx_of_unit_orders {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r)
    (hk : 0 < k)
    (hunit :
      ∀ i : Fin A.toCountedGeneralizedAllowableSequence.crossingMoves.card,
        A.toCountedGeneralizedAllowableSequence.moveOrder
          (A.toCountedGeneralizedAllowableSequence.crossingIdx i) = 1)
    (i : ℕ) (hi : i + 1 <
      A.toCountedGeneralizedAllowableSequence.crossingMoves.card) :
    A.toCountedGeneralizedAllowableSequence.moveOrder
          (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨i, by omega⟩) +
        A.toCountedGeneralizedAllowableSequence.moveOrder
          (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨i + 1, by omega⟩) - 1 ≤
      (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨i + 1, by omega⟩).val -
        (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨i, by omega⟩).val - 1 := by
  have hij :=
    A.toCountedGeneralizedAllowableSequence.consecutive_crossingIdx_succ i hi
  exact A.gap_between_consecutive_crossings_of_unit_orders hij hk
    (hunit ⟨i, by omega⟩) (hunit ⟨i + 1, by omega⟩)

theorem gap_between_crossingIdx {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r)
    (i : ℕ) (hi : i + 1 <
      A.toCountedGeneralizedAllowableSequence.crossingMoves.card) :
    A.toCountedGeneralizedAllowableSequence.moveOrder
          (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨i, by omega⟩) +
        A.toCountedGeneralizedAllowableSequence.moveOrder
          (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨i + 1, by omega⟩) - 1 ≤
      (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨i + 1, by omega⟩).val -
        (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨i, by omega⟩).val - 1 := by
  have hij :=
    A.toCountedGeneralizedAllowableSequence.consecutive_crossingIdx_succ i hi
  exact A.gap_between_consecutive_crossings hij

def CyclicEndGap {k r : ℕ} (A : ConcreteGeneralizedAllowableSequence k r)
    (hpos : 0 < A.toCountedGeneralizedAllowableSequence.crossingMoves.card) : Prop :=
  A.toCountedGeneralizedAllowableSequence.moveOrder
      (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨0, hpos⟩) +
      A.toCountedGeneralizedAllowableSequence.moveOrder
        (A.toCountedGeneralizedAllowableSequence.crossingIdx
          ⟨A.toCountedGeneralizedAllowableSequence.crossingMoves.card - 1, by omega⟩) - 1 ≤
    (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨0, hpos⟩).val +
      (r - 1 -
        (A.toCountedGeneralizedAllowableSequence.crossingIdx
          ⟨A.toCountedGeneralizedAllowableSequence.crossingMoves.card - 1, by omega⟩).val)

structure CyclicEndGapWitness {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r)
    (hpos : 0 < A.toCountedGeneralizedAllowableSequence.crossingMoves.card) where
  periodMoves : ℕ
  cyclic : ConcreteGeneralizedAllowableSequence k periodMoves
  lastCrossing : Fin periodMoves
  nextFirstCrossing : Fin periodMoves
  consecutive :
    cyclic.toCountedGeneralizedAllowableSequence.ConsecutiveCrossing
      lastCrossing nextFirstCrossing
  last_order :
    cyclic.toCountedGeneralizedAllowableSequence.moveOrder lastCrossing =
      A.toCountedGeneralizedAllowableSequence.moveOrder
        (A.toCountedGeneralizedAllowableSequence.crossingIdx
          ⟨A.toCountedGeneralizedAllowableSequence.crossingMoves.card - 1, by omega⟩)
  next_order :
    cyclic.toCountedGeneralizedAllowableSequence.moveOrder nextFirstCrossing =
      A.toCountedGeneralizedAllowableSequence.moveOrder
        (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨0, hpos⟩)
  cyclic_gap_eq :
    nextFirstCrossing.val - lastCrossing.val - 1 =
      (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨0, hpos⟩).val +
        (r - 1 -
          (A.toCountedGeneralizedAllowableSequence.crossingIdx
            ⟨A.toCountedGeneralizedAllowableSequence.crossingMoves.card - 1, by omega⟩).val)

theorem cyclicEndGap_of_witness {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r)
    {hpos : 0 < A.toCountedGeneralizedAllowableSequence.crossingMoves.card}
    (W : A.CyclicEndGapWitness hpos) :
    A.CyclicEndGap hpos := by
  have hgap := W.cyclic.gap_between_consecutive_crossings W.consecutive
  dsimp [CyclicEndGap]
  rw [← W.last_order, ← W.next_order, ← W.cyclic_gap_eq]
  simpa [add_comm] using hgap

theorem length_lower_bound_from_end_gap {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) (hk : 0 < k)
    (hnoFull :
      ∀ j : Fin r, A.toCountedGeneralizedAllowableSequence.IsCrossing j →
        A.toCountedGeneralizedAllowableSequence.moveOrder j < k)
    (hgap_ends :
      A.toCountedGeneralizedAllowableSequence.moveOrder
          (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨0, by
            exact A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk⟩) +
          A.toCountedGeneralizedAllowableSequence.moveOrder
            (A.toCountedGeneralizedAllowableSequence.crossingIdx
              ⟨A.toCountedGeneralizedAllowableSequence.crossingMoves.card - 1, by
                have htwo :=
                  A.toCountedGeneralizedAllowableSequence.two_le_crossingMoves_card_of_no_full_crossing
                    hk hnoFull
                omega⟩) - 1 ≤
        (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨0, by
          exact A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk⟩).val +
          (r - 1 -
            (A.toCountedGeneralizedAllowableSequence.crossingIdx
              ⟨A.toCountedGeneralizedAllowableSequence.crossingMoves.card - 1, by
                have htwo :=
                  A.toCountedGeneralizedAllowableSequence.two_le_crossingMoves_card_of_no_full_crossing
                    hk hnoFull
                omega⟩).val)) :
    2 * k ≤ r := by
  have htwo :=
    A.toCountedGeneralizedAllowableSequence.two_le_crossingMoves_card_of_no_full_crossing
      hk hnoFull
  exact A.toCountedGeneralizedAllowableSequence.length_lower_bound_from_gaps
    htwo
    (fun i hi => A.gap_between_crossingIdx i hi)
    (by
      simpa using hgap_ends)

theorem length_lower_bound_from_cyclic_end_gap {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) (hk : 0 < k)
    (hnoFull :
      ∀ j : Fin r, A.toCountedGeneralizedAllowableSequence.IsCrossing j →
        A.toCountedGeneralizedAllowableSequence.moveOrder j < k)
    (hend :
      A.CyclicEndGap
        (A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk)) :
    2 * k ≤ r := by
  exact A.length_lower_bound_from_end_gap hk hnoFull (by
    simpa [CyclicEndGap] using hend)

theorem crossingIdx_decreases_common_central_after {k r d : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r)
    (i : ℕ) (hi : i + 1 <
      A.toCountedGeneralizedAllowableSequence.crossingMoves.card)
    (hd :
      d ≤ A.toCountedGeneralizedAllowableSequence.moveOrder
        (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨i, by omega⟩)) :
    ReversalStep.DecreasingOnPositions
      (A.seq.π (stepTo
        (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨i, by omega⟩)))
      (PositionInterval.centralBarrierPositions k d) := by
  have hij :=
    A.toCountedGeneralizedAllowableSequence.consecutive_crossingIdx_succ i hi
  exact A.consecutive_crossing_decreases_common_central_after_first hij hd

theorem crossingIdx_increases_common_central_before_next {k r d : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r)
    (i : ℕ) (hi : i + 1 <
      A.toCountedGeneralizedAllowableSequence.crossingMoves.card)
    (hd :
      d ≤ A.toCountedGeneralizedAllowableSequence.moveOrder
        (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨i + 1, by omega⟩)) :
    ReversalStep.IncreasingOnPositions
      (A.seq.π (stepFrom
        (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨i + 1, by omega⟩)))
      (PositionInterval.centralBarrierPositions k d) := by
  have hij :=
    A.toCountedGeneralizedAllowableSequence.consecutive_crossingIdx_succ i hi
  exact A.consecutive_crossing_increases_common_central_before_second hij hd

end ConcreteGeneralizedAllowableSequence

theorem even_direction_bound_of_concrete_cyclic_sequence (points : Finset Point2)
    {k : ℕ} (hk : 0 < k) (hcard : points.card = 2 * k)
    (A : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy points).card)
    (hnoFull :
      ∀ j : Fin (directionsDeterminedBy points).card,
        A.toCountedGeneralizedAllowableSequence.IsCrossing j →
          A.toCountedGeneralizedAllowableSequence.moveOrder j < k)
    (W : A.CyclicEndGapWitness
      (A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk)) :
    points.card ≤ (directionsDeterminedBy points).card := by
  rw [hcard]
  exact A.length_lower_bound_from_cyclic_end_gap hk hnoFull
    (A.cyclicEndGap_of_witness W)

theorem even_direction_bound_of_concrete_end_gap_sequence (points : Finset Point2)
    {k : ℕ} (hk : 0 < k) (hcard : points.card = 2 * k)
    (A : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy points).card)
    (hnoFull :
      ∀ j : Fin (directionsDeterminedBy points).card,
        A.toCountedGeneralizedAllowableSequence.IsCrossing j →
          A.toCountedGeneralizedAllowableSequence.moveOrder j < k)
    (hend :
      A.CyclicEndGap
        (A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk)) :
    points.card ≤ (directionsDeterminedBy points).card := by
  rw [hcard]
  exact A.length_lower_bound_from_cyclic_end_gap hk hnoFull hend

theorem directions_lower_bound_of_even_concrete_cyclic_sequences (points : Finset Point2)
    (hcard : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : ∀ S : Finset Point2, ∀ k : ℕ, ∀ hk : 0 < k, S.card = 2 * k →
      NoncollinearSet S →
        ∃ A : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy S).card,
          ∃ _hnoFull :
            ∀ j : Fin (directionsDeterminedBy S).card,
              A.toCountedGeneralizedAllowableSequence.IsCrossing j →
                A.toCountedGeneralizedAllowableSequence.moveOrder j < k,
            Nonempty (A.CyclicEndGapWitness
              (A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk))) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  directions_lower_bound_of_even_direction_bound_all points hcard hncoll
    (fun S hEven hS => by
      rcases hEven with ⟨k, hk_even⟩
      have hcardS : S.card = 2 * k := by omega
      have hkpos : 0 < k := by
        rcases hS with ⟨p, hp, _q, _hq, _r, _hr, _hnon⟩
        have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨p, hp⟩
        omega
      rcases hcert S k hkpos hcardS hS with ⟨A, hnoFull, ⟨W⟩⟩
      exact even_direction_bound_of_concrete_cyclic_sequence S hkpos hcardS A hnoFull W)

theorem directions_lower_bound_of_even_concrete_end_gap_sequences (points : Finset Point2)
    (hcard : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : ∀ S : Finset Point2, ∀ k : ℕ, ∀ hk : 0 < k, S.card = 2 * k →
      NoncollinearSet S →
        ∃ A : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy S).card,
          ∃ _hnoFull :
            ∀ j : Fin (directionsDeterminedBy S).card,
              A.toCountedGeneralizedAllowableSequence.IsCrossing j →
                A.toCountedGeneralizedAllowableSequence.moveOrder j < k,
            A.CyclicEndGap
              (A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk)) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  directions_lower_bound_of_even_direction_bound_all points hcard hncoll
    (fun S hEven hS => by
      rcases hEven with ⟨k, hk_even⟩
      have hcardS : S.card = 2 * k := by omega
      have hkpos : 0 < k := by
        rcases hS with ⟨p, hp, _q, _hq, _r, _hr, _hnon⟩
        have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨p, hp⟩
        omega
      rcases hcert S k hkpos hcardS hS with ⟨A, hnoFull, hend⟩
      exact even_direction_bound_of_concrete_end_gap_sequence S hkpos hcardS A hnoFull hend)

/--
The universally valid fixed-axis finite-slope consequence of a projective
direction bound: losing the vertical direction costs at most one slope.
-/
theorem finite_slopes_bound_of_direction_bound (points : Finset Point2)
    (hdir : 2 * (points.card / 2) ≤ (directionsDeterminedBy points).card) :
    2 * (points.card / 2) - 1 ≤ (slopesDeterminedBy points).card := by
  have hle := directions_card_le_slopes_card_succ points
  omega

/-- If the projective direction count reaches `n`, finite slopes reach `n - 1`. -/
theorem slopes_card_sub_one_of_card_le_directions (points : Finset Point2)
    (hdir : points.card ≤ (directionsDeterminedBy points).card) :
    points.card - 1 ≤ (slopesDeterminedBy points).card := by
  have hle := directions_card_le_slopes_card_succ points
  omega

/-- If no vertical pair is present, direction and finite-slope counts agree. -/
theorem slopes_lower_bound_of_directions_lower_bound_noVerticalPairs
    {points : Finset Point2} (hnv : NoVerticalPairs points)
    (hdir : points.card - 1 ≤ (directionsDeterminedBy points).card) :
    points.card - 1 ≤ (slopesDeterminedBy points).card := by
  rwa [directions_card_eq_slopes_card_of_noVerticalPairs hnv] at hdir

/--
The remaining geometric/combinatorial core of Ungar's proof, exposed as an
explicit premise: for every even non-collinear point set, the rotating
projection sequence supplies the finite sweep certificate above.
-/
abbrev EvenUngarSweepCertificatePremise : Type :=
  ∀ S : Finset Point2, Even S.card → NoncollinearSet S →
    UngarSweepCertificate S.card (directionsDeterminedBy S).card

abbrev EvenConcreteCyclicSequencePremise : Prop :=
  ∀ S : Finset Point2, ∀ k : ℕ, ∀ hk : 0 < k, S.card = 2 * k →
    NoncollinearSet S →
      ∃ A : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy S).card,
        ∃ _hnoFull :
          ∀ j : Fin (directionsDeterminedBy S).card,
            A.toCountedGeneralizedAllowableSequence.IsCrossing j →
              A.toCountedGeneralizedAllowableSequence.moveOrder j < k,
          Nonempty (A.CyclicEndGapWitness
            (A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk))

abbrev EvenConcreteEndGapSequencePremise : Prop :=
  ∀ S : Finset Point2, ∀ k : ℕ, ∀ hk : 0 < k, S.card = 2 * k →
    NoncollinearSet S →
      ∃ A : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy S).card,
        ∃ _hnoFull :
          ∀ j : Fin (directionsDeterminedBy S).card,
            A.toCountedGeneralizedAllowableSequence.IsCrossing j →
              A.toCountedGeneralizedAllowableSequence.moveOrder j < k,
          A.CyclicEndGap
            (A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk)

abbrev EvenConcreteCyclicNoDirectFullSequencePremise : Prop :=
  ∀ S : Finset Point2, ∀ k : ℕ, ∀ hk : 0 < k, S.card = 2 * k →
    NoncollinearSet S →
      ∃ A : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy S).card,
        A.NoDirectFullMove ∧
          Nonempty (A.CyclicEndGapWitness
            (A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk))

abbrev EvenGeometricConcreteCyclicSequencePremise : Prop :=
  ∀ S : Finset Point2, ∀ k : ℕ, ∀ hk : 0 < k, S.card = 2 * k →
    NoncollinearSet S →
      ∃ A : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy S).card,
        A.FullMoveForcesCommonDirection S ∧
          Nonempty (A.CyclicEndGapWitness
            (A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk))

abbrev EvenGeometricConcreteEndGapSequencePremise : Prop :=
  ∀ S : Finset Point2, ∀ k : ℕ, ∀ hk : 0 < k, S.card = 2 * k →
    NoncollinearSet S →
      ∃ A : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy S).card,
        A.FullMoveForcesCommonDirection S ∧
          A.CyclicEndGap
            (A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk)

abbrev EvenLevelConcreteEndGapSequencePremise : Prop :=
  ∀ S : Finset Point2, ∀ k : ℕ, ∀ hk : 0 < k, S.card = 2 * k →
    NoncollinearSet S →
      ∃ L : PointLabeling S k,
        ∃ A : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy S).card,
          ∃ stepDir : Fin (directionsDeterminedBy S).card → Direction,
            A.DirectFullMoveForcesCommonLevel L stepDir ∧
              A.CyclicEndGap
                (A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk)

abbrev EvenBlockLevelConcreteEndGapSequencePremise : Prop :=
  ∀ S : Finset Point2, ∀ k : ℕ, ∀ hk : 0 < k, S.card = 2 * k →
    NoncollinearSet S →
      ∃ L : PointLabeling S k,
        ∃ A : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy S).card,
          ∃ stepDir : Fin (directionsDeterminedBy S).card → Direction,
            A.BlocksHaveCommonLevel L stepDir ∧
              A.CyclicEndGap
                (A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk)

abbrev EvenInjectiveBlockLevelConcreteEndGapSequencePremise : Prop :=
  ∀ S : Finset Point2, ∀ k : ℕ, ∀ hk : 0 < k, S.card = 2 * k →
    NoncollinearSet S →
      ∃ L : PointLabeling S k,
        ∃ A : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy S).card,
          ∃ stepDir : Fin (directionsDeterminedBy S).card → Direction,
            A.BlocksHaveCommonLevel L stepDir ∧
              Function.Injective stepDir ∧
                A.CyclicEndGap
                  (A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk)

structure UngarLevelSweepCertificate (S : Finset Point2) (k : ℕ) (hk : 0 < k) where
  labeling : PointLabeling S k
  sequence : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy S).card
  stepDir : Fin (directionsDeterminedBy S).card → Direction
  blocks_level : sequence.BlocksHaveCommonLevel labeling stepDir
  stepDir_injective : Function.Injective stepDir
  cyclic_end_gap :
    sequence.CyclicEndGap
      (sequence.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk)

namespace UngarLevelSweepCertificate

theorem stepDirectionsEnumerate {S : Finset Point2} {k : ℕ} {hk : 0 < k}
    (C : UngarLevelSweepCertificate S k hk) :
    ConcreteGeneralizedAllowableSequence.StepDirectionsEnumerate S C.stepDir :=
  C.sequence.stepDirectionsEnumerate_of_blocksHaveCommonLevel_of_injective
    C.labeling C.stepDir C.blocks_level C.stepDir_injective

theorem noDirectFullMove {S : Finset Point2} {k : ℕ} {hk : 0 < k}
    (C : UngarLevelSweepCertificate S k hk) (hncoll : NoncollinearSet S) :
    C.sequence.NoDirectFullMove :=
  C.sequence.noDirectFullMove_of_directFullMoveForcesCommonLevel
    C.labeling C.stepDir hncoll
    (C.sequence.directFullMoveForcesCommonLevel_of_blocksHaveCommonLevel
      hk C.labeling C.stepDir C.blocks_level)

theorem noFullCrossing {S : Finset Point2} {k : ℕ} {hk : 0 < k}
    (C : UngarLevelSweepCertificate S k hk) (hncoll : NoncollinearSet S) :
    ∀ j : Fin (directionsDeterminedBy S).card,
      C.sequence.toCountedGeneralizedAllowableSequence.IsCrossing j →
        C.sequence.toCountedGeneralizedAllowableSequence.moveOrder j < k :=
  C.sequence.moveOrder_lt_middle_of_noDirectFullMove hk (C.noDirectFullMove hncoll)

theorem two_le_crossingMoves_card {S : Finset Point2} {k : ℕ} {hk : 0 < k}
    (C : UngarLevelSweepCertificate S k hk) (hncoll : NoncollinearSet S) :
    2 ≤ C.sequence.toCountedGeneralizedAllowableSequence.crossingMoves.card :=
  C.sequence.toCountedGeneralizedAllowableSequence
    |>.two_le_crossingMoves_card_of_no_full_crossing hk (C.noFullCrossing hncoll)

theorem even_direction_bound {S : Finset Point2} {k : ℕ} {hk : 0 < k}
    (C : UngarLevelSweepCertificate S k hk)
    (hcard : S.card = 2 * k) (hncoll : NoncollinearSet S) :
    S.card ≤ (directionsDeterminedBy S).card :=
  even_direction_bound_of_concrete_end_gap_sequence S hk hcard C.sequence
    (C.noFullCrossing hncoll) C.cyclic_end_gap

end UngarLevelSweepCertificate

abbrev EvenUngarLevelSweepCertificatePremise : Prop :=
  ∀ S : Finset Point2, ∀ k : ℕ, ∀ hk : 0 < k, S.card = 2 * k →
    NoncollinearSet S → Nonempty (UngarLevelSweepCertificate S k hk)

theorem evenConcreteCyclicSequencePremise_of_noDirectFull
    (hcert : EvenConcreteCyclicNoDirectFullSequencePremise) :
    EvenConcreteCyclicSequencePremise := by
  intro S k hk hcard hncoll
  rcases hcert S k hk hcard hncoll with ⟨A, hnoDirect, hcyclic⟩
  exact ⟨A, A.moveOrder_lt_middle_of_noDirectFullMove hk hnoDirect, hcyclic⟩

theorem evenConcreteEndGapSequencePremise_of_geometric
    (hcert : EvenGeometricConcreteEndGapSequencePremise) :
    EvenConcreteEndGapSequencePremise := by
  intro S k hk hcard hncoll
  rcases hcert S k hk hcard hncoll with ⟨A, hfull, hend⟩
  have hnoDirect : A.NoDirectFullMove :=
    A.noDirectFullMove_of_fullMoveForcesCommonDirection hncoll hfull
  exact ⟨A, A.moveOrder_lt_middle_of_noDirectFullMove hk hnoDirect, hend⟩

theorem evenConcreteEndGapSequencePremise_of_level
    (hcert : EvenLevelConcreteEndGapSequencePremise) :
    EvenConcreteEndGapSequencePremise := by
  intro S k hk hcard hncoll
  rcases hcert S k hk hcard hncoll with ⟨L, A, stepDir, hlevel, hend⟩
  have hnoDirect : A.NoDirectFullMove :=
    A.noDirectFullMove_of_directFullMoveForcesCommonLevel L stepDir hncoll hlevel
  exact ⟨A, A.moveOrder_lt_middle_of_noDirectFullMove hk hnoDirect, hend⟩

theorem evenGeometricConcreteEndGapSequencePremise_of_level
    (hcert : EvenLevelConcreteEndGapSequencePremise) :
    EvenGeometricConcreteEndGapSequencePremise := by
  intro S k hk hcard hncoll
  rcases hcert S k hk hcard hncoll with ⟨L, A, stepDir, hlevel, hend⟩
  exact ⟨A, A.fullMoveForcesCommonDirection_of_directFullMoveForcesCommonLevel
    L stepDir hlevel, hend⟩

theorem evenLevelConcreteEndGapSequencePremise_of_blockLevel
    (hcert : EvenBlockLevelConcreteEndGapSequencePremise) :
    EvenLevelConcreteEndGapSequencePremise := by
  intro S k hk hcard hncoll
  rcases hcert S k hk hcard hncoll with ⟨L, A, stepDir, hblocks, hend⟩
  exact ⟨L, A, stepDir,
    A.directFullMoveForcesCommonLevel_of_blocksHaveCommonLevel hk L stepDir hblocks, hend⟩

theorem evenBlockLevelConcreteEndGapSequencePremise_of_injective
    (hcert : EvenInjectiveBlockLevelConcreteEndGapSequencePremise) :
    EvenBlockLevelConcreteEndGapSequencePremise := by
  intro S k hk hcard hncoll
  rcases hcert S k hk hcard hncoll with ⟨L, A, stepDir, hblocks, _hinj, hend⟩
  exact ⟨L, A, stepDir, hblocks, hend⟩

theorem evenInjectiveBlockLevelConcreteEndGapSequencePremise_of_certificate
    (hcert : EvenUngarLevelSweepCertificatePremise) :
    EvenInjectiveBlockLevelConcreteEndGapSequencePremise := by
  intro S k hk hcard hncoll
  rcases hcert S k hk hcard hncoll with ⟨C⟩
  exact ⟨C.labeling, C.sequence, C.stepDir, C.blocks_level,
    C.stepDir_injective, C.cyclic_end_gap⟩

theorem evenConcreteCyclicNoDirectFullSequencePremise_of_geometric
    (hcert : EvenGeometricConcreteCyclicSequencePremise) :
    EvenConcreteCyclicNoDirectFullSequencePremise := by
  intro S k hk hcard hncoll
  rcases hcert S k hk hcard hncoll with ⟨A, hfull, hcyclic⟩
  exact ⟨A, A.noDirectFullMove_of_fullMoveForcesCommonDirection hncoll hfull, hcyclic⟩

theorem evenConcreteCyclicSequencePremise_of_geometric
    (hcert : EvenGeometricConcreteCyclicSequencePremise) :
    EvenConcreteCyclicSequencePremise :=
  evenConcreteCyclicSequencePremise_of_noDirectFull
    (evenConcreteCyclicNoDirectFullSequencePremise_of_geometric hcert)

theorem ungar_directions_lower_bound_from_sweep (points : Finset Point2)
    (hn : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : EvenUngarSweepCertificatePremise) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  directions_lower_bound_of_even_ungar_sweep_certificates points hn hncoll hcert

theorem ungar_directions_lower_bound_from_concrete_cyclic (points : Finset Point2)
    (hn : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : EvenConcreteCyclicSequencePremise) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  directions_lower_bound_of_even_concrete_cyclic_sequences points hn hncoll hcert

theorem ungar_directions_lower_bound_from_concrete_end_gap (points : Finset Point2)
    (hn : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : EvenConcreteEndGapSequencePremise) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  directions_lower_bound_of_even_concrete_end_gap_sequences points hn hncoll hcert

theorem ungar_directions_lower_bound_from_no_direct_full_concrete_cyclic
    (points : Finset Point2)
    (hn : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : EvenConcreteCyclicNoDirectFullSequencePremise) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  ungar_directions_lower_bound_from_concrete_cyclic points hn hncoll
    (evenConcreteCyclicSequencePremise_of_noDirectFull hcert)

theorem ungar_directions_lower_bound_from_geometric_concrete_cyclic
    (points : Finset Point2)
    (hn : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : EvenGeometricConcreteCyclicSequencePremise) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  ungar_directions_lower_bound_from_concrete_cyclic points hn hncoll
    (evenConcreteCyclicSequencePremise_of_geometric hcert)

theorem ungar_directions_lower_bound_from_geometric_concrete_end_gap
    (points : Finset Point2)
    (hn : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : EvenGeometricConcreteEndGapSequencePremise) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  ungar_directions_lower_bound_from_concrete_end_gap points hn hncoll
    (evenConcreteEndGapSequencePremise_of_geometric hcert)

theorem ungar_directions_lower_bound_from_level_concrete_end_gap
    (points : Finset Point2)
    (hn : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : EvenLevelConcreteEndGapSequencePremise) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  ungar_directions_lower_bound_from_concrete_end_gap points hn hncoll
    (evenConcreteEndGapSequencePremise_of_level hcert)

theorem ungar_directions_lower_bound_from_block_level_concrete_end_gap
    (points : Finset Point2)
    (hn : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : EvenBlockLevelConcreteEndGapSequencePremise) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  ungar_directions_lower_bound_from_level_concrete_end_gap points hn hncoll
    (evenLevelConcreteEndGapSequencePremise_of_blockLevel hcert)

theorem ungar_directions_lower_bound_from_injective_block_level_concrete_end_gap
    (points : Finset Point2)
    (hn : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : EvenInjectiveBlockLevelConcreteEndGapSequencePremise) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  ungar_directions_lower_bound_from_block_level_concrete_end_gap points hn hncoll
    (evenBlockLevelConcreteEndGapSequencePremise_of_injective hcert)

theorem ungar_directions_lower_bound_from_level_sweep_certificate
    (points : Finset Point2)
    (hn : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : EvenUngarLevelSweepCertificatePremise) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  ungar_directions_lower_bound_from_injective_block_level_concrete_end_gap
    points hn hncoll
    (evenInjectiveBlockLevelConcreteEndGapSequencePremise_of_certificate hcert)

/--
Counting interface for Ungar's slope theorem: an injective family of witnessed
slopes gives the corresponding lower bound on the number of slopes.
-/
theorem card_le_slopes_of_injective_witness {ι : Type*} [Fintype ι]
    (points : Finset Point2) (witness : ι → ℝ)
    (hwitness : ∀ i, witness i ∈ slopesDeterminedBy points)
    (hinj : Function.Injective witness) :
    Fintype.card ι ≤ (slopesDeterminedBy points).card := by
  classical
  exact Finset.card_le_card_of_injOn witness (by intro i _hi; exact hwitness i)
    (by intro a _ha b _hb h; exact hinj h)

/--
Counting interface for the coordinate-free slope/direction theorem: an
injective family of witnessed projective directions gives a lower bound on
the number of directions.
-/
theorem card_le_directions_of_injective_witness {ι : Type*} [Fintype ι]
    (points : Finset Point2) (witness : ι → Direction)
    (hwitness : ∀ i, witness i ∈ directionsDeterminedBy points)
    (hinj : Function.Injective witness) :
    Fintype.card ι ≤ (directionsDeterminedBy points).card := by
  classical
  exact Finset.card_le_card_of_injOn witness (by intro i _hi; exact hwitness i)
    (by intro a _ha b _hb h; exact hinj h)

/--
Ungar's rotating-calipers theorem, stated for projective directions. This is
the coordinate-correct target: vertical lines count as one direction.
-/
theorem ungar_directions_lower_bound (points : Finset Point2)
    (hn : 3 ≤ points.card)
    (hncoll : NoncollinearSet points)
    (hcert : EvenUngarLevelSweepCertificatePremise) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  ungar_directions_lower_bound_from_level_sweep_certificate points hn hncoll hcert

theorem chapter11 {ι : Type*} [Fintype ι] (points : Finset Point2) (witness : ι → ℝ)
    (hwitness : ∀ i, witness i ∈ slopesDeterminedBy points)
    (hinj : Function.Injective witness) :
    Fintype.card ι ≤ (slopesDeterminedBy points).card :=
  card_le_slopes_of_injective_witness points witness hwitness hinj

/-! ## Sweep certificate construction

The remaining geometric core: construct `UngarLevelSweepCertificate` from the
rotating projection sweep of every even non-collinear point set.
-/

/-! ### BlockMove from monotone level function -/

noncomputable def nontrivialLevelValues {N : ℕ} (g : Fin N → ℝ) : Finset ℝ :=
  (Finset.univ.image g).filter fun v =>
    (Finset.univ.filter fun i : Fin N => g i = v).card ≥ 2

noncomputable def nontrivialLevelRep {N : ℕ} (g : Fin N → ℝ) (v : ℝ)
    (hv : v ∈ nontrivialLevelValues g) : Fin N :=
  (Finset.univ.filter fun i : Fin N => g i = v).min' (by
    have hmem := (Finset.mem_filter.mp hv).2
    exact Finset.card_pos.mp (by omega))

theorem nontrivialLevelRep_val {N : ℕ} {g : Fin N → ℝ} {v : ℝ}
    (hv : v ∈ nontrivialLevelValues g) :
    g (nontrivialLevelRep g v hv) = v := by
  have hmem : nontrivialLevelRep g v hv ∈
      Finset.univ.filter (fun i : Fin N => g i = v) :=
    Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hmem).2

private theorem levelBlockLo_le_of_monotone_eq' {N : ℕ}
    {g : Fin N → ℝ} (_hg : Monotone g) {rep p : Fin N}
    (hval : g p = g rep) :
    levelBlockLo g rep ≤ p := by
  by_contra h
  push_neg at h
  have hp_le_rep : p ≤ rep :=
    le_of_lt (lt_of_lt_of_le h levelBlockLo_le)
  have hp_in : p ∈ Finset.univ.filter fun j : Fin N => g j = g rep ∧ j ≤ rep :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hval, hp_le_rep⟩
  exact not_le.mpr h (Finset.min'_le _ _ hp_in)

private theorem le_levelBlockHi_of_monotone_eq' {N : ℕ}
    {g : Fin N → ℝ} (_hg : Monotone g) {rep p : Fin N}
    (hval : g p = g rep) :
    p ≤ levelBlockHi g rep := by
  by_contra h
  push_neg at h
  have hrep_le_p : rep ≤ p :=
    le_of_lt (lt_of_le_of_lt levelBlockHi_ge h)
  have hp_in : p ∈ Finset.univ.filter fun j : Fin N => g j = g rep ∧ rep ≤ j :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hval, hrep_le_p⟩
  exact not_le.mpr h (Finset.le_max' _ _ hp_in)

theorem nontrivialLevelRep_block {N : ℕ} {g : Fin N → ℝ} (hg : Monotone g) {v : ℝ}
    (hv : v ∈ nontrivialLevelValues g) :
    (levelBlockLo g (nontrivialLevelRep g v hv)).val <
      (levelBlockHi g (nontrivialLevelRep g v hv)).val := by
  by_contra h
  push_neg at h
  have hle := Fin.le_def.mp (levelBlockLo_le (f := g) (i := nontrivialLevelRep g v hv))
  have hge := Fin.le_def.mp (levelBlockHi_ge (f := g) (i := nontrivialLevelRep g v hv))
  have hrep := nontrivialLevelRep_val hv
  have hsingleton : ∀ j : Fin N, g j = v → j = nontrivialLevelRep g v hv := by
    intro j hj
    have hj_ge := levelBlockLo_le_of_monotone_eq' hg (hj.trans hrep.symm)
    have hj_le := le_levelBlockHi_of_monotone_eq' hg (hj.trans hrep.symm)
    exact Fin.ext (by
      have := Fin.le_def.mp hj_ge
      have := Fin.le_def.mp hj_le
      omega)
  have : (Finset.univ.filter fun i : Fin N => g i = v).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    exact (hsingleton a (Finset.mem_filter.mp ha).2).trans
      (hsingleton b (Finset.mem_filter.mp hb).2).symm
  have := (Finset.mem_filter.mp hv).2
  omega

private theorem mem_levelBlockMoveInterval_of_same_value {N : ℕ}
    {g : Fin N → ℝ} (hg : Monotone g) {rep p : Fin N}
    (hrep_lo_lt : (levelBlockLo g rep).val < (levelBlockHi g rep).val)
    (hval : g p = g rep) :
    (levelBlockMoveInterval g rep hrep_lo_lt).Mem p :=
  ⟨Fin.le_def.mp (levelBlockLo_le_of_monotone_eq' hg hval),
   Fin.le_def.mp (le_levelBlockHi_of_monotone_eq' hg hval)⟩

private theorem levelBlockMirror_eq_mirror_of_mem_levelBlockMoveInterval {N : ℕ}
    {g : Fin N → ℝ} (hg : Monotone g) {rep p : Fin N}
    (hrep_lo_lt : (levelBlockLo g rep).val < (levelBlockHi g rep).val)
    (hp : (levelBlockMoveInterval g rep hrep_lo_lt).Mem p) :
    levelBlockMirror g p = (levelBlockMoveInterval g rep hrep_lo_lt).mirror p hp := by
  apply Fin.ext
  simp only [levelBlockMirror, PositionInterval.mirror, levelBlockMoveInterval]
  rcases hp with ⟨hlo, hhi⟩
  have hp_val := monotone_levelBlock_eq hg
    (Fin.le_def.mpr (show (levelBlockLo g rep).val ≤ p.val from hlo))
    (Fin.le_def.mpr (show p.val ≤ (levelBlockHi g rep).val from hhi))
  have hlo_eq := levelBlockLo_of_mem_block hp_val hlo
  have hhi_eq := levelBlockHi_of_mem_block hp_val hhi
  rw [← congrArg Fin.val hlo_eq, ← congrArg Fin.val hhi_eq]

private theorem levelBlockMirror_eq_self_of_singleton {N : ℕ}
    {g : Fin N → ℝ} (p : Fin N)
    (hsingleton : levelBlockLo g p = levelBlockHi g p) :
    levelBlockMirror g p = p := by
  apply Fin.ext
  simp [levelBlockMirror]
  have := congrArg Fin.val hsingleton
  have := Fin.le_def.mp (levelBlockLo_le (f := g) (i := p))
  have := Fin.le_def.mp (levelBlockHi_ge (f := g) (i := p))
  omega

private theorem mem_nontrivialLevelValues_of_nontrivial_block {N : ℕ}
    {g : Fin N → ℝ} {p : Fin N}
    (hlt : (levelBlockLo g p).val < (levelBlockHi g p).val) :
    g p ∈ nontrivialLevelValues g := by
  simp only [nontrivialLevelValues, Finset.mem_filter, Finset.mem_image]
  refine ⟨⟨p, Finset.mem_univ _, rfl⟩, ?_⟩
  have hlo_in : levelBlockLo g p ∈
      Finset.univ.filter fun i : Fin N => g i = g p :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, levelBlockLo_val⟩
  have hhi_in : levelBlockHi g p ∈
      Finset.univ.filter fun i : Fin N => g i = g p :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, levelBlockHi_val⟩
  exact Finset.one_lt_card.mpr ⟨levelBlockLo g p, hlo_in,
    levelBlockHi g p, hhi_in, fun h => absurd (congrArg Fin.val h) (by omega)⟩

noncomputable def levelBlockMoveBlock {N : ℕ} (g : Fin N → ℝ) (hg : Monotone g)
    (i : Fin (nontrivialLevelValues g).card) : PositionInterval N :=
  levelBlockMoveInterval g
    (nontrivialLevelRep g ((nontrivialLevelValues g).equivFin.symm i).val
      ((nontrivialLevelValues g).equivFin.symm i).property)
    (nontrivialLevelRep_block hg ((nontrivialLevelValues g).equivFin.symm i).property)

noncomputable def levelBlockMoveOfMonotone {N : ℕ} (g : Fin N → ℝ) (hg : Monotone g)
    (hnt : (nontrivialLevelValues g).Nonempty) : BlockMove N where
  blockCount := (nontrivialLevelValues g).card
  blockCount_pos := Finset.card_pos.mpr hnt
  block := levelBlockMoveBlock g hg
  pairwise_disjoint := by
    intro i _hi j _hj hij
    have hne : ((nontrivialLevelValues g).equivFin.symm i).val ≠
        ((nontrivialLevelValues g).equivFin.symm j).val := by
      intro h
      exact hij ((nontrivialLevelValues g).equivFin.symm.injective (Subtype.ext h))
    have hgne : g (nontrivialLevelRep g _ ((nontrivialLevelValues g).equivFin.symm i).property) ≠
        g (nontrivialLevelRep g _ ((nontrivialLevelValues g).equivFin.symm j).property) := by
      simp only [nontrivialLevelRep_val]; exact hne
    exact Set.disjoint_of_subset_left (le_refl _)
      (Set.disjoint_of_subset_right (le_refl _)
        (levelBlockMoveInterval_disjoint hg _ _ hgne))
  nontrivial := by
    intro i
    show 2 ≤ (levelBlockMoveBlock g hg i).length
    simp only [levelBlockMoveBlock, PositionInterval.length, levelBlockMoveInterval]
    have := nontrivialLevelRep_block hg ((nontrivialLevelValues g).equivFin.symm i).property
    omega
  map := levelBlockMirrorPerm g hg

theorem levelBlockMoveOfMonotone_reversesBlocks {N : ℕ} {g : Fin N → ℝ} {hg : Monotone g}
    {hnt : (nontrivialLevelValues g).Nonempty} :
    (levelBlockMoveOfMonotone g hg hnt).ReversesBlocks := by
  constructor
  · intro i p hp
    show (levelBlockMirrorPerm g hg) p = _
    simp only [levelBlockMirrorPerm]
    show levelBlockMirror g p = ((levelBlockMoveBlock g hg i).mirror p hp)
    exact levelBlockMirror_eq_mirror_of_mem_levelBlockMoveInterval hg _ hp
  · intro p hnot
    show (levelBlockMirrorPerm g hg) p = p
    simp only [levelBlockMirrorPerm]
    apply levelBlockMirror_eq_self_of_singleton
    by_contra hne
    have hlt : (levelBlockLo g p).val < (levelBlockHi g p).val := by
      have := Fin.le_def.mp (levelBlockLo_le (f := g) (i := p))
      have := Fin.le_def.mp (levelBlockHi_ge (f := g) (i := p))
      omega
    have hv_mem := mem_nontrivialLevelValues_of_nontrivial_block hlt
    let idx := (nontrivialLevelValues g).equivFin ⟨g p, hv_mem⟩
    have hval_eq : ((nontrivialLevelValues g).equivFin.symm idx).val = g p := by
      simp [idx]
    have hv' := ((nontrivialLevelValues g).equivFin.symm idx).property
    have hrep_val : g (nontrivialLevelRep g
        ((nontrivialLevelValues g).equivFin.symm idx).val hv') = g p := by
      rw [nontrivialLevelRep_val hv', hval_eq]
    exact absurd (mem_levelBlockMoveInterval_of_same_value hg
      (nontrivialLevelRep_block hg hv') hrep_val.symm) (hnot idx)

/-! ### ReversalStep from sweep event -/

private theorem same_g_value_of_same_block {N : ℕ} {g : Fin N → ℝ}
    (hg : Monotone g) {hnt : (nontrivialLevelValues g).Nonempty}
    {i : Fin (levelBlockMoveOfMonotone g hg hnt).blockCount}
    {p q : Fin N}
    (hp : ((levelBlockMoveOfMonotone g hg hnt).block i).Mem p)
    (hq : ((levelBlockMoveOfMonotone g hg hnt).block i).Mem q) :
    g p = g q := by
  have hrep_block := nontrivialLevelRep_block hg
    ((nontrivialLevelValues g).equivFin.symm i).property
  have hp_val := monotone_levelBlock_eq hg (Fin.le_def.mpr hp.1) (Fin.le_def.mpr hp.2)
  have hq_val := monotone_levelBlock_eq hg (Fin.le_def.mpr hq.1) (Fin.le_def.mpr hq.2)
  exact hp_val.trans hq_val.symm

noncomputable def sweepReversalStep {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k)
    {θ₁ θ_e θ₂ θ₀ : ℝ}
    (hinj₀ : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₀ (L.point a)))
    (hinj₁ : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₁ (L.point a)))
    (hinj₂ : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₂ (L.point a)))
    (hid : sweepSort L θ₀ = Equiv.refl _)
    (h1e : θ₁ < θ_e) (he2 : θ_e < θ₂) (h_span : θ₂ - θ₁ < Real.pi)
    (honly_event : ∀ a b : Fin (2 * k), L.point a ≠ L.point b →
      ∀ θ ∈ Set.Icc θ₁ θ₂, θ ≠ θ_e →
        orientedLevel θ (L.point a) ≠ orientedLevel θ (L.point b))
    (hno_tie_0_to_1 : ∀ a b : Fin (2 * k), L.point a ≠ L.point b →
      orientedLevel θ_e (L.point a) = orientedLevel θ_e (L.point b) →
        ∀ θ ∈ Set.Icc θ₀ θ₁, orientedLevel θ (L.point a) ≠ orientedLevel θ (L.point b))
    (h01 : θ₀ ≤ θ₁)
    (hg_mono : Monotone (fun i => orientedLevel θ_e
      (L.point (sweepSort L θ₁ i))))
    (hnt : (nontrivialLevelValues (fun i => orientedLevel θ_e
      (L.point (sweepSort L θ₁ i)))).Nonempty) :
    ReversalStep k (sweepSort L θ₁) (sweepSort L θ₂) where
  move := levelBlockMoveOfMonotone
    (fun i => orientedLevel θ_e (L.point (sweepSort L θ₁ i))) hg_mono hnt
  step_apply := by
    intro p
    have hcomp := sweepSort_event_compose L hinj₁ hinj₂ h1e he2 h_span honly_event hg_mono
    show (sweepSort L θ₂) p = (sweepSort L θ₁)
      ((levelBlockMoveOfMonotone _ hg_mono hnt).map p)
    simp only [levelBlockMoveOfMonotone]
    rw [hcomp]; rfl
  increasing_before := by
    set g := fun i => orientedLevel θ_e (L.point (sweepSort L θ₁ i))
    intro i
    intro p hp q hq hpq
    simp only [PositionInterval.toSet, Set.mem_setOf_eq] at hp hq
    have htie : orientedLevel θ_e (L.point (sweepSort L θ₁ p)) =
        orientedLevel θ_e (L.point (sweepSort L θ₁ q)) :=
      same_g_value_of_same_block hg_mono hp hq
    have hstrict := sweepSort_strictMono_of_injective L θ₁ hinj₁ hpq
    have hne : L.point (sweepSort L θ₁ p) ≠ L.point (sweepSort L θ₁ q) :=
      fun h => ne_of_lt hstrict (congr_arg (orientedLevel θ₁) h)
    have hord₀ := orientedLevel_order_preserved_backward h01 hstrict
      (fun θ hθ => hno_tie_0_to_1 _ _ hne htie θ hθ)
    exact label_index_lt_of_orientedLevel_lt L θ₀ hid hord₀

/-! ### Sorted direction angle infrastructure -/

theorem sortedDirectionAngles_length (points : Finset Point2) :
    (sortedDirectionAngles points).length =
      (directionsDeterminedBy points).card := by
  simp [sortedDirectionAngles, Finset.card_image_of_injective _ Direction.angle_injective]

theorem sortedDirectionAngles_sortedLT (points : Finset Point2) :
    (sortedDirectionAngles points).SortedLT :=
  Finset.sortedLT_sort _

theorem sortedDirectionAngles_nodup (points : Finset Point2) :
    (sortedDirectionAngles points).Nodup :=
  Finset.sort_nodup _ _

noncomputable def sortedAngleAt (points : Finset Point2)
    (j : Fin (directionsDeterminedBy points).card) : ℝ :=
  (sortedDirectionAngles points).get
    ⟨j.val, by rw [sortedDirectionAngles_length]; exact j.isLt⟩

theorem sortedAngleAt_strictMono (points : Finset Point2) :
    StrictMono (sortedAngleAt points) := by
  intro i j hij
  have hsorted := sortedDirectionAngles_sortedLT points
  show (sortedDirectionAngles points).get ⟨i.val, _⟩ <
    (sortedDirectionAngles points).get ⟨j.val, _⟩
  exact hsorted.strictMono_get hij

theorem sortedAngleAt_mem (points : Finset Point2)
    (j : Fin (directionsDeterminedBy points).card) :
    sortedAngleAt points j ∈
      (directionsDeterminedBy points).image Direction.angle := by
  have hmem : sortedAngleAt points j ∈ sortedDirectionAngles points :=
    List.get_mem _ _
  rwa [sortedDirectionAngles, Finset.mem_sort] at hmem

theorem sortedAngleAt_nonneg (points : Finset Point2)
    (j : Fin (directionsDeterminedBy points).card) :
    0 ≤ sortedAngleAt points j := by
  rcases Finset.mem_image.mp (sortedAngleAt_mem points j) with ⟨d, _, hangle⟩
  rw [← hangle]; exact d.angle_nonneg

theorem sortedAngleAt_lt_pi (points : Finset Point2)
    (j : Fin (directionsDeterminedBy points).card) :
    sortedAngleAt points j < Real.pi := by
  rcases Finset.mem_image.mp (sortedAngleAt_mem points j) with ⟨d, _, hangle⟩
  rw [← hangle]; exact d.angle_lt_pi

theorem orientedLevel_eq_at_direction_angle {p q : Point2} (hpq : p ≠ q) :
    orientedLevel (direction p q).angle p = orientedLevel (direction p q).angle q := by
  cases hd : direction p q with
  | vertical =>
    simp only [Direction.angle]
    simp [orientedLevel, Real.sin_pi_div_two, Real.cos_pi_div_two]
    have : p.1 = q.1 := by unfold direction at hd; split_ifs at hd with hx; exact hx
    linarith
  | finite m =>
    have hcos_ne : Real.cos (Direction.finite m).angle ≠ 0 := by
      simp only [Direction.angle]
      split_ifs with h
      · exact ne_of_gt (Real.cos_arctan_pos m)
      · rw [Real.cos_add, Real.cos_pi, Real.sin_pi]
        simp; exact ne_of_lt (Real.cos_arctan_pos m) |>.symm
    have htan_eq : Direction.finite (Real.tan (Direction.finite m).angle) =
        Direction.finite m := by
      congr 1; simp only [Direction.angle]
      split_ifs with h
      · exact Real.tan_arctan m
      · rw [Real.tan_add_pi]; exact Real.tan_arctan m
    rw [orientedLevel_eq_cos_mul_directionLevel hcos_ne,
        orientedLevel_eq_cos_mul_directionLevel hcos_ne, htan_eq]
    exact congrArg _ (directionLevel_eq_of_direction_eq hd)

private theorem orientedLevel_sub_zero_at_direction_angle' {p q : Point2} (hpq : p ≠ q) :
    -(p.1 - q.1) * Real.sin (direction p q).angle +
      (p.2 - q.2) * Real.cos (direction p q).angle = 0 := by
  have h := orientedLevel_sub_eq (direction p q).angle p q
  linarith [orientedLevel_eq_at_direction_angle hpq]

theorem orientedLevel_ne_of_angle_between {p q : Point2} (hpq : p ≠ q)
    {θ₀ : ℝ}
    (hlo : (direction p q).angle - Real.pi < θ₀)
    (hhi : θ₀ < (direction p q).angle) :
    orientedLevel θ₀ p ≠ orientedLevel θ₀ q := by
  intro htie
  have hzero_d := orientedLevel_sub_zero_at_direction_angle' hpq
  have hprod := sinusoid_product_formula hzero_d (θ₁ := θ₀) (θ₂ := θ₀)
  have hzero₀ : -(p.1 - q.1) * Real.sin θ₀ + (p.2 - q.2) * Real.cos θ₀ = 0 := by
    have := orientedLevel_sub_eq θ₀ p q; linarith
  have hsin_neg : Real.sin (θ₀ - (direction p q).angle) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  have hpq_ne : -(p.1 - q.1) ≠ 0 ∨ (p.2 - q.2) ≠ 0 := by
    by_contra h; push_neg at h
    exact hpq (Prod.ext (by linarith [h.1]) (by linarith [h.2]))
  have h_sq_pos : 0 < (-(p.1 - q.1)) ^ 2 + (p.2 - q.2) ^ 2 := by
    rcases hpq_ne with ha | hb <;> positivity
  have hsin_sq_pos : 0 < Real.sin (θ₀ - (direction p q).angle) *
      Real.sin (θ₀ - (direction p q).angle) :=
    mul_pos_of_neg_of_neg hsin_neg hsin_neg
  have h_rhs_pos : 0 < ((-(p.1 - q.1)) ^ 2 + (p.2 - q.2) ^ 2) *
      (Real.sin (θ₀ - (direction p q).angle) * Real.sin (θ₀ - (direction p q).angle)) :=
    mul_pos h_sq_pos hsin_sq_pos
  have h_lhs_zero : (-(p.1 - q.1) * Real.sin θ₀ + (p.2 - q.2) * Real.cos θ₀) *
      (-(p.1 - q.1) * Real.sin θ₀ + (p.2 - q.2) * Real.cos θ₀) = 0 := by
    rw [hzero₀]; ring
  nlinarith [hprod, h_lhs_zero, h_rhs_pos]

theorem orientedLevel_injective_of_all_angles_between {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k)
    {θ₀ : ℝ}
    (hlo : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hhi : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle) :
    Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₀ (L.point a)) := by
  intro a b hab
  by_contra hne
  have hab' : a ≠ b := fun h => by subst h; exact hne rfl
  have hpq : L.point a ≠ L.point b := fun h => hab' (L.point_injective h)
  have hdir_mem := L.direction_mem hab'
  exact orientedLevel_ne_of_angle_between hpq (hlo _ hdir_mem) (hhi _ hdir_mem) hab

theorem orientedLevel_injective_at_non_direction_angle {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) {θ : ℝ}
    (hθ₁ : 0 ≤ θ) (hθ₂ : θ < Real.pi)
    (hne : ∀ d ∈ directionsDeterminedBy points, d.angle ≠ θ) :
    Function.Injective (fun a : Fin (2 * k) => orientedLevel θ (L.point a)) := by
  intro a b hab
  by_contra hneq
  have hab' : a ≠ b := fun h => by subst h; exact hneq rfl
  have hpq : L.point a ≠ L.point b := fun h => hab' (L.point_injective h)
  have hdir_mem := L.direction_mem hab'
  have hdir_angle : (direction (L.point a) (L.point b)).angle = θ :=
    orientedLevel_unique_tie_angle hpq (Direction.angle_nonneg _) (Direction.angle_lt_pi _)
      hθ₁ hθ₂ (orientedLevel_eq_at_direction_angle hpq) hab
  exact hne _ hdir_mem hdir_angle

end ProofsInTheBook.Chapter11
