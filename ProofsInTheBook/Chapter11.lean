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

theorem direction_mem_directionsDeterminedBy {points : Finset Point2} {p q : Point2}
    (hp : p ∈ points) (hq : q ∈ points) (hpq : p ≠ q) :
    direction p q ∈ directionsDeterminedBy points := by
  exact Finset.mem_image.mpr ⟨(p, q), by simp [hp, hq, hpq], rfl⟩

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

theorem mem_leftBarrierPositions {k d : ℕ} {p : Fin (2 * k)} :
    p ∈ leftBarrierPositions k d ↔ k - d ≤ p.val ∧ p.val < k := by
  simp [leftBarrierPositions]

theorem mem_rightBarrierPositions {k d : ℕ} {p : Fin (2 * k)} :
    p ∈ rightBarrierPositions k d ↔ k ≤ p.val ∧ p.val < k + d := by
  simp [rightBarrierPositions]

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

end PositionInterval

/--
A simultaneous move reverses several pairwise-disjoint consecutive blocks.
The actual permutation is kept as data; later lemmas prove its middle-barrier
crossing count from the block fields.
-/
structure BlockMove (N : ℕ) where
  blockCount : ℕ
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

def middleLeftPosition (k : ℕ) (hk : 0 < k) : Fin (2 * k) :=
  ⟨k - 1, by omega⟩

def middleRightPosition (k : ℕ) (hk : 0 < k) : Fin (2 * k) :=
  ⟨k, by omega⟩

def MiddlePairIncreasing (π : State (2 * k)) (hk : 0 < k) : Prop :=
  (π (middleLeftPosition k hk)).val < (π (middleRightPosition k hk)).val

def MiddlePairDecreasing (π : State (2 * k)) (hk : 0 < k) : Prop :=
  (π (middleRightPosition k hk)).val < (π (middleLeftPosition k hk)).val

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

theorem increasing_before_block {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (i : Fin M.move.blockCount) :
    IncreasingOnPositions π (M.move.block i).toFinset := by
  intro p hp q hq hpq
  rw [PositionInterval.mem_toFinset] at hp hq
  exact M.increasing_before i hp hq hpq

theorem decreasing_after_block_of_reversesBlocks {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (i : Fin M.move.blockCount) :
    DecreasingOnPositions ρ (M.move.block i).toFinset := by
  intro p hp q hq hpq
  rw [PositionInterval.mem_toFinset] at hp hq
  exact M.label_decreases_after_block_of_reversesBlocks hrev i hp hq hpq

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

end ConcreteGeneralizedAllowableSequence

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

theorem ungar_directions_lower_bound_from_sweep (points : Finset Point2)
    (hn : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : EvenUngarSweepCertificatePremise) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  directions_lower_bound_of_even_ungar_sweep_certificates points hn hncoll hcert

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
    (hcert : EvenUngarSweepCertificatePremise) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  ungar_directions_lower_bound_from_sweep points hn hncoll hcert

theorem chapter11 {ι : Type*} [Fintype ι] (points : Finset Point2) (witness : ι → ℝ)
    (hwitness : ∀ i, witness i ∈ slopesDeterminedBy points)
    (hinj : Function.Injective witness) :
    Fintype.card ι ≤ (slopesDeterminedBy points).card :=
  card_le_slopes_of_injective_witness points witness hwitness hinj

end ProofsInTheBook.Chapter11
