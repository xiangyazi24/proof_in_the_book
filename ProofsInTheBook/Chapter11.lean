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

/--
Finite schedule of crossing moves in Ungar's middle-barrier proof.  The
additional `idx` and gap fields are the data coming from the T/O/C pattern;
the inherited `blocks_fit` is the arithmetic consequence currently used by
the downstream certificate.
-/
structure UngarMoveSchedule (k r : ℕ) extends UngarCountingCertificate (2 * k) r where
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

theorem UngarMoveSchedule.sum_orders_le_moves {k r : ℕ}
    (C : UngarMoveSchedule k r) :
    (∑ i : Fin C.crossingCount, 2 * C.order i) ≤ r :=
  C.blocks_fit

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

/--
A reversal step together with the key finite counting theorem for that step.
The block-reversal geometry should eventually prove this field.
-/
structure CountedReversalStep (k : ℕ) (π ρ : State (2 * k)) extends
    ReversalStep k π ρ where
  crossed_labels_card : stepCrossingLabelsCard k π ρ = 2 * toReversalStep.order

/-- A generalized allowable sequence with counted reversal data on every step. -/
structure CountedGeneralizedAllowableSequence (k r : ℕ) where
  seq : GeneralizedAllowableSequence k r
  step : ∀ j : Fin r, CountedReversalStep k (seq.π (stepFrom j)) (seq.π (stepTo j))

namespace CountedGeneralizedAllowableSequence

/-- Counted reversal steps produce the `StepCounting` data used above. -/
noncomputable def toStepCounting {k r : ℕ} (A : CountedGeneralizedAllowableSequence k r) :
    GeneralizedAllowableSequence.StepCounting A.seq where
  order := fun j => (A.step j).toReversalStep.order
  crossed_labels_card := by
    intro j
    simpa [GeneralizedAllowableSequence.crossingLabelsCard, stepCrossingLabelsCard]
      using (A.step j).crossed_labels_card

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
The remaining geometric/combinatorial core of Ungar's proof: for every even
non-collinear point set, the rotating projection sequence supplies the finite
sweep certificate above.
-/
noncomputable def even_ungar_sweep_certificate (points : Finset Point2)
    (_hEven : Even points.card) (_hncoll : NoncollinearSet points) :
    UngarSweepCertificate points.card (directionsDeterminedBy points).card := by
  sorry

theorem ungar_directions_lower_bound_from_sweep (points : Finset Point2)
    (hn : 3 ≤ points.card) (hncoll : NoncollinearSet points) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  directions_lower_bound_of_even_ungar_sweep_certificates points hn hncoll
    (fun S hEven hS => even_ungar_sweep_certificate S hEven hS)

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
    (hncoll : NoncollinearSet points) :
    points.card - 1 ≤ (directionsDeterminedBy points).card :=
  ungar_directions_lower_bound_from_sweep points hn hncoll

theorem chapter11 {ι : Type*} [Fintype ι] (points : Finset Point2) (witness : ι → ℝ)
    (hwitness : ∀ i, witness i ∈ slopesDeterminedBy points)
    (hinj : Function.Injective witness) :
    Fintype.card ι ≤ (slopesDeterminedBy points).card :=
  card_le_slopes_of_injective_witness points witness hwitness hinj

end ProofsInTheBook.Chapter11
