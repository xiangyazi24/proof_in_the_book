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
