import ProofsInTheBook.ZinanCh36Theta
import ProofsInTheBook.PolygonWindingExterior

/-!
# `ZinanCh36RayDichotomy` — the full-line crossing list and the CONDITIONAL ray winding
  dichotomy

This file builds, on top of `ZinanCh36Theta`, the *full-line* analogue of the forward
crossing structure and uses it to discharge — CONDITIONALLY on a full-line alternation
hypothesis `Halt` — the ray winding dichotomy that `ZinanCh36Theta.§7` left as its named
residue.  It also proves the residue UNCONDITIONALLY for triangles (`n = 3`), the base case
of the Jordan kernel.

## What is proved here

* **Brick 1 (`LineCrossingEdges`).**  The edges span-crossed by the whole ray LINE through
  `x` (the `SpanCrossesSide`-filter; the exact predicate of
  `ZinanCh36Theta.lineCrossing_eSign_sum_zero`).  Unlike `CrossingEdges'` there is no
  forward `0 ≤ crossTau` guard.

* **Brick 2 (`crossTau_injOn_lineCrossingEdges`).**  Under the vertex-genericity guard
  `hvert` (no polygon vertex on the ray line), distinct line-crossing edges have distinct
  `crossTau` — the simplicity argument of `ZinanCh36Theta.crossTau_injOn_crossingEdges`,
  with the forward guard dropped (every span crossing — forward OR backward — meets its edge
  in the OPEN interior, and two distinct open edge interiors share no point off a vertex).

* **List substrate (`altSum_eq_getLast`, `suffix_sum_mem_of_alt`).**  Pure list
  combinatorics: an alternating `±1` list sums to `0` or to its last entry; hence, for an
  alternating `±1` list summing to `0`, every suffix sums to `0` or to that last entry — the
  two-value suffix law.  `filter_suffix_of_sorted` records that the `c ≤ τ` filter of a
  `τ`-ascending list is a (final-segment) suffix.

* **Brick 3 (`rayWindingDichotomy_of_fullLineAlternation`), CONDITIONAL.**  Given a full-line
  sorted enumeration whose `eSign` image alternates (`Halt`), the signed winding takes at
  most two values `{0, s}` (`s = ±1` the last sign) at every off-boundary point of the
  forward ray.  Proof: `windCross_translate` makes the winding at cut `c ≥ 0` a `τ ≥ c`
  suffix sum of the full-line list (the forward guard is absorbed by `c ≥ 0`); the full sum
  is `0` (`lineCrossing_eSign_sum_zero`); the suffix-sum law closes it.

* **Brick 4 (`triangle_rayWindingDichotomy`), UNCONDITIONAL base case.**  For `n = 3` the
  full-line crossing count is `0` or `2` (a closed triangle crosses any generic line an even
  number of times, and three vertices give at most two sign changes); in either case the
  suffix sums lie in `{0, s}` and the dichotomy holds with no `Halt` input.

* **Brick 5 (`rayCrossingAlternation_of_fullLineAlternation`), CONDITIONAL wrapper.**
  Compose Brick 3 through `ZinanCh36Theta.rayCrossingAlternation_of_ray_dichotomy` to obtain
  the Jordan kernel `RayCrossingAlternation` from `Halt`.

NOT IN SCOPE (the master's brick): the unconditional supply of `Halt` (the lobe/matching
alternation of the full-line crossing list).  Bricks 3 and 5 stay HONESTLY conditional on it.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36Theta

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonWinding (windCross)
open ProofsInTheBook.PolygonWindingExterior (eSign)
open ProofsInTheBook.PolygonWindingBound
  (Alt IsPM1 RayCrossingAlternation eSign_mem windCross_eq_sum_crossing_eSign
    windCross_mem_of_alternation)
open scoped RealInnerProductSpace BigOperators

noncomputable section

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ## §A. The full-line crossing edges (Brick 1) -/

/-- **The edges span-crossed by the whole ray LINE through `x`** (Brick 1).  The
`SpanCrossesSide`-filter — the exact predicate of `lineCrossing_eSign_sum_zero` — with NO
forward `0 ≤ crossTau` guard. -/
def LineCrossingEdges (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => SpanCrossesSide P ρ x i)

lemma mem_lineCrossingEdges_iff (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (i : Fin n) : i ∈ LineCrossingEdges P ρ x ↔ SpanCrossesSide P ρ x i := by
  classical
  unfold LineCrossingEdges
  simp [Finset.mem_filter]

/-- The forward crossing edges are the `0 ≤ crossTau` subset of the line-crossing edges. -/
lemma crossingEdges'_eq_filter_lineCrossing (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) :
    CrossingEdges' P ρ x
      = (LineCrossingEdges P ρ x).filter (fun i => (0 : ℝ) ≤ crossTau P ρ x i) := by
  classical
  ext i
  rw [Finset.mem_filter, mem_lineCrossingEdges_iff, mem_crossingEdges'_iff]
  unfold EdgeCrossesRay'
  tauto

/-! ## §B. Distinct line crossings have distinct ray parameters (Brick 2)

The simplicity argument of `crossTau_injOn_crossingEdges`, with the forward guard dropped:
every span crossing (forward OR backward) meets its edge in the OPEN interior
(`crossU_mem_Ioo`), and two distinct open edge interiors share at most a vertex
(`EdgeIntersectionCondition`), which cannot be on the ray line under `hvert`. -/

/-- **Distinct line crossings have distinct ray parameters** (Brick 2): the full-line
mirror of `crossTau_injOn_crossingEdges`.  Forwardness is not used. -/
theorem crossTau_injOn_lineCrossingEdges (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    {i j : Fin n} (hi : i ∈ LineCrossingEdges P ρ x) (hj : j ∈ LineCrossingEdges P ρ x)
    (hij : i ≠ j) : crossTau P ρ x i ≠ crossTau P ρ x j := by
  intro hτ
  have hspan_i := (mem_lineCrossingEdges_iff P ρ x i).mp hi
  have hspan_j := (mem_lineCrossingEdges_iff P ρ x j).mp hj
  have hui := crossU_mem_Ioo P ρ x i hspan_i (hvert i) (hvert (cyclicNext i))
  have huj := crossU_mem_Ioo P ρ x j hspan_j (hvert j) (hvert (cyclicNext j))
  have hyi : x + crossTau P ρ x i • ρ.r ∈ Edge P.q i :=
    crossPoint_mem_edge P ρ x i ⟨hui.1.le, hui.2.le⟩
  have hyj : x + crossTau P ρ x i • ρ.r ∈ Edge P.q j := by
    rw [hτ]; exact crossPoint_mem_edge P ρ x j ⟨huj.1.le, huj.2.le⟩
  have hside_y : ∀ k : Fin n, P.q k = x + crossTau P ρ x i • ρ.r → False := by
    intro k hk
    apply hvert k
    rw [hk]
    unfold side det2
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hEC := P.edge_intersection i j
  unfold EdgeIntersectionCondition at hEC
  rw [dif_neg hij] at hEC
  by_cases hnext : cyclicNext i = j
  · rw [dif_pos hnext] at hEC
    have hmem : x + crossTau P ρ x i • ρ.r ∈ Edge P.q i ∩ Edge P.q j := ⟨hyi, hyj⟩
    rw [hEC] at hmem
    exact hside_y j (Set.mem_singleton_iff.mp hmem).symm
  · rw [dif_neg hnext] at hEC
    by_cases hprev : cyclicNext j = i
    · rw [dif_pos hprev] at hEC
      have hmem : x + crossTau P ρ x i • ρ.r ∈ Edge P.q i ∩ Edge P.q j := ⟨hyi, hyj⟩
      rw [hEC] at hmem
      exact hside_y i (Set.mem_singleton_iff.mp hmem).symm
    · rw [dif_neg hprev] at hEC
      exact Set.disjoint_left.mp hEC hyi hyj

/-! ## §C. The list substrate: the two-value suffix law

Pure list combinatorics.  An alternating `±1` list sums to `0` or to its last entry;
consequently, for an alternating `±1` list summing to `0`, every suffix sums to `0` or to
that last entry.  And the `c ≤ τ` filter of a `τ`-ascending list is a final-segment
suffix. -/

/-- **An alternating `±1` list sums to `0` or to its last entry.**  (Odd length → first =
last entry; even length → `0`.) -/
theorem altSum_eq_getLast :
    ∀ (L : List ℤ), IsPM1 L → Alt L →
      L.sum = 0 ∨ ∃ v : ℤ, L.getLast? = some v ∧ L.sum = v := by
  intro L
  match L with
  | [] => intro _ _; left; simp
  | [a] =>
    intro hpm _
    right
    exact ⟨a, rfl, by simp⟩
  | (a :: b :: t) =>
    intro hpm halt
    have ha : a = 1 ∨ a = -1 := hpm a (List.mem_cons_self ..)
    have hb : b = 1 ∨ b = -1 := hpm b (List.mem_cons_of_mem a (List.mem_cons_self ..))
    have hab : a ≠ b := halt.1
    have hsum_ab : a + b = 0 := by
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
    have hpmt : IsPM1 (b :: t) := fun x hx =>
      hpm x (List.mem_cons_of_mem a hx)
    have halt2 : Alt (b :: t) := halt.2
    have hpmbt : IsPM1 (b :: t) := hpmt
    -- reduce the sum of `a :: b :: t` to the sum of `t`.
    have hsum_eq : (a :: b :: t).sum = t.sum := by
      simp only [List.sum_cons]
      have : a + (b + t.sum) = (a + b) + t.sum := by ring
      rw [this, hsum_ab, zero_add]
    -- and the getLast? is unchanged.
    have hgl : (a :: b :: t).getLast? = (b :: t).getLast? := by
      rw [List.getLast?_cons_cons]
    -- recurse on `b :: t`.
    have hpmt' : IsPM1 t := fun x hx =>
      hpm x (List.mem_cons_of_mem a (List.mem_cons_of_mem b hx))
    have halt_t : Alt t := by
      cases t with
      | nil => trivial
      | cons c t'' => exact halt2.2
    rcases altSum_eq_getLast t hpmt' halt_t with h0 | ⟨v, hv, hsv⟩
    · left; rw [hsum_eq]; exact h0
    · right
      refine ⟨v, ?_, by rw [hsum_eq]; exact hsv⟩
      rw [hgl]
      -- `(b :: t).getLast? = t.getLast?` when `t` nonempty; `t = []` contradicts `hv`.
      cases t with
      | nil => simp at hv
      | cons c t'' => rw [List.getLast?_cons_cons]; exact hv
  termination_by L => L.length

/-- `Alt` is preserved by dropping a prefix (`List.drop`). -/
theorem alt_drop : ∀ (L : List ℤ) (k : ℕ), Alt L → Alt (L.drop k) := by
  intro L
  induction L with
  | nil => intro k _; simp [Alt]
  | cons a t ih =>
    intro k halt
    cases k with
    | zero => simpa using halt
    | succ m =>
      rw [List.drop_succ_cons]
      cases t with
      | nil => rw [List.drop_nil]; trivial
      | cons b t' => exact ih m halt.2
  -- `Alt (a :: b :: t)` unfolds to `a ≠ b ∧ Alt (b :: t)`; `halt.2` is `Alt (b :: t)`.

/-- `IsPM1` is preserved by dropping a prefix. -/
theorem isPM1_drop (L : List ℤ) (k : ℕ) (h : IsPM1 L) : IsPM1 (L.drop k) :=
  fun x hx => h x (List.mem_of_mem_drop hx)

/-- A `getLast?` of a `drop`-suffix transports to the original list when nonempty. -/
theorem getLast?_drop_eq (L : List ℤ) (k : ℕ) (hk : (L.drop k) ≠ []) :
    (L.drop k).getLast? = L.getLast? := by
  have hsuf : (L.drop k) <:+ L := List.drop_suffix k L
  have hgl : (L.drop k).getLast hk = L.getLast (hsuf.ne_nil hk) := hsuf.getLast hk
  rw [List.getLast?_eq_some_getLast hk, List.getLast?_eq_some_getLast (hsuf.ne_nil hk), hgl]

/-- **The two-value suffix law.**  For an alternating `±1` list `L` summing to `0`, every
`drop`-suffix sums to `0` or to `s`, where `s` is `L`'s last entry (`0` if `L = []`). -/
theorem suffix_sum_mem_of_alt (L : List ℤ) (s : ℤ)
    (hpm : IsPM1 L) (halt : Alt L) (hsum : L.sum = 0)
    (hs : L.getLast? = some s ∨ (L = [] ∧ s = 0)) (k : ℕ) :
    (L.drop k).sum = 0 ∨ (L.drop k).sum = s := by
  by_cases hempty : (L.drop k) = []
  · left; rw [hempty]; simp
  · rcases altSum_eq_getLast (L.drop k) (isPM1_drop L k hpm) (alt_drop L k halt) with
      h0 | ⟨v, hv, hsv⟩
    · left; exact h0
    · right
      rw [hsv]
      -- v = getLast? (drop k) = getLast? L = s
      have hgl := getLast?_drop_eq L k hempty
      rw [hv] at hgl
      rcases hs with hsL | ⟨hLnil, _⟩
      · rw [hsL] at hgl; exact (Option.some.injEq _ _).mp hgl
      · rw [hLnil] at hempty; simp at hempty

/-- **The two-value suffix law, `IsSuffix` form.**  For an alternating `±1` list `L` summing
to `0`, every suffix `T <:+ L` sums to `0` or to `s` (`L`'s last entry, `0` if `L = []`). -/
theorem isSuffix_sum_mem_of_alt (L : List ℤ) (s : ℤ)
    (hpm : IsPM1 L) (halt : Alt L) (hsum : L.sum = 0)
    (hs : L.getLast? = some s ∨ (L = [] ∧ s = 0)) {T : List ℤ} (hT : T <:+ L) :
    T.sum = 0 ∨ T.sum = s := by
  obtain ⟨k, hk⟩ : ∃ k, T = L.drop k :=
    ⟨L.length - T.length, List.suffix_iff_eq_drop.mp hT⟩
  rw [hk]
  exact suffix_sum_mem_of_alt L s hpm halt hsum hs k

/-- **The `c ≤ τ` filter of a `τ`-ascending list is a final-segment suffix.**  Upward
closure (`c ≤ τ` is monotone along the increasing order) makes the kept elements a tail. -/
theorem filter_suffix_of_sorted {α : Type*} (τ : α → ℝ) (c : ℝ) :
    ∀ (L : List α), L.Pairwise (fun a b => τ a < τ b) →
      L.filter (fun i => decide (c ≤ τ i)) <:+ L := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons a t ih =>
    intro hsort
    have hpc := List.pairwise_cons.mp hsort
    by_cases hca : c ≤ τ a
    · -- a kept; every later element also kept (τ increasing) ⇒ filter = whole list.
      have hall : ∀ b ∈ t, c ≤ τ b := fun b hb => le_of_lt (lt_of_le_of_lt hca (hpc.1 b hb))
      have hfeq : (a :: t).filter (fun i => decide (c ≤ τ i)) = a :: t := by
        rw [List.filter_cons_of_pos (by simp [hca])]
        congr 1
        rw [List.filter_eq_self]
        intro b hb; simp [hall b hb]
      rw [hfeq]
    · -- a dropped; filter = filter t, a suffix of t, hence of a :: t.
      rw [List.filter_cons_of_neg (by simp [hca])]
      exact (ih hpc.2).trans (List.suffix_cons a t)

/-! ## §D. Brick 3: the CONDITIONAL ray winding dichotomy

`windCross_translate` makes the signed winding at cut `c ≥ 0` a `τ ≥ c` suffix sum of the
full-line sorted list (the forward `0 ≤ τ` guard is absorbed by `c ≥ 0`); the full sum is
`0` (`lineCrossing_eSign_sum_zero`); the suffix-sum law closes it. -/

/-- A cut-characterised nodup list computes the `c ≤ τ` filtered `eSign` sum of the
line-crossing edges, given `c ≥ 0` (which absorbs the forward guard). -/
theorem windCross_cut_eq_lineFilter_sum (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) {c : ℝ} (hc : 0 ≤ c) :
    windCross P ρ (x + c • ρ.r)
      = ∑ i ∈ (LineCrossingEdges P ρ x).filter (fun i => c ≤ crossTau P ρ x i),
          eSign P ρ i := by
  classical
  rw [windCross_translate P ρ x hc]
  -- the forward filter `(CrossingEdges').filter (c ≤ τ)` equals the line filter `(c ≤ τ)`.
  congr 1
  rw [crossingEdges'_eq_filter_lineCrossing P ρ x, Finset.filter_filter]
  apply Finset.filter_congr
  intro i _
  constructor
  · rintro ⟨_, h2⟩; exact h2
  · intro h; exact ⟨le_trans hc h, h⟩

/-- The full-line `eSign` sum telescopes to `0` along any nodup enumeration of the
line-crossing edges. -/
theorem fullLine_listSum_zero (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (L : List (Fin n)) (hnd : L.Nodup)
    (hmem : ∀ i, i ∈ L ↔ i ∈ LineCrossingEdges P ρ x) :
    (L.map (eSign P ρ)).sum = 0 := by
  classical
  have hline := lineCrossing_eSign_sum_zero P ρ x hvert
  have htf : L.toFinset = LineCrossingEdges P ρ x := by
    ext i; rw [List.mem_toFinset]; exact hmem i
  have hsum : (L.map (eSign P ρ)).sum = ∑ i ∈ L.toFinset, eSign P ρ i :=
    (List.sum_toFinset (eSign P ρ) hnd).symm
  rw [hsum, htf]
  unfold LineCrossingEdges
  exact hline

/-- The signed winding at cut `c ≥ 0` equals the `eSign`-sum of `L.filter (c ≤ τ)`, a
final-segment suffix of the sorted full-line list. -/
theorem windCross_cut_eq_listFilter_sum (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (L : List (Fin n)) (hnd : L.Nodup)
    (hmem : ∀ i, i ∈ L ↔ i ∈ LineCrossingEdges P ρ x)
    {c : ℝ} (hc : 0 ≤ c) :
    windCross P ρ (x + c • ρ.r)
      = ((L.filter (fun i => decide (c ≤ crossTau P ρ x i))).map (eSign P ρ)).sum := by
  classical
  rw [windCross_cut_eq_lineFilter_sum P ρ x hc]
  set Lc : List (Fin n) := L.filter (fun i => decide (c ≤ crossTau P ρ x i)) with hLcdef
  have hLcnd : Lc.Nodup := hnd.filter _
  have hLcmem : ∀ i, i ∈ Lc ↔ i ∈ LineCrossingEdges P ρ x ∧ c ≤ crossTau P ρ x i := by
    intro i
    rw [hLcdef, List.mem_filter]
    constructor
    · rintro ⟨hiL, hd⟩
      exact ⟨(hmem i).mp hiL, by simpa using hd⟩
    · rintro ⟨hiLC, hcτ⟩
      exact ⟨(hmem i).mpr hiLC, by simpa using hcτ⟩
  have hset : (LineCrossingEdges P ρ x).filter (fun i => c ≤ crossTau P ρ x i)
      = Lc.toFinset := by
    ext a
    rw [Finset.mem_filter, List.mem_toFinset, hLcmem]
  rw [hset]
  exact List.sum_toFinset (eSign P ρ) hLcnd

/-- **Brick 3 (CONDITIONAL): the ray winding dichotomy from a full-line alternation.**  Let
`x` be off the boundary with no polygon vertex on its ray line.  Given a full-line sorted
enumeration `L` of the line-crossing edges whose `eSign` image alternates (`Halt`), the
signed winding takes at most the two values `{0, s}` (`s = ±1` the last sign) at every
off-boundary point of the forward ray. -/
theorem rayWindingDichotomy_of_fullLineAlternation
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hoff : ¬ OnBoundary P x)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (Halt : ∃ L : List (Fin n), L.Nodup ∧
        (∀ i, i ∈ L ↔ i ∈ LineCrossingEdges P ρ x) ∧
        L.Pairwise (fun a b => crossTau P ρ x a < crossTau P ρ x b) ∧
        Alt (L.map (eSign P ρ))) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ∀ c : ℝ, 0 ≤ c → ¬ OnBoundary P (x + c • ρ.r) →
        windCross P ρ (x + c • ρ.r) = 0 ∨ windCross P ρ (x + c • ρ.r) = s := by
  classical
  obtain ⟨L, hnd, hmem, hsort, hAltL⟩ := Halt
  set σL : List ℤ := L.map (eSign P ρ) with hσLdef
  have hpmσ : IsPM1 σL := by
    intro v hv
    rw [hσLdef, List.mem_map] at hv
    obtain ⟨i, _, rfl⟩ := hv
    exact eSign_mem P ρ i
  have hfullSum : σL.sum = 0 := fullLine_listSum_zero P ρ x hvert L hnd hmem
  -- Pick `s` = last sign of `σL` (1 if empty), and pin `s = ±1`.
  rcases σL.eq_nil_or_concat with hnil | ⟨ys, yl, hcat⟩
  · -- empty sign list ⇒ `L = []`, every forward filter is empty ⇒ winding `0`; `s = 1`.
    refine ⟨1, Or.inl rfl, ?_⟩
    have hLnil : L = [] := by
      rcases L.eq_nil_or_concat with h | ⟨zs, zl, hz⟩
      · exact h
      · exact absurd hnil (by rw [hσLdef, hz]; simp)
    intro c hc _
    left
    rw [windCross_cut_eq_listFilter_sum P ρ x L hnd hmem hc, hLnil]
    simp
  · -- nonempty: `yl` is the last sign, `±1`.
    have hgl : σL.getLast? = some yl := by rw [hcat]; simp
    have hyl : yl = 1 ∨ yl = -1 := hpmσ yl (List.mem_of_getLast? hgl)
    refine ⟨yl, hyl, ?_⟩
    intro c hc _
    rw [windCross_cut_eq_listFilter_sum P ρ x L hnd hmem hc]
    -- the filter is a suffix of `L`, so its sign-map is a suffix of `σL`.
    have hsuf : (L.filter (fun i => decide (c ≤ crossTau P ρ x i))) <:+ L :=
      filter_suffix_of_sorted (crossTau P ρ x) c L hsort
    have hsufσ :
        (L.filter (fun i => decide (c ≤ crossTau P ρ x i))).map (eSign P ρ) <:+ σL :=
      hsuf.map (eSign P ρ)
    exact isSuffix_sum_mem_of_alt σL yl hpmσ hAltL hfullSum (Or.inl hgl) hsufσ

/-! ## §E. Brick 4: the UNCONDITIONAL triangle base case (`n = 3`)

A closed triangle crosses any generic line an even number of times: the full-line `eSign`
sum is `0`, so the `±1` crossing count is even.  With at most three edges this count is `0`
or `2`; in either case the sorted full-line list has length `≤ 2` and therefore alternates
trivially.  Hence `Halt` holds UNCONDITIONALLY for `n = 3`, and Brick 3 closes the
dichotomy with no external alternation input. -/

/-- A `±1` list of length `≤ 2` summing to `0` alternates (the only nontrivial case, length
`2`, forces opposite signs). -/
theorem alt_of_len_le_two (M : List ℤ) (hpm : IsPM1 M) (hlen : M.length ≤ 2)
    (hsum : M.sum = 0) : Alt M := by
  match M, hpm, hlen, hsum with
  | [], _, _, _ => trivial
  | [_a], _, _, _ => trivial
  | [a, b], hpm, _, hsum =>
    have ha : a = 1 ∨ a = -1 := hpm a (List.mem_cons_self ..)
    have hb : b = 1 ∨ b = -1 := hpm b (List.mem_cons_of_mem a (List.mem_cons_self ..))
    have hs : a + b = 0 := by simpa using hsum
    refine ⟨?_, trivial⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
  | (a :: b :: c :: t), _, hlen, _ =>
    exfalso
    simp only [List.length_cons] at hlen
    omega

/-- The full-line crossing list of a TRIANGLE has length `≤ 2`: at most three edges, and the
`±1`-`eSign` sum is `0`, so the count is even, hence `0` or `2`. -/
theorem lineCrossing_card_le_two (Q : StrictSimplePolygon 3) (ρ : RayDirection Q) (x : Pt)
    (hvert : ∀ k : Fin 3, side ρ.r x (Q.q k) ≠ 0)
    (L : List (Fin 3)) (hnd : L.Nodup)
    (hmem : ∀ i, i ∈ L ↔ i ∈ LineCrossingEdges Q ρ x) :
    L.length ≤ 2 := by
  classical
  -- length ≤ 3 (nodup list over Fin 3).
  have hle3 : L.length ≤ 3 := by
    have : L.toFinset.card ≤ (Finset.univ : Finset (Fin 3)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rwa [List.toFinset_card_of_nodup hnd, Finset.card_univ, Fintype.card_fin] at this
  -- the ±1 sum is 0 ⇒ length is even ⇒ not 3.
  have hpmσ : IsPM1 (L.map (eSign Q ρ)) := by
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨i, _, rfl⟩ := hv
    exact eSign_mem Q ρ i
  have hsum0 : (L.map (eSign Q ρ)).sum = 0 := fullLine_listSum_zero Q ρ x hvert L hnd hmem
  -- if length were 3, the ±1 sum would be odd, contradicting sum = 0.
  by_contra hgt
  have hlen3 : L.length = 3 := by omega
  -- a ±1 list of odd length has odd sum, so ≠ 0.
  have hodd : Odd (L.map (eSign Q ρ)).sum := by
    have hlenσ : (L.map (eSign Q ρ)).length = 3 := by rw [List.length_map]; exact hlen3
    -- parity of a ±1 sum equals parity of its length.
    have hparity : ∀ (M : List ℤ), IsPM1 M → M.sum % 2 = (M.length : ℤ) % 2 := by
      intro M
      induction M with
      | nil => intro _; simp
      | cons a t ih =>
        intro hpm
        have ha : a = 1 ∨ a = -1 := hpm a (List.mem_cons_self ..)
        have hpt : IsPM1 t := fun y hy => hpm y (List.mem_cons_of_mem a hy)
        have := ih hpt
        simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        rcases ha with rfl | rfl <;> omega
    have hp := hparity (L.map (eSign Q ρ)) hpmσ
    rw [hlenσ] at hp
    rw [Int.odd_iff]
    omega
  rw [hsum0] at hodd
  exact (by decide : ¬ Odd (0 : ℤ)) hodd

/-- **Brick 4 (UNCONDITIONAL base case): the triangle ray winding dichotomy.**  For a strict
simple triangle (`n = 3`), an off-boundary point with no vertex on its ray line has the
two-value ray winding dichotomy WITHOUT any external alternation input — the full-line
crossing list has length `≤ 2`, hence alternates trivially. -/
theorem triangle_rayWindingDichotomy (Q : StrictSimplePolygon 3) (ρ : RayDirection Q) (x : Pt)
    (hoff : ¬ OnBoundary Q x)
    (hvert : ∀ k : Fin 3, side ρ.r x (Q.q k) ≠ 0) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ∀ c : ℝ, 0 ≤ c → ¬ OnBoundary Q (x + c • ρ.r) →
        windCross Q ρ (x + c • ρ.r) = 0 ∨ windCross Q ρ (x + c • ρ.r) = s := by
  classical
  -- the genericity guard gives `crossTau`-injectivity, so a sorted enumeration exists.
  have hinj : ∀ a ∈ LineCrossingEdges Q ρ x, ∀ b ∈ LineCrossingEdges Q ρ x,
      crossTau Q ρ x a = crossTau Q ρ x b → a = b := by
    intro a ha b hb hEq
    by_contra hne
    exact crossTau_injOn_lineCrossingEdges Q ρ x hvert ha hb hne hEq
  obtain ⟨L, hnd, hmem, hsort⟩ :=
    exists_sorted_enum (crossTau Q ρ x) (LineCrossingEdges Q ρ x) hinj
  -- the mapped sign list alternates trivially (length ≤ 2, ±1 sum 0).
  have hpmσ : IsPM1 (L.map (eSign Q ρ)) := by
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨i, _, rfl⟩ := hv
    exact eSign_mem Q ρ i
  have hsum0 : (L.map (eSign Q ρ)).sum = 0 := fullLine_listSum_zero Q ρ x hvert L hnd hmem
  have hlen : (L.map (eSign Q ρ)).length ≤ 2 := by
    rw [List.length_map]; exact lineCrossing_card_le_two Q ρ x hvert L hnd hmem
  have hAltL : Alt (L.map (eSign Q ρ)) := alt_of_len_le_two _ hpmσ hlen hsum0
  exact rayWindingDichotomy_of_fullLineAlternation Q ρ x hoff hvert
    ⟨L, hnd, hmem, hsort, hAltL⟩

/-! ## §F. Brick 5: the CONDITIONAL `RayCrossingAlternation` wrapper

Compose Brick 3 through `rayCrossingAlternation_of_ray_dichotomy` to obtain the Jordan
kernel from the full-line alternation hypothesis `Halt`. -/

/-- **Brick 5 (CONDITIONAL wrapper): `RayCrossingAlternation` from a full-line alternation.**
-/
theorem rayCrossingAlternation_of_fullLineAlternation
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hoff : ¬ OnBoundary P x)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (Halt : ∃ L : List (Fin n), L.Nodup ∧
        (∀ i, i ∈ L ↔ i ∈ LineCrossingEdges P ρ x) ∧
        L.Pairwise (fun a b => crossTau P ρ x a < crossTau P ρ x b) ∧
        Alt (L.map (eSign P ρ))) :
    RayCrossingAlternation P ρ x := by
  obtain ⟨s, hs, H⟩ :=
    rayWindingDichotomy_of_fullLineAlternation P ρ x hoff hvert Halt
  exact rayCrossingAlternation_of_ray_dichotomy P ρ x hoff hvert s hs H

/-- **The triangle Jordan kernel, UNCONDITIONAL.**  Composing Brick 4 with the reduction:
for a strict simple triangle, `RayCrossingAlternation` holds at every generic off-boundary
point with no external input. -/
theorem triangle_rayCrossingAlternation (Q : StrictSimplePolygon 3) (ρ : RayDirection Q)
    (x : Pt) (hoff : ¬ OnBoundary Q x)
    (hvert : ∀ k : Fin 3, side ρ.r x (Q.q k) ≠ 0) :
    RayCrossingAlternation Q ρ x := by
  obtain ⟨s, hs, H⟩ := triangle_rayWindingDichotomy Q ρ x hoff hvert
  exact rayCrossingAlternation_of_ray_dichotomy Q ρ x hoff hvert s hs H

end

end ProofsInTheBook.ZinanCh36Theta

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.ZinanCh36Theta.LineCrossingEdges
#print axioms ProofsInTheBook.ZinanCh36Theta.crossingEdges'_eq_filter_lineCrossing
#print axioms ProofsInTheBook.ZinanCh36Theta.crossTau_injOn_lineCrossingEdges
#print axioms ProofsInTheBook.ZinanCh36Theta.altSum_eq_getLast
#print axioms ProofsInTheBook.ZinanCh36Theta.suffix_sum_mem_of_alt
#print axioms ProofsInTheBook.ZinanCh36Theta.isSuffix_sum_mem_of_alt
#print axioms ProofsInTheBook.ZinanCh36Theta.filter_suffix_of_sorted
#print axioms ProofsInTheBook.ZinanCh36Theta.windCross_cut_eq_lineFilter_sum
#print axioms ProofsInTheBook.ZinanCh36Theta.fullLine_listSum_zero
#print axioms ProofsInTheBook.ZinanCh36Theta.windCross_cut_eq_listFilter_sum
#print axioms ProofsInTheBook.ZinanCh36Theta.rayWindingDichotomy_of_fullLineAlternation
#print axioms ProofsInTheBook.ZinanCh36Theta.alt_of_len_le_two
#print axioms ProofsInTheBook.ZinanCh36Theta.lineCrossing_card_le_two
#print axioms ProofsInTheBook.ZinanCh36Theta.triangle_rayWindingDichotomy
#print axioms ProofsInTheBook.ZinanCh36Theta.rayCrossingAlternation_of_fullLineAlternation
#print axioms ProofsInTheBook.ZinanCh36Theta.triangle_rayCrossingAlternation