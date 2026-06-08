import ProofsInTheBook.PlanarMapCutCapCounts

/-!
# The cut-and-cap vertex count `V' = V + k` (Chapter 35 Jordan lemma)

This file closes the `vertex_count` field of `CutSigmaCounts`
(`PlanarMapCutCapSigma.lean`) for the concrete cut map `C.cutCapMap`:

  `(C.cutCapMap).V = M.V + C.len`.

The route is the design's transposition cycle count, carried out on top of the
verified toolkit in `PlanarMapCutCapCounts.lean`.  We exhibit `cutSigmaPerm` as

  `cutSigmaPerm = sigmaLift * mergeProd * splitProd`

where (reading the products by index `i : Fin k`):

* `mergeProd = ∏_i swap(ℓ_i^+, c_i^+) · swap(ℓ_i^-, c_i^-)` — the `2k` insertion
  swaps that splice the two fixed caps into the `σ`-orbit at `v_i` (each *merging*
  a fixed cap into that orbit: `numCycles` drops by `2k`, `V+2k → V`);
* `splitProd = ∏_i swap(c_i^+, c_i^-)` — the `k` swaps that *split* each merged
  orbit into its two banks (`numCycles` rises by `k`, `V → V+k`).

The split-phase side condition is `Q.SameCycle c_i^+ c_i^-` for `Q = sigmaLift *
mergeProd`, which is reduced to `σ.SameCycle p_i q_i` (both darts have tail `v_i`),
and the disjointness `¬ Q.SameCycle` conditions are reduced to `¬ σ.SameCycle`
between darts at *distinct* cycle vertices.  Both reductions go through a single
projection semiconjugacy `proj (Q x) ∈ {σ (proj x), proj x}`.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount

/-! ## The bank-start darts lie in one `σ`-orbit -/

/-- `p_i` and `q_i` share the tail vertex `v_i`. -/
lemma tail_pDart_eq_tail_qDart (C : SimplePrimalCycle M) (i : Fin C.len) :
    M.tail (C.pDart i) = M.tail (C.qDart i) := by
  rw [pDart_def, qDart_def, M.tail_alpha]
  -- `head (dart (prevIdx i)) = tail (dart (nextIdx (prevIdx i))) = tail (dart i)`
  rw [← C.tail_dart_nextIdx (C.prevIdx i), C.nextIdx_prevIdx]

/-- `p_i` and `q_i` lie in the same `σ`-cycle. -/
lemma sameCycle_pDart_qDart (C : SimplePrimalCycle M) (i : Fin C.len) :
    M.σ.SameCycle (C.pDart i) (C.qDart i) := by
  have h : Quotient.mk (cycleSetoid M.σ) (C.pDart i)
      = Quotient.mk (cycleSetoid M.σ) (C.qDart i) := C.tail_pDart_eq_tail_qDart i
  exact Quotient.exact h

/-- The tail vertex of `q_i` is `M.tail (C.dart i)`, the `i`-th cycle vertex. -/
lemma tail_qDart (C : SimplePrimalCycle M) (i : Fin C.len) :
    M.tail (C.qDart i) = M.tail (C.dart i) := rfl

/-- Distinct cycle indices give `p`-darts (resp. `q`-darts) in distinct
`σ`-orbits.  The shared tail of `p_i, q_i` is the `i`-th cycle vertex
`M.tail (dart i)`, and these are pairwise distinct by `tail_inj`. -/
lemma not_sameCycle_pDart_of_ne (C : SimplePrimalCycle M) {i j : Fin C.len}
    (hij : i ≠ j) : ¬ M.σ.SameCycle (C.pDart i) (C.pDart j) := by
  intro h
  apply hij
  have hq : M.tail (C.pDart i) = M.tail (C.pDart j) := Quotient.sound h
  rw [C.tail_pDart_eq_tail_qDart i, C.tail_pDart_eq_tail_qDart j,
    C.tail_qDart i, C.tail_qDart j] at hq
  exact C.tail_inj hq

/-! ## Distinctness of the bank-end and cap darts -/

@[simp] lemma lEndPlus_ne_capP (C : SimplePrimalCycle M) (i j : Fin C.len) :
    C.lEndPlus i ≠ C.capP j := by simp [lEndPlus, capP]
@[simp] lemma lEndPlus_ne_capM (C : SimplePrimalCycle M) (i j : Fin C.len) :
    C.lEndPlus i ≠ C.capM j := by simp [lEndPlus, capM]
@[simp] lemma lEndMinus_ne_capP (C : SimplePrimalCycle M) (i j : Fin C.len) :
    C.lEndMinus i ≠ C.capP j := by simp [lEndMinus, capP]
@[simp] lemma lEndMinus_ne_capM (C : SimplePrimalCycle M) (i j : Fin C.len) :
    C.lEndMinus i ≠ C.capM j := by simp [lEndMinus, capM]

lemma capP_ne_capM (C : SimplePrimalCycle M) (i j : Fin C.len) :
    C.capP i ≠ C.capM j := by simp [capP, capM]

lemma capP_inj (C : SimplePrimalCycle M) {i j : Fin C.len} (h : C.capP i = C.capP j) :
    i = j := by simpa [capP] using h

lemma capM_inj (C : SimplePrimalCycle M) {i j : Fin C.len} (h : C.capM i = C.capM j) :
    i = j := by simpa [capM] using h

lemma lEndPlus_inj (C : SimplePrimalCycle M) {i j : Fin C.len}
    (h : C.lEndPlus i = C.lEndPlus j) : i = j := by
  simp only [lEndPlus, Sum.inl.injEq] at h
  exact C.pDart_inj (M.σ.symm.injective h)

lemma lEndMinus_inj (C : SimplePrimalCycle M) {i j : Fin C.len}
    (h : C.lEndMinus i = C.lEndMinus j) : i = j := by
  simp only [lEndMinus, Sum.inl.injEq] at h
  exact C.qDart_inj (M.σ.symm.injective h)

lemma lEndPlus_ne_lEndMinus (C : SimplePrimalCycle M) (i j : Fin C.len) :
    C.lEndPlus i ≠ C.lEndMinus j := by
  simp only [lEndPlus, lEndMinus, ne_eq, Sum.inl.injEq]
  intro h
  exact C.pDart_ne_qDart i j (M.σ.symm.injective h)

/-! ## Evaluating a product of pairwise-disjoint transpositions -/

end SimplePrimalCycle

namespace CutCapCount

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- In a product of transpositions whose pairs are pairwise disjoint as point sets,
a point `x` equal to the head pair's first entry (and disjoint from every tail pair)
is sent to that pair's second entry. -/
lemma listSwap_prod_apply_fst (x y : E) (l : List (E × E))
    (hx : ∀ w ∈ l, x ≠ w.1 ∧ x ≠ w.2) :
    (((x, y) :: l).map (fun w => Equiv.swap w.1 w.2)).prod x = y := by
  rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
  rw [CutCapCount.listSwap_prod_apply_of_notMem x l hx]
  simp

/-- A swap product fixes a point disjoint from every pair (restated for membership
hypotheses obtained from `flatMap`/`map`). -/
lemma listSwap_prod_fix (x : E) (l : List (E × E))
    (h : ∀ w ∈ l, x ≠ w.1 ∧ x ≠ w.2) :
    (l.map (fun w => Equiv.swap w.1 w.2)).prod x = x :=
  CutCapCount.listSwap_prod_apply_of_notMem x l h

/-- **Orbit-fixed transport (powers).**  If `g` fixes every point of the
`p`-cycle of `a`, then `p * g` iterates as `p` from `a`. -/
lemma pow_mul_apply_of_orbit_fixed (p g : Equiv.Perm E) {a : E}
    (hfix : ∀ y, p.SameCycle a y → g y = y) :
    ∀ n : ℕ, ((p * g) ^ n) a = (p ^ n) a := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, Equiv.Perm.mul_apply,
        hfix ((p ^ n) a) ⟨(n : ℤ), by rw [zpow_natCast]⟩, ← Equiv.Perm.mul_apply, ← pow_succ']

/-- **Orbit-fixed transport (`SameCycle`).**  If `g` fixes every point of the
`p`-cycle of `a`, then `p.SameCycle a b` transfers to `p * g`. -/
lemma sameCycle_mul_of_orbit_fixed (p g : Equiv.Perm E) {a b : E}
    (hfix : ∀ y, p.SameCycle a y → g y = y) (hab : p.SameCycle a b) :
    (p * g).SameCycle a b := by
  obtain ⟨n, hn⟩ := hab.exists_nat_pow_eq
  exact ⟨(n : ℤ), by rw [zpow_natCast, pow_mul_apply_of_orbit_fixed p g hfix n, hn]⟩

/-- A fixed point stays fixed under all powers. -/
lemma pow_apply_of_fixed (p : Equiv.Perm E) {b : E} (hb : p b = b) :
    ∀ n : ℕ, (p ^ n) b = b := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hb]

/-- A point distinct from a fixed point of `p` is not `p`-co-cyclic with it. -/
lemma not_sameCycle_of_fixed (p : Equiv.Perm E) {a b : E}
    (hb : p b = b) (hab : a ≠ b) : ¬ p.SameCycle a b := by
  intro h
  obtain ⟨n, hn⟩ := h.symm.exists_nat_pow_eq
  exact hab ((pow_apply_of_fixed p hb n).symm.trans hn).symm

end CutCapCount

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount

/-! ## The merge and split swap lists -/

/-- The `2k` merge swaps: for each `i`, splice the two caps into the `σ`-orbit at
`v_i` by swapping each bank-end with its cap. -/
noncomputable def mergeList (C : SimplePrimalCycle M) : List (C.CutDart × C.CutDart) :=
  (List.finRange C.len).flatMap (fun i => [(C.lEndPlus i, C.capP i), (C.lEndMinus i, C.capM i)])

/-- The `k` split swaps: for each `i`, separate the merged orbit into its two banks
by swapping the two caps. -/
noncomputable def splitList (C : SimplePrimalCycle M) : List (C.CutDart × C.CutDart) :=
  (List.finRange C.len).map (fun i => (C.capP i, C.capM i))

/-- The product of the merge swaps. -/
noncomputable def mergeProd (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  (C.mergeList.map (fun w => Equiv.swap w.1 w.2)).prod

/-- The product of the split swaps. -/
noncomputable def splitProd (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  (C.splitList.map (fun w => Equiv.swap w.1 w.2)).prod

/-! ### Action of the split product

`splitProd` is a product of the pairwise-disjoint transpositions `swap c_i^+ c_i^-`.
It fixes every `inl d`, and swaps each cap pair. -/

/-- Over an arbitrary index list, the split product fixes `inl d`. -/
lemma splitMap_apply_inl (C : SimplePrimalCycle M) (d : D) (L : List (Fin C.len)) :
    ((L.map (fun i => (C.capP i, C.capM i))).map
        (fun w => Equiv.swap w.1 w.2)).prod (Sum.inl d) = Sum.inl d := by
  apply CutCapCount.listSwap_prod_fix
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨i, _, rfl⟩ := hw
  exact ⟨by simp [capP], by simp [capM]⟩

/-- The split product over a `Nodup` index list sends `capP i` to `capM i` when
`i` is in the list, and fixes it otherwise. -/
lemma splitMap_apply_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    ∀ L : List (Fin C.len), L.Nodup →
      ((L.map (fun j => (C.capP j, C.capM j))).map
        (fun w => Equiv.swap w.1 w.2)).prod (C.capP i)
        = if i ∈ L then C.capM i else C.capP i := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons j L' ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      obtain ⟨hj, hL'⟩ := hnd
      rw [List.map_cons, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih hL']
      by_cases hij : i = j
      · subst hij
        have hni : i ∉ L' := hj
        simp only [hni, if_false, List.mem_cons, true_or, if_true]
        exact Equiv.swap_apply_left _ _
      · by_cases hmem : i ∈ L'
        · simp only [hmem, if_true, List.mem_cons, or_true]
          -- apply `swap (capP j) (capM j)` to `capM i`: disjoint
          rw [Equiv.swap_apply_of_ne_of_ne
            (fun h => C.capP_ne_capM j i h.symm)
            (fun h => hij (C.capM_inj h))]
        · simp only [hmem, if_false, List.mem_cons, hij, false_or, if_false]
          -- apply `swap (capP j) (capM j)` to `capP i`: disjoint
          rw [Equiv.swap_apply_of_ne_of_ne
            (fun h => hij (C.capP_inj h)) (fun h => C.capP_ne_capM i j h)]

/-- The split product over a `Nodup` index list sends `capM i` to `capP i` when
`i` is in the list, and fixes it otherwise. -/
lemma splitMap_apply_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    ∀ L : List (Fin C.len), L.Nodup →
      ((L.map (fun j => (C.capP j, C.capM j))).map
        (fun w => Equiv.swap w.1 w.2)).prod (C.capM i)
        = if i ∈ L then C.capP i else C.capM i := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons j L' ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      obtain ⟨hj, hL'⟩ := hnd
      rw [List.map_cons, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih hL']
      by_cases hij : i = j
      · subst hij
        have hni : i ∉ L' := hj
        simp only [hni, if_false, List.mem_cons, true_or, if_true]
        exact Equiv.swap_apply_right _ _
      · by_cases hmem : i ∈ L'
        · simp only [hmem, if_true, List.mem_cons, or_true]
          rw [Equiv.swap_apply_of_ne_of_ne
            (fun h => hij (C.capP_inj h)) (fun h => C.capP_ne_capM i j h)]
        · simp only [hmem, if_false, List.mem_cons, hij, false_or, if_false]
          rw [Equiv.swap_apply_of_ne_of_ne
            (fun h => C.capP_ne_capM j i h.symm) (fun h => hij (C.capM_inj h))]

/-! ### `splitProd` closed forms -/

@[simp] lemma splitProd_inl (C : SimplePrimalCycle M) (d : D) :
    C.splitProd (Sum.inl d) = Sum.inl d := by
  rw [splitProd, splitList]; exact C.splitMap_apply_inl d _

@[simp] lemma splitProd_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.splitProd (C.capP i) = C.capM i := by
  rw [splitProd, splitList, C.splitMap_apply_capP i _ (List.nodup_finRange _)]
  simp [List.mem_finRange]

@[simp] lemma splitProd_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.splitProd (C.capM i) = C.capP i := by
  rw [splitProd, splitList, C.splitMap_apply_capM i _ (List.nodup_finRange _)]
  simp [List.mem_finRange]

/-! ### Action of the merge product

`mergeProd` is the product of the `2k` pairwise-disjoint transpositions
`swap (ℓ_i^±) (c_i^±)`.  Per index, the two swaps act on the four points
`ℓ_i^+, c_i^+, ℓ_i^-, c_i^-`, all distinct across all indices. -/

/-- The head 2-block of the merge flatMap at index `j`, as a product, applied to a
point disjoint from `ℓ_j^±, c_j^±`, fixes it. -/
lemma mergeBlock_fix (C : SimplePrimalCycle M) (j : Fin C.len) (x : C.CutDart)
    (h1 : x ≠ C.lEndPlus j) (h2 : x ≠ C.capP j)
    (h3 : x ≠ C.lEndMinus j) (h4 : x ≠ C.capM j) :
    (Equiv.swap (C.lEndPlus j) (C.capP j))
      ((Equiv.swap (C.lEndMinus j) (C.capM j)) x) = x := by
  rw [Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- Disjointness of `inl d` from the merge pairs at index `j` (when `d` is not the
two bank-ends at `j`). -/
lemma inl_ne_merge_points (C : SimplePrimalCycle M) {d : D} {j : Fin C.len}
    (hp : Sum.inl d ≠ C.lEndPlus j) (hq : Sum.inl d ≠ C.lEndMinus j) :
    (Sum.inl d ≠ C.lEndPlus j) ∧ (Sum.inl d ≠ C.capP j) ∧
      (Sum.inl d ≠ C.lEndMinus j) ∧ (Sum.inl d ≠ C.capM j) :=
  ⟨hp, by simp [capP], hq, by simp [capM]⟩

/-- Over an index list, the merge product fixes `inl d` whenever `d` is not a
bank-end (i.e. `inl d ≠ ℓ_j^±` for every `j` in the list). -/
lemma mergeMap_apply_inl_clean (C : SimplePrimalCycle M) (d : D)
    (hp : ∀ j, Sum.inl d ≠ C.lEndPlus j) (hq : ∀ j, Sum.inl d ≠ C.lEndMinus j)
    (L : List (Fin C.len)) :
    ((L.flatMap (fun i => [(C.lEndPlus i, C.capP i), (C.lEndMinus i, C.capM i)])).map
      (fun w => Equiv.swap w.1 w.2)).prod (Sum.inl d) = Sum.inl d := by
  apply CutCapCount.listSwap_prod_fix
  intro w hw
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hw
  obtain ⟨j, _, hwj⟩ := hw
  rcases hwj with rfl | rfl
  · exact ⟨hp j, by simp [capP]⟩
  · exact ⟨hq j, by simp [capM]⟩

/-- Merge product over a `Nodup` list: `capP i ↦ ℓ_i^+` when `i` is present. -/
lemma mergeMap_apply_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    ∀ L : List (Fin C.len), L.Nodup →
      ((L.flatMap (fun j => [(C.lEndPlus j, C.capP j), (C.lEndMinus j, C.capM j)])).map
        (fun w => Equiv.swap w.1 w.2)).prod (C.capP i)
        = if i ∈ L then C.lEndPlus i else C.capP i := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons j L' ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      obtain ⟨hj, hL'⟩ := hnd
      rw [List.flatMap_cons, List.map_append, List.prod_append, Equiv.Perm.mul_apply, ih hL']
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Equiv.Perm.mul_apply]
      by_cases hij : i = j
      · subst hij
        have hni : i ∉ L' := hj
        simp only [hni, if_false, List.mem_cons, true_or, if_true]
        -- inner swap(ℓ⁻,c⁻) fixes capP i; outer swap(ℓ⁺,c⁺) sends capP i ↦ ℓ⁺
        rw [Equiv.swap_apply_of_ne_of_ne (by simp [capP, lEndMinus]) (C.capP_ne_capM i i),
          Equiv.swap_apply_right]
      · by_cases hmem : i ∈ L'
        · simp only [hmem, if_true, List.mem_cons, or_true]
          -- both swaps fix ℓ_i^+
          rw [Equiv.swap_apply_of_ne_of_ne (C.lEndPlus_ne_lEndMinus i j) (C.lEndPlus_ne_capM i j),
            Equiv.swap_apply_of_ne_of_ne (fun h => hij (C.lEndPlus_inj h)) (C.lEndPlus_ne_capP i j)]
        · simp only [hmem, if_false, List.mem_cons, hij, false_or, if_false]
          -- both swaps fix capP i
          rw [Equiv.swap_apply_of_ne_of_ne (by simp [capP, lEndMinus]) (C.capP_ne_capM i j),
            Equiv.swap_apply_of_ne_of_ne (fun h => (C.lEndPlus_ne_capP j i h.symm))
              (fun h => hij (C.capP_inj h))]

/-- Merge product over a `Nodup` list: `capM i ↦ ℓ_i^-` when `i` is present. -/
lemma mergeMap_apply_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    ∀ L : List (Fin C.len), L.Nodup →
      ((L.flatMap (fun j => [(C.lEndPlus j, C.capP j), (C.lEndMinus j, C.capM j)])).map
        (fun w => Equiv.swap w.1 w.2)).prod (C.capM i)
        = if i ∈ L then C.lEndMinus i else C.capM i := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons j L' ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      obtain ⟨hj, hL'⟩ := hnd
      rw [List.flatMap_cons, List.map_append, List.prod_append, Equiv.Perm.mul_apply, ih hL']
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Equiv.Perm.mul_apply]
      by_cases hij : i = j
      · subst hij
        have hni : i ∉ L' := hj
        simp only [hni, if_false, List.mem_cons, true_or, if_true]
        -- inner swap(ℓ⁻,c⁻) sends capM i ↦ ℓ⁻; outer fixes ℓ⁻
        rw [Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne (C.lEndPlus_ne_lEndMinus i i).symm
            (fun h => (C.lEndMinus_ne_capP i i) h)]
      · by_cases hmem : i ∈ L'
        · simp only [hmem, if_true, List.mem_cons, or_true]
          -- both swaps fix ℓ_i^-
          rw [Equiv.swap_apply_of_ne_of_ne (fun h => hij (C.lEndMinus_inj h)) (C.lEndMinus_ne_capM i j),
            Equiv.swap_apply_of_ne_of_ne (C.lEndPlus_ne_lEndMinus j i).symm (C.lEndMinus_ne_capP i j)]
        · simp only [hmem, if_false, List.mem_cons, hij, false_or, if_false]
          -- both swaps fix capM i
          rw [Equiv.swap_apply_of_ne_of_ne (fun h => (C.lEndMinus_ne_capM j i h.symm))
              (fun h => hij (C.capM_inj h)),
            Equiv.swap_apply_of_ne_of_ne (by simp [capM, lEndPlus]) (fun h => (C.capP_ne_capM j i h.symm))]

/-- Merge product over a `Nodup` list: `ℓ_i^+ ↦ capP i` when `i` is present. -/
lemma mergeMap_apply_lEndPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    ∀ L : List (Fin C.len), L.Nodup →
      ((L.flatMap (fun j => [(C.lEndPlus j, C.capP j), (C.lEndMinus j, C.capM j)])).map
        (fun w => Equiv.swap w.1 w.2)).prod (C.lEndPlus i)
        = if i ∈ L then C.capP i else C.lEndPlus i := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons j L' ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      obtain ⟨hj, hL'⟩ := hnd
      rw [List.flatMap_cons, List.map_append, List.prod_append, Equiv.Perm.mul_apply, ih hL']
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Equiv.Perm.mul_apply]
      by_cases hij : i = j
      · subst hij
        have hni : i ∉ L' := hj
        simp only [hni, if_false, List.mem_cons, true_or, if_true]
        -- inner fixes ℓ⁺; outer swap(ℓ⁺,c⁺) sends ℓ⁺ ↦ capP i
        rw [Equiv.swap_apply_of_ne_of_ne (C.lEndPlus_ne_lEndMinus i i) (C.lEndPlus_ne_capM i i),
          Equiv.swap_apply_left]
      · by_cases hmem : i ∈ L'
        · simp only [hmem, if_true, List.mem_cons, or_true]
          -- both swaps fix capP i
          rw [Equiv.swap_apply_of_ne_of_ne (by simp [capP, lEndMinus]) (C.capP_ne_capM i j),
            Equiv.swap_apply_of_ne_of_ne (fun h => (C.lEndPlus_ne_capP j i h.symm))
              (fun h => hij (C.capP_inj h))]
        · simp only [hmem, if_false, List.mem_cons, hij, false_or, if_false]
          -- both swaps fix ℓ_i^+
          rw [Equiv.swap_apply_of_ne_of_ne (C.lEndPlus_ne_lEndMinus i j) (C.lEndPlus_ne_capM i j),
            Equiv.swap_apply_of_ne_of_ne (fun h => hij (C.lEndPlus_inj h)) (C.lEndPlus_ne_capP i j)]

/-- Merge product over a `Nodup` list: `ℓ_i^- ↦ capM i` when `i` is present. -/
lemma mergeMap_apply_lEndMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    ∀ L : List (Fin C.len), L.Nodup →
      ((L.flatMap (fun j => [(C.lEndPlus j, C.capP j), (C.lEndMinus j, C.capM j)])).map
        (fun w => Equiv.swap w.1 w.2)).prod (C.lEndMinus i)
        = if i ∈ L then C.capM i else C.lEndMinus i := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons j L' ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      obtain ⟨hj, hL'⟩ := hnd
      rw [List.flatMap_cons, List.map_append, List.prod_append, Equiv.Perm.mul_apply, ih hL']
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Equiv.Perm.mul_apply]
      by_cases hij : i = j
      · subst hij
        have hni : i ∉ L' := hj
        simp only [hni, if_false, List.mem_cons, true_or, if_true]
        -- inner swap(ℓ⁻,c⁻) sends ℓ⁻ ↦ capM i; outer fixes capM i
        rw [Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne (fun h => (C.lEndPlus_ne_capM i i) h.symm)
            (C.capP_ne_capM i i).symm]
      · by_cases hmem : i ∈ L'
        · simp only [hmem, if_true, List.mem_cons, or_true]
          -- both swaps fix capM i
          rw [Equiv.swap_apply_of_ne_of_ne (fun h => (C.lEndMinus_ne_capM j i h.symm))
              (fun h => hij (C.capM_inj h)),
            Equiv.swap_apply_of_ne_of_ne (by simp [capM, lEndPlus]) (fun h => (C.capP_ne_capM j i h.symm))]
        · simp only [hmem, if_false, List.mem_cons, hij, false_or, if_false]
          -- both swaps fix ℓ_i^-
          rw [Equiv.swap_apply_of_ne_of_ne (fun h => hij (C.lEndMinus_inj h)) (C.lEndMinus_ne_capM i j),
            Equiv.swap_apply_of_ne_of_ne (C.lEndPlus_ne_lEndMinus j i).symm (C.lEndMinus_ne_capP i j)]

/-! ### `mergeProd` closed forms -/

@[simp] lemma mergeProd_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.mergeProd (C.capP i) = C.lEndPlus i := by
  rw [mergeProd, mergeList, C.mergeMap_apply_capP i _ (List.nodup_finRange _)]
  simp [List.mem_finRange]

@[simp] lemma mergeProd_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.mergeProd (C.capM i) = C.lEndMinus i := by
  rw [mergeProd, mergeList, C.mergeMap_apply_capM i _ (List.nodup_finRange _)]
  simp [List.mem_finRange]

@[simp] lemma mergeProd_lEndPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.mergeProd (C.lEndPlus i) = C.capP i := by
  rw [mergeProd, mergeList, C.mergeMap_apply_lEndPlus i _ (List.nodup_finRange _)]
  simp [List.mem_finRange]

@[simp] lemma mergeProd_lEndMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.mergeProd (C.lEndMinus i) = C.capM i := by
  rw [mergeProd, mergeList, C.mergeMap_apply_lEndMinus i _ (List.nodup_finRange _)]
  simp [List.mem_finRange]

@[simp] lemma splitProd_lEndPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.splitProd (C.lEndPlus i) = C.lEndPlus i := by rw [lEndPlus, splitProd_inl]
@[simp] lemma splitProd_lEndMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.splitProd (C.lEndMinus i) = C.lEndMinus i := by rw [lEndMinus, splitProd_inl]

/-- `mergeProd` fixes `inl d` when `d` is not a bank-end. -/
lemma mergeProd_inl_clean (C : SimplePrimalCycle M) {d : D}
    (hp : ∀ i, Sum.inl d ≠ C.lEndPlus i) (hq : ∀ i, Sum.inl d ≠ C.lEndMinus i) :
    C.mergeProd (Sum.inl d) = Sum.inl d := by
  rw [mergeProd, mergeList]; exact C.mergeMap_apply_inl_clean d hp hq _

/-! ## The swap decomposition of `cutSigmaPerm`

`cutSigmaPerm = sigmaLift * mergeProd * splitProd`.  Reading right-to-left: the
split swaps fire first, then the merge swaps splice the caps into the orbit, and
finally `σ ⊕ 1` rotates.  Verified on each cut-dart class. -/

/-- `inl d = ℓ_i^+` iff `σ d = p_i`. -/
lemma inl_eq_lEndPlus_iff (C : SimplePrimalCycle M) (d : D) (i : Fin C.len) :
    Sum.inl d = C.lEndPlus i ↔ M.σ d = C.pDart i := by
  rw [lEndPlus, Sum.inl.injEq]
  constructor
  · intro h; rw [h, M.σ.apply_symm_apply]
  · intro h; rw [← h, M.σ.symm_apply_apply]

/-- `inl d = ℓ_i^-` iff `σ d = q_i`. -/
lemma inl_eq_lEndMinus_iff (C : SimplePrimalCycle M) (d : D) (i : Fin C.len) :
    Sum.inl d = C.lEndMinus i ↔ M.σ d = C.qDart i := by
  rw [lEndMinus, Sum.inl.injEq]
  constructor
  · intro h; rw [h, M.σ.apply_symm_apply]
  · intro h; rw [← h, M.σ.symm_apply_apply]

/-- **The transposition decomposition of the cut-and-cap rotation.** -/
theorem cutSigmaPerm_eq_sigmaLift_mul (C : SimplePrimalCycle M) :
    C.cutSigmaPerm = C.sigmaLift * C.mergeProd * C.splitProd := by
  ext x
  rw [cutSigmaPerm_apply, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul,
    Function.comp_apply, Function.comp_apply]
  rcases x with d | (i | i)
  · -- inl d : classify by divertKind
    rcases hd : C.divertKind d with (i | i) | u
    · -- σ d = p_i, so inl d = ℓ_i^+
      have hσ : M.σ d = C.pDart i := C.divertKind_eq_plus hd
      have hℓ : Sum.inl d = C.lEndPlus i := (C.inl_eq_lEndPlus_iff d i).2 hσ
      rw [C.cutSigma_inl_plus hd, hℓ, splitProd_lEndPlus, mergeProd_lEndPlus, capP, sigmaLift_inr]
    · have hσ : M.σ d = C.qDart i := C.divertKind_eq_minus hd
      have hℓ : Sum.inl d = C.lEndMinus i := (C.inl_eq_lEndMinus_iff d i).2 hσ
      rw [C.cutSigma_inl_minus hd, hℓ, splitProd_lEndMinus, mergeProd_lEndMinus, capM, sigmaLift_inr]
    · obtain ⟨hp, hq⟩ := C.divertKind_eq_none hd
      have hcp : ∀ i, Sum.inl d ≠ C.lEndPlus i := fun i hi =>
        hp i ((C.inl_eq_lEndPlus_iff d i).1 hi)
      have hcq : ∀ i, Sum.inl d ≠ C.lEndMinus i := fun i hi =>
        hq i ((C.inl_eq_lEndMinus_iff d i).1 hi)
      rw [C.cutSigma_inl_none hd, splitProd_inl, C.mergeProd_inl_clean hcp hcq, sigmaLift_inl]
  · -- capP i ↦ q_i
    show _ = C.sigmaLift (C.mergeProd (C.splitProd (C.capP i)))
    rw [cutSigma_capPlus, splitProd_capP, mergeProd_capM, lEndMinus, sigmaLift_inl,
      M.σ.apply_symm_apply]
  · -- capM i ↦ p_i
    show _ = C.sigmaLift (C.mergeProd (C.splitProd (C.capM i)))
    rw [cutSigma_capMinus, splitProd_capM, mergeProd_capP, lEndPlus, sigmaLift_inl,
      M.σ.apply_symm_apply]

/-! ## The merged permutation `Q = sigmaLift * mergeProd`

After the merge swaps each cap is spliced into the `σ`-orbit at `v_i`.  We record
the action of `Q` at the points relevant to the cycle-count side conditions, then
prove the projection semiconjugacy `proj (Q x) ∈ {σ (proj x), proj x}`. -/

/-- The merged permutation `Q = σ⊕1` times the merge swaps. -/
noncomputable def merged (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  C.sigmaLift * C.mergeProd

lemma merged_apply (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.merged x = C.sigmaLift (C.mergeProd x) := rfl

@[simp] lemma merged_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.merged (C.capP i) = Sum.inl (C.pDart i) := by
  rw [merged_apply, mergeProd_capP, lEndPlus, sigmaLift_inl, M.σ.apply_symm_apply]

@[simp] lemma merged_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.merged (C.capM i) = Sum.inl (C.qDart i) := by
  rw [merged_apply, mergeProd_capM, lEndMinus, sigmaLift_inl, M.σ.apply_symm_apply]

/-- On a clean dart (not a bank-end) `Q` acts as `σ`. -/
lemma merged_inl_clean (C : SimplePrimalCycle M) {d : D}
    (hp : ∀ i, M.σ d ≠ C.pDart i) (hq : ∀ i, M.σ d ≠ C.qDart i) :
    C.merged (Sum.inl d) = Sum.inl (M.σ d) := by
  have hcp : ∀ i, Sum.inl d ≠ C.lEndPlus i := fun i hi =>
    hp i ((C.inl_eq_lEndPlus_iff d i).1 hi)
  have hcq : ∀ i, Sum.inl d ≠ C.lEndMinus i := fun i hi =>
    hq i ((C.inl_eq_lEndMinus_iff d i).1 hi)
  rw [merged_apply, C.mergeProd_inl_clean hcp hcq, sigmaLift_inl]

/-- On the `+`-bank-end `ℓ_i^+` the merged map diverts to the `+`-cap. -/
lemma merged_lEndPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.merged (C.lEndPlus i) = C.capP i := by
  rw [merged_apply, mergeProd_lEndPlus, capP, sigmaLift_inr]

/-- On the `−`-bank-end `ℓ_i^-` the merged map diverts to the `−`-cap. -/
lemma merged_lEndMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.merged (C.lEndMinus i) = C.capM i := by
  rw [merged_apply, mergeProd_lEndMinus, capM, sigmaLift_inr]

/-- The merged map applied to `inl d` always lands in the `inl` summand, equal to
`inl (σ d)` away from bank-ends and to a cap at a bank-end (which equals
`inl (σ d)` after one more `Q`-step).  This is the unified statement used by the
projection. -/
lemma merged_inl (C : SimplePrimalCycle M) (d : D) :
    C.merged (Sum.inl d) = Sum.inl (M.σ d) ∨
      (∃ i, M.σ d = C.pDart i ∧ C.merged (Sum.inl d) = C.capP i) ∨
      (∃ i, M.σ d = C.qDart i ∧ C.merged (Sum.inl d) = C.capM i) := by
  by_cases hp : ∃ i, M.σ d = C.pDart i
  · obtain ⟨i, hi⟩ := hp
    right; left
    refine ⟨i, hi, ?_⟩
    rw [show Sum.inl d = C.lEndPlus i from (C.inl_eq_lEndPlus_iff d i).2 hi, merged_lEndPlus]
  · by_cases hq : ∃ i, M.σ d = C.qDart i
    · obtain ⟨i, hi⟩ := hq
      right; right
      refine ⟨i, hi, ?_⟩
      rw [show Sum.inl d = C.lEndMinus i from (C.inl_eq_lEndMinus_iff d i).2 hi, merged_lEndMinus]
    · left
      exact C.merged_inl_clean (fun i hi => hp ⟨i, hi⟩) (fun i hi => hq ⟨i, hi⟩)

/-! ## The projection semiconjugacy

`proj` sends each cut-dart back to an underlying dart of `D`: `inl d ↦ d`, and each
cap to its bank-start dart (`c_i^+ ↦ p_i`, `c_i^- ↦ q_i`).  Under `Q`, the
projection either advances by one `σ`-step (on `inl`-darts) or stalls (on caps).
This single fact yields all the `SameCycle` reductions to `σ`. -/

/-- The projection of a cut-dart back to `D`. -/
noncomputable def proj (C : SimplePrimalCycle M) : C.CutDart → D :=
  fun x => match x with
  | Sum.inl d => d
  | Sum.inr (Sum.inl i) => C.pDart i
  | Sum.inr (Sum.inr i) => C.qDart i

@[simp] lemma proj_inl (C : SimplePrimalCycle M) (d : D) : C.proj (Sum.inl d) = d := rfl
@[simp] lemma proj_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.proj (C.capP i) = C.pDart i := rfl
@[simp] lemma proj_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.proj (C.capM i) = C.qDart i := rfl

/-- **The per-step projection fact.**  `proj (Q x)` is either `σ (proj x)` (the
`inl`-dart case, including the divert-to-cap step) or `proj x` (the cap case). -/
lemma proj_merged (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.proj (C.merged x) = M.σ (C.proj x) ∨ C.proj (C.merged x) = C.proj x := by
  rcases x with d | (i | i)
  · -- inl d : always the σ branch
    left
    rcases C.merged_inl d with h | ⟨i, hi, h⟩ | ⟨i, hi, h⟩
    · rw [h]; rfl
    · rw [h, proj_capP, proj_inl, hi]
    · rw [h, proj_capM, proj_inl, hi]
  · -- capP i : stall branch (Q (capP i) = inl (p_i), proj = p_i = proj (capP i))
    right
    rw [show (Sum.inr (Sum.inl i) : C.CutDart) = C.capP i from rfl, merged_capP, proj_inl, proj_capP]
  · -- capM i : stall branch
    right
    rw [show (Sum.inr (Sum.inr i) : C.CutDart) = C.capM i from rfl, merged_capM, proj_inl, proj_capM]

/-- Iterating the per-step fact: `proj (Q^n x) = σ^m (proj x)` for some `m`. -/
lemma proj_merged_pow (C : SimplePrimalCycle M) (x : C.CutDart) :
    ∀ n : ℕ, ∃ m : ℕ, C.proj ((C.merged ^ n) x) = (M.σ ^ m) (C.proj x) := by
  intro n
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
      obtain ⟨m, hm⟩ := ih
      rcases C.proj_merged ((C.merged ^ n) x) with h | h
      · refine ⟨m + 1, ?_⟩
        rw [pow_succ', Equiv.Perm.mul_apply, h, hm, pow_succ', Equiv.Perm.mul_apply]
      · refine ⟨m, ?_⟩
        rw [pow_succ', Equiv.Perm.mul_apply, h, hm]

/-! ## `SameCycle` reductions to `σ` -/

/-- **Backward reduction.**  Co-cyclic `inl`-darts under `Q` are co-cyclic under
`σ`. -/
lemma sameCycle_merged_inl_imp (C : SimplePrimalCycle M) {a b : D}
    (h : C.merged.SameCycle (Sum.inl a) (Sum.inl b)) : M.σ.SameCycle a b := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  obtain ⟨m, hm⟩ := C.proj_merged_pow (Sum.inl a) n
  refine ⟨(m : ℤ), ?_⟩
  rw [zpow_natCast]
  have : C.proj ((C.merged ^ n) (Sum.inl a)) = b := by rw [hn]; rfl
  rw [hm, proj_inl] at this
  exact this

/-- One `σ`-step lifts to a `Q`-relation on `inl`-darts. -/
lemma sameCycle_merged_inl_sigma_step (C : SimplePrimalCycle M) (a : D) :
    C.merged.SameCycle (Sum.inl a) (Sum.inl (M.σ a)) := by
  by_cases hp : ∃ i, M.σ a = C.pDart i
  · obtain ⟨i, hi⟩ := hp
    -- inl a = ℓ_i^+, Q(ℓ_i^+) = c_i^+, Q(c_i^+) = inl(p_i) = inl(σ a)
    have hℓ : Sum.inl a = C.lEndPlus i := (C.inl_eq_lEndPlus_iff a i).2 hi
    refine ⟨(2 : ℤ), ?_⟩
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, Equiv.Perm.mul_apply,
      hℓ, merged_lEndPlus, merged_capP, hi]
  · by_cases hq : ∃ i, M.σ a = C.qDart i
    · obtain ⟨i, hi⟩ := hq
      have hℓ : Sum.inl a = C.lEndMinus i := (C.inl_eq_lEndMinus_iff a i).2 hi
      refine ⟨(2 : ℤ), ?_⟩
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, Equiv.Perm.mul_apply,
        hℓ, merged_lEndMinus, merged_capM, hi]
    · refine ⟨(1 : ℤ), ?_⟩
      rw [zpow_one, C.merged_inl_clean (fun i hi => hp ⟨i, hi⟩) (fun i hi => hq ⟨i, hi⟩)]

/-- **Forward reduction.**  Co-cyclic darts under `σ` lift to co-cyclic
`inl`-darts under `Q`. -/
lemma sameCycle_merged_inl_pow (C : SimplePrimalCycle M) (a : D) :
    ∀ n : ℕ, C.merged.SameCycle (Sum.inl a) (Sum.inl ((M.σ ^ n) a)) := by
  intro n
  induction n with
  | zero => simp only [pow_zero, Equiv.Perm.coe_one, id_eq]; exact Equiv.Perm.SameCycle.refl _ _
  | succ n ih =>
      have hstep := C.sameCycle_merged_inl_sigma_step ((M.σ ^ n) a)
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.trans hstep

lemma sameCycle_merged_inl_of_sigma (C : SimplePrimalCycle M) {a b : D}
    (h : M.σ.SameCycle a b) : C.merged.SameCycle (Sum.inl a) (Sum.inl b) := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have := C.sameCycle_merged_inl_pow a n
  rwa [hn] at this

/-! ### `SameCycle` facts about the caps under `Q` -/

/-- Each cap is `Q`-co-cyclic with its bank-start `inl`-dart. -/
lemma sameCycle_merged_capP_inl (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.merged.SameCycle (C.capP i) (Sum.inl (C.pDart i)) :=
  ⟨(1 : ℤ), by rw [zpow_one, merged_capP]⟩

lemma sameCycle_merged_capM_inl (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.merged.SameCycle (C.capM i) (Sum.inl (C.qDart i)) :=
  ⟨(1 : ℤ), by rw [zpow_one, merged_capM]⟩

/-- The two caps at `v_i` are `Q`-co-cyclic (reduces to `σ.SameCycle p_i q_i`). -/
lemma sameCycle_merged_capP_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.merged.SameCycle (C.capP i) (C.capM i) := by
  refine (C.sameCycle_merged_capP_inl i).trans ?_
  refine (C.sameCycle_merged_inl_of_sigma (C.sameCycle_pDart_qDart i)).trans ?_
  exact (C.sameCycle_merged_capM_inl i).symm

/-- Distinct-index caps are in different `Q`-cycles (reduces to distinct
`σ`-orbits at distinct cycle vertices). -/
lemma not_sameCycle_merged_capP_capP (C : SimplePrimalCycle M) {i j : Fin C.len}
    (hij : i ≠ j) : ¬ C.merged.SameCycle (C.capP i) (C.capP j) := by
  intro h
  apply C.not_sameCycle_pDart_of_ne hij
  apply C.sameCycle_merged_inl_imp
  exact ((C.sameCycle_merged_capP_inl i).symm.trans h).trans (C.sameCycle_merged_capP_inl j)

lemma not_sameCycle_merged_capP_capM (C : SimplePrimalCycle M) {i j : Fin C.len}
    (hij : i ≠ j) : ¬ C.merged.SameCycle (C.capP i) (C.capM j) := by
  intro h
  -- would give σ.SameCycle p_i q_j, but tail p_i = v_i ≠ v_j = tail q_j
  have hσ : M.σ.SameCycle (C.pDart i) (C.qDart j) := by
    apply C.sameCycle_merged_inl_imp
    exact ((C.sameCycle_merged_capP_inl i).symm.trans h).trans (C.sameCycle_merged_capM_inl j)
  apply hij
  have : M.tail (C.pDart i) = M.tail (C.qDart j) := Quotient.sound hσ
  rw [C.tail_pDart_eq_tail_qDart i, C.tail_qDart i, C.tail_qDart j] at this
  exact C.tail_inj this

/-! ## The merge phase: `numCycles (sigmaLift * mergeProd) = V` -/

/-- The list lengths. -/
lemma mergeList_length (C : SimplePrimalCycle M) : C.mergeList.length = 2 * C.len := by
  rw [mergeList, List.length_flatMap]
  simp only [List.length_cons, List.length_nil, List.map_const', List.sum_replicate,
    List.length_finRange, smul_eq_mul]
  ring

lemma splitList_length (C : SimplePrimalCycle M) : C.splitList.length = C.len := by
  rw [splitList, List.length_map, List.length_finRange]

/-- Every entry of `mergeList` is an `(ℓ, cap)` pair: first component `inl`, second
component a cap, and the two distinct. -/
lemma mergeList_mem (C : SimplePrimalCycle M) {w : C.CutDart × C.CutDart}
    (hw : w ∈ C.mergeList) :
    (∃ i, w = (C.lEndPlus i, C.capP i)) ∨ (∃ i, w = (C.lEndMinus i, C.capM i)) := by
  rw [mergeList, List.mem_flatMap] at hw
  obtain ⟨i, _, hwi⟩ := hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwi
  rcases hwi with rfl | rfl
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

/-- The caps as a flat list. -/
lemma mergeList_map_snd (C : SimplePrimalCycle M) :
    C.mergeList.map Prod.snd
      = (List.finRange C.len).flatMap (fun i => [C.capP i, C.capM i]) := by
  rw [mergeList, List.map_flatMap]
  rfl

/-- The second components of `mergeList` (the caps) are pairwise distinct. -/
lemma mergeList_snd_nodup (C : SimplePrimalCycle M) :
    (C.mergeList.map Prod.snd).Nodup := by
  rw [mergeList_map_snd]
  apply List.nodup_flatMap.2
  refine ⟨?_, ?_⟩
  · intro i _
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      and_true]
    exact ⟨C.capP_ne_capM i i, not_false⟩
  · apply (List.nodup_finRange C.len).pairwise_of_forall_ne
    intro i _ j _ hij
    rw [Function.onFun, List.disjoint_left]
    intro x hx hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false, capP, capM] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with h | h <;> exact hij (by simp_all)

/-- The first component of any `mergeList` entry is an `inl` dart. -/
lemma mergeList_fst_inl (C : SimplePrimalCycle M) {w : C.CutDart × C.CutDart}
    (hw : w ∈ C.mergeList) : ∃ d : D, w.1 = Sum.inl d := by
  rcases C.mergeList_mem hw with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- The second component of any `mergeList` entry is a cap (an `inr` dart). -/
lemma mergeList_snd_inr (C : SimplePrimalCycle M) {w : C.CutDart × C.CutDart}
    (hw : w ∈ C.mergeList) : ∃ c, w.2 = Sum.inr c := by
  rcases C.mergeList_mem hw with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- Each `mergeList` pair has distinct first and second components. -/
lemma mergeList_fst_ne_snd (C : SimplePrimalCycle M) {w : C.CutDart × C.CutDart}
    (hw : w ∈ C.mergeList) : w.1 ≠ w.2 := by
  obtain ⟨d, hd⟩ := C.mergeList_fst_inl hw
  obtain ⟨c, hc⟩ := C.mergeList_snd_inr hw
  rw [hd, hc]; exact Sum.inl_ne_inr

/-- The cap at position `j` does not occur in the prefix `mergeList.take j`. -/
lemma mergeList_get_snd_not_mem_take (C : SimplePrimalCycle M) (j : Fin C.mergeList.length)
    {w : C.CutDart × C.CutDart} (hw : w ∈ C.mergeList.take j) :
    (C.mergeList.get j).2 ≠ w.1 ∧ (C.mergeList.get j).2 ≠ w.2 := by
  have hwmem : w ∈ C.mergeList := List.mem_of_mem_take hw
  -- the cap (get j).2 is an `inr`; w.1 is `inl`
  obtain ⟨c, hc⟩ := C.mergeList_snd_inr (List.get_mem C.mergeList j)
  obtain ⟨d, hd⟩ := C.mergeList_fst_inl hwmem
  refine ⟨by rw [hc, hd]; exact Sum.inr_ne_inl, ?_⟩
  -- distinctness of the second components via the Nodup of `mergeList.map .2`
  intro hcontra
  have hnd := C.mergeList_snd_nodup
  obtain ⟨k, hk, hwk⟩ := List.mem_iff_getElem.1 hw
  have hkj : k < (j : ℕ) := lt_of_lt_of_le hk (List.length_take_le _ _)
  have hklt : k < C.mergeList.length := hkj.trans j.isLt
  rw [List.getElem_take] at hwk
  -- (map .2)[j] = (map .2)[k] forces j = k, but k < j
  have hmapj : (C.mergeList.map Prod.snd)[(j : ℕ)]'(by simp [j.isLt]) = (C.mergeList.get j).2 := by
    simp [List.getElem_map]
  have hmapk : (C.mergeList.map Prod.snd)[k]'(by simp [hklt]) = w.2 := by
    simp [List.getElem_map, hwk]
  have hjk : (j : ℕ) = k := by
    apply (hnd.getElem_inj_iff).1
    rw [hmapj, hmapk, hcontra]
  omega

/-- Any `splitList` entry is a cap pair. -/
lemma splitList_mem (C : SimplePrimalCycle M) {w : C.CutDart × C.CutDart}
    (hw : w ∈ C.splitList) : ∃ idx, w = (C.capP idx, C.capM idx) := by
  rw [splitList, List.mem_map] at hw
  obtain ⟨i, _, rfl⟩ := hw; exact ⟨i, rfl⟩

/-- The index carried by `splitList.get j`. -/
lemma splitList_get (C : SimplePrimalCycle M) (j : Fin C.splitList.length) :
    ∃ idx : Fin C.len, C.splitList.get j = (C.capP idx, C.capM idx) :=
  C.splitList_mem (List.get_mem C.splitList j)

/-- `splitList` is `Nodup`. -/
lemma splitList_nodup (C : SimplePrimalCycle M) : C.splitList.Nodup := by
  rw [splitList]
  apply (List.nodup_finRange C.len).map
  intro i j h
  exact C.capP_inj (Prod.ext_iff.1 h).1

/-- The index at position `j` of `splitList` differs from every prefix index. -/
lemma splitList_take_index_ne (C : SimplePrimalCycle M) (j : Fin C.splitList.length)
    {idx idx' : Fin C.len} (hidx : C.splitList.get j = (C.capP idx, C.capM idx))
    (hw : (C.capP idx', C.capM idx') ∈ C.splitList.take j) : idx' ≠ idx := by
  obtain ⟨k, hk, hwk⟩ := List.mem_iff_getElem.1 hw
  have hkj : k < (j : ℕ) := lt_of_lt_of_le hk (List.length_take_le _ _)
  have hklt : k < C.splitList.length := hkj.trans j.isLt
  rw [List.getElem_take] at hwk
  intro hcontra; subst hcontra
  -- splitList[k] = (capP idx, capM idx) = splitList[j], so k = j by Nodup
  have hkj_eq : k = (j : ℕ) := by
    have := (C.splitList_nodup.getElem_inj_iff (i := k) (hi := hklt) (j := (j : ℕ))
      (hj := j.isLt)).1
    apply this
    rw [hwk]
    exact hidx.symm
  omega

/-- **Merge phase.**  `numCycles (sigmaLift * mergeProd) + 2k = numCycles sigmaLift`. -/
lemma numCycles_merged_add (C : SimplePrimalCycle M) :
    _root_.numCycles C.merged + C.mergeList.length = _root_.numCycles C.sigmaLift := by
  rw [merged, mergeProd]
  apply CutCapCount.numCycles_mul_listSwap_merges
  intro j
  have hget : C.mergeList.get j ∈ C.mergeList := List.get_mem C.mergeList j
  refine ⟨C.mergeList_fst_ne_snd hget, ?_⟩
  -- the cap (get j).2 is fixed by `sigmaLift * (prefix)` ⟹ not co-cyclic with (get j).1
  apply CutCapCount.not_sameCycle_of_fixed
  · -- fixed: prefix product fixes the cap, sigmaLift fixes the cap
    rw [Equiv.Perm.mul_apply]
    obtain ⟨c, hc⟩ := C.mergeList_snd_inr hget
    rw [CutCapCount.listSwap_prod_apply_of_notMem _ _
      (fun w hw => C.mergeList_get_snd_not_mem_take j hw), hc, sigmaLift_inr]
  · exact C.mergeList_fst_ne_snd hget

/-- **Split phase.**  `numCycles (merged * splitProd) = numCycles merged + k`. -/
lemma numCycles_split (C : SimplePrimalCycle M) :
    _root_.numCycles (C.merged * C.splitProd)
      = _root_.numCycles C.merged + C.splitList.length := by
  rw [splitProd]
  apply CutCapCount.numCycles_mul_listSwap_splits
  intro j
  obtain ⟨idx, hidx⟩ := C.splitList_get j
  rw [hidx]
  refine ⟨C.capP_ne_capM idx idx, ?_⟩
  -- transport `merged.SameCycle (capP idx) (capM idx)` across the prefix split swaps
  apply CutCapCount.sameCycle_mul_of_orbit_fixed
  · intro y hy
    -- the prefix product fixes y, since y's `merged`-class avoids all prefix caps
    apply CutCapCount.listSwap_prod_apply_of_notMem
    intro w hw
    obtain ⟨idx', hw'⟩ := C.splitList_mem (List.mem_of_mem_take hw)
    subst hw'
    have hne : idx' ≠ idx := C.splitList_take_index_ne j hidx hw
    -- y ≠ capP idx' and y ≠ capM idx', else y co-cyclic with capP idx contradicts distinct orbits
    dsimp only
    refine ⟨fun hyc => ?_, fun hyc => ?_⟩
    · exact C.not_sameCycle_merged_capP_capP (Ne.symm hne) (hyc ▸ hy)
    · exact C.not_sameCycle_merged_capP_capM (Ne.symm hne) (hyc ▸ hy)
  · exact C.sameCycle_merged_capP_capM idx

/-! ## The vertex count `V' = V + k` -/

/-- `numCycles merged = V` (the merge swaps merge each of the `2k` caps into the
`σ`-orbit at its vertex). -/
lemma numCycles_merged (C : SimplePrimalCycle M) :
    _root_.numCycles C.merged = M.V := by
  have h := C.numCycles_merged_add
  rw [numCycles_sigmaLift, mergeList_length] at h
  omega

/-- **The cut-and-cap rotation has `V + k` cycles.** -/
theorem numCycles_cutSigmaPerm (C : SimplePrimalCycle M) :
    _root_.numCycles C.cutSigmaPerm = M.V + C.len := by
  rw [cutSigmaPerm_eq_sigmaLift_mul, ← merged, numCycles_split, numCycles_merged,
    splitList_length]

/-- **The vertex count of the concrete cut-and-cap map: `V' = V + k`.**  This is the
`vertex_count` field of `CutSigmaCounts`. -/
theorem cutCapMap_V (C : SimplePrimalCycle M) :
    (C.cutCapMap).V = M.V + C.len := by
  rw [CombMap.V_eq_numCycles, cutCapMap_sigma, numCycles_cutSigmaPerm]

end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap
