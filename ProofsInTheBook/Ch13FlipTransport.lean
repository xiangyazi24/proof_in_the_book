import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.PlanarMapDelete
import ProofsInTheBook.SubmapPlanar
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13MarkedSphere
import ProofsInTheBook.Ch13MarkedReduction
import ProofsInTheBook.Ch13ActiveComponent

/-!
# Ch13 flip transport: strict `vertexFlip` on the active submap = skip-zeros count on `M`

This file discharges the `htrans` residual of
`Ch13ActiveComponent.marked_sphere_low_active_vertex_modular`: the flip-count transport between
the kept (active) submap and the original marked sphere.

The active submap's rotation is `Equiv.Perm.deleteSet M.σ Del` — `M.σ` with the deleted (zero-sign)
darts spliced out of each cycle.  Hence the `deleteSet`-orbit `toList` of a kept dart `d` is the
`M.σ`-orbit `toList` of `d` with the deleted (= zero) darts removed.  The strict flip count of the
kept signs around the active vertex (`vertexFlip` via the strict bridge
`Ch13MarkedReduction.vertexFlipCountSkipZeros_strict_eq_vertexFlip`) therefore counts exactly the
adjacent strict-sign flips among the surviving nonzero darts in cyclic order — which is precisely
`vertexFlipCountSkipZeros M es d` (the skip-zeros count of the full `M.σ`-orbit sign sequence).

## The core list identity

The mathematical heart is the **filtered-toList identity** (`deleteSet_toList_map_val`):

  `((deleteSet p S).toList x).map Subtype.val = (p.toList x.1).filter (· ∉ S)`,

i.e. the underlying darts of the `deleteSet`-orbit list of `x` are exactly the surviving (`∉ S`)
darts of the `p`-orbit list of `x.1`, **in the same cyclic order**.  It is proved by `getElem`
correspondence: the cumulative `firstOutside` offsets that index the `deleteSet` orbit are exactly
the increasing enumeration of the kept indices of the `p`-orbit.
-/

namespace ProofsInTheBook.Ch13FlipTransport

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13MarkedReduction
open ProofsInTheBook.Ch13ActiveComponent
open ProofsInTheBook.SubmapPlanar
open EdgeSign
open Equiv Equiv.Perm

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## The cumulative `firstOutside` offset sequence -/

open ProofsInTheBook -- for DeleteSet.firstOutside via Equiv.Perm namespace

/-- The underlying dart of the `n`-th iterate of `deleteSet p S` from `x` is a `p`-power of `x.1`,
recorded with its explicit exponent `gOffset`.  `gOffset p S x n` is the cumulative sum of the
`firstOutside` steps along the first `n` `deleteSet`-iterates. -/
noncomputable def gOffset (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S}) : ℕ → ℕ
  | 0 => 0
  | n + 1 => gOffset p S x n + Equiv.Perm.DeleteSet.firstOutside p S (((deleteSet p S) ^ n) x)

/-- The underlying dart of the `n`-th `deleteSet`-iterate of `x` is the `gOffset n`-th `p`-power
of `x.1`. -/
theorem deleteSet_pow_coe (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S}) (n : ℕ) :
    (((deleteSet p S) ^ n) x : D) = (p ^ gOffset p S x n) x.1 := by
  induction n with
  | zero => simp [gOffset]
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, gOffset]
      -- ((deleteSet p S) ((deleteSet p S)^n x)).1 = (p ^ firstOutside ...) ((deleteSet p S)^n x).1
      rw [Equiv.Perm.deleteSet_apply_coe, ih, ← Equiv.Perm.mul_apply, ← pow_add, Nat.add_comm]

/-- `gOffset` is strictly monotone in `n`: each `firstOutside` step is positive. -/
theorem gOffset_strictMono (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S}) :
    StrictMono (gOffset p S x) := by
  have hstep : ∀ n, gOffset p S x n < gOffset p S x (n + 1) := by
    intro n
    rw [gOffset]
    have := Equiv.Perm.DeleteSet.firstOutside_pos p S (((deleteSet p S) ^ n) x)
    omega
  exact strictMono_nat_of_lt_succ hstep

/-- Every value `gOffset n` lands on a kept dart (`∉ S`): it is the underlying value of the
`n`-th `deleteSet`-iterate, which lives in the subtype. -/
theorem gOffset_kept (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S}) (n : ℕ) :
    (p ^ gOffset p S x n) x.1 ∉ S := by
  rw [← deleteSet_pow_coe]
  exact (((deleteSet p S) ^ n) x).2

/-- The orbit length `L = (p.toList x).length` is a period of `x` under `p`. -/
theorem pow_length_toList_apply (p : Equiv.Perm D) (x : D) :
    (p ^ (p.toList x).length) x = x := by
  rw [Equiv.Perm.length_toList]
  have := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply p ((p.cycleOf x).support.card) x
  rw [Nat.mod_self, pow_zero, Equiv.Perm.coe_one, id_eq] at this
  exact this.symm

/-- **`firstOutside` wrap bound.**  If `y.1 = (p ^ g) x.1` with `g < L = (p.toList x.1).length`,
then the next surviving forward iterate of `y` is reached within `L - g` steps, because index `L`
returns to `x.1`, which survives (`x.1 ∉ S`).  Hence `firstOutside p S y ≤ L - g`. -/
theorem firstOutside_wrap_le (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S})
    (g : ℕ) (hg : g < (p.toList x.1).length) (y : {d : D // d ∉ S}) (hy : y.1 = (p ^ g) x.1) :
    Equiv.Perm.DeleteSet.firstOutside p S y ≤ (p.toList x.1).length - g := by
  set L := (p.toList x.1).length with hL
  have hpos : 0 < L - g := Nat.sub_pos_of_lt hg
  have hval : (p ^ (L - g)) y.1 = x.1 := by
    rw [hy, ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (le_of_lt hg),
      pow_length_toList_apply]
  refine Nat.find_le ?_
  exact ⟨hpos, by rw [hval]; exact x.2⟩

/-- **Nodup injectivity of iterates on the orbit list.**  If `a, b < L' = length of the
`deleteSet`-orbit list of `x` and the `a`-th and `b`-th iterates coincide, then `a = b`. -/
theorem deleteSet_pow_inj (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S})
    {a b : ℕ} (ha : a < ((deleteSet p S).toList x).length)
    (hb : b < ((deleteSet p S).toList x).length)
    (hab : ((deleteSet p S) ^ a) x = ((deleteSet p S) ^ b) x) : a = b := by
  have hnodup := Equiv.Perm.nodup_toList (deleteSet p S) x
  rw [List.nodup_iff_injective_getElem] at hnodup
  have hga : ((deleteSet p S).toList x)[a] = ((deleteSet p S) ^ a) x :=
    Equiv.Perm.getElem_toList _ _ _ _
  have hgb : ((deleteSet p S).toList x)[b] = ((deleteSet p S) ^ b) x :=
    Equiv.Perm.getElem_toList _ _ _ _
  have : (⟨a, ha⟩ : Fin _) = ⟨b, hb⟩ := by
    apply hnodup
    simp only [hga, hgb, hab]
  exact Fin.mk.injEq .. ▸ this

/-- **Boundedness of `gOffset`.**  For `n` below the `deleteSet`-orbit length `L'`, the cumulative
offset `gOffset n` stays strictly below the full orbit length `L = (p.toList x.1).length`.

Proof: were some `gOffset n ≥ L` with `n < L'`, take the minimal such `n`; then `n > 0`
(`gOffset 0 = 0`), `gOffset (n-1) < L`, and the wrap bound forces `gOffset n ≤ L`, hence
`gOffset n = L`, so `(deleteSet)^n x` returns to `x` — contradicting `Nodup` (`n ≠ 0`, both
`< L'`). -/
theorem gOffset_lt_length (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S})
    (hL : 0 < (p.toList x.1).length) :
    ∀ n, n < ((deleteSet p S).toList x).length → gOffset p S x n < (p.toList x.1).length := by
  set L := (p.toList x.1).length with hLdef
  set L' := ((deleteSet p S).toList x).length with hL'def
  by_contra hcon
  push Not at hcon
  obtain ⟨n, hnL', hgn⟩ := hcon
  -- minimal counterexample
  obtain ⟨m, hmL', hgm, hmin⟩ :
      ∃ m, m < L' ∧ L ≤ gOffset p S x m ∧ ∀ k < m, ¬ (k < L' ∧ L ≤ gOffset p S x k) := by
    have hex : ∃ m, m < L' ∧ L ≤ gOffset p S x m := ⟨n, hnL', hgn⟩
    classical
    let m := Nat.find hex
    have hspec := Nat.find_spec hex
    exact ⟨m, hspec.1, hspec.2, fun k hk => Nat.find_min hex hk⟩
  -- m > 0 since gOffset 0 = 0 < L
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, gOffset] at hgm; omega
    · exact hpos
  -- gOffset (m-1) < L
  have hm1L' : m - 1 < L' := by omega
  have hgm1 : gOffset p S x (m - 1) < L := by
    by_contra h
    push Not at h
    exact hmin (m - 1) (by omega) ⟨hm1L', h⟩
  -- the underlying dart at iterate (m-1)
  have hval : (((deleteSet p S) ^ (m - 1)) x : D) = (p ^ gOffset p S x (m - 1)) x.1 :=
    deleteSet_pow_coe p S x (m - 1)
  -- wrap bound: firstOutside ≤ L - gOffset (m-1)
  have hwrap : Equiv.Perm.DeleteSet.firstOutside p S (((deleteSet p S) ^ (m - 1)) x)
      ≤ L - gOffset p S x (m - 1) :=
    firstOutside_wrap_le p S x (gOffset p S x (m - 1)) hgm1 _ hval
  -- gOffset m = gOffset (m-1) + firstOutside, so gOffset m ≤ L
  have hmsucc : gOffset p S x m
      = gOffset p S x (m - 1)
        + Equiv.Perm.DeleteSet.firstOutside p S (((deleteSet p S) ^ (m - 1)) x) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [gOffset]
  have hgmLe : gOffset p S x m ≤ L := by omega
  have hgmEq : gOffset p S x m = L := le_antisymm hgmLe hgm
  -- so (deleteSet)^m x = x
  have hreturn : ((deleteSet p S) ^ m) x = x := by
    apply Subtype.ext
    rw [deleteSet_pow_coe, hgmEq, pow_length_toList_apply]
  -- contradiction with Nodup: m and 0 both < L', m > 0
  have hzero : ((deleteSet p S) ^ (0 : ℕ)) x = x := by simp
  have := deleteSet_pow_inj p S x hmL' (by omega : (0:ℕ) < L') (by rw [hreturn, hzero])
  omega

/-- The powers `p^i x` for `i < L = (p.toList x).length` are pairwise distinct. -/
theorem pow_inj_lt_length (p : Equiv.Perm D) (x : D) {a b : ℕ}
    (ha : a < (p.toList x).length) (hb : b < (p.toList x).length)
    (hab : (p ^ a) x = (p ^ b) x) : a = b := by
  have hnodup := Equiv.Perm.nodup_toList p x
  rw [List.nodup_iff_injective_getElem] at hnodup
  have hga : (p.toList x)[a] = (p ^ a) x := Equiv.Perm.getElem_toList _ _ _ _
  have hgb : (p.toList x)[b] = (p ^ b) x := Equiv.Perm.getElem_toList _ _ _ _
  have : (⟨a, ha⟩ : Fin _) = ⟨b, hb⟩ := by
    apply hnodup; simp only [hga, hgb, hab]
  exact Fin.mk.injEq .. ▸ this

/-- The `deleteSet`-orbit length `L'` is a period: `(deleteSet)^(n % L') x = (deleteSet)^n x`. -/
theorem deleteSet_pow_mod_length (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S}) (n : ℕ) :
    ((deleteSet p S) ^ (n % ((deleteSet p S).toList x).length)) x = ((deleteSet p S) ^ n) x := by
  rw [Equiv.Perm.length_toList]
  exact Equiv.Perm.pow_mod_card_support_cycleOf_self_apply (deleteSet p S) n x

/-- **Completeness of `gOffset`.**  Every kept index `i < L` of the `p`-orbit of `x.1` is hit by
some `gOffset n` with `n < L'`.  Proof: the kept dart `p^i x.1` is `deleteSet`-`SameCycle` to `x`
(via `sameCycle_deleteSet_iff`), hence equals `(deleteSet)^n x` for some `n < L'` (reduce the
exponent mod the period `L'`); injectivity of `p^· x.1` on `[0,L)` then pins `gOffset n = i`. -/
theorem gOffset_surj (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S})
    (hL : 0 < (p.toList x.1).length) (hL'pos : 0 < ((deleteSet p S).toList x).length)
    {i : ℕ} (hi : i < (p.toList x.1).length)
    (hkept : (p ^ i) x.1 ∉ S) :
    ∃ n, n < ((deleteSet p S).toList x).length ∧ gOffset p S x n = i := by
  set L' := ((deleteSet p S).toList x).length with hL'def
  -- the kept dart as a subtype element
  set y : {d : D // d ∉ S} := ⟨(p ^ i) x.1, hkept⟩ with hy
  -- p.SameCycle x.1 y.1, hence deleteSet-SameCycle x y
  have hsc : p.SameCycle x.1 y.1 := ⟨i, by rw [zpow_natCast]⟩
  have hsc' : (deleteSet p S).SameCycle x y :=
    (Equiv.Perm.sameCycle_deleteSet_iff p S x y).2 hsc
  obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (f := deleteSet p S) hsc'
  -- reduce k mod L'
  refine ⟨k % L', Nat.mod_lt _ hL'pos, ?_⟩
  have hpow : ((deleteSet p S) ^ (k % L')) x = y := by
    rw [deleteSet_pow_mod_length, hk]
  -- p^(gOffset (k%L')) x.1 = p^i x.1
  have hval : (p ^ gOffset p S x (k % L')) x.1 = (p ^ i) x.1 := by
    rw [← deleteSet_pow_coe, hpow]
  -- gOffset (k%L') < L by boundedness, i < L, injectivity ⟹ equal
  have hgbnd : gOffset p S x (k % L') < (p.toList x.1).length :=
    gOffset_lt_length p S x hL (k % L') (Nat.mod_lt _ hL'pos)
  exact pow_inj_lt_length p x.1 hgbnd hi hval

/-! ## `toList` as a `range`-map -/

/-- `p.toList x` is the `range`-map of the orbit powers. -/
theorem toList_eq_range_map (p : Equiv.Perm D) (x : D) :
    p.toList x = (List.range (p.toList x).length).map (fun i => (p ^ i) x) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi2
    rw [List.getElem_map, List.getElem_range, Equiv.Perm.getElem_toList]

/-! ## The index-list identity and the filtered-`toList` identity -/

/-- **Index-list identity (G).**  When the `deleteSet`-orbit of `x` is nontrivial (`L' > 0`), the
cumulative-offset sequence enumerates exactly the kept indices of the `p`-orbit, in increasing
order:
  `(range L').map gOffset = (range L).filter (fun i => (p ^ i) x.1 ∉ S)`.
Proved by `Perm.eq_of_sortedLE`: both lists are `Nodup`, `SortedLE`, and have the same membership
(boundedness + kept ⟹ ⊆; completeness ⟹ ⊇). -/
theorem gOffset_range_map_eq_filter (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S})
    (hL : 0 < (p.toList x.1).length) (hL'pos : 0 < ((deleteSet p S).toList x).length) :
    (List.range ((deleteSet p S).toList x).length).map (gOffset p S x)
      = (List.range (p.toList x.1).length).filter (fun i => decide ((p ^ i) x.1 ∉ S)) := by
  set L := (p.toList x.1).length with hLdef
  set L' := ((deleteSet p S).toList x).length with hL'def
  -- membership characterization of each side
  have hmemL : ∀ i, i ∈ (List.range L').map (gOffset p S x)
      ↔ (i < L ∧ (p ^ i) x.1 ∉ S) := by
    intro i
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨gOffset_lt_length p S x hL n hn, gOffset_kept p S x n⟩
    · rintro ⟨hiL, hkept⟩
      obtain ⟨n, hn, hgn⟩ := gOffset_surj p S x hL hL'pos hiL hkept
      exact ⟨n, hn, hgn⟩
  have hmemR : ∀ i, i ∈ (List.range L).filter (fun i => decide ((p ^ i) x.1 ∉ S))
      ↔ (i < L ∧ (p ^ i) x.1 ∉ S) := by
    intro i
    rw [List.mem_filter, List.mem_range, decide_eq_true_iff]
  -- both Nodup
  have hndL : ((List.range L').map (gOffset p S x)).Nodup :=
    (List.nodup_range).map (gOffset_strictMono p S x).injective
  have hndR : ((List.range L).filter (fun i => decide ((p ^ i) x.1 ∉ S))).Nodup :=
    (List.nodup_range).filter _
  -- Perm via mutual subperm
  have hperm : ((List.range L').map (gOffset p S x)).Perm
      ((List.range L).filter (fun i => decide ((p ^ i) x.1 ∉ S))) := by
    apply List.Subperm.antisymm
    · apply hndL.subperm
      intro i hi; rw [hmemR]; exact (hmemL i).1 hi
    · apply hndR.subperm
      intro i hi; rw [hmemL]; exact (hmemR i).1 hi
  -- both SortedLE
  have hsortL : ((List.range L').map (gOffset p S x)).SortedLE := by
    rw [List.sortedLE_iff_pairwise, List.pairwise_map]
    exact List.pairwise_lt_range.imp (fun hab => le_of_lt ((gOffset_strictMono p S x) hab))
  have hsortR : ((List.range L).filter (fun i => decide ((p ^ i) x.1 ∉ S))).SortedLE := by
    rw [List.sortedLE_iff_pairwise]
    exact (List.pairwise_lt_range.imp (fun h => le_of_lt h)).filter _
  exact hperm.eq_of_sortedLE hsortL hsortR

/-- **Filtered-`toList` identity (L), nontrivial case.**  When the `deleteSet`-orbit of `x` is
nontrivial, the underlying darts of the `deleteSet`-orbit list of `x` are exactly the surviving
(`∉ S`) darts of the `p`-orbit list of `x.1`, in cyclic order. -/
theorem deleteSet_toList_map_val (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S})
    (hL : 0 < (p.toList x.1).length) (hL'pos : 0 < ((deleteSet p S).toList x).length) :
    ((deleteSet p S).toList x).map Subtype.val = (p.toList x.1).filter (fun d => decide (d ∉ S)) := by
  -- LHS = (range L').map (p^(gOffset ·) x.1)
  have hLHS : ((deleteSet p S).toList x).map Subtype.val
      = (List.range ((deleteSet p S).toList x).length).map (fun n => (p ^ gOffset p S x n) x.1) := by
    conv_lhs => rw [show (deleteSet p S).toList x
      = (List.range ((deleteSet p S).toList x).length).map
          (fun n => ((deleteSet p S) ^ n) x) from toList_eq_range_map (deleteSet p S) x]
    rw [List.map_map]
    apply List.map_congr_left
    intro n _
    exact deleteSet_pow_coe p S x n
  -- RHS = ((range L).filter (∉S after p^·)).map (p^· x.1), via injective map-filter commute
  have hRHS : (p.toList x.1).filter (fun d => decide (d ∉ S))
      = ((List.range (p.toList x.1).length).filter (fun i => decide ((p ^ i) x.1 ∉ S))).map
          (fun i => (p ^ i) x.1) := by
    conv_lhs => rw [toList_eq_range_map p x.1]
    rw [List.filter_map]
    rfl
  rw [hLHS, hRHS]
  -- both are maps over index lists that agree by (G)
  rw [← gOffset_range_map_eq_filter p S x hL hL'pos, List.map_map]
  rfl

/-! ## From the filtered-`toList` identity to the cyclic flip-count transport -/

/-- On a nonzero edge sign, `EdgeSign.toStrict` is `some` of `edgeToStrict`. -/
theorem toStrict_eq_some_edgeToStrict {a : EdgeSign} (h : a ≠ EdgeSign.zero) :
    a.toStrict = some (edgeToStrict a) := by
  cases a with
  | plus => rfl
  | minus => rfl
  | zero => exact absurd rfl h

omit [Fintype D] [DecidableEq D] in
/-- `filterMap (toStrict ∘ es)` over a list equals `map (edgeToStrict ∘ es)` over the sublist of
darts with nonzero sign.  (A `filterMap` whose option is governed by the nonzero predicate is a
`filter` followed by a `map`.) -/
theorem filterMap_toStrict_eq_filter_map (es : D → EdgeSign) (l : List D) :
    l.filterMap (fun d => (es d).toStrict)
      = (l.filter (fun d => decide (es d ≠ EdgeSign.zero))).map (fun d => edgeToStrict (es d)) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.filterMap_cons, List.filter_cons]
      by_cases ha : es a = EdgeSign.zero
      · rw [ha]
        rw [show (EdgeSign.zero.toStrict) = none from rfl]
        rw [if_neg (by simp), ih]
      · rw [toStrict_eq_some_edgeToStrict ha, if_pos (by simpa using ha), List.map_cons, ih]

/-- **The kept strict list equals the `M`-filtered strict list (nontrivial case).**
For `S = {d : es d = zero}`, the strict signs of the kept (`deleteSet`) orbit list of `x` equal the
zero-skipped strict signs of the full `p`-orbit list of `x.1`. -/
theorem kept_strict_list_eq (p : Equiv.Perm D) (es : D → EdgeSign) (S : Finset D)
    (hSzero : ∀ d, d ∈ S ↔ es d = EdgeSign.zero)
    (x : {d : D // d ∉ S})
    (hL : 0 < (p.toList x.1).length) (hL'pos : 0 < ((deleteSet p S).toList x).length) :
    ((deleteSet p S).toList x).map (fun y => edgeToStrict (es y.1))
      = ((p.toList x.1).map es).filterMap EdgeSign.toStrict := by
  -- RHS = (p.toList x.1).filterMap (toStrict ∘ es) = (filter nonzero).map (edgeToStrict ∘ es)
  rw [List.filterMap_map, Function.comp_def, filterMap_toStrict_eq_filter_map]
  -- LHS = ((deleteSet.toList x).map val).map (edgeToStrict ∘ es)
  have hLHS : ((deleteSet p S).toList x).map (fun y => edgeToStrict (es y.1))
      = (((deleteSet p S).toList x).map Subtype.val).map (fun d => edgeToStrict (es d)) := by
    rw [List.map_map]; rfl
  rw [hLHS, deleteSet_toList_map_val p S x hL hL'pos]
  -- filter (∉ S) = filter (es ≠ zero), since d ∉ S ↔ es d ≠ zero
  congr 1
  apply List.filter_congr
  intro d _
  simp only [decide_eq_decide]
  rw [ne_eq, ← hSzero d]

/-- `cyclicFlipCount` of a list of length `≤ 1` is `0`. -/
theorem cyclicFlipCount_eq_zero_of_length_le_one {α : Type*} [DecidableEq α] (l : List α)
    (h : l.length ≤ 1) : cyclicFlipCount l = 0 := by
  match l, h with
  | [], _ => rfl
  | [a], _ => simp only [cyclicFlipCount, flipAux, ne_eq, not_true_eq_false, if_false]

/-- **Degenerate case.**  When the `deleteSet`-orbit list of `x` is empty (`x` is a sole survivor
or a fixed point), the zero-skipped strict signs of the full `p`-orbit list of `x.1` already have
`cyclicFlipCount = 0`: every surviving dart of the orbit equals `x.1`, so the filtered list has
length `≤ 1`. -/
theorem cyclicFlipCount_filterMap_eq_zero_of_empty (p : Equiv.Perm D) (es : D → EdgeSign)
    (S : Finset D) (hSzero : ∀ d, d ∈ S ↔ es d = EdgeSign.zero) (x : {d : D // d ∉ S})
    (hempty : (deleteSet p S).toList x = []) :
    cyclicFlipCount (((p.toList x.1).map es).filterMap EdgeSign.toStrict) = 0 := by
  apply cyclicFlipCount_eq_zero_of_length_le_one
  rw [List.filterMap_map, Function.comp_def, filterMap_toStrict_eq_filter_map, List.length_map]
  -- the kept sublist of the p-orbit has length ≤ 1
  -- deleteSet fixes x (empty toList ⟹ x ∉ support)
  have hxfix : (deleteSet p S) x = x := by
    have hnotsupp : x ∉ (deleteSet p S).support := Equiv.Perm.toList_eq_nil_iff.mp hempty
    exact Equiv.Perm.notMem_support.mp hnotsupp
  -- every kept dart of the p-orbit equals x.1
  have hall : ∀ y ∈ (p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero)), y = x.1 := by
    intro y hy
    rw [List.mem_filter, decide_eq_true_iff] at hy
    obtain ⟨hymem, hynz⟩ := hy
    have hyS : y ∉ S := by rw [hSzero]; exact hynz
    have hsc : p.SameCycle x.1 y := (Equiv.Perm.mem_toList_iff.mp hymem).1
    have hsc' : (deleteSet p S).SameCycle x ⟨y, hyS⟩ :=
      (Equiv.Perm.sameCycle_deleteSet_iff p S x ⟨y, hyS⟩).2 hsc
    -- deleteSet fixes x, so the only element same-cycle to x is x
    obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (f := deleteSet p S) hsc'
    have : ((deleteSet p S) ^ k) x = x :=
      Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hxfix k
    have hyx : (⟨y, hyS⟩ : {d : D // d ∉ S}) = x := by rw [← hk, this]
    exact congrArg Subtype.val hyx
  -- a nodup list whose elements are all x.1 has length ≤ 1
  have hnodup : ((p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero))).Nodup :=
    (Equiv.Perm.nodup_toList p x.1).filter _
  by_contra hlen
  push Not at hlen
  -- length ≥ 2 ⟹ two distinct elements both = x.1, contradicting nodup
  obtain ⟨a, b, hab, ha, hb⟩ :
      ∃ a b, a ≠ b ∧ a < ((p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero))).length
        ∧ b < ((p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero))).length :=
    ⟨0, 1, by omega, by omega, by omega⟩
  rw [List.nodup_iff_injective_getElem] at hnodup
  apply hab
  have he : ((p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero)))[a]
      = ((p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero)))[b] := by
    rw [hall _ (List.getElem_mem ha), hall _ (List.getElem_mem hb)]
  have : (⟨a, ha⟩ : Fin _) = ⟨b, hb⟩ := hnodup he
  exact Fin.mk.injEq .. ▸ this

/-! ## The cyclic flip-count transport -/

/-- **Cyclic flip-count transport.**  For `S = {d : es d = zero}`, the cyclic flip count of the
strict signs around the `deleteSet`-orbit of `x` equals the zero-skipped cyclic flip count of the
full `p`-orbit of `x.1`.  Both the nontrivial and the degenerate (sole-survivor / fixed-point)
cases are handled. -/
theorem cyclicFlipCount_transport (p : Equiv.Perm D) (es : D → EdgeSign) (S : Finset D)
    (hSzero : ∀ d, d ∈ S ↔ es d = EdgeSign.zero) (x : {d : D // d ∉ S}) :
    cyclicFlipCount (((deleteSet p S).toList x).map (fun y => edgeToStrict (es y.1)))
      = cyclicFlipCount (((p.toList x.1).map es).filterMap EdgeSign.toStrict) := by
  by_cases hL'pos : 0 < ((deleteSet p S).toList x).length
  · -- nontrivial deleteSet orbit ⟹ p-orbit also nontrivial
    have hL : 0 < (p.toList x.1).length := by
      by_contra h
      push Not at h
      have hxfix : p x.1 = x.1 := by
        have : x.1 ∉ p.support := Equiv.Perm.toList_eq_nil_iff.mp (List.length_eq_zero_iff.mp (by omega))
        exact Equiv.Perm.notMem_support.mp this
      -- p fixes x.1 ⟹ deleteSet fixes x ⟹ deleteSet orbit trivial, contradiction
      have hdfix : (deleteSet p S) x = x := by
        apply Subtype.ext
        rw [Equiv.Perm.deleteSet_apply_coe]
        exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hxfix _
      have : x ∉ (deleteSet p S).support := Equiv.Perm.notMem_support.mpr hdfix
      rw [← Equiv.Perm.toList_eq_nil_iff] at this
      rw [this] at hL'pos; simp at hL'pos
    rw [kept_strict_list_eq p es S hSzero x hL hL'pos]
  · -- degenerate case: deleteSet orbit empty
    push Not at hL'pos
    have hempty : (deleteSet p S).toList x = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hempty, List.map_nil, cyclicFlipCount,
      cyclicFlipCount_filterMap_eq_zero_of_empty p es S hSzero x hempty]

/-! ## The flip-transport (the `htrans` residual) -/

/-- **Flip transport.**  The strict `vertexFlip` of the kept (active) submap at the active vertex of
a kept dart `d` equals the book's skip-zeros flip count at the corresponding `M`-vertex.

This discharges the `htrans` hypothesis of
`Ch13ActiveComponent.marked_sphere_low_active_vertex_modular`. -/
theorem flip_transport (M : CombMap D) (es : D → EdgeSign) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)
    (hDelZero : ∀ d, d ∈ Del → es d = EdgeSign.zero)
    (hKeptNonzero : ∀ d, d ∉ Del → es d ≠ EdgeSign.zero)
    (d : {d : D // d ∉ Del}) :
    vertexFlip (keptMap M Del hsub) (keptSign M es Del)
        (Quotient.mk (cycleSetoid (keptMap M Del hsub).σ) d)
      = vertexFlipCountSkipZeros M es d.1 := by
  -- `Del = {d : es d = zero}` as a membership iff
  have hSzero : ∀ c, c ∈ Del ↔ es c = EdgeSign.zero :=
    fun c => ⟨hDelZero c, fun h => by by_contra hc; exact hKeptNonzero c hc h⟩
  -- strict bridge: vertexFlip of the kept map = skip-zeros count of strictToEdge ∘ keptSign
  rw [← vertexFlipCountSkipZeros_strict_eq_vertexFlip (keptMap M Del hsub) (keptSign M es Del) d]
  -- unfold both skip-zero counts to cyclic flip counts of filtered strict lists
  rw [vertexFlipCountSkipZeros, vertexSignList, cyclicFlipCountSkipZeros,
      vertexFlipCountSkipZeros, vertexSignList, cyclicFlipCountSkipZeros]
  -- the kept map's σ is `deleteSet M.σ Del`; the LHS strict list collapses
  have hLHSlist :
      (((keptMap M Del hsub).σ.toList d).map (fun y => strictToEdge (keptSign M es Del y))).filterMap
          EdgeSign.toStrict
      = ((deleteSet M.σ Del).toList d).map (fun y => edgeToStrict (es y.1)) := by
    rw [keptMap_sigma]
    -- map (strictToEdge ∘ keptSign) = (map keptSign).map strictToEdge, then filterMap recovers it
    rw [show (fun y : {d : D // d ∉ Del} => strictToEdge (keptSign M es Del y))
          = strictToEdge ∘ (keptSign M es Del) from rfl, ← List.map_map,
        filterMap_toStrict_map_strictToEdge]
    rfl
  rw [hLHSlist]
  -- now the goal is exactly the cyclic flip-count transport
  exact cyclicFlipCount_transport M.σ es Del hSzero d

/-! ## Discharging the `htrans` residual

`flip_transport` is exactly the `htrans` hypothesis of
`Ch13ActiveComponent.marked_sphere_low_active_vertex_modular`.  Plugging it in removes that residual,
leaving only the two genuinely topological residuals (`hconn`, `hFaceDeg`). -/

/-- **With-zeros low active vertex, transport discharged.**  Same as
`marked_sphere_low_active_vertex_modular` but with the flip-count transport `htrans` supplied by
`flip_transport`; the only remaining hypotheses are the two topological residuals (connectivity and
`faceDeg ≥ 3`) together with the natural zero-set conditions on `Del`. -/
theorem marked_sphere_low_active_vertex_no_htrans
    (M : CombMap D) (es : D → EdgeSign) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)
    (hclosed : ∀ d, d ∈ Del → M.α d ∈ Del)
    (hsphere : M.IsSphereMap) (hes : ∀ d, es (M.α d) = es d)
    (d₀ : {d : D // d ∉ Del})
    (hDelZero : ∀ d, d ∈ Del → es d = EdgeSign.zero)
    (hKeptNonzero : ∀ d, d ∉ Del → es d ≠ EdgeSign.zero)
    (hconn : (keptMap M Del hsub).Connected)
    (hFaceDeg : ∀ R, 3 ≤ faceDeg (keptMap M Del hsub) R) :
    ∃ d : D, ActiveVertex M es d ∧ vertexFlipCountSkipZeros M es d ≤ 2 :=
  marked_sphere_low_active_vertex_modular M es Del hsub hclosed hsphere hes d₀
    (fun d => hKeptNonzero d.1 d.2) hconn hFaceDeg
    (fun d => flip_transport M es Del hsub hDelZero hKeptNonzero d)

/-! ## §3.3 Non-vacuity

The hypotheses of `flip_transport` are satisfiable with a **nonempty** deleted set `Del` (so the
transport is not vacuously about the empty deletion).  On the tetrahedron `tetraMap`, the signing
that zeros the single edge `{0,3}` (darts `0,3`) and marks every other edge `plus` makes
`Del = {0,3}` a genuine nonempty `α`-closed zero set, and `flip_transport` applies, yielding a real
equality between the kept submap's `vertexFlip` and the book's skip-zeros count. -/

/-- A `±/0` signing on the tetrahedron whose only zero edge is `{0,3}`. -/
def tetraZeroSign : Fin 12 → EdgeSign := fun d =>
  if d = 0 ∨ d = 3 then EdgeSign.zero else EdgeSign.plus

/-- The deleted (zero) dart set `{0,3}` of `tetraZeroSign`. -/
def tetraDel : Finset (Fin 12) := {0, 3}

theorem tetraDel_nonempty : tetraDel.Nonempty := ⟨0, by decide⟩

theorem tetraDel_hsub : ∀ d, d ∈ tetraDel ↔ ProofsInTheBook.Ch13MarkedSphere.tetraMap.α d ∈ tetraDel := by
  decide

theorem tetraDel_hDelZero : ∀ d, d ∈ tetraDel → tetraZeroSign d = EdgeSign.zero := by decide

theorem tetraDel_hKeptNonzero : ∀ d, d ∉ tetraDel → tetraZeroSign d ≠ EdgeSign.zero := by decide

/-- **Non-vacuity witness.**  `flip_transport` instantiates on the tetrahedron with the nonempty
zero set `Del = {0,3}`: for the kept dart `1`, the kept submap's `vertexFlip` at its vertex equals
the book's skip-zeros count of `tetraZeroSign` at `1`.  (The hypotheses are all discharged by
`decide`, and `Del` is genuinely nonempty.) -/
theorem flip_transport_tetra_nonvacuous :
    vertexFlip (keptMap ProofsInTheBook.Ch13MarkedSphere.tetraMap tetraDel tetraDel_hsub)
        (keptSign ProofsInTheBook.Ch13MarkedSphere.tetraMap tetraZeroSign tetraDel)
        (Quotient.mk
          (cycleSetoid
            (keptMap ProofsInTheBook.Ch13MarkedSphere.tetraMap tetraDel tetraDel_hsub).σ)
          ⟨1, by decide⟩)
      = vertexFlipCountSkipZeros ProofsInTheBook.Ch13MarkedSphere.tetraMap tetraZeroSign 1 :=
  flip_transport ProofsInTheBook.Ch13MarkedSphere.tetraMap tetraZeroSign tetraDel
    tetraDel_hsub tetraDel_hDelZero tetraDel_hKeptNonzero ⟨1, by decide⟩

end ProofsInTheBook.Ch13FlipTransport
