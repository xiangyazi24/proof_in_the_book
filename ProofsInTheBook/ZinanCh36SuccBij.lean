import ProofsInTheBook.ZinanCh36LobeWiring
import ProofsInTheBook.ZinanCh36Alternation

/-!
# `ZinanCh36SuccBij` — two residual geometric items of the Ch36 alternation closure.

This file discharges TWO of the three named geometric residues of `ZinanCh36Alternation`
(see `HANDOFF/outbox/ch36alternation-reply.md`):

1. **`boundarySucc` injectivity + single-cycle covering.**  `boundarySucc` on a line crossing is
   `nextCrossing`: "advance to the next crossing in cyclic walk order".  We prove

   * `boundarySucc_injOn` / `boundarySuccSub_injective` — the `hinj` slot of
     `boundarySucc_cycle_connected` / `fullLineCrossingAlternation_of_geom`.  Direct cyclic-distance
     argument: if `nextCrossing i = nextCrossing j = m` with `i ≠ j`, then the farther of `i, j`
     (in forward walk order) puts the nearer one strictly inside its `no_crossing_before_next`
     interval — contradiction.
   * `boundarySucc_cover` — the `hcover` slot: the orbit of any fixed crossing `i₀` under
     `boundarySuccSub` covers ALL crossings.  Via the sorted boundary list: `boundarySucc` is the
     cyclic list-successor (`boundarySucc_eq_listSucc`), so its iterates from `i₀` realise every
     list entry.

   Combined, `boundarySucc_cycle_connected_unconditional` discharges the cycle-connectedness with
   only `hvert` (the genericity guard) — no named geometric hypotheses.

2. **Carrier disjointness of distinct same-sign lobes.**  `upperLobes_carrier_disjoint` /
   `lowerLobes_carrier_disjoint`: for distinct crossings `i ≠ j` with `eSign` both `+1` (resp.
   `−1`), the two lobe chains have disjoint carriers.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36SuccBij

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonWindingExterior (eSign osign eSign_eq_osign)
open ProofsInTheBook.PolygonWindingBound (eSign_mem)
open ProofsInTheBook.ZinanCh36Theta (LineCrossingEdges mem_lineCrossingEdges_iff
  crossTau_injOn_lineCrossingEdges exists_sorted_enum)
open ProofsInTheBook.ZinanCh36Lobes (arcPos UpperLobe)
open ProofsInTheBook.ZinanCh36LobeWiring
open scoped RealInnerProductSpace BigOperators

noncomputable section

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ## §0. `arcPos` / `cyclicSteps` retraction arithmetic -/

/-- `cyclicSteps i (arcPos i k) = k` for a strictly-inside offset `0 < k < n`. -/
lemma cyclicSteps_arcPos (i : Fin n) {k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    cyclicSteps i (arcPos i k) = k := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  unfold cyclicSteps arcPos
  simp only
  by_cases hsmall : i.val + k < n
  · -- (i+k) % n = i+k ≥ i.val
    rw [Nat.mod_eq_of_lt hsmall]
    rw [if_pos (by omega)]
    omega
  · -- (i+k) % n = i+k-n < i.val
    have hge : n ≤ i.val + k := by omega
    have h2n : i.val + k < 2 * n := by have := i.isLt; omega
    have hmodeq : (i.val + k) % n = i.val + k - n := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    rw [hmodeq]
    have hlt : i.val + k - n < i.val := by omega
    rw [if_neg (by omega)]
    omega

/-- `arcPos i (cyclicSteps i j) = j` (forward retraction). -/
lemma arcPos_cyclicSteps (i j : Fin n) : arcPos i (cyclicSteps i j) = j := by
  apply Fin.ext
  unfold arcPos cyclicSteps
  simp only
  by_cases hle : i.val ≤ j.val
  · rw [if_pos hle]
    have : i.val + (j.val - i.val) = j.val := by omega
    rw [this, Nat.mod_eq_of_lt j.isLt]
  · rw [if_neg hle]
    have hjv : j.val < i.val := by omega
    have : i.val + (n - i.val + j.val) = n + j.val := by
      have := i.isLt; omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt j.isLt]

/-- `arcPos` depends on the offset only modulo `n`. -/
lemma arcPos_mod (i : Fin n) (k : ℕ) : arcPos i (k % n) = arcPos i k := by
  apply Fin.ext
  unfold arcPos
  simp only
  rw [Nat.add_mod i.val (k % n) n, Nat.mod_mod, ← Nat.add_mod]

/-- `arcPos i` is injective on offsets `< n`. -/
lemma arcPos_injOn_lt (i : Fin n) {p q : ℕ} (hp : p < n) (hq : q < n)
    (h : arcPos i p = arcPos i q) : p = q := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have e := congrArg Fin.val h
  unfold arcPos at e
  simp only at e
  -- (i+p)%n = (i+q)%n with p,q<n.
  have key : ∀ r : ℕ, r < n → (i.val + r) % n =
      if i.val + r < n then i.val + r else i.val + r - n := by
    intro r hr
    by_cases hs : i.val + r < n
    · rw [if_pos hs, Nat.mod_eq_of_lt hs]
    · rw [if_neg hs]
      have hge : n ≤ i.val + r := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  rw [key p hp, key q hq] at e
  split_ifs at e <;> omega

/-- `arcPos` composes: `arcPos (arcPos i a) b = arcPos i (a + b)`. -/
lemma arcPos_arcPos (i : Fin n) (a b : ℕ) :
    arcPos (arcPos i a) b = arcPos i (a + b) := by
  apply Fin.ext
  unfold arcPos
  simp only
  rw [Nat.add_mod ((i.val + a) % n) b n, Nat.mod_mod, ← Nat.add_mod, ← Nat.add_assoc]

/-- The forward offset to `nextCrossing i` equals `nextCrossDist i`, recovered as a `cyclicSteps`. -/
lemma cyclicSteps_nextCrossing (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) :
    cyclicSteps i (nextCrossing P ρ x i) = nextCrossDist P ρ x i := by
  unfold nextCrossing
  exact cyclicSteps_arcPos i (nextCrossDist_pos P ρ x hvert hi) (nextCrossDist_lt P ρ x hvert hi)

/-! ## §1. Item 1a — injectivity of the boundary successor

If `nextCrossing i = nextCrossing j = m` with `i ≠ j`, the farther-back crossing (in forward
walk order) sees the nearer one strictly inside its `no_crossing_before_next` interval. -/

/-- **Key contradiction lemma.**  For distinct crossings `i ≠ j` with `nextCrossing i = j`, the
forward distance `cyclicSteps j i = n − cyclicSteps i j` is positive and the crossing `i` cannot
lie strictly before `nextCrossing j`.  Used to rule out a collision. -/
lemma nextCrossing_injOn (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i j : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) (hj : j ∈ LineCrossingEdges P ρ x)
    (hEq : nextCrossing P ρ x i = nextCrossing P ρ x j) :
    i = j := by
  classical
  by_contra hne
  set m := nextCrossing P ρ x i with hm
  -- m ≠ i, m ≠ j
  have hmi : m ≠ i := nextCrossing_ne P ρ x hvert hi
  have hmj : m ≠ j := by rw [hEq]; exact nextCrossing_ne P ρ x hvert hj
  -- forward offsets a = cyclicSteps i m, b = cyclicSteps j m, both = nextCrossDist.
  have ha : cyclicSteps i m = nextCrossDist P ρ x i := cyclicSteps_nextCrossing P ρ x hvert hi
  have hb : cyclicSteps j m = nextCrossDist P ρ x j := by
    rw [hEq]; exact cyclicSteps_nextCrossing P ρ x hvert hj
  have hapos : 0 < cyclicSteps i m := by rw [ha]; exact nextCrossDist_pos P ρ x hvert hi
  have hbpos : 0 < cyclicSteps j m := by rw [hb]; exact nextCrossDist_pos P ρ x hvert hj
  -- WLOG: relate i and j by their offsets from i.  cyclicSteps i j > 0.
  have hijpos : 0 < cyclicSteps i j := cyclicSteps_pos_of_ne i j hne
  have hjipos : 0 < cyclicSteps j i := cyclicSteps_pos_of_ne j i (Ne.symm hne)
  have hsumij : cyclicSteps i j + cyclicSteps j i = n := cyclicSteps_add_reverse i j hne
  have hsumim : cyclicSteps i m + cyclicSteps m i = n := cyclicSteps_add_reverse i m (Ne.symm hmi)
  have hsumjm : cyclicSteps j m + cyclicSteps m j = n := cyclicSteps_add_reverse j m (Ne.symm hmj)
  -- The two crossings i, j relative to one another are symmetric; do a case split on which is
  -- "closer" forward from the OTHER.  In either case the farther one contains the nearer.
  -- Claim A: cyclicSteps i j ≥ cyclicSteps i m  (j is not strictly before m from i).
  have hclaimA : cyclicSteps i m ≤ cyclicSteps i j := by
    by_contra hlt
    push_neg at hlt
    -- j = arcPos i (cyclicSteps i j) is a crossing at offset 0 < cyclicSteps i j < nextCrossDist i
    have hjarc : arcPos i (cyclicSteps i j) = j := arcPos_cyclicSteps i j
    have hcontra := no_crossing_before_next P ρ x hvert hi hijpos (by rw [← ha]; exact hlt)
    rw [hjarc] at hcontra
    exact hcontra hj
  -- Claim B: cyclicSteps j i ≥ cyclicSteps j m  (i is not strictly before m from j).
  have hclaimB : cyclicSteps j m ≤ cyclicSteps j i := by
    by_contra hlt
    push_neg at hlt
    have hiarc : arcPos j (cyclicSteps j i) = i := arcPos_cyclicSteps j i
    have hcontra := no_crossing_before_next P ρ x hvert hj hjipos (by rw [← hb]; exact hlt)
    rw [hiarc] at hcontra
    exact hcontra hi
  -- All offsets < n.
  have himn : cyclicSteps i m < n := by omega
  have hjmn : cyclicSteps j m < n := by omega
  -- Now combine.  cyclicSteps i j ≥ cyclicSteps i m and cyclicSteps j i ≥ cyclicSteps j m,
  -- with cyclicSteps i j + cyclicSteps j i = n.  Forward-distance composition: going from i,
  -- we reach m at offset (cyclicSteps i m); going from j, we reach m at offset (cyclicSteps j m).
  -- The relation cyclicSteps i m = (cyclicSteps i j + cyclicSteps j m) mod n holds because both
  -- routes land on m.  Concretely arcPos i (cyclicSteps i j + cyclicSteps j m) = m.
  have hcompose : arcPos i (cyclicSteps i j + cyclicSteps j m) = m := by
    -- arcPos i (cyclicSteps i j) = j, then arcPos j (cyclicSteps j m) = m, and arcPos composes.
    have h1 : arcPos i (cyclicSteps i j) = j := arcPos_cyclicSteps i j
    have h2 : arcPos j (cyclicSteps j m) = m := arcPos_cyclicSteps j m
    apply Fin.ext
    have hjval : j.val = (i.val + cyclicSteps i j) % n := by
      have := congrArg Fin.val h1; unfold arcPos at this; simpa using this.symm
    have hmval : m.val = (j.val + cyclicSteps j m) % n := by
      have := congrArg Fin.val h2; unfold arcPos at this; simpa using this.symm
    unfold arcPos
    simp only
    rw [hmval, hjval]
    rw [Nat.add_mod ((i.val + cyclicSteps i j) % n) (cyclicSteps j m) n, Nat.mod_mod,
      ← Nat.add_mod, ← Nat.add_assoc]
  -- Reduce the offset modulo n and use forward-offset uniqueness `< n`.
  have hsmm : arcPos i ((cyclicSteps i j + cyclicSteps j m) % n) = arcPos i (cyclicSteps i m) := by
    rw [arcPos_mod, hcompose, arcPos_cyclicSteps]
  have hmodlt : (cyclicSteps i j + cyclicSteps j m) % n < n :=
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  have huniq : (cyclicSteps i j + cyclicSteps j m) % n = cyclicSteps i m :=
    arcPos_injOn_lt i hmodlt himn hsmm
  -- cyclicSteps j m ≤ cyclicSteps j i = n − cyclicSteps i j ⟹ sum ≤ n; and sum ≥ 1.
  have hji_eq : cyclicSteps j i = n - cyclicSteps i j := by omega
  have hsum_le : cyclicSteps i j + cyclicSteps j m ≤ n := by omega
  -- the mod collapses: if sum < n it is sum; if sum = n it is 0.  Both contradict.
  rcases Nat.lt_or_ge (cyclicSteps i j + cyclicSteps j m) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at huniq; omega
  · have heqn : cyclicSteps i j + cyclicSteps j m = n := by omega
    rw [heqn, Nat.mod_self] at huniq; omega

/-- **`boundarySucc_injOn`.**  The boundary successor is injective on the line crossings. -/
theorem boundarySucc_injOn (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i j : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) (hj : j ∈ LineCrossingEdges P ρ x)
    (hEq : boundarySucc P ρ x i = boundarySucc P ρ x j) :
    i = j := by
  rw [boundarySucc_eq_nextCrossing P ρ x hi, boundarySucc_eq_nextCrossing P ρ x hj] at hEq
  exact nextCrossing_injOn P ρ x hvert hi hj hEq

/-- **`boundarySuccSub_injective`.**  The `hinj` slot: `boundarySuccSub` is injective on the
crossing subtype. -/
theorem boundarySuccSub_injective (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) :
    Function.Injective (boundarySuccSub P ρ x hvert) := by
  intro a b hab
  -- the underlying values agree, so injOn closes it.
  have hval : boundarySucc P ρ x a.1 = boundarySucc P ρ x b.1 := congrArg Subtype.val hab
  exact Subtype.ext (boundarySucc_injOn P ρ x hvert a.2 b.2 hval)

/-! ## §2. Item 1b — single-cycle covering via the `cyclicSteps i₀` key rank

The crossings carry the injective `key c := cyclicSteps i₀ c` (offset from the base crossing
`i₀`, with `key i₀ = 0` the minimum).  Forward distance composes additively below the wrap:
`key (nextCrossing c) = (key c + nextCrossDist c) mod n`.  We prove the forward orbit of `i₀`
covers ALL crossings by strong induction on `key`: a crossing `w ≠ i₀` has a key-predecessor `c`
(largest key `< key w` among crossings — `i₀` qualifies), and `nextCrossing c = w` because the
walk-forward-next from `c` coincides with the key-order-next. -/

/-- The key of a crossing: its `cyclicSteps` offset from the base crossing `i₀`. -/
abbrev keyf (i₀ a : Fin n) : ℕ := cyclicSteps i₀ a

/-- `key i₀ i₀ = 0` and any other key is `< n`. -/
lemma keyf_self (i₀ : Fin n) : keyf i₀ i₀ = 0 := by
  unfold keyf cyclicSteps; simp

lemma keyf_lt (i₀ a : Fin n) : keyf i₀ a < n := by
  unfold keyf cyclicSteps
  by_cases hle : i₀.val ≤ a.val
  · rw [if_pos hle]; have := a.isLt; omega
  · rw [if_neg hle]; have := a.isLt; have := i₀.isLt; omega

/-- `key` is injective. -/
lemma keyf_injective (i₀ : Fin n) {a b : Fin n} (h : keyf i₀ a = keyf i₀ b) : a = b :=
  cyclicSteps_injOn i₀ a b h

/-- **Key-difference is the forward distance.**  For crossings/indices with `key i₀ c < key i₀ w`,
`cyclicSteps c w = key w − key c` and `arcPos c (key w − key c) = w`. -/
lemma cyclicSteps_of_keyf_lt (i₀ c w : Fin n) (hlt : keyf i₀ c < keyf i₀ w) :
    cyclicSteps c w = keyf i₀ w - keyf i₀ c ∧
      arcPos c (keyf i₀ w - keyf i₀ c) = w := by
  -- c = arcPos i₀ (key c), w = arcPos i₀ (key w); both keys < n; key c < key w.
  have hc : arcPos i₀ (keyf i₀ c) = c := arcPos_cyclicSteps i₀ c
  have hw : arcPos i₀ (keyf i₀ w) = w := arcPos_cyclicSteps i₀ w
  have hwn : keyf i₀ w < n := keyf_lt i₀ w
  set d := keyf i₀ w - keyf i₀ c with hd
  have hdpos : 0 < d := by omega
  have hdlt : d < n := by omega
  -- arcPos c d = arcPos i₀ (key c + d) = arcPos i₀ (key w) = w.
  have harc : arcPos c d = w := by
    rw [← hc, arcPos_arcPos]
    have hkeysum : keyf i₀ c + d = keyf i₀ w := by omega
    rw [hkeysum, hw]
  refine ⟨?_, harc⟩
  -- cyclicSteps c w = d by uniqueness of forward offset `< n`.
  have hcomp : arcPos c (cyclicSteps c w) = arcPos c d := by
    rw [arcPos_cyclicSteps, harc]
  -- both offsets `< n`: cyclicSteps c w < n, d < n.
  have hcwn : cyclicSteps c w < n := by
    have hcwlt := keyf_lt c w; unfold keyf at hcwlt; exact hcwlt
  exact arcPos_injOn_lt c hcwn hdlt hcomp

/-- **No crossing with key strictly between `c` and `nextCrossing c` (when forward).**  Combined
with key composition: if `c` is a crossing whose key-successor among crossings is `w` (largest
crossing key `< key w`, no crossing key strictly between), then `nextCrossing c = w`. -/
lemma nextCrossing_eq_of_keyf_successor (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i₀ c w : Fin n}
    (hc : c ∈ LineCrossingEdges P ρ x) (hw : w ∈ LineCrossingEdges P ρ x)
    (hlt : keyf i₀ c < keyf i₀ w)
    (hgap : ∀ z ∈ LineCrossingEdges P ρ x, ¬ (keyf i₀ c < keyf i₀ z ∧ keyf i₀ z < keyf i₀ w)) :
    nextCrossing P ρ x c = w := by
  obtain ⟨hcw, harc⟩ := cyclicSteps_of_keyf_lt i₀ c w hlt
  set d := keyf i₀ w - keyf i₀ c with hd
  -- nextCrossDist c ≤ cyclicSteps c w = d (since w is a crossing forward from c).
  have hdpos : 0 < d := by omega
  have hdlt : d < n := by have := keyf_lt i₀ w; omega
  -- nextCrossDist c is the MINIMUM forward crossing distance; d is one such, so nextCrossDist ≤ d.
  have hdmem : d ∈ crossingDists P ρ x c := by
    rw [mem_crossingDists_iff]
    exact ⟨hdlt, hdpos, by rw [harc]; exact hw⟩
  have hne := crossingDists_nonempty P ρ x hvert hc
  have hle : nextCrossDist P ρ x c ≤ d := by
    unfold nextCrossDist; rw [dif_pos hne]
    exact (crossingDists P ρ x c).min'_le d hdmem
  -- nextCrossing c = arcPos c (nextCrossDist c) is a crossing; its key lies in [key c, key w).
  -- If nextCrossDist c < d, that crossing has key strictly between key c and key w — contra hgap.
  set e := nextCrossDist P ρ x c with he
  have hepos : 0 < e := nextCrossDist_pos P ρ x hvert hc
  have heln : e < n := nextCrossDist_lt P ρ x hvert hc
  have hnext_cross : nextCrossing P ρ x c ∈ LineCrossingEdges P ρ x := nextCrossing_mem P ρ x hvert hc
  have hwn : keyf i₀ w < n := keyf_lt i₀ w
  have hkeyw : keyf i₀ c + d = keyf i₀ w := by omega
  -- key (nextCrossing c) = (key c + e) mod n; with e ≤ d and key c + d = key w < n, so key c + e < n.
  have hsum_lt : keyf i₀ c + e < n := by omega
  have hkey_next : keyf i₀ (nextCrossing P ρ x c) = keyf i₀ c + e := by
    -- nextCrossing c = arcPos c e = arcPos i₀ (key c + e).
    have hnc : nextCrossing P ρ x c = arcPos i₀ (keyf i₀ c + e) := by
      show arcPos c e = arcPos i₀ (keyf i₀ c + e)
      have hcc : c = arcPos i₀ (keyf i₀ c) := (arcPos_cyclicSteps i₀ c).symm
      conv_lhs => rw [hcc]
      rw [arcPos_arcPos]
    rw [hnc]
    -- key (arcPos i₀ (key c + e)) = (key c + e) since key c + e < n and > 0.
    unfold keyf
    exact cyclicSteps_arcPos i₀ (by omega) (by omega)
  -- Now: nextCrossing c is a crossing with key = key c + e ∈ [key c + 1, key c + d] = [.., key w].
  -- gap forbids key strictly between key c and key w, so key c + e = key w, i.e. e = d.
  by_cases hed : e = d
  · -- e = d ⟹ nextCrossing c = arcPos c d = w.
    rw [show nextCrossing P ρ x c = arcPos c e from rfl, hed, harc]
  · -- e < d ⟹ key (nextCrossing c) strictly between key c and key w — contradiction.
    have helt : e < d := by omega
    exfalso
    apply hgap (nextCrossing P ρ x c) hnext_cross
    rw [hkey_next]
    constructor
    · omega
    · -- key c + e < key c + d = key w.
      have : keyf i₀ c + d = keyf i₀ w := by omega
      omega

/-- **Existence of a key-predecessor crossing.**  For a crossing `w` with `key i₀ w > 0` (i.e.
`w ≠ i₀`), there is a crossing `c` with `key c < key w` and no crossing key strictly between. -/
lemma exists_keyf_predecessor (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    {i₀ w : Fin n} (hi₀ : i₀ ∈ LineCrossingEdges P ρ x) (hw : w ∈ LineCrossingEdges P ρ x)
    (hwpos : 0 < keyf i₀ w) :
    ∃ c ∈ LineCrossingEdges P ρ x, keyf i₀ c < keyf i₀ w ∧
      (∀ z ∈ LineCrossingEdges P ρ x, ¬ (keyf i₀ c < keyf i₀ z ∧ keyf i₀ z < keyf i₀ w)) := by
  classical
  -- the crossings with key < key w, nonempty (i₀ has key 0 < key w).
  set S : Finset (Fin n) :=
    (LineCrossingEdges P ρ x).filter (fun z => keyf i₀ z < keyf i₀ w) with hS
  have hi₀S : i₀ ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨hi₀, by rw [keyf_self]; exact hwpos⟩
  have hSne : S.Nonempty := ⟨i₀, hi₀S⟩
  -- pick c ∈ S maximising key.
  obtain ⟨c, hcS, hcmax⟩ := S.exists_max_image (keyf i₀) hSne
  rw [hS, Finset.mem_filter] at hcS
  refine ⟨c, hcS.1, hcS.2, ?_⟩
  intro z hz hbetween
  -- z has key c < key z < key w, so z ∈ S with key z > key c — contradicts maximality.
  have hzS : z ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨hz, hbetween.2⟩
  have := hcmax z hzS
  omega

/-- **The forward orbit covers all crossings (underlying form).**  Every crossing `w` is reached
from `i₀` by some number of `boundarySucc` steps. -/
theorem boundarySucc_orbit_covers (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i₀ : Fin n}
    (hi₀ : i₀ ∈ LineCrossingEdges P ρ x) {w : Fin n} (hw : w ∈ LineCrossingEdges P ρ x) :
    ∃ m : ℕ, (boundarySucc P ρ x)^[m] i₀ = w := by
  classical
  -- strong induction on key i₀ w.
  generalize hk : keyf i₀ w = K
  induction K using Nat.strong_induction_on generalizing w with
  | _ K IH =>
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · -- key w = 0 ⟹ w = i₀.
      refine ⟨0, ?_⟩
      have : keyf i₀ w = keyf i₀ i₀ := by rw [hk, hK0, keyf_self]
      rw [keyf_injective i₀ this]
      rfl
    · -- key w > 0 ⟹ predecessor.
      have hwpos : 0 < keyf i₀ w := by rw [hk]; exact hKpos
      obtain ⟨c, hc, hclt, hgap⟩ := exists_keyf_predecessor P ρ x hi₀ hw hwpos
      have hnext : nextCrossing P ρ x c = w :=
        nextCrossing_eq_of_keyf_successor P ρ x hvert hc hw hclt hgap
      -- key c < key w = K, so IH applies to c.
      have hckey : keyf i₀ c < K := by rw [← hk]; exact hclt
      obtain ⟨m, hm⟩ := IH (keyf i₀ c) hckey hc rfl
      refine ⟨m + 1, ?_⟩
      rw [Function.iterate_succ_apply', hm, boundarySucc_eq_nextCrossing P ρ x hc, hnext]

/-- **`boundarySucc_cover`.**  The `hcover` slot: the orbit of `⟨i₀, hi₀⟩` under `boundarySuccSub`
covers ALL crossings. -/
theorem boundarySucc_cover (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i₀ : Fin n}
    (hi₀ : i₀ ∈ LineCrossingEdges P ρ x) :
    ∀ b : CrossSet P ρ x, ∃ m : ℕ,
      (boundarySuccSub P ρ x hvert)^[m] ⟨i₀, hi₀⟩ = b := by
  intro b
  obtain ⟨m, hm⟩ := boundarySucc_orbit_covers P ρ x hvert hi₀ b.2
  refine ⟨m, ?_⟩
  apply Subtype.ext
  rw [boundarySuccSub_iterate_val P ρ x hvert]
  exact hm

/-! ## §3. The discharged cycle-connectedness (unconditional in `hvert`)

`boundarySucc_cycle_connected` of `ZinanCh36LobeWiring` takes `hinj` and `hcover` as named
geometric hypotheses; we now supply both from §1–§2, giving an unconditional
(modulo the genericity guard `hvert`) cyclic connectedness of the boundary successor. -/

/-- **`boundarySucc_cycle_connected_unconditional`.**  Any two crossings are connected by iterating
`boundarySucc`, with NO named geometric hypotheses beyond the genericity guard `hvert`. -/
theorem boundarySucc_cycle_connected_unconditional (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    {i j : Fin n} (hi : i ∈ LineCrossingEdges P ρ x) (hj : j ∈ LineCrossingEdges P ρ x) :
    ∃ k : ℕ, (boundarySucc P ρ x)^[k] i = j :=
  boundarySucc_cycle_connected P ρ x hvert (boundarySuccSub_injective P ρ x hvert) hi
    (boundarySucc_cover P ρ x hvert hi) hi hj

/-! ## §4. Item 2 — carrier disjointness of distinct same-sign lobes

For distinct crossings `a ≠ b` with `eSign` both `+1` the two upper lobes have disjoint carriers.
The proof factors into a combinatorial core and a geometric layer:

* **Index disjointness** (`upperLobe_index_disjoint`): the walk-edge index sets of the two lobes,
  `{arcPos a k : 0 ≤ k ≤ dA}` and `{arcPos b l : 0 ≤ l ≤ dB}` (with `dA = nextCrossDist a`,
  `dB = nextCrossDist b`), are disjoint.  In `cyclicSteps a`-offset coordinates the X-offsets are
  `[0, dA]` and the Y-offsets are `[β, β+dB]` with `β = cyclicSteps a b`; the sign-flip rules out
  the boundary collisions (`b ≠ bsucc a`, `a ≠ bsucc b`) and `no_crossing_before_next` forces
  `β > dA` and `β + dB < n`, so the offset intervals are disjoint in `[0, n)`.
* **Geometric layer** (`upperLobes_carrier_disjoint`): each clipped chain segment lies in the
  polygon edge of its index, and the feet meet their edges in the OPEN interior
  (`crossU ∈ (0,1)`); since the index sets are disjoint, distinct/adjacent edges meet only at a
  shared vertex, which is never on a clipped lobe segment (feet are interior; shared vertices are
  off the ray line).  Hence no carrier point is shared. -/

open ProofsInTheBook.ZinanCh36LobeChain
  (lobeChain footFirst footLast lobeLastEdge chainPt lobeChain_segA lobeChain_segB
    chainPt_zero chainPt_len chainPt_interior carrier_side_nonneg)
open ProofsInTheBook.ZinanCh36Theta (crossU_mem_Ioo crossPoint_mem_edge)

variable {P : StrictSimplePolygon n} {ρ : RayDirection P} {x : Pt}

/-- The walk-edge index of chain segment `i` of an upper lobe is `arcPos start i`. -/
def lobeEdgeIdx (L : UpperLobe P ρ x) (i : ℕ) : Fin n := arcPos L.start i

/-! ### Index disjointness (combinatorial core) -/

/-- For two distinct `+1` crossings `a ≠ b`, the boundary successor of `a` is not `b`
(sign-flip: `eSign (bsucc a) = -1 ≠ 1 = eSign b`). -/
lemma boundarySucc_ne_of_pos (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {a b : Fin n}
    (ha : a ∈ LineCrossingEdges P ρ x) (hσa : eSign P ρ a = 1) (hσb : eSign P ρ b = 1) :
    boundarySucc P ρ x a ≠ b := by
  intro hEq
  have hflip := boundarySucc_sign_flip P ρ x hvert ha
  rw [hEq, hσb, hσa] at hflip
  norm_num at hflip

/-- **Index disjointness.**  The walk-edge index offset sets of two distinct `+1` lobes are
disjoint: if `arcPos a kA = arcPos b kB` with `kA ≤ nextCrossDist a` and `kB ≤ nextCrossDist b`
then a contradiction. -/
lemma upperLobe_index_disjoint
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {a b : Fin n}
    (ha : a ∈ LineCrossingEdges P ρ x) (hb : b ∈ LineCrossingEdges P ρ x)
    (hab : a ≠ b) (hσa : eSign P ρ a = 1) (hσb : eSign P ρ b = 1)
    {kA kB : ℕ} (hkA : kA ≤ nextCrossDist P ρ x a) (hkB : kB ≤ nextCrossDist P ρ x b)
    (heq : arcPos a kA = arcPos b kB) : False := by
  classical
  set dA := nextCrossDist P ρ x a with hdA
  set dB := nextCrossDist P ρ x b with hdB
  set β := cyclicSteps a b with hβ
  have hdApos : 0 < dA := nextCrossDist_pos P ρ x hvert ha
  have hdBpos : 0 < dB := nextCrossDist_pos P ρ x hvert hb
  have hdAlt : dA < n := nextCrossDist_lt P ρ x hvert ha
  have hdBlt : dB < n := nextCrossDist_lt P ρ x hvert hb
  have hβpos : 0 < β := cyclicSteps_pos_of_ne a b hab
  have hsum : β + cyclicSteps b a = n := cyclicSteps_add_reverse a b hab
  have hbapos : 0 < cyclicSteps b a := cyclicSteps_pos_of_ne b a (Ne.symm hab)
  -- β > dA: else b = arcPos a β is a crossing strictly inside (a, bsucc a).  b ≠ bsucc a by sign.
  have hb_ne_bsucc : b ≠ nextCrossing P ρ x a := by
    rw [← boundarySucc_eq_nextCrossing P ρ x ha]
    exact (boundarySucc_ne_of_pos hvert ha hσa hσb).symm
  have hβgtdA : dA < β := by
    rcases Nat.lt_or_ge dA β with h | h
    · exact h
    · exfalso
      -- β ≤ dA, β > 0; b = arcPos a β.  If β = dA then b = nextCrossing a (excluded); if β < dA,
      -- b = arcPos a β is a crossing strictly before next — contra no_crossing_before_next.
      have harc : arcPos a β = b := arcPos_cyclicSteps a b
      rcases Nat.lt_or_ge β dA with hlt | hge
      · have := no_crossing_before_next P ρ x hvert ha hβpos hlt
        rw [harc] at this; exact this hb
      · -- β = dA ⟹ b = arcPos a dA = nextCrossing a — excluded.
        have hβeq : β = dA := le_antisymm h hge
        apply hb_ne_bsucc
        rw [← harc, hβeq]
        unfold nextCrossing; rw [hdA]
  -- symmetric: cyclicSteps b a > dB, i.e. β + dB < n.
  have ha_ne_bsuccb : a ≠ nextCrossing P ρ x b := by
    rw [← boundarySucc_eq_nextCrossing P ρ x hb]
    exact (boundarySucc_ne_of_pos hvert hb hσb hσa).symm
  have hbagtdB : dB < cyclicSteps b a := by
    rcases Nat.lt_or_ge dB (cyclicSteps b a) with h | h
    · exact h
    · exfalso
      have harc : arcPos b (cyclicSteps b a) = a := arcPos_cyclicSteps b a
      rcases Nat.lt_or_ge (cyclicSteps b a) dB with hlt | hge
      · have := no_crossing_before_next P ρ x hvert hb hbapos hlt
        rw [harc] at this; exact this ha
      · have hbaeq : cyclicSteps b a = dB := le_antisymm h hge
        apply ha_ne_bsuccb
        rw [← harc, hbaeq]
        unfold nextCrossing; rw [hdB]
  have hβdBlt : β + dB < n := by omega
  -- Now arcPos a kA = arcPos b kB = arcPos a (β + kB).
  have hY : arcPos b kB = arcPos a (β + kB) := by
    rw [← arcPos_cyclicSteps a b, arcPos_arcPos, hβ]
  rw [hY] at heq
  -- both offsets < n: kA ≤ dA < n, β + kB ≤ β + dB < n.
  have hkAn : kA < n := by omega
  have hβkBn : β + kB < n := by omega
  have hoff := arcPos_injOn_lt a hkAn hβkBn heq
  -- kA = β + kB with kA ≤ dA < β ≤ β + kB — contradiction.
  omega

/-! ### Geometric layer: clipped segments live on polygon edges -/

/-- The lobe's first edge `start` is a span crossing with both feet off the ray line; its crossing
point `footFirst` meets edge `start` in the OPEN interior. -/
lemma footFirst_crossU_Ioo (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (L : UpperLobe P ρ x) :
    crossU P ρ x L.start ∈ Set.Ioo (0 : ℝ) 1 :=
  crossU_mem_Ioo P ρ x L.start L.cross_first (hvert L.start) (hvert (cyclicNext L.start))

/-- `footLast` meets edge `lobeLastEdge L` in the open interior. -/
lemma footLast_crossU_Ioo (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (L : UpperLobe P ρ x) :
    crossU P ρ x (lobeLastEdge L) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hsp : SpanCrossesSide P ρ x (lobeLastEdge L) := by
    have := L.cross_last
    unfold lobeLastEdge
    exact this
  exact crossU_mem_Ioo P ρ x (lobeLastEdge L) hsp (hvert _) (hvert _)

/-- `footFirst L ∈ Edge (arcPos L.start 0) = Edge L.start`. -/
lemma footFirst_mem_edge (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (L : UpperLobe P ρ x) : footFirst L ∈ Edge P.q (arcPos L.start 0) := by
  rw [arcPos_zero]
  have := footFirst_crossU_Ioo hvert L
  unfold footFirst
  exact crossPoint_mem_edge P ρ x L.start ⟨this.1.le, this.2.le⟩

/-- `footLast L ∈ Edge (lobeLastEdge L)`. -/
lemma footLast_mem_edge (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (L : UpperLobe P ρ x) : footLast L ∈ Edge P.q (lobeLastEdge L) := by
  have := footLast_crossU_Ioo hvert L
  unfold footLast
  exact crossPoint_mem_edge P ρ x (lobeLastEdge L) ⟨this.1.le, this.2.le⟩

/-- An interior chain vertex `chainPt L ⟨k,_⟩` (`0 < k < len`) is the polygon vertex
`P.q (arcPos start k)`, which sits at BOTH ends of two consecutive edges; in particular it is in
`Edge (arcPos start k)` (as its first vertex) and in `Edge (arcPos start (k-1))` (as its last). -/
lemma chainPt_mem_edge_start (L : UpperLobe P ρ x) {k : ℕ} (hk0 : 0 < k) (hklen : k < L.len)
    (hk : k < L.len + 1) :
    chainPt L ⟨k, hk⟩ = P.q (arcPos L.start k) := chainPt_interior L hk0 hklen hk

/-- **Clipped chain segment ⊆ polygon edge.**  Segment `i` of `lobeChain L` lies on the polygon
edge `arcPos L.start i`. -/
lemma lobeChain_seg_subset_edge (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (L : UpperLobe P ρ x) (i : Fin L.len) :
    seg ((lobeChain L).segA i) ((lobeChain L).segB i) ⊆ Edge P.q (arcPos L.start i.val) := by
  -- the edge as a convex set; show both segment endpoints lie on it.
  have hconv : Convex ℝ (Edge P.q (arcPos L.start i.val)) := by
    unfold Edge seg; exact convex_segment _ _
  apply hconv.segment_subset
  · -- segA = chainPt L ⟨i, _⟩.
    rw [lobeChain_segA]
    rcases Nat.eq_zero_or_pos i.val with hi0 | hi0
    · -- segA = footFirst, in Edge (arcPos start 0) = Edge (arcPos start i) since i = 0.
      have : chainPt L ⟨i.val, by omega⟩ = footFirst L := by
        unfold chainPt; rw [if_pos hi0]
      rw [this]
      have hedge : arcPos L.start i.val = arcPos L.start 0 := by rw [hi0]
      rw [hedge]
      exact footFirst_mem_edge hvert L
    · -- segA = P.q (arcPos start i) — first vertex of Edge (arcPos start i).
      have hilen : i.val < L.len := i.isLt
      rw [chainPt_mem_edge_start L hi0 hilen (by omega)]
      unfold Edge seg
      rw [segment_eq_image_lineMap]
      exact ⟨0, by norm_num, by rw [AffineMap.lineMap_apply_zero]⟩
  · -- segB = chainPt L ⟨i+1, _⟩.
    rw [lobeChain_segB]
    by_cases hilast : i.val + 1 = L.len
    · -- segB = footLast, and arcPos start i = lobeLastEdge L (i = len-1).
      have : chainPt L ⟨i.val + 1, by omega⟩ = footLast L := by
        unfold chainPt
        rw [if_neg (by simp), if_pos hilast]
      rw [this]
      have hlast : arcPos L.start i.val = lobeLastEdge L := by
        unfold lobeLastEdge
        congr 1; omega
      rw [hlast]
      exact footLast_mem_edge hvert L
    · -- segB = P.q (arcPos start (i+1)) = P.q (cyclicNext (arcPos start i)) — last vertex of edge.
      have hilen1 : i.val + 1 < L.len := by have := i.isLt; omega
      rw [chainPt_mem_edge_start L (by omega) hilen1 (by omega)]
      have hsucc : arcPos L.start (i.val + 1) = cyclicNext (arcPos L.start i.val) :=
        (cyclicNext_arcPos L.start i.val).symm
      rw [hsucc]
      unfold Edge seg
      rw [segment_eq_image_lineMap]
      exact ⟨1, by norm_num, by rw [AffineMap.lineMap_apply_one]⟩

/-- The vertex immediately PAST a `+1` lobe's last foot (`P.q (arcPos a (dA+1))`) is on the
NEGATIVE side: `nextCrossing a` has `eSign = -1`, so its end vertex is negative. -/
lemma side_arcPos_succ_neg (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {a : Fin n}
    (ha : a ∈ LineCrossingEdges P ρ x) (hσa : eSign P ρ a = 1) :
    side ρ.r x (P.q (arcPos a (nextCrossDist P ρ x a + 1))) < 0 := by
  have hmem : nextCrossing P ρ x a ∈ LineCrossingEdges P ρ x := nextCrossing_mem P ρ x hvert ha
  have hesign : eSign P ρ (nextCrossing P ρ x a) = -1 := by
    rw [eSign_nextCrossing P ρ x hvert ha, hσa]
  have h1 := sideAt_one_neg_of_eSign_neg_one P ρ x hvert hmem hesign
  -- sideAt (nextCrossing a) 1 = side (P.q (arcPos (nextCrossing a) 1)).
  have harceq : arcPos (nextCrossing P ρ x a) 1 = arcPos a (nextCrossDist P ρ x a + 1) := by
    have : nextCrossing P ρ x a = arcPos a (nextCrossDist P ρ x a) := rfl
    rw [this, arcPos_arcPos]
  unfold sideAt at h1
  rw [harceq] at h1
  exact h1

/-- **`upperLobes_carrier_disjoint`.**  For distinct crossings `a ≠ b` both with `eSign = 1`, the
two upper lobes have disjoint carriers. -/
theorem upperLobes_carrier_disjoint
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {a b : Fin n}
    (ha : a ∈ LineCrossingEdges P ρ x) (hb : b ∈ LineCrossingEdges P ρ x)
    (hab : a ≠ b) (hσa : eSign P ρ a = 1) (hσb : eSign P ρ b = 1) :
    Disjoint (lobeChain (upperLobeOfPos P ρ x hvert ha hσa)).carrier
             (lobeChain (upperLobeOfPos P ρ x hvert hb hσb)).carrier := by
  classical
  set X := upperLobeOfPos P ρ x hvert ha hσa with hXdef
  set Y := upperLobeOfPos P ρ x hvert hb hσb with hYdef
  have hXstart : X.start = a := rfl
  have hYstart : Y.start = b := rfl
  have hXlen : X.len = nextCrossDist P ρ x a + 1 := rfl
  have hYlen : Y.len = nextCrossDist P ρ x b + 1 := rfl
  rw [Set.disjoint_left]
  rintro z hzX hzY
  -- z lives on a segment of X and of Y.
  obtain ⟨iX, hziX⟩ := hzX
  obtain ⟨jY, hzjY⟩ := hzY
  -- z is on the polygon edges of the two indices.
  have hzeX : z ∈ Edge P.q (arcPos a iX.val) := by
    have := lobeChain_seg_subset_edge hvert X iX hziX
    rwa [hXstart] at this
  have hzeY : z ∈ Edge P.q (arcPos b jY.val) := by
    have := lobeChain_seg_subset_edge hvert Y jY hzjY
    rwa [hYstart] at this
  -- index bounds: iX ≤ dA, jY ≤ dB.
  have hiXlt : iX.val < nextCrossDist P ρ x a + 1 := hXlen ▸ iX.isLt
  have hjYlt : jY.val < nextCrossDist P ρ x b + 1 := hYlen ▸ jY.isLt
  have hiXle : iX.val ≤ nextCrossDist P ρ x a := by omega
  have hjYle : jY.val ≤ nextCrossDist P ρ x b := by omega
  -- the two edge indices are DISTINCT (index disjointness).
  have hidx_ne : arcPos a iX.val ≠ arcPos b jY.val := by
    intro hcoll
    exact upperLobe_index_disjoint hvert ha hb hab hσa hσb hiXle hjYle hcoll
  -- EdgeIntersectionCondition on (arcPos a iX, arcPos b jY).
  set eX := arcPos a iX.val with heX
  set eY := arcPos b jY.val with heY
  have hEC := P.edge_intersection eX eY
  unfold EdgeIntersectionCondition at hEC
  rw [dif_neg hidx_ne] at hEC
  by_cases hnext : cyclicNext eX = eY
  · -- shared vertex z = P.q eY.
    rw [dif_pos hnext] at hEC
    have hzv : z = P.q eY := by
      have : z ∈ Edge P.q eX ∩ Edge P.q eY := ⟨hzeX, hzeY⟩
      rw [hEC] at this; exact this
    -- eY = cyclicNext eX = arcPos a (iX+1).
    have heYsucc : eY = arcPos a (iX.val + 1) := by
      rw [← hnext, heX, cyclicNext_arcPos]
    by_cases hlast : iX.val = nextCrossDist P ρ x a
    · -- last X segment: eY = arcPos a (dA+1); side(P.q eY) < 0 but z ∈ carrier X ⟹ side z ≥ 0.
      have hsucc_eq : eY = arcPos a (nextCrossDist P ρ x a + 1) := by rw [heYsucc, hlast]
      have hsneg : side ρ.r x (P.q eY) < 0 := by
        rw [hsucc_eq]; exact side_arcPos_succ_neg hvert ha hσa
      have hsnn : 0 ≤ side ρ.r x z := carrier_side_nonneg X ⟨iX, hziX⟩
      rw [hzv] at hsnn; linarith
    · -- iX + 1 ≤ dA: index collision arcPos a (iX+1) = eY = arcPos b jY.
      have hiX1 : iX.val + 1 ≤ nextCrossDist P ρ x a := by omega
      exact upperLobe_index_disjoint hvert ha hb hab hσa hσb hiX1 hjYle
        (by rw [← heYsucc])
  · rw [dif_neg hnext] at hEC
    by_cases hprev : cyclicNext eY = eX
    · -- shared vertex z = P.q eX.
      rw [dif_pos hprev] at hEC
      have hzv : z = P.q eX := by
        have : z ∈ Edge P.q eX ∩ Edge P.q eY := ⟨hzeX, hzeY⟩
        rw [hEC] at this; exact this
      have heXsucc : eX = arcPos b (jY.val + 1) := by
        rw [← hprev, heY, cyclicNext_arcPos]
      by_cases hlast : jY.val = nextCrossDist P ρ x b
      · have hsucc_eq : eX = arcPos b (nextCrossDist P ρ x b + 1) := by rw [heXsucc, hlast]
        have hsneg : side ρ.r x (P.q eX) < 0 := by
          rw [hsucc_eq]; exact side_arcPos_succ_neg hvert hb hσb
        have hsnn : 0 ≤ side ρ.r x z := carrier_side_nonneg Y ⟨jY, hzjY⟩
        rw [hzv] at hsnn; linarith
      · have hjY1 : jY.val + 1 ≤ nextCrossDist P ρ x b := by omega
        exact upperLobe_index_disjoint hvert ha hb hab hσa hσb hiXle hjY1
          (heX.symm.trans heXsucc)
    · -- nonadjacent: edges disjoint.
      rw [dif_neg hprev] at hEC
      exact (Set.disjoint_left.mp hEC hzeX) hzeY

/-! ### Lower mirror -/

open ProofsInTheBook.ZinanCh36LobeWiring (LowerLobe lowerLobeOfNeg)
open ProofsInTheBook.ZinanCh36NonInterleave
  (lobeChainL footFirstL footLastL lobeLastEdgeL chainPtL chainPtL_interior
    lobeChainL_segA lobeChainL_segB carrierL_negside_nonneg negside_eq)

/-- Lower analogue of `boundarySucc_ne_of_pos`. -/
lemma boundarySucc_ne_of_neg (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {a b : Fin n}
    (ha : a ∈ LineCrossingEdges P ρ x) (hσa : eSign P ρ a = -1) (hσb : eSign P ρ b = -1) :
    boundarySucc P ρ x a ≠ b := by
  intro hEq
  have hflip := boundarySucc_sign_flip P ρ x hvert ha
  rw [hEq, hσb, hσa] at hflip
  norm_num at hflip

/-- **Lower index disjointness** (eSign `= -1` version). -/
lemma lowerLobe_index_disjoint
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {a b : Fin n}
    (ha : a ∈ LineCrossingEdges P ρ x) (hb : b ∈ LineCrossingEdges P ρ x)
    (hab : a ≠ b) (hσa : eSign P ρ a = -1) (hσb : eSign P ρ b = -1)
    {kA kB : ℕ} (hkA : kA ≤ nextCrossDist P ρ x a) (hkB : kB ≤ nextCrossDist P ρ x b)
    (heq : arcPos a kA = arcPos b kB) : False := by
  classical
  set dA := nextCrossDist P ρ x a with hdA
  set dB := nextCrossDist P ρ x b with hdB
  set β := cyclicSteps a b with hβ
  have hdApos : 0 < dA := nextCrossDist_pos P ρ x hvert ha
  have hdBpos : 0 < dB := nextCrossDist_pos P ρ x hvert hb
  have hdAlt : dA < n := nextCrossDist_lt P ρ x hvert ha
  have hdBlt : dB < n := nextCrossDist_lt P ρ x hvert hb
  have hβpos : 0 < β := cyclicSteps_pos_of_ne a b hab
  have hsum : β + cyclicSteps b a = n := cyclicSteps_add_reverse a b hab
  have hbapos : 0 < cyclicSteps b a := cyclicSteps_pos_of_ne b a (Ne.symm hab)
  have hb_ne_bsucc : b ≠ nextCrossing P ρ x a := by
    rw [← boundarySucc_eq_nextCrossing P ρ x ha]
    exact (boundarySucc_ne_of_neg hvert ha hσa hσb).symm
  have hβgtdA : dA < β := by
    rcases Nat.lt_or_ge dA β with h | h
    · exact h
    · exfalso
      have harc : arcPos a β = b := arcPos_cyclicSteps a b
      rcases Nat.lt_or_ge β dA with hlt | hge
      · have := no_crossing_before_next P ρ x hvert ha hβpos hlt
        rw [harc] at this; exact this hb
      · have hβeq : β = dA := le_antisymm h hge
        apply hb_ne_bsucc
        rw [← harc, hβeq]; unfold nextCrossing; rw [hdA]
  have ha_ne_bsuccb : a ≠ nextCrossing P ρ x b := by
    rw [← boundarySucc_eq_nextCrossing P ρ x hb]
    exact (boundarySucc_ne_of_neg hvert hb hσb hσa).symm
  have hbagtdB : dB < cyclicSteps b a := by
    rcases Nat.lt_or_ge dB (cyclicSteps b a) with h | h
    · exact h
    · exfalso
      have harc : arcPos b (cyclicSteps b a) = a := arcPos_cyclicSteps b a
      rcases Nat.lt_or_ge (cyclicSteps b a) dB with hlt | hge
      · have := no_crossing_before_next P ρ x hvert hb hbapos hlt
        rw [harc] at this; exact this ha
      · have hbaeq : cyclicSteps b a = dB := le_antisymm h hge
        apply ha_ne_bsuccb
        rw [← harc, hbaeq]; unfold nextCrossing; rw [hdB]
  have hβdBlt : β + dB < n := by omega
  have hY : arcPos b kB = arcPos a (β + kB) := by
    rw [← arcPos_cyclicSteps a b, arcPos_arcPos, hβ]
  rw [hY] at heq
  have hkAn : kA < n := by omega
  have hβkBn : β + kB < n := by omega
  have hoff := arcPos_injOn_lt a hkAn hβkBn heq
  omega

/-- The vertex immediately past a `-1` lobe's last foot is on the POSITIVE side
(`nextCrossing a` has `eSign = 1`, so its end vertex is positive). -/
lemma side_arcPos_succ_pos (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {a : Fin n}
    (ha : a ∈ LineCrossingEdges P ρ x) (hσa : eSign P ρ a = -1) :
    0 < side ρ.r x (P.q (arcPos a (nextCrossDist P ρ x a + 1))) := by
  have hmem : nextCrossing P ρ x a ∈ LineCrossingEdges P ρ x := nextCrossing_mem P ρ x hvert ha
  have hesign : eSign P ρ (nextCrossing P ρ x a) = 1 := by
    rw [eSign_nextCrossing P ρ x hvert ha, hσa]; norm_num
  have h1 := sideAt_one_pos_of_eSign_one P ρ x hvert hmem hesign
  have harceq : arcPos (nextCrossing P ρ x a) 1 = arcPos a (nextCrossDist P ρ x a + 1) := by
    have : nextCrossing P ρ x a = arcPos a (nextCrossDist P ρ x a) := rfl
    rw [this, arcPos_arcPos]
  unfold sideAt at h1
  rw [harceq] at h1
  exact h1

/-- Lower foot interiority. -/
lemma footFirstL_mem_edge (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (L : LowerLobe P ρ x) : footFirstL L ∈ Edge P.q (arcPos L.start 0) := by
  rw [arcPos_zero]
  have hu := crossU_mem_Ioo P ρ x L.start L.cross_first (hvert L.start) (hvert (cyclicNext L.start))
  unfold footFirstL
  exact crossPoint_mem_edge P ρ x L.start ⟨hu.1.le, hu.2.le⟩

lemma footLastL_mem_edge (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (L : LowerLobe P ρ x) : footLastL L ∈ Edge P.q (lobeLastEdgeL L) := by
  have hsp : SpanCrossesSide P ρ x (lobeLastEdgeL L) := L.cross_last
  have hu := crossU_mem_Ioo P ρ x (lobeLastEdgeL L) hsp (hvert _) (hvert _)
  unfold footLastL
  exact crossPoint_mem_edge P ρ x (lobeLastEdgeL L) ⟨hu.1.le, hu.2.le⟩

/-- **Lower clipped segment ⊆ polygon edge.** -/
lemma lobeChainL_seg_subset_edge (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (L : LowerLobe P ρ x) (i : Fin L.len) :
    seg ((lobeChainL L).segA i) ((lobeChainL L).segB i) ⊆ Edge P.q (arcPos L.start i.val) := by
  have hconv : Convex ℝ (Edge P.q (arcPos L.start i.val)) := by
    unfold Edge seg; exact convex_segment _ _
  apply hconv.segment_subset
  · rw [lobeChainL_segA]
    rcases Nat.eq_zero_or_pos i.val with hi0 | hi0
    · have : chainPtL L ⟨i.val, by omega⟩ = footFirstL L := by unfold chainPtL; rw [if_pos hi0]
      rw [this, show arcPos L.start i.val = arcPos L.start 0 from by rw [hi0]]
      exact footFirstL_mem_edge hvert L
    · have hilen : i.val < L.len := i.isLt
      rw [chainPtL_interior L hi0 hilen (by omega)]
      unfold Edge seg
      rw [segment_eq_image_lineMap]
      exact ⟨0, by norm_num, by rw [AffineMap.lineMap_apply_zero]⟩
  · rw [lobeChainL_segB]
    by_cases hilast : i.val + 1 = L.len
    · have : chainPtL L ⟨i.val + 1, by omega⟩ = footLastL L := by
        unfold chainPtL; rw [if_neg (by simp), if_pos hilast]
      rw [this, show arcPos L.start i.val = lobeLastEdgeL L from by unfold lobeLastEdgeL; congr 1; omega]
      exact footLastL_mem_edge hvert L
    · have hilen1 : i.val + 1 < L.len := by have := i.isLt; omega
      rw [chainPtL_interior L (by omega) hilen1 (by omega),
        show arcPos L.start (i.val + 1) = cyclicNext (arcPos L.start i.val) from
          (cyclicNext_arcPos L.start i.val).symm]
      unfold Edge seg
      rw [segment_eq_image_lineMap]
      exact ⟨1, by norm_num, by rw [AffineMap.lineMap_apply_one]⟩

/-- **`lowerLobes_carrier_disjoint`.**  For distinct crossings `a ≠ b` both with `eSign = -1`, the
two lower lobes have disjoint carriers. -/
theorem lowerLobes_carrier_disjoint
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {a b : Fin n}
    (ha : a ∈ LineCrossingEdges P ρ x) (hb : b ∈ LineCrossingEdges P ρ x)
    (hab : a ≠ b) (hσa : eSign P ρ a = -1) (hσb : eSign P ρ b = -1) :
    Disjoint (lobeChainL (lowerLobeOfNeg P ρ x hvert ha hσa)).carrier
             (lobeChainL (lowerLobeOfNeg P ρ x hvert hb hσb)).carrier := by
  classical
  set X := lowerLobeOfNeg P ρ x hvert ha hσa with hXdef
  set Y := lowerLobeOfNeg P ρ x hvert hb hσb with hYdef
  have hXstart : X.start = a := rfl
  have hYstart : Y.start = b := rfl
  have hXlen : X.len = nextCrossDist P ρ x a + 1 := rfl
  have hYlen : Y.len = nextCrossDist P ρ x b + 1 := rfl
  rw [Set.disjoint_left]
  rintro z hzX hzY
  obtain ⟨iX, hziX⟩ := hzX
  obtain ⟨jY, hzjY⟩ := hzY
  have hzeX : z ∈ Edge P.q (arcPos a iX.val) := by
    have := lobeChainL_seg_subset_edge hvert X iX hziX; rwa [hXstart] at this
  have hzeY : z ∈ Edge P.q (arcPos b jY.val) := by
    have := lobeChainL_seg_subset_edge hvert Y jY hzjY; rwa [hYstart] at this
  have hiXlt : iX.val < nextCrossDist P ρ x a + 1 := hXlen ▸ iX.isLt
  have hjYlt : jY.val < nextCrossDist P ρ x b + 1 := hYlen ▸ jY.isLt
  have hiXle : iX.val ≤ nextCrossDist P ρ x a := by omega
  have hjYle : jY.val ≤ nextCrossDist P ρ x b := by omega
  have hidx_ne : arcPos a iX.val ≠ arcPos b jY.val := by
    intro hcoll
    exact lowerLobe_index_disjoint hvert ha hb hab hσa hσb hiXle hjYle hcoll
  set eX := arcPos a iX.val with heX
  set eY := arcPos b jY.val with heY
  have hEC := P.edge_intersection eX eY
  unfold EdgeIntersectionCondition at hEC
  rw [dif_neg hidx_ne] at hEC
  -- carrier points: side ρ.r x z ≤ 0.
  by_cases hnext : cyclicNext eX = eY
  · rw [dif_pos hnext] at hEC
    have hzv : z = P.q eY := by
      have : z ∈ Edge P.q eX ∩ Edge P.q eY := ⟨hzeX, hzeY⟩; rw [hEC] at this; exact this
    have heYsucc : eY = arcPos a (iX.val + 1) := by rw [← hnext, heX, cyclicNext_arcPos]
    by_cases hlast : iX.val = nextCrossDist P ρ x a
    · have hsucc_eq : eY = arcPos a (nextCrossDist P ρ x a + 1) := by rw [heYsucc, hlast]
      have hspos : 0 < side ρ.r x (P.q eY) := by rw [hsucc_eq]; exact side_arcPos_succ_pos hvert ha hσa
      have hsnn : 0 ≤ side (-ρ.r) x z := carrierL_negside_nonneg X ⟨iX, hziX⟩
      rw [negside_eq, hzv] at hsnn; linarith
    · have hiX1 : iX.val + 1 ≤ nextCrossDist P ρ x a := by omega
      exact lowerLobe_index_disjoint hvert ha hb hab hσa hσb hiX1 hjYle (by rw [← heYsucc])
  · rw [dif_neg hnext] at hEC
    by_cases hprev : cyclicNext eY = eX
    · rw [dif_pos hprev] at hEC
      have hzv : z = P.q eX := by
        have : z ∈ Edge P.q eX ∩ Edge P.q eY := ⟨hzeX, hzeY⟩; rw [hEC] at this; exact this
      have heXsucc : eX = arcPos b (jY.val + 1) := by rw [← hprev, heY, cyclicNext_arcPos]
      by_cases hlast : jY.val = nextCrossDist P ρ x b
      · have hsucc_eq : eX = arcPos b (nextCrossDist P ρ x b + 1) := by rw [heXsucc, hlast]
        have hspos : 0 < side ρ.r x (P.q eX) := by rw [hsucc_eq]; exact side_arcPos_succ_pos hvert hb hσb
        have hsnn : 0 ≤ side (-ρ.r) x z := carrierL_negside_nonneg Y ⟨jY, hzjY⟩
        rw [negside_eq, hzv] at hsnn; linarith
      · have hjY1 : jY.val + 1 ≤ nextCrossDist P ρ x b := by omega
        exact lowerLobe_index_disjoint hvert ha hb hab hσa hσb hiXle hjY1 (heX.symm.trans heXsucc)
    · rw [dif_neg hprev] at hEC
      exact (Set.disjoint_left.mp hEC hzeX) hzeY

end

/-! ## Axiom audit (clean-3 expected: `propext`, `Classical.choice`, `Quot.sound`) -/

section Audit
open ProofsInTheBook.ZinanCh36SuccBij
#print axioms boundarySucc_injOn
#print axioms boundarySuccSub_injective
#print axioms boundarySucc_cover
#print axioms boundarySucc_orbit_covers
#print axioms boundarySucc_cycle_connected_unconditional
#print axioms upperLobe_index_disjoint
#print axioms upperLobes_carrier_disjoint
#print axioms lowerLobe_index_disjoint
#print axioms lowerLobes_carrier_disjoint
end Audit

end ProofsInTheBook.ZinanCh36SuccBij
