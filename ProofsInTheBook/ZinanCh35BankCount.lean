import ProofsInTheBook.ZinanCh35OuterSlack

/-!
# Chapter 35, Step 6: the boundary-bank face count (`BoundaryBankCount`)

This file discharges the single remaining residual of Chapter 35,
`BoundaryBankCount hNT : numCycles (M.φ * outerDualAlpha hNT) = M.V − B + 2`
(`B = outerCycle.length`), **unconditionally**, via Route B (swap-peeling).

## The route

By `ZinanCh35OuterSlack.phi_outerDualAlpha_eq_sigma_outerTau` we have
`M.φ * outerDualAlpha hNT = M.σ * outerTau hNT`, where `outerTau` is the identity off
`OuterDel` and equals `M.α` on `OuterDel` — that is, the `B` disjoint outer transpositions
`(q i, r i)`, with `q i := outerCycle.darts.get i` and `r i := M.α (q i)`.

We realise `outerTau` as a product of these `B` swaps, ordered so that the first `B−1`
each **merge** two distinct `σ`-cycles and the last one **splits** a cycle:

```
M.σ  →(B−1 merge swaps)→  pMerge   [count V − (B−1)]   →(1 split swap)→  P  [count V − B + 2]
```

The load-bearing invariant is a `SameCycle` characterization of the partial products
`pPrefix k := M.σ * (mergePairs.take k swaps)`: after `k` merges the darts
`q 0, r 0, …, q k` all lie in one "growing" cycle, while every other `q`/`r` stays put.
We prove it by induction on `k` using the merge engine
`PermTranspositionCycleCount.sameCycle_mul_swap_iff_mergeRel_of_not_sameCycle`.

No `sorry` / `axiom` / `admit` / `native_decide` in this file.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35BankCount

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35OuterDual
open ProofsInTheBook.ZinanCh35OuterSlack
open Equiv Equiv.Perm

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}

variable {hNT : NearTriangulation M}

/-! ## Setup: boundary length, boundary darts, and their `α`-partners. -/

/-- The boundary length `B`. -/
local notation3 "B" => hNT.outerCycle.length

/-- The `i`-th boundary dart `q i`. -/
noncomputable def qd (hNT : NearTriangulation M) (i : Fin hNT.outerCycle.length) : D :=
  hNT.outerCycle.darts.get ⟨i.1, by simpa [BoundaryCycle.length] using i.2⟩

/-- The `α`-partner `r i := M.α (q i)`. -/
noncomputable def rd (hNT : NearTriangulation M) (i : Fin hNT.outerCycle.length) : D :=
  M.α (qd hNT i)

/-- Cyclic successor index on `Fin B`. -/
noncomputable def nextIdx (hNT : NearTriangulation M) (i : Fin hNT.outerCycle.length) :
    Fin hNT.outerCycle.length :=
  ⟨(i.1 + 1) % hNT.outerCycle.length,
    Nat.mod_lt _ (by simpa [BoundaryCycle.length] using hNT.outerCycle.darts_length_pos)⟩

lemma nextIdx_val (i : Fin hNT.outerCycle.length) :
    (nextIdx hNT i).1 = (i.1 + 1) % hNT.outerCycle.length := rfl

/-- `q i` is a boundary dart. -/
lemma qd_mem (i : Fin hNT.outerCycle.length) : qd hNT i ∈ hNT.outerCycle.darts := by
  unfold qd
  exact List.get_mem _ _

/-- `q i ∈ OuterDel`. -/
lemma qd_mem_outerDel (i : Fin hNT.outerCycle.length) : qd hNT i ∈ OuterDel hNT := by
  rw [mem_outerDel_iff]; exact Or.inl (qd_mem i)

/-- `r i ∈ OuterDel`. -/
lemma rd_mem_outerDel (i : Fin hNT.outerCycle.length) : rd hNT i ∈ OuterDel hNT := by
  rw [mem_outerDel_iff]; right
  show M.α (M.α (qd hNT i)) ∈ hNT.outerCycle.darts
  rw [M.alpha_alpha]; exact qd_mem i

/-! ### Injectivity / disjointness of the `q`/`r` family. -/

lemma qd_inj {i j : Fin hNT.outerCycle.length} (h : qd hNT i = qd hNT j) : i = j := by
  unfold qd at h
  have := (hNT.outerCycle.darts_nodup.getElem_inj_iff).mp h
  exact Fin.ext (by simpa using this)

lemma qd_eq_iff (i j : Fin hNT.outerCycle.length) : qd hNT i = qd hNT j ↔ i = j :=
  ⟨qd_inj, fun h => by rw [h]⟩

lemma rd_inj {i j : Fin hNT.outerCycle.length} (h : rd hNT i = rd hNT j) : i = j :=
  qd_inj (M.α.injective h)

lemma qd_ne_rd (i j : Fin hNT.outerCycle.length) : qd hNT i ≠ rd hNT j := by
  intro h
  -- q i ∈ darts, r j = α (q j) ∉ darts (partner of boundary dart).
  have hmem : M.α (qd hNT j) ∈ hNT.outerCycle.darts := by
    show rd hNT j ∈ hNT.outerCycle.darts
    rw [← h]; exact qd_mem i
  exact alpha_notMem_darts_of_mem (hNT := hNT) (qd_mem j) hmem

lemma rd_ne_qd (i j : Fin hNT.outerCycle.length) : rd hNT i ≠ qd hNT j :=
  fun h => qd_ne_rd j i h.symm

lemma qd_ne_rd_self (i : Fin hNT.outerCycle.length) : qd hNT i ≠ rd hNT i := qd_ne_rd i i

/-! ### The key dynamical fact: `M.σ (r j) = q (next j)`. -/

/-- `M.σ (r i) = q (next i)`: because `σ = φ ∘ α` and the boundary darts cycle under `φ`. -/
lemma sigma_rd_eq_qd_next (i : Fin hNT.outerCycle.length) :
    M.σ (rd hNT i) = qd hNT (nextIdx hNT i) := by
  -- σ (α (q i)) = φ (q i) = darts.get (cyclicNext i)
  have hσ : M.σ (rd hNT i) = M.φ (qd hNT i) := by
    show M.σ (M.α (qd hNT i)) = M.φ (qd hNT i)
    show M.σ (M.α (qd hNT i)) = (M.σ * M.α) (qd hNT i)
    rw [Equiv.Perm.mul_apply]
  rw [hσ]
  -- consecutive_phi: darts.get (cyclicNext i₀) = φ (darts.get i₀)
  set i₀ : Fin hNT.outerCycle.darts.length :=
    ⟨i.1, by simpa [BoundaryCycle.length] using i.2⟩ with hi₀
  have hcp := hNT.outerCycle.consecutive_phi i₀
  show M.φ (hNT.outerCycle.darts.get i₀) = qd hNT (nextIdx hNT i)
  rw [← hcp]
  -- both sides are `darts.get` at index (i+1) % B
  unfold qd nextIdx
  congr 1

/-! ### Base case: distinct boundary darts lie in distinct `σ`-cycles. -/

/-- `M.σ.SameCycle a b` is `M.tail a = M.tail b`. -/
lemma sigma_sameCycle_iff_tail (a b : D) :
    M.σ.SameCycle a b ↔ M.tail a = M.tail b := by
  show M.σ.SameCycle a b ↔
    (Quotient.mk (cycleSetoid M.σ) a : Quotient (cycleSetoid M.σ)) = Quotient.mk _ b
  rw [Quotient.eq]
  rfl

/-- Distinct boundary darts are in distinct `σ`-cycles: `σ.SameCycle (q i) (q j) ↔ i = j`. -/
lemma sigma_sameCycle_qd_qd (i j : Fin hNT.outerCycle.length) :
    M.σ.SameCycle (qd hNT i) (qd hNT j) ↔ i = j := by
  rw [sigma_sameCycle_iff_tail]
  constructor
  · intro h
    have := hNT.outerCycle.tail_injective_on_darts hNT.outer_simple (qd_mem i) (qd_mem j) h
    exact qd_inj this
  · intro h; rw [h]

/-! ### The merge-pair list and the partial products. -/

/-- The embedding `Fin (B−1) ↪ Fin B`. -/
noncomputable def emb (hNT : NearTriangulation M) (j : Fin (hNT.outerCycle.length - 1)) :
    Fin hNT.outerCycle.length :=
  ⟨j.1, by have := j.2; omega⟩

/-- The ordered list of the first `B−1` outer transposition pairs `(q j, r j)`. -/
noncomputable def mergePairs (hNT : NearTriangulation M) : List (D × D) :=
  (List.finRange (hNT.outerCycle.length - 1)).map (fun j => (qd hNT (emb hNT j), rd hNT (emb hNT j)))

/-- The partial product permutation after the first `k` merge swaps. -/
noncomputable def pPrefix (hNT : NearTriangulation M) (k : ℕ) : Equiv.Perm D :=
  M.σ * (((mergePairs hNT).take k).map (fun w => Equiv.swap w.1 w.2)).prod

lemma pPrefix_zero : pPrefix hNT 0 = M.σ := by simp [pPrefix]

/-- The dart at block position `m < B` (the `m`-th `q`). -/
lemma mergePairs_get_fst (k : ℕ) (hk : k < hNT.outerCycle.length - 1) :
    (mergePairs hNT).get ⟨k, by simpa [mergePairs] using hk⟩
      = (qd hNT ⟨k, by omega⟩, rd hNT ⟨k, by omega⟩) := by
  unfold mergePairs
  rw [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
  rfl

/-- Length of `mergePairs` is `B − 1`. -/
lemma mergePairs_length : (mergePairs hNT).length = hNT.outerCycle.length - 1 := by
  simp [mergePairs]

/-- One-step recurrence for the partial products: appending the `k`-th merge swap. -/
lemma pPrefix_succ (k : ℕ) (hk : k < hNT.outerCycle.length - 1) :
    pPrefix hNT (k + 1)
      = pPrefix hNT k * Equiv.swap (qd hNT ⟨k, by omega⟩) (rd hNT ⟨k, by omega⟩) := by
  unfold pPrefix
  have hlen : k < (mergePairs hNT).length := by rw [mergePairs_length]; exact hk
  -- take (k+1) = take k ++ [get k]
  have htake : (mergePairs hNT).take (k + 1)
      = (mergePairs hNT).take k ++ [(mergePairs hNT).get ⟨k, hlen⟩] := by
    rw [List.get_eq_getElem]
    exact List.take_succ_eq_append_getElem hlen
  rw [htake, List.map_append, List.prod_append, mergePairs_get_fst k hk]
  simp [mul_assoc]

/-! ### `nextIdx` arithmetic. -/

/-- For a non-final index, `nextIdx` increments the value (no wraparound). -/
lemma nextIdx_val_of_lt {i : Fin hNT.outerCycle.length} (hi : i.1 < hNT.outerCycle.length - 1) :
    (nextIdx hNT i).1 = i.1 + 1 := by
  rw [nextIdx_val, Nat.mod_eq_of_lt (by omega)]

/-- `nextIdx` is injective. -/
lemma nextIdx_inj {i j : Fin hNT.outerCycle.length} (h : nextIdx hNT i = nextIdx hNT j) :
    i = j := by
  have hpos : 0 < hNT.outerCycle.length := by
    simpa [BoundaryCycle.length] using hNT.outerCycle.darts_length_pos
  have hval := congrArg Fin.val h
  rw [nextIdx_val, nextIdx_val] at hval
  apply Fin.ext
  have hi := i.2; have hj := j.2
  -- both (i+1) and (j+1) lie in [1, B]; equal mod B ⟹ equal
  rcases Nat.lt_or_ge (i.1 + 1) hNT.outerCycle.length with hi1 | hi1
  · rw [Nat.mod_eq_of_lt hi1] at hval
    rcases Nat.lt_or_ge (j.1 + 1) hNT.outerCycle.length with hj1 | hj1
    · rw [Nat.mod_eq_of_lt hj1] at hval; omega
    · have : j.1 + 1 = hNT.outerCycle.length := by omega
      rw [this, Nat.mod_self] at hval; omega
  · have hib : i.1 + 1 = hNT.outerCycle.length := by omega
    rw [hib, Nat.mod_self] at hval
    rcases Nat.lt_or_ge (j.1 + 1) hNT.outerCycle.length with hj1 | hj1
    · rw [Nat.mod_eq_of_lt hj1] at hval; omega
    · have : j.1 + 1 = hNT.outerCycle.length := by omega
      omega

/-! ### The running invariant (THE key — proved by simultaneous induction on `k`). -/

/-- The simultaneous invariant after `k` merges (`q i` joins the block once `i.1 ≤ k`). -/
lemma bankInvariant :
    ∀ k : ℕ, k + 1 ≤ hNT.outerCycle.length →
      (∀ i j : Fin hNT.outerCycle.length,
          (pPrefix hNT k).SameCycle (qd hNT i) (qd hNT j)
            ↔ i = j ∨ (i.1 ≤ k ∧ j.1 ≤ k)) ∧
      (∀ i j : Fin hNT.outerCycle.length,
          (pPrefix hNT k).SameCycle (qd hNT i) (rd hNT j)
            ↔ i = nextIdx hNT j ∨ (i.1 ≤ k ∧ (nextIdx hNT j).1 ≤ k)) ∧
      (∀ i j : Fin hNT.outerCycle.length,
          (pPrefix hNT k).SameCycle (rd hNT i) (rd hNT j)
            ↔ i = j ∨ ((nextIdx hNT i).1 ≤ k ∧ (nextIdx hNT j).1 ≤ k)) := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [pPrefix_zero]
      refine ⟨?_, ?_, ?_⟩
      · -- q-q base: σ.SameCycle (q i)(q j) ↔ i = j
        intro i j
        rw [sigma_sameCycle_qd_qd]
        constructor
        · exact Or.inl
        · rintro (h | ⟨hi, hj⟩)
          · exact h
          · exact Fin.ext (by omega)
      · -- q-r base: σ.SameCycle (q i)(r j) ↔ i = next j
        intro i j
        have hr : M.σ.SameCycle (rd hNT j) (qd hNT (nextIdx hNT j)) := by
          rw [← sigma_rd_eq_qd_next]; exact ⟨1, by simp⟩
        constructor
        · intro h
          have : M.σ.SameCycle (qd hNT i) (qd hNT (nextIdx hNT j)) := h.trans hr
          left; exact (sigma_sameCycle_qd_qd i (nextIdx hNT j)).mp this
        · rintro (h | ⟨hi, hcon⟩)
          · subst h; exact hr.symm
          · -- i ≤ 0 ∧ (next j) ≤ 0 ⟹ i = next j
            have : i = nextIdx hNT j := Fin.ext (by omega)
            subst this; exact hr.symm
      · -- r-r base
        intro i j
        have hri : M.σ.SameCycle (rd hNT i) (qd hNT (nextIdx hNT i)) := by
          rw [← sigma_rd_eq_qd_next]; exact ⟨1, by simp⟩
        have hrj : M.σ.SameCycle (rd hNT j) (qd hNT (nextIdx hNT j)) := by
          rw [← sigma_rd_eq_qd_next]; exact ⟨1, by simp⟩
        constructor
        · intro h
          have : M.σ.SameCycle (qd hNT (nextIdx hNT i)) (qd hNT (nextIdx hNT j)) :=
            (hri.symm.trans h).trans hrj
          left; exact nextIdx_inj ((sigma_sameCycle_qd_qd _ _).mp this)
        · rintro (h | ⟨hci, hcj⟩)
          · subst h; exact SameCycle.rfl
          · have : nextIdx hNT i = nextIdx hNT j := Fin.ext (by omega)
            rw [nextIdx_inj this]
  | succ k ih =>
      intro hk1
      have hkB1 : k < hNT.outerCycle.length - 1 := by omega
      have hkB : k < hNT.outerCycle.length := by omega
      obtain ⟨ihqq, ihqr, ihrr⟩ := ih (by omega)
      set a := qd hNT ⟨k, hkB⟩ with ha
      set b := rd hNT ⟨k, hkB⟩ with hb
      have hnextk : (nextIdx hNT ⟨k, hkB⟩).1 = k + 1 := nextIdx_val_of_lt (by simpa using hkB1)
      have hak : (⟨k, hkB⟩ : Fin hNT.outerCycle.length).1 = k := rfl
      have hnsc : ¬ (pPrefix hNT k).SameCycle a b := by
        rw [ha, hb, ihqr ⟨k, hkB⟩ ⟨k, hkB⟩]
        rintro (hcon | ⟨_, hcon⟩)
        · have := congrArg Fin.val hcon; rw [hnextk] at this; simp at this
        · rw [hnextk] at hcon; omega
      have hstep := pPrefix_succ (hNT := hNT) k hkB1
      have engine : ∀ x y : D,
          (pPrefix hNT (k + 1)).SameCycle x y ↔
            (pPrefix hNT k).SameCycle x y ∨
              ((pPrefix hNT k).SameCycle x a ∧ (pPrefix hNT k).SameCycle y b) ∨
              ((pPrefix hNT k).SameCycle x b ∧ (pPrefix hNT k).SameCycle y a) := by
        intro x y
        rw [hstep]
        exact PermTranspositionCycleCount.sameCycle_mul_swap_iff_mergeRel_of_not_sameCycle
          (pPrefix hNT k) hnsc (x := x) (y := y)
      -- abbreviation: q i ~ a (= q ⟨k⟩) iff i.1 ≤ k
      have hqa : ∀ i : Fin hNT.outerCycle.length,
          (pPrefix hNT k).SameCycle (qd hNT i) a ↔ i.1 ≤ k := by
        intro i; rw [ha, ihqq i ⟨k, hkB⟩]
        constructor
        · rintro (h | ⟨hi, _⟩)
          · exact le_of_eq (congrArg Fin.val h)
          · exact hi
        · intro hi
          rcases Nat.lt_or_ge i.1 k with h | h
          · exact Or.inr ⟨by omega, le_refl k⟩
          · exact Or.inl (Fin.ext (le_antisymm hi h))
      -- q i ~ b (= r ⟨k⟩) iff i = next ⟨k⟩ (= ⟨k+1⟩) [block bound k+1 ≤ k impossible]
      have hqb : ∀ i : Fin hNT.outerCycle.length,
          (pPrefix hNT k).SameCycle (qd hNT i) b ↔ i.1 = k + 1 := by
        intro i; rw [hb, ihqr i ⟨k, hkB⟩, hnextk]
        constructor
        · rintro (h | ⟨_, hcon⟩)
          · have := congrArg Fin.val h; rw [hnextk] at this; exact this
          · omega
        · intro hi; left; exact Fin.ext (by rw [hnextk]; exact hi)
      -- r i ~ b (= r ⟨k⟩) iff i = ⟨k⟩, i.e. (next i).1 = k+1
      have hrb : ∀ i : Fin hNT.outerCycle.length,
          (pPrefix hNT k).SameCycle (rd hNT i) b ↔ (nextIdx hNT i).1 = k + 1 := by
        intro i; rw [hb, ihrr i ⟨k, hkB⟩, hnextk]
        constructor
        · rintro (h | ⟨hi, hcon⟩)
          · subst h; rw [hnextk]
          · omega
        · intro hi; left; exact nextIdx_inj (Fin.ext (by rw [hnextk]; omega))
      refine ⟨?_, ?_, ?_⟩
      · -- q-q at k+1
        intro i j
        rw [engine (qd hNT i) (qd hNT j), ihqq i j, hqa i, hqb j, hqb i, hqa j]
        constructor
        · rintro (h | ⟨hi, hj⟩ | ⟨hi, hj⟩)
          · rcases h with h | ⟨hi, hj⟩
            · exact Or.inl h
            · exact Or.inr ⟨by omega, by omega⟩
          · -- i ≤ k, j.1 = k+1
            right; refine ⟨by omega, by omega⟩
          · right; refine ⟨by omega, by omega⟩
        · rintro (h | ⟨hi, hj⟩)
          · exact Or.inl (Or.inl h)
          · -- i ≤ k+1, j ≤ k+1
            rcases Nat.lt_or_ge i.1 (k+1) with hik | hik
            · rcases Nat.lt_or_ge j.1 (k+1) with hjk | hjk
              · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
              · -- j.1 = k+1, i ≤ k
                right; left; exact ⟨by omega, by omega⟩
            · -- i.1 = k+1
              rcases Nat.lt_or_ge j.1 (k+1) with hjk | hjk
              · right; right; exact ⟨by omega, by omega⟩
              · -- both = k+1 ⟹ i = j
                exact Or.inl (Or.inl (Fin.ext (by omega)))
      · -- q-r at k+1
        intro i j
        rw [engine (qd hNT i) (rd hNT j), ihqr i j, hqa i, hrb j, hqb i]
        -- (pPrefix k).SameCycle (r j) a = (q-a symm): r j ~ q⟨k⟩ ↔ (next j).1 ≤ k
        have hrja : (pPrefix hNT k).SameCycle (rd hNT j) a ↔ (nextIdx hNT j).1 ≤ k := by
          rw [ha, Equiv.Perm.sameCycle_comm, ihqr ⟨k, hkB⟩ j]
          constructor
          · rintro (h | ⟨_, hj⟩)
            · have : (nextIdx hNT j).1 = k := (congrArg Fin.val h).symm
              omega
            · exact hj
          · intro hj
            rcases Nat.lt_or_ge (nextIdx hNT j).1 k with h | h
            · exact Or.inr ⟨by omega, by omega⟩
            · left; exact Fin.ext (by omega)
        rw [hrja]
        constructor
        · rintro (h | ⟨hi, hj⟩ | ⟨hi, hj⟩)
          · rcases h with h | ⟨hi, hj⟩
            · exact Or.inl h
            · exact Or.inr ⟨by omega, by omega⟩
          · -- i ≤ k ∧ (next j).1 ≤ k+1
            right; exact ⟨by omega, by omega⟩
          · -- i.1 = k+1 ∧ (next j).1 ≤ k
            right; exact ⟨by omega, by omega⟩
        · rintro (h | ⟨hi, hnj⟩)
          · exact Or.inl (Or.inl h)
          · rcases Nat.lt_or_ge i.1 (k+1) with hik | hik
            · rcases Nat.lt_or_ge (nextIdx hNT j).1 (k+1) with hnjk | hnjk
              · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
              · right; left; exact ⟨by omega, by omega⟩
            · -- i.1 = k+1
              rcases Nat.lt_or_ge (nextIdx hNT j).1 (k+1) with hnjk | hnjk
              · -- (next j) ≤ k
                right; right; exact ⟨by omega, by omega⟩
              · -- i.1 = k+1 and (next j).1 = k+1 ⟹ i = next j
                exact Or.inl (Or.inl (Fin.ext (by omega)))
      · -- r-r at k+1
        intro i j
        rw [engine (rd hNT i) (rd hNT j), ihrr i j, hrb j, hrb i]
        have hria : (pPrefix hNT k).SameCycle (rd hNT i) a ↔ (nextIdx hNT i).1 ≤ k := by
          rw [ha, Equiv.Perm.sameCycle_comm, ihqr ⟨k, hkB⟩ i]
          constructor
          · rintro (h | ⟨_, hi⟩)
            · have := congrArg Fin.val h; omega
            · exact hi
          · intro hi
            rcases Nat.lt_or_ge (nextIdx hNT i).1 k with h | h
            · exact Or.inr ⟨by omega, by omega⟩
            · left; exact Fin.ext (by omega)
        have hrja : (pPrefix hNT k).SameCycle (rd hNT j) a ↔ (nextIdx hNT j).1 ≤ k := by
          rw [ha, Equiv.Perm.sameCycle_comm, ihqr ⟨k, hkB⟩ j]
          constructor
          · rintro (h | ⟨_, hj⟩)
            · have := congrArg Fin.val h; omega
            · exact hj
          · intro hj
            rcases Nat.lt_or_ge (nextIdx hNT j).1 k with h | h
            · exact Or.inr ⟨by omega, by omega⟩
            · left; exact Fin.ext (by omega)
        rw [hria, hrja]
        constructor
        · rintro (h | ⟨hi, hj⟩ | ⟨hi, hj⟩)
          · rcases h with h | ⟨hi, hj⟩
            · exact Or.inl h
            · exact Or.inr ⟨by omega, by omega⟩
          · right; exact ⟨by omega, by omega⟩
          · right; exact ⟨by omega, by omega⟩
        · rintro (h | ⟨hni, hnj⟩)
          · exact Or.inl (Or.inl h)
          · rcases Nat.lt_or_ge (nextIdx hNT i).1 (k+1) with hnik | hnik
            · rcases Nat.lt_or_ge (nextIdx hNT j).1 (k+1) with hnjk | hnjk
              · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
              · right; left; exact ⟨by omega, by omega⟩
            · rcases Nat.lt_or_ge (nextIdx hNT j).1 (k+1) with hnjk | hnjk
              · right; right; exact ⟨by omega, by omega⟩
              · -- both next = k+1 ⟹ i = j
                have : nextIdx hNT i = nextIdx hNT j := Fin.ext (by omega)
                exact Or.inl (Or.inl (nextIdx_inj this))

/-! ### Counts: the merges, the final split, and assembly. -/

/-- The fully-merged permutation after all `B−1` merges. -/
noncomputable def pMerge (hNT : NearTriangulation M) : Equiv.Perm D :=
  pPrefix hNT (hNT.outerCycle.length - 1)

/-- The `B−1` merge swaps each merge two distinct cycles of the running product. -/
lemma mergePairs_merge_condition :
    ∀ j : Fin (mergePairs hNT).length,
      ((mergePairs hNT).get j).1 ≠ ((mergePairs hNT).get j).2 ∧
        ¬ (M.σ * (((mergePairs hNT).take j).map (fun w => Equiv.swap w.1 w.2)).prod).SameCycle
            ((mergePairs hNT).get j).1 ((mergePairs hNT).get j).2 := by
  intro j
  have he : (mergePairs hNT).length = hNT.outerCycle.length - 1 := mergePairs_length
  have hjlen : (j : ℕ) < hNT.outerCycle.length - 1 := by have := j.2; omega
  have hjB : (j : ℕ) < hNT.outerCycle.length := by omega
  rw [mergePairs_get_fst (j : ℕ) hjlen]
  -- the running product is pPrefix j
  have hpp : M.σ * (((mergePairs hNT).take (j : ℕ)).map (fun w => Equiv.swap w.1 w.2)).prod
      = pPrefix hNT (j : ℕ) := rfl
  refine ⟨?_, ?_⟩
  · -- q ⟨j⟩ ≠ r ⟨j⟩
    exact qd_ne_rd_self ⟨(j : ℕ), hjB⟩
  · rw [hpp]
    obtain ⟨_, ihqr, _⟩ := bankInvariant (hNT := hNT) (j : ℕ) (by omega)
    rw [ihqr ⟨(j : ℕ), hjB⟩ ⟨(j : ℕ), hjB⟩]
    have hnext : (nextIdx hNT ⟨(j : ℕ), hjB⟩).1 = (j : ℕ) + 1 :=
      nextIdx_val_of_lt (by simpa using hjlen)
    rintro (hcon | ⟨_, hcon⟩)
    · have := congrArg Fin.val hcon; rw [hnext] at this; simp at this
    · rw [hnext] at hcon; omega

/-- After all `B−1` merges, the cycle count is `V − (B−1)`. -/
lemma numCycles_pMerge_add :
    _root_.numCycles (pMerge hNT) + (hNT.outerCycle.length - 1) = M.V := by
  have hmerge := CombMap.CutCapCount.numCycles_mul_listSwap_merges M.σ (mergePairs hNT)
    (mergePairs_merge_condition (hNT := hNT))
  rw [mergePairs_length] at hmerge
  -- pMerge = M.σ * swapProd mergePairs = pPrefix (B-1) (since take (B-1) = whole list)
  have hpm : pMerge hNT = M.σ * ((mergePairs hNT).map (fun w => Equiv.swap w.1 w.2)).prod := by
    unfold pMerge pPrefix
    rw [List.take_of_length_le (by rw [mergePairs_length])]
  rw [hpm, hmerge, M.V_eq_numCycles]

lemma length_pos' : 0 < hNT.outerCycle.length :=
  hNT.outerCycle.darts_length_pos

/-- The last boundary pair `(q last, r last)`, `last = ⟨B−1⟩`. -/
noncomputable def lastIdx (hNT : NearTriangulation M) : Fin hNT.outerCycle.length :=
  ⟨hNT.outerCycle.length - 1, by have := length_pos' (hNT := hNT); omega⟩

/-- In `pMerge`, the last pair lies in the same cycle (so the closing swap splits). -/
lemma pMerge_lastPair_sameCycle :
    (pMerge hNT).SameCycle (qd hNT (lastIdx hNT)) (rd hNT (lastIdx hNT)) := by
  unfold pMerge
  have hBpos : 0 < hNT.outerCycle.length := hNT.outerCycle.darts_length_pos
  obtain ⟨_, ihqr, _⟩ := bankInvariant (hNT := hNT) (hNT.outerCycle.length - 1) (by omega)
  rw [ihqr (lastIdx hNT) (lastIdx hNT)]
  -- last.1 = B-1 ≤ B-1 and (next last).1 = 0 ≤ B-1
  right
  have hnl : (nextIdx hNT (lastIdx hNT)).1 = 0 := by
    rw [nextIdx_val]
    show ((hNT.outerCycle.length - 1) + 1) % hNT.outerCycle.length = 0
    rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
  refine ⟨?_, ?_⟩
  · show (hNT.outerCycle.length - 1) ≤ hNT.outerCycle.length - 1; exact le_refl _
  · rw [hnl]; exact Nat.zero_le _

/-! ### The outer transposition product equals `outerTau`. -/

/-- Evaluation of the disjoint-swap product at a `q`-dart whose index is in the (nodup) list. -/
lemma listSwapQR_apply_qd (m : Fin hNT.outerCycle.length) :
    ∀ L : List (Fin hNT.outerCycle.length), L.Nodup → m ∈ L →
      ((L.map (fun i => (qd hNT i, rd hNT i))).map (fun w => Equiv.swap w.1 w.2)).prod
          (qd hNT m) = rd hNT m := by
  intro L
  induction L with
  | nil => intro _ hm; simp only [List.not_mem_nil] at hm
  | cons c t ih =>
      intro hnd hm
      rw [List.map_cons, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
      have hndt := (List.nodup_cons.mp hnd)
      by_cases hmt : m ∈ t
      · -- m ∈ t, so c ≠ m (nodup); tail moves q m ↦ r m, head fixes r m
        have hcm : c ≠ m := fun h => hndt.1 (h ▸ hmt)
        rw [ih hndt.2 hmt]
        show Equiv.swap (qd hNT c) (rd hNT c) (rd hNT m) = rd hNT m
        rw [Equiv.swap_apply_of_ne_of_ne (rd_ne_qd m c) (fun h => hcm (rd_inj h).symm)]
      · -- m = c
        have hmc : m = c := by
          rcases List.mem_cons.mp hm with h | h
          · exact h
          · exact absurd h hmt
        subst hmc
        -- tail fixes q m
        have htail : ((t.map (fun i => (qd hNT i, rd hNT i))).map (fun w => Equiv.swap w.1 w.2)).prod
            (qd hNT m) = qd hNT m := by
          apply CombMap.CutCapCount.listSwap_prod_apply_of_notMem
          intro w hw
          rw [List.mem_map] at hw
          obtain ⟨i, hi, hwi⟩ := hw
          have hineq : i ≠ m := fun h => hmt (h ▸ hi)
          subst hwi
          exact ⟨fun h => hineq (qd_inj h).symm, qd_ne_rd m i⟩
        rw [htail]
        show Equiv.swap (qd hNT m) (rd hNT m) (qd hNT m) = rd hNT m
        rw [Equiv.swap_apply_left]

/-- Evaluation of the disjoint-swap product at an `r`-dart whose index is in the (nodup) list. -/
lemma listSwapQR_apply_rd (m : Fin hNT.outerCycle.length) :
    ∀ L : List (Fin hNT.outerCycle.length), L.Nodup → m ∈ L →
      ((L.map (fun i => (qd hNT i, rd hNT i))).map (fun w => Equiv.swap w.1 w.2)).prod
          (rd hNT m) = qd hNT m := by
  intro L
  induction L with
  | nil => intro _ hm; simp only [List.not_mem_nil] at hm
  | cons c t ih =>
      intro hnd hm
      rw [List.map_cons, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
      have hndt := (List.nodup_cons.mp hnd)
      by_cases hmt : m ∈ t
      · have hcm : c ≠ m := fun h => hndt.1 (h ▸ hmt)
        rw [ih hndt.2 hmt]
        show Equiv.swap (qd hNT c) (rd hNT c) (qd hNT m) = qd hNT m
        rw [Equiv.swap_apply_of_ne_of_ne (fun h => hcm (qd_inj h).symm) (qd_ne_rd m c)]
      · have hmc : m = c := by
          rcases List.mem_cons.mp hm with h | h
          · exact h
          · exact absurd h hmt
        subst hmc
        have htail : ((t.map (fun i => (qd hNT i, rd hNT i))).map (fun w => Equiv.swap w.1 w.2)).prod
            (rd hNT m) = rd hNT m := by
          apply CombMap.CutCapCount.listSwap_prod_apply_of_notMem
          intro w hw
          rw [List.mem_map] at hw
          obtain ⟨i, hi, hwi⟩ := hw
          have hineq : i ≠ m := fun h => hmt (h ▸ hi)
          subst hwi
          exact ⟨rd_ne_qd m i, fun h => hineq (rd_inj h).symm⟩
        rw [htail]
        show Equiv.swap (qd hNT m) (rd hNT m) (rd hNT m) = qd hNT m
        rw [Equiv.swap_apply_right]

/-- Evaluation at a dart that is neither a `q`- nor `r`-dart of the list: it is fixed. -/
lemma listSwapQR_apply_other (d : D)
    (L : List (Fin hNT.outerCycle.length))
    (hd : ∀ i ∈ L, d ≠ qd hNT i ∧ d ≠ rd hNT i) :
    ((L.map (fun i => (qd hNT i, rd hNT i))).map (fun w => Equiv.swap w.1 w.2)).prod d = d := by
  apply CombMap.CutCapCount.listSwap_prod_apply_of_notMem
  intro w hw
  rw [List.mem_map] at hw
  obtain ⟨i, hi, hwi⟩ := hw
  subst hwi
  exact hd i hi

/-- A boundary dart is some `qd m`. -/
lemma exists_qd_of_mem_darts {d : D} (hd : d ∈ hNT.outerCycle.darts) :
    ∃ m : Fin hNT.outerCycle.length, d = qd hNT m := by
  obtain ⟨n, hgn⟩ := List.get_of_mem hd
  refine ⟨⟨n.1, by simpa [BoundaryCycle.length] using n.2⟩, ?_⟩
  unfold qd; rw [← hgn]

/-- The full pair list over all `B` indices. -/
noncomputable def allPairs (hNT : NearTriangulation M) : List (D × D) :=
  (List.finRange hNT.outerCycle.length).map (fun i => (qd hNT i, rd hNT i))

/-- `outerTau` is the product of the `B` disjoint outer transpositions. -/
lemma outerTau_eq_swapProd :
    outerTau hNT = ((allPairs hNT).map (fun w => Equiv.swap w.1 w.2)).prod := by
  have hnd : (List.finRange hNT.outerCycle.length).Nodup := List.nodup_finRange _
  ext d
  unfold allPairs
  by_cases hd : d ∈ OuterDel hNT
  · rw [outerTau_eq_alpha_of_mem (hNT := hNT) hd]
    rw [mem_outerDel_iff] at hd
    rcases hd with hdd | hαd
    · -- d = qd m, α d = rd m
      obtain ⟨m, rfl⟩ := exists_qd_of_mem_darts (hNT := hNT) hdd
      rw [listSwapQR_apply_qd m _ hnd (List.mem_finRange m)]; rfl
    · -- α d ∈ darts ⟹ d = rd m (where α d = qd m)
      obtain ⟨m, hm⟩ := exists_qd_of_mem_darts (hNT := hNT) hαd
      have hdrm : d = rd hNT m := by
        rw [rd]; rw [← hm, M.alpha_alpha]
      subst hdrm
      show M.α (rd hNT m) = _
      rw [listSwapQR_apply_rd m _ hnd (List.mem_finRange m)]
      show M.α (M.α (qd hNT m)) = qd hNT m
      rw [M.alpha_alpha]
  · rw [outerTau_eq_self_of_notMem (hNT := hNT) hd]
    refine (listSwapQR_apply_other d _ ?_).symm
    intro i _
    refine ⟨?_, ?_⟩
    · intro h; exact hd (h ▸ qd_mem_outerDel i)
    · intro h; exact hd (h ▸ rd_mem_outerDel i)

/-- `allPairs = mergePairs ++ [last pair]`. -/
lemma allPairs_eq_append :
    allPairs hNT = mergePairs hNT ++ [(qd hNT (lastIdx hNT), rd hNT (lastIdx hNT))] := by
  have hBpos : 0 < hNT.outerCycle.length := hNT.outerCycle.darts_length_pos
  have hlenA : (allPairs hNT).length = hNT.outerCycle.length := by
    simp [allPairs, List.length_map, List.length_finRange]
  have hmlen : (mergePairs hNT).length = hNT.outerCycle.length - 1 := mergePairs_length
  have hlenR : (mergePairs hNT ++ [(qd hNT (lastIdx hNT), rd hNT (lastIdx hNT))]).length
      = hNT.outerCycle.length := by
    rw [List.length_append, hmlen, List.length_singleton]; omega
  apply List.ext_getElem (by rw [hlenA, hlenR])
  intro n hn1 hn2
  rw [hlenA] at hn1
  -- LHS
  have hLHS : (allPairs hNT)[n] = (qd hNT ⟨n, hn1⟩, rd hNT ⟨n, hn1⟩) := by
    simp only [allPairs]
    rw [List.getElem_map, List.getElem_finRange]
    congr 1
  rw [hLHS]
  by_cases hnlast : n < hNT.outerCycle.length - 1
  · -- left part
    rw [List.getElem_append_left (by rw [hmlen]; exact hnlast)]
    simp only [mergePairs]
    rw [List.getElem_map, List.getElem_finRange]
    show (qd hNT ⟨n, hn1⟩, rd hNT ⟨n, hn1⟩)
      = (qd hNT (emb hNT _), rd hNT (emb hNT _))
    congr 1
  · -- right part: n = B-1
    rw [List.getElem_append_right (by rw [hmlen]; omega)]
    have hidx : (⟨n, hn1⟩ : Fin hNT.outerCycle.length) = lastIdx hNT :=
      Fin.ext (by simp only [lastIdx]; omega)
    rw [hidx, List.getElem_singleton]

/-! ### Final assembly. -/

/-- `M.σ * outerTau = pMerge * swap (q last) (r last)`. -/
lemma sigma_outerTau_eq :
    M.σ * outerTau hNT
      = pMerge hNT * Equiv.swap (qd hNT (lastIdx hNT)) (rd hNT (lastIdx hNT)) := by
  rw [outerTau_eq_swapProd, allPairs_eq_append, List.map_append, List.prod_append]
  unfold pMerge pPrefix
  rw [List.take_of_length_le (by rw [mergePairs_length]), List.map_singleton, List.prod_cons,
      List.prod_nil, mul_one, ← mul_assoc]

/-- **Step 6 (the boundary-bank face count) — UNCONDITIONAL.**
`numCycles (M.φ * outerDualAlpha hNT) = M.V − B + 2`. -/
theorem boundaryBankCount_holds (hNT : NearTriangulation M) : BoundaryBankCount hNT := by
  -- reduce to numCycles (M.σ * outerTau) = V - B + 2
  unfold BoundaryBankCount
  rw [phi_outerDualAlpha_eq_sigma_outerTau, sigma_outerTau_eq]
  -- split count: numCycles (pMerge * swap) = numCycles pMerge + 1
  have hsplit : _root_.numCycles
      (pMerge hNT * Equiv.swap (qd hNT (lastIdx hNT)) (rd hNT (lastIdx hNT)))
      = _root_.numCycles (pMerge hNT) + 1 :=
    CombMap.CutCapCount.numCycles_mul_swap_of_sameCycle (pMerge hNT)
      (qd_ne_rd_self (lastIdx hNT)) (pMerge_lastPair_sameCycle (hNT := hNT))
  rw [hsplit]
  -- merge count: numCycles pMerge + (B-1) = V
  have hmerge := numCycles_pMerge_add (hNT := hNT)
  have hBpos : 0 < hNT.outerCycle.length := hNT.outerCycle.darts_length_pos
  have hBV : hNT.outerCycle.length ≤ M.V := outerCycle_length_le_V hNT
  omega

/-- **Discharge of `OuterDualNumCompTwo` — UNCONDITIONAL.**  Supplying the now-proved
boundary-bank count to the genus-slack assembly closes the Chapter-35 coverage atom. -/
theorem outerDualNumCompTwo_holds (hNT : NearTriangulation M) :
    ZinanCh35OuterCount.OuterDualNumCompTwo hNT :=
  ZinanCh35OuterSlack.outerDualNumCompTwo_of_boundaryBankCount' hNT
    (boundaryBankCount_holds hNT)

end ProofsInTheBook.ZinanCh35BankCount

/-! ## Axiom audit (expect clean-3: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35BankCount.boundaryBankCount_holds
#print axioms ProofsInTheBook.ZinanCh35BankCount.outerDualNumCompTwo_holds
