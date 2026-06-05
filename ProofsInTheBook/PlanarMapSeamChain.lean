import ProofsInTheBook.PlanarMapCutCap2FWalk

/-!
# The abstract seam-chain permutation theorem (Chapter 35, the F-count core)

This file proves, in full and unconditionally, the **abstract** seam-chain
permutation theorem designed in `HANDOFF/CH35_FCHAIN_DESIGN.md`, which is the
deepest open core of the corrected Chapter 35 face count
`numCyclesCutPhi2 : numCycles φ'₂ = F + 2`.

## The abstract theorem (`numCycles_mul_seamChain_delta`)

Let `p : Equiv.Perm X` and let one cap chain be in **normal form**

  `L = [γ₀, u₀, v₀, γ₁, u₁, v₁, …, γ_{k-1}, u_{k-1}, v_{k-1}]`

with the structural equations

  `p γᵢ = γᵢ`     (caps are `p`-fixed)
  `p uᵢ = vᵢ`     (each movable pair is a `p`-arrow)

and `L.Nodup` (all `3k` elements distinct).  Then

  `numCycles (p * formPerm L) = numCycles p − (k − 1)`.

The proof is a **signed transposition walk** over the partial products
`Pⱼ := p * formPerm (L.take (j+1))`, with the per-step pivot
`SameCycle Pⱼ L[j] L[j+1]` (split `+1` if same cycle, merge `−1` if not).  The
**active seam-cycle invariant** forces, per block `[γ,u,v]`, the determined sign
pattern: `γᵢ–uᵢ` merge (−1), `uᵢ–vᵢ` split (+1), `vᵢ–γ_{i+1}` merge (−1), with the
per-block merge/split pair cancelling and the only net losses being the `k−1`
inter-block cap merges.

We then specialise to the two `faceCorr₂` chains (the `+`-cap chain and the
`−`-cap chain, with disjoint supports), and conclude `numCyclesCutPhi2_holds`.

`cycleOfList` is Mathlib's `List.formPerm`; the walk step is `formPerm_append_pair`,
the action formula is `formPerm_apply_getElem`, and the per-swap dichotomy is the
repository's `numCycles_mul_swap_*` toolkit.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function List

namespace ProofsInTheBook.PlanarMap

namespace SeamChain

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Layer A: the integer swap dichotomy

The repository supplies `numCycles_mul_swap_of_not_sameCycle` (merge, `+1 =`) and
`CutCapCount.numCycles_mul_swap_of_sameCycle` (split, `+1`).  We package the signed
form once. -/

open CombMap.CutCapCount in
/-- Integer form of the swap dichotomy: `Δ numCycles = +1` if `SameCycle`, `−1`
otherwise. -/
theorem numCycles_mul_swap_delta (p : Equiv.Perm X) {a b : X} (hab : a ≠ b) :
    ((numCycles (p * Equiv.swap a b) : ℤ) - (numCycles p : ℤ))
      = if p.SameCycle a b then 1 else -1 := by
  by_cases h : p.SameCycle a b
  · rw [if_pos h, numCycles_mul_swap_of_sameCycle p hab h]; push_cast; ring
  · rw [if_neg h]
    have := numCycles_mul_swap_of_not_sameCycle p hab h
    omega

/-! ## Layer B: the list-cycle as a product of consecutive swaps

`cycleOfList = List.formPerm`.  Mathlib's `formPerm_append_pair` gives the
right-multiplication step `formPerm (l ++ [a,b]) = formPerm (l ++ [a]) * swap a b`,
which builds the chain one consecutive swap at a time. -/

/-- `cycleOfList` is Mathlib's `List.formPerm`. -/
abbrev cycleOfList (L : List X) : Equiv.Perm X := L.formPerm

/-- **The prefix walk step.**  Extending the prefix `L.take (j+1)` by one element
multiplies `formPerm` on the right by the swap of the two new consecutive elements:

  `formPerm (L.take (j+2)) = formPerm (L.take (j+1)) * swap L[j] L[j+1]`. -/
theorem formPerm_take_succ (L : List X) {j : ℕ} (hj : j + 1 < L.length) :
    cycleOfList (L.take (j + 2))
      = cycleOfList (L.take (j + 1))
        * Equiv.swap (L[j]'(by omega)) (L[j+1]'hj) := by
  -- `L.take (j+2) = L.take j ++ [L[j], L[j+1]]` and `L.take (j+1) = L.take j ++ [L[j]]`.
  have hjlt : j < L.length := by omega
  have h1 : L.take (j + 2) = L.take j ++ [L[j]'hjlt, L[j+1]'hj] := by
    have he : L.take (j + 2) = L.take (j + 1 + 1) := by ring_nf
    rw [he, List.take_add_one, List.take_add_one]
    simp only [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjlt,
      Option.toList, List.append_assoc, List.singleton_append]
  have h2 : L.take (j + 1) = L.take j ++ [L[j]'hjlt] := by
    rw [List.take_add_one]
    simp only [List.getElem?_eq_getElem hjlt, Option.toList]
  simp only [cycleOfList]
  rw [h1, List.formPerm_append_pair, ← h2]

/-- The signed contribution of step `j` of the walk over `L` from base `p`:
`+1` (split) if `L[j]` and `L[j+1]` are in the same cycle of the partial product
`p * formPerm (L.take (j+1))`, `−1` (merge) otherwise. -/
noncomputable def stepSign (p : Equiv.Perm X) (L : List X) (j : ℕ) : ℤ := by
  classical
  exact
    if h : j + 1 < L.length then
      (if (p * cycleOfList (L.take (j + 1))).SameCycle (L[j]'(by omega)) (L[j+1]'h)
        then 1 else -1)
    else 0

/-- **The signed walk delta.**  For a nodup list `L`, after consuming the first
`m + 1` elements, the cycle-count change from base `p` is the signed sum of the
first `m` step contributions. -/
theorem numCycles_take_delta (p : Equiv.Perm X) {L : List X} (hL : L.Nodup) :
    ∀ m : ℕ, m + 1 ≤ L.length →
      ((numCycles (p * cycleOfList (L.take (m + 1))) : ℤ) - (numCycles p : ℤ))
        = ∑ j ∈ Finset.range m, stepSign p L j := by
  intro m
  induction m with
  | zero =>
      intro _
      -- `take 1` is a singleton: `formPerm` of a singleton is `1`.
      have hlen : 1 ≤ L.length := by omega
      have : cycleOfList (L.take 1) = 1 := by
        rcases L with _ | ⟨x, xs⟩
        · simp at hlen
        · simp [cycleOfList, List.take_succ_cons, List.formPerm_singleton]
      rw [this, mul_one, Finset.range_zero, Finset.sum_empty]; ring
  | succ m ih =>
      intro hm
      have hm' : m + 1 ≤ L.length := by omega
      have hstep : m + 1 < L.length := by omega
      have hmlt : m < L.length := by omega
      -- The new partial product is the old one times one swap.
      have hsplit : cycleOfList (L.take (m + 1 + 1))
          = cycleOfList (L.take (m + 1)) * Equiv.swap (L[m]'hmlt) (L[m+1]'hstep) := by
        have := formPerm_take_succ L (j := m) hstep
        simpa using this
      have hne : (L[m]'hmlt) ≠ (L[m+1]'hstep) := by
        intro he
        have := (List.Nodup.getElem_inj_iff hL).mp he
        omega
      -- Apply the swap dichotomy to the running product `p * formPerm (take (m+1))`.
      have hbase := ih hm'
      rw [hsplit, ← mul_assoc]
      have hdelta := numCycles_mul_swap_delta (p * cycleOfList (L.take (m + 1))) hne
      -- rewrite the sum: range (m+1) = range m ∪ {m}
      rw [Finset.sum_range_succ]
      -- stepSign at j = m
      have hsm : stepSign p L m
          = if (p * cycleOfList (L.take (m + 1))).SameCycle (L[m]'hmlt) (L[m+1]'hstep)
              then 1 else -1 := by
        simp only [stepSign, dif_pos hstep]
      -- combine
      have : ((numCycles (p * cycleOfList (L.take (m + 1)) * Equiv.swap (L[m]'hmlt) (L[m+1]'hstep)) : ℤ)
                - (numCycles p : ℤ))
          = ((numCycles (p * cycleOfList (L.take (m + 1))) : ℤ) - (numCycles p : ℤ))
            + ((numCycles (p * cycleOfList (L.take (m + 1)) * Equiv.swap (L[m]'hmlt) (L[m+1]'hstep)) : ℤ)
                - (numCycles (p * cycleOfList (L.take (m + 1))) : ℤ)) := by ring
      rw [this, hbase, hdelta, hsm]

/-! ## Layer C: the list-cycle action formula

For a nodup list `L`, `p * formPerm L` sends `L[r]` to `p (L[(r+1) % length])` and
fixes (up to `p`) every point off `L`.  These give the exact arrows of the partial
product. -/

/-- `(p * cycleOfList L) (L[r]) = p (L[(r+1) % L.length])` for a nodup list. -/
theorem mul_cycleOfList_apply_getElem (p : Equiv.Perm X) {L : List X} (hL : L.Nodup)
    {r : ℕ} (hr : r < L.length) :
    (p * cycleOfList L) (L[r]'hr)
      = p (L[(r + 1) % L.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le r) hr))) := by
  rw [Equiv.Perm.mul_apply]
  simp only [cycleOfList]
  rw [List.formPerm_apply_getElem L hL r hr]

/-- `(p * cycleOfList L) x = p x` for `x ∉ L`. -/
theorem mul_cycleOfList_apply_of_not_mem (p : Equiv.Perm X) {L : List X} {x : X}
    (hx : x ∉ L) : (p * cycleOfList L) x = p x := by
  rw [Equiv.Perm.mul_apply]
  simp only [cycleOfList]
  rw [List.formPerm_apply_of_notMem hx]

/-! ## Invariant-set confinement of `SameCycle`

If a set `A` is forward-invariant under `q` (`x ∈ A → q x ∈ A`), then `SameCycle q`
cannot connect a point of `A` to a point outside `A`.  (`SameCycle` over a finite
type is realised by a *natural* power, so forward invariance suffices.) -/

/-- A forward-`q`-invariant set confines `SameCycle q`. -/
theorem not_sameCycle_of_invariant (q : Equiv.Perm X) {A : Set X} {a b : X}
    (ha : a ∈ A) (hb : b ∉ A) (hinv : ∀ x ∈ A, q x ∈ A) :
    ¬ q.SameCycle a b := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hpow : ∀ m : ℕ, (q ^ m) a ∈ A := by
    intro m
    induction m with
    | zero => simpa using ha
    | succ m ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hinv _ ih
  exact hb (hn ▸ hpow n)

/-! ## Layer D: the abstract seam chain

The chain in normal form is `seamList γ u v = [γ₀,u₀,v₀, γ₁,u₁,v₁, …]`, of length
`3k`.  `SeamChainData` packages the structural hypotheses; the active-cycle
invariant then forces, block by block, the merge/split/merge sign pattern. -/

/-- The seam list in normal form: `[γ₀,u₀,v₀, γ₁,u₁,v₁, …, γ_{k-1},u_{k-1},v_{k-1}]`. -/
def seamList {k : ℕ} (γ u v : Fin k → X) : List X :=
  (List.finRange k).flatMap fun i => [γ i, u i, v i]

@[simp] lemma seamList_length {k : ℕ} (γ u v : Fin k → X) :
    (seamList γ u v).length = 3 * k := by
  simp only [seamList, List.length_flatMap, List.map_const', List.sum_replicate,
    List.length_finRange, smul_eq_mul, List.length_cons, List.length_nil]
  ring

/-- The packaged abstract seam-chain data. -/
structure SeamChainData (X : Type*) [Fintype X] [DecidableEq X] where
  p : Equiv.Perm X
  k : ℕ
  hk : 0 < k
  γ : Fin k → X
  u : Fin k → X
  v : Fin k → X
  nodup_seam : (seamList γ u v).Nodup
  cap_fixed : ∀ i, p (γ i) = γ i
  seam_pair : ∀ i, p (u i) = v i

/-! ### Indexing the seam list

`seamList γ u v` equals `List.ofFn` of the block decoder, giving clean `getElem`
formulas at `3i`, `3i+1`, `3i+2`. -/

/-- The block decoder: at index `3i+s` returns `γ i`, `u i`, `v i` for `s = 0,1,2`. -/
def seamFn {k : ℕ} (γ u v : Fin k → X) (j : Fin (3 * k)) : X :=
  ![γ, u, v] ⟨j.1 % 3, Nat.mod_lt _ (by norm_num)⟩ ⟨j.1 / 3, by
    have := j.2; omega⟩

/-- `seamList = List.ofFn (seamFn)`. -/
lemma seamList_eq_ofFn {k : ℕ} (γ u v : Fin k → X) :
    seamList γ u v = (List.ofFn (seamFn γ u v)) := by
  rw [List.ofFn_mul' (m := 3) (n := k) (seamFn γ u v), seamList, List.flatMap]
  rw [show (List.ofFn fun i : Fin k => List.ofFn fun j : Fin 3 =>
      seamFn γ u v ⟨3 * (i:ℕ) + (j:ℕ), by have := i.2; have := j.2; omega⟩)
      = List.map (fun i : Fin k => List.ofFn fun j : Fin 3 =>
          seamFn γ u v ⟨3 * (i:ℕ) + (j:ℕ), by have := i.2; have := j.2; omega⟩)
          (List.finRange k) from (List.ofFn_eq_map)]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i _
  -- inner: [γ i, u i, v i] = ofFn (fun j : Fin 3 => seamFn ⟨3*i+j⟩)
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  have key : ∀ (s : ℕ) (hs : s < 3) (hb : 3 * (i:ℕ) + s < 3 * k),
      seamFn γ u v ⟨3 * (i:ℕ) + s, hb⟩ = ![γ, u, v] ⟨s, hs⟩ i := by
    intro s hs hb
    simp only [seamFn]
    have e1 : (⟨(3 * (i:ℕ) + s) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = ⟨s, hs⟩ := by
      apply Fin.ext; simp only [Fin.val_mk]; omega
    have e2 : (⟨(3 * (i:ℕ) + s) / 3, by have := i.2; omega⟩ : Fin k) = i := by
      apply Fin.ext; simp only [Fin.val_mk]; omega
    rw [e1, e2]
  have h0 := key 0 (by norm_num) (by have := i.2; omega)
  have h1 := key 1 (by norm_num) (by have := i.2; omega)
  have h2 := key 2 (by norm_num) (by have := i.2; omega)
  simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero] at *
  rw [h0, h1, h2]
  rfl

/-- `getElem` of `seamList` at an arbitrary index, via the block decoder. -/
lemma seamList_getElem {k : ℕ} (γ u v : Fin k → X) {j : ℕ} (hj : j < 3 * k) :
    (seamList γ u v)[j]'(by rw [seamList_length]; exact hj)
      = seamFn γ u v ⟨j, hj⟩ := by
  rw [List.getElem_of_eq (seamList_eq_ofFn γ u v)]
  rw [List.getElem_ofFn (by rw [List.length_ofFn]; exact hj)]

/-- `seamList … [3i] = γ i`. -/
lemma seamList_getElem_gamma {k : ℕ} (γ u v : Fin k → X) (i : Fin k) :
    (seamList γ u v)[3 * (i:ℕ)]'(by rw [seamList_length]; have := i.2; omega) = γ i := by
  rw [seamList_getElem γ u v (j := 3 * (i:ℕ)) (by have := i.2; omega)]
  simp only [seamFn]
  have e1 : ((⟨(3 * (i:ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3)) = ⟨0, by norm_num⟩ := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  have e2 : ((⟨(3 * (i:ℕ)) / 3, by have := i.2; omega⟩ : Fin k)) = i := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  rw [e1, e2]; rfl

/-- `seamList … [3i+1] = u i`. -/
lemma seamList_getElem_u {k : ℕ} (γ u v : Fin k → X) (i : Fin k) :
    (seamList γ u v)[3 * (i:ℕ) + 1]'(by rw [seamList_length]; have := i.2; omega) = u i := by
  rw [seamList_getElem γ u v (j := 3 * (i:ℕ) + 1) (by have := i.2; omega)]
  simp only [seamFn]
  have e1 : ((⟨(3 * (i:ℕ) + 1) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3)) = ⟨1, by norm_num⟩ := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  have e2 : ((⟨(3 * (i:ℕ) + 1) / 3, by have := i.2; omega⟩ : Fin k)) = i := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  rw [e1, e2]; rfl

/-- `seamList … [3i+2] = v i`. -/
lemma seamList_getElem_v {k : ℕ} (γ u v : Fin k → X) (i : Fin k) :
    (seamList γ u v)[3 * (i:ℕ) + 2]'(by rw [seamList_length]; have := i.2; omega) = v i := by
  rw [seamList_getElem γ u v (j := 3 * (i:ℕ) + 2) (by have := i.2; omega)]
  simp only [seamFn]
  have e1 : ((⟨(3 * (i:ℕ) + 2) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3)) = ⟨2, by norm_num⟩ := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  have e2 : ((⟨(3 * (i:ℕ) + 2) / 3, by have := i.2; omega⟩ : Fin k)) = i := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  rw [e1, e2]; rfl

/-! ### The partial-product action on a prefix

For a nodup list `L` and a prefix length `m ≤ L.length`, the partial product
`p * formPerm (L.take m)` sends `L[r]` (for `r < m`) to `p (L[(r+1) % m])`, and any
point off the prefix to `p`.  These are the exact arrows of `P_j`. -/

/-- `(p * formPerm (L.take m)) (L[r]) = p (L[(r+1) % m])` for `r < m ≤ L.length`,
`L` nodup. -/
theorem mul_take_apply_getElem (p : Equiv.Perm X) {L : List X} (hL : L.Nodup)
    {m r : ℕ} (hm : m ≤ L.length) (hr : r < m) :
    (p * cycleOfList (L.take m)) (L[r]'(by omega))
      = p (L[(r + 1) % m]'(by have : (r + 1) % m < m := Nat.mod_lt _ (by omega); omega)) := by
  have hlen : (L.take m).length = m := by rw [List.length_take]; omega
  have hnodup : (L.take m).Nodup := (List.take_sublist m L).nodup hL
  have hr' : r < (L.take m).length := by omega
  have hget : (L.take m)[r]'hr' = L[r]'(by omega) := List.getElem_take
  have := mul_cycleOfList_apply_getElem p hnodup (r := r) hr'
  rw [hget] at this
  rw [this]
  -- rewrite the RHS index using length = m and getElem_take
  congr 1
  rw [List.getElem_take]
  congr 1
  rw [hlen]

/-- `(p * formPerm (L.take m)) x = p x` for `x` not in the prefix `L.take m`. -/
theorem mul_take_apply_of_not_mem (p : Equiv.Perm X) {L : List X} {x : X} {m : ℕ}
    (hx : x ∉ L.take m) : (p * cycleOfList (L.take m)) x = p x :=
  mul_cycleOfList_apply_of_not_mem p hx

/-! ### The partial product of a `SeamChainData`

`P S m := S.p * formPerm (seamList.take m)`.  We compute its action on the seam
elements `γ_t` and `v_t` directly, using the prefix-action formula and the modular
index arithmetic, then read off forward-invariance of the active set. -/

namespace SeamChainData

variable (S : SeamChainData X)

/-- The partial product `P S m = p * formPerm (seamList.take m)`. -/
noncomputable def P (m : ℕ) : Equiv.Perm X :=
  S.p * cycleOfList ((seamList S.γ S.u S.v).take m)

/-- Membership of `γ t` in a take-prefix of the seam list (`3t < m`). -/
lemma gamma_mem_take {m : ℕ} {t : Fin S.k} (ht : 3 * (t:ℕ) < m) :
    S.γ t ∈ (seamList S.γ S.u S.v).take m := by
  have hlen : 3 * (t:ℕ) < (seamList S.γ S.u S.v).length := by
    rw [seamList_length]; have := t.2; omega
  have hjm : 3 * (t:ℕ) < ((seamList S.γ S.u S.v).take m).length := by
    rw [List.length_take]; omega
  rw [← seamList_getElem_gamma S.γ S.u S.v t,
    show (seamList S.γ S.u S.v)[3 * (t:ℕ)]'(by rw [seamList_length]; have := t.2; omega)
      = ((seamList S.γ S.u S.v).take m)[3 * (t:ℕ)]'hjm from (List.getElem_take).symm]
  exact List.getElem_mem hjm

/-- Membership of `v t` in a take-prefix of the seam list (`3t+2 < m`). -/
lemma v_mem_take {m : ℕ} {t : Fin S.k} (ht : 3 * (t:ℕ) + 2 < m) :
    S.v t ∈ (seamList S.γ S.u S.v).take m := by
  have hlen : 3 * (t:ℕ) + 2 < (seamList S.γ S.u S.v).length := by
    rw [seamList_length]; have := t.2; omega
  have hjm : 3 * (t:ℕ) + 2 < ((seamList S.γ S.u S.v).take m).length := by
    rw [List.length_take]; omega
  rw [← seamList_getElem_v S.γ S.u S.v t,
    show (seamList S.γ S.u S.v)[3 * (t:ℕ) + 2]'(by rw [seamList_length]; have := t.2; omega)
      = ((seamList S.γ S.u S.v).take m)[3 * (t:ℕ) + 2]'hjm from (List.getElem_take).symm]
  exact List.getElem_mem hjm

/-- Action of `P S m` on `γ t` when its successor `u t` is still inside the prefix
(`3t+1 < m`): `P S m (γ t) = v t`. -/
lemma P_apply_gamma_inner {m : ℕ} {t : Fin S.k} (hm : m ≤ 3 * S.k)
    (ht : 3 * (t:ℕ) + 1 < m) : S.P m (S.γ t) = S.v t := by
  have hpos : 3 * (t:ℕ) < m := by omega
  have hlen : m ≤ (seamList S.γ S.u S.v).length := by rw [seamList_length]; exact hm
  have hgt : (seamList S.γ S.u S.v)[3 * (t:ℕ)]'(by omega) = S.γ t :=
    seamList_getElem_gamma S.γ S.u S.v t
  have hmod : (3 * (t:ℕ) + 1) % m = 3 * (t:ℕ) + 1 := Nat.mod_eq_of_lt ht
  unfold SeamChainData.P
  rw [← hgt, mul_take_apply_getElem S.p S.nodup_seam hlen hpos]
  have hb : (3 * (t:ℕ) + 1) % m < (seamList S.γ S.u S.v).length := by
    have : (3 * (t:ℕ) + 1) % m < m := Nat.mod_lt _ (by omega); omega
  have helem : (seamList S.γ S.u S.v)[(3 * (t:ℕ) + 1) % m]'hb = S.u t := by
    rw [getElem_congr rfl hmod]
    exact seamList_getElem_u S.γ S.u S.v t
  rw [helem]
  exact S.seam_pair t

/-- Action of `P S m` on `γ t` when it is the last prefix element (`m = 3t+1`):
`P S m (γ t) = γ 0`. -/
lemma P_apply_gamma_last {t : Fin S.k} (h0 : 0 < S.k) :
    S.P (3 * (t:ℕ) + 1) (S.γ t) = S.γ ⟨0, h0⟩ := by
  have hm : 3 * (t:ℕ) + 1 ≤ 3 * S.k := by have := t.2; omega
  have hpos : 3 * (t:ℕ) < 3 * (t:ℕ) + 1 := by omega
  have hlen : 3 * (t:ℕ) + 1 ≤ (seamList S.γ S.u S.v).length := by rw [seamList_length]; exact hm
  have hgt : (seamList S.γ S.u S.v)[3 * (t:ℕ)]'(by omega) = S.γ t :=
    seamList_getElem_gamma S.γ S.u S.v t
  unfold SeamChainData.P
  rw [← hgt, mul_take_apply_getElem S.p S.nodup_seam hlen hpos]
  have hb : (3 * (t:ℕ) + 1) % (3 * (t:ℕ) + 1) < (seamList S.γ S.u S.v).length := by
    rw [Nat.mod_self]; rw [seamList_length]; omega
  have helem : (seamList S.γ S.u S.v)[(3 * (t:ℕ) + 1) % (3 * (t:ℕ) + 1)]'hb = S.γ ⟨0, h0⟩ := by
    rw [getElem_congr rfl (Nat.mod_self _)]
    have := seamList_getElem_gamma S.γ S.u S.v ⟨0, h0⟩
    simpa using this
  rw [helem]
  exact S.cap_fixed _

/-- Action of `P S m` on `v t` when its successor `γ (t+1)` is still inside the
prefix (`3t+3 < m`): `P S m (v t) = γ (t+1)`. -/
lemma P_apply_v_inner {m : ℕ} {t : Fin S.k} {t1 : Fin S.k} (hm : m ≤ 3 * S.k)
    (ht : 3 * (t:ℕ) + 3 < m) (ht1 : (t1:ℕ) = (t:ℕ) + 1) :
    S.P m (S.v t) = S.γ t1 := by
  have hpos : 3 * (t:ℕ) + 2 < m := by omega
  have hlen : m ≤ (seamList S.γ S.u S.v).length := by rw [seamList_length]; exact hm
  have hgt : (seamList S.γ S.u S.v)[3 * (t:ℕ) + 2]'(by omega) = S.v t :=
    seamList_getElem_v S.γ S.u S.v t
  have hmod : (3 * (t:ℕ) + 2 + 1) % m = 3 * (t:ℕ) + 3 := by
    rw [show 3 * (t:ℕ) + 2 + 1 = 3 * (t:ℕ) + 3 from by ring]; exact Nat.mod_eq_of_lt ht
  unfold SeamChainData.P
  rw [← hgt, mul_take_apply_getElem S.p S.nodup_seam hlen hpos]
  have hb : (3 * (t:ℕ) + 2 + 1) % m < (seamList S.γ S.u S.v).length := by
    have : (3 * (t:ℕ) + 2 + 1) % m < m := Nat.mod_lt _ (by omega); omega
  have hidx2 : 3 * (t:ℕ) + 3 = 3 * (t1:ℕ) := by rw [ht1]; ring
  have helem : (seamList S.γ S.u S.v)[(3 * (t:ℕ) + 2 + 1) % m]'hb = S.γ t1 := by
    rw [getElem_congr rfl hmod]
    rw [getElem_congr rfl hidx2]
    exact seamList_getElem_gamma S.γ S.u S.v t1
  rw [helem]
  exact S.cap_fixed _

/-- Action of `P S m` on `v t` when it is the last prefix element (`m = 3t+3`):
`P S m (v t) = γ 0`. -/
lemma P_apply_v_last {t : Fin S.k} (h0 : 0 < S.k) :
    S.P (3 * (t:ℕ) + 3) (S.v t) = S.γ ⟨0, h0⟩ := by
  have hm : 3 * (t:ℕ) + 3 ≤ 3 * S.k := by have := t.2; omega
  have hpos : 3 * (t:ℕ) + 2 < 3 * (t:ℕ) + 3 := by omega
  have hlen : 3 * (t:ℕ) + 3 ≤ (seamList S.γ S.u S.v).length := by rw [seamList_length]; exact hm
  have hgt : (seamList S.γ S.u S.v)[3 * (t:ℕ) + 2]'(by omega) = S.v t :=
    seamList_getElem_v S.γ S.u S.v t
  unfold SeamChainData.P
  rw [← hgt, mul_take_apply_getElem S.p S.nodup_seam hlen hpos]
  have hmz : (3 * (t:ℕ) + 2 + 1) % (3 * (t:ℕ) + 3) = 0 := by
    rw [show 3 * (t:ℕ) + 2 + 1 = 3 * (t:ℕ) + 3 from by ring]; exact Nat.mod_self _
  have hb : (3 * (t:ℕ) + 2 + 1) % (3 * (t:ℕ) + 3) < (seamList S.γ S.u S.v).length := by
    rw [hmz, seamList_length]; omega
  have helem : (seamList S.γ S.u S.v)[(3 * (t:ℕ) + 2 + 1) % (3 * (t:ℕ) + 3)]'hb = S.γ ⟨0, h0⟩ := by
    rw [getElem_congr rfl hmz]
    have := seamList_getElem_gamma S.γ S.u S.v ⟨0, h0⟩
    simpa using this
  rw [helem]
  exact S.cap_fixed _

/-- Action of `P S m` on `u t` when it is the last prefix element (`m = 3t+2`):
`P S m (u t) = γ 0`. -/
lemma P_apply_u_last {t : Fin S.k} (h0 : 0 < S.k) :
    S.P (3 * (t:ℕ) + 2) (S.u t) = S.γ ⟨0, h0⟩ := by
  have hm : 3 * (t:ℕ) + 2 ≤ 3 * S.k := by have := t.2; omega
  have hpos : 3 * (t:ℕ) + 1 < 3 * (t:ℕ) + 2 := by omega
  have hlen : 3 * (t:ℕ) + 2 ≤ (seamList S.γ S.u S.v).length := by rw [seamList_length]; exact hm
  have hgt : (seamList S.γ S.u S.v)[3 * (t:ℕ) + 1]'(by omega) = S.u t :=
    seamList_getElem_u S.γ S.u S.v t
  unfold SeamChainData.P
  rw [← hgt, mul_take_apply_getElem S.p S.nodup_seam hlen hpos]
  have hmz : (3 * (t:ℕ) + 1 + 1) % (3 * (t:ℕ) + 2) = 0 := by
    rw [show 3 * (t:ℕ) + 1 + 1 = 3 * (t:ℕ) + 2 from by ring]; exact Nat.mod_self _
  have hb : (3 * (t:ℕ) + 1 + 1) % (3 * (t:ℕ) + 2) < (seamList S.γ S.u S.v).length := by
    rw [hmz, seamList_length]; omega
  have helem : (seamList S.γ S.u S.v)[(3 * (t:ℕ) + 1 + 1) % (3 * (t:ℕ) + 2)]'hb = S.γ ⟨0, h0⟩ := by
    rw [getElem_congr rfl hmz]
    have := seamList_getElem_gamma S.γ S.u S.v ⟨0, h0⟩
    simpa using this
  rw [helem]
  exact S.cap_fixed _

/-- Action of `P S m` on `γ t` for `t` strictly interior (`3t+1 < m`) — restated to
land in `γ`/`v` form for invariance bookkeeping.  (Alias of `P_apply_gamma_inner`.) -/
lemma P_apply_gamma_to_v {m : ℕ} {t : Fin S.k} (hm : m ≤ 3 * S.k)
    (ht : 3 * (t:ℕ) + 1 < m) : S.P m (S.γ t) = S.v t :=
  S.P_apply_gamma_inner hm ht

/-! ### Active sets and forward invariance

The active cycle of `P S m` at the two merge sites is an explicit set of `γ`s and
`v`s.  We prove forward invariance directly from the action lemmas, then confine
`SameCycle` with `not_sameCycle_of_invariant`. -/

/-- The active set before the `γᵢ–uᵢ` merge (state `m = 3i+1`):
`{γ_t : t ≤ i} ∪ {v_t : t < i}`. -/
def ActiveGU (i : Fin S.k) : Set X :=
  {x | (∃ t : Fin S.k, (t:ℕ) ≤ (i:ℕ) ∧ x = S.γ t) ∨
       (∃ t : Fin S.k, (t:ℕ) < (i:ℕ) ∧ x = S.v t)}

/-- The active set before the `vᵢ–γ_{i+1}` merge (state `m = 3i+3`):
`{γ_t : t ≤ i} ∪ {v_t : t ≤ i}`. -/
def ActiveVG (i : Fin S.k) : Set X :=
  {x | (∃ t : Fin S.k, (t:ℕ) ≤ (i:ℕ) ∧ x = S.γ t) ∨
       (∃ t : Fin S.k, (t:ℕ) ≤ (i:ℕ) ∧ x = S.v t)}

/-- `γ 0` lies in `ActiveGU i` (since `0 ≤ i`). -/
lemma gamma0_mem_ActiveGU (i : Fin S.k) : S.γ ⟨0, S.hk⟩ ∈ S.ActiveGU i := by
  left; exact ⟨⟨0, S.hk⟩, Nat.zero_le _, rfl⟩

/-- `γ 0` lies in `ActiveVG i`. -/
lemma gamma0_mem_ActiveVG (i : Fin S.k) : S.γ ⟨0, S.hk⟩ ∈ S.ActiveVG i := by
  left; exact ⟨⟨0, S.hk⟩, Nat.zero_le _, rfl⟩

/-- Forward invariance of `ActiveGU i` under `P S (3i+1)`. -/
lemma ActiveGU_invariant (i : Fin S.k) :
    ∀ x ∈ S.ActiveGU i, S.P (3 * (i:ℕ) + 1) x ∈ S.ActiveGU i := by
  have hm : 3 * (i:ℕ) + 1 ≤ 3 * S.k := by have := i.2; omega
  rintro x (⟨t, hti, rfl⟩ | ⟨t, hti, rfl⟩)
  · -- x = γ t with t ≤ i
    rcases lt_or_eq_of_le hti with hlt | heq
    · -- t < i : interior, γ t → v t, t < i
      rw [S.P_apply_gamma_inner hm (by omega)]
      right; exact ⟨t, hlt, rfl⟩
    · -- t = i : last, γ i → γ 0
      have hrw : 3 * (i:ℕ) + 1 = 3 * (t:ℕ) + 1 := by omega
      rw [hrw, S.P_apply_gamma_last S.hk]
      exact S.gamma0_mem_ActiveGU i
  · -- x = v t with t < i : v t → γ (t+1), t+1 ≤ i
    have ht1lt : (t:ℕ) + 1 < S.k := by have := i.2; omega
    rw [S.P_apply_v_inner (t1 := ⟨(t:ℕ) + 1, ht1lt⟩) hm (by omega) (by simp)]
    left; exact ⟨⟨(t:ℕ) + 1, ht1lt⟩, by simp; omega, rfl⟩

/-- Forward invariance of `ActiveVG i` under `P S (3i+3)` (needs `i+1 < k`, i.e.
`i ≤ k-2`, so that `v t → γ (t+1)` stays in range). -/
lemma ActiveVG_invariant (i : Fin S.k) (hi : (i:ℕ) + 1 < S.k) :
    ∀ x ∈ S.ActiveVG i, S.P (3 * (i:ℕ) + 3) x ∈ S.ActiveVG i := by
  have hm : 3 * (i:ℕ) + 3 ≤ 3 * S.k := by omega
  rintro x (⟨t, hti, rfl⟩ | ⟨t, hti, rfl⟩)
  · -- x = γ t with t ≤ i : γ t → v t (3t+1 < 3i+3 since t ≤ i)
    rw [S.P_apply_gamma_inner hm (by omega)]
    right; exact ⟨t, hti, rfl⟩
  · -- x = v t with t ≤ i
    rcases lt_or_eq_of_le hti with hlt | heq
    · -- t < i : v t → γ (t+1), t+1 ≤ i
      have ht1lt : (t:ℕ) + 1 < S.k := by have := i.2; omega
      rw [S.P_apply_v_inner (t1 := ⟨(t:ℕ) + 1, ht1lt⟩) hm (by omega) (by simp)]
      left; exact ⟨⟨(t:ℕ) + 1, ht1lt⟩, by simp; omega, rfl⟩
    · -- t = i : last, v i → γ 0
      have hrw : 3 * (i:ℕ) + 3 = 3 * (t:ℕ) + 3 := by omega
      rw [hrw, S.P_apply_v_last S.hk]
      exact S.gamma0_mem_ActiveVG i

/-! ### Nodup distinctness of the block letters

`nodup_seam` makes all `3k` entries distinct.  Two seam letters coincide iff their
seam indices coincide; we extract the pairwise-distinctness facts the exclusions
need. -/

/-- Two seam letters are equal iff their indices are.  Here `a b < 3k` are the seam
positions; equality of the entries forces `a = b`. -/
lemma seam_index_inj {a b : ℕ} (ha : a < 3 * S.k) (hb : b < 3 * S.k)
    (heq : (seamList S.γ S.u S.v)[a]'(by rw [seamList_length]; exact ha)
         = (seamList S.γ S.u S.v)[b]'(by rw [seamList_length]; exact hb)) : a = b := by
  have := (List.Nodup.getElem_inj_iff S.nodup_seam).mp heq
  exact this

/-- `u i ≠ γ t`. -/
lemma u_ne_gamma (i t : Fin S.k) : S.u i ≠ S.γ t := by
  intro h
  have h' : (seamList S.γ S.u S.v)[3 * (i:ℕ) + 1]'(by rw [seamList_length]; have := i.2; omega)
      = (seamList S.γ S.u S.v)[3 * (t:ℕ)]'(by rw [seamList_length]; have := t.2; omega) := by
    rw [seamList_getElem_u, seamList_getElem_gamma]; exact h
  have := S.seam_index_inj (by have := i.2; omega) (by have := t.2; omega) h'
  omega

/-- `u i ≠ v t`. -/
lemma u_ne_v (i t : Fin S.k) : S.u i ≠ S.v t := by
  intro h
  have h' : (seamList S.γ S.u S.v)[3 * (i:ℕ) + 1]'(by rw [seamList_length]; have := i.2; omega)
      = (seamList S.γ S.u S.v)[3 * (t:ℕ) + 2]'(by rw [seamList_length]; have := t.2; omega) := by
    rw [seamList_getElem_u, seamList_getElem_v]; exact h
  have := S.seam_index_inj (by have := i.2; omega) (by have := t.2; omega) h'
  omega

/-- `γ` is injective on `Fin k`. -/
lemma gamma_inj {s t : Fin S.k} (h : S.γ s = S.γ t) : (s:ℕ) = (t:ℕ) := by
  have h' : (seamList S.γ S.u S.v)[3 * (s:ℕ)]'(by rw [seamList_length]; have := s.2; omega)
      = (seamList S.γ S.u S.v)[3 * (t:ℕ)]'(by rw [seamList_length]; have := t.2; omega) := by
    rw [seamList_getElem_gamma, seamList_getElem_gamma]; exact h
  have := S.seam_index_inj (by have := s.2; omega) (by have := t.2; omega) h'
  omega

/-- `γ s ≠ v t`. -/
lemma gamma_ne_v (s t : Fin S.k) : S.γ s ≠ S.v t := by
  intro h
  have h' : (seamList S.γ S.u S.v)[3 * (s:ℕ)]'(by rw [seamList_length]; have := s.2; omega)
      = (seamList S.γ S.u S.v)[3 * (t:ℕ) + 2]'(by rw [seamList_length]; have := t.2; omega) := by
    rw [seamList_getElem_gamma, seamList_getElem_v]; exact h
  have := S.seam_index_inj (by have := s.2; omega) (by have := t.2; omega) h'
  omega

/-- `u i ∉ ActiveGU i`. -/
lemma u_not_mem_ActiveGU (i : Fin S.k) : S.u i ∉ S.ActiveGU i := by
  rintro (⟨t, _, ht⟩ | ⟨t, _, ht⟩)
  · exact S.u_ne_gamma i t ht
  · exact S.u_ne_v i t ht

/-- `γ (i+1) ∉ ActiveVG i` (when `i+1 < k`). -/
lemma gamma_succ_not_mem_ActiveVG (i : Fin S.k) (hi : (i:ℕ) + 1 < S.k) :
    S.γ ⟨(i:ℕ) + 1, hi⟩ ∉ S.ActiveVG i := by
  rintro (⟨t, hti, ht⟩ | ⟨t, hti, ht⟩)
  · have := S.gamma_inj ht; simp at this; omega
  · exact S.gamma_ne_v ⟨(i:ℕ) + 1, hi⟩ t ht

/-! ### The three step classifications

`γᵢ–uᵢ` and `vᵢ–γ_{i+1}` are merges (confined by the invariant set); `uᵢ–vᵢ` is a
split (explicit `SameCycle` path). -/

/-- **Type A merge**: `¬ SameCycle (P (3i)) (γ i) (u i)`.  Note the partial product is
indexed by *take length* `m = 3i+1`, i.e. the prefix `[…,γ i]`. -/
lemma seam_gamma_u_merge (i : Fin S.k) :
    ¬ (S.P (3 * (i:ℕ) + 1)).SameCycle (S.γ i) (S.u i) := by
  apply not_sameCycle_of_invariant (A := S.ActiveGU i)
  · left; exact ⟨i, le_refl _, rfl⟩
  · exact S.u_not_mem_ActiveGU i
  · exact S.ActiveGU_invariant i

/-- **Type C merge**: `¬ SameCycle (P (3i+2)) (v i) (γ (i+1))` for `i+1 < k`.  The
partial product is indexed by take length `m = 3i+3`, i.e. the prefix `[…,v i]`. -/
lemma seam_v_gamma_merge (i : Fin S.k) (hi : (i:ℕ) + 1 < S.k) :
    ¬ (S.P (3 * (i:ℕ) + 3)).SameCycle (S.v i) (S.γ ⟨(i:ℕ) + 1, hi⟩) := by
  apply not_sameCycle_of_invariant (A := S.ActiveVG i)
  · right; exact ⟨i, le_refl _, rfl⟩
  · exact S.gamma_succ_not_mem_ActiveVG i hi
  · exact S.ActiveVG_invariant i hi

/-! ### The split: `uᵢ–vᵢ` same cycle at state `m = 3i+2`

At the prefix `[…, γ i, u i]` (length `3i+2`), the cap prefix has linked `u i` and
`v i` into one orbit:  `u i → γ 0 → v 0 → γ 1 → … → γ i → v i`. -/

/-- A single forward `P`-step is a `SameCycle` link. -/
lemma sameCycle_step {q : Equiv.Perm X} {x y : X} (h : q x = y) : q.SameCycle x y :=
  ⟨1, by simpa using h⟩

/-- At state `m = 3i+2`, `SameCycle (γ 0) (γ t)` for every `t ≤ i`, via the forward
chain `γ 0 → v 0 → γ 1 → … → γ t`. -/
lemma sameCycle_gamma0_gamma_at_split (i : Fin S.k) :
    ∀ t : Fin S.k, (t:ℕ) ≤ (i:ℕ) →
      (S.P (3 * (i:ℕ) + 2)).SameCycle (S.γ ⟨0, S.hk⟩) (S.γ t) := by
  have hm : 3 * (i:ℕ) + 2 ≤ 3 * S.k := by have := i.2; omega
  -- strong induction on the nat value of t
  intro t
  induction' ht : (t:ℕ) using Nat.strong_induction_on with n IH generalizing t
  intro hti
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- t = 0
    have : t = (⟨0, S.hk⟩ : Fin S.k) := by apply Fin.ext; simp only [Fin.val_mk]; omega
    rw [this]
  · -- t = s+1, with s < i
    set s : ℕ := n - 1 with hs
    have hsn : n = s + 1 := by omega
    have hslt : s < S.k := by omega
    have hsi : s < (i:ℕ) := by omega
    -- IH at s: SameCycle (γ 0) (γ ⟨s⟩)
    have hIH : (S.P (3 * (i:ℕ) + 2)).SameCycle (S.γ ⟨0, S.hk⟩) (S.γ ⟨s, hslt⟩) :=
      IH s (by omega) ⟨s, hslt⟩ rfl (by omega)
    -- step γ s → v s : P (γ s) = v s, needs 3s+1 < 3i+2 ⟺ s ≤ i
    have step1 : (S.P (3 * (i:ℕ) + 2)).SameCycle (S.γ ⟨s, hslt⟩) (S.v ⟨s, hslt⟩) :=
      sameCycle_step (S.P_apply_gamma_inner hm (by simp only [Fin.val_mk]; omega))
    -- step v s → γ (s+1) : needs 3s+3 < 3i+2 ⟺ s < i
    have htfin : t = (⟨s + 1, by omega⟩ : Fin S.k) := by
      apply Fin.ext; simp only [Fin.val_mk]; omega
    have step2 : (S.P (3 * (i:ℕ) + 2)).SameCycle (S.v ⟨s, hslt⟩) (S.γ t) := by
      rw [htfin]
      exact sameCycle_step (S.P_apply_v_inner (t1 := ⟨s + 1, by omega⟩) hm
        (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]))
    exact (hIH.trans step1).trans step2

/-- **Type B split**: `SameCycle (P (3i+1)) (u i) (v i)`.  The partial product is
indexed by take length `m = 3i+2`, i.e. the prefix `[…, γ i, u i]`. -/
lemma seam_u_v_split (i : Fin S.k) :
    (S.P (3 * (i:ℕ) + 2)).SameCycle (S.u i) (S.v i) := by
  have hm : 3 * (i:ℕ) + 2 ≤ 3 * S.k := by have := i.2; omega
  -- u i → γ 0  (u i is the last prefix element)
  have hu0 : (S.P (3 * (i:ℕ) + 2)).SameCycle (S.u i) (S.γ ⟨0, S.hk⟩) :=
    sameCycle_step (S.P_apply_u_last S.hk)
  -- γ 0 → γ i  (forward chain)
  have h0i : (S.P (3 * (i:ℕ) + 2)).SameCycle (S.γ ⟨0, S.hk⟩) (S.γ i) :=
    S.sameCycle_gamma0_gamma_at_split i i (le_refl _)
  -- γ i → v i  (P (γ i) = v i, needs 3i+1 < 3i+2)
  have hiv : (S.P (3 * (i:ℕ) + 2)).SameCycle (S.γ i) (S.v i) :=
    sameCycle_step (S.P_apply_gamma_inner hm (by omega))
  exact ((hu0.trans h0i).trans hiv)

end SeamChainData

/-! ## Layer D-final: the signed sum over the seam walk

We evaluate `stepSign S.p (seamList …) j` at each `j` via the three classification
lemmas, then sum the closed-form signs over `range (3k-1)`. -/

namespace SeamChainData

variable (S : SeamChainData X)

/-- `stepSign` of the seam walk at `j = 3i` is `-1` (the `γᵢ–uᵢ` merge). -/
lemma stepSign_block_A (i : Fin S.k) :
    stepSign S.p (seamList S.γ S.u S.v) (3 * (i:ℕ)) = -1 := by
  have hj : 3 * (i:ℕ) + 1 < (seamList S.γ S.u S.v).length := by
    rw [seamList_length]; have := i.2; omega
  have hg : (seamList S.γ S.u S.v)[3 * (i:ℕ)]'(by omega) = S.γ i :=
    seamList_getElem_gamma S.γ S.u S.v i
  have hu : (seamList S.γ S.u S.v)[3 * (i:ℕ) + 1]'hj = S.u i :=
    seamList_getElem_u S.γ S.u S.v i
  simp only [stepSign, dif_pos hj]
  rw [if_neg]
  · -- match the SameCycle to the classification lemma
    rw [show (S.p * cycleOfList ((seamList S.γ S.u S.v).take (3 * (i:ℕ) + 1)))
          = S.P (3 * (i:ℕ) + 1) from rfl]
    rw [hg, hu]
    exact S.seam_gamma_u_merge i

/-- `stepSign` of the seam walk at `j = 3i+1` is `+1` (the `uᵢ–vᵢ` split). -/
lemma stepSign_block_B (i : Fin S.k) :
    stepSign S.p (seamList S.γ S.u S.v) (3 * (i:ℕ) + 1) = 1 := by
  have hj : 3 * (i:ℕ) + 1 + 1 < (seamList S.γ S.u S.v).length := by
    rw [seamList_length]; have := i.2; omega
  have hu : (seamList S.γ S.u S.v)[3 * (i:ℕ) + 1]'(by omega) = S.u i :=
    seamList_getElem_u S.γ S.u S.v i
  have hv : (seamList S.γ S.u S.v)[3 * (i:ℕ) + 1 + 1]'hj = S.v i := by
    rw [getElem_congr rfl (show 3 * (i:ℕ) + 1 + 1 = 3 * (i:ℕ) + 2 from by ring)]
    exact seamList_getElem_v S.γ S.u S.v i
  simp only [stepSign, dif_pos hj]
  rw [if_pos]
  rw [show (S.p * cycleOfList ((seamList S.γ S.u S.v).take (3 * (i:ℕ) + 1 + 1)))
        = S.P (3 * (i:ℕ) + 2) from by
        unfold SeamChainData.P; rw [show 3 * (i:ℕ) + 1 + 1 = 3 * (i:ℕ) + 2 from by ring]]
  rw [hu, hv]
  exact S.seam_u_v_split i

/-- `stepSign` of the seam walk at `j = 3i+2` is `-1` (the `vᵢ–γ_{i+1}` bridge merge),
for `i+1 < k`. -/
lemma stepSign_block_C (i : Fin S.k) (hi : (i:ℕ) + 1 < S.k) :
    stepSign S.p (seamList S.γ S.u S.v) (3 * (i:ℕ) + 2) = -1 := by
  have hj : 3 * (i:ℕ) + 2 + 1 < (seamList S.γ S.u S.v).length := by
    rw [seamList_length]; omega
  have hv : (seamList S.γ S.u S.v)[3 * (i:ℕ) + 2]'(by omega) = S.v i :=
    seamList_getElem_v S.γ S.u S.v i
  have hg : (seamList S.γ S.u S.v)[3 * (i:ℕ) + 2 + 1]'hj = S.γ ⟨(i:ℕ) + 1, hi⟩ := by
    rw [getElem_congr rfl (show 3 * (i:ℕ) + 2 + 1 = 3 * ((i:ℕ) + 1) from by ring)]
    have := seamList_getElem_gamma S.γ S.u S.v ⟨(i:ℕ) + 1, hi⟩
    simpa using this
  simp only [stepSign, dif_pos hj]
  rw [if_neg]
  rw [show (S.p * cycleOfList ((seamList S.γ S.u S.v).take (3 * (i:ℕ) + 2 + 1)))
        = S.P (3 * (i:ℕ) + 3) from by
        unfold SeamChainData.P; rw [show 3 * (i:ℕ) + 2 + 1 = 3 * (i:ℕ) + 3 from by ring]]
  rw [hv, hg]
  exact S.seam_v_gamma_merge i hi

/-- **The partial signed sum.**  For `n + 1 ≤ k`, the signed sum over the first
`3n+2` steps is `-(n)`: each block `i ≤ n` contributes its cancelling `(-1)+(+1)`
pair, and the `n` inter-block bridges each contribute `-1`. -/
lemma seam_partial_sum (n : ℕ) (hn : n + 1 ≤ S.k) :
    ∑ j ∈ Finset.range (3 * n + 2), stepSign S.p (seamList S.γ S.u S.v) j
      = -(n : ℤ) := by
  induction n with
  | zero =>
      -- range 2 = {0,1}: block A + block B at i = 0
      have h0 : (0 : ℕ) < S.k := S.hk
      rw [show 3 * 0 + 2 = 2 from rfl]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      have hA := S.stepSign_block_A ⟨0, h0⟩
      have hB := S.stepSign_block_B ⟨0, h0⟩
      simp only [Fin.val_mk, Nat.mul_zero, Nat.zero_add] at hA hB ⊢
      rw [hA, hB]; ring
  | succ n ih =>
      have hn' : n + 1 ≤ S.k := by omega
      have hsucc : (n : ℕ) + 1 < S.k := by omega
      -- range (3(n+1)+2) = range(3n+2) ∪ {3n+2, 3n+3, 3n+4}
      have hrange : 3 * (n + 1) + 2 = (3 * n + 2) + 1 + 1 + 1 := by ring
      rw [hrange, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        ih hn']
      -- the three new terms
      have hC := S.stepSign_block_C ⟨n, by omega⟩ (by simp only [Fin.val_mk]; omega)
      have hA := S.stepSign_block_A ⟨n + 1, hsucc⟩
      have hB := S.stepSign_block_B ⟨n + 1, hsucc⟩
      simp only [Fin.val_mk] at hC hA hB
      rw [show 3 * n + 2 = 3 * n + 2 from rfl, hC]
      rw [show 3 * n + 2 + 1 = 3 * (n + 1) from by ring, hA]
      rw [show 3 * n + 2 + 1 + 1 = 3 * (n + 1) + 1 from by ring, hB]
      push_cast
      ring

/-- **The one-chain count.**  `numCycles (p * formPerm (seamList γ u v)) =
numCycles p − (k − 1)` (integer form). -/
theorem numCycles_mul_seamChain_delta :
    ((numCycles (S.p * cycleOfList (seamList S.γ S.u S.v)) : ℤ)
      - (numCycles S.p : ℤ)) = -((S.k : ℤ) - 1) := by
  have hlen : (seamList S.γ S.u S.v).length = 3 * S.k := seamList_length S.γ S.u S.v
  have h3k : 3 * S.k - 1 + 1 ≤ (seamList S.γ S.u S.v).length := by
    rw [hlen]; have := S.hk; omega
  -- the walk delta up to consuming all 3k elements
  have hwalk := numCycles_take_delta S.p S.nodup_seam (3 * S.k - 1) h3k
  -- take (3k-1+1) = take (3k) = whole list
  have htake : (seamList S.γ S.u S.v).take (3 * S.k - 1 + 1) = seamList S.γ S.u S.v := by
    apply List.take_of_length_le
    rw [hlen]; have := S.hk; omega
  rw [htake] at hwalk
  rw [hwalk]
  -- the sum equals -((k-1)) via the partial-sum lemma at n = k-1
  have hk1 : 3 * (S.k - 1) + 2 = 3 * S.k - 1 := by have := S.hk; omega
  have hps := S.seam_partial_sum (S.k - 1) (by have := S.hk; omega)
  rw [hk1] at hps
  rw [hps]
  have := S.hk
  push_cast [Nat.cast_sub (by omega : 1 ≤ S.k)]
  ring

end SeamChainData

end SeamChain
