import ProofsInTheBook.PlanarMapCutCapSigma

/-!
# The CORRECTED cut-and-cap vertex rotation `σ'` (Chapter 35 Jordan lemma, σ-half)

This file is a **fix** of `PlanarMapCutCapSigma.lean`.  The kernel arbitration in
`PlanarMapCutCapEval.lean` established (by direct `#eval` of the orbit counts of
the *implemented* `cutSigma`, mirrored clause-for-clause) that the implemented
surgery on the triangle sphere map yields

```
V' = 6,  E' = 6,  F' = 8,  χ' = 8,  c = 4 components
```

whereas the design (`HANDOFF/CH35_JORDAN_DESIGN.md` §3.1) intends

```
V' = 6,  E' = 6,  F' = 4,  χ' = 4,  c = 2 components.
```

## Diagnosis (the off-by-one cap-splice bug)

The cap dart `c_i^+` is `α'`-paired with `dart i = q_i`, the `+`-bank start at
`v_i`.  Since `q_i` leaves `v_i` for `v_{i+1}`, the cap `c_i^+` has its **tail at
`v_{i+1}^+`** (the head of `dart i`).  Therefore it must be spliced into the
rotation at the bank-end `ℓ_{i+1}^+ = σ⁻¹ p_{i+1}` of vertex `v_{i+1}^+`, **not**
at `ℓ_i^+`.  The implementation wired `σ'(ℓ_i^+) = c_i^+` (and `σ'(c_i^+) = q_i`),
which splices `c_i^+` at the *wrong* vertex.  This shatters the `+` cap into `k`
fixed `φ'`-orbits and merges them incorrectly, giving `c = 4` and `F' = F + 2c − 2`
instead of `F' = F + 2`.

The `−` bank was already correct (`c_i^-` has tail `v_i^-`, spliced at `ℓ_i^-`).

## The corrected `σ'`

```
σ' (ℓ_i^+) = c_{prevIdx i}^+      σ' (c_i^+) = inl (dart (nextIdx i))   -- + cap FIXED
σ' (ℓ_i^-) = c_i^-               σ' (c_i^-) = inl (p_i)                -- − cap (as before)
σ' (inl d) = inl (σ d)           otherwise
```

The corrected map is verified by the kernel (`cutSigmaC2` in
`PlanarMapCutCapEval.lean`) to give `V'=6, E'=6, F'=4, χ'=4, c=2` on the triangle
and `V'=7, E'=9, F'=6, χ'=4, c=2` on the tetrahedron — exactly the design intent,
with both original faces preserved and two cap faces added.

This file constructs the corrected `σ'` as an honest `Equiv.Perm` (full inverse,
5-case `left_inv`/`right_inv` bash, mirroring the original file), assembles the
corrected `cutCapMap2 : CombMap C.CutDart`, and restates the orbit-count targets
as named Props (`CutSigmaCounts2`) for the corrected map.  `α'` is unchanged, so
the `cutAlpha` involution facts import directly.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

/-! ## The corrected vertex rotation `σ'₂`

We reuse `divertKind` (classify `inl d` by whether `σ d = p_i` or `σ d = q_i`) and
`startKind` (classify `inl d` by whether `d = q_i` or `d = p_i`) from
`PlanarMapCutCapSigma.lean`, together with `pDart`, `qDart`, `nextIdx`, `prevIdx`
and all their lemmas.  Only the cap index wiring changes. -/

open Classical in
/-- Corrected forward map of the cut-and-cap rotation `σ'`. -/
noncomputable def cutSigma2 (C : SimplePrimalCycle M) : C.CutDart → C.CutDart :=
  fun x => match x with
  | Sum.inl d =>
      match C.divertKind d with
      | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl (C.prevIdx i))  -- ℓ_i^+ ↦ c_{prevIdx i}^+  (FIX)
      | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)             -- ℓ_i^- ↦ c_i^-
      | Sum.inr () => Sum.inl (M.σ d)                          -- unchanged rotation
  | Sum.inr (Sum.inl i) => Sum.inl (C.dart (C.nextIdx i))      -- c_i^+ ↦ dart (nextIdx i)  (FIX)
  | Sum.inr (Sum.inr i) => Sum.inl (C.pDart i)                 -- c_i^- ↦ p_i

open Classical in
/-- Corrected inverse map of the cut-and-cap rotation `σ'`. -/
noncomputable def cutSigmaInv2 (C : SimplePrimalCycle M) : C.CutDart → C.CutDart :=
  fun x => match x with
  | Sum.inl d =>
      match C.startKind d with
      | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl (C.prevIdx i))  -- d = q_i ↦ c_{prevIdx i}^+  (FIX)
      | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)             -- d = p_i ↦ c_i^-
      | Sum.inr () => Sum.inl (M.σ.symm d)                     -- unchanged inverse rotation
  | Sum.inr (Sum.inl i) => Sum.inl (M.σ.symm (C.pDart (C.nextIdx i)))  -- c_i^+ ↦ ℓ_{i+1}^+ = σ⁻¹ p_{i+1}
  | Sum.inr (Sum.inr i) => Sum.inl (M.σ.symm (C.qDart i))             -- c_i^- ↦ ℓ_i^- = σ⁻¹ q_i

/-! ### Forward map unfolding lemmas -/

lemma cutSigma2_inl_plus (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.divertKind d = Sum.inl (Sum.inl i)) :
    C.cutSigma2 (Sum.inl d) = Sum.inr (Sum.inl (C.prevIdx i)) := by
  show (match C.divertKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl (C.prevIdx i))
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ d)) = _
  rw [h]

lemma cutSigma2_inl_minus (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.divertKind d = Sum.inl (Sum.inr i)) :
    C.cutSigma2 (Sum.inl d) = Sum.inr (Sum.inr i) := by
  show (match C.divertKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl (C.prevIdx i))
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ d)) = _
  rw [h]

lemma cutSigma2_inl_none (C : SimplePrimalCycle M) {d : D}
    (h : C.divertKind d = Sum.inr ()) :
    C.cutSigma2 (Sum.inl d) = Sum.inl (M.σ d) := by
  show (match C.divertKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl (C.prevIdx i))
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ d)) = _
  rw [h]

@[simp] lemma cutSigma2_capPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutSigma2 (Sum.inr (Sum.inl i)) = Sum.inl (C.dart (C.nextIdx i)) := rfl

@[simp] lemma cutSigma2_capMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutSigma2 (Sum.inr (Sum.inr i)) = Sum.inl (C.pDart i) := rfl

/-! ### Inverse map unfolding lemmas -/

lemma cutSigmaInv2_inl_q (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.startKind d = Sum.inl (Sum.inl i)) :
    C.cutSigmaInv2 (Sum.inl d) = Sum.inr (Sum.inl (C.prevIdx i)) := by
  show (match C.startKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl (C.prevIdx i))
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ.symm d)) = _
  rw [h]

lemma cutSigmaInv2_inl_p (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.startKind d = Sum.inl (Sum.inr i)) :
    C.cutSigmaInv2 (Sum.inl d) = Sum.inr (Sum.inr i) := by
  show (match C.startKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl (C.prevIdx i))
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ.symm d)) = _
  rw [h]

lemma cutSigmaInv2_inl_none (C : SimplePrimalCycle M) {d : D}
    (h : C.startKind d = Sum.inr ()) :
    C.cutSigmaInv2 (Sum.inl d) = Sum.inl (M.σ.symm d) := by
  show (match C.startKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl (C.prevIdx i))
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ.symm d)) = _
  rw [h]

@[simp] lemma cutSigmaInv2_capPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutSigmaInv2 (Sum.inr (Sum.inl i)) = Sum.inl (M.σ.symm (C.pDart (C.nextIdx i))) := rfl

@[simp] lemma cutSigmaInv2_capMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutSigmaInv2 (Sum.inr (Sum.inr i)) = Sum.inl (M.σ.symm (C.qDart i)) := rfl

/-! ### `cutSigma2` is a bijection -/

open Classical in
lemma cutSigma2_leftInv (C : SimplePrimalCycle M) :
    Function.LeftInverse C.cutSigmaInv2 C.cutSigma2 := by
  intro x
  rcases x with d | (i | i)
  · -- x = inl d, split on divertKind d
    rcases hd : C.divertKind d with (i | i) | u
    · -- σ d = p_i : ℓ_i^+, goes to c_{prevIdx i}^+, must come back to inl d
      have hσ : M.σ d = C.pDart i := C.divertKind_eq_plus hd
      rw [C.cutSigma2_inl_plus hd, cutSigmaInv2_capPlus, C.nextIdx_prevIdx, ← hσ,
        M.σ.symm_apply_apply]
    · -- σ d = q_i : ℓ_i^-, goes to c_i^-, must come back
      have hσ : M.σ d = C.qDart i := C.divertKind_eq_minus hd
      rw [C.cutSigma2_inl_minus hd, cutSigmaInv2_capMinus, ← hσ, M.σ.symm_apply_apply]
    · -- unchanged
      obtain ⟨hp, hq⟩ := C.divertKind_eq_none hd
      rw [C.cutSigma2_inl_none hd, C.cutSigmaInv2_inl_none (C.startKind_none hq hp),
        M.σ.symm_apply_apply]
  · -- x = c_i^+ : σ' c_i^+ = inl (dart (nextIdx i)) = inl (q_{nextIdx i})
    rw [cutSigma2_capPlus]
    -- dart (nextIdx i) = qDart (nextIdx i); startKind sees it as q-dart at nextIdx i
    rw [show C.dart (C.nextIdx i) = C.qDart (C.nextIdx i) from rfl,
      C.cutSigmaInv2_inl_q (C.startKind_q (C.nextIdx i)), C.prevIdx_nextIdx]
  · -- x = c_i^- : σ' c_i^- = inl (p_i); startKind sees it as p-dart at i
    rw [cutSigma2_capMinus,
      show C.pDart i = C.pDart i from rfl, C.cutSigmaInv2_inl_p (C.startKind_p i)]

open Classical in
lemma cutSigma2_rightInv (C : SimplePrimalCycle M) :
    Function.RightInverse C.cutSigmaInv2 C.cutSigma2 := by
  intro x
  rcases x with d | (i | i)
  · -- x = inl d, split on startKind d
    rcases hd : C.startKind d with (i | i) | u
    · -- d = q_i : goes to c_{prevIdx i}^+, must come back to inl d = inl q_i
      have hq : d = C.qDart i := C.startKind_eq_q hd
      rw [C.cutSigmaInv2_inl_q hd, cutSigma2_capPlus, C.nextIdx_prevIdx, hq]; rfl
    · -- d = p_i : goes to c_i^-, must come back to inl p_i
      have hp : d = C.pDart i := C.startKind_eq_p hd
      rw [C.cutSigmaInv2_inl_p hd, cutSigma2_capMinus, hp]
    · -- neither
      obtain ⟨hq, hp⟩ := C.startKind_eq_none hd
      rw [C.cutSigmaInv2_inl_none hd]
      have hdiv : C.divertKind (M.σ.symm d) = Sum.inr () := by
        apply C.divertKind_none
        · intro i; rw [M.σ.apply_symm_apply]; exact hp i
        · intro i; rw [M.σ.apply_symm_apply]; exact hq i
      rw [C.cutSigma2_inl_none hdiv, M.σ.apply_symm_apply]
  · -- x = c_i^+ : inv sends it to inl (σ⁻¹ p_{nextIdx i}) = ℓ_{nextIdx i}^+,
    -- which σ' sends to c_{prevIdx (nextIdx i)}^+ = c_i^+
    rw [cutSigmaInv2_capPlus]
    have hdiv : C.divertKind (M.σ.symm (C.pDart (C.nextIdx i))) = Sum.inl (Sum.inl (C.nextIdx i)) :=
      C.divertKind_plus (by rw [M.σ.apply_symm_apply])
    rw [C.cutSigma2_inl_plus hdiv, C.prevIdx_nextIdx]
  · -- x = c_i^- : inv sends it to inl (σ⁻¹ q_i) = ℓ_i^-, which σ' sends to c_i^-
    rw [cutSigmaInv2_capMinus]
    have hdiv : C.divertKind (M.σ.symm (C.qDart i)) = Sum.inl (Sum.inr i) :=
      C.divertKind_minus (by rw [M.σ.apply_symm_apply])
    rw [C.cutSigma2_inl_minus hdiv]

/-- The corrected vertex rotation `σ'` as a permutation of the cut dart set. -/
noncomputable def cutSigmaPerm2 (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart where
  toFun := C.cutSigma2
  invFun := C.cutSigmaInv2
  left_inv := C.cutSigma2_leftInv
  right_inv := C.cutSigma2_rightInv

@[simp] lemma cutSigmaPerm2_apply (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.cutSigmaPerm2 x = C.cutSigma2 x := rfl

/-! ## The corrected concrete cut-and-cap map

`α'` is unchanged (`cutAlphaPerm`); only `σ'` is corrected. -/

/-- The corrected concrete cut-and-cap combinatorial map. -/
noncomputable def cutCapMap2 (C : SimplePrimalCycle M) : CombMap C.CutDart where
  α := C.cutAlphaPerm
  σ := C.cutSigmaPerm2
  α_invol := by
    ext x
    show C.cutAlpha (C.cutAlpha x) = x
    exact C.cutAlpha_involutive x
  α_no_fixed := by
    intro x
    show C.cutAlpha x ≠ x
    exact C.cutAlpha_no_fixed x

@[simp] lemma cutCapMap2_alpha (C : SimplePrimalCycle M) :
    (C.cutCapMap2).α = C.cutAlphaPerm := rfl

@[simp] lemma cutCapMap2_sigma (C : SimplePrimalCycle M) :
    (C.cutCapMap2).σ = C.cutSigmaPerm2 := rfl

/-! ### Corrected `σ'` closed forms at the seam (inputs to the orbit counts) -/

/-- `σ' (c_i^+) = dart (nextIdx i)`: the `+`-cap re-enters its bank at the next
forward cycle dart (the corrected wiring). -/
lemma cutSigma2_capPlus_eq (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap2).σ (Sum.inr (Sum.inl i)) = Sum.inl (C.dart (C.nextIdx i)) := rfl

/-- `σ' (c_i^-) = p_i`: the `−`-cap re-enters its bank at the `−`-bank start. -/
lemma cutSigma2_capMinus_eq (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap2).σ (Sum.inr (Sum.inr i)) = Sum.inl (C.pDart i) := rfl

/-- A `+`-bank-end dart `ℓ_i^+ = σ⁻¹ p_i` diverts into the *previous* `+`-cap
`c_{prevIdx i}^+` (the corrected splice). -/
lemma cutSigma2_plusEnd (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : M.σ d = C.pDart i) :
    (C.cutCapMap2).σ (Sum.inl d) = Sum.inr (Sum.inl (C.prevIdx i)) :=
  C.cutSigma2_inl_plus (C.divertKind_plus h)

/-- A `−`-bank-end dart `ℓ_i^- = σ⁻¹ q_i` diverts into the `−`-cap `c_i^-`. -/
lemma cutSigma2_minusEnd (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : M.σ d = C.qDart i) :
    (C.cutCapMap2).σ (Sum.inl d) = Sum.inr (Sum.inr i) :=
  C.cutSigma2_inl_minus (C.divertKind_minus h)

/-- Away from the bank ends the rotation is unchanged: `σ' (inl d) = inl (σ d)`. -/
lemma cutSigma2_clean (C : SimplePrimalCycle M) {d : D}
    (hp : ∀ i, M.σ d ≠ C.pDart i) (hq : ∀ i, M.σ d ≠ C.qDart i) :
    (C.cutCapMap2).σ (Sum.inl d) = Sum.inl (M.σ d) :=
  C.cutSigma2_inl_none (C.divertKind_none hp hq)

end SimplePrimalCycle

/-! ## Orbit-count targets for the corrected map (named Props for the next round)

`α'` is unchanged, so the edge count `E' = E + k` transfers from
`CutCapSurgery.edge_count` (it depends only on `cutAlpha`).  The three remaining
facts are stated about the *corrected* concrete map `C.cutCapMap2`.  The kernel
arbitration (`PlanarMapCutCapEval.lean`) confirms they hold on the triangle
(`V'=6, E'=6, F'=4, c=2`) and tetrahedron (`V'=7, E'=9, F'=6, c=2`); their general
proofs are the genus-0-per-component Euler count, left as the next-round target. -/

/-- The three orbit-count / connectivity facts of the **corrected** cut-and-cap
surgery, stated about the corrected concrete map `C.cutCapMap2`.  With the
corrected `σ'` these are the genuine design numbers (`F' = F + 2`, two
components). -/
structure CutSigmaCounts2 (M : CombMap D) (C : SimplePrimalCycle M) : Prop where
  /-- Vertex count rises by `k`. -/
  vertex_count : (C.cutCapMap2).V = M.V + C.len
  /-- Face count rises by `2` (now genuinely achievable: the two cap faces are
  `c_0^+ … c_{k-1}^+` and the reversed `c_{k-1}^- … c_0^-`). -/
  face_count : (C.cutCapMap2).F = M.F + 2
  /-- Connectivity from a cycle-avoiding dual path. -/
  connected_of_dual_path : ∀ i : Fin C.len,
    DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
      (C.cutCapMap2).Connected

/-- **Edge count of the corrected map** — proved unconditionally, since `α'` is
unchanged.  `cutAlpha` is a fixed-point-free involution, so `E' = E + k`. -/
theorem cutCapMap2_edge_count {M : CombMap D} (C : SimplePrimalCycle M) :
    (C.cutCapMap2).E = M.E + C.len := by
  have hN : 2 * (C.cutCapMap2).E = Fintype.card C.CutDart := (C.cutCapMap2).two_mul_E_eq_card
  have hM : 2 * M.E = Fintype.card D := M.two_mul_E_eq_card
  have hcard : Fintype.card C.CutDart = Fintype.card D + 2 * C.len := by
    simp [CombMap.SimplePrimalCycle.CutDart, Fintype.card_sum, Fintype.card_fin]
    ring
  omega

/-- **The Euler jump for the corrected map**, conditional on the corrected vertex
and face counts.  With `V' = V + k`, `E' = E + k`, `F' = F + 2` we get
`χ' = χ + 2`. -/
theorem cutCapMap2_eulerChar_eq {M : CombMap D} {C : SimplePrimalCycle M}
    (h : CutSigmaCounts2 M C) :
    (C.cutCapMap2).eulerChar = M.eulerChar + 2 := by
  unfold CombMap.eulerChar
  rw [h.vertex_count, cutCapMap2_edge_count, h.face_count]
  push_cast
  ring

/-- **The Jordan lemma from the corrected cut-and-cap map**, conditional on the
corrected orbit counts and the Euler inequality.  Identical contradiction to the
original (`χ' = 4` for a connected map of `χ ≤ 2`), now resting on the corrected
surgery whose `F' = F + 2` is the genuine design number. -/
theorem jordan_simple_cycle_of_counts2 {M : CombMap D} {C : SimplePrimalCycle M}
    (h : CutSigmaCounts2 M C)
    (hchi : M.eulerChar = 2)
    (chi_le : (C.cutCapMap2).Connected → (C.cutCapMap2).eulerChar ≤ 2)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) := by
  intro hpath
  have hconn : (C.cutCapMap2).Connected := h.connected_of_dual_path i hpath
  have hjump : (C.cutCapMap2).eulerChar = 4 := by
    rw [cutCapMap2_eulerChar_eq h, hchi]; norm_num
  have hle : (C.cutCapMap2).eulerChar ≤ 2 := chi_le hconn
  rw [hjump] at hle
  norm_num at hle

end CombMap

end ProofsInTheBook.PlanarMap
