import ProofsInTheBook.PlanarMapCutCap

/-!
# The cut-and-cap vertex rotation `σ'` (Chapter 35 Jordan lemma, σ-half)

This file is the σ-rotation companion to `PlanarMapCutCap.lean`.  That file built
the new edge involution `cutAlpha` of the cut-and-cap surgery and proved the edge
count `E' = E + k` and the Euler jump `χ' = χ + 2`, isolating the σ-dependent
content (the new vertex rotation `σ'`, the vertex/face counts, and connectivity)
as the abstract bundle `CutCapSurgery`.

Here we **construct `σ'` concretely** and assemble the cut-and-cap `CombMap`
`N = ⟨cutAlpha, σ'⟩` explicitly, discharging the bundle's `alpha_eq` field by
construction.  This narrows the isolated core from "an abstract map satisfying
four fields" down to "three named orbit-count facts about *this concrete* `σ'`".

## The construction of `σ'` (design §3.1, enumeration-free form)

Write `q_i := dart i` (the forward cycle dart at `v_i`) and
`p_i := α (dart (prevIdx i))` (the reverse dart entering `v_i`).  Both have tail
`v_i`, so they lie in the same `σ`-orbit; by simplicity (`3 ≤ len`) the `2k`
darts `{p_i, q_i}` are pairwise distinct.  The `σ`-orbit at `v_i` splits at
`p_i, q_i` into two banks `[q_i, p_i)` (the `+` bank) and `[p_i, q_i)` (the `−`
bank).

The two **bank-end** darts at `v_i` are the darts whose `σ`-successor crosses the
bank boundary:

* `ℓ_i^+ := σ⁻¹ p_i` — the last `+`-bank dart (its `σ`-successor is `p_i`);
* `ℓ_i^- := σ⁻¹ q_i` — the last `−`-bank dart (its `σ`-successor is `q_i`).

These `2k` darts are distinct (`σ⁻¹` is injective and the `p_i, q_i` are
distinct).  The new rotation `σ'` on `D ⊕ (Fin k ⊕ Fin k)` is `σ` rerouted at the
bank ends through the caps:

```
σ' (ℓ_i^+)   = c_i^+        σ' (c_i^+) = q_i      -- + bank closes through its cap
σ' (ℓ_i^-)   = c_i^-        σ' (c_i^-) = p_i      -- − bank closes through its cap
σ' (inl d)   = inl (σ d)    -- every other original dart: old rotation
```

This is well defined (the `ℓ` darts are distinct, the caps are fresh) and is a
permutation; we prove it so by exhibiting the explicit inverse.

## Honest scope

* **Proved here (new content):** the concrete permutation `cutSigma`/`cutSigmaPerm`
  (full bijection proof), the concrete cut map `cutCapMap`, and the construction
  of a `CutCapSurgery` whose `alpha_eq` is discharged by `rfl`-level construction
  and whose `N` is the concrete `⟨cutAlpha, σ'⟩`.
* **Isolated (narrowed core):** the three remaining bundle fields — `vertex_count`
  (`V' = V + k`), `face_count` (`F' = F + 2`), and `connected_of_dual_path` — are
  the genuine orbit-count / connectivity facts about the *concrete* `σ'`.  They are
  packaged as the structure `CutSigmaCounts`, which is satisfiable (the genuine
  cut-and-cap map witnesses it) and from which `cutCapSurgery_of_counts` builds the
  `CutCapSurgery` bundle.  This is strictly less isolation than the prior abstract
  `CutCapSurgery`: the map, its `α`, and its `σ` are now all concrete and the only
  open facts are three orbit counts about an explicit permutation.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

/-! ## The bank-start darts `p_i, q_i` and their distinctness -/

/-- The forward cycle dart at `v_i` (the `+`-bank start). -/
def qDart (C : SimplePrimalCycle M) (i : Fin C.len) : D := C.dart i

/-- The reverse dart entering `v_i` (the `−`-bank start), `p_i = α (dart (prevIdx i))`. -/
def pDart (C : SimplePrimalCycle M) (i : Fin C.len) : D := M.α (C.dart (C.prevIdx i))

@[simp] lemma qDart_def (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.qDart i = C.dart i := rfl

@[simp] lemma pDart_def (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.pDart i = M.α (C.dart (C.prevIdx i)) := rfl

/-- `q`-darts are pairwise distinct. -/
lemma qDart_inj (C : SimplePrimalCycle M) : Function.Injective C.qDart :=
  C.dart_inj

/-- `p`-darts are pairwise distinct. -/
lemma pDart_inj (C : SimplePrimalCycle M) : Function.Injective C.pDart := by
  intro i j h
  simp only [pDart_def] at h
  have := C.dart_inj (M.α.injective h)
  exact C.nextIdx_inj (by rw [← C.nextIdx_prevIdx i, ← C.nextIdx_prevIdx j, this])

/-- A `p`-dart never equals a `q`-dart (rules out the digon, uses `3 ≤ len`). -/
lemma pDart_ne_qDart (C : SimplePrimalCycle M) (i j : Fin C.len) :
    C.pDart i ≠ C.qDart j := by
  simp only [pDart_def, qDart_def]
  exact fun h => C.dart_ne_alpha_dart j (C.prevIdx i) h.symm

/-! ## The bank-end classifier

A dart `d ∈ D` is a `+`-bank end at index `i` when `σ d = p_i` (so `σ' d = c_i^+`);
a `−`-bank end at index `i` when `σ d = q_i` (so `σ' d = c_i^-`); otherwise its
rotation is unchanged.  We classify by the *successor* `σ d`. -/

open Classical in
/-- Classify a dart by where its `σ`-successor sits among the bank-start darts:
`inl (inl i)` if `σ d = p_i` (`d` is the `+`-bank end `ℓ_i^+`); `inl (inr i)` if
`σ d = q_i` (`d` is the `−`-bank end `ℓ_i^-`); `inr ()` otherwise. -/
noncomputable def divertKind (C : SimplePrimalCycle M) (d : D) :
    (Fin C.len ⊕ Fin C.len) ⊕ Unit :=
  if hp : ∃ i, M.σ d = C.pDart i then Sum.inl (Sum.inl hp.choose)
  else if hq : ∃ i, M.σ d = C.qDart i then Sum.inl (Sum.inr hq.choose)
  else Sum.inr ()

open Classical in
lemma divertKind_plus (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : M.σ d = C.pDart i) : C.divertKind d = Sum.inl (Sum.inl i) := by
  have hp : ∃ j, M.σ d = C.pDart j := ⟨i, h⟩
  rw [divertKind, dif_pos hp]
  congr 2
  exact C.pDart_inj (hp.choose_spec.symm.trans h)

open Classical in
lemma divertKind_minus (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : M.σ d = C.qDart i) : C.divertKind d = Sum.inl (Sum.inr i) := by
  have hnp : ¬ ∃ j, M.σ d = C.pDart j := by
    rintro ⟨j, hj⟩; exact C.pDart_ne_qDart j i (hj.symm.trans h)
  have hq : ∃ j, M.σ d = C.qDart j := ⟨i, h⟩
  rw [divertKind, dif_neg hnp, dif_pos hq]
  congr 2
  exact C.qDart_inj (hq.choose_spec.symm.trans h)

open Classical in
lemma divertKind_none (C : SimplePrimalCycle M) {d : D}
    (hp : ∀ i, M.σ d ≠ C.pDart i) (hq : ∀ i, M.σ d ≠ C.qDart i) :
    C.divertKind d = Sum.inr () := by
  rw [divertKind, dif_neg (by rintro ⟨i, hi⟩; exact hp i hi),
    dif_neg (by rintro ⟨i, hi⟩; exact hq i hi)]

open Classical in
lemma divertKind_eq_plus (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.divertKind d = Sum.inl (Sum.inl i)) : M.σ d = C.pDart i := by
  rw [divertKind] at h
  by_cases hp : ∃ j, M.σ d = C.pDart j
  · rw [dif_pos hp] at h
    simp only [Sum.inl.injEq] at h
    rw [hp.choose_spec, h]
  · rw [dif_neg hp] at h; split at h <;> simp at h

open Classical in
lemma divertKind_eq_minus (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.divertKind d = Sum.inl (Sum.inr i)) : M.σ d = C.qDart i := by
  rw [divertKind] at h
  by_cases hp : ∃ j, M.σ d = C.pDart j
  · rw [dif_pos hp] at h; simp at h
  · rw [dif_neg hp] at h
    by_cases hq : ∃ j, M.σ d = C.qDart j
    · rw [dif_pos hq] at h
      simp only [Sum.inl.injEq, Sum.inr.injEq] at h
      rw [hq.choose_spec, h]
    · rw [dif_neg hq] at h; simp at h

open Classical in
lemma divertKind_eq_none (C : SimplePrimalCycle M) {d : D}
    (h : C.divertKind d = Sum.inr ()) :
    (∀ i, M.σ d ≠ C.pDart i) ∧ (∀ i, M.σ d ≠ C.qDart i) := by
  constructor
  · intro i hi; rw [C.divertKind_plus hi] at h; simp at h
  · intro i hi; rw [C.divertKind_minus hi] at h; simp at h

/-! ## The bank-start classifier (for the inverse rotation)

The inverse of `σ'` needs to recognise the bank-start darts `q_i, p_i`, which are
the images of the caps under `σ'`.  We classify a dart by whether it is a `q`-dart
(`σ' c_i^+ = q_i`), a `p`-dart (`σ' c_i^- = p_i`), or neither. -/

open Classical in
/-- Classify a dart by whether it is a bank-start dart: `inl (inl i)` if `d = q_i`,
`inl (inr i)` if `d = p_i`, `inr ()` otherwise. -/
noncomputable def startKind (C : SimplePrimalCycle M) (d : D) :
    (Fin C.len ⊕ Fin C.len) ⊕ Unit :=
  if hq : ∃ i, d = C.qDart i then Sum.inl (Sum.inl hq.choose)
  else if hp : ∃ i, d = C.pDart i then Sum.inl (Sum.inr hp.choose)
  else Sum.inr ()

open Classical in
lemma startKind_q (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.startKind (C.qDart i) = Sum.inl (Sum.inl i) := by
  have hq : ∃ j, C.qDart i = C.qDart j := ⟨i, rfl⟩
  rw [startKind, dif_pos hq]; congr 2; exact C.qDart_inj hq.choose_spec.symm

open Classical in
lemma startKind_p (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.startKind (C.pDart i) = Sum.inl (Sum.inr i) := by
  have hnq : ¬ ∃ j, C.pDart i = C.qDart j := by
    rintro ⟨j, hj⟩; exact C.pDart_ne_qDart i j hj
  have hp : ∃ j, C.pDart i = C.pDart j := ⟨i, rfl⟩
  rw [startKind, dif_neg hnq, dif_pos hp]; congr 2; exact C.pDart_inj hp.choose_spec.symm

open Classical in
lemma startKind_none (C : SimplePrimalCycle M) {d : D}
    (hq : ∀ i, d ≠ C.qDart i) (hp : ∀ i, d ≠ C.pDart i) :
    C.startKind d = Sum.inr () := by
  rw [startKind, dif_neg (by rintro ⟨i, hi⟩; exact hq i hi),
    dif_neg (by rintro ⟨i, hi⟩; exact hp i hi)]

open Classical in
lemma startKind_eq_q (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.startKind d = Sum.inl (Sum.inl i)) : d = C.qDart i := by
  rw [startKind] at h
  by_cases hq : ∃ j, d = C.qDart j
  · rw [dif_pos hq] at h; simp only [Sum.inl.injEq] at h; rw [hq.choose_spec, h]
  · rw [dif_neg hq] at h; split at h <;> simp at h

open Classical in
lemma startKind_eq_p (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.startKind d = Sum.inl (Sum.inr i)) : d = C.pDart i := by
  rw [startKind] at h
  by_cases hq : ∃ j, d = C.qDart j
  · rw [dif_pos hq] at h; simp at h
  · rw [dif_neg hq] at h
    by_cases hp : ∃ j, d = C.pDart j
    · rw [dif_pos hp] at h
      simp only [Sum.inl.injEq, Sum.inr.injEq] at h; rw [hp.choose_spec, h]
    · rw [dif_neg hp] at h; simp at h

open Classical in
lemma startKind_eq_none (C : SimplePrimalCycle M) {d : D}
    (h : C.startKind d = Sum.inr ()) :
    (∀ i, d ≠ C.qDart i) ∧ (∀ i, d ≠ C.pDart i) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [hi, C.startKind_q] at h; simp at h
  · rw [hi, C.startKind_p] at h; simp at h

/-! ## The new vertex rotation `σ'`

`cutSigma` is the forward map; `cutSigmaInv` the inverse.  We prove they invert
each other (`Equiv.mk`).  The forward map reroutes the bank ends through the caps;
the inverse map reroutes the bank starts back. -/

open Classical in
/-- Forward map of the cut-and-cap rotation `σ'`. -/
noncomputable def cutSigma (C : SimplePrimalCycle M) : C.CutDart → C.CutDart :=
  fun x => match x with
  | Sum.inl d =>
      match C.divertKind d with
      | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)   -- ℓ_i^+ ↦ c_i^+
      | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)   -- ℓ_i^- ↦ c_i^-
      | Sum.inr () => Sum.inl (M.σ d)                -- unchanged rotation
  | Sum.inr (Sum.inl i) => Sum.inl (C.qDart i)       -- c_i^+ ↦ q_i
  | Sum.inr (Sum.inr i) => Sum.inl (C.pDart i)       -- c_i^- ↦ p_i

open Classical in
/-- Inverse map of the cut-and-cap rotation `σ'`. -/
noncomputable def cutSigmaInv (C : SimplePrimalCycle M) : C.CutDart → C.CutDart :=
  fun x => match x with
  | Sum.inl d =>
      match C.startKind d with
      | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)   -- q_i ↦ c_i^+
      | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)   -- p_i ↦ c_i^-
      | Sum.inr () => Sum.inl (M.σ.symm d)           -- unchanged inverse rotation
  | Sum.inr (Sum.inl i) => Sum.inl (M.σ.symm (C.pDart i))  -- c_i^+ ↦ ℓ_i^+ = σ⁻¹ p_i
  | Sum.inr (Sum.inr i) => Sum.inl (M.σ.symm (C.qDart i))  -- c_i^- ↦ ℓ_i^- = σ⁻¹ q_i

/-! ### Forward map unfolding lemmas -/

lemma cutSigma_inl_plus (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.divertKind d = Sum.inl (Sum.inl i)) :
    C.cutSigma (Sum.inl d) = Sum.inr (Sum.inl i) := by
  show (match C.divertKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ d)) = _
  rw [h]

lemma cutSigma_inl_minus (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.divertKind d = Sum.inl (Sum.inr i)) :
    C.cutSigma (Sum.inl d) = Sum.inr (Sum.inr i) := by
  show (match C.divertKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ d)) = _
  rw [h]

lemma cutSigma_inl_none (C : SimplePrimalCycle M) {d : D}
    (h : C.divertKind d = Sum.inr ()) :
    C.cutSigma (Sum.inl d) = Sum.inl (M.σ d) := by
  show (match C.divertKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ d)) = _
  rw [h]

@[simp] lemma cutSigma_capPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutSigma (Sum.inr (Sum.inl i)) = Sum.inl (C.qDart i) := rfl

@[simp] lemma cutSigma_capMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutSigma (Sum.inr (Sum.inr i)) = Sum.inl (C.pDart i) := rfl

/-! ### Inverse map unfolding lemmas -/

lemma cutSigmaInv_inl_q (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.startKind d = Sum.inl (Sum.inl i)) :
    C.cutSigmaInv (Sum.inl d) = Sum.inr (Sum.inl i) := by
  show (match C.startKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ.symm d)) = _
  rw [h]

lemma cutSigmaInv_inl_p (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.startKind d = Sum.inl (Sum.inr i)) :
    C.cutSigmaInv (Sum.inl d) = Sum.inr (Sum.inr i) := by
  show (match C.startKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ.symm d)) = _
  rw [h]

lemma cutSigmaInv_inl_none (C : SimplePrimalCycle M) {d : D}
    (h : C.startKind d = Sum.inr ()) :
    C.cutSigmaInv (Sum.inl d) = Sum.inl (M.σ.symm d) := by
  show (match C.startKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ.symm d)) = _
  rw [h]

@[simp] lemma cutSigmaInv_capPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutSigmaInv (Sum.inr (Sum.inl i)) = Sum.inl (M.σ.symm (C.pDart i)) := rfl

@[simp] lemma cutSigmaInv_capMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutSigmaInv (Sum.inr (Sum.inr i)) = Sum.inl (M.σ.symm (C.qDart i)) := rfl

/-! ### `cutSigma` is a bijection -/

open Classical in
lemma cutSigma_leftInv (C : SimplePrimalCycle M) :
    Function.LeftInverse C.cutSigmaInv C.cutSigma := by
  intro x
  rcases x with d | (i | i)
  · -- x = inl d, split on divertKind d
    rcases hd : C.divertKind d with (i | i) | u
    · -- σ d = p_i : ℓ_i^+
      have hσ : M.σ d = C.pDart i := C.divertKind_eq_plus hd
      rw [C.cutSigma_inl_plus hd, cutSigmaInv_capPlus]
      rw [← hσ, M.σ.symm_apply_apply]
    · -- σ d = q_i : ℓ_i^-
      have hσ : M.σ d = C.qDart i := C.divertKind_eq_minus hd
      rw [C.cutSigma_inl_minus hd, cutSigmaInv_capMinus]
      rw [← hσ, M.σ.symm_apply_apply]
    · -- unchanged
      obtain ⟨hp, hq⟩ := C.divertKind_eq_none hd
      rw [C.cutSigma_inl_none hd, C.cutSigmaInv_inl_none (C.startKind_none hq hp),
        M.σ.symm_apply_apply]
  · -- x = c_i^+
    rw [cutSigma_capPlus, C.cutSigmaInv_inl_q (C.startKind_q i)]
  · -- x = c_i^-
    rw [cutSigma_capMinus, C.cutSigmaInv_inl_p (C.startKind_p i)]

open Classical in
lemma cutSigma_rightInv (C : SimplePrimalCycle M) :
    Function.RightInverse C.cutSigmaInv C.cutSigma := by
  intro x
  rcases x with d | (i | i)
  · -- x = inl d, split on startKind d
    rcases hd : C.startKind d with (i | i) | u
    · -- d = q_i
      have hq : d = C.qDart i := C.startKind_eq_q hd
      rw [C.cutSigmaInv_inl_q hd, cutSigma_capPlus, hq]
    · -- d = p_i
      have hp : d = C.pDart i := C.startKind_eq_p hd
      rw [C.cutSigmaInv_inl_p hd, cutSigma_capMinus, hp]
    · -- neither: d ≠ q_i, p_i for all i
      obtain ⟨hq, hp⟩ := C.startKind_eq_none hd
      rw [C.cutSigmaInv_inl_none hd]
      have hdiv : C.divertKind (M.σ.symm d) = Sum.inr () := by
        apply C.divertKind_none
        · intro i; rw [M.σ.apply_symm_apply]; exact hp i
        · intro i; rw [M.σ.apply_symm_apply]; exact hq i
      rw [C.cutSigma_inl_none hdiv, M.σ.apply_symm_apply]
  · -- x = c_i^+ : σ⁻¹ p_i ↦ back to c_i^+
    rw [cutSigmaInv_capPlus]
    have hdiv : C.divertKind (M.σ.symm (C.pDart i)) = Sum.inl (Sum.inl i) :=
      C.divertKind_plus (by rw [M.σ.apply_symm_apply])
    rw [C.cutSigma_inl_plus hdiv]
  · -- x = c_i^-
    rw [cutSigmaInv_capMinus]
    have hdiv : C.divertKind (M.σ.symm (C.qDart i)) = Sum.inl (Sum.inr i) :=
      C.divertKind_minus (by rw [M.σ.apply_symm_apply])
    rw [C.cutSigma_inl_minus hdiv]

/-- The new vertex rotation `σ'` as a permutation of the cut dart set. -/
noncomputable def cutSigmaPerm (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart where
  toFun := C.cutSigma
  invFun := C.cutSigmaInv
  left_inv := C.cutSigma_leftInv
  right_inv := C.cutSigma_rightInv

@[simp] lemma cutSigmaPerm_apply (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.cutSigmaPerm x = C.cutSigma x := rfl

/-! ## The concrete cut-and-cap map

`cutCapMap` is the `CombMap` on `C.CutDart` with edge involution `cutAlphaPerm`
(constructed and proved fixed-point-free involution in `PlanarMapCutCap.lean`) and
vertex rotation `cutSigmaPerm`. -/

/-- The concrete cut-and-cap combinatorial map. -/
noncomputable def cutCapMap (C : SimplePrimalCycle M) : CombMap C.CutDart where
  α := C.cutAlphaPerm
  σ := C.cutSigmaPerm
  α_invol := by
    ext x
    show C.cutAlpha (C.cutAlpha x) = x
    exact C.cutAlpha_involutive x
  α_no_fixed := by
    intro x
    show C.cutAlpha x ≠ x
    exact C.cutAlpha_no_fixed x

@[simp] lemma cutCapMap_alpha (C : SimplePrimalCycle M) :
    (C.cutCapMap).α = C.cutAlphaPerm := rfl

@[simp] lemma cutCapMap_sigma (C : SimplePrimalCycle M) :
    (C.cutCapMap).σ = C.cutSigmaPerm := rfl

/-! ### `σ'` closed forms at the seam

`φ' = σ' ∘ α'`.  These closed forms record exactly how the rotation reroutes at
the bank ends and how the caps re-enter the banks; they are the inputs to the
orbit-count facts.

* `σ' c_i^+ = q_i` and `σ' c_i^- = p_i` — the caps re-enter their banks at the
  bank-start darts (by definition).
* The bank-end darts divert to the caps: if `σ d = p_i` then `σ' (inl d) = c_i^+`;
  if `σ d = q_i` then `σ' (inl d) = c_i^-`.
* Every other original dart keeps its rotation `σ' (inl d) = inl (σ d)`. -/

/-- `σ' (c_i^+) = q_i`: the `+`-cap re-enters its bank at the `+`-bank start. -/
lemma cutSigma_capPlus_eq (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap).σ (Sum.inr (Sum.inl i)) = Sum.inl (C.qDart i) := rfl

/-- `σ' (c_i^-) = p_i`: the `−`-cap re-enters its bank at the `−`-bank start. -/
lemma cutSigma_capMinus_eq (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap).σ (Sum.inr (Sum.inr i)) = Sum.inl (C.pDart i) := rfl

/-- A bank-end dart `ℓ_i^+ = σ⁻¹ p_i` diverts into the `+`-cap `c_i^+`. -/
lemma cutSigma_plusEnd (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : M.σ d = C.pDart i) :
    (C.cutCapMap).σ (Sum.inl d) = Sum.inr (Sum.inl i) :=
  C.cutSigma_inl_plus (C.divertKind_plus h)

/-- A bank-end dart `ℓ_i^- = σ⁻¹ q_i` diverts into the `−`-cap `c_i^-`. -/
lemma cutSigma_minusEnd (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : M.σ d = C.qDart i) :
    (C.cutCapMap).σ (Sum.inl d) = Sum.inr (Sum.inr i) :=
  C.cutSigma_inl_minus (C.divertKind_minus h)

/-- Away from the bank ends the rotation is unchanged: `σ' (inl d) = inl (σ d)`. -/
lemma cutSigma_clean (C : SimplePrimalCycle M) {d : D}
    (hp : ∀ i, M.σ d ≠ C.pDart i) (hq : ∀ i, M.σ d ≠ C.qDart i) :
    (C.cutCapMap).σ (Sum.inl d) = Sum.inl (M.σ d) :=
  C.cutSigma_inl_none (C.divertKind_none hp hq)

end SimplePrimalCycle

/-! ## Assembling the surgery bundle from the concrete map

The concrete map `C.cutCapMap` already discharges the edge involution (it *is*
`cutAlphaPerm`), so the only open content is the three orbit-count / connectivity
facts about this explicit `σ'`.  We package them as `CutSigmaCounts` — a bundle on
the **concrete** map — and convert it to the `CutCapSurgery` bundle of
`PlanarMapCutCap.lean` with `alpha_eq` discharged by `rfl`.

This is strictly tighter isolation than the original abstract `CutCapSurgery`: the
map, its `α`, and its `σ` are all now concrete and the open facts are three
orbit-count statements about a single explicit permutation. -/

/-- The three orbit-count / connectivity facts of the cut-and-cap surgery, stated
about the **concrete** cut map `C.cutCapMap`.

* `vertex_count`: each cycle vertex's `σ`-orbit splits into its two banks under
  `σ'`, raising the vertex count by `k` (design §3.2, transposition split count).
* `face_count`: the old faces survive (rerouted) and the caps add two new faces,
  raising the face count by `2` (design §3.2).
* `connected_of_dual_path`: a cycle-avoiding dual path between the two faces of a
  cycle edge makes the cut map connected (design §4). -/
structure CutSigmaCounts (M : CombMap D) (C : SimplePrimalCycle M) : Prop where
  /-- Vertex count rises by `k`. -/
  vertex_count : (C.cutCapMap).V = M.V + C.len
  /-- Face count rises by `2`. -/
  face_count : (C.cutCapMap).F = M.F + 2
  /-- Connectivity from a cycle-avoiding dual path. -/
  connected_of_dual_path : ∀ i : Fin C.len,
    DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
      (C.cutCapMap).Connected

/-- **Assemble the surgery bundle from the concrete map.**  Given the three
orbit-count facts about the explicit `σ'`, build the `CutCapSurgery` bundle whose
underlying map is the concrete `C.cutCapMap`; `alpha_eq` holds by construction. -/
noncomputable def CutSigmaCounts.toSurgery {M : CombMap D} {C : SimplePrimalCycle M}
    (h : CutSigmaCounts M C) : CutCapSurgery M C where
  N := C.cutCapMap
  alpha_eq := rfl
  vertex_count := h.vertex_count
  face_count := h.face_count
  connected_of_dual_path := h.connected_of_dual_path

/-- **The Jordan lemma from the concrete cut-and-cap map.**  Conditional only on
the three orbit-count facts (`CutSigmaCounts`, satisfiable by the genuine surgery)
and the sanctioned Euler inequality `chi_le` for the *concrete* cut map: the two
faces of a cycle edge are not joined by a cycle-avoiding dual path.  This is the
end-to-end statement with `σ'` fully constructed (the abstract `CutCapSurgery`
bundle of `PlanarMapCutCap` no longer appears — its `N`, `α'`, `σ'` are all
explicit here). -/
theorem jordan_simple_cycle_of_counts {M : CombMap D} {C : SimplePrimalCycle M}
    (h : CutSigmaCounts M C)
    (hchi : M.eulerChar = 2)
    (chi_le : (C.cutCapMap).Connected → (C.cutCapMap).eulerChar ≤ 2)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  h.toSurgery.jordan_simple_cycle hchi chi_le i

end CombMap

end ProofsInTheBook.PlanarMap
