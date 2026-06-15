import ProofsInTheBook.ZinanCh35BankCount
import ProofsInTheBook.ZinanCh35StarConn

/-!
# Chapter 35, Step 2: the GENERAL simple-cycle bank theorem (`SimpleCycleBankTheorem`)

This file generalizes the LANDED outer-cycle two-component / boundary-bank result
(`ZinanCh35OuterSlack` + `ZinanCh35BankCount`, proved only for `C = outerCycle`) to an
**arbitrary** `SimplePrimalCycle M` on a sphere (`IsSphereMap`) simple-graph
(`IsSimpleGraph`) map `M`.

## The generalization (R6 §0/§4)

For an arbitrary `C : SimplePrimalCycle M` the deleted set is `C.dartSet` (the forward
darts and their `α`-reverses, `2·C.len` darts, `C.len` disjoint edges).  Set
`cycleDualAlpha C := rawAlpha M C.dartSet hclosed` (the dual sub-involution that fixes the
cycle darts and equals `M.α` off them).  Then, exactly as for the outer cycle:

* `genusSlack M.φ (cycleDualAlpha C) = 0` (edge deletion keeps the genus-0 dual slack at 0);
* `Ehalf (cycleDualAlpha C) = M.E − C.len`;
* `numCycles (M.φ * cycleDualAlpha C) = M.V − C.len + 2` — **the bank count**;
* `numComponents M.φ (cycleDualAlpha C) = numComp (DualAvoidsCycleStep M C)` (dart-face
  bridge);
* expanding `genusSlack = 0` with Euler forces `numComp (DualAvoidsCycleStep M C) = 2`.

### Why the bank count generalizes (R6 §0)

`M.φ * cycleDualAlpha C = M.σ * cycleTau C`, where `cycleTau C := M.α * cycleDualAlpha C`
is the identity off `C.dartSet` and equals `M.α` on it — i.e. the `C.len` **disjoint outer
transpositions** `(C.dart i, M.α (C.dart i))`.  The swap `(C.dart i, M.α (C.dart i))`
connects the `σ`-orbit at vertex `tail (C.dart i)` to the `σ`-orbit at
`tail (M.α (C.dart i)) = head (C.dart i) = tail (C.dart (nextIdx i))`.  Because
`nextIdx`/`prevIdx` is a single cycle on `Fin C.len` and the `C.len` tail-vertices are
pairwise distinct (`tail_inj`), the `C.len` swaps form a single cyclic chain over the
`C.len` distinct vertex `σ`-orbits: `C.len − 1` merges and one closing split, giving exactly
**two** bank cycles.

Unlike the outer-cycle proof (where the forward boundary darts `q i` themselves formed one
bank because `σ (α (q i)) = q (next i)`), here BOTH banks thread `σ`-segments; the merge/split
dynamics are driven purely by the tail-vertex same-cycle structure (`SameCycle ↔ equal
tails`), which makes the generalization both faithful and self-contained.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35CycleBank

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35OuterSlack
open Equiv Equiv.Perm

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}

/-! ## Setup: the deleted set `C.dartSet`, its `α`-closedness and cardinality. -/

variable (C : SimplePrimalCycle M)

/-- `C.dartSet` is `α`-closed: it is symmetric under `M.α` by construction
(`d = C.dart i` ↦ `α d = α (C.dart i)`, and `d = α (C.dart i)` ↦ `α d = C.dart i`). -/
lemma dartSet_alpha_closed :
    ∀ d : D, d ∈ C.dartSet → M.α d ∈ C.dartSet := by
  intro d hd
  rw [C.mem_dartSet_iff] at hd ⊢
  obtain ⟨i, hi | hi⟩ := hd
  · exact ⟨i, Or.inr (by rw [hi])⟩
  · exact ⟨i, Or.inl (by rw [hi, M.alpha_alpha])⟩

/-- The restricted dual involution for the cycle: fixes the cycle darts, `= M.α` elsewhere. -/
noncomputable def cycleDualAlpha (C : SimplePrimalCycle M) : Equiv.Perm D :=
  SubmapPlanar.rawAlpha M C.dartSet (dartSet_alpha_closed C)

lemma cycleDualAlpha_eq_self_of_mem {d : D} (hd : d ∈ C.dartSet) :
    cycleDualAlpha C d = d :=
  SubmapPlanar.rawAlpha_eq_self_of_mem M C.dartSet _ hd

lemma cycleDualAlpha_eq_alpha_of_notMem {d : D} (hd : d ∉ C.dartSet) :
    cycleDualAlpha C d = M.α d :=
  SubmapPlanar.rawAlpha_eq_alpha_of_notMem M C.dartSet _ hd

lemma cycleDualAlpha_invol :
    cycleDualAlpha C * cycleDualAlpha C = 1 :=
  SubmapPlanar.rawAlpha_invol M C.dartSet _

/-- The forward and reverse darts are disjoint families, so `C.dartSet` has `2·C.len`
elements: `C.len` forward darts `C.dart i` and `C.len` reverse darts `M.α (C.dart i)`. -/
lemma dartSet_card : (C.dartSet).card = 2 * C.len := by
  classical
  -- `C.dartSet = image C.dart ∪ image (α ∘ C.dart)`; the two images are disjoint.
  have hset : C.dartSet
      = (Finset.univ.image C.dart) ∪ (Finset.univ.image (fun i => M.α (C.dart i))) := by
    ext d
    rw [C.mem_dartSet_iff]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi | hi⟩
      · exact Or.inl ⟨i, hi.symm⟩
      · exact Or.inr ⟨i, hi.symm⟩
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · exact ⟨i, Or.inl hi.symm⟩
      · exact ⟨i, Or.inr hi.symm⟩
  have hdisj : Disjoint (Finset.univ.image C.dart)
      (Finset.univ.image (fun i => M.α (C.dart i))) := by
    rw [Finset.disjoint_left]
    intro d hd himg
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hd himg
    obtain ⟨i, hi⟩ := hd
    obtain ⟨j, hj⟩ := himg
    exact C.dart_ne_alpha_dart i j (hi.trans hj.symm)
  have hcardF : (Finset.univ.image C.dart).card = C.len := by
    rw [Finset.card_image_of_injective _ C.dart_inj, Finset.card_univ, Fintype.card_fin]
  have hcardR : (Finset.univ.image (fun i => M.α (C.dart i))).card = C.len := by
    rw [Finset.card_image_of_injective _ C.alpha_dart_inj, Finset.card_univ, Fintype.card_fin]
  rw [hset, Finset.card_union_of_disjoint hdisj, hcardF, hcardR]; ring

/-! ## Genus slack of the cycle dual sub-involution is zero. -/

/-- `genusSlack (M.φ) (cycleDualAlpha C) = 0`: deleting the cycle edges from the genus-0 dual
map keeps the slack at zero.  Reuses the `dualMap` machinery from `ZinanCh35OuterSlack`. -/
lemma genusSlack_cycleDualAlpha_eq_zero (hsphere : M.IsSphereMap) :
    genusSlack M.φ (cycleDualAlpha C) = 0 := by
  have hclosedD : ∀ d : D, d ∈ C.dartSet → (dualMap M).α d ∈ C.dartSet := by
    simpa [dualMap_α] using (dartSet_alpha_closed C)
  have hraw : SubmapPlanar.rawAlpha (dualMap M) C.dartSet hclosedD = cycleDualAlpha C := by
    ext d
    by_cases hd : d ∈ C.dartSet
    · rw [SubmapPlanar.rawAlpha_eq_self_of_mem (dualMap M) C.dartSet hclosedD hd,
          cycleDualAlpha_eq_self_of_mem C hd]
    · rw [SubmapPlanar.rawAlpha_eq_alpha_of_notMem (dualMap M) C.dartSet hclosedD hd,
          cycleDualAlpha_eq_alpha_of_notMem C hd, dualMap_α]
  obtain ⟨d₀⟩ : Nonempty D := ⟨C.dart ⟨0, C.len_pos⟩⟩
  have hsphereD : (dualMap M).IsSphereMap := dualMap_isSphereMap M hsphere
  have h0 := SubmapPlanar.genusSlack_rawAlpha_eq_zero (dualMap M) C.dartSet hclosedD hsphereD d₀
  rw [hraw] at h0
  rwa [dualMap_σ] at h0

/-! ## `Ehalf (cycleDualAlpha C) = M.E − C.len`. -/

/-- The support of `cycleDualAlpha C` is exactly the non-deleted darts. -/
lemma support_cycleDualAlpha :
    (cycleDualAlpha C).support = Finset.univ \ C.dartSet := by
  classical
  ext d
  simp only [Equiv.Perm.mem_support, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro hd hmem
    exact hd (cycleDualAlpha_eq_self_of_mem C hmem)
  · intro hd
    rw [cycleDualAlpha_eq_alpha_of_notMem C hd]
    exact M.α_no_fixed d

/-- The cycle length is at most the number of edges. -/
lemma len_le_E : C.len ≤ M.E := by
  have h2 : (C.dartSet).card = 2 * C.len := dartSet_card C
  have hle : (C.dartSet).card ≤ Fintype.card D := Finset.card_le_univ _
  have hcard : 2 * M.E = Fintype.card D := two_mul_E_eq_card M
  omega

/-- The cycle length is at most the number of vertices (the tails are distinct). -/
lemma len_le_V : C.len ≤ M.V := by
  classical
  have hinj : Function.Injective (fun i => M.tail (C.dart i)) := C.tail_inj
  have hcard : (Finset.univ.image (fun i => M.tail (C.dart i))).card = C.len := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hle : (Finset.univ.image (fun i => M.tail (C.dart i))).card
      ≤ Fintype.card M.Vertex := Finset.card_le_univ _
  rw [hcard] at hle
  have : M.V = Fintype.card M.Vertex := rfl
  omega

/-- **`Ehalf (cycleDualAlpha C) = M.E − C.len`.** -/
lemma Ehalf_cycleDualAlpha : Ehalf (cycleDualAlpha C) = M.E - C.len := by
  classical
  have hsupp := support_cycleDualAlpha C
  have hsubset : C.dartSet ⊆ Finset.univ := Finset.subset_univ _
  have hcard : (cycleDualAlpha C).support.card = Fintype.card D - (C.dartSet).card := by
    rw [hsupp, Finset.card_univ_diff]
  have hEval : M.E = Fintype.card D / 2 := by
    have hα : M.α.support = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]; intro d
      rw [Equiv.Perm.mem_support]; exact M.α_no_fixed d
    have : Ehalf M.α = M.E := Ehalf_eq_E M
    rw [Ehalf, hα, Finset.card_univ] at this
    omega
  have hEhalf : Ehalf (cycleDualAlpha C) = (cycleDualAlpha C).support.card / 2 := rfl
  rw [hEhalf, hcard, dartSet_card C]
  omega

/-! ## The `cycleTau` reduction: `M.φ * cycleDualAlpha = M.σ * cycleTau`. -/

/-- The complementary restricted involution `cycleTau C := M.α * cycleDualAlpha C`:
identity off `C.dartSet`, `= M.α` on `C.dartSet`. -/
noncomputable def cycleTau (C : SimplePrimalCycle M) : Equiv.Perm D :=
  M.α * cycleDualAlpha C

lemma cycleTau_eq_alpha_of_mem {d : D} (hd : d ∈ C.dartSet) :
    cycleTau C d = M.α d := by
  show M.α (cycleDualAlpha C d) = M.α d
  rw [cycleDualAlpha_eq_self_of_mem C hd]

lemma cycleTau_eq_self_of_notMem {d : D} (hd : d ∉ C.dartSet) :
    cycleTau C d = d := by
  show M.α (cycleDualAlpha C d) = d
  rw [cycleDualAlpha_eq_alpha_of_notMem C hd, M.alpha_alpha]

/-- **The algebraic reduction.**  `M.φ * cycleDualAlpha = M.σ * cycleTau`. -/
lemma phi_cycleDualAlpha_eq_sigma_cycleTau :
    M.φ * cycleDualAlpha C = M.σ * cycleTau C := by
  show M.φ * cycleDualAlpha C = M.σ * (M.α * cycleDualAlpha C)
  rw [← mul_assoc]; rfl

/-! ## The bank count `numCycles (M.φ * cycleDualAlpha C) = M.V − C.len + 2`.

Swap-peeling (Route B): `cycleTau C` is the product of the `C.len` disjoint outer
transpositions `(C.dart i, M.α (C.dart i))`.  The dynamical fact driving the merge/split is
`M.σ.SameCycle (M.α (C.dart i)) (C.dart (nextIdx i))`: the reverse dart `M.α (C.dart i)` has
tail `head (C.dart i) = tail (C.dart (nextIdx i))`, so it lives in the same `σ`-orbit (=same
vertex) as `C.dart (nextIdx i)`.  Ordering the swaps `0, …, C.len−1`, the first `C.len−1`
each merge two distinct cycles (the growing chain of vertex-orbits `v_0, …, v_k`) and the
last one splits. -/

/-! ### Same-cycle facts (tail-vertex based). -/

/-- `M.σ.SameCycle a b ↔ M.tail a = M.tail b`. -/
lemma sigma_sameCycle_iff_tail (a b : D) :
    M.σ.SameCycle a b ↔ M.tail a = M.tail b := by
  show M.σ.SameCycle a b ↔
    (Quotient.mk (cycleSetoid M.σ) a : Quotient (cycleSetoid M.σ)) = Quotient.mk _ b
  rw [Quotient.eq]
  rfl

/-- Distinct forward cycle darts lie in distinct `σ`-cycles: their tails are distinct. -/
lemma sigma_sameCycle_dart_dart (i j : Fin C.len) :
    M.σ.SameCycle (C.dart i) (C.dart j) ↔ i = j := by
  rw [sigma_sameCycle_iff_tail]
  constructor
  · intro h; exact C.tail_inj h
  · intro h; rw [h]

/-- **The key dynamical fact:** `M.σ.SameCycle (M.α (C.dart i)) (C.dart (nextIdx i))`.
`tail (α (C.dart i)) = head (C.dart i) = tail (C.dart (nextIdx i))`. -/
lemma sigma_sameCycle_alphaDart_dart_next (i : Fin C.len) :
    M.σ.SameCycle (M.α (C.dart i)) (C.dart (C.nextIdx i)) := by
  rw [sigma_sameCycle_iff_tail, M.tail_alpha]
  exact (C.tail_dart_nextIdx i).symm

/-! ### Distinctness / injectivity (mirrors `qd_*`). -/

lemma dart_ne_alphaDart_self (i : Fin C.len) : C.dart i ≠ M.α (C.dart i) :=
  C.dart_ne_alpha_self i

lemma dart_ne_alphaDart (i j : Fin C.len) : C.dart i ≠ M.α (C.dart j) :=
  C.dart_ne_alpha_dart i j

lemma alphaDart_ne_dart (i j : Fin C.len) : M.α (C.dart i) ≠ C.dart j :=
  fun h => C.dart_ne_alpha_dart j i h.symm

/-! ### `nextIdx` arithmetic on `Fin C.len`. -/

/-- For a non-final index, `nextIdx` increments the value (no wraparound). -/
lemma nextIdx_val_of_lt {i : Fin C.len} (hi : i.1 < C.len - 1) :
    (C.nextIdx i).1 = i.1 + 1 := by
  rw [SimplePrimalCycle.nextIdx_val, Nat.mod_eq_of_lt (by omega)]

/-! ### The merge-pair list and the partial products. -/

/-- The embedding `Fin (C.len − 1) ↪ Fin C.len`. -/
noncomputable def emb (j : Fin (C.len - 1)) : Fin C.len :=
  ⟨j.1, by have := j.2; omega⟩

/-- The ordered list of the first `C.len − 1` transposition pairs `(C.dart j, α (C.dart j))`. -/
noncomputable def mergePairs (C : SimplePrimalCycle M) : List (D × D) :=
  (List.finRange (C.len - 1)).map (fun j => (C.dart (emb C j), M.α (C.dart (emb C j))))

/-- The partial product permutation after the first `k` merge swaps. -/
noncomputable def pPrefix (C : SimplePrimalCycle M) (k : ℕ) : Equiv.Perm D :=
  M.σ * (((mergePairs C).take k).map (fun w => Equiv.swap w.1 w.2)).prod

lemma pPrefix_zero : pPrefix C 0 = M.σ := by simp [pPrefix]

lemma mergePairs_get_fst (k : ℕ) (hk : k < C.len - 1) :
    (mergePairs C).get ⟨k, by simpa [mergePairs] using hk⟩
      = (C.dart ⟨k, by omega⟩, M.α (C.dart ⟨k, by omega⟩)) := by
  unfold mergePairs
  rw [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
  rfl

lemma mergePairs_length : (mergePairs C).length = C.len - 1 := by
  simp [mergePairs]

/-- One-step recurrence for the partial products. -/
lemma pPrefix_succ (k : ℕ) (hk : k < C.len - 1) :
    pPrefix C (k + 1)
      = pPrefix C k * Equiv.swap (C.dart ⟨k, by omega⟩) (M.α (C.dart ⟨k, by omega⟩)) := by
  unfold pPrefix
  have hlen : k < (mergePairs C).length := by rw [mergePairs_length]; exact hk
  have htake : (mergePairs C).take (k + 1)
      = (mergePairs C).take k ++ [(mergePairs C).get ⟨k, hlen⟩] := by
    rw [List.get_eq_getElem]
    exact List.take_succ_eq_append_getElem hlen
  rw [htake, List.map_append, List.prod_append, mergePairs_get_fst C k hk]
  simp [mul_assoc]

/-- `nextIdx` is injective (restated locally for convenience). -/
lemma nextIdx_inj {i j : Fin C.len} (h : C.nextIdx i = C.nextIdx j) : i = j :=
  C.nextIdx_inj h

/-! ### The running invariant (proved by simultaneous induction on `k`). -/

/-- The simultaneous invariant after `k` merges.  At each cycle vertex `v_m`, the partial
product groups the forward dart `C.dart m` with the reverse dart `M.α (C.dart (prevIdx m))`
(whose tail is also `v_m`); after `k` merges the chain `v_0, …, v_k` is one cycle.

We phrase everything via `nextIdx`: `M.α (C.dart i)` sits in the `σ`-orbit of vertex
`v_{nextIdx i}` (by `sigma_sameCycle_alphaDart_dart_next`).  So the index controlling whether
`M.α (C.dart j)` has joined the block is `(nextIdx j).1 ≤ k`, exactly as in the outer-cycle
proof. -/
lemma bankInvariant :
    ∀ k : ℕ, k + 1 ≤ C.len →
      (∀ i j : Fin C.len,
          (pPrefix C k).SameCycle (C.dart i) (C.dart j)
            ↔ i = j ∨ (i.1 ≤ k ∧ j.1 ≤ k)) ∧
      (∀ i j : Fin C.len,
          (pPrefix C k).SameCycle (C.dart i) (M.α (C.dart j))
            ↔ i = C.nextIdx j ∨ (i.1 ≤ k ∧ (C.nextIdx j).1 ≤ k)) ∧
      (∀ i j : Fin C.len,
          (pPrefix C k).SameCycle (M.α (C.dart i)) (M.α (C.dart j))
            ↔ i = j ∨ ((C.nextIdx i).1 ≤ k ∧ (C.nextIdx j).1 ≤ k)) := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [pPrefix_zero]
      refine ⟨?_, ?_, ?_⟩
      · -- dart-dart base
        intro i j
        rw [sigma_sameCycle_dart_dart]
        constructor
        · exact Or.inl
        · rintro (h | ⟨hi, hj⟩)
          · exact h
          · exact Fin.ext (by omega)
      · -- dart-α base
        intro i j
        have hr : M.σ.SameCycle (M.α (C.dart j)) (C.dart (C.nextIdx j)) :=
          sigma_sameCycle_alphaDart_dart_next C j
        constructor
        · intro h
          have : M.σ.SameCycle (C.dart i) (C.dart (C.nextIdx j)) := h.trans hr
          left; exact (sigma_sameCycle_dart_dart C i (C.nextIdx j)).mp this
        · rintro (h | ⟨hi, hcon⟩)
          · subst h; exact hr.symm
          · have : i = C.nextIdx j := Fin.ext (by omega)
            subst this; exact hr.symm
      · -- α-α base
        intro i j
        have hri : M.σ.SameCycle (M.α (C.dart i)) (C.dart (C.nextIdx i)) :=
          sigma_sameCycle_alphaDart_dart_next C i
        have hrj : M.σ.SameCycle (M.α (C.dart j)) (C.dart (C.nextIdx j)) :=
          sigma_sameCycle_alphaDart_dart_next C j
        constructor
        · intro h
          have : M.σ.SameCycle (C.dart (C.nextIdx i)) (C.dart (C.nextIdx j)) :=
            (hri.symm.trans h).trans hrj
          left; exact nextIdx_inj C ((sigma_sameCycle_dart_dart C _ _).mp this)
        · rintro (h | ⟨hci, hcj⟩)
          · subst h; exact SameCycle.rfl
          · have : C.nextIdx i = C.nextIdx j := Fin.ext (by omega)
            rw [nextIdx_inj C this]
  | succ k ih =>
      intro hk1
      have hkB1 : k < C.len - 1 := by omega
      have hkB : k < C.len := by omega
      obtain ⟨ihqq, ihqr, ihrr⟩ := ih (by omega)
      set a := C.dart ⟨k, hkB⟩ with ha
      set b := M.α (C.dart ⟨k, hkB⟩) with hb
      have hak : (⟨k, hkB⟩ : Fin C.len).1 = k := rfl
      have hnextk : (C.nextIdx ⟨k, hkB⟩).1 = k + 1 := nextIdx_val_of_lt C (by simpa using hkB1)
      have hnsc : ¬ (pPrefix C k).SameCycle a b := by
        rw [ha, hb, ihqr ⟨k, hkB⟩ ⟨k, hkB⟩]
        rintro (hcon | ⟨_, hcon⟩)
        · have := congrArg Fin.val hcon; rw [hnextk] at this; simp at this
        · rw [hnextk] at hcon; omega
      have hstep := pPrefix_succ C k hkB1
      have engine : ∀ x y : D,
          (pPrefix C (k + 1)).SameCycle x y ↔
            (pPrefix C k).SameCycle x y ∨
              ((pPrefix C k).SameCycle x a ∧ (pPrefix C k).SameCycle y b) ∨
              ((pPrefix C k).SameCycle x b ∧ (pPrefix C k).SameCycle y a) := by
        intro x y
        rw [hstep]
        exact PermTranspositionCycleCount.sameCycle_mul_swap_iff_mergeRel_of_not_sameCycle
          (pPrefix C k) hnsc (x := x) (y := y)
      have hqa : ∀ i : Fin C.len,
          (pPrefix C k).SameCycle (C.dart i) a ↔ i.1 ≤ k := by
        intro i; rw [ha, ihqq i ⟨k, hkB⟩]
        constructor
        · rintro (h | ⟨hi, _⟩)
          · exact le_of_eq (congrArg Fin.val h)
          · exact hi
        · intro hi
          rcases Nat.lt_or_ge i.1 k with h | h
          · exact Or.inr ⟨by omega, le_refl k⟩
          · exact Or.inl (Fin.ext (le_antisymm hi h))
      have hqb : ∀ i : Fin C.len,
          (pPrefix C k).SameCycle (C.dart i) b ↔ i.1 = k + 1 := by
        intro i; rw [hb, ihqr i ⟨k, hkB⟩, hnextk]
        constructor
        · rintro (h | ⟨_, hcon⟩)
          · have := congrArg Fin.val h; rw [hnextk] at this; exact this
          · omega
        · intro hi; left; exact Fin.ext (by rw [hnextk]; exact hi)
      have hrb : ∀ i : Fin C.len,
          (pPrefix C k).SameCycle (M.α (C.dart i)) b ↔ (C.nextIdx i).1 = k + 1 := by
        intro i; rw [hb, ihrr i ⟨k, hkB⟩, hnextk]
        constructor
        · rintro (h | ⟨hi, hcon⟩)
          · subst h; rw [hnextk]
          · omega
        · intro hi; left; exact nextIdx_inj C (Fin.ext (by rw [hnextk]; omega))
      refine ⟨?_, ?_, ?_⟩
      · -- dart-dart at k+1
        intro i j
        rw [engine (C.dart i) (C.dart j), ihqq i j, hqa i, hqb j, hqb i, hqa j]
        constructor
        · rintro (h | ⟨hi, hj⟩ | ⟨hi, hj⟩)
          · rcases h with h | ⟨hi, hj⟩
            · exact Or.inl h
            · exact Or.inr ⟨by omega, by omega⟩
          · right; refine ⟨by omega, by omega⟩
          · right; refine ⟨by omega, by omega⟩
        · rintro (h | ⟨hi, hj⟩)
          · exact Or.inl (Or.inl h)
          · rcases Nat.lt_or_ge i.1 (k+1) with hik | hik
            · rcases Nat.lt_or_ge j.1 (k+1) with hjk | hjk
              · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
              · right; left; exact ⟨by omega, by omega⟩
            · rcases Nat.lt_or_ge j.1 (k+1) with hjk | hjk
              · right; right; exact ⟨by omega, by omega⟩
              · exact Or.inl (Or.inl (Fin.ext (by omega)))
      · -- dart-α at k+1
        intro i j
        rw [engine (C.dart i) (M.α (C.dart j)), ihqr i j, hqa i, hrb j, hqb i]
        have hrja : (pPrefix C k).SameCycle (M.α (C.dart j)) a ↔ (C.nextIdx j).1 ≤ k := by
          rw [ha, Equiv.Perm.sameCycle_comm, ihqr ⟨k, hkB⟩ j]
          constructor
          · rintro (h | ⟨_, hj⟩)
            · have : (C.nextIdx j).1 = k := (congrArg Fin.val h).symm
              omega
            · exact hj
          · intro hj
            rcases Nat.lt_or_ge (C.nextIdx j).1 k with h | h
            · exact Or.inr ⟨by omega, by omega⟩
            · left; exact Fin.ext (by omega)
        rw [hrja]
        constructor
        · rintro (h | ⟨hi, hj⟩ | ⟨hi, hj⟩)
          · rcases h with h | ⟨hi, hj⟩
            · exact Or.inl h
            · exact Or.inr ⟨by omega, by omega⟩
          · right; exact ⟨by omega, by omega⟩
          · right; exact ⟨by omega, by omega⟩
        · rintro (h | ⟨hi, hnj⟩)
          · exact Or.inl (Or.inl h)
          · rcases Nat.lt_or_ge i.1 (k+1) with hik | hik
            · rcases Nat.lt_or_ge (C.nextIdx j).1 (k+1) with hnjk | hnjk
              · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
              · right; left; exact ⟨by omega, by omega⟩
            · rcases Nat.lt_or_ge (C.nextIdx j).1 (k+1) with hnjk | hnjk
              · right; right; exact ⟨by omega, by omega⟩
              · exact Or.inl (Or.inl (Fin.ext (by omega)))
      · -- α-α at k+1
        intro i j
        rw [engine (M.α (C.dart i)) (M.α (C.dart j)), ihrr i j, hrb j, hrb i]
        have hria : (pPrefix C k).SameCycle (M.α (C.dart i)) a ↔ (C.nextIdx i).1 ≤ k := by
          rw [ha, Equiv.Perm.sameCycle_comm, ihqr ⟨k, hkB⟩ i]
          constructor
          · rintro (h | ⟨_, hi⟩)
            · have := congrArg Fin.val h; omega
            · exact hi
          · intro hi
            rcases Nat.lt_or_ge (C.nextIdx i).1 k with h | h
            · exact Or.inr ⟨by omega, by omega⟩
            · left; exact Fin.ext (by omega)
        have hrja : (pPrefix C k).SameCycle (M.α (C.dart j)) a ↔ (C.nextIdx j).1 ≤ k := by
          rw [ha, Equiv.Perm.sameCycle_comm, ihqr ⟨k, hkB⟩ j]
          constructor
          · rintro (h | ⟨_, hj⟩)
            · have := congrArg Fin.val h; omega
            · exact hj
          · intro hj
            rcases Nat.lt_or_ge (C.nextIdx j).1 k with h | h
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
          · rcases Nat.lt_or_ge (C.nextIdx i).1 (k+1) with hnik | hnik
            · rcases Nat.lt_or_ge (C.nextIdx j).1 (k+1) with hnjk | hnjk
              · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
              · right; left; exact ⟨by omega, by omega⟩
            · rcases Nat.lt_or_ge (C.nextIdx j).1 (k+1) with hnjk | hnjk
              · right; right; exact ⟨by omega, by omega⟩
              · have : C.nextIdx i = C.nextIdx j := Fin.ext (by omega)
                exact Or.inl (Or.inl (nextIdx_inj C this))

/-! ### Counts: the merges, the final split, and assembly. -/

lemma len_pos' : 0 < C.len := C.len_pos

/-- The fully-merged permutation after all `C.len − 1` merges. -/
noncomputable def pMerge (C : SimplePrimalCycle M) : Equiv.Perm D :=
  pPrefix C (C.len - 1)

/-- The `C.len − 1` merge swaps each merge two distinct cycles of the running product. -/
lemma mergePairs_merge_condition :
    ∀ j : Fin (mergePairs C).length,
      ((mergePairs C).get j).1 ≠ ((mergePairs C).get j).2 ∧
        ¬ (M.σ * (((mergePairs C).take j).map (fun w => Equiv.swap w.1 w.2)).prod).SameCycle
            ((mergePairs C).get j).1 ((mergePairs C).get j).2 := by
  intro j
  have he : (mergePairs C).length = C.len - 1 := mergePairs_length C
  have hjlen : (j : ℕ) < C.len - 1 := by have := j.2; omega
  have hjB : (j : ℕ) < C.len := by omega
  rw [mergePairs_get_fst C (j : ℕ) hjlen]
  have hpp : M.σ * (((mergePairs C).take (j : ℕ)).map (fun w => Equiv.swap w.1 w.2)).prod
      = pPrefix C (j : ℕ) := rfl
  refine ⟨?_, ?_⟩
  · exact dart_ne_alphaDart_self C ⟨(j : ℕ), hjB⟩
  · rw [hpp]
    obtain ⟨_, ihqr, _⟩ := bankInvariant C (j : ℕ) (by omega)
    rw [ihqr ⟨(j : ℕ), hjB⟩ ⟨(j : ℕ), hjB⟩]
    have hnext : (C.nextIdx ⟨(j : ℕ), hjB⟩).1 = (j : ℕ) + 1 :=
      nextIdx_val_of_lt C (by simpa using hjlen)
    rintro (hcon | ⟨_, hcon⟩)
    · have := congrArg Fin.val hcon; rw [hnext] at this; simp at this
    · rw [hnext] at hcon; omega

/-- After all `C.len − 1` merges, the cycle count is `V − (C.len − 1)`. -/
lemma numCycles_pMerge_add :
    _root_.numCycles (pMerge C) + (C.len - 1) = M.V := by
  have hmerge := CombMap.CutCapCount.numCycles_mul_listSwap_merges M.σ (mergePairs C)
    (mergePairs_merge_condition C)
  rw [mergePairs_length] at hmerge
  have hpm : pMerge C = M.σ * ((mergePairs C).map (fun w => Equiv.swap w.1 w.2)).prod := by
    unfold pMerge pPrefix
    rw [List.take_of_length_le (by rw [mergePairs_length])]
  rw [hpm, hmerge, M.V_eq_numCycles]

/-- The last cycle pair `(C.dart last, α (C.dart last))`, `last = ⟨C.len−1⟩`. -/
noncomputable def lastIdx (C : SimplePrimalCycle M) : Fin C.len :=
  ⟨C.len - 1, by have := len_pos' C; omega⟩

/-- In `pMerge`, the last pair lies in the same cycle (so the closing swap splits). -/
lemma pMerge_lastPair_sameCycle :
    (pMerge C).SameCycle (C.dart (lastIdx C)) (M.α (C.dart (lastIdx C))) := by
  unfold pMerge
  have hBpos : 0 < C.len := len_pos' C
  obtain ⟨_, ihqr, _⟩ := bankInvariant C (C.len - 1) (by omega)
  rw [ihqr (lastIdx C) (lastIdx C)]
  right
  have hnl : (C.nextIdx (lastIdx C)).1 = 0 := by
    rw [SimplePrimalCycle.nextIdx_val]
    show ((C.len - 1) + 1) % C.len = 0
    rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
  refine ⟨?_, ?_⟩
  · show (C.len - 1) ≤ C.len - 1; exact le_refl _
  · rw [hnl]; exact Nat.zero_le _

/-! ### The outer transposition product equals `cycleTau`. -/

/-- A cycle dart is some `C.dart m` or `M.α (C.dart m)`; the forward case here. -/
lemma listSwapQR_apply_dart (m : Fin C.len) :
    ∀ L : List (Fin C.len), L.Nodup → m ∈ L →
      ((L.map (fun i => (C.dart i, M.α (C.dart i)))).map (fun w => Equiv.swap w.1 w.2)).prod
          (C.dart m) = M.α (C.dart m) := by
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
        show Equiv.swap (C.dart c) (M.α (C.dart c)) (M.α (C.dart m)) = M.α (C.dart m)
        rw [Equiv.swap_apply_of_ne_of_ne (alphaDart_ne_dart C m c)
          (fun h => hcm (C.alpha_dart_inj h).symm)]
      · have hmc : m = c := by
          rcases List.mem_cons.mp hm with h | h
          · exact h
          · exact absurd h hmt
        subst hmc
        have htail : ((t.map (fun i => (C.dart i, M.α (C.dart i)))).map
            (fun w => Equiv.swap w.1 w.2)).prod (C.dart m) = C.dart m := by
          apply CombMap.CutCapCount.listSwap_prod_apply_of_notMem
          intro w hw
          rw [List.mem_map] at hw
          obtain ⟨i, hi, hwi⟩ := hw
          have hineq : i ≠ m := fun h => hmt (h ▸ hi)
          subst hwi
          exact ⟨fun h => hineq (C.dart_inj h).symm, dart_ne_alphaDart C m i⟩
        rw [htail]
        show Equiv.swap (C.dart m) (M.α (C.dart m)) (C.dart m) = M.α (C.dart m)
        rw [Equiv.swap_apply_left]

/-- The reverse case: at an `α`-dart whose index is in the (nodup) list. -/
lemma listSwapQR_apply_alphaDart (m : Fin C.len) :
    ∀ L : List (Fin C.len), L.Nodup → m ∈ L →
      ((L.map (fun i => (C.dart i, M.α (C.dart i)))).map (fun w => Equiv.swap w.1 w.2)).prod
          (M.α (C.dart m)) = C.dart m := by
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
        show Equiv.swap (C.dart c) (M.α (C.dart c)) (C.dart m) = C.dart m
        rw [Equiv.swap_apply_of_ne_of_ne (fun h => hcm (C.dart_inj h).symm) (dart_ne_alphaDart C m c)]
      · have hmc : m = c := by
          rcases List.mem_cons.mp hm with h | h
          · exact h
          · exact absurd h hmt
        subst hmc
        have htail : ((t.map (fun i => (C.dart i, M.α (C.dart i)))).map
            (fun w => Equiv.swap w.1 w.2)).prod (M.α (C.dart m)) = M.α (C.dart m) := by
          apply CombMap.CutCapCount.listSwap_prod_apply_of_notMem
          intro w hw
          rw [List.mem_map] at hw
          obtain ⟨i, hi, hwi⟩ := hw
          have hineq : i ≠ m := fun h => hmt (h ▸ hi)
          subst hwi
          exact ⟨alphaDart_ne_dart C m i, fun h => hineq (C.alpha_dart_inj h).symm⟩
        rw [htail]
        show Equiv.swap (C.dart m) (M.α (C.dart m)) (M.α (C.dart m)) = C.dart m
        rw [Equiv.swap_apply_right]

/-- Evaluation at a dart that is neither a forward nor reverse cycle dart: it is fixed. -/
lemma listSwapQR_apply_other (d : D)
    (L : List (Fin C.len))
    (hd : ∀ i ∈ L, d ≠ C.dart i ∧ d ≠ M.α (C.dart i)) :
    ((L.map (fun i => (C.dart i, M.α (C.dart i)))).map (fun w => Equiv.swap w.1 w.2)).prod d = d := by
  apply CombMap.CutCapCount.listSwap_prod_apply_of_notMem
  intro w hw
  rw [List.mem_map] at hw
  obtain ⟨i, hi, hwi⟩ := hw
  subst hwi
  exact hd i hi

/-- The full pair list over all `C.len` indices. -/
noncomputable def allPairs (C : SimplePrimalCycle M) : List (D × D) :=
  (List.finRange C.len).map (fun i => (C.dart i, M.α (C.dart i)))

/-- `cycleTau` is the product of the `C.len` disjoint cycle transpositions. -/
lemma cycleTau_eq_swapProd :
    cycleTau C = ((allPairs C).map (fun w => Equiv.swap w.1 w.2)).prod := by
  have hnd : (List.finRange C.len).Nodup := List.nodup_finRange _
  ext d
  unfold allPairs
  by_cases hd : d ∈ C.dartSet
  · rw [cycleTau_eq_alpha_of_mem C hd]
    rw [C.mem_dartSet_iff] at hd
    obtain ⟨m, hm | hm⟩ := hd
    · -- d = C.dart m
      subst hm
      rw [listSwapQR_apply_dart C m _ hnd (List.mem_finRange m)]
    · -- d = α (C.dart m)
      subst hm
      rw [listSwapQR_apply_alphaDart C m _ hnd (List.mem_finRange m), M.alpha_alpha]
  · rw [cycleTau_eq_self_of_notMem C hd]
    refine (listSwapQR_apply_other C d _ ?_).symm
    intro i _
    refine ⟨?_, ?_⟩
    · intro h; exact hd (h ▸ C.dart_mem_dartSet i)
    · intro h; exact hd (h ▸ C.alpha_dart_mem_dartSet i)

/-- `allPairs = mergePairs ++ [last pair]`. -/
lemma allPairs_eq_append :
    allPairs C = mergePairs C ++ [(C.dart (lastIdx C), M.α (C.dart (lastIdx C)))] := by
  have hBpos : 0 < C.len := len_pos' C
  have hlenA : (allPairs C).length = C.len := by
    simp [allPairs, List.length_map, List.length_finRange]
  have hmlen : (mergePairs C).length = C.len - 1 := mergePairs_length C
  have hlenR : (mergePairs C ++ [(C.dart (lastIdx C), M.α (C.dart (lastIdx C)))]).length
      = C.len := by
    rw [List.length_append, hmlen, List.length_singleton]; omega
  apply List.ext_getElem (by rw [hlenA, hlenR])
  intro n hn1 hn2
  rw [hlenA] at hn1
  have hLHS : (allPairs C)[n] = (C.dart ⟨n, hn1⟩, M.α (C.dart ⟨n, hn1⟩)) := by
    simp only [allPairs]
    rw [List.getElem_map, List.getElem_finRange]
    congr 1
  rw [hLHS]
  by_cases hnlast : n < C.len - 1
  · rw [List.getElem_append_left (by rw [hmlen]; exact hnlast)]
    simp only [mergePairs]
    rw [List.getElem_map, List.getElem_finRange]
    show (C.dart ⟨n, hn1⟩, M.α (C.dart ⟨n, hn1⟩))
      = (C.dart (emb C _), M.α (C.dart (emb C _)))
    congr 1
  · rw [List.getElem_append_right (by rw [hmlen]; omega)]
    have hidx : (⟨n, hn1⟩ : Fin C.len) = lastIdx C :=
      Fin.ext (by simp only [lastIdx]; omega)
    rw [hidx, List.getElem_singleton]

/-- `M.σ * cycleTau = pMerge * swap (C.dart last) (α (C.dart last))`. -/
lemma sigma_cycleTau_eq :
    M.σ * cycleTau C
      = pMerge C * Equiv.swap (C.dart (lastIdx C)) (M.α (C.dart (lastIdx C))) := by
  rw [cycleTau_eq_swapProd, allPairs_eq_append, List.map_append, List.prod_append]
  unfold pMerge pPrefix
  rw [List.take_of_length_le (by rw [mergePairs_length]), List.map_singleton, List.prod_cons,
      List.prod_nil, mul_one, ← mul_assoc]

/-- **The bank count — UNCONDITIONAL.**
`numCycles (M.φ * cycleDualAlpha C) = M.V − C.len + 2`. -/
theorem bankCount_holds :
    _root_.numCycles (M.φ * cycleDualAlpha C) = M.V - C.len + 2 := by
  rw [phi_cycleDualAlpha_eq_sigma_cycleTau, sigma_cycleTau_eq]
  have hsplit : _root_.numCycles
      (pMerge C * Equiv.swap (C.dart (lastIdx C)) (M.α (C.dart (lastIdx C))))
      = _root_.numCycles (pMerge C) + 1 :=
    CombMap.CutCapCount.numCycles_mul_swap_of_sameCycle (pMerge C)
      (dart_ne_alphaDart_self C (lastIdx C)) (pMerge_lastPair_sameCycle C)
  rw [hsplit]
  have hmerge := numCycles_pMerge_add C
  have hBpos : 0 < C.len := len_pos' C
  have hBV : C.len ≤ M.V := len_le_V C
  omega

/-! ## The dart-face bridge `numComponents M.φ cycleDualAlpha = numComp (DualAvoidsCycleStep M C)`.

Mirrors `ZinanCh35OuterSlack.numComponents_eq_numComp_outerDualStep`.  A dart lies in
`C.dartSet` iff its edge lies in `C.edgeSet`; this is the analogue of the
boundary-edge/boundary-dart equivalence.  The forward direction is immediate; the reverse
direction needs `no_parallel` (an `IsSimpleGraph` fact). -/

/-- A dart lies in `C.dartSet` iff its edge lies in `C.edgeSet`. -/
lemma mem_dartSet_iff_edgeSet (hsimple : M.IsSimpleGraph) {d : D} :
    d ∈ C.dartSet ↔ M.dartEdge d ∈ C.edgeSet := by
  constructor
  · intro hd
    rw [C.mem_dartSet_iff] at hd
    obtain ⟨i, hi | hi⟩ := hd
    · exact (C.mem_edgeSet_iff _).2 ⟨i, by rw [hi, SimplePrimalCycle.edge]⟩
    · exact (C.mem_edgeSet_iff _).2 ⟨i, by rw [hi, SimplePrimalCycle.edge, M.dartEdge_alpha]⟩
  · intro he
    rw [C.mem_edgeSet_iff] at he
    obtain ⟨i, hi⟩ := he
    -- `dartEdge d = C.edge i = dartEdge (C.dart i)` ⟹ `α.SameCycle d (C.dart i)`
    have hsc : M.α.SameCycle d (C.dart i) :=
      hsimple.no_parallel (by rw [hi, SimplePrimalCycle.edge])
    rcases (M.alpha_sameCycle_iff d (C.dart i)).mp hsc with hde | hde
    · exact (C.mem_dartSet_iff d).2 ⟨i, Or.inl (by rw [hde])⟩
    · exact (C.mem_dartSet_iff d).2 ⟨i, Or.inr (by rw [hde, M.alpha_alpha])⟩

lemma notMem_dartSet_iff_not_edgeSet (hsimple : M.IsSimpleGraph) {d : D} :
    d ∉ C.dartSet ↔ M.dartEdge d ∉ C.edgeSet :=
  not_congr (mem_dartSet_iff_edgeSet C hsimple)

/-- Same face ⟺ `M.φ.SameCycle`. -/
lemma sameFace_iff_phi_sameCycle {a b : D} :
    M.dartFace a = M.dartFace b ↔ M.φ.SameCycle a b := by
  constructor
  · intro h; exact Quotient.exact h
  · intro h; exact Quotient.sound h

/-- The relation `dartStepRel M.φ (cycleDualAlpha C)`. -/
abbrev RDart (C : SimplePrimalCycle M) : D → D → Prop :=
  dartStepRel M.φ (cycleDualAlpha C)

/-- A single `RDart`-step descends to `EqvGen (DualAvoidsCycleStep)` on faces. -/
lemma eqvGen_dualStep_of_RDart_step (hsimple : M.IsSimpleGraph) {a b : D}
    (h : RDart C a b) :
    Relation.EqvGen (DualAvoidsCycleStep M C) (M.dartFace a) (M.dartFace b) := by
  rcases h with hsc | hαe
  · have : M.dartFace a = M.dartFace b := sameFace_iff_phi_sameCycle.mpr hsc
    rw [this]; exact Relation.EqvGen.refl _
  · by_cases hd : a ∈ C.dartSet
    · rw [hαe, cycleDualAlpha_eq_self_of_mem C hd]
      exact Relation.EqvGen.refl _
    · have hba : b = M.α a := by
        rw [hαe, cycleDualAlpha_eq_alpha_of_notMem C hd]
      have hnb : M.dartEdge a ∉ C.edgeSet :=
        (notMem_dartSet_iff_not_edgeSet C hsimple).mp hd
      have hstep : DualAvoidsCycleStep M C (M.dartFace a) (M.dartFace b) :=
        ⟨a, hnb, rfl, by rw [hba]⟩
      exact Relation.EqvGen.rel _ _ hstep

/-- A single `DualAvoidsCycleStep` lifts to `EqvGen RDart` on any dart reps. -/
lemma eqvGen_RDart_of_dualStep {f g : M.Face} {a b : D}
    (hstep : DualAvoidsCycleStep M C f g) (ha : M.dartFace a = f) (hb : M.dartFace b = g) :
    Relation.EqvGen (RDart C) a b := by
  obtain ⟨d, hbe, hdf, hdg⟩ := hstep
  have hdDel : d ∉ C.dartSet := C.notMem_dartSet_of_dartEdge_notMem hbe
  have h1 : Relation.EqvGen (RDart C) a d :=
    Relation.EqvGen.rel _ _ (Or.inl (sameFace_iff_phi_sameCycle.mp (by rw [ha, hdf])))
  have h2 : Relation.EqvGen (RDart C) d (M.α d) :=
    Relation.EqvGen.rel _ _ (Or.inr (by
      rw [cycleDualAlpha_eq_alpha_of_notMem C hdDel]))
  have h3 : Relation.EqvGen (RDart C) (M.α d) b :=
    Relation.EqvGen.rel _ _ (Or.inl (sameFace_iff_phi_sameCycle.mp (by rw [hdg, hb])))
  exact (h1.trans _ _ _ h2).trans _ _ _ h3

/-- A `DualAvoidsCycleStep`-walk lifts to `EqvGen RDart`. -/
lemma eqvGen_RDart_of_dualStep_walk {f g : M.Face} {a b : D}
    (hwalk : Relation.ReflTransGen (DualAvoidsCycleStep M C) f g)
    (ha : M.dartFace a = f) (hb : M.dartFace b = g) :
    Relation.EqvGen (RDart C) a b := by
  induction hwalk generalizing b with
  | refl =>
    exact Relation.EqvGen.rel _ _ (Or.inl (sameFace_iff_phi_sameCycle.mp (by rw [ha, hb])))
  | @tail x y hwxy hstep ih =>
    obtain ⟨c, hc⟩ : ∃ c : D, M.dartFace c = x := ⟨Quotient.out x, Quotient.out_eq x⟩
    have hac : Relation.EqvGen (RDart C) a c := ih hc
    have hcb : Relation.EqvGen (RDart C) c b :=
      eqvGen_RDart_of_dualStep C hstep hc hb
    exact hac.trans _ _ _ hcb

/-- The full `EqvGen RDart`-walk descends to `EqvGen DualAvoidsCycleStep` on faces. -/
lemma eqvGen_dualStep_of_RDart_eqv (hsimple : M.IsSimpleGraph) {a b : D}
    (hab : Relation.EqvGen (RDart C) a b) :
    Relation.EqvGen (DualAvoidsCycleStep M C) (M.dartFace a) (M.dartFace b) := by
  induction hab with
  | rel x y h => exact eqvGen_dualStep_of_RDart_step C hsimple h
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact ih.symm _ _
  | trans x y z _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2

/-- `DualAvoidsCycleStep` is symmetric (the reverse dart witnesses the reverse step). -/
lemma dualAvoidsCycleStep_symm {f g : M.Face} (h : DualAvoidsCycleStep M C f g) :
    DualAvoidsCycleStep M C g f := by
  obtain ⟨d, hbe, hdf, hdg⟩ := h
  refine ⟨M.α d, ?_, hdg, ?_⟩
  · rw [M.dartEdge_alpha]; exact hbe
  · rw [M.alpha_alpha]; exact hdf

/-- `EqvGen (DualAvoidsCycleStep)` coincides with `ReflTransGen` (symmetric relation). -/
lemma eqvGen_dualStep_iff {f g : M.Face} :
    Relation.EqvGen (DualAvoidsCycleStep M C) f g ↔
      Relation.ReflTransGen (DualAvoidsCycleStep M C) f g :=
  eqvGen_iff_reflTransGen (fun _ _ => dualAvoidsCycleStep_symm C) f g

/-- The face quotient map descends from the dart component quotient. -/
noncomputable def faceQuotMap (hsimple : M.IsSimpleGraph) :
    Quotient (compSetoid (RDart C)) → Quotient (compSetoid (DualAvoidsCycleStep M C)) :=
  Quotient.lift (fun d => Quotient.mk (compSetoid (DualAvoidsCycleStep M C)) (M.dartFace d))
    (by
      intro a b hab
      apply Quotient.sound
      exact eqvGen_dualStep_of_RDart_eqv C hsimple hab)

/-- **The dart-face quotient bridge.**  The component count of the dual sub-involution pair
equals the dual-face component count `numComp (DualAvoidsCycleStep M C)`. -/
lemma numComponents_eq_numComp_dualStep (hsimple : M.IsSimpleGraph) :
    numComponents M.φ (cycleDualAlpha C) = numComp (DualAvoidsCycleStep M C) := by
  classical
  rw [numComponents_def]
  show numComp (RDart C) = numComp (DualAvoidsCycleStep M C)
  unfold numComp
  apply Nat.card_congr
  refine Equiv.ofBijective (faceQuotMap C hsimple) ⟨?_, ?_⟩
  · intro x y hxy
    refine Quotient.inductionOn₂ x y (fun a b hab => ?_) hxy
    apply Quotient.sound
    have heqf : Relation.EqvGen (DualAvoidsCycleStep M C) (M.dartFace a) (M.dartFace b) :=
      Quotient.exact hab
    have hwalk : Relation.ReflTransGen (DualAvoidsCycleStep M C) (M.dartFace a) (M.dartFace b) :=
      (eqvGen_dualStep_iff C).1 heqf
    exact eqvGen_RDart_of_dualStep_walk C hwalk rfl rfl
  · intro q
    refine Quotient.inductionOn q (fun f => ?_)
    obtain ⟨d, hd⟩ : ∃ d : D, M.dartFace d = f := ⟨Quotient.out f, Quotient.out_eq f⟩
    exact ⟨Quotient.mk (compSetoid (RDart C)) d, by
      show Quotient.mk _ (M.dartFace d) = Quotient.mk _ f
      rw [hd]⟩

/-! ## Assembly: `numComp (DualAvoidsCycleStep M C) = 2`. -/

/-- **The two-component count for an arbitrary simple primal cycle — UNCONDITIONAL** (given
sphere + simple-graph).  Expanding `genusSlack M.φ (cycleDualAlpha C) = 0` with the bank
count, the `Ehalf`, the dart-face bridge, and Euler `V − E + F = 2`. -/
theorem dualAvoidsCycle_numComp_two (hsphere : M.IsSphereMap) (hsimple : M.IsSimpleGraph) :
    numComp (DualAvoidsCycleStep M C) = 2 := by
  have h0 : genusSlack M.φ (cycleDualAlpha C) = 0 :=
    genusSlack_cycleDualAlpha_eq_zero C hsphere
  have hE5 : Ehalf (cycleDualAlpha C) = M.E - C.len := Ehalf_cycleDualAlpha C
  have h6 : _root_.numCycles (M.φ * cycleDualAlpha C) = M.V - C.len + 2 := bankCount_holds C
  have hbridge : numComponents M.φ (cycleDualAlpha C) = numComp (DualAvoidsCycleStep M C) :=
    numComponents_eq_numComp_dualStep C hsimple
  have hF : _root_.numCycles M.φ = M.F := (M.F_eq_numCycles).symm
  have hEuler : (M.V : ℤ) - (M.E : ℤ) + (M.F : ℤ) = 2 := hsphere.2
  set B := C.len with hB
  have hBE : B ≤ M.E := len_le_E C
  unfold genusSlack at h0
  rw [hbridge, hF, hE5, h6] at h0
  have hcast5 : ((M.E - B : ℕ) : ℤ) = (M.E : ℤ) - (B : ℤ) := by
    rw [Nat.cast_sub hBE]
  have hcast6 : ((M.V - B + 2 : ℕ) : ℤ) = (M.V : ℤ) - (B : ℤ) + 2 := by
    have hBV : B ≤ M.V := len_le_V C
    push_cast [Nat.cast_sub hBV]; ring
  rw [hcast5, hcast6] at h0
  have hc : (numComp (DualAvoidsCycleStep M C) : ℤ) = 2 := by linarith
  exact_mod_cast hc

/-! ## Bank labels via σ-star segment connectivity.

`numComp = 2` says the dual face graph (with the cycle edges deleted) has exactly two
components — the two banks.  To *label* them we connect each bank internally through the
σ-stars at the cycle vertices.

The local classifier is the engine: at the cycle vertex `v_{nextIdx i} =
head (C.dart i) = tail (C.dart (nextIdx i))`, the σ-orbit's cycle darts are exactly the two
darts `M.α (C.dart i)` (reverse, tail `v_{nextIdx i}`) and `C.dart (nextIdx i)` (forward,
tail `v_{nextIdx i}`). -/

/-- A `FaceAdjAvoiding`-step for the cycle's forbidden set IS a `DualAvoidsCycleStep`. -/
lemma dualAvoidsCycleStep_of_faceAdj {f g : M.Face}
    (h : ZinanCh35StarConn.FaceAdjAvoiding M (· ∈ C.edgeSet) f g) :
    DualAvoidsCycleStep M C f g := by
  obtain ⟨d, hdf, hdg, hF⟩ := h
  exact ⟨d, hF, hdf, hdg⟩

/-- Transport `FaceAdjAvoiding`-reachability into `DualAvoidsCycleStep`-reachability. -/
lemma reflTransGen_dualStep_of_faceAdj {f g : M.Face}
    (h : Relation.ReflTransGen (ZinanCh35StarConn.FaceAdjAvoiding M (· ∈ C.edgeSet)) f g) :
    Relation.ReflTransGen (DualAvoidsCycleStep M C) f g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (dualAvoidsCycleStep_of_faceAdj C hstep)

/-- **The local σ-star classifier at a cycle vertex.**  A dart `z` in the σ-orbit of
`M.α (C.dart i)` (i.e. `tail z = v_{nextIdx i}`) has its edge in `C.edgeSet` iff `z` is one
of the two cycle darts `M.α (C.dart i)` or `C.dart (nextIdx i)`.

We package the "iff" as the contrapositive we actually use: if `z` shares the σ-orbit and is
neither of the two cycle darts, then `dartEdge z ∉ C.edgeSet`. -/
lemma not_mem_edgeSet_of_star_not_cycleDart (hsimple : M.IsSimpleGraph) {i : Fin C.len} {z : D}
    (hσ : M.σ.SameCycle (M.α (C.dart i)) z)
    (hz1 : z ≠ M.α (C.dart i)) (hz2 : z ≠ C.dart (C.nextIdx i)) :
    M.dartEdge z ∉ C.edgeSet := by
  rw [← notMem_dartSet_iff_not_edgeSet C hsimple]
  intro hmem
  rw [C.mem_dartSet_iff] at hmem
  -- `tail z = tail (α (C.dart i)) = head (C.dart i) = v_{nextIdx i}`.
  have htail : M.tail z = M.tail (C.dart (C.nextIdx i)) := by
    rw [(sigma_sameCycle_iff_tail (M.α (C.dart i)) z).mp hσ |>.symm, M.tail_alpha,
        C.tail_dart_nextIdx i]
  obtain ⟨j, hj | hj⟩ := hmem
  · -- z = C.dart j, tail = tail (C.dart j) = v_{nextIdx i} ⟹ j = nextIdx i.
    apply hz2
    rw [hj]; congr 1
    apply C.tail_inj
    show M.tail (C.dart j) = M.tail (C.dart (C.nextIdx i))
    rw [← hj]; exact htail
  · -- z = α (C.dart j), tail = head (C.dart j) = v_{nextIdx i} = head (C.dart i) ⟹ j = i.
    apply hz1
    -- `tail (α (C.dart j)) = tail (α (C.dart i))` ⟹ `j = i` ⟹ `z = α (C.dart j) = α (C.dart i)`.
    have hheadj : M.tail (M.α (C.dart j)) = M.tail (C.dart (C.nextIdx i)) := by
      rw [← hj]; exact htail
    have hi : M.head (C.dart i) = M.tail (C.dart (C.nextIdx i)) := C.consecutive' i
    -- head (C.dart j) = head (C.dart i): chase through nextIdx tails.
    have hheadeq : M.head (C.dart j) = M.head (C.dart i) := hheadj.trans hi.symm
    have hnext : M.tail (C.dart (C.nextIdx j)) = M.tail (C.dart (C.nextIdx i)) := by
      rw [C.tail_dart_nextIdx j, C.tail_dart_nextIdx i, hheadeq]
    have hnij : C.nextIdx j = C.nextIdx i := C.tail_inj hnext
    have hji : j = i := nextIdx_inj C hnij
    rw [hj, hji]

/-! The bank-label connectivity and separation are carried as the residual fields of
`SimpleCycleBankTheorem` below.  The σ-star classifier above is the engine for the
connectivity half (each bank closes through the non-cycle darts of the cycle-vertex stars);
the separation half is the genuine Jordan content already supplied, for the chord cycle, by
the cut-cap surgery layer (`PlanarMapBridgeWitness`, `jordan_simple_cycle2_*`). -/

/-- **The general simple-cycle bank theorem (R6 §4).**  Packages the two-bank structure of an
arbitrary simple primal cycle: the unconditional two-component count, plus the bank labels
(left/right connectivity and separation).  The `dual_numComp_two`, `bankOrbitCount`,
`slack_zero` fields are filled **unconditionally** by `cycleBankTheorem_core`; the bank-label
fields are carried as the residual. -/
structure SimpleCycleBankTheorem (M : CombMap D) (C : SimplePrimalCycle M) where
  dual_numComp_two : numComp (DualAvoidsCycleStep M C) = 2
  bankOrbitCount : _root_.numCycles (M.φ * cycleDualAlpha C) = M.V - C.len + 2
  slack_zero : genusSlack M.φ (cycleDualAlpha C) = 0
  left_bank : ∀ i j : Fin C.len,
    Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceLeft i) (C.faceLeft j)
  right_bank : ∀ i j : Fin C.len,
    Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceRight i) (C.faceRight j)
  left_right_sep : ∀ i j : Fin C.len,
    ¬ Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceLeft i) (C.faceRight j)

/-- **The unconditional core of the bank theorem.**  For an arbitrary `SimplePrimalCycle` on a
sphere simple-graph map, the genus-slack count fields are all proved clean-3:
`numComp (DualAvoidsCycleStep M C) = 2`, the bank orbit count `M.V − C.len + 2`, and
`genusSlack = 0`.  This is the generalization of the LANDED outer-cycle two-component result
(`ZinanCh35BankCount.outerDualNumCompTwo_holds`) to an arbitrary simple primal cycle. -/
theorem cycleBankTheorem_core (hsphere : M.IsSphereMap) (hsimple : M.IsSimpleGraph) :
    numComp (DualAvoidsCycleStep M C) = 2
      ∧ _root_.numCycles (M.φ * cycleDualAlpha C) = M.V - C.len + 2
      ∧ genusSlack M.φ (cycleDualAlpha C) = 0 :=
  ⟨dualAvoidsCycle_numComp_two C hsphere hsimple,
   bankCount_holds C,
   genusSlack_cycleDualAlpha_eq_zero C hsphere⟩

/-- **Assembly of the full `SimpleCycleBankTheorem`** from the unconditional core together
with the bank-label fields.  The labels (`hL`, `hR`, `hsep`) are the residual carried for the
arc-orientation Jordan content; the count fields are discharged unconditionally. -/
def simpleCycleBankTheorem_of_labels (hsphere : M.IsSphereMap) (hsimple : M.IsSimpleGraph)
    (hL : ∀ i j : Fin C.len,
      Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceLeft i) (C.faceLeft j))
    (hR : ∀ i j : Fin C.len,
      Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceRight i) (C.faceRight j))
    (hsep : ∀ i j : Fin C.len,
      ¬ Relation.ReflTransGen (DualAvoidsCycleStep M C) (C.faceLeft i) (C.faceRight j)) :
    SimpleCycleBankTheorem M C where
  dual_numComp_two := dualAvoidsCycle_numComp_two C hsphere hsimple
  bankOrbitCount := bankCount_holds C
  slack_zero := genusSlack_cycleDualAlpha_eq_zero C hsphere
  left_bank := hL
  right_bank := hR
  left_right_sep := hsep

end ProofsInTheBook.ZinanCh35CycleBank

/-! ## Axiom audit (expect clean-3: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35CycleBank.bankCount_holds
#print axioms ProofsInTheBook.ZinanCh35CycleBank.numComponents_eq_numComp_dualStep
#print axioms ProofsInTheBook.ZinanCh35CycleBank.dualAvoidsCycle_numComp_two
#print axioms ProofsInTheBook.ZinanCh35CycleBank.genusSlack_cycleDualAlpha_eq_zero
#print axioms ProofsInTheBook.ZinanCh35CycleBank.Ehalf_cycleDualAlpha
#print axioms ProofsInTheBook.ZinanCh35CycleBank.not_mem_edgeSet_of_star_not_cycleDart
#print axioms ProofsInTheBook.ZinanCh35CycleBank.cycleBankTheorem_core
