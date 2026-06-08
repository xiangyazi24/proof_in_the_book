import ProofsInTheBook.TouchRank

/-!
# The bank-component touch certificate for `faceCorr₂` (Chapter 35, the F-count residue)

This file builds the **position-free bank-component reduction** that turns the one
genuinely topological residue of Chapter 35's corrected face count into its cleanest
closed form, and assembles the unconditional downstream consequences from it.

`TouchRank.lean` reduced `(cutCapMap2).F ≥ M.F + 2` to a `FaceCorrTouchCert C`: the
cycle-decomposition word data of `faceCorr₂` (always available) plus the `2·len − 2`
bank generator edges on `phiLift`-orbits and a per-*letter* reachability field
`endpoint_reachable`.  That per-letter field still references the concatenated word's
internal indexing.  Here we:

* **Reduce the per-letter field to a per-cycle field.**  Every letter of `concatWord Ls`
  swaps two *consecutive* elements of one of the cycle lists `L ∈ Ls`
  (`concatWord_letter_mem`, by induction on `Ls` through `appendWord`).  Hence the
  bank-reachability only needs to know that *each `faceCorr₂`-cycle's darts all lie in one
  connected bank component* — the natural topological statement "every `faceCorr₂`-cycle is
  swallowed by one bank component", with no reference to word positions.

* **Package this as `BankComponentCert C`** — the position-free analogue of
  `FaceCorrSplitCert`/`FaceCorrTouchCert`: the cycle lists (with nodup, length facts and
  the factorisation, all of which are *provable* by `exists_cycleListProd_nodup`), the
  `2·len − 2` generator edges, and the one isolated field `same_component`.

* **Build `FaceCorrTouchCert` from it** (`BankComponentCert.toTouchCert`), discharging
  `endpoint_reachable` by `concatWord_letter_mem` + `same_component`, and re-export the
  unconditional `cutCapMap2_F_lower` / Jordan / separation consequences of `TouchRank.lean`.

## The isolated residue

`same_component` is the single genuinely topological joint, identical in mathematical
content to the `NumCyclesCutPhi2` core of `PlanarMapCutCap2Counts.lean` / the
`merge_u_v` + split links of `PlanarMapSeamSpec.lean`: it says the `phiLift`-orbits met by
one `faceCorr₂`-cycle are connected through the bank generator graph.  As recorded in
`FaceCorrWord.lean` and `PlanarMapSeamSpec.lean`, the repository carries **no** concrete
abstract `SimplePrimalCycle` instance and **no** abstract characterisation of `faceCorr₂`'s
seam/orbit structure (it lives only on the computable mirror, kernel-`#eval`-anchored), so
an *unconditional* `BankComponentCert` cannot be exhibited for lack of a concrete cut —
exactly as the split route could not exhibit an unconditional `FaceCorrSplitCert`.  The
reduction below makes the residue minimal: a per-cycle component statement.

### Kernel anchors (from `PlanarMapSeamSpec.lean` / `FaceCorrWord.lean`)

`faceCorr₂` is the two cap chains `C₊ ⊔ C₋`.  Triangle (`k = 3`): both pure `3`-cycles of
`phiLift`-fixed caps, `numCycles φ'₂ = 4 = F + 2`.  Tetra mixed cut (`k = 3`): a pure
`−`-chain and a mixed `+`-chain `γ₀u₀v₀γ₁u₁v₁γ₂u₂v₂` with `phiLift γᵢ = γᵢ`,
`phiLift vᵢ = u_{i+1}`.  The bank generator graph (two `len − 1`-edge path forests,
`2·len − 2` edges total) is exactly the witness that each cap chain lies in one component.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function List

namespace ProofsInTheBook

namespace TouchCert

open ForcedSplits ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.PlanarMap.SeamChain

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Per-letter structure of the concatenated word

Every letter of `concatWord Ls` swaps two consecutive elements `L[r]`, `L[r+1]` of one of
the cycle lists `L ∈ Ls`.  This is the bridge from the word's internal index to the
cycle-list membership the bank-component statement is phrased over. -/

/-- **Each letter of `wordOfList L` swaps consecutive list elements.**  Letter `j` is the
swap of `L[j]` and `L[j+1]`, both members of `L`, with `j + 1 < L.length`. -/
lemma wordOfList_letter_mem (L : List X) (j : Fin (L.length - 1)) :
    ∃ r : ℕ, ∃ (hr : r + 1 < L.length),
      (wordOfList L j).x = L[r]'(by omega) ∧ (wordOfList L j).y = L[r+1]'hr := by
  refine ⟨j.val, by have := j.isLt; omega, ?_, ?_⟩
  · rfl
  · rfl

/-- **Each letter of `concatWord Ls` swaps consecutive elements of one cycle list.**
There is a list `L ∈ Ls` and an index `r` with `r + 1 < L.length`,
`(concatWord Ls j).x = L[r]` and `(concatWord Ls j).y = L[r+1]`. -/
lemma concatWord_letter_mem :
    ∀ (Ls : List (List X)) (j : Fin (concatLen Ls)),
      ∃ L ∈ Ls, ∃ r : ℕ, ∃ (hr : r + 1 < L.length),
        (concatWord Ls j).x = L[r]'(by omega) ∧ (concatWord Ls j).y = L[r+1]'hr := by
  intro Ls
  induction Ls with
  | nil => intro j; exact absurd j.isLt (by simp [concatLen])
  | cons L rest ih =>
      intro j
      -- `concatWord (L :: rest) = appendWord (wordOfList L) (concatWord rest)`
      show ∃ L' ∈ (L :: rest), ∃ r : ℕ, ∃ (hr : r + 1 < L'.length),
        (appendWord (wordOfList L) (concatWord rest) j).x = L'[r]'(by omega) ∧
          (appendWord (wordOfList L) (concatWord rest) j).y = L'[r+1]'hr
      by_cases hj : j.val < L.length - 1
      · -- letter lives in the first block `wordOfList L`
        obtain ⟨r, hr, hx, hy⟩ := wordOfList_letter_mem L ⟨j.val, hj⟩
        refine ⟨L, List.mem_cons_self .., r, hr, ?_, ?_⟩
        · show (appendWord (wordOfList L) (concatWord rest) j).x = _
          rw [appendWord, dif_pos hj] at *; exact hx
        · show (appendWord (wordOfList L) (concatWord rest) j).y = _
          rw [appendWord, dif_pos hj] at *; exact hy
      · -- letter lives in the tail block `concatWord rest`
        have hjlen : j.val < concatLen (L :: rest) := j.isLt
        have hrestlt : j.val - (L.length - 1) < concatLen rest := by
          simp only [concatLen] at hjlen; omega
        obtain ⟨L', hL', r, hr, hx, hy⟩ := ih ⟨j.val - (L.length - 1), hrestlt⟩
        refine ⟨L', List.mem_cons_of_mem L hL', r, hr, ?_, ?_⟩
        · show (appendWord (wordOfList L) (concatWord rest) j).x = _
          rw [appendWord, dif_neg hj]; exact hx
        · show (appendWord (wordOfList L) (concatWord rest) j).y = _
          rw [appendWord, dif_neg hj]; exact hy

/-- `L[r]` and `L[r+1]` are both members of `L`. -/
lemma getElem_mem_pair (L : List X) {r : ℕ} (hr : r + 1 < L.length) :
    (L[r]'(by omega)) ∈ L ∧ (L[r+1]'hr) ∈ L :=
  ⟨List.getElem_mem _, List.getElem_mem _⟩

/-! ## The nodup cycle-decomposition data

`exists_cycleListProd` (FaceCorrWord.lean) produces, for any permutation, a list-of-lists
of `length ≥ 2` lists whose `cycleListProd` is the permutation.  We strengthen it to carry
**Nodup** for each list (the `toList` cycle supports are nodup), which is what the
bank-component statement and the per-cycle reachability need. -/

/-- **Every finite permutation is a `cycleListProd` of nodup lists of length `≥ 2`.**
Reproves `exists_cycleListProd` carrying the nodup witness of each cycle support. -/
theorem exists_cycleListProd_nodup (q : Equiv.Perm X) :
    ∃ Ls : List (List X),
      (∀ L ∈ Ls, 2 ≤ L.length) ∧ (∀ L ∈ Ls, L.Nodup) ∧ cycleListProd Ls = q := by
  classical
  induction q using Equiv.Perm.cycle_induction_on with
  | base_one => exact ⟨[], by simp, by simp, rfl⟩
  | base_cycles σ hσ =>
      obtain ⟨x, hx, -⟩ := id hσ
      have hxs : x ∈ σ.support := by rw [Equiv.Perm.mem_support]; exact hx
      refine ⟨[Equiv.Perm.toList σ x], ?_, ?_, ?_⟩
      · intro L hL
        simp only [List.mem_singleton] at hL; subst hL
        exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hxs
      · intro L hL
        simp only [List.mem_singleton] at hL; subst hL
        exact Equiv.Perm.nodup_toList σ x
      · simp only [cycleListProd, mul_one, cycleOfList]
        rw [Equiv.Perm.formPerm_toList, Equiv.Perm.IsCycle.cycleOf_eq hσ hx]
  | induction_disjoint σ τ hdisj hσ hστ hτ =>
      obtain ⟨Lσ, hLσpos, hLσnd, hLσ⟩ := hστ
      obtain ⟨Lτ, hLτpos, hLτnd, hLτ⟩ := hτ
      refine ⟨Lσ ++ Lτ, ?_, ?_, ?_⟩
      · intro L hL
        rcases List.mem_append.mp hL with h | h
        · exact hLσpos L h
        · exact hLτpos L h
      · intro L hL
        rcases List.mem_append.mp hL with h | h
        · exact hLσnd L h
        · exact hLτnd L h
      · rw [cycleListProd_append, hLσ, hLτ]

end TouchCert

/-! ## The bank-component certificate and the unconditional downstream

We package the position-free residue as `BankComponentCert C` and build a
`FaceCorrTouchCert C` from it, threading into the unconditional `TouchRank.lean`
consequences.  The single isolated topological field is `same_component`: every
`faceCorr₂`-cycle's darts lie in one connected bank component. -/

namespace PlanarMap

open ForcedSplits ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.TouchCert

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

/-- **The bank-component certificate for `faceCorr₂`** (position-free).  Carries the nodup
cycle-decomposition lists of `faceCorr₂` (always available, by `exists_cycleListProd_nodup`)
plus the `2·len − 2` bank generator edges on `phiLift`-orbits, and the single isolated
topological field `same_component`: every `faceCorr₂`-cycle's darts lie in one connected
component of the bank generator graph.  This is the cleanest residue — no word positions, no
per-letter indexing: just "each `faceCorr₂`-cycle is swallowed by one bank component". -/
structure BankComponentCert (C : SimplePrimalCycle M) where
  /-- The cycle-decomposition support lists of `faceCorr₂`. -/
  Ls : List (List C.CutDart)
  /-- Each cycle list has length `≥ 2` (a genuine cycle). -/
  Ls_len : ∀ L ∈ Ls, 2 ≤ L.length
  /-- Each cycle list is nodup. -/
  Ls_nodup : ∀ L ∈ Ls, L.Nodup
  /-- The cycle-decomposition product reconstructs `faceCorr₂`. -/
  factor : FaceCorrWord.cycleListProd Ls = C.faceCorr2
  /-- The `2·len − 2` bank generator edges on `phiLift`-orbits. -/
  gen : Fin (2 * C.len - 2) → POrb C.phiLift × POrb C.phiLift
  /-- **The isolated topological residue.**  Every `faceCorr₂`-cycle's darts lie in one
  connected component of the bank generator graph: any two darts of a single cycle list have
  `gen`-reachable `phiLift`-orbits. -/
  same_component : ∀ L ∈ Ls, ∀ x ∈ L, ∀ y ∈ L,
    Relation.EqvGen (genRel gen) (pOrbOf C.phiLift x) (pOrbOf C.phiLift y)

/-- **The touch-rank certificate built from a bank-component certificate.**  The
`endpoint_reachable` field of `FaceCorrTouchCert` is discharged from `same_component`: every
letter's endpoints are consecutive elements `L[r], L[r+1]` of one cycle list `L ∈ Ls`
(`concatWord_letter_mem`), hence members of `L`, hence in one bank component. -/
def BankComponentCert.toTouchCert {C : SimplePrimalCycle M}
    (cert : C.BankComponentCert) : C.FaceCorrTouchCert where
  Ls := cert.Ls
  Ls_pos := fun L hL => by have := cert.Ls_len L hL; omega
  factor := cert.factor
  gen := cert.gen
  endpoint_reachable := by
    intro j
    obtain ⟨L, hL, r, hr, hx, hy⟩ := concatWord_letter_mem cert.Ls j
    rw [hx, hy]
    obtain ⟨hxmem, hymem⟩ := getElem_mem_pair L hr
    exact cert.same_component L hL _ hxmem _ hymem

/-- **The corrected face-count lower bound from a bank-component certificate**
(position-free, unconditional in the word/`prefix_eq`).  `(cutCapMap2).F ≥ M.F + 2`. -/
theorem cutCapMap2_F_lower_of_bankCert (C : SimplePrimalCycle M)
    (cert : C.BankComponentCert) :
    (C.cutCapMap2).F ≥ M.F + 2 :=
  C.cutCapMap2_F_lower_of_touchCert cert.toTouchCert

/-- **The lower-bound Jordan / chord-separation theorem from a bank-component certificate.**
No cut edge of a simple primal cycle on a sphere is straddled by a cycle-avoiding dual path,
consuming only the position-free lower bound and the standing connectivity / Euler
parameters. -/
theorem jordan_simple_cycle2_lower_of_bankCert (C : SimplePrimalCycle M)
    (cert : C.BankComponentCert)
    (hchi : M.eulerChar = 2)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  C.jordan_simple_cycle2_lower_of_touchCert cert.toTouchCert hchi hconn i

end SimplePrimalCycle

end CombMap

end PlanarMap

/-! ## Non-vacuity: the reduction machinery is satisfiable and non-degenerate

The genuinely topological residue (`same_component`) cannot be exhibited unconditionally —
the repository carries no concrete abstract `SimplePrimalCycle` instance (see the file
header) — so we instead exercise the **position-free reduction** itself on a concrete word,
ruling out the "vacuous reduction" failure mode for the new layer:

* `exists_cycleListProd_nodup` is exercised on the `3`-cycle `(0 1 2)` of `Fin 3`.
* `concatWord_letter_mem` is exercised on `Ls = [[0,1,2]]`: its two letters are the
  consecutive swaps `(0,1)` and `(1,2)`, both pairs of list members.

These confirm the per-letter → per-cycle bridge fires non-degenerately on a genuine
multi-letter word. -/

namespace TouchCert

open ForcedSplits ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.PlanarMap.SeamChain

/-- The nodup cycle-decomposition existence fires on `(0 1 2)` of `Fin 3`. -/
example : ∃ Ls : List (List (Fin 3)),
    (∀ L ∈ Ls, 2 ≤ L.length) ∧ (∀ L ∈ Ls, L.Nodup) ∧
      cycleListProd Ls = cycleOfList ([0, 1, 2] : List (Fin 3)) :=
  exists_cycleListProd_nodup (cycleOfList ([0, 1, 2] : List (Fin 3)))

/-- The first letter of `concatWord [[0,1,2]]` swaps consecutive list members `0`, `1`. -/
example :
    ∃ L ∈ ([[0, 1, 2]] : List (List (Fin 3))), ∃ r : ℕ, ∃ (hr : r + 1 < L.length),
      (concatWord ([[0, 1, 2]] : List (List (Fin 3)))
        ⟨0, by decide⟩).x = L[r]'(by omega) ∧
      (concatWord ([[0, 1, 2]] : List (List (Fin 3)))
        ⟨0, by decide⟩).y = L[r+1]'hr :=
  concatWord_letter_mem ([[0, 1, 2]] : List (List (Fin 3))) ⟨0, by decide⟩

/-- The second letter of `concatWord [[0,1,2]]` swaps consecutive list members `1`, `2`. -/
example :
    ∃ L ∈ ([[0, 1, 2]] : List (List (Fin 3))), ∃ r : ℕ, ∃ (hr : r + 1 < L.length),
      (concatWord ([[0, 1, 2]] : List (List (Fin 3)))
        ⟨1, by decide⟩).x = L[r]'(by omega) ∧
      (concatWord ([[0, 1, 2]] : List (List (Fin 3)))
        ⟨1, by decide⟩).y = L[r+1]'hr :=
  concatWord_letter_mem ([[0, 1, 2]] : List (List (Fin 3))) ⟨1, by decide⟩

end TouchCert

end ProofsInTheBook

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.TouchCert.concatWord_letter_mem
#print axioms ProofsInTheBook.TouchCert.exists_cycleListProd_nodup
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.cutCapMap2_F_lower_of_bankCert
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.jordan_simple_cycle2_lower_of_bankCert
