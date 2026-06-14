import Mathlib
import ProofsInTheBook.Chapter13

/-!
# Ch13 cyclic-sign helpers (Cauchy rigidity, combinatorial layer)

This file is the *cyclic-list* layer of the discrete Cauchy sign-change lemma.

Around a vertex of a triangulated signed sphere the edge signs form a **cyclic**
sequence in `EdgeSign = {+, -, 0}`.  Cauchy's argument counts how many times the
sign *flips* as we walk once around the vertex, **skipping the zeros** (edges whose
dihedral angle does not change).

We model "the signs around a vertex/face in cyclic order" by a `List EdgeSign`
together with the convention that the list is read cyclically (the successor of the
last entry is the first).  The two main definitions are:

* `cyclicFlipCount : List α → ℕ` (for `DecidableEq α`) — the number of cyclically
  adjacent **unequal** pairs, i.e. the sign-flip count of a cyclic sequence.
* `cyclicFlipCountSkipZeros : List EdgeSign → ℕ` — the flip count after dropping the
  zeros, i.e. `cyclicFlipCount` of the strict sub-sequence `xs.filterMap toStrict`.

The three facts Cauchy's proof needs, all proved here with no `sorry`/`axiom`:

1. `cyclicFlipCountSkipZeros_eq_strict`: zeros are genuinely dropped —
   `cyclicFlipCountSkipZeros xs = cyclicFlipCount (xs.filterMap EdgeSign.toStrict)`.
2. `cyclicFlipCount_even` (for a two-valued alphabet, here `StrictEdgeSign`): the
   number of flips around a *cycle* is even (each `+→-` is matched by a `-→+`).
3. `cyclicFlipCountSkipZeros_insert_zero`: inserting a zero anywhere does not change
   the skip-zero flip count.
-/

namespace ProofsInTheBook.Ch13CyclicSigns

open ProofsInTheBook.Chapter13
open EdgeSign

/-! ## The cyclic flip count of a list -/

variable {α : Type*} [DecidableEq α]

/-- Count cyclically-adjacent unequal pairs of `x :: xs`, where the cyclic successor
of the last element is `first`.  `firstAux first prev xs` walks the tail `xs` with
`prev` the previous element, and at the end compares the last element to `first`. -/
def flipAux (first : α) : α → List α → ℕ
  | prev, [] => if prev ≠ first then 1 else 0
  | prev, x :: xs => (if prev ≠ x then 1 else 0) + flipAux first x xs

/-- The cyclic flip count of a list: the number of cyclically adjacent unequal pairs.
For a one-element (or empty) list it is `0`. -/
def cyclicFlipCount : List α → ℕ
  | [] => 0
  | x :: xs => flipAux x x xs

/-- The cyclic skip-zero flip count of a list of `EdgeSign`s: drop the zeros, then
take the cyclic flip count of the resulting strict sequence. -/
def cyclicFlipCountSkipZeros (xs : List EdgeSign) : ℕ :=
  cyclicFlipCount (xs.filterMap EdgeSign.toStrict)

/-- (1) Zeros are dropped: by definition, the skip-zero count is the cyclic flip
count of the strict sub-sequence. -/
@[simp] theorem cyclicFlipCountSkipZeros_eq_strict (xs : List EdgeSign) :
    cyclicFlipCountSkipZeros xs = cyclicFlipCount (xs.filterMap EdgeSign.toStrict) := rfl

/-! ## Parity of the cyclic flip count over a two-valued alphabet

We prove the flip count is even for `StrictEdgeSign = {+, -}`.  The proof maps signs
to `ZMod 2` and telescopes: the indicator `[a ≠ b]` equals `valZ a + valZ b` in
`ZMod 2`, so the cyclic sum telescopes to `0`. -/

/-- A two-valued sign as an element of `ZMod 2`. -/
def StrictEdgeSign.valZ : StrictEdgeSign → ZMod 2
  | StrictEdgeSign.plus => 0
  | StrictEdgeSign.minus => 1

/-- For a two-valued alphabet, the inequality indicator equals the `ZMod 2` sum of
the two values: `[a ≠ b] = valZ a + valZ b`. -/
theorem indicator_eq_valZ_add (a b : StrictEdgeSign) :
    ((if a ≠ b then 1 else 0 : ℕ) : ZMod 2) = StrictEdgeSign.valZ a + StrictEdgeSign.valZ b := by
  cases a <;> cases b <;> decide

/-- The `ZMod 2` value of `flipAux first prev xs` telescopes to `valZ prev + valZ first`. -/
theorem flipAux_valZ (first : StrictEdgeSign) :
    ∀ (prev : StrictEdgeSign) (xs : List StrictEdgeSign),
      ((flipAux first prev xs : ℕ) : ZMod 2)
        = StrictEdgeSign.valZ prev + StrictEdgeSign.valZ first
  | prev, [] => by
      simp only [flipAux]
      have := indicator_eq_valZ_add prev first
      simpa using this
  | prev, x :: xs => by
      simp only [flipAux, Nat.cast_add]
      rw [indicator_eq_valZ_add prev x, flipAux_valZ first x xs]
      have hxx : StrictEdgeSign.valZ x + StrictEdgeSign.valZ x = 0 := by
        cases x <;> decide
      calc StrictEdgeSign.valZ prev + StrictEdgeSign.valZ x
              + (StrictEdgeSign.valZ x + StrictEdgeSign.valZ first)
          = StrictEdgeSign.valZ prev
              + (StrictEdgeSign.valZ x + StrictEdgeSign.valZ x) + StrictEdgeSign.valZ first := by
            ring
        _ = StrictEdgeSign.valZ prev + StrictEdgeSign.valZ first := by rw [hxx]; ring

/-- (2) Cyclic parity: over the two-valued alphabet `StrictEdgeSign`, the cyclic flip
count is even. -/
theorem cyclicFlipCount_even (xs : List StrictEdgeSign) :
    Even (cyclicFlipCount xs) := by
  rcases xs with _ | ⟨x, xs⟩
  · simp [cyclicFlipCount]
  · have h : ((cyclicFlipCount (x :: xs) : ℕ) : ZMod 2) = 0 := by
      simp only [cyclicFlipCount]
      rw [flipAux_valZ x x xs]
      cases x <;> decide
    exact ZMod.natCast_eq_zero_iff_even.mp h

/-! ## Inserting a zero does not change the skip-zero flip count -/

/-- (3) Inserting a zero anywhere into the cyclic sequence does not change the
skip-zero flip count, because `filterMap toStrict` drops the inserted zero. -/
theorem cyclicFlipCountSkipZeros_insert_zero (xs ys : List EdgeSign) :
    cyclicFlipCountSkipZeros (xs ++ EdgeSign.zero :: ys)
      = cyclicFlipCountSkipZeros (xs ++ ys) := by
  simp only [cyclicFlipCountSkipZeros, List.filterMap_append, List.filterMap_cons]
  rfl

/-- Parity of the skip-zero count: it is even (it equals a strict cyclic flip count). -/
theorem cyclicFlipCountSkipZeros_even (xs : List EdgeSign) :
    Even (cyclicFlipCountSkipZeros xs) :=
  cyclicFlipCount_even _

end ProofsInTheBook.Ch13CyclicSigns
