import Mathlib
import ProofsInTheBook.Chapter31

open ProofsInTheBook.Chapter31
open SimpleGraph

namespace ProofsInTheBook.Chapter31

/-! ## Ch31 Tier 2 sub-development:
    pruferDecode injectivity via degree characterization

Goal: prove `Function.Injective pruferDecode` so that we can construct
`pruferEquiv : LabeledTree n ≃ pruferCodeSpace n` from cardinality squeeze.

Heart: in the decoded tree, deg(v) = 1 + (# j with s j = v). -/

/-- Count of times vertex `v` appears as `s j` for j with j.val < m. -/
private def countOccurrences {n : ℕ} (s : pruferCodeSpace n) (m : ℕ) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun (j : Fin (n - 2)) => j.val < m ∧ s j = v)).card

/-- The decoded edge set's underlying graph: degree of `v` after `m` iterations
of pruferDecodeAux equals (# of s-occurrences of v with index < m) +
(0 if v still active, 1 if v has been removed). -/
private theorem pruferDecodeAux_degree (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (m : ℕ) (hm : m ≤ n - 2) (v : Fin n) :
    (fromEdgeSet (V := Fin n)
      ((pruferDecodeAux hn s m hm).val.2 : Set (Sym2 (Fin n)))).degree v =
    countOccurrences s m v +
    (if v ∈ (pruferDecodeAux hn s m hm).val.1 then 0 else 1) := by
  induction m with
  | zero =>
    -- Base case: empty edge set ⇒ degree 0; count 0; v in univ adds 0.
    -- Show both sides equal 0.
    have hcount : countOccurrences s 0 v = 0 := by
      apply Finset.card_eq_zero.mpr
      ext j; simp [countOccurrences]
    have hmem : v ∈ (pruferDecodeAux hn s 0 hm).val.1 := by
      show v ∈ Finset.univ
      exact Finset.mem_univ v
    -- The graph at state 0 has empty edges. The degree is 0.
    -- Direct compute: degree in empty edge graph.
    -- TODO: base case stuck on dependent-typing motive in `fromEdgeSet` rewrite.
    -- Tried: rw [Finset.coe_empty, fromEdgeSet_empty], simp_only variants,
    -- conv_lhs, show, change. All hit "motive is not type correct" or
    -- "simp made no progress". The blocker is rewriting inside
    -- `((pruferDecodeAux ... 0 ...).val.2 : Set (Sym2 (Fin n)))` — the coercion
    -- between Finset and Set under the dependent Set ascription doesn't reduce
    -- cleanly even though `(pruferDecodeAux ... 0 ...).val.2 = ∅` is `rfl`.
    -- Pivot strategy: instead of degree-counting, prove
    -- `Function.LeftInverse pruferDecode (pruferEncode hn)` via induction on
    -- tree size. This bypasses degree counting entirely and is the standard
    -- presentation of Cayley/Prüfer.
    sorry
  | succ m ih =>
    sorry

end ProofsInTheBook.Chapter31
