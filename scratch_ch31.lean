import Mathlib
import ProofsInTheBook.Chapter31

open ProofsInTheBook.Chapter31

namespace ProofsInTheBook.Chapter31

structure DecodeForest (n : ℕ) (state : Finset (Fin n) × Finset (Sym2 (Fin n))) : Prop where
  acyclic : (SimpleGraph.fromEdgeSet (state.2 : Set (Sym2 (Fin n)))).IsAcyclic
  available_covers : ∀ u : Fin n, ∃ v ∈ state.1, (SimpleGraph.fromEdgeSet (state.2 : Set _)).Reachable u v
  not_reach_future : ∀ v ∈ state.1, ∀ f ∈ state.1, v ≠ f → ¬ (SimpleGraph.fromEdgeSet (state.2 : Set _)).Reachable v f

-- wait, the third one is `not_reach_future`, which is `available_uniq_per_component`.
-- Do we need it to prove acyclicity?
-- "Adding edge {nextLeaf, s[i]} preserves acyclicity iff ¬ Reachable nextLeaf s[i]"
-- If `nextLeaf ∈ available` and `s[i]`'s root is `r' ∈ available`,
-- then `Reachable nextLeaf s[i]` implies `Reachable nextLeaf r'`.
-- If we have `available_uniq_per_component`, since `nextLeaf ≠ r'`, they are not reachable.
-- YES! We NEED `available_uniq_per_component` to prove `¬ Reachable nextLeaf s[i]`!
-- So we keep exactly the 3 invariants from the Oracle.

structure DecodeForestFull (n : ℕ) (state : Finset (Fin n) × Finset (Sym2 (Fin n))) : Prop where
  acyclic : (SimpleGraph.fromEdgeSet (state.2 : Set (Sym2 (Fin n)))).IsAcyclic
  covers : ∀ u : Fin n, ∃ v ∈ state.1, (SimpleGraph.fromEdgeSet (state.2 : Set _)).Reachable u v
  uniq : ∀ v ∈ state.1, ∀ w ∈ state.1, v ≠ w → ¬ (SimpleGraph.fromEdgeSet (state.2 : Set _)).Reachable v w

lemma decodeForest_init (n : ℕ) (hn : 2 ≤ n) :
    DecodeForestFull n (Finset.univ, ∅) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u p hp
    have hne := hp.ne_nil
    cases p with
    | nil => exact False.elim (hne rfl)
    | cons hadj _ => simp at hadj
  · intro u
    exact ⟨u, Finset.mem_univ u, SimpleGraph.Walk.nil.reachable⟩
  · intro v _ w _ hvw hreach
    rcases hreach with ⟨walk⟩
    cases walk with
    | nil => exact hvw rfl
    | cons hadj _ => simp at hadj

end ProofsInTheBook.Chapter31
