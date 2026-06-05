import Mathlib
import ProofsInTheBook.Chapter31

open ProofsInTheBook.Chapter31
open SimpleGraph

lemma components_eq_of_acyclic {n : ℕ} (edges : Finset (Sym2 (Fin n)))
    (h_acyclic : (fromEdgeSet (edges : Set _)).IsAcyclic) :
    Fintype.card ((fromEdgeSet (edges : Set _)).ConnectedComponent) = n - edges.card := by
  -- mathlib should have something like this
  sorry

lemma uniq_of_covers_and_count {n : ℕ} {available : Finset (Fin n)} {edges : Finset (Sym2 (Fin n))}
    (h_acyclic : (fromEdgeSet (edges : Set _)).IsAcyclic)
    (h_covers : ∀ u, ∃ v ∈ available, (fromEdgeSet (edges : Set _)).Reachable u v)
    (h_count : available.card + edges.card = n) :
    ∀ v ∈ available, ∀ w ∈ available, v ≠ w → ¬ (fromEdgeSet (edges : Set _)).Reachable v w := by
  sorry
