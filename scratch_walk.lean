import Mathlib
import ProofsInTheBook.Chapter31

open ProofsInTheBook.Chapter31
open SimpleGraph

lemma reachable_sup_edge {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (hreach : (G ⊔ edge u v).Reachable x y) :
    G.Reachable x y ∨
    (G.Reachable x u ∧ G.Reachable v y) ∨
    (G.Reachable x v ∧ G.Reachable u y) := by
  rcases hreach with ⟨p⟩
  induction p with
  | nil => exact Or.inl Walk.nil.reachable
  | cons h_adj p' ih =>
    rcases h_adj with (hG | hedge)
    · rcases ih with (ih1 | ⟨ih2u, ih2v⟩ | ⟨ih3v, ih3u⟩)
      · exact Or.inl (Reachable.trans (Adj.reachable hG) ih1)
      · exact Or.inr (Or.inl ⟨Reachable.trans (Adj.reachable hG) ih2u, ih2v⟩)
      · exact Or.inr (Or.inr ⟨Reachable.trans (Adj.reachable hG) ih3v, ih3u⟩)
    · revert hedge
      simp [edge, Sym2.eq]
      intro hedge'
      rcases hedge' with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · intro _
        rcases ih with (ih1 | ⟨ih2u, ih2v⟩ | ⟨ih3v, ih3u⟩)
        · exact Or.inr (Or.inl ⟨(Walk.nil.reachable : G.Reachable u u), ih1⟩)
        · exact Or.inl (Reachable.trans ih2u.symm ih2v)
        · exact Or.inr (Or.inl ⟨ih3v, Reachable.trans ih3u.symm ih2v⟩)
      · intro _
        rcases ih with (ih1 | ⟨ih2u, ih2v⟩ | ⟨ih3v, ih3u⟩)
        · exact Or.inr (Or.inr ⟨(Walk.nil.reachable : G.Reachable v v), ih1⟩)
        · exact Or.inr (Or.inr ⟨ih2u, Reachable.trans ih2v.symm ih3u⟩)
        · exact Or.inl (Reachable.trans ih3v.symm ih3u)
