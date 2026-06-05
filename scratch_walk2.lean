import Mathlib
import ProofsInTheBook.Chapter31

open ProofsInTheBook.Chapter31
open SimpleGraph

lemma refl_symm {V : Type*} {G : SimpleGraph V} {x y : V}
    (h : Relation.ReflTransGen G.Adj x y) : Relation.ReflTransGen G.Adj y x :=
  (SimpleGraph.reachable_iff_reflTransGen y x).mp ((SimpleGraph.reachable_iff_reflTransGen x y).mpr h).symm

lemma reachable_sup_edge {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (hreach : Relation.ReflTransGen (G.Adj ⊔ (edge u v).Adj) x y) :
    Relation.ReflTransGen G.Adj x y ∨
    (Relation.ReflTransGen G.Adj x u ∧ Relation.ReflTransGen G.Adj v y) ∨
    (Relation.ReflTransGen G.Adj x v ∧ Relation.ReflTransGen G.Adj u y) := by
  induction hreach with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | tail h_trans h_adj ih =>
    rcases h_adj with (hG | hedge)
    · rcases ih with (ih1 | ⟨ih2u, ih2v⟩ | ⟨ih3v, ih3u⟩)
      · exact Or.inl (Relation.ReflTransGen.tail ih1 hG)
      · exact Or.inr (Or.inl ⟨ih2u, Relation.ReflTransGen.tail ih2v hG⟩)
      · exact Or.inr (Or.inr ⟨ih3v, Relation.ReflTransGen.tail ih3u hG⟩)
    · revert hedge
      simp [edge, Sym2.eq]
      intro hedge'
      rcases hedge' with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · intro _
        rcases ih with (ih1 | ⟨ih2u, ih2v⟩ | ⟨ih3v, ih3u⟩)
        · exact Or.inr (Or.inl ⟨ih1, Relation.ReflTransGen.refl⟩)
        · exact Or.inl (Relation.ReflTransGen.trans ih2u (refl_symm ih2v))
        · exact Or.inl ih3v
      · intro _
        rcases ih with (ih1 | ⟨ih2u, ih2v⟩ | ⟨ih3v, ih3u⟩)
        · exact Or.inr (Or.inr ⟨ih1, Relation.ReflTransGen.refl⟩)
        · exact Or.inl ih2u
        · exact Or.inl (Relation.ReflTransGen.trans ih3v (refl_symm ih3u))
