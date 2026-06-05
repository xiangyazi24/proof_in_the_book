import Mathlib
import ProofsInTheBook.Chapter31
open SimpleGraph
lemma test {V : Type*} {G : SimpleGraph V} {x y : V} (p : G.Walk x y) : True := by
  induction p with
  | nil => exact True.intro
  | cons _ _ _ => exact True.intro
