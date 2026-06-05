import Mathlib
import ProofsInTheBook.Chapter31
open SimpleGraph
lemma test {V : Type*} {G : SimpleGraph V} {x y : V} (p : G.Walk x y) : True := by
  induction p with
  | nil => exact True.intro
  | cons v h p' ih =>
    -- check types
    have hv : V := v
    have hh : G.Adj x v := h
    have hp : G.Walk v y := p'
    exact True.intro
