import Mathlib

open Finset List Equiv

-- STEP 1: Path Family Type
structure LatticePathFamily (n : ℕ) (V : Type*) [DecidableEq V] where
  perm : Equiv.Perm (Fin n)
  paths : Fin n → List V
  nodup : ∀ i, (paths i).Nodup

def LatticePathFamily.bad {n V} [DecidableEq V] (F : LatticePathFamily n V) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ ((F.paths i).toFinset ∩ (F.paths j).toFinset).Nonempty

variable {V : Type*} [DecidableEq V] [LinearOrder V] {n : ℕ}

-- STEP 2: The Involution
def Path.firstIntersection (p q : List V) : Option V :=
  let common := p.toFinset ∩ q.toFinset
  if h : common.Nonempty then some (common.min' h) else none

def LatticePathFamily.firstBadPair (F : LatticePathFamily n V) : Option (Fin n × Fin n) :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => p.1 < p.2 ∧ (Path.firstIntersection (F.paths p.1) (F.paths p.2)).isSome))
  |>.min

def Path.splitAtFirst (p : List V) (v : V) : List V × List V :=
  let idx := p.findIdx (· == v)
  (p.take (idx + 1), p.drop (idx + 1))

def Path.swapTailAt (pi pj : List V) (v : V) : List V × List V :=
  let (pi_head, pi_tail) := Path.splitAtFirst pi v
  let (pj_head, pj_tail) := Path.splitAtFirst pj v
  (pi_head ++ pj_tail, pj_head ++ pi_tail)

lemma splitAtFirst_append_eq (p : List V) (v : V) :
    (Path.splitAtFirst p v).1 ++ (Path.splitAtFirst p v).2 = p := by
  dsimp [Path.splitAtFirst]
  exact take_append_drop _ _
