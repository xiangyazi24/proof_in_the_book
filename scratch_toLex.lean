import Mathlib

open Finset List Equiv

variable {n : ℕ} {V : Type*} [DecidableEq V] [LinearOrder V]

structure LatticePathFamily (n : ℕ) (V : Type*) [DecidableEq V] where
  perm : Equiv.Perm (Fin n)
  paths : Fin n → List V
  nodup : ∀ i, (paths i).Nodup

def Path.firstIntersection (p q : List V) : Option V :=
  let common := p.toFinset ∩ q.toFinset
  if h : common.Nonempty then some (common.min' h) else none

def LatticePathFamily.firstBadPair (F : LatticePathFamily n V) : Option (Fin n × Fin n) :=
  let badPairs := (Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => p.1 < p.2 ∧ (Path.firstIntersection (F.paths p.1) (F.paths p.2)).isSome)
  if h : badPairs.Nonempty then
    let lexPairs := badPairs.image toLex
    have h_nonempty : lexPairs.Nonempty := Finset.Nonempty.image h toLex
    some (ofLex (lexPairs.min' h_nonempty))
  else none
