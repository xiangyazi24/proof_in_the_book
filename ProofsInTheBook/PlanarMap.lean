import Mathlib

/-!
# Planar maps via combinatorial maps (Layer 1)

Infrastructure for the faithful formalization of Chapter 12 (Euler's formula applications)
and Chapter 35 (Five Color Theorem), which Mathlib currently lacks.

A **combinatorial map** is a finite dart set `D` with an edge involution `α` (fixed-point-free)
and a vertex rotation `σ`. Vertices = `σ`-orbits, edges = `α`-orbits, faces = `φ`-orbits where
`φ = σ * α`. The Euler characteristic `V - E + F` equals `2 - 2g` for genus `g`; a **plane**
(sphere) map is the faithful genus-zero notion `IsSphereMap := Connected ∧ eulerChar = 2`
(NOT an inductive build certificate — that would risk an incomplete fragment).

This file is Layer 1: the raw map, the orbit counts, and the Euler characteristic.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

/-- A combinatorial (orientable) map on a finite dart set `D`:
edge involution `α` (fixed-point-free) and vertex rotation `σ`. -/
structure CombMap (D : Type*) [Fintype D] [DecidableEq D] where
  /-- Edge involution: pairs each dart with its reverse. -/
  α : Equiv.Perm D
  /-- Vertex rotation: cyclic order of darts around each vertex. -/
  σ : Equiv.Perm D
  /-- `α` is an involution. -/
  α_invol : α * α = 1
  /-- `α` has no fixed dart (every edge has two distinct darts). -/
  α_no_fixed : ∀ d, α d ≠ d

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Face permutation `φ = σ ∘ α`. Its orbits are the faces. -/
def φ (M : CombMap D) : Equiv.Perm D := M.σ * M.α

/-- The `SameCycle` equivalence of a permutation, as a `Setoid` on the dart set.
Its classes are the orbits (cycles, including fixed points). -/
def cycleSetoid (p : Equiv.Perm D) : Setoid D where
  r := p.SameCycle
  iseqv := ⟨fun x => Equiv.Perm.SameCycle.refl p x, fun h => h.symm, fun h h' => h.trans h'⟩

instance (p : Equiv.Perm D) : DecidableRel (cycleSetoid p).r :=
  (inferInstance : DecidableRel p.SameCycle)

instance (p : Equiv.Perm D) : Fintype (Quotient (cycleSetoid p)) :=
  Quotient.fintype (cycleSetoid p)

/-- Number of vertices: the number of `σ`-orbits. -/
def V (M : CombMap D) : ℕ := Fintype.card (Quotient (cycleSetoid M.σ))

/-- Number of edges: the number of `α`-orbits. -/
def E (M : CombMap D) : ℕ := Fintype.card (Quotient (cycleSetoid M.α))

/-- Number of faces: the number of `φ`-orbits. -/
def F (M : CombMap D) : ℕ := Fintype.card (Quotient (cycleSetoid M.φ))

/-- The Euler characteristic `V - E + F`. -/
def eulerChar (M : CombMap D) : ℤ := (V M : ℤ) - (E M : ℤ) + (F M : ℤ)

/-- A power of an involution is either the identity or the involution itself. -/
lemma zpow_involution (α : Equiv.Perm D) (h : α * α = 1) (i : ℤ) :
    α ^ i = 1 ∨ α ^ i = α := by
  have hsq : α ^ (2 : ℤ) = 1 := by
    have h2 : α ^ (2 : ℤ) = α * α := by
      rw [show (2 : ℤ) = 1 + 1 from rfl, zpow_add, zpow_one]
    rw [h2, h]
  rcases Int.even_or_odd i with ⟨r, hr⟩ | ⟨k, hk⟩
  · left
    rw [hr, show r + r = 2 * r from by ring, zpow_mul, hsq, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]

/-- The edge containing a dart `d` is exactly `{d, α d}`: the `α`-orbit of any dart has
the two darts of its edge and no more. -/
lemma alpha_sameCycle_iff (M : CombMap D) (d x : D) :
    M.α.SameCycle d x ↔ x = d ∨ x = M.α d := by
  constructor
  · rintro ⟨i, rfl⟩
    rcases zpow_involution M.α M.α_invol i with h1 | h1
    · left; rw [h1]; rfl
    · right; rw [h1]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

/-- Two darts are in the same vertex iff they share a `σ`-cycle. -/
def vertexConnected (M : CombMap D) : D → D → Prop := fun a b => (M.σ.SameCycle a b)

/-- Adjacency of the underlying multigraph on darts: same vertex, or joined by an edge. -/
def dartStep (M : CombMap D) (a b : D) : Prop :=
  M.σ.SameCycle a b ∨ b = M.α a

/-- The map is connected if every two darts are linked by a chain of `dartStep`s
(same-vertex moves and edge crossings). -/
def Connected (M : CombMap D) : Prop :=
  ∀ a b : D, Relation.ReflTransGen M.dartStep a b

/-- A **plane (sphere) map**: connected and of Euler characteristic `2` (genus zero).
This is the faithful combinatorial definition of a planar graph embedding; it is NOT an
inductive build certificate, so theorems proved for `IsSphereMap` are about all plane graphs. -/
def IsSphereMap (M : CombMap D) : Prop :=
  M.Connected ∧ M.eulerChar = 2

end CombMap

end ProofsInTheBook.PlanarMap
