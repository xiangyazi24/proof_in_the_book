import Mathlib
import Archive.Wiedijk100Theorems.FriendshipGraphs

/-!
# Chapter 40: Of friends and politicians

From "Proofs from THE BOOK":

**Friendship theorem** (Erdős–Rényi–Sós 1966): In a finite graph where every two
distinct vertices have exactly one common neighbor, there exists a vertex adjacent
to all others (a "politician").

The book's proof uses spectral graph theory: the adjacency matrix A
satisfies A² = J + (k-1)I. The graph is d-regular; eigenvalue analysis and
a characteristic polynomial argument over 𝔽_p (for p | d-1) yields contradiction
unless d ≤ 2, which is handled separately.

Formalized in Mathlib's archive as `Theorems100.friendship_theorem`.
-/

namespace ProofsInTheBook.Chapter40

open SimpleGraph Theorems100

/-!
### Friendship theorem via Mathlib Archive

Every finite nonempty friendship graph has a politician.
-/

theorem chapter40_friendship_theorem
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hG : Friendship G) : ExistsPolitician G :=
  Theorems100.friendship_theorem hG

theorem chapter40 {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hG : Friendship G) : ExistsPolitician G :=
  chapter40_friendship_theorem G hG

end ProofsInTheBook.Chapter40
