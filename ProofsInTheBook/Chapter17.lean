import Mathlib

/-!
# Chapter 17: Sets, functions, and the continuum hypothesis

From "Proofs from THE BOOK":

**Cantor's theorem**: For any set S, |S| < |𝒫(S)| = 2^|S|.

The book proves this via the diagonal argument: if f : S → 𝒫(S),
the set D = {s ∈ S | s ∉ f(s)} is not in the range of f.

Also proved: |ℝ| = |ℝ²| (space-filling curves / interleaving),
the Schröder-Bernstein theorem, and a discussion of the
independence of the continuum hypothesis.
-/

namespace ProofsInTheBook.Chapter17

/-!
### Cantor's theorem

*Book proof (diagonal argument).* Suppose f : S → 𝒫(S) is surjective.
Let D = {s ∈ S | s ∉ f(s)}. Then D ∈ 𝒫(S), so D = f(d) for some d.
If d ∈ D, then d ∉ f(d) = D, contradiction. If d ∉ D, then d ∈ f(d) = D,
contradiction.
-/

theorem chapter17_cantor {α : Type*} (f : α → Set α) :
    ¬ Function.Surjective f := by
  intro hsurj
  let D : Set α := {x | x ∉ f x}
  rcases hsurj D with ⟨d, hd⟩
  by_cases hmem : d ∈ f d
  · have hdD : d ∈ D := by
      simpa [hd] using hmem
    have hnot : d ∉ f d := by
      simpa [D] using hdD
    exact hnot hmem
  · have hdD : d ∈ D := by
      simpa [D] using hmem
    have hfd : d ∈ f d := by
      simpa [hd] using hdD
    exact hmem hfd

theorem chapter17 {α : Type*} :
    ¬ ∃ f : α → Set α, Function.Surjective f := by
  rintro ⟨f, hf⟩
  exact chapter17_cantor f hf

end ProofsInTheBook.Chapter17
