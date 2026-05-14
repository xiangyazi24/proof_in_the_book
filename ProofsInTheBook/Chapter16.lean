import Mathlib

/-!
# Chapter 16: Borsuk's conjecture

From "Proofs from THE BOOK":

**Borsuk's conjecture**: Can every bounded set in ℝ^d be partitioned
into d+1 parts, each of smaller diameter? Borsuk conjectured yes (1933).

The book discusses the conjecture and its eventual disproof (for d ≥ 298)
by Kahn and Kalai (1993) using combinatorial arguments.
-/

namespace ProofsInTheBook.Chapter16

/--
A finite coloring certificate for a Borsuk-style partition: points with the
same color are required to have pairwise distance below the target bound.
-/
def HasSmallColorClasses {α : Type*} [PseudoMetricSpace α] {d : ℕ} (points : Finset α)
    (diamBound : ℝ) (color : α → Fin (d + 1)) : Prop :=
  ∀ x ∈ points, ∀ y ∈ points, color x = color y → dist x y < diamBound

/-- One color class in the finite partition. -/
def colorClass {α : Type*} {d : ℕ} (points : Finset α) (color : α → Fin (d + 1))
    (c : Fin (d + 1)) : Finset α :=
  points.filter fun x => color x = c

theorem mem_colorClass_iff {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    (points : Finset α) (color : α → Fin (d + 1)) (c : Fin (d + 1)) (x : α) :
    x ∈ colorClass points color c ↔ x ∈ points ∧ color x = c := by
  simp [colorClass]

theorem colorClass_subset_points {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    (points : Finset α) (color : α → Fin (d + 1)) (c : Fin (d + 1)) :
    colorClass points color c ⊆ points := by
  intro x hx
  exact (mem_colorClass_iff points color c x).mp hx |>.1

theorem mem_colorClass_of_mem {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    {points : Finset α} {color : α → Fin (d + 1)} {x : α}
    (hx : x ∈ points) : x ∈ colorClass points color (color x) := by
  rw [mem_colorClass_iff]
  exact ⟨hx, rfl⟩

theorem exists_colorClass_of_mem {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    {points : Finset α} {color : α → Fin (d + 1)} {x : α}
    (hx : x ∈ points) : ∃ c : Fin (d + 1), x ∈ colorClass points color c :=
  ⟨color x, mem_colorClass_of_mem hx⟩

theorem disjoint_colorClass_of_ne {α : Type*} {d : ℕ} [DecidableEq (Fin (d + 1))]
    {points : Finset α} {color : α → Fin (d + 1)} {c₁ c₂ : Fin (d + 1)}
    (hne : c₁ ≠ c₂) : Disjoint (colorClass points color c₁) (colorClass points color c₂) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  have h₁ := (mem_colorClass_iff points color c₁ x).mp hx₁
  have h₂ := (mem_colorClass_iff points color c₂ x).mp hx₂
  exact hne (h₁.2.symm.trans h₂.2)

/--
The basic verification step for a Borsuk partition: every color class has
the advertised smaller pairwise diameter bound.
-/
theorem same_color_dist_lt_of_mem_colorClass {α : Type*} [PseudoMetricSpace α] {d : ℕ}
    [DecidableEq (Fin (d + 1))] {points : Finset α} {diamBound : ℝ}
    {color : α → Fin (d + 1)} (h : HasSmallColorClasses points diamBound color)
    {c : Fin (d + 1)} {x y : α}
    (hx : x ∈ colorClass points color c) (hy : y ∈ colorClass points color c) :
    dist x y < diamBound := by
  rw [mem_colorClass_iff] at hx hy
  exact h x hx.1 y hy.1 (hx.2.trans hy.2.symm)

theorem chapter16 {α : Type*} [PseudoMetricSpace α] {d : ℕ} [DecidableEq (Fin (d + 1))]
    {points : Finset α} {diamBound : ℝ} {color : α → Fin (d + 1)}
    (h : HasSmallColorClasses points diamBound color) (c : Fin (d + 1)) {x y : α}
    (hx : x ∈ colorClass points color c) (hy : y ∈ colorClass points color c) :
    dist x y < diamBound :=
  same_color_dist_lt_of_mem_colorClass h hx hy

end ProofsInTheBook.Chapter16
